import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_12869.Model
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


end PEqualNP.Outside.L_meta_12869.Model

namespace PEqualNP.Outside.L_meta_12869
open PEqualNP.Outside.L_meta_12869.Model
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

end PEqualNP.Outside.L_meta_12869

namespace PEqualNP.Outside.L_meta_12869
open PEqualNP.Outside.L_meta_12869.Model
def gbK8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x841fd21083f842107b08420bf28041ff40083f680107f90020fea0041fc40083f080107fcc020ff18041fd30083f860107fc8020f790041fe20083f440107f48020f690041f920083fea9885fd5310ff2a6217e54c43faa9885f55310fe2a6217c54c43fea7885fd4f10ff29e217e53c43faa7885f54f10fe29e217c53c43fe87887f90f10fea1e21fc43c43fea5885fd4b10ff296217e52c43faa5885f54b10fe296217c52c43fe85887f90b10fea1621fc42c43fe65887f8cb10fe99621fc32c43fe83887f90710fea0e21fc41c43fe63887f8c710fb18e21fd31c43ea63887f0c710ff90e21fe21c43fa43887f08710ffa0621fe40c43fa81887f10310ff98621fe30c43fa61887f0c310ff90621fe20c43fa41887f08310ffaa4217f54843fca9085f95210feaa4217d54843f8a9085f15210ffa9c217f53843fca7085f94e10fea9c217d53843f8a7085f14e10ffa1c21fe43843fa87087f10e10ffa94217f52843fca5085f94a10fea94217d52843f8a5085f14a10ffa1421fe42843fa85087f10a10ff99421fe32843fa65087f0ca10bea8c21ff41843ee83087f90610fea0c21fc41843e883087fcc610ff18c21fd31843f863087fc8610ff10c21fd21843f843085f94210ffa0421fe40843fa81087f10210ff98421fe30843fa61087f0c210ff90421fe20843fa41087f08210ff88421f710843f621087fd5110bfaa221bf544427ea8887f95110bf2a221fd54442faa8887f15110be2a221bc5444278a8887fd4d10bfa9a21df53442bea6887f94d10bf29a21fd53442faa6887f14d10be29a21dc53442b8a6887fd0d10ff21a21fd43443f886887fd4910bfa9221ef52442dea4887f94910bf29221fd52442faa4887f14910be29221ec52442d8a4887fd0910ff21221fd42443f884887fcc910ff19221fd32443f864887fd0510ff20a21fd41443f882887fcc510ff18a21f631443fa62887d4c510fe18a21ff21443fc42887f48510fe10a21ff40443fc80887f50110fe20221ff30443fc60887f4c110fe18221ff20443fc40887f48110fe10221ff10443f620887f84110fb08221ff54042fea8087f95010bf2a021fd54042faa8087f15010be2a021ff53042fea6087f94c10bf29821de53042bca6087f54c10bea9821dd53042baa6087f14c10be29821ff43043fc86087f50c10fe21821ff52042fea4087f94810bf29021fd52042faa4087f14810be29021ff42043fc84087f50810fe21021ff32043fc64087f4c810fe190217e51043fe82087dd0410ff20821fd41043f882087d10410ff98821fe31043fa62087f0c410ff90821fe21043fa42087f08410bf28021ff40043fc80087f50010fe20021ff30043fc60087f4c010fe18021ff20043fc40087f48010fe10021ff10043ee20087f84010fd08021fd10043ea20087e44010
  | 1 => 0xf304c3f660987f8c130ef18261ff540c2fea8187f95030bf2a061fd540c2faa8187f15030be2a0617e530c3fe861877d0c30ff21861fd430c3f886187710c30ffa9061fe520c2fca4187f54830bea9061fc520c3fe84187f90830fea1061fc420c3fe641877cc830ff19061fd320c3ba64187f0c830ffa8861fe510c2fca2187d94430bb28861fd510c2faa2187d54430baa8861fc510c3fe82187f90430fea0861fc410c3fe62187f8c430ef18861fd310c3f86218770c430ff90861fe210c3fa42187f08430bf28061ff400c3fc80187f50030fe20061ff300c3be60187f8c030fd18061fd300c3ba60187e4c030ffaa6417f54c83fca9905f95320feaa6417d54c83f8a9905f15320ffa9e417f53c83fca7905f94f20ef29e415e53c83faa7905f54f20eea9e415d53c83f8a7905f14f20ffa1e41fe43c83fa87907f10f20ffa1641fe42c83fa85907f10b20ff99641fe32c83fa65907f0cb20ffa8e41fe51c82fca3907f54720bea8e41fc51c83fe83907f90720fea0e41fc41c83fe63907f8c720fe98e41fc31c83fe43907f88720fe90e41fc21c83fe81907ed0320ff20641fd40c83f881907e10320ff98641fe30c83fa61907f0c320ffaa4417f54883fca9105f95220feaa4417d54883f8a9105f15220ffa9c417f53883fca7105f94e20fea9c417d53883f8a7105f14e20ffa1c41fe43883fa87107f10e20bea9441ff42883de85107f90a20fea1441fc42883d885107fcca20ff19441ee32883fa65107b4ca20fe19441ff51883fca3105f94620fea8c417d51883f8a3107fd0620ff20c41fd41883f883107fcc620ff18c41fd31883f863107fc8620ff10c41ee21883fa43107f08620f610c417e50883fe81107f90220fea0441fc40883fe61107f8c220fe98441fc30883fe41107bc8220fd90441ff54482fea8907f95120bf2a241fd54482faa8907f15120be2a241ff53482fea6907f94d20bf29a41fd53482faa6907f14d20be29a41ff43483fc86907f50d20fe21a41ff42483fc84907f50920fe21241ff32483fc64907f4c920fe19241ff51482fea2907f94520fea8a41fc51482f8a2907fd0520ff20a41fd41483f882907fcc520ff18a41fd31483f862907fc8520ff10a41fd21483f842907fd0120ff20241fd40483f880907fcc120ff18241fd30483f860907fc8120fd90241fe20483dc40907fd5020bfaa041fe54082fca8107f55020beaa041fc54082f8a8107fd4c20bfa9841fe53082fca6107f54c20bea9841fc53082f8a6107fd0c20ff21841fd43083f886105f94820ffa1041ef42083fc84107f50820fe21041ec42083fe64107f8c820f719041fd32083da64107f0c820ffa8841fe51082fca2107f54420bea8841fc51083fe82107f90420fea0841fc41083fe62107f8c420fe98841fc31083fe42107f88420f710
  | 2 => 0x3f885207fcca40ff19481fd32903f865207fd4640ff28c817e51903faa3205f54640fe28c81ff41903fc83206f90640fea0c81fc419037883207fcc640ff18c81fd31903f863207fc8640ff10c81fd21903f843205f94240ffa0481bf40903f681207fd4d40bfa9a81df53502bea6a07f94d40fea9a81fc53502f8a6a07714d40ae29a81ff43503fc86a07f50d40fe21a81ff52502fea4a07bd4940b7a9281fe52503faa4a07f14940be29281ec52502d8a4a07fd0940ff21281fd42503f884a07fcc940ff19281fd32503f864a07fd4540bfa8a81f751502eea2a07f94540fea8a81fc51502f8a2a07d14540ba28a81ff41503fc82a07f50540fe20a81ff31503fc62a07f4c540fe18a81ff21503fc42a07f48540fe10a81ff40503f680a07f90140df202817e54103fea6207f94c40bf29881fd53102faa6207f14c40ffa1881fe43103fa86207f10c40ffa9081fe52102fca4207f54840bea9081fc52103fe84207f90840fea1081fc42103fe64207f8c840fe99081fc32103fea2207f94440bf28881fd51102faa2207f14440ffa0881fe411037c82207f50440fe20881bc41103fe62207f8c440fe98881fc31103fe42207f88440fe90881fc21102fca0207fd0040dfa0081fe40103f480207f50040dea0081f940103fea9985fd5330ff2a6617e54cc3faa9985f55330fe2a6617c54cc3fe87987f90f30fea1e61fc43cc3fea5987f94b30bf29661ee52cc2dca5987f54b30bea9661ed52cc2daa5987f14b30ffa1661fe42cc3fa85987f10b30ff99661fe32cc3fa65987f0cb30ffa8e61fe51cc2fca3987f54730bea8e61fc51cc3fe83987f90730fea0e61fc41cc3fe639877cc730ff18e61fd31cc3ba63987f0c730ff90e61fe21cc3fa43987f08730ffa0661fe40cc3fa81987f10330ffaa4617f548c3fca9185f95230feaa4617d548c3f8a9185f15230bea9c61ff438c3be87187f90e30fea1c61fc438c3b887187fd4a30ff294617e528c3faa5185f54a30fe29461ff428c3fc85187f50a30fe21461ff328c3be65187f8ca30fe99461dd328c3f865187fd4630ff28c617e518c3faa3185f54630fe28c61ff418c3fc83187f50630fe20c61ff318c3fc6318778c630fe98c61fc318c3b863187fc8630ff10c61fd218c3f843185f94230ffa0461fe408c3fa81187f10230ff98461df308c3f661187fd5130bfaa261fe544c2fca8987f55130beaa261fc544c2f8a8987fd0d30ff21a61fd434c3f886987fd4930bfa9261fe524c3faa4987f14930be29261ff424c3fc84987f50930fe21261ff324c3fc64987f4c930fe19261ff514c2fea2987f94530fea8a61fc514c2f8a2987fd0530ff20a61fd414c3f882987fcc530ef98a61fe314c3fa6298774c530fe18a61ff214c3fc42987f48530fe10a61ff404c3fc80987f50130fe20261f
  | 3 => 0xa098ff14131be28263ff540c6fea818ff95031bf2a063fd540c6faa818ff15031be2a0637e530c7fe8618ff90c31fea1863fc430c7fea418ff94831bf29063fd520c6faa418ff14831ffa1063fe420c7fa8418ff10831ff99063fe320c7fa6418ff0c831bf28863ff410c7fc8218ff50431fe20863ff310c7be6218ff8c431fb18863fd310c7ba6218fd4c431ffa8063fe500c6fca018ff54031bea8063fc500c7fea990dfd5321ff2a6437e54c87faa990df55321fe2a6437c54c87fea790dfd4f21ff29e437e53c87faa790df54f21fe29e437c53c87fe8790ff90f21fea1e43fc43c87fe8590ff90b21fea1643fc42c87fe6590ff8cb21fe99643fc32c87fe8390fdd0721ff20e43fd41c87f88390fd10721ff98e43fe31c87fa6390ff0c721ffa8643fe50c86fca190ff54321bea8643fc50c87fea910dfd5221ff2a4437e54887faa910df55221fe2a4437c54887fea710dfd4e21ff29c437e53887faa710df54e21fe29c437c53887fe8710ff90e21fea1c43fc43886faa510ffd0a21ff21443fd42887f88510ffcca21ff19443fd32887f86510df94621ffa0c43fe41887fa8310ff10621ff98c43fe31887fa6310ff0c621ff90c43ef21887ee4310ffd4221ff284437e50887faa110df54221fe28443ff54486fea890ff95121bf2a243fd54486faa890ff15121be2a243ff53486fea690ff94d21bf29a43fd53486faa690ff14d21be29a43ff43487fc8690ff50d21fe21a43ff42487fc8490ff50921fe21243ff32487fc6490ff4c921fe19243ff41487fc8290ff50521fe20a43ff31487fc6290ff4c521fe18a43ff21487ee4290ff88521f710a43ff50486fea090ff94121fea8243fc50486f8a090ffd5021bfaa043fe54086fca810ff55021beaa043fc54086f8a810ffd4c21bfa9843fe53086fca610f794c21af29843fd53086faa610f754c21aea9843fc53086f8a610ffd0c21ff21843fd43087f88610df94821ffa1043fe42087fa8410ff10821ff99043fe32087fa6410ff0c821bf28843ff41087ee8210ff90421fea0843fc41087e88210ffcc421ff18843fd31087f86210ffc8421f790843fe21087ec4210ff48421f690843f521087fea010ff94021bf28043fd50086faa010ff14021ffa9e81fe53d02fca7a07f54f40bea9e81fc53d03fe87a07f90f40fea1e81fc43d03fea5a07f94b40bf29681fd52d02faa5a07f14b40ffa1681fe42d03fa85a07f10b40ff99681fe32d03fa65a07f0cb40ffa8e81fe51d02fca3a07f54740bea8e81fc51d03fe83a07f90740fea0e81fc41d03fe63a07f8c740fe98e81fc31d03fe43a07f88740fe90e81fc21d02faa9207fd4e40ff29c817e53903faa7205f54e40fe29c81ff43903fc87207f50e40fe21c81ff52903fca5205f94a40fea94817d52903f8a5207fd0a40ff21481fd429
  | 4 => 0x7f55032beaa065fc540caf8a8195f94c32ffa1865df430cbfc86197f50c32fe21865dc430cafca4197fd0832ff21065fd420cbf884197fcc832ef99065fe320cbdc64197f4c832ee99065ed320cbfea2197f94432bf28865fd510cafaa2197f14432ffa8065fe500cafca0197f54032bea8065fc500cbfea7a0ff94f41bf29e83fd53d06faa7a0ff14f41ffa1e83fe43d07fa87a0ff10f41ffa9683fe52d06fca5a0ff54b41bea9683fc52d07fe85a0ff90b41fea1683fc42d07fe65a0ff8cb41fe99683fc32d07fea1a0ff94341bf28683fd50d06faa1a0ff14341beaa483ff53907fca720df94e41ef29c835e53907faa720df54e41eea9c835d53907f8a720ffd0e41ff21c83fd43907f88720ffd4a41ff294837e52907faa520df54a41fe29483ff42907fc8520ff50a41fe21483ff32907fc6520ff4ca41fe194837e51907fe8320efd0641fba0c83ff50907fca120df94241fea84837d50907f8a120ffd4d41bfa9a83fe53507faa6a0ff14d41be29a83ff43507fc86a0ff50d41fe21a83ff52506fea4a0ff94941fea9283fc52506f8a4a0ffd0941ff21283fd42507f884a0ffcc941ff19283fd32507f864a0ffd0541fba0a83fe415077c82a0ffd4141bfa8283fe50507faa0a0ff14141be282837e54107fea620ff94c41bf29883fd53106faa620ff14c41ffa1883fe43107fa8620ff10c41ffa9083fe52106fca420ff54841bea9083fc52107fe8420ff90841fea1083fc42107fe6420ff8c841fe99083fc32106fca220ffd0441dfa0883fe41107ec8220ff50441dea0883f541107fea020ff94041bf28083fd50106faa020ff14041ffaa6637f54cc7fca998df95331feaa6637d54cc7f8a998df15331ffa1e63df43cc7fc8798ff50f31fe21e63dc43cc7fea598ff94b31bf29663fd52cc6faa598ff14b31ffa1663fe42cc7fa8598ff10b31ff99663df32cc7fc6598ff4cb31ee99663fc32cc7fe8398ff90731fea0e63fc41cc7fea198ff94331bf28663fd50cc6faa198ff14331ffaa4637f548c7fca918df95231feaa4637d548c7f8a918df15231bea9c63ff438c7fc8718ff50e31fe21c63ff528c7fca518df94a31fea94637d528c7f8a518ffd0a31ff21463fd428c7f88518ffcca31ff19463fd328c7f86518df94631ffa0c63f7418c7fc8318ff50631fe20c63f4418c7fe6318f7cc631fb98c63ff508c7fca118df94231fea84637d508c7f8a118ffd5131bfaa263fe544c6fca898ff55131beaa263fc544c6f8a898ffd0d31efa1a63fe434c7fa8698ff10d31ee21a63ff524c6fea498ff94931fea9263fc524c6f8a498ffd0931ff21263fd424c7f88498ffcc931ef99263fe324c7fa6498f74c931fe19263ff414c7ee8298ff90531fea0a63fc414c7e88298ffcc531fb98a63fe314c7bc6298ffd4131bfa8263fe504c7fa
  | 5 => 0xa43ff294877e5290ffaa521df54a43fe29487ff5190ffca321df94643fb28c87765190ffaa321df54643faa8c87755190ff8a321ffd4243ff284877e5090ffaa121df54243fe28487ff4350fbe86a1ff90d43df21a87ff5250efea4a1ff94943fea9287fc5250ef8a4a1ffd4543bfa8a87fe5150ffaa2a1ff14543be28a87ff5050efea0a1ff94143fea8287fc5050ef8a0a1df95043bf29887ff4310f7e8621ff90c43ef21887fd4310f7a8621f750c43ffa9087fe5210efca421fb94843b729087fd5210efaa421fb54843b6a9087fc5210ffea221ff94443bf28887fd5110efaa221ff14443ffa8087fe5010efca021ff54043bea8087fc5010ffea7a17f94f42bf29e85fd53d0afaa7a17f14f42ffa1e85fe43d0bfa87a17f10f42ffa8e85fe51d0afca3a17f54742bea8e85fc51d0bfea1a17f94342bf28685fd50d0afaa1a17f14342beaa485ff5390bfca7215f94e42fea9c857d5390bf8a7217fd0e42ff21c85fd4390bf887215f94a42ffa1485bf4290bde85217fd4642ff28c857e5190bfaa3215f54642fe28c85ff5090bfca1215f94242fea84857d5090bf8a1217fd4d42bfa9a85df5350abea6a17f94d42fea9a85fc5350af8a6a17714d42ae29a85ff4350bfc86a17f50d42fe21a85ff4250bde84a17f90942df21285ff5150afea2a17dd4542bba8a85fe5150bfaa2a17f14542be28a85f45150ae8a2a17fd4142bfa8285fb5050af6a0a17f94142fea8285fc5050af8a0a17e14142bc282857e5410bfea6217f94c42bf29885de5310abca6217f54c42bea9885dd5310abaa6217f14c42ffa1885fe4310bfa86217f10c42bf29085ff4210b7e84217f90842f721085fd4210b7a84217b50842ffa8885fe5110afca2217f54442bea8885fc5110bfea0217f94042bf28085fd5010afaa0217f14042ffaa6657f54ccbfca9995f95332feaa6657d54ccbf8a9995f15332ffa1e65fe43ccbbc87997f50f32eea1e65fc43ccbfe85997f90b32fea1665fc42ccbfea3997f94732bf28e65fd51ccafaa3997f14732ffa8665fe50ccafca1997f54332bea8665fc50ccbfea9195fd5232ff2a4657e548cbfaa9195f55232fe2a4657c548cafaa7197fd0e32efa1c65fe438cbfa87197f10e32ee21c657e528cbfe85197f90a32f721465fd428cbda85197f10a32ff99465df328cbde65197fd4632ff28c657e518cbfaa3195f54632fe28c65ff508cbfca1195f94232fea84657d508cbf8a1197fd5132bfaa265fe544cafca8997f55132beaa265fc544caf8a8997fd0d32ff21a65de434cbfa86997750d32fe21a65ff424cbfc84997b90932fea1265ed424cbf884997fcc932f799265fe324cbbc64997fd4532bfa8a65fe514cbfaa2997f14532be28a65ff504cafea0997f94132fea8265fc504caf8a0997fd5032bfaa065fe540cafca819
  | 6 => 0x623d6c6452eb766f200017650604e1a6d80910b1200000000200000500000000000201400b00000701a00300000100700100300300600200100100400002900001200b00200500300700701101700400000100100d00400000300300000400000400400400900400200000300301000500700000200000600100200000200200000400d00000004c00000c00800100600002600000200e00001f00000401900000800301e00101000000200301600000700000300e00100200700000201300000000400000000000a00a00100b00900800100000e01200900000901600d00000000000900400400100900400400400000200700100000000100700001700100000000000000900000100600600000000500100000700700600900000000000a00000000100400000000200100200001500100000500200000900200400400000e00504c00100200000d00200001100000300d00100600000100000700200000000600700100000000500100200603200000100000400000500000100100a00001600000000000000000100000000100400200100100000000801800500000201700100200500900000600d01000e00900000500000100000400000000100001000000600300d00700000100300000500001800500100800400000302000a00000100000200000500900700000000800f01e00000500100200400600000500300000501300400000000000100000d00300400100000500000b00500100000000400000400000800100000400600001d00000000300400200300100700400000002001e00b00000300800000200300700100000300c01700200500100000100600200b00100001000000400000000100100200000100300b00300100000100000000000400700500800000600200000200000001800200001a00600100201601700000f00000200202800900400000000700000700400000200b00200200300100500900000000900600900000000000c00000100200700800100200a00000100c00700d00000a00600300e00800001d02c00200000001100000900000c00f00701000000700000100100501900900b00004b00200100500700200200000a00200300d00600d01500000300200100b01600000900b00100400500000100000000000300200000000200001600100f00800000200801000501301400600401700000101101c00000200500100200000200001700b00100000b00d00000b00200000300000000000400b00001800200300200100400100001000001300303901601500000000600000b00300100100a007000ffa9687fe52d0efca5a1ff54b43bea9687fc52d0ffea3a1ff94743bf28e87fd51d0efaa3a1ff14743ffa8687fe50d0efca1a1ff54343bea8687fc50d0efaa921df94e43ffa1c87bf4390fbe8721ffd4
  | 7 => 0x445cb8866a0d24b0c8269803c00000000000a0000001c000031c00000000047eb7c0005f259c000aec3120823f227000088a34442a70c0000002dc28a0000000009387f6a0e140000d785be000000000000000c140000000000007de0000005d000050a62ea36000d8a23a000a507a091e03a49847c000b0ad1ed640006bab7e9bebf29a40f47f2ddae38bf87842247a804a372580612de000c5bc1a264a936000000d8e534672cea2e0c2494229ace4b36524630e1060841e60a008d820009441d86dc000d6058c000a443c2cf869c3c8712beabcec7ca1e0fe00000097a740cc2cbe108b2a15a9e4a340b87c20487ea2c45acc904309ac12c8660001dea42bd60587b0da8ba60ea0001e29e8bba2140008728a0538b528148186b25ea0006bcdaeda458a2f0b9600016000043e0004dcd6a2ae0000006b800064cb46bd81b0ba837c326b9835005a42e07a9e6d48a20daa654d707565500bcc2e34096aa5c30c9b0a400006a0e5c0002d47c4cdca7c0e8000000d6200011e54cce6378aaad9c9f67108aea168b21e067626e61c4da2f8914696cf2cb62c8d0487631e4f20a2e3e01eb3c512a6a3ac7d67325d26fac9815e73c1c28445e0754a6c3a46ec000c30e12996000aaecf656c00060252ad7e1420f642076c0d01ce0002ca000000356cc80009f40000005d83cc000000836b24000000000e5e00026c95214e0000003bcca8dcc76aa0a4f0000ca2afe47a1b80000e06228862886f00000000b075e00000027c5de0000007ee8fad7680eb5a448000000000dd4e44000000600138000000000000d7c0a4000ae600043889800000000000067a010408bcc79c180000000c808ec5fe396284bbc3488ca870e300000000008c60000000003d0b9e10a2e20020a6a80274104000ad0dce7e69d4b3ab86ac29bc424504620c94d02820cb47a65922f2d8c384704aa0c28a060280001a85aa4e4b4e0000000004a40004be9aa01ac502e87e26500000004aa67044c5fc0001f8610664000b6c7b2abc720d960006cce5a0000000802a6782000d7453c00000017c2c20005c8000de4000004a3e9c8ba00003c6af8992908ce29168d2252cd44067b87ae8162ba6aa3ea9b4764e0624c574000e34c0aa8aa2a0be000000000204544000000d2a000000c96000000000e3a83802c000000e183f82e6398000ae0000ad435c44234ed4e0004a2000972a52e48b30084c54a74ab26b46605948782cc0c4000cc60c820e000e321983ae0e4c5a2b8000000000918e660000000009944840002d81927b6000184000000000000000000e003a600087e874b06b2277acb0db68eea8c5424c6a9ac465dcd5cdc29a82285a24185f068096606c9cc73add02381e84b8022af66480c6c6821ec120009201f20f2abeac80007440001683548c4000522780386b148cc9
  | 8 => 0xad22faac664493492e0b64928cee40434000000e08000000000cbc97e6bee2a0aa000000000000240000444000000000000a9eb4c6943880006360006d4840b8a0009d01fc7acbc6c5e000be89de0003e8c4c0000000001f6000b3e0000005360340006c45b6000000000df800000017a132b70242aa6b8ec78000c8a31486854e000e589300182d6c9cd12c0666600082a7f82b4df246cdb8000000834dc40ba024d86d5e000306d08db0cf08f6182000de24ce5b474c6aea1c61ebda45080c6de8fcd464a8e2e4d836c9e200000086e6eab567e07f400000e0000005840001aa3fc0005cc0001c6ce050072252cb16000cfa0002f618c392dc6264000c1a0008debaa000000566bdc8ea1463ee7d0e52ada00000064600058ed14752dd8b1cb040b20943b0cfe090488b827eca2610083ec40000af00003280003660004ae5ca000000bb60000000004ec000000000380000000bc2518b08044000d9226a20612e79007400027a2e40dad186c8a948a20006eec88c70026b1a0004d4000c38000320000000bb4b6a45662a51c00085ae620008f41ec0004020520c04320ec99875070e802932000892552796d06000c62428b2c230170d987b4c6c56e0564ba68ac92bb04c439e390d526a8a080003b694c19aacc22c6e4bc46d053eab85988062683e0afa63a9ce49c186120a68a86d1c22aac08283f6000000244000e1c3a8b10734060000000294c6a000000000b7ab808c0308a4cd16b9a0c2810e02000000dee32a852c9a578336c6625400071a1b60008bc460cde76623e41c8d80008fe6da482cec978ab4568b9c27832eb8cc4a7d22104e2d908dcad6826b0287a0686c66e8c5cb900007240f89e00007f06c0ca4d3685ea048322ac9fe1d2194d385820004d6a1ae2095e78c400c3e2d02f469a762000000000cc4cc063c7fa15436ea6018a00036442c03e000dc052085c000000000d5add604c3702b6c164fabe6c048300009240dc8da0003e40007e837494693a49ad88000ad809a00049400000073e0007741d60008e80006f49c0d1a0000007e4d6c2228a83b20005a069e16a0006b6894000e1ecee000158362000ce85260009a200038e000df437eae8a3829210c6e0000688e56a460001bcbf4d9ade600095a000a10000d54cb81220000008e6bd2000a9085400006600000000013c3deb680002fe0aca32000624e60000000bf019c1ea65cdb4cba888cac9da77edea576c1eb5450c95caa237a68671c446e222be616bae00016c000bd45a4b4ad2c860000a7800045e9ea000c52786bb21fa1ca6a6b0cdfc7c83dc07e0009f821a0000000000000003aaa5eb66ccc00055a17e0005964de16e00000020a14a0003f40004f41be00075800029c000af44808120005c00381ae00020297686c7007a461a76e7c6d7a13ec0c000bac6a
  | 9 => 0xe022e26641ab846280001a0476a2e472590bfe7780d89fc82ca8e0000000000008005b25e8884000000150000000d34dbc0004f80002c600000000072aaea738d22d940001100000006ca00089092a7da83c9f0db23585c4760c84d1000000000067857c000000046772626000c34000cca404d507a20007083ce9d6412076000000640d72e0cd4a7308e225e06e1c84fe9405e6000000974a2c0009648642904e649e0000000faaa40e21488a60000005ae0000000000000000009a62ec000000acacda0008f267c5c2000000d0a44a368a544bc43ab40000a3c70263e00027ec9e718a7678e89c3d2000c8c968a28c2c0007ba436a2400000059e5160000000000000000003a000038cb264ea0000003467be9820000009c293e84c000b60064a7ab482ea51a90e0000005484b29f2d320004d065600024806a33a000466000302b721ba586b9244e00068c02a000000d2000064e86ad4000066268e000000d0e28cbfa96013a72c66c5622a872e0cc9ba3e2dfa81eddc7bce4a0000000004ee8b45f648c33c6b019e60648a55454609646a4167cc3001d0b742bc152a5a27634c8820003fecd8768560a621c41269a00401160000002aa3c400046202e8240009908b85b03e600024a0000007cad304901440ca97c000000804da6000280846692000c7e0006d20008d008e09277c0d6c205d409c0000005f457a1304a600001240ec2655e798440000000000d2832c8806c20985085e4a7e808cceda00000001d4970072da2e0a88e0008d635aa123b808c000c7ab34042000000000afc0008226fe000470502a180d4caa2d290011a50ee0ed3e15600033051e93c0000000009b8000cd6b284c8788054000000360ae2000c8ec36e3ce54980000020316234000000746b50088e2488c000abaa586fc0ee000ace9ec614a82ab694ebbe67ea0cdac000014000a3a5e20005280005ee8d4000c6000000022629e000716d581cc2129dcb4400005e00000068425c000000d2e3d4a9c0004744cc5ce7fc3321964e8dcaa4e3a214c000e64c4835e7281f40169588c2d000aed3c5b884874a98a000000000000000000d26000e42000e28178dd2000714c183da4529ee33e38a00000098e0000008be0001da0000000005c600000061800026221634a0009d84e000000060e6d69220002ce000338112322c02000bec46445a2daa72000bc8a00000de8000000000a9257000000099e68275a21cd660007aabd02a40001a423cca0690b4283a6ceb1e00099c4fc1b298c000794030000c2ae264c0c745ec3d807853263255caac67410e80a272b32bde1dc776b000a0bb807015cb6265e66ed846e2a303ba0368a400060c000c3200099a000ae48aa72690212400000000039c000be2296d3a7fe3ca458cd2cfcbe04680002de0000008f09b63b44b491c24e
  | 10 => 0xb6e00000031adc88c80a890400028625adde06287cc7624684eb5cb202c070a4541b45da948c00e36e14410556106d4ca660b479e6f80005a689a000188422000df0000ab00000000009d24cac3cb2e9aed6ee1a928000000342df6a48d2412ac58bcae2c20c53a6ac05c856a0228274807c09e90a6d882eb1830a118e0412892665aa84000190000b380000008b6000be43fa8ac0008b00009861fe3180009c6d563827d89b2a14032b585ba6f6aa896c260000220000bee58800040ac0e0000000e68e4e4e00000000062cc4e7d473664292c00000048600051096ed424c2ca656acb28ba4a02a20002565d69fa00000000000059a75cc086e6dba334a5678a42600000000000000091aa88000c8600039a6344f600011c988376ade08a5407703beac4b940000001e61620de000000c1031048ee16b5ee4c7928500008422a000000025013481a000a6e000050166414954896aee0000000f0000000b64cf474243c9ca5fa4b694ac44324658218ba218e0866041e428e3ec0007dc2ee706a22adc304912d441aca98208dfe006858000862298000dec000638000bc090657e9c4b789841646a2200c1c1f0ba40000003c046e90c0000008f8dbe000000956a6454ac72a4a40c4d21747ce81c1361023f05305f874e236c427c0000c56c3abf65140fc01ca9657236ae46558e504acd682b2cae668a7071e564394d0cbfc49630e0003526521ee47879a232b0e5a8114c6ec22000d9e2fc2b095084a000000000af20ce89ecd01722588
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x41042f56010410fc58041042f160104109f597310435e53cc410d754f310427f658c4109f596310435e538c410d754e3104376518c410be98231042f9608c4109fd95310435e534c410d754d3104376514c4109fd94310427d650c410d794c310435d530c410be98031042f9600c4109f597210435e53c8410d754f210427f65884109f596210435e5388410d754e210436e5288410db54a21042fa6088410be582210427f6548410d794d210435d53484109fd94210427d6508410b798c21042dd6308410d794c210435d5308410db948210436d5208410be98021042f960084109f992500427d64940109f98e500427d63940109f98a500427d62940109f58650043774194010dd106500427d65d0010d794f400435d53d00109fd96400427d6590010cf952400433d5490010d794e400435d5390010bd98640042f56190010ed106400427f6550010b7d8d40042dc6350010d794d400435d5350010bbd8940042ec6250010bdd8540042f461500109fd94400427e65100109f594400427c6510010cf950400433d5410010d794c400435d5310010bd98440042f56110010ed104400427d65cc010d794f300435d53cc010bb98b30042ed62cc0109fd96300427d658c010d794e300435d538c010bd98630042f5618c0109fd95300435e534c010d754d300427f650c0109f994300427d650c0109f194300435e530c010d754c30042f6610c010bd584300427d65c8010b798f20042dd63c8010d794f200435d53c80109fd96200427d6588010d794e200435d5388010db94a200436d5288010bd98620042f561880109fd95200435e5348010d754d200427f65080109f994200427d65080109f194200435e5308010d754c200436e5208010db54820042f66108010bd584200435e53c4010d754f100437565c4010bd99310042f464c4010ddd4f10043d653c4010dd54f10043d553c4010d554f100435e5384010d754e10042f56184010dd94610042f96584010de59610042796584010f694e10043d95384010be586100437a5184010fc94610043f34184010fc106100427f6544010afd9110042bc6444010b7d8d10042dc6344010d794d100435d5344010bbd8910042ec6244010bdd95100437765440109dd9510043b76444010bd99110042f46444010ed19110042b46444010f5d8d10043d46344010ddd4d10043d65344010dd54d10043d55344010d554d10043e76244010f918910042f76044010dd94110043f24044010fc50110043f33044010fc0c110043f32044010fc08110042fb6544010ded95100427b6544010eed9110043b86444010f6d8d10043d86344010f694d10043d95344010fad8910043e86244010bed8510043f36144010de94510043f25144010fc90510043f14144010fccc510043f03144010fcc8510043f02144010
  | 1 => 0x427f6590c109f996430427d6590c109f196430435e5390c10d754e43042f66190c10bd586430427f6550c109f995430427d6550c109f195430435e5350c10d754d43042f76150c10bd18543042fb6050c10be181430427f6510c109f994430427d6510c109f194430435e5310c10d754c43042ee6210c10bb58843042de63d4810b758f520435e53d4810d754f520427e64d48109f593520427e63d4810d798f520425e63d48109f58f520435d63d48109758f520427e61d4810dd987520427e60d4810de983520427d6594810d794e520435d5394810dbd4a520427e64948109f592520427e63948109f58e520435e5354810d754d520427f64548109f191520427f63548109f18d520436f62548109fd85520427d61548109fd81520427d6054810af99052042bd6414810b798c52042dd6314810d794c520435d5314810db548520427e6414810cf990520423e64148109f590520433d64148108f590520427e6314810d798c520425e63148109f58c520435d63148109758c520427e6214810db988520427e6114810dd984520427e6014810de980520427f65d08109f997420427d65d08109f197420433e54d0810cf553420435e53d0810d754f420427f65908109f996420427d65908109f196420435e5390810d754e420436e5290810db54a42042f66190810bd586420427f65508109f995420427d65508109f195420433e5450810cf55142042df6350810b718d420435e5350810d754d420436e5250810db54942042f76150810bd18542042fb6050810be181420427f65108109f994420427d65108109f19442042de6310810b758c420435e5310810d754c420427f65cc8109f997320427d65cc8109f197320435e53cc810d754f320427f658c8109f996320427d658c8109f196320435e538c810d754e320427f654c8109f995320427d654c8109f195320435e534c810d754d32042f7614c810bd18532042fb604c810be181320427f650c8109f994320427d650c8109f194320435e530c810d754c320427e64944109f592510427e63944109f58e510427e62944109f58a510427d65d0410d794f410435d53d0410bd597410437565d0410ddd53410437554d0410ddd4f41043d653d0410dd54f41043d553d0410d554f410437652d0410dd14b41042f560d04109fd96410427d6590410cf952410433d5490410b798e41042dd6390410d794e410435d5390410bd98641042fa6090410be582410427f6550410d794d410435d53504109fd94410427d6510410cf950410433d5410410d794c410435d5310410ed50441042fa6010410be580410437565104109d59441042f66410410ed99041043775410410ed95041043755410410ed55041043775310410f594c41043755310410f554c41043555310410dd94841043745210410fc98
  | 2 => 0x534c110dbd49304436c524c110bdd8530442f4614c110f54c5304427e650c110cfd50304433c540c110d7d4c304435c530c110dbd48304436c520c110bd98430442f5610c110f58c4304427e65c8110cfd53204433c54c8110b798f20442dd63c8110d7d4f204435c53c8110dbd4b204436c52c8110bd98720442f561c81109f996204433f5488110cf152204435f5388110d714e204436f5288110db14a204427f65481109f595204427c6548110cfd51204433c5448110d7d4d204435c5348110dbd49204436c5248110bdd8520442f461481109f994204433f5408110cf150204435f5308110d714c204436f5208110db14820443e92008110cfd53104433c54c4110d7d4f104435c53c4110dbd4b104436c52c4110eed5310443b854c4110f6d4f10443d853c4110fad4b10443e852c4110fc8c710443f131c4110cfd52104433c5484110d7d4e104435c5384110dbd4a104436c5284110edd5210443765484110dd15210443b45484110cd15210442f76384110bd58e10443d75384110f514e10443e75284110f914a10443f35084110b798f54042dd63d50109f98f540435e63d50109798f540427d63d5010d758f540425d63d50109f98b540427d62d50109f987540437661d50109f983540437a60d50109f596540433f54950109f98e540427d63950109f98a540427d6295010cfd91540427f63550109f18d540427f62550109f189540427f61550109f585540437461550109fd81540427d6055010cf55054042de6315010b758c54042ee6215010bb588540427e6415010cf990540427e6315010d798c540425e63150109f58c540435d63150109758c540427e6215010db988540426e62150109f588540436d62150109b588540427e6115010dd984540427e6015010de980540427e64d4c109f593530427e62d4c109f58b530427e61d4c10dd987530427e60d4c10de983530427d6594c10d7d4e530427e6494c109f592530427e6294c109f58a530425d6594c10d7d52530435e5494c10d7552530435c5494c10d7d92530435e6494c10d7592530435c6494c10d7d8a530435e6294c10d758a530435c6294c10d7986530435c6194c10d7982530435c6094c109fd91530427c6454c10d7d8d530427f6254c109f189530427f6154c109f585530427f6054c109f581530435f6554c10d7d51530435e5454c10d7551530435c5454c10d7d91530435e6454c10d7591530435c6454c10d7d89530435e6254c10d7589530435c6254c10d7985530435c6154c10d7981530435c6054c10d704153042de6314c10d754c530427e6414c109f590530427e6314c10d798c530425e6314c109f988530427d6214c109f98453043766114c109d984530427e6014c10de980530427f65d0c109f997430427d65d0c109f197430435e53d0c10d754f430
  | 3 => 0x9109f994324427d650c9109f194324433f540c910cf150324435f530c910d714c324436f520c910db14832442f6610c910bd584324427e65d0510cfd53414433c54d0510d7d4f414435c53d0510dbd4b414436c52d0510be98341442f960d05109f996414433f5490510cf15241442de6390510b758e414435f5390510d714e414436f5290510db14a414427c6550510cfd51414433c5450510d7d4d414435c5350510dbd49414436c5250510bed8141442f860505109f994414433f5410510cf150414435f5310510d714c414436f5210510db148414427e65cc510cfd53314433c54cc510d7d4f314435c53cc510dbd4b314436c52cc510be98331442f960cc5109f996314433f548c510cf152314435f538c510d714e314436f528c510db14a31442f6658c510dd99631443b7548c510dd9523144374548c510ed1523144334548c510bd58e31443d7538c510dd94e3144374538c510f514e3144354538c510f9d4a31443e4528c510bd982314427c654c510cfd51314433c544c510d7d4d314435c534c510dbd49314436c524c510bed8131442f8604c510dd1953144274654c510edd513144376544c510dd15131443b4544c510cd15131443d7634c510f5d4d3144376534c510dd14d31443d4534c510f5d0d31443d4434c510f9d4931443e4524c510f5cc931443d5324c510fcd8131442f4604c510fc18131442f0604c5109f994314433f540c510cf150314435f530c510d714c314436f520c510db14831442f6610c510f54c4314427e65c8510cfd53214433c54c8510d7d4f214435c53c8510dbd4b214436c52c8510be98321442f960c85109f996214433f5488510cf152214435f5388510d714e214436f5288510db14a214427c6548510cfd51214433c5448510d7d4d214435c5348510dbd49214436c5248510bed8121442f860485109f994214433f5408510cf15021442de6308510b758c214435f5308510d714c214436f5208510db148214427e65d0110cfd53404433c54d0110d7d4f404435c53d0110dbd4b404436c52d0110bd98740442f561d01109f996404433f5490110cf152404435f5390110d714e404436f5290110db14a404427f65501109f595404427c6550110cfd51404433c5450110b7d8d40442dc6350110d7d4d404435c5350110bbd8940442ec6250110dbd49404436c5250110bdd8540442f461501109f994404433f5410110cf150404435f5310110d714c404436f5210110db148404427e65cc110cfd53304433c54cc110d7d4f304435c53cc110bb98b30442ed62cc110dbd4b304436c52cc110bd98730442f561cc110f54c7304427e658c110cfd52304433c548c110d7d4e304435c538c110dbd4a304436c528c110f58c6304427f654c1109f595304427c654c110cfd51304433c544c110d7d4d304435c
  | 4 => 0xb153524432c54d4910dbd4f52443cf53d4910d3d4f524436e53d4910db54f524436c53d4910f314f524434c53d4910dbd93524436e64d4910db593524436c64d4910dbd8f524436e63d4910db58f524436c63d4910dbd0f524436e43d4910db50f524436c43d4910dbd87524436d61d4910dbd83524436d60d4910af99252442bd6494910cfd52524433c5494910b798e52442dd6394910d7d4e524435c5394910dbd4a524427e6494910cf992524423e64949109f592524433d64949108f592524427e6394910d798e524425e63949109f58e524435d63949109758e524427e62949109b98a524427d6194910dd586524427d6094910de58252442bf6454910af191524433f5454910cf15152442df6354910b718d524435f5354910d714d524427f6454910cfd91524423f64549109f191524433c64549108f191524427f6354910d7d8d524425f63549109f18d524435c63549109718d524436f62549109fd85524437761549109fd81524437b60549109f994524433f5414910cf150524435f5314910d714c524436d52149109f990524427d64149109f98c524427d6314910db988524427e61149109f184524427e60149109f18052442ee6514910db994524426e6514910dbd5052443af5414910cbd50524436e5414910db550524436c5414910eb150524432c5414910dbd4c52443cf5314910d3d4c524436e5314910db54c524436c5314910f314c524434c5314910dbd90524436e6414910db590524436c6414910dbd8c524436e6314910db58c524436c6314910dbd0c524436e4314910db50c524436c4314910dbd84524436d6114910dbd80524436d6014910db440524427f65d09109f997424427d65d09109f197424433f54d0910cf153424435f53d0910d714f424436f52d0910db14b424427f65909109f996424427d65909109f196424433f5490910cf152424435f5390910d714e424436f5290910db14a424427f65509109f995424427d65509109f195424433f5450910cf15142442df6350910b718d424435f5350910d714d424436f5250910db14942442f76150910bd18542442fb6050910be181424427f65109109f994424427d65109109f194424433f5410910cf15042442de6310910b758c424435f5310910d714c424436f5210910db14842442f66110910bd58442442fa6010910be580424427f65cc9109f997324427d65cc9109f197324433f54cc910cf153324435f53cc910d714f324436f52cc910db14b32442f661cc910bd58732442fa60cc910be583324427f658c9109f996324427d658c9109f196324433f548c910cf152324435f538c910d714e324436f528c910db14a324427f654c9109f995324427d654c9109f195324433f544c910cf151324435f534c910d714d324436f524c910db149324427f650c
  | 5 => 0x54442ec6255110cfd91544427f6355110d7d8d544425f63551109f18d544435c63551109718d544427f6255110dbd89544426f62551109f189544436c62551109b189544427f6155110ddd85544427761551109fd81544437b60551109f994544433d5415110cf990544427e63151109f58c544427e62151109f588544427e61151109f184544427e60151109f18054442be6515110cf994544423e6515110cfd8c544433e6315110cf58c544433c6315110cfd88544433e6215110cf588544433c6215110cfd84544433d6115110cfd80544433d6015110cf440544433f54d4d10cf153534427e64d4d109f593534427e62d4d109f58b534435f54d4d10e7d53534431f54d4d10d7953534435d54d4d10d7153534439c54d4d10c715353443d761d4d10d7d93534435e64d4d10d7593534435c64d4d10d7d8b534435e62d4d10d758b534435c62d4d10d7d87534435d61d4d10d7d83534435d60d4d10af99253442bd6494d10cfd52534433c5494d10d7d4e53442ee6294d10bb58a534427e6494d10cf992534423e6494d109f592534433d6494d108f592534427e6394d109798e534427e6294d10db98a534426e6294d109f58a534436d6294d109b58a534427d6194d10dd586534427d6094d10de58253442bf6454d10af191534433f5454d10cf15153442ef6254d10bb189534427f6454d10cfd91534423f6454d109f191534433c6454d108f191534435f6354d109fd89534436f6254d109bd89534427c6254d10db189534426c6254d109fd8553443776154d109fd81534437b6054d109f994534433f5414d10cf150534435d5314d109f990534427d6414d10d798c534427e6214d109f588534427e6114d10dd584534427c6114d109f980534427c6014d10b7994534435e6514d1097994534435f5414d10e7d50534431f5414d10d7950534435d5414d10d7150534439c5414d10c715053443d56114d10d7d90534435e6414d10d7590534435c6414d10d7d88534435e6214d10d7588534435c6214d10d7d84534435d6114d10d5584534435f6014d10d7580534435d1014d109fd97434427e65d0d109f597434427c65d0d10cfd53434433c54d0d10d7d4f434435c53d0d109fd96434427e6590d109f596434427c6590d10cfd52434433c5490d10d7d4e434435c5390d10bd98643442f56190d109fd95434427e6550d109f595434427c6550d10cfd51434433c5450d10d7d4d434435c5350d109fd94434427e6510d109f594434427c6510d10cfd50434433c5410d10d7d4c434435c5310d10bb98843442ed6210d10bd98443442f56110d10be98043442f96010d10cfd53524433c54d4910d7d4f524435c53d49109f993524427d64d49109f98f524427d63d4910dbd5352443af54d4910cbd53524436e54d4910db553524436c54d4910e
  | 6 => 0x36d5214a109f990528427d6414a109f98c528427d6314a10db98852843756114a10de980528427f65d0a109f997428427d65d0a109f197428427f6590a109f996428427d6590a109f19642842f66190a10bd586428427f6550a109f995428427d6550a109f19542842df6350a10b718d42842f76150a10bd18542842fb6050a10be181428427f6510a109f994428427d6510a109f19442842de6310a10b758c42842fa6010a10be580428427f65cca109f997328427d65cca109f197328435f53cca10d714f32842fa60cca10be583328427f658ca109f996328427d658ca109f196328427f654ca109f995328427d654ca109f195328435f534ca10d714d32842f7614ca10bd185328427f650ca109f994328427d650ca109f194328433e54d0610cf55341842fa60d0610be583418437565d0610ddd5341843b654d0610dd55341843b554d0610ddd4f418437553d0610dd94b418437452d0610fc98341842f560d0610fc583418433f5490610cf15241842de6390610b758e418433e5450610cf55141842fb6050610be181418433f5410610cf15041843b54110610bd59441843756510610ed99041843775410610edd5041843755410610ed15041843775310610dd54c41843765210610dd14841842f56010610d794f318435d53cc610be98331842f960cc610d7d4e318435c538c610d794d318435d534c610bed8131842f8604c610d7d4c318435c530c610db94b218436d52c8610be98321842f960c8610dbd4a218436c5288610db949218436d5248610bed8121842f86048610b798c21842dd6308610dbd48218436c5208610cf952408433d5490210bd98640842f56190210ed10640842df6350210b718d40842ef6250210bb18940842f76150210bd185408433e5410210cf55040842f66110210bd58440843b44110210d7d4f308435c53cc210bb98b30842ed62cc210d794e308435d538c210bd98630842f5618c210d7d4d308435c534c210d794c308435d530c210bd98430842f5610c210b798f20842dd63c8210db94a208436d5288210bd98620842f56188210db948208436d5208210bd98420842f56108210fa48020842f565c4210dd59710842f664c4210bd193108437753c4210dd54f10842f965c4210de597108427e63d51109f58f544427e62d51109f58b544433f63d5110cf98f544433d63d5110cf18f544433f62d5110cf98b544433d62d5110cf18b544433f61d5110cf587544433f60d5110cf583544433f5495110b798e54442dd6395110bb98a54442ed62951109f992544423e64951109f98e544435e63951109798e544427d6395110d758e544425d63951109f98a544436e62951109b98a544427d6295110db58a544426d62951109f586544437561951109f58254443796095110b7d8d54442dc6355110bbd89
  | 7 => 0x50cb109f19432c42f6610cb10bd58432c433e5490710cf55241c42de6390710b758e41c42fa6090710be58241c433e5410710cf55041c42fa6010710be58041c435f53cc710d714f31c435e538c710d754e31c42fa608c710be58231c4375658c710dd95231c4374548c710dd94e31c43d6538c710f554e31c4374538c710bd98231c43f2608c710fc58231c435f534c710d714d31c42f7654c710ddd9531c4376544c710dd15131c43d7634c710f5d4d31c4376534c710dd14d31c43d4534c710f5d0d31c43d4434c710f5cc931c43d5324c710bd18131c435e530c710d754c31c43d5310c710be98031c42f9600c710db94a21c436d5288710be98221c42f96088710b798c21c42dd6308710db94821c436d5208710be98021c42f96008710cf95340c433d54d0310bd98740c42f561d0310cfd5240c433c5490310cf95140c433d5450310b7d8d40c42dc6350310bbd8940c42ec6250310bdd8540c42f46150310cfd5040c433c5410310d794f30c435d53cc310bb98b30c42ed62cc310bd98730c42f561cc310f54c730c435f538c310d714e30c43d6318c310d794d30c435d534c310bdd8530c42f4614c310f54c530c435f530c310d714c30c42f6610c310bd58430c43d6310c310b798f20c42dd63c8310db94b20c436d52c8310bd98720c42f561c8310dbd4a20c436c5288310db94920c436d5248310bdd8520c42f46148310dbd4820c436c52083109f98f548427d63d52109f98b548427d62d5210dd587548437a60d5210cfd52548427e63952109f58e548427e62952109f58a54842df6355210b718d548433f64552109fd8d548435f635521097d8d548427c6355210d718d548425c63552109fd89548427c6255210ddd85548433d5415210cf990548427e63152109f58c548427e62152109f58854843756115210de980548427e64d4e109f593538427e62d4e109f58b538437561d4e10de983538435f5394e109f992538427d6494e109f98a538427d6294e109fd91538427c6454e10d7d8d538427f6254e109f189538435d5314e109f990538427d6414e10d798c538427e6214e109f58853843756114e10de980538427f65d0e109f997438427d65d0e109f197438435f53d0e10d714f438427f6590e109f996438427d6590e109f19643842f66190e10bd586438427f6550e109f995438427d6550e109f19543842f76150e10bd185438427f6510e109f994438427d6510e109f194438435f5310e10d714c43842ee6210e10bb58843842fa6010e10be580438427e64d4a109f593528427e63d4a109f58f528437561d4a10de98352842de6394a10b758e528436f5294a109f992528427d6494a109f98e528435e6394a109798e528427d6394a10d758e528425d6394a109fd91528427c6454a109fd8d528427c6354a10dbd895284
  | 8 => 0x20fa8ca20083e93288020fa88620083e821880209fd9520082ef6548020dbd95200826f6548020bb99120082ec6448020bbd8d20082ed6348020bb18520082ef6048020db94120083eb4048020fa10120083eb3048020fa0c120082fb6548020ded95200827b6548020be99120082f86448020bed8920083eb6248020de94920083ea5248020fad0920083e84248020facc920083e83248020fac8520083e92148020b798f54c42dd63d5310bb98b54c42ed62d53109f98f54c435e63d53109798f54c427d63d5310d758f54c425d63d53109f98b54c436e62d53109b98b54c427d62d5310db58b54c426d62d5310dd98754c437960d5310cfd5254c427e63953109f58e54c427e62953109f58a54c433f64553109fd8d54c427c63553109fd8954c427c6255310cf55054c433e64153109f98c54c427d63153109f98854c427d6215310dd98454c437960153109f99353c427d64d4f109f98b53c427d62d4f10dd98753c437960d4f10d7d4e53c427e6494f109f59253c427e6294f109f58a53c43766194f109fd9153c427c6454f10d7d8d53c427f6254f109f18953c435d5314f10bb98853c42ed6214f109f99053c427d6414f10d798c53c427e6214f10db98853c426e6214f109f58853c436d6214f109b58853c43766114f10de58053c427f65d0f109f99743c427d65d0f109f19743c435e53d0f10d754f43c427f6590f109f99643c427d6590f109f19643c42f66190f10bd58643c427f6550f109f99543c427d6550f109f19543c42fb6050f10be18143c427f6510f109f99443c427d6510f109f19443c435e5310f10d754c43c42ee6210f10bb58843c42f66110f10bd58443c427e64d4b109f59352c427e63d4b109f58f52c437661d4b10de58352c436f5294b109f99252c427d6494b109f98e52c427d6394b109fd9152c427c6454b109fd8d52c427c6354b10dbd8952c42de6314b10b758c52c436d5214b109f99052c427d6414b109f98c52c435e6314b109798c52c427d6314b10d758c52c425d6314b10db98852c43766114b10de58052c427f65d0b109f99742c427d65d0b109f19742c436e52d0b10db54b42c427f6590b109f99642c427d6590b109f19642c427f6550b109f99542c427d6550b109f19542c42df6350b10b718d42c42f76150b10bd18542c42fb6050b10be18142c427f6510b109f99442c427d6510b109f19442c42de6310b10b758c42c436e5210b10db54842c42f66110b10bd58442c427f65ccb109f99732c427d65ccb109f19732c435e53ccb10d754f32c42f661ccb10bd58732c427f658cb109f99632c427d658cb109f19632c436e528cb10db54a32c427f654cb109f99532c427d654cb109f19532c435e534cb10d754d32c436e524cb10db54932c42fb604cb10be18132c427f650cb109f99432c427d6
  | 9 => 0x544510827f65d04209f997410827d65d0420cf953410833d54d0420bb98b41082ed62d04209fd96410827e65904209f59641082de6390420b758e41082ee6290420bb58a41083765190420dd54641082fa6090420be582410827f65504209f595410827c6550420cf951410833d5450420bbd8941082ec6250420dd94541083755150420bed8141082f860504209fd94410827e65104209f594410827f65cc4209f997310827d65cc420d794f310835d53cc420bb98b31082ed62cc420f34cb310827f658c4209f996310827d658c420dd9463108375518c4209fd95310827d654c4209f195310835e534c420d754d31082ef624c420bb18931083cd324c420dd9453108375514c420bed8131082f8604c4209fd94310827e650c4209f59431082ee620c420bb58831082fa600c420be580310837651c8420dd54721082fa60c8420be583210827d6588420bb596210836d6588420bb99221082ec6488420bbd8e21082ed6388420bb986210836d5188420bb582210827f6548420b798c21082dd6308420dd94421083755108420be98021082f96008420bb99021082ec6408420bbd8c21083ce6308420bb58c21083cd6308420b358c21082ee6108420f998421083e65108420db54421083e55108420f9d0421083e44108420fa98021082ed6008420fa58021082e960084209f992500827d64940209f98e500827d6394020dbd0a500836c4294020db8ca500836d3294020db886500836c21940209f59740082f965d0020de597400837b54d0020de55340083eb62d0020be58b40083e862d0020de94b40083eb42d0020fa10b40083ea32d0020fa4cb40083ea21d0020fa087400827f65900209f596400833e5490020cf55240082ee6290020bb58a40082fa60900209fd9540082df6350020b718d40082ef6250020bb18940082f76150020bd185400827f65100209f994400827d65100209f194400833e5410020cf55040082ee6210020bb58840082f96510020de59440082796510020be99040083ba6410020ded5040083ba5410020de55040083b95410020fa98840082f96210020fa588400837a5210020fad0840083e84210020fa8c840083e93210020ee90440083b84110020fa88440083e821100209f59730082ee62cc020bb58b300827f658c0209f596300835e538c020d754e30082ee628c020bb58a30083cd328c0209fd95300827f650c0209f994300827d650c0209f194300835e530c020d754c30082ee620c020bb58830083cd320c020bd98430082f5610c020f64c030082de63c8020b758f20082ee64c8020bb19320082ef63c8020f398f20082ed63c8020f358f20082cd63c8020bb98720083eb40c8020fa10320082ed6288020db94a20082fa6488020be19220082f96288020de94a20083ea5288020fad0a20083e842880
  | 10 => 0x40827e6115020dd984540827661150209f584540837561150209d584540827e6015020de980540827e64d4c209f593530827e62d4c20db98b530827e61d4c209f587530827e60d4c20de983530827d6594c20d7d4e530827e6494c209f592530836e6294c209f986530827d6194c209fd91530827c6454c20d7d8d530827f6254c209f589530827f6154c209f18553082be6414c20af590530835d5314c20bd98453082f56114c209f990530833e6414c208f990530827d6414c20cf590530823d6414c209f98c530835e6314c209f988530836e6214c209f98453083766114c209d984530827d6114c20dd58453082756114c209f980530837a6014c209fd97430827e65d0c209f597430827c65d0c20cf953430833d54d0c20d7d4f430835c53d0c209fd96430827e6590c209f596430827c6590c20d794e430835d5390c20bb98a43082ed6290c20bd98643082f56190c20be98243082f96090c209fd95430827e6550c209f595430827c6550c20cf951430833d5450c20d794d430835d5350c20bbd8943082ec6250c20bed8143082f86050c209fd94430827e6510c209f594430827c6510c20d7d4c430835c5310c20bb98843082ed6210c209f992520827d64948209f98e520835e63948209798e520827d6394820d758e520825d63948209f59742082ed65d0820db597420836f54d0820db55342082ed63d0820bb98742083eb60d0820bb58342083e860d08209fd96420827d6590820cf952420833d5490820bb98a42082fa6090820be582420827f6550820b7d8d42082dc6350820bdd8542082f46150820bed81420827f65108209f594420833e5410820cf55042082de6310820b758c42082fa6010820be580420836d65108209b59442082ee6410820eb990420836f5410820eb950420836d5410820eb550420832d5410820f398c42082ed6310820f358c42082cd6310820bb98442083ea6010820bb58042083e960108209f597320835f53cc820d714f320827f658c8209f596320835e538c820d754e32082fa608c820be582320836d658c8209b59632082ee648c820bb192320836f548c820db55232082ed638c820db94e32083ce538c820f354e320836c538c820f3d0e32083cc438c820bb98632083ea608c820bb58232083e9608c820ba582320827f654c820d7d4d320835c534c820bbd95320836f654c820bb99132082ec644c820dbd51320836d544c820f3d8d32083cf534c820db94d320836c534c820f314d32083ce434c820f350d32082ec614c820bbd81320827f650c8209f594320835e530c820d754c32082ee620c820f34c832082fa600c820be580320837751944209f992510827d64944209f98e510827d63944209fd91510827c64544209fd8d510827c6354420af99051082bd6414420b798c51082dd6314420dd
  | 11 => 0x5c5310d20bb98843482ed6210d209f997424833f54d0920cf15342482fa60d0920be583424827e65909209f195424833f5450920cf15142482df6350920b718d42482f76150920bd18542482fb6050920be181424827e6510920b798c42482dd6310920eb508424827e65cc920d7d4f324835c53cc920be98332482f960cc9209f996324827c654c920d7d4d324835c534c920bed8132482f8604c9209f994324827e64d45209f593514827e63d45209f58f51483775194520afd9151482bc6454520b7d8d51482dc6354520b798c51482dd6314520dd544514827e64145209f590514827e6314520d798c514825e63145209f58c514835d63145209758c514827e65d05209f597414827c65d0520ddd47414837451d05209f996414827d65905209f196414833f5490520cf15241482de6390520b758e414827f65505209f995414827c65505209f994414827d65105209f194414833f5410520cf15041482ee6210520bb58841483775110520dd14441482fa6010520be580414827e65cc5209f597314827c65cc520d794f314835d53cc520ddd47314837451cc5209f996314827d658c5209f196314835f538c520d714e314827f654c5209f995314827c654c520d794d314835d534c5209f994314827d650c5209f194314835f530c520d714c3148377510c520dd144314827e65c8520ddd4621483745188520be98221482f96088520ddd4521483745148520bed8121482f860485209f99421482de6308520b758c214827e65d0120cfd53404833c54d0120bb98b40482ed62d01209f996404827f65501209f595404827c6550120cfd51404833c5450120b7d8d40482dc6350120bbd8940482ec6250120bdd8540482f461501209f994404827e65cc120d7d4f304835c53cc120bb98b30482ed62cc1209f996304835e538c120d754e304827f654c1209f595304827c654c120d7d4d304835c534c120bbd8930482ec624c1209f994304835e530c120d754c30482f6610c120bd58430482de63c8120b758f204837a54c8120de15320483da63c8120f658f204836e5488120db152204836f5388120db54e204836c5188120fad42204827e63d50209f58f540827e62d5020db98b540827e61d50209f587540827e60d5020de983540827d6595020cfd52540827e63950209f58e540827e61950209f58654082df6355020b718d54082f76155020bd185540833f64550209fd8d540835f635502097d8d540827c6355020d718d540825c63550209fd89540827d6255020db189540827f6155020ddd85540827761550209f185540837461550209d18554083786055020cf55054082de6315020b758c54082f66115020bd584540827e6415020cf990540827e6315020d798c540825e63150209f58c540835d63150209758c540827e6215020db9885
  | 12 => 0x8c6209f996318827d658c620dd9463188375518c6209fd95318827d654c6209f195318835e534c620d754d31882ef624c620bb18931883cd324c620dd9453188375514c6209fd94318827e650c6209f59431882ee620c620bb58831883765188620dd54621882fa6088620be58221882ee6488620bb19221882ef6388620bb58e21883e65188620db54621883e55188620fa98221882ed6088620fa58221883765148620dd54521882fb6048620be18121882de6308620b758c21882ed6508620db59421882ee6408620bb19021882ef6308620f398c21882ed6308620f358c21882cd6308620f9984218836d5108620f9d0421883e44108620bb580218833e5490220cf55240882ee6290220bb58a40882df6350220b718d40882ef6250220bb18940882f76150220bd185408833e5410220cf55040882ee6210220bb58840882ee62cc220bb58b308835e538c220d754e30882ee628c220bb58a30883cd328c220d794c308835d530c220bb98830882ed620c220f34c830882f6610c220bd58430882de63c8220b758f20882ed65c8220db59720882ee64c8220bb19320882ef63c8220f398f20882ed63c8220f358f20882cd63c8220bb98720882f965c8220de597208837a54c8220de15320883da63c8220f658f208827e63d51209f58f544827e61d51209f587544833f54951209f992544827e63951209f58e544827d6295120db58a544827e61951209f586544827d6095120de58254482df6355120b718d54482f76155120bd185544833f64551209fd8d544835f635512097d8d544827c6355120d718d544825c63551209fd89544836f62551209bd89544827f6155120ddd85544827761551209f185544837461551209d185544827f6055120ded81544827b60551209f994544833d5415120cf990544827e63151209f58c544827e62151209f188544827e61151209f584544827e64d4d209f593534827e61d4d209f587534835f5394d209f992534827d6494d209f98e534827d6294d20db58a534826d6294d209f986534827d6194d209f58253483796094d20afd9153482bc6454d20bdd8553482f46154d209fd91534833f6454d208fd91534827c6454d20cf191534823c6454d20d7d8d534827f6254d20dbd89534827f6154d20ddd8553482776154d209f18553483746154d209d185534827f6054d20ded81534827e6514d20d754c534827e6414d209f590534835e6314d209f988534827c6214d209f984534827d6114d209fd97434827e65d0d209f597434827c65d0d20d7d4f434835c53d0d209fd96434827e6590d209f596434827c6590d20cfd52434833c5490d20bd98643482f56190d209fd95434827e6550d209f595434827c6550d209fd94434827e6510d209f594434827c6510d20cfd50434833c5410d20d7d4c43483
  | 13 => 0xf64c030c82de63d5220b758f54882f661d5220bd587548827e63d5220d798f548825e63d52209f58f548835d63d52209758f548836d62d52209f987548837661d52209d987548827d61d5220dd587548827561d5220de983548833f54952209f98e548827d63952209f986548827d6195220cfd91548827f63552209f18d548836f62552209fd85548827c6155220cf550548833e64152209f98c548827d6315220db588548827e61152209f584548837a60152209f993538827d64d4e20db58b538827e61d4e209f587538837a60d4e20d7d4e538827e6494e209f592538836d6294e209f986538827d6194e209fd91538827c6454e20d7d8d538827f6154e209f185538835d5314e20bd98453882f56114e209f990538827d6414e20d798c538836d6214e209f98453883766114e209d984538827d6114e20dd58453882756114e20de980538827f65d0e209f997438827d65d0e209f197438835e53d0e20d754f438827f6590e209f996438827d6590e209f19643882ee6290e20bb58a43882f66190e20bd586438827f6550e209f995438827d6550e209f19543882ef6250e20bb189438827f6510e209f994438827d6510e209f194438835e5310e20d754c43882ee6210e20bb588438833e54d0a20cf55342882fa60d0a20be583428836d65d0a20dbd5342883ae54d0a20db55342883ad54d0a20bb58f42882ee61d0a20fa98342882ed60d0a20fa583428833e5450a20cf55142882df6350a20b718d42882f76150a20bd18542882fb6050a20be18142882de6310a20b758c42882ed6510a20db59442883ae6410a20dbd50428836d5410a20f398c42882ed6310a20f358c42882cd6310a20bb98442882ed6010a20d794f328835d53cca20be98332882f960cca20bb596328836d658ca20bb99232882ec648ca20dbd52328836d548ca20db94e328836c538ca20f3d0e32883cc438ca20bb98632882ed608ca20d794d328835d534ca20bed8132882f8604ca20dbd9532882ee644ca20bb191328836f544ca20db55132883cf634ca20db94d32883ce534ca20f354d328836c534ca20f390d32883cd434ca20bb18532882ef604ca20fad8132883e8604ca20f34c8328837751946209f992518827d64946209f98e518827d63946209fd91518827c64546209fd8d518827c6354620b798c51882dd6314620dd544518827f65d06209f997418827d65d0620bb98b41882ed62d0620dd947418837551d06209fd96418827e65906209f59641882de6390620b758e41882ee6290620bb58a418827f65506209f595418827c6550620bbd8941882ec62506209fd94418827e65106209f59441883765110620dd54441882fa6010620be580418827f65cc6209f997318827d65cc620d794f318835d53cc620bb98b31882ed62cc620f34cb318827f65
  | 14 => 0x9643c835e5390f20d754e43c82f66190f20bd58643c82fa6090f20be58243c827f6550f209f99543c827d6550f209f19543c835e5350f20d754d43c82fb6050f20be18143c827f6510f209f99443c827d6510f209f19443c835e5310f20d754c43c82ee6210f20bb58843c835e53d0b20d754f42c833e5490b20cf55242c835e5390b20d754e42c82fa6090b20be58242c82df6350b20b718d42c835e5350b20d754d42c82f76150b20bd18542c82f86050b20cf95042c833d5410b20b798c42c82dd6310b20d794c42c835d5310b20eb50842c82fa6010b20be58042c835e53ccb20d754f32c835e538cb20d754e32c82fa608cb20be58232c835e534cb20d754d32c835e530cb20d754c32c82fa600cb20be58032c82be64d4720af59351c82de63d4720b758f51c835e53d4720d754f51c835e5394720d754e51c837751947209f99251c827d64947209f98e51c827d6394720d794d51c835d53547209fd9151c827c64547209fd8d51c827c6354720b798c51c82dd6314720d794c51c835d5314720dd54451c827f65d07209f99741c827d65d0720d794f41c835d53d0720dd94741c837551d07209fd9641c827e65907209f59641c833e5490720cf55241c82de6390720b758e41c835e5390720d754e41c82fa6090720be58241c827f65507209f59541c827c6550720d794d41c835d5350720bed8141c82f860507209fd9441c827e65107209f59441c833e5410720cf55041c835e5310720d754c41c82ee6210720bb58841c83765110720dd54441c827f65cc7209f99731c827d65cc720d794f31c835d53cc7209fd9631c827e658c7209f59631c835e538c720d754e31c827f654c7209f59531c827c654c720d794d31c835d534c720bed8131c82f8604c7209fd9431c827e650c7209f59431c835e530c720d754c31c82fa600c720be58031c835e53c8720d754f21c837651c8720dd54721c82fa60c8720be58321c835e5388720d754e21c835e5348720d754d21c82de6308720b758c21c835e5308720d754c21c83765108720dd54421c82fa6008720be58021c833e54d0320cf55340c835e53d0320d754f40c82ee62d0320bb58b40c82f965d0320de59740c837b54d0320ee95340c837954d0320ee55340c83da53d0320f654f40c83ea62d0320be58b40c83e962d0320d794e40c835d5390320cf95140c833d5450320b7d8d40c82dc6350320d794d40c835d5350320bbd8940c82ec6250320bdd8540c82f46150320d794c40c835d5310320be59440c83796510320ee99040c837b5410320de55040c83da5310320f654c40c82f96210320ee90440c83b84110320d794f30c835d53cc320bb98b30c82ed62cc320d794e30c835d538c320d794d30c835d534c320bbd8930c82ec624c320d794c30c835d530c320bd98430c82f5610c32
  | 15 => 0xc3755148430bed81210c2f860484309fd94210c27e65084309f594210c2de6308430b758c210c3765108430dd544210c27e64940309f592500c35f4394030d710e500c35f3294030d74ca500c35e3194030d70c6500c27d65d0030dd947400c37551d00309fd96400c27d6590030cf952400c33d5490030b798e400c2dd6390030dd946400c37551900309fd95400c2df6350030b718d400c2ef6250030bb189400c2f76150030bd185400c3765150030dd545400c27f65100309f994400c27d65100309f194400c33e5410030cf550400c2de6310030b758c400c3765110030dd544400c3b94010030bb98b300c2ed62cc030dd947300c37551cc030b7993300c2dc64cc030f398b300c2dd62cc030f358b300c2cd62cc030b7987300c3d651cc030d7547300c3d551cc030d5547300c2dd638c030d794e300c376518c030dd546300c2f9638c030de94e300c3da538c030f6d0e300c3d8438c030f6cca300c3d9328c030fc946300c3f1518c030f68c6300c3d8318c0309fd95300c376514c030dd545300c2df654c030d7d95300c25f654c030b7991300c2dc644c030b7d89300c2dc614c030f5945300c35d514c030f5545300c355514c030b7d81300c35e504c030bed95300c37b654c0309ed95300c2fb634c030f6d8d300c37a534c030f694d300c3da324c030f60c9300c3f2514c030fc545300c2de63d5320b758f54c82f661d5320bd58754c827e63d5320d798f54c825e63d53209f58f54c835d63d53209758f54c836e62d53209f98754c837661d53209d98754c827d61d5320dd58754c827561d5320de58354c833f54953209f98e54c827d63953209f98654c827d6195320cfd9154c827f63553209f18d54c827f61553209f18554c837b6055320cf55054c82de6315320b758c54c833e64153209f98c54c835e63153209798c54c827d6315320d758c54c825d6315320db98854c827e61153209f58454c837960153209f99353c827d64d4f20db98b53c827e61d4f209f58753c837960d4f20d7d4e53c827e6494f209f59253c827e6194f209f58653c835f5494f20d795253c835d5494f20d715253c835f6494f20d799253c835d6494f20d719253c835e6294f20d718a53c835f6194f20d798653c835d6194f20d718653c835f6094f20d758253c827f6454f209f19153c835f6354f209fd8553c827c6154f20d7d9553c835f5454f20d795153c835d5454f20d715153c835f6454f20d799153c835d6454f20d719153c835e6254f20d718953c835f6154f20d798553c835d6154f20d718553c835f6054f20d758153c835d5314f209f99053c827d6414f20d798c53c836e6214f209f98453c827d6114f20de58053c827f65d0f209f99743c827d65d0f209f19743c835e53d0f20d754f43c827f6590f209f99643c827d6590f209f1
  | 16 => 0xe64cc830b7193320c35f54cc830d7553320c35e52cc830f394b320c3cd52cc830b7987320c3da60cc830b7583320c3d960cc830b6583320c27d658c830b758e320c27f654c830b7d95320c35f654c830b7991320c2dc644c830d7d51320c35d544c830f3d89320c3cf524c830d7949320c3cc524c830f3909320c3cd424c830b7185320c2df604c830b798c320c36e520c830db548320c3cd320c830be980320c2f9600c830ddd46510c27e64944309f592510c27e62944309f58a510c3775494430dd952510c3755494430dd152510c3d46394430f5d0e510c3d44394430ddd4a510c3765294430dd54a510c3745294430f5cca510c3d53294430ddd92510c3766494430dd592510c3746494430dd18e510c3774394430dd90e510c3754394430dd10e510c3776294430dd98a510c3756294430dd18a510c3774294430dd90a510c3754294430dd10a510c3773294430dd8ca510c3753294430dd0ca510c3766094430dd182510c27f64544309f191510c35f4354430d710d510c27f62544309f189510c35f3254430d74c9510c3776554430ddd51510c3765454430dd551510c3745454430f518d510c3d74354430f510d510c3775254430dd949510c3755254430dd149510c3d73254430f54c9510c3776454430dd991510c3756454430dd191510c3766354430ddd0d510c3574354430dd90d510c3754354430dd10d510c3544354430ddd89510c3766254430dd589510c3746254430ddd09510c3764254430dd509510c3744254430ddcc9510c3573254430dd8c9510c3753254430d54c9510c3743254430dd981510c3746054430dd0c1510c2f66114430dd544510c27f65d04309f997410c27d65d0430b798f410c2dd63d0430dd947410c37551d04309fd96410c27e65904309f596410c2de6390430b758e410c3765190430dd546410c27f65504309f595410c27c6550430b7d8d410c2dc6350430dd945410c3755150430bed81410c2f860504309fd94410c27e65104309f594410c3765110430dd544410c35e53cc430dd947310c37551cc430be983310c2f960cc4309f596310c375518c430b7596310c35d658c43097596310c2de648c430b7192310c2dd628c430b7986310c3d6518c430d7546310c3d5518c430d5546310c3d7418c430f5106310c2dd608c4309fd95310c35e534c430dd945310c376510c430dd544310c2fa600c430be580310c2de640c430b7190310c2dd620c430b7984310c3d6610c430f5944310c35d510c430f5544310c355510c430f6980310c2dd600c430f6580310c27f65c84309f997210c27d65c8430b798f210c2dd63c8430dd947210c37551c84309fd96210c27e65884309f596210c2df6388430b718e210c3765188430dd546210c27f65484309f595210c27c6548430b7d8d210c2dc6348430dd94521
  | 17 => 0xc530d7145314c3d4514c530f5d05314c3d4414c530f6d81314c2dc604c530f6181314c27e650c530b798c314c3d5310c5309f997214c27d65c85309f197214c37751c8530dd147214c27e65885309f596214c27c6588530b798e214c2dd6388530dbd4a214c36c5288530be982214c2f960885309fd95214c27e65485309f195214c27e65085309f594214c27c6508530b798c214c2dd6308530dbd48214c36c5208530ddd44214c37451085309f997404c33f54d0130cf153404c2de63d0130b758f404c27e65901309fd95404c27d65501309f195404c33f5450130cf151404c2df6350130b718d404c2ef6250130bb189404c2f76150130bd185404c27e6510130bb98b304c2ed62cc130fa98b304c3e962cc130f6cc7304c3d931cc130d7952304c35c548c130d7d4a304c2dd618c130d7146304c3db508c130bd987540c2f561d50309f98f540c35e63d50309f98b540c27d62d50309f987540c37661d50309d987540c27d61d5030dd587540c27561d50309f983540c37a60d50309f596540c33f54950309f98a540c27d62950309f986540c27d6195030cfd91540c27f63550309f58d540c35c63550309fd89540c27c62550309fd85540c27c6155030cf550540c2ee6215030bb588540c2f66115030bd584540c27e6415030cf990540c27e6315030d798c540c27e6215030db988540c26e62150309f588540c36d62150309b588540c27e6115030dd984540c27661150309f584540c37561150309d584540c27e6015030de980540c27e6494c309f592530c36e6294c30db58a530c27d65d0c30b7597430c35d65d0c30d7d53430c35d54d0c30b758b430c2de61d0c30b7583430c27f6590c309f596430c33e5490c30cf552430c2de6390c30bd986430c2f56190c30be982430c2f96090c309fd95430c27f6510c309f594430c33e5410c30cf550430c2ee6210c30bb588430c2fa6010c30be580430c35d6510c3097594430c2de6410c30e7990430c35f5410c30e7950430c35d5410c30e7550430c3ce6210c30b7588430c3cd6210c30b3588430c2de6110c30f6980430c2dd6010c30f6580430c2f661d4830bd587520c36f52948309f992520c27d6494830d7d0e520c35c43948309f986520c27d61948309fd91520c27c64548309fd85520c27c6154830af990520c2bd6414830db548520c2f66114830bd584520c27f65d08309f997420c27d65d0830cf953420c33d54d08309fd96420c27e65908309f596420c2de6390830b758e420c36e5290830db54a420c27f65508309f595420c27c6550830cf951420c33d5450830b7d8d420c2dc6350830db949420c36d5250830bdd85420c2f46150830bed81420c2f860508309fd94420c27e65108309f594420c2de6310830b758c420c36e52cc830db54b320c2fa60cc830be583320c2d
  | 18 => 0x9fd95218c27d65486309f195218c2df6348630b718d218c27f65086309f994218c27d6508630b798c218c2dd6308630cf952408c33d5490230b798e408c2dd6390230b7d8d408c2dc6350230bbd89408c2ec6250230bdd85408c2f46150230cf950408c33d5410230b798c408c2dd6310230bb98b308c2ed62cc230b7597308c35d65cc230b7993308c2dc64cc230f398b308c2dd62cc230f358b308c2cd62cc230b7987308c35d51cc230be597308c37965cc230fa98b308c3e962cc2309f98b544c27d62d51309f987544c27d61d5130cfd52544c27e64951309f58e544c35d63951309f98a544c27d62951309f986544c27d61951309f582544c3796095130bbd89544c2ec6255130bdd85544c2f46155130cfd91544c27f6355130d7d8d544c25f63551309fd89544c36f62551309bd89544c27c6255130db189544c26c62551309fd85544c37761551309dd85544c27c6155130dd185544c27461551309fd81544c37b60551309f994544c33d5415130cf990544c27e63151309f18c544c27e62151309f588544c27e61151309f584544c27e65d0d30cfd53434c33c54d0d30be983434c2f960d0d309f996434c2f66190d30bd586434c27c6550d30cfd51434c33c5450d30bed81434c2f86050d309f994434c2ee6210d30bb588434c27e64d49309f593524c27e61d49309f587524c36f5294930afd91524c2bc6454930bdd85524c2f46154930db548524c27e64149309f590524c27e61149309f584524c27e65d09309f597424c27c65d0930dbd4b424c36c52d09309f996424c27d65909309f196424c33f5490930cf152424c27f65509309f995424c27c6550930b7d8d424c2dc6350930bdd85424c2f46150930bed81424c2f860509309f994424c27d65109309f194424c33f5410930cf150424c2de6310930b758c424c36f5210930db148424c27e65cc930dbd4a324c36c528c930be982324c2f9608c930dbd49324c36c524c930bed81324c2f8604c9309f994324c27e64d45309f593514c27e62d45309f58b514c3775194530afd91514c2bc6454530bbd89514c2ec6254530dd544514c27e64145309f590514c27e62145309f588514c27e65d05309f597414c27c65d0530ddd47414c37451d05309f996414c27d65905309f196414c33f5490530cf152414c2de6390530b758e414c27f65505309f995414c27c65505309f994414c27d65105309f194414c33f5410530cf150414c2de6310530b758c414c3775110530dd144414c2fa6010530be580414c27e65cc530b7997314c35e65cc53097997314c35e54cc530d7153314c35f52cc530d7147314c2de60cc530b758e314c377518c530dd146314c2fa608c530be582314c377514c530dd145314c2fb604c530be181314c35e544c530d7151314c35f524c530f5d85314c3d7514
  | 19 => 0x140cc33d5450330b7d8d40cc2dc6350330bbd8940cc2ec6250330db94940cc36d5250330bdd8540cc2f46150330db94840cc36d5210330ee50040cc35d63d52309f98b548c27d62d52309f987548c27d61d5230de983548c33f54952309f98a548c27d62952309f986548c27d6195230bdd85548c2f46155230cfd91548c35f63552309fd89548c27c62552309fd85548c37761552309dd85548c27c6155230dd185548c2746155230cf550548c33e6415230d758c548c27e62152309f588548c27e61152309f584548c37a6015230cf953438c33d54d0e30be983438c2f960d0e30d7597438c35f54d0e30e7953438c35d54d0e30e7553438c2dd62d0e30b7987438c3da60d0e30b7583438c3d960d0e30bd986438c2f56190e30cf951438c33d5450e30bed81438c2f86050e30bb988438c2ed6210e30b7594438c35d6510e30e7990438c35f5410e30d7550438c3ce6210e30b7588438c3cd6210e30b3588438c2de6110e30b7580438c36f5294a309f992528c27d6494a30d7d0e528c35c4394a309f986528c27d6194a309fd91528c27c6454a309fd85528c27c6154a30db548528c27f65d0a309f997428c27d65d0a309fd96428c27e6590a309f596428c2de6390a30b758e428c27f6550a309f595428c27c6550a30b7d8d428c2dc6350a30bdd85428c2f46150a30bed81428c2f86050a309fd94428c27e6510a309f594428c2de6310a30b758c428c2dd65cca30d7597328c2de64cca30b7193328c35f54cca30d7553328c35e52cca30b7987328c2dd60cca30db94a328c36d528ca30be982328c2f9608ca30db949328c36d524ca30bed81328c2f8604ca30b7991328c2dc644ca30d7d51328c35d544ca30f3d89328c35e524ca30f3949328c3cd524ca30f3909328c3cd424ca30b7185328c2df604ca30f6d81328c3d8604ca30f34c8328c37751946309f992518c27d64946309f98a518c27d62946309fd91518c27c6454630d7d0d518c35c43546309fd89518c27c6254630d7cc9518c35d3254630dd544518c27f65d06309f997418c27d65d0630b798f418c2dd63d06309fd96418c27e65906309f596418c2de6390630b758e418c27f65506309f595418c27c6550630b7d8d418c2dc63506309fd94418c27e65106309f594418c2fa6010630be580418c376518c630dd546318c2fa608c630be582318c2de648c630b7192318c2dd628c630f5946318c35d518c630f5546318c3d7418c630f5106318c3da608c630b7582318c3d9608c630dd945318c375514c630bed81318c2f8604c630b7594318c35d650c630b7990318c2dc640c630b7588318c3d6610c630d7544318c2dd600c6309fd97218c27e65c86309f597218c2de63c8630b758f218c27f65886309f996218c27d6588630b7d8e218c2dc6388630be982218c2f96088630
  | 20 => 0xc36c5494b30dbd9252cc36e6494b30db59252cc36c6494b30db18e52cc36f4394b30db90e52cc36d4394b30db10e52cc36f6194b30db98652cc36d6194b30db18652cc36f6094b30db58252cc27f6454b309f19152cc27f6154b309f18552cc36f6554b30dbd5152cc36e5454b30db55152cc36c5454b30dbd9152cc36e6454b30db59152cc36c6454b30db98d52cc36f4354b30db90d52cc36d4354b30db10d52cc36f6154b30db98552cc36d6154b30db18552cc36f6054b30db58152cc36d5214b309fd9742cc27e65d0b309f59742cc36e52d0b30db54b42cc27f6590b309f99642cc27d6590b30db94a42cc36d5290b309fd9542cc27d6550b309f19542cc2df6350b30b718d42cc36e5250b30db54942cc2f76150b30bd18542cc2fb6050b30be18142cc27f6510b309f99442cc27d6510b30b798c42cc2dd6310b30db94842cc36d5210b30db94b32cc36d52ccb30be98332cc2f960ccb30db54a32cc36e524cb30db94832cc36d520cb30be98032cc2f9600cb30af99351cc2bd64d4730bb98b51cc2ed62d4730db94b51cc36d52d4730db94a51cc36d5294730ddd4651cc27e64947309f59251cc27e62947309f58a51cc36e5254730db54951cc27f64547309f19151cc27f62547309f18951cc2ee6214730bb58851cc36e5214730db54851cc37551147309fd9741cc27e65d07309f59741cc36e52d0730db54b41cc37651d0730dd54741cc27f65907309f99641cc27d6590730cf95241cc33d5490730b798e41cc2dd6390730db94a41cc36d52907309fd9541cc27d65507309f19541cc36e5250730db54941cc2fb6050730be18141cc27f65107309f99441cc27d6510730cf95041cc33d5410730b798c41cc2dd6310730db94841cc36d5210730dd94441cc3755110730db94b31cc36d52cc730dd94731cc37551cc730be98331cc2f960cc730d795331cc35c54cc730f394b31cc35d52cc730f354b31cc34d52cc730d794731cc3d651cc730f554731cc2de60cc730f698331cc3d960cc730db94a31cc36d528c730db94931cc36d524c730b7d9531cc35f654c730d795131cc35c544c730f394931cc35d524c730f354931cc34d524c730f5d8531cc3d7514c730d794531cc3d4514c730f5d0531cc3d4414c730b718131cc36e520c730db54831cc376510c730dd54431cc3d5310c730be98031cc2f9600c7309fd9721cc27e65c87309f59721cc36e52c8730db54b21cc27f65887309f99621cc27d6588730b798e21cc2dd6388730db94a21cc36d52887309fd9521cc27d65487309f19521cc36e5248730db54921cc2fb6048730be18121cc27f65087309f99421cc27d6508730b798c21cc2dd6308730db94821cc36d5208730cf95340cc33d54d0330b798f40cc2dd63d0330db94b40cc36d52d0330db94a40cc36d5290330cf95
  | 21 => 0x604c8409fd94321027e650c8409f594321037751944409f98e511027d63944409f98a511027d62944409fd8d511027c63544409fd89511027c6254440b798c51102dd6314440bb98851102ed6214440dd544511037651d0440dd54741102fa60d0440be583411027d6590440b798e41102dd6390440af596411033d6590440e798e411039d6390440af986411033d5190440af582411027f6550440dd94441103755110440ed50441102fa6010440be58041102be6110440ed98441103b65110440cf54441103b55110440ee98041102bd6010440ee580411027f65cc4409f997311027d65cc440af99331102bd64cc440d794f311035d53cc4409fd96311027e658c4409f5963110376518c440dd54631103b4418c4409fd95311027d654c4409f19531102bf644c440af191311035e534c440d754d3110376514c440dd54531103b4414c440bed8131102f8604c4409fd94311027e650c4409f594311027f65c84409f997211027d65c8440af99321102bd64c8440db94b211036d52c8440ed107211027f65884409f996211027d6588440dd94621103755188440be98221102f960884409fd95211027d65484409f19521102bf6448440af191211036e5248440db54921103765148440dd54521102fb6048440be181211027f65084409f994211027d6508440b798c21102dd6308440ed104211033e4194040cf10650102be61d0040af592401033e5490040be592401037a5490040ee95240102fa6290040ee90640103b841900409fd9540102df6350040b718d40102ef6250040bb18940102f76150040bd18540102bf6550040cfd95401023f6550040e7d8d401039c6350040ebd8940103ac6250040edd8540102bc6150040ed18540102b46150040afd81401033e5050040bed95401037b65500409ed9540102fb6450040eed91401037a5450040ee95140103db6350040f618d40103ba4350040ee10d40103eb6250040be18940103e86250040ba18940103f36150040fc18540102ee62d5330bb58b54cc2f661d5330bd58754cc35e63d53309f98b54cc36e62d53309b98b54cc27d62d5330db58b54cc26d62d53309f98754cc37661d53309d98754cc27d61d5330dd58754cc27561d5330de58354cc33f54953309f98a54cc27d62953309f98654cc27d6195330cfd9154cc27f62553309f18954cc27f61553309f18554cc33d5415330bb98854cc2ed6215330cf99054cc35e63153309f98854cc36e62153309b98854cc27d6215330db58854cc26d62153309f98454cc27d6115330de58054cc33e5490f30cf55243cc2f66190f30bd58643cc2fa6090f30be58243cc33e5410f30cf55043cc2ee6210f30bb58843cc2fa6010f30be58043cc36f5294b309f99252cc27d6494b309f98652cc27d6194b30dbd5252cc36e5494b30db55252c
  | 22 => 0x540b798e41502dd6390540d7d4e415035c5390540dbd4a415036c5290540ddd4641503745190540be98241502f96090540d7d4d415035c5350540dbd49415036c5250540ddd4541503745150540bed8141502f860505409f994415035f5310540d714c415036f5210540db148415037751105409f997315027d65cc5409f197315035f53cc540d714f315036f52cc540db14b315037751cc540dd147315027e658c5409f596315027c658c540d7d4e315035c538c540dbd4a315036c528c540ddd463150374518c5409fd95315027e654c5409f195315035f534c540d714d315036f524c540db1493150377514c540dd145315027e650c5409f594315027c650c540d7d4c315035c530c540dbd48315036c520c540ddd443150374510c540be98031502f9600c5409f997215027d65c85409f197215035f53c8540d714f215036f52c8540db14b215037751c8540dd147215027e65885409f596215027c6588540d7d4e215035c5388540dbd4a215036c5288540ddd46215037451885409fd95215027e65485409f195215035f5348540d714d215036f5248540db14921503775148540dd145215027e65085409f594215027c6508540af99021502bd6408540b798c21502dd6308540d7d4c215035c5308540dbd48215036c5208540ddd4421503745108540be98021502f96008540d7d4f405035c53d0140dbd4b405036c52d0140ddd47405037451d0140f6d4f40503d853d0140fad4b405037852d0140fa14b405036852d0140fcd4740503f051d0140d7d4e405035c5390140dbd4a405036c5290140ddd4640503745190140e7d4e405039c5390140ebd4a40503ac5290140edd46405033c5190140ed14640503345190140eed42405035f5394c409f98a531027d6294c409f986531027d6194c409fd89531027c6254c409fd85531027c6154c40d754c53102ee6214c40bb58853102f66114c40bd584531035e53d0c40d754f43102fa60d0c40be583431027d6590c40bd98643102f56190c409fd95431035e5310c40d754c43102ee6210c40bb58843102fa6010c40be580431036f52948409f98e521027d63948409f986521027d61948409fd8d521027c63548409fd85521027c6154840de18152102de6314840b758c521036d5214840bd98452102f56114840db94b421036d52d0840be98342102f960d08409f596421027f6550840b7d8d42102dc6350840bdd8542102f46150840bed8142102de6310840b758c421036e5210840db54842102fa6010840be580421027f65cc8409f997321027d65cc840d794f321035d53cc840be98332102f960cc8409fd96321027e658c8409f596321036e528c840db54a321027f654c8409f595321027c654c840afd9132102bc644c840d794d321035d534c840db949321036d524c840bed8132102f8
  | 23 => 0x718d525035f5354940d714d52502f76154940bd185525035f5314940d714c525036d52149409f98c525027d63149409f984525027d6114940bb994525036e6514940dbd4c52503cf5314940d3d4c525036e5314940db54c525036c5314940f314c525034c5314940dbd90525036f6314940db98c525036d6314940db18c525036f4314940db90c525036d4314940db10c525036f6114940db984525036d6114940db184525036f6014940db580525036d40149409f997425035f53d0940d714f425036c52d0940d7d4e425035c5390940dbd4a425036c5290940be98242502f96090940b7d8d42502dc6350940d7d4d425035c5350940dbd49425036c5250940bdd8542502f46150940bed8142502f860509409f99442502de6310940b758c425035f5310940d714c425036f5210940eb508425027e65cc9409f597325027c65cc940d7d4f325035c53cc940dbd4b325036c52cc9409f996325027d658c9409f196325035f538c940d714e325036f528c940db14a325027f654c9409f995325027c654c940d7d4d325035c534c940dbd49325036c524c9409f994325027d650c9409f19432502be640c940af590325035f530c940d714c325036f520c940db148325035f53d4540d714f515036f52d4540db14b515027e63d45409f58f515027e62d45409f58b515037753d4540f5d4f515035753d4540dd94f515037553d4540dd14f51503d453d4540d514f515037752d4540f9d4b515036752d4540dd94b515037552d4540dd14b51503e452d4540d914b515037764d4540ddd8f515037663d4540dd58f515037463d4540ddd0f515037643d4540dd50f515037443d4540ddd8b515037662d4540dd58b515037462d4540ddd0b515037642d4540dd50b515037442d4540ddccb515037632d4540dd4cb515037432d4540ddd83515037560d4540b798e51502dd6394540d7d4e515035c5394540bb98a51502ed6294540dbd4a515036c5294540ddd4651502df6354540b718d515035f5354540d714d51502ef6254540bb189515036f5254540db149515035f5314540d714c515036f5214540db148515037551145409f98c515027d63145409f988515027d6214540bd99451503766514540ddd4c51503d75314540d5d4c51503765314540dd54c51503745314540f514c51503545314540ddd4851503e75214540d9d4851503765214540dd54851503745214540f914851503645214540ddd9051503776314540dd98c51503756314540dd18c51503774314540dd90c51503754314540dd10c51503776214540dd98851503756214540dd18851503774214540dd90851503754214540dd10851503773214540dd8c851503753214540dd0c851503776014540dd580515037540145409f997415035f53d0540d714f415036f52d0540db14b415037451d0
  | 24 => 0x42902f86050a40b798c42902dd6310a409fd97329027e65cca409f597329027f658ca409f996329027d658ca40d794e329035d538ca409fd95329027d654ca409f19532902bf644ca40af191329027f650ca409f994329027d650ca40d794c329035d530ca40ddd46519027e63946409f58e519027e62946409f58a519027f63546409f18d519027f62546409f18951902de6314640b758c51903755114640b798e41902dd6390640dd94641903755190640be98241902f96090640e798e419039d6390640ed946419033d5190640ed54641903ba6090640af58241903b96090640dd94541903755150640bed8141902f86050640ed50441902bd6510640cf59441903b66110640edd44419033d5110640ed14441902bd60106409fd97319027e65cc6409f59731902be64cc640af593319035e53cc640d754f319027f658c6409f996319027d658c640dd9463190375518c640ed106319027f654c6409f595319027c654c640afd9131902bc644c640d794d319035d534c640dd9453190375514c640ed105319027f650c6409f994319027d650c640be98031902f9600c6409fd97219027e65c86409f59721902be64c8640af593219037651c8640dd54721903b441c86409fd96219027e65886409f596219027f65486409f595219027c6548640afd9121902bc64486409fd94219027e65086409f59421902de6308640b758c21903765108640dd54421903b44108640be98021902f96008640af597409033d65d0240af98740902f965d0240de597409037a52d02409f98b535027d62d4d409f987535027d61d4d40d7d93535035f62d4d40d798b535035d62d4d40d718b535035f61d4d40d7987535035d61d4d40d7187535035f60d4d40d7583535035f5394d40bb98a53502ed6294d40bd98653502f56194d40bbd8953502ec6254d40bdd8553502f46154d40d754c535027e6214d409f588535027e6114d409f58453502de6514d40d7994535035f6414d40d7d88535035e6214d40d7588535035c6214d40d7d84535035e6114d40d7584535035c6114d40d7d80535035d6014d40d7500535027e65d0d40d714f435035f5390d40d714e43502f66190d40bd58643502fa6090d40be582435035f5350d40d714d43502fb6050d40be181435027e6510d40d7d4c43502ee6210d40bb588435035f53d4940d714f525027e63d49409f58f525027e61d49409f587525036f53d4940f3d4f525034f53d4940db94f525036d53d4940db14f52503cc53d4940d314f525036f64d4940dbd8f525036e63d4940db58f525036c63d4940dbd0f525036e43d4940db50f525036c43d4940dbd87525036e61d4940db587525036c61d4940dbd83525036d60d4940b798e52502dd6394940d7d4e525035c5394940dbd4a52502f66194940bd58652502df6354940b
  | 25 => 0x2f56194f409f98a53d027d6294f409f98653d03766194f409d98653d027d6194f40dd58653d02756194f409fd8953d027c6254f409fd8553d027c6154f40d754c53d02ee6214f40bb58853d035e53d0f40d754f43d02fa60d0f40be58343d02f66190f40bd58643d035e5310f40d754c43d02ee6210f40bb58843d02fa6010f40be58043d036f5294b409f98e52d027d6394b409f98652d027d6194b409fd8d52d027c6354b409fd8552d027c6154b40ded8152d02de6314b40b758c52d036d5214b40db94b42d036d52d0b40be98342d02f960d0b40b7d8d42d02dc6350b40bdd8542d02f46150b40be18142d02de6310b40b758c42d036e5210b40db54842d03ad4210b40be98042d02f96010b409fd9732d027e65ccb409f59732d035e53ccb40d754f32d02fa60ccb40be58332d027f658cb409f99632d027d658cb40db94a32d036d528cb409fd9532d027d654cb409f19532d035e534cb40d754d32d036e524cb40db54932d02fb604cb40be18132d027f650cb409f99432d027d650cb40af99032d02bd640cb40b798f51d02dd63d4740bb98b51d02ed62d4740b798e51d02dd6394740ddd4651d027e6394740d798e51d025e63947409f58e51d035d63947409758e51d027e62947409f58a51d027f63547409f18d51d027f62547409f18951d03755114740dd94741d037551d0740be98341d02f960d0740b798e41d02dd6390740dd94441d03755110740be98041d02f960107409fd9731d027e65cc7409f59731d027f658c7409f99631d027d658c740d794e31d035d538c7409fd9531d027d654c7409f19531d02fb604c740be18131d027f650c7409f99431d027d650c740d794c31d035d530c7409fd9721d027e65c87409f59721d027f65887409f99621d027d6588740db94a21d036d5288740be98221d02f960887409fd9521d027d65487409f19521d02fb6048740be18121d027f65087409f99421d027d6508740af99021d02bd6408740b798c21d02dd6308740db94821d036d5208740d7d4e53902ee6294e40bb58a539027e6294e40db98a539026e6294e409f58a539036d6294e409b58a539027e6194e409f586539027f6254e409f189539027f6154e409f185539035d5314e40bd98453902f56114e40d794e439035d5390e40bd98643902f56190e40be98243902f96090e40d794d439035d5350e40bed8143902f86050e40bb98843902ed6210e40b798f52902dd63d4a40bd98752902f561d4a40b798e52902dd6394a40dbd4a529027e6394a40d798e529025e6394a409f58e529035d6394a409758e529027e6194a409f586529027f6354a409f18d529027f6154a409f185529036d5214a40db94a429036d5290a40be98242902f96090a40b7d8d42902dc6350a40db949429036d5250a40bdd8542902f46150a40bed81
  | 26 => 0x150c219fd94430867e6510c219f594430867c6510c21d794c430875d5310c21bb98843086ed6210c219f992520867d64948219f98e520867d63948219f597420875e53d0821d754f420867f65908219f596420873e5490821cf552420875e5390821d754e42086f66190821bd586420867f6550821b7d8d42086dc6350821d794d420875d5350821bdd8542086fb6050821be181420867f65108219f594420873e5410821cf55042086de6310821b758c420875e5310821d754c42087ad4210821bd98442086f561108219f597320875e53cc821d754f320867f658c8219f596320875e538c821d754e32086f6618c821bd586320867f654c821d794d320875d534c8219fd94320867d650c821d794c320875d530c821f34c832086f6610c821bd584320867e64944219f592510867e63944219f58e510867d65d0421d794f410875d53d0421bd597410877565d0421ddd53410877554d0421ddd4f41087d653d0421dd54f41087d553d0421d554f41086f562d0421dd94b410867f65904219f596410873e5490421cf55241086de6390421b758e410875e5390421d754e41086ee6290421bb58a41086f661904219fd95410875e5350421d754d410867f65104219f994410867d65104219f194410873e5410421cf550410875e5310421d754c41086ee6210421bb58841086f56510421dd59441086756510421bd99041087b66410421ddd5041087b65410421dd55041087b55410421cd55041087775310421f594c41087755310421f554c41087555310421f998841086f56210421f9588410877652104219f597310875e53cc421d754f310867f658c4219f596310875e538c421d754e31086ee628c421bb58a310867f654c421d794d310875d534c4219fd94310867e650c4219f594310867c650c421d794c310875d530c421bb98831086ed620c421f54c4310875e53c8421d754f21087ce53c8421f354f21087e741c8421f910721086ee60c8421d794e210875d5388421bb58a210876e5288421bd99221086f46488421f594e21087d55388421bd58a21087765288421f994a210867f6548421d794d210875d5348421bbd95210876f65484219bd9521087ce5348421f354d21086ef6148421db94521087e73148421f90c521086ec6048421bdd95210877765484219dd9521086f66448421bd19121087d65348421f554d21086f76248421f9d8921087765248421f994921087e73248421f90c921086de63d4021b758f500875e53d4021d754f500875e5394021d754e500877b50940219f992500867d64940219f98e500867d6394021ddd0650087744194021d794d500875d53540219fd91500867c64540219fd8d500867c6354021af99050086bd6414021b798c50086dd6314021d794c500875d5314021de540500875f5394f40bd98653d0
  | 27 => 0x21bd98742486f561d09219f996424867c6550921cfd51424873c5450921b7d8d42486dc6350921bdd8542486f46150921bed8142486f860509219f99442486de6310921b758c424867e65cc921d7d4f324875c53cc921bd98732486f561cc9219f996324867c654c921d7d4d324875c534c921bdd8532486f4614c9219f994324867e65d0521cfd53414873c54d0521bb98b41486ed62d05219f99641486de6390521b758e414867f65505219f595414867c6550521cfd51414873c5450521bbd8941486ec62505219f99441487b541105219f997314875f53cc521d714f31486ee62cc521bb58b314867e658c5219fd95314867d654c5219f195314875f534c521d714d31486ef624c521bb189314867e650c521dd953214877454c8521f9d46214867e64d41219f593504867e63d41219f58f504877b5094121afd9150486bc6454121b7d8d50486dc6354121de540504867e64141219f590504867e63141219f58c504876e2114121b798f54086dd63d50219f98f540875e63d50219798f540867d63d5021d758f540865d63d50219f98b540876e62d50219f987540877661d50219f983540867d60d50219f596540873f54950219f98e540867d63950219f982540867d6095021cfd91540867f63550219f18d540877461550219fd81540867c6055021cf55054086de6315021b758c54086fa6015021be580540867e6415021cf990540867e6315021d798c540865e63150219f58c540875d63150219758c540867e6215021db988540867e6115021dd984540867e6015021de980540867a60150219f580540877960150219e580540867e64d4c219f593530867e62d4c21db98b530867e61d4c21dd987530867e60d4c219f583530867d6594c21d7d4e530867e6494c219f592530867e6094c219f582530865d6594c21d7d52530875e5494c21d7552530875c5494c21d7d92530875e6494c21d7592530875c6494c21d798a530875c6294c21d7986530875c6194c21d7d82530875e6094c21d7582530875c6094c219fd91530867c6454c21d7d8d530867f6054c219f181530875f6554c21d7d51530875e5454c21d7551530875c5454c21d7d91530875e6454c21d7591530875c6454c21d7989530875c6254c21d7985530875c6154c21d7085530875f6054c21d7981530875d6054c21d718153086de6314c21d754c530867e6414c219f590530867e6314c21d798c530865e6314c219f988530876e6214c219f98453087766114c219f980530867d6014c219fd97430867e65d0c219f597430867c65d0c21d794f430875d53d0c219fd96430867e6590c219f596430867c6590c21d794e430875d5390c21bd98643086f56190c219fd95430867e6550c219f595430867c6550c21d794d430875d5350c21bbd8943086ec6250c21bdd8543086f46
  | 28 => 0x58053886796014e219fd97438867e65d0e219f597438867c65d0e21d794f438875d53d0e219fd96438867e6590e219f596438867c6590e21bd98643886f56190e219fd95438867e6550e219f595438867c6550e21bbd8943886ec6250e219fd94438867e6510e219f594438867c6510e21d794c438875d5310e21bb98843886ed6210e21cf953428873d54d0a21bd98742886f561d0a21cf951428873d5450a21b7d8d42886dc6350a21bdd8542886f46150a21bed8142886f86050a21b798c42886dd6310a21eb508428875e53cca21d754f32886f661cca21bd587328875e534ca21d754d32886f7614ca21bd18532887cd320ca21cf952418873d5490621b798e41886dd6390621bb98a41886ed6290621cf950418873d5410621bb98841886ed6210621ed504418875f53cc621d714f318875e538c621d754e31886ee628c621bb58a318875f534c621d714d318875e530c621d754c31886ee620c621bb58831886ed65c8621db59721886ee60c8621bd597218877565c8621dd953218877454c8621ded42508867e64942219f592508867e63942219f58e50886df6354221b718d508867f64542219f191508867f6354221d7d8d508865f63542219f18d508875c63542219718d50886de6314221b758c508877950142219f98f544867d63d51219f983544867d60d5121cfd52544867e64951219f98e544867d63951219f58a544876d62951219f586544877561951219f982544867d6095121b7d8d54486dc6355121bed8154486f86055121cfd91544867f6355121d7d8d544865f63551219f18d544875c63551219718d544867f6255121dbd89544867f6155121ddd85544867761551219fd81544877b60551219ed81544867c6055121de181544867860551219f994544873d5415121cf990544867e63151219f58c544867e60151219f580544867e64d4d219f593534867e60d4d219f583534875f5394d219f992534867d6494d219f98e534867d6294d21db58a534867d6194d21dd586534867e6094d219f58253486bf6454d21af19153486fb6054d21be181534867f6454d21cfd91534863f6454d219f191534873c6454d218f191534875f6354d219fd89534876f6254d219fd8553487776154d219fd81534877b6054d219ed81534867c6054d21de18153486786054d219f994534875d5314d219f990534867d6414d21d798c534867e6014d219f580534867f65d0d219f997434867d65d0d219f197434875f53d0d21d714f434867f6590d219f996434867d6590d219f196434873f5490d21cf15243486f66190d21bd586434867f6550d219f995434867d6550d219f195434867f6510d219f994434867d6510d219f194434873f5410d21cf150434875f5310d21d714c43486ee6210d21bb588434867e65d0921cfd53424873c54d09
  | 29 => 0x4c875d63153219758c54c876e6215321dd58454c867e60153219f58054c867e64d4f219f59353c876e62d4f21dd58753c867e60d4f219f58353c875f5394f219f99253c867d6494f219f98253c867d6094f219fd9153c867c6454f21d7d8d53c867f6054f219f18153c86be6414f21af59053c875d5314f219f99053c873e6414f218f99053c867d6414f21cf59053c863d6414f21d798c53c876e6214f21dd58453c867e6014f219f58053c867f65d0f219f99743c867d65d0f219f19743c873e54d0f21cf55343c875f53d0f21d714f43c867f6590f219f99643c867d6590f219f19643c875e5390f21d754e43c86f66190f21bd58643c867f6550f219f99543c867d6550f219f19543c873e5450f21cf55143c875e5350f21d754d43c86f76150f21bd18543c867f6510f219f99443c867d6510f219f19443c875f5310f21d714c43c86ee6210f21bb58843c873e5490b21cf55242c86f66190b21bd58642c86df6350b21b718d42c86f46150b21bed8142c86f86050b21cf95042c873d5410b21b798c42c86dd6310b21bd98442c86f56110b21d7d4f32c875c53ccb21d794e32c875d538cb21bd98632c86f5618cb21d7d4d32c875c534cb21d794c32c875d530cb21bd98432c86f5610cb21cf95341c873d54d0721bb98b41c86ed62d0721bd59741c877565d0721ddd5341c87b654d0721dd55341c87b554d0721ddd4f41c877553d0721f998b41c86f562d0721f958b41c86de6390721b758e41c873e5450721cf55141c86ef6250721bb18941c86f56510721dd59441c87b66410721ddd5041c87755410721ddd4c41c87755310721bd58841c875e53cc721d754f31c86ee62cc721bb58b31c875e534c721d754d31c86ef624c721bb18931c87d5310c721af99350c86bd64d4321b798f50c86dd63d4321ded4250c867e64943219f59250c867e63943219f58e50c87774194321dd10650c867f64543219f19150c867f63543219f18d50c87795014321b798f54886dd63d5221be98354886f960d52219f98f548875e63d52219798f548867d63d5221d758f548865d63d5221db58b548877661d52219f983548877a60d52219e983548867d60d5221de583548867960d5221cfd52548867e63952219f58e548867e60952219f582548873f64552219fd8d548867c63552219fd81548867c6055221cf550548873e64152219f98c548867d6315221db588548877661152219f980548867d60152219f993538867d64d4e21db58b538877661d4e219f983538867d60d4e21d7d4e538867e6494e219f592538867e6094e219f582538867f6454e219f191538875f6354e219fd81538867c6054e21d754c53886fa6014e21be580538867e6414e219f590538875e6314e21db58853887766114e219f980538877a6014e219e980538867d6014e21de
  | 30 => 0x5e63d50319f98b540c67d62d50319f987540c77661d50319d987540c67e60d50319f583540c67d6595031cfd52540c67e62950319f58a540c67e60950319f582540c73f64550319fd89540c67c62550319fd81540c67c6055031cf550540c6ee6215031bb588540c6fa6015031be580540c67e6415031cf990540c67e6315031d798c540c67e6215031db988540c66e62150319f588540c76d62150319b588540c67e6115031dd984540c67e6015031de980540c67a60150319f580540c77960150319e580540c67e6494c319f592530c67d65d0c31d794f430c67f6590c319f596430c73e5490c31cf552430c6f66190c31bd586430c67f6550c319fd94430c67d6510c31cf950430c73d5410c31d794c430c79d4310c31bb988430c6ed6210c31bd984430c6f56110c31be983520c6f960d4831dbd4a520c67e64948319f592520c67e60948319f582520c67f64548319f191520c67f60548319f181520c76d52148319fd97420c67e65d08319f597420c67f65908319f996420c67d6590831db94a420c76d52908319fd95420c67d65508319f195420c6df6350831b718d420c76e5250831db549420c6f76150831bd185420c6fb6050831be181420c67f65108319f994420c67d6510831b798c420c6dd6310831d794f320c76e52cc831db54b320c6f661cc831bd587320c67d658c8319fd95320c75e534c831db948320c76d520c831f34c8320c6f6610c831bd584320c67e64944319f592510c67d65d0431dd947410c67f65904319f596410c73e5490431cf552410c6de6390431b758e410c67f65504319fd94410c67e65104319f594410c67c6510431cf950410c73d5410431b798c410c6dd6310431dd944410c7b54110431d7953310c75c54cc431d754b310c6de60cc431b758e310c75e538c431dd952310c774548c431bd58e310c776538c431f594e310c67f654c431b7d95310c75f654c43197d95310c75e544c431d7151310c75d524c431b7d85310c75e514c431f5d05310c7d4414c431b7181310c6f7654c431ddd95310c677654c431dd951310c774544c431bdd8d310c7d7634c431dd94d310c7d6534c431f5d0d310c7d4434c431f58c9310c7d4324c431bb98b500c6ed62d4031ded42500c67e64940319f592500c67e62940319f58a500c67f64540319f191500c67f62540319f189500c75f3154031dd8c5500c75d3154031dd4c5500c77950140319f98f54c867d63d5321db98b54c877561d53219f98354c867d60d5321cfd5254c867e63953219f58e54c867e60953219f58254c86df6355321b718d54c873f64553219fd8d54c875f635532197d8d54c867c6355321d718d54c865c6355321ddd8554c867f60553219f18154c873d5415321b798c54c86dd6315321cf99054c867e6315321d798c54c865e63153219f58c5
  | 31 => 0x151319f988544c67d62151319f980544c67d60151319f997434c73f54d0d31cf153434c6f661d0d31bd587434c75e65d0d3197997434c75f54d0d31e7d53434c75d54d0d31e7153434c6dd62d0d31b7987434c7d661d0d31f5587434c6dd60d0d319f996434c6de6390d31bd986434c67c6550d31cfd51434c73c5450d31bdd85434c6f46150d319f994434c6ee6210d31bb588434c6de6510d31d7994434c6de6410d31e7990434c75f5410d31d7550434c7ce6210d31b7588434c7cd6210d31b3588434c7d76110d31b7984434c7d46110d31b7580434c67e64d49319f593524c67e60d49319f583524c76f5294931afd91524c6bc6454931bed81524c6f86054931db548524c67e64149319f590524c75f4314931d710c524c67e60149319f580524c67e65d09319f597424c67c65d0931dbd4b424c76c52d09319f996424c67d65909319f196424c73f5490931cf152424c6de6390931b758e424c6f66190931bd586424c67f65509319f995424c67c6550931b7d8d424c6dc6350931bdd85424c6f46150931bed81424c6f860509319f994424c67d65109319f194424c73f5410931cf150424c6de6310931b758c424c76f5210931db148424c67e65cc931b7997324c75e65cc931b7993324c6dc64cc931d7d53324c75d54cc931d714b324c6de61cc931b7583324c6dd638c931dbd4a324c76c528c931bd986324c6f5618c931dbd49324c76c524c931bdd85324c6f4614c931b7991324c6dc644c931d7d51324c75d544c931f3d89324c7cf524c931d7149324c7cc524c931d3149324c7ce424c931f3509324c7d7614c931b7185324c7d4614c931b5185324c6df604c9319f994324c6de630c9319f997414c73f54d0531cf153414c6de63d0531b758f414c6f665d0531dd997414c67665d0531ddd53414c7b754d0531dd553414c7b454d0531bd98f414c7d663d0531f558f414c7d743d0531f510f414c77452d0531f5ccb414c7d532d0531bd583414c67e6590531b798e414c6dd6390531bd986414c67f65505319f595414c67c6550531cfd51414c73c5450531b7d8d414c6dc63505319f994414c6f66510531dd994414c6f66410531ed990414c7775410531dd550414c7d76310531bd98c414c7d46310531f5d0c414c7d44310531dd148414c7d73210531f54c8414c6f56010531bd993314c6f464cc531f5d0f314c7d443cc531f5ccb314c7d532cc531bd583314c6de648c531b7192314c6dd628c531f5d46314c7d7418c531f5106314c6dd608c5319f993504c67d64d41319f98b504c67d62d4131ded42504c6bf6454131af191504c6ef6254131bb189504c77950141319f990504c67d6414131d7d0c504c75c43141319f988504c67d6214131d7cc8504c75d3214131ddd04504c7744114131d78c4504c67e63d5031d798f540c6
  | 32 => 0x1d755132cc7cf624cb31d794932cc7ce424cb31f350932cc6dc614cb31b7d8132cc76e520cb31db54832cc6f6610cb31bd58432cc73e54d0731cf55341cc6de63d0731b758f41cc6de6390731b758e41cc73e5450731cf55141cc6df6350731b718d41cc7b54110731af99350cc6bd64d4331bb98b50cc6ed62d4331ded4250cc67e64943319f59250cc75f4394331d710e50cc67e62943319f58a50cc75f3294331d74ca50cc67f64543319f19150cc67f62543319f18950cc7795014331d758f548c67e62d52319f58b548c77661d52319f983548c67d60d5231cfd52548c67e62952319f58a548c67e60952319f582548c73f64552319fd89548c67c6255231dd185548c67f60552319f181548c73d5415231cf990548c75d63152319f988548c67d6215231dd984548c67e60152319f580548c73e54d0e31cf553438c6f661d0e31bd587438c6f56190e31cf951438c73d5450e31bdd85438c6f46150e31e750c438c6ee6210e31bb588438c76f5294a319f992528c67d6494a319f982528c67d6094a319fd91528c67c6454a319fd81528c67c6054a31db548528c67f65d0a319f997428c67d65d0a319fd96428c67e6590a319f596428c6f66190a31bd586428c67f6550a319f595428c67c6550a31b7d8d428c6dc6350a31bdd85428c6f46150a31bed81428c6f86050a319fd94428c67e6510a319f594428c6de6310a31b758c428c76e528ca31db54a328c6f6618ca31bd586328c76e524ca31db549328c6f7614ca31bd185328c7cd320ca31bd597418c77565d0631ddd53418c77554d0631bd98f418c77652d0631bd583418c73e5490631cf552418c6de6390631b758e418c73e5410631cf550418c6de6310631b758c418c6f56510631dd594418c7b66410631ddd50418c7b65410631dd550418c7b55410631cd550418c6f66310631f598c418c7d56310631dd948418c6f56010631b7597318c75d65cc631d7953318c75c54cc631d754b318c6de60cc631bd597318c77565cc631bd993318c6f464cc631bd583318c77b50942319f992508c67d64942319f98a508c67d6294231ddd06508c7744194231bbd89508c6ec62542319fd91508c67c64542319fd89508c76f62542319bd89508c67c6254231db189508c66c6254231d7cc5508c7795014231d758f544c67e62d51319f58b544c77561d51319f983544c67d60d5131cfd52544c67e64951319f58e544c75d63951319f98a544c67d62951319f586544c77561951319f982544c67d6095131bbd89544c6ec6255131bed81544c6f86055131cfd91544c67f6355131d7d8d544c67f6255131dbd89544c66f62551319f189544c76c62551319b189544c67f6155131ddd85544c67f6055131ded81544c67b60551319f181544c77860551319e181544c67e6515131cf550544c73e64
  | 33 => 0x4f32106f661cc841bd587321067f658c8419f996321067d658c841db94a321076d528c8419fd95321067d654c8419f19532106bf644c841af191321075e534c841d754d321076e524c841db54932106f7614c841bd185321067f650c8419f994321067d650c841af99032106bd640c841bd98432106f5610c841d798e511075d6394441af98341106bd6490441cf95241106de6390441b758e41106f56490441dd95241107b65490441f598e41106f56390441f558e41106d56390441bd98a41106f660904419fd9541106bf6550441cfd95411063f6550441afd85411073e5150441af18141106f76550441ddd9541106776550441bdd9141107b76450441dd95141107b65450441bdd8d41107b64350441ed10d41106f46250441edd0941107b54250441bd181411077b50940419f98e501067d63940419f98a501067d6294041b7d8d50106dc6354041bbd8950106ec62540419fd8d501075f635404197d8d501067c6354041d718d501065c63540419fd89501076f62540419bd89501067c6254041db189501066c6254041b798c50106dd6314041bb98850106ed6214041de540501075e63d53319f98b54cc67d62d5331dd58754cc67e60d53319f58354cc73f54953319f98a54cc67d62953319f98254cc67d6095331cfd9154cc75c63553319fd8954cc67c62553319fd8154cc67c6055331cf55054cc6ee6215331bb58854cc73e6415331d798c54cc67e6215331db98854cc66e62153319f58854cc76d62153319b58854cc77561153319f98054cc67d6015331b759743cc75d65d0f31d7d5343cc75d54d0f31b758b43cc6de61d0f31b758343cc73e5490f31cf55243cc6f66190f31bd58643cc73e5410f31cf55043cc6ee6210f31bb58843cc6f66110f31bd58443cc75d6510f31e799043cc75f5410f31e795043cc75d5410f31e755043cc71d5410f31f398843cc6dd6210f31f358843cc6cd6210f31b798443cc7d66110f31f558443cc6dd6010f31dbd4a52cc67e6494b319f59252cc75f4394b31d710e52cc67e6094b319f58252cc67f6454b319f19152cc67f6054b319f18152cc6be6414b31af59052cc76d5214b319fd9742cc67e65d0b319f59742cc73e54d0b31cf55342cc67f6590b319f99642cc67d6590b31b798e42cc6dd6390b31db94a42cc76d5290b319fd9542cc67d6550b319f19542cc73e5450b31cf55142cc6df6350b31b718d42cc76e5250b31db54942cc6f76150b31bd18542cc6fb6050b31be18142cc67f6510b319f99442cc67d6510b31b798c42cc6dd6310b31db94b32cc76d52ccb31bd98732cc6f561ccb31b799332cc6dc64ccb31d7d5332cc75d54ccb31d794b32cc7ce52ccb31f354b32cc6de61ccb31f598732cc7d561ccb31b758332cc6df654cb31d7d9532cc6de644cb31b719132cc75f544cb3
  | 34 => 0x9067d650ca41af99032906bd640ca41d794c329075d530ca41d794f419075d53d0641af597419073d65d0641e794f419079d53d0641af98341906f565d0641dd59741907d653d0641dd54f41907d553d0641d554f419077652d0641b798f50906dd63d4241d794f509075d53d4241bb98b50906ed62d4241d794e509075d5394241ded42509067e63942419f58e509067e62942419f58a50907774194241d794d509075d53542419fd8d509067c63542419fd89509067c6254241b798c50906dd6314241d794c509075d5314241de540509067e62d4d419f58b535067e60d4d419f583535075f5394d41bbd8953506ec6254d41bed8153506f86054d41d754c535067e6214d419f588535067e6014d419f580535067e65d0d41d7d4e435075c5390d41bd98643506f56190d41d7d4d435075c5350d41bdd8543506f46150d419f99443506ee6210d41bb588435067e63d49419f58f525067e60d49419f583525076f5294941b7d8d52506dc6354941bed8152506f86054941b798c52506dd6314941db548525067e6314941d798c525065e63149419f58c525075d63149419758c525067e60149419f580525067e65d0941dbd4a425076c5290941bd98642506f56190941b7d8d42506dc6350941dbd49425076c5250941bdd8542506f46150941bed8142506f860509419f99442506de6310941b758c425067e65cc9419f597325067c65cc941dbd4b325076c52cc9419f996325067d658c9419f196325075f538c941d714e325067f654c9419f995325067c654c9419f994325067d650c9419f194325075f530c941d714c325076f520c941db148325077753d0541dd14b41506de6390541b758e415079e6390541e758e41507b751905419f98f505067d63d41419f98b505067d62d4141ded4250506df6354141b718d50506ef6254141bb189505077950141419f98c505067d63141419f988505067d6214141ddd04505073e4114141d7d4e531067e6294c419f58a53107766194c419f982531067d6094c419fd89531067c6254c419fd81531067c6054c41d754c53106ee6214c41bb58853106fa6014c41be580531075e53d0c41d754f43106f661d0c41bd587431067d6590c41bd586431067f6550c41d794c431075d5310c41e750c43106ee6210c41bb58843106f66110c41bd584431076f52948419f98e521067d63948419f982521067d60948419fd8d521067c6354841dd185521067f60548419f18152106de6314841b758c521076d5214841be98052106f96014841db94b421076d52d0841bd98742106f561d08419f596421067f6550841b7d8d42106dc6350841bdd8542106fb6050841be18142106de6310841b758c421076e5210841db54842107ad4210841bd98442106f561108419fd97321067e65cc8419f597321075e53cc841d75
  | 35 => 0xd32940329f986500ca7d61940329fd91500ca7c64540329fd85500ca7c6154032af990500cabd6414032bd984500caf56114032de540500cb5f5394f419f98a53d067d6294f41dd58653d067e6094f419f58253d067f6254f419f18953d067f6054f419f18153d075d5314f41bb98853d06ed6214f41d794f43d075d53d0f41bd98743d06f561d0f41bd98643d075e5310f41d754c43d06ee6210f41bb58843d06f66110f41bd58443d076f5294b419f98e52d067d6394b419f98252d067d6094b419fd8d52d067c6354b41ddd8552d067f6054b419f18152d06de6314b41b758c52d076d5214b41db94b42d076d52d0b41bd98742d06f561d0b41b7d8d42d06dc6350b41bd18542d06fb6050b41be18142d06de6310b41b758c42d076e5210b41db54842d06f66110b41bd58442d067f65ccb419f99732d067d65ccb41d794f32d075d53ccb41bd98732d06f561ccb419fd9632d067e658cb419f59632d076e528cb41db54a32d067f654cb419f59532d067c654cb41d794d32d075d534cb41db94932d076d524cb41bdd8532d06f4614cb419fd9432d067e650cb419f59432d06f6610cb41bd58432d06de63d4341b758f50d06ee62d4341bb58b50d077b50943419f98e50d067d63943419f98a50d067d62943419fd8d50d067c63543419fd8950d067c6254341de54050d075f5394e419f98a539067d6294e419f982539067d6094e41d7d92539075f6294e41d798a539075d6294e41d718a539075e6194e41d7186539075f6094e41d7982539075d6094e41d7182539067f6254e419f189539067f6054e419f181539075f6554e41d7591539075f6254e41d7989539075d6254e41d7189539075e6154e41d7185539075f6054e41d7981539075d6054e41d7181539075d5314e41d794f439075e5390e41d754e43906f66190e41bd586439075e5350e41d754d43906f76150e41bd185439075d5310e41e750c43906ee6210e41bb58843906de63d4a41b758f529075e53d4a41d754f52906fa60d4a41be583529075e5394a41d754e529076f5294a419f98e529067d6394a419f982529067d6094a41d794d529075d5354a419fd8d529067c6354a419fd81529067c6054a41b798c52906dd6314a41d794c529075d5314a41db548529075e53d0a41d754f429075e5390a41d754e429076e5290a41db54a42906f66190a41bd58642906df6350a41b718d429075e5350a41d754d429076e5250a41db54942906f76150a41bd18542906fb6050a41be18142906de6310a41b758c429075e5310a41d754c42907ad4210a419fd97329067e65cca419f597329075e53cca41d754f329067f658ca419f996329067d658ca41d794e329075d538ca419fd95329067d654ca419f19532906bf644ca41af191329075e534ca41d754d329067f650ca419f99432
  | 36 => 0x932fa181424cae860509329f994424cade6310932b758c424caee6210932bbd93324caed64cc932f390f324cbcd43cc932bb983324cadf648c932b7592324cb5e548c932d7152324cbcf528c932f390a324cbcd428c932b7586324cade608c9329f993514ca7d64d45329f983514ca7d60d4532ddd46514cabf6454532af191514cafb6054532be181514cb7551145329f990514ca7d64145329f980514ca7d60145329f993504ca7d64d41329f987504ca7d61d4132ded42504cabf6454132af191504caf76154132bd185504cb7950141329f990504ca7d64141329f984504ca7d6114132bd987540caf561d50329f98f540cb5e63d50329f98b540cb6e62d50329f987540cb7661d50329d987540ca7d61d5032dd587540ca7561d50329f983540ca7d60d50329f596540cb3f54950329f986540ca7d61950329f982540ca7d6095032cfd91540cb5c63550329fd85540ca7c61550329fd81540ca7c6055032cf550540ca7e6415032cf990540ca7e6315032d798c540ca5e63150329f988540cb6e62150329b988540ca7e61150329f584540ca7e60150329f580540ca7e6494c329f592530ca7d65d0c32b7597430cb5d65d0c3297597430cb5f54d0c32d7553430cadd62d0c329fd96430ca7d6590c32cf952430cb3d5490c32b798e430cb5e5390c32bb98a430caed6290c32bd986430caf56190c329fd95430cb5e5350c329fd94430ca7d6510c32cf950430cb3d5410c32bb988430caed6210c32d7594430ca5d6510c32b7990430cb9e6410c32d7d50430cb9e5410c32d7550430cb9d5410c32f3988430cadd6210c32f3588430cacd6210c329f992520ca7d6494832d7d0e520cb5c43948329f597420ca7f65908329f596420cb3e5490832cf552420cade6390832b758e420cb6e52908329fd95420cadf6350832b718d420cb6e5250832bdd85420caf46150832bed81420caf860508329fd94420ca7e65108329f594420ca7c6510832cf950420cb3d5410832b798c420cadd6310832eb508420cade64cc832b7193320cb5f54cc832d7553320cadd638c832d794e320cb6f548c832db552320caed638c832db94e320cbce538c832f3d0e320cbcc438c8329fd95320cadf654c832d7d95320ca5f654c832b7991320cadc644c832d7d51320cb5d544c832b7d89320cb5e524c832f3909320cbcd424c832bbd95320cb6f654c8329bd95320cb6f544c832db551320caef634c832f3d8d320cb6e534c832f394d320cbce434c832f350d320cabe64d4432af593510cb7751944329f992510ca7d64944329f982510ca7d60944329fd91510ca7c6454432d7d0d510cb5c4354432d7cc9510cb5d32544329fd81510ca7c6054432dd544510cb7b50940329f992500ca7d6494032d7d0e500cb5c4394032d7cca500cb6e3294032d74ca500cb6
  | 37 => 0xb7588438cbcd6210e32b3588438cb3e5490a32cf552428cade6390a32b758e428caed6590a32db596428cb6e5490a32eb952428cbad5490a32db152428caee6390a32f398e428cbcd6390a32f3d0e428cbcc4390a32bb982428cadf6350a32b718d428caf76150a32bd185428cafb6050a32be181428caef6550a32dbd95428cbaf6450a32db951428cb6c5450a32f3d8d428caec6350a32f318d428cacc6350a32f3d0d428cbcc4350a32f9d85428cbe46150a32fad81428caec6050a32fa181428cae86050a32cf950428cb3d5410a32b798c428cadd6310a32b7597328cb5d65cca32b7993328cadc64cca32d7d53328cb5d54cca32bb597328cb6d65cca32bbd93328caed64cca32bb983328cb7751946329f992518ca7d64946329f982518ca7d60946329fd91518ca7c6454632d7d0d518cb5c4354632d7cc9518ca7f60546329f181518cb755114632ded42508ca7e64942329f592508cb5f4394232d710e508cb5f32942329f986508ca7d61942329fd91508ca7c64542329fd85508ca7c6154232de540508ca7e61d51329f587544ca7e60d51329f583544cb3f54951329f992544ca7d6395132d758e544ca7d6295132db58a544ca7e61951329f586544ca7e60951329f582544caf76155132bd185544cafb6055132be181544cb3f64551329fd8d544cb5f635513297d8d544ca7f6255132dbd89544ca7f6155132ddd85544ca7761551329f185544cb7461551329d185544ca7f6055132ded81544ca7b60551329f181544cb7860551329e181544ca7e6515132cf550544cb3e6415132d758c544cb6d62151329f984544ca7d61151329f980544ca7d60151329f997434cb3f54d0d32cf153434caee62d0d32bb58b434ca7e6590d32bd986434caf56190d32b7996434cb5e6590d3297996434cadd6490d32d7952434cb5c5490d32f3d8a434cade6290d32f318a434cbd66190d32b7586434cbd56190d32b5586434cade6090d329f195434cb3f5450d32cf151434caef6250d32bb189434cb5c6550d3297195434cb9f6450d32e7d51434cb5e5450d32d7151434cb9c5450d32f3d89434cadc6250d32f3189434cadf6150d32b7181434ca7e6510d32b798c434caee6210d329f997424cb3f54d0932cf153424cade63d0932b758f424ca7e6590932bb996424cb6e6590932bb592424cb6e5490932db152424cbcf6390932bb98e424cbcc6390932f390e424cbcd4390932bb982424ca7f65509329f595424ca7c6550932cfd51424cb3c5450932b7d8d424cadc6350932bdd85424caf46150932bed81424caf86050932bb195424cb6c65509329b195424cbaf6450932ebd51424cb6e5450932db151424cbac5450932cb151424cbcf6350932bb18d424cbcc6350932f390d424cbcd4350932f9d85424cbe46150932fad81424caec605
  | 38 => 0x14210aec6050842fa1814210ae86050842b798f5110add63d4442d794f5110b5d53d4442d794e5110b5d5394442ddd465110a7e63944429f58e5110a7e60944429f5825110b5e5354442d754d5110a7f63544429f18d5110a7f60544429f1815110ade6314442b758c5110b5e5314442d754c5110b755114442be9805110af96014442b798f5010add63d4042d794f5010b5d53d4042d794e5010b5d5394042ded425010a7e63940429f58e5010a7e61940429f5865010b5e5354042d754d5010a7f63540429f18d5010a7f61540429f1855010ade6314042b758c5010b5e5314042d754c5010af66114042bd5845010b795014042bd98754ccaf561d5332be98354ccaf960d5332d798f54ccb6d62d53329f98754ccb7661d53329d98754cca7d61d5332dd58754cca7561d53329f98354ccb7a60d53329e98354cca7d60d5332de58354cca7960d5332cfd5254ccb5e63953329f98654cca7d61953329f98254cca7d6095332cfd9154cca7f61553329f18554cca7f60553329f18154ccb3d5415332cf99054ccb5e6315332db58854cca7e61153329f58454cca7e60153329f58054ccb3e5490f32cf55243ccaee6290f32bb58a43ccaf66190f32bd58643ccb5d6590f32d795243ccb9e5490f32e755243ccb5c5490f32b798a43ccbce6290f32f358a43ccbd66190f32b758643ccbd56190f32b558643ccade6090f32b7d9543ccb5f6550f32e7d9143ccb5e5450f32d715143ccadc6250f32b7d8543ccadc6050f32cf95043ccb3d5410f32bb98843ccaed6210f32cf95342ccb3d54d0b32b798f42ccadd63d0b32cf95142ccb3d5450b32b7d8d42ccadc6350b32bdd8542ccaf46150b32bed8142ccaf86050b32b798c42ccadd6310b32eb50842ccb7751947329f99251cca7d64947329f98251cca7d60947329fd9151cca7c64547329fd8151cca7c6054732dd54451ccafa6014732be58051ccb7b50943329f99250cca7d64943329f98650cca7d61943329fd9150cca7c64543329fd8550cca7c6154332bd98450ccaf56114332de54050ccb5d63d5232db98b548ca7e61d52329f587548ca7e60d52329f583548cb3f5495232db98a548ca7e61952329f586548ca7e60952329f582548caf76155232bd185548cb3f6455232d7d8d548ca7f6155232ddd85548ca7761552329f185548cb7461552329d185548ca7f60552329f181548cb3d5415232cf990548cb5d6315232db988548ca7e61152329f584548ca7e60152329f580548cb3e54d0e32cf553438caee62d0e32bb58b438cb5d65d0e32d7d53438cb9e54d0e32d7553438cb9d54d0e32f398b438cadd62d0e32f358b438caf66190e32bd586438cb3e5450e32cf551438caef6250e32bb189438caed6210e32b7594438cb5d6510e32e7990438cb5f5410e32d7550438cbce6210e32
  | 39 => 0xb776014542dd9805150b756014542dd1805150b5f53d4142d714f5050b7751d4142dd1475050a7e63d41429f58f5050a7e61d41429f5875050b7b53d4142f6d4f5050b5b53d4142de94f5050b7953d4142de14f5050bd853d4142d614f5050beb42d4142ee90b5050b7b51d4142fcd475050b7351d4142de9475050b7951d4142de1475050bf051d4142dc1475050b7b64d4142ded8f5050b7a63d4142de58f5050b7863d4142ded0f5050b7a43d4142de50f5050b7843d4142ded8b5050b7b42d4142de90b5050b7b61d4142de9875050b7961d4142de1875050ade6394142b758e5050b5f5394142d714e5050af66194142bd5865050b775194142dd1465050b7b5094142b7d8d5050adc6354142d7d4d5050b5c5354142bdd855050af46154142ddd455050b745154142d7d4c5050b5c5314142ddd445050b745114142de5405050a7e63141429f58c5050b6f42141429f9845050a7d6114142be9945050b7a6514142ded4c5050bdb5314142d6d4c5050b7a5314142de54c5050b785314142f614c5050b585314142fad085050bba4214142ded445050bf35114142dcd445050b7a5114142de5445050b785114142fc1445050b705114142ded905050b7b6314142de98c5050b796314142de18c5050b7b4314142de90c5050b794314142de10c5050b7b6214142ded085050b6b4214142de9085050b794214142ded845050b7a6114142de5845050b786114142d7d4e5310a7e6194c429f5865310a7e6094c429f5825310b5c6494c42d798a5310b5c6294c42d7d865310b5e6194c42d75865310b5c6194c42d7d825310b5e6094c42d75825310b5c6094c429fd855310a7c6154c429fd815310a7c6054c42d7d955310b5e6454c42d79895310b5c6254c42d71095310b5f6154c42d79855310b5d6154c42d71855310b5f6054c42d79815310b5d6054c42d71815310ade6314c42d754c5310b5e53d0c42d754f4310aee62d0c42bb58b4310a7d6590c42d754e4310af66190c42bd5864310a7f6550c42d794d4310b5e5310c42d754c4310aee6210c42bb5884310b5e53d0842d754f4210b9e53d0842e754f4210abd6490842cf9524210b5e5390842d754e4210aed6490842db9524210bae5490842f394e4210b6d5390842f354e4210b4d5390842bb9824210a7f6550842b7d8d4210adc6350842d794d4210b5d5350842bdd854210af46150842bed814210af86050842afd954210b3f65508428fd954210b9f6350842e718d4210b9e5350842e754d4210abf6250842cf9494210bb76150842ed1854210bbb6050842ee1814210aef6550842dbd954210a6f6550842bbd914210baf6450842db9514210bae5450842f3d8d4210bcc6350842f394d4210b6d5350842f354d4210b4d5350842eb90d4210bac4350842f9d854210be46150842fad8
  | 40 => 0x6354342b718d50d0a7f6354342d7d8d50d0a5f63543429f18d50d0b5c63543429718d50d0a7f61543429f18550d0b795014342d7d4e5390b6e6294e429f9865390a7d6194e429f9825390a7d6094e429fd855390a7c6154e429fd815390a7c6054e42d754c5390af66114e42bd5845390b5e5390e42d754e4390aee6290e42bb58a4390af66190e42bd5864390b5e5350e42d754d4390aef6250e42bb1894390aed6210e42af5974290b3d65d0a42bb5974290b6d65d0a42bb58f4290b7751946429f98e5190a7d63946429f9825190a7d60946429fd8d5190a7c63546429fd815190a7c6054642b798c5190add6314642dd5445190ade63d4242b758f5090af661d4242bd5875090b7b50942429f98e5090a7d6394242dbd0a5090a7e61942429f5865090a7f63542429f18d5090a7f61542429f1855090b7950142429f9875350a7d61d4d429f9835350a7d60d4d42f3d8b5350b5f64d4d42d7d8b5350b5d62d4d42d7d875350b5e61d4d42d75875350b5c61d4d42d7d835350b5e60d4d42d75835350b5c60d4d42d7d4e5350af66194d42bd5865350afa6094d42be5825350af76154d42bd1855350afb6054d42be1815350b5d5314d42db5885350a7e6114d429f5845350a7e6014d429f5805350ade6514d42d79945350bcd6214d42d7d905350b5f6214d42d75885350b4d6214d42d75085350b5f6114d42d79845350b5d6114d42d71845350b5f6014d42d79805350b5d6014d42d71805350a7e65d0d42d714f4350b5f5390d42d714e4350aee6290d42bb58a4350af66190d42bd5864350b5f5350d42d714d4350aef6250d42bb1894350a7e6510d42d7d4c4350aee6210d42d7d4f4250b5c53d0942bb58f4250bcf53d0942f314f4250b5f5390942d714e4250b9f5390942e714e4250baf5290942d7d4f5150b5c53d45429f98f5150a7d63d45429f9835150a7d60d4542ddd4f5150bd753d4542d5d4f5150b7653d4542dd54f5150b7453d4542f514f5150b5453d4542f9d0b5150bb642d4542ddd935150b7763d4542dd98f5150b7563d4542dd18f5150b7743d4542dd90f5150b7543d4542dd10f5150b7762d4542ddd0b5150b7642d4542ddd835150b7660d4542dd5835150b7460d4542b798e5150add6394542d7d4e5150b5c5394542ddd465150afa6094542be5825150adf6354542b718d5150b5f5354542d714d5150afb6054542be1815150b5f5314542d714c5150b7551145429f98c5150a7d63145429f9805150a7d6014542bd9945150b766514542ddd4c5150bd75314542d5d4c5150b765314542dd54c5150b745314542f514c5150b545314542f9d085150bb64214542ddd905150b776314542dd98c5150b756314542dd18c5150b774314542dd90c5150b754314542dd10c5150b776214542ddd085150b764214542dd508515
  | 41 => 0x9439f5835250f6f5294943bdd855250ef46154943bed815250ef86054943db5485250f5f43149439f9845250e7d61149439f9805250e7d6014943d7d0f5150e7e62d45439f58b5150e7e60d45439f5835150f775194543bbd895150eec6254543bed815150ef86054543dd5445150e7e62145439f5885150e7e60145439f5805150e7e62d41439f58b5050e7e61d41439f5875050f7b5094143bbd895050eec6254143bdd855050ef46154143de5405050f5f43141439f9885050e7d62141439f9845050e7d6114143dd9865310f756194c43af5924310f3e5490c43bd9864310ef56190c43b75924310f5e5490c43e79524310ede6290c43f59864310edd6190c43f55864310ed56190c43b79824310e7f6550c43afd954310f3f6550c438fd954310ebf6350c43cf94d4310edf6550c43d7d954310e5f6550c43b7d914310f9f6450c43d79514310f9e5450c43b71894310edf6150c43b71814310f6f52948439f9865210e7d61948439f9825210e7d6094843f318e5210faf4394843f390e5210fad4394843f350e5210f6c6494843db18e5210f6f4394843db90e5210f6d4394843dbd865210f6e6194843db5865210f6c6194843dbd825210f6e6094843db5825210f6c6094843d790d5210f5d43548439fd855210e7c61548439fd815210e7c6054843dbd955210fcc6354843ebd0d5210fce4354843eb50d5210fcd4354843db9915210f6e6354843dbd0d5210f6e4354843d390d5210f6d4354843d350d5210f6c4354843dbd855210f6e6154843db5855210f6c6154843dbd815210f6e6054843db5815210f6c6054843bb9885210f6d5214843bb98b5110eed62d4443db94b5110f6d52d4443db94a5110f6d5294443ddd465110e7e62944439f58a5110e7e60944439f5825110f6e5254443db5495110e7f62544439f1895110e7f60544439f1815110eee6214443bb5885110f6e5214443db5485110f755114443be9805110ef96014443bb98b5010eed62d4043db94b5010f6d52d4043db94a5010f6d5294043ded425010e7e62940439f58a5010e7e61940439f5865010f6e5254043db5495010e7f62540439f1895010e7f61540439f1855010eee6214043bb5885010f6e5214043db5485010ef66114043bd5845010f795014043d7d4e53d0a7e6194f429f58653d0a7e6094f429f58253d0a7f6154f429f18553d0a7f6054f429f18153d0b5d5314f42d794f43d0b5d53d0f42bb98b43d0aed62d0f42bd98643d0af56190f42d794c43d0b5d5310f42bb98843d0aed6210f42b798e51d0add6394742ddd4651d0a7e6394742d798e51d0a5e63947429f58e51d0b5d63947429758e51d0a7e60947429f58251d0a7f63547429f18d51d0a7f60547429f18151d0b755114742ded4250d0a7e63943429f58e50d0a7e61943429f58650d0adf
  | 42 => 0x2c0000028008000001800180000008018000800000000000004000003400200080000050005002c00a000c0220074022000002900000010010007000c0060014001001c0010008030001c0050014014006c0190000000009c00f00680310010000000000f006800600000020014004000c0000000000003c01600140030008002003c00200c000a001000000040020000000001001b00140000000000004c0010000029001c002001800c0008007001c01d00200160018013000c00100000320070002000000d0000007000400400000040010000000c0180008000003400100100000008002003000f0018013004c00000540080024015000800100040090038002000800e000400100c8019002000000000060048000001c0010000001001001600b4006002c002002c013001c0090008005006007f000800c002800300100070040001000802100f4011000400500040010008003002000000240090010001002000600040000004006000f6f5294b439f98652d0e7d6194b439f98252d0e7d6094b439fd8552d0e7c6154b439fd8152d0e7c6054b43db54852d0f7751947439f98a51d0e7d62947439f98251d0e7d60947439fd8951d0e7c62547439fd8151d0e7c6054743dd54451d0f7b50943439f98a50d0e7d62943439f98650d0e7d6194343bbd8950d0eec62543439fd8950d0f6f62543439bd8950d0e7c6254343db18950d0e6c62543439fd8550d0e7c6154343de54050d0ebd65d0e43cf5974390edd65d0e43d75974390edd62d0e43bd9875290ef561d4a43be9835290ef960d4a43dbd4a5290f5f4394a439f9865290e7d6194a439f9825290e7d6094a439fd855290e7c6154a439fd815290e7c6054a43db5485290ef66114a43bd5845290f7751946439f98a5190e7d62946439f9825190e7d6094643edd0e5190fd74394643ddd4a5190f765294643dd54a5190f745294643ddd925190f746394643ddd0e5190f776294643dd98a5190f756294643dd18a5190f776094643dd9825190f756094643dd1825190f5f43546439fd895190e7c62546439fd815190e7c6054643ddd955190fb74354643f5d0d5190f775254643dd9495190f755254643dd1495190f756454643dd98d5190f774354643d5d0d5190f776254643dd9895190f756254643dd1895190f776054643dd9815190f756054643dd1815190f755114643bb98b5090eed62d4243bd9875090ef561d4243dd9475090f7551d4243dd9465090f755194243ded425090f5f43942439f98a5090e7d62942439f9865090e7d6194243dd9455090f7551542439fd895090e7c62542439fd855090e7c6154243bd9845090ef56114243dd9445090f755114243de5405090edd62d0d43bd9864350ef56190d43e7d4e4350fb66190d43ed5864350e7e61d49439f5875250e7e60d4
  | 43 => 0x1e00080020004017008400700c40050020000000004f000c0090000000001800e0000008000800e00bc00400180000074000000000300000000054000004401100c8009002800a00340080000009001400b0028013001800100340010010000000001b000403a000801700100010020007001c00b0014003000800a0004001001c0010090012000400000000040050003001c011003400a0000001001800000200010008008000000a00d400100100120004008003c00400700040020004000001400000050040015001000300240100000000000800e0000000000c03c000002c00140010000006005000800080000000001001c00000400080008004000800400bc001002400300d000500180000014001003401500080000004000017800f000c009003800a000800000000150004002002c00000000020000000000000200000000008009000400b01680000018013000400400040000000000004400500000090008002001c00200080030000000000800a0000005000c00b0000003001c01c00180010004002000400000880080074000001c001000400f000000300100000008018003800a000800000000070020001003c02900000040000019005c00800080160074009002802b00680020018000001401b00400010000002000c00a001000000000000018000000c01000000370008000001800a00500040000000009c00000040020044002003c00e006403100180010000002002c000003c01500180100000000003402d00000010000009001c00a00080070000002000000000080010000000000c006001c002000000300000000000008005800c00040010050019005400001d80010054001000402300280050008003001000100640000000000002800000b000000100070004009000c00c002400800080080000002001c07c000c035000000300a8019003c000000c00400440040048000001000a0024019006c001002400500200050004001000000700180020000004000801600640000020000005800000180050074004000000100000100000009001c0040040000001c000001800200b80030028004004c002005c0020080003000c002000000b005c0000004023000000b0044005000c001001c0500000000000c000003c0000050000001000100080000000000000800c000c002020c008006800900140020030001000000000b0000000000000240000010000000000600700130028006000401b004c000006000e00b80060034004000000a00f000100b000100380000008005000400100080120000001001c003007000700280020044018000800100000040000000005c00000a40020000002001400300140700004003000000800580010008000001c01200380000028008000000000240030024013001000000100000
  | 44 => 0x5004c003001000100e4000000000800200050004007009001a0008006000400d000801b001000c0010001007000d0004001000800b0000000001c033000007a00940050018000010c0010064000000000200bc000000000c001800100000000014002002401c00000050020004000000c00040080000003000c0070018003001c00c0008005002800900040080010000006c002000800100140010000019008001c0010001000c0000000054000803000000030000002004c00200000020000013000400b000000b004c002001000200040040008009000c00000080100004001002c004006401a00000000010000012800100000050000023004400d000c00200b400900000060004039001c00300140100088040003c00300000000034000000000100000010074001000000700280000000015001802800580120004000001802e000c0000004022000c00d001000000480000018000003c001002000e00300080018000006c000001800400200000000015000400b001400000400160054000001c000000c00d0000005000800000b0000000c01200280130004006000800000380000000001000400900280020030000001c00700c4004000400000000010054002000c00f002000b0008005000c002000c018006805e000400101e00130018004001800400100020050003001000100380200014004000c02400000060010043000002700e800d002801f0004001006400000240080020036004c012002c0050004004001c00500000050010001001400000000000000030002001b0044000008c00300000000008003000400000e800200240040004009000000000000000000000001001a000000200e000a0000039000400300040510024000001c0040000006000000c0000007000c00f0028026000002d002400800000030090006001400500000010004028002800200080010048004000802000600090000009002401400000000004001000c00100100000024014000000000300000090006001c00600100010014001001c002000001e00080090000000001402f000000a02100030024007000000b000001d002000f000c003003c00000140010000001000c04a00100030010005000403c000000800380000084002004000d009c01e001800b0020003000000b000000300e4004000000000140000018001011801000340030038004002c004000000100000020020005008c013002800a000800500180000004007000c03500400040010000000800f001c00200080000024000001800500040cc000400000d800e000000c0054001004402e0158000005c000000000a01300070004000000c00000300060000017002802d0024001002000400ac00500b408a00100030024005000000b0000002003c007001001800500060010
  | 45 => 0xc01b000c0010008029001402c0044000000000b007801b000001400100480000002000c000001800d0044008000400000500000020007006000a000400000040020018004000c0090000001001400b006400000080080038002000c0000000000000802000dc0010020002005800400080000008001000000f0038001000c000007800b015401200800030000006000c006000400000080030018000008c0000028003000c01d00080010004048000400300080020000002000c0020000005001000001c00010020000000400000740000028021003000e000400200140090000002001c01b000402a0008001001c00200e400000140000000004000c0020000003002c02f00100000000001000805200440090124000000001100000010038005000c0040010014001c00000100120080000016c00200200030000001000000500000030040001009000000140010040006002802c0054000000000000180080000000001c000000000000500000014003004400000040000000005003400c002801600080050000009000000100240050020004000c00900b0000001800000300080068000000402e0010000000400600040020008017000000300c0001000c00000b402c006407e001000b000c00000080020004011001400a007003a001800400dc0040000001000c006000c00e00000110000001000000000800020004001001000201e4003001800d008c004000c00200cc007001c00300c4000002c0130000000000000900f40100000001001800100040070024008006c000000000e0004000000c01200740000024002001c00b00780160030000001402d00cc016001003b001c005000000a005c000001800000280020050000000802e00280060020004004000b00680010028006001004900800060004000000800f003000400c00260004001004c002003c00800080370060007000c0030010000002000300000000010019004000500080070038006006c0020000001002c0000038003006000d000000d0000005001002600100000020000001c0420000000000000100500100000012000400c000000a000400b001800500240070014001002c00201dc003000801e00040030000004000000b0014005003c00400080020008000007c0030050000003c0000040000002400f001c00b000000000300020088016001800400000310008019000801d00e000c001c00e000404100000080000017000c00000ac0010014008001800a000801e0004000000000100680050010000006c00000200020010001004800000100080000000005c0010028014003802100480180000010000000000080000024001006801e00000030004003000401500040010024004001001f0000006003400000440220038005003c00b006401c0014000000c005
  | 46 => 0x50010001000000b006800400000000000003000001800000050000000000c0040000010000000b000c007005003200080030000002004c000009c0000000001004800e000c03700200400000000000c014000000d0010000003000d000000f00a80130018001002c032003801700000070008005015002b00300080000009002c0000000006001000601840120040000000401000100110000001000800000100070008006001804500000000020001003000000740010004023000c022000800200180050000000005802e00000010000009000001d0014000000400d001400300100000008000002c0010000042000000400000030010007004c000000400a0000003000000000080070000006001c0300030011001c0000008003000000e001800300040000188000001800400bc0000008000006000000580000004009001c00f0010004004400e00140010000000001c00b00f400100400040028006001000000580020004000001000f004000d004c0060004003001800000780030000042002000200000040000002000400c00080060000002000c035004400100180000000001000c00d0018004003400201100070000002004800500040000000002000c0040000002000c05e001400e0000036000400900680050038001005400700000070028035001800d0014007005c0060008002001c00c008c00a000400600080000060000000c0000008000000401100a4012000403d001401b000c0020018003000000f0000000000c01600080160004013000c003000c00a0004000003400000000020034000000c00500b4023003000d0010008005c0080030000001000600400210020017004400100140290048032000000800500110008000000c0010024000000000400000010010008000800600840070008003001402000040080038000001002e030001c004c02600000000018005004800a0004003000000000240070078002000000f00e00010054020002000b000400800180000000000000800d001000700bc00a0028000000000200000010004000017800000040010030000004c031000400000500110008002000000e0014001001404e0000002000400201e8000000400100000150010002002001300040000000000001c0030008017000c0000000003003000902640070020005000c00600140090000007001400000000010038002003001b001401000180000004001000800300540000018006001401d001800a001403600040020034009003800b000c0170078008000c00800380000008002000800000000000000001003c01800040160020007006400100340010000000001c002002000000c408100340000090002000c00100200020020000001c001006400700200010004009000000b000400b00000000034001011
  | 47 => 0xf9909d95cf2c1e6b4c00011311d92000021d836418de8c300001fed398e8bf8ba823bb017807880000aae451e0fdc2ae22022a840c18ba284f346ac0b40a119bc83e428b68ee01a664732811823fa1cf00f834582a680000f624ee89dba13001fc6d00239924a13ca06990a7814228f449385a5020b23e432f1090000d003000000740010010001000000300980000014020000401000280000010000000c01700040120014012000c014005000000d8002000400200000070000005000000a0000006000c000002c0000004000000400000840030014016000402900d800500580220020001002800b0008000000800000840040014000000400a0000000001800000580020000005001c001002c0000000000000801a000800f007c0030000000001c025000000200040250040010001800d0010003003400d00140290018003001801200080030000005006c001002800000640000020001002400100000000018003000000000300230018002002c01800000040000001001800c003c02f0010000007400200200170000008002c00c00440010004003001c01e00040040000081002000200280030100002000800000200020078000005403400dc0050004019001800200a400100100020004002009000000000180018001000000a0000001004c00000080170034001000400900340060008011006400100080200048002000c00000100000014000000000000d8000000400500640000060005026800100200050018051004c00a00140010000000000000e0044000000400500140090000001000400c000c004001803a00040050004001002000b000000a0010007000000000340000000006006000c006c00000000010004002021400000000240008002000000b000000600800480010001000001a002000a000400400000000004004000001500080070030009000c0190000000004801d00300050040003000000b003c0220000001003c0040000000000400600040000000000006800700d80240008015000400a000000000080020000023003800100000130074001004400a001c000000000100140000028002000400c001003600b800000080040004056003c00100400050000001000000a008004f000000b0000000000400600080060010000001800000100010008000000000b0070019001c000000000300a000000080000024015000c00300000000000022000c0000000000000800000100020020000000400400000030008001005c01a001400500040000008004002802d0000000000c0000000004007800f001c016000c011003800a00280170028008000c010000400a0000005003003400340040004001003400e000800a002c005000000000400550088004004000500080000020002000803200000000014004007000
  | 48 => 0xd4e41be2a1ce8602ad07d04640e9e9fde30c0000000000003236808c00023963cfa6c207e49a47220a22a49d1870628180000fb4804425da85c4c10000003d650e4dcf847e0588792000004f4254e53f06ca00001a7a8c8400021a744927ff8e5293da313c000074e9bc0213608a4b0510b00cc885d84b89b2f3a5e5350fd098cd17780f1cb0c9e2538e01f95097884e0d3a1ccc21503962fb2289463693af1e3c7e8ce451caf14527a805b30d093b66669c2ab9c200fb2024c940818636008bb1072046c02aa2cd834010cd36a03a8c2bf127411ac236cb9d1bd0372002e443790d00a201dc4cb2947628566f24b5d00534408197c807180832de88990351431304625344a899612fa039946001ecf31a46b8c0000000000027e8a0d0ada00000c5865f0fdd0000437023d0ace00008a240000000000000008c6000043826d345ca800000008c780001fb3000061b4000203900000000cc4a070335600009d00000086a755400022f7428a2b10cf39aff0000000000000000bee7bbcd81960d133476b8c10800006680000416866718c01d3d14b008715548708cd3000000006ddc5a1978b22460090e1e06dc08c600004ea8000293e1d4d17f800000005b8911400003a7e0a7cf599dcd02fc454c3ad8e952b968e35109a03636460000ec9800000000504f088000450605980ef046b282c86cc8b5082b1e5887407909b17370e62dc000199116fe211cb1c0000000000000000000282000004ec8d480a6c00009a2221600002718000082100007b24b3517b9474489b471c800044e44df4d490c862ab64aa910907551fb2000115d8000280862c05af007e0c0c8aa4ddea37c1414369cdbf00f71b5619bcea7984213666e88e358b6e33e0348c7fa0cef149a00000000b1403d2000100d1c8f39840c3820e20cc46c6066016a96a3234e33a400012c10be67d9c194a06106988f291b2081037e007b0be20f802914000071e9568393436448bf98583f1a2304942a240231423c06c0049601aa5444b200d67161c496ce300117441c1eac9af027e1a1408601e419f3051443880000219117c74782d810e131247a9000018fb05c00f740020000000054387569cc603fc3bacb831f1719ee5128e228ed205d812d85c69323000058503670f9c3b6808e0d4d88663f724aeca430f1915b6000013a826442180000005053838820fc06e5134b45a6144495e85891c460000ead0975318a000015f9ce3000000004971bf119205f2cacd898500761015143977a134402fc99920ec2d628b80f4122fb052488802448b20000013a891580004380025c0c80ad300000000020800007ca0000000000016b05f1507e1a4300003e5c01f1e8b33f278dc00000e4000041d49ef0e4d33d415ed1d900e5376649e49281251397007703b71e9805be166517c90f53a686
  | 49 => 0x8a5cb69898122e63f4cadb82d32e58551061a13fd455e7578f5580003f6050510bd8000000037f902780001aee5b1002f9a5113dc0ea8ed1000000000000000020846de31944c40000000000005e78000380862285118f943302895479b000000001b2407600002a5466740880fd4453e33e800010db477473b51540b9c0000555cd3b0000216a3efcddf8000366c00006df96f402f61a4cbec007d1ef4000000006e5150a0000ec68e521d785a301b8800018448d2800000003f34154068f0000000000011810a4416a4000060b9f380d52707c6b9867013285e7c565000000000000010186500000000e5a1194388083dc29301643f5031c8000188400000000000095700001778d150000000044805b7800025043d98359166424225390e4480002cfc3e407b59dc710b600d881680000000621916f1bf800003e849558db928fa000006f800033785c38f2d97a8000067a4da60b13033e81b8fbd8a223a2462ccebf1b43451c6764bfb8a9739b46f70a5e221512705cc89121d63000088c05e88e2a32228d3c0da800018fa0000bfd80000694000072b98620000600119d8c8d138864f50fe1fdd47a219645958c3f381a37382620c873e1c7fa8b9f1f93298a0bbc1808e2604648684f06186625ee2414bfd18142b7029e512d96c5328c1b310c200001054512cfa822d2154a0000bc9000000000e240001e10000012f43da00000000000013c9ba500004c6cf8c000006560000e3615af2b4841b49ae802d00ca7bb455e00000000719cdee94e926b640cd0430000000059ac0fa0e2e252e0b7861c85e7224e86dc12c1f0535463c08bf89fbc1be85e98896945d35523d84be61f3c16104a650fe849d2a0c2100301088d267c6b9865b85700000000036980001edc0718000077a0d8454bc0001cee0fd483d0eaf94fe0bf8000073c21db1400000000007f8330a4444c689f40062a39a41b60cf3000039dc5a6023609da000080001371cc276383191e30282617b4b3d051317dc1d108e49e540bae365d1c99dab00002e4ce1f1e6122a403b51041e68441a6bdcae498f50fac633cbf80d7d023c50c86a6928a3cea0000ee7800025700000000000000003ddc0002293000055a8b0811810000000054d045429ce21b46a39e0b09980000947800000000154ac5147b445e0000000000020ee509c00014d91bc25cec7a9800020e657cc000073f011218443c2929323ee7b551be94e511581d98cef00002d0a4b9c4b19a633fb400009cc16582bfe1de43b80f1a2e56807ce83800000ce1fe4d7d00002c48172c35590102f0e612887322180da21cd0000000000000000bbb17ad000031a4d3988412676000090da1c31fce41ec0fb00e1245c000040d1fb63c846fe40000431279e0000f230000000065e1067914500002a44000000000007e70bfb1
  | 50 => 0x43c43b8ce790a4200000000eed9775185a0e74e27836a440267f8cad09ff02bc4564d1013ac161605d42828da123106dcc5c1023413a000011769e17262e51340001797000041a8000002b31003d2d0d5808d1a2a5604cc180001afc11c0a3b9757323e5a0c17a0000068815b80000f240000435519a9baf00003ad00000000308c42482259dd734703ce846422ba2a1e25f8d968d863c3a4528000068938582e750e6800000000000e70063b00000000be38f6520362248a52050b2c6425e8524010333de1390dbb1d39136471f87919f5240148994aab140d08808d9c7d8a107234836a8adc875e285e02e885196391c1a7244320a1f0189648b43990c94006472548ae9934174a17b0197140f31302e783e9005412d8863000003d4111800000001b9146f659d90079c880aea8344ee89b860f2881d84131d48000042087669f76266255f10148000347c2e0017d08df39ba10a4c5a98be197e0ae88e692a209dc2494aaa1e9900000000631000031f282bce67989a187c000000000001c580220daa0dc000000000d89800030e440880001197452803fc9bd8000462c00003c09dce328462fcce20000000000000001e6b00005608239120925aa00008f622d928aa00005f5800000000000000070a0000245c3799da100000001138818131c000000001cc12b4c31ac00000003f6e238519280000ede00002db1b27430c0000e0d80001b107eecd878fd610c47d143df910044ce80cd0fd866228d28968c18020f2d5226ecdc0064823b41a687d005d6139a1ff80000ccf20d68088284078647c8160401507a51be688c91cf9c6939885cfc38286a507dc45bc4d2803c3a523f3458010c016322610e689c2947ba5e94f510a7706b050f026893a413a6862cbb4800040188264cb81eea158224002d917a4427e1e600000d6235d012b034f8079200e2b84b7193c22a74177085000002a3c2638a35a02d1aa244b88428c102ac60b2cde2205b3ac4128878e95ba27c623fc52a0dd506ce1e6433601fc2f6c780905b00ab385c57f4b811f9e281263f062b04c9389615011061dea23700f24f4f060f06645849070134601f83f449381f8e39d4774894e09f1115486b8ea09a350f066dfd1bb8000113c33a887c09ac05160000cd2911d07363c04f28938500007188c97a0783fb089fd0a198ad31040970ac395e63476702891511a60e168eac9ae2252319c059cc082158212815209472051137e576400021871bf62508aac0000379a00003e78c4e00006cc8ee58ac91f2657080b9076400005a6019c00000a3281790908000074678a000009961404000109600000c12000117b000045966de83960cb01e5268902c708a8375019d04529b6233504b586d2927827ee790ce729b510ac41f702b28ca116c24b8485f8d8340a84c18e9b20c60060
  | 51 => 0xa5d45089a1ad31fc09c49f217253c4e3b80f208f7341ae4100685856b0acc4dd878217da12544b48d41948f39d034a0ee2026b2daa1bf8768118b231e831c21581c3457a4a980b8809839b25910bfe232f3ee66b24605869c1cfa1e9cba1a1f93eba8b0c48420063bb00804d589a6c3e9875402dc1d66124047d85d89d7937f64b0c395a225201e360918d8b48295a03f4a2185f60d7e337c000000000001d84e5e9bea2c0237a442d234e1e8e268040209de1d12671828183281ed460b40319d4a3a1e0d890200fb5169c6fc80be110c3a862dc800010e00000373449187e21b7a07e000000000cec4c4cadf80002068568c26d90550c6680c08031cf13fb65304e71181e055466502cf95b213d60088b17a37a23782c9c28690032a3471ec5400d42007402d098e8727080271348a711250b98051489ea2a41ce87338f69225616da08504a2880e478e54d4591908d17285e0c31f00c043e68c9099b962826c82840abe8ed600001e2400001b922c250648ce133c373c0000b850a93000040dc3178000424a60084f50000153c00010f586b53bf47a0c731118719821908fe114ed1aa64fbcf1a80e8044a1b88c9c172e3e5425f007d833517c2877817b110100ea5f2400007c61fc45a9c03999ca00007c2c0000000317a00006fe0000000056590d412fa0be46c681c28384326210f41918a980af00000c0ba31500007aec9949f5a312e2ab400000001d8e8e1c7651d24007268c85201e3b0c58356cedc800037f88dac9fa0a630000000077b000030340904bce8131000072fc9b580000000641cf5f90b22ccc82911089784000001a80001b8c000068ac00003793ed42b80649079536d05adcd66998b11860000000200b2a0a3eb46d0048d037c2a0cb0320280cc621c83d315fc1f9642786191516439837706569109223240f890e16a2371a2500000000043e24f2c00000001f440b5841c880a0b1670a8b8d000024047b64fe68000000000005861922030e2f200a580001a4c8d885520000145e889000000990f080a18a518c6800000000000000026a23af4c6806ad1a7e17e8d8600003da239ec00018ee0000406477f000007402ad43d78da30000761087621f21df8487515300000000000000f8f13000000003fb05ad14565388000164c2a660000eca000039920c789e68013349e3768c5787ff1ba00000acf1722022c8f48d4b000011566a608bb0fe51a5675b0d558000132a4e1d0f18a19196c32b0ce414a21fbe75d843f12cd272868242b48681000000009582199000000000000000309e80f80001eb8067883783dc99982ce271f40000ded346624ecc1e800000005b48000229217ac63185ab96dd1cac34bc00011c6000000000001e7f40426908dd4884c0d6c0000a8415f10a5434701711b6930fa6804000158f00004f18d69
  | 52 => 0xa0cd03a880ac4ed2232b0b2460e47c0943b412656d80f192042e96630d0d60ab7406e19948161cb72d7665ecee18f050c064bbcaf28a05003276e87e010e31ba858ed1ad0ba61eb45514a9f033f2d1e7e0c8fd0000221a00005921f63465c84a4bae9ecd056866643271a81097c5c50a49903c000045503d19ec6237c4d94438878000008c34000000000004440ba49f7936e018551d31d45000029402578000036e271d0771a7102ac00000001255000045448310b0929a67c307a2802300007e58d6e0ea2453683b46bd0d43217087a071f8eb900001b54504800000000dc91e18f080ece8bac788983635603518ee99594016e0c10bde207d2a943fec35e00513e6a2d5072f9e8147c089b059b9f5742ea071c0000b90409431180001c1528b865642c60e5829fa38782741f222e8c00000000f5b42902b986791635409c4614e2c0cdd062870003f7905701ac8120755160c22be7ca006686394710681c5a384432a6879590cd14aa1fc623e0f69907a22e834b4817a344037672c4094a21c0f1e464ca448fe646ba3fe8bc78df510ba2b08ee31d96154662f0ece01bf30640000c020eb631c28098389132d3f7c00d50ce16a42e8245186b58000134226000000e1200004d8000011290cb0597c9ab86571382864d18a0425078800001a1129511c010803760e0f0c1889f890016681756302052c087a12aa328864e13b6260400000001a0642205ea400000001aae46ccb89a35817e27eb41f08dcf296e1838000007100002aa0000041a336a4b4ceab80cb19c05b648db22c4235a0000000171900003f10000117926de7af8817094627167d642519543320000002ed00002f1a82b4d510b022cda26c4c50123d20d068b808000003b4a3d90e30834e15d211b478b00003a580a742228fee384429cd1688365219882c4a56000031d8316cafb9bb6007a000036080003b0c0000cdc993304743b94b23816f270253987ff8500060669f8f7a841433364098730036d2d0e2e9c87509fe2a7003c03e389dd46220dd51b093ed248484e0f7d8c353c725788684090f3954518c0008aa60570667c4628750305c3b109bf0c7e25c61b34dcc03c607567fec05b1d3c2a5c003858500fa30f40a54a039dee015c8908d53058718c82c7444d14f01be414311239bf708ae187cdae88f23e26174068c963a096a83004ad853919b81b14cd906a826dc13ac0001e0620e481489de00002dee1ef0a6d9a522e02408c468893f1e8062745e70dfa3308483400000001e8c2504dff864b11ba2aac70501a32d7e0e4ca6888ef38b88f708eb9c9e3f802b94adf077d3ab800002581a951bbe412861204a500001bdc2379607386010d06cb0c1a437c89ccd13810714980d590790bb700628e9c7ed951b3e7a8e087ec03a811104ea835c03a6431a23603109826077
  | 53 => 0x3200008679905000085a400000000000392c3c8139034f64de000000000000818c000187f42c45face760df820ac0000c1d800031e464c0d67800000000000f588a3e079a31dc2c41c48183c40c4d7c128000003cc05e3128600002cf8d66049320be11187419c853a0c000052387f322646c6c0000000259688b40e100e0326a3818ccd03470000430c04f8cd108984180b8780001ac641bc865120f363e000074897aa31548e3cb3c04623afe606c60a0aec00001858167800015f41a20000000000005be0fbc0000340815e44a986242f4280408d711f930ea329c98f9b61120e61e0b1290930374632459d219101984c9040d97123ec07f104b51c4c253e23ec0000e8c420c67fc7260c631ed8446c8e901623bb81fe80000000108c8498c7a171e34940be08c71de1351431111969d3708b07c18f270966325a739cf11100b0c3630f50d299c3407849b82b38f3e0ee41ca4c381406063247751e01708367414c0a260b601f5876a459e83b241e06dec5f280002fcc829c5d79d5416840a58137a2e835f832c8581825b1c866e800000000254680b884817bb0afa4c3493aa2d01cde46c4cba92b645e20000085000005761354d2c80002f6821b0712157f14946064e2822f0000030dc5930eb11c5252404bb9c1600008460def85bc442888ac2238000182455b1110961520ba76ec0000def000000003908ed947167d608e60c930dae7c5400018470c16000000001e60bc835a44649944174237185430fdc29020000c361f0a00001e5d0fd22ea000069f00001dde143e0d807270d8d0000506086d1a6d27564974a0f15902052569c4a911c036708258000000000180000e9f000006b2153c5f81cbb29865a6ce1d000029ee26a8000000043601fc02d48000127a05a0ffc9e2c2a5024280d0062600007bd80f7058328ce0408ff619fd45345fbcc609b2c362c00011cd1bee064c61b88192300000071b513d18e71004000040ca3a8039820c8d31024c3dca22907891e2a26c685b077f80000b203fd4fb91b35189e0b70a5416aa426857d097e0516000000001be000000006de4ee289a9441609580260ce63c9854b091b067200003598000014c0e8e13045bc9de5286c0000ab91874370439910249f4b453a33102ea1a50043e09b0fc38d9343141ab0e6d8c5028544b74f7e012025e418f11309b25295c228853e000009a6000000006370278363032e8ce32f6209c8c919b9723863e94ac414252cce0a249ce08553aac3198cf898c224de614866112d4002808fc27481e70da436f80ac0bc10abc785464f16b240887e7c5bb04a42fa289791a111e20b8a515c4f185e93f0c37884e90dcb356e293cebc0b322d3c2ed4724081200dc88a4000000038ea00700001c513a443cbcfe4230816e075607991eb641f68e4092c9d7d00001fd0bc
  | 54 => 0xde80000000565d105223d01e857f8f0980003e5a0000f3e1066066047b80378000267e73f813a230f01d235810c483c323720254bbd8808283855c4f4aa09406ba34cc42c80003b3423680000982140c0244000179e3f080000ac89807078a4bd110394f20e9c0ef016d20f107c00000c4483b323604c3c5820e510d1819e096c822c04a8000000007de02c6847d0b3800028820e9c000214730146d9000003f1000023d83e00b4130485be4f3c957307c43ec00db1139384241401639536220c0000fd611a526ea64b80001cf921e8091800023182f7c68f493ea17237d27544a360481151a57a042783db02022bc4ed504360bf68468abc0000334433b80000363414c2ef8477186700e8098c6e10af6145c001c90d21b23644379c79512f8417a678cd71126d0ef60e502f5080b446845d490302c640ac58151859bac0e8453e85fc800000000000261800045f05b34000174816ce105d0f7180c215a2dd46b796c318542218bf7214c38f863611dc19531c043228a898919380a334c00023e2326467d475480002cba05380672371128600009ce99c2277613500001fc109901bb465da23618be348517a80001ebc52a40001f74191600008fd8f7c39b0000062a944e0000000009510f02530262c27da25f000085980b4830821b228c4c750012079805f4132800045b05738cd213f515d46f28f4f8000332605b0c6f0d50000c4560c6ca2231cbc254094b14ee00000000851069b343e25bcba721801dd21214653060d000052d0e758ec63bfe435800016a507b472b09560e183c9214c4be90aa731485000ee1024230982acc433807200003844f4e03b1237e3214472202a467e4780000114909567d544cc800000001ce00001d142d725b70d2a800035ca00003cf9baa2fca20d4f9c9e401ea04ff00002135369c60b10718aa1197400000000cff22c6000060d8000265e778c519096120744304d3d0d9e112805e0e0707e61d7c1f200a8185f1f4e23f42480e2144a61ba0eb8239132408a14dad00000242000055600000000502cbf4871600006ef0fc0221d34be5970309873b00003a3c2d000251d8a0000a7a835139b800000000000397822e8f2c0d593fa003c4000191904bc000103b90fb0000346cd401a58223c7cacfb79e3602c248291e5a0c30d324160abc8ce811da4a5072085764104490c36800000000727424916d00000151c90b158e17d2106504e20f600002ba0ac2893e2f0c0000a2b01dd23e624d469d0e3e31427238e3a209100003fc0c071a8b259404e4dcc9a9f370234dc4df03801a9e6c780ef8c04400277a49cf0dc500225780d7a95ec07a6895d03e1aaf12585ae096622dc44ba4960e211d382f7e806464e83ff0bfa2214f361d5b172c103087f964e09d822bc9e4863f37ac396ced80e472f6404444b40ac605
  | 55 => 0x1ba695104d0a57227c2f550f01b1232744dc8f5080003c8840c000005e000005a64eb0230a40ea804c9c11bba466066290b2952700008c1cf4905a23bce20f837087eb15200000d24000014b4074c89f9cf500000000000142e0000629c8e88000000085b4790000000006540c69800034ee7ff400f0000294e38c831a000006140000000000000007a4400009f9000050f4207000000000000e6b159500004d1cf05185010ca7a74d3294ff158e7cfc13d10e911cc308457200002c5208a00941809162400001570e361bd0075c0238000357c4af05d814be0a840000793946f00005ad4000132b095c77ec6c3890631e02aa4f2f000036b649a04d793f605e40facc798e4a18e20e9094d856416701034bac1e4f03fe85d0a63998622c8440cc5895ab30b8787824315e312ca1dd06af11b73e040c1c32da3b11f3e34c4be40d2015e0362c99c99f8134e35551e21ff6000078640002328449e0000000104e429a27a033e148e034a8d80852800000005e9c000037d348a08e45e80d98038a0000e58231c27e264fd047828e0812000020d835e1ba680151b818e4113277748128354457c6d1c9f995a510666ed400003872dd816342cc17673cc6816898390cb09ec745824387e4000059587f90fec371621408bd04ff0d902d70ff08ee710446f1c53c0406354e116c00000000000042d1518c4c0000000000013260000590c7b8141d28a01a8c0001011077040e02e7215a46cc2da8f900a960f98825cf298000031c67ecd9d8ef841663b0cb2900001a6a0000ecc00001c34297433d16e40d42126116000003e220000c3f0c3805b01ce492b8000192273311d8159c025c000080c0059000077acbc6168e14487a943f89500334262ac50e953d0aaa000000010910966000000002a100008f84b4e0000001a647426d0a8e13b8628caf7234c053c1254a8e8b25232453743860e2021e410110d504ef11f83e98a30958932da73980000afe0378314c14b92543f960410905985e2e722760bb28000379866f888f800000000000a4d0b4939ec229c00013532634052482400000000000034a0e9917d85abcbb993a908700914489064522480000b1007d708d2704cf6e008623b085cd073064c000051c46a48000009e00001139f8c33c2000085d9bb2392072104f11b0135227f58bd1019e0c9a6fb0be19c470000000005180000000866106e14e8157e0000000094a10ea00007a78c191ca06fe800000000000697000013963df0344856a9f9436301d68c921d9d2d66336cc4681b33f307f4c4d81ac005c85d886619e12446617d515a0af32cde20b003309e42bb621c09c720a9401a27305681f5f15ce268c4a59f1b1c5031e802b93700a042b5c18c16342d244f4d07115de0e003c6cee08b1535be22d4a8e009e2572507c44fa1d72fd00b304
  | 56 => 0x470f2d09106d087940000421a0000f6b0000000073000000e0e00004c881061a0500007a5000b828738de24380000efd2c3c00011ec8000000052788e214cf00002c680000300249e8550d499167000021590ae8000015e0b9c0000068154000009818af700000000000112a41a678e04fb8eae0bc66ab0daaa32644d441f04958d9b284851b903889f40a66629817b97ec38ee000111ba17900003cfd032a0c919ac7c6813b88483aca6b50ae41ba407aa0d98e8b8af438d4635ce38830939044420e9295171a9c8b380000bde19bc596c9ea9165367a7b90629053f246e2f7079e8a0424960000655160809f23ff41dd812f4236509800000003c8e7a986240bda000011410529f2c44780cf40000e161d30649c5578281264034f8c6d16743e948b6c0b7053a33aa81b09a08c4a2908000000000002ed4000053889c31b680000146800000005150ec811cb3f0485389f5800000004d0c57a840316583f1908901d400003b3cc4a123b027419f43e89e5c2a606a64e16986300004dd00000b8b46d80c4c3a00c6126c400000000c333eda7c3cdf20000293883a800000000e8c000084b9bcb19f26ae42ce835311e80000e1e9b093fe41c989950fde277c75bce6f9e3e3772340027b8de62ee42a08c25a24d3ca414f00529428215e7fd0b1593b427ce67b0ef6973100004580740045a000028b0e39800000005f6cde799e635a24014f6b88de27f21cd810d8b4f000000000000d54000000000001b31323800000001e73000000005b202c000b625e50cb016d4144561000004411220416c00000002ce60001107981f000045e11ce9aa4000025f40c58ca3460256c04988ad1000055bcc42a3e3006652304aa162d10fa000010a9ece1234542c08299492c664bc000016df0ce247a40000fc2000073bce089d8a45087fac69121d429a017b80da1a1d3f244b009220fb812bc5904e0b9bf441aa4e2448880e7136c096898f03c02b0c4150bd71c933b923cac93f83ad1f143ac113d9284424e73781ef93bf1ac8060853086252e5e02f4b541f4f2e40038c77d8f411c1668840000e9e1d480b7400004fd302a10dcc8d091b288e8cd0aee0b2836040000000041605fc000000006400000095c00004ad00000000eb68a6e3a0000010d1000000006494dba80000b7a3444000114b2432668cbce1e8f28045944876864f00004c0000000000236480425913a1221c000063380000ada5b2ccf1075731162b48254016a09f43b041ec0000287e3c88d9f012d262848a43aa0b2e1e4c50a415499b000006d6502e93c327b814f400019d0000064dcf990a8b2250000097480003dc000000000dad32c00984b3d8eea08c80000d179684469a000000000003006320903400002cea7230000019b23ca4500ecb85ba00000ce4000071f19ea00000001bed2
  | 57 => 0x112a551c0ca0fa4426418f45db147509087cc118487d308141388bd18abd3d865dac588000009c22dd018d8f960baa3730956841509a077c000000000c8e89d400019bb45cc7ad47b49a53253a60c4ecc9e7b372849184118ed533686570f57819d0796775423380003efe7e64dbe1b4b31d20000efe20244188800c35101ed001e2dacc9311570f922044000116200002fd0a95a04c296a3ff8c389e3c04b214a0c9408d717922e243dc226925c831e4b569c523338261c2418bf818b2497ccfd07e931de673881b0ab12fa816b000006fc400074ed0e9037f44c65ff4b5e12721a982f8d0ee8acd10d67dad05c9e72335e000017e0cfe0e5456802d596d7000000002220000045e0000508813500002ca4000234500000000b76a08c0000460c95a9fd400008238879a31a40c80e5459080002a721e08af7819908b27e40c831a17000050cd18319572fac10fc1f4996c17668f680001e762c78836cafc800021ca1df04ad0000427240d4a8902b31e766facaeb0fe91c620c810859e2b26d865284f7968d11888e1000000002c421c6c5830bae420677e4d4717ba33b64f5cb6a0b3c2e3e5a400000cd22d2813e105d0fc81996607491c088e3fca6f6494f1a1923820000d609349000065e43dd897b3e4812643928ddd1c440e3d1cf21421f6c7c990ee067537ec760c7529ef02d9c07e519100d413ea00001e7a14b00008f30505a045000000005219c7205e2421c2bd0ba20000000044522b90efc78b40a89a5e4626194c78480cf03500000d0c127e244400007c784df12ec00005359ee239020e30bfc99d82d3a74c0ec0a34b2fbe57311a3823024c821e4f4d800015120fccab313b02a8c1530db291aa3a540e8892d1249000089e4fc5231228920000f1912340b1e00000000000018a0000e2b0000462e343103f805a00000938d569a30297488685be9540232c08803841cae2612000051d800000000468b30077840ae806c4e50b9f00006124524994b000068fc65022bc00000000000092411960000e86a3b900000000000003700000000b8b800028f273340d792fe25403f04f6f84bb0b1406b4000055221de59dc2e207b532c600008d10000004e000058f1a4c180c000111f8f7d00006bb8e842098115a0000eb204c521f2450466706fd2ee209d90be214123a833f07a107be13c26d705a9997c40087524c498ac8244a259c3a182fd3adc00004c51d0523323b888421b9b2b760c90e2d063a35d6000000000000000000000011ea00000000ff11ea81e70000045a000020c880200001e2e00005e2515a8aeb3fc84d3101d80001c3e696c0000f5806f4645c00010e8000082f8e520000000011205df82eb0000000000012dc000012fcb4a80002992000000011ef42b68b50e1280002c927aa8f30094c1c4e000000000003a2a8878
  | 58 => 0x11db17f50f264ed411215ac3a06598457c02622ffe3e8c0ca800015ac623c7cd0cc5000000009588bf5032638c0f5902263fb8104107c098c08d400008c00d7608b864242aa008f383c00010208db546be00007198da42f7a209047b9d5239e867b909701571e6a2094ba78e4504546448a4e93fb36d832b83341a150d0e273cf250cf6113a45085cc04a60f423894f5682c9459855ec1fc8ca805a42ff89d686961ad07e545040ed304786b588c482480e3239e836d17cd1ce20700a7585f020925594a3686841be0240807aa1ba28d400010ec9f3e443234e05678ab63f7a720c0ba1c5d1ad4049c000000006445d7c99a9ea334145a6850a8534260a00000000b34000000003fe9e78359c1eb8000000039f634740001fb83d108970000112b3ee20e9513792de026025b4000068d06f06630000000034de0000000142d27341be879c8c54000043ac6bc22060860188cb918000198c157d14015ad384c55445d51679342c54050e20000306662e868d20e8124c6888000000000000000ae08000000021780000fd72e8e71e88f41e0e2efe1460d8e98ed2bec75840001215000075d4d610000311000000001f62000000003a592af401c0a141338ef41c00372400010b6299c6544000000000000000000097f24460000026800000000000fef9fab24406434b0108051372103cd07993e2f1c5d70000230400000e68644000000005f90e8d9a9e00002a482e68f9e0bfe15bd0670cb1000007247de016b2e8818a906e80b000006c1119e91c814ce5b686f19ff112305e648cc044f077e0000d528c28034e08ec00014f10f480a6cfce8b7b00000001181918d31445cd4d6d0e1c269e717cc7b099b361a39fcfda9dcc1fc80f7878b973d1cb44ca099e833b22700da070817ca1ada1cd400000000000663917e91350ab00dc05e0144228b20710ad5000000000000eef8c2c378a4ddc1e1226431b80000000186a1138011908521a90e061e7052e09e6183a2c604af988109fc2671146152647a653bc96d1e010d14451c1c68edc27184674d871d6b27d240791c08000083c0ca80000eec0000060c00000020182000090a201d0fb60000837227600006060000000039fa000100b986800da02f826e1f5c3688000000006b022da6e4c82200000000000068981d80c2400010e594cb1e6e40f51eb207a0a8a47f05e69cb215e46654a16059312c400007559a6b00007c64000015f26162948dab97283b04854886c1dda00000ec0ff78480080072506780cec26b0677ce5989091ba2102cfbb941702903918079a22a45921614f3506db1b6465a800000002dfa46b000017ea479e5d3465c96232ba60000d160f4a3a563ba0e199ec238dc0840ff404ba069e49ec2d7002f18021978045a09f17a67e6ca5d992b278e65c422b0ee60f944ba8b951681
  | 59 => 0x21f1268a07029e261ab079a45ff8df732c8364867696f639f84e282ab1d7c054054f0e4e03ef24ac2b78e501c8d2de4097ccdd0f8319c46df4aa58f1c093c2c8901a0fbb10f06b1063b0ffc130c526d1bf0b8f380e0c30cc3828827cc8d183a29a560b2864544a48bdf03ee2ca907f962e1a5221701c709e019b43f3cf6d05800b2c363907998a527805310e7d1ebc34d078f49b8a2b13e2c1f14757935a136e3fbc5b1183a157278d03b698c033c065d900f09322472137874a036904f86d7cca7179837d016ccf8802523ddc2df9096a19e22bc08cccdea09d139633d1049138f21a44fe04daa2000b4866486c48fb42a0489f468110b437ae28dc53a879a2018018023a89bc064e011400d938336e425cc9b48a9d1e928eb429b9781390c538c19f195f29c08e010811ebd422e85bc0eca19f2f56102041e174a30f81c1cf80150720540d3414818e8320255b84679dbe22fa16a82cb948740c07f98c2e8532290a0c14c960d3440967b00ca39ec8193069fc1f18dd93b245578dac155339d220349d40e15085c8620c13846818ae3080d79942225cc2484a6406a0241c21a4b4b9b3f15be104c6cf9f36116e1c38ccb8000080e19f800016be20100001035a1b10d48325c0001265000086386879f660000000037808291ae000010ac800b1f3600003478523024c4ef51679943000042a8b049a8c0e1e1dfd1e0821200008728000150435aa29d8b931e571db469840000442000670c8af4820416a082849f9192917a853a81eb2258087c6a24e2204fc1f86200ce1d8ad8182c27c8e1a0c0f000006300e7a3a302a40000aea85a72dfc000057e02a30dd60000c9b0000000030448bb812c0000000072486bd3eb600002d78000000000000000000476800d00000bba083a00010bd16ca2eb660583ae800041160000000150d00007070cd500000eb885290db1f8835964f64e99a2602a7636c4c14977c45e676982f09ca62f6e4898000020328e82b0c0001e033cf45118f3100003e2868e479714b016622e280b020ac292c03240000b711fb41be4c1f9f8b366e2d447c69a8d26382a8840b232a0ba4176c83080003d8a0000dc20f841d160000eba206200000000ad714a52de678700000692282463307b9000017cc000012881b022343548d3716223a0802e10ce92c927320000e40126700a45490efc1a14211e0000000000005a2000093b1d3a30a6810c86f21770d3c7bf448e05c8133e7f3cb998c9600002a30d75211937b6739078a0e5906e81aa8f4b937f40f2721c67d8cab2fce4c04d0996b036e80cc4f1986ff0c9200009ff198200001cf02089c180000000000009482b668280c21a182447408086408e6300000ed800020423c46198097d9b850f5213c4f100afd412034f0fa4888f39ae08246ca88c234e084f42df1e5001cc4f8
  | 60 => 0x1169226082acdb51b6d22b68904f97209b000000001050000000083a400000001efe55c037a1d2e0fce64286ae0960288a4f48f928491144e5d905f508840000000020c1cb600000690b0d011800001fb8ab58b051de2000059a85e8245e8544f3a0000000000000001a25000062e48ff848236827ae890f1b4f142e7020008000006aa5bbcdf18352079c0000000154e000001d8a8480000000117cfd1000029f02000a1f0d9000006f5440380000f1c0000ac99f033a027ba45b406cf0a406e3c51b156d272214ac0f81c63097831044fd9d193dd81d340fa9367328a889d1c290ee28f87fe0bbc800010c64de46cca2a508a48474aa4a1a300001ef41a48d2a43a2567cae0127a42ae1e885fd126c202e000016702e536784f887768622146000000000669000056a0faa03fe1bac60440000a350e50000000000000dc6390012592f34178660000000003210136489a231f073e00004c790f1352e1d3000014520ad0025061398223c5e1c88272852723b6286c7db800019ca453c4170082030a29e88ef1af1375c3674bbf0c89262a0e40000000044962e386e39d4c36f06328b7a9045255c62541fd80000000858c0130f003af62ee03a5113b016a50c115611f0405675e8b1500003936242c27a8000173600007c580001424000112c9d6a000000000270e5500003b6016110282a5248140e81c6509527cec8f21a3431ac374829d98ae14b61eb4fbf1a5d199007c8e298c5c37766e209238f5c17521bd4a4c9310281c1829174963e000056f009b07df2d9015044d406522bd67b6ceea0bfb02806f8097012b309ae410c2309f3735104a409d99af611a48aac1350561255031b86d10e6c119448b0652917e166028a91d00000000006240002352207e3a1c45e106900000000cf580001b708b950a21c460da834d8000184824e25b945f90f253a8c811c7e39ecb2eb425700c897c000f67a4c558083141082370ffe22fc222a6a70a7d92832ac81180fe6063628c0407075f8e9c28803e6011895991804076c2589f4e0b2a0c7ce1c925324c40120d7c89373bc85bacfec8559450420ec1c50eef44888754cd69525214e828ccfb00003aba72a4c1ba095085a0000d000e6b4378585c0000a8400000000b788c4229241138f4620d03ef42988382209e30c21728d0700000ed45c30baf0b593b6407f4000000000004a8452f21a00c524e941fa9df73ee08f605a001a900006938f450a0c000018680001c99098e2fa1146800019003528d8c83253caa51e000000001d0200003480b7c1d4c0000d34932e19c21b6000018912bda2cb484486df1e1a2e68e6522b220844e206bd800015b846541bd800026aa75000560acb2e3668404869eeb10ae60f03c58571323c0000000000000007998eeb04c01b1e2db026589742b446f9c91f22a
  | 61 => 0xd0448c000037906351f104598aac80a62288340d08a237430b64bfcc3c8af9118e1510a321bd217645530a00829a1d1c06847641711112e313438683ae047c1bb8f2e84e3098488d4e659e9a2608247501c16e6106c87a45131738116068c4cf291fe0a4888f87c29c37007e088c5479a2311626a1492e115035c22e8c2ae92db17720000b7d0216000073fcf5b991046da62ecd201f972c90638c000000029662d540001c01301a0000a531fc742d600004079fa935b04770d8307ac000017ac00019b810e84e5cfd886d943ee5a582a523752d581d610ec119b23fa3aa000019e4000000000000d9c11462cbcdd1830f0e3c728c89603972a6e14540000000214c5cd10dea02f000059c010ea01235e8018448f1b0705586ad05360a38395a70402ee84120cac1f382328ec0045a3acc0890e72039c5b589ff817f0000196804e155a2c3e1ed8e61814a16028f18273000027b6000013f8000368a24a43cb0edb000020710df873125d65a280000d040000109c65a90a1000022989e400002dd01798b9b11a9000072d40002027000065cc000000047a01ad0e509047417e420c000108000008f34000047c10a454c8217800020c65a4c7de80dc000000002e98000000000001089de0431e29fc33b92ce1ccc13350eb1521132e27f43571a2604ba535c1cc8817348c42e508402932a2a203100e155d41f27d0c30202fb23947d90ac680000fb00abc618190e0f245e201f3048e2d7a3d0c025995e00e00fd8000199008dc48fc665183532ac615832517d53d200000abb0e14266623e4000086007721cf91a8800012680000000022b14500c68d7e9f44153642f4f638f0f46dc1e6cb1b11ab2d847bdccdb9d8514cc43dc1a09793298c01247591024286e478400003ba36e20161058061801b00000304000036428dcd1bb00001ebe55d486a0000000000003e580000878221d0c0800009e47ba115701ae458a1230e2a051c00005d583638faf00004d580001c1d2af47b98967a1f4459a3dc478f92d01ae24dcc992800002b44b60734172d054c5ee0a0d962c1eb208384a220cb434c7740bee21df18140000000000000003b84000038816f44b5c0000000364c00006e180003422000000000003d0c000000000002a46379400015b13c101ff0a45977040401f8c0000d6525c44204000147e22740000db3800000004004bb19ac30000640ccea1b6f302630949090fb91fec7e946dd06fb2db627583e81d683b3c5ba49a29afb215c2f1006381ca116481642d418281e2045c91e408422226000032182b705da18b800022501ece0000d0414dc3a84439068680000b7208882ef800020bc8da4913800000008e6d06c1921380400011cb811520e8000114f000009e00000a6698593b3622ec0001a9d00006374478835000d682dc28d8000000000
  | 62 => 0x898def22d644902455150886e16be51c8103895d233c18404d2011c36bc6bc0a2f95481a0e207c692955220ca820403605fe0a027a1c09e9dac2fe8352c00002f00c8c71290e9986b322c8b7425391370f221abc0000b81420a3210d421e5900008024b4421682822814c0000607084c0b50b020a9f00000438ec00c1f3418525c81013ae33e40e188ea8e3c0ec40388baa851735d80a607f502600f9a370442990411e1852fcc7121ec1b143fa084f821c11261268bf99f011b6033003470e9b0a58537803ba1ff11ea71fcce617b533828dfc00001d6474207ec9c311a10b38147c867000000000000000075f3f860000c87888300002f6cafd0e420f10675c7c300001570488431400001bd800000000000000000000000000181c78fd1d5195546a03dd0f9490a9068c27b00000e9a3a3e4a90fd38d44350e57d50b70964216e3b2d1949aed46908cb0b98213c00002b5000007fb0a440000ab00cd941fc079506400000000000000000000000000000000000000000022a8000029e00006af9e090df00000b908154000077880000978000000000001c7900000000ca60a53186224111ef80050000000033c93ca066e84d80000083000039508ef9aae0000563000013d42c6065c8000000000005d98000000047380000d6b80000b0c77c51a487111e0e74405ec000000000001163879d2b7a22807c39466317000003779958406a8ab4000051e41545760000000034c84d001372209432807a870600001fe65ab850c05041c08000107d167d40648ce40000000000068b447f16271ac28c80c7d15771e144b208c31b2e3fce23187018173000015685f2000000004a68b881dbc015061cc0001ab50e5e8f080000db70eea000098c0713031e8cf8d4d0ecc0000000000016ee32cc0b8c0000000153837b8e6914ab000032d119c1dad00000b1400001da25523334ba122e10d8c2f28de88000426e1f105228deb2ea85dd00001fc600001250a7a155c0658000108b001a23ea8d78e5c800035c803081ae000021ae22b8ae301922984000000006b1000000001af93df41141fdc000010c00001a9cb3e1faf0000000000016cf3de65b00ce2a0743d6000010da8000262431c02b998c403e628d071580c63e1a839424d8868124e1f840000000386c87a8a79936800001af9066a1e102645244b018f4c36208c14d6e866a0000385c14100f246460000b0580000d06174483c96540ca2642c0001a1c32d0264c000105c18467914ea69e8023ac7cc4bcd888139e63168c00a0d61bb0673ca402368395000000d520b445c82e10000206f000019ec38a152d02120000f0d9d27087460d000000000f645c2d1c18000000048c11aa8000373a0000ed4085f32d2680c00000002eda7be458f860143764a4514817e100000000fa8a1e6361661140569c
  | 63 => 0xc7b000035685590000355420a10a4800044c400011df0fe0454000003a89729000000007818000148217887bf13500000716c7008ceb00001b008d01da03a468edc507203f000036a480b1a370d860fb4eda9c5e000000000000ff112dc000073501a23570329000007f530c845c041786542cc6000073e007a0000000011a81b140d252540000a94153208dcf1220832f84127d1c5083d06d62fcc38d0b8515de19ac6920d183c2872acf0b11ba251a6ca0f38a10f3efa57e06db111419f024d862c114c309c4e4c4c88c8e000031000000000242e1f047771ac647aa4f38ada1d1800521358fdd0da60f84407d14c80d72c7e71e0c75a10433f851203b58be23bcc47b483c13c4023e0b640001bd300bc050c000000004a6854101e9da323640188a861b5600006acc1730244000038748541e2107b879c0810954f00005bc0f021ef215ba0058bc2a0d9124478351ac8edf3da004201ec9613278205e8a8c00a7261c5480d681e8d464e498c3ee83ea013a207909181251ae85c7451e1db707a07cd015e873d24d649a4af0842c01187b601ce15d20fe4792c0bb92100f3c35e4099a10027624e6cb2c9f6e32a454c468f87aa075835fc0001bd442bc148425a227828402c1cf188e9229b03c380000a5518780001098945e0bb276bc55da26600001a14a6b000013e6341882d1b153d2c00000e097162caa2fbd187119f000051950330876368c8654ca080d1178e0000000000019180bcc26780002d12226c5d00ece142600000001724258e49f00002337242637d80001f4737380ed0000000023ce722c17f8000056029d0fdf813f000055a4e5100001ad81d80d951abf418a00000000a2d27a250e829291560a8632685d4196b2584168400000ca25dc1fb400000000000000000011bd30243a58c6f93b91070386c2119a4d4324239401406d63a12000113e0345031063f440c17770ae84ad0bf69233269000006b703a92f403de008300a00000000051014b100fe4c8400001530000471c3721f561e8831a908a841f41ea7ffc64f800045846db8f02939f03000000b5019621f040000c8c0c2e2e007e44000174c14ca300c1c9081312065eb08be000047bc123cd5000000aee6a40c6d9a740000603c8c20c051a025f04e3408a10b342458d149bb0221e0a509aa0e440b8e82c87858a462b86866cce48e4f01b285f8ef607370c3c8640ce99bc134ce534819996422df80020a1a9c3f31065488a34000005567e9047480003a04000000020ef346c54509d90e5c2ac40174a5c0b7340da000000018d4329a528081d938d3ec232cc8381ade1fa03d8011093083be8000115c05f437845020e4900c844dc7f2895f19742aaa326c92296d125fa8058edc15101b665d4c38b8da80dce79b48e801b8050687e0d590e67269a2004753824f41105
  | 64 => 0x52bc95d15c41116072040a146224c2537c3db83361cea89a031897e2229a579c4fe03b546a63fe4b819d4b11300edc6fc8ed711983e74dd39cf83dfe3e55008948d00006a3c1ab997d0c0a11ec00aa35b211c7ce8000015d000000001d78000389204f8c561f332e0e028405880000000310c00000000fd833544710000025616dc1540edd000044105fe9d8b3d683bc800018e50e9247e0ca78dfd4530234c328068b000070e10f295ea25d0577d1289ec427002f64f8921c91706839d03909b800007314ee506dd1fa4000000019cb3d9409e03968b0f1e6624e400017fe2dc263e0000000028fe1c40f8f800000003a082be04c61c5e24e846a969f2e126354d5d81842c962850566019a22aa0b5c00e80000000000029f18510a5a1e8087b0d17331e000105a86b3281418ac97a923a3770078400008e71eec56846d7800008cc00000548be047d016ec48f8042457e5f80000000018e80000c3b8c6c00003ab080d0000445809340000000000053b03398000000085900001e640000000000017820d6e77f40f0183e222429c84759b2b08ba4254feb80f92cae2e90000123200007fd4ae89fb43b121724fe295e41e0c5e582a71def24501ba900389ab2be466cd0911fd23c3e17048da88823ed8767c8b4216122b400000000e092674000042c02ca109a6a18091229c063a19b838e83fa463200000001737000000009bd0000336c0000153800004928f9425c1288300a2d6c459982f050000010c293ec240e4f7510f8b56000000000000000000078010958d103f1e28040000000000043f0d3c1c2705640000000000008f2000000017b347923bc110800000000609409a145107e4187064188343d587b9cedf8fc541505940000096b3e9a42accdf85a6000087bc7c8903910123b450f68000410a0000b0c054938504cd914315a93816000000011f123a60000bb01b1401d48de471b9dbd1758394c24e072e39c205191630d8102ec3ea8000084330ec419d1778f923e3a000060c13ee045c00009459c24438c11d8e21a02c0188514c8850000106e6eac2e10b91374c61bc7dd16161040030c8011009183848c45079f07463a0fe0fd5179004da6808f66026817da44cc897a25436cc23e81c59c980dec37fc84d234145e8244c93509c200004fa02f29d6903583bd43b411cf0e90857c45b104f34785f191ea1e3a3b185dbc4f3904b125a8a9c2fc0d40119c0cbc5e61ff0385e2cfd06d172715f61ae8a5e9d2024bc51605379939122864a90b009333eea036ce8e133003f40dcc6f0228821328160739989939aa02c82b1995407e88914bfc031c3f122868e2c8018410e44f01e9072440ce82344d721b42b942d10fa98fb338183aeca2d8aff2498122c05511bb15c679dc5628e760000224519b1fa6056c3cc430c9e8917a41144ec88
  | 65 => 0x90c842664a1cddf0d721d3e09411028cf100007190c860f68447627a405209f000000000a01998d335c49340002197181a00000000d2e00001f5400004490d4c07bcda4800032fe3ea1026800002880dd80000266118088b858d9f0438622af800010c221fa3fdc7df099d06fc28e4d208ef70134275c4da2183000000000001d8708646d8c0000a2123040000e5397e3162e0000d09088937122ad0d5090c92a142114af811ce00000000ceb1bad117274b45380d5d19ae6774930185700003ae862ea0552c8c10a0b349fd50000686d17194b9021a23a8000000022f641f817a9bda000030e853d96cc000000002cd9b20468602140000e85000000000001d1134fa505500a15501ec487205ae9d771e9a21445258a6801a67fccaed0e5d000077f87aa180b000000001b7000000007ae501d235c000000010759352047a8be8fe497611e685774bcd1359466617e40000ef9127800011c30f7b121846a116b8a0709c0793471d820d220e45b8d3916800000445c0ae08cd3df45b1c0000ae241127a3800009d137b016fd1aa078a000000000000e07288800005a6921f08ee5c1438a93951d6e0000e78047137ca0000186a1b9146673dc00022170000264883896ea00007198f70800000000000e5d00003e90445800014ca0000547cda980da30a8000094907651c681a5c000000020a66ccc8a19df537c415fd12181bd20d80c48ed89f7c0eb26450a029c060bde43444978e843a2645c413e9d0a147400002b906982098708c7ba948201de8a541a18d3b24a481cce1581ab1f566fbc069011927ca0000d25844a182a0ba880a078c35284bb01a0043942d4000023a000000000000c15136623841a44fd70050134c000000000000000886caea0f5111000000000000000001970a70968b372c8de0fc080001eda024040e993b35782404da500003a3a4b94a591840152a893853693d000120a4400012a5332c471452b2002013648f0b86a2df438a6a081f21f46360a6320bac887f157400009939913000076203309b2916f06ff425ba0fd08665220000051a38242f5c63a8b8825a24d7c0001db6092e28f400000000000409ceec80000000687913580002cd8199800005c03a6a3c5465ea23814c0012817095413b4e00008b580f8000002000001f683706323c7d48de40000000073800003fc00e0cd651ea9147e2a0415c90c53dfc615464a98b21f6423a07e51a5a20262ccc61481381e9c49007cc9b3923c633302b606b91f985b2509206823de84f6063e137c0de200009c91c76299884a00000bc23cdc0f442650617316c0f04f429a60474a0a907450cc93cb40ff0d1d1af23c34607017c872335de048c69816e033e83d5845ea1af1ec63390cd00a69000031cc000205f056a2d18000036f13ec7b5077d000034881b2c0000000479c
  | 66 => 0x38651de82bc0248000083b0d0526c28405171086a178a6b8000022ca21be000045c028f00004074efb03e741a86d807f68402452219b4c1c000002765b0418803d7129c21ed0dc1ee32cc40a7078c0000141a4318eb9009247ce297d1d6166530560000bf909c0040c000000020d2005c0000df080002cdc5ad867e80003638000042480000000000000020c22870000065480001d1a57ece8d000000002c44dff000024e64260f6f052914060100843215500000170e94197a410015445b4873a00002c58de300002418169475a808a1d2688c51260e792c9e4c5913a23a900001aeca7b0000000078601ad1c35073c69e428e91910a8c5b78ecaa27011c60bb89c2000021662f9cbee8d140000659c000000045140000bbc03be0c886e542d18069000049dc00002a20b8600e04c480000c5a000000021e400000000a381fd12e3867dcaa687873f4058751f3054b0a1442f03b19d0b06b66af4b3f95802a068ef002b0d3935ce8e510281b8a34164861199217f1f1c8adc29700f635b60814613177d32ba128400021fe032e7c78d5b1c9f2238528426e8a6a45543439111000016720000f2f8f550000000000000000000000026c1de80000000080907761e9009c0d2496c603a434c80001b110000000017493d600002720dda0000163885c088100001d4200005c60bbd371c000056c9841028e8e60000000031e242e8000000027440000cd893e141944d08dc91e65211449980000000341a0000ef9084a00002f740001046000000005c300002ce4623905711213ebc156cb298fce151042c42ec1b520a2465200ce045329b42f0c10f228b2bae0c09140814d2b6a5a0856022b342807720ac90a16031a4274a9f80842d2200000001bf33ae63b080000000000025c0f03984419a83d48bc01e0f000063fc83e89ed198e02ec00022c80fa80d8400000002f9c0258e2700000e046cd0b2d12b21b08205434aa3572158000041d20181c5a000007589721cdc38e103d975221886ec48a40000042600005ad100a309a00011b51bce117e3e301d098a813742d8c5bb90880a5e41645c9217d277071540001cd300000000ef981cd08445714000203124906c90b530b4521484668a6015672e801ec0f8e000025be8e30a41a12a00007ec8802220314c800000000bad0000468cbc50560256e7d0441f9d8f471c0000000098325f23030161817033b80b2111ca33a26da0fb04980dde258a72f91b900000f50044c123a1110b8c3710000234037ea00011ca87b332fc00003ed095827e058dc3748e13000000000d90c7f26702340a5b195b2e786258d5d1d310f8655d000019ed01ba1ee8b8c09c90ee622406eb88443dba02cd1ed9a1a133c830454506de021e439c4c696e703e2000028a189c13a8128117906e00480212c44b21e70e3858385a5
  | 67 => 0xc110b2ac20000bd780002f220c5d0ed1a570aa68eccb508fd543ec6b147bc93110fc062d071a8d85065a5bec893000010f81cc07d716ff4582056c6961ffa33a2751c4e705820a0c0000bd8076900002fdce9091b413b60000000109614387024a398d4143ea35d429a8b8700000000fa11e290000799c0000830000066b0d640a7e1d0c27e1012a15600005aace64100d42f08e480cb0000000058003808e3a000055f8657824321f467a030e97151ff01d48f57104d16ca1c808288c36000000008f58000000000008fa02db2c38143816091d914a28e90978a3bf2618626c12a8f3c31ee02887ab95832d0c312516a93cc2c8a39f8d85021a46203f84e9313a600586bf908719401fd6422cf3f10520c6040aca7c8c4500c807a05dd8bb442a6000000023890b6225640000000000000000000000000028782e78000000016d04d6a07e00006620000000000003178000101508fa00000000000438e4afc000000010ee0000c34800001a00000c4621460000072cf789a6a11b20c8491a800000000000f978000000037206a29ea722d80594901915c1eba5f3cc5490fe0400277c57723af218e0ddd0d2048a1af8631cf60839133521178d6c800000001db0e079b4800007258a4a165e00002fd8f4206000c4e0f2899a22b6000079bc3c6a10942b80000000000000003a40750000029300000000011d18560e04fc280002fae24a01fe94d5059a000108e0000000000009b50c2f00008d95070824a182636b81461d533fdc59347b785f10ad44bd8000000000000000ace80210000000000000000000000000014340508573483f87412482376c1cc0cb835d21424ac58000161a571d00a8000000089285fe22770b3c6b1cddb93a714fa725c6288b99278a339c1a5993c1bd475c40ea909c04e600000c523ae417626402c20081478a0000e018ef3269411e015f1fe3383236685cb9aa800006cc0bb718e6313e0000c030000000033600000aed1cda7c2088c187b217c3a20cb7034800002cecdcd050f129e188033fa2e70b2258c400018cb12ac349c0000000089a1ddcc439b6b00860000bca9f0902b246bd09f033a149c31e105c13fa3fd267005e58c0909a42184ae8082725188170ffb964a0a0e0c2c99608063a6409a40e8a3b510c850843f4061445dc1a18a8c99da10e618e0dd099cd042e423064c997711a87f3847980de2b3425a42738655269c12a81c11d5911d88cc49040000000026606ab000026143b9000000002ed01c611eb92c404f6641089106ca2d688ac0a278311000030ecb820854138a0000c8119c721a656600001d0e00003b78000161b467829646de00001d707c9c00002e800000000212000000f00000000213a0dcc36ec38480002fbc311caaf9f6533a403b87041c1a423c1d5876a00003e4600000001611000
  | 68 => 0x9da00004a24e6a185a0000479800001140b6a00002109a751d2e0a950e706c428b40790eb380003120000060393ea2fa600002670000333c4b1889b176c097270500bc93191be2251cb1e9c57378636b0b6
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x865a53580310432ca9cc1108219a54a6088410cb2a6b04420845e73d94210422eb9eca10821175d663084108beeab18420845f7694c210422ebb4a61082117dd953084108baeca98420845f73592500422e39ac928021179ce62940108bae7314a00843f74586500421e3a2c32802117dcd61940108b8e6b0ca00846f725865004236392c3280219554e6190010caaa6b0c800853575106400438aa9883200216c5c041900108eee3b2a800845e7694d400422e3b4a6a0021179d953500108b8eca9a800864e53d894004326a9ec4a00219394c6250010c9aa6312800865653d85400432aa9ec2a00219594c6150010caaa630a800845e73994400422eb9cca20021179cc65100108bae6328800846e721944004236b90ca200219554e6110010caaa6b08800853575104400438aa9882200219394e62cc010c9aa7316600864e5358b3004326a9ac5980219554e618c0108eeeab0c600865553586300423ab8aca180219554e610c010caca6b08600865553584300422fbb4a790021175da53c80108beeca9e400845d7654f200432aa9cc3100219554d61880108bce7328400845d73994200421f3a0ca100210f5d065080108bce6328400845d73194200432aa9cc2100219554d61080108eaea326200847576d4f100432b322a7880219519153c40108eaed28c20086596594e100432cb2aa7080211e5da51840108bced29a200845c7694d100430fb24a6880218719253440108bceca9a200845c7654d100430fb22a688021871915344010c9ca7b12200864d53d891004327298c4880219354c6244010caee7b2a200865473d95100431bb2ec8880211d5d6644401096ce93222008637651911004358b80c88802195d976344010d28c9b1a20086576518d100434a320c6880211d9db5344010c68c9a9a20085557594d100432bb2ca688021a51925344010c68c8a9a20086576554d100434a322a688021559d95344010aa8eca9a20087176454d100432b322a688021951915344010e28c8a9a20086146454d10043a8382a68802199d976244010d48c9b12200874553d891004333b28c488021a91906244010d88c6312200874553189100432aa9ec0880218d1925044010d60c920220087515390110042783b28088021741cd4044010ea2a6a0220085e07250110043583266088021d454f3044010bc4e59822008571750c110043583206088021ac1932044010ba4e7902200875153c8110043583204088021d454c2044010cb6e7b2a200865873d95100431db2ec8880218ed946444010cb6cbb1a200865b6518d100434c320c68802196d965344010cb6caa9a200866b65d891004335b28c488021aa1906244010d90c631220086b064d85100423d3b4a288021d454e51440109e4ed20a20085d27390510042b8bae6288021749cc2144010
  | 1 => 0x430432b29ac3218219554d6190c108dee4b2a860846c72595430432aa9ec2a18211d5d46150c10caaa630a860865953d81430423cba8c0a18211b9cb6510c108dae5b28860846e721944304236b90ca218211d9c46510c108f4e0328860864e539884304326a9cc4218219394d6210c10c9aa6b10860865563987520432cb1cc1a902117dcd64948108b8e6b24a40845e73191520422eb98c8a9021179cf60548108bae7b02a40845d7694c520430f324a6290218759253148108beeca98a40861e6454c520430eb22a6290211bdd95214810c5ac8a90a40863471590520430f324c629021875926314810c3cc8b18a40861d6458c5204316b24c4290218d5926114810caac7308a40863964980520422f39ccba1021175ce65d08108bce632e840845d73197420422f39ccb21021175ce65908108bce632c840845d73196420423abacc3210219554e61908109e2e130c840865553586420422f39ccaa1021175ce65508108ece332a840847a70995420422fb9acaa1021171cd65508108eee2b2a840847b70595420422f398caa1021175cc65508108baebb1a840845d7518d420422f3b4a6a1021171da53508108bceca9a840845c7654d420432b29ec2a10219554f61508108eaea30a840863654185420432b298c2a10219554c6150810ccca430a840865a53d81420432ca9ec0a10211e5d46050810c74a8302840865a53181420432ca98c0a10219a9486050810cd2a4302840845e73d94420422eb9eca21021179ce65108108bae7328840845e73194420422eb98ca210211d9c465108108f4e0328840845d7598c420422fbaac62102117dda53108108baed298840845f7654c420422ebb2a6210211d9c465cc8108f4e032e640843e74196320421eba0cb190210fdd1654c810878e8b2a640854c7254d320432aa9ec2990211d5d4614c810caaa630a640865953d81320423cba8c0990219654c604c81087ce8328640843d74194320423b388ca19021535ca530c810aaae7aa682086556554f410423abb0a5a08214d5d052d0410aaae6296820865553583410422f39ecb20821175cf65904108dce5b2c820846d72d96410422ebacc72082117dd563904108beed29c820845d7694e410422fbb2a720821175d95390410e2ca6a08820865953980410432ca9ac020821555cf54104108eeecaa0820847576d4c410429aba6a620821555d65310410e2aa929882087165454c410432b322a620821c599153104108eaec29082085357414841042aab98a420821d454e60104108eeeab0082086555358041043a8a9ac0208213cdd56010410ce6eab0082086d373580410436839ac0208219cd4d6010410da4a6b008208671535804104368a9ac0208219454d6010410dc6e4b0082086e072580410432ca9ac1188211b9cb650c4108dae5b2862
  | 2 => 0xa4a02218d1536150110caea7b0a808865453d854044333a96c2a02219914b6150110c6ea830a808863454185404432ba98c2a02219514c6150110ccea430a80886645218540442373acc5982218bd5262cc110c58a9316608864f5398b304432629cc5982211b1d562cc110c5ea8b16608862c5458b3044327a9ac5982219314d62cc1108deeda96608846d76d4b3044237bb0a5982211b5d852cc110c68a930e608865453987304431a2a2c398221551d531cc110e28a898e60886c5624c730442e8382639822195996318c110e28a918c608843e74d95304421eba6ca982211b9cb654c1108dae5b2a608843f74595304421e3a2ca982211bdc9654c1108d8e4b2a608863454d853044332296c2982218d150614c110caea630a60886645218530442aa3aa6298221c5151314c110ba0e098a608863754984304431a2a4c21822195d4e610c110ca8a73086088667529843044332294c2182218dd51610c110c68a8b08608865753584304432a29ac21822199d49610c110cc8a4b0860884d5768c4304432b32c6218221c5152310c1108bceb31e408861f5498f204430e2a4c790221171d563c8110c3ea8b1e408861c5458f204422fbb6a790221175db53c81108beec29e408845d7614f204432731ea5902219358f52c8110c9cc6296408864d6314b204431a2a4c3902219914a61c8110c68a8b0e408843e74d95204421eba6ca90221179cf65481108bae7b2a408843f74595204421e3a2ca9022117dcd65481108b8e6b2a408863454d85204432a29ec2902218d15061481109aae630a4088654531852044333a90c2902215a1d52008110e50a890040887485348020442f038a4010221c615053c4110e50a829620887485314b104431a2a6c7082218d1516384110e28a9a9c20887145414e10443922a6a508221c91505284110e88a6294208865563987540423b38cc72a02117dcd62950108b8e6b14a80845e73189540422eb98c4aa02117dcd60550108b8e6b02a80846f725815404236392c0aa0210fdd95415010c5aa8b10a80864e639885404326b1cc42a0218b9916215010c9cc6b10a80864d63588540432ab1cc22a0219958a6115010cb2c7300a8086696298054042a7390a929821535c85494c10aace3b24a60854e7219253042a6b90c929821935886294c10a9ce430ca60854d721865304237390c8a98211b5c86454c108dce5b02a60846d72d81530422f3b6a8a9821179d85454c10a9ce42a2a60854d7215153042ab38ec8a982153dc96454c10a98e4b22a6085547159153042ac382c8a9821539c86454c10a9ae4322a60851f74589530428e3a2c4a9821551c56254c10ab0e0b12a60864d62189530422fbb2a6298211b9c865d0c108dae432e860847571596430423b388cb218211d5d66190c10caaa730c86084f170986
  | 3 => 0x4a60cc9108f0eab06648863854583324432c29ac1992210f9d3658c91087ae9b2c648843f74596324421e3a2cb192210f9d3654c91087ae9b2a648843f74595324421e3a2ca992211ddc5654c9108f6e0b2a648843e74d94324421eba6ca192210fdd1650c910878e8b28648863454984324432a29cc2192219914a610c9108e8eab086488634545843244278382c2192218e15260d0510c3ea931c828861c5498e414430faa2c720a218715163905108beeda9c828845d76d4e414422fbb0a720a21175d85390510c9cc7a94828864d63d4a4144327318a520a219358c5290510cb0a7b02828866852d81414431daa0c0a0a219614c6050510cd0a430282886585398331442ab39ca918a218d994548c510caccba9c628871454d4e314429b3a4a718a21c5d50538c510e28a829c628872454d4a31443a229ea518a2199994528c510e48a829462887445314a314431a2a4c118a218e153604c510cd0a5b02628863854181314432da98c098a219a148604c5108eced2a2628853674951314438bb98a898a21c51cc544c510ca8cbb1a628871454d8d314438a2a6a698a214d9d2534c5108ecec29a62887145414d314432a32e8698a21c5153434c510ca8ca21a62887145410d31442e2b908698a21745c0434c510e48a9a9262887245414931443a2298a498a2195197324c510e28a999262885d170cc931442aa3aa6498a2195195324c510e28a8992628873054d81314431a2a0c098a21cc150604c510da6c630262884f27518131443393a8c098a21acd50604c510ce4a830262886705418131443582a0c098a218c150604c510da6a630262886d0531813144369a18c098a21b410c604c510dc6a430262886e0521813144369990c098a21b44c8604c510c68a930862886545398431442aa3aa6218a21c5151310c510e88a498862885d0704c43144334294c190a218e1536048510cb0a7b02428863854181214432c298c090a219ad486048510c3ea9318428861c5498c214430faa2c610a218715163085108beeda98428845d76d4c214422fbb0a610a21175d85308510c9cc7a90428864d63d482144327318a410a219358c5208510c68a930e80884d573987404431a2a2c3a0221179cf65501108bae7b2a808846e72d954044236b96caa022117dcd65501108b8e6b2a808846f725954044236392caa0221179d76350110c3ea9b1a808861c54d8d404422f3a8c6a022187d506350110c38a831a808845e76d4d404422e3b6a6a0221179d853501108b8ec29a808846e75d894044317aa6c4a02218b1536250110c9ea7b12808864c53d8940442373a8c4a02218bd506250110c58a8312808864f531894044326298c4a02211b9db52501108d8eda92808864f63d49404432631ea4a02211b9d852501108d8ec292808864f631494044326318
  | 4 => 0xbceda9aa48861f64d4d524430e326a6a9221179d85354910c3ec829aa48861c6414d524430fb26c6a9221871936354910c3ec831aa48861c6418d5244317b26c4a92218b1936254910c9ec7b12a48864c63d89524431a326c2a92219518f6154910c70c9b02a48865863d815244237bb2a4292214bdd15214910a58e8a90a48854f7354852442a639aa42922117dcd64149108b8e6b20a4884777159052442973a4c4292214b5d26214910a9ce7310a48854d73988524422f398c229221175cc6114910c5ccbaa0a48846d7695052442a739ca829221535ce54149108deecaa0a48854f7355052442a639aa8292218b9945414910c9ccba98a48870f54d4c52443862a6a6292211b5da5314910a5ce9298a48852d7494c5244237bb2a6292214bdd15314910a58e8a98a48864e6514c5244387aa0a629221c31505314910e8ae2298a48854f7359052442a639ac82922159dc56414910ad6e0b20a48854e7319052442a6b98c829221595c46414910ad2e0320a4885657118c52442b338c8629221595c643149108dcec218a48846d7610c52442a739ec029221535cf6014910a5ee8880a48852c7444052442a7b9a2029221531cd10149108bce7b2e848845d73d97424422fb9acba1221171cd65d09108bce7b2c848845d73d96424423ab8ecb2122117dcd65909108b8e6b2c848845e73d95424422eb9ecaa1221179ce65509108bae732a848845f73595424422e39acaa12211ddc565509108f6e0b2a848847471195424423c380caa1221179d76350910c3ea9b1a848861c54d8d424422f3a8c6a122187d506350910c38a831a848845e76d4d424422e3b6a6a1221179d853509108b8ec29a848864f63d49424432631ea4a122193d8c5250910c98c6292848847675d85424431a2a6c2a122195d4f6150910ca8a7b0a848866752d854244332296c2a12218dd506150910c68a830a848865753185424432a298c2a122199d486150910cc8a430a848847a75d81424431c2a6c0a122196d4f6050910cb0a7b02848866852d81424431daa0c0a12218e1506050910cb6a63028488658531814244335a90c0a12219a14860509108bce7b28848845d73d94424422fb9aca21221171cd65109108bce6328848845d73194424422f3acc62122187d526310910c38a9318848845c7558c424430faa2c6212218715163109108beeda98848845d76d4c424422fbb0a621221175d85310910c9cc7a90848864d63d484244327318a4212219358c5210910c68a9308848866452984424423a3aac2212218d1516110910c70a9300848866852980424423c3aac0212210f9d365cc91087ae9b2e648843f74597324421e3a2cb992218d15261cc910ca8a730e648866752987324423a3aac3992218d15161cc910ca8a6b0e648863854983324432c29cc1992219ad
  | 5 => 0x861d64d4e5344317aa4c529a218b1526294d10c9ea7314a68862f5458a53443162a2c529a2193d4d6294d10c5cc9314a68862d6498a5344317322c529a218b5916294d10c6cc8b0ca68843e76d51534421f3b0a8a9a218bd536254d10c58a9b12a68862f5418953443162a0c4a9a2187d936354d10c38c9b1aa68862f64d895344316326c4a9a2193d8f6254d10c5ec8312a68862c641895344327b18c4a9a218d1936154d10cc8c5b0aa68863864d815344334316c0a9a2117dd95314d10a3ee8a98a68851c7454c53442a7b92a629a21531c95314d10a3ce9318a68851d7498c53442a7394c629a21535ca6314d10c3ccbaa0a68845d7695053442a7394a829a21535ca5414d108beecaa0a68854f7255053442a6392a829a21879945414d10e2ea8b08a6887145458453442aab8ec829a21539c86414d10a9ae4320a6885557119053442acb80c829a21555c76214d10ab2e1b10a68855571188534432b322c229a21951916114d10caec4b08a6886556258453442a7396c029a21535cb6014d10caac3b00a68865561580534428fba22029a21471d11014d108dce5b2e868846d72d974344237b92cba1a211b1c965d0d108dce5b2c868846d72d96434423ab8ecb21a211bdc96590d108d8e4b2c868847671196434431baa4c321a218d1526190d10caea730c868865453986434423a3aac321a218d1516190d10caea6b0c8688654535864344278382c321a211b9cb6550d108dae5b2a868846f725954344236392caa1a211ddc56550d108f6e0b2a868846e72d944344236b96ca21a211bdc96510d108d8e4b28868846e721944344236b90ca21a211b9d66210d10c5ea9310868862c549884344327a9cc421a219314e6210d108d8eab10868862f5458843443162a2c421a2193d4d6210d10c98a6b10868863454984434432a29cc221a211d1d56110d10c68a8b08868863854980434432c29cc021a211e1d56010d108bce7326a48845d7399352442a739ca9a9221535ce54d4910a9ee6aa6a48854c735535244387aa6a7a9221c315353d4910a5ce929ea48852d7494f5244297ba2a7a92214b1d153d4910e1ea829ea48870c5414f52443a2b88a7a9221539cf64d4910a9ae7b26a48856571d9352442b4b86c9a9221539ce64d4910a9ae7326a4885657118f52442b4b80c7a9221599c643d4910acae321ea48846e7610f5244236bb087a922153dcd60d4910a98e6b06a48861f5498e524430e2a4c72922187d516394910c38a8b1ca48861e64d4e524430eb26a729221879905394910c3ac829ca48862e64d4a5244316b26a5292219398f5294910c9ac7a94a48861e6498e524430eb24c729221879916394910c3ac8b1ca48863664586524421f3b6a8a92210f9d85454910c3ea9b1aa48861c54d8d524430faa0c6a92218715063549108
  | 6 => 0xc432729ac5986219354d62cc310d8ac498e618854d7214e30c422f3b4a698621175db530c310a9ae429861886575358430c426abb462186219358e52c8310c9ac6a96418854d7314a20c42373b4a490621355cc61483108daeda90418854d7314820c422f39cc5aa421175ce62d5210caec7b0aa90865463d85548421fbb2a82a4219c5866015210ce2c3306a70845f7654c5384237394caa1c211b5ca6550e108dce5b28870846d72d944384237390ca21c211b5c86510e10a3ae8298870864f53588438432629ac421c219c58660d4a108deeca90a50845f73590528422e39ac82942117dcd65d0a108b8e6b2e850845e73d96428422eb9ecb21421179ce6550a108bae732a850845f73595428422e39acaa1421179cf6510a108bae7b28850845e73194428422eb98ca214219614d60cca1087ce932a650843d7499532842a7396a69942195d4c614ca1087ce8328650843d7419432842abb9aa9a0c21555ce52d061087ced2a2830843d76d5041842abb9aca20c211d5db541061096aedaa083085b270d5041842abb9aa820c216c9c05410610a6ee8a9883085357494841842aab9ca420c211d5d852106108bced29a630845d76d4c31842373b4a490c211b5db5208610c9ea6b16610864c5358b308422f3b0a69842117dd9530c210caca6b0861086555358430842a6b9ca510421535ce5208210aaee6b2e210846e7298f5444236b94c7aa221179ce62d51108bae7316a88852e7298f5444296b94c7aa2214d5c463d5110a3ce7b16a88851d73d8b544429ab8ec5aa2214e5c362d5110a3ce7316a88851d7398b544428f39ec1aa221475cf60d5110a5ce5b06a88852d72d83544430faa4c72a22187d516395110c5ea9314a88862f5458a544432ab8cc72a2219398e6295110c9ac7314a88864e6358a5444326b1ac52a22187d936355110c3ec831aa88862f64d895444327b1ec4aa2219318f6255110c5ec8312a88864f631895444326318c4aa22195d8f6155110ca8c7b0aa88866762d855444332316c2aa2219618f6055110cd0c5b02a88843f76550544428fb9aa82a221471cd5415110a5ee4aa0a88852c72550544428f39cc82a221475ce6415110a5ce5320a88852d72990544422fb9ac42a221171cd62151108bce7308a88845d73984544429ab8cc62a2214b9c86315110a5ae4318a8885357118c544429cb80c62a22147dcd6215110a38e6b10a88853771588544429db82c42a221479cc6215110a3ae6310a88853571188544429cb80c42a22147dcd6015110a38e6b00a88852f725805444296392c02a2211b9ca64d4d108dae5326a6884777159353442a7394a9a9a21535ca54d4d10a9ee4aa6a68854c72553534438a2a6c3a9a21539ca64d4d10a9ae5326a6885577159353442a7b92c1a9a21531c960d4d10c3cc9a9ca68
  | 7 => 0x298841b24c8604c420ce2a2302621046d751922108275b82c71084133dcd6088420caac72884210655635442108266b98c8108413a5c064084209d2e1b1842104cd7698c2108362b1ca210841b158d5108420d8ac7a084210565751042108362b188210841b258e6008420d94c6b0042106c9635802108275baac0108419add560084209d0e8b00421054d7310a50082a6b9843280415a5d762d0020b92e631680105697510b4008394aa085a0041725cc42d00209d4ed19680104ea7608740082d53a043a0041725cc21d00208bce7b2c801045d73d96400829a38aa9200418b552629002099ae7314801045e73194400822eb98ca200414d1c554100208f6ecaa080105b071550400823dbaac4200419a5974210020ad2ea21080106696510840082e4b9884200413a5da3210020cd2cb1908010669654c840082d43a264200414e5d441100209d2ec10880105c97308440083d020842200410f9d0650c02087ae8328601065653584300832aa9ac218041b14c9610c020da2c298060104cd7319320083553268190041b258f40c8020d92c6206401046d7694a20082a6b9ca5100411e5da5288020b92e729440106aa64d0a20082e4b988510041725cc21880208daeb322401046f7558d20082563a2c690041391c5634802099ae630a40104cd73d81200835432680900413a9db3048020d92c618240105e1710c1200823cbacc890041729ce5248020d50c9a1240105ca7310920082753b064900413a9db2148020c9cc7316a98864d6398b54c432731ac5aa6219358d62d5310cacc730ea9886556398754c4333314c3aa6219958a61d5310cd4c4b06a98846e7218d54c4236b90c6aa621179cc62553108bae6312a98843f7655054c42aab9cc22a6219c9856015310ce4c2b06a78845f7654c53c4326a9ac429e219398d6214f10cd4c4b00a78846e7299743c4236b94cba1e211b9c86590f108dae432c878846e7299543c4236b94caa1e211b9cb6510f108dae5b28878846e7219443c4236b90ca21e219394d6210f10c9aa6b1087886726158352c422fb9ac929621171cd6494b108deeca90a58864d6354852c4326b1cc429621179ce65d0b108bae732e858845e7319642c422eb98cb21621179ce6550b108bae732a858845f7359542c422e39acaa1621179cf6510b108bae7b28858845e7319442c422eb98ca216214b5d25210b10c9ac7290858864d6354842c421f3a4ca996210f5d2654cb1087ce9b28658843d74d9432c42a6b90a798e21179d8534c710a9ae429a63885d170d4d31c423b3b0a698e21359d8534c710b8ae429a63885c57210d31c42aa3aa6498e2174dc1324c7108beeca9863886d13158031c4326b1ca410e219358d5208710cd4a4b0043884d57398740c421f3b4a8a06218d9506150310c6aa830a818843d76d504
  | 8 => 0xc6255020c98c6312a81065763d85540832a31ec2aa0419918b6155020caec630aa810654631855408332310c2aa04196d8c6055020cb0c6302a810668621815408339b08c0aa0419c184605502087eecaa0a81061d5458c540831aaa2c22a041879916315020c9ac7310a81065663984540832ab1cc22a0418d9916115020cacc6b08a810655635845408333312c22a0419c58660150208eee2b26a61047471593530822fbb2a629841875915314c20caaa6b08a61061c73590530830eb24c6298418b5926214c20c6cc9308a61063564984530831b322c2298418d5916114c20cacc6b08a61047671197430823ab88cba1841471cd54d0c20a3ae829e86105557114f430823b38ecb218411d5c76590c208ece232c8610475711964308236bacc5218419594d6190c20caaa6b0c861047975982430822fb9acaa18411ddc56550c208e8e2b2a861047671195430823ab88caa1841179da5350c208daea312861062d54189430823cba8c0a18418e5506050c208dae4b28861046e72194430823b388ca218411d5c46510c208baeda98861045d7614c430828eba0a621841555c45310c208daeb31086104e9709884308327a9ac4218419314d6210c208bee6b2e841045c735974208267b9acba10413adc163d082099ae730e84104e97098742082b4baec1a104133dcd60d08208bce7b2c841045d73d96420822f39eca21041175cf6510820c3ca8b18841061d5458c4208296bacc8210414b5d654108208deecaa0841052f765504208317bb2a821041c3dcd5410820e18e6aa0841072771550420839238aa821041ca1c15410820c9acb318841070d5498c4208316aa2c621041935956310820e1aa8b18841064f5458c42083472a2c621041935516310820d1aa8b18841060d5458c4208364b1cc0210411bdd56010820d94c6b00841051d7414f32082aab88a7990411b5d4648c8209d2e0324641046d76d523208316322a919041531cd548c820a5ae829c641070d54d0e32082a6ba887190411bdd5608c8209d6eab04641066b7558232082743a2c119041179d8534c820a3ae829a64105557114d32082363b2a8990418b191544c820b94e1a9a641046e7614d3208296ba0a699041339d8534c820b1ae829a64105c57114d32082673b48699041715c6434c820b94e121a64104cc7650d3208386aa28699041721c1434c8209d2e030a641045f7654c3208364994c0190411ddd95114420c6ac8a88a21065563544510829a38aa9a08413a5c262d04208bce7b2c821045d73d96410832ab1ca3208419558d51904208bee6b2a821045c73595410822f398caa0841175cc6550420c5aa831282104cd731894108274b84c5988410fdd1654c420878e8b2a621043e74195310821eba0ca988419354c624c420c98ca99262105c4714c93108332312a
  | 9 => 0xce7b22a31045d73d91518823bbb2a228c419558d51146208bce7b2e831045d73d97418822f39ccba0c41175ce65d06208bce7b2c831045d73d964188266b98c4a0c414d5d251106209d0e4b00831043e74d97318821eba6cb98c419394d62cc620c9eca99263105c4714c93188267b9ac110c41335cc64086209d2e032043106c563d042188362b188210c41335ce6290220c5ca8b10811065653584308832aa9ac218441b14c9610c22099ae6326411064d6598f2088326b2ac7904419659663c8220cb2cab1e411046d7298f544822f39cc32a241175ce61951208bee6b04a89045c73582544830fb20c6aa24193d8f6255120c98c7b12a89065763d85544832a31ec2aa24199d8b6155120c6ec830aa89065763185544832a318c2aa24199d886155120cb6c7b02a89065863d815448339b0ec0aa2419c187605512087eecaa0a89051c73550544829a38aa82a241179cc62151208bae6310a89047771593534823a38ac9a9a41871936354d20c58c9b12a69063764d85534831a326c2a9a418dd906154d20c68c830aa690657631855348333b10c2a9a418e1936054d20ce0c3b02a69045f7654c534828e3a2a629a41551c55314d208ece3b2e869047571d974348237b92cba1a411b5cb6590d208ece3b2c869047571d96434823cb86cb21a411d9c46590d208eae232c869063754986434831a2a4c321a411bdc96550d208eee2b2a869047471595434823db82caa1a411b5cb6510d208eee2b288690474715944348237390ca21a411b1d56210d20c5ea8b10869064f53588434832629ac421a413a1c16210d20c3ea831a849061c5418d424831baa0c2a12418d1506150920c70a9b02849065853583324822fb9ac9a8a41171cd64d45208eeeca88a2905347454451482aa39aa228a41951c56314520aaae628e829045e73196414822eb98cb20a4187d526390520c38a931c829045f73594414822e39aca20a41179cc65105208bae6328829046e7598841482aab98a220a419c1456010520a9ae529e629051c7454f31482aa38aa798a41555cc51cc5208bced29a629054d7294d314828e3a2a698a41551c5534c52087ee8b28629043c74594314822ebb6a618a4117dcd65501208b8e6b2a809061f5418d404830e2a0c6a02418b1536250120c6ea830a8090634541854048327a9ac5982419314d62cc120a9ae529c609051c7454e30482aa38aa7182410fdd1654c120878e8b2a609045e7614d30482a6b94a618241565c2530c1208beeca98609051c7454c30482aa38aa6182419594d610c120caaa6b08609052c7454e20482b238aa710241535cc51881208bce7316a81045d7398b54082a6b9cc5aa0411d9c663950208eae331ca81045e73986540822eb9cc32a041939c86355020c9ae431aa81045f73589540822e39ac4aa04193d8
  | 10 => 0x5567118a53c82aab88c529e41955846194f20ab2e030ca79047671d9153c823ab8ec8a9e41179db5454f20aace3aa2a79055571d5153c822f3b0a8a9e41559c76454f20aaae3b22a79055b7059153c82a7390c8a9e4156dc16154f20caac230aa79051f7458153c828e3a2c0a9e4155dc56054f20aa8e2b02a79045f7654c53c823b38ecb21e411d5c76590f208ece232c87904757119643c832b29cc321e419554e6190f20caca6b0c87906555358643c832d29cc121e411d9c66550f208eae332a87906595318143c8326a9cc421e419394d6210f20c9aa6b10879045e7694d42c822e3b2a6a16419594f6150b20caaa7b0a85906565318542c832aa98c2a16419694c6050b20cb2a6302859045d7598c42c822fbaac621641175da5310b208beeca98859070e5350842c832ca9cc1196419694e600cb20c3cc929ea39061d6494f51c830f322a7a8e418759153d4720a6ce9a8ca39045e73d9151c822eb9ec8a8e41175da53147208beeca98a3904777654451c822f39ccba0e41175ce65d07208bce7b2c839045d73d9641c822f39ccb20e41175ce65907208baeb31c839045f7558e41c822fbb4a720e41175da53907208beeca9c839045d7654e41c822f398caa0e41175cc6550720cb4a7b02839065a5318141c822f39cca20e41175ce6510720c9aa7310839064d5358841c82aa38aa698e419654c604c720aaae3298639065a5398031c822ebacc610e4117dd563087208baed298439045f7654c21c8326a9cc5a06419354d62d0320cb2cb29e81906596554f40c822ebaec6a0641175d463503208bced29a819045c7654d40c832729ec4a06419354f6250320c5ca8312819064e5318940c8326a98c4a06419594f6150320caaa7b0a81906365418540c831aaa0c2a06419594c6150320caaa630a819047976d5040c8326a9cc5986419394d62cc320c9aa6b16619064d53d8930c8326a98c4986419594e610c320caaa730861906565358430c832aa9ac218641b4585300c320c9ae531ea91065663987548832ab1cc3aa4419598d61d5220caac6b0ea91065a63983548832cb1cc1aa4419a58a60d5220ce4c3306a91067161983548823b38cc72a4411d5c663952208bce730ca91045d73986548821fbb2a82a4419a58a60d4e208ece3b22a71047571d91538822fbb2a629c419554d6114e20cacc6b08a71067161980538823b38ccba1c411d5c665d0e208ece3b2c871047571d96438823b388cb21c411d5c46590e208ece332a871047571995438823b388ca21c411d5c46510e20c9ca6b10871064d535884388266b9cc3a144133dcd60d0a20c74a8302851046d76d504288326b2ac62144193d516310a20c9aa8b18851054e73d523288237bb2a9194419654c604ca20c58c9aa2651046e7694d32882673b48699441715c6434ca208b
  | 11 => 0xc2a2b9086a8861d49c04354430aaae021aa2187517010d510c2ab39cc4a88614ddd16254430a68e8b12a21855473589510c2b8382c4a8861559cc6254430aace7212a21855573909510c23bbb284a88611d1d94254430aaee6a12a21855473509510c2b9b8284a88615c1c14254430aace6212a21855573109510c2b938664a88615c5c33254430aaced992a21855674cc9510c2aa3a664a8861d49c33254430aaae1992a21875170cc9510c2a8b8664a8861551d93254430aace8992a218554744c9510c3a3b9264a8861d1d893254430e88c4992a218746424c9510c3a2a1264a886155dc132544308eeeca88a21865663547410c32ab1aa3a08619558e5190430cacc6a8c821865563546410c237b92caa08611b1c96550430a68e8a8a821865763545410c32a31aa2a08619c5476050430a6ae9288821867151583310c32b38acb18861175d4648c4309b6e0b14621865565946310c32b322a31886195191518c430caac4a8c621865565d06310c2aaba8831886195594418c43099ee4b04621865551582310c33928ac018861335c8640c4309b2e0320621855575984310c2abbb2a21886195dd9510c430cacc8a88621865464544310c32ab12a218861b4985600c430cacc6a8e421865563547210c22ebaec710861365c06388430caec6a8c421865463546210c21fba2ca908610f1d16548430caec6a8a421865463545210c338a8ec0908619c5446048430caac7288421865663544210c32ab1aa210861535c843940308baec18ca0184cd7298e400c32b31aa3200619558d51900308eced28a801847476945400c32bb1ca2a00619518e5150030ccec528a801866462945400c23b3b2a2a00611d1d95150030caec6a8a801865463545400c333b12a2a0061991895150030cacc6a88801865563544400c2d838a80200619998a51cc030ccac528e601866662547300c332b12a398061335c864cc030d8ac528e601845f76547300c326b12a3980619598551cc030d8ac4a8e601865776547300c32b322a3980619519151cc030e8cc4a8e601865562547300c3a2b12a3980619158951cc0308baed29c60184797694e300c2e4b94a718061725c8438c0308baeb322601865765945300c32a30aa29806195d95514c030ca8eca8a601865664545300c32a322a29806195d89514c030b94e529a60184da760c9300c339b2ca2980619cd95514c030ea4a6a8a601864e6398b54c8326b1cc5aa6419598e61d5320caac730ea9906666298754c832b31ac3aa6419558d61d5320cccc4b0ea99066a6258354c829b38ea92a641179ce61953208bae730ca99053671d9154c821fbb2a82a6419358e6215320cd4c4b06a79055671d5253c82aab8ea929e41559c76494f20aaae3b24a79055970d9253c82a7390c929e41479d06294f20a3ae8314a790
  | 12 => 0x20a618e1516010530ce0a2b00829845d76953314c38a2a08298a61745c0414c5308bceb31c429843f74594214c21e3a2ca10a619358f5208530c9ac6290429865563d44214c26ab8cc7a0261871536350130c5ea8312809862c54189404c31baa0c2a02618d1506150130caac228c609854d7298f540c32b31ac3aa0611ddc562950308e8e2b14a81843f76550540c316aa2c42a0618b9916215030c9cc6b10a81866662984540c332b14c22a0619598d6115030cccc4b08a81866562584540c338b0cc02a061555c754d0c309b6e0b1686184cf72583430c23abacc3218611ddd56190c30c5ca8b10861862d54588430c2aab8ea82186117dd95410c30c9acb310861864d65588430c327baac421861931d56210c30c9ea8b10861868e54588430c326aa2c421861a35516210c308baeb30886186c962980430c22fbaac021861b29896010c308eee2b24a41847471592520c22ebb08729061535c843948308deeca90a41862d64548520c23b38ccba10611d5c665d08308ece332c841847571996420c23bb8acaa10611d1c565508308ece232a841847571195420c30f2a0c6a10619318e52508308eaebb0a841847575185420c31d2a0c0a10619a9486050830cd2a4302841847671994420c23ab8cca21061365c064cc830aaae3aa6641845f76553320c22ebacc39906136dd560cc830cb6eab06641845e76d51320c2aab8ea899061171d9544c830b94e1a9264184ce76149320c2c6ba0a499061331d9424c830d18c8a12641870d54509320c2e43828499061b24ca600c830acce42a4a21856572152510c2e2b90c728861c55504394430b8ae421ca2185367414a510c29aba0a528861745c33294430e88a4994a21855673d92510c31ab20c928861599c86394430acae431ca2184757690e510c2b33908728861595c84394430aace6314a2184777650a510c23a3b2852886155dcd4294430aa8e6a14a2185737050a510c2b83828528861559cc4294430aaae6214a218745320ca510c2ab38e86a8861535c84354430aace221aa21855671cc9510c2acb8664a8861931893254430aa8e2992a21847676d51510c23b3b0a8a8861599c85454430acae42a2a21855575d0d510c38b2a086a8861715c843544308eceda92a21847676149510c29b3a0a4a88614d5d05254430e8aa5992a2185d170cc9510c2abbaa64a8861d1d493254430aace7b22a21855673991510c2aa39ac8a886159dc96454430ac8e4b22a21857070591510c31ab20c8a88614d9d26354430a6ae931aa2185667298d510c2b2b94c6a8861559db4354430e2ec9a1aa21871464d0d510c2aab9686a8861555c343544308eced21aa2185667210d510c2b2b9086a88615c9c04354430ae2e021aa2185567610d510c38b3a086a8861d19c84354430aaae421aa2187457210d51
  | 13 => 0x600cb30c5cc9296a39862d6494b51cc317322a5a8e618b59152d4730a6ce9a8ca39846d7694851cc237bb2a428e611ddd951147308dce532e839846d7299741cc237394cb20e611b5ca6590730c3ca931c839864e6394a41cc326b1ca520e619398d5290730c9ac6a94839846e7219541cc236b90caa0e619a94b6050730cd4a4302839846e7299441cc236b94ca20e619398d5210730c9ac6a90839854d7215331cc3a2a92a398e619354a60cc7308bcec2a2639854d7215131cc327b2ca498e61551c5524c730c9ecaa9263987477154931cc3a238aa498e61d154b614c730b2ce9a8a639874552d4531cc2e8b86a298e61359d8514c730e8ca428a639874552d0531cc38b2a08298e61d1548414c730c9aa43026398746524c431cc335294c018e619a949600c730da262b00639864e6354a21cc326b1aa510e619a5486048730c9ac7290439864e6354821cc326b1aa410e61355c663d0330c9cc6a96819864d6354b40cc30f2a0c6a06611b5d762503308daea312819846e7694940cc327b1ca4a06619318e52503308d8eca92819864f6354940cc32631aa4a06619994b6150330ccaa5b0a81986365418540cc31aaa0c2a0661999486150330ccaa430a81985b07150040cc32bb1ec2aa46195d8c615523087eecaa0a91855771553438c22ebacc3a1c6133dc960d0e30c72a8302871845d76d50438c2abb8aa821c61935956210e30c9eeab10871864f54588438c326aa2c421c61b2dc16210e30d90e0b10871845d76d0e528c2a6b9087294611bdd95214a308ece3b2c851847571d96428c23bb8acaa14611d1c56550a308baedaa6651845f76553328c2abb8aa999461171d9544ca30aaee2aa2651868c64509328c2e43828499461175d4614ca30c3ec821aa31854d7210d518c23bbb2a228c611b9cb65d06308dae5b2e83184d873580418c2e8b808318c6133dc9608c63099ae432063184d970190318c21f3a6cb90c610f5d365c86309b2e031c43184d873582218c29a38aa920461335ca6390230a68e2aa081184cd72193308c326b2cc5984619359562cc230c9ac4a8e611865661547308c334b2cc5984619a59562cc230c9ec7b12a89862f64189544c327b18c4aa26195d8f6155130ccec5b0aa89866462d85544c31bb20c2aa26195d8c6155130ccec430aa89866462185544c334316c0aa2619c187605513087eecaa0a89852c72550544c29a38aa82a2611ddc562151308e8e2b10a89863854583434c237bb2a4292614b1d15214930ac8e2a90a49847771590524c23a38ac8292611d9c665509308eae332a849847771594424c23a38aca2126187d516310930c9ac7a90849864d63148424c23bbb2a228a614d1d15114530ac8e4a88a29861c5458e414c237b92ca20a611b1c965105308dce4328829846d72194414c22f3acc6
  | 14 => 0xa330042a06685258021503a5a98a5a0281d214c52d0140ec0a5a8e80a07505314740503b0290a3a0281c314c5290140e2ea628c80a0714531464050393a90a320281c914851901408beeca98a62064d53588531032aa9ac2298813a1c960d0c40c9ca6b10862064d53588431022f398c2a9081175cc61548408deeca90a42064d635485210332a92c2290819358e5210840c9ac6a90842047771595321023a38aca990811d9c4654c8408eae232a642062c64549321032ca98c0990819a548604c8408bce6312a22045d73189511023bbb2a2288819558d5114440ccac4a88a2204e87258041102cab9cc2208816a1c96010440c6aca20c622046f725953110236392ca988811b9c8654c4408dae432a622061c6454d311031a322a2988819c544604c440d6082302622045f73595211022e39aca90881179cc65484408bae632a422062c645492110338a88c090881179cf65084408bae7b28422063565104211034ab1882108810f5da54900408f2ed2a4802061f65d8d401030fb28c6a00818bd976250040c5eca312802068c63189401031bb2ec2a00818dd946150040d2ec630a8020694631854010353b10c2a0081a91886150040cb6cbb1a802065b6518d4010335b2ec4a00819ad946250040d96c631280206c86318940103552a0c4a0081aa90c6250040d5086312802067365d854010370316c2a00819cd946150040d66c830a80206d0631854010370310c2a00819398e62d5330c9cc6b16a9986566398754cc333314c3aa6619958a61d5330cacc6b0ea9986666258754cc332b12c3aa6619a98960d5330a6ce3aa4a99853671d9154cc21fbb2a82a661555c66315330c9cc6b10a9986365498643cc31aaa4c321e611b5d66210f308deeab1087984777159252cc23a38ac929661599c75494b30acae3aa4a59854c7359252cc2b3b8ac929661591c56494b30ad6e0b24a59862d6419252cc2a7398c9296614b9d06394b30a5ae831ca5985667118e52cc2b2b88c729661599c64394b30acae321ca59856a7090e52cc2b4b8487296611b5d84394b30a9ce630ca59846e76d5152cc2b338ea8a9661595c75454b308dcec2a2a59854c7359152cc2b3b8ac8a9661591c56454b30ad6e0b22a59862d6419152cc2a7398c8a9661599c66354b30acae331aa5985667190d52cc2b2b8c86a96611b9d84354b30a9ce730aa59856b7058552cc2a7398c2a96614bdd16054b30a58e8b02a5985677158152cc2b238ac0a96611bdd95214b308eee2b2a85984747159542cc327b1ca4a16619318e5250b30a58e8a92859864f6354942cc32631aa4a16619994b6150b30ccaa5b0a85986665218542cc332a90c2a16619a94b6050b30cd4a430285986695218142cc296ba4a4216619358e5210b30c9cc6a90859864d6354842cc334a94c1996619a94a
  | 15 => 0x667294f51502b2b94a7a8a8159dc953d4540ac8e4a9ea2a074753d4b51503a229ea5a8a81559ce52d4540aaae7296a2a05577354b51502aa39aa5a8a81d1d4c52d4540e88a6296a2a04757690f51502b339087a8a81595c843d4540aace7316a2a05557398b515023bbb285a8a8155dcd42d4540aa8e6a16a2a05737050b51502b838285a8a81559cc42d4540aaae6216a2a055673d8351502aab9ec1a8a81599cb60d4540acae5b06a2a064f5398a515032629cc528a8193d4d6294540c98a6b14a2a064e63d4a5150326b1ea528a819398c5294540c9ac6294a2a065663d46515032ab1ea328a819998b5194540ccac5a8ca2a045e76d4d515022f3b0a6a8a8193d4f6254540c98a7b12a2a064f531895150326298c4a8a811b9db5254540c9ec7a92a2a064c63d4951502373b0a4a8a8193d8c5254540c98c6292a2a04777654451502abb9aa228a81551cd5114540acee4a88a2a056472544515032b32ea628a811d5da5314540acce5298a2a05657294c515023bbb2a628a8159dc95314540ac8e4a98a2a06566514c515033332ea428a81d1d4f5214540e88a7a90a2a04757694851502ab39ca428a81555ce52145408eeeca90a2a05577354851502aa39aa428a81999945214540e8ea6290a2a07445314851502ab39ec828a81555cf6414540ae2e0318a2a04757690c51502b9b828628a815c1c14314540acce4218a2a05657210c515029aba0c428a81559cc6214540aaae6310a2a057170188515023bbb28428a8155dcd4214540aa8e6a10a2a05737050851502b83828428a81559cc4214540aaae6210a2a072542108515029b3a06428a814d5d03214540aaee6b00a2a05547358051502b3b92c028a81591c96014540aaee6a00a2a05547350051502b3b928028a81591c940145408bceb31c82a045c7558e415022ebb6a720a81175d85390540c9cc7a9482a064d63d4a4150327318a520a819358c5290540cacc7a8c82a065563d46415032b318a320a819558c5190540cd0a530482a0670519824150334292c120a819614f6050540cd0a5b0282a0658531814150334290c0a0a819cd4460505408dee4b2e62a046c725973150237b92cb18a811b1c9658c5408dce5b2a62a046d72d953150237b92ca18a811b1c9650c540cb0a730062a066852980315033828cc018a819a149600c5408bee6b2e42a045c73597215022fb9acb10a81171cd65885408bce7b2a42a045d73d95215022fb9aca10a81171cd65085408bce632842a045d73194215022f3acc610a81171d563085408beeda9842a045d76d4c215022fbb0a610a81175d85308540c9cc7a9042a064d63d482150317320a410a819398c5208540c9ac629042a065663d44215032ab1ea210a818d9905108540c6ac828842a065663144215032ab18a210a819a14a6008540ce0
  | 16 => 0x22eb98c2a94811bdd95214a40a9ae7294852054d739494290335290c0a14811d9c6658ca408eae332c652054d7294e32902a6b94a6194811ddd95114640caac6a88a32065563946419032ab1aa320c81655ce611064096aeda8883205b270d4441902cab98a220c816c9c051106408dce5b2e632046d72d97319030eb24a798c81535ca53cc640c6cca20c632054d7294d3190237396ca18c811b5cb650c6408bce7b2e432045d73d97219022f39ccb90c81175ce65c86408bce7b28432045d73d94219032ab1ca210c819558d5108640c6cca208432069563104219035820cc010c8153dc960d4d40a98e4b06a6a064f5398a5350327a9ac529a8195d4e6194d40caea6b0ca6a045f7654c53502a7b92a629a81531c95314d40aaee2a98a6a05547154c53502ab38ec829a81555c76414d40a3ae8310a6a05597018453502a7396c029a81535cb6014d408eceb30c86a065753986435032a29cc321a811d1d56190d40caea6b0c86a065453586435032c29cc121a8196d4c6050d40c9ea731086a064f53588435022f39cc3a9281175ce61d4940acce329ea4a05657194f52502b3b8aa7a9281591c553d4940a9ce7b26a4a054d73d9352502b338ec9a9281595c764d4940acce321ea4a05657190f52502373b087a9281539ce61d4940a9ae730ea4a054f7358352502a639ac1a92819398f5294940c9ac7a94a4a065753986525032a29cc32928199d4a6194940caea6b0ca4a0654535865250333a92c329281179db53549408bcec29aa4a065753d85525032a29ec2a928195d4c6154940ca8a630aa4a046f7654852502a7b9aa429281531cd5214940acee2a90a4a056471548525032732ea6292811b5da5314940acce3298a4a05657194c5250237bb2a62928159dc55314940ac8e2a98a4a064e6514c5250296ba0c629281599c64314940acae3218a4a056a7090c52502b4b8486292815adc14314940ad0e0a18a4a046e7610c5250296ba0c229281539cc6114940a9ae6308a4a05697018452502a739ec029281535cf6014940a9ee6a00a4a054c735005250334294c121281179d763509408bcea31a84a045e76d4d425022f3b0a6a128193d8f5250940c98c7a9284a064f631494250326318a4a12811d9d76150940caea7b0a84a065453d854250333a96c2a12819914b61509408ecea30a84a065753185425032a298c2a128199d486150940cc8a430a84a065b53d81425032c29ec0a12819a14b6050940cb6a630284a0658531814250335a90c0a128117ddb53109408beec29884a064e63d484250326b1ea421281a358d4210940e18a6a1084a047771597325023a38acb992811ddc5658c9408e8e2b2c64a047671d95325023ab8eca992811ddc5650c9408e8e2b2864a061e6414c3250317320a419281179ce62d45408bae7316a2a05
  | 17 => 0x9843559c76454c21a98e4b22a610d547159153086adb82c8a9843561c16454c21a9ce4322a610d4e72d81530868fba2c0a9843471d16054c21a98e4b02a610d547158153086ab388c0a984317dd95314c218f4e032e8610c7970197430863b388cb218431d5d66190c21caaa730c8610e5653586430872aa9ac3218431edc16550c218f0e0b2a8610e4d53d894308636ba8c4a18439554f6150c218eaea30a8610e55531854308637390ca218431e9c06510c218f2e03288610c6d759884308726a9cc4218439394d6210c21c9aa6b108610c5f73592520862e39ac9290438d5526190821caaa730c8410e5553586420862f3b4a6a1043171da53508218bceca9a8410c5c7654d420872b29ec2a10439554f6150821cb4a7b028410e5953d81420872d298c0a10439654c60508218bce7b288410c5d73d94420862ebacc62104317dd563108218beed2988410c5d7694c420862fbb2a621043175d95310821e1ca6a108410e5553586320861f3a6ca190430f5d3650c821c9aca9906410e565358432086aab9ea9a0843179cf65904218bae7b2c8210c5d7598e410862fbaac72084317dda53904218baed29c8210c5f7654e410862ebb2a720843179ce65104218bae73288210c5e73194410862eb98ca208439354e6210421c9aa6b108210d357599041086aab9ea8208434d5d654104218eeecaa08210d3776550410871bbb2a8208434d1c154104218eaeda988210d3574d4c41086aabaca620843955965310421e2aa92988210e556554c410878b2a2a620843c55515310421cacc8a988210f166454c41087a2a9cc4208431ddd56210421e8aa6b108210e4d5358a310872729ac41884395595310c4218daed2944210c757694a2108727b2ca69084393d9553484218eaeb3224210e576594d210872bb2aa69084317dcd64940218b8e6b24a010c5d7694c500870f324a6280438759253140218beeca98a010e1e6454c500870eb22a6280431edd95014021c72c8a80a010e575358653d022fbb2a629e819354d6214f40aaae329e87a04e87258343d02aab8ca621e819394d6210f40c9aa6b1087a046f7654852d0326b1aa4296819358e5210b40c9ac6a9085a068d6350842d02d438284216811d9c765ccb408eae3b2e65a05557194f32d032d29ac199681555c6534cb408ece3b2865a047571d9432d032ab1ea328e81179cc62547408bae6312a3a04777654451d02aab9ca3a0e81555ce51107409d0e4b0083a046e7299631d0236b94cb18e81555c6538c740aaae329863a045e73d9621d022eb9ecb10e81179ce65887408bae732c43a045e73d9421d022eb9eca10e819358e5208740c9ac6a9043a064f5358a539022fbb2a629c819554d6114e40a9ae529c872065653586439032aa9ac321c81535ca5350e40c9ac7a94a52045e73185529
  | 18 => 0x1d4f218beeca98a790e1d6454c53c870e39ac829e43875926314f21c5ac9310a790e366458453c868e39aa9a1e43475d053d0f21caca6b0c8790e555358643c863d384caa1e431e5c26550f218bced29a8790c5d76d4c43c868eba0a621e4393d4d6210f21c98a6b108790e1e5458c42c870eaa2c6216438d9516110b21a3ae829e6590c5e7614d32c868eba0a69964317dd9530cb21aaee6aa68390e2d5418941c863abb6a820e4355dcd5410721a6ee8a988390e4d5318931c863dbb2a0286439598e61d5221caac730ea910e5a63983548872cb1cc1aa4439a58a60d5221ce4c3306a910e5a63583548872cb1ac1aa4439c98560d522187eecaa0a910c5f73580548862e39ac02a4439958a61d4e218beeca98a710e59535805388734b14c029c439698d6014e21ce4c2b00a710c7a70997438863cb84cba1c431e9c06590e218f2e032c8710c7a70995438863cb84caa1c431e9c06510e218f2e03288710e4e535884388726a9ac421c438d9506150a21caaa630a6510d597014f318862f3b0a698c43565c0534c6218beeca986310c5f73592508862e39ac928443959c46354221caae231aa110e597018d508863dbb2a0284439658d5014221c3ec831aa890e4c63d89544872bb1ec2aa2439518f6155121cb6c7b02a890e5863d815448739b0ec0aa2438ed906055121cb6c6302a890e58631815448735b10c0aa2439cd84605512187eecaa0a890d1c73550544869c382a82a24317dcd60151218b8e6b00a890c7771593534870e326c6a9a438b1936254d21c68c9b0aa690e3b64d81534871c326c0a9a438ed906054d21c70c8302a690e5b631815348735b10c0a9a439cd846054d218beeca98a690d1c7454c53486ac382a629a431e9c365d0d218f2e1b2e8690c7571d96434863d386cb21a431e5c36590d218e8eab0c8690e34545864348637b92caa1a431ddc56550d218f6e0b2a8690c78705954348636b96ca21a431edc16510d218f0e0b288690c6c755884348717aa2c421a438b1516210d21c9ea6b108690e4c53588434870faa0c6a1243871506350921c68a9b0a8490e3b54181424871c2a0c0a12439514d61cc921c58a8b168290c5f73595414862e39acaa0a439314d62cc52187ee8b2a6290c3c74595314863dbb2a0282434e1d15014121ab0e6a80a090c5f73590504862e39ac8282439558e61d50218bee6b04a810c5c73582540861fbb2a82a0438e5516015021c9ac7310a810e5a63980540872cb1cc02a0438e9916015021cb4c6b00a810e59635805408735312c02a0439c9856015021cd0e4b00a810d5a7015253086acb80a929843559c76494c21a9ce4324a610d1e7418a530868eba0c529843569c06194c21ab2e030ca610d4e72d8253086ab388c129843179db5454c218bcec2a2a610d5a7015153086acb80a8a
  | 19 => 0xb10a898c7870588544c637b92c02a2631b1c96015131c68a8b0e8698d4c72553434c6ac382a9a1a63171d560d0d3199ee4b068698c5f76550434c6a6392a821a63561c15410d319a8e2b108698e4e65588434c7263aac421a6393d516210d31c9aa8b108698ec771588434c76238ac421a63b158b6110d31aacea3088698ec662184434c6e8b80c221a631bdd95214931a58e8a90a498d6870548524c63db82c8292631e1c164149318baeda18a498d4d7210c524c63d384caa12631e5c265509318f6e0b288498c7870594424c70faa2c6212638715163109319a8e2b188498e4d63d48424c726b18a421263175db54cc9318beecaa66498d4c72553324c6ac382a999263359c6644c9318bcedaa26498e1c64d51324c6a6392a899263561c1544c931a9cebb126498d4e76149324c7273b0a499263535d0524c931c9cc82926498e4c64149324c6a7380a499263531d6424c931e1ea92126498ccc76509324c6a63aa8499263a3191424c931b90e0a126498cd675185324c72b3a8c299263359d0614c9319aae030a6498c5e75d81324c70e2a2c7a0a63591c954d0531ae0e0aa68298d5675d0f414c72b32e87a0a639599443d0531b8ae421e8298e5665ccb414c66bbb265a0a639599532d0531e88a49968298c7776550414c6b2392a820a635c1c15410531aacea3188298dc57218c414c6e8b80c620a63559d74310531e2aa82188298dc57210c414c69aba0a420a63351d93210531b28e89908298f44524c8414c74b3208798a63715c843cc531d2cc820c6298ccf72582314c63dbb2a0282634e1d15014131ad0e4a80a098c6f72590504c636392c828263535c84314131ab2e1990a098d54714c8504c6adb8264282635c5c04114131ab2e1188a098c7b7058a540c63c382c52a0631bdc960950318d8e4b04a818c3f76550540c72731ac42a0639a98a6015031cd2c5300a818e5a63580540c735312c02a0639a5896015031ce4c2b00a818e5873580540c71b2a4c321863475d25310c31a3eeaa188618e4e53588430c63bbaac2218635a9c352948318deeca90a418c7a70996420c63cb84cb210631edc165508318f0e0b2a8418e4c63949420c6963a2a4a1063999486150831cd4a43028418e6952181420c66ab8cc6210638795263904318beeab188218d3574944410c69bbaa8220863535c854cc431ab2e02a66218c5d7694e310c6b8b80a9188631d5da538c4318bcec2a26218d4d72151310c6acb80a898863c5950414c4318ecec2a26218d7170151310c78b2a08698863719c8434c431aaaeb1926218d6a72d42500c6ad38662a8063561c131540318f6eca80a018c5f7358254c862e39ac12a643939c86355321c9ae431aa990e5763d8554c872a31ec2aa6430fdd95415321c3aa8b18a990e1e6458c54c8726b1cc42a643999896
  | 20 => 0xe5358b5090726a9ac5a84835a9cb50942418bce7314a120c5d7398a509062ebb4a62848317dd953142418f6eca80a120c6f725835350636392c1a9a8317dd95314d41a98e4a98a6a0d587054c535072ba9ac321a8317dcd60d49418b8e6b06a4a0c6f7654852506a639aa4292835a1c152149418bce732e84a0c5d7399742506a6b98a5212839318f5250941a9ae629284a0e4c631494250732296c2a12839ad486050941cd0a430284a0d4d7314b325063db82ca192831e1c1650c941aaae629682a0c7b7654050506ac39aa0282835a1c950141418beeca98a620e4d53588531072ca9ac0298839394d6210c41c9aa6b108620e8d435884310637bb2a4290839358d5214841cd2a4b00a420cd5739874210726b1ca4210839358d5210841d1ac6a108420da870508421065aba4c3990831edc1654c8418f0e0b2a6420c7a70195321063cb80ca990838b191524c841caaa630a6420e6552185321061ebb4a9208831d5da5490441d2ca8b1c8220d9673d9141106d2b9086a0883355cc6250441b28e6a128220ea46250941106d838284a08831b9ca63940418dae531ca020c5e7398a501062eb9cc528083959c46354041caae231aa020e4f63d89501072631ec4a808393d8c6254041c98c6312a020c7b76540501072cb1aa0280839a5895014041cacc6b0ea998c6f7258254cc636392c12a6630fdd95415331c5aa8b10a998e2e6458854cc72731ac42a66333dc960d0f31c6ca8b0c8798e2e5458843cc716aa2c421e6317dd95410f31a3eecaa08798e1f7655043cc726b2cc421e63c35526210f31c3aa8b108798e4d6558843cc786aa2c421e6393dd56210f31c98eab108798e4f5458843cc7472a2c421e63935516210f31d1aa8b108798e0d5458843cc762b12c221e6317dd56010f318baec21ca598d4d7210e52cc637bb2a4296638b5915214b318f6e0b2a8598c787059542cc70f2a0c6a1663875506350b31c98c72928598e4c6354942cc71b2a6c2a16639994b6150b31c74a83028598e395418142cc735290c0a16639a5486050b318beecaa66598e1c6455332cc62fbaac199663179db544cb318b8ecaa26598e1c6455132cc7463228499663c3551424cb31b90e0a126598e1d5418d41cc6a6b9087286631edd95014331caac730ea918c3f76550548c637b92c02a4631b1c96015231c6aa830a8718c6f76548528c63db82caa14631e1c16550a31c3ca8b1c8318c7776550418c69bbb2a820c638ddd95410631a68e0aa08318cd473580418c727b1662a8463569c331542318f6eca80a118e5563587544c717b20c4aa26393d8c6255131c9ae6312a898e6462d85544c735b16c0aa2639a18b6055131c76c8302a898e5b63181544c735b10c0aa2639a1886055131ce6c2302a898c3f76550544c696392a82a2634e1c154151318f6e
  | 21 => 0xb342a0c0a1265aa1506050932c50a830284996cb73181424cb64398c0a1265b290c6050932d928630284994ea70d93324cb46b248799265715c643cc9329aee2b24649961d64152324cb46b248519265721c1428c9328eeeca88a29953474544514cab8382a228a650fdd16014532878e8b00a29947b76540504ca9c3a2a0282655c1c550141328eee2b20a09947471590504ca1fba2c2282650f1d16114132cacc6b0ea81953671d52540ca9b38ec8aa0650fdd95415032aaae3aa6861946f7558a430cb1b2a4c3218658d5526190c32c5aa9310861955571d50430ca2fbb2a821865935966210c328beeab10861964d65588430ca67baac42186593dd56210c32c9ea8b10861964d54588430ca2ebb08729065535c843948328beeab1c841961d5498c420caaab8ea99906517dd954cc832c3cc8aa6641945d7694e320ca36bb4a719065535d4438c8328baeb322641945e76d51320caaab8ea899065171d9544c832c38c8aa2641970d54909320ca663b28499065a3191424c832b88e2a1264195c870509320ca373b6a899065339da434c832e1aa921a64195c67190d320ca9b3a6a328865535c843544328eeeca88a21947771592500ca3a38ac928065535c8439403287ee8b0ca01943c74586500ca3dbb2a0280651b9cb6054f418dae5b02a7a0c5f7654c53d0726a9ac429e839394d6210f41c9aa6b1087a0c5e73d8152d062eb9ec0a96831bdd95214b41c9ac6a90a5a0cd57398742d0726b1ca4216839358d5210b418f4e1b2e65a0c7970d9732d072b29ac3996831b9ca63943418dae531ca1a0c5e7398a50d062eb9cc5286831edd95014341a3ae8314a720e4d6218a53906a7390c329c83535c86194e41ab4e030ca720d5970186539068eba6c129c83539cb6094e41a9ae5b04a720d56711825390637396c0a9c831b5cb6054e41a9ee4b22a720d4c7259153906adb82c8a9c83561c16454e41a3ee8b12a720e4d6218953906a7396c0a9c83535cb6054e41a3ee8b02a720d5671181539062fbb2a629c839554e6190e41caca6b0c8720e5553d854390726a9cc421c839354d6210e41d1a86b108720e5a53983529072ca9cc1a94839694d60d4a41cb2a6b06a520d6a70d4a529062f39ec0a9483175cf6054a418baed298a520c5f7654c5290637bb2a4294839554e6190a41caaa6b0c8520c5d75d8d429062eba8c6a1483179da5350a418b8eca9a8520e5653d85429072aa9ec2a14839594c6150a41caaa630a8520e6652185429072d29ec0a14839654f6050a41cb4a63028520e59531814290735290c0a14839a5486050a41d1ac6a108520f0e5350842906d4382842148387191534ca41a98e4a9a6520e1e6494c32906a6b94a6194838759653d0641c3acaa9e8320e556594f419072ab2aa7a0c839394e62d4241c9aa7316a120e4
  | 22 => 0x85b294c6050842cd2a630284216c9531814210b24a98c0a1085aa90c6050842d5086302842145f735825110a2e39ac128885179cc60544428bae6302a22145d7694c5110a2fbb2a6288851ddd95114442cb4a7300a221659539805110b2d29ac0288859654d6014442ce2a2b00a22145f735865010a2e39ac328085179cc61540428bae630aa02145d7694c5010a2fbb2a6280859594e6114042caaa7308a021656535845010b2aa9ac2280851edd95014042ce2c2a80a0216566398754ccb2b31ac3aa6659698e60d5332cd2c5306a9996726198354ccb38b0cc1aa6659698d60d5332ce4c2b06a9996716158354cca1fbb2a82a6659398d6215332caacb30c87996556558643ccb62b12c321e65959516190f32ca8a8b0c879945e7615143ccb16aa2c421e65879506350b328eeeca88a3996715158051cca3bb8ac9286651d1c564943328f6eca80a1996716154050ccb2bb1ec2aa46595d8c615523287eecaa0a91964d63988548caabb8aa9a1c658b5506250e328baedaa0871955771550438cb26b2cc421c6593d516210e32c9aa8b10871946e76151428cb27b2ec6a1465339db4350a3299cec21a85196c463d85428cb33b28c2a1465b118c6150a32d90c7b02851966b65181428cb65b18c0a1465b218c6050a32dc6c230285196e061181428cb352a0c0a14659a1506050a32d968630285196c843181428cb0eaa2c62146517dd954cca32c3cc8aa6651955771553328ca75386c99946587d904354632a9ae421aa31947776544518caa6b9087284651edd95014232caec7b0aa89963764185544cb2bb18c2aa26599d886155132cb6c7b02a89967361d81544cb3830ec0aa2658ed906055132cb6c6302a89966b62181544cb39b08c0aa2659c184605513287eecaa0a89953471550544ca9c382a82a2659358d62151328eee2b00a89947471580544cb162a2c5a1a65935ca6590d32b94e1b14869954e7518a434cb27328c521a65959966190d32d88c530c86994cc72586434cb2b32ac321a65b1d896190d32caca8b0c869965454586434cb63b92c321a65b11c96190d328bcec2a2869954e7518e424cae2b88c721265539d64390932b8ae321c849954c7550e424cb0e2a6c6a12658dd506150932c68a830a849963b54181424cb1c2a0c0a12654b9d76450932a5ce92a2849946e76151424ca973b0a8a12658b9d85450932e1ae62a2849964c65d8d424cb862a6c6a1265c31506350932a9ceb21a849964c6590d424cb862a486a1265715c64350932a98eaa1a849964c6550d424cb3232ec2a1265c91536150932cc8ca30a849972454185424cb62318c2a12659a1976050932e50a9b02849962c54181424cb34328c0a1265ca1506050932d96c630284996c863181424cb71b08c0a1265b81846050932d56a8302849966a54181424c
  | 23 => 0xd4142ab4e7b0ea0a155973d875050ab4b96c3a8285569ce61d4142ab2e730ea0a1657539865050b2a29cc32828595d4d6194142ca8a6b0ca0a165663d465050b2ab1ea3282859598c5194142caac628ca0a165a63d425050b2cb1ea1282859c9875094142ce2c3a84a0a145e76d4d5050a2f3b0a6a828595d4f6154142ca8a7b0aa0a1657531855050b2a298c2a82851d9db5154142caec7a8aa0a165463d455050a3b3b0a2a828595d8c5154142ca8c628aa0a147b765405050aadb9aa028285561cd5014142ae6e2a80a0a1570715405050a2fb9ac228285171cd6114142cb4cba98a0a174b72d4c5050a3cbb4a6282855c9c65314142ae2e3298a0a147b7654c5050ab9b8aa6282855c1c55314142cb4ca298a0a17497214c5050ba5a9e8428285d214f4214142e30a7210a0a167265d445050ba9a9ea228285d414f5114142ec685a88a0a1479769445050aad39ca228285565ce51141428f6eca88a0a155b735445050aac39aa2282859c9945114142ea6a6288a0a1750531445050bb1a10a228285cc9085114142ad2e5318a0a15397418c5050ab4b90c6282855c9c46314142ae2e2318a0a156a7290c5050ab4b9486282855c9c64314142ae2e3218a0a156b7250c5050ab439286282855a9c84314142ad2e7a10a0a155b735085050aac39a84282855cdc54214142ae0e2a10a0a153b745845050aadb9ac228285561cd6114142ad6e4b08a0a1539741845050aad398c228285565cc6114142ad2e4308a0a15567118a5310aaab88c529885955846194c42a9ce5b04a621556711825310aaab88c1298851d9c46054c428eae2302a62151c745855310aa6392c2a988556dc16154c42ab0e0b0aa621655611855310aa7396c0a9885471d16054c42a98e4b02a621557715815310aaa38ac0a9885559c46054c42aaae2302a62145f7654c5310b26a9ac5a18859554e6190c42caaa6b0c862164d539884310b2729ac4218850f5da54908428daed2a4842164d539824210a2e3b4a6a1085179d95350842caca7b0a842165553d854210b2b298c2a10859554c6150842cb4a7b02842165953d814210b2d298c0a10859654c6050842c3ee7b2a842161c73d954210b0fb2ec6a108587d946350842c3ecb29a842161f6554d4210b1bb2ec2a10858dd946150842d28c630a842163b65d814210b1db28c0a1085a618c6050842d60c2302842164f73d954210b2639ecaa108593d976350842c9eca31a842164f6594d4210b27b2aa6a1085539d95350842a98eca9a842170f6454d4210b86a9c86a1085699c64350842ccecbb0a842174553d854210b33b28c2a1085b118c6150842e8aa630a842166b65d814210ba4a9ec0a10859354c6050842cd6ca30284216cb631814210b64318c0a1085d254c6050842dc6c230284216e0611814210b552a0c0a1
  | 24 => 0xa90a421c6f725825110e36392c1288871b5da52144438deeca90a221c77765445110f35294c0288879a54a6014443cd4a4b00a221e69525805110f38a8ac0288871bdc961940438d8e4b0ca021c6d769485010e37bb2a4280879994a6114043ccaa5308a021e66525845010f32a92c2280871edd95014043ce2c2a80a021c5f7654c53d0b26a9ac421e851ddd951147428f6eca80a1a145f7654c5390b2aa9ac229c859594d6190e42caaa6b0c87214cf735974290a2fb9ac128c85171cd60946428eeeca88a321655635445190a3b388c6a84851d5c463542428bce630aa12145d731855090a3dbb2a0284851d9c660d4d428eae3306a6a1556719835350aaab8cc1a9a8553dc960d4d42caea730ca6a1657535865350b2da9cc129a8596d4d6094d428beeca98a6a15577154c5350aaa38aa629a8556dc15314d42ab0e0a98a6a155671d905350aaab8ec829a85475d36114d42a9ae5b08a6a164d625845350aa6b90c229a85535cb6014d42c9ac5300a6a151d741805350aa6b90c029a85559c46014d42aaae2300a6a164c5398a4350a3b3acc321a8595d4e6190d42ca8a730c86a1474755864350b2ba9ac321a859514d6190d42c9ea631286a164f539884350a2f39cc1a8a85175ce60d4542ae4e129ea2a15717094f5150ab9b82a7a8a855c1c153d4542e8ae429ea2a15357418f5150ab2b90c7a8a851d5da43d4542acce421ea2a153574d835150aab39ec1a8a85555cf60d4542acae5b06a2a1556739835150aaab9cc1a8a859598f5194542caac7a8ca2a165b539825150b2c29cc128a859cd466094542cb6a6b04a2a1658535825150b39a8ac128a85179db53545428bcec29aa2a165b53d815150b2c29ec0a8a8596d4c6054542cb0a6302a2a1477765445150aabb9aa228a85551cd5114542ae6e0a88a2a1570705445150a2fb9ac028a85171cd6014542caccba98a2a14757694c5150ab9384a628a855c5c253145428eeeca98a2a15737054c5150ab8382a628a85959945314542e8ae4298a2a174453d085150b8a29c8428a85559cf6414542aaae7b20a2a15657218c5150a3abb48628a8559dc94314542ac8e4a18a2a15667210c5150aabb9a8428a85551cd4214542a6ee8b00a2a1557735805150aaa39ac028a8559dc96014542a6ae8300a2a1556731805150aaab98c028a85595c860145428ece331ea0a14757198f5050a2f39cc3a8285175ce61d4142ae4e329ea0a15717194f5050ab9b8aa7a82855c1c553d4142e92e429ea0a175353d475050ba829ea3a8285569ce51d4142ab2e728ea0a155b735475050aac39aa3a8285d4d4c51d4142ea0a628ea0a155a73d935050aacb9ec9a82855c9c764d4142ae2e3b26a0a15727198f5050ab8b8cc7a82855a5c863d4142ae4e321ea0a15717190f5050ab539087a82854e5d361
  | 25 => 0xa80000020050030014006004004000003400300180000240010058000014003000000c000000002001c016003002800800800100180000000000048004002002003001c0000020028008002008001001c00800e000000400e01d005800400000b00080080180050008004012006000800400200500a8004000006000000c0000000050000000002000001800a0030000004008000000002c0480040020010000003001800800000100480180060050010000000006000000000e00100300040120020000014000005008000401000000000280000040000000000003002000000200e0018000000000000000000a00500800000000040000000000000003800c002005003001c000007001000000c0040008010012000000800800000b0060000000000000001000000000280080031bdd95214b438eeeca88a3a1c7b7654050d0eb5386a529487535cb4394a438deeca90a521c6f725825190e36392c128c874d5d74394643aaaeba1ca321d7270d4a5190eb8b86a528c87599c86394643acae431ca321d727018e5190eb8b80c728c87559cc6294643a6ee8b04a321d54735825190eb3b92c128c87591c96094643aace6304a321e71601825190e9abae86a8c87555d743546438eceda92a321d7270d495190eb8b86a4a8c871d9d85254643acee4b22a321d64725915190eb9b82c8a8c875c1c16454643acce531aa321d657298d5190eaab9686a8c87559ce6254643a6ee8b12a321d56731895190e9bba2c0a8c87551cd6054643acee4b02a321d64725815190eab398c0a8c879c58060546438eeeca88a321e66629475090f32b14a3a84879998951d4243ccac4a8ea121d6a72d425090e3abb4a2284871ddd951142438f6eca80a121c6f765485250eb238aa4292875a1c15214943a9ae5a18a4a1c77765445150eb2392a228a875c1c151145438dee4b00a2a1c6c725805150e3dbb2a0282875a1c95014143ae0e2a80a0a1c6f725845050e36392c2282870f5da5490c438baed2a48621e96545864310ecb38ec8a1887715c46394843b8ae321ca421d2f7550e5210ea7baa8729087599c46394843acae231ca421d667190e5210eb2b8c8729087539cc6194843a9ce7b04a421e69601825210ea739486a9087555c64354843a98e4a1aa421dc57190d5210e97baa86a908753dd54354843acce331aa421d657198d5210eb5384c6a90875a5c26354843acce321aa421d657190d5210fa338c86a9087535c64354843e8ae321aa421d457190d5210ea738486a9087531d94354843e1ee8a1aa421d4f7150d5210ea638286a9087539ce6154843a58e8b0aa421d4c735855210eb5b82c2a90875a1c16154843a9ce630aa421d4e73d815210ea739cc0a90874b1d16054843a98e6b02a421d67715815210eb238ac0a90879a58060548438deec
  | 26 => 0x8000000001000400000c0030038000003000800800800100000040140150020020002000002801c000003000000800001c003802800600c0000020000008003000c0020000008040002000009801000c00300600040080000018018002001000000400e00f00080140020040010020002000000001c002002000800800a0010000000002000000800000600100000080000010000008000004004800000400c0018000006000000003c0000070008000016000004002800000200000180020140030004002001000002c0080000000068002014000800c00800a0058048000005004000800000c00180000000030018004036005000001400200e00200000040000040024000003000000000400100180240000040050000002000000000000c006002002000200000500100000030010000002000000000000000300480040000010000028004004000800800a000001800000000400b8028002005000802400e0000008004008007000000000000d0030008002003009000c00a0000048000008000000800000400100080140020020008010000008000800400c0050000000000000001802c0120380008024004002000800800000d0030000008001005001c0160010000008010006002800400000d0008040000002000001c008013000002000e00c000801401e01f0008000000003000800000a000000800000e002002000c00c0020000000000000002801000200400100000000050000038022003004000000800100380040020020000000014008001800000600000f8000000004000800c01c000001002000000400280080060010010008006001000002801400000000000040060000014002005001002c0080070000024004000005000003c00100080000100010008004000001000000800200000d800400000900a804c002003000000000600000100240000000028040000003000000000000600400000180000000008002005000000400c00500000080040050000010008000002000800a001000001c0020010000008000001000800800200d002000400c00c000000001400000000000000000008008004002003000800000200000080040060000014006001001001000000000200000040040010004000000000801c00000400600280000050028010000001000001000c00700380000000010020000008000002003801a006000800c0000040000000008001000000400400400100000060020068004002001009800c00000500200080020000000000008001000800000800100280040140000010004006002000803000000100080000060000028000000006000801c01600000180000060020010000002003001801c00a0060038010026002007802400200200280140000020000000014000003000001800100100000040
  | 27 => 0x540a7215084f90ee4a3b33f41a00b6482f2a3899137049d70cd4001000800400000000000040020000008000000002002800000a0000030004000002000000c00000100380000020010070000002000001801000200000080080140010028000002000000000400a0190040014000001000001000a0080008024004002003800000200200000280000040000018006005000000000400d000800000000a00880140000030000014000000000000000000c000801000400400180340080000000000002002000800800600000080000000010020008012006000801c0060010028000008000003800000c004004006c0000020000000008001000001000c000001001c00200000080000040020048018000000001800c000007000803000a008001800000600800200040100170018000002001000000001e002001001400400d0060068006000003801400a003004002c002001001000800400000280000040040008004004001002800400a003001801000a00500000040300010000028004004001000001000100080000000030000004008018000000000400400100000000020038008022004005001000a00f000003c0000150008020002000001005000600100080000040010008008008000000001c00000e0010008000002002800c000001000000000c000000000c0000010008004000009005800000800000a000c0000000008004002004000801000000000080000040100000000000003001001c0020000010004000002000802c00200000000000040000048004008001000806000c00000a800402a00500000000020010030000008000003000000c000000000000200200000000080010038008004000000000000a0040010004016004000800c000001004000c000002000800c00400200580000000060000004008003000800000600000080100140000008008000002000800c000009001001c0000070000000006004002800400000a00080100000010000004004000000800400200300000080020010010034000005000000c002000001000000201100080140060050000004002001000000c000002000000000000a004003c00000a00080000000060008000000002003800400000e00280140020000000000002000000000c00c000000000400a001002800800e003000800c006000001800400000000d000000a000000800000a0000078010000001000000000000100180080040030010000000001001801800000100700280020070028000012001004001000000200100080020060010034000002003000c00a00000080040020010000030036000000000000000f003000400000501180040080020008000002000000801c006000000000c00600800100000000000028004006003002001400000400000040040010000
  | 28 => 0xa241c2007096b0000ac100001ec04b80000c0000018ec00000001430000d6d36b00001ee48a32ad89eb000045a00000000000150086067839a86c63b9c00039d47713e5c0ac17e0b4d000000000009110000a7000000000000190000000000010be00000000000ad119b80002e9c00000006cf28745b32a1032200009e1098503815486e03798ba83cd405607484b700000880644ca50360d172e5430d00007a428e80000000c863c8c00009885501174597000000000000002bb4bdd16bce810000e7f0418bb200009d33494eb51ed0d9600000001fc4e502060c7330bc95614ac00028ac0000000000381400000000000bdd0ab22a4fe70a54483000074f0000fee0f540000fb08b700000001c9837d0a1418a2650a080000a2113b05303ad032f20cc000000093929a47440000000000000024a00000000c751de051600000000994000000027e370c0003b6c1d438400000000fdc3ae49613ad872a0000d9512a024502e4a1c00006434210000000107c338c0000ff0000089c0000000000000100e0400000144c0000000fbb06988081204a562ca82d113b42f12af0d08037c93b1cc000003988d03080cae0000bef40040143b8ca4c1df83e92c94c6125b4d871c248bd003400000008bc367c43e410074c2b34cb000004020000000144407a25344791910000000028e2904ab40000d8a1f3493c2e747e6315090934ec0003d047a2388083b2e2c00007e8000350800000000000d24be94024fb6084c2ce0b08a5503c47012484d401f3099f3a290bc2aec2e43f2c3aa31450563ba41f100010303d200721b5cc02158468b02c45a3298c0001654000394cbe62b3c8721bdc1202e208dd27448bf389c8c227ec7c6357cd2318d8a3e1d0cd450d00c0437dc6f31ea4cfe1114eed382c00000d4e640ed025b0000a0b00007730b0ca0110b803d000000000008c300000000234a8b2a5858c37ec1f900007b5000000033a40003b5c00000006a523ecaa33bfcda7170cbda35889a916145553b90e5a42b8a221be07e01e9908d15f5026000000032280002e080003c8000000000000000c233b345650000b7a000000000006e200000000c30000000000039f40002b8d0b507dc0002c401ac2239022137c5a60000a0a000022a000016b0000000147840a2ce84640000000099007c0000bc2006c4ff1c7c0004090c9c3f80b19247050d36800000028000000000000000000000000000071400000001bf47e31de89a22bf50521a50a042f7088a2fb4b3b38483ac000105d199c0000f880a212280003ed4ba222a8c97247c6bb0c440cc3f6c8a50000493092c3f40958000000000000007d01ba000004480003b690a818e80000000af20b180f93e80d140b60000000040e090c0003e1813439f0e923b3cbdf1f5c623313430f2dc885a22ac8382
  | 29 => 0x7823bc0000000000015a80000000d6932841140000ddb404800000000000000c100000000223cb0a000005c254cd5b0000000000000024d000000000002c98aec000091d3780263333c16e0f6020c3510e870c406561e8000040200001bc856c40d033e3b0886f1f541350000d101fcc84d2d2400018cc0002dd800000001820000000000088d1bc476e00000001f9000000003c2000077c00006fc0000000328109d22400000a3400013d400000000001ebc24d000090b0000d6332a10350000a380a840000f9017011484ae0000000010c6643b640000000afe00008910000abf32d454f134870c058400019505430f945920000000000099500440003e44404332423f14d83cf0b5400003d4000206c5353568d0a31ecf100000339000000009980000000000000037b000000000004223cec0004244cf600000000000000000000010c400000003bc0000f4904f8000000000000000000000000000000040c89321d24e56245047d2788e2f24b425f29700000000e792d800002e48cdf05cc00000002060000497000000035e4000048432c13bc00018f0000000000020080000000e520000ebb2cd400001140001bd46d137740000001075000000035bc00031d0a2300000000000000029c00000000002fcc000198c00000006c92dfc33109787f728582ff00000ad1cbc0001ee0d571bd000000000000000ad30eccaa10000b4f2f44e2300000001a240000000000000000041f800000002e90000000000000006dc9ea000006e3c1400027e40000000000000000030445fc4228ffe00004c40b7cc930d103992b6012a222c6e52ad4233380c46325541650d6000028c49433bdc000000061f3c8800000000003cd8bba2c9c0000f5c58930b88510be483f30a48d8028c6a734a4bd936400002c60d9125786dd1054b412d2858f00004b800000000000e9c0000000000055e2cb80003a1000000008f400006ea0000000079832935e03d623f8000326c78733cd0c400005d900000002fec00000000000000ce20568aae0000032079c000125800018f80000000af3180800000000c332e4d760d78dc41748ea13bf80000afcfbc1e2800000000000000000000000016d800026600000000000000000000000001e5c34c3aa01e92d8ccf230e4df6178015517bc000000000016680000000000000000037248d724cc6ed0974f0905201770970b160e482a93dc07c117702b13db838a3e1c0e008d8e780128cce16406492ae00003e6886c00005212cdce5d1b1c312000000038b840325b80000f501960000cfa0000cbc000024200000003b7400000000000000000000016038083160e743db19d40002fc8000000092a0000000000064a0000000184ce0e00000003784fa30ae04481638a5235f0d3017a879f17dc4bf0ff807f00000000000
  | 30 => 0x1e2ce8f3f040003adc0000000000371898a123860700000a900003c0229900c3da85a2000046e0000124008429b00000000410e2a000039b42a8b6a000091200000002dd02d73744a6a2adce0112c8c45385000023f04da000027216b446f38c439c356453e406c7950700ac42700978402849d3950000404d0a63f48fd317f50c80ca86d00ddc6030000da9402c0002074b592d9cf2f2258be12cc81c100001d33470eb100004ea0a60ba31afcbc500004c617c07043d3400000009a625d800000000001dec38f0000000149400000000002f004fb0ac076900000003544588000022d17a400015284540000308350c000000105800000000000000000000000000000000000000000000006832cf804d1ad00e217d400040b016c37cc43d00003a9039001840f400005c4d8b000047300000cf000000028d4103263818e30342a4266cc9d1888dff0080c253e9c06a1ac08b035d4a902f3c6fe1c5d094000021b162c1b922c498909300bc06682ed400800017300000000e1f3b387113f348f10000000208037400000001c9c00000000002bdc26042d0ed3000013c0e7c00000003880000000000014700010a1000000023989bb2df0c7f25505f9107c09241d0abe205c0002f300002634000000000000000e131d87dc36e432429d0be21e3c48f270c00000006202f9c8b314649ef33b45591da0354061cfdd38a0e9f052ce60398d00606b4ad51a78296000000023788c00898ad60efc000134c49c22641a500000000cd015b06c09000f9ccb117e8200186d050016c0fc0000ccb220043f00003c831280003d4c0612a640000000abd244028c352100325f03e83a8cf94039c46c3f7899c165907100009a82708f6c354000039e876c00000001c00ee635d0fa217b006f395c000352859d00000003c0c0000000f6d00b4f760a4c15d3df4e4b0e5c75200004a71b4819700005450000ce53ce000008e800008d40003cf02ee0000000233ca572a4c39800002e33d810a53c380073d84825000000034e40000000c2c18b00000000000134400026e80001e4c22b201cc6f00008ff00003c603dc00000000002e5800015e400000003b600000003f88000050821900000000000ee100000be000000021a896c0000000000000000900001218000000000000004cd0000ed2396cb0d0000000000096441dcec0364c00000009ec2e0000000000000ad40000000a9230d408716c400014b8000387400035cc0003b710362138000061907b396475e2174d0d23b49172f50546344c00017140270278be438c000033fc8a100006c502144f6083c586080800015fc40b0000d2c00005341e40e190ba80001788ac910f0e1e26dc0c729bc000205489f1dbc9de3ab017a2cf4000208c0000000000236c000000067110ac00000000000000000
  | 31 => 0xb14889b4000000000000000000000339c9b31724d010f24d8f2b70a51283067b00e09b517d000024bc9fc260408a11fc5ba27141a200000003108000000000000000000000000000000008388390000c380000dfa00001f300000000000bf806a442900003f505a106033ec0000a9c0000000959000069d07d035022301ca072c00004440002b809700010000380040f3770000000093f0000d9b0000c5b004cff3310046a0000e8200000000000b45116c74e1b58f9b29e83372614c5e39ac4d0355800039d81fc000000000000000000f18026cf4b0000b611b100003fa400000000000000145082c01a19400000000000000000000000002c080002cc400034740002dec73b00004e9078c4c300006061ef80003b145a1195416a3180037000000000000000000000414425241943b0279ccd84248178074437100004ce15f000012b08d63e00765158c37c000090500010b00000000011cec939b8f3400000000000000000000002700fa0000000003cd070c506c22dbc0000000000086844721540003408000172c00010701250bc00a118a40000000010352c6df000000015447220f400002084ef30fccd7e403c0000000fc4239438c00000003becdcb0000b2300000002e940000000000000013933b00f2104cc4634a0000000000000008e01fe4b6c202c30600000000000b5505f81fb3ea467e00008760001039000000000003761ac47ba11401270cac0002684e3a00000003de0b690fec0401d5464732fc000030908e3de800000006842cbc000225c6450460dde00008e4271800000007a82740ff6310c042182c66a00000002140d4e000000000002fd000000000000001c18f47259c0001398000060c0002fac6483188000000000000004eb00000000bf800000009270000873000074b2e8419d1c700001e7082d15c0e210000ab9194c6ef2538b1302d000025d48a7296d02b192d0c20000c4130f8cc21a58b29000000026bc84a0000e6c00f01543d40fa80420bc62c3034801f8e8e26e4f681084b1d0d5c920417055b34880003b28a1f0000d7a000017b00000000000000000013300000000000e1b0000090000000008885030eac000000058d0000e652ffc91e3a14d7229f0f371d1c00038f4f723354000000109f12085261f1400000780000cb400014500000000000138c00000004de0000d4900000002df451f227901a04340002eb8eec000000013802290c540002f5416404a405d0000000000016f00bc0000000000000031e34e0000000000005b4000000076400000003c5800000005442160355000000000003130000b523064000000091a138846526ac000000000018d00000a7898b0fc000000000003bd800030f400039cc5401cb000029dc0003c3045e14a4fc802ec8eb00003a5000000000000000000000000
  | 32 => 0x6cd2d1dd05c1323c9262f04bb6045833b0e1c8690000d1a000000014a00000000000000000000000000000a950000aab00000002c2cf75000101c2bfc687000082900000000000000000000019447de3204000000000000007c03d489f83550ff0311c00041205483b94a1a23a800000000d60758f5b02b8824000090d08c0d1f3854000000002600007c90000dc71b34894000050a0dd4e3e0f78b9940104a93d78012148087412ed0ad258c20d0f2cc723984cb200007560000c563690d9a3e2400021dc0000ca0d4d0000ee000d000038946de3bac00028b0d1130b40002204453264000033ac000000074a09f40000000000318ccdc42d8000116493e274909624b06a40b6836f2ef88163930b53000004b000000014090050000000370800000004c7251400030046811f507bf0ec83c4000049e15c40000000000000034b00000000000738184482817f89b8000000033000003ddc7f5000000038f00460c15000000000000002ec3a500000000000000008e10c0c3400002fb1720f0d257cd92043052f20c0cb4020033c242056700000003d380000000adf06f4e9704c4ec32bd50572248d85122453f29d400001309360000000000000000000000bd0fb90ea08d50000f4c0000a5f2dad02e00000000000000174c00023d8c711d840001bd86da000000000000000000af80000bf9000039501a400009d8fb80000e3241080003cb8f2a0000bce2950000266400002a9054304842541980000000000000000019dcf5a153800000000000000a68292ccb300003f20000ade37e00000000000000037a3f580000000000085400000000001048605000000036e800025c4491218c00012640002290b650000492000000022bc000043c00009d479b00005570000365177c0000000000294c0001680bd33a745e800002320000b0411e85f60dc89e80294aa7353c4c807f850e000000026c84691a486403dd06170e34b8137b4da21cc4a6739dd0951c3c72b018c000420000018910bf1ec0b9f07fc000417c6d40f28ea216448ca309c00000003ee095cea52e9000000000002ce40000000000000078334000000000575358021d3f1407301c010133f042c25a0a3c00001a40794064000000036dce0700000000000b8c1a38bd01904edf00000000000a1e305c8da30285a730686e61d8000000008f000000000258000000000031ac9db25200000000c4f36bc000000041e207065732980b300000000ae8000000000000000000000000000000000003ed0a44000116006d2b0039319d054c257400026f8ffd0000b730000fa509e84dd04bc8360000eb31af48bb29d84323e7c70d1eb40e9000000036c4c580b6c1850c1071611b4d8200000001c6000037f84410000022000000000000000000a4000000000000000000000040bc8b516b8b1
  | 33 => 0x210cf0b37bc29d2b500002cc00000d4c000000067f000000026f0d0442049e01fd8000000000008e000010d000009eced50000f552e4c0001c088c619382de25102d027980001da84230bd891900000001e30000000000000006eb00000002d983822f5c0000000a3700000000000dcd00009fa31f44f00348e4e1dc01b4243cebc00000001fb40000000000053c6a8000000022e47dd2b1c000292000021f0b060e6819b2860ac327f4000127c3a20000d5e000070819bcb3c3fb0fe621805d4323000031387c8106806c11c8d2a00008261fb0d26286cc660c081bf2b5cc08000000012800000000d892004a4e3dfcfae1ad864611a0ff4246d06d33e06002d5c2142eccb421a688d200000c5000000029e1017312c9511c648d3000000000001cd000014015dc00017610c13ca471b09dc4ad2674a473c9036200000002fe80862fb028100000003fa802b2e2800007d8000059c7f033505d5428cb5d00000000000000000000042e8b771d50ac207848ad048c0003e301f00724cdd000064c00000000000000000000000007aa00000000000af637a80002fc47f417c4d7b1eec01900cc2a307880d535fc8e31c74aac066400039d00a00000bde1600b0000006be02d8772317c000000078439bc0000000000105c370226c0fb2b480d93120d4c256cd2f07d4d0c000080e0000b753ce41b21e5000026f40000000c5a22e871e10303a615d075723dc0000f3035a2e78f8a2f94da817c84b922240313220c870000000000000000000000000000000000013dc6ba37301cc0ab4000000009732a40001110cef3484fd131710c30d1c9f7410464f3b587d10000000093c00042f4000132c0000000000383000000000003fb40001cccf1d0e9c0c602fc0001adc000278c1570024a360f1400000002c51460e5f3a80000000000000000000000000000105a00000000000000219c5533330b9004e8000000053b0000e0a0000866000000000001932de00000000eb8000026a1bec000272c000000000037b0d2b29084010c2cb48000031f2c544e80000b1f2d40b4c38b034e00004e1412414c1e78d810a809651d6c2ab16b0e16285462b0e58c8b076ccc61c9000001ec69c00003420000db20000ae21700ce63ffcd99000000000005150bbc0002c2000028c0b4400003030000af40a3c00000a400021d4ce40000fc300008cc281899320ac0251dd4b383c849d41e9cfb200007b72f24d1202bccf00a2c08c0b310a21014000000054132e0bac1220000184800028b400014c40000000efa328d0c6077400000002cd032000000006520000000284800022a060400007b3000061400000003f3cf692b84a2f0000000000000005d400000006e718a81840824000091cc7a11006aa2808c77000055600000002cac8fa1c2c3262214ef81934b5f2a
  | 34 => 0x61066d21acb890000b360aa8451000000021c0f7c326800000005820000000000000016dc0003620aa8213cfb30b2400027a4d3c2ccc78606d800037e4c060000000183cbc40cc000000000000000000000000010e0e4f000061538d43a000003ff41a4a030c9444f1f10e112a604b63f3015c2a306183cf4aa42c900000000d3f2508385431c000189472e2158f423e70d7d19640000d2815f02040000b28e9e000056616a429a0d84a343ef88cd0e1852c000000007c87673a441d0000108f30300000000000000000003743c10000000000000000005b432f42c10e380001394d310000000169055c00006b311d40003998d9d0000efd00000000000ede000036440444800000000376000019f103b0000c212418cc525ec00008f87893e0486800005bd32aca46279000000005e100008040304fe540a411c0000000109800004287a505487a10000845000075c000000000004be3670ba91064000000089a3fbc000000000019a5018000000000008cb00000b500006ec08bc000143cbea3ac000000007052d180000000a2900000000000000000000000004f32fd44c00dac0000000f1100000002a7c8140338f1c24080003cb400b3f28ad920e8015079000029141591f681050e0c0002dc4d6c06aca2800383693834000324104402900000000d5c035c8d93eb0a9c0000000000000020d00030000000418cd650000d701cdc00031a4b2237f000000004d900003be2f289da320c0000000000000000000000000424bf612d4000000054b00000001a6000023b8b3f00000002a78000000042d30d84b3065473e0000c3132dcd460000fa1000021e3a183ae42e40750000ef1171c0000000dd400000003ebc94f30ac0002dc0b5b3d44c4c00d8e182a50aca13540001e147ee000063200f80e8000108b050460a0d70051112400036a887901207d9336c729000044d0000000000000007ac11d0000000000080a00002fc00007ca2a1400040b447800000003ff01ce2734ed8419c25300007e8000056e00000001b8406b0000b4e02e00002c1c931005c9412b2c01f0000000187004f1dacd352218000000000000000003ce80db0000ef525600000000000000000000000003e3cc6d000000000000000000000000104e000066c366000000000002b200001a18a503fc43f128e4ffa08201760000b0e2164ec409bc000073cc9400000001cfc287304c000000000010345b8000027036d0000040807709285991628e6d0000a580194dd00000c1d17443df000000036e1078000089d000102a016059e2ec009a16fc000000000030c80000000189000054913e00003e582f8104063f00000003f1c00002506d83a6c0001c0c0000000ed01bb87b20000a3200005c410e80000000000000000000000da0000000147448b0254000000000000000
  | 35 => 0x1b83f2484b01509031738e260a48273000000000000000000eee0000bd2252800004d8d712658000146c85f00000001df400000005a80000c2628ccb622f6000008489602df8000374c00007bd0533b308b8000000000002840f7400000008e20344000000000000000000000d770000000000000000002680bd40002e98e1a00002101fe8ef4000057e081cda501f4f8d3fe000000009230000b5624dc8df00000000000dd501d05e30d48997407906f00009dd302c32034cc00000000570880806326011b0000000206800026c40000e000ab1ce40000000de74218f44044c000105000024a40000000dce32b40000000091000017208f07103f8ca880e04bab0000000238400000007b12edc0000b9400000000003a2c000221c0001a989ae23e40000000e6915acf0000000000000e7e000000000003431404fc21c684cc1fecac62e5cefc000000011f865f0000000000000000000000000779343cab00accf591984237067c95c16f0cac133c0003928ab230540cb02f4000000000000000001e74000375c00000005093fe4fd53f642482f0ccd11184c1800000003e645c2000000000006d500000000db80002ba400000010ac1c840000000a2e00000003304fda0a0cb031ab8433000000000004980b503f937c4b540b9ca142b14c64149cbe8131454d196028000005b523b044241e465b00e8fbf38e062124903681cb42e200000001eac000000000000000002c5000000007c740c4a620000000330c812410c0003e782a6035023112d00001138f8b00008f3390800000001a1000000000000000000eaf1e20000252400009180000000f540000f2700003f80000000075c27f3090fe12a2845c29ec6661a6d083212486d0000000000012d40940000de4d5d03b00b727581b12ee4dda000036321b800000003bd2978f1f000000000008c80d6400000000002598e2b00000001cf00002428c3a00000000000000000000022b800000000000000f2b000039e33804ab22800000a94ea70524aef2824ae60d182342178871283463d0000c3b13d04d7334c000172814600005ff01485db23e00830168a890ce006614c893d0000f4f3fdc1fd25dc000417861e000000033e45b900000000000000390c564314c0003aac31813f059f0000000045c000331c00000006cb3ab8f5c245457a3a6000039c400000008c10000000255c00000001c41868f310000aeb04b089300001a80be8f462ae901f398822e256896f00008833a98619146869f16047d80000cf41bfd0a40000000101cdf517780000000000000073441cc000000000000000001e68aa503703ef05e4251363050800009ac0000d240440b430000000013800013b800000004dc289400016f800012c502000009252c84f7b15e06a11b0ca8f000000000000000000dbd0074ca21
  | 36 => 0x81400012340000000e1326106a920408530f8c000000000000000000000bbd0154000024c4462210000000000042800000000707000000012f466225307531a5c76d3c3ce24420868f2be8eba18981a313f8000000024100004180000f1300000000ec431a0000000408425927d4000175d037000000024380000000000000080d3e10000047ca2a3320fe839047eb000000005342c734140000000e403ed0000000000000000002e60000258800000006e922b00000000000000000040fc0000e2c65d0000de40000b830b210b301e02110180f30283c9ee38a46fa000026e371483e000068805f04f1216c000000000003100001e3482200009830d340001eb000026c00002aa4d2e00004a10000b9b20641af2934000000000000000003254000000000025e8e5804fc00000008652350d270000676000000000000000000000303c00000000001ae468d05f4b5e000080f12880002e100003f6109c1794000000000042c40003a0c00019a00001c54a820c240003b208b635600000d98ba00fd84ba27109822ff8512261c9df0000f8834644560000ea4303800003fd03e0000000000000000006bc000000000009040000000000000010000000630000000083c0000000078000000000710000e3b0828f922621087000000000000000000af92150000382093800009a73ba0cd6268c6391be400042c9014000000000001071b8c0002ed400003784083d98000418400027d0c5d3fc82280000ccd26183fd24ac000200c000077c0003e4000025f4000000000038d8b8600000000da82ac019c53d2d1c00041a801613585330000d3e00000000000cbb1d886900d74de500000000000f1500003333978aa6145c7fc27d8d1b1a80cde33b8dbb0e8c00000000000000000399c00000000000000000000000004c8f0800000000000000112c3e1167000000000002964f1a000000014e025405a48780000000000000000001803a0000000007ff109c002000000000004550eb4bcb000014a00007df000051c19e8f7100004112548000022c2d6121c0001cf41dc0aa02163598bdb0000000000046706480000274afb09a43eb2e500a63c18f0a00004ca3cb00003dbc85c34c907d0000c6c000000023a4ebe0a5c751347800010e400010bc05000000623c780002b9400040589f00a7cdee000000030f01da09f017f000000041d875f00000000000000305000024040000000000000000000003bb23f482c00000002b9000035a00003e908c941e833f000000000000000000000000025800010a7000000036d4000000000000000001b3024438fc00009c400000003b500000003fd4000000081100000fd0000137000049b0c8c57600007d61d080000000000354c71303bc2cb08940003c94f9800000003914000391c0f8039426d281452d038c
  | 37 => 0x8000000000000000003818000179c03905980000ee81d8000000036d86ac0000f0400000000000115340c4fd2a000000000a790c5c45701240000000f190c6c00014dcf1400000000000000251800005880002148dd21f4cfb1000000010a866000000001a5400020f40000c700000328000385c00000008b4000000006600000018126000000003000002d2c22403d8aee1cc800000000000b84b0f35b800000006ab09b03910000000241c0000000000288000018349c9000000016601ed3504c922a740000000e37026428a1b7038404f41511ad4dfd156084123a09fe19e40f0271c9ca00001ee32903cd04640593d9429908844853f50b4002a05c61fa4e51231cb2023100001c806280714000000000032100000000000239c000401c00033a800000000000000cb60cd8dbe14e8420000061d183907f02e86ce0000ea900000000000000000000000009c800010bb2e44cf5000000000000001588ae70000000388800029f81d500004a32754000000000000000000dcc00006040003d7c98c425cb2c00004431b20000000000029cc000375836c3a64e5c00007b600004a4000108906f000034540002b400000000000000019e2ac4d5525a412b209c7a3062c75933649a436ccb870c740001d6855d30fc0000000000000063528f50460df846b413474d00004f20de057b23bcebd04a0f823b04000000103c09680000000000000000011d05f33d74547043865c1128f633ccc5d00ba0523000024911f09c100010270000000000000000007bd000000020c4000000000011ecfb000000000b481c3000000023700000000000000000000000003340cba0000cd71ce89ed000028242bcd642f8c5aa0e40d6b00002d3215c2c00b9811e00007f20a50d370f6800000003a100007250000dca000000000009a53d9c0000000bfd211c0000000df000000000000bcd000000000006e4000000020b800037d0000000000000000b22ed0cf11e602b24074b2d21841c70000d3d39ec4bc09e000010250680af000034d10c03d281c82f80d6700000001ff800000000000000240281c00132a89cf000055a1f6cc1600000ed36ac00000007351820a911254000000000035a800000000001b640000000000000000000000001f0c7ea25fcfab000000006cc0000c040003d88b05284c03f3000000000062e15502740000000319c0000000fb7000097918dccf70000a4f31f90701058adb00ec0c91e0420122887e736100000000980423000037c800000001a7000060931c0c9610dc000212000000002eb3d5c2af29940003bbc00000001561968d9e12503273c5c7ae2c4901932240000000f2625f8000245800000000003f5c00037a492e0d9c93541ac00000000000000c0900000000000bb80cb80000000000300c000141cd9400000000000000
  | 38 => 0x30c0000372000000000000000000000000016ecd521f3cd3a3f90130000050012306f0023c10b2a185e42acce4812bc00029b000022c800023c800000000002c24000243079203b89f30a887500f703d22ba0f4337ac7233a34d0e164d0553f7c2b909540003e14ebf000000000002030000000000075d00a014e3164fc6139c7910000c1b0000a6d0340de808100980cc87990210506169498f37641b5173c7c20fe86d30cf4e49118881e2928b8f0ab8c57058cc22149000000009b6000000042a4cda2a0c8d12270a7f1198ec6365c477000000000000000000d180000000348000000000000000f9300000000af40002b745600000000426821f18c4000000031900000000000d802668c500000000000000000000000d0400000008be0000c3304ec67d014c0760000f950468c99000037f0c380000001064000050c0000000248905b0000c1e000000003d10103700000000000000000002998000301c0001ae0436291066b2ba902825007770000c1f1c389ce38250722c70e9515cc96a0938e8c252c0002d4480c027c00029ac0004278000411c0000000d09290caf02f2088200002b440cc1ae1a88cca1abc7fd10744900b7435f1d042392bf0f070b100002100da13de47283b1c0000000a5a31a800027600002eb400000005ab17ac18d3cfcdae000042820a8bbf0a4033a0000000377c000099c79636c10b83ba8f3e00000000000c650000000000000000000000001085000000032005da00c00823214c8e085d04c0940000285cfeb2db4c9e0000a3f25c857221eccaf20d400000004aa0d6c000391859b000062f00002e00000000000000000006db00140000000d8e1804e4400000002c6800018580002e34000000000022200002db8000157c000000056d41b8a6118c00cd286400026789470000a2713600000000000412c00012685941a8cf2800009ad0000aa039c030a42dc0002c44000000000010ec7f800001aa0000fad02c0000000000000000000000041177400000000002c780002e680004054c52000000000000001298000000008941b07482a04b641b04dbc2da000000000001294baa2d6000010d4000378800000000000c1c0001d010990000e04000000038cc4600000a26280000000005830000cc4264870a324400021f4000363400c0db48f53234aad338487f000078e31542b60000c49000000026a80000000e4d00000d342600003c0484600000000bc90593fec0000adc000383c0002d700000000d0b000081300000000000f640000000000000031e000024e800000000000000000000100d0000de33f38a1111d800020146383f400231a000002b6832127706930edc52a106c1de2fb8cbe00000002fd080900006ca000078000000001f2c0000ebc6992990b8539c800000000000000539218
  | 39 => 0x2c2c04fc00000e1c2e70b34000026b0000484141000000000003458000067000042404db21e8000000000027fc0fe0f984c200000000000a600000122283800013e800030a800000010232890bbc25d05cd329c21c0f38f4500000001a4460c3c0800000007ef3d5800000000003618000413c00000000000000d061f940002ca0000000000038b4895000056811c0ed142200003584c793110bb10f0c00038d0ead07a89a02a346722a5c2880d3c3a40000e902b385b2207c4c13a249cc00b804415a4000244d0933bc838916c000033486271908f9d0510bbb36b4a1001a068206e805e0e503d317b468500005d63ef400029f4da33b2c18f360c7581dd8e55000015e0000ce81f48673000000007e000006ec00000007e105600000fdcee21ef0000113022317ec3b83e0c6ad2b300000000faa3d6000000a800027c4b5a1a300000000000000000000000003aa8000200109b3a6893014140000000dcf0000d4701e4f8e00000000000000000074600000000000c820a7000019c084c1b000002de45ee0d443562fdd06230dc84420dc34500000002764000161c0000000000054ce8815bced4144050b00000001d8cf400af8aaa2314188000000041280001c4800000003d13a4c0003c481d900007ce2338f731a28000000023b2bc466510908643df8bd618b4e684114000000087e3ee8f1b31a03d929c49f22a68832000017436fc7e23ac8f6b307000012c03601ac84d431b83e01798fa604e0b8e0b3c89803a84c92abcb1707a09e53be427914f08422f1cbaf2fc000036982dc00000000f1caa2000028611c40003cc81be34d805f26fc7362a1c0f329240000000bfc00002bb000023d0000000000077f00000001d98c0525cc0000000000000000000203ea31f0000327ce96297400006502f3117c00000009181840c2808b04e4000000000000001978000000000000007450000e3900010c529b8000000103a071800003ac0001018000000000
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x56210c30a4581d516210c30a0c86551424c830c88641c1424c830d05545c84394430b05841493294430d06545c84354430a4686d493254430945829cf6454430a24825906454430a30805906454430953805cb4354430947825c34354430d41729c04354430d42725c04354430951801d33254430b4280dc93254430a44865093254430d04745093254430b40805093254430a5380589518c430c4772545608c430a4582191510c430a5185985600c430a458298d5190030a458219151cc030b428294d514c030c51615c06194f20a0d8694d4210b20a51831456010520a148454d610c120a0d8414d6210c20a458114d6210c20d04731c55410820d08731c15410820d20711c15410820c0f875516310820c0c875516310820e07815516310820e04815516310820e08805516310820c0c76551434c820d09541c1434c8208a8845c0614c820c0d545cc6250420a0d84195324c4209c1801c5324c420ac0814c8604c420c457558c4108420d09545cc42d0020c0d545ce6290020c49655cc4210020c29651d13210020ca1761042110020b21851042110020d81731042110020a888458c3048020ac08158c3048020cc1635c43048020a51839856015310c0d7458e5210b10a0d8414d6210e10a45821916114d10a51801916114d10a5180d896114d10c45725876014d10c30541c16190d10c30541c1610c910b05821cc544c510b11801cc544c510944855c8434c510c44655c8434c510d04545c8434c510c50655c3324c510d10545c3324c510e1054d8c604c510e1383150604c510e1083150604c510e1054d4c604c510e105414c604c510e1054d0c604c510e105410c604c510ac18210c604c510e2054d48604c510e2054148604c510e4053148604c510e1054cc8604c510a50854c8604c510e10544c8604c510d10541c1310c510d40521c1310c510c14545ce61d0110a448558931cc110c447558931cc110e045458931cc110d10541c131cc110cc1621c131cc110d10541c1314c110c1576152310c110c14545cc61481108558714c6148110d20541c520081109c1831c52008110d40531c52008110a0c845886254c10c51535c26190c10c51535c26190810a528754d6010410a508754d6010410e4153dc96010410cc0731c96010410e41531c96010410d11535c04190010a90835c06444010aa0825c06444010a16849915344010c16761915344010c14761915344010e11801915344010e10641c15344010e046454f6244010a448654c6244010e046454c6244010e106454e40440109508754d4044010c507654d4044010d41531c94044010e106454f3044010ca0649cb3044010d41539cb3044010c31751903044010c90649cf20440109538754f2044010e106454f2044010e106454c2044010951859ce4144010951859cc2144010
  | 1 => 0x33c00000c80000000027000d1000013e0000000a4bf4280000010000000000000000964400000000000000000016140890000000342e93400c50000052000d000003f068000000000016600000000600580012a0000000c6000000030ba0828c00c353b88000000000008f00000000000000000000000008d548d85a0000000b80000001b4000004800000010c00000000072004a000005a53001962c0000000690000076000000000502bb34008e400000000003257c07498858e001000000000b8315c1c460010eab3d800009d0020c00b859194000000010001e00000000018850140018001360b258003600248000000000000000380000000000800004040100001003000020000300405000020000000400004000040000400000000000300c0002402000060000200001014020000000000004040000301003000050040100404010000000600400010020080d0000200000945829cc6054643b0681dd14354843945819cf6054843a28845806054843a60815806054843a50805846154c42d05539c64350842a448654c6150842a4a8654c6050842a488654c6050842e4153d846050842e41531846050842e095390c6050842aa28190c6050842a47815516210e32c0f645c843546328c687d896190d32ac280d896190d328c4865c64350932d04545c64350932e045418c6150932e0854d8c6050932e085418c6050932e2054d846050932e20541846050932e09831506050932e0854dcc6050932a89841cc6050932e08541cc6050932ac1811cc6050932a4a8590c6050932e085490c6050932ac18190c6050932a4581d516210c32c84641c5424c832c88641c1424c832d05549c6434c832c0d745886294e41c89631c14210a41d0a531c14210a41a49831486050941c89631c14210841a85831894250441c84731894250441ca0621c14250441a0c86551424cb31c88641c1424cb31d09541c1424cb31a48805516210d318c5879886110d31cc2625c06110d31948805d0524c93184d87190524c931c0c75191424c931c88641c1424c931894845c0614c931c46655c843d0531b04825504310531b10805504310531d05545c84310531930805d052105318d1801d93210531b05841493210531d04741493210531c86645c843cc531951801c53214131a0d8494d6210c31a28845486050831a0d8414d6210f21a0d8694d4210821a458194d6210f40c89631c14210b40a518194d60ccb40a458294d6190e40a49839486050a40c0d645ca53cc640d05735084214540a458198d6215330945819cc6454b30a28845486050b30c0d7458e5210b30d067454b514c73094587948514c730e42524c5600c730a458198d52d0330a47815516210e30c88641c1424ca30c0f645c84354630d10545c0414c530a458298d61d5030a45811d
  | 2 => 0x4f000000000288007300155b600352a1345b0014da6000011012d7001f8e4000014400130013050000017c0086000000000000000015000000016000000040620014a000000000b9000017a00000000000002900000000006ad6608000000199d00027240000000000f1c20017800000000001b2000000000b70000094000037400000026400d200000000000208f01f3d00178006e000d6ac07000824f30000cc4e3080000670000000006f00000003f80000b56a338007500260fa376c2b400000000000000000000050000000001100000003b800ec0000320ac32000004aaf23000544537a44000f4b80000021237d16d5118007000388000000002c4000000000000000001808168044000000000006e1d1b010b60e8000000660010800452400000551658ce05d81884003e09800000000000001700168001f0000000343088e54159787aa13c8000000000019400491880064368
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x5cd38f28c2d048200000958000010001c1c505918301101d01501b00000851a6137810a00618310e585a0153a06431814210b0090c2a2e321a8499680151811cc6050932d002a303218c0a12654819318870509411068112caa0e0a126598d40241545c84310531980483082926420a63105981d0524c8414c622128c00e2990a098e01218745093254430c803a100a1264a8861804872055458c420830110e402a8b1884106802048055163108208c04a30038a64988418217661441084400832030ab98821088010520251635c43048020b00c91062a0c098a21240956084318131443400a8c10863026288510255621c131cc110e002a2c438263982219005460c714802044228330298e2900408851025d531c96010410a084bb00322a688021600926006454d10043800c8a9ce59822008604e1c6454f2044010
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 40
  | 6 => 1844
  | 5 => 9193
  | 4 => 4297
  | 3 => 227
  | 2 => 31
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
  | 5 => packedAt gbK5 (392230+((h/3064+packedAt gbK5 (349334+(h % 3064)*14) 14) % 11032)*15) 15
  | 4 => packedAt gbK4 (229169+((h/1432+packedAt gbK4 (210553+(h % 1432)*13) 13) % 6862)*14) 14
  | 3 => packedAt gbK3 (14370+((h/75+packedAt gbK3 (13620+(h % 75)*10) 10) % 529)*9) 9
  | 2 => packedAt gbK2 (2261+((h/10+packedAt gbK2 (2201+(h % 10)*6) 6) % 45)*6) 6
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x1fff80fffffffff03ffc0ffe0ffffff98e3fff
  | 1 => 0xe03fff01ffe03fffc0fff07ff0ffc0fef1c7c7
  | 2 => 0x3ffffe03ffffffff00007fff0fffff01f8ff
  | 3 => 0xffc0000003ffc07fffffff80000fff07fe00f8
  | 4 => 0xfffffffffc00007ffffffffffff00007ffff00
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x4184a614282489100b2c42960152c948861b5b
  | 1 => 0xca8d0a4c50439232c054d22a506558d2b0c5c5
  | 2 => 0x952a14289a8924655502884d6a09b2a70168ae
  | 3 => 0x62c58b163120779a69aeb01484e3cc7da00f0
  | 4 => 0x183060c1821c384e38e30c718c8020056db600
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 31 gbPos gbNeg, 0xeee8a080eee8a080eee8a080eee8a080eee8a080eee8a080eee8a080eee8a080eee8a080eee8a080eee8a080eee8a080eee8a080eee8a080eee8a080eee8a080, gbN, gbR, (fun _ _ => 0), gbI⟩
end PEqualNP.Outside.L_meta_12869
namespace PEqualNP.Outside.L_meta_12869
open PEqualNP.Outside.L_meta_12869.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 31 := block_range (n:=31) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 31 := bgb_2_0
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
theorem bgb_3_224 : Interval gbAtlas 3 224 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 227 := (concat (concat (concat bgb_3_0 bgb_3_32) (concat bgb_3_64 bgb_3_96)) (concat (concat bgb_3_128 bgb_3_160) (concat bgb_3_192 bgb_3_224)))
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
theorem bgb_4_4288 : Interval gbAtlas 4 4288 9 := block_range (n:=9) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 4297 := (concat (concat (concat (concat (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96)) (concat (concat bgb_4_128 bgb_4_160) (concat bgb_4_192 bgb_4_224))) (concat (concat (concat bgb_4_256 bgb_4_288) (concat bgb_4_320 bgb_4_352)) (concat (concat bgb_4_384 bgb_4_416) (concat bgb_4_448 bgb_4_480)))) (concat (concat (concat (concat bgb_4_512 bgb_4_544) (concat bgb_4_576 bgb_4_608)) (concat (concat bgb_4_640 bgb_4_672) (concat bgb_4_704 bgb_4_736))) (concat (concat (concat bgb_4_768 bgb_4_800) (concat bgb_4_832 bgb_4_864)) (concat (concat bgb_4_896 bgb_4_928) (concat bgb_4_960 (concat bgb_4_992 bgb_4_1024)))))) (concat (concat (concat (concat (concat bgb_4_1056 bgb_4_1088) (concat bgb_4_1120 bgb_4_1152)) (concat (concat bgb_4_1184 bgb_4_1216) (concat bgb_4_1248 bgb_4_1280))) (concat (concat (concat bgb_4_1312 bgb_4_1344) (concat bgb_4_1376 bgb_4_1408)) (concat (concat bgb_4_1440 bgb_4_1472) (concat bgb_4_1504 (concat bgb_4_1536 bgb_4_1568))))) (concat (concat (concat (concat bgb_4_1600 bgb_4_1632) (concat bgb_4_1664 bgb_4_1696)) (concat (concat bgb_4_1728 bgb_4_1760) (concat bgb_4_1792 bgb_4_1824))) (concat (concat (concat bgb_4_1856 bgb_4_1888) (concat bgb_4_1920 bgb_4_1952)) (concat (concat bgb_4_1984 bgb_4_2016) (concat bgb_4_2048 (concat bgb_4_2080 bgb_4_2112))))))) (concat (concat (concat (concat (concat (concat bgb_4_2144 bgb_4_2176) (concat bgb_4_2208 bgb_4_2240)) (concat (concat bgb_4_2272 bgb_4_2304) (concat bgb_4_2336 bgb_4_2368))) (concat (concat (concat bgb_4_2400 bgb_4_2432) (concat bgb_4_2464 bgb_4_2496)) (concat (concat bgb_4_2528 bgb_4_2560) (concat bgb_4_2592 (concat bgb_4_2624 bgb_4_2656))))) (concat (concat (concat (concat bgb_4_2688 bgb_4_2720) (concat bgb_4_2752 bgb_4_2784)) (concat (concat bgb_4_2816 bgb_4_2848) (concat bgb_4_2880 bgb_4_2912))) (concat (concat (concat bgb_4_2944 bgb_4_2976) (concat bgb_4_3008 bgb_4_3040)) (concat (concat bgb_4_3072 bgb_4_3104) (concat bgb_4_3136 (concat bgb_4_3168 bgb_4_3200)))))) (concat (concat (concat (concat (concat bgb_4_3232 bgb_4_3264) (concat bgb_4_3296 bgb_4_3328)) (concat (concat bgb_4_3360 bgb_4_3392) (concat bgb_4_3424 bgb_4_3456))) (concat (concat (concat bgb_4_3488 bgb_4_3520) (concat bgb_4_3552 bgb_4_3584)) (concat (concat bgb_4_3616 bgb_4_3648) (concat bgb_4_3680 (concat bgb_4_3712 bgb_4_3744))))) (concat (concat (concat (concat bgb_4_3776 bgb_4_3808) (concat bgb_4_3840 bgb_4_3872)) (concat (concat bgb_4_3904 bgb_4_3936) (concat bgb_4_3968 bgb_4_4000))) (concat (concat (concat bgb_4_4032 bgb_4_4064) (concat bgb_4_4096 bgb_4_4128)) (concat (concat bgb_4_4160 bgb_4_4192) (concat bgb_4_4224 (concat bgb_4_4256 bgb_4_4288))))))))
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
theorem bgb_5_9184 : Interval gbAtlas 5 9184 9 := block_range (n:=9) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 9193 := (concat (concat (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)))) (concat (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 bgb_5_384)) (concat (concat bgb_5_416 bgb_5_448) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544))))) (concat (concat (concat (concat bgb_5_576 bgb_5_608) (concat bgb_5_640 bgb_5_672)) (concat (concat bgb_5_704 bgb_5_736) (concat bgb_5_768 (concat bgb_5_800 bgb_5_832)))) (concat (concat (concat bgb_5_864 bgb_5_896) (concat bgb_5_928 bgb_5_960)) (concat (concat bgb_5_992 bgb_5_1024) (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120)))))) (concat (concat (concat (concat (concat bgb_5_1152 bgb_5_1184) (concat bgb_5_1216 bgb_5_1248)) (concat (concat bgb_5_1280 bgb_5_1312) (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408)))) (concat (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 bgb_5_1536)) (concat (concat bgb_5_1568 bgb_5_1600) (concat bgb_5_1632 (concat bgb_5_1664 bgb_5_1696))))) (concat (concat (concat (concat bgb_5_1728 bgb_5_1760) (concat bgb_5_1792 bgb_5_1824)) (concat (concat bgb_5_1856 bgb_5_1888) (concat bgb_5_1920 (concat bgb_5_1952 bgb_5_1984)))) (concat (concat (concat bgb_5_2016 bgb_5_2048) (concat bgb_5_2080 bgb_5_2112)) (concat (concat bgb_5_2144 bgb_5_2176) (concat bgb_5_2208 (concat bgb_5_2240 bgb_5_2272))))))) (concat (concat (concat (concat (concat (concat bgb_5_2304 bgb_5_2336) (concat bgb_5_2368 bgb_5_2400)) (concat (concat bgb_5_2432 bgb_5_2464) (concat bgb_5_2496 (concat bgb_5_2528 bgb_5_2560)))) (concat (concat (concat bgb_5_2592 bgb_5_2624) (concat bgb_5_2656 bgb_5_2688)) (concat (concat bgb_5_2720 bgb_5_2752) (concat bgb_5_2784 (concat bgb_5_2816 bgb_5_2848))))) (concat (concat (concat (concat bgb_5_2880 bgb_5_2912) (concat bgb_5_2944 bgb_5_2976)) (concat (concat bgb_5_3008 bgb_5_3040) (concat bgb_5_3072 (concat bgb_5_3104 bgb_5_3136)))) (concat (concat (concat bgb_5_3168 bgb_5_3200) (concat bgb_5_3232 bgb_5_3264)) (concat (concat bgb_5_3296 bgb_5_3328) (concat bgb_5_3360 (concat bgb_5_3392 bgb_5_3424)))))) (concat (concat (concat (concat (concat bgb_5_3456 bgb_5_3488) (concat bgb_5_3520 bgb_5_3552)) (concat (concat bgb_5_3584 bgb_5_3616) (concat bgb_5_3648 (concat bgb_5_3680 bgb_5_3712)))) (concat (concat (concat bgb_5_3744 bgb_5_3776) (concat bgb_5_3808 bgb_5_3840)) (concat (concat bgb_5_3872 bgb_5_3904) (concat bgb_5_3936 (concat bgb_5_3968 bgb_5_4000))))) (concat (concat (concat (concat bgb_5_4032 bgb_5_4064) (concat bgb_5_4096 bgb_5_4128)) (concat (concat bgb_5_4160 bgb_5_4192) (concat bgb_5_4224 (concat bgb_5_4256 bgb_5_4288)))) (concat (concat (concat bgb_5_4320 bgb_5_4352) (concat bgb_5_4384 bgb_5_4416)) (concat (concat bgb_5_4448 bgb_5_4480) (concat bgb_5_4512 (concat bgb_5_4544 bgb_5_4576)))))))) (concat (concat (concat (concat (concat (concat (concat bgb_5_4608 bgb_5_4640) (concat bgb_5_4672 bgb_5_4704)) (concat (concat bgb_5_4736 bgb_5_4768) (concat bgb_5_4800 (concat bgb_5_4832 bgb_5_4864)))) (concat (concat (concat bgb_5_4896 bgb_5_4928) (concat bgb_5_4960 bgb_5_4992)) (concat (concat bgb_5_5024 bgb_5_5056) (concat bgb_5_5088 (concat bgb_5_5120 bgb_5_5152))))) (concat (concat (concat (concat bgb_5_5184 bgb_5_5216) (concat bgb_5_5248 bgb_5_5280)) (concat (concat bgb_5_5312 bgb_5_5344) (concat bgb_5_5376 (concat bgb_5_5408 bgb_5_5440)))) (concat (concat (concat bgb_5_5472 bgb_5_5504) (concat bgb_5_5536 bgb_5_5568)) (concat (concat bgb_5_5600 bgb_5_5632) (concat bgb_5_5664 (concat bgb_5_5696 bgb_5_5728)))))) (concat (concat (concat (concat (concat bgb_5_5760 bgb_5_5792) (concat bgb_5_5824 bgb_5_5856)) (concat (concat bgb_5_5888 bgb_5_5920) (concat bgb_5_5952 (concat bgb_5_5984 bgb_5_6016)))) (concat (concat (concat bgb_5_6048 bgb_5_6080) (concat bgb_5_6112 bgb_5_6144)) (concat (concat bgb_5_6176 bgb_5_6208) (concat bgb_5_6240 (concat bgb_5_6272 bgb_5_6304))))) (concat (concat (concat (concat bgb_5_6336 bgb_5_6368) (concat bgb_5_6400 bgb_5_6432)) (concat (concat bgb_5_6464 bgb_5_6496) (concat bgb_5_6528 (concat bgb_5_6560 bgb_5_6592)))) (concat (concat (concat bgb_5_6624 bgb_5_6656) (concat bgb_5_6688 bgb_5_6720)) (concat (concat bgb_5_6752 bgb_5_6784) (concat bgb_5_6816 (concat bgb_5_6848 bgb_5_6880))))))) (concat (concat (concat (concat (concat (concat bgb_5_6912 bgb_5_6944) (concat bgb_5_6976 bgb_5_7008)) (concat (concat bgb_5_7040 bgb_5_7072) (concat bgb_5_7104 (concat bgb_5_7136 bgb_5_7168)))) (concat (concat (concat bgb_5_7200 bgb_5_7232) (concat bgb_5_7264 bgb_5_7296)) (concat (concat bgb_5_7328 bgb_5_7360) (concat bgb_5_7392 (concat bgb_5_7424 bgb_5_7456))))) (concat (concat (concat (concat bgb_5_7488 bgb_5_7520) (concat bgb_5_7552 bgb_5_7584)) (concat (concat bgb_5_7616 bgb_5_7648) (concat bgb_5_7680 (concat bgb_5_7712 bgb_5_7744)))) (concat (concat (concat bgb_5_7776 bgb_5_7808) (concat bgb_5_7840 bgb_5_7872)) (concat (concat bgb_5_7904 bgb_5_7936) (concat bgb_5_7968 (concat bgb_5_8000 bgb_5_8032)))))) (concat (concat (concat (concat (concat bgb_5_8064 bgb_5_8096) (concat bgb_5_8128 bgb_5_8160)) (concat (concat bgb_5_8192 bgb_5_8224) (concat bgb_5_8256 (concat bgb_5_8288 bgb_5_8320)))) (concat (concat (concat bgb_5_8352 bgb_5_8384) (concat bgb_5_8416 bgb_5_8448)) (concat (concat bgb_5_8480 bgb_5_8512) (concat bgb_5_8544 (concat bgb_5_8576 bgb_5_8608))))) (concat (concat (concat (concat bgb_5_8640 bgb_5_8672) (concat bgb_5_8704 bgb_5_8736)) (concat (concat bgb_5_8768 bgb_5_8800) (concat bgb_5_8832 (concat bgb_5_8864 bgb_5_8896)))) (concat (concat (concat bgb_5_8928 bgb_5_8960) (concat bgb_5_8992 bgb_5_9024)) (concat (concat bgb_5_9056 bgb_5_9088) (concat bgb_5_9120 (concat bgb_5_9152 bgb_5_9184)))))))))
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
theorem bgb_6_1824 : Interval gbAtlas 6 1824 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1844 := (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)) (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 bgb_6_416)))) (concat (concat (concat bgb_6_448 (concat bgb_6_480 bgb_6_512)) (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640))) (concat (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 bgb_6_768)) (concat (concat bgb_6_800 bgb_6_832) (concat bgb_6_864 bgb_6_896))))) (concat (concat (concat (concat bgb_6_928 (concat bgb_6_960 bgb_6_992)) (concat (concat bgb_6_1024 bgb_6_1056) (concat bgb_6_1088 bgb_6_1120))) (concat (concat bgb_6_1152 (concat bgb_6_1184 bgb_6_1216)) (concat (concat bgb_6_1248 bgb_6_1280) (concat bgb_6_1312 bgb_6_1344)))) (concat (concat (concat bgb_6_1376 (concat bgb_6_1408 bgb_6_1440)) (concat (concat bgb_6_1472 bgb_6_1504) (concat bgb_6_1536 bgb_6_1568))) (concat (concat (concat bgb_6_1600 bgb_6_1632) (concat bgb_6_1664 bgb_6_1696)) (concat (concat bgb_6_1728 bgb_6_1760) (concat bgb_6_1792 bgb_6_1824))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 5 zero,inputs.getD 4 zero]
def fullWord : Sig := 0xeee8eee8eee8a080eee8eee8eee8a080eee8eee8eee8a080eee8eee8eee8a080eee8eee8eee8a080eee8eee8eee8a080eee8eee8eee8a080eee8eee8eee8a080
theorem fullBound (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have low := boundgb certgb
  have lift := lift_ok (u:=true) (ms:=fixRows 32 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 5 zero,3,35)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 5 zero,3,35)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008242920 * 2 ^ 32 + 4008222848) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_12869.Model.Repr at out
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

def mono : List Gate := [⟨.or,[2,3]⟩,⟨.or,[0,1]⟩,⟨.and,[6,7]⟩,⟨.or,[1,3]⟩,⟨.or,[4,5]⟩,⟨.and,[0,9]⟩,⟨.or,[10,11]⟩,⟨.or,[2,10]⟩,⟨.or,[8,11]⟩,⟨.and,[12,14]⟩,⟨.and,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008242920 * 2 ^ 32 + 4008222848) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008242920 * 2 ^ 32 + 4008222848) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_12869

open PEqualNP.Outside.L_meta_12869 in
theorem PEqualNP.Outside.L_meta_12869 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008242920 * 2 ^ 32 + 4008222848) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008242920 * 2 ^ 32 + 4008222848) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound allgb)
