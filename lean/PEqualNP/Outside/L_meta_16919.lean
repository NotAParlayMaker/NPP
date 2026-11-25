import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_16919.Model
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


end PEqualNP.Outside.L_meta_16919.Model

namespace PEqualNP.Outside.L_meta_16919
open PEqualNP.Outside.L_meta_16919.Model
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

def SBf (j : Nat) : Nat := [5, 6, 6, 8, 7, 7].getD j 0

def tips (raw : List Sig) (v : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let b := v % 256
    (b/36,raw.getD (b/6 % 6) zero,raw.getD (b % 6) zero)::tips raw (v >>> 8) n

def deadTest (raw : List Sig) (ws : List Sig) (k hint : Nat) : Bool :=
  let j := min ((hint % 8)-1) 5
  let d := neg (raw.getD j zero)
  let cs := tips raw (hint >>> 6) (hint/8 % 8)
  (makePool true d raw cs).any (fun pool => poolCut true d (SBf j) k cs.length pool ws)

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
      Slice true (roots g) (target g) (neg ((roots g).getD (min ((tip g k i % 8)-1) 5) zero)) (SBf (min ((tip g k i % 8)-1) 5))

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

end PEqualNP.Outside.L_meta_16919

namespace PEqualNP.Outside.L_meta_16919
open PEqualNP.Outside.L_meta_16919.Model
def s0K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s0K4 (i*5) 5
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s0K4 (6+((h/1+packedAt s0K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x1ffe07fffff81c1fffff03fe0fffff007e73fc
  | 2 => 0xfffff81f81ffffe0f81ffffff0780fff93fccf
  | 3 => 0xe0ffffe001ffffff001ffc1fff800fffe38f0f
  | 4 => 0xfffffffe001fffffe0001ffffff001fc0ff0
  | 5 => 0xff00000000001fffffffffe000000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xc22231451041240529272126048a690c26315c
  | 2 => 0x444450c8229208a05a09464a9050a25490d4c5
  | 3 => 0x8aa8a2035525154b0512a9152d014ca9630b0a
  | 4 => 0x14d1049260365a729640c219ca658031d80ea0
  | 5 => 0x18e1c71c79c79f9ce79cf3818c4608c1ffe000
  | _ => 0
def s0Atlas : Atlas := ⟨4,rawDecor 62 s0Pos s0Neg, 0xfcccf0c0fcccf000fcccf0c0fcccf000fcccf0c0fcccf000fcccf0c0fcccf000fcccf0c0fcccf000fcccf0c0fcccf000fcccf0c0fcccf000fcccf0c0fcccf000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_16919
namespace PEqualNP.Outside.L_meta_16919
open PEqualNP.Outside.L_meta_16919.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x3004022400050000000003c03400c62c01ce04428800901040df43be43bc43dc439c43bf42bd42df32dd32bf41bd41df31dd31be40bc40de30dc30
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x30c7520690000008000000042804b000404794e438ea90871d5110e3ca021c714d428e2a6651c544ca38a6a0c7153318e2a2631e539023ca9184715030
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x800c808558454cca0d621533183588540c2156115030
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 17
  | 3 => 13
  | 2 => 4
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (i*5) 5
  | 4 => packedAt s1K4 (i*16) 16
  | 3 => packedAt s1K3 (i*27) 27
  | 2 => packedAt s1K2 (i*38) 38
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (6+((h/1+packedAt s1K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s1K4 (297+((h/5+packedAt s1K4 (272+(h % 5)*5) 5) % 29)*6) 6
  | 3 => packedAt s1K3 (371+((h/4+packedAt s1K3 (351+(h % 4)*5) 5) % 24)*5) 5
  | 2 => packedAt s1K2 (155+((h/1+packedAt s1K2 (152+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffff07fffc1ff83ffff07ff07ff07fe7cf3cf
  | 2 => 0xf07fff83fffe1ffc1f07f87ff87ff83fa33cf3
  | 3 => 0xff83fffc1fffe1ffe007ff87ff87ffc1c3cf3c
  | 4 => 0x3ffffe00001fffff80007fff80001fc0fc0
  | 5 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x8108111084820000a5090089008902940c5145
  | 2 => 0x24112209091030940a42485248525028a12492
  | 3 => 0x4222442052210329408495049504a501428a28
  | 4 => 0x6b5b894a43b555ce73d0c447e660318df40fc0
  | 5 => 0x8c630e739c3999f39ce7e660c440c631fbf000
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfaaafaa0faa0faa0faaafaa0faa0faa0faaafaa0faa0faa0faaafaa0faa0faa0faaafaa0faa0faa0faaafaa0faa0faa0faaafaa0faa0faa0faaafaa0faa0faa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_16919
namespace PEqualNP.Outside.L_meta_16919
open PEqualNP.Outside.L_meta_16919.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0xe00156900046228030a0001c62be43bc43bf42bd42bf41bd41ef21ed21be40bc40ee20ec20
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x58010096a90871c535063ca7205954420
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 4
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (i*5) 5
  | 4 => packedAt s2K4 (i*16) 16
  | 3 => packedAt s2K3 (i*27) 27
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (6+((h/1+packedAt s2K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s2K4 (212+((h/4+packedAt s2K4 (192+(h % 4)*5) 5) % 18)*5) 5
  | 3 => packedAt s2K3 (111+((h/1+packedAt s2K3 (108+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffff83ff83fffe0ff83ffffc1fc0fffe4ff39f
  | 1 => 0x3fffc1ffff07ff07fc3c1ffe1fff03fb13cf3
  | 3 => 0xfc1fffe003ff87ff8003fe1ffe00ffc1c1cf1c
  | 4 => 0x1ffffffc0007fffffc001fffff0001fe0fe0
  | 5 => 0xffe00000000007ffffffffe000000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x1080888404a000029804822802441518065185
  | 1 => 0x484910492104c250224151452092a0a4912432
  | 3 => 0x295a21436a4c4eb506227517540aca85c18e18
  | 4 => 0xb2944a1240691529cca8201a992c03096a0bc0
  | 5 => 0xc318739c738e67ce7733b98310308c31fdf000
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeeeaa88eeccaa88eeeeaa88eeccaa88eeeeaa88eeccaa88eeeeaa88eeccaa88eeeeaa88eeccaa88eeeeaa88eeccaa88eeeeaa88eeccaa88eeeeaa88eeccaa88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_16919
namespace PEqualNP.Outside.L_meta_16919
open PEqualNP.Outside.L_meta_16919.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x40e225c59e004c00c30587840000005248ce9a2001300000000d00500a12a011250418d83321d200389c01f14804831541c8153003042000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x4817e53903bca7205794e40bea9c81dd53902baa7206fd0e40dea1c817e52902faa5206f90a40de214817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c535037c86a06f10d40bfa9281ef52502dea4a05f14940f6292816c525037e84a06f50940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40bea9881bf431037a86205f94840bea9081be421037884205f94440bea8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330efa1e61dc43cc2fca5987b94b30b7296617d52cc3daa5985b54b30ef99661dd32cc2fca3985f54730ef98e61dd31cc2fea9185f95230df2a4613e548c2faa9186f552309eaa4617c548c2faa7185f94a30bea94617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130efa1a61dc434c2fea4985f14930ef99261dd324c2fea2985f14530ef98a61dd314c3f66098778c130bfaa0617e540c2faa8185f15030bf298617e520c2faa4185f94430bea8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20bf28e417d51c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea9441ef42883d885107b8ca20f6994417e51882faa3107b88620f610c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a417e53482faa6905f14d20bfa8a417c51483de42907b48520fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53082fca4107bd0820f621041ee32083da64105f94420fb288417651082faa2107d54420baa8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3085f94210fd18421f930843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fb10a21f521443f460887e4c110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c52042fca2085f94010fb88021fa10043ea20087e44010
  | 1 => 0xd5190afca1215f54242bfa9a857c5350b7e86a16f50d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42ef298855e5310afaa6217754c42aea9885be4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332ef21e65dd43ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7195f94a32f721465ed428cbbe65197bcca32bf28c657d518cafca1195f54232bfaa265bf544ca7ea8995f95132beaa2657c544cb78a8994f15132ef21a65dd434cbdc84997b50932f799265de324cafea2995f14532bfa82657c504cafea8195f95032df2a0653e540cafaa8196f550329eaa0657c540cafca6195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef50f41bf296837d52d077c85a0ef10b41bf286837d50d06faa920df94e41bea9c83be43907788720df94a41f7294836e52906faa520fb54a41b6a9483bf429077a8520df94641dfa0c83f741906fca120df54241bfa9a83df53506bea6a0df14d41ee29a835c535077e86a0ef50d41bfa92837c525077c84a0ef10941fba0a83be41506fea0a0df14141bf2a0837e53106faa620ef90c41de218837e52106faa420efd0841dea10837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331bf296637d52cc6fca198df54331bfaa4637e548c6faa918df15231bea9c63df438c7b88718df94a31bea9463df328c7ba6518df94631ef98c63f7318c6fca118df54231bfaa263bf544c67ea898df95131beaa2637c544c778a898cf15131bfa92637c524c7ee6298f78c531bfa82637c504c6fea818df95031df2a0633e540c6faa818ef550319eaa0637c540c6fca618f7d0c31ee218637e520c7dca418db94831bea9063ed520c6daa418f7cc831ee990637e510c7be6218fd8c431ee98863f5310c6fca018fe94031bd280637d500c7f2a018de54031bfaa6437e54c877ca990cf95321beaa643bd54c867aa990df15321bfa9e437e53c87bca790d794f21bea9e43dd53c86baa790df14f21f7a1643ec42c87dc6590fb4cb21bf286437d50c86fea910df95221df2a4433e54886faa910ef552219eaa4437c54886fea710df94e21bea9c437c53886faa510df94621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21f7a1243ec42487dc6490fb4c921fb90a43ee21486fea090df14121bfaa0437e54086faa810df15021bfa98437e53086faa610df14c21bf290437e51087de4210fd88421f690843f521086fca010df54021bf29e817d53d037c87a06f10f40bf296817d52d037e85a06f50b40bf28e817d51d037e83a06f50740beaa
  | 2 => 0x20442b9b52440005a08727e7a00000031e000001010ec000000003320000000000004c0017443885c9695b000000000012a6000002015160000680035a00073000000000412150000009880000000027a530000004e0a9190000001a80000012180006869c0012b00012000000282000cf24e000000000000000000024800000000000000000bd0f00000000000028c5cc000000000013525934c0010f12e000570f622b00e86902983000694ef9c00000012927c30e0ac650000000009a17d000494001db414988b200000000000064170934001bf000000b09da0ac00113a6533e4452a897114000000000008dc000372ee000418940d200139000144860000000000500016529e650311fe2160003d8000009dc0027d0000007687d20ca30aa0004081dcc40da000000000000000009c0004d8000f51430000d46029418606c8511212c3ec3908f4849d14403f2d07e82825429a000000004280004200001c028caa33000000000005041bcae8e82f6000592380f827d1a9ac3f03943a8450087d80000024e8889b1b927c00066800000098000d20006eccb8fa0000000000000003cff8004bc0000008643a4f000000000000b00003423b92f8d80006dc00000000000200af27a3900022e000000001af20e9cd3f800000000000002ce0a03f2510000000000037866c8980012a6f4000650ba424fb8004f028c0b950000000d50060880ccd99eb06c4a47494e00400a00c0000400400c010110000000080400800002800008000010110020040000c00e0000000300000c0380e0080000001a000004008000020000000300000800003016000000010000100080500000009000000044000020180000080e00a00409800000018000140140300a002006014000020020080400300e0000e00300000000801002000018000040000800104a0040280000202c0080000200001007002004010020000000000001a00c0000100a01400002004014000070080140000000600000000000004008000020340580001e00406802006030008000080200000100c0040580b0040240300b00000405802012018000020020040080000c00000000028008008000040080200000c0000200000000400802000008000010000000680300200c0400001400802800bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421fb94843b7290877d5210fdaa421db54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7216f90e42de21c857e5290b7e85217bd0a42bf28c857
  | 3 => 0x350000000006800000041a430699d54f4000002610000e0119261f8a288400031a4393a97800000000000000000e80005240000000000071c000d1258624000cc3da00000000326280b11e02e038c3c00052a0002197f48e0011219c00057c000000004e80013b00092cf88293ac1cc0012421e6683300003e260000000000010c9de0001a80000000047cbaa4f000048000000001c0fa0001220000000000036cc61e40007282fa3d00045cad00000048c238003ce0000016d000000610000f20000000016200000285000464758c1000600b5842060000001f500015478a4400029c001d91fc000e4880000a34e180029600064a8e18a000000cb3f6000b18001500080028304035c270bf416760170000000000000050c000e60003f20010d80000078c001c60006b8000000006c4f30160002050823b1782f8638050008bc0002a000434000242fc6a400000000000000000006acab0000000007a0ce0005a8ee9844da8e40017c1ac0002d0f21d89acb4a411aa484e5a690b69c02584c33a800f82303166e0b3135072a1025019062544d21b20002d8e70004528f9188993b82d400000000000520000ce440a11280d67cc1e8ac00000111800000379078084b69f86c88c0a60000d2960006e87100030a00059800000000001982985785580023a000a4800238000b8a344de15000258360000019c24b40007780000095d499553220013225c3442940002502a6d842800266000001031b8514c81be0001fc001d43c48f0001183de3d4ac9a31740010105c0003e4eba324943e00000009a898000000000000011b1ce2a80e82723437514287000000f29f22b0000a210413a0e8a0246000000e20004a00008a9370006493d8520160c8799054d0930248090dc000b78003fa0f0000a60000002898200024c4d800000638b71b452e78504a1339a74430a67474400002071a0528a922d28e5201609a410894080002645e400000454000361fc00087c5d80018c8b0980000002850192f32c2412b068442088441570009b8108001fe9e40009e3828d800000000974001860000002f0000005b0001cf0000005e800000838bb08b082a001f0182e4458e426648a3dc8f0cf314a402c0b91be9d88a0633d22b47b03b15c0bd488b03dc0003a00c1120010600011a000000000003a8620000000012000038a848000e0000a3d408000b2180368b73a400038a6300000000000124070810e10009800007a40c0010893942c481101d3000604168000000000f0000003f42300000000144a3f0002393892a49
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x53c823e64947208f59251c825e63d52209758f548823e64d4e208f593538823e6494e208f59253882cd6310a20ab191328823f64546208f191518825f63546209718d51882ae64886208f992544826f62551208f994544823e6494d208f592534826d6294d208fd91534823c6454d209dd8553482746154d209b997214832c54c8520cb151214832c54881209798f540825d63d50209d987540827561d50208f596540832c62550208f990540825e63150209758c540827661150209d584540823e64d4c208f593530827661d4c209d587530825d6594c20c7952530831d5494c20d398a530831e5454c20c7551530823e6414c208f590530825e6314c209d98453082756114c20cb553420826d6510820b358c420826d658c820cb55232082ac644c820cb551320834e534c820cd95251083355494420d594e51083555394420cd95151083355454420d594d51083555354420d9d0951083644254420d98c9510836532544209b59621082ae6488420d954621083655108420d9547200826f6548020ab191200836551480209ed95200826e62d53109b58b54c425f63553109718d54c423f6454f108f19153c423e6414f108f59053c426e6214f109b58853c423e64d4b108f59352c423e6494b108f59252c425e6394b109758e52c425e63d52109758f548426f62552109b189548423e64d4e108f593538423e6494e108f592538426e6294e109b58a538423f6454a108f191528423e6414a108f590528425e6314a109758c528423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f994544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d1097994534431f5414d10c715053443596014d10cbd53524432c54d4910d3d4f524434c53d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524426e6514910cbd50524432c5414910d3d4c524434c5314910d9584524436452885109d1952144358538c1109e195304425e63d50109758f540426e62d50109b58b540423d65950108f990540425e63150109758c540426e62150109b588540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c108f990530423d6414c109798c530426e6214c109b588530427a6014c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520423e64148108f590520425e63148109758c520426e62148109d984520436552c40109e596100435953840109dd95100436552440109ed9510043595344010
  | 1 => 0xc63e649513197d8d544c63e6515131c7152314c66e62d50319b58b540c67a60d50319e583540c63d6595031c718d540c63e64150319b988540c66d62150319e980540c6796015031c7553430c65d6510c31b3588430c72e5494831cb552520c72e5454831cb551520c71d54cc831a7191320c71d544c831d3949320c65f654c431a7191310c677654c431ce952500c7395494031da94a500c7695294031ce951500c7395454031da949500c7695254031d6d0d500c7584354031d6cc9500c7593254031d6cc5500c75931540319798f54c865d63d5321cb18954c865e63153219758c54c863e64d4f218f59353c871e5494f21c755253c874e6294f21c795153c871d5454f218f99053c863d6414f21cb55342c86cd6310b21cb55232c86ac644cb21cb55132c874e534cb218f993538863d64d4e218f990538863d6414e219e98053886796014e21cb953218865f63551219718d544867b60551219e181544863f6454d218f191534867b6054d219e181534863e6414d218f590534866e65d0921b358c424866c654c921ab19132486e4614c921ab992214863e64141218f590504865e63141219758c504866e62d50219798c540865d63150219e980540867960150218fd91530863c6454c218f990530863d6414c219b988530867a6014c219e580530863e64948218f592520865e63948219758e520863e64944218f592510866f65484219dd95210863f64540218f19150086ad6210f409b98a51d026d6294740a718d41d026e6294e409b58a539034e6294e40d358a539031e53d0e40c794d439031e5390a40a758c429031e5310a40c794e41902ae6290640c794c419031e53d02408f99443502ad6210d409798c525025d6314940d398c525034d6314940cb90c525032c43149408f997425032c52d0940cb149425023e65d0540cb14b415029c6350540cb149415029e6390140cb14a405023f6550c408f596421029d631084097d8d511025c63544408f59641102ae62904408fd9540102ac62500409ed95401026e62d53309b58b54cc31c63553309b98854cc26d6215330c755343cc2cd6210f30cb95252cc32d5494b30cb95152cc32d5454b30c755332cc29c644cb30c755132cc34e524cb30a719131cc31e548c630c7950318c2d9600c630c7953308c26f62551309b189544c27761551309d185544c25e65d0d30b3588434c23e64149308f590524c29c644c930b6181324c23e64145308f590514c26e62145309b588514c25e65cc530a7191314c29e648c1309798f540c26e62150309b588540c27661150309d584540c23e6494c308f592530c23f64548308f191520c23f64544308f191510c25d658c430b6580310c23e64940308f592500c25f654c0309ed95300c25e63153209758c54c823f6454f208f19153c823e6414f208f59
  | 2 => 0x63cfd11a07c000ee0001f822cac8003d633400112334344da8dc1ee4e8f00000007f80017a0105f80000015c80c0015e156000a1073000000328002da000ec83c40a6e07e887072140de1030b2130000463de864629db2420b8ab1fb0360d4e2201150024958150001707f8a338e41802029000324468da0005a40021724a570d40000001b02291419c7f01b0063140004483a000000c08191ba7449a8e71605e40005d16601c000122f82b4c30110be5a09c81e3e6148a39990f6810661cd15e3889199300064841800000670b98002000886d80e424658651f532e284ad8200000010109e1380940680003061c8080030a3a8e09cf000000000000000004f86b2ca4d0bf90b36e7c800000000214878ec000000001980000000000000001006034030000000c00000030180300c0e02c0302c0404c00008000040000c000000001c00000300000200001000000000000c360040b0000a0000002000010001140201c0c0141600c000001000000014020000100c00034000341c008000000001800014030040200c000040c02c000000d0180100c0101802004020100801c0000c000101501401020000480e020000183c01c1401c160080c060390340200800014010140602c000280101001004000180001c020200000c0d02000034040000d00400014010080302402000260080003043000010080101c00004010326e62947439b58a51d0e6f62543439b18950d0e3f6550c4397d954310f2f4354843d390d5210f2d4354843d350d5210e5f63547429718d51d0a5e63943429758e50d0aad6210e428f9974350a3d6590c42c754e4310b1d5310c42ab5884310b1d53d0842d354e4210a3f6550842c754d4210a6f6550842d354d4210a7a60d53329e58354cca3f64547328f19151cca3e64943328f59250cca7661d52329d587548ca3e64946328f592518ca3f64542328f191508ca3e64951328f994544cb1d6315132cb588544cb1c5490d3297195434cb2c5490932e390e424ca6c6550932e350d424ca3d65950328f990540ca5e63150329b988540cb1d54cc832cb552320ca5f654c832c7551320ca6f654c832cb551320ca9d6310b419798e50d065d6394341ab588439065e6394a419758e529074e6394a41d358e529072e4394a41cb10e529072e52d0a41cb949429072e52d06419b988535066d6214d41d3988535074d6214d418f997435071c53d0d41c714d435071c53909418f994425069d6310941c714c425071c5390541ab98a415063d6590c41ab588431063f65508418fd95411069c63504419dd95411066f62540419b189501066e62153319b58854cc63f6454b318f19152cc63e64943318f59250cc66e62d52319b58b548c6cd6210e318f992528c63d6494a31a7191328c63f64542318f191508c66f62542319b189508
  | 3 => 0x9404f000740c89cc000145048003760e0309ac2ce240d39e7000104c00d00003b417a0c03819cb60002ba000000a22607a4cf06f336230001462867b45b05b2e47c00000016e04c690000006d0ef05a2ee2510500035662ca294b14c1a4249ec3122107c9bf36615cd29f708458ca49b10043187c2112b003cf513c01849c0001a3ac0fcb88e40f8500810bd000000cf9e50004bd0d0d711c70c001ca0005bc000003ae3ac001901401786a08a14877c160f342c7086a9740005d8180161267e40002d0003c4601c510c7007f0001f60000013f000384658001820000006d00000039000000310000b5000134000004162e08600041a000001481580000006613631c4b9290000000000000033ce98c23e24c4a60000004149c14d2ae000000000000006f1940007e00000023e0000014e3900044c1040462e8000680c06c01d9a22123a4258212264c88890a0f4774838370fc5f431200006690d198d17c204488780001d48c87922c854731c933a5280006e3c26e8000bf2361c04d188266680c20a50005c0001d440e000b71af000000001d537c0000008826e0ac000713ec440e9118152274718d90ec25419164000788a88002d6138b01542885e0b08430204786b02826c014050e5066050782060fa128ff8542b40f47a90d4207383192032a26435152172638320c84261590414108e29cdc8341e82005d9cb34c630e312c11e0c50a0004303a0951e323a598db122000160f417b35a6b85890e000000000003fa248000530004b8000000007d0410000000010796a0ee2c8d9044000000000df2a6074001e627a4ec6995503e1548a84000009cf2175048540d4924000838de92d0001d00013e0000004b0ef0000008b80000000015000000360f71821ec120930bc00057cc181704c3e8ec1aa00000000000000420000000163c8000e01864707714f3b42a8d08001685883f80
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x12c63cc4891cd00551800e1000165c309354029100840b01801c2118358d6215132a1ae72928520d0d7214d435070629cc520a83435c86355031838ecaa26418d497210d500c68c3a264a8063461d13154031a1ae6312a990c2c7655132c8686b94a6a1c818394e6290640a1ae629284a060c631494150307318a520281435c86355330838ecaa2659861a54580318c286b98c4aa0410b1d9544c820a8ae6212a210524744c95108313322a310841891915148020
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x40b000080d8714e629054180d8794e629064080d8718c525054080d8798c5290140
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 664
  | 4 => 539
  | 3 => 25
  | 2 => 4
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s3K7 (i*5) 5
  | 6 => packedAt s3K6 (i*16) 16
  | 5 => packedAt s3K5 (i*27) 27
  | 4 => packedAt s3K4 (i*38) 38
  | 3 => packedAt s3K3 (i*49) 49
  | 2 => packedAt s3K2 (i*60) 60
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s3K7 (6+((h/1+packedAt s3K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s3K6 (718+((h/13+packedAt s3K6 (640+(h % 13)*6) 6) % 53)*7) 7
  | 5 => packedAt s3K5 (20359+((h/221+packedAt s3K5 (17928+(h % 221)*11) 11) % 1059)*11) 11
  | 4 => packedAt s3K4 (22272+((h/179+packedAt s3K4 (20482+(h % 179)*10) 10) % 711)*11) 11
  | 3 => packedAt s3K3 (1265+((h/8+packedAt s3K3 (1225+(h % 8)*5) 5) % 31)*6) 6
  | 2 => packedAt s3K2 (243+((h/1+packedAt s3K2 (240+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x87fff83ff87ffe0ff87f87fe1fc0fffd38f39f
  | 1 => 0xf81fffc1fffe1ff07f87f87fe1ffe07ec73cf3
  | 2 => 0xffe0fffe007fe3ff8007ff8ffe00ff8307cf1c
  | 4 => 0xffffff8003fffff8000fffff0003f80fe0
  | 5 => 0xffff0000000003fffffffff000000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0xa0840888409400029809009402442a30185185
  | 1 => 0x2421104902020502082882220924148432432
  | 2 => 0x114aa214354906b50444d50b540a950b058e18
  | 4 => 0x5594c4a1240d4b29cd50440d992c0613a80bc0
  | 5 => 0x66188739c67193ce7667664110301863f6f000
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xeeeee8e8ececa8a8eeeee8e8ececa8a8eeeee8e8ececa8a8eeeee8e8ececa8a8eeeee8e8ececa8a8eeeee8e8ececa8a8eeeee8e8ececa8a8eeeee8e8ececa8a8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_16919
namespace PEqualNP.Outside.L_meta_16919
open PEqualNP.Outside.L_meta_16919.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x4200b86000001c0031682007d00406b0aae4c3520e4e94d9e101549d000038060a9889005000b000000a20000004400d11020001600a0c9324011801ebc0000060000560000482220800f0e080000c00000ff43bf43fe43fd43bd43fc43ff42fe42be42fd42fc42bc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31f631fd31f531fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x1dc067003a2d123146245001f071347495178446a150009ce6003419104413e800a40531800402212024da4942a682ca3002887a001b0e000454097c940000064c0212c94cec00002505867001e400340026c00932a91c001004000804e002740c00098011c8a0600000390025c086c1595924002802c004c22000000030908f800001603a8d1b998008618060763e3d828526f232110643198352c6e4f8fc289c2d21c549812920f01c0f264d45c0115c46621913c1e1b25a9120122f1505a713a8b84c00289f8e4a000a842e5b0d1753c7f44000e8000023c7828349e8ca6b0c00030a0a8993008000828280018085888b9604028280000f8c0280088000000b811684000b9d00008887000180048a82028282170200cf94b439f28e873d50d0e7aa921dd94643baa8c879f5350e78a4a1cf145439fa82873e5410eeca221dd54443bb28c85755190a7aa7214f94a429f28c85b65190a6ca3216d546429ea84853d5310a7ca4216b948429f288853d5010a7ca9994f55332bb28e657551cca7ea9194f152329faa2653c544ca7ca8194f55032bb2886575510caf4a0195e540329ea9c833e529067ca320cf54241af298835d531073ca620cf54c41cea98831d531067ca420cf94441db288833d501067ca998cf55331cea1e633f548c678a918ed90631da20c63b7548c768a918dd54e31dba1c63b5438c76c8518ed10a319faa2633c544c73a8698ed90531da20a63b7544c768a898f5d4d31dba1a63d6434c76a8698f550d31caa1a63b6424c7688498f58c931ea192633e540c67aa818dd944319f2a6433d54c867ca910cf55221af29c435d53887688310cfd51219e2a243b4414867ea810cf150219ea9e813e52d027ca3a06d8c740da98e813d54902eea2a05d145409fa9a813c525036ea2a04f14540da28a8134515036c62a06d4c540dda82813e541027ca9984f55330bb28e617551cc3aa63984f952309eaa4613e544c27aa898754c5309f2a0613d540c2dca4185b54830bb2886175510c27ea9904f153209f2a4413d548827ea8904f15120afa9a415c53482eea2905d145209f2a0413d54082bca6105754c20bb2884175510827ea9884f153109f2a4213d548436883084fd51109e2a2213e540427aa8085794c10aea98216e52042daa4086d10410
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x28001cf8000a8030166d00000b80002ce909a4e01d800000000000000000e00005a40180380158f00140002e98a806c00480000002200a403200004000c35780684c0000000023000020000008ac023002400cc0000000000000003904000251c00e8000000003c28cb70000000000090030c40000000a0000d4000000000000000000006000000000003000000000000030001000200068d98652d0e3461543439558e5190a1d6394642a558e5190b1663946428d58e5190b1563946428558e5190a3461540428d987548ca3661d5132c5985531071553944418b98b548c69563d5231a998b548c69563152318d996428c61c6550d31a5592434c6966550d31a5195434c6946250d31a5d81434c6366590931a558c424c697648c931a5590324c6d1600c931a558c41887155310621a558c414863661d50218758c540863960150218d98652d0315534c7409558c515021d6314540a558c515031663145408d58c515031563145408558c5150234658c5408d1953150315544c7308d185548c22c62551308d185544c315544c5308d98754c823461552208758c54c429563106108d59441042956310410c554c41043255210410
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x380c000041020000140920c02160ab98c2a8085415ca6154c4190ce532a8698c1573987540860ab9cc329681411c9544c53082ae730ea99041573185548820abb2a6208218158d5210410
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 50
  | 4 => 165
  | 3 => 60
  | 2 => 10
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (i*5) 5
  | 5 => packedAt s4K5 (i*16) 16
  | 4 => packedAt s4K4 (i*27) 27
  | 3 => packedAt s4K3 (i*38) 38
  | 2 => packedAt s4K2 (i*49) 49
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (6+((h/1+packedAt s4K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s4K5 (912+((h/16+packedAt s4K5 (800+(h % 16)*7) 7) % 80)*7) 7
  | 4 => packedAt s4K4 (4895+((h/55+packedAt s4K4 (4455+(h % 55)*8) 8) % 199)*9) 9
  | 3 => packedAt s4K3 (2440+((h/20+packedAt s4K3 (2280+(h % 20)*8) 8) % 151)*7) 7
  | 2 => packedAt s4K2 (505+((h/3+packedAt s4K2 (490+(h % 3)*5) 5) % 18)*5) 5
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xf0fffc3f0fffffc1c3ffc3fe1c1ffffe38f0ff
  | 1 => 0xff0fffc00f87c7fe03c3fc7fe01e1c3f273c93
  | 2 => 0xfff07ffff007f87ffc03ff87ffe01fc1c7cf1c
  | 3 => 0x7ffffff8007ffffc0007ffffe001f80fe0
  | 5 => 0xffff80000000007ffffffff800000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x14000408120100004084808804028510085025
  | 1 => 0x22634886a54a8c4e2161645720d448ad232c92
  | 2 => 0x40251112011400928402490249401284458518
  | 3 => 0xa8a6224884095652a68204592994009b00ac0
  | 5 => 0x8ccc43b8ce672679f3b3b26103118331fef000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xfae8fae8faa8faa8fae8fae8faa8faa8fae8fae8faa8faa8fae8fae8faa8faa8fae8fae8faa8faa8fae8fae8faa8faa8fae8fae8faa8faa8fae8fae8faa8faa8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_16919
namespace PEqualNP.Outside.L_meta_16919
open PEqualNP.Outside.L_meta_16919.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x388000a1ea0c25004008e0058000268400d362c1064e009290e10a2a4c68f1522011800a2159744252003a7cc8c0604000608002404d240040ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xdd550000008818e8500000011564e40000005400000000013c0000994c000034011c4cf4004150012cd9100044fc00000000000000d40080300038ad3548009cecc128cc5804000121596000000000680168009400000000f0b86400000000007000200000000104000000004828011800006cf94400910800015c0010140000742d241c60d0e1310cb03c008c007c00a45c0024000000c8000000080000000001400000000000000000a00cb538a80000840000000000000078000000c4bc00020800060c0204000004040a04000002000000020e0404000000020205765190eeaa321dd94642baa8c853e540ca7aa819734c832bb2886575510caf4a0195e540329f28c833d50906bca620d754c41b7290836d52106f4a020de54041cf298839d531075ca420eb548419f28883b65110774a020cf54041dca808339501067ca998cf55331b7294636d528c7688318cfd51319e2a263b4414c67ca990cf55321af29c435d53887688310cfd51219e2a243b4414867ca3a04f55240bba8a8174515036ea2a04f14540da28a81345150376a0a04f950409f2a4613d548c2dea4985b149309f2a0613d540c2dca4185b54830bb2886175510c27ca9104f55220afa9a415c534827ca8104f55020af298415d53082eca2105d544209faa6213c54c427ca9084f55210da20c21b9408427ea8884f15110dca02213e540427aa8085794c10aea98216e52042daa4086d10410
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0xb0e72e006c0c00081a0000148a4212a80616a0a98401e09000200004504327493254032c354d521071a5354041c654d501072a5254041ca54950107255210631ac580418c6b16010531c554c41886b16010621ac58041487166314540c558c51503266214540c9588515033160145408d185548c2346155220ac58041842b061502108e19540442356510410c554c41043255210410
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0xc0840000101885496010631c22a6b008310e05635885150308b1ac028a81885896014540
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 91
  | 3 => 25
  | 2 => 5
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (i*5) 5
  | 5 => packedAt s5K5 (i*16) 16
  | 4 => packedAt s5K4 (i*27) 27
  | 3 => packedAt s5K3 (i*38) 38
  | 2 => packedAt s5K2 (i*49) 49
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (6+((h/1+packedAt s5K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s5K5 (788+((h/14+packedAt s5K5 (704+(h % 14)*6) 6) % 53)*7) 7
  | 4 => packedAt s5K4 (2697+((h/30+packedAt s5K4 (2457+(h % 30)*8) 8) % 193)*8) 8
  | 3 => packedAt s5K3 (998+((h/8+packedAt s5K3 (950+(h % 8)*6) 6) % 34)*6) 6
  | 2 => packedAt s5K2 (249+((h/1+packedAt s5K2 (245+(h % 1)*4) 4) % 11)*4) 4
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfe1fe3c7e3fffe1c71f8fc0c707fffe19c0ff
  | 1 => 0xf1fe3fff803c78fe07e3f1fff8070e1e667c93
  | 2 => 0x1ffc03fffc07f1ff803fe00fff80fe1878f1c
  | 3 => 0xfe00003fffff801ffffc0000fffff001f80fe0
  | 4 => 0xffffffc00000001fffffffff00000001fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x4028004410502000420502480101429008c025
  | 1 => 0x24448c080c88910601209086c832244c221c92
  | 2 => 0xa88094912409402a8802a41252500944870518
  | 3 => 0x41529224820125515480024a4a4a009700ac0
  | 4 => 0xc919300371326499e693493800c0c191dde000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfeecfaa8feecfaa8feecfaa8feecfaa8feecfaa8feecfaa8feecfaa8feecfaa8feecfaa8feecfaa8feecfaa8feecfaa8feecfaa8feecfaa8feecfaa8feecfaa8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_16919
namespace PEqualNP.Outside.L_meta_16919
open PEqualNP.Outside.L_meta_16919.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x10050f029a7a316910001b8000cc01e00e17a012855001e0400a58d5ca600183ae6c219343689499487c5bb06000302a0022b289493a62400164660e0d2638b9d4e061868100040000e0c4800c08700263c18001ffd5005fe54007f55005fc5400ffd4c037f5300ff94c03fd5300df54c03fc5300ffd0c03fe4300ff50c03fc4301ffd4801fe52007f54807fc52017fd0801fe42007f50805fc4200ffcc803fe3200ff4c803fc3201ffd4401fe51007f54407fc51017fd0401fe41007f50405fc4100ffcc403fe3100ff4c403fc31007fc8401fe21007f48401fc2101ffd4001fe50007f54007fc50017fd0001fe40007f50005fc4000ffcc003fe3000ff4c003fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2a2000dfd9510004feca88037fe65440077f32a2000ff59510005faca88037fc65440077e32a2000df1951001cf8ca88003ff64440017fb222000efd91100057ec888033fe64440057f3222000ff59110005fac888033fc64440057e3222000ef1911001578c888037ff5444019ff2a22000ff55110067f8a88802fff63440177fb1a200bff98d1000dfcc68802ffd63440177eb1a200bff18d1000df8c68802fff5344017bfa9a200bff94d1005ffaa68802f7d5344017fe29a200bffd0d1005ffc868802ffd4344017fe21a2000ffd8910005fec488003fe62440157f3122000ff58910005fac488003fc62440157e312200dffd4910007fca488003fd524401bfe292200cffd0910007fc8488003fd4244019fe212200bffcc91005ffc648802ffd3244017fe192200dffd4510027fca288003fd5144009fe28a200cffd0510027fc8288003fd4144009fe20a200bffcc510027fc628802ff63144017fe98a200bfd4c510027f86288003ff2144009ff10a2000fd88510007fa4288003f52144009fe10a200dffd4110007fca088003fd504401bfe282200cffd0110007fc8088003fa4044001fea022000fe50110067f8808802fff3044017ff182200bff4c11005ff86088003ff2044001ff1022000ff48110007f84088013ff1044009fd8822000ff84110007ec2088017ff65040097fb282004ff9941001dfcca080137e65040073f3282004ff59410005faca080137d65040013eb282005ff19410025f8ca08017ff64040097fb202004ff99010015fcc808013be64040055f3202004ff59010005fac808013bd64040015eb202005ff19010025f8c808023ff540400fff2a02000ff5501003ff8a808017ff63040097fb182004ff98c1000dfcc608013de63040036f3182004ff58c10035fac608013dd63040016eb182005ff18c10025f8c60801bff530400dbfa982006ff94c10037faa60801b7d530400dfe2982006ffd0c10037fc860801bfd430400dfe2182005ffd8810025fec408013fe62040157f3102004fb98810005dcc408013fd62040017eb102004fb58810005dac408017fc62040097e3102008ffd4810007fca408003fd5204011fe2902007ffd0810007fc8408003fd420400ffe2102006ffcc810037fc640801bfd320400dfe1902004bf98410027fea208013fe5104009fea882004ff14410027fe8208013fe4104009fea082004ff10410027fe6208013fe3104009fe9882004ff0c410027fe4208013fe2104009fe9082004ff0841004dfcc008023ff500400bff2802000ff5401002ff8a00801fff400400bff2002000ff5001002ff8800801bff300400bff1802006ff4c01002ff86008003ff200400bff1002000ff4801002ff84008013ff1004009fb8802005ff84010027f42008013fd1004001fa8802004fe44010
  | 1 => 0x3fc4108027ff9884013ff8c42009ffa621004ffc3108015ff908400aff88420057fa421002bfc210802d7f3004015ffd402002ffca010003fd500800bfe2804014ffd002002ffc8010003fd400800bfe2004013ffcc02002ffc601004ffd300800bfe180400affc8020057de4010017fe2008015fd100400aff48020007da401002bf92008009ffb2e2004bfd9710027fccb8800efe65c4009feb2e2000bf59710027f8cb88012fc65c4009ffb262004bfd9310027fcc98800afe64c4009feb262000bf59310027f8c988012fc64c4025ffaa62011ff95310007faa988047fc54c4009ffb1e2004bfd8f10027fcc788006fe63c4009feb1e2010bf58f10027f8c788012fc63c4021ffa9e2010dfd4f10087fca788043fd53c4021bea9e2010ff14f10087fe8788043fe43c4021fea1e2010ff10f10027fec588012ff62c4009ff316200abf98b10027fac588002fd62c4009fe3162004bf18b10097fea588003fe52c4001fea962012ff14b1008ffe8588003fe42c4001fea162011ff10b10087fe6588043fe32c4021fe9962010ff0cb10027fea388013fe51c4009fea8e2004ff14710027fe8388013fe41c4009fea0e2004ff10710027fe6388013fe31c4009fb18e2004ff4c710087ea6388013fc31c4009ff90e2004ff88710027ec4388013fd21c4001fa90e2004ff08710097fea188003fe50c4001fea862012ff1431008ffe8188003fe40c4001fea062011ff10310087fe6188043fe30c4021fe9862010ff0c310007fe4188003fe20c4001fe9062000ff0831002ffecb08002ff658401fff32c2003bf99610007facb08002fd658400bfe32c2003bf1961002ffec908002ff648401dff3242002bf99210007fac908002fd648400bfe3242002bf1921007ffea90803bfe5484001feaa4200eff1521002ffec708026ff6384013ff31c2001bf98e1004ffac708026fd638400bfe31c2001bf18e1004ffea7080277f5384013ff29c2009ff54e1004efaa708027fc5384013ffa1c2009ff90e1004ffa8708027fc438400bffb142000bfd8a10007fcc50802afe6284001feb142000bf58a1002ff8c50802afc628401fffa942000ff94a10007faa50803ffc528401dffa142000ff90a10007fa850803bfc4284013ff9942009ff8ca1004ffa6508027fc32840177eb0c200fffd4610027fca308003fd5184009fe28c200effd0610027fc8308003fd4184009fe20c2009ffcc610027fc6308027fd3184009fe18c2000ffc8610027fc4308003fd2184009fe10c2004bf9821007ffea108017fe5084001fea842005ff14210077fe8108017fe4084001fd2042000ff50210007f28108017fc4084013ff9842005ff8c21004ffa6108017fc3084001ff9042005ff88210007fa4108017fc2084009ff8842000fdc4210027f62108003ff65440017fb
  | 2 => 0x20007fcc310012fe6188001feb0c4000bf5862002ff8c31006fff5188001ff28c4000ff546200dff8a31006bff4188001ff20c4000ff506200d7f8831005bff318802dff18c4016ff4c6200b7f8631002bff2188001ff10c4000ff48620057f8431002afe6088037ffa844005ff94220007faa110017fc5088035ffa044005ff90220007fa8110017fc408802dff9844005ff8c2200b7f4611005bfd308802dfc9844005ff0c220057fe4110003ef2088015fd9044000ffd9520005feca900037f65480013fb2a4019ff9952001dfcca90003fd65480017eb2a4019ff1952001df8ca900037c65480073e32a4000ffd9120005fec890063fe64480057f3224000ff59120005fac890063fc64480057e3224019ffd51200c7fca890003fd5448031fe2a24017ffd8d200bdfec690003df63480016fb1a4017ff98d2000dfcc69005ffd634802f7eb1a4017ff18d2000df8c69005fdc63480036e31a4017ffd4d200befea69005ffe534802ffea9a4017df54d200bff8a69005fff434802fff21a4017ff50d200bff88690067ff5248015ff2924000ff54920057f8a490063ff4248015ff2124000ff50920057f8849005fff3248015ff1924017fb8c9200bffa649005fed3248015fe1924000ffd8520005fec290003fe6148001feb0a4000ff18520025f8c290067ff5148001ff28a4000ff545200cff8a290063ff4148001ff20a4000ff505200c7f8829005fff314802fff18a4017ff4c5200bff8629002bff2148001f790a4000ff88520007fa4290003ed2148015fe10a4019ffd4120007fca090003fd5048033fe2824018ffd0120007fc8090003fd4048031fe2024017ffcc1200bffc609005ffa304802ffe9824017fe4c1200bff8609002bff2048015fd9024000ff88120007dc4090017ff65080157fb28400aff9942001dfcca1002b7e65080073f328400aff59420005faca1002b7d65080013eb284005ff19420055f8ca10017ff64080157fb20400aff99020015fcc81002bbe64080055f320400aff59020005fac81002bbd64080015eb204005ff19020055f8c810057ff5408029ff2a04000ff550200a7f8a810017ff63080157fb18400aff98c2000dfcc61002bde63080036f318400aff58c2009dfac61002bdd63080016eb184005ff18c20055f8c61004fff5308027bfa984013ff94c2009ffaa61004f7d5308027fe2984013ffd0c2009ffc861004ffd4308027fe218400abf98820057fea41002bfe5208015fea90400aff14820057fe841002bfe4208015fea10400aff10820057fe641002bfe3208015fe990400aff0c82002ffec21002bfe61080097f308400afd98420005ecc21002bfd61080017eb08400afd58420005eac210017fc610802bffa884000ff94420007faa210057fc5108029ffa084000ff90420007fa821005
  | 3 => 0xe2a28002ef151400fffec6a007eff635003fff31a8001bf98d400fffac6a007efd635003ffe31a8001bf18d400fffea6a007f7f535003fff29a801fff54d400fefaa6a007ffc5350005ffa1a8002efd0d40017fc86a000bfd435003fdea1a8002ff10d40007fec4a0002ff6250001ff3128000ff58940007f8c4a002afc6250041ffa928000ff94940007faa4a0083fc5250005ffa128002efd0940017fc84a000bfd4250001dea128002ff109400fffe64a007ffe325003ffe992801fff0c940007fec2a0002ff6150001ff30a8000ff58540007f8c2a0012fc6150041ffa8a8000ff94540007faa2a0083fc5150005ffa0a8002efd0540017fc82a000bfd4150001dea0a8002ff105400fffe62a007ffe315003ffe98a801fff0c540007fe42a0003fe2150001fe90a8000ff08540015fec0a0083ff5050001ff2828000ff54140107f8a0a000bff4050005fda028002ff901400077c80a000bfc4050005de2028002fe101400fffe60a007ffe305003ffe982801fff0c140057fecb9002aff65c8015ff32e4003bf99720057facb90002fd65c8015fe32e400abf19720057fec99002aff64c8015ff3264002bf99320057fac990002fd64c8015fe326400abf193200f7fea990077fe54c8001feaa6401dff15320057fec79002aff63c8015ff31e4001bf98f20057fac790072fd63c8015fe31e400abf18f200e7fea7900737f53c8039ff29e401cff54f200e6faa790073fc53c8039ffa1e401cff90f200e7fa8790073fc43c8015ffa96400aff94b20057faa59002bfc52c8015ffa16400aff90b20057fa859002bfc42c8015ff996400aff8cb20057dc659002bfd32c8039f6996400aff0cb20057fec39002bfe61c80097f30e400aff58720005fac39002bfc61c803dffa8e4000ff94720007faa39007bfc51c803bffa0e4000ff90720007fa8390077fc41c8039ff98e401cff8c7200e7fa6390073fc31c8015ff90e400afbc8720057fc439002bfd21c8001f690e400aff087200f7fea190003fe50c8001fea86401eff143200effe8190003fe40c8001fea06401dff103200e7fe6190073fe30c8039fe986401cff0c32002ffecb10002ff6588037ff32c4003bf99620007facb10002fd658800bfe32c4003bf1962002ffec910002ff6488035ff3244002bf99220007fac910002fd648800bfe3244002bf192200dffea91006bfe5488001feaa4401aff1522002ffec71005aff638802dff31c4001bf98e200b7fac71005afd638800bfe31c4001bf18e200b7fea71005b7f538802dff29c4016ff54e200b6faa71005bfc538802dffa1c4016ff90e200b7fa871005bfc438802f7eb14401bffd4a20057fca510003fd5288015fe294401affd0a20057fc8510003fd4288015fe2144016ffcca20057fc651005bfd3288015fe1944005ffd86
  | 4 => 0xffd5194007fe28ca003df14650137fe8328003fe4194001fea0ca026ff1065012ffe6328097fe319404bfe98ca025ff0c650007fe4328003fe2194001fe90ca000ff0865001dfcc12800fff5094007bfa84a003fed425002ff8a12800ff8509404dffa04a005ff1025012ffe6128017fe309404bfe984a005ff0c25001dfecaa8003ff64540017fb22a024ff99150015fcc8a8003fd6454049fe322a002bf1915001ffea8a800ffe5454049bf2a2a003ff5515001ff8a8a800f7c5454047ffb1aa023bfd8d5011ffcc6a8006fe6354047feb1aa023bf58d5011ff8c6a8006fc6354007ffa9aa003dfd4d5001ffca6a800ffd5354047bea9aa003ff14d5011ffe86a808ffe4354047fea1aa023ff10d50007fec4a8002ff6254001ff312a000ff58950007f8c4a802afc6254007ffa92a003dfd495001ffca4a800ffd5254001bea92a003ff14950127fe84a8003fe4254001fea12a024ff1095011ffe64a808ffe3254047fe992a023ff0c950007fec2a8002ff6154001ff30aa000ff58550007f8c2a8012fc6154007ffa8aa003dfd455001ffca2a800ffd5154001bea8aa003ff14550127fe82a8003fe4154001fea0aa024ff1055011ffe62a808ffe3154047fe98aa023ff0c550007fe42a8003fe2154001fe90aa000ff0855001dfec0a800fff5054007fda82a003ff94150006fca0a800ffc5054007be282a003fe14150127fe80a8093fc4054047ff982a023ff8c15011ffa60a808ffc305400bffb2c8000bfd9640117fccb2000efe6590001bf32c80039f99640007facb20002fd6590001beb2c80009f5964002ff8cb2000efc65900057eb248002ffd5240017fca92000bfd5490005fe2a48005ffd8e4010dfec720087fe63900037f31c8021ff58e4010dfac720017fc63900037e31c8021ffd4e4010efea720087fe5390043fea9c8021df54e4010ff8a72000bff4390005ff21c8002ff50e40017f88720017ff6290001ff314800abf98a40007fac520002fd629000bfe3148022ffd4a40007fca520003fd5290045fe2948002ffd0a40017fc852000bfd4290005fe2148021ffcca4010ffc6520087fd3290043fe1948005ffd8640007fcc320012fe6190001feb0c8000bf5864002ff8c32008bff5190001ff28c8000ff54640117f8a32000bff4190005ff20c8000ef90640017fa832000bfc4190005de20c8021ffcc64010ffc6320087fd3190043fe18c8000ffc8640007fc4320003fd2190001fe10c8002bf98240117fea120017fe5090001fea848005ff14240017fe812000bbf4090005fda048005ff10240017f08120087ff309000bff1848021ff4c24002ff86120003ff65500017fb2a8020ff9954001dfccaa0003fd65500017eb2a8020ff1954001df8caa000aff6450005ffaa28020efd5140017fca8a000bfd5450005f
  | 5 => 0x9121005fac8908affc64484057e322422cffd512115ffca890803fd5448457fe2a2422affd8d21155fec6908abfe63484037f31a422aff58d21155fac6908abfc63484037e31a422affd4d21156fea6908abfe5348455fea9a422adf54d21157f8a6908abff4348455ff21a422aff50d21157f886908b3ff5248415ff2924200ff54921057f8a4908afff4248415ff2124200fb90921007fa8490803ed4248415fe212422affcc921057fc64908abfd3248415fe192422cffd4521027fca290803fd5148409fe28a422bffd0521027fc8290803fd4148409fe20a422affcc521027fc62908abf63148455fe98a422afd4c521027f8629082bff2148415fb90a4204ff88521027dc4290803ff60484017fb024200ff98121007fac090803fc60484017e302422cffd4121167f8a0908afff4048457fe202422affcc121157fc60908abfd3048455fe1824204ffd9421025feca10813fe65084077f3284204ff59421005faca10813fc65084097e3284204ffd9021025fec810813fe64084057f3204204ff59021005fac810813fc64084097e3204229ffd5021147fca810803fd5408451fe2a04204ffd8c21025fec610813fe63084037f3184204ff58c2113dfac610813fc63084097e3184227ffd4c2113efea61089ffe530844ffea984227df54c2113ff8a61089fff430844fff2184227ff50c2113ff8861082afe6208415ffa90420aff94821057faa41082bfc5208415ffa10420aff90821057fa841082bfc4208415ff990420aff8c821057fa641082bfc32084097f3084204ffd4421027fca210813fd5108409fe2884204ffd0421027fc8210813fd4108409fe2084204ffcc421027fc6210813fd3108409fe1884204ffc8421027de4210813fe2108409fb1084204ff48421027da421082bf52108409ffb004204ff98021005fcc010813fd60084017eb004204ff1802114ffea0108a7fc5008451ffa004228ff1002113ffe601089ffe300844ffe9804227ff0c02101dfacb28017ff649404dff324a002bf992500077cc92800abe6494001feb24a000bf592500077ac928002bd649400bfe324a002bf1925001ffea92800f7f5494007ff2a4a003ff55250006faa92800ffc549400bffb1ca025bfd8e5012ffcc728006fe639404bfeb1ca025bf58e5002ff8c728006fc6394007ffa9ca003dfd4e5001ffca72800ffd539404bbea9ca003ff14e5012ffe8728097fe439404bfea1ca025ff10e5002ffec528003fe62940157f314a000ff58a50005fac528017fc6294007ffa94a003ff94a50006fca52800ffd5294007fe294a003df14a50137fe8528003fe4294001fea14a026ff10a5012ffe6528097fe329404bfe994a025ff0ca5002ffec328003fe61940097f30ca000ff58650005fac328017fc6194007ffa8ca003ff94650006fca328
  | 6 => 0x7fe1928202bfd85411a7fea2a0813fe5150401fea8a8204ff14541017fe82a080bf74150409ff20a8204ef90541027f882a0813bc4150405fa20a8233ffcc541027fc62a08cffd3150409fe18a8200ffd8141005fec0a0803fe6050401feb028200ff18141005f8c0a08d3ff5050469fe2828202ffd01410177e80a080bfc4050467ff9828233ff8c14119ffa60a08cffc3050415ffb2e420abfd9721057fccb9080efe65c8415bf32e42039f99721057facb90802fd65c8415beb2e42009f59721057f8cb9082afc65c8415ffb26420abfd9321057fcc99080afe64c8415df3264202af99321057fac990802fd64c8415deb264200af59321057f8c99082afc64c8465ffaa64231ff95321007faa9908c7fc54c8415ffb1e420abfd8f21057fcc790806fe63c8415feb1e4230bf58f21057f8c79082afc63c8461ffa9e4230dfd4f21187fca7908c3fd53c8461bea9e4230ff14f21187fe87908c3fe43c8461fea1e4230ff10f21057fea59082bfe52c8415fea96420aff14b21057fe859082bfe42c8415f7216420aff50b21007da859082bfc42c8415ff996420aff8cb21057fa659082bfc32c8465ffa8e4204ff94721007faa390813fc51c8463ffa0e4204ff90721007fa8390813fc41c8461ff98e4204ff8c721187fa6390813fc31c8415ffb06420aff98321005fcc19082bfd60c84017eb06420aff18321197fea1908cbfc50c8463ffa064231ff10321187fe61908c3fe30c8461fe9864230ff0c321027fecb10812ff6588409ff32c4203bf99621026fccb1080e7e6588409feb2c4200bf59621026facb108027d6588409fe32c4204bf19621027fec910812ff6488409ff3244202bf99221027fac910802fd6488409fe3244204bf1922117ffea9108bbfe5488401feaa4422eff15221027fec710812ff6388409ff31c4201bf98e21027bcc710806de6388409feb1c422dbf58e21027bac710802dd6388409fe31c4204bf18e2116ffea7108b77f538845bff29c422dff54e2116efaa7108b7fc538845bffa1c422dff90e2116ffa87108b7fc43884557eb14422fffd4a21057fca510803fd5288415fe294422effd0a21057fc8510803fd4288415fe214422dffcca21057fc65108b7fd3288415fe1944204bf98621027fea310813fe5188409fea8c4204ff14621027fe8310813fe4188409fea0c4204ff10621027fe6310813fe3188409fb18c4204ff4c62116fea6310813fc3188409ff90c4204fbc8621057ee4310813ff6088409ff3044200bf98221027fac110802fd6088409fe304422fffd422117ff8a1108bbff408845dfe204422dffcc22116ffc61108b7fd308845bfe1844200ffd9521005feca908b3fe65484077f32a4200ff59521005faca908b3fc65484077e32a4200ffd9121005fec8908affe64484057f3224200ff5
  | 7 => 0x28812ff6554401ffb22a200bfd91510077ec8a8802bf6454471ff322a202bf99151007fac8a88e3fc64544057e322a200ef1915101578c8a880fff5454407bfaa2a203ff9515101ffaa8a88037d5454407fe2a2a237ffd8d511bdfec6a88dffe63544037f31aa237ff58d511bdfac6a88dffc63544037e31aa203ffd4d5101efea6a880ffe5354407fea9aa237df54d5101ff8a6a88dfff435446fff21aa237ff50d511bff886a8803ff62544017fb12a200ff98951007fac4a8803fc62544157e312a203ffd495101ffca4a88037e5254407fea92a203ff1495101ef8a4a88e3ff4254401ff212a200ff509511c7f884a88dfff325446fff192a237ff4c9511bff864a880eff6154407ffa8aa203fdd4551027fca2a88137e5154409fe28aa204df1455101fe8a2a88e3ff4154409fe20aa237ffcc551027fc62a88dffd3154409fe18aa200ffd8151005fec0a8803fe6054401feb02a200ff18151005f8c0a880fff5054407bfa82a203ff141511c7fe80a88e3fc405446fff982a237ff8c1511bffa60a88dffc3054409ffb2c8204bfd9641027fccb2080efe6590409feb2c8200bf59641027f8cb20812fc65904057eb248202ffd52411b77ea92080bfe5490405feaa48202ff1524101778a920813ff63904097fb1c8204ff98e4100dfcc720813fd639046b7eb1c8204ff18e41025f8c7208d7ff539046bbfa9c8235ff94e411affaa7208d77d539046bfe29c8202ffd0e410177e872080bfe4390405fea1c8235ef50e41017f88720813ff6290409ff314820abf98a41027fac520802fd6290409fe3148236ffd4a41007fca520803fd529046dfe2948202ffd0a410177e852080bfe4290405fea148200ef50a41017f885208d7ff329046bff1948235ff4ca411aff86520812fe6190409ffa8c8204ff94641027faa320813fc5190409ffa0c8204efd0641017ee8320813fc4190409fa20c8204ffcc641027fc6320813fd3190409fe18c8204ffd8241027fcc120802fe6090409feb048200bf58241027f8c1208dbff509046dfe2848202ffd0241017f8812080bbc409046bff9848235ff8c2411affa61208d7fc3090401ffb2a8200bfd9541006fecaa08027f6550469ff32a8203bf99541007facaa0802fd6550469fe32a8203bf19541006f8caa080e7c65504097fb228202ffd5141017fca8a080bfd5450405fe2a28233ffd8d4119dfec6a08cffe63504037f31a8233ff58d4119dfac6a08cffc63504037e31a8233ffd4d4119efea6a08cffe5350467fea9a8233df54d4119ff8a6a080bff4350405ff21a8202ff50d41017f886a0803ff62504017fb128200ff98941007fac4a0803fc62504157e3128234ffd4941007fca4a0803fd5250469fe2928202ffd0941017fc84a080bfd4250405fe2128233ffcc94119ffc64a08cffd325046
  | 8 => 0xf98e4200dfcc72102bfd639087b7eb1c840aff18e42055f8c7210f7ff539087bbfa9c843dff94e421effaa7210f77d539087bfe29c8402ffd0e42017fc872100bfd4390805fe21c840abf98a42057fea52102bfe5290815fea94840aff14a42057fe852102bbf4290805f7a14840aff10a42057d8852102bff3290815ff194840aff4ca42057f8652102bff6190815ff30c8404bf98642057fac321002fd6190815fe30c843effd46421f7f8a32100bff4190805fe20c843dffcc6421effc63210f7fd319087bfe18c840affd8242057fcc121002fe6090815feb048400bf58242057f8c1210fbff509087dfe2848402ffd0242017f881210f7ff309087bff184843dff4c2421eff86121003ff65508017fb2a8400dfd9542004fecaa10f3fe65508077f32a8400ff59542005facaa10f3fc65508077e32a8400df1954201cf8caa102aff6450805ffaa28402ff951420177ca8a100bfd5450801deaa28402ff151421dffec6a10eeff6350877ff31a8401bf98d421dffac6a10eefd6350877fe31a8401bf18d421dffea6a10ef7f5350877ff29a843bff54d421defaa6a10effc5350805ffa1a8402efd0d42017fc86a100bfd4350877dea1a8402ff10d42015fec4a10f3ff5250815ff2928400ff54942057f8a4a100bff4250805f7a12840aff909420577c84a102bfc4250815de2128402fb109421dffe64a102bfe3250877fe992840aff0c942007fec2a1002ff6150801ff30a8400ff58542007f8c2a1012fc6150879ffa8a843cff14542017fe82a100bfc4150805de20a843bffcc5421dffc62a10effd3150877fe18a8400ffd8142005fec0a1003fe6050801feb028400ff18142005f8c0a10f3ff5050879fe2828402ffd01420177e80a100bfc4050877ff982843bff8c1421dffa60a10effc30508077eb2ca204ffd9251027fcc92880afe6494409feb24a200bf59251027f8c928812fc6494407ffaa4a203ff952511d6fca92880ffd5494407fe2a4a203df15251027fec728812ff6394409ff31ca201bf98e51027fac7288e6fd6394409fe31ca204bf18e5101ffea72880f7f5394407ff29ca203ff54e511cefaa72880ffc5394473ffa1ca239ff90e511cffa87288e7fc4394409ffb14a204ff98a51055fcc528813fd62944017eb14a204ff18a5101ffea52880f7f5294407ff294a203ff54a51006faa52880ffc5294475ffa14a200ff90a51007fa85288ebfc4294473ff994a239ff8ca511cffa65288e7fc32944097f30ca204ffd4651026fea32880ff75194409fe28ca204fd14651027fe8328813fc4194409ff98ca204ff8c651027fa6328813fc3194409ffb04a204ff98251005fcc128813fd60944017eb04a204ff1825101ffea12880ffc5094407be284a23affd02511d7f881288e7ff3094473ff184a239ff4c2511cff861
  | 9 => 0x7ffa9aa803dfd4d5401ffca6aa00ffd5355087bea9aa803ff14d54017fe86aa00bfe4355005fea1aa802ff10d54007fec4aa002ff6255001ff312a800ff58954007f8c4aa02afc6255007ffa92a803dfd495401ff8a4aa00bff4255005dfa12a802ff1095421ffe64aa10ffe3255087fe992a843ff0c954007fec2aa002ff6155001ff30aa800ff58554007f8c2aa012fc6155007ffa8aa803dfd455401ff8a2aa00bff4155005fe20aa843ffcc55421ffc62aa10ffd3155087fe18aa800ffd8154005fec0aa003fe6055001feb02a800ff18154005f8c0aa00fff5055007fe282a803df14154017fe80aa00bfc4055087ff982a843ff8c15421ffa60aa10ffc30550077eb2ca40affd9252057fcc92900afe6494815feb24a400bf59252057f8c92902afc6494807ffaa4a403ff95252216fca92900ffd5494807fe2a4a403df15252057fec72902aff6394815ff31ca401bf98e52057fac729106fd6394815fe31ca40abf18e5201ffea72900f7f5394807ff29ca403ff54e5220efaa72900ffc5394883ffa1ca441ff90e5220ffa8729107fc43948157f314a40affd4a52056fea52900fef5294815fe294a40afb14a52057fe852902bfc4294815ff994a40aff8ca52057fa652902bfc3294815ffb0ca40aff98652025fcc32902bfd61948017eb0ca40aff1865201ffea32900f7f5194807fe28ca442ffd0652217f88329107ff3194883ff18ca441ff4c65220ff8632902bff6094815ff304a400bf98252057fac129002fd6094815fe304a403ffd425201ff8a12900f7c5094885ffa04a442ff1025220ffe6129107fe3094883fe984a441ff0c252055fecaa9003ff64548017fb22a440ff99152015fcc8a9003fd6454881fe322a402bf1915201ffea8a900f7f5454807ff2a2a403ff55152006faa8a900ffc545487fffb1aa43fbfd8d521fffcc6a9006fe635487ffeb1aa43fbf58d521fff8c6a9006fc6354807ffa9aa403dfd4d5201ffca6a900ffd535487fbea9aa403ff14d521fffe86a90fffe435487ffea1aa43fff10d5201dfec4a900fff5254807f7a92a40aff94952056fca4a902bfc5254815be292a403fb14952207fe84a902bfc425487fff992a40aff8c9521fffa64a902bfc3254801ffb0aa400bfd8552007fcc2a9003fd6154801fe30aa404bf1855201ffea2a900ffc5154807be28aa440ffd0552207f882a90ffff315487fff18aa43fff4c5521fff862a9003ff60548017fb02a400ff98152007fac0a9003fc60548017e302a403ffd415201efea0a900ffc5054881ffa02a440ff101521fffe60a90fffe305487ffe982a43fff0c152057fecb2102aff6590815ff32c8403bf99642057facb21002fd6590815fe32c840abf19642015fac92100bff5490805ff2a48402ff55242017f8a92102bff63908157fb1c840af
  | 10 => 0x80000200380000100000280000080080080300100000100500000100080000000000000000000080200000080000e00000280000080100580380000100080a00380700380000080380000000000200080080100000080000100500300300300000000080080200100000000080080180400000000100000180300000000000000100080300000000100100500000100080000080100380000000100000180280000000200000180100180080800000100000000800000180180080100000280400280180080100180080000080180180300000180280080000000000180380080000100000080280100100080000200080100000100000000180080100000480000100100000180000000300000000000000000000000080000200600880000200100580080100080080080200500080000000100000000280080000100080200000280000180100080000500000180000100200600100100300100100080000000000000080000100280600000180000180000000000200200000480200080080080180000300080200000100380200000180080000000000500400180400800000180280200000000080000100180280000280000000300280280280300b80000000480080000380080180200000000000000000000280080000000200000080000000000000000000080000000080100000000000480180000000000100100000100000000080080100080000000080000100000380800180080080000000100080200000400100200000100480000200600280880380100400180000000000180000180100280000000200100000180100000000280180200000000380080080280080200100000000180100100000000000000200080000080080680100080000000200000080080100080000280100380000380100000180080080980000080200080180280080000080100200200100080000000100180280300180000080000080180200100500100100000100000280080100000000080580200080000000080100180200200000000780380000700080000000080400480100280180000000000080280180100200000a80180400000280000000100100580000000000080780300080280000000080100000000000080000080180000080180280080000a80100000000080000080100080000080180000080200300000080000200000000080000080200080000300000580280280000080080080000080180100000100000080000500280000000180000100180000000080080000380000100080280080000700100000180000080080000aff65550057fb22a802ffd515401f7ea8aa00bfe5455005bf2a2a802ff15154016f8a8aa00bbc5455087ffb1aa843bfd8d5421ffcc6aa006fe6355087feb1aa843bf58d5421ff8c6aa006fc6355
  | 11 => 0x413a00023591d8b641d24310000a5641332a10950ea10f26321e8df84e708f000000075e1fe9d640000003c2000000001221c800017a0001409738a28368080800000051b00016547b213900000000000002530000000000000000000019519283400006db075141475c0001d28c5800000014e000000000018988c400030932e9df000022127692f44887b407f0000f185a218600bc9387da38b8000b0a69f09109349660b80002078c828883cd86b8eee5020001d005c00002e38000000000000000000062a28f800084c13a0000000000000000000000024c00000001280000000000222132154860c6fe5362d4a0d01c2000000221800088c000000000000023a8f40bd400020600002a45f743a1df48805f028b0b18378000094896c4a46e42471f1450a2bd3e19d807f818404800000000001b380505b0000000164c0000001cb8000cdc240353000000000009f178048e12026d00000006190000a800000751609b681bc47213608ac13861d2790518ea68232d88b105220e728e90a49744b72219b807b857e24400004de0000d28854da66d631f80886c666945986a11461a32a201309d4000000000000000000000000000000000000f9c0000000000000228000000036c25e4401024722000000092ce72000000000000045a2b000000004d503b80000005ed00000000001b500000000006f33cf800109e0002f40000000000000000105e7610921ec800000024c8000c7400000009cc01600e00014842820000280908000000000000000070900004c00000000000000cca00000010bc000000000000000000008fa15c53a01c3411b2027829a2b680000000bc000221414a4a0089836800000200016f00000dc000000089e51c00d8f1c00000000014d09ec4bc13689dca7624900021900002d700000007e463800000000000000000d044f80000000000e7471d368000000067710880010a42b84001cf42380000000000ac87de0678decd182f500000000000000001464bf00000f8000000000041c8000e9255a18d9b70b423a6000000063238a13e9b9c00076900000000000a23ae20a00005b8000194c000000000000089825835e9870e1a1181c798687d86cb3338b245620000000f5800061e00015f000061700000009fc00000021580000000000cf06025f535686148da3ac069224d10847000580000180000580100080400100200080000000000000100080280180100080000080100000080400080080000000000080000000000100000280080080000000080000380100000200000400100000000400280480400000000180080100080000000180000000080080300100200000100080000000100480000000180180000080000080400180100080000000100000000080000000100180000200000680000000100000000
  | 12 => 0x44720fc00048416a000064400000000000004be0601910d285281348398a900180001490fca0000749d2ccbc86742e0ad000084300021180000000be8dd83904e907c98849d80003831b0c79600000000006522d926880005ce00042d8c28de2000000000000021a01d800034407407c13ec0000000ce21786962750000ecc00000006b8cf44ca7f51c60a5800036e04580e10c26b41ee9adc0004fa000000000017a2b880000004bb35700003f2053000000000000000000000000000000acc0000004148000afa00000000009b60003f6000000055300008a40002f040097343607c61508e810287213e2127400007d33f817c2b200936c9124b3400000000000000000000000000000000120c00000000000000007aa00000000006fd0e7800000054f0000ce40000003db000084e000237800000069b0001514eba0000001ccc9b00003ca800041e00030381bc00000000000000002143f18000a947e6000156c412000096800000000000000587527eb000000000000000010dca54264111800095600014f1b450c00001828f200003140f59440d7223609b877099e20303c000005815f0000e047a20001110000000000382000099c80400018b80005a300021a45c2000000000000000005f00000000000da103ce7e47e05780010e0596000173c00000000000007cc000301a2600002500001d080000001d380009c400000011c400000000000003a6000033000115a2bb0931d5038466f02e1eac78473700001b008878902900003800001b1205400061f39480000001943ad8fe8ebe3d700019ac0da15c07d0e1c73000017480000004792b2800051264900000008ae01a0000f2800000000013f4000000000000000000000002fc0006f500000003d40000000dac000000000000000019d0f705e000003012d000090a2010001b1406c000000079000070e381996cff02c22f5800004c0000001a48eda82403390108cc1820000ddc348474000209c0000170001f0000000000000000003a220100000006401f28a0c00047c1b3161cad235722887410660002b10000bc262900000000007a000007340000000539fcc8783b50001d1c0000002df01a80000001a10214d2c0000001d889cc60f2cf1a6400065f3c30fe40000002e60d206fc3d5195113400600017d1c2c63e6641ed91e001400008d86acd4a000000000090049b3c380000001ef08a800000033e380089083e4f304d0d1c0005181b500000005af000160c0006f42bb221c2cc02a3d200b51580000a700003f64b93c7048c4c41ac00011a40005e91f99630000000000000000000000000006800002a9000000000000000002a60003cb94802920000000d6476245000000000007310088000c7c68b33e000025c2f73920678f94000000015c00000000000000002a5000013
  | 13 => 0xd062d6382800113220700000002705e42e100007123150dc82cc5a21700758df441811d35d8e4000000000000002b00cb00000000007b941a80000000002301175128000000146800000000011ec00068d0000000eb065912e9b7900a4531a30000dec0f7000000056c0481a68d4000041500000001240001d5800000000000010500004f80f98e380003f400014d4e4c0000309a9c21a01f000120838200000008709160003d30000000433000228405080d196200c2060002890dcc000686000034c9800000000af86ea5070001880bb449a20080004744180ff10f40000000940000a7e00000000000004000001a5503200000000000000001db19580000003b8800040a000000010065c00000013c400089e00015dc0004a300000003ee80800012c8f5a098314000004e00000016b40001793769d300002c72c69b8400000023119cd0f862c0001fb91341e800003940006dd000091800000000000000000000001d10fb800029c00000003533199f5800000016d00000001980000620000000000172800010701e860400010a11006180000000000750546616000188c00e27e285095d09003a162a030a1a4b60000ff80000000001640ea23ba0001c94b546d804a88f8c100003e9063059c680203000000000000000000000ee00000000000000e48fa045a5f2000000000039209617e42da00014820082561c300014a42f80000001c5000000000002c40ba33000020b00000000cb97009ea8820890360a660310b0189c00000000000003a20ef0e300000000000000000cc200000005c445e7ed0a4000000084500013b800044e041000107a00000000000004ca1c280000000004050000000000000057400069e000000000000030c0000e3020e0c00cfc0000000000a640007d900012b000010c000000000000000010f8dd000000014c80006b600000000000000002224b1c0003b188dca2287b000220405c23b3ba80007702f342890e03e42000001e600002340b79f508760000000000c4a3e7000000000000000011651383173e380000001b8109000064820b1e911200e43272b3980813e5ef0000000000543186885cf226502da0000afe4b4043800000025900000000000002239b28000338156800000000042383c40007f400002302fc4030000d845300000409c440b4000379152c00000019b9a907da000000086028a80927b8a290625592d2000000069d000000000000005800000c60003bc8000000000133800000060c00006c800a69300f1234ef600035d000000018912986640000ff00004d000000000000000000000c380000003e00000000d5e00011e8000a0600040300000000000001db00002930000000000000000000000062400000000000000000000f027450001a1452462d00015745f8000000151800000
  | 14 => 0x38f800090e0000a58edc0000001318d9000042e0340000c264dc000000000010e0000000f141a70021f046f23c1082800093c0001ae06480000002610000cfc40e2c7912800051320e0e100002711458e640323c50000ad4000232000000045c0000001c703f88422a89e9c7f000019d00000000000b50000dc67b700000002e468a415093c00035421900007c4000000000000087e0c70a980003032111d1800081f0000000000000335123001a0ac0000a5c0000b233c92e00003f500000000005c10859accbce00000010800004440001a10d7c1a00000000a1e65a05680000000000000000f7e21000000000004d00000000c5e0c125292186686471801d20000790000000017442d21a21540000000001044b9214d000155c0007d8000000000071500000000003c03028000fb67d7000000081a00000019f400000041b0000e7800000019600000c5000000025e7882ea1f9c47e2ed00404d8694000175800009c00042c835800052e0001bfc82c0002961b3814c15e000000016a41e00010c0b885bd07d80005360003361f4c77a0000700000a7454700000000006a82f70264aa82800000f7cbe235b2a4a274b5c00027f80002a2000000000000064e03f9794bfa0000000cad0760000661620b3827b00000000000000000dd0f7c5d81dc8000000820000000000023c00019ecb5609636100005ca56a05c9ce02888a50000000000000000051cb900001e99bf882000000000000000f532191080003ff000000000000000000000002610000558d621f500000000008b200007590822ca2521eec66471a03b1b7d0d600006a02a04ac1ad0c985548be6f936a96fc0000002bd00009a60000000000000818000176c000000450000000000021a800083a25c1300d3c0003230000000000000000220c00039e3ea9e642e63e924b1b109be0001ae86fcf907560000b890f200000000000000000c7a1c816e0003180154000000112800109200041d11ccb8c0000198b0c000000000000000030b000004c0f800020d0000c640000000000b3200033d0bf81c80004520000abe0001b295d00000002c500000000000009118000441055800000028400017e8bcc000000000000000035e20b82280002e59bdc00039a0128000398000458862c00033600000000004633d11c20000895000000043a0003f419d87980000000000000000000115102e7653a0845c1e60002930d544f04e8000165c00000000000007760000000000c5600000000000007e41a200009e000000000000000000000000000000000000000053018e042516c2510001b980000000cfa2880520b62861438d700d500017143ca7192718000f420002ff0000b4086f000226d0da00014a00000001e000000000000001fb8bd0d560000000000000000000219432c00013580
  | 15 => 0xa889820000cd15ec5547fc14a80000000001a18000000000000000000000035180007c82bc25a800051e13b00000000000000000000ba03ce0000f7800000000022c000000000009e800000040800002660001f08000000767000000037a0003f01e1400000000000d40003a80001170ed64c91600fc00006ea146119d060000000000000087300000000002ae15b80005be0000431254aea3ef0000000698000000000000064d2b59908b167f92a60d4400013f000000103800000000000006452f980000000003c6800115600000003380001100f487b447014200001905480f001181a4f9800032880000002bf30d80003c65f60c8145437400038d95cc9de000363108cce80971be0000a6e00000016b00e66f80ec000000039600011dc00000000000000004d9000201c000000308093800008a08100009f25fc45796080002ac1b487646f08664130000f7044b0a79c8ca0c0000001f7c00078323d00008dc33b13b15984661251941320000000000000000056e03f00000f60003a787e82ce85a0001560b300203980000858000098a044ff659b0000bfc6f42dc00015046e40000001488f166222450000000000000023c27a6980951c4000003c2d304180004550001c78f3c00004701040004c500000000000000000324eec5de00000000005090001c04aaa4311838000c0c0001998000000572000090503a689000000082e3450bd866cdde0540000000a7864639a185043231d1380b200000003a700005603bc189000000083c00000000000000e7082893e5312489828d1c7223020aac0001544550000ad000000000000007f20d79c08f0406017d800043c7680000c08f4a22c00007b00003f10b5848400086e10200000000ae1e221c435472708c80005cc5a50001478e5e64f3008308ce00003fb9fe82c471327a0000ea400007e21f45502ea1680c8000007000000000000002b81c3ca0035f1e780000000000000c381880000158054ba60000000b8c00046539512c0a7c5b93dd00010d0652000000060c3b221b000046a0000000efc00000024980006ac81600000000004fc0000000e400100001a80c1c39f308800000000013706440000000000000000000000037cf840000821bb0000000000050c5fa3880001f74000000000000019a00000000000000002c88000000000284000000000000000000000003ad00007360000000808c6a04b2bc11842d07cd0b28f0c95a6313368000000000000106505600000000009ba00037280000007bd0001764f6a71200000000dc0001250d481c430426915bc51c0911b880008ac5f42938db40006a22d3930c0000000000528a462cd1da06ccf46000000119084218a1130000c9800035f80000000000000000000793000013cd3867500019c80000002b600000000000000000da80
  | 16 => 0x74a00022444e800039aa088f3488a00000004f227207689a05a422a02b1ecc0008530001800000000000000000000012a21e00007ef1881c3050e42800000000001e233100000000000bf800000041b00000000000790000ea850c83e1ec00000003ad00000000000002c3000000045831b8b4c38a04226b0e906920000ad87c4c786cc0002140f9e0000000fb81900000000000e580003408000eae1e61b817746d88a7000192c4d40003bc1cac3aa80f084182c8161dd11399e041a77a0000f34000071000000011004a000055c7f60d110400005f000000006f800059f00003c80000003648954ed45e2000142c88a0a044b89987161a93f891f4aac6572bc9ba448625f3d6058c0b21770761d54a5a5b700016d516a7b000007fc2e8308000000000000000019a06421bb19a9ff800053900000c80001e1000000000000002280000000000000c3ccb80000000ae400000000012a887477300002a83e88ae000009075e00000000000007cb000049c00053d00000001680000000b54a80000040000001e4cd0a0075d07032600000000005c342500000004810000000d200003c01538caa61500000010ee0000001e5004240500020489a8408000000000008d43b0124dd6000377000000076427095340005d12ca1db80000001030000ab88a917200000000000001380d546fa0fc018814800011ca1003be750000000111e0002dd85b10640001c6a29806800610d80008d842b04d8698bac73e00000000005b00001ff4000660331800106e28842e800000000010b1610000000000000000063d0000000000612000000006e00000003d80000001f19dc800000040d8b300000000000b2c9882cf000129c000000000213800089f1ce80010be896000011c0000000001b5c000688000071c0006a91ad00000002de0001fa40001a100000000187e100005a40000003b300005e20e803d10285ba1b12c0933039400032400000000000001f400000000000000b244eb00007100006c731a224800000035080007064e500000f870c1de04f000018e0a12ee0000b660003d8872c9ae5b6000000000000038b000085472e292800102600027217fcee068f0000000000000000000072a38026392fcccc1160000fac00018d3a68000a5e73b0ba800054e083000000000000000012c4000394454123c1863c60eda0680000001779748f50000071916cb124a1416800108867102f00000004980ad0328bf6046000087c000000234000000000018d177c55e00021f8210aa0492000122400078f00016740000002570c600000001889e480000001ac00009960a90000000000000000000065e000000000000000035a80000003f615d019400079d000000111a213177010c0b62ec3f111480d6890000014400000037d828cf5e0003b78000da41502dd0
  | 17 => 0x79269102c0a7ce6400000000010b00000001f44d340000001d0c18c0002f180000000000001dfc000863000222c0002db0000d80d8224825785b8c6c000367982400084c00000002984122ea80fd0427f60000000abc0002120be4d6036f3ff93780002300000ef8d643a30db958494410000005d8f2c0930000ba000000031d80000005a800004d41ba00000000003ec00028200000000001228000efc7070b080000006c03d489fc00000000007f50a80000001250f5c000000000072670a306925c000000000160065a00041292400000003e48f50f3800000000000000004070000d583da1d817b0e6c4a9000000050486a00e80e400072840591a90d800022f0000c7208900000001fa5421d09b3473828d00012a00000003968000d2e0001f51a1c00035e3711fa869c164000079cf7850145a0000fe0000000212c0000001590cc400000000000000000002eb80000000004268bc880e11a17b00000006f000000000000bb3ba0e08ac687f18f11fc3b40d900018981e800028b800000000006d8000c94
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc5458810006ef7358810006ee7358810006ed7358810006ec7358810006ef53588100066f5358810006ee5358810006ed53588100066d5358810006ec5358810006ef4358810006ee4358810006ed4358810006ec4358810026ef7158810026ee7158810026ed7158810026ec7158810026ef5158810026ee5158810026ed5158810026ec5158810026ef4158810026ee4158810026ed4158810026ec4158810026ef3158810026ee3158810026ed3158810026ec315881002eee705881002eec7058810006ef505881002eee505881002eec5058810006ef405881002eee405881002eec4058810006ef305881002eee3058810006ed305881002eec3058810026ef1058810026e7105881002eee1058810026ed105881002eec1058810054ff769481002cfe7694810004fd769481002cfc769481001e7e65948100067d6594810216be6494810006bd649481020ede6394810006dd6394810056ee6294810006ed6294810004ff765481002cfe7654810004fd765481002cfc765481001e7e65548100067d6554810206be6454810006bd64548101fede6354810006dd6354810056ee6254810006ed6254810054ff769081002cfe7690810004fd769081002cfc76908101f67e65908100067d6590810016be6490810006bd64908101eede6390810006dd6390810056ee6290810006ed6290810004ff765081002cfe7650810004fd765081002cfc76508100057f75508100457c75508101e67e65508100067d6550810016be6450810006bd64508101dede6350810006dd6350810056ee6250810006ed6250810005f77150810025f4715081007cff765401001e7e65540100067d6554010126be6454010006bd645401011ede6354010006dd6354010006ee6254010006ed6254010074ff76500101067e65500100067d6550010016be6450010006bd64500100fede6350010006dd6350010006ee6250010006ed6250010076fa6050010004fd76c80100f67e65c80100067d65c80100eebe64c8010006bd64c80100e6de63c8010006dd63c8010056ee62c8010006ed62c8010004ff76480100057f75480100457c75480100ce7e65480100067d65480100c6be6448010006bd6448010005df7348010035dc73480100bede6348010006dd6348010056ee6248010006ed624801002fe8204801002df77644010006f77644010004f7764401000777754401000774754401002f76654401002f756544010007b77444010007b4744401002fb6644401002fb5644401002ef7634401002fd66344010226f5634401002fd56344010006d5634401022777534401022775534401002ef7624401002fe66244010006f5624401002fe56244010006e5624401002df77044010027f3704401002ef6604401002ff2604401002ff25044010007f15044010
  | 1 => 0x9010004ff765501002cfe7655010004fd765501002cfc765501001e7e65550100067d6555010016be6455010006bd645501021ede6355010005f77155010025f47155010006df7558c10006de7558c100065e7558c10006dd7558c100065d7558c10006dc7558c10006df7458c10006de7458c10006dd7458c10006dc7458c10006df5458c10006de5458c10006dd5458c10006dc5458c10006df7258c10006de7258c10006dd7258c10006dc7258c10006df5258c10006dc5258c10006df4258c10006dc4258c10026df7158c10026de7158c10026dd7158c10026dc7158c10026df5158c10026de5158c10026dd5158c10026dc5158c10026df4158c10026de4158c10026dd4158c10026dc4158c10026df2158c10026de2158c10026dd2158c10026dc2158c10036df7058c1002ede7058c10036dd7058c1002edc7058c10006df5058c1002ede5058c1002edc5058c10006df4058c1002ede4058c1002edc4058c1002ede2058c1002edc2058c10026df1058c10026d71058c1002ede1058c10026dd1058c1002edc1058c10056ef7598810056ee7598810056ed7598810056ec7598810056ef7498810056ee7498810056ed7498810056ec7498810006ef5498810006ee5498810006ed5498810006ec5498810056ef7398810056ee7398810056ed7398810056ec7398810006ef53988100066f5398810006ee5398810006ed53988100066d5398810006ec5398810006ef4398810006ee4398810006ed4398810006ec4398810026ef7198810026ee7198810026ed7198810026ec7198810026ef5198810026ee5198810026ed5198810026ec5198810026ef4198810026ee4198810026ed4198810026ec4198810026ef3198810026ee3198810026ed3198810026ec319881002eee709881002eec7098810006ef509881002eee509881002eec5098810006ef409881002eee409881002eec4098810006ef309881002eee3098810006ed309881002eec3098810026ef109881002eee1098810026ed109881002eec1098810004ff755881001cfe755881001cfc7558810004ff7458810014fe7458810014fc7458810004ff735881000cfe7358810004fd735881000cfc73588100067f53588100067d535881002cff725881002eef7258810006ef5258810006ec5258810006ef4258810006ec4258810006ef3258810006ee3258810006ed3258810006ec3258810024ff7158810024fe7158810024fd7158810024fc7158810026ee2158810026ec2158810054ff705881002cfe7058810054fd705881002cfc705881002eee205881002eec2058810026f71058810006ef7558810006ee7558810006ed7558810006ec7558810006ef7458810006ee7458810006ed7458810006ec7458810006ef5458810006ee5458810006ed5458810006e
  | 2 => 0xcfc73594100467f53594100067e53594100067d53594100467c5359410004ff7259410054fc72594100467f52594100467c5259410024ff7159410024fe7159410024fd7159410024fc71594100267e51594100267c515941001cff705941002cfe705941001cfd705941002cfc705941002e7e505941002e7c50594100067f74594100067e74594100067d74594100067c74594100067f73594100047f73594100067e73594100067d73594100047d73594100067c73594100067f43594100067e43594100067d43594100067c43594100067f72594100067e72594100067d72594100067c72594100067f42594100067c42594100067f32594100067e32594100067d32594100067c32594100267f71594100267e71594100267d71594100267c71594100267f41594100267e41594100267d41594100267c41594100267f31594100267e31594100267d31594100267c31594100267f21594100267e21594100267d21594100267c21594100467f705941002e7e705941002e7c70594100067f405941002e7e405941002e7c40594100067f305941002e7e30594100067d305941002e7c305941002e7e205941002e7c20594100267f105941002e7e10594100267d105941002e7c1059410004ff755901001cfe755901001cfc755901002cff745901002ebf7459010006bf545901003ebe545901003ebc5459010004ff735901000cfe7359010004fd735901000cfc73590100067f53590100067d535901003ebf4359010006be4359010006bd435901003ebc4359010004ff7259010054fc725901003ebf425901003ebc4259010024ff7159010024fe7159010024fd7159010024fc7159010026be4159010026bc4159010014ff705901002cfe7059010014fd705901002cfc705901002ebe405901002ebc4059010026fa1059010026f91059010006bf7559010006be7559010006bd7559010006bc7559010006bf7359010006be7359010006bd7359010006bc7359010006bf53590100063f5359010006be5359010006bd53590100063d5359010006bc5359010006bf7259010006be7259010006bd7259010006bc7259010006bf5259010006bc5259010006bf3259010006be3259010006bd3259010006bc3259010026bf7159010026be7159010026bd7159010026bc7159010026bf5159010026be5159010026bd5159010026bc5159010026bf3159010026be3159010026bd3159010026bc3159010026bf2159010026be2159010026bd2159010026bc215901003ebf705901002ebe705901002ebc7059010006bf505901002ebe505901002ebc5059010006bf305901002ebe3059010006bd305901002ebc305901002ebe205901002ebc2059010026bf105901002ebe1059010026ba1059010026bd1059010026b9105901002ebc105
  | 3 => 0x54248510007f3704851002df47048510007f07048510026f76048510027f36048510094fe76941100067f659411001e7c6594110065be7494110005bd7494110006bf6494110136bc649411001cff765411006cfd7654110024fc76541100067f655411001e7c6554110006bf6454110126bc6454110005f77154110025f4715411008cfe769011006d7e75901100057d75901100067f65901101167c6590110006bf6490110016bc6490110005fa769011008efa76901100077a75901100077975901100077b6590110007786590110065f97490110007bb6490110016fa6490110016f86490110067b86490110016b8649011024f7b539011024f795390110025fa7190110025f8719011002efb6190110257ba4190110257b8419011024ff2319011024ff13190110007f22190110007f12190110014ff7650110064fd7650110024fc76501100067f65501101067c6550110006bf6450110016bc6450110005f77150110025f47150110067b84050110025f87650110016f87650110024f876501100077b6550110007786550110065fb7450110007bb7450110007bb6450110016fa6450110016f86450110067b86450110247bb5450110067b8545011023f7b535011023f795350110067bb435011023fb94350110067bb4250110007b94250110007f37150110025fa7150110025f87150110007f07150110067bb4150110007b9415011023ff2315011023ff13150110007f22150110007f12150110024fe76c8110024fc76c81100067f65c81100f67c65c8110006bf64c81100eebc64c8110006ef62c8110056ec62c8110025f671c8110005f571c8110007e521c8110004fe76881100067f65881100de7c6588110006bf64881100d6bc6488110054ff7648110004fd7648110024fc76481100057f754811006d7c75481100067f65481100ce7c6548110006bf64481100c6bc6448110005df734811005ddc7348110006ef6248110056ec6248110005f77148110025f47148110007e52148110004fe760811006d7e75081100057d75081100067f65081100ae7c6508110065be7408110005bd7408110006bf64081100a6bc640811005dde7308110005dd7308110025f67108110005f571081100067f658411007e7c6584110006bf6484110076bc6484110025fa7084110026fb6084110025f6768411002ef67684110024f67684110007776584110007746584110007b76484110007b4648411002df77384110235f5738411022f77538411022f75538411002df77284110005f5728411002df6708411002ef76084110027f3608411002ff24084110007f1408411002cff755941002e7f7559410004ff7459410014fe7459410014fc74594100467f54594100067e54594100467c5459410004ff735941000cfe7359410004fd7359410
  | 4 => 0x891006d7c75589100067f65589100067c6558910005bf7458910065bc7458910006bf6458910006bc6458910005df735891005ddc7358910004ff75589100067f75589100047f755891001cfe755891001cfc75589100067c755891001c7c7558910004ff7458910006bf7458910004bf7458910014fe7458910014fc7458910006bc7458910014bc7458910004ff7358910006df7358910004df735891000cfe7358910004fd735891000cfc7358910006dc735891000cdc73589100067f53589100067d5358910006ef7258910004ff7158910006f77158910006f63158910006f53158910004ff7058910006fb7058910004fe76189100067f65189100067c6518910006bf6418910006bc6418910056ee6218910006ed6218910054ff7694910004fe7694910004fd7694910054fc76949100067f659491001e7c6594910006bf6494910216bc6494910025f67194910005f57194910004ff7654910004fe7654910004fd7654910004fc76549100067f655491001e7c6554910006bf6454910206bc6454910054ff7690910004fe7690910004fd7690910054fc76909100067f65909101f67c6590910006bf6490910016bc6490910025f67190910005f57190910004ff7650910004fe7650910004fd7650910004fc76509100057f755091006d7c75509100067f65509101e67c6550910006bf6450910016bc645091001cfc76545100067f655451001e7c6554510005bf7454510065bc7454510006bf64545101c6bc6454510005fb7054510005f87054510027f01054510014fc76505100057f755051006d7c75505100067f65505101a67c6550510006bf6450510016bc6450510005fb7050510005f87050510004fe76c851002cfc76c851006d7e75c85100057d75c85100067f65c85101967c65c8510065be74c8510005bd74c8510006bf64c851018ebc64c8510006ef62c8510056ec62c8510005fa70c8510005f970c8510005f67688510026f67688510027767588510027757588510007776588510007746588510007b76488510007b46488510025f77388510027d67388510275f57388510027d57388510005d5738851026ef7638851026ef5638851026f77538851026f755388510265f57288510056f66288510056f4628851002df67088510026f76088510027f36088510054fc76485100067f65485101667c6548510006bf644851015ebc6448510006ef6248510056ec6248510027e42148510005fb7048510005f87048510056f47648510054f47648510007776548510007746548510007b76448510007b46448510265f77348510265f5734851025ef7634851025ef5634851025f77534851025f755348510025f77248510027e77248510007e76248510056f66248510056f46248510007e46248510007e64248510007e
  | 5 => 0x66bf42d9110066bc42d9110024fe71d9110064fd71d9110024fc71d9110066bf41d911002cfe70d9110024fd70d911002cfc70d9110066bf40d9110065be76d9110014be76d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110006bf63d9110006be63d9110006bd63d9110006bc63d91100073f53d91100073d53d9110007b631d9110007b531d9110257bb70d9110257bb10d9110257b810d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d91100063f53d9110006be53d9110006bd53d91100063d53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006bf52d9110006bc52d9110006bf32d9110006be32d9110006bd32d9110006bc32d9110006bf71d9110256be71d9110006bd71d9110256bc71d9110006bf51d9110256be51d9110256bc51d9110006bf31d9110256be31d9110006bd31d9110256bc31d9110256be21d9110256bc21d9110256bf70d9110066be70d9110006bd70d9110006bf50d9110006bc50d9110006bf30d9110006be30d9110006bd30d9110006bc30d9110256bf10d9110256bc10d91100057f755911006d7c75591100067f65591100067c6559110066bc6459110004ff75591100067f75591100047f755911001cfe755911001cfc75591100067c755911001c7c7559110064ff7459110006bf7459110004ff735911000cfe7359110004fd735911000cfc73591100067f53591100067d5359110004ff7259110054fc7259110074ff7159110006f7715911008cff7059110006fb7059110005be7619110066be7619110004be7619110006bf65191100073f65191100063f6519110006be6519110006bd6519110006bc65191100073c65191100063c6519110006bf6319110006be6319110006bd6319110006bc63191100073f53191100073d5319110007b63119110007b53119110067b9701911027ebf601911027fbb101911027fb81019110004ff7655110004fe7655110004fd7655110004fc76551100067f655511001e7c6555110006bf6455110016bc6455110054fe76d89100067f65d89100067c65d8910006bf64d8910006bc64d891001cfe75d8910004fd75d891001cfc75d8910014fe74d8910004fd74d8910014fc74d8910004ff73d891000cfe73d8910004fd73d891000cfc73d89100067f53d89100067d53d8910006ef32d8910006ec32d8910024fe71d8910024fc71d8910006f631d8910006f531d891002cfe70d891002cfc70d891006d7e75989100057d75989100067f65989100067c6598910065be7498910005bd7498910006bf6498910006bc6498910006ef62989100057f755
  | 6 => 0xb4150210007b9415021002eef62c821002eec62c82100057f754821007d7c7548210005df734821004ddc734821002eef624821002eec624821002df576c4210026f576c421002ef763c4210296f563c42102977753c42102977553c421002ef762c4210006f562c421002ff260c421001cfe76d951006e7e65d9510014fe74d9510004fd74d9510014fc74d951006e7f54d95100067e54d951006e7c54d9510004ff73d951000cfe73d9510004fd73d951000cfc73d951006e7f53d95100067e53d95100067d53d951006e7c53d9510054fe72d9510004fd72d951006e7f52d951006e7c52d9510024fe71d951006cfd71d9510024fc71d951006e7f51d951002cfe70d9510024fd70d951002cfc70d951006e7f50d951006d7e76d951001c7e76d95100067e64d95100067c64d95100057f73d95100057d73d95100067f63d95100067e63d95100067d63d95100067c63d95100077631d95100077531d951028f7b10d951028f7810d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100047f73d95100067e73d95100067d73d95100047d73d95100067c73d95100067f43d95100067e43d95100067d43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100067c42d95100067f32d95100067e32d95100067d32d95100067c32d95100067f71d951028e7e71d95100067d71d951028e7c71d95100067f41d951028e7e41d951028e7c41d95100067f31d951028e7e31d95100067d31d951028e7c31d951028e7e21d951028e7c21d951028e7f70d951006e7e70d95100067d70d95100067f40d95100067c40d95100067f30d95100067e30d95100067d30d95100067c30d951028e7f10d951028e7c10d951006e7c6559510005bf7459510065bc745951006cff75595100067f7559510004ff7459510006bf7459510004bf7459510014fe7459510014fc7459510006bc7459510014bc7459510004ff735951000cfe7359510004fd735951000cfc735951006e7f53595100067d5359510004ff7259510054fc725951007cff7159510006f77159510094ff7059510006fb70595100057e761951006e7e76195100047e76195100067e64195100067c641951006d7f73195100057d73195100067f63195100067e63195100067d63195100067c63195100077631195100077531195102867f60195102877b1019510287781019510014fe76d91100067f65d91100067c65d9110066be64d911001cfe75d9110004fd75d911001cfc75d9110006bf54d9110066be54d9110066bc54d9110004ff73d911000cfe73d9110004fd73d911000cfc73d91100067f53d91100067d53d9110066bf43d9110006be43d9110006bd43d9110066bc43d9110054fe72d9110004fd72d9110
  | 7 => 0x9210006bf5459210076bc5459210004ff735921000cfe7359210004fd735921000cfc73592100067f53592100067d5359210076bf4359210006bd4359210004ff7259210054fc7259210076bf4259210076bf415921002cfc705921002ebe405921002ebc4059210004ff765521002cfe7655210004fd765521002cfc76552100067f655521001e7c6555210005f77155210025f4715521001cfe75d8a10004fd75d8a1002cfc75d8a10014fe74d8a10004fd74d8a1002cfc74d8a1002cff73d8a1000cfe73d8a10004fd73d8a1002cfc73d8a100067f53d8a100067d53d8a1002ef571d8a1002efa70d8a10004fd7698a1002eef6298a1002eec6298a10054ff7658a100057f7558a1007d7c7558a10005df7358a1004ddc7358a1002eec6258a10004ff7558a100067f7558a100047f7558a1001cfe7558a1001cfc7558a100067c7558a1001c7c7558a10004ff7458a10014fe7458a10014fc7458a10004ff7358a10006df7358a10004df7358a1000cfe7358a10004fd7358a1000cfc7358a10006dc7358a1000cdc7358a100067f5358a100067d5358a1002eef7258a10006ee3258a10006ed3258a1002cfc7058a1002eee2058a1002eec2058a10054ff7694a1002cfe7694a10004fd7694a1002cfc7694a100067f6594a1001e7c6594a10004ff7654a1002cfe7654a10004fd7654a1002cfc7654a1001e7e6554a100067d6554a10054ff7690a1002cfe7690a10004fd7690a1002cfc7690a10004ff7650a1002cfe7650a10004fd7650a1002cfc7650a100057f7550a1007d7c7550a10016be6450a10006bd6450a10005f77150a10025f47150a1001cff765461002cfc765461001e7e65546100067d6554610005bf7454610075bc7454610005fb705461002df87054610014ff765061002cfc76506100057f755061007d7c7550610016be6450610006bd6450610005fb705061002df8705061007d7e75c86100057d75c8610075be74c8610005bd74c8610056ee62c8610006ed62c861002dfa70c8610005f970c8610054ff7648610056ee6248610006ed6248610005fb704861002df87048610044ff765421002e7f655421002e7c655421002df9769021002ef97690210024f9769021002f7a759021002f797590210016fa649021002fba649021002fb9649021002ef864902102af7b53902102af795390210025fa719021002ff2719021002ff1719021002df87190210257ba4190210257b8419021003cff765021002ebf645021002ebc645021002fb84050210005fb765021003efb765021002fbb745021002fbb6450210016fa6450210016f8645021002fb864502102a7bb5450210077b8545021029f7b535021029f795350210077bb435021029fb94350210077bb4250210007b94250210025fa7150210025f87150210077b
  | 8 => 0x24fc7158b10026f63158b10006f53158b10026ee2158b10026ec2158b10054ff7694b10024fe7694b10004fd7694b10024fc7694b1001e7e6594b100067d6594b10025f67194b10005f57194b10004ff7654b10024fe7654b10004fd7654b10024fc7654b102ce7f6554b1001e7c6554b10054ff7690b10024fe7690b10004fd7690b10024fc7690b10056ee6290b10006ed6290b10025f67190b10005f57190b10004ff7650b10024fe7650b10004fd7650b10024fc7650b100057f7550b100957c7550b102c6bf6450b10016bc6450b10056ee6250b10006ed6250b10025f77648710006f776487102bdf773487102bdf57348710026f763487102b6f563487102b77753487102b7755348710027e77248710027e76248710056f66248710026f46248710027e46248710007e64248710007e5424871002df4704871006cfd769431028e7f659431001e7c659431008dbe7494310005bd749431001cff7654310024fc765431001e7e65543100067d6554310005f77154310025f47154310064fd76903100957e75903100057d7590310256bf6490310016bc6490310014ff7650310024fc7650310016be6450310006bd6450310005f77150310025f47150310056ee62c8310006ed62c8310025f671c8310005f571c8310007e521c831002df47188310054ff76483100057f75483100957c7548310005df7348310085dc7348310056ee6248310006ed6248310005f77148310025f47148310007e521483100957e75083100057d750831008dbe7408310005bd7408310085de7308310005dd7308310025f67108310005f57108310007e9200831007cfd75d9610014fe74d961002ebe74d9610014be74d9610004fd74d961002ebd74d9610004bd74d961002cfc74d961007e7f54d961002cff73d961000cfe73d9610004fd73d961002cfc73d961007e7f53d96100067d53d9610054fe72d9610004fd72d961007e7c52d961002ef571d961028e7e51d961028e7c51d961002efa70d961002e7f50d961001cff765961002e7c655961002e7f7559610004ff7459610014fe7459610014fc74596100067e545961007e7c5459610004ff735961000cfe7359610004fd735961000cfc735961007e7f53596100067d5359610004ff7259610054fc725961007e7f525961007e7f515961002cfc705961002e7e505961002e7c505961001cfe75d921002e7e75d921001c7e75d9210004fd75d921002e7d75d92100047d75d921002cfc75d9210074fd74d921002cff73d921000cfe73d9210004fd73d921002cfc73d92100067f53d92100067d53d9210054fe72d9210004fd72d921002ef571d9210256be41d9210256bc41d921002efa70d921002ebf40d9210014ff765921002ebc6459210004ff755921001cfe755921001cfc755921002ebf745
  | 9 => 0x44058420006f7305842002ef63058420006f5305842002ef43058420056f72058420056e7205842002ef62058420056f5205842002ef42058420024ff769442002cfe7694420004fd769442001e7e65944200067d65944201d6be6494420006bd64944201cede6394420006dd6394420026f66194420006f56194420004ff7654420004fd765442002cfc765442001e7e65544200067d6554420005bf74544200a5bc74544201c6be6454420006bd64544201bede6354420006dd6354420026f66154420006f56154420024ff769042002cfe7690420004fd76904201b67e65904200067d6590420016be6490420006bd64904201aede6390420006dd6390420026f66190420006f56190420004ff7650420004fd765042002cfc76504200057f75504200ad7c75504201a67e65504200067d6550420016be6450420006bd645042019ede6350420006dd6350420026f66150420006f561504200dcff765402001e7e65540200067d6554020126be6454020006bd645402011ede6354020006dd6354020006f66154020006f561540200d4ff76500201067e65500200067d6550020016be6450020006bd64500200fede6350020006dd6350020006f66150020006f5615002002def7648020006ef7648020004ef76480200076f75480200076c754802002f6e654802002f6d654802002fae644802002fad6448020007cf73480202d7cc734802002eef634802002fce63480202d6ed634802002fcd6348020006cd63480202d76f53480202d76d534802002fe66148020006ed614802002fe56148020006e5614802002def7048020057eb704802002eee604802002fea604802002fea5048020007e9504802002fea4048020007e9404802002fea30480202d7e930480200267f7559710004ff7459710006bf7459710004bf7459710014fe7459710014fc7459710006bc7459710014bc74597100967f5459710004ff735971000cfe7359710004fd735971000cfc73597100967f53597100067d5359710004ff7259710054fc72597100967c5259710024fc71597100267e51597100267c51597100967f5059710004ff75593100067f75593100047f755931001cfe755931001cfc75593100067c755931001c7c7559310026bf7459310004ff735931000cfe7359310004fd735931000cfc73593100067f53593100067d5359310004ff7259310054fc7259310024fc7159310026be4159310026bc415931008ebf4059310026fa1059310026f91059310004ff7655310024fe7655310004fd7655310024fc765531001e7e65553100067d6555310004ff7558b1001cfe7558b1001cfc7558b10004ff7458b10014fe7458b10014fc7458b10004ff7358b1000cfe7358b10004fd7358b1000cfc7358b100067f5358b100067d5358b10026ef7258b10
  | 10 => 0x8c20056dd5258c20056dc5258c20056df4258c20056de4258c20056dd4258c20056dc4258c20006df7158c20006de7158c20006dd7158c20006dc7158c20006df5158c20006dc5158c20006df4158c20006dc4158c20056df2158c20056de2158c20056dd2158c20056dc2158c2009edf7058c2002ede7058c2009edd7058c2002edc7058c20006df5058c2002ede5058c2002edc5058c20006df4058c2002ede4058c2002edc4058c20056df2058c20056cf2058c2002ede2058c20056da2058c20056dd2058c20056d92058c2002edc2058c2002ede1058c2002edc1058c20026f77598420026f67598420026f57598420026f47598420026f77498420026f67498420026f57498420026f47498420006f75498420006f65498420006f55498420006f45498420026f77398420026f67398420026f57398420026f47398420006f75398420006775398420006f65398420006f55398420006755398420006f45398420006f74398420006f64398420006f54398420006f44398420026f77298420026f67298420026f57298420026f47298420056f75298420056f65298420056f55298420056f45298420056f74298420056f64298420056f54298420056f44298420056f73298420056f63298420056f53298420056f4329842002ef6709842002ef47098420006f7509842002ef6509842002ef45098420006f7409842002ef6409842002ef44098420006f7309842002ef63098420006f5309842002ef43098420056f7209842002ef62098420056f5209842002ef42098420004ff755842001cfe755842001cfc7558420004ff7458420014fe7458420014fc7458420004ff735842000cfe7358420004fd735842000cfc73584200067f53584200067d535842002ef77158420006f75158420006f45158420006f74158420006f44158420006f73158420006f63158420006f53158420006f43158420056f72158420056f42158420024ff7058420056ef205842002ef6105842002ef41058420006f77558420006f67558420006f57558420006f47558420006f77458420006f67458420006f57458420006f47458420006f75458420006f65458420006f55458420006f45458420006f77358420006f67358420006f57358420006f47358420006f75358420006775358420006f65358420006f55358420006755358420006f45358420006f74358420006f64358420006f54358420006f44358420056f77258420056f67258420056f47258420056f75258420056f65258420056f55258420056f45258420056f74258420056f64258420056f54258420056f44258420056f73258420056f63258420056f53258420056f4325842002ef6705842002ef47058420006f7505842002ef6505842002ef45058420006f7405842002ef6405842002ef
  | 11 => 0x67d74594200067c74594200067f73594200047f73594200067e73594200067d73594200047d73594200067c73594200067f43594200067e43594200067d43594200067c43594200567f72594200567e72594200567d72594200567c72594200567f42594200567e42594200567d42594200567c42594200567f32594200567e32594200567d32594200567c32594200067f71594200067e71594200067d71594200067c71594200067f41594200067c41594200067f31594200067e31594200067d31594200067c31594200567f21594200567e21594200567d21594200567c21594200ae7f705942002e7e705942002e7c70594200067f405942002e7e405942002e7c40594200067f305942002e7e30594200067d305942002e7c30594200567f205942002e7e20594200567d205942002e7c205942002e7e105942002e7c1059420004ff755902001cfe755902001cfc755902002cff745902002ebf7459020006bf54590200a6be54590200a6bc5459020004ff735902000cfe7359020004fd735902000cfc73590200067f53590200067d53590200a6bf4359020006be4359020006bd43590200a6bc4359020054ff7259020054fe7259020054fd7259020054fc7259020056be4259020056bc4259020004ff7159020024fc71590200a6bf41590200a6bc415902002cfe705902002cfc705902002ebe405902002ebc4059020006bf7559020006be7559020006bd7559020006bc7559020006bf7359020006be7359020006bd7359020006bc7359020006bf53590200063f5359020006be5359020006bd53590200063d5359020006bc5359020056bf7259020056be7259020056bd7259020056bc7259020056bf5259020056be5259020056bd5259020056bc5259020056bf3259020056be3259020056bd3259020056bc3259020006bf7159020006be7159020006bd7159020006bc7159020006bf5159020006bc5159020006bf3159020006be3159020006bd3159020006bc3159020056bf2159020056be2159020056bd2159020056bc21590200a6bf705902002ebe705902002ebc7059020006bf505902002ebe505902002ebc5059020006bf305902002ebe3059020006bd305902002ebc3059020056bf205902002ebe2059020056bd205902002ebc205902002ebe105902002ebc1059020004ff765502002cfe7655020004fd765502002cfc765502001e7e65550200067d6555020016be6455020006bd645502021ede6355020006df7558c20006de7558c200065e7558c20006dd7558c200065d7558c20006dc7558c20006df7458c20006de7458c20006dd7458c20006dc7458c20006df5458c20006de5458c20006dd5458c20006dc5458c20056df7258c20056de7258c20056dd7258c20056dc7258c20056df5258c20056de525
  | 12 => 0xe7290520005ed7290520004ff7650520004fe7650520004fc76505200057f75505200cd7c75505200067f65505201a67c6550520006df635052019edc6350520005ee76c8520056ee76c85200576e75c85200576d75c85200076f65c85200076c65c8520057ae74c8520057ad74c8520006ef64c8520006ed64c8520055ef73c8520305ed73c8520007cf63c85202ffcc63c85202ff6f53c85202ff6d53c8520026ee61c8520026ec61c852002dee70c8520056ef60c8520057eb60c85202ffea30c85202ffe930c85200cd7e75885200057d75885200067f658852017e7c65885200bdde7388520005dd7388520006df638852016edc63885202f5ed7288520006f76188520026f46188520005fa7088520005f97088520057e82088520024fc76485200067f65485201667c6548520006df6348520156dc6348520006f76148520026f46148520057e42148520005fb7048520005f87048520024ec76485200076f65485200076c6548520006ef6448520006ed64485202f5ef73485202f5ed7348520007cf63485202efcc63485202ef6f53485202ef6d5348520055ef7148520057e77148520007e76148520026ee6148520026ec6148520007e461485202efe631485202efe53148520007eb704852002dec7048520007e87048520005e87048520056ef6048520057eb60485202efea30485202efe930485200f4fe76941200067f659412001e7c65941200c5be7494120005bd7494120006df639412012edc639412001cff76541200ccfd7654120054fc76541200067f655412001e7c6554120006df635412011edc6354120005ef7254120055ec72541200ecfe76901200cd7e75901200057d75901200067f65901201167c6590120006df639012010edc6390120014ff76501200c4fd7650120054fc76501200067f65501201067c6550120006bf6450120016bc6450120006df63501200fedc6350120005ef7250120055ec72501200067f65881200de7c6588120006df63881200b6dc6388120055fa7088120056fb60881200076f65881200076c658812002def73881202e5ed7388120007cf63881202dfcc63881202df6f53881202df6d5388120005ed718812002dee708812002eef6088120057eb608812002fea30881202dfe9308812002cff755942002e7f7559420004ff7459420014fe7459420014fc74594200ae7f54594200067e54594200ae7c5459420004ff735942000cfe7359420004fd735942000cfc73594200ae7f53594200067e53594200067d53594200ae7c5359420054ff7259420054fe7259420054fd7259420054fc72594200567e52594200567c5259420004ff7159420024fc71594200ae7f51594200ae7c515942002cfe705942002cfc705942002e7e505942002e7c50594200067f74594200067e7459420
  | 13 => 0x9120006f47159120024f471591200ecff7059120006fb7059120004ff7655120004fe7655120004fd7655120004fc76551200067f655512001e7c655512021edc63551200bdde76d8d200bede76d8d2000cde76d8d200075f75d8d200075c75d8d20006df65d8d200075f65d8d200065f65d8d20006de65d8d20006dd65d8d20006dc65d8d200075c65d8d200065c65d8d20006df64d8d20006de64d8d20006dd64d8d20006dc64d8d20007cf72d8d200bfcc72d8d2030fdb70d8d200bfd870d8d2030fdb20d8d2030fd820d8d20006df75d8d200065f75d8d20006de75d8d20006dd75d8d20006dc75d8d200065c75d8d20006df74d8d20006de74d8d20006dd74d8d20006dc74d8d20006df54d8d20006de54d8d20006dd54d8d20006dc54d8d20006df72d8d2030ede72d8d200bedd72d8d2030edc72d8d20006df52d8d2030ede52d8d2030edc52d8d20006df42d8d2030ede42d8d2030edc42d8d20006df71d8d20006de71d8d20006dd71d8d20006dc71d8d20006df51d8d20006dc51d8d20006df41d8d20006dc41d8d2030edf21d8d2030edc21d8d2030edf70d8d200bede70d8d200bedd70d8d200bedc70d8d20006df50d8d20006dc50d8d20006df40d8d20006dc40d8d2030edf20d8d200bedd20d8d2030edc20d8d2001cfc76549200067f655492001e7c6554920006df63549201fedc6354920005fb7054920005f87054920057e82054920014fc76509200057f75509200cd7c75509200067f65509201e67c6550920006bf6450920016bc6450920006df63509201dedc6350920005fb7050920005f87050920057e820509200067f65d85200067c65d8520006df63d8520006dc63d852001cfe75d8520004fd75d852001cfc75d8520014fe74d8520004fd74d8520014fc74d8520004ff73d852000cfe73d8520004fd73d852000cfc73d85200067f53d85200067d53d8520006f741d8520006f441d852002cfe70d85200cd7e75985200057d75985200067f65985200067c65985200bdde7398520005dd7398520006df6398520006dc6398520006f761985200057f75585200cd7c75585200067f65585200067c6558520005bf74585200c5bc7458520005df73585200bddc7358520006df6358520006dc63585200067f65185200067c6518520006df6318520006dc6318520026f66118520006f56118520004fe7694520004fd7694520024fc76945200067f659452001e7c6594520006df63945201cedc6394520055ee7294520005ed7294520004ff7654520004fe7654520004fc76545200067f655452001e7c6554520005bf74545200c5bc7454520006df63545201bedc6354520004fe7690520004fd7690520024fc76905200067f65905201b67c6590520006bf6490520016bc6490520006df63905201aedc6390520055e
  | 14 => 0xcd7e76d952001c7e76d95200067e64d95200067c64d95200057f73d95200057d73d95200067f63d95200067e63d95200067d63d95200067c63d95200075c63d95200065c63d95200076e32d95200076d32d95200077a30d95200077930d952031f7b20d952031f7820d95200067f74d95200067e74d95200067d74d95200067c74d95200067f73d95200047f73d95200067e73d95200067d73d95200047d73d95200067c73d95200067f43d95200067e43d95200067d43d95200067c43d95200067f72d952031e7e72d95200067d72d952031e7c72d95200067f42d952031e7e42d952031e7c42d95200067f32d952031e7e32d95200067d32d952031e7c32d95200067f71d95200067e71d95200067d71d95200067c71d95200067f41d95200067c41d95200067f31d95200067e31d95200067d31d95200067c31d952031e7f21d952031e7c21d952031e7f70d95200ce7e70d95200067d70d95200067f40d95200067c40d95200067f30d95200067e30d95200067d30d95200067c30d952031e7f20d952031e7c20d95200ce7c6559520005df73595200bddc7359520006dc63595200ccff75595200067f7559520004ff7459520014fe7459520014fc7459520004ff7359520006df7359520004df735952000cfe7359520004fd735952000cfc7359520006dc735952000cdc73595200ce7f53595200067d53595200dcff7259520006ef7259520004ff7159520024fc71595200f4ff7059520006fb70595200057e76195200ce7e76195200047e76195200067e64195200067c64195200cd7f73195200057d73195200067f63195200067e63195200067d63195200067c63195200075c63195200065c63195200076e32195200076d32195203167f60195200077a30195200077930195203177b2019520317782019520014fe76d91200067f65d91200067c65d91200c6be64d9120006dc63d912001cfe75d9120004fd75d912001cfc75d9120004ff73d912000cfe73d9120004fd73d912000cfc73d91200067f53d91200067d53d9120054fe72d91200c4fd72d9120054fc72d91200c6bf42d9120024fe71d9120004fd71d91200c6bc41d9120054fd70d91200c6bf40d91200057f75591200cd7c75591200067f65591200067c65591200c6bc6459120005df73591200bddc7359120006dc6359120005f77159120005f47159120004ff75591200067f75591200047f755912001cfe755912001cfc75591200067c755912001c7c75591200c4ff7459120006bf7459120004ff7359120006df7359120004df735912000cfe7359120004fd735912000cfc7359120006dc735912000cdc73591200067f53591200067d53591200c6bf4359120006bd43591200d4ff7259120006ef7259120004ff7159120006f77159120004f77159120024fc715
  | 15 => 0xe75d9220004fd75d922002e7d75d92200047d75d922002cfc75d92200d4fd74d922002cff73d922000cfe73d9220004fd73d922002cfc73d92200067f53d92200067d53d922002eed72d9220024fe71d9220004fd71d92200d6bc41d922002efa70d922002ebf40d9220014ff765922002ebc6459220004ff755922001cfe755922001cfc755922002ebf7459220006bf54592200d6bc5459220004ff735922000cfe7359220004fd735922000cfc73592200067f53592200067d53592200d6bf4359220006bd43592200d6bf4259220004ff7159220024fc71592200d6bf415922002cfc705922002ebe405922002ebc4059220004ff765522002cfe7655220004fd765522002cfc76552200067f655522001e7c655522001cff7654a2002cfc7654a2001e7e6554a200067d6554a20005fb7054a2002df87054a20014ff7650a2002cfc7650a200057f7550a200dd7c7550a20016be6450a20006bd6450a20005fb7050a2002df87050a2002ef7619862002ef461986200057f75586200dd7c7558620005bf74586200d5bc745862002ef46158620004ff75586200067f75586200047f755862001cfe755862001cfc75586200067c755862001c7c7558620004ff7458620006bf7458620004bf7458620014fe7458620014fc7458620006bc7458620014bc7458620004ff735862000cfe7358620004fd735862000cfc73586200067f53586200067d5358620006f63158620006f5315862002cfc705862002ef6105862002ef41058620024ff769462002cfe7694620004fd76946200067f659462001e7c6594620004ff7654620004fd765462002cfc765462001e7e65546200067d6554620005bf74546200d5bc7454620024ff769062002cfe7690620004fd7690620006bf6490620016bc6490620004ff7650620004fd765062002cfc76506200057f75506200dd7c7550620016be6450620006bd64506200dd7e75886200057d75886200b5de7388620005dd7388620026f66188620006f5618862002dfa7088620005f97088620024ff7648620026f66148620006f56148620005fb704862002df870486200acff765422002e7f655422002e7c65542200a4ff765022002ebf645022002ebc645022002ded76c8220056ed76c822002eef63c8220326ed63c82203276f53c82203276d53c8220006ed61c822002fea60c822001cfe76d95200ce7e65d9520006dc63d9520014fe74d9520004fd74d9520014fc74d95200ce7f54d95200067e54d95200ce7c54d9520004ff73d952000cfe73d9520004fd73d952000cfc73d95200ce7f53d95200067e53d95200067d53d95200ce7c53d9520054fe72d95200ccfd72d9520054fc72d95200ce7f52d9520024fe71d9520004fd71d95200ce7f51d95200ce7c51d9520054fd70d95200ce7f50d9520
  | 16 => 0x972000cfe7359720004fd735972000cfc73597200f67f53597200067d5359720054fc72597200567e52597200567c5259720004ff7159720024fc71597200f67c51597200f67f5059720004ff75593200067f75593200047f755932001cfe755932001cfc75593200067c755932001c7c7559320056bf74593200eebe5459320004ff735932000cfe7359320004fd735932000cfc73593200067f53593200067d53593200eebf4359320006bd4359320054fc7259320056be4259320056bc4259320004ff7159320024fc71593200eebc4159320056ef21593200eebf4059320004ff7655320054fe7655320004fd7655320054fc765532001e7e65553200067d6555320016be6455320006bd6455320004ff755872001cfe755872001cfc7558720004ff7458720014fe7458720014fc7458720004ff735872000cfe7358720004fd735872000cfc73587200067f53587200067d5358720056f77158720006f63158720006f53158720056f72158720056f42158720024ff7694720054fe7694720004fd769472001e7e65947200067d6594720055ee7294720005ed7294720004ff7654720004fd7654720054fc765472033e7f655472001e7c6554720005bf74547200edbc7454720024ff7690720054fe7690720004fd7690720016be6490720006bd6490720055ee7290720005ed7290720004ff7650720004fd7650720054fc76507200057f75507200f57c7550720055ef7648720006ef7648720056ef6448720006ed6448720335ef7348720335ed734872032f6f534872032f6d5348720057e77148720057e76148720026ee6148720026ec6148720057e4614872032fe6314872032fe5314872002dec70487200ccfd769432031e7f659432001e7c65943200edbe7494320005bd749432001cff7654320054fc765432001e7e65543200067d6554320005ef7254320055ec72543200c4fd76903200f57e75903200057d7590320014ff7650320054fc7650320016be6450320006bd6450320005ef7250320055ec72503200dcfd75d9620014fe74d962002ebe74d9620014be74d9620004fd74d962002ebd74d9620004bd74d962002cfc74d96200de7f54d962002cff73d962000cfe73d9620004fd73d962002cfc73d96200de7f53d96200067d53d962002eed72d962031e7e52d962031e7c52d9620024fe71d9620004fd71d96200de7c51d962002efa70d962002e7f50d962001cff765962002e7c655962002e7f7559620004ff7459620014fe7459620014fc74596200067e54596200de7c5459620004ff735962000cfe7359620004fd735962000cfc73596200de7f53596200067d53596200de7f5259620004ff7159620024fc71596200de7f515962002cfc705962002e7e505962002e7c505962001cfe75d922002e7e75d922001c7
  | 17 => 0x73f7550940105be7550940105bc75509400073c75509401053c7550940006bf6550940006bd6550940375bf7350940375bd735094036ebf635094036ebd635094036f3f535094036f3d5350940015bf7250940017af7250940007af6250940056be6250940056bc6250940007ac6250940005bf71509402c6bc6150940007bb705094002dbc7050940007b87050940016bf6050940017bb605094001cfe75d8540004fd75d854001cfc75d8540004ff73d854000cfe73d8540004fd73d854000cfc73d85400067f53d85400067d53d8540054fe72d8540004fd72d8540006f751d8540006f451d8540076f641d8540076f541d8540006f631d8540006f531d8540006f76198540065f970985400057f75585401057c755854008dfb70585401057e75185400057d75185400fdde7318540005dd7318540005ee7218540005ed7218540026f66118540006f56118540004fe7694540004fd7694540024fc76945400067f659454001e7c6594540015be7494540005bd74945401d73c5494540005fa7094540005f97094540004ff7654540004fe7654540004fc765454001e7e65545400067d6554540005bf7454540015bc74545401073f5454540024bc76505400073f7550540105be7550540105bc75505400073c75505401053c7550540365bf7350540365bd735054035f3f535054035f3d5350540005bf7250540015bf7150540017b77150540007b76150540026be6150540026bc6150540007b46150540007bb705054002dbc7050540007b87050540016bf6050540017bb6050540004fe76c8540004fd76c8540054fc76c85401057e75c85400057d75c8540015be74c8540005bd74c8540056ee62c8540007ad42c8540006f761c8540026f461c8540004fe7688540004fd7688540024fc76885401057e75885400057d7588540015be7488540005bd74885400fdde7388540005dd7388540005fa7088540005f97088540004ff7648540004fe7648540004fc7648540015be7448540005bd7448540007ad4248540004fe7608540004fd7608540024fc7608540015be7408540005bd7408540006f76108540026f46108540005fa7008540005f97008540354fe769414001e7e65941400067d6594140015be7494140105bd74941401073f54941401077b509414001cff7654140014fe7654140124fd7654140014fc76541400067f655414001e7c6554140005bf7454140015bc74541401273c5454140105be759014002f3e75901401053e759014002f3d759014002dbc759014002dbf739014034dbd73901403473f53901403473d5390140005bd7290140005bd7190140256bc619014002dbe709014002fba709014002ebf6090140017bb60901400567f7559720004ff7459720014fe7459720014fc74597200f67f5459720004ff735
  | 18 => 0xd65906401b6bc6590640386bf6390640386bd63906403873f53906403873d5390640006bd6290640015be7190640017b67190640257b66190640256bd6190640007b56190640257ba7090640005bd7090640257b97090640016be6090640017ba6090640054ff76c864002cfe76c8640004fd76c86401157e75c86400057d75c86401967e65c86400067d65c8640015be74c8640005bd74c8640056ee62c8640006ed62c8640024ff768864002cfe7688640004fd76886401157e75886400057d758864017e7e65886400067d658864010dde7388640005dd7388640026f66188640006f5618864002dfa7088640005f97088640004ff7648640004fd764864002cfc76486401667e65486400067d6548640005bf7448640015bc7448640056ee6248640006ed6248640026f66148640006f56148640024ff760864002cfe7608640004fd760864014e7e65086400067d650864002dfa7008640005f9700864037cff765424001e7e65542401267d6554240127bb405424001cfe76d95401067e65d9540015be74d95401073f54d954002cff74d9540014fe74d9540134fd74d9540106bd74d9540104bd74d9540014fc74d95401367f54d9540106bf54d95401063f54d95401367d54d9540136bc54d9540004ff73d954000cfe73d9540004fd73d954000cfc73d95401067f53d95400067d53d9540054fe72d9540004fd72d95401067c52d9540136bf42d9540024fe71d9540004fd71d95401067c51d9540014fd70d95401067f50d95401067c65595401273c5459540005f77159540005f4715954037dfb7059540134ff75595400067f7559540124ff7459540006bf7459540106bf54595401267e54595401267c5459540126bc5459540004ff735954000cfe7359540004fd735954000cfc73595401067f53595400067d5359540004ff7259540054fc72595401067f5259540126bf4259540004ff7159540006f77159540004f77159540024fc7159540006f47159540024f471595401067f515954037cff7059540006fb70595401067c505954001cfe75d8940004fd75d894001cfc75d8940004ff73d894000cfe73d8940004fd73d894000cfc73d89400067f53d89400067d53d89400d6bf43d8940006bd43d89400d6ee42d89400d6ed42d8940024fe71d8940004fd71d8940006ef62989400c5f970989400057f75589401057c7558940005df73589400fddc7358940005f77158940005f471589400edfb70589401057e75189400057d7518940056ee6218940006ed6218940004fe7694940004fd7694940054fc76949400067f659494001e7c6594940015be7494940005bd74949402173c5494940004ff7654940004fe7654940004fc765494001e7e65549400067d6554940005bf7454940015bc74549401073f5454940054bc7650940
  | 19 => 0x964000cfe7359640004fd735964000cfc73596401167f53596400067e53596400067d53596401167c5359640004ff7259640054fc72596401167f52596401167c5259640004ff7159640024fc71596401167f51596401167c515964002cfe705964002cfc705964002e7e505964002e7c505964002d7f76596401167f765964001c7f76596400057f73596400057d735964002e7f63596400067e63596400067d635964002e7c635964002e7f625964002e7c625964002e7f615964002e7c61596401273c415964002f3f40596401277b405964002f7840596401267f74596401267e74596401267d74596401267c74596400067f73596400047f73596400067e73596400067d73596400047d73596400067c73596401267f43596401267e43596401267d43596401267c43596400067f72596400067e72596400067d72596400067c72596401267f42596401267e42596401267d42596401267c42596400067f32596400067e32596400067d32596400067c32596400067f71596400067e71596400067d71596400067c71596401267f41596401267e41596401267d41596401267c41596400067f31596400067e31596400067d31596400067c31596401167f705964002e7e705964002e7c70596401267f405964002e7e40596401267d405964002e7c40596400067f305964002e7e30596400067d305964002e7c305964002e7e205964002e7c205964002e7e105964002e7c10596400067e6598a400067d6598a4002eef6298a4002eec6298a400067e6558a400067d6558a4002eec6258a40004ff7558a4001cfe7558a4001cfc7558a40004ff7358a4000cfe7358a40004fd7358a4000cfc7358a400067f5358a400067d5358a400c6ee4258a400c6ed4258a40006ee3258a40006ed3258a40004ff7158a40024fc7158a400c6bc4158a4002cfc7058a400c6bf4058a4002eee2058a4002eec2058a40054ff7694a4002cfe7694a40004fd7694a4001e7e6594a400067d6594a40004ff7654a40004fd7654a4002cfc7654a4001e7e6554a400067d6554a400067e65986400067d659864002ef7619864002ef461986400067e65586400067d655864002ef46158640004ff755864001cfe755864001cfc7558640004ff735864000cfe7358640004fd735864000cfc73586400067f53586400067d5358640004ff7258640054fc7258640066f64158640066f54158640256bc4158640006f63158640006f5315864002cfc7058640066bf405864002ef6105864002ef41058640024ff769464002cfe7694640004fd769464001e7e65946400067d659464002dfa7094640005f97094640004ff7654640004fd765464002cfc765464001e7e65546400067d6554640005bf7454640015bc74546401b6be65906400073e65906401b63e65906400073
  | 20 => 0x3b57f73549503b57d73549503ae7f63549503ae7d635495001d7f725495001f6f72549500076f62549500567e62549500567c62549500076c62549500057f71549502ce7c61549500077b705495002d7c705495000778705495001e7f605495001f7b6054950004fe7690950004fd7690950054fc769095001d7e75909500057d7590950004ff7650950004fe7650950004fc76509500057f755095001d7c7550950016be64509501273e5450950014fe74d8550004fd74d8550014fc74d8550004ff73d855000cfe73d8550004fd73d855000cfc73d855007e7f53d85500067d53d8550054fe72d8550004fd72d855007ef651d855007ef551d8550006f741d8550006f441d8550006f7619855006df97098550005bf7458550125bc7458550095fb705855011dde7318550005dd7318550026f66118550006f561185500247c76545500073f74545501257e74545501257c74545500073c74545501253c74545500067f64545503a57f73545503a57d735455039e7f635455039e7d63545500057f725455033e7c625455001d7f715455001f7771545500077761545500267e61545500267c61545500077461545500077b705455002d7c705455000778705455001e7f605455001f7b6054550004fe7690550004fd7690550024fc769055001d7e75905500057d7590550006bf6490550016bc64905501273c5490550004ff7650550004fe7650550004fc76505500057f755055001d7c7550550004fe76c8550004fd76c8550054fc76c855001d7e75c85500057d75c8550125be74c8550005bd74c8550004fe7688550004fd7688550024fc768855001d7e75885500057d758855011dde7388550005dd7388550004ff7648550004fe7648550004fc764855001d7e75485500057d7548550004fe7608550004fd7608550024fc760855001d7e75085500057d7508550005fa7008550005f970085501257e749415002f3e74941501253e749415002f3d749415002d7c74941500067f649415002d7f73941503957d739415038e7f639415038e7d63941500057d729415031e7c62941500057d719415028e7c619415002d7e709415002f7a709415002e7f609415001f7b6094150124fd75d964002ebd74d964002cff73d964000cfe73d9640004fd73d964002cfc73d96401167f53d96400067d53d9640054fe72d9640004fd72d9640024fe71d9640004fd71d964002cfe70d964002efa70d96401247d769964037e7d64996401157f73996400057d739964002e7f63996400067e63996400067d639964002e7c639964002e7f629964002e7c629964002e7f619964002e7c619964037f3c419964002e7e609964002f3f409964037f7b409964002f78409964001cff765964002e7c655964002e7f75596401267f54596401267d5459640004ff735
  | 21 => 0xd6450a500073d5450a50006be6498650006bd649865002ef7619865002ef46198650006be6458650006bd645865002ef46158650004ff7458650014fe7458650014fc745865006e7f54586500067d5458650004ff735865000cfe7358650004fd735865000cfc735865006e7f53586500067d5358650004ff7258650054fc72586500067e525865006e7c525865006ef6515865006ef5515865028e7c5158650006f63158650006f5315865002cfc705865006e7f505865002ef6105865002ef410586500057d74946501d67e64946500073e64946501d63e64946500073d64946501d67c649465028d7f73946503cd7d73946503c67f63946503c67d639465031d7e72946500067d629465001d7e719465001f76719465028f76619465028e7d619465000775619465028f7a70946500057d709465028f79709465001e7e609465001f7a6094650024ff769065002cfe7690650004fd769065028d7f759065001d7c7590650016be6490650006bd64906501b73f5490650004ff7650650004fd765065002cfc76506500057f755065001d7c7550650016be6450650006bd6450650054ff76c865002cfe76c8650004fd76c865001d7e75c86500057d75c8650135be74c8650005bd74c865018ebe64c8650006bd64c8650056ee62c8650006ed62c8650024ff768865002cfe7688650004fd768865001d7e75886500057d7588650176be6488650006bd648865012dde7388650005dd7388650026f66188650006f56188650004ff7648650004fd764865002cfc76486500057f754865001d7c754865015ebe6448650006bd6448650056ee6248650006ed6248650026f66148650006f56148650024ff760865002cfe7608650004fd760865028d7f750865001d7c7508650146be6408650006bd640865002dfa7008650005f97008650014fe76d915001d7e75d9150126be64d91501273e54d9150014fc75d91501267e54d9150126be54d91501263e54d9150116bd54d91501267c54d9150004ff73d915000cfe73d9150004fd73d915000cfc73d91501167f53d91500067d53d9150054fe72d9150004fd72d91501167f52d9150024fe71d9150004fd71d91501167f51d9150126bc41d915001cfd70d91501167c50d9150126bf40d9150126bc64591501273c5459150005f77159150005f471591503bdfb7059150014fe74d8950004fd74d8950014fc74d8950004ff73d895000cfe73d8950004fd73d895000cfc73d89500de7f53d89500067d53d89500deee52d89500deed52d8950006ef32d8950006ec32d8950024fe71d8950004fd71d8950006ef62989500cdf97098950005df735895011ddc73589500f5fb7058950125be7418950005bd7418950056ee6218950006ed62189500547c76549501257e74549501257c74549500067f6454950
  | 22 => 0x9250004ff7259250054fc7259250136bf4259250136bc4259250004ff7159250024fc7159250136bf4159250136bc415925002cfe705925002cfc705925002ebe405925002ebc405925002dbf7659250136bf7659250014bf76592501073e75592500073d755925002ebf6359250006be6359250006bd635925002ebc63592501073f53592500073d535925002ebf625925002ebc62592501073c525925002ebf615925002ebc61592501073c515925002f3f5059250107bb505925002fb85059250106be7559250106bd7559250136bc7559250006bf7359250006be7359250006bd7359250006bc7359250106bf53592501063f5359250106be5359250106bd53592500063d5359250106bc5359250006bf7259250006be7259250006bd7259250006bc7259250106bf5259250106be5259250106bd5259250106bc5259250006bf3259250006be3259250006bd3259250006bc3259250006bf7159250006be7159250006bd7159250006bc7159250106bf5159250106be5159250106bd5159250106bc5159250006bf3159250006be3159250006bd3159250006bc3159250136bf705925002ebe705925002ebc7059250106bf505925002ebe5059250106bd505925002ebc5059250006bf305925002ebe3059250006bd305925002ebc305925002ebe205925002ebc205925002ebe105925002ebc10592501357f76552500167f76552500147f765525001d7f745525001f3f74552500167e64552501373e64552500163e64552500073d64552500167c64552503ed7f73552503ed7d73552503e67f63552503e67d635525031d7c72552501373f425525028d7c71552500057f70552500077b705525000778705525001e7e605525001f7a6055250006be6498a50006bd6498a5002eef6298a5002eec6298a50006be6458a50006bd6458a5002eec6258a50004ff7458a50014fe7458a50014fc7458a500ce7f5458a500067d5458a50004ff7358a5000cfe7358a50004fd7358a5000cfc7358a500ce7f5358a500067d5358a500ceee5258a500ceed5258a5031e7c5258a50006ee3258a50006ed3258a50004ff7158a50024fc7158a500ce7c5158a5002cfc7058a500ce7f5058a5002eee2058a5002eec2058a500057d7494a502167e6494a500073e6494a502163e6494a500073d6494a502167c6494a5031d7f7394a503dd7d7394a503d67f6394a503d67d6394a5001d7e7294a5001f6e7294a5031f6e6294a5031e7d6294a500076d6294a5028d7e7194a5031f7a7094a500057d7094a5031f797094a5001e7e6094a5001f7a6094a50054ff7690a5002cfe7690a50004fd7690a5031d7f7590a5001d7c7590a50016be6490a50006bd6490a50004ff7650a50004fd7650a5002cfc7650a500057f7550a5001d7c7550a50016be6450a50006b
  | 23 => 0x15dbe7418121005bd7418121155de7318121005dd7318121006f9601812101cfe751812102e7e751812101c7e7518121004fd751812102e7d75181210047d751812102cfc7518121014fe741812102ebe7418121014be7418121004fd741812102ebd7418121004bd741812102cfc741812102cff731812100cfe731812102ede731812100cde7318121004fd731812102edd7318121004dd731812102cfc73181210067f53181210067d5318121024ff75594210267f7559421004ff7459421014fe7459421014fc745942114e7f5459421004ff735942100cfe7359421004fd735942100cfc735942114e7f53594210067d5359421054fe7259421054fc72594210567e52594210567c5259421024fe7159421024fc71594210267e51594210267c5159421004ff705942102cfc705942114e7f5059421004ff75590210067f75590210047f755902101cfe755902101cfc75590210067c755902101c7c7559021024ff7459021026bf7459021146be5459021004ff735902100cfe7359021004fd735902100cfc73590210067f53590210067d5359021146bf4359021006bd4359021054fe7259021054fc7259021056be4259021056bc4259021024fe7159021024fc7159021026be4159021026bc4159021026ef2159021026ed2159021004ff705902102cfc7059021146bf4059021004ff7655021024fe7655021004fd7655021024fc765502101e7e65550210067d6555021016be6455021006bd645502101cfe7598021004fd759802102cfc7598021014fe7498021004fd749802102cfc749802102cff739802100cfe7398021004fd739802102cfc73980210067f53980210067d539802102cfe709802102efa709802102efa3098021006f93098021056fb209802102ef82098021026fb109802102ef81098021004ff75580210067f75580210047f755802101cfe755802101cfc75580210067c755802101c7c7558021004ff7458021014fe7458021014fc7458021004ff735802100cfe7358021004fd735802100cfc73580210067f53580210067d5358021026ef2158021026f62158021026ed2158021056f52158021026fb7058021006fa3058021006f93058021056fb2058021056f82058021026fb1058021026f810580211373e75992501373d7599250126bd659925002ebf6399250006be6399250006bd639925002ebc63992503bf3f53992500073d539925002ebf629925002ebc62992503bf3c529925002ebf619925002ebc61992503bf3c519925002ebe609925002f3f50992503bfbb509925002fb85099250014ff765925002ebc6459250136be5459250106bd5459250004ff735925000cfe7359250004fd735925000cfc73592501067f53592500067d5359250136bf4359250006be4359250006bd4359250136bc435
  | 24 => 0xe7359521004fd735952100cfc73595211667f53595210067d535952117cff7259521006ef725952133e7e525952133e7c5259521194ff7159521006f771595212ce7e51595212ce7c5159521004ff705952102cfc70595211667f5059521014fe76d912115ebe64d912101cfe75d9121004fd75d912101cfc75d9121006bf54d912115ebc54d9121004ff73d912100cfe73d9121004fd73d912100cfc73d91210067f53d91210067d53d912115ebf43d9121006bd43d9121024fd72d912115ebf42d9121054fd71d912115ebf41d912102cfe70d9121004fd70d912115ebc40d91210057f75591211657c755912115ebc6459121004ff75591210067f75591210047f755912101cfe755912101cfc75591210067c755912101c7c755912115cff7459121006bf7459121004ff735912100cfe7359121004fd735912100cfc73591210067f53591210067d5359121174ff7259121006ef725912118cff7159121006f771591212c6be41591212c6bc4159121004ff705912102cfc705912115ebf4059121004ff7655121004fe7655121004fd7655121004fc765512101e7e65551210067d6555121005f77155121025f47155121024fc76549210067f655492101e7c6554921005f77154921025f47154921057e42154921005ee7690921056ee769092115ded7490921016ee6490921016ec64909213ff6f53909213ff6d5390921025ee7190921025ec7190921056ef6190921057e761909213ffe631909213ffe53190921005ed7090921024fc76509210057f75509211657c7550921006bf6450921016bc6450921005f77150921025f47150921025ec7650921016ec7650921024ec76509210076f75509210076c7550921055ef7450921057af7450921007af6450921016ee6450921016ec645092115fac645092115fae5450921007ad54509213f76f53509213f76d535092115faf43509213f7ad4350921007e77150921025ee7150921025ec7150921007e47150921056ef6150921057e761509212c7ae41509212c7ac41509213f7e631509213f7e53150921005ef705092115faf405092101cff7654521164fd7654521054fc76545210067f655452101e7c6554521005bf745452115dbc7454521005ef7254521055ec7254521027e42154521014ff765052115cfd7650521054fc76505210057f75505211657c7550521006bf6450521016bc6450521005ef7250521055ec725052101cfe75d8121004fd75d812101cfc75d8121014fe74d8121004fd74d8121014fc74d8121004ff73d812100cfe73d8121004fd73d812100cfc73d81210067f53d81210067d53d8121006f631d8121006f531d8121006fb60981210057f75581211657c7558121005bf745812115dbc7458121005df7358121155dc73581211657e75181210057d7518121
  | 25 => 0x922100cfe7359221004fd735922100cfc73592210067f53592210067d5359221176bf4259221024fc7159221026be4159221026bc4159221026ef2159221026ed2159221004ff705922102cfc7059221176bf4059221004ff7655221024fe7655221004fd7655221024fc765522101e7e65552210067d655522121ede6355221005f77155221025f47155221006df7558e21006de7558e210065e7558e21006dd7558e210065d7558e21006dc7558e21006df7458e21006de7458e21006dd7458e21006dc7458e21006df5458e21006de5458e21006dd5458e21006dc5458e2116edf7258e21406de7258e21006dd7258e21406dc7258e21006df5258e21406de5258e21406dc5258e21006df4258e21406de4258e21406dc4258e21026df7158e21026de7158e21026dd7158e21026dc7158e21026df5158e21026de5158e21026dd5158e21026dc5158e21026df4158e21026de4158e21026dd4158e21026dc4158e21026df2158e21026de2158e21026dd2158e21026dc2158e21006df7058e21006de7058e21006dd7058e21006dc7058e21006df5058e21006dc5058e21006df4058e21006dc4058e21406df2058e21406dc2058e21026df1058e21026d71058e21026de1058e21026dd1058e21026dc1058e2101cff7654a21024fc7654a2101e7e6554a210067d6554a211fede6354a21006dd6354a21005f77154a21025f47154a21014ff7650a21024fc7650a210057f7550a2117d7c7550a211e67e6550a210067d6550a21016be6450a21006bd6450a211dede6350a21006dd6350a21005f77150a21025f47150a2101cfe7598221004fd759822102cfc7598221014fe7498221004fd749822102cfc749822102cff739822100cfe7398221004fd739822102cfc73982210067f53982210067d5398221024fe7198221024f6719822102efa709822102ef71098221026fb109822102ef81098221004ff755822101cfe755822101cfc7558221004ff7458221014fe7458221014fc7458221004ff735822100cfe7358221004fd735822100cfc73582210067f53582210067d5358221024fc7158221026f63158221006f53158221026ef2158221026ed2158221026fb7058221026fb1058221026f8105822101cfe76d95211667e65d9521014fe74d9521004fd74d9521014fc74d95210067e54d95211667c54d9521004ff73d952100cfe73d9521004fd73d952100cfc73d95211667f53d95210067d53d9521024fd72d95211667f52d9521054fd71d95211667f51d952102cfe70d9521004fd70d95211667c50d95211667c6559521005bf745952115dbc7459521164ff75595210067f7559521004ff7459521006bf7459521004bf7459521014fe7459521014fc7459521006bc7459521014bc74595211667f5459521004ff735952100cf
  | 26 => 0x16be6455321006bd6455321055ef7650b21146ef7650b210076f7550b210076c7550b210576e6550b210576d6550b21057af7450b21016ee6450b21057ae6450b21016ae6450b21057ad6450b21056ec6450b2118fae5450b21007ad5450b2140f6f5350b2140f6d5350b2118faf4350b2140fad4350b21025ee7150b21025ec7150b212c7ae4150b212c7ac4150b21005ef7050b2118faf4050b2101cff7654721054fc765472101e7e65547210067d6554721005bf745472118dbc74547211c6be6454721006bd6454721005ef7254721055ec7254721014ff7650721054fc76507210057f75507211957c75507211a67e65507210067d6550721016be6450721006bd6450721005ef7250721055ec725072101cfe7598321004fd759832102cfc7598321014fe7498321004fd749832102cfc749832102cff739832100cfe7398321004fd739832102cfc73983210067f53983210067d5398321024fe7298321024ee729832102efa709832102efa3098321006f9309832102eef2098321056fb209832102ef82098321004ff755832101cfe755832101cfc7558321004ff7458321014fe7458321014fc7458321004ff735832100cfe7358321004fd735832100cfc73583210067f53583210067d5358321024fc7258321056f62158321056f52158321056fb7058321006fa3058321006f93058321056fb2058321056f820583210267f7559621004ff7459621014fe7459621014fc745962117e7f54596210067e545962117e7c5459621004ff735962100cfe7359621004fd735962100cfc735962117e7f53596210067e53596210067d535962117e7c535962117e7f5259621024fc71596210267e51596210267c5159621004ff705962102cfc705962117e7f505962117e7c50596210067f74596210067e74596210067d74596210067c74596210067f73596210047f73596210067e73596210067d73596210047d73596210067c73596210067f43596210067e43596210067d43596210067c43596210067f725962133e7e72596210067d725962133e7c72596210067f425962133e7e425962133e7c42596210067f325962133e7e32596210067d325962133e7c32596210267f71596210267e71596210267d71596210267c71596210267f41596210267e41596210267d41596210267c41596210267f31596210267e31596210267d31596210267c31596210267f21596210267e21596210267d21596210267c21596210067f70596210067e70596210067d70596210067c70596210067f40596210067c40596210067f30596210067e30596210067d30596210067c305962133e7f205962133e7c20596210267f10596210267e10596210267d10596210267c1059621004ff755922101cfe755922101cfc7559221026bf7459221004ff735
  | 27 => 0xf401814102efa401814103ef940181410567f7559721004ff7459721014fe7459721014fc74597211967f54597210067e54597211967c5459721004ff735972100cfe7359721004fd735972100cfc73597211967f53597210067e53597210067d53597211967c5359721024fc72597210567e52597210567c52597211967f5159721004ff705972102cfc70597211967f50597211967c50597210067f74597210067e74597210067d74597210067c74597210067f73597210047f73597210067e73597210067d73597210047d73597210067c73597210067f43597210067e43597210067d43597210067c43597210567f72597210567e72597210567d72597210567c72597210567f42597210567e42597210567d42597210567c42597210567f32597210567e32597210567d32597210567c32597210067f71597212ce7e71597210067d71597212ce7c71597210067f41597212ce7e41597212ce7c41597210067f31597212ce7e31597210067d31597212ce7c31597210567f21597210567e21597210567d21597210567c21597210067f70597210067e70597210067d70597210067c70597210067f40597210067c40597210067f30597210067e30597210067d30597210067c30597210567f20597210567e20597210567d20597210567c20597212ce7f10597212ce7c1059721004ff755932101cfe755932101cfc7559321056bf7459321006bf545932118ebe545932118ebc5459321004ff735932100cfe7359321004fd735932100cfc73593210067f53593210067d535932118ebf4359321006be4359321006bd435932118ebc4359321024fc7259321056be4259321056bc425932118ebf4159321004ff705932102cfc705932118ebf405932118ebc4059321006bf7559321006be7559321006bd7559321006bc7559321006bf7359321006be7359321006bd7359321006bc7359321006bf53593210063f5359321006be5359321006bd53593210063d5359321006bc5359321056bf7259321056be7259321056bd7259321056bc7259321056bf5259321056be5259321056bd5259321056bc5259321056bf3259321056be3259321056bd3259321056bc3259321006bf71593212c6be7159321006bd71593212c6bc7159321006bf51593212c6be51593212c6bc5159321006bf31593212c6be3159321006bd31593212c6bc3159321056bf2159321056be2159321056bd2159321056bc2159321006bf7059321006be7059321006bd7059321006bc7059321006bf5059321006bc5059321006bf3059321006be3059321006bd3059321006bc3059321056bf2059321056be2059321056bd2059321056bc20593212c6bf10593212c6bc1059321004ff7655321054fe7655321004fd7655321054fc765532101e7e65553210067d6555321
  | 28 => 0x95411d67d43d95411d67c43d95410067f72d95410067e72d95410067d72d95410067c72d95411d67f42d95411d67e42d95411d67d42d95411d67c42d95410067f32d95410067e32d95410067d32d95410067c32d95411d67f71d95414367e71d95411d67d71d95414367c71d95411d67f41d95414367e41d95414367c41d95410067f31d95414367e31d95410067d31d95414367c31d95414367e21d95414367c21d95410067f70d95410067e70d95410067d70d95410067c70d95411d67f40d95411d67e40d95411d67d40d95411d67c40d95410067f30d95410067e30d95410067d30d95410067c30d95414367f10d95414367c10d95411a67c655954142df771595411d4ff75595410067f75595411c4ff7459541006bf74595411b4bf7459541004ff735954100cfe7359541004fd735954100cfc73595411a67f53595410067d5359541004ff7259541054fc725954142cff7159541006f77159541004ff705954102cfc70595411d57e76195411a67e76195411d47e76195414267f64195414263f64195411a57f73195410057d73195410067f63195410067e63195410067d63195410067c631954141e7f611954141f7741195414273e41195414273c411954141f74411954141f3f40195410067f65d89410067c65d894101cfe75d8941004fd75d894101cfc75d8941024fd74d8941004ff73d894100cfe73d8941004fd73d894100cfc73d89410067f53d89410067d53d8941176ee42d8941176ed42d8941416be41d8941416bc41d894102cfe70d8941004fd70d8941176bf40d89411a57e75989410057d75989410067f65989410067c6598941006ef629894115df571989410057f75589411a57c75589410067f65589410067c655894118df771589410067f65189410067c6518941056ee6218941006ed6218941004fe7694941004fd7694941054fc76949410067f659494101e7c6594941004ff7654941004fe7654941004fc76549410067f655494101e7c655494101cff7654541014fe76545411c4fd7654541014fc76545410067f655454101e7c6554541005bf7454541015bc74545410067f65d81410067c65d814101cfe75d8141004fd75d814101cfc75d8141024fd74d8141004ff73d814100cfe73d8141004fd73d814100cfc73d81410067f53d81410067d53d8141054fe72d8141004fd72d814108efa40d81411a57e75981410057d75981410067f65981410067c6598141006fb60981410057f75581411a57c75581410067f65581410067c65581410067f65181410067c6518141006f9601814101cfe7518141004fd751814102cfc7518141024fd741814102cff731814100cfe7318141004fd731814102cfc73181410067f53181410067d5318141054fe7218141004fd721814127ebe411814127ebc411814102eb
  | 29 => 0xcfc73596411b67f53596410067d5359641004ff7259641054fc72596411b67c52596411c6bf4259641024fe7159641024fc71596410267e51596410267c5159641004ff705964102cfc70596411b67f5059641004ff7558a4101cfe7558a4101cfc7558a41004ff7358a4100cfe7358a41004fd7358a4100cfc7358a410067f5358a410067d5358a4115ebf4358a41006bd4358a41026ef7258a4115eee4258a4115eed4258a41024fc7158a41026ee2158a41026ec2158a41004ff7058a4102cfc7058a41054ff7694a41024fe7694a41004fd7694a4101e7e6594a410067d6594a41015be7494a41005bd7494a412173c5494a41004ff7654a41004fd7654a41024fc7654a412ce7f6554a4101e7c6554a41005bf7454a41015bc7454a411b73f5454a41054bf7650a410073f7550a411b5be7550a411b5bc7550a410073c7550a411b53c7550a412c6bf6550a41006bd6550a41445bf7350a41445bd7350a412c6bf6350a4143ebd6350a4143f3f5350a4143f3d5350a41015bf7250a41017af7250a41056be6250a412c7ae6250a412c7ad6250a41056bc6250a412c5bf7150a41007b77150a412c7b47150a41016be6150a41017b66150a41005bc7050a4101cfe7598241004fd759824102cfc759824102cff739824100cfe7398241004fd739824102cfc73982410067f53982410067d5398241054fe7298241004fd7298241024fe719824102cfc719824102efa709824102efa4098241076f94098241026fb109824102ef81098241004ff75582410067f75582410047f755824101cfe755824101cfc75582410067c755824101c7c7558241006bf5458241066bc5458241004ff735824100cfe7358241004fd735824100cfc73582410067f53582410067d5358241066bf4358241006bd4358241004ff7258241054fc7258241066bf4258241006bd4258241024fc7158241026bf4158241026bd4158241026fb7058241066fa4058241066bc4058241026fb1058241026f8105824101cfe76d95411a67e65d9541024ff74d9541024fd74d95411d67f54d95411d67d54d9541004ff73d954100cfe73d9541004fd73d954100cfc73d95411a67f53d95410067e53d95410067d53d95411a67c53d9541054fe72d9541004fd72d95411a67f52d95411a67c52d9541014fd71d95411a67f51d954102cfe70d9541004fd70d95411a67f50d95411a67c50d954141d7e76d954101c7e76d95410057f73d95410057d73d95410067f63d95410067e63d95410067d63d95410067c63d95411d77741d95414373e41d95414373c41d95411d77441d95411d73f40d95414367f74d95411d67e74d95411d67d74d95411d67c74d95410067f73d95410047f73d95410067e73d95410067d73d95410047d73d95410067c73d95411d67f43d95411d67e43d
  | 30 => 0xf65191514263f6519151006bf6319151006be6319151006bd6319151006bc63191514773f53191510073d53191514773c521915142ebf6119151477b751191514273e51191514273c5119151477b451191514773f50191510257c76551510167c76551510247c765515101d7f745515101f3f74551510073f64551510167e64551510167c64551511c73c64551510163c645515146d7f735515146d7d73551514667f63551514667d635515133d7c72551511c73f42551510077771551510257e71551510257c715515100774715515101e7f615515101f7761551510057f7055151006bf64d8951006bc64d8951024fd75d8951014fe74d8951004fd74d8951014fc74d895117e7f54d89510067d54d8951004ff73d895100cfe73d8951004fd73d895100cfc73d895117e7f53d89510067d53d895117eee52d895117eed52d895133e7c52d895145e7e51d895145e7c51d895102cfe70d8951004fd70d895117e7f50d89511c5be7498951005bd7498951006bf6498951006bc6498951006ef6298951165f57198951005bf74589511c5bc7458951006bf6458951006bc6458951195f77158951006bf6418951006bc6418951056ee6218951006ed62189510247e76949510057d74949510073f64949512167e64949512167c64949510073c64949512163c649495133d7f73949514557d739495144e7f639495144e7d639495101d7e729495101f6e729495133e7f62949510076f629495133f6c62949510257e719495133f76719495133f7571949510257c719495101e7f619495101f7761949510057d7094951004fe7690951004fd7690951054fc769095133d7f759095101d7c7590951006bf6490951016bc6490951004ff7650951004fe7650951004fc76509510057f755095101d7c7550951006bf6450951016bc64509510073d5450951006bf64d8151006bc64d8151024fd75d8151014fe74d8151004fd74d8151014fc74d8151004ff73d815100cfe73d8151004fd73d815100cfc73d81510967f53d81510067d53d8151054fe72d8151004fd72d8151096fa50d81511c5be7498151005bd7498151006bf6498151006bc6498151006fb6098151005bf74581511c5bc7458151006bf6458151006bc6458151006bf6418151006bc6418151006f96018151024fd7518151014fe7418151004fd741815102cfc74181510467f54181510067d541815102cff731815100cfe7318151004fd731815102cfc73181510467f53181510067d5318151054fe7218151004fd72181510067e52181510467c52181512867e51181512867c511815102e7f501815102efa5018151046f950181510267f75596411b6bf74596411c67f54596411b6bf54596411b63f54596411c67d54596411c6bc5459641004ff735964100cfe7359641004fd7359641
  | 31 => 0x4a512ce7f6354a5148e7d6354a5101d7f7254a5101f6f7254a510567e6254a512cf6e6254a512cf6d6254a510567c6254a512cd7f7154a51007777154a512cf747154a5101e7e6154a5101f766154a510057c7054a51054ff7690a51024fe7690a51004fd7690a5101d7e7590a510057d7590a51056ee6290a51006ed6290a51004ff7650a51004fd7650a51024fc7650a510057f7550a5101d7c7550a51016bc6450a511d73e5450a51056ee6250a51006ed6250a51014fe7498251004fd749825102cfc749825102cff739825100cfe7398251004fd739825102cfc739825107e7f53982510067d5398251054fe7298251004fd7298251024fe719825102cfc719825102efa709825102efa509825107ef95098251026fb109825102ef81098251004ff7458251014fe7458251014fc74582510067e545825106e7c5458251004ff735825100cfe7358251004fd735825100cfc735825106e7f53582510067d5358251004ff7258251054fc725825106e7f52582510067d5258251024fc71582510267f51582510267d5158251026fb705825106efa505825106e7c5058251026fb1058251026f81058251014fe76d91511c6be64d9151024fd75d91511c6be54d91511b6bd54d9151004ff73d915100cfe73d9151004fd73d915100cfc73d91511b67f53d91510067d53d91511c6bf43d9151006be43d9151006bd43d91511c6bc43d9151054fe72d9151004fd72d91511c6bf42d91511c6bc42d915101cfd71d91511c6bf41d915102cfe70d9151004fd70d91511c6bf40d91511c6bc40d91511c5be76d9151014be76d91514873f75d91511b73c75d9151006bf63d9151006be63d9151006bd63d9151006bc63d91511b73f53d91510073d53d91511b73c52d91511b7b751d91514873e51d91514873c51d91511b7b451d91511b73f50d9151486bf75d91511c6be75d91511b6bc75d9151006bf73d9151006be73d9151006bd73d9151006bc73d91511b6bf53d91511b63f53d91511b6be53d91511b6bd53d91510063d53d91511b6bc53d9151006bf72d9151006be72d9151006bd72d9151006bc72d91511b6bf52d91511b6be52d91511b6bd52d91511b6bc52d9151006bf32d9151006be32d9151006bd32d9151006bc32d91511b6bf71d9151486be71d91511b6bd71d9151486bc71d91511b6bf51d9151486be51d9151486bc51d9151006bf31d9151486be31d9151006bd31d9151486bc31d9151486be21d9151486bc21d9151006bf70d9151006be70d9151006bd70d9151006bc70d91511b6bf50d91511b6be50d91511b6bd50d91511b6bc50d9151006bf30d9151006be30d9151006bd30d9151006bc30d9151486bf10d9151486bc10d91511c6bc645915147df771591511b5be76191511c6be76191511c73e75191511c73d7519151426b
  | 32 => 0x4b73c42195424af6c42195424af3c41195424af3f4019542055bc765514201ebc7655142054bc7655142015bf75551420173f75551420073f655514201ebe655514201ebc65551421e73c65551424a5bf73551424a5bd73551421e73f535514249f3d5355142007af7255142055be7255142055bc7255142007ac7255142016bf6255142017af62551421e73f52551422c5bc71551421e73f5155142005bf70551421e73c505514201cff7654942014fe7654942204fd7654942014fc76549420067f655494201e7c6554942005bf7454942015bc74549420073d5454942057ac42549420067f65d85420067c65d854201cfe75d8542004fd75d854201cfc75d8542054fd74d8542004ff73d854200cfe73d8542004fd73d854200cfc73d85420067f53d85420067d53d854218ef641d85422c6bc41d8542006f631d8542006f531d854202cfe70d8542004fd70d854218ebf40d85421e57e75985420057d75985420067f65985420067c65985421ddde7398542005dd7398542006f761985420057f75585421e57c75585420067f65585420067c65585420067f65185420067c6518542026f66118542006f561185420067f65d81420067c65d814201cfe75d8142004fd75d814201cfc75d8142054fd74d8142004ff73d814200cfe73d8142004fd73d814200cfc73d81420067f53d81420067d53d81420eebf43d8142006bd43d8142024fe71d8142004fd71d81420eefa40d81421e57e75981420057d75981420067f65981420067c6598142006fb60981420057f75581421e57c75581420067f65581420067c6558142005df73581421dddc7358142005f77158142005f471581420067f65181420067c6518142006f9601814201cfe7518142004fd751814202cfc7518142054fd741814202cff731814200cfe7318142004fd731814202cfc73181420067f53181420067d5318142024fe7118142004fd71181420a6bc411814202ebf401814202efa40181420a6f94018142026bf74592511d67e54592511d6be54592511d63e54592511a6bd54592511d67c5459251004ff735925100cfe7359251004fd735925100cfc73592511a67f53592510067d5359251004ff7259251054fc72592511a67f5259251024fe7159251024fc71592510267f51592510267d5159251026be4159251026bc4159251004ff705925102cfc70592511a67c50592511d6bf4059251004ff7458a51014fe7458a51014fc7458a51004ff7358a5100cfe7358a51004fd7358a5100cfc7358a511667f5358a510067d5358a51026ef7258a51166ee5258a51166ed5258a51006ef3258a51006ec3258a51024fc7158a51026ee2158a51026ec2158a51004ff7058a5102cfc7058a510547f7654a511d57e7454a511d57c7454a510067d6454a514957f7354a514957d735
  | 33 => 0xe7398242004fd739824202cfc73982420067f53982420067d5398242054fe729824202cfc7298242024fe7198242004fd719824202efa709824202efa40982420d6f9409824202efa3098242006f93098242056fb209824202ef82098242004ff75582420067f75582420047f755824201cfe755824201cfc75582420067c755824201c7c7558242004ff735824200cfe7358242004fd735824200cfc73582420067f53582420067d5358242054fc7258242056bf4258242056bd4258242004ff7158242024fc7158242056ef2158242056fb70582420c6fa4058242006fa3058242006f93058242056fb2058242056f8205824201cfe76d95421e67e65d9542054ff74d9542054fd74d95422167f54d95422167d54d9542004ff73d954200cfe73d9542004fd73d954200cfc73d95421e67f53d95420067e53d95420067d53d95421e67c53d9542014fd72d95421e67f52d9542024fe71d9542004fd71d95421e67f51d95421e67c51d954202cfe70d9542004fd70d95421e67f50d95421e67c50d95424ad7e76d954201c7e76d95424c73f74d95422173c74d95420057f73d95420057d73d95420067f63d95420067e63d95420067d63d95420067c63d95422173f43d95420073d43d95422176f42d95424c73e42d95424c73c42d95422176c42d95422173c41d95422173f40d95424c67f74d95422167e74d95422167d74d95422167c74d95420067f73d95420047f73d95420067e73d95420067d73d95420047d73d95420067c73d95422167f43d95422167e43d95422167d43d95422167c43d95422167f72d95424c67e72d95422167d72d95424c67c72d95422167f42d95424c67e42d95424c67c42d95420067f32d95424c67e32d95420067d32d95424c67c32d95420067f71d95420067e71d95420067d71d95420067c71d95422167f41d95422167e41d95422167d41d95422167c41d95420067f31d95420067e31d95420067d31d95420067c31d95424c67f21d95424c67c21d95420067f70d95420067e70d95420067d70d95420067c70d95422167f40d95422167e40d95422167d40d95422167c40d95420067f30d95420067e30d95420067d30d95420067c30d95424c67f20d95424c67c20d95421e67c65595424bdef7259542214ff75595420067f7559542204ff7459542006bf7459542004ff735954200cfe7359542004fd735954200cfc73595421e67f53595420067d53595424bcff7259542006ef7259542004ff7159542024fc7159542004ff705954202cfc70595422157e76195421e67e76195422147e76195424af3e74195421e73d74195424b67f64195421e57f73195420057d73195420067f63195420067e63195420067d63195420067c63195424af3f43195420073d43195424ae7f62195424af6f42195424b73e4219542
  | 34 => 0x8252004fd735825200cfc73582520ce7f53582520067d5358252054fc72582520567f52582520567d5258252004ff7158252024fc71582520ce7f5158252056fb70582520cefa50582520ce7c5058252006fa3058252006f93058252056fb2058252056f82058252014fe76d9152206be64d9152054fd75d9152206be54d91521f6bd54d9152004ff73d915200cfe73d9152004fd73d915200cfc73d91521f67f53d91520067d53d915201cfd72d9152206bf42d9152024fe71d9152004fd71d9152206bc41d915202cfe70d9152004fd70d9152206bf40d9152206bc64591524e5ef72591520557c76551520167c76551520547c765515201d7f745515201f3f74551520073f64551520167e64551520167c64551522073c64551524dd7f73551524dd7d73551524d67f63551524d67d63551520076f72551520557e72551520557c72551520076c725515201e7f625515201f6f62551522073f42551522cd7c71551520057f7055152054fd75d8552014fe74d8552004fd74d8552014fc74d85521967f54d85520067d54d8552004ff73d855200cfe73d8552004fd73d855200cfc73d85521967f53d85520067d53d85524ce7e52d85524ce7c52d8552196f651d85522ce7c51d855202cfe70d8552004fd70d85521967f50d85521fdde7398552005dd7398552006f76198552005bf7458552205bc7458552026f66118552006f56118552054fd75d8152014fe74d8152004fd74d8152014fc74d8152004ff73d815200cfe73d8152004fd73d815200cfc73d81520f67f53d81520067d53d8152024fe71d8152004fd71d81520f6fa50d8152205be7498152005bd7498152006fb6098152005df73581521fddc7358152006f96018152054fd7518152014fe7418152004fd741815202cfc74181520ae7f54181520067d541815202cff731815200cfe7318152004fd731815202cfc73181520ae7f53181520067d53181523167e52181523167c5218152024fe7118152004fd71181520ae7c511815202e7f501815202efa50181520aef950181520567f75596422067f54596422067d5459642004ff735964200cfe7359642004fd735964200cfc73596421f67f53596420067d5359642054fe7259642054fc72596420567e52596420567c5259642056bf4259642056bd4259642004ff7159642024fc71596421f67c5159642004ff705964202cfc70596421f67f5059642004ff755864201cfe755864201cfc7558642004ff735864200cfe7358642004fd735864200cfc73586420067f53586420067d5358642054fc7258642056f77158642006f75158642006f4515864215ef64158642006f63158642006f53158642056f72158642056f42158642004ff705864202cfc705864201cfe7598242004fd759824202cfc759824202cff739824200cf
  | 35 => 0x1400000d001007c00e016003002000000300000680060190010000016014054fe76d8954014fd75d895401cfd74d8954004ff73d895400cfe73d8954004fd73d895400cfc73d89544e67f53d89540067d53d89544e6ee52d89544beee42d8954024fe71d8954004fd71d895402cfe70d8954004fd70d89544c67f6598954006ef6298954005f67198954005f571989544c67f6518954056ee6218954006ed6218954024fe76d8554014fd75d855401cfd74d8554004ff73d855400cfe73d8554004fd73d855400cfc73d855447e7f53d85540067d53d8554054fe72d8554004fd72d855447ef651d855442ef641d8554006f631d8554006f531d855402cfe70d8554004fd70d85544367f6598554486bf6498554006f761985544367f6518554486bf641855421dde7318554005dd7318554026f66118554006f56118554014fd75d815437e7d75d815401cfd74d81543bebf54d815437e7e54d815437e7c54d815437ebc54d8154004ff73d815400cfe73d8154004fd73d815400cfc73d81543be7f53d81540067d53d8154054fe72d8154004fd72d81543be7f52d815437ebf42d8154024fe71d8154004fd71d81543be7f51d81543befa50d81543be7c50d815437efa40d8154006fb6098154005f77158154005f47158154006f96018154014fd751815401cfd741815402cff731815400cfe7318154004fd731815402cfc73181544ee7f53181540067d5318154054fe7218154004fd7218154024fe7118154004fd711815402efa50181544eef9501815402efa4018154356f94018154056bf74592522167e5459252216be54592522163e54592521e6bd54592522167c5459252004ff735925200cfe7359252004fd735925200cfc73592521e67f53592520067d5359252216bf4359252006bd4359252054fe7259252054fc72592520567f52592520567d5259252056be4259252056bc4259252004ff7159252024fc71592521e67f5159252216bc4159252004ff705925202cfc70592521e67c5059252216bf4059252004ff7458652014fe7458652014fc7458652004ff735865200cfe7358652004fd735865200cfc73586521667f53586520067d5358652054fc7258652056f77158652166f65158652006f74158652006f44158652006f63158652006f53158652056f72158652056f42158652004ff705865202cfc7058652014fe7498252004fd749825202cfc749825202cff739825200cfe7398252004fd739825202cfc73982520de7f53982520067d5398252054fe729825202cfc7298252024fe7198252004fd719825202efa709825202efa50982520def9509825202efa3098252006f93098252056fb209825202ef82098252004ff7458252014fe7458252014fc74582520067e54582520ce7c5458252004ff735825200cfe735
  | 36 => 0x5009800000e0130010008026003002800400a0030020030006020003800000600000580c0002037000000c00a003007805800a007001801002a00000d800001c01a00e8000002005011800400801d00180a4008008001800803400600f800c00a002000802000e01101400040040080008008006000001000001a001000001401e0040010000016001000804000800200a000000001a009806c000019005800400e02c00880200100010068044002002001800801a000000800c01200b000004400a00a0098000000000005000004200000000cc01a00200d000000a001001001c02e0060068084000004006800400000500000040140040000018030001000000401c00600000080000010040000000011000801400202400a00080180180008024160000001001c00400100000600120070010060002002002001801e000000801800e00500b002c002000001001c04c000002001800a02900b000003c001000001c01000e007004001600400f8038008002001000c000003000005c05e00300280240040030018024008000000802801603b008804c006008000001006e001004000802c0080010000004011005000000000f003001000c001000002002a00a000800800400000000000200000000034000002000802803600100000040080110008000070017000004c000003004000c00800b004000400601300e8020026000007800800a001002000402a00600800000f0003000002001600400b000000000502c8000000007002000000000000f00d801200100003a4000004000801c0020000030004008025006801000601a001001002a000000001800e0010078000042000000000000200200080100020070000080028007009013801e0120160000004001005004400600003e800000e014006009402000200a000000200d00600100060000050020002000000000c01c00e000000c0180100010004000001000000000000a001805400a012002001c0ca0000018004004000005800400000f00100b40020040178014002014002000001200f0080018004000019000001000100b80040000110040020000001000001800c0000000008000006001800c000001001013000800000900080000080048024004012000001c0360030000004016029000002000601601000300340060000000008000000000800207300000040000080100070006017004809801e01400d006400001200000640ce0000098000008011011000800e00000400a000000000800100000200010000010005000001801c0070008004014000002800800600a000804806000200c010c00400800100040040030030000008014000802400200000000000460530040004000004000800000c001000000401c00000300000140020000000014005000002007004500000
  | 37 => 0x480ae00700c800406400b0018014000000000000000a0010000030034000000800400001b00c800800000b000000400c004000000401c0010078000008000004000801c002000800001a000006806000a00e0008004012000000002801404600d0000014004002001804e00b00180080080020148000000000000000001400000d805400400b004000000a006000800000c005000003002a003000802c000011010800400a009005800805a000010009000401900180140040020078008008011001006403400a000000003c00b0038060022004003003000602d006800001a0020000060016009004003400204a003005800a008002800001a002001806c000000000000400e00600780bc000000007000000400000100000000080018004004003001000400000200280500180000000000000002027000000000c0000008012002010000000400100e802c00202900e801802c001013800402801700000140040000000000000008002803c05c00100000000180000020000002006015003c02a005002003001000200180c800000d000006c0100050060008002004007003800600a005000400000001c0040032000001803800000e001800400400000c8028004002003001c0100050008000004000000800c00602b0000000012004002000800000b0038010004001000000400800200480440340050018000000000001817000600a000000c000000001000c0060000018000002007004000000200300a0004002001006008400007b00c008c0c0007001002400400a000803c01c00a000800800000100700000080050018030000020000005801e01a00000000040050008000000000006000004400c00301e800e00301a004c002007005000005a0010000018000001002802c00200000080040000060010020024001003800000000d01c000405600f001002c0ec01b00b001c008022002800c00200c00000180f200000400300100030068014004000008000c00400000b005000201f0020008000003000004c04200300000000060050000000006002000006c014000005000000e00100200c800a02300380040000070048008026017017810c00000600200140260040028000000000000008c05c00f000005400c000001800401c01400b8008000014010004404a0020098010000000004000001e00900080ec00e00d0038000022000006808402c00c000003000000e00000800040080088010000002010002c0000490010010004011000800c008001001801801800b0000000000009000004400401d0010008000000003803000c0030000004004022007803c00c0050098000000014000002c02400100c80500180040008008002000000807c0000010030000002007001004400405600c0050002001002004c01400700300240040
  | 38 => 0x2004800c05a00700d000000400700e800805c005002001c0240010028000020000000001412000a011004800600b000806000400500000340040000028000016001006802400200000202c400203100080040260000120000034012008000002c00100380040020000010008004006004804c00003700200000200030000008004001003000c01a003007000403600000180000140040060014006009000000000001b0000074002005000800400000702f00100220000010000000004015800000201300080000aa001003802c00200b0058008004003000003800001d000800005000b0038090002000002005802c00d001000400e024008800001c0000078038000000005807800c0010228134014001000000800a00000080000120000080000002000008801400000c009002400e00400000000080070000014020000002813002600300200100020050028030006027003014c00000d004000000002501180a8000005000000400401b000002800200000d805400000f012005801400000200800180040010008000005005806406c0000010000000000001800400000000700080020030088008000002023000000c009007000000a007002800802a003005009800c008004800003800500000180040070000000000000013800402600800b002c030019009000400a0000030000026005005001000400500100080b2001005003c00000100400080000020000040016001000001c03a00d00a008800000e00080040060080000000012000009803801200000200000060000120034014000000003002a004000003400a00700900000040050000008000012007800000000900a8010030015004802813c002000800c00600301b802400205a00c8024004001003800406a001003803818800e000000c01400c001001c008002000000400800500b800001000b020801001e004001803c020006007806c010009004801c00800c001800801400100500100020010008020006000000002800a00300280100000140000004002000001806c000005000800401000500500140000020158004022001003803400a02d0178000000007001822c00000100c800c00203300080780080510018010004010001002c006007005002400e006000802404c0000010034000005000000400000000100e40000000008014008010001000c0000000018010008006004800002a021000802400c009002000001e00101b8004002000004801000600500280240040130008010004001006002c000016003000000000100080f40020070010018006008000001400200f003800c01a003001802400c006003000000400600480000260000000038002018001800c08e001004800c012002009002800000200080000000020078004008000000802801c0210058
  | 39 => 0x762b90000b199fa43a4a75885693805c5866e94e8a36b79a55e4fc2d1646218400a829ec4ea2e36a048000923085c0001e4671b15f8ba980003908f2eb65864e37d00000f70beaa788b820002d346be1b929182f34abc01aa4338ad83a40c8819d25ce92ba9ae4a22eaa6c6a23e0001af641f000000007be4f9848295b92602bd968886d103238b130a7cca22430707e65c8299c35c85da3f38000ab5ae643d8a30e39e82b2bf90000676000000005c4bf22b9850280000000c6e93f80b6b95908a6a981c0000006810e04b61eb12a02d51d42a538a569c618f2258292416e80009d98000578ab4c8098ba28caa790000094a00000000a980008a200003911c686642e8cbcf0000000000090980000e09d9006715405b884e44ce89be96006e6a662e3431215740e5a9b448400008c1000000002ea77d1bd223307680eea4fa00011c4000297815ca398a5520a843a105274ea4247af01764af137213c85d09e10000056a1d40dc807c4a7a02e27b0162470ac88b7880009fe000073917c025e1eb480390c600000009de8f7a4a28000a020000687000051920460a1800039f2b580002fa860224c8000000000028529be8bd80d5000072a2ea84821d48b560b62195033000020568920000265000059981d6ad719a467b011a0002aa86b18000000157699414fe0002f9c03e2dd200013a245a80001d91e60000029400013cc032841e0002d90b4f80005c52ecc0001794457a28234f81780000e9c34a800000014b234c24e2bf08592a3c97d40000000a60800070c2384a9393ec000000064b89aaa971b4624f000032328be4e280003ff9ea08f68bba000000039182386b380000000b22a150e880000e1e30a000022a952a7ca00001bd07086bd1200045afd40001ed4b1c8c548402eb4ab980009a628609848000818abb622788f44cf800088588c0b5b99707431d2607d1db873e110280783e8238a1bca0f0f128518eb646f11b04b313ae789867c25889e82ed80824be17445f9a7f424ea88c7a10b9e5af80be75a1cf000010bc3e408801b817089170a8638016c800000005fe92aa0001fa200018fc000000000000005ed000061d8000000106200028561cfaec68bf00080020030024004000012006400000400e001404e004000000000400900a8010000021000001c000004000009c004015000000c00400100500080160000010014002000000800c00801e0000000076000000800000a00000781d000a00c00000080140010020000000003000001800000e007000000400200f000000000400000340020020000000000002000000400200100300300200060038018002001010800c000000001000001001b001000400a00a0020000002000000001000c000000802401800200000580120060000000018001000000c0060040038000000
  | 40 => 0x12225fc7c120320001d5443f932e000237681e0b04000000000000000000aa45ba846abe393565429e2e96310182d12fe24648f322f4067a8cc9f304071daa1d6125276b9b94321233085d9a2cb62999ebb117a06111c1c79e89348fe92548f09004a8695d209a25e64eca5142ed1c1620b0c80234aa405d295fa5bf16b6ba8a14a39d13e23e50ad650d0d84ad81fce77381d2b589adc033953891203c87fda5e04ef22d644da4ac7e088c40a79bf0ab09c1ebcc8fd67d41430139881c1d5ae308d1853009b1f38715ac7a12e27aaa542c403b18ff651d23ae64e963241c8c7006529fe9bf1bee2ac19ea6f62dc22ea058a69d1b908022a623d1900c6618f167270164bc29526a19a500481aff06b9adb42ff1a821232aea9530e14283961ab829f065fd883c940a17e551997405f82cc5a91de88e0a6ce1cb077e99d1a20a1a1f2ea65027038706d6591ae74573ac2a007af7aa4d0a54aa38c94556855c8132fd849113341958d9c9718bf65e326f07b90fc65548aa6a4c9c5a6fa84d87aeabbe46aa01c89f1df8a9a2d1861528504019050931842a7e712c245b26a0747056297e02f2b8a28dc80c18521fc17628d2144290b0baabb6a004b5280d82872f543aa9bac9c9929a73c94c2899a4626cc0e6ea9083ae36f9ef08978b3683f08ecafc296600000000002c5ab29aa829731df6ab71b2a0fb81b6b161a600002e7c0001fc04590a162a30d8a0001d9893c88c802c143800003263660e721c52f4c10a00001bdaaa22d20e36304a8a827a800034989fe00002eeb0590b485d11681a211de891a690af683062002e8a2119728a032210b2081305f918c89c416d65932d8866ea7a8b9391542438cf45c9147039a1cca40995220001b2c00000007fa24ee33a800044bab1c5289d9266f13944c0a0e800a91da3ecaa32b0b2c7c12589a02c989a49132c30a3b9abcb8785024d7a044a83024e1272f52557000072c9f8c00022a48dd0b6a94d2c8e00009bc0000078359800072080000000000a46816673e84329041866000000023c1b4a49995300002aac0000000bca800014aadaa6a590880c7255a000044e830aceab1f946634e179c6b321b807787d846b8000000229cab28d42a1199ac2f5181ebe8800000008b4000000000000001991ac429782d649400380001898134a49c42480001f32a9c2d811a2000011e00e80000001f703ed85f4b920000000106043086a436d092a43025ee2421d6a72d959a277800085718ba0a90516000070e26b800039e22084a90e6049d894420e2b565110000a68800093600007f42bd4167221a19f9d227e2953c822a72883d9b64bc1846c74016964b119b24e780003ad1030a980af855a800030d038c4f011ee15821fe000269cb510b8e2bb9cea0001d6089b00000000972000025056f18186ec8c22417a
  | 41 => 0x2abc2a612ce94b2d322b426425ec07d0b7a9a3c3ee000089a8cc4744040044e1c105418ee80002c9084597667778bdea33289a402ad3c0a5a6823dfa46e4699e88237079c5c7a2c8573040806e94961900304a3d99dc46b0000ba514b056e93e031f85669f42ab064d280a8688c2e3d29b665a19aeeb61936ebf6a5740fb03cc069a446443ada0000000042d9190000147800015e00b29be640a86fc40e0e804d4197ea22858c16aae0058a2ad000022688a1000045880008d4098c0000000262ab760001d74b328a8833788ea024afb87b8a370bbf182e6ed82ac00016a06032da233f0472774800002a13f830f093e0002a48000154a72d03da248147aaa11c14054961e450a63e2ce24aabdf936a000151470a847e0faa1c20001ece00008ee0000646603aa126651280468272cb1e151e41e2e448d08000000239a7ed80002cfadbe6c9a158000264a8958000000000000000000001a92b89142c0000000000238cbbd00000b51d2052b80000f500001170faa0000ed28e4165629f1ea4000000000005109b9800084c000053527ea203a8ac347000059c23a03cdad02000015c7ee812e2619932533119c2f70ece3e92ddabf710467d003168c989225411b1c4f105c08ad0b7c80510f816c27788e709e0404209237725d049c20b28be8998a3121b6613160c41da4d67632a20624206e9c20a9a7411b0e0002f142359f580cd015e93b2ba43ab80c899890fc426a8301372d425b99c8a0000fee2f3006e22ea32e000000059287720002976000163a9f48b4eb190b283eba1066472bbc2af28ec5650000a7d8000b5a12400262e66b4c20e216f12acb8b9d4eb7caf8a95911669079900769aba21999f960001c2ca6829022b514028b4128400000001c68e3007180008ba980a477202273883507b2834261e87408a995dc5a12e9c330108c7b9a4cc6940d52122832e62319444159b4c40597ac5a6050a0002ac602e07a01f8afb27b71f3a7f91caa7460782ad0ae0e5a29c40129aa5a7dd0dd87f58d4000028149b310f674c1a38a0982ba13a00c473bada698ca16cbac96cc56aaf8c545a67c86689ceb488fa89ff2dae99c800000000008319c669380e8a048821e4a71c2215106a66cc97d816983be00005e65d705422a39c0091e0c443e6a7e4941a9b2000237e239a0a24ce2ae41c80076b251afca5492986fe1d0e000243845e800092f00000001cf40002ef20002c6e4d11d860000732000000094795a89fb027ab6da91417b995c7e68000311a1d6000127e6b01d72b4b01fe3490dc6424052ca08800049220e4644a57a00022a2b12a33c0002b2431986dc0001a8e2e7143a4078c5e96b2fc6b7e28a66e0af208ca26b087287420001cde0bea24a06b2a1852a20706f680000002a3600026a853b800070b800000000003929c0e92418ae
  | 42 => 0x833500007330672b4e8256a71960aa911340678800048e8000000000000000004c402769a4a8bc000000008f0000180983825900005d325b00f58000000099c6920036a07800000019c822200000d98d582fc0000b2f0826bb7000002b01989cd9f547e1a6da000000078c219c218014e11297e80002d50af71878ab4a44e8ff8188a0e1fcc0eb1f92789169e0531c0cab8000000015707972bf411d084e9a38f106372a144398e042e2092640b834624c29c28f29ad2bb0816e6108d68afc83e23e7086650226f26c4865a4992f0c0002124a6b0a6201cad980002de88de8b9850680000000ee000000000000000754912ab9280006ac92ee0000000b150788000166c67814005220ed00000f6e0001612000000072b800052087c04090bda71ca44a41d05269198000b2e823eab385124870d8e62a21ea0002772942839c85797360001b24559173cb9b86cc4ada2d8000000000013de45017a400003d80000d6439f904e0658d6047406166390984461178238193747ab00001a8ab743e89636b2604643dc80000000e3ebba950cb60115a79c888e006186407f178e615999c49e9a9c7010c8e9eda73a0972b0c8dc911a50886b0b4a278eb8ea67800024e81960a744c1887c0000000af80ab6a96000043c90da917ab2c00018327eb29e831da3b458191320000c5800023de31c8e709f3209089088b26661dc803b024a30c9608621260c64186e28f2202a1662d12920872422a2434671000052d0d2e4d300006f41828bbf9e1c7db82740a68bec30f8f442d193fc06400000ff1424000000087bafa020b8cac4388000a4a134e63b19209028dc25daa6ae85f00000e127429500278570234400001ee7d21c8e6992cf84639420a9b0e263fc1296178277e2e12eac83e175a18328fa7068c6c6e79b6871fa6180309a305b7115208b03122542a30013a85c64504fa862188600011ec228a4001518d161d7985807c2392ae100d0aad000019806b28de0000a2c99fc84313e825b85200858e4871e83e41d49e500001e5e8cb0000146263800009883c10cdab7f207a509a2c4000187296c80003c71484b630000b072b043ce04167652f228660000bd683f4bda8a8a17c027cb0d09cc13180000a02f9e7d98388000000074a00000002d6a7a2a69a49b033a6588ee252814f6abf20a436b282c9af220a2fa2f806c400007409b984b2248aa9e94b60000aa29ed1b608650968393231e48b148a27d0bcea3a2f5c0bd845426e989a51fa7d8000223682f800000004065c880009a9091600017a88c4293a32293287f508f80000422a808f6a278800036e154e10f8bee0000f22b9da9c862da946862977009016ae1b38d701861e3a4f52c8644d114e93d8504afb8e6c57b2ee4aee81a4786af5e78198888c1ad4022910fa64101da1610c422d301f21a0
  | 43 => 0xfa8b000002366649db26fd00047d9000091d10d6000000081600000002ede0002b3481f1b544e10554a3c06fe00012ec7ad80000002538b7793d872300002a500c00a700007540dc094904ec56b81063a0a8de71aacd6ad42b486622ab80b880304a08000acf84980000ae27a012b00000c18171840e0000000a81a96e5b81f1a42ea8c233b2d9a6fb0dfe688acee6902ca0b6525725e5963c945a0aa153aa88630279aab32dd4000231a78100004b882d0952118213a80000000ee613d0df8bdd00004f1a9625269d6200007cea3986764c91286ab212ca59500003d98caa0001bfe93a983000022ee0000000baf8000a67a34e00013627ef11ca84b90343372c06a899c8443c00000002ae2849a6805540bf44530356000059e90a2218282145ea510000934a72a4ee2a780df173a17eaaf210500e20e78952a62811c9a98000ae015580001b7200000d622515006500c2c8d696600000a2c0000af042708a6b4e265c5242f0051f000099592220dda5dc38c95c23ef8a024e22098000000017a8000000045a910a75a77a80000000000000256090607fea7ca542a70248e000000008d000000000000fc9b085f58f7c97f8dcaa5c91507a60b24000195027c0dde72b09567369316412213a0002b16ae493480d60e206be94d0360870abf78d04b2b1330237a0e00001bbc00680006ba00000001d6c4d28040a1f92fa31e01f67c295c451a2a7201b2b2022f99da755923445e0d4c36aae9a0001f346468dfcbf9800000003c087b013a1ba0b8a6ee888c5db212825f94ce25a969a8730a4e29613ee9512c020f1167a200995a51014fa18c1de2772800062283fe8ce84844af950e6818000a438deeb2486c8ad7886e0001eb86ca0000837a7e821210be91ca6ec0001f5a03a80000002bb888326280002652376ad263e78d10b2a0000894063a4830db02beaf2e58829ba33c2b08148ae703fc92781ae985a0001ca047194ea8711fe200022c20001ed80000000a5d073a0de8000867aee200029debc9000077e8000a0c8000a97936600017b6000138e59a00522212b6267b8000b719d88000291001311ea000260a5799982473a9004ec0226ad6800008ea1785cd2ba69fc8000b2b8000b648000a949c32000000028d25ba1c7857402427c400026a210e80000680aba517258a8ae83404961de0686a98caaa935aa9f103a0678000000160ea4bad2a08414044bf0aac1189e960990afcb5f2b406b807c8000000058986aa7e5017a469229e88aabca9151326969825838088c6b970140784158e5f786c0a388d228120a1eb670ef68e2280299a80007269d2a532282e17d92d034cadf420c227e18a1d963b31f263219ba658b0e1235d96f04ab9c3aaf2248030a8c9ab3413a07418ebc3e08dea31910de11a0000bb2800094a2b9c19098bc2b010a
  | 44 => 0x9049f23a2966958407809c200c80e6511a93643505c20002cb01f80000000250c1268ec08df21dc0908000a2daaa0b178e3a07293fea041c0a926a98010d9a72022997c756286268a26d2711212c3a5095c8b8a7140c893004c48fe632a11581e00eca58d1e6a73dac000122c9aa47270468c9518525045e15f052870828a46558d7c61b99f22942828a5ea606a6e0b5a94b865021b0bb00dc082437da70008baea0987a028bc38b86a0620f4ac1a5bebc78f2a2659b3a9b59c7c9499feebaf1e427db1c3e846ab88b2316f28299532b55a5cab88262c650a4c40002798000000017f03fa713aaae4d51d760000336842a19296a09dc3f92f961061d1e8ff2040af89fde08114e2770a62e3f81a2ea282b46297281c6a780001422c527ffa358497afac073000092d93ea72fab0e000000000023806c3279c2e51e1e6d4943c00003742cf0f021d186f07baafec3681b8a6c500007c20000b96800066d07f600000faacf07e865a2f4002ba07215e2794000097c6bf9d3c47e1508b9618f46c1049e000189c4cd880662c1b5c000000000021ce000195e19e27a2a03834a12c91c84451916944aad44d612e87c61e3c0001d340798a040000000795000000000005f28f245d02b3255f1bdc33980000b080000aa974852926967c8156631a2a76ba90000aa79c34ade80008e50000000214068581ec5812c3e000296a29c036c10b25a29ba14100bd2352121800033c9aca2e82cc600b831e751000000019ce64da716019178801400000000000bc682de083234a71624b092229bc83ca9f48259b34a42855ebe12caa9df19f44391e38948a4520839a2a2452b6860f0f20000110c00000003cf0f3013127fe0001e6c35b000090a8000abd8000049264e958913093d000000023d400005328208244677994ab3522de00000a4b810d74a812c26498acf0b3d20dcb2128e42c5824ca8f8aa802d02ec85424e6575962e8471c268adad60b052b227fb21e8b9ea76a220abce97029e03fe057621914f401d02c41de2d52256a2cc7fe06bc1468854b3716641e89dd48c8000075ea8ce7130fc26c029a413e278c1e98000312964896127ee4c62b7e23da5b6bcb2dc838aa4e450d9a7a1f5000032f2eae084a1d297e800043710a62d7ad6400000002dc197a0eda4645911e2036a27b0a7a8a0a07386a018da0245fc84b0551295e00009b63c3146e73000000000ae021fa68c000000000006103630644000000067e8c7c85c28360000eac86aac7464f956eb531be4b739a3a7188000000163e45b952438f0000a4191107569fd2b2e1098000000000000001e5172caa921a00c3000055ea9266d21452870195400014762702406ba22c2414e80000e29b8656306984f4211042100000b1800000023b20002eb0a0e95788cfa57c2bd222c90c9e9e20a04508a
  | 45 => 0xe9fe692c8cd27c721329b41e48071133208a0e4eb5fa1620f40000649aec05fd056ea178b529e82b9442e0bc00001590acbaf109aea1fa3678b1a5fb1fc4490895e9f00c0e406af563c6afee17881bea25a8f8346089c7d58000a46000032b800029b0448a9b8fda773118679480005908f3a00004c00000000271941e59e00008d900000002fc469a00001cc0000594829295726c800013da15492e60000000b1700886962a9a4b1816a2eb907021a8a929bba4a4000099e455800011028d6a3d08bca4c00000002820000040a0cb0000491861a0002bf83a917c66c7840c5218c1ebdca1e2aafae62a192cf675700000000da200001f800000000000fb00c694f8b8516947458000b57946a65999240aa288018380005c18dd256d85be18c80009c7893644a0000000000047e80000000ac202a965a3241daca5200c640383901b420bcbb4937e6c283680002916634000051b0ff4a6d801c038091c0b4936c0372912000100000028821dd905a7c318ea72e00000168ab22361a460d72b8c687a9381520f0a0000b9aaa5acb2ae1800083b06269db17e2a73224e2a12ce61a40000a8b8000070adecb6118804dd8000675110a8cd00000001d66106af480001a00bc49c94a5a2212216111200019f05761b16606a3620c28000b10878a93508365dc8f68a758acaa58026004318d87fe96e405c8df2a7b800082215dea4f9aea00faeba00000005e42c1800025c80002d0c507117c527917200023d86cf00000002340702000000021f80000000709098e5bf998447d80005dd825a0002b1214d09241a7152cbef80007e2000054d8000b42a2ec48ba0d4bb9818a5622fba000071271500000000000000000055fa964a1da3565940a32990215270080005a88cb25d79560acc297cb440f5c5df0fc88c21e74987002cb110aa0ade00009d59692abb00620052c224c696f60d900000c90cee2261e9abc200002b200003450000212a35e7aaa238b0415a60001662b7d800062f9f104238f70589000048800002d00000a432bd2964018603311b816000007cf238ea3fa87426682be80192de57501447828000000281a6bcadac420a5789620ef06f5011469997cc5408c7a072000006c800065d800000000000000aea9aaacc864a80a247923b659b906689baa3a00009486088d3c00000009998492b8400009b01238555023200029425d905dc3a8000003ca25a00021de2db9f4a64f03a09be0a1abed8000000068e0002c563f316a893019ae76c14182a707da5cc81e295a800092485b682b966a7b416ba9d5238a0d20000608076c3249f3689e97989cc272259f16fabbb145839425304e098f8b13a9aa1381702b400de49c712c07d895962e48d860461fc664e0df01b09a0e9f518a01f180da16c8b78a3187a45a98cbea101b5eb8f229a1ce2e
  | 46 => 0xafa0000f52ae2930c1ba8868341ac600090000b5b018e89e056c3f490029f686480002b709b080000000000017832a06f0000b4503f06b6231400014ac28e01929b7073c0a107de8232e3e30dad7a99602b01418e544658f980000620b5d17840000000a8a99a815f94620001054000029896d21807b21448925a6262968000a88932a10915109a5184875e17c45ec80009e780005558000a2701ae760242095b000000010587fd000090324ba9141eae8c721a871d8c265480000928268a0002cc0684913c331a0b08278a3e18a9b7c00001b85bb0f7415597ba023a298bc626460001618356a2d236daf905b2ac482e582e06b5891a06118e812f243c0001fdc87ca0102cb11e66ab12da6988bbe6aa8142a27800000010ae8fbad709f72becb0e09929c900003438d6a8fc29701fb145a4899b2e9a1128c850a63c6cd9bfca71055a327112020c91709008c149c68000000000073403603feab9ea53139cbd90dceb570a428fd9a5400023c465196d47f2a6b826d0dae5d800000a21868b6c921e72f00006741bc497698a623929849da15ca05a0b3232809a2000248624299cc64c068a3750cd67670266a1f28b49f7a154819879617e0612aa198d2731830e0002f040002e9886c80ee00025e467082e63f7800000022021932408ac78dcc14f2e6a30825969089b9600000000001ec28da0e86357000018100000002d8e9ef80e848c28d463f80000ae0d0a2bf800008909fc4fd9bb85a01f4212a91b68bc93681fea3d288781362799a36b42044c557adc400003de2b117920ed00007afacb69bd98a26a50e98ae424a847886d83b5079249ba6deafea2447b7821a0c218c61ea8ec844b263a9951e78963906400018000001d3828880002f89700a52ae680002b6a38900000000d1e276aa7e871a4b8000000030180003788b5c000113a91b00000002324272a54aaeb95a2a8a2a541d309ac75911760129ff26f3981c0002ed8639a25c000169c76f000000002bc71b9fea7ed000097d0db20e526863650000539a53687d800000015e46912770aea89d20000d5eb43ab546d88f64000120400000001072f76425800001991ba92784a03ac0abe4459dec538161400005364f7119e96f0d286dc2e1a080a31880e15b8b3b1b58b6a19be90f8c027e113081f90b90000000092f800043221640a42d2440d8120086077c6f01ea290b94288a38d2c6ae07008960e6469b033e04e182600006b6bd18bfe51515f05c42dfa0ad01b0ad48000000094679028709d7989209f800016d26be02000000000f2894f9450bf32c4c823a274a482ece98aace24a40100ac500004fe9cdc0000c08000295c16180f07c5053839724a2532857a48507162d620da00029a854d2f944e980000001398a4f0a407d30a305ae04f66c8152811e1dbe29282628b990688
  | 47 => 0x29301d470d994c39880000002f8299b0ea26379c865b79b9cbbe987e0b20bf806d2bfc31825868478000000097629f809e9d28000182091e000000000024309542d7815400000000c5c000000000017f80000da60002ec88799b508b502dc360151270a224c7f6000078b1c907742bcc00027060ca29e4a09196a1ea0d34b85a33600000000000000000180689498e09d1000000000006d000007b4a8948a58000a6993d6000056a835a6c46978b2a1e403c65be106a0000000abfa46a937accc00000002c300009e9924c7bd959e00027bc3c186688140fc0b0ca2aa0002fd065600001d42ad8000083a00000005859e7c73f0d922741ade00021ac7c008e0000188eb5380001e783a40000b761c0800042b1f760002ddc1bb8cfa5601ba81730000b1b1e648000d0016a11460001bf200016bc6fe8f84afa8000b3399644dc2668a4b17d287917eaac0881028a8cce8bd96300949dd681aa1c8acaaf6c975206cb6eafe82cc16c40a38012bbc0b146489a8ab02813c8f9295a0162020a4226d476d03801721dda8d7266001a9d9e4781622aa2938c0c622bc714ad1c1c726c66c88edc52e8606082a5589800c50302983e3259fc2b3109185bd03a23fa840260aa09c89c96103390d5614723cc21c259e3d21bf677f828247c16741652be67b00b723e18000197241c6dd04560002e7e10d12368a30a727932ed477f20ea49a970a5e2ab0a826a0ac42a999aa8228aa00015f288004cc28f0e666d0903e48f259c0000d50000000065226ac00003526aa210e00000008fd17f08c0000000011262a080009c28ab40790084605035a84494127b19232b729322a75250e5df89d400016e89d4ab6e4ad2e5285a8a7832c2cfaa1eaba888c868c9710b7e1b689001ab283e9250398a010006bf29b8e54e98468f5882a4f288da4252be457185b89fc07342142df0397880455ca8fc6dfa7aea38148c0000d8861c14fc0b625b853a16ce85b878ebef28a200017740ab9256951951ab6e214c9990fb4b4da186081a3be85807cabde20c04d08e84915940c055850e4c10b128faacb4adc84ba6f310caaff800035218247de10e0aaeaca41d98070ac40ec409b9f6015a063c2c184764529e4a693889080b289235e06b8524800091fa4da921000000010200002b7c00000002f8000097a29880002d069690000174800000026361d81fae160a2046929390869212a2d427c853580006e200003552f428d80a6600020b4163a41247f80005d52a1c388ac6800018367da1b800000a9057b860a08029be97614e48da89ee7bb0a065ff9a0a48092ea13680a0af40314bcd92d66daa73e3d3934611b89f233e1b764ac9ea6351239688d00000000000bfd0000bdb8000b3818960000000a50000048900005ce15fe2ae1a9a192a19091120165b00a3a98205e46f1a
  | 48 => 0x2e9e00000000ba05f2000000075280003aa02a200005143139e44000081e2862a8c0db93b612b00000000ae63cb0e0856088920001ab43c616907c780008eb00004de800027d8c6a447818071418347a31aba6041978836008645127f6a941e92964a6d80000a527d7026a19c00000000000beb80003d5124ead1014a4cf1ed60000c0024419f851ca84c53b0c24433031095f9fa623a0e7663c0812b079a840449ef40001a34a1e21f474d800066c20806331c18068a28a82190a22842b282c0ac704a88eea00011cc53c84e23afa85a20200008a026f400000002050000aa013d20000000b568e1a711a2260002570b8a80005ab14c4905207e3e58fdc0bf86525722d723e284ee04b0efe679a65eba02e4c75b998eba10d464a51a8c80d04d612029228aca2c625b27c6a23a1f05628000a878c10000019aaeb2ba0af1128e54f98b891a069a28bad462f287263e0255434300007bbaa10000260222b80006b2174e000194ea918d90a121fc817f81326311e128fe298ea7f0cb8b06a5684ae9012689000001527e29e0800000003b017596b26a1af6885e8404116279600009287ac919aacda166a3210d83de205e0760af299b87b27a0a138906afd20be1d1a4b6000075f8ca62db074e00013ce4b4890cab78154780800005400006718000a1b0000a0a8bacb3f8ef88c4a72068f8ee499685966f797186898d4e000284278f9cc2000000015c000000000fc6e681ea305a2e0000084c5cc0d08000286eaa40000000002689d8f26be18000635800000000009f08000018000075f172a42c27b27e4000200006f250aa50400019d678a15a01ca00007ec8f14668800049ca40e5f68000513ae4069c164ebd994dc5368000000292a960800000021ba73fafe0b039b5ab391aa2b309b7a000015810407042111124000000000012dc2ce800000008d400004d40000000646000077100005c480000001a1400021207fc000087f16aa757800011f1e9c0001e160000000000125c00011f40000f5e8610000000000069e15e8be680000001d320002834704a30c8c88000000075a96a8efaa55809622d842e97b08ca744971c0d300000001b6c00021d000000000002b6c00015ac3b79ffc1caa6700001a562758000b89800065b800052600006db80004bf8000587000032898ee735a884215a3d0aed2102bce84668988ce813292f6000106e24cab8272ea1b04c80ae86a000001ff17fc385a3b03e4a5f299d98600a323b82a5a05abbd800063e93be46516d01b5278a2da000000015b21e68eb201f83b80852f0294814062d927e000015da67d800000027ce3c0094076886ec000288878623e8ad9000059f9e5a128aeee9cf1bca09797a600000008128f4200000000232f3e0000fa60000be400016726a91a5aabe2e6c00028da000200c6308efc
  | 49 => 0xe8e91f7c878218e6c62a346a21bc8000000066822b08c58c1a0002bf60002f880001f0200020120002ee0985a4708f3800000013c27cf95b464400008450b0e0000000a66a8ea50c9a6a9f2817463dafb45c1130e9dda2ae02f1efc04f92162f2227097c00463b587c230c07b828a1b840000000bd29ba21e18f8c9890bf22dd0b1e9539ac200029da2b32e960002d662f980005802dd680f06143a30d205e680000e487ba29e8f58af0800000000000002ed6a138c0473b125a3f884ce94f2e1c4f92d5416227809c09d240379b4e00027e638ba70c8b71b560f497aa77c182cb831ada888816048a882094616b44fd1c6091f245a9680adeb9507d632d9c4a47585acb0e84deab108784d700006cfa4a6042205496520020000cccb3f0bc6b6c04a42219c886b907b4b7027462062f2699eaf1c80680001ed974217a05a283388b823f8c5aab6a0f02e9a240aa620fe78d052e8210dba84d192848a01dc0032dfe00f1ca642811be2882fce3340da42852e72bce00007518000000206843480003c22faa3eb172e0ef2f160c811e8a1c93923a59be268318b40a28000156141490d8c986140906000000013085ca2c72bd6bb41e580269f2200004126af800009229ce0002fb0000054a24b222e000102c8342eb6000000064b15922c28dc468107ea2068de663527381118fd43a3945656c000000000003d0000071080007bc9f0e217a9f89ac800047c8000000000081480005e00b182268000000236662a80008ae02e44661e76771a2606e803b20391cb0b1da4f82c416d838d1fe023caa0e00008fa18908d071e1efa0002b00a8e1a4c62922fe8ea821caa4833857d8a68613a6fe6ac0e5848614f03f400f6395a8004a9a2143b68442b9791d849d2c2044009827801d3e358810e4eb2e06b2f8272ac6904297a9352ab004209d010226a61118839861c4d92e0857f1e94a110ce0b7806969558938acea104a01937c6a42c2e1d7018c8251d8a66d918014020c88b38bc272009580f08f565bb97b88f8226423099b82d9931e2a0004208c02fc13f8386a360000470000012381287dcaf440000000bd403f63bd241694a8bbc0001e0e421af28b3c8d1243d049437b1cc41fe284a71c1a0821d8bfa49a0028383885ab3798b23d68d4a5f406c437a1f4e43b9804732072e9e1a2e81a79a109d723e6b032b4a6728622848897077728c0a92a9d83b0800085a19d20f807d24bc9dee96b800041e8000ac60b20049aeb85c680000000e6a4ae29ca5471f52000175097d81103ef00006329af069d800000019e81b92622a99ab2666a983a61b14aa492a64c7ac071869b800016821445c30c4c00009424628f765da106c000000000027ba8ef11fc000043c55a0000205a9d046a03a85a0943e6e3070cbd829584e909028d51f166f80e9a73a0000000
  | 50 => 0xc82a6580004bc15ea00000000000b008761dc06c0ad828e98e186790cb418f8d9601e8cc2a5b2118828179e9baa2e430ea60e41287741be15d003f800029d8000853800000026e23bbae428c2962a5a391b20352060a2e188217b097403d15a427e1e360b3a76e002820826c20ee84d8a645c98000000289000000005cf8a12b4827b800021da7de800045824588b003020d889b27ea8000766ae0229185641c4000037826b68658d3a0002c04986ad9e20d0254000274e531abb21b19fb00daa6ca6b50044ae684705521e90625069270e187482e889678a9baa000000002ea9e635e80005d19da873380006ec1ee867fa5326ed1cd29341f9884fad04aa5236c197ae182411ce6a93229072598ac0d7a7626a80d1aa61a0cc5130f50b1880008fb0cfe4eeaae8a7c0bb8000000089523ba0002816a85af7c00000001b4800052019c00000bd26429e86a9aa6340c000002b7050c00020d2b3a1ad0420221c9c4800000019a60bc29fa00d247a7e820187292aa657d25e22d28000b27a286000000000016c200007bc417000000019526ef956243426b40000eb80000000742000013c00000ad921ab369d840000000ace1a0293c2774590080c44706346048fba6ce05a47ef89b830e2604289afa6a4111064278000b5d9f7e00014bc9a784261dba9d20e6a1820002c361d880005efa4982cba8d223f022261285d81e6274c2832a0029a9e8e31d00000000000000000021e883e617131c881817c954af4e5ef047a782092e00024b43bb016c000286ab200000bd89f5e8bc04440002a3c8ab07ee65c98620001df2b7403e67451a7e4e1861e2de90405670000a8b1de4726078400017a20000246484968c8dbac4658e0bd679584be93386845809ef81be8000029a3e200000003cfad1a95daf983a99d2c1c1942e4d801486eb862c3a7a05c8b288628109122ba498e248fabc616b9d40724a0366409cd86ad9d2e78c8000a828b349cb9f4699f87f48e19be84b909c478301d012400000000000888000014faaee5f38fc400227609cc9eda5f2220eb7bae2c37eabc07cb0ef26de2c1240217e000028d002528580cf14be000000000000003320fe83758e5aa9c0c0c0002fa46338e40665a2f8b940000b02191e0000000000054c90ea7fa329218c6b8ae12b3489a64e68000527120e3e8117e2f112d42282a560000722550800053027a4a770f4c88f297eb0f0ace000120a98800003720ad2712234c000010a000000043b29b02e30000ad3ab96600915c000000013f0000000000093f2f301e30b420de1f6a9e4940e6f58ac600028ba0f2996c3d82788b521f1244f80003cd000006a000004100000001d700001174000233888e8ffc8a822f41ec0fca96601e81dc074a5299a428f02c8a97487f226a1ca26e919087938a248a517dc29206d
  | 51 => 0xbfa8600ad98d6e21004604b800d29cd0430000000e0000000000000039480000002a74015866c4de0000b731e70a260842a8928ae802a1ae12d22a866294164ea90ea71d26e43fb0a60ae38e108522d2e0002ef800023026aba61429ba6487ea18da00011d20000cca000158613402c00001a1800009d83ae80004f200000000000000037e2a7834eaac8b800f38000a219d4c00019805b6800027e9d8e605a440000018264394d86d1291e0cc918c70f2ca200017781de801000000002552bb000014d200000000002e38000069400000007b10524bf000000000822694ac9c3740c621af8e0c38e000025e800004a907e9309dba553001638a087200003aa31480007278000977800000024040002a6421d1f441a093142c22f7007e989e1eb904c000247600011b40002c50af610b20002bde1752566ba1a1beaad80009a213960000b5688a1598afa1658697207447525c229100001f106a80002da40b6a3dc0000ba40000cf654b97ae0000c560002e789329cd4bd61e1479fa9905e1800019aadbc55b062e3e206ae79a0d7ebfc97ee0082de40fe0a00b91a0b861a94b80e9a51c01700003360000000073613205908312af4ba08ed888c148e9c3a63079b822004d17560002e8e80f800000007dc166800051280001ad170e000000000024dc2bb1c067690aaa0000d364290f0e214914800009c87ca965c222a7ac1500d0240f1e2294426e061f213c3669bc23c78170518051e9d212f48ea198c0d1099056fac6a819204e5d62dd8114ae226580f8e7bf8c4071905ce5dea2da537a1569f59d0a7380dbc2b696b0338965e00016c67171de61779752051976e869876ab47985e2ec8f6c97597c21b2800022c2c287e3af927ee20fa000000000000002539e660001aec8a4800059d875476088ce6c191083829f9e0e3894c776299294684a82602cd87c91e62000000000000000000662000068640a000094213b482dafd64fc80229911c5e000276408a9ea80002e320408000984000043107484a4aee83f62e6076d80b22791ee00001da00000000000080a00008ac7f6809c00021087e028ca41100001d100008fc89127b30cbab25901400006386430aae0000000259a0ca8e79a7c8f184ae000132c9d40c9e5b4a1724aa110400
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x8ee87cc962040014dd0b992c4080029b617325881002c7643a64b102000a6e850c962040014db0a192c408002aba10325881000556c2064b102004ae6810c9620400b5d500192c408002aba10755881000556c20eab102000a6f855d162040014d90aba2c408012b9205745881000537428e8b102000a6d851d16204001c5ea92a2c408002b9e0554588100257240aa8b102000a6e859cd62040014db0b39ac4080029ba14735881000536c28e6b102000aae841cd620400155b0839ac408012b9a04735881000572c08e6b102005aea801cd62040015d30039ac40827b99c4353588104fd36c2ca6b102000e4f5394d6204001c9f06a9ac40827f93cc553588104ff2698aa6b10209fe671054d620413d4dd0a29ac4080029ba16435881000536c2c86b102004ae68190d62040015cb0321ac4080029ba14435881000536c2886b102000a6e85d0162040014db0ba02c4080029ba17305881000536c2e60b102005ec8304c1620400b0ff0eb2ca4080161f217765481002c3e43acaa9020058ec87589520400b17f0eb24840800e1f217765081002c5e426eca10200087f855d942040070f90abb284080123d20576508100043ec36eaa102042c3e64dd542040018bcc7baa84082631b98b75508100043f43acaa10200087c87595420400b1790eb2284080030fdd564508100061e3aac8a102000c5f7558d42040018b8eab1a8408013351c5635081002c7643ac4a102000c6f7558942040018d8eab128408013391c562508100065ab26e2a102000cd563dc542040019cac5b8a84080163b60976c801001c3e42eec90020018dc83dd9200400b1d905bb240080661f61b75480100061f326ea9002000c5e63dd520040c78dcc5baa40080021fa1d65480100443e43aca9002000c5c73595200400bcd040b2a40080030fdd564480100061e3aac89002000c9c73591200400bd5040b22400805e3761b73480100062f32ee69002000c5d65dcd200400193cc9b9a400800327593734801030e67316e690020008de8758d200400d1b90eb1a400800317dd563480100062e3aac69002005ec82058d20040018deeab1240080031b1d5624801000667b9ac49002000ccc73589200400b5d100b1240080031de1776440100063a42eec8802000cb784dd9100400196909bb220080031dd4f76440100063aa9eec8802000c7776dd510040018eeec3aa20080032dddb74440100065bbb0e88802000d34751d11004001cad0ab1a20080039561563440100072bbaac68802000e547558d1004001d2ee8b1a2008003a51d1634401002e6bb82c68802004ed37058d1004001cceeab122008003991d5624401000753ba2c48802000ea4745891004001ccea6b1220080039954d624401002e73b82c48802004ee370589100400bdc4a0b122008003b85895044010
  | 1 => 0xee729aca080161f21d53594100062fb9aa6b282000c3f749d165040094e902ba2ca0827e1f61e73594100062fb9ce6b282000c5f835cd650413d0fd0e39aca080021fa1e43594100043ec3c86b282004a768190d65040014eb0321aca080021fa1c43594100043ec3886b282000a3e841c9650400147b08392ca080021fa1c42594100043ec3884b28200087e87cc965040010fb0f992ca080021fa1c32594100043ec3864b282000a3e840c9650400147b08192ca080129da0432594100053ac0864b282005a7a800c965040014f300192ca080221fa1f40594100043ec3e80b28200887e87cc165040010fb0f982ca080162fa1f54590100061fbaea8b2020058be8790d640400147d0b21ac8080028f61643590100255b40c86b2020058bc8750d640400187eeb3aac808012ad20575590100051f42ce6b202000a3d859cd640400956d0339ac808002ad60673590100051f428e6b202000a3d851cd640413dc7421a9ac80827b8e44353590104fd1ec2ca6b202000e1f5394d6404001c3f06a9ac80827f87cc553590104ff0e98aa6b20209fe3a1054d640413fc7220a9ac80827a8fa1453590100051fc2ae4b202000a3c855c9640400956902b92c8080028fa1472590100051ec28e4b2020008be87149640400117b0e292c8080028fa1732590100051ec2e64b2020008be870c9640400117b0e192c8080028fa1432590100051ec2864b202004ab6810c9640400156b02192c808016aea0032590100055cc0064b202000a3e85cc1640400147b0b982c808017a60c130590100247a40aecaa0200587c87595540400b1790eb22a8080031d59771550100065ab26e2aa02000c5f759d5630413f4bb0f3aac60827b95c427558c100062fc3aeab18209fc5f715d5630413f8bae2baac60827f95c417558c104f52f428eab182000a5e85dd163040014bb0bba2c608012b5a077458c100356ac0ee8b182000a5e851d163040014bb0a3a2c60800387d525458c100056bc0aa8b182004ad48155163040014bd0bb92c608002976177258c100052f428e4b182000a5d851c9630400153d08392c608002a76107258c100256b408e4b182006ad5811c9630400b5b500392c60801ab66007258c100054f420a4b182000a9d8414963040014bd0a212c608002976144258c100052f42e80b182000a5d85d016304001c5ea92a4c40827e9b616539881000727a9ca73102000e4f8354e620413fc9e62a9cc40827f934c553988104f537428a73102000a6e8590e62040014db0b21cc408012b9a06439881000572c0c873102000a6e8510e62040014db0a21cc4080029ba17409881000536c2e813102000a6e85cc262040014db0b984c4080163ba1f525881000557420a4b102000aad84149620400b1dd0fa12c4080029ba14425881000536c2884b102005
  | 2 => 0x3755051041c3f43ecaa0a203a87c87d95414400187eebb2282880030f1d764505100065db20e0a0a200387c859db2144005179093b642880021f21975c85100061e322eb90a200087f87d9721440010fb0fb2e42880030f9d365c85100045e432e990a2000c3f655d32144001878caba642880022fe1f64c85100045ec3ec990a2000c3e75d93214400187aebb26428802b3a18970c85100065b3b0c910a2000e34651922144001aad0ab9c4288003556157388510006abb2ae710a2000d54655ce2144001b2ec8b9c42880036519173885100266bb02e710a2004dd3605ce21440a3cc843b2a42880026e61070485100071a328c890a2000e676518921440017630838242880030f9d365941101345e432e92822000c3f655d25044041878caba4a0880022fe1f64941100645ec3ec92822051c7471d955044001968c9b8aa08808a1f21975901101261e322eb202200087f87d96404401b0fb0fb2c80880030f9d764901100061ebaec9202206fe38649d64044049c70c8bac80880038e19365901100071c320cb2022002aba86d924044001974edb248088002f460e21901102565a38ec8a022000c7465dc540440a38f0edb2a80881431e1d865501100165c3b6e8a022048b3a85dd14044095970edb22808800b2e1d942501102459c42a84a02204adb3741c540440017a30638a8088002f86087150110024dc43a82a022004cb87650540440916710aa0a80880136c1c54150110005e8c1c42a022000fa142485404400b5c90c90e40880163d60676881100043fc2aec902200387c855d9204400117f08bb2408800a2f21176481100046fc1aec90220018dc835d920440a10fd0dbaa40880030f19375481103143f43eca902205187c87d9520440018b8e7b2a40880030fdd764481100061e3aec89022000c9c73d9120440018becbb9a40880031719773481100064fb26e69022000c9c64dcd2044001998e7b1240880163da1b71481100065a326e290220059e487485204400b5c90c90a4088016f8201214811001c3e42cec10220028bc849d8204400b1e9033b040880561f21975081100061e322ea102200087f87d94204401b0fb0fb2840880030f9d365081100062f39eca1022051c7671d9420440291790cba040880030fd9574081100061e32ae810220008bf87d90204401917b0fb2040880030f9d764081100061ebaec81022000c9e73d90204409596ce3b20408800317d9573081100062e32ae61022000c9f645cc2044001938c8b9840880031dd9571081100063a32ae21022000cb7645c42044001968c8b8840881471d9db658411001e3b3b0cb082204acb676d92104400596cec32420880038d1946484110004ebc1ae5082200587e87951650400187ee92a2ca080061f21773594100062fa9ae6b28200587e8794d65040018b
  | 3 => 0x63222000aac8258c644400147d0a318c8880028f614631911027d5b408c63222000a3e86d4c64440014790da98c8880030f9db53191100051f432a63222000a3c8654c644400187ceca98c8880038dd9631191100071a32c623222000ab4864c46444001c6eca988c8880038d19531191100074bb1a623222000f15534c464440010ff0abb2a8880022fe1176551100047bc0aecaa2200287e87d95544400717d0fb22a888002b960432d891000574c0065b122001cd6734c76244001caaa698ec488003b10c931d89100061f3a6cb3122000c3e74196624400187ecaba4c4880030f19574989100061f3aec93122000c3d75d92624400187cea324c4880030f5d464989100043f43ecab122000c3c74d9562440018b8e7b2ac4880021fa1c65589100061e3a0cab122000c5c73195624400187ecbba2c4880030f19774589100045f43ec8b122000c3f75d916244001878ebb22c488003271cf64589100045f438c8b122000c3f751916244001878ea322c488003271cc64589100062fb2ee6b122000c5c65dcd624400193ec9b9ac4880032719373589100043ec1eeab122000c3f75dd16244001878ebba2c4880030fdd474589100061e3a8e8b122000c5f75dcd62440018b8ebb9ac48800327dd373589100064e3a6e6b122000c5f85dcd62440018b90bb9ac4880021fe15735891001c3e42ae6b1220008bf845cd624400517908b9ac4880023be0973589100062fba8e6b122000c5c751cd624400193ee839ac488003271d073589100043f43ea6b12200387c87d4d624400187ee9a9ac48828f0f1d353589100062fb9ea6b122001c5c73d4d62440010fd0ea9ac4880021f21d53589100061fba2a6b1220a2c3c7454d62440018bee6a9ac488007171cd53589100066639ee4b122000cb474dc56244143968e918ac488007351ce315891000c7a43a62b1220a0cb4744c56244001caaa698ac4880023be1d62189100056641ac431220008bf845da524400517908bb4a4881471d9c7659491002c7a432e32922000cb4645c6524400517d09bb2a4880022f61376549100045fc22eca9220028bc845d952440011bf06bb2a4880063720d76549100543f43ecaa92200087f855da42440070f90abb4848812b2d9c7649091002c7a432e32122000c74655c642440070fd0bbb284880021f617765091001c3f42ceca12200087d859d942440010ff0abb2848800e1f21576509100046fc1aeca1220018dc835d942440011ef02bb2848800e1f21476509100043f436eaa122042c3c64dd542440010fd0fb2a84880021f21f65509100545f43ec8a122000c3f75d914244001878ebb2284880030f1d365545100045f436e8a8a2000c3f65dd1514406d878cbba2a28823a2fa1f64545101b45e43ec8a8a2000c7b651c151440010fd0dbaa82880eb0f19
  | 4 => 0x54400147b08186ca880029ba0830d951000536c1061b2a2051a76810c365440014eb02186ca880030f19774595100145f43ee8b2a2000c3f75dd1654400187ea7ba2ca880030fdd474595100043fc2ae6b2a20008bf845cd654400517908b9aca880023be09735951005476412e6b2a200187c8754d654400187ee8a9aca8828b0f1d153595100062fb9aa6b2a2000cb474dc565440010fb073b0ca880021fe1f63195100062eb9ec632a200087d8798c654400147d09318ca880028f61263195100043fc3ac632a2000a3f8458c654400147908b18ca880029be09631951000536412c632a200387e8718c65440010fb0e318ca88003175cc63195100053a4326232a2000d55734c4654400187aebaa6c8880028fa1643d91100051ec2c87b2220018bf8750f644400147b07b2ec8880028f60c65d91100051f42cc7b222000a3d8598f644400147f0ab1ec8880028f21563d911000557c12c7b222000aac8258f644400147d0a31ec8880028f61463d91100051f436a7b222000a3c86d4f644414787ceda9ec8880028fa1953d91100051e432a7b2220a2c3e7654f644414196cec98ec888003c554d31d91100061eba8ebb222000a3e859cf644400147b0b39ec8880028fa1473d91100051ec28e7b22204aab6811cf644400156b0239ec88800387d4e53d91100070fc1aa7b222000a3e85dcb644400147b0bb96c8880028fa1672d91100051ec2ce5b222000ab5811cb644400117d0e296c8880022f61c52d91100051f42e65b222000a3d85ccb644400117d0e196c8880022f61c32d91100051f42865b222000a3d850cb644409556d02196c888002ad60432d91100055d40065b222000ab9800cb644400147d0bb8ec8880028f61771d91100045f43e63b2220008bd87cc7644400147d0b98ec8880028f61731d91100070ea9e63b222000e1d534c7644400147f0ab86c8880028f21570d91100051f42e61b222000a3d85cc3644400117d0e186c8880322f61c30d91100051f42861b222000a3d850c3644400155d04186c888002ab60830d91102555b40861b222000ab5810c36444001878c9baac8880021fa1f65591100043f438cab22200387e87dd564440010fb07baac8880030fdd774591100061e3aee8b22200087f855cd64440070f90ab9ac8880022fe11735911000477c12e6b22200a8ec825cd64440010fd0fa9ac88800e1f21f53591100043f43aa6b22200087c8754d64440018e8ebb8ac8880030f9db65191100051ec1eca3222000e3970d94644400117b0f328c8880028fa1665191100045fc3aca3222000a3e86194644400187cec328c8880028f60c65191100071cb80ca32220008bd8798c644400147d0b318c8880028f61663191100055ac0cc632220008bf8758c644400147f0ab18c8880028f215631911000557c12c
  | 5 => 0x80121fe1d6594b102151e422cb296200a87d85dd952c400117f08bb2a58800a2f2117654b100545ec26eca16200087f855d942c40070f90abb285880123b21d6250b101251e422caa862020a3c8559140c400b7c10090a4188003725cd2008310006f0b8a401062000c3f535d365840030ff0ea9ecb0828b0f9d153d96100061eba2a7b2c2000c5d7354f658400b0fd0f2a2cb080030fdd2545961000477c12e6b2c200a8ec825cd658400b0f90ea9acb0800317dcd53596100043fc1aebb24200387f87d4f64840010fb0fa9ec9080021fe1d53d92100043ec3aa7b2420058be87d51648400187eebaa2c9080162f21d43592100143f43ecaaa42002a3e84d9554840070fd0fbaac5080021f60f7558a1000c6f43ee6b142000c5f75dcd62840018b8ebb9ac50800317e177358a100062e42ee6b14200087f855cd62840070f90ab9ac50800237a1c7358a100062fba8e6b142000c5c751cd62840010fd0fa9ac50800e1f21f5358a100062fb9ea6b142001c5c73d4d62840010fd0ea9ac5080021f21d5358a100062fb9aa6b142001c5c7354d6284003998e7192c5080163b21d3258a102151f426cb294200087f855d952840011bf06bb2a5080063720d7654a1002c3e43acaa94200087f855da42840070f90abb485080021fe157650a1001c3e42aeca1420008df835d942840031b906bb285080162f21d6450a100061e3aac8a142000c3c745955184001878eab2283080173a1c162486102a59c42a84a042000bb381509408400b3710ea0a8108152ce21541502100056bc1ac58842000c3d7495365440014f3012a6ca88003175ce53d95100053ac0ca7b2a200187f8754f65440018bae6a9eca88003175cf63d95100051f424c7b2a2000a3d8498f654400147f08b1eca880028f21163d951000537c12c7b2a2000a6c8258f654401b0fb0e31eca88003175cc63d9510006abb9a63b2a2000e54634c7654400187ae83a6ca880029ea0074d951028d3cc00e9b2a2000c5f835cf65440018bae639eca881469da0473d95100053ac08e7b2a200087e8790f65440010fb0f21eca881469da0643d95100053ac0c87b2a200087e8710f65440010fb0e21eca880028fa1272d95100051ec24e5b2a2000a75811cb65440010fd0e216ca880021f61c42d95100043f43e65b2a200087d87ccb65440010fd0e196ca880021f61c32d95100051f42065b2a2000a3d840cb65440a34ed02196ca880029d60432d95100053d40065b2a2000a79800cb654400147d09b8eca880028f61371d95100043f43e63b2a200087d87cc7654400147d0998eca880028f61331d95100062fb9e63b2a2000c5f734c765440a3ca86298eca881461fa1f40d95100043ec3e81b2a205187e87cc365440010fb0f986ca880021fa1c30d951006c3ec3861b2a2000a3e840c36
  | 6 => 0x53a42ae8b084000a76851d161080014eb0a3a2c210002b5a0c74584200056ac18e8b08400aae6821d161080015cb043a2c210016bca00745842000578c00e8b084000e375495161080014ed0b39ac2100029d61673584200055b424e6b084000ab5849cd61080015cf04b9ac21002ab920973584200053b428e6b084000a75851cd610814bcce41a9ac21029a9d61653584200072ba9ca6b084000ae78254d61080155c904a9ac21000395e0d53584200072b39aa6b084000e557354d6108001ccf04a9ac21029b99209535842053733902a6b0840a5a768514d61080155cd05a1ac210002b960b43584200047b43c86b0840008f58790d61080014ed0b21ac2100029d61643584200053b42886b084000a758510d61080014ed0ba02c2100029d61740584200053b42e60b084000a7585cc1610800b0f90bbb2a21000a2f21376544200045fc22eca8840028bc845d95108001878e8b2aa2100022f61b74544201b61f32ee8a884000c3d65dd1510800193cc7ba2a2102432d98774544200045f43ac8a8840008bc87591510800193ee8b1aa210003271d1635442002c7a43ac2a884000cb7745855108001968e8b0aa21000e1f217765042002c5e426eca08400087f855d941080070f90abb282100021f61b75504201d61f326eaa084000c5e63dd5410810d8ecc3baa82100021fa1d65504200043e43acaa084000c3f755914108001878eab22821000317dd563504200062e3aac6a0840058f48758541080018eeeab0a82100031d1d561504200066639eec9004000c6f85dd920080018d90bbb2401000333e0f76480200066641eec9004000c6f53dd920080018daa7bb240100031bddb754802000637bb0ea9004000d4c731d5200800199eedb9a4010002b3a1d63480202d56643ac69004000e4e8558d2008001c9b0ab1a401000393dd56348020007263aac69004005eca8058d2008149d9300b1a401001733dc1634802005765b82c69004005eca5058d200800bd9480b1a4010017b2041634802000733baac29004000e64755852008001d8ee6b0a4010003b11cd614802000733a9ac29004000e6553585200800bdc100b0a401002bb8dc1614802002f71282c29004005ee240585200800bdc460b0a4010003b84c1614802000764b1aa09004000ee1615412008001d92c6a024010003b858540480200145f43ee8b2e2000c3f53dd165c410987eea3a2cb880022fe1173597100145e422e6b2e200487c8754d65c400187ee8a9acb8828b0f1d153597100062fb9aa6b2e200387e87dd564c40010fb07baac9882130fdd075593100043fc2ae6b26200387c855cd64c40010fd0fa9ac98800e1f21f53593100043f43aa6b26200087c8754d64c410d0ff0abb2a9882422fe1176553100243e43acaaa62002a3c8459554c4001caaa698ac58
  | 7 => 0x5d734c565080010fd0e18aca100021f61c31594200ac3f43e80b28400087d87d01650802b0fd0f982ca100021f61f305942002c5f43ea8b204000c3f75d51640800b17d0f21ac8100028fa1643590200051ec2c86b204000ab68190d640800156b0321ac8100162f21d43590200061fbaceab204000a3e859cd640800147b0b39ac810002ada0673590200055ac0ce6b204000a3e851cd640800147b0a39ac81029a8f61653590200070fa9ca6b204000e1f8354d640814b47d0a29ac8100028fe1571590200051e42ae2b204000a3e851c5640800147b0a38ac810002a7a0c71590200054ec18e2b20400aaae821c5640802955b0438ac810016aea0071590200a55cc00e2b204000a9e83145640800153b0628ac8100022fa1f31590200045ec3e62b204000a3e85cc5640800147b0b98ac8100038754f31590200070ea9a62b204000a3e850c5640800147b0a18ac8100028fa1730590200051ec2e60b20400587c87595540800b1790eb22a81000317dd67558c205352ec3ceab1840a5e4f209d5630814bcb4413aac610297964827558c2054d67c12eab18400aacc825d563080018bf0ebaac61000393e097558c2053726412eab1840a6e4f205d5630814dcb440baac61029b964817558c2052d2f428eab184000a5e85dd163080014bb0bba2c610002b5a077458c200056ac0ee8b18400aace829d1630815159b053a2c61000297a147458c200052ec28e8b184000e1f5495163080014bd0bb8ac610002976177158c200062ebaee2b184000a9e84dc5630800153b09b8ac610003175d57158c2053d67c12e2b18400aacc825c563080014bd0a38ac610002976147158c200046f438a2b1840008dd8714563080011bd0e20ac6100023761c4158c200052f42882b184000a5d85105630801559d0420ac610002b36084158c2002d6d40082b184000ad98010563080014bd0ba02c610002976174058c200071baa4a9308409fa758594e6108001caea729cc21000395e0d53984204ff2b39aa7308409fe557354e610813d4ed0a29cc2100123da1e43984200047ac3c873084000a768590e61080014eb0b21cc2100029da1443984200053ac28873084000a7685d0261080014eb0ba04c2100029da1730984200053ac2e61308400a8ec825cd61080038bce6a9ac210003175cd53584200056b418a2b084000ad58314561080014ed0a20ac2100029d61441584200056b41882b084000ad58310561080155cd0420ac210016bca00415842002c7b43e62b084000a7685cc561080014eb0b98ac210002ada1331584200055ac2662b084000e5553cc5610800b1e90e98ac2100039554d31584200557241262b084000a76850c561080014eb0a18ac210002ade1175584200055a422eab084000ad6831d561080015ab063aac2100029de1574584200
  | 8 => 0xea31ac290003171d463585200064fba0c6b0a4000c9c7418d61480011ef0eb08c290002ad21161185200046fc1aed28a40018dc835da51480c78dce5b2ca2900033318d729452002cf4402e528a40018de83dd951480011bb07bb2a29000a2fa1276545200045ec24eca8a4000c3c74d95514800187ecbba2a2900db0f19774545200064e31ee8a8a4000c9f74d8d5148001938e9b1aa2900021fe15769052001c3e42aed20a40008df835da41480031b906bb482900167a201729052001c3f42eeca0a400087d85dd941480031bd07bb282900023760f765052001c3f42ceca0a400087d859d941480070f90a3b282900021fa1b75505200062e31eeaa0a400087e87d9541480010f90fb2a829000317dd763505200062e3aec6a0a4000ccc639db2148001c98c632e4290012b920564c85200043e432eb10a4000c5c635d621480cfad040bac42900021f61f65885200062f39ecb10a40008dc865ce21480018becab9c4290003171957388520406e4102e710a40008dd87d8e21480018bcebb1c4290003175d7638852031f3210eca90a40009d9831c12148001c98c632a42900123b21d644852000733b28c290a4000bc9831c121480013d50c38242900173aa18704852002eb5428e090a4005d69851c12148001ad6ca38242900035a194704852002ed5420e090a4005da9841c1214800b3d706382429001772a0c7048520004f4c18e090a4005dc9831c1214800139306382429000372d8c7048520006e4318e090a4000d6b531c12148001ad2a638242900030f9d365941200061fb2ae92824020c3c655d25048001938c6ba4a0900176a08174941200064f3a6c72824000c9d74d8e50480c78d8e5b2aa0900033318f72541201143e432eb2024000c5c635d6404800bad040bac80900021fe1f65901200cc3ec3ecb2024000c5e75d8e40480018baebb1c809018f1b9db658812001e373b0cb1024000e4c6319620480c399cedb1c40900161fa1e54594200061fba4a8b284000c5f535cd65080151d904b9aca100161fa1e53594200062fb9ca6b28400587c8754d65080018bee6a9aca100030fdd274594205343ec3ce6b284000c5f739cd65080014df04b9aca1002a9b20973594200062fc1ae6b284000c6f825cd650814d8d904b9aca102961fa1c73594200553741686b284000a6d82d0d65080010fd0f21aca100021f61e43594200053b40c86b284000a758190d65080010fd0e21aca100021f61c43594200051fc22e2b284000a3c845c565080014bd0638aca100029760c71594200043f43882b28400087d8710565080014bd0620aca100029760c41594200553741082b284000a6d82105650800b4f50020aca100029e60041594200043f43e62b28400087d87cc5650800147d0998aca100028f61331594200062eb9e62b284000c
  | 9 => 0x71591200066a318e2b22400387e87dd564480010fb07baac89000637a1f73591200062fbaee6b224000c5c75dcd64480018bf0bb9ac8900031721773591200043fc2ae6b22400387c855cd64480011ef02b9ac8900123d20573591200046f438e6b224000c5f751cd64480018b8ea39ac8900021fa1f535912001c3e43ea6b224000c5f73d4d64480038b8e7a9ac89027b1d1c753591200043f43aa6b22400087c8754d64480018bee6a9ac890007171cd53591204fe3a38aa6b2240018bc8750d6448155968e2a1ac8900031ddd771591200063a3aee2b224000cd773dc564480019a8e7b8ac8900031dd4f71591200063aa9ee2b224000c77751c564480018e8ea38ac8900032ddd071591200066bb98e2b224000cd4731c564480031bd07bb2a8900023760f76551200043fc2aecaa240008df835d954480031b906bb2a8900023de0576551200247a40aecaa2400287e87d95544800547d09b2aa89000297a1b75d8d200062f3b6ebb1a4000a5e861d763480018bcec3aec690003179db65d8d200046ec3ccbb1a4000a5e8599763480011bf0eb2ec69000297a1865d8d200062f3b0cbb1a40008dd8799363480014bd0b326c6900029761664d8d200046fc3ac9b1a4000a5f8559363480014b90ab26c690002b5e0564d8d200056a40ac9b1a4017ace86dcb63480c3b96e1b96c69000297a1675d8d200062eba8ebb1a4000a5e871d763480018bd0e3aec69000297a1674d8d200052ec2ce9b1a4000a5f855d363480014b90aba6c690002b5e0574d8d200056a40ae9b1a4000e1f5495363480b55b501b96c69000317dd771d8d200052f42ce3b1a4000a5d859c763480014bf0ab8ec6900029721571d8d200062fbaae3b1a4000a9f845c7634800153908b8ec690186b3a0871d8d2000566c10e3b1a40008de8714763480011bb0e28ec69000237a1c41d8d200046ec3883b1a4000a5e8510763480014bb0a20ec690186b3a0841d8d2000566c1083b1a4000ada8010763480015b30020ec69000297a1740d8d200052ec2e81b1a4000c7b651c152480010fd0dbaa84900031718f75509204c6b4106eaa12409587e87d9542480850f90fb2a849000317dd763509200062e3aec6a124000c5f7354f61480038b8e6a9ec290002b960841d852000578c0083b0a4000c5e73d9661480018bce632cc29000317d9573985200062e32ae730a4000c5e75d8e61480018baebb1cc290003179d463985200062eba8c730a400087e87d956148001878e9b2ac290003171cf65585200043f438cab0a4000c3c7419561480018b8e632ac2900030fd9774585200061e32ee8b0a40018de86dcd61480018becbb9ac2900031719773585200046f43ec6b0a4000c5f75d8d61480018b8ebb1ac29000327dd363585200064e3a6c6b0a40008de8718d61480018be
  | 10 => 0xb2a4000c5f53dcf65480018bae729eca900029b60a53d95200053cc04a7b2a400187f8754f65480018bae6a9eca9000297a0e64d95200052ec1cc9b2a4000c5d73d8f65480330fb0e31eca900028fa1063d95200051ec20c7b2a4000c5d7318f65480014ed0231eca900029d60463d95200062ec38c7b2a4000e1e8418f6548001c3b0831eca900039360863d95200072b408c7b2a4000e558118f6548001cb30031eca900039318e32d95200072c31c61b2a4000f4a328c365480c74f10c986ca90003d24c930d95200061fba4e9b2a4000c3d741d365480018bf06b9eca900028fa1073d95200051ec20e7b2a4000c5d731cf65480c74dd0439eca900029b60873d95200053b408e7b2a4000a75811cf65480014f50039eca9018e9e60073d95200043f43c87b2a400087d8790f65480014ed0321eca900029d60643d95200043f43887b2a400087d8710f654800147d09b96ca900028f61372d95200043f43e65b2a400087d87ccb654800147d09b8eca900028f61371d95200052f41ce3b2a4000a5d839c765480014db0438eca900021fa1c41d95200043ec3883b2a4000a5e8310765480014bb0620eca9018e9ba0841d952000536c1083b2a4000a7a8010765480014f30020eca900021fa1f31d95200043ec3e63b2a4000a3e84cc7654800147b0998eca9000317dcf31d95200062fb9a63b2a400087e870c765480010fb0e18eca9018e1fa1f40d95200043ec3e81b2a406387e87cc365480010fb0f986ca900021fa1c30d95200cc3ec3861b2a4000a3e840c3654800147b08186ca9018e9ba0830d952000536c1061b2a4000a76810c365480014eb02186ca9000317197735952000c6f43ee6b2a4000c5f75dcd65480018bf0bb9aca900031721773595200043fc2ae6b2a40008ef825cd65480011bd0e39aca9000317dd4735952000c3e43aa6b2a4000c5f7354d65480038b8e6a9aca90003331cf72595200043ec1cec32a4000a5e8399065480014bb07320ca900021fe1f63195200062eb9ec632a400087d8798c65480010ff0eb18ca900029be09631952001c3f438c632a400087d8718c654800147d08318ca900028f61063195200062eb98c632a4000a768118c65480014eb02318ca900031761c63195200070f420c632a4000e1d8418c6548001c9b04318ca9000395a0463195200072ac08c632a4000e598018c65480014dd0d190ca900039318e3219520005364326432a4000e4c634c86548001cb0c7180ca90003d28ca30195203153c4326032a4000f49324c065480010fd0fb2ac890003171cf65591200043f438cab224000c5c7319564480018becbb9ac8900031719773591200062fba8c6b224000c5c7518d64480018eecbb8ac8900031d19771591200066a31ee2b224000c77651c564480018e8ca38ac8900032d190
  | 11 => 0x500011df0eb10c4a00030fd9574949400543e43acaa928059a7481595525012b27d0fbaa84a02630f1db75509404b61e3b0eaa128020c3c75d9542500151790eb2a84a0162ad20565509400045f436e2a128058cb461dc54250001a70ebb8284a00034edd470509400043fc2ae5b0a800387c855cb61500011bf06b96c2a00063720d72d85400056ac18a3b0a80018f7874c76150001caaa698ec2a00023de1d61185400053a42ac230a8000c3f655d251500091f10cb84a2a02af4e15170945400145e420eca8a8000c3f541d951500090f90eb2aa2a00930f1d165545400253a40acaa8a808393e87dd5415010d878edbaa82a02130fdd875505404261e3b0eaa0a8000d3475d854150001a68ea30a82a00034e1d770505400545e424ed90a80048ee829db21500b1968c2ba642a00032b9d942c85402c75230a8590a8000c7675d8721500091f10cb8442a000e1fa1476485400043ec28ec90a80058bc865d121500412790aba242a00021fe15760854001c3e42aec10a802093c855d021500091f10cb8042a000a1fe1d65941401261f3a2cb2828051a7481596505000187ecbba2a0a000a2f21971901402565a30ae32028005db2105c640500150f90ea9acb9000317dcd535972001c3f43eeab26400087d83dd564c80010ff0ab9ac99000e1f21573593200043f43ea6b26400387c87d4d64c80010fd0ea9ac9900021f21d53593200545e43a86b26409887f855d954c80150f90eb2aa99002a2f21d64553200547a43a62b0e4000e55534c561c80090fb0bbb2a3900022fe1176547200145e422eca8e4036a3c8559241c80010ff0abb2839000e1f21576507201051e42ac8a064000c3f535d365880030ff0ea9ecb1028b0f9d153d96200061eba2a7b2c4000c5d7354f658800b0fd0f2a2cb100030fdd2545962002c3e43aa6b2c4000c5f7354d65880010ff06baec91000e1fe1f53d92200043ec3ea7b24400087f8754f64880010fb0ea9ec9100162fa1f54592200061fbaea8b2440058bc8750d64880011ef02bb2a9100123d20576552200143f43ecaaa44002a3e84d955488001878eab2285100021f60f75586200061fbaee8b0c4000c3c75dd1618800187eea3a2c3100030f1d474586200043fc2ae6b0c400387c855cd618800117f08b9ac31000a2f21173586200043f43ea6b0c400387c87d4d618800187ee9a9ac31028f0f1d353586200043f43aa6b0c400087c8754d618800187ee8a9ac31028b0f1d1535862050e5a3a462b0c40058f4874c56188141968e898ac3100039554d31586201d51f426cb28c40008bf845d9518800517908bb2a3100030f1d165546200043fc2aed20c400387c855da418806d47d0bb2483100021fe15765062001c3e42aeca0c4000c3c7559141880099acc2b9c4310003355cd61886200061eba4a9
  | 12 => 0x30f95076509500062fb9aa7b0aa0008df835cb61540031b906b96c2a80029d61441d855000578c0083b0aa051c5f655cc61540011ef0eb08c2a8002ad21161185501249f43ee8a8aa090c3c76dd1515410987eec3a2a2a82130f1d874545504243f43ec8a8aa024c3c74d9151540010fd0db92a2a80034d1d361545500069a3a0c2a8aa000d3874dc1515400187aebb2482a800e1f21476505500543e42ced90aa00487c859da215400b0f90cbaa42a80924f21175485500247c432e010aa00387d87d92505404987ce9b24a0a800e1f219729415031e36312e5282a00387c865c650540a38e8c2b8ca0a80061fe1d53d96400062eb9aa7b2c8020c3d645ce65900018bae731ccb20003175cd639964002c3f43ca6b2c8000c5f7394d659000b0f90ea9acb2000317dcd53596400043fc32e6b2c802287e8798d65900018bee731acb2000e1fa1d63596400062fb9ac6b2c800087d879cd65900018bee739acb2000317e0d73596400043f438e6b2c8024a3e841c9659000147b08392cb200021fa1f32596400043ec3e64b2c800087e870c965900010fb0e192cb200928fa1032596400051ec2064b2c8000a76810c965900014eb02192cb200169ea0032596400053cc0064b2c8005a7a809c5659000147f08b8acb2000297a0c71596400052ec18e2b2c800087e87cc565900010fb0f98acb200928fa1331596400051ec2662b2c8000c5d73cc565900018bae698acb200021fa1c31596400043ec3862b2c802287e87cc165900010fb0f982cb2000317dcd5358a4000e2e39aa6b1480058ec874c962900070fd0bb8ac5200021f6177158a4002e3d384cb30c8005c7a7059661900df878e932ac32000e1fa1772586400043ec2ee4b0c80058f4874c56190001caaa698ac3200031e595709464002c3e42eeca8c8024c3c74595519006d87ccbba2a3200030f59774546400061fbb4cb20c8000e366199641900df47f0cb2c83200038d595619064027c5fc32e120c8000c3e655c241900070fd0abb643200021fe1975c86400043fc3acb90c800087d87597219004987ce8b2e43200030f99574c86400061eb2ae990c8000cad7458b21900070fd0abb443200021fe1975886400043fc3acb10c800087d8759621900018bce6b2c43200031799573886400062eb2ae710c8004cd6615ce21900019aae6b0c43200030f997744864002e3d382ca10c8000c79655c0219000b17b09b9ecaa00061fe1d53d95400051fc22a7b2a8020c3d7454f65500018bae6a9ecaa00031d19471595400069a2a0e2b2a80008ef825cd65500151d904b9acaa00023de0573595400247a40ae6b2a800187c8754d65500018bee6a9acaa027f1d1c553595400063ba9ee2b2a8000c7553dc565500018eeea38acaa00032ddd071595400043fc2ae3b12800387c855c762
  | 13 => 0x43f43ea6b00420387c87d4d60084010fd0ea9ac0108021f21d53580210247c43a60b0042a3a3e8558e649400147f0ca9cc9280028f61953992500070eb1aa7324a000a3d8590d649400156d0321ac928002ad606435925002c5e43a86b24a000b34815d5649414587eeca9ac9280038798d53592500070eb1aa6b24a020a3e859cd649400147b0b39ac928002ada0673592500055ac0ce6b24a026a3e851cd649400147b0a39ac9280828fe0d53592501070fc1aa6b24a000a3f855c9649404d47d0a392c9280028f61472592501051f42e64b24a000a3d85cc9649400117d0e192c9280022f61c32592501051f42864b24a000a3d850c9649400156d02192c928002ad604325925002d5d40064b24a000ab9800c9649400147f0ab8ac92809a8fa1471592500051ec28e2b24a000a9e831c5649400153b0638ac928002aba08715925000556c10e2b24a005aba801c5649404d5730038ac9280022fa1f31592500045ec3e62b24a020a3e85cc5649400147b0b98ac9280038754f31592500070ea9a62b24a020a3e850c5649400147b0a18ac9280828fa1730592500051ec2e60b24a002a3f86591549404d87eecb22a9280821f61b705525037e1f326e0aa4a077d3b74dc1549412b878eb322c5282561f21d5458a500161f3a2a8b14a000c5f53dcd629400b1d90e992c52800a2fa137158a500045ec26e2b14a00087f865d2529408587cc8ba4a5280030fdda6494a5000717314c9294a042a3f865925294001c5ac8b14a52818a1fe197094a500061f322e1294a042c3e64dd5429400187eeab2285280830f1d56450a5001c9e43aa8a14a002a3f86551429400187eecaa2852820f0f1d6645865041c3e43aa8b0ca000c5d7354d61940010fd0f292c3281469da06525865002c7a43a62b0ca000e55534c561940010ff0cba4a3280eb0f99174946500061fbb4c928ca000e3661992519407547f0cb24a3280021fe1d629465031e37392c528ca000e356458651940a10ff0cb84a3280030f99170946500061faa2ed20ca0058bc84dd9419407587cc9baa83280030fdd564506501061e3aac8a0ca0028be845db219400187cc8bae43280022fe1974c86500045fc3ac990ca0008bd87593219404187ceab2643280030f5d564c865000636baac590ca000c3e645d6219404187ceab2443280030f5d564886500064f39ac910ca000c9e645ce219400193ac8b9c43280133598573886500063abaac310ca000cd573586219400187cc9baa43280172e9c1640865001cbc42ae010ca000cb9645c02194001968c838ac8a80034d150715915000536c2e65b12a000a6d850cb62540015d300196c4a80022fe1171d89500145e422e3b12a063c3f655d062540011df0eb10c4a8002b320d62189504b43f43ec8a92a00087e86dc552540070f90a3b284a8
  | 14 => 0xd879d5638853dcae213aac71080317e1d7558e214fe2fb8aeab1c429fc5d715d5638853fcae20baac710a7a97a147558e210052f42ee8b1c4200a5d85dd163884095ad03ba2c7108b6b56077458e210052f428e8b1c4200a5d851d16388401c3ea92a2c710802b5e055458e210256a40aa8b1c42acad7815c963884014bd0bb82c710802976177058e210256b40ce0b1c424dad5819c1638840159f04b82c710a02b32097058e210052f428e0b1c4200a5d851c1638840153d08382c710802a76107058e2140567410e0b1c4200acd821c163884095ad02382c7108b6b56047058e210066cb80e0b1c4204ad68114163884015ab02282c71080297a174058e210052ec2e80b1c4204ad68110163884015ab02202c7108031d5977154a210043ec36eaa144200c5e63dd542884850fd0eb2a8510a561f21d6550a210062fbaac6a144200c5c7558d42884099a8e2b1a85108033558f7150a2101c3f42ee8b04420087d85dd160884039ace698ac1108039554d31582210061eba4a9b2a4200a6d8295365484091db05b9eca908061fe1d53d95210062eb9aa7b2a42028be87dd1654840187ea7ba2ca908030fdd474595210045fc22e6b2a42028bc845cd65484011f700b9aca908163e201735952100c3e43aa6b2a4200c3f7454d6548545878e8a9aca9080317dcd53595210061ebaea9b2242018bf8750f64484010ff0ab86c89080e1f21570d912101c3f43eeab22420087d83dd56448401878ebba2c8908021fe15735912101c3e42ae6b2242008fb805cd644840b1f100b9ac8908021fa1f535912101c3e43ea6b22420087e8754d64484010f90ea9ac8908021fe1576551210045fc22ecaa2420287c87595544840547908b2aa89082a3da1b71551210061e3aec8a124242c6c76dd5424852b8d8ec3aa8490962e92055450921006b3ba8e2a124200c3c74d955148401878ebb2282908022fe1175d81210145e422ebb02420087f855d360484070f90aba6c0908039554d31d81210047dc3ac0302420087f835d4604840b97420ba0c09080317a1573181210062ec2ae63024205ccf205cc604840b9b440b98c09081733481731812102e6b882e63024205cd5105cc60484070ff0fa98c0908021f61f531812151e1f3a6a63024200c3d74d4c60484038bce7a98c090803175cf53181210043fc3aa6302420087d8754c604854587ce8a98c0908030f5d1531812100e2f39aa63024200c5d7354c60484090f90ea9aca1080317dcd535942101c3f43eeab20420087d83dd564084010ff0ab9ac81080e1f21573590210043f43ea6b20420387c87d4d64084010fd0ea9ac8108021f21d53590210245e43a86b20428687f855d954084090f90eb2aa8108122f21d645502101c3f43eeab00420087d83dd560084010ff0ab9ac01080e1f215735802100
  | 15 => 0x5382cb908021fa1f40597210043ec3e80b2e420aa6e8210165c84014db04202cb908021fa1f30597210043ec3e60b2e420087e870c165c84010fb0e182cb908028fa1030597210051ec2060b2e420aa6e820c165c84014db04182cb909669da0430597210053ac0860b2e420a8be87d5164c840187eebaa2c99082a2fa1e43593210051f42c86b264200a3d8590d64c840156b0321ac99082a2f21d435932101c3f42ee0b26420087d85dc164c840187eeb3aac9908028fa1673593210051ec2ce6b264258ab6819cd64c840156b0339ac9908028fa1473593210051ec28e6b2642a6a3d8594d64c8401c3ea729ac99080387e0d535932152d1f428a6b264200a3f855c564c84014790ab8ac9908022fa1f31593210045ec3e62b264200a3e85cc564c840147b0b98ac9908038754f31593210070ea9a62b264200a3e85dc164c840147b0bb82c9908028fa1670593210051ec2ce0b26420aaae829c164c840156f02b82c99082aaba08505932100556c10a0b264200a3e85cc164c840147b0b982c9908022fa1c30593210045ec3860b264200a3e850c164c840147b0a182c99082aaba08305932100556c1060b264258ab6810c164c840156b02182c99082a1f21d65553210545e43ac8aa64242e2e64dd542c852bc5cc83aa8590802abe195450b210061e3a2caa8e42008bd86dd151c846d87ccbba2a3908030f59774547211b45f43ac8a8e428e8bc8759151c84018dacbb92a3908021f61b75507211d61f326eaa0e423a87e8759541c85070f90eb2a83908030fdd564507210061e3aac8a0e4200cad64dc941c840517d09baac1908022f613755832101c3f42ee8b06420087d85dd160c84018bee6a9ac190807171cd53583210547c43a60b06420487e87951658840187ee92a2cb1080317d4d73596210243f43ca6b2c4200c5f7394d65884090f90ea9acb1080317dcd53596210061fba4e8b2c4204a74815d1658840187ae83a2cb10a7e1f61e73596210051f424e6b2c4200a3d849cd65884018bee739acb108129da0673596210053ac0ce6b2c4200c5f835cd658853d0fd0e39acb108021fa1e43596210043ec3c86b2c4204a768190d65884014eb0321acb108021fa1c43596210043ec3886b2c4200a3f845c9658840147908b92cb108021fa1f32596210043ec3e64b2c4200a3e849c1658840147b09382cb108129da0670596210043f43e80b2c420087d87d0165884094ed02202cb108029d60440596210043f43e60b2c420087d87cc165884010fd0e182cb108021f61c30596210051f42060b2c4200a3d840c165884cf4dd04182cb108029b60830596210253b40860b2c4200a75810c165884070fd0bb82c9108021f61770592210247a40aecaa4420487c87595548840547908b2aa9108031d59771552210062fbaceab1c429fa5
  | 16 => 0x494a410543ec2eeca94829593e87dd5429053187eedbaa8520a5b0fdd87550a410069a388eaa148236c3c755954290401a6eebb8a85208022f6187050a410043fc2ae5304820387c855ca60904011bf06b94c1208063720d729824101c3f43eeab048200c3e84dd5609040187b09baac1208021f60f75582410061fa16eab048200c3f75d5160904010ff0ab9ac12080e1f215735824100477c12e6b04820a8ec825cd60904010fd0fa9ac12080e1f21f53582410043f43aa6b04820087c8754d60904014790aa12c1208030fdd542582410062eb9ca7b2a820187f8754f65504018bae6a9ecaa0803175cf63d95415853ac0cc7b2a823487d8718f65504018bae631ecaa08021f61e73d95410062fc1ae7b2a8200c5d731cf655047547d09396caa08028f61272d95410043f43e65b2a820087d87ccb65504010fd0e196caa08021f61c32d95411d51f42065b2a8200a3d840cb655050d4ed02196caa08029d60432d95410053d40065b2a8200a79800cb65504750fd0f98ecaa08021f61f31d95411d51f42663b2a8200a3d84cc765504018bee798ecaa080317dcd31d95414351ec20e1b2a820087e87cc365504010fb0f986caa08021fa1c30d95410043ec3861b2a823aa3e840c3655040147b08186caa08029ba0830d954100536c1061b2a8286a76810c365504014eb02186caa08021fe1573595410045fc22e6b2a820187c8754d655046d87ee8a9acaa080317dcd53595411b61fb22e632a820087f87d8c65504018bae7b18caa08021f61e63195410051ec24c632a82afa758198c65504010ff0eb18caa08028fe11631954101c3f438c632a820087d8718c65504018bae6318caa0807179cd53d89410062eb9aa7b1282aec757119662504010fd0fb2ac4a08021fa1c655894100477c3ac4312823ac3c74d95515040187ecbba2a2a08db0f19774545414343e436eab02820087e87d9560504010fd0e32ac0a0ab71ddc4655814141e1f3a0ca30282008fb8758060504038bce6a98c0a0803175cd53181410043fc2ae4302820387c855c860504150fd0f2a2cb908030fdd2545972102476412e6b2e420a87e8794d65c84018bee729acb9082a1f21d53597210062fb9aa6b2e4200c3f749d165c84154dd053a2cb908029b60a74597215343ec3ce6b2e4200c5f739cd65c84014df04b9acb9082a9b20973597210062fc1ae6b2e4200c6f825cd65c854d8d904b9acb90a961fa1c73597210553741686b2e4200a6d82d0d65c84010fd0f21acb908021f61e43597212cd3b40c86b2e4200a758190d65c84010fd0e21acb908021f61c43597210051fc22e2b2e4200a3c845c565c84010fd0f98acb908021f61f31597210051f42662b2e4200a3d84cc565c84018bae798acb90803175cd31597210051f424e0b2e4200a3d849c165c84154dd0
  | 17 => 0xa8400c5c655ce61508099a8c2b9cc2a1003355cf61985420043f43ecab0a840087e87195615092b878e8328c2a10023de1d611854201476c16e7b02849887c86dd560508010fd0fb2ac0a1003171cf65581420043f438cab028400c5c7319560508018becbb9ac0a10031719773581420063bb2ee2b028400c7465dc560508018eeca38ac0a10031d19471581424ae1f3a0ca30284008fb8758060508038bce6a98c0a1003175cd53181420043fc2ae2302840387c855c460508014db0b992c5288029b6143258a5100556c2064b14a204ae6810c962944015d300192c528a5a1f21d6454a510043ec30e0a94a20a8bd84dd9429440187ca9bb28528a631b98b7550a510247643ac4a14a2008df835ca60944031b906b94c1288021fa1e54582510053d404a8b04a26287c87549609440147b0b21ec8a88062fe1d43d91510143e42ae1b22a290a3c8654f645454587ceca9ec8a880387d8d53d91511c51f42ce7b22a200a3d859cf645446d47d0a39ec8a8a428f61473d91514855b408e7b22a236ab5811cf645446d47f06a9ec8a88db87e0d53d91514851ec2ee5b22a238a3e859cb645440147b0b396c8a88da8fa1732d91510051ec2e65b22a2008be870cb645440117b0e196c8a88da8fa1432d91510051ec2865b22a290ab6810cb645440156b02196c8a8802aea0032d91510055cc0065b22a2368be87cc7645440117b0f98ec8a88da8fa1731d91510051ec2e63b22a200e1d53cc76454401c3aa698ec8a88028fe1570d91511c51e42ae1b22a290a3d851c3645446d47d0b986c8a88028f61730d91510045f43861b22a2008bd870c3645446d47d0a186c8a88028f61430d91510055741061b22a200aad820c3645452156d02186c8a8802ad60430d91510045ec3cc6322a200a3d8598c645456756b03318c8a88022fe1d63191510051fc2ac6322a2a3a3e8518c645450947d0ca98c8a8a128f21953191510070fb1aa6322a202a3e86d915454521878edb22a8a8a434ddd071551512843f436e0aa2a26fc3c64dc1545452b0ff0eaa6c4a880b0f1d154d89510062fa9ae7b12a2b2cb571192625440117d0fb22c4a88022fa1c64589514ae1e3a8c8312a2008ef8758862545090f90cba4a4a890b0f19174949512151f436c9292a290c3e76d92525450987cec324a4a8a130f1d8649495100716310c9292a200e2f64d8a52544a10f90cb84a4a88030f19170949510243ec2ced212a242c3c64dd5425440187eebb2284a88db0f1d7645095101c9e43aa8a12a202a3c865514254401878ecaa284a8a422f21b74581510045f43ec8b02a2008be87191605456396ee2322c0a89bf0f9d464181510047dc3ac0302a26f87f8755060544018bea6b98c0a88021f61e52181510243e43aa6b2c8200a3f8454d65904018bee6a9acb208030f5957
  | 18 => 0x20000000004000801c0000020008010004000000000c00000000100040000010000004008008000801400400300000040000060010008000000002000000000000000040160020028000000000007800c00286c77659c662550011df0eb10c4aa2629be1562189540062fb9aa7b0aa8018f7874c76155001caaa698ec2aa21b17d9573185540047bc3ac230aa886a7785584615512156f08b08c2aa00a1f61773d81545143ec3aa7b02a8b5c7975d826055169972e9b04c0aa21b1dd9471581544865bb20e2b02a8008fb87580605508547d08a9ac92902a2f21d43592520051fc2a86b24a400c5d7354d61948014eb0a20ac329002b560c41586520557341082b0ca400af18010561948151e90e98ac3290039554d31586520045fc22e3304a4028bc845c660948010fd0f2a2c12900317d4f73582520547c43a60b04a46287e86dc154549070ff0eaa6c2a900317dcd53d85520047bc3ac230aa4008fb8758060548df0ff0eaa0c0a900317d4d73181520045fc22e2302a4028bc845c460548150f90ea9acb2100317dcd53596420056ac18a2b0c840a8f4874c56190801caaa698ac3210021fe15719824201c3e42ae3304840387e87dd5609080187d09baac1210030f61375582420043ec1eeab048463c3f42dd560908c787a85baac1210021fe15735824201c3e42ae6b04840a8ec825cd60908010fd0fa9ac12100e1f21f53582420043f43aa6b04840087c8754d60908151f10e982c1210028f61253d95420062eb9ca7b2a840187f8754f65508018bae6a9ecaa1003175cf63d95420053b40cc7b2a8400a758198f65508790fb0e31ecaa1003175cc63d95424c51e43287b2a8400e1c6350f65508010fb0f39ecaa100317e0d73d95422151f420e7b2a8498a3d841cf65508018bae639ecaa110a1fa1f32d95420043ec3e65b2a8498a3d84dc765508014bd0738ecaa10029760e71d954221536c10e3b2a840087e87cc765508010fb0f98ecaa110a8fa1331d95420051ec2663b2a8400c5f73cc765508018bee698ecaa10021fa1c31d95420043ec3863b2a8498a3d841c365508010fd0f986caa10021f61f30d95420043f43861b2a840087d870c3655088547d08186caa10028f61030d95424c53741061b2a8400a6d820c365508014ed02186caa10029d60430d95420043fc2ae6b2a840187c8754d65508018bee6a9acaa10021fe1f63195420062eb9ec632a840087d8798c65508014ed03318caa10029d60663195420043fc3ac632a840387e8718c65508010fb0e318caa1003175cc63195424b51e4328632a8498c3c76d955450931a5eea392a8a110b0f1d365549420061fb2ee8a92840a93c8755152508154790caa2a4a102acb209545494200c7bc3a63b0a8400e55534c761508018bce7b2cc2a1003179cc65985420062fb2ae73
  | 19 => 0x1e00000000000000000008004000002000000000000000180040040000000000000000000801c000002000000000000000000000000020010000000000002000001200200000380020000008014002000000001000000300080040000000008000000001001000c0020000000000004001000001400400000000040060000008010000000000001c00e00400080000080000000004004001002000000200000000040020020008008000000000001401600400000000000000018008002000000000000200200280080060010008000002000000800c00000100000000040020000004000000002800400a0000000000002000000800800800300000000000000020000000000000800c00400000000000000030008004022003003000c00200100000000020010010004000002002801000a000003000c002003000000c00800000100000040030020008000000000000000200200080040060020000008004001000000800200000000000020000000000004005000800c0020010018000000002002000001a00000180000000000018028000000000800c000001001000c0000000000004000001000000000c0000000000000000000800c00000400080000020000018000000000000800000a0000000000008000001000000400c000000400000100080080000010028000000000000000401200000000000140010020000000004000000400200400100040000000000004004001002802001600000100000020040008000002005000000400600000100000020010000000002001000801c00000000080040040000008000000001000800000200000100000060020000010000007000800400c0030000000000003006000400c00000200000000020000000000000000800400400000100280020050008008004004000800400200100100100000020008008006011001800400000000180000020000010000000010000800000a005000800000600000000000040020000004006006000800000000300080000020000010010004000000800c000001001800000e003000001000600700000080020000010004000000000000c000001001800000a00100100000020010020004004001000000c000004000000c0020060018004002005000000400c006000000000400000080000080000030000000002007800400a00000100040000000008000002003000000000200c000000400400000080000040010048000008000001002400000a0010000000000001000c0020000008000004003000000000000100000000000030000004004000002000000000000080100040000000004000005001000000c001000000000e001000000000000200100000000060000000002002000000000c00000080000060020000008000001001000400000000
  | 20 => 0x3ca00000000002ab9a748de000000000000000041694ac0003920e800000005ef33a00007f22c800000000000000001c2c00000000000c80000000000ccc0001be00000000000000000000052760438800110200000014d523a00011c9e9800000000000000002b100000008740001238dc800053a00007a80480000000140c2c32b00000000000000000000000000000173c4fa00000004680002660000000e5a50b000000000000000000002aa02021e16e940c4c7389814ce7000025100000000000000000e2e00000012f01664f10000000456000000000000074100020040005ed00000000000000fe0000000000000200cc625a200007703f64f600000000000000001d3c68416900023600007070520000ddc00000016800000000000000ef400000000000004ec32990d800056800000000004ce46d8d587e8000000000063e0004e50e7000062900007740000000001a9ca828eb17b8ba400014136d913c0000000d5000000000000000000004b2519800081e42900000000000002c100000000000000000000000000101c0000fb0ab80001429ed000251000000030d0000eea0001e6a81c0e2028000228c0620000ec044c1ba0000000f640000004f09cc03fa00019889140000004828000000000000000000016700000000000000002704b4c0002f180000007e2000081800025400013e80009a9000111c00000002080000d471c0001458000000000000000000040316fc0000003938000c4c0000000000000000292a27101241f00000000000b10000a2400000000025a0000000000000000000000000014422015188000000174000024800000000004a0000000000000000000000000002444de04726985700a5000154c00009051800000005cb42a00013240000000000000000000235400000017987e13b623a30584ec00046549d0ebc3dc00000000000001760000000000000106998080c2140000000000000000800e000000000400000100080080040040010014002002001800000600000000280000020000000006003000000400000000000000020000000008000002001000000000000000100100020000000002004000800c00e00500100000000040000010000000000000400000400000000000000008000002000000800000c0070020000006002002000400000300180000020000000000006000000000000200200080000020000008008000002000000800400800280000000040000008000001002800000000400000000060010000014000000000002000a00400000000000030018000000000000001000000200100040000000000000000002001800000c0010008014000001000000400200200100140000080018000000000000800c01000100080080020000000000010001000000000000100100000
  | 21 => 0xe00019f95f50b47c900000000000002a000012fc0003b69a3cf4a35019d8000aea4482e026d80000004c29dd08e8000000000143406c1b20c386a443d00022a40000000001240ab44952138000000000000214017c0003de8000a3e92f33f800000000026200002c2000196800073677839700000009550000df87a257b0dd000000000051621dc0008694a4213425695d323232c57826c3528a480009c31b50810000000000000000000000000000000b6316000000000000000000000001898000000000226000000000000000000000001220000000000121800000000022300000000003be2734a1400000017a400000036a105c0007d90001b680000000000000000632000138c0005ab0711978470047412858935a0000001b7c62000049f000000060a00016cc00047e17d92e8000000171000111600000008442607261c721e400000000000000005bd00000000764681ba188cd560003dc80009c800000001e8c8600000000000000003a900013929bc1a585407845f000000000000004f2279c0000003c8238c00059d3d400002d0666175158d0ae2b0000051c0000000000000e0a00029c0000000000250a37c00c0001a200001ac6e132d000000089b24b02580000bb0a886bd3f06eb2a511a89100004d880008ae00000020e88f01bd46f24c80002513ed00000000000001bf0d280d10000000000000000285c00008113d80000000000000b281746f100000004ba00000000000007122e4800000004e1f1800000000000005700006c1000071432482e2e80e8c7761ab00000380008fc0000c213061373349cac83067200000005405e229827b000089500014880001144f50000fac0003f6a2ec00000030280000000003e51e154380000000000abc000000114d16c0003b089b80009da28f26240001354dc1068b6a0000000000c440000000b98000000000000119818c390036c00000000026180000cf0e404b00001494fa94f80009e6000000000000015b80000006301c2800000018e000000000000004680000002e4000205435200000000004e88ce0620000000000000000000000034580014483eb00025240000000001300000414252800050e0000000000000000000000000063c00000000004fb23680000002d502ba24c0009152ae16951a6000000000092e0000000000d7035d0001a3400076a11f0f611880a3000000000000000005c43ac0000000ca12d600007e91e400000000001200003c500027f506000000000ccb348f300023653dc00000000002fc3bf0000000bf00f325a06d400099c4310e046a279b00027dc00035500000002b62c0000211c0000000eb98e8000044194800077400042f9ad8034000000000000000023f9e9cd1283b00027d800000020da480f9e96a000000000036900010000000
  | 22 => 0x2f98ce06248d000000000001fe2700ed8f3a0450c42458000000000000000054d000063c0000000002850b080001aa241cd428bf27c9468ffc5342a20490b209a2000234488a000000000000000000000000001ce2d098389c473100a80000002991ef28d000005100000000000000000000000000000000000032f00000000000a60000000000000000000000000019e198c9622964c000000003bc4f583a509444e2421b3c00083600010740065e01478c6cb5e0432af83dc15c3a04a280006c276c000275c2300bf13f9ea40004d513b00012c442137300000009f900000000000000c480008b6000000205103200028088a437882036185f40003e53f006c83981a500000005ec0000000a3819800000017980000003831d50020000000000137a66c28180000000542b4924c6c40000000e5c000000129000000096700027a03a634926100004f89dc0000c1836878047c800028a4c12f41d7c0000002cc800000062f0000000f5c00000000005e40000002304c7a51b0512154000000000092000000000000008b20003cb000000057c4e6000000073d00001a40006a21d3a5c524a07422f0f5ce8e00001e9d1800000000000004f012047605bca243ac0fa80003f4000000000061a0000500000fa21290000d6070078639a00009300003169014000000000000000000000000006a600000000000008b500000000003b1199217800000000000002da0000002228000647181000142635747919240000942b680000003e635ea7080000003c9800000000000000012bc3f827500007340001e9800000001d3cc80000d017a00000006b80000000000000000000000059a0000f0102491800000009540000000000000000000000088800000036a8000728000023000000000035a800000054500000000000001b380000008d7000000000000018501980000004b2078453e4403601864aaa9983c20d8c498a250000470b3800038a00a892200000026e54465760000000000000000000134e00015c8000000000000252c0005f7000098cdc071b1b792ed084a1e10d0f54000000000000058800000007fc380000000000000083d2a48000000000000000000077d000000106600000000011f000001a9e5400004b126800000003a2eb9aa00001ef00000009a08a10000000d520000000d207e685c000000013640a11a800097000037c11084e209100000000009b000007d02e60c54eb00000000002ab000000081e00000000000004df000000080200007c4c7096f00013600000002fa800022ea0b42225f045e00044712bc2d60000000f30f0400037aa76504602f2ae818c00063b50514e47b88044f2976c0007af0000000000000000000000064200000000c400004d19393ba0003669cbc0001c2000000112c2530000
  | 23 => 0x80009488433ef800000000000000005f000000000000008c800000000000002f600000007c700000007920000000bf40000004ca00003a83b20000000000093000263000029a33b80000009263e300640000000001e5c00059200008c800000051700ac00000000000000000360000000000000000000010c000506800000028c3ab0000a622c54e7a04879c00000025680000000001370f3e0002c188800009ab18e80000000bd000240400000000000012687be070a2340008a50000000eb6a09000000000000001f9e600000580c680000000003fea2f0f865721018aa49027a032200000005fd00000005448404bd2558000000173a2c47ee711000000000000000000012a04f2000000000000000000002b253b000000000000007a97f91486794b9800000000000000006e222619d00000002000001d0c0000000000d04000000093800000000002605002ee65d000134862e20714422a0e3e0000000000ad80e0000000091c00000000004f2000042000000000000018552cc08f2dc08cc000709114000000000000000002ea5ff000000000000000000000004f0000000000000000008300007d0000000000000000006601bc2501f41cdc7703e439087682c00000000b50000000000000000000000019580000005130d78dc600000000000000001fe86fc0000000001b780003110000c000003260e79174000000123187c8380000001c20ace7f11d2a394cae8ba120a09c0000000000000000000000000000000000019f000000011a26d48ac0000000000000000000000051400000000000003ff00000008c43fa0860000d780004c800080006b700006180000002941655332413000000000000000000000001a846d13f85420000001ca832e98b34d052d31e000191000000000033b03a800027322880000000001df23fc0000002bb800000014a0000000000000000000000000034c00000009e90001b2040a0000119a8000000039e00013480001b2963c00000000000001e00000e4800000000000014bc6066d23408c792e000000000000000ef4fd8000000323405800138c00000000002e422c0000000000000000000000000000000009dc0000000000000935284255000092b0400e2400000000000000000002d2046c00013d3d203944b640c1d700001aa2851d11a5cc0600000000000000000000000f4623d238998800005f00000b0e8a8652d18000d603bd01393acb3c0000000ecc0003c71f90000d1c8001699e68a4270100000000009c82cc196532e3982b980005a2000000000000000000000000000000000000a080000001dec000000000167c00084b00000000000000000ea4d2400000023a000060f0000000dde82c45380e400000000000000007003fa800000000000014a446000000000000000000000870000
  | 24 => 0x44cb1bd1e44de67cc2008788d549ac000089c74248a0850b48b287e600000007485813da04bc32a000343914800000000000007326f73fb00000000000000aec0000003868000e9a00000000010100001551a98000a2a00000014065154068000000000000000146a58828e8e4400000000000003c88e00001b910f604f14e0000000000000000000075a0001b5c0000000000000ca8000000000000087d0001644000000000000000000000000009ae61c0002854b780b53961824e520003f20000780000000000116e2c702d1d20b525e5000000000000500000000002120000000f3836645a00001d60000000000000000000000000017c3ef00000000001879b280000000000000d8e0001be0000c6a40200000012e400000016e43223ec0000048bf606d3279fb0f9a00040b90cc0000000001be43160002b780012808660000000a0e000000041c0001f3000000073e00038500008e600000000004ce00000017590e0000087a5380004100001ef05d66d133980000000001bf800000000000000000004cd18d000000000024480009f000014ba4b43e000000000000007ff00000008ec4230001d44c9892400018d05c684f218a0bd0f877943b1b7400024a00022cc00010816c80000004a8000002400000000000003e40b8192882cc28307407270124e0522400db80008880000ad4cce0000000000000000000284866000018c043934273b00000004360002d608fc0007160000034000000000000000000000000000000002970000bf80fa0e21d744c22cf2e724dcc1a1650a7000000047519c940000000000025700360000b300012b000000000008b470c0000000ae8000000000079400047da41000086800016c8eec0004e8110ce742d609504646be4f300000000000000000000000000499800000000023013240005430d6a104b500673fb939400000000012a489a38b00000003bc9ba0000000f0e66a00000000000001c4000000000019b80014820000000b38ea009f21700000000000000000000000000000000000000018e400000000023dc000000000000000000000000000000000000000cfc00000005e033600044100014521523bf1edc21607741c03b00006ba0000001228000000000000081618e16280000000000000be274900000010b21eb00026a000029300000000000000001d7842c0002b3289c0000af000000000096e50123f400037d0000bbc20800000000009b684631280005066fb081000000000015580000c20001078000e7c00010480003d84252018854000000000000136813f43a1584b861e717e10fc00067b2518bd4882a2f49516582a82b42fc99d400000c1848000000000443000050895300027c49fa000000116000066f000092400036b447a65486053323700003944a012580000000001a3
  | 25 => 0x68000000000216000091e00000020986ea5d94590000000000000188000000000000000008be48c0000d143e1000000078697b0a222440000000d880501969f23f0959000067d440000022235b2d6800000088c0000000d627fb13284480007c424f2390e440004028000000000000002800019d2d81cc80005050000000e666ec0001714f3c0000000c1400000000028fc00000000000000007e8000026442e00000000005bc5023c094f423e0004ef879800000000021847c489f00028f81301b60000b6800000007380000000000001dcc00031947d0000000000000000000050f00014312fa0000000000000a19332000000000000011c0000000442219000090049800012440000000754000000000000000000000000010f04f50000000808000000206c0000003df800046e00000000000000000bc8fd8e1c000000221c0009790001438a6400000022c0a1213e51d0e400f200000020f8000000000000000078800000005fc0004cd97280004721d522400003140f420c889600000020fc0000000000fa8b9a340000069067a000000000000000020c8000894000000000000068000000002fe02600000000006c200000001be0000000000d3e91751c800000037600000000000003428000000000000000000000000001d87b400000000000000000000000358000009800000095b178035c000438000181c6f6000000000000000000000004c40ac000000057a62b02e00000000004e7118c000000000000000000000000000001a03b813bce6a0000000000a9600025700000000000000000ed25da0001be8edc2940000000e9c7d800000000000000000000000678411244c000000270800000092c3c48de4d9c84c44d0134000000274800000000000000004b85360000000000000000129c000000449076c0000003e283a00007fc3430000000000000225c5b09d13e000006981701f883e076e92924c96dd27819000009c87ce00b38e80000f889e07912e400000000000000008583f592f8ece4b024e80000007d70001b5811000024180000000004a1148d0ea9120b71600ff0000376a5492c200000000000000000001d713084fc3f820300000000000000db89aa00000000000004738a8d00e10d000000000081c000040c0008b800000000007e31f70000a3890d4318010da664a450174c0000002ea80000005874a50000bc80000608e4c1040000000000a5a00024900006165be060172136e0000000000d469af00003413a4000348144000000038d0968c5c00048595c43ee66b0000000b122bf30900006945260002444a9c0000000000000000000153026461d02c80007a05dc34a8e2800003e27f8000000055320000092800000006ec6f078a00015a80009360000000000a2b0001d98000000290000000079200000005f
  | 26 => 0x9e98e0000000262000000000000000000000000006bb00000000000000000000000000000000000069300000000003163e400000006284ff8000596304000000012a0000001d0800000000000000000000000000000688000000026691f3659ec400063e21200011fc0000001dfcaa4455000000000000007b000114c3c8000000075034300000003d23f00000000000000000000000001e3000000000001000000000000000000004bc00020f2350000975000000000000000000000000000002678fe60000000000ab600000028002bc00000008780006910000000000000319800000000000007b40006b90460aa000000000026681cc54600000000004e6000000000074c39c800000000014590ec0002f449e9d90000000000135024c477000000096a0ca00000000000004d1800096e00000002c800013809700000001cd0001b24000000415000102058b00000006d07ac00000000000000000000f1e1533ea80010344a600000000000001a3240c0000000000000be43274bb000000006000000000000001cf00000005504c380000007830830e5850000048483f84040b7477a7609ac0001c626cc75607f000136533e00000000000008aa000000000024f1709d60000000000253108a6fd00000000000000000a441b200013492706c074a00000000009f00000000ba815f23381bc000000000000000093b000000000066e0698ca93044544df868c00000000000000008c00000000640000341a57d1ba00014a800000000042b00000004b30000614a6e2ba000000000000000000010fc0000001fa8000000000000000000016d80000000000000b70b1a0002d8800025a0000001f380000004560000b4e000000027918a0ce3821fe400005600000000000000001e387be710000000000000047800000006611ce8000c0c7030002328000487255000090a0000001e341e891b4a322244620000000000c4200000000000000000000000dca000338049400021930100000006b44f00000f64000000000000000000000000006d92e200012ae7ba0000000000000000000000004929e20f04ae0000001a6c0000000000000e8027549f800000014f0000000000000511000000009d091a33c000000000216c000000000000000013944a00000000001ff04d0000960000088c000000302000061800000010f8000771483000000000000001ec00058e00000000004bd0001840000699288a1cc00000000000000000000e9000000000000000000002b3000029c0001c700000012d204a00000000000000c9800000000000000000000000000000000000000000000000000000007ba00030f00012fe000246a17420000029600000005eb00021bc00000006400004d44ed0c208b90560000001b1000025f0000000000000000007087233532
  | 27 => 0x1f9c00019e000072c000000000089000000020709587960114840000000993000000074c000381000000000000004d80000003fd00004fc5510000000000000000000110a0002d5283ce9600023480013a67f20dca37053a6a447a90ac12ea320001c608f6000328203c000762000000000071e17000000009de000000000000009d00008f80000c12308caa0a94c0a58c0006270000a40f6600000000005a0000000000000000052128f4000000273a1b08c200049c000000000818aa02854a4e800002b4000000000197c00096c00002e45ca0380e30000000524000282000051734b01b833e00017c80000000000000000000000000000115e0000c00000000931066855800000011e00000003240000000000000000000000000000000b40000000b222e454c0000000cb000000000017313fc7190000bfc00078b26424848929c40580000000a2d3da800000000000000011060000b6000000000007c90bc00044414311e80002b6000102ceb287f00000010720891788000000000000199400000000005192f03c44618e0844a2ed00001ac000000000000000014c0000e34de0000428800000000051b20d4b0a00015397a800000000000002c628100000000000004ea80000000000001cfc000000039000000000000000000000001e0800000005e2b8000000000000000001846cc1daa8308be6e800000000000000000000ede0000000000986000000000064257a31b80008402ac24f80003420004d70000000377000000000000000000007f800000000000008991fa80000802ad0e09f6cdd486e3f29d4c69a8d221a00005ae0000f1a43c9563b40638e108b8000000000000094d000040400000050fa09041c4223b40000000000000000000000000000d0b3600010999b40000000000000000755455800000000037494a80002cc00028809367280ce04540000004dd9208a0c75700013300fa236000000037038f00000000003950000000c8a0002a7a8f05847ab0000000000000000144c00026400000003060001808cd00000004cb000106200000000840008f6000000000094f1eb219c0000000000000000000000000000058635f00000ca22a4f79f4c00024e1c3816c00000000000008d800000026c800019631200003b200036310a81500001570000000000000000000008a2b00db0e46078334194869c0003578000000000000278c000000325a5b40000000000000dc40000000000000181000087c0000000000000000000000022c81000017704409a600000000000006710000fa400006400000000004b63f7898138a5f40000000f4400000000002127b60000000d6463f4e3a3880000002f08a609b47c204193dc0e0259082a59432894330c10340007f40e89a311d400f2a10bb07600000000000000a011a28af87
  | 28 => 0x15c0aa0c39f04fd26b30fc959410e00040e800131000030da28828600023ea8403321b7011034800084900008411e29e200000000009cb46381f80000005200214dfc000000000000000000017b8000000392800000086a0000000c220000001d9400000000000000000000ad0000adc0002a3904547022d4bb847898a57e3ee9464c822c337905744e00d43240e0c6b200000000000000002ac000027800000000001c6121000185c06e00044c122d1d257f47a0000f425f62cb9f700003b900014610f49a500000012200000000000000000000000000000050e869c2d427a2db079400082100000008240000001ab0d5c62a0002674000000000000000000000016ec0000420000db431400021a997003000012102f000000000022b400000034f0f80414578000000000026800000000000001b98e1923800000000011cc00000000010a42dd2ac80006e08130000000000000000000000000000000000000ff00000000000002da0fbc48000000016b8ec600000000000000000000000dce0003dc0000f6000000000000004d107689b519a00046b000055e0000001cd8000000000000000021d000045836091a0000000000a0e0000a3531a00000020613e60000d9a5d000000000000001b414200028ec000000000000000000000025040000000000000ac4000000000000000000000000000000001afc00000000000000002c1463000121400000000c0ad60160000000da02e80001820b1800000000000007ee000068921c2c9233037142c35a0000000000860000032532211d0000000f764ac286a4e4a7e78c0efa4644de6512ef93181b00000000f4906834f00009dd21826b12c1704bf43ad0618318bce00051b9d100000004fe0fec0001f6000000044200000000000008e100010dcb84000000000123c0004088000bb000000000000000000000000db000000000000000000d3000117a0f1000000000007537f88612504bf4ea11ad0d60732ee80000000004240000000000000082004a29e50d800000000000000000006f4000000000000000013d11daa18000000000000000000000000000001eb49340000001f48000000000000000000000000000000000000000000829000000003e4cf00018d90500000000000e4800000000000000003bb800000000000010b4cf40000000000000a05000232400065b4fa000066c000000000000023b05a1a0800092e00000013f484e00000002b009c07700014500000000000f9600000026280000000000a901f800050880f00005790cd0000a2860c01700000000000001c3c000000000000000042648128100006844d000000000000000000000000000000000000000021b40000002320000b8c2820000000b2633e0a400000000001630000000000000000000000000000000000000
  | 29 => 0x95a45026fa5447a80000000b7c0005d20000000000000000000029a1c30000000fa841643922747b600000b8000cb094700000000000000000ac8d8a5d14919c5490c5483b5984c78c0003568000c0200000006b80000004ac80000000002190000000527000171caa8000429a0dd03e6f6214137499400000000001c800000002ac000000000000000000014d8000bbc3ed19700000008ee20a8000ee417b34e00000007aa0000175
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x180522b4a9cd9530703ac06188965c1458a548879d5078800080072100000292648b9f1a2000046004a05a98c82000001a2804800400034b0922c0780092b03c981d954509510040fa5c85509609040103e98dd542582410040fe61741d16588509434915d0745962100632609701c1638840122c9261953992500060ddd8815d5649412b03c98dd95450a500050da58541c5645416dc147454d3158620006856118118f6548001a498260063d9520006946058018f654800103f985d074d9520006155cd8118c6548001855876046319520006856118118c6548001a49826006319520006946058018c654800164a968ca301952031692219324c06548001455919db75d8d2000652a55831c121480019499560c704852000652d95831c121480019486560c704852000472e63631c121480011c99818c704852000712194631c1214800194983d4c70485200051a259531c121480019498354c70485200051325d8558d200800184c871d56348020007111d47358520080014649754d614802000615219734c4654416dc167654d31d91100058564c654c464440016169654d3119110005b0640324c762440038548754d31589105b7051d1534c56244001c14651917388510007051d47458d1004001c24751d16244010
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x1000014245332ac18e090a4000c126606518c7048520
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x4
  | 2 => 0x5
  | 3 => 0x6
  | 4 => 0x2
  | 5 => 0x1
  | 6 => 0x4c
  | 7 => 0x4d
  | 8 => 0x4e
  | 9 => 0x124c
  | 10 => 0x3
  | 11 => 0x94c
  | 12 => 0x94d
  | 13 => 0x94e
  | 14 => 0x124d
  | 15 => 0x124e
  | 16 => 0x138c
  | 17 => 0x138d
  | 18 => 0x138e
  | 19 => 0x8c
  | 20 => 0x8d
  | 21 => 0x8e
  | 22 => 0x128c
  | 23 => 0x98c
  | 24 => 0x98d
  | 25 => 0x98e
  | 26 => 0x128d
  | 27 => 0x128e
  | 28 => 0x150c
  | 29 => 0x150d
  | 30 => 0x150e
  | 31 => 0xa0c
  | 32 => 0xa0e
  | 33 => 0x130c
  | 34 => 0x130e
  | 35 => 0xa4c
  | 36 => 0xa4d
  | 37 => 0x134c
  | 38 => 0x134d
  | 39 => 0x20c
  | 40 => 0x20d
  | 41 => 0x20e
  | 42 => 0xb0c
  | 43 => 0xb0d
  | 44 => 0xb0e
  | 45 => 0x140c
  | 46 => 0x140d
  | 47 => 0x140e
  | 48 => 0x154c
  | 49 => 0x154d
  | 50 => 0x154e
  | 51 => 0xb8c
  | 52 => 0xb8e
  | 53 => 0x148c
  | 54 => 0x148e
  | 55 => 0xbcc
  | 56 => 0xbcd
  | 57 => 0x14cc
  | 58 => 0x14cd
  | 59 => 0xd0c
  | 60 => 0xd0e
  | 61 => 0x160c
  | 62 => 0x160e
  | 63 => 0xd4c
  | 64 => 0xd4d
  | 65 => 0x164c
  | 66 => 0x164d
  | 67 => 0x104c
  | 68 => 0x94054
  | 69 => 0x124954
  | 70 => 0x95254
  | 71 => 0xa0954
  | 72 => 0xa0956
  | 73 => 0x130954
  | 74 => 0x130a
  | 75 => 0xb0954
  | 76 => 0x94b14
  | 77 => 0x140954
  | 78 => 0x95414
  | 79 => 0x10a
  | 80 => 0x14a
  | 81 => 0x134a
  | 82 => 0x139254
  | 83 => 0xa1254
  | 84 => 0xa1256
  | 85 => 0x131254
  | 86 => 0xb1394
  | 87 => 0x138b14
  | 88 => 0xd0a
  | 89 => 0xd4a
  | 90 => 0x98094
  | 91 => 0x128994
  | 92 => 0x99294
  | 93 => 0xb0994
  | 94 => 0x98b14
  | 95 => 0x154994
  | 96 => 0x99554
  | 97 => 0x12cb
  | 98 => 0x14b
  | 99 => 0x134b
  | 100 => 0x151294
  | 101 => 0xb1514
  | 102 => 0x150b14
  | 103 => 0xbcb
  | 104 => 0x130a14
  | 105 => 0xa1314
  | 106 => 0x14d
  | 107 => 0xb8a14
  | 108 => 0xa0b94
  | 109 => 0xd0a14
  | 110 => 0xa0d14
  | 111 => 0x198d
  | 112 => 0x149314
  | 113 => 0x134a54
  | 114 => 0xa5354
  | 115 => 0xbca54
  | 116 => 0xa4bd4
  | 117 => 0xd4a54
  | 118 => 0xa4d54
  | 119 => 0x180e
  | 120 => 0x14d354
  | 121 => 0x1354d4
  | 122 => 0x165354
  | 123 => 0x135654
  | 124 => 0x105354
  | 125 => 0x135054
  | 126 => 0xd0b14
  | 127 => 0x160b14
  | 128 => 0xb4b
  | 129 => 0xd1554
  | 130 => 0x188a
  | 131 => 0x2cd
  | 132 => 0x74a
  | 133 => 0x19cd
  | 134 => 0x194a
  | 135 => 0xd1494
  | 136 => 0x148d14
  | 137 => 0x164bd4
  | 138 => 0xbd654
  | 139 => 0x1a0a
  | 140 => 0x104bd4
  | 141 => 0xbd054
  | 142 => 0x28e
  | 143 => 0x184e
  | 144 => 0x1a8a
  | 145 => 0xd54d4
  | 146 => 0x14cd54
  | 147 => 0x104d14
  | 148 => 0xd1054
  | 149 => 0x44d
  | 150 => 0x74b
  | 151 => 0x1a0d
  | 152 => 0x194b
  | 153 => 0x19cb
  | 154 => 0x104d54
  | 155 => 0xd5054
  | 156 => 0x188e
  | 157 => 0x10e
  | 158 => 0x1a4a
  | 159 => 0xeca
  | 160 => 0xb4d
  | 161 => 0x144d
  | 162 => 0xecd
  | 163 => 0x1a4d
  | 164 => 0x8994
  | 165 => 0x1a4b
  | 166 => 0xecb
  | 167 => 0x9414
  | 168 => 0x8d14
  | 169 => 0x9a14
  | 170 => 0xe8a
  | 171 => 0x94a16
  | 172 => 0x141554
  | 173 => 0x2d255
  | 174 => 0x2cb15
  | 175 => 0x2cb55
  | 176 => 0x14cb55
  | 177 => 0x29256
  | 178 => 0x28b16
  | 179 => 0x28b56
  | 180 => 0x180a16
  | 181 => 0x198a55
  | 182 => 0xecb55
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 62
  | 7 => 2231
  | 6 => 6139
  | 5 => 2627
  | 4 => 47
  | 3 => 2
  | _ => 0
def gbR (k i : Nat) : Nat :=
  match k with
  | 9 => packedAt gbK9 (i*15) 6
  | 8 => packedAt gbK8 (i*26) 17
  | 7 => packedAt gbK7 (i*37) 28
  | 6 => packedAt gbK6 (i*48) 39
  | 5 => packedAt gbK5 (i*59) 50
  | 4 => packedAt gbK4 (i*70) 61
  | 3 => packedAt gbK3 (i*81) 72
  | _ => 0
def gbH (k i : Nat) : Nat :=
  match k with
  | 9 => gbHint (packedAt gbK9 (i*15+6) 9)
  | 8 => gbHint (packedAt gbK8 (i*26+17) 9)
  | 7 => gbHint (packedAt gbK7 (i*37+28) 9)
  | 6 => gbHint (packedAt gbK6 (i*48+39) 9)
  | 5 => gbHint (packedAt gbK5 (i*59+50) 9)
  | 4 => gbHint (packedAt gbK4 (i*70+61) 9)
  | 3 => gbHint (packedAt gbK3 (i*81+72) 9)
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 9 => packedAt gbK9 (16+((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 2)*1) 1
  | 8 => packedAt gbK8 (1752+((h/20+packedAt gbK8 (1612+(h % 20)*7) 7) % 75)*7) 7
  | 7 => packedAt gbK7 (91463+((h/743+packedAt gbK7 (82547+(h % 743)*12) 12) % 3918)*13) 13
  | 6 => packedAt gbK6 (321270+((h/2046+packedAt gbK6 (294672+(h % 2046)*13) 13) % 7367)*14) 14
  | 5 => packedAt gbK5 (166368+((h/875+packedAt gbK5 (154993+(h % 875)*13) 13) % 5582)*13) 13
  | 4 => packedAt gbK4 (3380+((h/15+packedAt gbK4 (3290+(h % 15)*6) 6) % 57)*7) 7
  | 3 => packedAt gbK3 (165+((h/1+packedAt gbK3 (162+(h % 1)*3) 3) % 7)*2) 2
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xc1fe1c1c1fc3f8061c07fffffc29c71e19c0ff
  | 1 => 0xfe1fe01fe1fc3fffe00781c0fcd624e6667c93
  | 2 => 0xffe1ffe001ffc007fff801ff031838f9878f1c
  | 3 => 0x1fffffe000007fffffe0003e03f01f80fe0
  | 4 => 0x1fffffffffff80000000003ffc001fff000
  | 5 => 0xfffe0000000000000000000003fffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x80220408028048400400a8546000c10a08c025
  | 1 => 0x52146005204412372035048298422464221c92
  | 2 => 0x6540a920016a80924950012a091808b0870518
  | 3 => 0x101152575400012592a6540012e03601700ac0
  | 4 => 0x21019f9a99b325c000c0180c23bd4001dde000
  | 5 => 0xb99803031022060103046030c3ffbfde000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeefae8feecfaa8feeefae8feecfaa8feeefae8feecfaa8feeefae8feecfaa8feeefae8feecfaa8feeefae8feecfaa8feeefae8feecfaa8feeefae8feecfaa8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_16919
namespace PEqualNP.Outside.L_meta_16919
open PEqualNP.Outside.L_meta_16919.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 1 := bs0_4_0
theorem alls0 : ∀ k ≤ 4, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_2_0 : Interval s1Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 4 := bs1_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 13 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 17 := block_range (n:=17) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 17 := bs1_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 1 := bs1_5_0
theorem alls1 : ∀ k ≤ 5, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_2 i (by omega) hi
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 4 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 12 := bs2_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 1 := bs2_5_0
theorem alls2 : ∀ k ≤ 5, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_0 : Interval s3Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 4 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 25 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_32 : Interval s3Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_64 : Interval s3Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_96 : Interval s3Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_128 : Interval s3Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_160 : Interval s3Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_192 : Interval s3Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_224 : Interval s3Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_256 : Interval s3Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_288 : Interval s3Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_320 : Interval s3Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_352 : Interval s3Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_384 : Interval s3Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_416 : Interval s3Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_448 : Interval s3Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_480 : Interval s3Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_512 : Interval s3Atlas 4 512 27 := block_range (n:=27) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 539 := (concat (concat (concat (concat bs3_4_0 bs3_4_32) (concat bs3_4_64 bs3_4_96)) (concat (concat bs3_4_128 bs3_4_160) (concat bs3_4_192 bs3_4_224))) (concat (concat (concat bs3_4_256 bs3_4_288) (concat bs3_4_320 bs3_4_352)) (concat (concat bs3_4_384 bs3_4_416) (concat bs3_4_448 (concat bs3_4_480 bs3_4_512)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_64 : Interval s3Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_96 : Interval s3Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_128 : Interval s3Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_160 : Interval s3Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_192 : Interval s3Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_224 : Interval s3Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_256 : Interval s3Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_288 : Interval s3Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_320 : Interval s3Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_352 : Interval s3Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_384 : Interval s3Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_416 : Interval s3Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_448 : Interval s3Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_480 : Interval s3Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_512 : Interval s3Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_544 : Interval s3Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_576 : Interval s3Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_608 : Interval s3Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_640 : Interval s3Atlas 5 640 24 := block_range (n:=24) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 664 := (concat (concat (concat (concat bs3_5_0 bs3_5_32) (concat bs3_5_64 (concat bs3_5_96 bs3_5_128))) (concat (concat bs3_5_160 bs3_5_192) (concat bs3_5_224 (concat bs3_5_256 bs3_5_288)))) (concat (concat (concat bs3_5_320 bs3_5_352) (concat bs3_5_384 (concat bs3_5_416 bs3_5_448))) (concat (concat bs3_5_480 (concat bs3_5_512 bs3_5_544)) (concat bs3_5_576 (concat bs3_5_608 bs3_5_640)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_32 : Interval s3Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 40 := (concat bs3_6_0 bs3_6_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_7_0 : Interval s3Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_7 : Interval s3Atlas 7 0 1 := bs3_7_0
theorem alls3 : ∀ k ≤ 7, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_2 i (by omega) hi
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
  · exact alls3_6 i (by omega) hi
  · exact alls3_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_0 : Interval s4Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 10 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_32 : Interval s4Atlas 3 32 28 := block_range (n:=28) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 60 := (concat bs4_3_0 bs4_3_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_32 : Interval s4Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_64 : Interval s4Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_96 : Interval s4Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_128 : Interval s4Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_160 : Interval s4Atlas 4 160 5 := block_range (n:=5) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 165 := (concat (concat bs4_4_0 (concat bs4_4_32 bs4_4_64)) (concat bs4_4_96 (concat bs4_4_128 bs4_4_160)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 50 := (concat bs4_5_0 bs4_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 1 := bs4_6_0
theorem alls4 : ∀ k ≤ 6, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_2 i (by omega) hi
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
  · exact alls4_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_0 : Interval s5Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 5 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 25 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_32 : Interval s5Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_64 : Interval s5Atlas 4 64 27 := block_range (n:=27) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 91 := (concat bs5_4_0 (concat bs5_4_32 bs5_4_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 44 := (concat bs5_5_0 bs5_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 1 := bs5_6_0
theorem alls5 : ∀ k ≤ 6, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_2 i (by omega) hi
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
  · exact alls5_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 2 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 47 := (concat bgb_4_0 bgb_4_32)
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
theorem bgb_5_2624 : Interval gbAtlas 5 2624 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2627 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 bgb_5_192) (concat bgb_5_224 (concat bgb_5_256 bgb_5_288)))) (concat (concat (concat bgb_5_320 bgb_5_352) (concat bgb_5_384 (concat bgb_5_416 bgb_5_448))) (concat (concat bgb_5_480 bgb_5_512) (concat bgb_5_544 (concat bgb_5_576 bgb_5_608))))) (concat (concat (concat (concat bgb_5_640 bgb_5_672) (concat bgb_5_704 (concat bgb_5_736 bgb_5_768))) (concat (concat bgb_5_800 bgb_5_832) (concat bgb_5_864 (concat bgb_5_896 bgb_5_928)))) (concat (concat (concat bgb_5_960 bgb_5_992) (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088))) (concat (concat bgb_5_1120 (concat bgb_5_1152 bgb_5_1184)) (concat bgb_5_1216 (concat bgb_5_1248 bgb_5_1280)))))) (concat (concat (concat (concat (concat bgb_5_1312 bgb_5_1344) (concat bgb_5_1376 (concat bgb_5_1408 bgb_5_1440))) (concat (concat bgb_5_1472 bgb_5_1504) (concat bgb_5_1536 (concat bgb_5_1568 bgb_5_1600)))) (concat (concat (concat bgb_5_1632 bgb_5_1664) (concat bgb_5_1696 (concat bgb_5_1728 bgb_5_1760))) (concat (concat bgb_5_1792 (concat bgb_5_1824 bgb_5_1856)) (concat bgb_5_1888 (concat bgb_5_1920 bgb_5_1952))))) (concat (concat (concat (concat bgb_5_1984 bgb_5_2016) (concat bgb_5_2048 (concat bgb_5_2080 bgb_5_2112))) (concat (concat bgb_5_2144 bgb_5_2176) (concat bgb_5_2208 (concat bgb_5_2240 bgb_5_2272)))) (concat (concat (concat bgb_5_2304 bgb_5_2336) (concat bgb_5_2368 (concat bgb_5_2400 bgb_5_2432))) (concat (concat bgb_5_2464 (concat bgb_5_2496 bgb_5_2528)) (concat bgb_5_2560 (concat bgb_5_2592 bgb_5_2624)))))))
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
theorem bgb_6_1888 : Interval gbAtlas 6 1888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1920 : Interval gbAtlas 6 1920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1952 : Interval gbAtlas 6 1952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1984 : Interval gbAtlas 6 1984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2016 : Interval gbAtlas 6 2016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2048 : Interval gbAtlas 6 2048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2080 : Interval gbAtlas 6 2080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2112 : Interval gbAtlas 6 2112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2144 : Interval gbAtlas 6 2144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2176 : Interval gbAtlas 6 2176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2208 : Interval gbAtlas 6 2208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2240 : Interval gbAtlas 6 2240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2272 : Interval gbAtlas 6 2272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2304 : Interval gbAtlas 6 2304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2336 : Interval gbAtlas 6 2336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2368 : Interval gbAtlas 6 2368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2400 : Interval gbAtlas 6 2400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2432 : Interval gbAtlas 6 2432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2464 : Interval gbAtlas 6 2464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2496 : Interval gbAtlas 6 2496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2528 : Interval gbAtlas 6 2528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2560 : Interval gbAtlas 6 2560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2592 : Interval gbAtlas 6 2592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2624 : Interval gbAtlas 6 2624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2656 : Interval gbAtlas 6 2656 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2688 : Interval gbAtlas 6 2688 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2720 : Interval gbAtlas 6 2720 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2752 : Interval gbAtlas 6 2752 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2784 : Interval gbAtlas 6 2784 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2816 : Interval gbAtlas 6 2816 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2848 : Interval gbAtlas 6 2848 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2880 : Interval gbAtlas 6 2880 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2912 : Interval gbAtlas 6 2912 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2944 : Interval gbAtlas 6 2944 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_2976 : Interval gbAtlas 6 2976 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3008 : Interval gbAtlas 6 3008 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3040 : Interval gbAtlas 6 3040 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3072 : Interval gbAtlas 6 3072 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3104 : Interval gbAtlas 6 3104 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3136 : Interval gbAtlas 6 3136 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3168 : Interval gbAtlas 6 3168 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3200 : Interval gbAtlas 6 3200 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3232 : Interval gbAtlas 6 3232 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3264 : Interval gbAtlas 6 3264 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3296 : Interval gbAtlas 6 3296 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3328 : Interval gbAtlas 6 3328 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3360 : Interval gbAtlas 6 3360 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3392 : Interval gbAtlas 6 3392 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3424 : Interval gbAtlas 6 3424 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3456 : Interval gbAtlas 6 3456 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3488 : Interval gbAtlas 6 3488 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3520 : Interval gbAtlas 6 3520 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3552 : Interval gbAtlas 6 3552 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3584 : Interval gbAtlas 6 3584 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3616 : Interval gbAtlas 6 3616 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3648 : Interval gbAtlas 6 3648 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3680 : Interval gbAtlas 6 3680 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3712 : Interval gbAtlas 6 3712 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3744 : Interval gbAtlas 6 3744 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3776 : Interval gbAtlas 6 3776 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3808 : Interval gbAtlas 6 3808 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3840 : Interval gbAtlas 6 3840 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3872 : Interval gbAtlas 6 3872 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3904 : Interval gbAtlas 6 3904 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3936 : Interval gbAtlas 6 3936 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_3968 : Interval gbAtlas 6 3968 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4000 : Interval gbAtlas 6 4000 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4032 : Interval gbAtlas 6 4032 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4064 : Interval gbAtlas 6 4064 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4096 : Interval gbAtlas 6 4096 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4128 : Interval gbAtlas 6 4128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4160 : Interval gbAtlas 6 4160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4192 : Interval gbAtlas 6 4192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4224 : Interval gbAtlas 6 4224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4256 : Interval gbAtlas 6 4256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4288 : Interval gbAtlas 6 4288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4320 : Interval gbAtlas 6 4320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4352 : Interval gbAtlas 6 4352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4384 : Interval gbAtlas 6 4384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4416 : Interval gbAtlas 6 4416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4448 : Interval gbAtlas 6 4448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4480 : Interval gbAtlas 6 4480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4512 : Interval gbAtlas 6 4512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4544 : Interval gbAtlas 6 4544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4576 : Interval gbAtlas 6 4576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4608 : Interval gbAtlas 6 4608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4640 : Interval gbAtlas 6 4640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4672 : Interval gbAtlas 6 4672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4704 : Interval gbAtlas 6 4704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4736 : Interval gbAtlas 6 4736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4768 : Interval gbAtlas 6 4768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4800 : Interval gbAtlas 6 4800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4832 : Interval gbAtlas 6 4832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4864 : Interval gbAtlas 6 4864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4896 : Interval gbAtlas 6 4896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4928 : Interval gbAtlas 6 4928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4960 : Interval gbAtlas 6 4960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_4992 : Interval gbAtlas 6 4992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5024 : Interval gbAtlas 6 5024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5056 : Interval gbAtlas 6 5056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5088 : Interval gbAtlas 6 5088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5120 : Interval gbAtlas 6 5120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5152 : Interval gbAtlas 6 5152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5184 : Interval gbAtlas 6 5184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5216 : Interval gbAtlas 6 5216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5248 : Interval gbAtlas 6 5248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5280 : Interval gbAtlas 6 5280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5312 : Interval gbAtlas 6 5312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5344 : Interval gbAtlas 6 5344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5376 : Interval gbAtlas 6 5376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5408 : Interval gbAtlas 6 5408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5440 : Interval gbAtlas 6 5440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5472 : Interval gbAtlas 6 5472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5504 : Interval gbAtlas 6 5504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5536 : Interval gbAtlas 6 5536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5568 : Interval gbAtlas 6 5568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5600 : Interval gbAtlas 6 5600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5632 : Interval gbAtlas 6 5632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5664 : Interval gbAtlas 6 5664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5696 : Interval gbAtlas 6 5696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5728 : Interval gbAtlas 6 5728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5760 : Interval gbAtlas 6 5760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5792 : Interval gbAtlas 6 5792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5824 : Interval gbAtlas 6 5824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5856 : Interval gbAtlas 6 5856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5888 : Interval gbAtlas 6 5888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5920 : Interval gbAtlas 6 5920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5952 : Interval gbAtlas 6 5952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5984 : Interval gbAtlas 6 5984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6016 : Interval gbAtlas 6 6016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6048 : Interval gbAtlas 6 6048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6080 : Interval gbAtlas 6 6080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6112 : Interval gbAtlas 6 6112 27 := block_range (n:=27) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 6139 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat bgb_6_288 (concat bgb_6_320 bgb_6_352)))) (concat (concat (concat bgb_6_384 (concat bgb_6_416 bgb_6_448)) (concat bgb_6_480 (concat bgb_6_512 bgb_6_544))) (concat (concat bgb_6_576 (concat bgb_6_608 bgb_6_640)) (concat bgb_6_672 (concat bgb_6_704 bgb_6_736))))) (concat (concat (concat (concat bgb_6_768 (concat bgb_6_800 bgb_6_832)) (concat bgb_6_864 (concat bgb_6_896 bgb_6_928))) (concat (concat bgb_6_960 (concat bgb_6_992 bgb_6_1024)) (concat bgb_6_1056 (concat bgb_6_1088 bgb_6_1120)))) (concat (concat (concat bgb_6_1152 (concat bgb_6_1184 bgb_6_1216)) (concat bgb_6_1248 (concat bgb_6_1280 bgb_6_1312))) (concat (concat bgb_6_1344 (concat bgb_6_1376 bgb_6_1408)) (concat bgb_6_1440 (concat bgb_6_1472 bgb_6_1504)))))) (concat (concat (concat (concat (concat bgb_6_1536 (concat bgb_6_1568 bgb_6_1600)) (concat bgb_6_1632 (concat bgb_6_1664 bgb_6_1696))) (concat (concat bgb_6_1728 (concat bgb_6_1760 bgb_6_1792)) (concat bgb_6_1824 (concat bgb_6_1856 bgb_6_1888)))) (concat (concat (concat bgb_6_1920 (concat bgb_6_1952 bgb_6_1984)) (concat bgb_6_2016 (concat bgb_6_2048 bgb_6_2080))) (concat (concat bgb_6_2112 (concat bgb_6_2144 bgb_6_2176)) (concat bgb_6_2208 (concat bgb_6_2240 bgb_6_2272))))) (concat (concat (concat (concat bgb_6_2304 (concat bgb_6_2336 bgb_6_2368)) (concat bgb_6_2400 (concat bgb_6_2432 bgb_6_2464))) (concat (concat bgb_6_2496 (concat bgb_6_2528 bgb_6_2560)) (concat bgb_6_2592 (concat bgb_6_2624 bgb_6_2656)))) (concat (concat (concat bgb_6_2688 (concat bgb_6_2720 bgb_6_2752)) (concat bgb_6_2784 (concat bgb_6_2816 bgb_6_2848))) (concat (concat bgb_6_2880 (concat bgb_6_2912 bgb_6_2944)) (concat bgb_6_2976 (concat bgb_6_3008 bgb_6_3040))))))) (concat (concat (concat (concat (concat (concat bgb_6_3072 (concat bgb_6_3104 bgb_6_3136)) (concat bgb_6_3168 (concat bgb_6_3200 bgb_6_3232))) (concat (concat bgb_6_3264 (concat bgb_6_3296 bgb_6_3328)) (concat bgb_6_3360 (concat bgb_6_3392 bgb_6_3424)))) (concat (concat (concat bgb_6_3456 (concat bgb_6_3488 bgb_6_3520)) (concat bgb_6_3552 (concat bgb_6_3584 bgb_6_3616))) (concat (concat bgb_6_3648 (concat bgb_6_3680 bgb_6_3712)) (concat bgb_6_3744 (concat bgb_6_3776 bgb_6_3808))))) (concat (concat (concat (concat bgb_6_3840 (concat bgb_6_3872 bgb_6_3904)) (concat bgb_6_3936 (concat bgb_6_3968 bgb_6_4000))) (concat (concat bgb_6_4032 (concat bgb_6_4064 bgb_6_4096)) (concat bgb_6_4128 (concat bgb_6_4160 bgb_6_4192)))) (concat (concat (concat bgb_6_4224 (concat bgb_6_4256 bgb_6_4288)) (concat bgb_6_4320 (concat bgb_6_4352 bgb_6_4384))) (concat (concat bgb_6_4416 (concat bgb_6_4448 bgb_6_4480)) (concat bgb_6_4512 (concat bgb_6_4544 bgb_6_4576)))))) (concat (concat (concat (concat (concat bgb_6_4608 (concat bgb_6_4640 bgb_6_4672)) (concat bgb_6_4704 (concat bgb_6_4736 bgb_6_4768))) (concat (concat bgb_6_4800 (concat bgb_6_4832 bgb_6_4864)) (concat bgb_6_4896 (concat bgb_6_4928 bgb_6_4960)))) (concat (concat (concat bgb_6_4992 (concat bgb_6_5024 bgb_6_5056)) (concat bgb_6_5088 (concat bgb_6_5120 bgb_6_5152))) (concat (concat bgb_6_5184 (concat bgb_6_5216 bgb_6_5248)) (concat bgb_6_5280 (concat bgb_6_5312 bgb_6_5344))))) (concat (concat (concat (concat bgb_6_5376 (concat bgb_6_5408 bgb_6_5440)) (concat bgb_6_5472 (concat bgb_6_5504 bgb_6_5536))) (concat (concat bgb_6_5568 (concat bgb_6_5600 bgb_6_5632)) (concat bgb_6_5664 (concat bgb_6_5696 bgb_6_5728)))) (concat (concat (concat bgb_6_5760 (concat bgb_6_5792 bgb_6_5824)) (concat bgb_6_5856 (concat bgb_6_5888 bgb_6_5920))) (concat (concat bgb_6_5952 (concat bgb_6_5984 bgb_6_6016)) (concat bgb_6_6048 (concat bgb_6_6080 bgb_6_6112))))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_32 : Interval gbAtlas 7 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_64 : Interval gbAtlas 7 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_96 : Interval gbAtlas 7 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_128 : Interval gbAtlas 7 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_160 : Interval gbAtlas 7 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_192 : Interval gbAtlas 7 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_224 : Interval gbAtlas 7 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_256 : Interval gbAtlas 7 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_288 : Interval gbAtlas 7 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_320 : Interval gbAtlas 7 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_352 : Interval gbAtlas 7 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_384 : Interval gbAtlas 7 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_416 : Interval gbAtlas 7 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_448 : Interval gbAtlas 7 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_480 : Interval gbAtlas 7 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_512 : Interval gbAtlas 7 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_544 : Interval gbAtlas 7 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_576 : Interval gbAtlas 7 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_608 : Interval gbAtlas 7 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_640 : Interval gbAtlas 7 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_672 : Interval gbAtlas 7 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_704 : Interval gbAtlas 7 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_736 : Interval gbAtlas 7 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_768 : Interval gbAtlas 7 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_800 : Interval gbAtlas 7 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_832 : Interval gbAtlas 7 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_864 : Interval gbAtlas 7 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_896 : Interval gbAtlas 7 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_928 : Interval gbAtlas 7 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_960 : Interval gbAtlas 7 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_992 : Interval gbAtlas 7 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1024 : Interval gbAtlas 7 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1056 : Interval gbAtlas 7 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1088 : Interval gbAtlas 7 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1120 : Interval gbAtlas 7 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1152 : Interval gbAtlas 7 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1184 : Interval gbAtlas 7 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1216 : Interval gbAtlas 7 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1248 : Interval gbAtlas 7 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1280 : Interval gbAtlas 7 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1312 : Interval gbAtlas 7 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1344 : Interval gbAtlas 7 1344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1376 : Interval gbAtlas 7 1376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1408 : Interval gbAtlas 7 1408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1440 : Interval gbAtlas 7 1440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1472 : Interval gbAtlas 7 1472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1504 : Interval gbAtlas 7 1504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1536 : Interval gbAtlas 7 1536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1568 : Interval gbAtlas 7 1568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1600 : Interval gbAtlas 7 1600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1632 : Interval gbAtlas 7 1632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1664 : Interval gbAtlas 7 1664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1696 : Interval gbAtlas 7 1696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1728 : Interval gbAtlas 7 1728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1760 : Interval gbAtlas 7 1760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1792 : Interval gbAtlas 7 1792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1824 : Interval gbAtlas 7 1824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1856 : Interval gbAtlas 7 1856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1888 : Interval gbAtlas 7 1888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1920 : Interval gbAtlas 7 1920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1952 : Interval gbAtlas 7 1952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_1984 : Interval gbAtlas 7 1984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2016 : Interval gbAtlas 7 2016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2048 : Interval gbAtlas 7 2048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2080 : Interval gbAtlas 7 2080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2112 : Interval gbAtlas 7 2112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2144 : Interval gbAtlas 7 2144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2176 : Interval gbAtlas 7 2176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2208 : Interval gbAtlas 7 2208 23 := block_range (n:=23) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2231 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 bgb_7_224))) (concat (concat (concat bgb_7_256 bgb_7_288) (concat bgb_7_320 bgb_7_352)) (concat (concat bgb_7_384 bgb_7_416) (concat bgb_7_448 (concat bgb_7_480 bgb_7_512))))) (concat (concat (concat (concat bgb_7_544 bgb_7_576) (concat bgb_7_608 bgb_7_640)) (concat (concat bgb_7_672 bgb_7_704) (concat bgb_7_736 (concat bgb_7_768 bgb_7_800)))) (concat (concat (concat bgb_7_832 bgb_7_864) (concat bgb_7_896 bgb_7_928)) (concat (concat bgb_7_960 bgb_7_992) (concat bgb_7_1024 (concat bgb_7_1056 bgb_7_1088)))))) (concat (concat (concat (concat (concat bgb_7_1120 bgb_7_1152) (concat bgb_7_1184 bgb_7_1216)) (concat (concat bgb_7_1248 bgb_7_1280) (concat bgb_7_1312 bgb_7_1344))) (concat (concat (concat bgb_7_1376 bgb_7_1408) (concat bgb_7_1440 bgb_7_1472)) (concat (concat bgb_7_1504 bgb_7_1536) (concat bgb_7_1568 (concat bgb_7_1600 bgb_7_1632))))) (concat (concat (concat (concat bgb_7_1664 bgb_7_1696) (concat bgb_7_1728 bgb_7_1760)) (concat (concat bgb_7_1792 bgb_7_1824) (concat bgb_7_1856 (concat bgb_7_1888 bgb_7_1920)))) (concat (concat (concat bgb_7_1952 bgb_7_1984) (concat bgb_7_2016 bgb_7_2048)) (concat (concat bgb_7_2080 bgb_7_2112) (concat bgb_7_2144 (concat bgb_7_2176 bgb_7_2208)))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 30 := block_range (n:=30) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 62 := (concat bgb_8_0 bgb_8_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_9_0 : Interval gbAtlas 9 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_9 : Interval gbAtlas 9 0 1 := bgb_9_0
theorem allgb : ∀ k ≤ 9, ∀ i < count gbAtlas k, checkRow gbAtlas k i = true := by
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
  · exact allgb_9 i (by omega) hi
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 5 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 16, 18),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 33, 49),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefae8feecfaa8feeefae8feecfaa8feeefae8feecfaa8feeefae8feecfaa8feeefae8feecfaa8feeefae8feecfaa8feeefae8feecfaa8feeefae8feecfaa8
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) (SBf 1) :=
    slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have s2 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 2 zero)) (SBf 2) :=
    slice_correct (ms:=fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
  have s3 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 3 zero)) (SBf 3) :=
    slice_correct (ms:=fixRows 8 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds3 certs3)
  have s4 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 4 zero)) (SBf 4) :=
    slice_correct (ms:=fixRows 16 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds4 certs4)
  have s5 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 5 zero)) (SBf 5) :=
    slice_correct (ms:=fixRows 32 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds5 certs5)
  have allCuts : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val) := by
    intro v
    fin_cases v
    · exact s0
    · exact s1
    · exact s2
    · exact s3
    · exact s4
    · exact s5
  have low := boundgb certgb allCuts
  have lift := lift_ok (u:=true) (ms:=fixRows 0 0) (raw:=fullRoots) (T:=fullWord) (xs:=[]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 0 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277074664 * 2 ^ 32 + 4276943528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_16919.Model.Repr at out
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

def mono : List Gate := [⟨.or,[1,2]⟩,⟨.and,[1,5]⟩,⟨.and,[0,6]⟩,⟨.and,[0,5]⟩,⟨.or,[1,9]⟩,⟨.or,[0,2]⟩,⟨.and,[4,10]⟩,⟨.or,[3,8]⟩,⟨.or,[7,13]⟩,⟨.and,[11,14]⟩,⟨.or,[12,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074664 * 2 ^ 32 + 4276943528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074664 * 2 ^ 32 + 4276943528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_16919

open PEqualNP.Outside.L_meta_16919 in
theorem PEqualNP.Outside.L_meta_16919 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074664 * 2 ^ 32 + 4276943528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074664 * 2 ^ 32 + 4276943528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
