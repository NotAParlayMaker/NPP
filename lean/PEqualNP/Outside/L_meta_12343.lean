import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_12343.Model
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
  (n*(n+971)) % 2305843009213693951
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


end PEqualNP.Outside.L_meta_12343.Model

namespace PEqualNP.Outside.L_meta_12343
open PEqualNP.Outside.L_meta_12343.Model
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

end PEqualNP.Outside.L_meta_12343

namespace PEqualNP.Outside.L_meta_12343
open PEqualNP.Outside.L_meta_12343.Model
def gbK8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x7800048000000001c0080000000001d000000044400000098009000040000300000000000320000000000000000d800a00000000000000000000000000000098000000000000000040000000000000000f0000000000000000001c000000001f4200000000002700000000000000000000000000000000000000000000000000000080004400000005000000025000000e0000000000c000009000000000000000000168c00000000000000d000058017000000600000000000004003400000000150000018000000000500000000000000000000000000000000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x8417e52083fe84107f90820fea1041fc42083fe64107f8c820fe99041fc32083fea2107f94420bf28841fd51082faa2107f14420ffa0841fe41083fa82107f10420ff98841fe31083fa62107f0c420ff90841fe21083fa42107f08420bf28041ff40083fc80107f50020fe20041ff30083fc60107f4c020fe18041ff20083de40107f88020fd10041fd20083da40107e48020f490041ff54c42fea9887f95310bf2a621fd54c42faa9887f15310be2a621ff53c42fea7887f94f10bf29e21fd53c42faa7887f14f10be29e21ff43c43fc87887f50f10fe21e21ff52c42fea5887f94b10bf29621fd52c42faa5887f14b10be29621ff42c43fc85887f50b10fe21621ff32c43fc65887f4cb10fe19621ff41c43fc83887f50710fe20e21ff31c43fc63887f4c710fe18e21ff21c43fc43887f48710fe10e21ff40c43fc81887f50310fe20621ff30c43fc61887f4c310fe18621ff20c43fc41887f48310fe10621ff54842fea9087f95210bf2a421fd54842faa9087f15210be2a421ff53842fea7087f94e10bf29c21fd53842faa7087f14e10be29c21ff43843fc87087f50e10fe21c21ff52842fea5087f94a10bf29421fd52842faa5087f14a10be29421ff42843fc85087f50a10fe21421ff32843fc65087f4ca10fe194217d51843fe83087f90610fea0c21fc41843fe63087f8c610fe98c21fc31843fe43087f88610fe90c21fc21842fca1087fd0210ff20421fd40843f881087fcc210ff18421fd30843f861087fc8210ff10421fd20843f841087fc4210fb88421fb10843fea8885fd5110ff2a2217e54443faa8885f55110fe2a2217c54443fea6885fd4d10ff29a217e53443faa6885f54d10fe29a217c53443fe86887f90d10fea1a21fc43443fea4885fd4910ff292217e52443faa4885f54910fe292217c52443fe84887f90910fea1221fc42443fe64887f8c910fe99221fc32443fe82887f90510fea0a21fc41443fe62887f8c510fe98a21fc31443fe42887f88510fe90a21fc21443fe80887f90110fea0221fc40443fe60887f8c110fe98221fc30443fe40887f88110fe90221fc20443fe20887ec4110ff08221f610443fea8085fd5010ff2a0217e54043faa8085f55010fe2a0217c54043fea6085fd4c10ff298217e53043faa6085f54c10fe298217c53043fe86087f90c10fea1821fc43043fea4085fd4810ff290217e52043faa4085f54810fe290217c52043fe84087f90810fea1021fc42043fe64087f8c810fe99021fc32042fca2087fd0410ff20821fd41043f882087fcc410ff18821fd31043f862087fc8410ff10821fd21043f842085f94010ffa0021fe40043fa80087f10010ff98021fe30043fa60087f0c010ff90021fe20043fa40087f08010ff88021f710043fc20087e84010fe88021f510043f220087c44010
  | 1 => 0xf308c3be61187ecc230ffaa2617f544c3fca8985f95130feaa2617d544c3f8a8985f15130ffa1a61fe434c3fa86987f10d30ffa92617f524c3fca4987f54930fe292617c524c3fe84987f90930fea1261fc424c3fe64987f8c930fe99261fc324c3fea2985fd4530ff28a61fd514c3f8a2985f14530ffa0a61fe414c3fa82987f10530ff98a61fe314c3fa62987f0c530ff90a61fe214c3fa42987f08530ffa0261fe404c3fa80987f10130ff98261fb304c3fc6098778c130ffaa0617f540c3fca8185f95030feaa0617d540c3f8a8185f15030bf29861ff430c3fc86187f50c30fe21861ff520c3fca4185f94830fea90617d520c3f8a4187fd0830ff21061fd420c3f884187fcc830ff19061fd320c3f864187fd4430ff288617e510c3faa2185f54430fe28861ff410c3fc82187f50430fe20861ff310c3fc62187f4c430fe18861ff210c3fc42187f48430fe108617e500c3fe80187f90030fea0061fc400c3fe601877cc030ff18061fa300c3fa6018774c030fc98061d9300c3fea9905fd5320ff2a6417e54c83faa9905f55320fe2a6417c54c83fea7905fd4f20ff29e417e53c83faa7905f54f20fe29e417c53c83fe87907f90f20fea1e41fc43c83fe85907f90b20fea1641fc42c83fe65907f8cb20fe99641fc32c83fea3907f94720bf28e41fd51c82faa3907f14720ffa0e41fe41c83fa83907f10720ff98e41fe31c83fa63907f0c720ff90e41fe21c83fa43907f08720ffa0641fe40c83fa81907f10320ff98641fe30c83fa61907f0c320ffaa4417f54883fca9105f95220feaa4417d54883f8a9105f15220ffa9c417f53883fca7105f94e20fea9c417d53883f8a7105f14e20ffa1c41fe43883fa87107f10e20bea9441ff42883fc85107f50a20fe21441ff32883fc65107f4ca20fe19441ff51883fca3105f94620fea8c417d51883f8a3107fd0620ff20c41fd41883f883107fcc620ff18c41fd31883f863107fc8620ff10c41fd21883f843105f94220ffa0441fe40883fa81107f10220ff98441fe30883fa61107f0c220ff90441ef20883f641107fd5120bfaa241fe54482fca8907f55120beaa241fc54482f8a8907fd4d20bfa9a41fe53482fca6907f54d20bea9a41fc53482f8a6907fd0d20ff21a41fd43483f886907fd0920ff21241fd42483f884907fcc920ff19241fd32483f864907fd4520bfa8a41fe51483faa2907f14520be28a41ff41483fc82907f50520fe20a41ff31483fc62907f4c520fe18a41ff21483fc42907f48520fe10a41ff40483fc80907f50120fe20241ff30483fc60907f4c120fe18241ff20483f640907f88120f710241ff54082fea8107f95020bf2a041fd54082faa8107f15020be2a041ff53082fea6107f94c20bf29841fd53082faa6107f14c20be29841ff43083fc86107f50c20fe21
  | 2 => 0x87fe6210ff8c421fe98843fc31087fe4210fbc8421ff10843f621087fa4210fb48421fa90843e521087fea010ff94021bf28043fd50086faa010ff14021ffa9e81fe53d02fca7a07f54f40bea9e81fc53d03fe87a07f90f40fea1e81fc43d03fea5a07f94b40bf29681fd52d02faa5a07f14b40ffa1681fe42d03fa85a07f10b40ff99681fe32d03fa65a07f0cb40ffa8e81fe51d02fca3a07f54740bea8e81fc51d03fe83a07f90740fea0e81fc41d03fe63a07f8c740fe98e81fc31d03fe43a07f88740fe90e81fc21d02faa9207fd4e40ff29c817e53903faa7205f54e40fe29c81ff43903fc87207f50e40fe21c81ff52903fca5205f94a40fea94817d52903f8a5207fd0a40ff21481fd42903f885207fcca40ff19481fd32903f865207fd4640ff28c817e51903faa3205f54640fe28c81ff41903fc83207f50640fe20c81ff31903fc63207f4c640fe18c81ff21903fc43207f48640fe10c817e50903fe81206fd0240fda0481ff53502fea6a07f94d40fea9a81fc53502f8a6a07fd0d40ff21a81fd43503f886a07fd4940bfa9281fe52503faa4a07f14940be29281ff42503fc84a07f50940fe21281ff32503fc64a07f4c940fe19281ff51502fea2a07f94540fea8a81fc51502f8a2a07fd0540ff20a81fd41503f882a07fcc540ff18a81fd31503f862a07fc8540ff10a81fd21503f842a07fd0140fda0281fe405037c80a05f95040ffa9881fe53102fca6207f54c40bea9881fc53103fe86207f90c40fea1881fc43103fea4207f94840bf29081fd52102faa4207f14840ffa1081fe42103fa84207f10840ff99081fe32103fa64207f0c840ffa8881fe51102fca2207f54440bea8881fc51103fe82207f90440fea0881fc41103fe62207f8c440fe98881fc31103fe42207f88440fe90881fc21102fca0207fd0040dfa0081fe40103f480207f50040dea0081f9401037280207fd5330bfaa661fe54cc2fca9987f55330beaa661fc54cc2f8a9987fd0f30ff21e61fd43cc3f887987fd4b30ff296617e52cc3faa5985f54b30fe29661ff42cc3fc85987f50b30fe21661ff32cc3fc65987f4cb30fe19661ff51cc3fca3985f94730fea8e617d51cc3f8a3987fd0730ff20e61fd41cc3f883987fcc730ff18e61fd31cc3f863987fc8730ff10e61fd21cc3f843987fd0330ff20661fd40cc3f881987fd5230bfaa461fe548c2fca9187f55230beaa461fc548c2f8a9185f54e30ffa1c61fe438c3fa87187f10e30ffa9461fe528c2fca5187f54a30bea9461fc528c3fe85187f90a30fea1461fc428c3fe65187f8ca30fe99461fc328c3fea3187f94630bf28c61fd518c2faa3187f14630ffa0c61fe418c3fa83187f10630ff98c61fe318c3fa63187f0c630ff90c61fe218c3fa43187f08630bf28461ff408c3fc81187f50230fe20461f
  | 3 => 0x8398ff10731ffa8663fe50cc6fca198ff54331bea8663fc50cc7fea918dfd5231ff2a4637e548c7faa918df55231fe2a4637c548c6faa718ffd0e31ff21c63fd438c7f88718ffd4a31ff294637e528c7faa518df54a31fe29463ff428c7fc8518ff50a31fe21463ff328c7fc6518ff4ca31fe194637e518c7fe8318ff90631fea0c63fc418c7fe6318f7cc631fb98c63ff508c7fca118df94231fea84637d508c7f8a118ffd5131bfaa263fe544c6fca898ff55131beaa263fc544c6f8a898ffd0d31ff21a63fd434c7f88698ffd4931bfa9263fe524c7faa498ff14931be29263ff424c7fc8498ff50931fe21263ff324c7fc6498ff4c931fe19263ff414c7fc8298ff50531fe20a63ff314c7ee6298ff8c531ef18a63ff504c6fea098ff94131fea8263fc504c6f8a098ffd5031bfaa063fe540c6fca818ff55031beaa063fc540c6f8a818df94c31ffa1863fe430c7fa8618ff10c31ffa9063fe520c6fca418ff54831bea9063fc520c7fe8418ff90831fea1063fc420c7fe6418ff8c831fe99063fc320c6fca218ffd0431ff20863fd410c7f88218ffcc431ef98863fe310c7ec6218ff4c431ee98863f5310c7aa6218ffd4031ff280637e500c7faa018df54031fe28063ff54c86fea990ff95321bf2a643fd54c86faa990ff15321be2a643ff53c86fea790ff94f21bf29e43fd53c86faa790ff14f21be29e43ff43c87fc8790ff50f21fe21e43ff42c87fc8590ff50b21fe21643ff32c87fc6590ff4cb21fe19643ff41c87fc8390ff50721fe20e43ff31c87fc6390ff4c721fe18e43ff50c87fca190df94321fea86437d50c87f8a190ffd5221bfaa443fe54886fca910ff55221beaa443fc54886f8a910ffd4e21bfa9c43fe53886fca710ff54e21bea9c43fc53886f8a710ffd0e21ff21c43fd43887f88710df54a21ffa1443fe42887fa8510ff10a21ff99443fe32887fa6510ff0ca21bf28c43ff41887fc8310ff50621fe20c43ff31887fc6310ff4c621fe18c43ff21887de4310fdc8621ffa8443fe50886fca110ff54221bea8443fc50887fea890dfd5121ff2a2437e54487faa890df55121fe2a2437c54487fea690dfd4d21ff29a437e53487faa690df54d21fe29a437c53487fe8690ff90d21fea1a43fc43487fe8490ff90921fea1243fc42487fe6490ff8c921fe99243fc32487fe8290ff90521fea0a43fc41487fe6290ff8c521fe98a43fc31487fe4290fdc8521ff10a43ee21487fea090dfd4121ff28243fd50487f8a090df14121ffaa0437f54087fca810df95021feaa0437d54087f8a810df15021ffa98437f53087fca610df94c21fea98437d53087f8a610df14c21ffa1843fe43087fa8610ff10c21bf29043ff42087fc8410ff50821fe21043ff32087fc6410ff4c821fe190437e51087fe8210ff90421fea0843fc410
  | 4 => 0x7f94042bf28085fd5010afaa0217f14042ffaa6657f54ccbfca9995f95332feaa6657d54ccbf8a9995f15332ffa1e65fe43ccbfa87997f10f32ffa1665fe42ccbfa85997f10b32ffa8e65fe51ccafca3997f54732bea8e65fc51ccbfea1997f94332bf28665fd50ccafaa1997f14332ffaa4657f548cbfca9195f95232feaa4657d548cbf8a9195f15232bea9c65ff438cbfc87197f50e32fe21c657e528cbfe85197f90a32fea1465fc428cbfe651977cca32f799465ff518cbfca3195f94632fea8c657d518cbf8a3197fd4232ff284657e508cbfaa1195f54232fe28465ff544cafea8997f95132bf2a265fd544cafaa8997f15132be2a265ff434cbfc86997f50d32fe21a65ff424cbfc84997f50932fe21265ff324cbde64997f8c932ef19265ff514cafea2997f94532fea8a65fc514caf8a2997fd4132bfa8265fe504cbfaa0997f14132be28265ff540cafea8197f95032bf2a065fd540cafaa8197f15032be2a0657e530cbfe86197f90c32fea1865fc430cafca4197fd0832ff21065fd420cbf884197fcc832ef99065fe320cbdc64197f4c832ee99065ed320cb9a64197fd4432ff288657e510cbfaa2195f54432fe28865ff500cbfca0195f94032fea80657d500cbf8a0197fd4f41ff29e837e53d07faa7a0df54f41fe29e83ff43d07fc87a0ff50f41fe21e83ff52d07fca5a0df94b41fea96837d52d07f8a5a0ffd0b41ff21683fd42d07f885a0ffccb41ff19683fd32d07f865a0ffd4341ff286837e50d07faa1a0df54341fe286837d54907fea720ff94e41bf29c83fd53906faa720ff14e41ffa1c83fe43907fa8720ff10e41ffa9483fe52906fca520ff54a41bea9483fc52907fe8520ff90a41fea1483fc42907fe6520ff8ca41fe99483fc32906fca320ffd0641dfa0c83f741907fea120ff94241bf28483fd50906faa120ff14241ffa9a837f53507fca6a0ff54d41fe29a837c53507fe86a0ff90d41fea1a83fc43507fea4a0dfd4941ff29283fd52507f8a4a0df14941ffa1283fe42507fa84a0ff10941ff99283fe32507fa64a0ff0c941ffa0a83f741507fc82a0ef90541ffa82837f50507fca0a0ff54141fe282837c50506fca820ffd4c41ff298837e53107faa620df54c41fe29883ff43107fc8620ff50c41fe21883ff52107fca420df94841fea90837d52107f8a420ffd0841ff21083fd42107f88420ffcc841ff19083fd32107f86420df94441ffa0883bf41107fc8220fd90441fea0883bd41107ea8220ed50441ffa8083fe50106fca020ff54041bea8083fc50107fea998dfd5331ff2a6637e54cc7faa998df55331fe2a6637c54cc7fe8798ff90f31fea1e63fc43cc7fea598ff94b31bf29663fd52cc6faa598ff14b31ffa1663fe42cc7fa8598ff10b31ff99663fe32cc7fa6598ff0cb31ffa0e63fe41cc7fa
  | 5 => 0x400000000001000800800000000400000400000c00000c00000400000000001000001c00001000800800000c01400800000000001c00800000002c00000000400000400800000400401800000000800000c00000800804400c00000000000000400001400800000000001400000400000000001400000000000000001000400400800000400000400800000000800000000000401000400000000000001c00000000000000c00000800c00400000400000400000400800400000000000000000400002800400000000800000400002400400400000400000000400802400800000c00002400000000000000800002400001400800801800001000001000400800400800400000c00000000000000000400801400400000001000000000800000000400001000000400801402000400001800800401801400c00400000001800400401400000000000001400000000c00c01800400000401000000800400000000400400400000000c01000400000ffea5a1ff94b43bf29687fd52d0efaa5a1ff14b43ffa8e87fe51d0efca3a1ff54743bea8e87fc51d0ffea1a1ff94343bf28687fd50d0efaa1a1ff14343beaa4877e5390ffe8721efd0e43efa1c87ff5290ffca521df94a43fea94877d5290ff8a521ffd4643ff28c877e5190ffaa321df54643fe28c87ff5090ffca121df94243fea84877d5090ff8a121ffd0d43efa1a87fe4350f7c86a1ffd4943bfa9287fe5250ffaa4a1ff14943be29287ff5150efea2a1ff94543fea8a87fc5150ef8a2a1ffd4143bfa8287fe5050ffaa0a1ff14143be282877e5410efca621ffd0c43dfa1887fe4310fbc8621ff50c43dea1887dd4310f3a8621ffd4843ff290877e5210ffaa421df54843fe29087ff5110ffca221df94443fea88877d5110ff8a221ffd4043ff280877e5010ffaa021df54043fe28087ff53d0bfca7a15f94f42fea9e857d53d0bf8a7a17fd0f42ff21e85fd43d0bf887a17fd4742ff28e857e51d0bfaa3a15f54742fe28e85ff50d0bfca1a15f94342fea86857d50d0bf8a1a15f55242ffa9c85fe5390afca7217f54e42bea9c85fc5390bfe87217f90e42fea1c85fc4390afca5217fd0a42dfa1485ef4290bfea3217f94642bf28c85fd5190afaa3217f14642ffa8485fe5090afca1217f54242bea8485fc5090bfea6a15fd4d42ff29a85fd5350bf8a6a15f14d42ffa1a85fe4350bfa86a17f10d42ffa1285ef4250bfc84a16f90942ffa8a857f5150bfca2a17f54542fe28a857c5150bfea0a15fd4142ff28285fd5050bf8a0a15f14142bf2a085ff5310bfca6215f94c42fea98857d5310bf8a6217fd0c42ff21885fd4310bf886215f94842ffa1085bf4210bfc84217b90842fea1085bd4210bda84216b50842ffa8885fe5110afca2217f54442bea8885fc5110bfea021
  | 6 => 0x2d78000460000000001e499c82f2a9a7880000000000003e1421d70000af8000000000001978001a900000018e80000031e317af49ea94080000000032482a80035380023714726d0000000000000000000002ea1928000001e700000000001318031aa8313726fa4e25223f0002200000868000b58000001008001760c50000002c500000029a80000000009697e81080001600005d1af1b180013da4585800026c8e30000000000000001441410d20000000001bb00000014f22f0000f400030b8f20000000002bf8000000000001740d52fb2a48000000002d680000027c0000000000000900000000000000000002598000001a720d8000000c98000000d49b98668842622b90ae12a80e20ba3395e8000000000000000221148bb0732c68000000000002eb22700000000000000000000000016b8d000c8000001249aa84b80000000000032a00000017700001780005e954a381ca0000000000000000000fd9fe8000000000000318230000a2b3f0000598000002c102700000018133ca6400019d01b0000000e00000000fc00000000000006480000025c8002b98000268000000610000000000002908000002708c092b0df0000000002c980000005000000022a13a844a9c00000000000000000026ea220000d5b311de00015b8000001f800000000000000003d13ca3a8000002358001720001f580005400001830e8000000000000000002ed986a54891800000000356000000000000000002800400001000800c00400400000400401401000001800000800000002000001801000000000800800000c00000400000000400000000800c01000400001800000000000c01400000000400002800400400000001c00000400400000c00800402400000000000c00400400800000801000000000000000000000000400000000c01400000c00400c00400000c00800000000000c00000c00000000000000400000400002c00400400400400801400000000000000000000000400400400000800800401800c01400001801000000400c00000c00000000000c00000000000000801000c01000000400c00000c00000000000001400000400002800400000800400800c00400401c00000400001001000400400000001c00000000400000000c00000000800000002c00000000002001000000400000000800000000000401000400800000000000000000c01400000002000000400400000000802400000001800400000400001c01001c00000400800400400000000001000c00400000000800800400000800c00000400000000000400000000000000000000000800000400000400000400002801001000001001801400400000800800800800000000000000400000000800400000000000001400c00c0000000000000000040080080040
  | 7 => 0xf481680034080000000008d85b00000000012302c80680019080023b00235580000000000000031f99500000022380032300010608c1ee8548a51be8a10002629489870000000000000000000000000003442d0a4c8000000002182b880010e8d68000000000000002278000002b091400000000000000000000000000000018f8000002e30ee00000002290b25180003f2e7adf0000000000001df80006d000000000000000000000296a561b60f600000007500000000011b800000000000000323a8d2f110486b8000000000000aa000250af5967b4e00007c17a0002e295211a2ec2120128002c89c3b070000a600000001b800000038b5100000016202c00000000000013b0000000000000000002b12848001949361a580000000008e8000000002be11080022187632f0911e22e48000000000000001c8ae5208a780000000000000000002f31310000002888000308000000000000000002440000000002dfa911b5b2b99927e21b12c018b1610c8001d38000000001a69c230200029d26180009d11f0000000000000000b2a839cfaaaa2b8048000cd80017000000031d2a60080e783aa5d0bb80029806e0c8a268000000000008940001cc9a50001e634c21b80001e80000000011c9fd0000342da0000000000000001b10002c28000c38000a180019f881add8002d3a5da5aab3b3500000000000030f0000001f30000000cc2f2ae18000000f380000000000028c1af93185f8000000000000000002ae00000000023f8000000000000000000000000000000000000ab09729f16894d070b54800098b2000000000030600020d00000000000031b0519da0000000000a9922149159b4216700004f0000001f1b500002d800013bb0d0001c0b290000002a0a5909b0f980000000009980000000000032facf29400000028780031980000004a00021310a00007b0000000dd0000000000000000ef22f800000000000329a0200000000031305c8ec80000021080005780007880000000033fb2080000000000000000000000000000011280000000012900017f24d8000001d6000155a8533e0002710000cc8078ce00000024b00026a0000000000000c00002040000003092e20e880031680025c1d08002dcb331f03118000000000ba1f70000001ac0bf8000000000000000000003520ac000000266169b1c00000020580028000000000000012e80000000000027a97480000011e8001fc2e41db0000000b70000000000000000001bf0000000000001fe00000000000000000000000007d23b80000d00000000034d00014e0000000000000000000000001fb11fb3c09e0000002ef1879790f7800127008aa000017780014685214c8001c98608602902148468801f0aaf0b180013280016f2b20001c732e83fa740311bc0d40000000c4
  | 8 => 0x801100000000000013207d8410a83381542768002ec96580000e80022909b8280fa95c972ade0000000000001cd0000000000002ae9308db2f62c4a950000b49b40000348098dd8001750000000000000000000000000000001a000000000000000000000000000000000017800000003618aab80711b834500034f85604e34d8920001be2d4b4c8000000ac80000000000012296a18b800083000087a600378c480000000031280009f0bda3a0001cd9f280031a02625e0b010000000000022a9579860cbb432252400c30b312b9708000000000000002082228620fb8e28588000a00003028001ac8000001428000000000572ac8000000000000000000000000000000dea1a8000000000000002489ab32500000000019c0000000000001338768000000640002c580000006780000000031b8000000001eda7f8a40dbb28125800211024334ae90e680011600000000000000000000000000000000000000000012e04b351a578000000000000002cd8f120180000001182380010880000014b0000060d280000000000000004980000003811300033a34a1c90eb00020900000000000000000034980580000000015a8002860c600000000000000000000000000028f00000034180027180020380000000000000002000000032880000000016c0bc8cd1ef8002db8002808000001ad8000bf0000000001a600014f8001c60000000000002a59330871ddacb0000000b202e26098496f80000019b8000001d3101000000000000196b0115f9fb8001a80001e90002e380017d15624085a225b370000e3ae700003babb0ff8000002448000000001d180011180020027593796c8000000000002930002fe00018c8e200000033000032104c8000000002aa0002dc2918003032f7af88002b7a388001b3000000000344b2c8670000000000c580008c8000000000591438000000002498000001639158000001818000000000000000000000880000000000a5b3d8000002c023c32600022093e0001ec1e300000000b0000002550f527c8002302c73390ca2e580027218818f16282b0003181d48000000000001d801919395f0012fea6b20aa06af00f72c400026a8000001ba0000f000002a2868000000002a400007386c28c8001020000003108000000000000000002460d391a8002190000000000000000000680d60002993490e480000000f84c0950000003150040000418000d09168002c800000030b0002c20001552fa1dea5a00031f2da8000000001b70000000002fbb4b000000000013af50000000000000000003268799dd1a300005080000000026700021f8000000000002cc00000000000001c0000001079ceb04ad303680000000025400000000022c1a403981d1d00000000000000002010718001530ea32d23407ea5f0039c49
  | 9 => 0x80000000000000000009d80000000000000020f8000000002cf8f300000c0e080000023180000000010d80000000000000000005c0000000001600001f43050001a28000002ab95c0000001da8000000000ed00000002100000000005a8000002a517d80024ea97800040000156939ae80000000939028002bc00000000010d08580000003c80000012c800267a762142390be80000032e0000002f18e50000000000850002ce12a00010922c80018203580000032200020b0000fd1c79b38000000000000001d280000000000002f8000000000000000eb800000217258b039852422a1198209b06a6f13a32721a24500000022b19000000009a2558000700001fa2ba8438001ea00b98e0001ffa3c8658000000000000000000000000000001218000001120000000000f88b080006516e0151888000002f38370000000ab8000003149b0820b2296920513eaa89ca8898dc8000000000000100000000000003398000000000320f48f28001bd1c18000a700016400000000000032799d8002fd0000000002958000001e5000000000000335b01800000000062a8d8000000000000000001919f53000000002b331701a80000000029d8000000000002491508c100026e00000030980000000020c0001f3afc8000001e027981400000000008a9cf0000d10000002f81202cd0000000000002f925f83a1083088000b880000013880000000000000029e1038001a48001e389780a00000030e00000022429b8ea8002b680000000000000000000000000028bae030a0000001e78000000bc000000266b0c33e800000000000268afa8000002b48838001a188f0001c000000000000000000020e80000000000000000023286a13900022da6300000000029b3488001dc000000047800000000000118a9980000000015396e80009599b2008b12d22280778550002483110a38fb22485594e9c400016d8001478001f600012800000027b000000341000182ab00a30000de00000023d80015294499114a042a8f92780003b15821880000000006e8000000000000002128002570638000001898000000000002a192d1d111d285861a7a3438002cb88600000004580000026b93500000005680000000014807200000000034f33b23981c800000000000000000000315a5112380023780000032a81d9451f9000000000185b531e28b79eb00000028e8001bb8000000632921808002af80000000018b0001ab800000000000105b1c8000001608000000002ee28900000008080000027d9f7aa780000000000017c0000000660000000430000510000001d40000c78000000000000cb17a800000164800000000000000000040800000126800000298800000264ad8894b4a9fd80021e34281f2e60000000003318000000002178002e128b2bc8000001e
  | 10 => 0x11500008b03d8000000000003120000000000000000000c29e987700000004813d0001c11e68000072138000000000000a78000000001fa9650000000002299e4192025afda960000002e08148292ca80022e00033608fa320000000000a68000002eeb3d16307480000000000000000000000000021680019a00027e8f82fc24d31916b0a0aa921987b91133080000000020f06a800017338800000230800015acca9f9f20000001190000990000000000000cf9bd80004d80000014d8050001eca539731a200013580029a0002f20000001d580009604900027f00030dac300000007580000006f0002639d880000015880013431400000000000000011d80028a2ba2478ae9ee30a80000010bb460002289068000002330b500027517583c000000000000000000101b320000000000000000000000e934e8790d70000000be0000a90000000001b28350001668e40f6929a3621c0b98c80fc8000002c91b00000003528729ff2a300000034700023e0539f997f9d2090b081240df8000d80000028002820c68000002b293f8000000000000000000001830b680000000033b94aad90000000001418000000002700000000000002b50288000af0002c780000000000018a0000000002692a809c949a9c8000000000001789458000001368000000002a280000000020780000000000000000000000000000000014032b289abe8001ef00000000000032d80024f8002d280000000031eaeb80000004e80d8000000002ef80000000007400000000015d0a89660000000001c5a7316113f0000d7ab72ed1460000e804d00000002d80000000000000000005b80018419617c8002d407a8000000003458000000c913c2581e10298000000000000000bd0ad16a8000000d897b10715b1df0000000003368000002de80000000023480000023e8000000000002bf0000000000e9a4a87a00028100000014c1a98dc00027b8002828000000000002c380000000000009a8000000000000001a10b6000000000176800000000173a212939b9236893272a42a9716d07f1cbaf09041b694333a80a95d8000b39710ce91e0001bf90a80003308e00021f0000002f70018000002410000000003258000adae999eabd0090000002c180004f8ba9ae00000000000000021608927718d0000828002ac01fa0a00000000000007c8002f998c0000000ef9100000000000000000000000000fa0001b480017e00000004200000000000000000000030780000000000006f8000000001510000000d314b9c680000007fa1d12110c06d8000000000000000002ad00000020302e80000000000000000011c00000000000019700024b852b339c50000000690f9000337b4b8000002ff00000000002d1e199ab0f800019a650001178001500fe2ea8001958000001a0
  | 11 => 0x2882311aa00f0000001bc8d18001252d18000002a699300016180000000017bad00000002d505d80010e09e920a738002d700028400000001e24c1d68440002e695e08d00000000009280000020e0001ae8ed80009f8471b88000000ff0000000cf2418000000000000002c0a351eb80000000000000000000025000000000027d0a48e180018d80012f8000000000002dd26daa22b1abd8002438120000002791c28b425e800000138171b13a779ba9d500020725280024300000021c82bb480000000000000000002c60001518002230001ce1941b506c8000000000000000000000001050000ca80000000000003900011b0003400000da2698d900000005f25bae88001a3ab62d60001e8aca0000820a20000e70000002948000c20000001c80002ff80005301a0000000001f888a2658000000001ed2612b403031da4a0003508fe8250f18001138001d792d80028a99880008880000000000000003e8001cc2db0002260000e100032c0000000000000000000000339d900000000000010f8000000002530001e599f2a720280000021e8000002a390300000000000000000025b00000012600000000000000000009c000000000356b342470811dc8e58698b924f000000268300b240000000000000031180248452ab000000000048ad10000000001d980029285e10f068a1192f027a2d0000000003058000000daace8d980015729e9170002158ee8002b580000009810980025680000035500000000000000021532180000000000000000000007e0000001590000ec20c9a880000000030c88b8000002870000000000003328001a780000000000000018380000000000000000000022e80000000000019980000026c0aaa10000000000168000310084b468000c1ad99348000002060000000000000000000001dba46af400000000007823d0000001799cb0001300002f6ad58000000000000f58001c303280000012880000000000000000000018900000027499e06b0003188001fc800347a8e00004a8000000000000000000000218001198000002bb9e08000f08003540000001b20000e600000000028180000000000021d8003040001f11ad1b78c70000002048001f6aad95a0b80
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x6320427c658c810db94a320436d528c8109fd95320427e654c8109f595320427c654c810d794d320435d534c810db949320436d524c810bdd8532042f4614c810bed8132042f8604c8109fd94320427e650c8109f594320427c650c810f34c8320427e64944109f592510427e63944109f58e510427e62944109f58a510427d65d04109fd96410427d6590410cf952410433d5490410be98241042f960904109fd95410427f65104109f594410433e5410410cf55041043b54110410be98041042f960104109f597310427f658c4109f596310435e538c410d754e31042fa608c410be582310427f654c4109fd94310427d650c410d794c310435d530c410f54c431042fa600c410be580310427d65c84109fd96210427d6588410db94a210436d5288410be98221042f960884109fd95210427f65084109f594210436e5208410db54821043e52108410be98021042f960084109f992500427d64940109f98e500427d63940109f98a500427d62940109f586500427d65d00109fd96400427d6590010cf952400433d5490010bd98640042f561900109fd95400427f65100109f994400427d65100109f194400433e5410010cf55040042f66110010bd58440043b940100109f597300427f658c0109f596300435e538c010d754e30042f6618c010bd586300427f654c0109fd94300427e650c0109f594300427c650c010d794c300435d530c010bd98430042f5610c010f64c0300427d65c80109fd96200427d6588010db94a200436d5288010bd98620042f561880109fd95200427f65080109f994200427d65080109f194200436e5208010db54820042f66108010bd58420043e92008010dd59710042f56184010dd94610042f96584010de59610042796584010be58610042f16184010de94610043f251840109fd9510042f76544010ddd9510042776544010bdd8110043765044010fcd0110043f24044010fc50110043f04044010fccc110043f23044010fc4c110043f03044010fcc8110043f22044010fc48110043f02044010bed95100437b65440109ed9510042fb6144010fcd85100437a5144010fc94510043f34144010fc90510043f14144010fc10510043f33144010fc8c510043f13144010fc0c510043f32144010fc88510043f12144010fc08510043f36544010bcd9510043736544010fcd9110043f26444010fc59110043f06444010fcd5110043f25444010fc55110043f05444010fcd8d10043f26344010fc58d10043f06344010fcd4d10043f25344010fc54d10043f05344010fcd0d10043f24344010fc50d10043f04344010fcd8910043f26244010fc58910043f06244010fcd4910043f25244010fc54910043f05244010fcd0910043f24244010fc50910043f04244010fccc910043f23244010fc4c910043f03244010
  | 1 => 0x427e65881109fd95204427d65481109f195204436f5248110db14920442f76148110bd185204427e6508110fa48020443f350841109f98f540427d63d50109f98b540427d62d50109f987540437661d50109f983540437a60d50109f596540433f54950109f98e540427d63950109f98a540427d6295010cfd91540427f63550109f18d540427f62550109f189540427f61550109f585540427f60550109f581540433d5415010b798c54042dd6315010bb98854042ed62150109f990540433e64150109f98c540435e63150109798c540427d6315010d758c540425d63150109f988540436e62150109b988540427d6215010db588540426d62150109f984540437661150109f980540437a60150109f993530427d64d4c109f98b530427d62d4c109f987530437661d4c109f983530437a60d4c109f596530435f5394c109f992530427d6494c109f98a530427d6294c109fd91530427c6454c10d7d8d530427f6254c109f189530427f6154c109f585530427f6054c109f58153042be6414c10af590530435d5314c10bb98853042ed6214c109f990530433e6414c108f990530427d6414c10cf590530423d6414c109f98c530435e6314c109f988530436e6214c109b988530427d6214c10db588530426d6214c109f98453043766114c109f980530437a6014c109fd97430427e65d0c109f597430427c65d0c10cf953430433d54d0c109fd96430427e6590c109f596430427c6590c10d794e430435d5390c109fd95430427e6550c109f595430427c6550c10cf951430433d5450c10d794d430435d5350c10bdd8543042f46150c10bed8143042f86050c109fd94430427e6510c109f594430427c6510c10e750c430427e64d48109f593520427e63d48109f58f520427e61d4810dd987520427e60d4810de983520427d6594810dbd4a520427e64948109f592520427e63948109f58e520427f64548109f191520427f63548109f18d520436f62548109fd85520427d61548109fd81520427d6054810af99052042bd6414810b798c52042dd6314810db548520427e6414810cf990520423e64148109f590520433d64148108f590520427e6314810d798c520425e63148109f58c520435d63148109758c520427e6214810db988520427e6114810dd984520427e6014810de980520427f65d08109f997420427d65d08109f197420433e54d0810cf553420427f65908109f996420427d65908109f196420436e5290810db54a420427f65508109f995420427d65508109f195420433e5450810cf551420436e5250810db54942042f76150810bd18542042fb6050810be181420427f65108109f994420427d65108109f19442043ad42108109fd97320427e65cc8109f597320427c65cc810d794f320435d53cc8109fd96320427e658c8109f59
  | 2 => 0x6414d109f590534435e6314d109f988534427d6214d109f984534427c6114d109f980534427c6014d109fd97434427e65d0d109f597434427c65d0d10d7d4f434435c53d0d109fd96434427e6590d109f596434427c6590d10cfd52434433c5490d109fd95434427e6550d109f595434427c6550d109fd94434427e6510d109f594434427c6510d10cfd50434433c5410d10d7d4c434435c5310d10e750c43442f66110d10bd58443442fa6010d10be580434427e64d49109f593524427e63d49109f58f524436f52949109f992524427d64949109f98e524427d63949109f98a524427d6194910dd586524427d6094910de58252442bf6454910af19152442df6354910b718d524427f6454910cfd91524423f64549109f191524433c64549108f191524427f6354910d7d8d524425f63549109f18d524435c63549109718d524436f62549109fd85524437761549109fd81524437b60549109f994524436d52149109f990524427d64149109f98c524427d6314910db988524427e61149109f184524427e60149109f180524427f65d09109f997424427d65d09109f197424436f52d0910db14b424427f65909109f996424427d65909109f196424433f5490910cf152424427f65509109f995424427d65509109f195424427f65109109f994424427d65109109f194424433f5410910cf150424436f5210910db14842443ad4210910bd98442442f56110910be98042442f960109109fd97324427e65cc9109f597324427c65cc910dbd4b324436c52cc9109fd96324427e658c9109f596324427c658c910d7d4e324435c538c9109fd95324427e654c9109f595324427c654c9109fd94324427e650c9109f594324427c650c910d7d4c324435c530c910dbd48324436c520c910f34c832442f6610c910bd58432442fa600c910be580324427e65d0510cfd53414433c54d0510be98341442f960d05109f996414427c6550510cfd51414433c5450510bed8141442f860505109f99441443b541105109f997314435f53cc510d714f31442fa60cc510be583314427e658c5109f195314435f534c510d714d31442fb604c510be181314427e650c510f54c4314427e65c8510dbd4b214436c52c8510be98321442f960c85109f996214427c6548510dbd49214436c5248510bed8121442f860485109f99421443e521085109f997404433f54d0110cf15340442f661d0110bd587404427e65901109fd95404427d65501109f195404433f5450110cf15140442f76150110bd185404427e6510110ee500404427e65cc110d7d4f304435c53cc110bd98730442f561cc1109f996304427f654c1109f595304427c654c110d7d4d304435c534c110bdd8530442f4614c1109f99430443d9300c1109f997204436f52c8110db14b20442f661c8110bd587204
  | 3 => 0xe10bd185438427f6510e109f994438427d6510e109f194438439d4310e10be98043842f96010e109f993528427d64d4a109f98f528427d63d4a10dd587528437a60d4a10dbd4a528427e6494a109f592528427e6394a109f58e528427f6454a109f191528427f6354a109f18d528436f6254a10db548528427e6414a109f590528427e6314a109f58c528436e6214a10dd584528437a6014a109fd97428427e65d0a109f597428427c65d0a109fd96428427e6590a109f596428427c6590a109fd95428427e6550a109f595428427c6550a10bdd8542842f46150a109fd94428427e6510a109f594428427c6510a10eb50842842fa6010a10be580428427f65cca109f997328427d65cca109f197328427f658ca109f996328427d658ca109f196328427f654ca109f995328427d654ca109f19532842f7614ca10bd185328427f650ca109f994328427d650ca109f19432843cd320ca10be98032842f9600ca10cf953418433d54d0610be98341842f960d0610cf951418433d5450610bed8141842f86050610ed504418435e53cc610d754f31842fa60cc610be583318435e534c610d754d31842fb604c610be18131843d5310c610db94b218436d52c8610be98321842f960c8610db949218436d5248610bed8121842f86048610f9484218433e5490210cf55240842f66190210bd586408433e5410210cf55040842f66110210bd58440843b94010210d794e308435d538c210bd98630842f5618c210d794c308435d530c210bd98430842f5610c210f64c0308436e5288210db54a20842f66188210bd586208436e5208210db54820842f66108210bd58420843e92008210bd597108437565c4210be597108437965c42109f98f544427d63d51109f98b544427d62d5110cfd52544427e64951109f98e544427d63951109f98a544427d62951109f586544437561951109f58254443796095110b7d8d54442dc6355110bbd8954442ec6255110cfd91544427f6355110d7d8d544425f63551109f18d544435c63551109718d544427f6255110dbd89544426f62551109f189544436c62551109b189544427f6155110ddd85544427f6055110ded81544427e6515110cf550544433e64151109f98c544427d63151109f988544427d62151109f984544427c61151109f980544427c60151109f993534427d64d4d109f98b534427d62d4d10d7d4e534427e6494d109f592534427e6394d109f98a534427d6294d109f58653443756194d109f58253443796094d10afd9153442bc6454d10bbd8953442ec6254d109fd91534433f6454d108fd91534427c6454d10cf191534423c6454d10d7d8d534427f6254d10dbd89534426f6254d109f189534436c6254d109b189534427f6154d10ddd85534427f6054d10ded81534427e6514d10d754c534427e
  | 4 => 0xf58a53c427f6454f109f19153c435f6354f109fd8953c427c6254f10d754c53c427e6414f109f59053c435e6314f109f98853c427d6214f10dd98453c43796014f109fd9743c427e65d0f109f59743c427c65d0f109fd9643c427e6590f109f59643c427c6590f109fd9543c427e6550f109f59543c427c6550f10bed8143c42f86050f109fd9443c427e6510f109f59443c427c6510f10e750c43c42f66110f10bd58443c427e64d4b109f59352c427e63d4b109f58f52c437661d4b10de58352c436f5294b109f99252c427d6494b109f98e52c427d6394b109fd9152c427c6454b109fd8d52c427c6354b10dbd8952c436d5214b109f99052c427d6414b109f98c52c427d6314b10db98852c43766114b10de58052c427f65d0b109f99742c427d65d0b109f19742c427f6590b109f99642c427d6590b109f19642c427f6550b109f99542c427d6550b109f19542c42fb6050b10be18142c427f6510b109f99442c427d6510b109f19442c43ad4210b10bd98442c42f56110b109fd9732c427e65ccb109f59732c427c65ccb109fd9632c427e658cb109f59632c427c658cb109fd9532c427e654cb109f59532c427c654cb10bed8132c42f8604cb109fd9432c427e650cb109f59432c427c650cb10f34c832c42f6610cb10bd58432c433e5490710cf55241c42fa6090710be58241c433e5410710cf55041c43b54110710be98041c42f96010710d794e31c435d538c710be98231c42f9608c710d794c31c435d530c710f54c431c42fa600c710be58031c436e5288710db54a21c42fa6088710be58221c436e5208710db54821c43e52108710be98021c42f96008710cf95340c433d54d0310bd98740c42f561d0310cf95140c433d5450310bdd8540c42f46150310ee50040c435e53cc310d754f30c42f661cc310bd58730c435e534c310d754d30c42f7614c310bd18530c43d9300c310db94b20c436d52c8310bd98720c42f561c8310db94920c436d5248310bdd8520c42f46148310fa48020c427e63d52109f58f548427e62d52109f58b548437561d5210de983548433f54952109f98e548427d63952109f98a548427d6295210cfd91548427f63552109f18d548427f62552109f189548433d5415210cf990548427e63152109f58c548427e62152109f58854843756115210de980548427e64d4e109f593538427e62d4e109f58b538437561d4e10de983538435f5394e109f992538427d6494e109f98a538427d6294e109fd91538427c6454e10d7d8d538427f6254e109f189538435d5314e109f990538427d6414e10d798c538427e6214e109f58853843756114e10de980538427f65d0e109f997438427d65d0e109f197438427f6590e109f996438427d6590e109f196438427f6550e109f995438427d6550e109f19543842f76150
  | 5 => 0x51082bd6414420b798c51082dd6314420dd544510827f65d04209f997410827d65d0420cf953410833d54d04209fd96410827e65904209f59641083765190420dd546410827f65504209f595410827c6550420cf951410833d5450420bbd8941082ec6250420dd94541083755150420bed8141082f860504209fd94410827e65104209f59441083b541104209fd97310827e65cc4209f597310835e53cc420d754f310827f658c4209f996310827d658c420dd9463108375518c4209fd95310827d654c4209f195310835e534c420d754d31082ef624c420bb1893108376514c420dd54531082fb604c420be181310827f650c4209f994310827d650c420f54c4310837651c8420dd54721082fa60c8420be583210827d65884209fd9521083765108420dd54421083e52108420be98021082f960084209f992500827d64940209f98e500827d63940209f597400827f65900209f596400833e5490020cf55240082ee6290020bb58a400827f65500209fd94400827e65100209f594400827c6510020cf950400833d5410020bb98840082ed6210020ee500400827d65cc0209fd96300827d658c020d794e300835d538c020bb98a30082ed628c0209fd95300827f650c0209f994300827d650c0209f194300835e530c020d754c30082ee620c020bb58830083d9300c020bb58a200836e5288020be58a20082e96288020de94a20083ea52880209fd9520082ef6548020dbd95200826f6548020bbd81200836e5048020fad0120083ea4048020fa50120083e84048020facc120083ea3048020fa4c120083e83048020bed95200837b65480209ed9520082fb6248020fad89200837a5248020fa94920083eb4248020fa90920083e94248020fa10920083eb3248020fa8c920083e93248020fa0c920083eb2148020fa88520083e92148020fa08520083eb6548020bad95200836b6548020fad9120083ea6448020fa59120083e86448020fad5120083ea5448020fa55120083e85448020fad8d20083ea6348020fa58d20083e86348020fad4d20083ea5348020fa54d20083e85348020fad0d20083ea4348020fa50d20083e84348020fad8520083ea6148020fa58520083e86148020fad4520083ea5148020fa54520083e85148020fad0520083ea4148020fa50520083e84148020facc520083ea3148020fa4c520083e831480209f98f54c427d63d53109f98b54c427d62d5310dd98754c437960d5310cfd5254c427e63953109f58e54c427e62953109f58a54c433f64553109fd8d54c427c63553109fd8954c427c6255310cf55054c433e64153109f98c54c427d63153109f98854c427d6215310dd98454c437960153109f99353c427d64d4f109f98b53c427d62d4f10dd98753c437960d4f10d7d4e53c427e6494f109f59253c427e6294f109
  | 6 => 0x27c654c5209f994314827d650c5209f194314835f530c520d714c31482ee620c520bb5883148377510c520dd14431483d5310c520be98031482f9600c5209f99721483775188520dd14621482fa6088520be58221483775148520dd14521482fb6048520be181214827e6508520f9484214827e65d0120cfd53404833c54d0120bb98b40482ed62d01209f996404827f65501209f595404827c6550120cfd51404833c5450120bbd8940482ec62501209f99440483b940101209f997304835f53cc120d714f30482ee62cc120bb58b304827e658c1209fd95304827d654c1209f195304835f534c120d714d30482ef624c120bb189304827e650c120f64c030483eb50881209f98f540827d63d50209f98b540836e62d50209f987540827d61d50209f983540837a60d50209f596540833f54950209f98e540827d63950209f986540827d6195020cfd91540827f63550209f18d540827f62550209f589540827f61550209f185540833d5415020b798c54082dd6315020bd98454082f561150209f990540833e64150209f98c540835e63150209798c540827d6315020d758c540825d63150209f988540836e62150209f984540837661150209d984540827d6115020dd584540827561150209f980540837a60150209f993530827d64d4c209f98b530836e62d4c209f987530827d61d4c209f983530837a60d4c209f596530835f5394c209f992530827d6494c209f986530827d6194c209fd91530827c6454c20d7d8d530827f6254c209f589530827f6154c209f18553082be6414c20af590530835d5314c20bd98453082f56114c209f990530833e6414c208f990530827d6414c20cf590530823d6414c209f98c530835e6314c209f988530836e6214c209f98453083766114c209d984530827d6114c20dd58453082756114c209f980530837a6014c209fd97430827e65d0c209f597430827c65d0c20cf953430833d54d0c209fd96430827e6590c209f596430827c6590c20d794e430835d5390c209fd95430827e6550c209f595430827c6550c20cf951430833d5450c20d794d430835d5350c20bbd8943082ec6250c20bed8143082f86050c209fd94430827e6510c209f594430827c6510c20e750c430827e64948209f592520827e63948209f58e520827d65d08209fd96420827d6590820cf952420833d5490820be98242082f960908209fd95420827f65108209f594420833e5410820cf55042083ad4210820be98042082f960108209f597320827f658c8209f596320835e538c820d754e32082fa608c820be582320827f654c8209fd94320827d650c820d794c320835d530c820f34c832082fa600c820be580320837751944209f992510827d64944209f98e510827d63944209fd91510827c64544209fd8d510827c6354420af990
  | 7 => 0x490220cf55240882ee6290220bb58a408833e5410220cf55040882ee6210220bb58840883b94010220d794e308835d538c220bb98a30882ed628c220d794c308835d530c220bb98830882ed620c220f64c030882ed65c8220db59720882f965c8220de597208827e63d51209f58f544827e61d51209f587544833f54951209f992544827e63951209f58e544827d6295120db58a544827e61951209f586544827d6095120de58254482df6355120b718d54482f76155120bd185544833f64551209fd8d544835f635512097d8d544827c6355120d718d544825c63551209fd89544836f62551209fd85544837761551209dd85544827c6155120dd185544827461551209fd81544837b60551209f994544833d5415120cf990544827e63151209f58c544827e62151209f188544827e61151209f584544827e64d4d209f593534827e61d4d209f587534835f5394d209f992534827d6494d209f98e534827d6294d20db58a534827e6194d209f586534827d6094d20de58253482bf6454d20af19153482f76154d20bd185534827f6454d20cfd91534823f6454d209f191534833c6454d208f191534835f6354d209fd89534836f6254d209fd8553483776154d209dd85534827c6154d20dd18553482746154d209fd81534837b6054d209f994534835d5314d209f990534827d6414d20d798c534827e6214d209f188534827e6114d209f584534827f65d0d209f997434827d65d0d209f197434835f53d0d20d714f434827f6590d209f996434827d6590d209f196434833f5490d20cf152434827f6550d209f995434827d6550d209f195434827f6510d209f994434827d6510d209f194434833f5410d20cf150434835f5310d20d714c434839d4310d20bb98843482ed6210d20be98043482f96010d209f997424833f54d0920cf15342482fa60d0920be583424827e65909209f195424833f5450920cf15142482fb6050920be181424827e6510920eb508424827e65cc920d7d4f324835c53cc920be98332482f960cc9209f996324827c654c920d7d4d324835c534c920bed8132482f8604c9209f99432483cd320c9209f993514827d64d45209f98f514827d63d4520ddd4651482bf6454520af19151482df6354520b718d514837551145209f990514827d64145209f98c514827d63145209f997414827d65d05209f197414837751d0520dd147414827e65905209f596414827c6590520cfd52414833c54905209fd95414827e65505209f195414827e65105209f594414827c6510520cfd50414833c5410520bb98841482ed6210520ddd4441483745110520ed50441482fa6010520be580414827e65cc5209f597314827c65cc520ddd47314837451cc5209f996314827d658c5209f196314835f538c520d714e314827f654c5209f9953148
  | 8 => 0x20d754c32c83cd320cb20be98032c82f9600cb20ddd4651c827e64947209f59251c827e63947209f58e51c827f64547209f19151c827f63547209f18d51c837551147209fd9741c827e65d07209f59741c827f65907209f99641c827d65907209fd9541c827d65507209f19541c82fb6050720be18141c827f65107209f99441c827d6510720bb98841c82ed6210720ed50441c827f65cc7209f99731c827d65cc7209fd9631c827e658c7209f59631c827f654c7209f59531c827c654c720bed8131c82f8604c7209fd9431c827e650c7209f59431c82ee620c720bb58831c83d5310c720dd94721c837551c8720be98321c82f960c8720dd94421c83755108720f948421c82fa6008720be58021c833e54d0320cf55340c82ee62d0320bb58b40c833e5450320cf55140c82ef6250320bb18940c83b94010320d794f30c835d53cc320bb98b30c82ed62cc320d794d30c835d534c320bbd8930c82ec624c320f64c030c827e63d52209f58f548836d62d52209f987548827d61d5220de983548833f54952209f98e548827d63952209f986548827d6195220cfd91548827f63552209f18d548827f61552209f185548833d5415220cf990548827e63152209f58c548836d62152209f984548827d6115220de980548827e64d4e209f593538836d62d4e209f987538827d61d4e20de983538835f5394e209f992538827d6494e209f986538827d6194e209fd91538827c6454e20d7d8d538827f6154e209f185538835d5314e209f990538827d6414e20d798c538836d6214e209f984538827d6114e20de980538827f65d0e209f997438827d65d0e209f197438827f6590e209f996438827d6590e209f196438827f6550e209f995438827d6550e209f19543882ef6250e20bb189438827f6510e209f994438827d6510e209f194438839d4310e20be98043882f96010e20cf953428833d54d0a20be98342882f960d0a20cf951428833d5450a20bed8142882f86050a20eb508428835e53cca20d754f32882fa60cca20be583328835e534ca20d754d32882fb604ca20be18132883cd320ca20ddd46518827e64946209f592518827e63946209f58e518827f64546209f191518827f63546209f18d518837551146209fd97418827e65d06209f597418827f65906209f996418827d65906209fd95418827d65506209f19541882ef6250620bb189418827f65106209f994418827d6510620ed50441882fa6010620be580418827f65cc6209f997318827d65cc6209fd96318827e658c6209f596318827f654c6209f595318827c654c620bbd8931882ec624c6209fd94318827e650c6209f59431883d5310c620be98031882f9600c620dd94621883755188620be98221882f96088620dd94521883755148620bed8121882f86048620f9484218833e5
  | 9 => 0xd94410c27e65104309f594410c3b54110430dd947310c37551cc430be983310c2f960cc4309f596310c27f654c430dd944310c375510c430f54c4310c2fa600c430be580310c27f65c84309f997210c27d65c8430db94b210c36d52c84309fd96210c27e65884309f596210c3765188430dd546210c27f65484309f595210c27c6548430b7d8d210c2dc6348430db949210c36d5248430dd945210c3755148430bed81210c2f860484309fd94210c27e65084309f594210c3e521084309f992500c27d64940309f597400c27f65900309f596400c33e5490030cf552400c2de6390030b758e400c27f65500309fd94400c27e65100309f594400c27c6510030cf950400c33d5410030b798c400c2dd6310030ee500400c2dd638c030d794e300c2f9638c030b658e300c37a538c030f694e300c27f654c030b7d95300c35f654c03097d95300c2df604c030d7941300c3db404c030f6901300c3d9404c030f6101300c2fb654c030ded95300c27b654c030bed8d300c3db634c030de94d300c3da534c030f6d0d300c3da434c030f650d300c3d8434c030f6cc9300c3da324c030f64c9300c3d8324c030f6cc5300c3da314c030f64c5300c3d8314c030f6d95300c2db654c030d6d95300c3db644c030f6991300c3d9644c030f6191300c3db544c030f6951300c3d9544c030f6151300c3db624c030f6989300c3d9624c030f6189300c3db524c030f6949300c3d9524c030f6149300c3db424c030f6909300c3d9424c030f6109300c3db614c030f6985300c3d9614c030f6185300c3db514c030f6945300c3d9514c030f6145300c3db414c030f6905300c3d9414c030f6105300c3db214c030f6885300c3d9214c030f6085300c27e63d53209f58f54c836e62d53209f98754c827d61d5320de58354c833f54953209f98e54c827d63953209f98654c827d6195320cfd9154c827f63553209f18d54c827f61553209f18554c833d5415320cf99054c827e63153209f58c54c836e62153209f98454c827d6115320de58054c827e64d4f209f59353c836e62d4f209f98753c827d61d4f20de58353c835f5394f209f99253c827d6494f209f98653c827d6194f209fd9153c827c6454f20d7d8d53c827f6154f209f18553c835d5314f209f99053c827d6414f20d798c53c836e6214f209f98453c827d6114f20de58053c827f65d0f209f99743c827d65d0f209f19743c827f6590f209f99643c827d6590f209f19643c827f6550f209f99543c827d6550f209f19543c82fb6050f20be18143c827f6510f209f99443c827d6510f209f19443c839d4310f20bb98843c82ed6210f20cf95242c833d5490b20be98242c82f96090b20cf95042c833d5410b20eb50842c82fa6010b20be58042c835e538cb20d754e32c82fa608cb20be58232c835e530cb
  | 10 => 0x14c33f5490530cf152414c27f65505309f995414c27c65505309f994414c27d65105309f194414c33f5410530cf150414c2de6310530b758c414c3775110530dd144414c3b54110530be980414c2f960105309f997314c377518c530dd146314c2fa608c530be582314c377514c530dd145314c2fb604c530be181314c27e650c530f54c4314c27e65c85309f597214c27c65c8530ddd47214c37451c85309f996214c27d65885309f196214c36f5288530db14a214c27f65485309f995214c27c65485309f994214c27d65085309f194214c2de6308530b758c214c36f5208530db148214c3775108530dd144214c3e52108530be980214c2f960085309f997404c33f54d0130cf153404c2de63d0130b758f404c27e65901309fd95404c27d65501309f195404c33f5450130cf151404c2df6350130b718d404c27e6510130ee500404c3db508c1309f98f540c35e63d50309f98b540c27d62d50309f987540c27d61d50309f983540c37a60d50309f596540c33f54950309f98a540c27d62950309f986540c27d6195030cfd91540c27f63550309f58d540c27f62550309f189540c27f61550309f185540c33d5415030bb988540c2ed6215030bd984540c2f561150309f990540c33e64150309f98c540c35e63150309f988540c36e62150309b988540c27d6215030db588540c26d62150309f984540c37661150309d984540c27d6115030dd584540c27561150309f980540c37a60150309f992530c27d6494c309f597430c27f6590c309f596430c33e5490c30cf552430c2fa6090c30be582430c27f6550c309fd94430c27d6510c30cf950430c33d5410c30e750c430c2fa6010c30be580430c36f52948309f992520c27d64948309f986520c27d61948309fd91520c27c64548309fd85520c27c6154830af990520c2bd6414830db548520c2f66114830bd584520c27f65d08309f997420c27d65d0830cf953420c33d54d08309fd96420c27e65908309f596420c36e5290830db54a420c27f65508309f595420c27c6550830cf951420c33d5450830b7d8d420c2dc6350830db949420c36d5250830bed81420c2f860508309fd94420c27e65108309f594420c3ad4210830db94b320c36d52cc830be983320c2f960cc8309f596320c27f654c830db948320c36d520c830f34c8320c2fa600c830be580320c37751944309f992510c27d64944309f98a510c27d62944309fd91510c27c64544309fd89510c27c6254430af990510c2bd6414430bb988510c2ed6214430dd544510c27f65d04309f997410c27d65d0430cf953410c33d54d04309fd96410c27e65904309f596410c3765190430dd546410c27f65504309f595410c27c6550430cf951410c33d5450430b7d8d410c2dc6350430dd945410c3755150430bed81410c2f860504309f
  | 11 => 0x7d6590a309fd95428c27d6550a309f195428c2df6350a30b718d428c27f6510a309f994428c27d6510a30eb508428c2fa6010a30be580428c36e528ca30db54a328c2fa608ca30be582328c36e524ca30db549328c2fb604ca30be181328c3cd320ca30ddd46518c27e64946309f592518c27e62946309f58a518c27f64546309f191518c27f62546309f189518c37551146309fd97418c27e65d06309f597418c27f65906309f996418c27d65906309fd95418c27d65506309f195418c2df6350630b718d418c27f65106309f994418c27d6510630ed504418c2fa6010630be580418c376518c630dd546318c2fa608c630be582318c376514c630dd545318c2fb604c630be181318c3d5310c6309fd97218c27e65c86309f597218c27f65886309f996218c27d65886309fd95218c27d65486309f195218c2df6348630b718d218c27f65086309f994218c27d6508630f9484218c2fa6008630be580218c33e5490230cf552408c2de6390230b758e408c33e5410230cf550408c2de6310230b758c408c3b94010230b7597308c35d65cc230be597308c37965cc2309f98b544c27d62d51309f987544c27d61d5130cfd52544c27e64951309f58e544c35d63951309f98a544c27d62951309f986544c27d61951309f582544c3796095130bbd89544c2ec6255130bdd85544c2f46155130cfd91544c27f6355130d7d8d544c27f6255130dbd89544c26f62551309f189544c36c62551309b189544c27f6155130ddd85544c27761551309f185544c37461551309d185544c27f6055130ded81544c27e6515130cf550544c33e64151309f98c544c27c63151309f988544c27d62151309f984544c27d61151309f997434c33f54d0d30cf153434c2fa60d0d30be583434c27e6590d309f195434c33f5450d30cf151434c2fb6050d30be181434c27e6510d30e750c434c27e64d49309f593524c27e61d49309f587524c36f5294930afd91524c2bc6454930bdd85524c2f46154930db548524c27e64149309f590524c27e61149309f584524c27e65d09309f597424c27c65d0930dbd4b424c36c52d09309f996424c27d65909309f196424c33f5490930cf152424c27f65509309f995424c27c65509309f994424c27d65109309f194424c33f5410930cf150424c2de6310930b758c424c36f5210930db148424c3ad4210930be980424c2f960109309f997324c36f528c930db14a324c2fa608c930be582324c36f524c930db149324c2fb604c930be181324c27e650c930f34c8324c27e64d45309f593514c27e62d45309f58b514c3775194530afd91514c2bc6454530bbd89514c2ec6254530dd544514c27e64145309f590514c27e62145309f588514c27e65d05309f597414c27c65d0530ddd47414c37451d05309f996414c27d65905309f1964
  | 12 => 0x50040eed8d40103ba6350040ee58d40103b86350040eed4d40103ba5350040ee54d40103b85350040eed8940103ba6250040ee58940103b86250040eed4940103ba5250040ee54940103b85250040eecc940103ba3250040ee4c940103b83250040eed8540103ba6150040ee58540103b86150040eed4540103ba5150040ee54540103b85150040eecc540103ba3150040ee4c540103b83150040eec8540103ba2150040ee48540103b82150040d798f54cc27e62d53309f58b54cc27e61d53309f58754cc37960d5330cfd5254cc27e62953309f58a54cc27e61953309f58654cc33f64553309fd8954cc27c62553309fd8554cc27c6155330cf55054cc33e6415330d798c54cc27e62153309f58854cc27e61153309f58454cc3796015330cf95243cc33d5490f30be98243cc2f96090f30cf95043cc33d5410f30e750c43cc2fa6010f30be58043cc36f5294b309f99252cc27d6494b309f98652cc27d6194b309fd9152cc27c6454b309fd8552cc27c6154b30db54852cc27f65d0b309f99742cc27d65d0b309fd9642cc27e6590b309f59642cc27f6550b309f59542cc27c6550b30bed8142cc2f86050b309fd9442cc27e6510b309f59442cc2de6310b30b758c42cc3ad4210b30db94b32cc36d52ccb30be98332cc2f960ccb30db94832cc36d520cb30f34c832cc2fa600cb30be58032cc37751947309f99251cc27d64947309f98a51cc27d62947309fd9151cc27c64547309fd8951cc27c6254730dd54451cc27f65d07309f99741cc27d65d07309fd9641cc27e65907309f59641cc27f65507309f59541cc27c6550730bed8141cc2f860507309fd9441cc27e65107309f59441cc2de6310730b758c41cc3b54110730dd94731cc37551cc730be98331cc2f960cc730dd94431cc375510c730f54c431cc2fa600c730be58031cc27f65c87309f99721cc27d65c87309fd9621cc27e65887309f59621cc27f65487309f59521cc27c6548730bed8121cc2f860487309fd9421cc27e65087309f59421cc2de6308730b758c21cc3e52108730cf95340cc33d54d0330b798f40cc2dd63d0330cf95140cc33d5450330b7d8d40cc2dc6350330ee50040cc35d63d52309f98b548c27d62d52309f987548c27d61d5230de983548c33f54952309f98a548c27d62952309f986548c27d6195230cfd91548c27f62552309f189548c27f61552309f185548c33d5415230cf990548c35d63152309f988548c27d62152309f984548c27d6115230de980548c33e54d0e30cf553438c2fa60d0e30be583438c33e5450e30cf551438c2fb6050e30be181438c39d4310e30dbd4a528c27e6494a309f592528c27e6194a309f586528c27f6454a309f191528c27f6154a309f185528c36d5214a309fd97428c27e65d0a309f597428c27f6590a309f996428c2
  | 13 => 0xd714c3150377510c540dd14431503d5310c540be98031502f9600c5409f997215027d65c85409f197215037751c8540dd147215027e65885409f596215027c6588540dbd4a215036c52885409fd95215027e65485409f195215027e65085409f594215027c6508540af99021502bd6408540dbd48215036c5208540ddd4421503745108540f948421502fa6008540be58021503bb5090140d7d4e531027e6294c409f58a531027e6194c409f586531027f6254c409f189531027f6154c409f185531035d5314c40bb98853102ed6214c40bd98453102f56114c40d794f431035d53d0c40be98343102f960d0c409f596431027f6550c40d794c431035d5310c40e750c43102fa6010c40be580431036f52948409f98e521027d63948409f986521027d61948409fd8d521027c63548409fd85521027c6154840b798c52102dd6314840db54852102f66114840bd584521036e52d0840db54b42102fa60d0840be583421027d65908409fd95421036e5210840db54842103ad4210840be98042102f960108409fd97321027e65cc8409f597321035e53cc840d754f321027f658c8409f996321027d658c840db94a321036d528c8409fd95321027d654c8409f19532102bf644c840af191321035e534c840d754d321036e524c840db54932102fb604c840be181321027f650c8409f994321027d650c840f34c8321037751944409f98e511027d63944409f98a511027d62944409fd8d511027c63544409fd89511027c6254440b798c51102dd6314440bb98851102ed6214440dd544511037651d0440dd54741102fa60d0440be583411027d65904409fd9541103765110440dd54441103b54110440be98041102f960104409fd97311027e65cc4409f597311035e53cc440d754f311027f658c4409f996311027d658c440dd9463110375518c4409fd95311027d654c4409f19531102bf644c440af191311035e534c440d754d3110376514c440dd54531102fb604c440be181311027f650c4409f994311027d650c440f54c4311027f65c84409f997211027d65c8440db94b211036d52c84409fd96211027e65884409f59621103765188440dd546211027f65484409f595211027c6548440afd9121102bc6448440db949211036d5248440dd94521103755148440bed8121102f860484409fd94211027e65084409f59421103e52108440af592401033e5490040be59240102b96490040de95240103ba54900409fd9540102bf6550040cfd95401023f6550040afd81401033e5050040bed95401037b65500409ed9540102fb6450040eed91401037a5450040ee95140103bb4350040ee90d40103b94350040ee10d40103bb4250040ee90940103b94250040ee10940103bb4150040ee90540103b94150040ee10540103bb6550040aed95401033b65
  | 14 => 0x4d43902fb6050e40be181439039d4310e40dbd4a529027e6394a409f58e529027e6194a409f586529027f6354a409f18d529027f6154a409f185529036d5214a40db94a429036d5290a40be98242902f96090a40db949429036d5250a40bed8142902f86050a40eb508429027f65cca409f997329027d65cca409fd96329027e658ca409f596329027f654ca409f595329027c654ca40afd9132902bc644ca409fd94329027e650ca409f59432903cd320ca40be98032902f9600ca40ddd46519027e63946409f58e519027e62946409f58a519027f63546409f18d519027f62546409f18951903755114640dd94641903755190640be98241902f96090640dd94541903755150640bed8141902f86050640ed504419027f65cc6409f997319027d65cc6409fd96319027e658c6409f596319027f654c6409f595319027c654c640afd9131902bc644c6409fd94319027e650c6409f59431903d5310c640be98031902f9600c6409fd97219027e65c86409f597219027f65886409f996219027d65886409fd95219027d65486409f19521902bf6448640af191219027f65086409f994219027d6508640f948421902fa6008640be58021902bd65d0240cf59740902f965d0240de597409027e62d4d409f58b535027e61d4d409f587535035f5394d40bbd8953502ec6254d40bdd8553502f46154d40d754c535027e6214d409f588535027e6114d409f584535027e65d0d40d7d4e435035c5390d40be98243502f96090d40d7d4d435035c5350d40bed8143502f86050d409f994435039d4310d409f98f525027d63d49409f987525027d61d4940dbd4a52502df6354940b718d52502f76154940bd185525036d52149409f98c525027d63149409f984525027d61149409f997425036f5290940db14a42502fa6090940be582425036f5250940db14942502fb6050940be181425027e6510940eb508425027e65cc9409f597325027c65cc940dbd4b325036c52cc9409f996325027d658c9409f196325035f538c940d714e325027f654c9409f995325027c654c9409f994325027d650c9409f19432502be640c940af590325035f530c940d714c325036f520c940db14832503cd320c940be98032502f9600c9409f98f515027d63d45409f98b515027d62d4540ddd4651502df6354540b718d51502ef6254540bb189515037551145409f98c515027d63145409f988515027d62145409f99741503775190540dd14641502fa6090540be58241503775150540dd14541502fb6050540be181415027e6510540ed504415027e65cc5409f597315027c65cc540ddd47315037451cc5409f996315027d658c5409f196315035f538c540d714e315027f654c5409f995315027c654c5409f994315027d650c5409f19431502be640c540af590315035f530c54
  | 15 => 0x86ee628c421bb58a310867f654c4219fd94310867e650c4219f594310867c650c421d794c310875d530c421bb98831086ed620c421f54c431086ed6288421db94a21086f56288421b958a21087765288421f994a210867f6548421bbd95210876f65484219bd9521086ef6148421db94521087e74148421f990521087e54148421f910521087e73148421f98c521087e53148421f90c521086f76548421ddd9521086776548421bdd8921087e76248421dd94921087e65248421f9d0921087e64248421f950921087e44248421f9cc921087e63248421f94c921087e43248421f9d9521086e76548421d9d9521087e76448421f999121087e56448421f919121087e75448421f995121087e55448421f915121087e76348421f998d21087e56348421f918d21087e75348421f994d21087e55348421f914d21087e74348421f990d21087e54348421f910d21087e76048421f998121087e56048421f918121087e521d4021f9486500877b50940219f992500867d64940219f98e500867d6394021f9485500867f64540219f191500867f63540219f18d50086be6414021af59050086de6314021b758c50087e52114021de540500875f5394f409f98a53d027d6294f409f98653d027d6194f409fd8953d027c6254f409fd8553d027c6154f40d754c53d035e53d0f40d754f43d02fa60d0f40be58343d035e5310f40d754c43d039d4310f40be98043d02f96010f40dbd4a52d027e6394b409f58e52d027e6194b409f58652d027f6354b409f18d52d027f6154b409f18552d036d5214b40db94b42d036d52d0b40be98342d02f960d0b40db94842d036d5210b40eb50842d02fa6010b40be58042d027f65ccb409f99732d027d65ccb409fd9632d027e658cb409f59632d027f654cb409f59532d027c654cb40bed8132d02f8604cb409fd9432d027e650cb409f59432d02be640cb40af59032d03cd320cb40ddd4651d027e63947409f58e51d027e62947409f58a51d027f63547409f18d51d027f62547409f18951d03755114740dd94741d037551d0740be98341d02f960d0740dd94441d03755110740ed50441d02fa6010740be58041d027f65cc7409f99731d027d65cc7409fd9631d027e658c7409f59631d027f654c7409f59531d027c654c740bed8131d02f8604c7409fd9431d027e650c7409f59431d02be640c740af59031d03d5310c7409fd9721d027e65c87409f59721d027f65887409f99621d027d65887409fd9521d027d65487409f19521d02fb6048740be18121d027f65087409f99421d027d6508740af99021d02bd6408740f948421d035f5394e409f98a539027d6294e409f986539027d6194e409fd89539027c6254e409fd85539027c6154e40d754c539035e5390e40d754e43902fa6090e40be582439035e5350e40d75
  | 16 => 0xc54d0521bb98b41486ed62d05219f996414867f65505219f595414867c6550521cfd51414873c5450521bbd8941486ec62505219f99441487b541105219f997314875f53cc521d714f31486ee62cc521bb58b314867e658c5219fd95314867d654c5219f195314875f534c521d714d31486ef624c521bb189314867e650c521f54c431487e751885219f993504867d64d41219f98f504867d63d4121ded4250486bf6454121af19150486df6354121b718d504877950141219f990504867d64141219f98c504867d63141219f98f540867d63d50219f98b540876e62d50219f987540877661d50219f983540867d60d50219f596540873f54950219f98e540867d63950219f982540867d6095021cfd91540867f63550219f18d540867f60550219f181540873d5415021b798c54086dd6315021be98054086f960150219f990540873e64150219f98c540875e63150219798c540867d6315021d758c540865d63150219f988540876e62150219f984540877661150219f980540877a60150219e980540867d6015021de580540867960150219f993530867d64d4c219f98b530876e62d4c219f987530877661d4c219f983530867d60d4c219f596530875f5394c219f992530867d6494c219f982530867d6094c219fd91530867c6454c21d7d8d530867f6054c219f18153086be6414c21af590530875d5314c21be98053086f96014c219f990530873e6414c218f990530867d6414c21cf590530863d6414c219f98c530875e6314c219f988530876e6214c219f98453087766114c219f980530877a6014c219e980530867d6014c21de58053086796014c219fd97430867e65d0c219f597430867c65d0c21cf953430873d54d0c219fd96430867e6590c219f596430867c6590c21d794e430875d5390c219fd95430867e6550c219f595430867c6550c21cf951430873d5450c21d794d430875d5350c21bbd8943086ec6250c21bdd8543086f46150c219fd94430867e6510c219f594430867c6510c21e750c430867e64948219f592520867e63948219f58e520867d65d08219fd96420867d6590821cf952420873d5490821bd98642086f561908219fd95420867f65108219f594420873e5410821cf55042087ad4210821bd98442086f561108219f597320867f658c8219f596320875e538c821d754e32086f6618c821bd586320867f654c8219fd94320867d650c821d794c320875d530c821f34c832086f6610c821bd584320867e64944219f592510867e63944219f58e510867d65d04219fd96410867d6590421cf952410873d5490421bb98a41086ed62904219fd95410867f65104219f994410867d65104219f194410873e5410421cf55041086ee6210421bb58841087b541104219f597310867f658c4219f596310875e538c421d754e31
  | 17 => 0x4e21dd984538867e6014e219f580538867f65d0e219f997438867d65d0e219f197438867f6590e219f996438867d6590e219f196438867f6550e219f995438867d6550e219f19543886ef6250e21bb189438867f6510e219f994438867d6510e219f194438879d4310e21bd98443886f56110e21cf953428873d54d0a21bd98742886f561d0a21cf951428873d5450a21bdd8542886f46150a21eb508428875e53cca21d754f32886f661cca21bd587328875e534ca21d754d32886f7614ca21bd18532887cd320ca21cf952418873d5490621bb98a41886ed6290621cf950418873d5410621bb98841886ed6210621ed504418875e538c621d754e31886ee628c621bb58a318875e530c621d754c31886ee620c621bb58831887d5310c621bb597218876d65c8621bd597218877565c8621ded42508867e64942219f592508867e63942219f58e508867f64542219f191508867f63542219f18d508877950142219f98f544867d63d51219f983544867d60d5121cfd52544867e64951219f98e544867d63951219f58a544876d62951219f586544877561951219f982544867d6095121b7d8d54486dc6355121bed8154486f86055121cfd91544867f6355121d7d8d544865f63551219f18d544875c63551219718d544867f6255121dbd89544867f6155121ddd85544867f6055121ded81544867b60551219f181544877860551219e181544867e6515121cf550544873e64151219f98c544867d63151219f980544867d60151219f993534867d64d4d219f983534867d60d4d21d7d4e534867e6494d219f592534867e6394d219f58a534876d6294d219f58653487756194d219f982534867d6094d21afd9153486bc6454d21bed8153486f86054d219fd91534873f6454d218fd91534867c6454d21cf191534863c6454d21d7d8d534867f6254d21dbd89534867f6154d21ddd85534867f6054d21ded81534867b6054d219f18153487786054d219e181534867e6514d21d754c534867e6414d219f590534875e6314d219f980534867d6014d219fd97434867e65d0d219f597434867c65d0d21d7d4f434875c53d0d219fd96434867e6590d219f596434867c6590d21cfd52434873c5490d219fd95434867e6550d219f595434867c6550d219fd94434867e6510d219f594434867c6510d21cfd50434873c5410d21d7d4c434875c5310d21e750c43486ee6210d21bb58843486f66110d21bd584434867e65d0921cfd53424873c54d0921bd98742486f561d09219f996424867c6550921cfd51424873c5450921bdd8542486f461509219f99442487ad42109219f997324875f53cc921d714f32486f661cc921bd587324867e658c9219f195324875f534c921d714d32486f7614c921bd185324867e650c921f34c8324867e65d0521cfd53414873
  | 18 => 0xf5d8d310c776534c431f594d310c7d7434c431f590d310c7d5434c431f510d310c7d7324c431f58c9310c7d5324c431f50c9310c7d7654c431b5d95310c757654c431f5d91310c7d6644c431f5591310c7d4644c431f5d51310c7d6544c431f5551310c7d4544c431f5d89310c7d6624c431f5589310c7d4624c431f5d49310c7d6524c431f5549310c7d4524c431f5d09310c7d6424c431f5509310c7d4424c431f5d81310c7d6604c431f5581310c7d4604c431f54c7500c7d53194031ded42500c67e64940319f592500c67e62940319f58a500c7d531540319fd91500c67c64540319fd89500c67c6254031af990500c6bd6414031bb988500c6ed6214031f54c4500c77950140319f98f54c867d63d5321db98b54c877561d53219f98354c867d60d5321cfd5254c867e63953219f58e54c867e60953219f58254c873f64553219fd8d54c867c63553219fd8154c867c6055321cf55054c873e64153219f98c54c867d6315321db98854c877561153219f98054c867d60153219f99353c867d64d4f21db98b53c877561d4f219f98353c867d60d4f21d7d4e53c867e6494f219f59253c867e6094f219f58253c867f6454f219f19153c875f6354f219fd8153c867c6054f21d754c53c867e6414f219f59053c875e6314f21db98853c87756114f219f98053c867d6014f219fd9743c867e65d0f219f59743c867c65d0f219fd9643c867e6590f219f59643c867c6590f219fd9543c867e6550f219f59543c867c6550f21bdd8543c86f46150f219fd9443c867e6510f219f59443c867c6510f21e750c43c86ee6210f21bb58843c873e5490b21cf55242c86f66190b21bd58642c873e5410b21cf55042c87ad4210b21bd98442c86f56110b21d794e32c875d538cb21bd98632c86f5618cb21d794c32c875d530cb21f34c832c86f6610cb21bd58432c873e54d0721cf55341c86ee62d0721bb58b41c873e5450721cf55141c86ef6250721bb18941c87b54110721d794f31c875d53cc721bb98b31c86ed62cc721d794d31c875d534c721bbd8931c86ec624c721f54c431c877b50943219f99250c867d64943219f98e50c867d63943219fd9150c867c64543219fd8d50c867c6354321de54050c867e63d52219f58f548876d62d5221dd987548867e60d52219f583548873f54952219f98e548867d63952219f982548867d6095221cfd91548867f63552219f18d548867f60552219f181548873d5415221cf990548867e63152219f58c548876d6215221dd984548867e60152219f580548867e64d4e219f593538876d62d4e21dd987538867e60d4e219f583538875f5394e219f992538867d6494e219f982538867d6094e219fd91538867c6454e21d7d8d538867f6054e219f181538875d5314e219f990538867d6414e21d798c538876d621
  | 19 => 0x524c67d60149319f997424c67d65d09319f197424c76f52d0931db14b424c67e65909319f596424c67c6590931cfd52424c73c54909319fd95424c67e65509319f195424c67e65109319f594424c67c6510931cfd50424c73c5410931b798c424c6dd6310931dbd48424c76c5210931eb508424c6f66110931bd584424c67e65cc931dbd4a324c76c528c931bd986324c6f5618c931dbd49324c76c524c931bdd85324c6f4614c9319f994324c7cd320c9319f997414c73f54d0531cf153414c6de63d0531b758f414c67e65905319fd95414c67d65505319f195414c73f5450531cf151414c6df6350531b718d414c67e6510531ed504414c7d7518c5319f993504c67d64d41319f98b504c67d62d4131ded42504c6bf6454131af191504c6ef6254131bb189504c77950141319f990504c67d64141319f988504c67d62141319f98f540c75e63d50319f98b540c67d62d50319f987540c77661d50319f983540c67d60d50319f596540c73f54950319f98a540c67d62950319f982540c67d6095031cfd91540c67f62550319f189540c67f60550319f181540c73d5415031bb988540c6ed6215031be980540c6f960150319f990540c73e64150319f98c540c75e63150319f988540c76e62150319b988540c67d6215031db588540c66d62150319f984540c77661150319f980540c77a60150319e980540c67d6015031de580540c67960150319f992530c67d6494c319f597430c67f6590c319f596430c73e5490c31cf552430c6f66190c31bd586430c67f6550c319fd94430c67d6510c31cf950430c73d5410c31e750c430c6f66110c31bd584430c76f52948319f992520c67d64948319f982520c67d60948319fd91520c67c64548319fd81520c67c6054831af990520c6bd6414831db548520c6fa6014831be580520c67f65d08319f997420c67d65d0831cf953420c73d54d08319fd96420c67e65908319f596420c76e5290831db54a420c67f65508319f595420c67c6550831cf951420c73d5450831b7d8d420c6dc6350831db949420c76d5250831bdd85420c6f461508319fd94420c67e65108319f594420c7ad4210831db94b320c76d52cc831bd987320c6f561cc8319f596320c67f654c831db948320c76d520c831f34c8320c6f6610c831bd584320c67e64944319f592510c67d65d04319fd96410c67d6590431cf952410c73d5490431b798e410c6dd63904319fd95410c67f65104319f994410c67d65104319f194410c73e5410431cf550410c6de6310431b758c410c7b54110431b758e310c75e538c431bd58e310c6d5638c431dd94e310c7d6538c4319fd95310c6df654c431d7d95310c65f654c431b7d85310c75e514c431f5d05310c7d6414c431f5505310c7d4414c431bdd95310c777654c4319dd95310c6f7634c431
  | 20 => 0xc6f56110f31dbd4a52cc67e6494b319f59252cc67e6094b319f58252cc67f6454b319f19152cc67f6054b319f18152cc76d5214b319fd9742cc67e65d0b319f59742cc67f6590b319f99642cc67d6590b319fd9542cc67d6550b319f19542cc6f76150b31bd18542cc67f6510b319f99442cc67d6510b31b798c42cc6dd6310b31eb50842cc76e52ccb31db54b32cc6f661ccb31bd58732cc76e520cb31db54832cc7cd320cb31bd98432cc6f5610cb31cf95341cc73d54d0731b798f41cc6dd63d0731cf95141cc73d5450731b7d8d41cc6dc6350731ed50441cc77b50943319f99250cc67d64943319f98a50cc67d62943319fd9150cc67c64543319fd8950cc67c6254331de54050cc75d63d52319f98b548c67d62d5231dd987548c67e60d52319f583548c73f54952319f98a548c67d62952319f982548c67d6095231cfd91548c67f62552319f189548c67f60552319f181548c73d5415231cf990548c75d63152319f988548c67d6215231dd984548c67e60152319f580548c73e54d0e31cf553438c6f661d0e31bd587438c73e5450e31cf551438c6f76150e31bd185438c79d4310e31dbd4a528c67e6494a319f592528c67e6094a319f582528c67f6454a319f191528c67f6054a319f181528c76d5214a319fd97428c67e65d0a319f597428c67f6590a319f996428c67d6590a319fd95428c67d6550a319f195428c6df6350a31b718d428c67f6510a319f994428c67d6510a31eb508428c6f66110a31bd584428c76e528ca31db54a328c6f6618ca31bd586328c76e524ca31db549328c6f7614ca31bd185328c7cd320ca31cf952418c73d5490631b798e418c6dd6390631cf950418c73d5410631b798c418c6dd6310631ed504418c6dd65cc631d7597318c6f565cc631dd597318c77b50942319f992508c67d64942319f98a508c67d62942319fd91508c67c64542319fd89508c67c6254231de540508c67e62d51319f58b544c67e60d51319f583544c73f54951319f992544c67d6395131d758e544c67e62951319f58a544c67d6195131dd586544c67e60951319f582544c6ef6255131bb189544c6fb6055131be181544c73f64551319fd8d544c75f63551319fd89544c76f62551319bd89544c67c6255131db189544c66c62551319fd85544c77761551319fd81544c77b60551319ed81544c67c6055131de181544c67860551319f994544c73d5415131cf990544c67e62151319f588544c67e60151319f580544c67e65d0d31cfd53434c73c54d0d31bd987434c6f561d0d319f996434c67c6550d31cfd51434c73c5450d31bdd85434c6f46150d319f994434c79d4310d319f993524c67d64d49319f983524c67d60d4931dbd4a524c6bf6454931af191524c6fb6054931be181524c76d52149319f990524c67d64149319f98
  | 21 => 0x52cc941db14b325067e658c9419f596325067c658c941d7d4e325075c538c9419fd95325067e654c9419f195325067e650c9419f594325067c650c941af99032506bd640c941d7d4c325075c530c941dbd48325076c520c941f34c832506f6610c941bd58432507b751905419f98f505067d63d41419f98b505067d62d4141ded4250506df6354141b718d50506ef6254141bb189505077950141419f98c505067d63141419f988505067d6214141d7d4e531067e6294c419f58a531067e6094c419f582531067f6254c419f189531067f6054c419f181531075d5314c41bb98853106ed6214c41be98053106f96014c41d794f431075d53d0c41bd98743106f561d0c419f596431067f6550c41d794c431075d5310c41e750c43106f66110c41bd584431076f52948419f98e521067d63948419f982521067d60948419fd8d521067c63548419fd81521067c6054841b798c52106dd6314841db54852106fa6014841be580521076e52d0841db54b42106f661d0841bd587421067d65908419fd95421076e5210841db54842107ad4210841bd98442106f561108419fd97321067e65cc8419f597321075e53cc841d754f321067f658c8419f996321067d658c841db94a321076d528c8419fd95321067d654c8419f19532106bf644c841af191321075e534c841d754d321076e524c841db54932106f7614c841bd185321067f650c8419f994321067d650c841f34c832106bd6490441cf95241106f56490441ad59241107765490441ed952411067f6550441afd95411073f65504418fd9541106bf6150441cf94541106f76550441ddd9541106776550441bdd9141107b76450441dd95141107b65450441edd0d41107b64350441ed50d41107b44350441edd0941107b64250441ed50941107b44250441edd9541106b76550441cdd9541107b76350441ed98d41107b56350441ed18d41107b75350441ed94d41107b55350441ed14d41107b76250441ed98941107b56250441ed18941107b75250441ed94941107b55250441ed14941107b73250441ed8c941107b53250441ed0c941107b76050441ed98141107b56050441ed18141107b541d4041ed506501077b50940419f98e501067d63940419f98a501067d6294041ed505501067f63540419f18d501067f62540419f18950106de6314041b758c50106ee6214041bb58850107b54114041de540501075e63d53319f98b54cc67d62d5331dd58754cc67e60d53319f58354cc73f54953319f98a54cc67d62953319f98254cc67d6095331cfd9154cc67f62553319f18954cc67f60553319f18154cc73d5415331cf99054cc75e63153319f98854cc67d6215331dd58454cc67e60153319f58054cc73e5490f31cf55243cc6f66190f31bd58643cc73e5410f31cf55043cc79d4310f31bd98443c
  | 22 => 0x4329fd91510ca7c64544329fd81510ca7c6054432af990510cabd6414432f34c8510cb755114432be980510caf96014432f34cb500cbcd3294032ded42500ca7e64940329f592500ca7e61940329f586500cbcd32540329fd91500ca7c64540329fd85500ca7c6154032af990500cabd6414032f34c8500caf66114032bd584500cb795014032d7d4e53d067e6294f419f58a53d067e6094f419f58253d067f6254f419f18953d067f6054f419f18153d075d5314f41d794f43d075d53d0f41bd98743d06f561d0f41d794c43d075d5310f41e750c43d06f66110f41bd58443d076f5294b419f98e52d067d6394b419f98252d067d6094b419fd8d52d067c6354b419fd8152d067c6054b41db54852d076e52d0b41db54b42d06f661d0b41bd58742d076e5210b41db54842d07ad4210b41bd98442d06f56110b419fd9732d067e65ccb419f59732d067f658cb419f99632d067d658cb419fd9532d067d654cb419f19532d06f7614cb41bd18532d067f650cb419f99432d067d650cb41af99032d06bd640cb41f34c832d077b50943419f98e50d067d63943419f98a50d067d62943419fd8d50d067c63543419fd8950d067c6254341de54050d075f5394e419f98a539067d6294e419f982539067d6094e419fd89539067c6254e419fd81539067c6054e41d754c539075e5390e41d754e43906f66190e41bd586439075e5350e41d754d43906f76150e41bd185439079d4310e41dbd4a529067e6394a419f58e529067e6094a419f582529067f6354a419f18d529067f6054a419f181529076d5214a41db94a429076d5290a41bd98642906f56190a41db949429076d5250a41bdd8542906f46150a41eb508429067f65cca419f997329067d65cca419fd96329067e658ca419f596329067f654ca419f595329067c654ca41afd9132906bc644ca419fd94329067e650ca419f59432907cd320ca41bd98432906f5610ca41af597419073d65d0641bd597419077565d0641ded42509067e63942419f58e509067e62942419f58a509067f63542419f18d509067f62542419f189509077950142419f98b535067d62d4d419f983535067d60d4d41d7d4e53506ef6254d41bb18953506fb6054d41be181535075d5314d419f988535067d6214d419f980535067d6014d419f997435075f5390d41d714e43506f66190d41bd586435075f5350d41d714d43506f76150d41bd185435067e6510d41e750c435067e63d49419f58f525067e60d49419f583525076f5294941b7d8d52506dc6354941bed8152506f86054941db548525067e63149419f58c525067e60149419f580525067e65d0941dbd4a425076c5290941bd98642506f56190941dbd49425076c5250941bdd8542506f461509419f99442507ad42109419f997325067d65cc9419f197325076f
  | 23 => 0xd185544cafb6055132be181544cb3f64551329fd8d544cb5f63551329fd89544cb6f62551329fd85544cb7761551329dd85544ca7c6155132dd185544ca7461551329fd81544cb7b60551329ed81544ca7c6055132de181544ca7860551329f994544cb3d5415132cf990544ca7e61151329f584544ca7e60151329f580544ca7e65d0d32cfd53434cb3c54d0d32bb98b434caed62d0d329f996434ca7c6550d32cfd51434cb3c5450d32bbd89434caec6250d329f994434cb9d4310d329f997424cb3f54d0932cf153424cade63d0932b758f424ca7e65909329fd95424ca7d65509329f195424cb3f5450932cf151424cadf6350932b718d424ca7e6510932eb508424cbcf528c9329f993514ca7d64d45329f983514ca7d60d4532ddd46514cabf6454532af191514cafb6054532be181514cb7551145329f990514ca7d64145329f980514ca7d60145329f993504ca7d64d41329f987504ca7d61d4132ded42504cabf6454132af191504caf76154132bd185504cb7950141329f990504ca7d64141329f984504ca7d61141329f98f540cb5e63d50329f98b540cb6e62d50329f987540ca7d61d50329f983540ca7d60d50329f596540cb3f54950329f986540ca7d61950329f982540ca7d6095032cfd91540ca7f61550329f185540ca7f60550329f181540cb3d5415032bd984540caf56115032be980540caf960150329f990540cb3e64150329f98c540cb5e63150329f988540cb6e62150329f984540cb7661150329d984540ca7d6115032dd584540ca7561150329f980540cb7a60150329e980540ca7d6015032de580540ca7960150329f992530ca7d6494c329f597430ca7f6590c329f596430cb3e5490c32cf552430caee6290c32bb58a430ca7f6550c329fd94430ca7d6510c32cf950430cb3d5410c32e750c430caee6210c32bb588430ca7e64948329f592520ca7d65d08329fd96420ca7d6590832cf952420cb3d5490832b798e420cadd63908329fd95420ca7f65108329f994420ca7d65108329f194420cb3e5410832cf550420cade6310832b758c420cbad4210832b758e320cb5e538c832bb58e320cacd638c832db94e320cbce538c8329fd95320cadf654c832d7d95320ca5f654c832b7d89320cb5e524c832f3d09320cbce424c832f3509320cbcc424c832bbd95320cb6f654c8329bd95320caef634c832f3d8d320cb6e534c832f394d320cbcf434c832f390d320cbcd434c832f310d320cbcf654c832b3d95320cb4f654c832f3d91320cbce644c832f3591320cbcc644c832f3d51320cbce544c832f3551320cbcc544c832f3d85320cbce614c832f3585320cbcc614c832f3d81320cbce604c832f3581320cbcc604c832f34cb510cbcd3294432ddd46510ca7e64944329f592510ca7e60944329f582510cbcd3254
  | 24 => 0x4210a7f6550842afd954210b3f65508428fd954210abf6250842cf9494210aef6550842dbd954210a6f6550842bbd914210baf6450842db9514210bae5450842ebd0d4210bae4350842eb50d4210bac4350842ebd954210aaf6550842cbd954210baf6350842eb98d4210bad6350842eb18d4210baf5350842eb94d4210bad5350842eb14d4210baf6150842eb9854210bad6150842eb1854210baf6050842eb9814210bad6050842eb1814210bad42d4442eb50a5110b7751944429f98e5110a7d63944429f9825110a7d6094442eb5095110a7f63544429f18d5110a7f60544429f1815110ade6314442b758c5110bad4214442dd5445110afa6014442be5805110bad42d4042eb50a5010b7b50940429f98e5010a7d63940429f9865010a7d6194042eb5095010a7f63540429f18d5010a7f61540429f1855010ade6314042b758c5010bad4214042bd9845010af56114042de5405010b5e63d5332db58b54cca7e61d53329f58754cca7e60d53329f58354ccb3f54953329f98654cca7d61953329f98254cca7d6095332cfd9154cca7f61553329f18554cca7f60553329f18154ccb3d5415332cf99054ccb5e6315332db58854cca7e61153329f58454cca7e60153329f58054ccb3e5490f32cf55243ccaee6290f32bb58a43ccb3e5410f32cf55043ccb9d4310f32bb98843ccaed6210f32cf95342ccb3d54d0b32b798f42ccadd63d0b32cf95142ccb3d5450b32b7d8d42ccadc6350b32eb50842ccb7751947329f99251cca7d64947329f98251cca7d60947329fd9151cca7c64547329fd8151cca7c6054732dd54451ccb7b50943329f99250cca7d64943329f98650cca7d61943329fd9150cca7c64543329fd8550cca7c6154332de54050ccb5d63d5232db98b548ca7e61d52329f587548ca7e60d52329f583548cb3f54952329f986548ca7d61952329f982548ca7d6095232cfd91548ca7f61552329f185548ca7f60552329f181548cb3d5415232cf990548cb5d6315232db988548ca7e61152329f584548ca7e60152329f580548cb3e54d0e32cf553438caee62d0e32bb58b438cb3e5450e32cf551438caef6250e32bb189438cb9d4310e32cf952428cb3d5490a32b798e428cadd6390a32cf950428cb3d5410a32b798c428cadd6310a32eb508428cadd65cca32d7597328caed65cca32db597328cb7751946329f992518ca7d64946329f982518ca7d60946329fd91518ca7c64546329fd81518ca7c6054632dd544518cb7b50942329f992508ca7d64942329f986508ca7d61942329fd91508ca7c64542329fd85508ca7c6154232de540508ca7e61d51329f587544ca7e60d51329f583544cb3f54951329f992544ca7d6395132d758e544ca7d6295132db58a544ca7e61951329f586544ca7e60951329f582544caf76155132b
  | 25 => 0xe7e60948439f5825210f9d43548439fd855210e7c61548439fd815210e7c6054843e750c5210f6d5214843bd9845210ef56114843be9805210ef96014843e750f5110f9d4394443ddd465110e7e62944439f58a5110e7e60944439f5825110f9d43544439fd895110e7c62544439fd815110e7c6054443e750c5110eee6214443bb5885110f755114443be9805110ef96014443e750f5010f9d4394043ded425010e7e62940439f58a5010e7e61940439f5865010f9d43540439fd895010e7c62540439fd855010e7c6154043e750c5010eee6214043bb5885010ef66114043bd5845010f795014043d7d4e53d0a7e6194f429f58653d0a7e6094f429f58253d0a7f6154f429f18553d0a7f6054f429f18153d0b5d5314f42d794f43d0b5d53d0f42bb98b43d0aed62d0f42d794c43d0b5d5310f42e750c43d0aee6210f42bb58843d0b7751947429f98e51d0a7d63947429f98251d0a7d60947429fd8d51d0a7c63547429fd8151d0a7c6054742dd54451d0b7b50943429f98e50d0a7d63943429f98650d0a7d61943429fd8d50d0a7c63543429fd8550d0a7c6154342de54050d0b5f5394e429f9865390a7d6194e429f9825390a7d6094e429fd855390a7c6154e429fd815390a7c6054e42d754c5390b5e5390e42d754e4390aee6290e42bb58a4390b5e5350e42d754d4390aef6250e42bb1894390b9d4310e42af5974290b3d65d0a42bb5974290b6d65d0a42ddd465190a7e63946429f58e5190a7e60946429f5825190a7f63546429f18d5190a7f60546429f1815190b755114642ded425090a7e63942429f58e5090a7e61942429f5865090a7f63542429f18d5090a7f61542429f1855090b7950142429f9875350a7d61d4d429f9835350a7d60d4d42d7d4e5350af76154d42bd1855350afb6054d42be1815350b5d5314d429f9845350a7d6114d429f9805350a7d6014d429f9974350b5f5390d42d714e4350aee6290d42bb58a4350b5f5350d42d714d4350aef6250d42bb1894350a7e6510d42e750c4350baf52909429f98f5150a7d63d45429f9835150a7d60d4542ddd465150adf6354542b718d5150afb6054542be1815150b7551145429f98c5150a7d63145429f9805150a7d60145429f98f5050a7d63d41429f9875050a7d61d4142ded425050adf6354142b718d5050af76154142bd1855050b7950141429f98c5050a7d63141429f9845050a7d6114142d7d4e5310a7e6194c429f5865310a7e6094c429f5825310a7f6154c429f1855310a7f6054c429f1815310b5d5314c42bd9845310af56114c42be9805310af96014c42d794f4310b5d53d0c42bb98b4310aed62d0c429f5964310a7f6550c42d794c4310b5d5310c42e750c4310aee6210c42bb5884310abd6490842cf9524210aed6490842ab5924210b6e5490842eb952
  | 26 => 0x1800c000000800c00c00180040140260030004002019001000002a00600000200000010080068008001008804c00601e0010008008013000807000a000004800805a007000000c010019002800003801f00180040080010258000008003000001000c00901400240000000008014032000001003800000500d8004002006005800800002d0008000058004008803400800500000000ac0020000000014018000801805a001001000c016011000800c09000000201f8006011008000000c014005800801a000000000400c009011802401000000a009800a00200d8000000004000001402604100380040000000038014066002007800c00a000007001c00401800580200080060000008000031001800c0080180098084006004001802801e000008000001001a005000c00e00100c800000000400180000060050040008022003003800002a010003800f6f5294b439f98652d0e7d6194b439f98252d0e7d6094b439fd8552d0e7c6154b439fd8152d0e7c6054b43db54852d0f7751947439f98a51d0e7d62947439f98251d0e7d60947439fd8951d0e7c62547439fd8151d0e7c6054743dd54451d0f7b50943439f98a50d0e7d62943439f98650d0e7d61943439fd8950d0e7c62543439fd8550d0e7c6154343de54050d0ebd65d0e43cf5974390edd65d0e43d75974390f6f5294a439f9865290e7d6194a439f9825290e7d6094a439fd855290e7c6154a439fd815290e7c6054a43db5485290f7751946439f98a5190e7d62946439f9825190e7d60946439fd895190e7c62546439fd815190e7c6054643dd5445190f7b50942439f98a5090e7d62942439f9865090e7d61942439fd895090e7c62542439fd855090e7c6154243de5405090f9f5390d439f9875250e7d61d49439f9835250e7d60d4943dbd4a5250ef76154943bd1855250efb6054943be1815250f6d52149439f9845250e7d61149439f9805250e7d60149439f98b5150e7d62d45439f9835150e7d60d4543ddd465150eef6254543bb1895150efb6054543be1815150f7551145439f9885150e7d62145439f9805150e7d60145439f98b5050e7d62d41439f9875050e7d61d4143ded425050eef6254143bb1895050ef76154143bd1855050f7950141439f9885050e7d62141439f9845050e7d6114143af5924310f3e5490c43b75924310e9d6490c43d79524310f9e5490c439fd954310ebf6550c43cfd954310e3f6550c43afd8d4310f3e5350c43b7d954310f5f6550c4397d954310edf6450c43e7d914310f5e5450c43e79514310f9f6550c43a7d954310f1f6550c43e7d894310f9e6250c43e75894310f9c6250c43e7d854310f9e6150c43e75854310f9c6150c43e7d814310f9e6050c43e75814310f9c6050c43e750f5210f9d4394843dbd4a5210e7e61948439f5865210
  | 27 => 0x1002c000019006004801e00300080a4002000002000000a002002000004600f00080000020020030004008014000000001400f002800003a00000480cc01400700d800403e0030018004004031000004c00c0020000000030028001800c01a00300000000200040010000002025000002c002000001800400200500a000800200000400740020000010114002003007802c0020010008040002015003800000000b002800402c00b002800000e000000006000e031000001402400b001002802200500f0000038027000006c0ae001010003800200a0018040000002006800801c000004802002e0160058000004010002801000000100d018400000c001006800000800d800400202b000008800800500400100020060070004008004003005c00200801580080720060010000072000002002c010014002000001802100d0034002000008000000200000680640000000000000004000000004c000005001800c01800900480000000320000080018000000001802a003002800800c0100090024002002000000401a01a000007c002000001003800600c000800000200c000002c000007005800001400b01880040000080040004000000007802801600b000008000e01600400a00100060000014000005007803801803a004807808c0040078000080000001800c09400100000b80000160000048002006002805400001200800000020110008048042000000800804e000008800c016002001002800a0140020000000001014802c0000110098004000000000800001400100200000040020068014000021004800402804100180000000030018010000014000002800a010003000c04c005001001c000006001801c0000080000004000001000000801200100a80140000000000004012006004813c0240030070018002004012002c00002300900140000050000034030005008800c00000100100200100090010004002010001007800c005001801c01e002022800000e00e0000024000008001004801e007011800c0000000058000010000004800c004004000002c0000020068000006000000801c00e00a000000001c00001b8000008060002800c04c001000800000400000400000080000088008048000010004803a00800380140020120000018006003006003405600a0008018004000000000c006025000000801600000200000160030048018000001001000000400d011002400e021006800c0080070138000010000009003000000d00180180020030058020000005005803800a000000000802002b002811000e02d002800404c026002003800e00200380040020000090020000003005801000000000180300240000008024016010000001000000900700340040070000054000000004802000000d001004800000600580380
  | 28 => 0x940010018000000000005800800600f00a000400a00f001005800400a000003400000200d0014010000002800000400700e802c00c0000050020008008000000000200c00e8000004021006801002000a000803401a00501700040200320008000000000001800401401600200740040060010004024009000000c01800200b8000000004000000400000001b802800400000e000c02c002000006c000002001009800000e00080380100000020000018038000000408e0080038000012000001000000000001b00240440010000024000017002800c010000006800000000100e000000800101b802001a001007001400a000006004c0000010088000000000001000002a00700680240000000020008010006003001c00e00d009803400e006000000000a000001802400c0040030000002000000801c00401c000801802e000002000400000100880240000010058004036002005000000a00f0018014000004000805c00e002000805402c000001000000c0070028004000007000000402a000015800801000200580400040040048000000010000007c01000b003802800200400d0020048001000802800200d003000c00600000080000080050028094018006000801407e011002802000a001000001000a002003800c000011001800c016031002802803400f000000009c00100080b000002900300200040000078008042004003007000c0010000004002005008800c00001d00000080440450000000000001011001c01e002000800c054012000804c002004011001400000a00e008005c00001a0008016004002000c012000000004402a002003801400a006002005c00000500300000260000068014002004009000000c001000800401e003000002800e0030010068000000005805c000009002801002800400080940000000058008012000005000007200a0010000010000001001401000c01180140b4001004803400c022000800000000302280000020110000000002040002802001000200000080020010010014000002002800800600d00e8028004004002008400600100180b80000000038000010000001000000400c012801800c00100f001001401a004002400c00c00900100020020050004006005003000400200d01f80040080010008030000001000000001e000002000801c0520058044010001004000000400b000002000000c000800000000d00000280080020010000006000018005800a0000030008016002003801c04e005005800800002a002801400402100b800800600b000004400800000080600000030010004010000001000801600001d80b400e00000a805c01000400080040100000008000002000007000000401f00a8000008001000000000000c0078020000013000000c00e002005040c03400e0
  | 29 => 0xf0a9d03d0bcc3c1174561d0178f4540954304eb93fe41694402a7900d0000c6f062c78d17ec00000000001c2400000000431c54000328ca9d00000003b889ac427d0b352e13514c506563e8000035d800a041080e1704cb20000000082800000000003404000586519d12013e4224005d22d05b30c34e8400005bc1b4c0003f7d6334fa032946dccc355dc0000000ff154bc0000ffc85d58dc2a202dc50518d534d361cf3e50b005110991292ef8f6e45413441ce812f00000002af40001ea88313844fce3f54ea13114d0a39bd0b01b88bfe2bdc7d200008a60c8532c000010d00000000ea000030505194edc28e0000000465400029a41492b7800000007ca1df429d00000000000615000152c0600da304c51dd50ec0eb36e8a4e4a043db0040020003002000c02000000080040000060018000024004000000400000400d80b400e0040100008000007005800400c01f000003001003000380100020000020068002005000000003201b000000000001000100440100000010000014001002800c00000800b00cc02000900c001800600200380e402c00b001812000000f0028010000013000000c00c0000028024002010000800004a00100101a801a00100780000100200010000026000009800400203c000802400200000180040400000008030016001003802000c017005003c014001006000001200000d8080000001001800404201200000180080030000008000008003001000e0010000008030005008000404000004b003000000d007000c00600d0060000002002000001c008001004002800a000004001404400900000280000000000000000000006000000a00a00100380000080010004018000008000000001001c8010002006000800400c00400100100020c900080080200040010074000035000802c000000003000001e004006003000a000006800000c02b027801800a021000800401800000280680040090000030000004000805c00600100380280000070008024000012000800400e0040050000000005001003c000000001802801401a00f8000004002004001c004000003806c03600000000200040030010004000000001003000000000280000000110030008030000001004c0020150000004026008005000400000300200100020060010000000024000003000409600500300000000000004004005002800002c0090070000000000001004400c010003801c004043002002400000a000004400800500000380000060040064000000000000c00002b027801800a000000001c0040060000048000000000000400000000000180140000008004000000002800c01201a00900300040070170000002008005801000400f0018008000011001000c00001500b000c022027000802000601800b00200140000000014
  | 30 => 0x9ca3b000063416b0488561c7440688894420468123fc5ef12c08ba174828300000de196537d18200d14e480113fdcce600002ab21300003ee9388443d11d1cfc0003a413024524b4740292b83970ab5316548b3d3865825700a5342d5ef0e20ca908012ce0fac75601dc00033d0952000000000000003ca9239403840330d400000012b747652f53054a2c585c3fe1c00a410c3000000000003ba933349d55e21fd06890504944544157f0000bf759d557036208dc101c2b2098108254553c110083ce000135658851ed3e8c85a2e30d2e398c00059904ef01100002cc0b27578078542a400021c400008c947d56384383e880000448dbb19880001d04bc433cc000313400000000002b5c4a62ce4be600009771e0400042845b40498000498d3c82ff000010ac00042ac8430b311ad46d8b0a3150a07000092459bcf1449dc19f106ccb3000006b000116f1c1000000d01e02c90bc337dcffc1ed53a347f8880278c2030dd00001f7c6cb00bd2d402a435811ec1d34b9d36d2a9897838b945c48940075108b32000039a16542b405e000059a45550000d3f0001521000000000000001574000000000000010e71a106101f840001f80322000000030ccfec032cef20000000000000029c0e0958a4172000000040cc389558cac30acc61a30843d400003d822d4f3000008f200001424f2d5b0238d31f35092a60000000000038d2e3cc2c0d6c0002504f660dbc78f4b7cc7557004fc2ca47963351045236c2b5285946801f00004ec096303e810f2988ae800008b056e15e900013aa0000d3400000002ae01ae3e94b7f000113d1ba860756d00a8088cef10e80000000000051d4000179881603d4af2118441100009f9401c00000000000c8c00052bd2bb25bce781539228493c00008254dc38f108051295520000d6703b8f3354b400030f00000ce157b0000c24226000030dc1ea271c00036d439400003fb3de50313958c9a58780004348c570e1c0005010000420cecb0eb8b9e51e400000014ab0000e21015014057b00000001611311c1fd12e160a3df143d17b026201400b6000029a2a013181e6800000010ea2e4448b52712140ef8c5232f0000000000000002ef43912f80000981250877814d8c89269142a392547803a529e000140100004a3016000000005010528a8a000136833f83014190bf5049049c01589e2320c03f33250aa34b51c62af848d470d370299445b4a8cd5d447d60b40a8d79154443d46007a2292d366409c795134820823d4d511f6447e08981da5278c1a50c93dc3d20dfb03ecd38424d00b5810f111cd021e3a4c3da43bd15138b557847302f141b84f80d7527c0ce8ffb33ac6453cf122455a80004b904364a0cd6350142b900007e900000000000000000155c000067d17680000a84cfc00013e00aa427046ac0b
  | 31 => 0xd800010063df8d1b3c8000010e800009e500209f512f24d41273c54ef743545c33f0c3fa268ce9b0f8ccab209159d00010f21e4930a4bdc64e3fd457e2054f644f512154e2490700013125244f0751a4ce7250c5b733e83c649649f611447c11f413933918eb822a0c49305c4be1cf49cd0dac73516b4f7d22f462d204d63e44a09020a3c2f43e14612000010a00007194d500c3000016423ccbd102e0c015668bfa4ef43124630027451c784425c5483cc8000244c6f245110323c652eb353906326480c240fd29548b87051d8093a4dc4a490000a631ba1558000046b0000949000000003b066a00000dd0ba02e3542c00000009c513240002c1916e00000001b54afe0b2c0bb4d0002c480071c0000ca50a300001500e2800016741cf95b108805a70024fac00000001ee89cb324031d01b145f18c800058b82b60000ed25859086371491849244d4000136a05e8f4b0000bec44787d70af00005228c7b0d847790cdc1191814f4000c0ccd40f00c63eccaef0000b5e0be40662f3470a00014710328f9129c8a861eb538c10615354384a0c394cc5623b0e20039c0f3079c42f55cd1a6574052500000004664b0323100001ebd10b5658d0300008d23db43df2a34c1947614ad0c60cb927a000017fc00006f42550000d7000016410260000338544e00000000000247047d279000000057d045f599d4be000000048680001b092b50000581575400015f4f5600000000000f9547cc00038540004bb0000000000000001670000000436c0001e292a20000b3c0000b1203bc0000914000000162f00006503c0c423324800040b8903455cb654ff0afc2e4913c5474af500000af51c06a130582ba41c893807ed2a42d7cd5748f40e656a151b449089521b86730ee43c51b6139d096026b1f345921cbce554020aeb12841e61cb91d23bd4aa5000108a3464335456ced01bf461e47406a73db0e621be061115ac69b3bf467430254a836c0f753868f7b0ed071728401c01a600d42ae5105125076603fd0fe17182643b9c7ce39dc4603251014030114d15a0f8a2e880004a1484e000000017b400035688023510f6b1ec0fed376cbea0e700000b241b42ed550235f085441286a80a043d6005d17546ec0000000baa26d840a17303cd055c6ac57948fa55aced359c8000282d19012b446a35e80001f2566254d11454a2476b26f40000000d3923e400000008ab1adc0000000f0d00016083578476086c91e30d015c4d155532318557241007046a14c0438825a51acdb70be88610e6c000235c56d4b24f72029078b24f9350560937800015685064590045c0a706fc00003a001551f0cf058e01ba3fa4422345ca4d2c4c951466918915f1365349d3fa1804f174d6c5471c911720b2898a22c465552d84df00007674cf55f70d78a5938e89a950fcd2f50
  | 32 => 0x60847445d8bb7281928e35b8de10001085257939f00013112d440000000b2300007c500015362f180004628f9300011690d3c0000bc00003c286da00014813be4f0f00008df00006bc000000010191af49180003fc82d64e9cdfe3b0125b1d240003f00000504044a1be517d4f00000000085618e5079472033305b142d58693354dec000085014608301f817f0a7d36a0d52381ca3c29e5211565d2451bd44b9291829e55e946f10b00004004a5d0de461853e417138dcb3a130424d00004ec10d00670f4d25418cd3d340b42c02d1400027ec36d30b4811000114a011cd9c0000000000014c00006ab4fe07bf2228fbf1c0c926000114f00011962d600003b6c000000117b36e08d63f5c000457c23643a0000000019959080000000797404c80734f800000000000000000199120f4d840004b653854aa0000181939654592c04c1d1c041245630c248590e2c98442e459401f46300000ed146106ec4a845f92c9549a433c52840a0cbf3a24bba3f401f34af4b9029b50441440c8405602802b381351564ed639b800034a49360fd109a4d60c6b31088de051525700000000000d8f00000000000d7159254fb317097f00e1233000004e050d6073bac7a745211cd308c602000072956b40003f8c9af25e8e7a07b015927b14f700002e200000001fa0d040000000200cf4c4dcc0002b4d5272b1c3bb0000211174c876000131c3ae800015c80002718c5500007ae538c0000000cbb0000dcc2bd858e4f9d07028506fe000141504e400020280001eb110018111ac000098f472d1823de13ea313906c58250871a7d09b14f8c4b18ac2cd193d3bc5358d611f983763a480004b44cdb3a1d15836ac00017c95af00011363f1c2042e7c00057fc99f09d48b24dd03c955791a5576126e42f02431230b60000123e000035c0d054533a64000208400000000000000000476c62800004400fb8004299d2f31ad4ecc228c690259cbe53d0871a000086353f00000f84e91000062100003992a2000016b86160000000000113f324424a0001101082c7550e60e6a44d49de2854de83340de617900000000ce0145078808e0b8407354c30724f8b347097624e44900000000220c9e44bb400b2df89320fdcfeb000060e0e752914e614bd195c5653b809e7077144f3e68da7537d1e32df50b628241db20a45de1d610213520990463902c34f0000334418151c803504b050f1fed5514f3041909d962708a127f31b93a848dc53244a91bc46d0c2506e06dd5640ecf5000f9429e93321db0560048c17435fc37a4f888a0027080d0f984851c8c0572c3446500007692ba4b1c23900000bad5d349f4b360288d6952ec000000103953a04ba43044f00fcd1f800001c72e5115619f800049946e14ac444d54248e126c40000f10000217c7db518c3b30dfc8c54fcc2
  | 33 => 0xb6601a49f549309da07bcb702328000503cdf851ec326194c216219d66b0e7d4ea53c032057444b31984ffa20043840d8d5b60254d20268881c07f141e0df4e3920d40000224e4d0f443543e0000000016200000ece0000f8100000000000e9625a80b918f0609089149b56984eb547ca4f2af1524396d270263860314109c413353b1040114c3ab037e333105604214a225acd50343c70b391139a164454b1d84b403628e33105091212b074001942ee16bc166206138e34404b5270013640610d9389139c3008f9e28c53c9222557933e47be111112637f468055c5146446537f3160f964ffc344048486a23403a4094ca6b0000be419e102010fc1f0411d3d013909bc1fd40df511c8e62898000000146e48393e601b41f94c394873d0c95b47c464d212c89b0200ee124b03f64af921e00013c40ff02024b188e82304313000000020ed37510240b50000b4839a41e324a40000000faf1e4d37e22a8000407400002195db1fe01c13f8400022055430000f530210000000000000015bf30ac0005900b5c2b010041c50b734c3c00041f811c27c4e13187d0844830db400003aa49e800000002a400000000000000000126b00014d509ec0003b0c834208160028147a604ec56733c44f53f3473107554b232d0a3a1498e103c4802d000014800000000000fc21514212339437c0000c65021c8654054b670a403670cb896c5960fdc2ebd37c4aad0a736cc93d03dce88432cdf5156c49b06c8c9b42980d629fc0b14d395a200011c217e871801e931725c849500001bb38bd4a9000163f08ccded579905b08f54cd3a946a345b0fad000000000000005430f740001067046c000000058c1ff80000000ac4516510726c000008e809445f8000407c5e93ae402a22ed4741a1ca1d0e08b1034385344728e0843a52e2000116237600004ed031e00013254660d7212783c231753824c40b202a80df900014e020a15bc4b354252f88000054c17d00011eb303826d51807e337700000a50000392153f56c923b35d500c4d751e82fa50354a2c2010e451603cf4874179c71609f0dcd0d30dea1f3d54214b0a42131088d290130b1bad338397c79d2fb53b32625187145c125215d51845853d701fc4bf24451e6335400000010fd04a42400000000366112014242d026e8b1b09a4c1d140068e0e300004a7cedd068c70f1bdc000270c2e4000092737514c915a800017ac00002782560f1c000284c492000135a00001d7513099c51dc445086885511794e22be415407ac82b0bd800001241a4000000009c50ac4b5c6244ae43a3524892b452d64c21e52292a506401a7446e1b3048300000001394f4117243281c41428590c00050cc0005398f612f3064802f8a470340bd342c533a4ba80b337b894c356c0d903f00004d786b0000000053d144600003151
  | 34 => 0x3cecb71467150d18c525e41a14d73e2401c06295ae47f40001fc4000260c58b28352982f8465e30352a90b081ee54c4cac499d5d7527ca9c0da824100ac74c33f4cef23c411a5348d0d136890550c46b22a0449828f400034cc000579c6b64f755694d4c92f4e94b8d112c54a000087e16c9024168c00030bc00035ed3373b08c86586d5ab55512401ae44c74b315dc20a8b5044205f41b40d553f202a82b70bf414e0aca224400027993d534691233ed8d6d2290bb10ed416b2308e4a2fa077e0c1910a0000c734689559450106a471c6761ecd0f531a8de41e6c4ab14a858f32a8bb20ec934a020445c171483a0000ab6148963c53b112b57b48142f794371e18371415c853544848a03884cc0994b1622b49224d8c08d4314b1102e80e03edc81f1ddc04c3860b1d41bd6713850e73366478c3814bcb464ceb1041879c00012f152b017301d404a0000f4900006fb07405df57c842e508d20d4014647022d54b512cb192a6400056851fb2a3c16f0a596454044a8338c4d1f1b10e2227f0cf748f057034acc6d17f931954e0c1e0f0c20e15bcbd752552b415ed342415118602213c606382e61ea51d53c7517703614f3362d07514b47c2549486005545e54b702250ef5673532892e26840004750f5b20310d62c994bc1a080000e547253550e2718506e4083ca293ea94550dc0c0a1c4cb54348865f08c49603a34add3cbc0002738e0e3f1413053b4ca019c4ef344e04f439f00001f501b958b015617891a339d80001ff4221378d65100001d10000000000000046e0bc920645731b94b6918ec21d35640003980105000140d0000b4100004ea3afc6a61668000000000000014380000da12864334589412a2c142b04cfc0004710ca600011a91294583087c1aa1728e804a01122380508e504c17559b8cf2510d38d19b00062b502fd000000020bd13e2e6089f09b800036f47cb0c404713ddcb6e39f4eb038181700000dae4a6c8970000a00081c00019a46e746e8ab3124c9650fc8d464b103641c80fb100008624938cc72e64b0216f537639ece98000122f553800059111df23f964b4e84ba62e0c16314e4ce31f78b7a2b2caee4cc078232e156043d843305340003088f510d4c7751fc930c1d7c37800010d42aa895532050f41041505257c6204d240001fb95990000550000148d1a900002e80ad1000023b441918f2f70be30b64b61191800000e48924eec9cc25f80b0417c000000000053e04b113ec360595c00008648a240ad18111b54db125d35523886d957243e20000b6b0dc8000431163045b400017a1670560c0003d8c000341400055140da05ed606097909e2750e751d406ce00014e125152dd42a071110a019d0000f8c393c8c845fc0004efd40c4888efa00000000000f8200500230000db2000074b00010c903387b82ab4
  | 35 => 0x15cf565134c0730f8e18e00000000000134000025652580000000000068328e487a000095000000000a2013c11fc0e526ccfcf00013050000c6156f52ca505c0910000a2f4a10e611a4ce1204f8a111bf14b108354f5546800004dcb1f19f132d00000180950dce03c95cb3bbd304560091b286cb9d2cac4de0000e0f3e6484728c0cb70aec95728911f42678fd32114574140956548c0b9353f8e173f10459314cad013dc9732588f5e17d48e717b9529570c701423cf1f017cda00000000512146712a8ad628e13f00888521209c7285958bda1318ca41174e8e053c7ed2fc42102b48c8e30e41d850ac7630064bf8480cb95146cdc04ef887d003c6f0500c87556b007900e81b32e214b00c7c8120d4482c56f92e80748e4e15b800025681320000000445417e178400047780004f8400010380000000000025c08500002c5561415233d8625096d0c60ba847d23d8fe756a89db0000000051c54d0fa05a60b70d3b00009fd1df080b466c773559cd8128ac79934c43033aa0ba43fd0cea335c01624cd1661438ca105dd63116783f51a8947e52108d44b60a0105b85f712d01153748fcc27254200460b0421ad1fa048026a3b600e140411a406146850bb0cad443515d0a8d36430fc31124c00b2127c5881aa51ce462d0fb25d135f48ad5613098ae303e04a45239520007c0523858bb33d349a800010414274bdb00011911780466058921f1e256152c3120437182341b2559e379c25c2db10c3254cb1a458d4ae34207534cf0d89507d39b2a5441a000143e31fc9993a194a633285f03b5c8704484c7714ac8cc00409be26fc000445881d0090fef138066f329c89c1e40dd72238424405c00034300000cb0b8050386aa21f13c7364104653d8dc816610fc413c4415190f5015b01033ec1276248d0f009095ce4100c934370bbc1c1c000000000000000004b1cd6600000001a291853f7800042548a74eac93f000121c21a4a2722fc00035cc00028282f51eac5030a28ef6592800000001c24c891684438d841dbcb0f2c5c8a5109d3e51d782ed27b4ab0275870e2fc87a12f50c1214187ff08bc9ae4e281161b48bb937f0ebe44e824813390dd24a810c380083651cc2f74a580aa45945aa178cf6a23dcb9607510033f28cda2a7c1bc0f3c53b16754b424b4b85297953029a0aec4088af4209433c0c095145604bae024d54f59855441d18b3e18dca8b4808aae2bec3ca390c9e50d4132758d4d371a689f334009a028d8f234bd11395588edf37ad2940b6867b49ed15e49545f3000000037240bc3d686bf3a0cefc1a55019198cb7857344693f602bf50e559b0d152743378000000157e4650475247400026184a8310ce8f00a44ff0ab060c3e5cbc013648cb00013ec55050ba000000035913395618a1731b000000003dc00014eb12c8a61
  | 36 => 0xe00009f00000988138cde52860b81000095800015f3473c0002000da25498e3d0b4d10c0a7022c21e00032dd400000011d705f00004758000000000007dc00054c80000000000000063d00009e9482908901bc9cf41fc1881d6c3ed2dbc0e410a93a2011400055f0001107104d09240000edc95d1034b590640ce900008394538a1f42f484d44c12b612a53eb2ab06912a911523040bb6571000039b06d600000002c5000000000000cd800018b8000358809000000000d5800000003322b65142000000000003cb14c476221ec000000019b1dd0f223b686ef1468c5f18880000000ce84de800031e550725f4ec11ab800059180002ff4000325864c26e46be0001612433400021044c210dcfb400005a8547000047a8c9715993ac0000a28468121806c4ac11288a5245c0f284db80002088f353830f0e16642913be01331e803e70c711f52efd28d283c00033fd4441e952bf095d45d2f2852e38ec000269c27f016d24d1deceae4fd45242668ebd3a28bee16909ea30703391864bc829f8e541870aab15a45a008a84ed2c54fe431f00a30000dff09cc72c387061338985180c2010e12dcf6547e550e026cc7e0000d2314f45965260a6a42dc43e46c52fa49912275060d21168800000010710d21655400071b2b2499d000063f2cb8dc11a94fff41d0e29121c8e95830f24111ca82045138f2a38aa92fbcdc7060cf2c3c3165a00015fa000019e4e1c0000f4820506f80554b80fbd0d7cde91458aa12d491ef4f491e2034d1310a54af1514878e089d2171f540ac199449d53441980578a4a0000eab3b8cdf03f58acc0000d4d118c00012692fb53fc7a43450aa203c0971157800032c4e3235a0d4b54e50d022d8b2c5464593000058921700000000f5f3f486bb14d40000118d1815245c0000116a471459b075800020f0d9d0000a780000f9843dc00022f8b18544ca9622cc1ff536064304ad3462b9400002acc3e1c1800046c00000000f5c0b809972770e9500002ce000000026acf92000032a0a182de444400014dcc130001343000000000003681d0cb08000057f2bf472a42d48993648f37000094a446ce7928c80000000e5e37790163d880003f64e672e294d904746cf3e100000000702486ceed000000039608963a50d82482d22d35d06dc51688261ac56224a4ce9d2cecba351fd4060dcc00032354513c412e93c6800059652121f00df2449cff300008644cd824600010cc0c00629583cada0000000000000000000001c98fbb3c98e3f373ce341ce4a330ec0db141cc81a04b45d0327030e4c7843104e060a284876d3a7146249444cb01ccb9a234c6c52360ff01548de214f00003b555b9479ce7100014070001260553475c07902d400009f7248424f00004ae37d04493d3c0004d9d210000000000000002cbd0e3416511a000
  | 37 => 0x7400000016533b28d3a5784e1f072c00008b90900c58f550a988a101914dd13b8000000154a4b8c30f0d5c67057e4000155800048245972534bbb000157600000000000a2248a8000000000009b0a3f0a5cd1d01a8ea936982c700f40000adc3dd07192c10d3874a573119e0348f05412000025ec4cf2380f2b0000d4736bc67a1cc87d600000004b412c53aa850b3178f472b9c51c4a6457a0000f0123441ca445d04b2bcc73b05a418c4b3cfb511e1216593802e440c43c0bf875a123c675113837745f0eb6221c7872e5c00000f047023c161f1a200001b28dc20000000173800023ec3b632f4df116289df1ea10df32644dd4e50dd53adc5cf4aa854345c481708a5102434d2420a2ce5103704fe0c6cae10cc147a13d933102641d924f02a0295501b2c040004fbc3d722680003b782871f180002b7c0000ac46c343448cf139d3ca214814b03c52822f585804b6c00000011a100013ce1a3c73700008c050d12de365445a3a2c2060000e724f61104000047a00007300000fa7000135c33b40005718d240000712202046f36301b606a400013e4677000000033180000000de0000000000001ad1dc800008e4b4c000106900a00000000000182c0001ed816a00008232e9460d161400042c82684c4cf1853211b900012413a68667135851500010990000985523d6503e98806103d67600000005114908596cffe0b3c65b0000eb5188c7c820c84823d1013a00693b526088eb29b8f8818e924a49cd1be1b34abf28a87571875391356054401a14bf171d5ca598d53d00003a24154e9e06b065221995e4093069e1d74f3819b9012490c03601807fa4f3cd4300007e258e96033678e7f3449219099959c43214211fad25d4a9c000114d4350000d962aa0fe00a7ca641b8136257580bd597963201082a500006df1974d6a38ad0a02d580a03e0d5fb290d52a52d50ca33012fc548c263024800042d13f212d953e0000636144c6c7236901c49114493570a7153bc1091054b7450e85114bd8ea21af51f701694ce3bd07483cd93f100004c300000003c94f1c0000b680e1512e30604e8366c38114bca2538e054c54ec38e0540c000aa925a2fc00004ebce6532b80002ef4000491d28c115163b00003e43a5ce52488d5490c10b4f27849fa253884a10743314ab4a900f5503e4e0c9d2595055f1bc50ed2f0547613601794ed86c029600005258cc5207921d23b91a731d864b34a90b8280d07c3524da50dd516b1ab507b10144323e18bd256e92060a6c868253c0004dbc0003cd00000000e4207e862c0000c9828b472d0be132625590fa39d131d1a70000000023e04fc6960000000000139e431c0001be91e500008301bd958c24700001568a0255d0d26070c0fd35bce1e51a909c41b46270000fc941494575694e25197133400955d9000145
  | 38 => 0xda2c78000000000026dc8af45cc000003067f53048884f34d361f441a0168439623f40003444040533d61c38647cc0b1883f3b2131b0b9c5cb5574000264cce40e01050227954742b962b00201844770c6406980000e4098c0000f8d014c34625214b9000162d316c96e3408000354ccd33ee532443940003dc0c6746b800000009944820bff00000004998a7516ac000004800004a132a0db000006500002599065000006148141873d6400005812b21e78fab56545291ae958f00000004565091000003b00004f1246500951b024e0ee919f3dd808316c4542107d23600cca2134f5286364d2e538753ee4988a56000079100000003f942924ca0000408c0003a140003f6cc9554f0f6f135c000000083d4bfd2a011f1066206d3b247fcc413bc160d55b400020dc73638a82374ae8efb1d4913b3580168175108b246851d30312d64bbca3e2f080050ef0420027cba1302098d23bd01e0001601529cc0f042c3d03a045122ad0b7b3f88c7000006b445043f841e0ad51da0fc60fb06c6321447310b407833d41b01f9ce6d539ca89036c9204bf4722576877052849153e4017f1079271183ceaf54dd04e4c20352374c6c12e9c8ae216090008f105d033c34244241893d18ca80324b0e3b7086d00000000000393000154652a94ba1428c1b59b0ae6138923832e8a3725e4dd01bd00000000f214dad40a190956c0b843594acc0004b2c27e203d508097cb6d0abcfe63fe40000000f7a1224000555912c25d527843c49d3534d5c856d40001c746510d1cdb9424932e49a0c300fa8c2710e51e00334561296c88c14351e41fc0d971fb01f4347917947689ef172090b20b8cd65314c2a16193903d74aea518515a0c14a9305746990a3499b012c04d1edccfb02389a608c009a0f8033f3cc419557d90ce10200202b3c4721f104bc103000017651f049f9466000085b34d562a0000ca2000000000000000d2808c11494fa1e6158a2fe400011dc0000f00a3459355030e783fd21fc88f31c85cd530894b38f80f424d13f400007bc46fd52e0ee0000006d316528c9d80f9460041840000000bc7092c000000000015052c2374400000001b740ec00000012690000000000000029705080b0c00000013010000319000000030d94543558b864cf800058382df0001665000142400000001d380000000ce248b126f0000000353c0001dd80004294b222d093773f2c0004e100004590a0e13e8eec3af0c480e1841233716524880e660d2457525c150a21253d108ac8ce2d904c056807c340c13600000f2e3b245541980b53000090c36346724fe40004494e362b911344a6814e16c0d2800002d5000112d2f748fc000105e0310a6c470548c00000000000b4a49480000568000153d4e52d2c55c00009400a085774e54b090000000307ca924a749d11f
  | 39 => 0x338000111800040dc3e92bb49ad2a10c202be000054ac00000000001774fb80000fa416fc00004787800000111000000001d8ff8423068c23245620000000588c66600000001f715b30000d7e02b4dad2b3400036a40001d1d051330800e149d4cb4fb48bc18bd522577d5040618ff624282ff3ef85583b193e32d0c2c4571c5f819694f2000000000000000000b0b04d0000000041346d4000302d1c930451ee2eb0fa802d071f41dc42940e10a329d14120000fc106482d102b93290000b9b12ec000575093100002503b1d29c28114da0000000566165d0b4868b00006d7000084852949c800002b80000eb307a4b3828790da141c00d171000243ac0002aecc78258541a147c00000013c3297c26700001e1000125f00014d007112bc53500000000e043ef09140cecec457f8a0813c8a6f45e0b282a1ce4c51053da436021c1058343222c00003e52d359705b606bcc8f25900001cac25900015061d440004bc0f0032001f5516d4b3316815f1b78aff53f480536f0c502e2ca97460cc3234245d81db86b81dc4aaf245886f2b20f5755c889d112086c0efc8724ee42444ac05be386ca1c41acd7d0eb400013983b12d351d33c6c3ef4e2c2f20d555f02e1c4e14e900002a4400052dc1fe52401c527e034d11a08a90b2061b2ea55ea2e084ca53c4a2e4cec4212f6504216d540b3834000231c9ee0001221380c3d9322c64147b130043ccb620eacd253da50d70000aa707200132b1400000005793f500002f80cb60000afa000149437d800027800001e7c18d4fa47bb42ec53f0a103f959a11430000bb443e01f21c9c9c21bb955a3d488850e0d41100004d523740001a5c102391d0a2406800041f400013210de00010c053a520700013df00011e13a9d36c318c9d041d8b4644c8a7b3e706e9593c9ca438082d5224dbe26600a60001043000023f2fac0633cfc8e536a8c82185cc7d1ef47940e5c88626d500f444118d067036648c8ddf2ee08c32ac550032bcf29584153a4f792ee0c1d3060af85d5000153359b4f87000109843e4f5800007594ea400000004014d489173d28c05161c2992a601df327cd4c34c00c500011e950983172fd84db1924c4025a470d37bd23a113cdd915d8c660cb4f7300013d631285530001517332c0320000ccf3e745c200005db2010bce16e0b07564c0004dc92973974481038c3f04bf8dac2cdc83e556ca1a0b045332cd0000569000000000004e5d16700012903ce4e5700000004b991334c540001fdc0001b8ccb0007536955988f435e0a511ec4626214469430eccd846c931a1accb5b32751371d9530d3b907b2097445817d94580164aba55f559f34592011f6000006440000000ebb50a54803f68d770000e590000324102c000457000016e56024ee83a9000014449a8000073d4c73ba0e681f907
  | 40 => 0x9eb48d4cd21b50e6b4290f0b363800013a408223e071e1239493000021554040724a1d0603a98b3d42bca8c124499524382722b6d34f1c84000555c0000000000129c26126e06af423400000014a40d0036919515a322b128848d1112520c0001d9124b49846ed3010c8a38280001910b633418b310000c74000164737593c24f6cd8632d430a3bf93fb29dc417027477f30b930303d8f7f00005bb4e0409657046ff394078316a4e4014c05f114787ef02849a525b432b1d502dd31c403e376915532f8ffd1b209d50a2526c1a344dc18f803138084571fd9528454c00000012c34308a5331103c80e994854258b4e2da902930a4ab71158954084d0581e8c07e00014c44f645d700008460000ee63c9c1dd00003ac2b18bab3b140000cf49bb42203de2a6862a55d400027c93c50000c8c494cf3a00dc06e10d4c46000134b28d4a9b2f3c1e85050026578c59f3c18000484c0003ba400000000000b5ccc11a194a030f434b562d1f226588503bfcf134c843655860a663c083f101d0a4c0228fdd00001104c8c0002fcd4092940f082950b211f951974ab132b0000d8300014990000c315070c880608ae049709370d882e5000132058a000023547b42ddc6d135001a147d82513b6467905b4be738d494641e828527f832544615bb288000040d800000001131d3d28f54453f6447013d414c0004d2000036903925088e7e2ea0d8529207081ccceb20d6874d58d01a73ea452314307d30cbc7c7000144d000123f04054cc4a488ed262c00059988b721dc00049b43af000038a00007453d80bdf3600cec51b4cee4fdc5463a094ee261d1fc1694b9c06694653320d4a13cd0bf0000000031d60536fcfea29cd4de39c0cdd1191592563534743fc9b40e3c2175140bd022e41765980ea050bc1a529109251ff0b2d270541d3dc4b49555528a29f057809dce6455b9399300c9060e9c85e4e003273c58a6057f02fc1188c692040cd94be55502b6002221112d21c301ed57152314250b722c00f5400005d62fecd5f29142ad0b6c9dd04b8fb23eb83cc0c2c7423cb4ab209d0c874cbca57494149d3b94e9f5708c624d04ecd525d1743bb808f1130c28000007b17f40002b080cc3e6c4003c1097c03a95ee45510ad25a000020e06e6288d18800016480000ed41cf044341714023d9d38603f85dc06d4e3012f47f3371000000843a526011924ab88b800015b71fa8c3a0000000000000046f40002cd40000000000000000009e81650ba4ead10ec0c10ab902f16716145621114506d04c59a884f2e3800000000003c2452000000000a4c842296890f58988931a81248131541636d8c7a0000000000000000004af0cf89910db88d90000000000000050d8b5735ac00040e8e4137cc00000013a6000064a331000021cd4e400012263644bd500000003
  | 41 => 0x337d5e8474404f301c4960000e8c2a1400057480001634e452de4d4500011134d5cc0600015a70000f9f388c0003da00000000c510000ae200001a81de837b00000003f45482244090151589095644b334eb4eb40000d1500013090c504fd37e800058d8278000158400005ba382d0e64098e5a14e84d319b4b8942f80001da92af00000000000d9a00000000000000000000000008cd119c00000000c84a949ff1bcc000000000008608844b845711a48d13000044237b15405220d9400015fd15900005520dcb43b0f1e08d555f19acd414ee000000000000000b5a2ec01f603540002d540000788c682ca800000009b200010344b2140816105ea000000019a084000008ea00002fb07380004de4000247c000543c00043b8bc5000093b0000d2c2df00ed07c4048035c22d01c4af011b0e4b10c0bad27655f54b5556f065c161251c90d1140b44313012257e04551b6d5f124a12f2275cea30e84479553161358913a029d82bd3e3d2da4d6401e00013fd49c883350b800007949f40c680005774d32063c1962f615891fe55eb46cc4250104062377565f38b15de00000001ce148646a82522d74c9e35941de58f4fe83180aa300002980000d9f064cb763e852565478dc3134415109bc49945e8486041d0622cfcea426a95a9313c0000000c3806ac4840000404056ccf835b000058e44a0341c809559143c3fb800001708821ee4000372800000000005318
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x846c725954304237390caa18211b5c86550c10a38e6aa2860851c7454d430423aba8c2a18218d5506150c10caaa630a86084f170185430423cba8c0a18218e5506050c10cb2a630286084f1711814304237390ca218211b5c86510c108ece2328860847a70194430430fb2a8621821875954310c108deeca90a40862d645485204326b1aa429021879926314810c3ac9318a40861e6458c520430eb22c6290218b5926214810c9ac7310a40863564984520432ab1cc2290218e5926014810cb2c7300a40845e73197420422eb98cba1021179cc65908108bae632c840845f73595420422e39acaa1021179cc65508108bae632a840852c7255142042963a2a4a10211d5d46150810c6aa830a8408665521854204278b80c2a10211e5d46050810c72a83028408669521814204278b88c0a1021179cc65108108bae6328840847671194420423d380ca210218bd954210810c5acaa10840843e74197320421eba0cb990210f9d0658c81087ae832c640843f74595320421e3a2ca990210f9d0654c81087ae832a640854c7254d32042a639aa4990211d5d4614c810caaa630a6408665521853204278b80c2990211e5d4604c810cb2a63026408669521813204278b88c0990210f9d0650c81087ae8328640847671194320423d380ca1902193d95320c810c9aca990640863954982410429ab8aa8208219654e608c410aaae2a9862086695298221042b2b8aa4108218d55261900108bce6328800845d731944004237390ca200211b5c86510010a72e0aa0800865553986300421f3a0ca180210f5d0650c0108dce4328600846d7219430042acb82a6180219954a618801087ce8328400843d74194200422f398ca10021175cc6508010ad2e0a90400847576946100423cbb4a3080211e9da5144010ce2ebb2a200857276d9510043393b6ca880215c5d66444010ae6eab2220085d37359110042e839ac88802178dc96444010bc0e4b2220086b16419110042793b6a8880213c9d85444010e62a82a220085d27315110042e8b98a888021789c85444010bc2e42a220085717598d10042b9baac6880216cdd16344010b60e8b1a20085e37258d10042f0392c688021b458c63440109e4eda9a20084f27614d10042d93a0a6880216c5d05344010ea2a629a20085e27214d10042f0b90a6880213cdd943440109e0eca1a20085727510d10042b8ba88688021e450c4344010ae2eb31220085737558910042d9ba2c4880216c1d16244010ba6e6b1220085d0735891004370b10c4880213c9db52440109e4ec29220085b27414910042d8ba0a488021749cc5244010ba2e62922008761521491004279bb284880213c1d94244010ae4ea21220085717510910043d0a1084880213cdd932440109e0ec9922008572750c910042b8ba86488021f04c83244010
  | 1 => 0x328421eba0ca194218e5506050610cb2a6302630866952181218431b2a2c2204219594d610c210ccca4b08410861f6418d5444327b1ec4aa2219318f6255110c5ec8312a88864f631895444326318c4aa2219518f6155110cc8c5b0aa88865863d815444334316c0aa2210fdd95415110a38e6aa0a88852c72550544430e326c6a9a218bd936254d10c58c9b12a68862f641895344316320c4a9a2193d8c6254d10c68c9b0aa68866462d85534431c326c0a9a219a18b6054d108beeca98a68851c7454c53442a6392a629a211b9cb65d0d108dae5b2e868846e72d964344236b96cb21a211bdc96550d108d8e4b2a868847771595434423db82caa1a211bdc96510d108d8e4b28868846e721944344236b90ca21a21475cc5410d10a3ae8298868851e7550c434428e3aa8621a211d1d56110d10c68a8b088688654535844344278382c221a211e1d56010d10c70a8b00868865853580434427838ac021a2187d936354910c38c9b1aa48861f6418d524430e320c6a92218b1936254910c98c7b12a48863464d85524432a31ec2a92218e1936054910cb0c7b02a48846f7654852442963a2a429221531cd52149108bce7b2e848845d73d97424422f39ecb21221175cf65909108bee6b2a848845c73595424423bb8acaa12211edc165509108bee6b28848845c73594424422f398ca21221175cc6510910a5ae42a0848852d7414842442973aa84212214b1d542109108e8eab088488634545844244332292c2212213c1c161109108f0eab008488638545804244334292c0212213c1c5601091087ce9b2e648843d74d97324421f3a6cb192210f5d3658c91087ee8b2a648843c74595324423bb8aca992211edc1654c91087ee8b28648843c74594324421f3a0ca192210f5d0650c910a9ae4298648854d7314832442a73aa6419221531d5320c9108e8eab086488654535843244332292c2192213c1c1610c9108f0eab006488658535803244334292c0192213c1c5600c910c70a8b068288658535833144334292c190a218d15161d01108bee6b2a808845c735954044237b92caa02211b1c96550110ca8a6b0e608843f74595304421e3a2ca982211bdc9654c1108d8e4b2a608866452587204421fba2ca902210f1d165481108bee6b2a408845c73595204421fbb2a82a021875516315010c5aa8b10a80861e6458c540432731cc42a0219358e6215010c5cc8b10a80864e635885404326b1ac42a0219558e6115010ccac5308a808659639805404334b14c02a02117dd95314c10c3ac8a98a60864d53588530430eb24c6298218b9926214c10c5ac9310a60862e645885304316b22c4298219398d6214c10c6ac9308a60866562984530431cb24c0298219a58a6014c108dce432e860846d721974304237390cb218211b5c86590c108dee4b2a86
  | 2 => 0xcaa18411d9c46550c208eae232a861051c73551430828e3a2a6a18411b5d46250c20c5aa8312861064d531894308274b80c4a18411e5d46050c20c72a83028610659531814308274b90c0a18411b9c86510c208ece2328861047571194430823d380ca2184187d954310c20c3acaa188610639549824208296b92a8210419654e608c820a9ae4a98641047776544510831ab22a2288419558d51144208bee6b2a821045c73595410822f398caa0841175cc6550420a68e2aa2821062d541894108274b80c4a08414d1d15150420cc8c4a8a8210639541814108274b90c0a08419c5446050420c6ecaa08821063565504410821fba2ca988410f1d1654c42087ce832a621043d7419531082aa38aa6988419354c624c4209d2e03126210554735453108332312a2988419654c604c4209d2e4302621067151181310832bb2a621884195595310c420c5aa9314801045e73194400822eb98ca200419354e628c02087ce8328601043d741943008236bb4a5100411e5da5288020cd2ebb2a401066a76d9520082b4bacc8900415add56448020b96e6b2240105c87359120082f1b8ac890041781c56448020d52c832240104ea76d5120082753b0a890041ca5505448020b94e62a240105c97315120082f1388a890041785c45448020ad2eb31a401056b7558d20082d5ba2c6900416a1d16348020bc6e2b1a40105e07158d2008364b18c6900413a9db53480209d4ec29a40105aa7414d20082d4ba0a690041d254c5348020bc4e229a40105e17114d2008275bb286900413a1d94348020ad4ea21a40105697510d20083c4a1886900415a5d66148020ad6eab0a40105ab7458520082d43a2c29004172dcd6148020b90e6b0a40106e16118520082753b6a2900413a9d85148020b54e828a40105a97414520082e5398a290041725cc5148020ec2a228a40104eb7650520082743b282900415a9d44148020ad2ea20a40107a1411052008275bb262900413a1d93148020ad4ea18a4010569750c520083e098862900419c98560d531087eecaa0a9886726158054c433930ac1a9e2117dd95314f10ce4c2b00a78846e7299543c4236b94caa1e211b9c86510f108dae432887886726158352c4237bb2a4296219c9856014b108bce732a858845d7399542c422f398ca21621175cc6510b1087ce932a658843d7499532c421f3a0ca196210f5d0650cb10c74a8b00838865a5358031c4335292c010e218d5506150310caaa630a61886655218520c4338b0cc1aa4210fdd95415210ce2c3300a90867161983538422fbb2a629c219c5866014e108dce532a870846d729954384237390ca21c211b5c86510e10ce2c3306a50846f765485284338b0cc029421179ce6550a108bae732a850845e73194428422eb98ca214210f9d2654ca1087ae932a650843e74194
  | 3 => 0xdb514c0309b4ec28a601859a74145300c2ccba0a298061729c8514c030b92e428a601875151145300c26dbb28298061361d9414c030ab4ea20a601855975105300c3c8a08829806136dd9214c0309b0ec90a601855a75085300c2acba84298061f0484214c030cd4c4b06a99043f7655054c8335312c02a6419a98960d4f208beeca98a79066a6258053c823b38ccaa1e411d5c66550f208ece232887904757119443c831d2a2c0216419694d600cb208eeeca88a39062d5418940c8326a98c4986419a58a60d522087eecaa0a910669629805488334b14c1a9c4117dd95314e20cd2c5300a71047671995438823ab8ccaa1c411d9c46510e208eae2328871063954181428832ca98c0994411ddd95114620c5ca8b10811064e53588308830fb20c6aa2419318f6255120caec7b0aa89065463d85544831bb20c2aa24195d8c6155120ca8c630aa89066762185544832c31ec0aa2419c187605512087eecaa0a89051c73550544829a38aa82a241871936354d20c58c9b12a69063764d85534831a326c2a9a418dd906154d20c68c830aa690657631855348333b10c2a9a418e1936054d20ce0c3b02a69045f7654c534828e3a2a629a41551c55314d208ece3b2e869047571d97434823b38ecb21a411d5c76590d208dee4b2a869047771595434823a38acaa1a411edc16550d208eee2b28869047471594434823b388ca21a411d5c46510d20a3ae62a0869051d7414c434828f3aa8621a41471d54310d208d8eab10869062c54588434832629ac421a413a1c16210d208f0eab00869063854580434832c29ac021a413a1c96010d20c70a8b06849065853583324823bbb2a228a414d1d15114520aa8e6a88a29045f73594414822e39aca20a41179cc65105208bae632882905357115041483162a2c420a413a1c16210520a6ae8288829066562144414829b3aa8220a414d1d54110520c70a8b0082904e872580414833828ac020a410fdd1650c520878e8b28629043e74194314821eba0ca18a41555c4530c520c98a6b1062904e87058831482aab98a218a4199588510c520aacea9886290554754c4314832c29ac018a413a1c9600c520ce0a2b00629062c5458b404822fb9acaa0241171cd6550120c98a6b16609043f74595304821e3a2ca982410fdd95415020c3aa8b18a81063554584540830f322c62a0419358e6215020cacc7308a81065563984540831b322c22a0419598d6115020caac6b08a81066662584540832cb1cc02a0419c58660150208beeca98a61061d6454c530832aa9ac229841875926314c20c5ac9310a61063664984530831ab24c2298418d9916114c20c6ac8b08a610656635845308333312c2298418e5926014c20ce2c3300a61047671197430823ab88cba18411d9c46590c208eae232c861047771595430823a38a
  | 4 => 0x6ec830aa89865763185544c333b10c2aa261991886155130cd0c5b02a89867061d81544c21fbb2a82a2614b1c95415130a68e2aa0a89863854583434c237bb2a4292614b1d15214930ac8e2a90a49847771594424c23a38aca212611d9c465109308eae2328849852d72150424c30e2a2c621261361c16310930a5ae8290849864d63148424c2973aa84212614b1d54210930c70a8b0084984d873580424c334292c0212611ddd95114530a68e8a88a29856472544514c237b92ca20a611b1c965105308dce4328829846d72194414c29ab88a820a618715163105309b0e0b18829853574144414c32ab18a220a614d9d54110530a68eaa08829863854580414c26c39ac020a619c145601053087ee8b28429843c74594214c21f3a0ca10a610f5d065085309b0e0b18429864d63148214c2b2b88a410a619558c5108530acae4288429856675484214c2b23aa4210a61361cd6008530cd0a4b00429867051580214c30e2a2c7a02610fdd95415030c5aa8b10a81863554584540c317322c42a0619398d6215030cccc5308a81866562984540c31b322c22a0619598d6115030cccc4b08a81866562584540c334b14c02a0619c5866015030c72a9304861851d73550430c237bb2a4290618b5915214830ccaa4b08a41847771595420c23a38acaa10611d9c465508308eae232a841852c72551420c30eaa0c6a1061365c06350830a58e8a92841864c63549420c31caa0c0a1061365cc6050830cd2a4302841862f65508420c316b2a84210611ddd95114430c6ac8a88a21866562544510c237b92caa08611b1c965504308dce432a821846d72195410c29a38aa8a08618755063504309b2e031a821853474545410c32a31aa2a08618e55060504309b2e6302821867151181410c31bb2a82208618d595411043087ee8b2a421843c74595210c21f3a0ca908610f5d065484309b2e031a421864c63549210c2b238aa4908619518d5148430ac8e4a8a42184d973181210c334a90c0908619c5446048430cceca908421866565484210c30eaa4c720061175da538c0308f2ed29c601865975d95300c32d3b6ca98061565d6644c030ab6eab2260185cb72591300c2e4392c89806174dc5644c030ba0e2b22601869964191300c26d3b6a898061369d8544c030e32a82a260185ca72151300c2e4b90a898061749c4544c030ba2e22a2601855975989300c2adbaac49806166dd1624c030b30e8b1260185d371589300c2e838ac498061b2588624c0309b4eda9260184da76149300c2cd3a0a498061665d0524c030e92a429260185d271149300c2e8b88a49806136dd9424c0309b0eca12601855a75109300c2acba88498061e2508424c030ab2eb30a601855b75585300c2cdba2c298061661d1614c030b96e4b0a60185c872585300c368b08c298061369
  | 5 => 0x54d7314832502a73aa6419281531d5320c940970e8b0064a0658535803250334292c0192811ddd95114540aa8e6a88a2a0564725445150237b92ca18a811b1c9650c5408dce432862a046d72194315025c382c818a8187590530c540aaae229862a06356414431502aab98a218a81559d5310c540aa8ea98862a04b874580315032c29ac018a819c145600c5408bee6b2842a045c73594215022f398ca10a81175cc6508540970e0b2042a062d6414821502b2b88a410a818d5905108540acae428842a05667548421502b23aa4210a812e1d16008540cd0a4b0042a067051580215022fbb2a6298819354d6214c40caaa6b08a62046f765485210326b1aa4290819954961148408eee2b2a642047471595321023b388ca990811d5c4654c840972e0322642061c6454d32102a6392a6990818b191524c840a98e6a9264204b974181321032ca98c0990819a548604c840c9eca990642064d654c8321023bbb2a2288819558d5114440ccac4a88a22046f725953110236392ca988811b9c8654c4408dae432a62204b970191311030e322a698881551c5534c440c68c8a8a622055473545311025cba0c0988819654c604c440ce2a23026220657654c4311032ab2a621888117dcd65484408b8e6b2a422045e73195211022eb98ca908812e5c06448440c58c8a92422056471549211031a322a290881591c95148440972e83024220669521812110338a88c09088199d952108440ccaca908422043d76952401023cbb4a9200818e5d76550040c74edb2a80205397598d401029dbaac6a00816adc96350040b50e4b1a80205b37158d40102d838ac6a0081a658c6350040974eda9a80204ba7614d401038ca98a6a00816a9c85350040b52e429a80205b27114d40102d8b88a6a00814e5d66250040a76eab12802059b7358940102cc39ac4a00816cdc56250040b60e2b1280206a962189401025d3b6a4a00812e9d85250040b34e62928020599731494010394a90a4a00816c9c45250040b62e229280204bb764c9401025c3b264a00814e9d43250040a72ea1928020789320c9401029cbacc2a00814edd56150040b36e6b0a80205987358540102d5b92c2a00816a1c96150040d62c230a80204ba76d45401025d3b0a2a0081669cc5150040b32e628a80205aa7214540102d4b90a2a0081cc5445150040976ec98a80204b8764c5401029d3a862a00814e5d43150040f226218a80204bb76485401025c3b242a00814e9d42150040a72ea10a80207a121085401032d31ac1aa6610fdd95415330cb4c6b00a99863a5458043cc237bb2a4296611ddd95114730c3aa831a819865963983548c21fbb2a82a4619658e6015230c72a8302871846f76548528c23bbb2a228c61879516310230c5ec8312a89864f63189544c333b16c2aa2619918b6155130c
  | 6 => 0x34863d386cba1a431e5c365d0d218f4e1b2c8690c7970d964348637b92caa1a431ddc56550d218f6e0b2a8690c7870595434863db82ca21a431e1c16510d218f4e03288690c7970194434868eb98a821a43475d05310d21a3ceaa188690d1c7550c43486363aac421a438b1516210d21c98a6b108690ce471588434863a3aac221a438d1516110d21ca8a6b088690ce472584434871a2a2c3a12439514d61cc921c58a8b168290c5f73595414862e39acaa0a439314d62cc52187ee8b2a6290c3c74595314863dbb2a0282434e1d15014121ab0e6a80a090c3f76550540870eaa2c62a0438e5516015021c3cc8b18a810e4d63988540872ab1cc22a0439698e6015021cb2c7300a810e3a64580540872d31ac02a0439658d6015021cd4c4b00a810e7261580540862fbb2a629843875915314c21cb2a6b00a610e1d6498c5308716b24c4298438d5926114c21c74c9300a610e3964980530871d322c0298438e5916014c21cb4c6b00a610e6a62580530873930ac0298431e9c065d0c218f2e032e8610c7a70196430863cb80cb218431edc16550c218f0e0b2a8610c7a70195430863cb80caa1843471cd5450c21a38e8a9a8610c6d751894308716aa0c4a18439354c6250c219cae23128610c7575185430871aaa0c2a18439554c6150c219cae430a8610c6e72194430863b388ca218431e9c06510c218f2e03288610e1f6550c430870eb2a86218438d5526190821caaa730c6410e2d5498a410862f398ca20843175cc6510421c9aa73146210c3e74194310861eba0ca188431b5da52884218eaed2944210e6575d9521087333b6ca90843595d66448421aceeab224210dc77359121086e239ac89084378dc16448421bc0e0b224210ea56419121086733b6a890843399d85448421e4aa82a24210dc67315121086e2b98a890843789c05448421bc2e02a24210d657598d21086b3baac69084369dd16348421b48e8b1a4210de37058d21086f0382c690843b158c63484219cceda9a4210ce67614d21086d33a0a690843695d05348421e8aa629a4210de27014d21086f0b80a69084339dd943484219c8eca1a4210d667510d21086b2ba88690843e150c4348421acaeb3024210d677558121086d3ba2c090843691d16048421b8ee6b024210dc4735812108770b00c09084339dd921d40219ceec908a010ea6644845008752b224228043b198d2114021d8ac6908a010c7b76540500871cb22a0280439658d5014021ec242a80a010c5f7654c53d0237bb2a4296811ddd951147408beeca98a72046f76548529023bbb2a228c8117dd95314d40a98e4a98a6a05547154c5350237bb2a429281531cd5214940ac8e2a90a4a047771594325023a38aca192811d9c4650c9408eae232864a04b870590325030eb20a619281535c8530c940c5ac829064a
  | 7 => 0xaa2630fdd95415131a58e4aa0a898d3870550544c71a2a2c3a1a631bdd95214931a58e8a90a498d6870548524c63db82ca212631e1c165109318f4e03288498c7970194424c696b90a8212638715163109319a8e2b188498d2d74148424c726b18a4212634b9d54210931a58eaa108498e3454584424c66a39ac221263991496110931c38a8b1e8298c7b76540504c69c3a2a0282635a1c9501413187eecaa0a818e2d54588540c71caa2c02a0638b9916215031c9cc6b10a818e6562984540c735314c02a0639a58a6015031c74c8b00a818e5a63580540c735312c02a0639a5896015031ce4c2b00a818e3554986430c637bb2a4290638b5915214831cd2a4b00a418c7b70595420c63c382caa10631e9c065508318f2e032a8418d2c72551420c70eaa0c6a1063355c46350831a58e8a928418e4c63549420c71aaa0c2a1063355cc6150831ccaa430a8418e2f65508420c716b2a84210638755263904318baed29c6218c757694e310c72abaeca98863959db654c431aaaeb3226218d5775591310c6e3b92c898863711c9644c431ba6e0b226218dd070591310c74ab20c898863359db544c4319acec2a26218f1554151310c6e3390a898863715c8544c431ba4e02a26218dd170151310c6aabacc49886355dd5624c431b2ee8b126218d9474589310c6e9b82c498863741c1624c431d8ac43126218cd676d49310c66b3b0a498863659d0524c431b2ae82926218f4552149310c6e9380a498863745c0524c4319aeeca126218cd476509310c6ab3a88498863555d4424c431f0a842126218d5575981310c6abbaac09886365dd1604c431b28e8b026218dc772581310c6e2392c098863b4580604c4319aeec98ea018cd7764c4500c74b3226228063a55913114031d8cc4988a018ec5624c4500c63dbb2a0280638e5915014031cd2c4a80a018f5131540500c733312c3aa6430fdd95415321cccc4b08a990e666258753c862fbb2a629e43999896114f218f4e132a8790c797099543c863d380ca21e431e5c06510f21c6ca8b088590e565358432c8716aa0c4a0e439354c624c7218f6eca80a190e6562987548861fbb2a82a4439958a6115221ccac530ea710c5f7654c5388732b14c229c431e9c26550e218f2e132a8710c7a70194438863cb80ca21c438d5506150a21caaa630a6510e2e54588418872729ac418c431edd95014221c3ec831aa890e4c63d89544872a31ec2aa24396d8f6055121cb0c7b02a890e3b64181544872db18c0aa2439618c6055121cd6c4302a890e7361181544861fbb2a82a243471cd5415121a70e0aa0a890e1c64d8d5348716326c4a9a438d1936154d21c76c9b02a690e3864d81534871db20c0a9a438e1906054d21cb6c6302a690e6b621815348739b08c0a9a4317dd95314d21a38e8a98a690d587054c5
  | 8 => 0xb544c83299cec2a2641970d54151320cae3388a899065715c4544c832b94e02a264195c970151320caa6bacc29906553dd5614c832b1ee8b0a641958c74585320cae5b82c299065721c1614c832d8ac230a641954d75981320caa7baac09906563dd1604c832b18e8b0264195c771581320cae238ac099065b2580604c83299eec996a2194cf764c8510cb473226428865a359132144328eeeca88a21963564544510cba2992a228865b24ca6014432d9264b00a21967151580510ca67bb265a806533dd93214032d1cc8990a01968d644c8500cb62994c228065b14c961140328f6eca80a01963964540500cba4992a0280659c58550140328beeca98a7a0c6f7654852d063dbb2a02868317dd95314e418deeca90a520c7b76540509062fbb2a629a83531c95314d41ab0e0a98a6a0c6f7654852506a639aa4292835a1c152149418f6e0b2864a0c7870594325063d380ca192831e5c0650c941968e2b2064a0e1d6414c32506a6b90a6192838b590520c941a9ae629064a0d4e754c832506a63aa64192832d1d1610c941ca8a6b0864a0e6452584325063dbb2a028283561cd5014141ad0e4a80a0a0c5f7654c5310726a9ac4298839654d6014c418deeca90a420e4d635485210734a92c0290831edc1654c8418f0e0b2a6420c7a70195321063cb80ca990832d5c4644c841c38c8a9a6420d4c7254d3210716322a499083531cd524c84196ae830a6420e55531853210732a90c29908393d95320c841c9aca9906420c3d76952411063abb4a9208838d5d76550441c6cedb2a8220d357598d411069bbaac6a088369dc96350441b48e4b1a8220db37058d41106d8382c6a0883a558c635044196ceda9a8220cb67614d411078aa98a6a0883699c85350441b4ae429a8220db27014d41106d8b80a6a08834d5d66250441a6eeab128220d977358941106ca39ac4a08836cdc16250441b60e0b128220ea562189411065b3b6a4a08832d9d85250441b2ce62928220d95731494110792a90a4a08836c9c05250441b62e02928220cb7764c9411065a3b264a08834d9d43250441a6aea1928220f85320c9411069abacc0a08834ddd56050441b2ee6b028220d947358141106d3b92c0a0883691c96050441d62c03028220cb776507501065bbb28228083a598d4114041d2ac6a08a020ea6625045010752b1282280831edd95014041cb2c6a80a020e69625405010798a0aa0280839598d61d533187eecaa0a998e566358454cc71b2a2c221e631bdd95214b31c3aa831a8398c7b7654050cc72ab1cc3aa4630fdd95415231caac7308a918e3554185438c637bb2a4294638795163106318f6eca80a118e2f64189544c727b18c4aa2639918b6155131cd6c5b02a898e6862d81544c71db20c0aa26396d8c6055131cd6c4302a898e6862181544c739b08c
  | 9 => 0xeeab028621d8f725814310ec6392c0a188765dc56050c43b28e2b028621e99601814310e4fbb287a908727dd943148438deeca90a421f0d435485210f4aa1cc229087a550d6114843ccaa4b08a421e99439805210f4ca1ac0290879a549601484393eeca1ea221c9f7650c5110f46a1cc428887a350d62144438eeeca88a221f15435445110f32b12a228887a650e6014443d3286b00a221e71515805110e4fbb287a808727dd94314043d1a87310a021e8d435885010f4aa1cc228087a550d61140438f6eca80a021f19435405010f34b12a0280879c58550140438beeca98a7a14777654451d0a3dbb2a02868517dd95314e428eeeca88a32147b765405090a2fbb2a629a85551c55314d42ab0e0a98a6a1477765445150aaa39aa228a855c1c151145428f6eca80a0a1558735405050ab838aa02828517dd95314c42caaa6b08a621659535805310a1ebb4a9210851b5da5490842c5aebb2a842162e76d954210a96bacc6a10854bdd56350842b4ee2b1a84215a47158d4210ad5b82c6a10856a1c16350842d1ac631a84214ae76d4d4210a573b0a6a1085c354c5350842b4ce229a84215a57114d4210ad5380a6a10856a5c05350842a5aeb30a842152f755854210ac7b9ac2a1085631cd6150842b56e0b0a84215a8705854210b52b08c2a10854b5d66050842a5eeab02842158f735814210ac639ac0a108569dc56050842b48e2b0284216a9601814210a57bb285a88852bdd94214442d1cc6a10a22168d635085110a3bbb2a2288859558d5114442e4a84a88a2216a9429805110b54a12c0288859c545601444295eeca16a0214af765085010b4731a8428085a358d4214042d4a85308a0216a5425845010a3dbb2a0280859658d5014042e5284a80a021671615405010b2731ac5aa6650fdd95415332c9cc6b10a99962e5458843ccb0eaa0c6a16651ddd951147328f6eca80a19964d6398b548ca1fbb2a82a4659358e6215232c5aa8312871961e5458c428ca3bbb2a228c651edd95014232c6ec830aa89965763185544cb33b10c2aa2659cd876055132ce0c3b02a89963b64181544cb2db18c0aa2659ad886055132ce6c2302a89967061181544ca1fbb2a82a2654d1c55415132a70e0aa0a89962c5458b434cb0e2a2c7a12651ddd95114532a68e8a88a29957070544514ca3dbb2a0282654e1d15014132ae0e2a80a09943f76550540cb1aaa2c22a0658e5516015032c6cc8b08a81965663584540cb33312c22a0659c9866015032ce2c3300a81963a64580540cb2d31ac02a0659a9896015032ce4c2b00a81967161580540cb16aa4c5218658755263908328baed29c641946d7694e320cb26baeca99065939db654c832a9aeb322641954f75591320cae3b8ac899065711c5644c832b96e0b2264195c870591320cb46b20c899065339d
  | 10 => 0x400000000000000001000000400800c00803c00000800800000005000400001400003800000801800000400c00400000801403007800803c00001c00000800400000400401800400002002400402400000000000800800400c03001c00400001c0000000000000000080000440000bc00004c00800000001c00803000400000000401c00803401800801c00000400c01000400001001800400c00000800000000000401400801800000000002400c01800800800400801000801405801000c02800000c00800002c00000800000000400000805000c00c00000802800c00400400000000400001401000800404400800006400000400001000000800801c00c00401000000800c01001406800004c00000003000c00001001000401801c01404000402c01800401000001000c00800400801002400005400000000400804800400002000800000400000800000001800000400403400400000000000400000800802400401000c00000002400000801000402800000800c03c00000c00000400000400400000800001c00000800005401800400001c00000400400400400000400c00800001000c00400001400c00000000802401000000000401001401402000002800400000000800001403000401c01000000000001400400400000000400800400001800400400402c05000001001000000000c00001c00000002c00000800000c01001002800800400000000403000000000000000001800400c00400400800800800800000c00001400401401000c00400800000400c00400003002401400400000001800000000400000001c00401800001000002400802003001000c00801400801801000000000001c00000000000000401800400400801000c00000801400002800406c01800404c00001c00401c00000c00801400000003001002c00800002800000001800001003400c03801000001401800000800000000800000c00c00002000000002c02c00c00400800000400003800000000000400000c01001400400000000000000800002800000001002800001800801400005400001c02000000400402400000400801403001c01c00401000000002000005802c01800001400000000000800000000000637bb2a4296871ddd951147438f6eca80a1a1c6f765485290e3bbb2a228c871edd950142438deeca90a4a1d64715485250eb4382a4292871ddd95114543ac8e4a88a2a1d70705445150e3dbb2a0282875a1c95014143ae0e2a80a0a1c3d769524310e2ebb4a921887875d76550c43c3cedb2a8621d1d759894310e8fbaac4a188765dc56250c43b28e2b128621d9b705894310ecc382c4a1887a35886250c43a3aeb30a8621d1f755854310ec7b92c2a1887631c96150c43b36e0b0a8621d98705854310f4ab08c2a1887475d66050c43a3
  | 11 => 0xefb330ca9adb3790a83b09e80011c95600026a0000003061fb0110e4901954a620eba0a8002928002e627680003fa800038fe89a00015a89004910980012a2e22ae09d1e48001690002f8b1d0000000001ab14c2138381f6829141ae48000000001761c00000000000002c62d40000002bd9db80000011d0002592b11ec0001fe8f99410000000ce80000020300000000030e0d50000000000000000cd2b09e5a269d50000002782628350000a13260000c480025880000017f91e8002988002728000000000000000000398002aa80034700000004a8af800000201ad81452b300000009a8000002598f00000002363539a2931a078000fa2cb80000024b2150001c401d8000b68000001a180719214592c0000000f180034e1c509b00202eaee0c70e58278bd2a40c927bad022880000014c800274ace98500013480000000000000017400023dac1354b1eadaa671391438c79461a71c32ab9a91249258fb144131005a6f9ae1d2b1c1cf2b9ac18b58588000000ab1c79a88a897f1b335180000014d85217307aa0f29d0602770be8000001d48000000000002e9ac40000000000000001300ef00029400000021fadf0000000ae0003342432bd036a1d2de0000003480000822132a800001e00013a30280033080030087d2a618e0000a90191dfa51b488c880000018e91e0003041179808000000000001cb0003230838000eb235800290132aa280000000000000023726f31e17280018f00011f95710119e80ea869600d013784e1212198002a30001598dc3540002511e80002320000000001b780005a0000d31b20002ad0000002a69d68002ce32b2be89996c2b61141f330a9ce10b26b00024208410c89f9722b39931da80024ca4c1c917804b9f800018816f00021a80000000031c8000b60000000001db00000035200023d0002f1800000000000164a528e62be075b498d22fa86d8000000002cd0000003069751ec998a2088e9278002f4ad3079000183aa925e000000305084a8d0001530000000d70010bf24b9670258000000000001d10002461e9268a4fb171d3a4e8000cb2348aa044b4509c87eaf798031a8aa8000000002d70f48000001bc8218000001668000003268a71528000000000000001f398d8558340000000003168130000000001f60000ee25e8ac8cc0198752fd82f34cb0c80000017d8001208002a98000000f38002638000000ae904a2c00033b8000201d200000000000006c8000001158003151bf00016a2521f91f10002408000000003280000000000000000001c1307942800279000185a89b14165a812550000002318a22bb0002c5acf1190001072e780000000004da5f8808000001aea818001e10bb0001a5000000c00000002800803000400001c00400001c05400000c00400003800004400400800000
  | 12 => 0xf9bd0d81b89848182ac2dc0a680027da7a80000000029700028e00000f00000000000024700000026800f8000a99251628ec2c30250f597b06083eb01800000143088b109512052162d792f00013300029fa9a1588f40001ed8cb800000227973885000a6680aacd83297907e248af51c71b52ec11d8001cfa2e21c000000000000072a3897000000026190c32e02ca0103a21b00000000000020080027fb290b51a380ca0902c1d99e688f91a22a82a8002060000000000001491afa6c8000090000000000001272aa0178001af0000000000000000000003240269f58000001100d11242181788000780001501202ef30b2ea0440ea1cb80018ba8b8100002228001ce8978388e50833020000000000000000001818768000a8121a4186999c2331bc1508000000000000001dc9c98c380a00026e8000000bb9ef174ac79ba80000000017d22d0000cf8002b69642798000e7a21176840b410c180000000000009123e80022380000000000025d00024d000161a4d9c200022c80000004f8000000b72f380000017180000025680029a80000029680033c00005080000000000000000034f86ab251be80000033c93a8000000000002f725c0000000000000709558000000000000001901e1a3c0000003478001591811b680019130f94214e9568000000dd00006f8001b10000de80007f8349ffa3e00027100000025a2e28000002e680034a8208000000000000000d18b983f33485b3148000000000002ec9d08bda9f27e023a312378000000619309408002fc1b598a90eb393441c199b0a590409b8000000000003118000000000003432c8ae000000033e9b92248000cf0000000003098001d9056195a608000000000000000000000002bb94a80009c06496600015d23800000000000016e1351a080034a30a0b80a18001eb126a0d83390b80015f00026917101c0000001c48000000001e080000000009383700000033980029123c8b39260622a8b228a386308000420e148b0f0761f28001679078001320a0800029ac92eb8002eb0000002bf218abc8000000580dbb088002601d7a648629bb02b8551998240000000000001088000f30000fbb3225a81700000034b80032ab3a25b871ae0ab5b33ac09080d92d8b2a028873882a2f0f70c10643113238ed15c95400015e818990b001dd2260000000002ba84800000000000000000000019780000022b9360001fca88a2e8002e7312b13b3d2a22038ce1ca2df95797e0e9867a5d99e0991f021491f345af9a2b1d82040002718e286d234192a9b19a00000029d80008d80016511b06e00016c8002fbb3b000177ab001d00000015f8000000000000000002b18002700002980000001fab1989e17c00003bae590610d80b00000017b8770a420c09310a1950000d68db0003448000c028a9
  | 13 => 0x2afa8f0000000000ff2ff8001d880000002d8000001518001d026c11333614d1bf80000001a1aa04010300027509631f2170002bc1dd80020002d191902a8f8c300004f0002759161f98f095b8000940710bc9638000002ba0590002a50001e40001499470000a000000000000000005d00032c12d9dc0d0ac980000000009520f9f221e0001e52350958fc162291969a53253843b161fe230031a102f32d5911304a21b2002813d0e18e82adb2bb3532d1ee22f8000138af03d97a00000007b8002820ad81f2088002f610f0001f080000007b0002478b2aa194784b194182a8e80008ca3f1ba33a83d0410b033d8140df0ed85bb3e33f0b231b1e88ca1b827c00000021680d00024a1772fe0000000000000ad0000f8285284327a998002dd80034c2cc80830d8300003418000b41ee80000027a00016880025099d00001aaa5b4f2258569eb8001fd913b0d32f32180000000018c23b93d83e0420d60000002290001e63318001972d900000018786ead6a6e34b3071c834d2fc846a9c3509f18000001e00000000000001cc00000024e2f593e1758e73258000000000000379b3a70a7222200033f8000001ff2732e92b82e88000000000000000001de03c2d0800000051acb00000000000780000005a80000000012e80023f80e1b980000010680000000000021287a11a9d582e0e413400012998f87ca0b24689220c9822cc2a78220361bbac20000ff9050720908dcad100006894f2308018c81e70b88fe21daf132f92b2642280001e2a329400c6a838000428321c5a9500032c80000031a0538fd8000001cab512948da1ac80000000020b865000000000000000155278b490002558d4aa11bd84cb4008108b320a121468002a09520c0a450970c500023a00019f3221a40000000e68000000002830000002658000000000e300000028c00000005e8000000000000c61eaa8590f98425c8000f204c00000000000000001606688680000023b2080002cfa4480012e1968000000000001cd0e90001ad0cda8d9d63178002f21f79de80000027f0000002070151c393b9f70672ef8002fe85da1ea2413b1b28b310901b0001d73500002958000002d4a3981cad18000002392a700000020485c00020a1118870000000000e09a59a100012baa026796080000c00b8000000000000000690118001b480000000000000000000015b1708878d4313059adb800229800000000043000336a020000ab8000000001381fa00031b80000008934205e2fb284857078a3a8bf9680d58000000001fbaa3800000153800033163000074b030000001da0dd92d00032d8880e107da8602b1980a79832db28b1cd8b180006bad20000002252f69a6b012140f91151288502da12384a0462920488000002068002650001370002de9a98ec8062c4add12
  | 14 => 0x13f000000000343a5480000029b99d96e8b780009284793380010d1ccb1006b0740fa8f51861b030595e1a780025b07300000008a0000000231f8800000144ac513c800000000100a6980003aa8c8981230002d9b1893e8001c68c200000000007780031200000006c1ed00021cac2b380000000002f91f401693593688c01f8000002960001e788d0000000000000000a315a00000000027b0000000000000a600000000000000000000515c0003428002b7a562b48000000000000002d50001e20000002dc8002501e313c33004724801200008582f800000000000000000290905a82989aca961205b1924f1a02c008991981496b8529be0000089892c6afa31f9948000001d1b40a118c98d2a6aa17a1f20d2c38000e00000002ae80018a0000000000d980000018d0000000a50000000000000fd00000002a186ac708600000000000020280000030b80010391095d8512e386607c31d979b2485f068000000000000000000000000000193809a6626d81e80000000014e00000000016f8000001aa8d78a28000000001df0000b10001e380006f0000000000000000efb4695808bb0c0c28002438000000002490002b900034da760de00000000000016b00016d8000000000000068c5800112236a099b62880003310000000000000f68000128000000000000002578002fd2ed21bab72ff0d3824a778b0a9e89f0948260000818001c280019f80000000033288f0002f080028792a80029300000025f0000c424280016d0df80000029e00008e2e812c8bc2af0e20002e409d84d00027d2742978028f628a2e51228000002a48530309182d39fc1990002b20be05f94b9291ea0000001148000578000498000000001220419d32b88000000d897eb182e19b402735327ea4000011b8003080000000002e333880020eaeea410cc80000000000000000000034e8001a300000000000000014a0002d29ab9b721a2bfa459482e10000000049d427380000017a80035291700000029caf29ac07013f854112b2899c89180006122a0000000000ea80000028722011c26d0000000b92f42890002270000000000000000000000000000000000001280000000001b0a9900009880003122318880000000027c90e00013880022d8000000001f4a158f124408a8e88000f7af000019b94b1c09a20001870fc8003091c88000000000002b50000000000548450000000000e3a190da8bab46000337000063af814f84e80016ab0e8000000000000000000a480000004580000007980024a80d8002c80002583038001b189697caed916a498ee9a82d6211233a938b48000002b28002ab1e98000f880025700003918b21087f0003271a6065a5419a800021100035b15803335a6b86a280ab42ea85caca139b2e83cb2998c8000002610ac1a4902000263
  | 15 => 0x1fd01b8ba2ac8108001c63210000159f50000001961188f28228000
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xc6350842d05535c45350842d09535c05350842a84835846150842aa0805846150842a88835806050842aa0815806050842e05635095114442e21425456014442e09635095014042e21425855014042a8481590644c832a8880590644c832d05545c4544c832d09545c0544c832a8484584614c832ac080584614c832a8884580604c832ac081580604c832e05644c95114432e41325456014432e09644c95014032e41325855014032a848258c6350441a908058c6350441d05535c85350441d11535c05350441a84835886250441aa0805886250441d05735485250441d21525c05250441a84864c83250441d05754c83250441a90835806050441aa0825806050441e11635055014041e21625055014041a8482590644c431a9080590644c431d05545c8544c431d11545c0544c431a8484588624c431ac080588624c431d0574548524c431d41525c0524c431a8486508424c431d0575508424c431a9084580604c431ac082580604c431e11644c55014031e41624c55014031a84835906448421aa0805906448421d05545cc5448421d21545c05448421a848458c6348421ac08058c6348421d057454c5348421d41535c05348421a848650c4348421d057550c4348421aa0845806048421ac0835806048421e21644855014021e41634855014021a888258c6350040a908158c6350040d09535c85350040d11535c45350040a88835886250040aa0815886250040d09735485250040d21525c45250040a88864c83250040d09754c83250040a90835846150040aa0825846150040d11735445150040d21725445150040a90864c43150040d11754c43150040aa0864842150040d21754842150040a8882590644c030a9081590644c030d09545c8544c030d11545c4544c030a8884588624c030ac081588624c030d0974548524c030d41525c4524c030a8886508424c030d0975508424c030a9084584614c030ac082584614c030d1174544514c030d4172544514c030a9086504414c030d1175504414c030ac086484214c030d4175484214c030a88835906448020aa0815906448020d09545cc5448020d21545c45448020a888458c6348020ac08158c6348020d097454c5348020d41535c45348020a888650c4348020d097550c4348020aa0845846148020ac0835846148020d21745445148020d41735445148020aa0865044148020d21755044148020ac0864c43148020d41754c43148020a90835906444010aa0825906444010d11545cc5444010d21545c85444010a908458c6344010ac08258c6344010d117454c5344010d41535c85344010a908650c4344010d117550c4344010aa0845886244010ac0835886244010d21745485244010d41735485244010aa0865084244010d21755084244010ac0864c83244010d41754c83244010
  | 1 => 0x94ee6b15a50180035220424a32818340a2c000c22d0e800644f3f00000851780000000000000002b000300000244000200178c4000011800003984c008b219b42c360000000004983c3c864382000000012c62282882c7007001d5042711234004802080d211001e8f62400240ae84209bc9c3a3880cfa550c980123d1a964ce0d4723c8a2a00000007600000b61700190a06c0000000004922800000e168ba003c80052001700098121f9f0581f2101466490005000003f800007200000e0343a04080544a80118000003800010a80000891e1347c83299e0dc23330c0c6520000102001b91c0000340ec885f0d80000802e0e44c000005030900000703050000030003000501050202020a01000000010f080100020801040502050205010b06050802010102a84815886250c43a88805886250c43a84825846150c43a90805846150c43a88825806050c43a90815806050c43e05435496114843e09435496014843e05435895114443e11435456014443e09435895014043e11435855014043a848158c6350842a888058
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x2c01cae519a9010620016040020249804865d5320c9411070090cbaa842126218e012197550c4348421c04432ea99064a0081810865d5310c5401030410cbaa4210a802060221975508424c030c08432eaa088298061840865d521085300c30110cbaa8621a4010608219755044148020c20432ea9886290041810865d54310d100430410cbaa842122008610219754c83244010
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 40
  | 6 => 1710
  | 5 => 5751
  | 4 => 1706
  | 3 => 150
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
  | 7 => packedAt gbK7 (744+((h/13+packedAt gbK7 (640+(h % 13)*8) 8) % 247)*7) 7
  | 6 => packedAt gbK6 (53010+((h/570+packedAt gbK6 (46170+(h % 570)*12) 12) % 3634)*12) 12
  | 5 => packedAt gbK5 (243459+((h/1917+packedAt gbK5 (218538+(h % 1917)*13) 13) % 6902)*14) 14
  | 4 => packedAt gbK4 (90410+((h/568+packedAt gbK4 (83594+(h % 568)*12) 12) % 2724)*12) 12
  | 3 => packedAt gbK3 (9400+((h/50+packedAt gbK3 (9000+(h % 50)*8) 8) % 218)*9) 9
  | 2 => packedAt gbK2 (1090+((h/5+packedAt gbK2 (1065+(h % 5)*5) 5) % 19)*5) 5
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xff80ffffc07ffffc0fc7e3fe3ffc7fc0e3f1ff
  | 1 => 0x7ff01ffff80fffff007fc7fc7ff8fc71c7e3f
  | 2 => 0x7fffe03ffff01fffff8007ff8fff1f81f8fc7
  | 3 => 0xf8000003fffffe03ffffff8000fffe3fe00ff8
  | 4 => 0xfffffffc00000003ffffffffff00003ffff000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x30a614284712244802c16096092c124061b0db
  | 1 => 0x510a4c50890e4890b002a42a425484830c562d
  | 2 => 0xa214289912241d215548004c90992118168b46
  | 3 => 0xc058b1622448903a6994c90000e2482da00db0
  | 4 => 0x460c1803870e1c38e27127124000036db6000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 31 gbPos gbNeg, 0xfee8e880fee8e880fee8e880fee8e880fee8e880fee8e880fee8e880fee8e880fee8e880fee8e880fee8e880fee8e880fee8e880fee8e880fee8e880fee8e880, gbN, gbR, (fun _ _ => 0), gbI⟩
end PEqualNP.Outside.L_meta_12343
namespace PEqualNP.Outside.L_meta_12343
open PEqualNP.Outside.L_meta_12343.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bgb_3_128 : Interval gbAtlas 3 128 22 := block_range (n:=22) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 150 := (concat (concat bgb_3_0 bgb_3_32) (concat bgb_3_64 (concat bgb_3_96 bgb_3_128)))
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
theorem bgb_4_1696 : Interval gbAtlas 4 1696 10 := block_range (n:=10) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 1706 := (concat (concat (concat (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat bgb_4_96 (concat bgb_4_128 bgb_4_160))) (concat (concat bgb_4_192 (concat bgb_4_224 bgb_4_256)) (concat (concat bgb_4_288 bgb_4_320) (concat bgb_4_352 bgb_4_384)))) (concat (concat (concat bgb_4_416 (concat bgb_4_448 bgb_4_480)) (concat (concat bgb_4_512 bgb_4_544) (concat bgb_4_576 bgb_4_608))) (concat (concat bgb_4_640 (concat bgb_4_672 bgb_4_704)) (concat (concat bgb_4_736 bgb_4_768) (concat bgb_4_800 bgb_4_832))))) (concat (concat (concat (concat bgb_4_864 (concat bgb_4_896 bgb_4_928)) (concat bgb_4_960 (concat bgb_4_992 bgb_4_1024))) (concat (concat bgb_4_1056 (concat bgb_4_1088 bgb_4_1120)) (concat (concat bgb_4_1152 bgb_4_1184) (concat bgb_4_1216 bgb_4_1248)))) (concat (concat (concat bgb_4_1280 (concat bgb_4_1312 bgb_4_1344)) (concat (concat bgb_4_1376 bgb_4_1408) (concat bgb_4_1440 bgb_4_1472))) (concat (concat bgb_4_1504 (concat bgb_4_1536 bgb_4_1568)) (concat (concat bgb_4_1600 bgb_4_1632) (concat bgb_4_1664 bgb_4_1696))))))
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
theorem bgb_5_5728 : Interval gbAtlas 5 5728 23 := block_range (n:=23) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 5751 := (concat (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 (concat bgb_5_192 bgb_5_224)) (concat bgb_5_256 (concat bgb_5_288 bgb_5_320)))) (concat (concat (concat bgb_5_352 bgb_5_384) (concat bgb_5_416 (concat bgb_5_448 bgb_5_480))) (concat (concat bgb_5_512 (concat bgb_5_544 bgb_5_576)) (concat bgb_5_608 (concat bgb_5_640 bgb_5_672))))) (concat (concat (concat (concat bgb_5_704 bgb_5_736) (concat bgb_5_768 (concat bgb_5_800 bgb_5_832))) (concat (concat bgb_5_864 (concat bgb_5_896 bgb_5_928)) (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024)))) (concat (concat (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120)) (concat bgb_5_1152 (concat bgb_5_1184 bgb_5_1216))) (concat (concat bgb_5_1248 (concat bgb_5_1280 bgb_5_1312)) (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408)))))) (concat (concat (concat (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 (concat bgb_5_1536 bgb_5_1568))) (concat (concat bgb_5_1600 (concat bgb_5_1632 bgb_5_1664)) (concat bgb_5_1696 (concat bgb_5_1728 bgb_5_1760)))) (concat (concat (concat bgb_5_1792 bgb_5_1824) (concat bgb_5_1856 (concat bgb_5_1888 bgb_5_1920))) (concat (concat bgb_5_1952 (concat bgb_5_1984 bgb_5_2016)) (concat bgb_5_2048 (concat bgb_5_2080 bgb_5_2112))))) (concat (concat (concat (concat bgb_5_2144 bgb_5_2176) (concat bgb_5_2208 (concat bgb_5_2240 bgb_5_2272))) (concat (concat bgb_5_2304 (concat bgb_5_2336 bgb_5_2368)) (concat bgb_5_2400 (concat bgb_5_2432 bgb_5_2464)))) (concat (concat (concat bgb_5_2496 (concat bgb_5_2528 bgb_5_2560)) (concat bgb_5_2592 (concat bgb_5_2624 bgb_5_2656))) (concat (concat bgb_5_2688 (concat bgb_5_2720 bgb_5_2752)) (concat bgb_5_2784 (concat bgb_5_2816 bgb_5_2848))))))) (concat (concat (concat (concat (concat (concat bgb_5_2880 bgb_5_2912) (concat bgb_5_2944 (concat bgb_5_2976 bgb_5_3008))) (concat (concat bgb_5_3040 (concat bgb_5_3072 bgb_5_3104)) (concat bgb_5_3136 (concat bgb_5_3168 bgb_5_3200)))) (concat (concat (concat bgb_5_3232 bgb_5_3264) (concat bgb_5_3296 (concat bgb_5_3328 bgb_5_3360))) (concat (concat bgb_5_3392 (concat bgb_5_3424 bgb_5_3456)) (concat bgb_5_3488 (concat bgb_5_3520 bgb_5_3552))))) (concat (concat (concat (concat bgb_5_3584 bgb_5_3616) (concat bgb_5_3648 (concat bgb_5_3680 bgb_5_3712))) (concat (concat bgb_5_3744 (concat bgb_5_3776 bgb_5_3808)) (concat bgb_5_3840 (concat bgb_5_3872 bgb_5_3904)))) (concat (concat (concat bgb_5_3936 (concat bgb_5_3968 bgb_5_4000)) (concat bgb_5_4032 (concat bgb_5_4064 bgb_5_4096))) (concat (concat bgb_5_4128 (concat bgb_5_4160 bgb_5_4192)) (concat bgb_5_4224 (concat bgb_5_4256 bgb_5_4288)))))) (concat (concat (concat (concat (concat bgb_5_4320 bgb_5_4352) (concat bgb_5_4384 (concat bgb_5_4416 bgb_5_4448))) (concat (concat bgb_5_4480 (concat bgb_5_4512 bgb_5_4544)) (concat bgb_5_4576 (concat bgb_5_4608 bgb_5_4640)))) (concat (concat (concat bgb_5_4672 bgb_5_4704) (concat bgb_5_4736 (concat bgb_5_4768 bgb_5_4800))) (concat (concat bgb_5_4832 (concat bgb_5_4864 bgb_5_4896)) (concat bgb_5_4928 (concat bgb_5_4960 bgb_5_4992))))) (concat (concat (concat (concat bgb_5_5024 bgb_5_5056) (concat bgb_5_5088 (concat bgb_5_5120 bgb_5_5152))) (concat (concat bgb_5_5184 (concat bgb_5_5216 bgb_5_5248)) (concat bgb_5_5280 (concat bgb_5_5312 bgb_5_5344)))) (concat (concat (concat bgb_5_5376 (concat bgb_5_5408 bgb_5_5440)) (concat bgb_5_5472 (concat bgb_5_5504 bgb_5_5536))) (concat (concat bgb_5_5568 (concat bgb_5_5600 bgb_5_5632)) (concat bgb_5_5664 (concat bgb_5_5696 bgb_5_5728))))))))
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
theorem bgb_6_1696 : Interval gbAtlas 6 1696 14 := block_range (n:=14) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1710 := (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 bgb_6_384)))) (concat (concat (concat bgb_6_416 (concat bgb_6_448 bgb_6_480)) (concat (concat bgb_6_512 bgb_6_544) (concat bgb_6_576 bgb_6_608))) (concat (concat bgb_6_640 (concat bgb_6_672 bgb_6_704)) (concat (concat bgb_6_736 bgb_6_768) (concat bgb_6_800 bgb_6_832))))) (concat (concat (concat (concat bgb_6_864 (concat bgb_6_896 bgb_6_928)) (concat bgb_6_960 (concat bgb_6_992 bgb_6_1024))) (concat (concat bgb_6_1056 (concat bgb_6_1088 bgb_6_1120)) (concat (concat bgb_6_1152 bgb_6_1184) (concat bgb_6_1216 bgb_6_1248)))) (concat (concat (concat bgb_6_1280 (concat bgb_6_1312 bgb_6_1344)) (concat (concat bgb_6_1376 bgb_6_1408) (concat bgb_6_1440 bgb_6_1472))) (concat (concat bgb_6_1504 (concat bgb_6_1536 bgb_6_1568)) (concat (concat bgb_6_1600 bgb_6_1632) (concat bgb_6_1664 bgb_6_1696))))))
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
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 5 zero,inputs.getD 4 zero]
def fullWord : Sig := 0xfee8fee8fee8e880fee8fee8fee8e880fee8fee8fee8e880fee8fee8fee8e880fee8fee8fee8e880fee8fee8fee8e880fee8fee8fee8e880fee8fee8fee8e880
theorem fullBound (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have low := boundgb certgb
  have lift := lift_ok (u:=true) (ms:=fixRows 32 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 5 zero,3,35)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 5 zero,3,35)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276682472 * 2 ^ 32 + 4276676736) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_12343.Model.Repr at out
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

def mono : List Gate := [⟨.and,[2,3]⟩,⟨.or,[4,5]⟩,⟨.or,[2,3]⟩,⟨.or,[0,1]⟩,⟨.and,[8,9]⟩,⟨.or,[7,10]⟩,⟨.and,[0,1]⟩,⟨.or,[6,12]⟩,⟨.and,[7,10]⟩,⟨.or,[13,14]⟩,⟨.and,[11,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276682472 * 2 ^ 32 + 4276676736) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276682472 * 2 ^ 32 + 4276676736) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_12343

open PEqualNP.Outside.L_meta_12343 in
theorem PEqualNP.Outside.L_meta_12343 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276682472 * 2 ^ 32 + 4276676736) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276682472 * 2 ^ 32 + 4276676736) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound allgb)
