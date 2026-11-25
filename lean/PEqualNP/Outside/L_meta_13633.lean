import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_13633.Model
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


end PEqualNP.Outside.L_meta_13633.Model

namespace PEqualNP.Outside.L_meta_13633
open PEqualNP.Outside.L_meta_13633.Model
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

def SBf (j : Nat) : Nat := [5, 2, 6, 6, 6, 6].getD j 0

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

end PEqualNP.Outside.L_meta_13633

namespace PEqualNP.Outside.L_meta_13633
open PEqualNP.Outside.L_meta_13633.Model
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
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0x7fff00ffffffffc03fff80fffffff807f8ffc7
  | 3 => 0xffffff00ff807fffffffff01fc03ffffff18ff
  | 4 => 0x83ffffff00007fffc03ffffe0003fff80fe0f8
  | 5 => 0x3ffffffffff8000003ffffffffc00000fff00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x104b092124851444848a8b162d545b4a936b5b
  | 2 => 0xa095d84a4d4a28a3a915c0ab569aa8c5a8b5c5
  | 3 => 0x412652e88a534d293227558198c335974d18ae
  | 4 => 0x76389c8cec6c723223b9e6cd0313c6e18ee0f0
  | 5 => 0x7bc0e0f0f0707c3c3c3e78f1e3e207060fde00
  | _ => 0
def s0Atlas : Atlas := ⟨4,rawDecor 62 s0Pos s0Neg, 0xccc0c0c0cc00c000ccc0c0c0cc00c000ccc0c0c0cc00c000ccc0c0c0cc00c000ccc0c0c0cc00c000ccc0c0c0cc00c000ccc0c0c0cc00c000ccc0c0c0cc00c000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_13633
namespace PEqualNP.Outside.L_meta_13633
open PEqualNP.Outside.L_meta_13633.Model
def s1K1 : Nat → Nat
  | 0 => 0x7
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 1 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 1 => packedAt s1K1 (i*3) 3
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 1 => packedAt s1K1 (4+((h/1+packedAt s1K1 (3+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 4 => 0xffffffffffffffffffffffffffffffffffde73
  | 5 => 0x6f9c
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffff8205
  | 4 => 0x2552
  | 5 => 0x1958
  | _ => 0
def s1Atlas : Atlas := ⟨1,rawDecor 49 s1Pos s1Neg, 0xaaaaaaaaaaaa0000aaaaaaaaaaaa0000aaaaaaaaaaaa0000aaaaaaaaaaaa0000aaaaaaaaaaaa0000aaaaaaaaaaaa0000aaaaaaaaaaaa0000aaaaaaaaaaaa0000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_13633
namespace PEqualNP.Outside.L_meta_13633
open PEqualNP.Outside.L_meta_13633.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x80398054a16112860304bf43bd43ef32ec32bf41bd41ee21ec21be40bc40ef20ed20
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x5004e02244000d06008026aa3a1d994732c6a18651d53d069ca710e9504218ea9881355110298a6905914520
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 10
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
  | 4 => packedAt s2K4 (208+((h/4+packedAt s2K4 (192+(h % 4)*4) 4) % 15)*5) 5
  | 3 => packedAt s2K3 (282+((h/3+packedAt s2K3 (270+(h % 3)*4) 4) % 14)*5) 5
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffff83ffffffe07ffffffff03fffff1ff1ff
  | 1 => 0x83f03ffc1f83ffff870783e0ffc3c1ffea4e4f
  | 3 => 0xfc003fffe003e0fff807fc00fffc01e0f38f8c
  | 4 => 0x3ffffffc00fffff80000fffffe00fc0ff0
  | 5 => 0xffffc000000000ffffffffff00000000fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x80200088010000000808842210044422009095
  | 1 => 0x28c65910ca255865834323446642895c6a464a
  | 3 => 0x196aaa29474a89aab885e90abaa81586b38b8c
  | 4 => 0x528d34429460d2d355d04210cd333808dc0d60
  | 5 => 0x630e387318731cfc66e6739c0e222110ff6000
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeaaaaaaeeaa8888eeaaaaaaeeaa8888eeaaaaaaeeaa8888eeaaaaaaeeaa8888eeaaaaaaeeaa8888eeaaaaaaeeaa8888eeaaaaaaeeaa8888eeaaaaaaeeaa8888, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_13633
namespace PEqualNP.Outside.L_meta_13633
open PEqualNP.Outside.L_meta_13633.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x1200040402d0551cc000c400404de43dd43ef42ec42df31dd31ee21ec21de30dc30ef20ed20
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0xc29400c201c850005eaaa321d994742c6a18851d54cc65ca910f14c4218eaa06155510c258a8905914520
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 10
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (i*5) 5
  | 4 => packedAt s3K4 (i*16) 16
  | 3 => packedAt s3K3 (i*27) 27
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (6+((h/1+packedAt s3K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s3K4 (212+((h/4+packedAt s3K4 (192+(h % 4)*5) 5) % 17)*5) 5
  | 3 => packedAt s3K3 (282+((h/3+packedAt s3K3 (270+(h % 3)*4) 4) % 13)*5) 5
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xc1ffffffffffffe07fff81ffffffffff1c7fff
  | 1 => 0xfe0fc1f83f03ffff8707fe1e0f07c1ffeb924f
  | 2 => 0xfff001ffc003e0fff807ffe00ff801e0f3e38c
  | 4 => 0x1fffffc00fffff800000ffffe00fc03f0
  | 5 => 0xfffffe00000000fffffffffff0000000fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x44008008020000000808802221084422002495
  | 1 => 0x88a312919455546583432a144646895c69924a
  | 2 => 0x1465a5228e9a85aab885cd40abd21586b2e38c
  | 4 => 0x394a39c528d0d6f355d069110ce73908fc0360
  | 5 => 0x218c318630e318dc66e67199c0842010df5800
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xeaeaeaeaaaaa8888eaeaeaeaaaaa8888eaeaeaeaaaaa8888eaeaeaeaaaaa8888eaeaeaeaaaaa8888eaeaeaeaaaaa8888eaeaeaeaaaaa8888eaeaeaeaaaaa8888, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_13633
namespace PEqualNP.Outside.L_meta_13633
open PEqualNP.Outside.L_meta_13633.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x1010034880b500e0414c2032de43dd43de32dc32de31dc31ee21ec21df30dd30ef20ed20
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0xb0020a6292871d540c63aa9985914520
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 4
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (i*5) 5
  | 4 => packedAt s4K4 (i*16) 16
  | 3 => packedAt s4K3 (i*27) 27
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (6+((h/1+packedAt s4K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s4K4 (208+((h/4+packedAt s4K4 (192+(h % 4)*4) 4) % 16)*5) 5
  | 3 => packedAt s4K3 (111+((h/1+packedAt s4K3 (108+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x7fffffc0fffff03ffff83ffffc0fffe7c7e3f
  | 1 => 0xf81fc0fffffffffc1e07fc1e07ffffff9393ff
  | 2 => 0xffe000fff03f07ffe007ffe007ff0781e3e3cc
  | 3 => 0xffffc007fffff8000007fff801fc03f0
  | 5 => 0xffffff00000007fffffffffff8000001fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x1082880460822100622880a231484c94242615
  | 1 => 0x224511488514822c0c832414429191689190ea
  | 2 => 0x5149aa9123a82d55a125cac094ea460d62e34c
  | 3 => 0xe5963ce24a0eb79ad7b06291273ce431fc03b0
  | 5 => 0x861830c38c30c6e319c67319c0308041db5800
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xeaeaeaeac888c888eaeaeaeac888c888eaeaeaeac888c888eaeaeaeac888c888eaeaeaeac888c888eaeaeaeac888c888eaeaeaeac888c888eaeaeaeac888c888, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_13633
namespace PEqualNP.Outside.L_meta_13633
open PEqualNP.Outside.L_meta_13633.Model
def s5K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x6000e82a841010035a406310ee42ed42ef32ec32de31dc31ee21ec21df30dd30ef20ed20
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x990a629a852d54086a8a2984b55320
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 4
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s5K5 (i*5) 5
  | 4 => packedAt s5K4 (i*16) 16
  | 3 => packedAt s5K3 (i*27) 27
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s5K5 (6+((h/1+packedAt s5K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s5K4 (208+((h/4+packedAt s5K4 (192+(h % 4)*4) 4) % 16)*5) 5
  | 3 => packedAt s5K3 (111+((h/1+packedAt s5K3 (108+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfffffffc0fffff03fe0fffffffc0fffe63fe3f
  | 1 => 0xf81fc0fffffffffc1ff0781e07ffffff9c93ff
  | 2 => 0xffe000fff03f07ffe0007fe007ff0f81e0e3cc
  | 3 => 0xffffc007ffffff800007fff001ff03f0
  | 4 => 0xffffff00000007fffffffffff8000001fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x4882880460822100620288a231489494212615
  | 1 => 0x124511488514822c0c903214429129688c90ea
  | 2 => 0x6149bad123a8af55a18a5ed094fa8e0de0e34c
  | 3 => 0x45962ca24a0e359ad72b0481272cc4317703b0
  | 4 => 0x861830c38c30c6e319cc6719c0300841dad800
  | _ => 0
def s5Atlas : Atlas := ⟨5,rawDecor 31 s5Pos s5Neg, 0xeeaac888eeaac888eeaac888eeaac888eeaac888eeaac888eeaac888eeaac888eeaac888eeaac888eeaac888eeaac888eeaac888eeaac888eeaac888eeaac888, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_13633
namespace PEqualNP.Outside.L_meta_13633
open PEqualNP.Outside.L_meta_13633.Model
def gbK8 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0xd05042000001c958a9c09800003879490a0989a951f0080119383162105801e8002100f1692888000019b92111786860e001d000b18028d9701001f891d800b880f801b07000a19048c9a21998e9e140c1306860c04a0010000840014580001c48000e4080027fd5007fe54007f55007fc54027fd4c05fe53007f54c05fc5301ffd0c05fe43007f50c05fc43027fd4803fe52007f54803fc5201ffd0803fe42007f50803fc42017fcc803fe32007f4c803fc32027fd4401fe51007f54409fc5101ffd0401fe41007f50407fc41017fcc401fe3100778c401fd31017f0c401dc3100ffc8401fe21007b88401fd2100ff08401ec21027fd4001fe50007f54009fc5001ffd0001fe40007f50007fc40017fcc001df30007f8c001fd3000774c005fc3000ffc8001ef20007f88001fd20007b48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x2a4000db19520007dec89001fee6448001f6b224007fb19120047dea89001fee5448001f6aa24007fb15120007dec69001bee6348001f6b1a4006fb18d20047dea69001bee5348001f6a9a4006fb14d2003fde869001bee4348001f6a1a4006fb10d20007dec290003ee6148001f6b0a4000fb18520005d8c290023ef5148001f728a4000fb54520047d8a29001fef4148001f720a4000fb5052003fd8829001bef3148001f718a4000f38c520007da629001bec3148001e618a4001fbd812000ddec090007eb6048011f7a824005fb94120007daa090017ec504800ff7a024005fb90120007da8090017ec404800df79824000f3cc12002fdc6090003ed3048001e69824005fb0c120005fecb88012fe65c40017eb2e2004bf19710005fec98800efe64c40017eb262003bf19310005fec788003df63c40016fb1e2002bf98f10005fac78800afc63c4001ee31e2002b718f10005fec588003ef62c400177b162001bf98b10005fac588006fc62c4001f63162001bb18b10007eca388003f551c4001fb20e2000fd50710007bc6388003dc31c4001f710e2000fb08710007be6188003dd30c4001f79062000fb4831002dfecb08012fe65840017eb2c2005bf1961002dfec90800efe64840017eb242005bf1921002dfec70800afe638400bef31c2002b798e10005fac708017dd63840016eb1c2005bf18e1002dfec508006fe628400bf73142001bb98a10005fac508017ed628400176b142005bf18a10005fac308003de3184001ee18c2000fb88610007d84308016fe608400bef9842005f74c21002fde4108017ed208400bfb8842000fec4210005feca880037f65440013fb2a2004bf99510005faca88012fc6544001be32a20049f19510005fec888003bf64440015fb222003bf99110005fac88800efc6444001de3222003af19110005fec688003df63440016fb1a2002bf98d10005fac68800afc6344001ee31a2002b718d10005fec488003ef624400177b122001bf98910005fac488006fc6244001f63122001bb18910007eca288003f55144001fb20a2000fd50510007bc6288003dc3144001f710a2000fb08510007be6088003dd3044001f79022000fb48110007f62088017f6104400b7fb282004bf9941002efcca080127e65040017eb282005df59410004faca08016fc650400b7fb202003bf9901002f7cc80800ebe64040017eb202005ef590100057ac808016fc640400b7fb182002bf98c1002fbcc60800ade63040017eb182005f758c10005bac608016fc630400b7fb102001bf9881002fdcc408006ee62040017eb102005fb58810005dac408016fc62040017f3082000f78c410007b86208003ee2104001f61082005bf9801002fbe6008017dd300400bf79002005fb4801002fee2008017fa100400bfa8802000fe44010
  | 1 => 0x3dd534c005ee29a600df7d0d30017bc8698003dd434c005ee21a6000bfd893000dfcc498006fc624c005ef992600cf78c930007ba649800bdc324c0017fb0a6000bf18530017be6298003de314c001ee98a6002f70c530007dc4298003ec214c0057fb026002fecc13002fbc6098017dc304c005fc1826000f7d9530077bcca98003dd654c01dee32a6000f7d91300073ec898037de644c001eeb22600df71913000738c89803bdf544c01bef2a26000f75513006fb8a898003df624c019ef3126000f758930067b8c49803bdf524c019ef2926000f754930067b8a498037df424c019ef2126000f750930067b88498003df614c001ef30a6000f758530007b8c298002dc614c01defa8a6000f794530007baa29803bdc514c01befa0a6000f790530007ba8298037dc414c019ef90a6000f7885300079c4298003dd214c019ee10a6000f308530017bec09800adf604c005edb02600ef7d413002fbca098003dd504c00bee282600df7d013002fbc8098003dd404c00bee202600cf7c813002fb84098007ef65c8003f732e4001fb5972000fd8cb90007ef64c8003f73264001eb9932000fdac990007ad64c8003f6326400bfbd5320057dca990003ed54c8015f62a64001fbd8f2000fdcc790007ed63c8003f631e400bfbd4f2004fdca790003ed53c8013f629e400afbd0f2004fdc8790003ed43c8013f621e4001fbd872000fdcc390002ee61c8003f6b0e4001fb1872005fdea390003ee51c8001f6a8e400bfb14720057de8390003ee41c8001f6a0e400afb1072004fde6390003ee31c8001e718e4000fb4c72004fd86390003cc31c8017f7a864005fb94320007daa190017ec50c8015f7a064005fb90320007da8190017ec40c8013f79864000f3cc32002fdc6190003ed30c8001e69864005fb0c32002dfecb10012fe65880017eb2c4005bf1962002dfec91000efe64880017eb244005bf1922002dfec71000afe638800bef31c4002b798e20005fac710017dd63880016eb1c4005bf18e2000dfac510002ed62880017f30c4000bf58620007bc6310003dc3188001f710c4001fb0862002dfcc110017df308800bee9844005fbc822000ff64110017f820880017fb2a4000dfd9520004feca90012fe65480017eb2a4004bf19520006f8ca900127c65480017fb224003bf99120005fac89000efc64480017fb1a4002bf98d20005fac69000afc634800b7fb124008fbd492000fdca490003ed5248003f62924007fbd092000fdc8490003ed4248003f62124006fbcc92000fdc6490003ed3248003f61924000bfd8520005f8c290003de3148001ee18a4001fbc8520007dc4290003ed2148003f610a4001bfd8120007be6090003dd3048003fd9024005fb8812002fd84090007f82048001f7b2a4000dbd9520047dcca90003ed6548011f63
  | 2 => 0x210afde8010857ec4008429f79804214fb0c021025facb2800efe64940017eb24a005bf19250015fcc728017de63940056f31ca000bf58e5002fbac728002dd639400b7e31ca004dfd4e50006faa728006fe629400bf7314a001bb98a50005fac528017ed629400176b14a005bf18a5009efca5280137c52940017f30ca000bf58650006fca3280137c5194001ef18ca000f70c650007dc4328003ec219400b7f304a005dfd4250027f6a128017f8509400b7fb2aa000bfd915001dfcc8a800efc6454009bfaa2a000df55150005fec6a800afe63540057e31aa000bfd895000dfcc4a8006fc62540017fb0aa000bf18550026fea2a80037d5154001ef18aa000f70c550007dc42a8003ec21540097fb02a004fed415002efca0a80177c5054009fc282a005bfd9640025fccb20002fd659000b7e32c8003bf59240015fcc720017de63900056f31c8000bf58e4002fbac720002dd639000b7e31c8012ef90e4001f788720006fe629000bf73148001bb98a40005fac520017ed629000176b148005bf18a4001f7e8520003bd42900017f30c8000bf586400077c832000fbc4190001ef18c8000f70c640007dc4320003ec219000b7f3048005efd024001ff68120017f840900017fb2a8004bf99540005facaa0012fc655000b7fb228003ef951400077aa8a0002ff63500057f31a8002bf18d40005fec4a0006fe62500037e3128000bfd8540005f8c2a000fbf4150001dea0a8000f78c540007b862a0003ee2150001f610a8003bfd814001ff680a0017be405000bde2028003fe10140017becb9800bde65cc005af32e6002f759730016bacb9800bdc65cc005efb266002f799330017bac99800bdc64cc023efaa66010f795330007baa998043dc54cc005efb166002f798b30017bac59800bdc62cc023efa96600ff794b30007baa59803fdc52cc021efa16600ff790b30007ba859803fdc42cc005efb0e6002f798730005bcc39800bdd61cc005ee30e6011f7d4730007bca398003dd51cc023ee28e6010f7d0730007bc8398003dd41cc021ee20e600ff7c8730007bc4398003ce21cc001ee90e600ff708730007984398047df50cc00bef2866000f75433002fb8a198043df40cc00bef2066000f75033002fb8819803fdf20cc00bee1066005bfd9630025fccb18002fd658c00b7e32c6005bfd923001dfcc918002fd648c00b7e3246002bf58e30005bac718006fe628c00bf73146001bb98a30005fac518017ed628c00176b146005bf18a30005fcc318002fd618c001ef18c6002f70c630007dc4318003ec218c00b7f3046005f7cc230017f66118017f8308c0017fb2a6004bf99530005faca98012fc654c0017fb226000efd91300057ec89800efe644c0017eb226003bf1913000778c89800ebc644c00b7fb1a600ef7d4d30017bca69800
  | 3 => 0xa18a6200bfd813102df8c09880bdf304c405efb286202f799431016bcca1880bdd650c405aeb286202f719431017bec81880bde640c405eeb206202f7190310e7bea81886fde540c401eeaa0621bf715031017bec41880bde620c405eeb106202f7188310e7bea41886bde520c401eea90621af7148310dfbe841886bde420c401eea10621af710831017bcc218802de610c405eb308621cf7d4431007bca218803dd510c439ee288621bf7d0431007bc8218803dd410c437ee208621af7c84310d7b8421880bdf600c405ef3006202f758031005bac01880bdc600c439efa80621cf7140310dfbe801886fdc400c435ef900621af708031005fecb10812fe6588401bf32c42049f99621005facb108037d65884013eb2c4204bf19621005fec91080efe64884017eb244203bf19221005fec71080afe63884017eb1c4202bf18e2100dfac510867ef5288403f72944200fb54a2100fd8a510863ef4288403f72144200fb50a2100fd8851085fef3288403f71944200fb4ca2100fd86510806fe6188401ef18c4200f70c62100fde4310807f72188403fa10c4205bf98221005fac110807ef2088403f61044200fbd96210cfdccb108036e6588401f6b2c4200db596210cfd8cb10803ef6488431f73244200fb592210c7d8c910867ef5488431f72a44200fb552210c7d8a910803ef638842ff731c4200fb58e210bfd8c710867ef538842ff729c4200fb54e210bfd8a710863ef438842ff721c4200fb50e210bfd88710806ee6188433f7a8c4200fb94621007daa310867ec5188431f7a0c4200fb90621007da8310863ec418842ff798c4200fb8c6210079c6310803ed318842ff618c4200f30c621007dec110803ee6088401f6b044200bb58221007d8c110867ef5088433f62844218fbd02210c7d8811085fef308842ff61844200bfd9521025fcca90802fd65484097e32a4200bfd912101dfcc890802fd64484077e3224200bfd8d21007bec690802df63484057f31a4200bf58d21015f8c690803dc63484056e31a4201bfd892100dfec290803de3148401ee18a4201fdc8521007dc4290807ec2148403fa10a4200bfd812102df8c090807ef2048403f7b284201fb9942100fdaca10807ec6508403f7b204201fb9902100f5cc810807ed6408403d6b204201fb190210b7dea810857ee5408401f6aa04215fb1502100fdec610807ee6308403f6b184201fb18c210b7dea610853ee5308401f6a984214fb14c210afde8610853ee4308401f6a184214fb10c2100fdcc210802ee6108403f33084216fbd4421007dca210803ed510842df62884215fbd0421007dc8210803ed410842bf62084214fbcc421007dc6210803ce3108401f69884214fb0c421007986210807ef6008403f73004201fb58021005dac010807ec600842df7a804216fb140
  | 4 => 0xbde534c801eea9a6401bfd893200fdc8499003ed424c805f79926401f78c93200fb86499007ec324c8017fb0a6400bf18532017b86299007ec214c8017fb026405bf18132017be6099007ef204c8097eb2ca203bf99251005fac92880efc6494409bfaa4a200df55251015fcc728802fd63944057e31ca201bf98a51005fac528806fc62944097f30ca204dfd4651027eea328813f4519440b7f304a200bf58251026f8a128812ff65544017fb22a203bf9915101df8c8a8802ff6354401efb1aa200b7d8d51015fcc6a880afc6354401ee31aa202b718d51026fea6a88037d53544017fb12a200fbd8951005dec4a8806fe62544037e312a200fb1895100dd8c4a88877e5254409be292a204bfd8551027eea2a88037e5154409be28aa204fd14551005fec0a8816fc6054409bfa82a200bfd9641025fccb20802fd65904097e32c8203bf5924101f7ca920803bd54904057f31c8200bf58e41015f8c720806fe62904017eb148201bf18a4101dfcc32080fbf4190407fba0c8203fd1064102dfcc120802fd6090407de2048200bfd9541025fccaa0802fd65504097e32a8203bfd9141005fec6a0803df63504016fb1a8202bf98d41015f8c6a0803dc63504056e31a8220ef90d4101f7886a0802ff6250401f7b128200bbd894100dfcc4a0806fc6250401f63128201bb1894101f7e84a0803bd42504077fb0a8203fdd05410077c82a080fbc4150407fa20a8200bfd814102df8c0a080fbf40504017fb2c6204bf99631005facb18812fc658c4017fb246203bf992310077cc91880ebe648c4017eb246200ef592310057ac91880efc648c4057eb1c621ff7d4e31017bca718803dd538c405ee29c621ef7d0e31017bc8718803dd438c405ee21c6201bf98a31005fac518806fc628c405ef994621df78ca31007ba651880bdc328c4057f30c6202f7cc631017ee631880bf4318c40b7f3046200bf58231017be611880bdc308c401efb2c621ff799631007bacb1887fdc658c401efb24621ef7992310073cc918803dd648c401ceb24621ef7192310ffbea91887bde548c401eeaa4621ef715231007bec518877de628c401eeb14621df718a310ffbea518877de528c401eea94621df714a310f7be8518877de428c401eea14621df710a31015bcc31887fdf518c401ef28c6200f7546310ffb8a31887bdf418c401ef20c6200f7506310f7b88318877df218c43bee10c6200f7d8231007bcc118803dd608c4016eb046200f7182310ffbea11887fdc508c43defa04621ef7102310efbe4118877dc208c4017fb2a6204bf99531005faca98812fc654c4017fb226203bf99131005fac89880efc644c4057fb1a6200bfd8931007dec498802ef624c4037f3126201bf18931007d8c498806ec624c4057fb0a6202fdcc531007bc629880bdc314c405f
  | 5 => 0x803802008004100080080040100500400400802002014030050020080480000207c08000000004008170700380201400e00001000030094000610000001700200600c0380802c00004805000000008120000380000400c0000b8060160bc02804004000050040120081700d00001809803002038000020080080180100c0040000000a020030040000240200201a0140c8010020001680307a044010000000740200000a0080681301c004000040500600280703c00c0f80602600c00807004038070090080180100702e024028000000081000000c01c16800002000060000080000081500400c0380e00008c0080005c000010090020a80682a02a0103100a00a0040200d00202c0000f0120040a00400802c0600100600c0481c03c0280e0070100000000100c0040306600a01c00000006050050130040101280001c0540100002c0000300901c0a81181300a0000000000c00c008060080000b80000e0380401401a0040100602005c0a800004000020110220041280000002000001000004018000060280080000201007000004014008130060140080600200407000004000077fb2aa803bfd91540277ea8aa00f7e5455007be2a2a803ef15154005fec6aa00afe63550057e31aa804dfd4d5412f7c86aa00fbc43550017fb12a801bf9895400df8c4aa0937e5255009be292a803efd0954005fec2aa002fc6155009be28aa803ef10554005fec0aa016fc6055009bfa82a803efd0154015fecaa9802ff6454c077f322a603bf19153026fea8a98037d5454c057fb1aa604f7d4d53016fca6a980b7c5354c05ee29aa623f7d0d53017b886a9802ff6254c01f7b12a600bbd895300dfcc4a9806fc6254c01f6312a601bb18953017be64a9802ff6154c017e30aa604dfd4553017b862a9802ff6054c0b7e302a604df14153017be60a9802ff6550c097f32a8600bf59543025f8caa180aff6450c057fb1a8603f7d0d430177c86a180bbc4350c05ee21a8600bfd894300dfcc4a1806fc6250c017fb0a8600bf18543017b862a1802ff6050c0b7e3028602f7cc14300dfecaa9002ff64548077f322a403bf19152005fec6a900afe63548057e31aa401bfd8952027dea4a90077e5254803be292a401fb14952005fec2a9002fc6154803f610aa400bfd815202df8c0a9007ef20548017fb2a8404bf99542005facaa1012fc65508037fb228403ef951420077aa8a1002ff6350801efb1a8400b7d8d42015fcc6a100afc6350801ee31a8402b718d4200dfec4a108bef5250803f62928403fbd094200f7c84a1007bc4250803f62128401fb8c942005fec2a1002fc6150807dfa0a8401fb08542005fec0a1016fc6050807de2028401fbc8142005feca99012fe654c8017eb2a6404bf19532005fec89900efe644c8017eb226403bf1913200dfec699
  | 6 => 0x3c8e4152800059800000130a2a00020e9a280019107511c9e094e94d8f700016b1970d282480b89a00f8440378000ab03d80000011382f82100018188304300004c000256926939000251041855a361770af8000948e7a1b80000d0570d38000000bb17c8df85e0001ca1af00010420a22e0ff91789d8718000000058988039be870850214925863099035a5c0000001ee8000000001c007618101a13d0b514e2028388001e30002578000b680f10d93c9b80bd9b20000000b8a01155a4e00005da0f1ec88d90713b8391e59b118e95a8ea9d28000001580e2a12a6024ba5e81200000023680014f8270f222a9d18000c780010012f98a90a8bd0f794903b095045914179a0c8b380b22f23aa1a98d800a3500001f8bc8000a50000000001b600008f90981800005a1c992d2630608000ad2588002669371431bd1de1c09c78e900000009012ba211eba308fd0ae86690c0b40641ef91b980a550a200025908395a1bb0268001710438ff13e05a9b90908190001a4a650001a90081c81469d800019f9960540c00e71df9b01f68da9841540dd0000000eea68893a031d314180719522d80611280009f2228000001aa0c30002581978000000001888000000d30ef8000000001db90616007e02a017800240129848247a3b1fd1fa23da548c717500010686613a8fe00003616ea661599d612a0c1a460001f70001620000000000139b385394480a90900006d908a50a0605f1228001650000201f10368429dc0000000289d921412f2078cf01d1f91968499510dc99b9e821219e9641d588685304a03408c099a1623f1230659240051ec0d18d916491b2292069260be89b0a0a5c88991a93da158000a62019fb81f0000e21699b696d0000000aa8b00460001218000098001d512494393b00003d1900e98f99bb80000023404b800185a0a8578dc26721983800000005c0001f79b31591e78001ce0f51df23e8001080001ac2440740a022610d21701e9a5033a639010689a78ec06c80000016c010a451a18fb8681830001852380fe8651009031ae0b718f2610000001171a39db00000005814c9b58d68000f00f082d1720228c280000000024d9cf1e505900001619e2000001e21cf8c812e06f00023e0b901880014007d2469d7a448000000000d61790000a30420000000001e982514f07c19808b26583291e0a68a90b791323898297d88900082b000000060030000000000601e0300400104a01400006002000058040040040280300000400801014004008080141000100000e138000010140000080700a090000000020381e8030000040001b0000001e80705c01c0080300800c0d80300000c0c000014040068000060200d80100a004000050000002000000001401009000010038020000000180a0200740200700001
  | 7 => 0x1fca4aa4917405183702b9389ab90b9c20000621d08000001588e52320ba13a0298eb1dd8451660df195a4d21a1989561c61288878de1238b3205973084a5205ba378639161ff02a984a1ea35a1824f081067209a5292919b1ca8600e125ba431fd9c38d089c1c195f8001ea0cc9250280b0a258a78c921f1321dc9de85084e99304913f88aa3d0d483210a0ce91d8c892e8001688290001d418ba410f8a0fa488000092190528dd8bf9da8002458ea0cd952178948a6082da5f14a08587999411186100686904707106480e9a21e114b9e907709c9fa8f41149d697386b8230f59a71f98c09d11f416811f91c2530fb232a3a1e18ed0311709050841aaa4c1a6a5615795f2698b1a13a471cda3302580c8db2418478d81150209a01312349ed80014404095389403c1351f08000a40cb17f0521fe9639c900000013485d0728000000f28000000000fa9a610ca6181c1ea94800e0d00fa20420d93190b0028758000000002070808b10932248e588ca370d11999b484499180c0d59168b20cc17d23c9860100d2253a311e89b506b07aa5a8399211a98bc08a1a091d1920b293e9ff81b0ac8278af03e81501980d877a049368c10f3194a0b85e8568fd83197680000016911a00020503485125180024f8001bf00025e01307c8ca94723017a02e915a3f9e40e30780d986f86d1208b622e9568da0aa0c39c315003508614a9ee0be11225d88d1ba0001c722083e14b0c5a021cc04f0001af96aa498000000001b1a089bc09e00020d0928560ac0ec87a00007221f81109102f0002268e18001cb08e02619d1761da00892018c2649ed0c20ed8e09c48e819c1049f016783015d8a29c501d8a9a29a559451cba0c14785b07b054a2f8800b48551f22399a826a0888d89611190e62240000b5a5425b21d22702b21e00006e0fc24e8c400000000019aa2322896f8000000748cf9110e497489694217b97595ea338d40a700000002c0000000001c11ce8e00a38b984c9181c593801b8000a4a428001408e68001778148f102e0000ae1bc99c989218a251548001e49700000ba80000025d1e719a00001692700021500021c0129b8a4b18f93f18c97b03f9f184f9ef13021196a16f00122d21d8788f615180000020813306a80026a9f62408001fb09604e12780000000015d23b9b709f80007913416197e22c9f49ba800048a3c1fc1719d380021311002407b84b01405fa109bd86280a0000ce0d71d887304a80018d0ca01a963203a4a16e13c14d2278f690f0001e69820a10821058ad89a8d78000001670001eb05ca2219917f8c480002381e0bf1ae9c28850e89198001f51039d48001cd000000217a5710e9ad87e84698b178102a501f300014c0d502c8f911088800000422824823900011882199f22c1f892c98395300013602211f0001e61328
  | 8 => 0x1668c60308000002678000f480026209d06c0cb8000dba16a420ee1c41a41dd03b89800481c9ac800145a10000139a690619e01e392a8588000c50eb90f8000001018de8158000bb9a10001410cd18e16b88295e0f39658e39f294297e800040192a438001a59800018000001908002629898701d70f800000018712da00a641881b79b98b825a0001378000a89d01f581707da0900000003f13580006e80000009780203a0000411cc9221be1c680024c80000025f8a18002219d215b80000000780000018794612b15c972a110918331a3011a1c8c698a03a88e97a8a59c886a17c1280768031a89079498971ab1b288f06787f0739b08ab9d996c88b9e286999da0e10e0ef09204da23a681508a815721b20b08198687f84d22025991e95b0f18872319339ad1fe1bf9f81551609b409b9020001628fc8c996d95c1f380022b89e895a2b19392c00
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xf7359110014dc7359110004ef725911000cec7259110004be76191100063f65191100063c6519110014de76d8d100065f65d8d100065c65d8d100069f64d8d100069c64d8d10014de71d8d10014dc71d8d100047f7558d100247c7558d10004bf7458d1001cbc7458d10004ef7258d1000cec7258d10004de7618d100065f6518d100065c6518d100069f6418d100069c6418d1000cee76d89100066f65d89100066c65d8910006af64d8910006ac64d8910006cf63d8910006cc63d891000cee71d891000cec71d89100047f75589100247c7558910004bf745891001cbc7458910004df7358910014dc7358910004ee76189100066f65189100066c6518910006af6418910006ac6418910006cf6318910006cc631891002674659451002cf4765451001eb4649051002cf47650510004de768c5100065f658c5100fe5c658c5100069f648c5100f69c648c510006cf628c5100eecc628c510004de760c5100065f650c5100e65c650c5100069f640c5100de9c640c510006cf620c5100d6cc620c510004ee76885100066f65885100ce6c6588510006af64885100c6ac6488510006cf63885100becc6388510004ee76085100066f65085100b66c6508510006af64085100aeac6408510006cf63085100a6cc6308510004de76cc1100065f65cc11008e5c65cc1100069f64cc1100869c64cc110006cf62cc11007ecc62cc110005d671cc110014dc764c1100065f654c1100765c654c1100069f644c11006e9c644c110006cf624c110066cc624c110005d4714c110004ee76c81100066f65c811005e6c65c8110006af64c8110056ac64c8110006cf63c811004ecc63c8110005e671c811000cec76481100066f65481100466c6548110006af644811003eac6448110006cf6348110036cc6348110005e47148110007c9304811002cfa76c411002e5f305941002e5d305941002e6f205941002e6d205941002e77105941002e75105941002e9f305901002e9d305901002eaf205901002ead205901002eb7105901002eb5105901002cdf7058c1002cdd7058c1002ecf2058c1002ecd2058c1002cef705881002ced705881002ecf305881002ecd3058810004df768c410014dd768c4100fe5e658c4100065d658c4100f69e648c4100069d648c4100eece628c410006cd628c410005d9708c410014df760c410004dd760c4100e65e650c4100065d650c4100de9e640c4100069d640c4100d6ce620c410006cd620c410005d9700c410004ef768841000ced76884100ce6e65884100066d65884100c6ae6488410006ad64884100bece6388410006cd6388410005e9708841000cef7608410004ed76084100b66e65084100066d65084100aeae6408410006ad64084100a6ce6308410006cd6308410007c43108410005e97008410004fb7644010
  | 1 => 0x85200456e75985200056d75985200066f65985200066c6598520005e970985200056f75585200456c7558520005af745852003dac7458520005cf7358520035cc7358520005eb70585200066f65185200066c651852003dae7418520005ad7418520006ae7418520006ad7418520006e74118520006e44118520006e73118520006e43118520004ef7654520004ec7654520005cf7354520035cc7354520004ef7650520004ec7650520005cf7350520035cc735052003dae748c520005ad748c5200074f658c5200074c658c5200078e748c5200078d748c520035ce718c520006cc618c520005cd708c5200eecf608c5200efcb608c520004ef764c520004ec764c5200374e750c5200374d750c5200074f650c5200074c650c520005ce710c520037c6710c520007c7610c520006cc610c520007c4610c520006c4610c520037ca700c520005cd700c520037c9700c520005c9700c5200d6cf600c5200d7cb600c5200374e75cc1200374d75cc1200074f65cc1200074c65cc120005ce71cc120006cc61cc12002dcd70cc12002ecf60cc12007fcb60cc120005af744c12003dac744c1200074f654c1200074c654c1200078f744c1200078c744c120005cc714c120006cc614c12002dcf704c120037cb704c12002ecf604c120067cb604c12002fca104c120004df7359710014dc7359710004ef725971000cec7259710004df7359310014dc7359310004ef725931000cec725931001cbe74d8f10004bd74d8f100069e74d8f100069d74d8f10006d671d8f10006d970d8f10004ef7258f1000cec7258f100247e75d8b100047d75d8b10006cf63d8b10006cc63d8b100066e75d8b100066d75d8b10006e671d8b10006e970d8b10004df7358b10014dc7358b10006cf6318b10006cc6318b1002cf5769471002676659471002cf57690710006cf628c7100eecc628c710005d9708c710006cf620c7100d6cc620c710005d9700c710006cf63887100becc6388710005e97088710006cf63087100a6cc6308710005e97008710006cf62cc31007ecc62cc310005d671cc310006cf624c310066cc624c310005d4714c310006cf63c831004ecc63c8310005e671c8310006cf6348310036cc6348310005e47148310004bf7458e1001cbc7458e100069f7458e100069c7458e1002ecf2058e1002ecd2058e100047f7558a100247c7558a100066f7558a100066c7558a1002ecf3058a1002ecd3058a100eece628c610006cd628c6100d6ce620c610006cd620c6100bece6388610006cd63886100a6ce6308610006cd6308610007c431086100247e76d9510004bf745951001cbc7459510004df7359510014dc7359510004ef725951000cec72595100047e761951001cbe76d91100063f65d91100063c65d91100047f75591100247c7559110004d
  | 2 => 0x6cc6188530005cd70885300becf60885300bfcb6088530004df7648530004dc76485300678e74085300678d74085300078f64085300078c6408530005ce7108530067c67108530007c76108530006cc6108530007c46108530006c46108530067ca7008530005cd7008530067c97008530005c9700853007ecf60085300a7cb600853002f984050130004ef7654f2000cec7654f200066e75987200066d759872000ee67198720004ef765472000cec7654720005cf735472004dcc7354720004ef765072000cec7650720005cf735072004dcc7350720055ae748c720005ad748c7200078e748c7200078d748c7200ef8e648c7200ef8d648c720006ce618c720005cd708c720004ef764c72000cec764c72004f4e750c72004f4d750c7200d78e640c7200d78d640c72004fc6710c720006ce610c720005cd700c72004f4e75cc32004f4d75cc32007f8e64cc32007f8d64cc320005ce71cc320006ce61cc320005af744c320055ac744c3200078f744c3200078c744c3200678e644c3200678d644c320005cc714c320006ce614c32004fcb704c320004dc7158e20066cc2158e2002ecf2058e2002ecd2058e2000eeb7058a20004df7358620014dc7358620004df768c620004dd768c620014df760c620004dd760c620005d9700c6200bece6388620006cd6388620006e6618862002ced72d95200466f52d95200247e76d952009e6e72d95200066d72d952009e6c21d952009c7e761952002ced72d91200047f75591200247c7559120004df7359120014dc7359120004f77159120004f4715912002ced72d8d200047f7558d200247c7558d20004bf7458d2001cbc7458d20004f77158d20004f47158d2002cec765492002cec76509201166c655092001eac6450920005cf7350920035cc735092002cec764c920014de73d8520004dd73d852001cbe7418520004bd74185200065f658c5200fe5c658c5200065f650c5200e65c650c520006d7610c520006d4610c520005d9700c52002cee76885200456e75885200056d75885200066f65885200ce6c6588520006e4618852002cec7648520005cf7348520035cc73485200065f65cc12008e5c65cc1200065f654c1200765c654c1200466e65d95200456e76d952009e6f60d952009f6b60d9520005eb70595200056e76195200466e76195200472e74195200472d74195200474e73195200474d73195200066e63195200066c63195201366f60195201376b60195200066c65d91200056f75591200456c75591200066c655912003eac6459120005cf7359120035cc7359120005e77159120005e47159120005eb70591200056f7558d200456c7558d20005af7458d2003dac7458d20005e77158d20005e47158d20005eb7058d20004ef7654d20004ec7654d20035ce73d8520005cd73d
  | 3 => 0xe72d9540004ed72d954002cbc7655140014de73d8540004dd73d854000cee72d8540004ed72d854002cbc7650540005d9700c540006e76108540006e46108540004df7650b30014dc7650b300069e74987300069d7498730016d67198730004df7654730014dc7654730005cf725473007dcc7254730004df7650730014dc7650730005cf725073007dcc725073008d5e75887300055d75887300074e75887300074d75887300bf4e65887300bf4d6588730006ce6188730005cd7088730004df7648730014dc76487300a74e65087300a74d650873007f8e740873007f8d740873007fc67108730006ce6108730005cd7008730016db7058e30004ec7158a30036cc3158a3002ecf3058a3002ecd3058a30004ef725863000cec72586300eece628c630006cd628c630006d6618c630004ef7688630004ed768863000cef7608630004ed7608630005e9700863002cdd73d95300765f53d9530004bf745953001cbc7459530004ef725953000cec7259530004f77159530004f4715953002cdd73d913001cbe76d91300969e73d91300069d73d91300969c31d9130094be761913002cdc7654d3011e9c6454d30005cf7254d30065cc7254d3002cdc7650d3002cdd73d893002cdc764c93000cee72d8530004ed72d85300247e75185300047d751853002cde768c53006d9e748c5300059d748c5300069f648c5300f69c648c530006d4618c53002cdc764c530005cf724c530065cc724c530006d4614c530006af64885300c6ac6488530006af64085300aeac6408530006e76108530006e46108530005e970085300765e65d95300059f745953006d9c7459530005cf7259530065cc7259530005d77159530005d47159530005db705953006d9e76d91300969f60d91300979b60d9130005db70591300059e761913006e9e761913006f1e751913006f1d75191300069f65191300069d651913006f8e721913006f8d72191300069e62191300069c621913013e9f601913013f9b60191300055f75589300755c75589300059f745893006d9c7458930005d77158930005d47158930005db7058930004df7650930004dc7650930065ce72d8530005cd72d853006d9e74985300059d74985300069f64985300069c6498530005d970985300055f75585300755c75585300059f745853006d9c7458530005cf7258530065cc7258530005db70585300755e75185300055d75185300069f64185300069c6418530006d561185300065e75185300065d7518530006d75118530006d45118530006d72118530006d42118530004df7654530004dc7654530005cf7254530065cc7254530004df7650530004dc7650530005cf7250530065cc72505300755e75885300055d75885300074e75885300074d75885300078f64885300078c6488530065ce7188530
  | 4 => 0xc6210078e748c6210078d748c621005cd708c6210a4ef764c6210bf4e750c6210bf4d750c6210074e650c6210074d650c6210bfc6710c621005cd700c6210cd6e75d82210056d75d82210066e65d82210066d65d82210bdce7398221005cd73982210066e65582210066d6558221005af74582210c5ac7458221006af7458221006ac7458221006ce3158221006cc31582210cd6e75182210056d75182210c5ae7418221005ad74182210bdce7318221005cd7318221004df7359521014dc73595210ccef7259521004df7359121014dc73591210c4ef7259121014de76d8d210eecc21d8d21004dd70d8d210eecf20d8d210bcef7258d210ecde7618d210d4de768c5210ecde760c521006cf63885210becc6388521004ef7654c2100cec7654c210ce6e75984210066d759842100ee671984210ccef7654421005cf73544210a5cc73544210c4ef7650421005cf73504210a5cc73504210afa441504210adae748c421005ad748c4210078e748c4210078d748c4210ef8e648c4210ef8d648c4210d5ce718c421006ce618c4210efc6618c421005cd708c4210bcef764c4210a74e750c4210a74d750c4210d78e640c4210d78d640c4210edce710c4210a7c6710c4210bece610c4210d7c6610c421007c6510c421007c5510c421007c6410c421007c5410c421005cd700c4210066f75580210066c7558021006ce3158021006cc315802100eeb7058021004bf7458e5001cbc7458e500069f7458e500069c7458e50004dc7158e5002ecf2058e5002ecd2058e500147f7654e5009d6c7254e5009e6c7558a50004ec7158a5002ecf3058a5002ecd3058a50004bf745865001cbc7458650004df7358650014dc7358650004ef725865000cec7258650004df768c650004dd768c6500eece628c650006cd628c650014df760c650004dd760c6500d6ce620c650006cd620c650004ef7688650004ed76886500bece6388650006cd638865000cef7608650004ed76086500a6ce6308650006cd6308650005e97008650014de73d9150004dd73d915002c7c7655150014de73d8550004dd73d855000cee72d8550004ed72d855002c7c7654550006d7610c550006d4610c550005e970085500969c7458e40004dc7158e4002ecf2058e4002ecd2058e400047f7558a400247c7558a400066f7558a400066c7558a40004ec7158a4002ecf3058a4002ecd3058a4000cbf7650a400959c7350a400047f75586400247c7558640004df7358640014dc7358640004ef725864000cec7258640004df768c640004dd768c6400eece628c640006cd628c640014df760c640004dd760c6400d6ce620c640006cd620c640005d9700c640004ef7688640004ed76886400bece6388640006cd638864000cef7608640004ed76086400a6ce6308640006cd630864000ce
  | 5 => 0x66d75d8941004ed70d8941006cf6318941006cc631894100cbc76509411059c7350941005b4715094101cbe74d9631004bd74d963100cee72d9631004ed72d96310fe5f5359631104bd769923101cbf76592310069f73592311069c73592311069f3059231024df7654e3111e9e6454e31005cf7254e310edcc7254e3101cdf7650e3100cdf764ca310047f75582310247c75582310f59e74d96310059d74d96310edce72d9631005cd72d9631005d671d96310fe5c6559631005d671d92310f71e75992310f71d75992310069f65992310069d65992310f78e72992310f78d72992310069e62992310069c629923114e9e619923114f9661992310f69f76592311069e61592311079661592310fd5e75d8a310055d75d8a310f59e74d8a310059d74d8a31005d671d8a31004df7650a31004dc7650a310ff5751946310e4df7654631005cf72546310edcc72546310dcdf7650631005cf72506310edcc72506310f59e74d82310059d74d82310069e64d82310069d64d82310edce7298231005cd72982310055f75582310fd5c75582310069e64582310069d64582310065f75582310065c75582310fd5e75182310055d75182310f59e74182310059d74182310edce7218231005cd72182310fcdf7359531004ef725953100cec72595310f4df7359131004ef725913100cec725913100cee76d89310becc31d8931004ed70d89310becf30d8931006cf628c5310eecc628c531004df7650831014dc76508310f69e74984310069d7498431016d671984310fcdf7654431005cf72544310d5cc72544310e75451544310f4df7650431005cf72504310d5cc72504310df9441504310069f74580310069c7458031016db705803110c7d76996210ce6f52596210247f76596210066f725962110e6c725962110e6f20596210247e75d92210047d75d9221014de73d9221004dd73d92210247e75d8e210047d75d8e2101cbe74d8e21004bd74d8e21024ef7654a2101cef7650a211166e6550a2101eae6450a21005cf7350a210bdcc7350a21014ef764ca210fe5e658c6210065d658c6210e65e650c6210065d650c621004bf745822101cbc7458221005e671d96210cf2e74996210cf2d74996210cf4e73996210cf4d73996210066e63996210066c63996211466e61996211476661996210ce6c65596210ce6f765962110e6e615962110f6661596210cd6e75d92210056d75d92210066e65d92210c6ae64d92210bdce73d9221005cd73d9221005e671d92210066e65592210cd6e75d8e210056d75d8e210c5ae74d8e21005ad74d8e21005e671d8e21004ef7654e21004ec7654e210cf6751946210b4ef7654621005cf73546210bdcc73546210acef7650621005cf73506210bdcc73506210c5ae748c621005ad748c6210074e658c6210074d658
  | 6 => 0x4000000904000008700754cf4000000fd40000000000006a8329104e18a4c000438af8000000000de4e4c4d400000c0000200a05c0000002000c00003014004000030160100180001a004038040000101700000003000820000000010010000040180d0380000280200c00000801000008000020000040100000007c0180101000400000004000038000060040000c010000000000020400000500201000800008040000040020240c022006018018000080000080400200000807002004000000000040080f002030018030060180280000000c02800010014038030040000700600603402001002000000000020100480d0240480000200601c0100001000c048030000080280000c0100080003a02c0000c01202402002000008030080020280300101c0540000400a000038100000200000900e004048010140100a0000140300400000002405000018000020010040000100d004028000010100000401c004020048000020140300a0060040180600400008800000054020040060180000100202801000012008060010240640480100002c000010020000400000000c008020000040080304c004028000140000000100200c040050080000000600a000008080020080100001a0040800302c000010000020000000100201402801000000020010000000580504005013009004000000090000100200100604002801000000000000120540100000e02801801006014008010020140000000a0100180000000000806024bd74d8d5401c7d75d8954014de73d8554004dd73d855400cee72d8554004ed72d8554024dd73d91530147c765515301e3c645515312f1c43551531266c625515300cee76d8953004ee71d895315ecc31d8953004ed70d895315ecf30d895300cee72d8553004ed72d8553004ef725954300cec725954300cee72d8543004ed72d8543014de73d8552004dd73d855201ced72d9542004df7359542014dc735954200cbc765514212e9c63551421272c5255142014de76d8d42004de71d8d42156cc21d8d42004dd70d8d42156cf20d8d42014de73d8542004dd73d854215cef7259532154df735913200cdc7654d32014ec7650932015cc7350932004df7359251014dc735925101c7f765525101cbe74d8d51004bd74d8d51014de76d8d510069e74d8d510069d74d8d51004dd70d8d510147c7654d5110d6c7254d51005747154d5100cee76d8951006cf63d8951006cc63d895110e6e75d8951004ed70d8951006cf6318951006cc6318951004ef725964100cec7259641024bf7655241004df7359541014dc7359541004ef725954100cec7259541004fb705954102cf87059541014de76d8d411069e74d8d41004dd70d8d410247e75d89410047d75d894100cee76d8941006cf63d8941006cc63d89410066e75d8941
  | 7 => 0xb3c1282250b80000000000000000000000000001b403c0000000000007fc8d41c00005bc13c000c50a983f08b8a2cb845e90fc1dcf11040ec0cc892cab0600ae06b00000548f86040000000008146bc710000b2c000000044000764fcc8803307348850b4df00000009b8d98cc4614000cd4f6005c374000000000334000e1400057cfa4594108954db89800000ec1b800000073c6181101f8000b507b80001d0b390383d8248dc91180007240007f400059c000000c2c000000fe4000000000b246dc9400000000007b4000078ce866852c218318000808f980000004c8440490000000de849c530029060bf0bc8968c14e500810d800072c00047400000093884d0f05a8d68fc8e9ca0c198fbc5c0c70134844a50d801d46e8b281bc8688bcfe83090ac9ac264750644460ab4fb4e80b706ecf1c5283fc2c83ac000828f30000000000ac8000c780000003a8b40f845843a06f0f3875c000000001124000fb85a40000004d09983b8890038fc4000bc0b1c000151094c94000000c65008c400e1114568e2847800019ce64e6855c744a480001f0d78c10320d3835d090d4c27c1d887c4446d03e000107c0004b8000000a00000f243400002bccb000047c00000000066c6986d42f0d880002b0b2000000000000095041c81ca5c0000000006cc000abc000000000bf40010f4000e5800054c271128958000580000bd07783b0000000000000be0000ca400000083c4a4000000dd0f3cd58efc0001a00000006c89fc00031c0004800001e8a18001064f00000000e3cc3010ca880001a50b08a80000006ac0b0488f9c690dd4e5cc68f44ea4e54000e08c186d8a6400037c0001ac00046c41015c384848fc079093c5f0fa8d50d307b000040ca6c5e4510f6c0000945401e4388a44d8d109120c1cec8c20bdc1f50743589e4b00984000000000000001045050034000000000d34ee8000000000a5824467000000028ca34c540008b0cac000f4d138000000af0e34d94000000000c7c0004bc64c00048cae8a08178894000000a201c869cd84000000b100000004c00003910240007380003e80000004b4838000000000680000000001098d2c000840000dc1030b480010a8d548a00000000583e4cb8000000000c48518e6000039cdd848426c558d484989005f4000290000000000000f90000000b7800014032c154000718524494aa030c5004f50100007f11348000007700003cc0000006e500cdac4702d4798098000888d240500000000000007308702e02d112c000bb40000004f8eec000f58000da8758d404cc36c2ec00094c1440745b407c554c386849780c8ba8000000aa4259080adc6481fc0e4c8000000000000000024c2940004547680000000000e8dc4000000001058000000170944cbc000d9c4dcbbc06c0010c46e0688000000a2
  | 8 => 0x30c089ec3690ccf189f4658cfcdfc000e441310007e02ccccc38040002cee4b88468eb06b8d648c82fc77c000000424000ba4160cf07acdbc8343f80000001380003542a8b807c4000ff84ed0bd0705749a8f680fc000e7c4180004645ccf5ccdc0003d000009c0000000000000000d40008642887dd09c3c4aecfecbd8a7456060c2c07d0d0500480cd5d0885c4348cd0000674d103d40cc740b9000000000093038cad4e04bec4b0c34b5cb74ed817c164c740000008f422c78468ce88000000000000000000e78000000f7400000097462889811400000044c000cb4d18f202105a01b0eace90994000000000720000e2400078c214eb40000003946fc85cca800045c0000011000000000000000010d42b433c4340144a0c90000000000000000ba0df8b949e81808d8000ae40dcc58c5c0009c00001e0f344f0168e98e2c9d8f4020c34c3f502c7a00f50dc578a60000b580004ac0007041ccde05f8d60bfc824b6400067c3146f45c8ea09d06302e90f8f880003bc310000000a80aac00000025c0b80008dc878af466014c0002b80008fcf280011100002acd0cdb0678bd4c8432416c3645890e4408e000000000d80002300ac184000000a70788000d91028a40024000bb0000000f80a38000119078c00208c2842ca04be404c6541a8d700000a490c1940009287f85e0ad8608e7400000000096d0d09883c8ef49106f855051d06c8e4934ac4fd0c60000e20e1c6c0000544000000918e38c88a849648503b4c8c000c6c000ed40a8b4c6a0a280010185aceccfd801058c0000640000003c00000000000009f80000005b80009703440000f8db4a14a1cbf874c79c9cc0005650541ec7941c47d47e80000004500a0000000000000000158428000000000000000a688d0000ee00000000003609c8590000000000b444482d8e6c0000000bc0007cc378cd8f2cbc40005dc000504f0cc0cd3c95c00000099c000d74000c047089140885d48c4a10a3c000820004304000bcc2386b4990c44338b54ca06210a06c4538000000da418c9a070c56c000f044e86506a47ec279048ec44a81202a00487a8000774f700000009f0640000000000420000000061084f14000000d7c8b4000e480000007bc26800000000103c71c2c400063886050c000040c3c62461c430000000000cc0068000acc000d440002e40003508180f000045823c4148040000000c41240004e0000000b0843cb60000fa05989b02a49dd01476010012c29d11c3990a4ff0274000d6c3a482cb688e08e8000908d288749b49600000000000840000009bc000714ad0df40010e8000000fdc000000000000000000f8cafc000a90000000b30b6c0010c053c62c63c030404fad01c920f090207a408c5140901908540c07e4000240000a9cffcf4894904c4c4000104000bac97c
  | 9 => 0xea8b7d10cf640010ec000aa8000200e102f801c370000188a94000000070250e30f7c21c1480009c4d200006648c0000eb80000010c89e0e407d80000000008304e4ef000000065c0000000000010e0b0cef80004fc3ec0000000b4000000c2469489cff4cf9068dccac000000000076c000000000000fb0000000000f7905c0d02548f098c5b0d003dcddcda0280dec570534508ebc748b04d142045ecb8c30000cf94c9cedcf545fcb18a7c0009a4f50cec000924810174ed029861000088c0008587c0000e708ecce02f400091c228000e94ce4000c4c000d08a542347c8000000ab8520b980000180000000000000005d0780000260fe0000000c984d800011cbe8548b347288cc000b145d8a78b9c22000108c28513086c8a4e0c0009d4a8cbb8e846348ac021034e8cd1c0000002dca
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x1e0f3a52000000005915361b5c0a124d2a003c0d000001000050070b000800002e1c200000000031240000005b3b4c0619004f0c411d00373f27210002005400000046001300000000001f040000384734562f115800350529093e2d57420000004e25005a000051330014000000431600444b280e2b261045004017183230003d2c4a0339000053220000481a00000055492300078080808000020100000181800002810482808101808000010000008100003310c671d89530066210ce3b1a8400a8e82d96648c40183eeb322c118803139ce65d9221004a6c3cca18c422de4661594318840185ccbba2c110802a361a748c421166c338ae91884200ac9800c5600840158902b106328002b1205630865000664b1ae010ca000ac4815883190001992c4b806320002b1205630864000526c34eb10e6000cc4311c5628c001988e430a6298002a320965191300054a40aca3226000c1d75190614c0014a90ab08c298002b1209611853000563416a230a600098d87190214c001d0ec83084298003a1190610853000723428c210a6000e4585184214c001d0ce83084298003a15d0610853000761380c210a6000ec170184214c001988c2b80429800352e157008530006a442ae010a6000d8b645c0214c001b10c8b80429800370d8570085300066430ae010a6000dc0615c0214c00151b0d3a46390002a3618744c32000662108e2b1c4000cd0615c03148001898e632ac89000319194715912000652320e2b224000c2c655d0614800158d07a08c290002b86003118520004a6c38ca18a4000e47651843148001c88ca3086290003919d4610c52000722ba8c218a4000e86841843148001d0b083086290003b09c0610c52000760b80c218a4000cc4615c03148001a96cab80629000352195700c520006c5c22e018a4000d88845c03148001b86c2b80629000332185700c520006e030ae018a4000cc0615c0314800129b0e32e6090003311c4614c12000665b12e018e2000ccb635c021c4001988c438a61880033118c71483100062a328e29822000cc4621c53044001948c838a40880033118c71481100356443260902200ccc8764c12044001b80e2982408800326591700c41000664b12e01882000ac5860c4210400198aec188420800391594310841000742b20621082000bc1800c421040018d2cab8042080033258d7008410
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xd19c0052cae61901490400807010014c091589700c6400052165c64184214c001c82745c0610853000720190615c0214c00144597194610c520007109d5701843148001c41755c0610c52000710d94615c03148001c4065185700c52000720a50615c03148001c8194185700c52000720e10615c03148001c8084185700c520006305d9800c42104001a81646003108410
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x9206a484185700c520
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x4
  | 3 => 0x5
  | 4 => 0x6
  | 5 => 0x1
  | 6 => 0x98c
  | 7 => 0x98d
  | 8 => 0x98e
  | 9 => 0x150c
  | 10 => 0x150d
  | 11 => 0x150e
  | 12 => 0x9cb
  | 13 => 0x9cd
  | 14 => 0x9ce
  | 15 => 0x168b
  | 16 => 0x168d
  | 17 => 0x168e
  | 18 => 0x130c
  | 19 => 0x134b
  | 20 => 0x20c
  | 21 => 0x20d
  | 22 => 0x20e
  | 23 => 0x140c
  | 24 => 0x140d
  | 25 => 0x140e
  | 26 => 0x24b
  | 27 => 0x24d
  | 28 => 0x24e
  | 29 => 0x144b
  | 30 => 0x144d
  | 31 => 0x144e
  | 32 => 0xb8c
  | 33 => 0xbcb
  | 34 => 0xd0e
  | 35 => 0xecd
  | 36 => 0x104b
  | 37 => 0x104c
  | 38 => 0x14b
  | 39 => 0x10c
  | 40 => 0x19cb
  | 41 => 0x184c
  | 42 => 0x18cb
  | 43 => 0x1a0c
  | 44 => 0xb8214
  | 45 => 0xbc253
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 68
  | 6 => 1238
  | 5 => 1103
  | 4 => 93
  | 3 => 15
  | 2 => 1
  | _ => 0
def gbR (k i : Nat) : Nat :=
  match k with
  | 8 => packedAt gbK8 (i*15) 6
  | 7 => packedAt gbK7 (i*26) 17
  | 6 => packedAt gbK6 (i*37) 28
  | 5 => packedAt gbK5 (i*48) 39
  | 4 => packedAt gbK4 (i*59) 50
  | 3 => packedAt gbK3 (i*70) 61
  | 2 => packedAt gbK2 (i*81) 72
  | _ => 0
def gbH (k i : Nat) : Nat :=
  match k with
  | 8 => gbHint (packedAt gbK8 (i*15+6) 9)
  | 7 => gbHint (packedAt gbK7 (i*26+17) 9)
  | 6 => gbHint (packedAt gbK6 (i*37+28) 9)
  | 5 => gbHint (packedAt gbK5 (i*48+39) 9)
  | 4 => gbHint (packedAt gbK4 (i*59+50) 9)
  | 3 => gbHint (packedAt gbK3 (i*70+61) 9)
  | 2 => gbHint (packedAt gbK2 (i*81+72) 9)
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 8 => packedAt gbK8 (16+((h/1+packedAt gbK8 (15+(h % 1)*1) 1) % 2)*1) 1
  | 7 => packedAt gbK7 (1922+((h/22+packedAt gbK7 (1768+(h % 22)*7) 7) % 82)*8) 8
  | 6 => packedAt gbK6 (50338+((h/412+packedAt gbK6 (45806+(h % 412)*11) 11) % 1486)*12) 12
  | 5 => packedAt gbK5 (56981+((h/367+packedAt gbK5 (52944+(h % 367)*11) 11) % 1601)*12) 12
  | 4 => packedAt gbK4 (5735+((h/31+packedAt gbK4 (5487+(h % 31)*8) 8) % 148)*8) 8
  | 3 => packedAt gbK3 (1075+((h/5+packedAt gbK3 (1050+(h % 5)*5) 5) % 19)*5) 5
  | 2 => packedAt gbK2 (82+((h/1+packedAt gbK2 (81+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffff01ff807fffffffe01ffff4473e3e63fe3f
  | 1 => 0x7c07fe07ff81e03e03fffffffbbac9c99c93ff
  | 2 => 0x8007fff80001ffc003ffe0f80c3cf1f1e0e3cc
  | 3 => 0x7fffffffe000003ffff000fc0fe01ff03f0
  | 4 => 0x7fffffffffffffc0000000fff0001fffc00
  | 5 => 0xfff8000000000000000000000ffffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x84310018800a214218a10948a0001212212615
  | 1 => 0x684216033480c434214a3297419a48c88c90ea
  | 2 => 0x97ab680c297d904a7748e06c2cb171e0e34c
  | 3 => 0x2125cdb5d96c0900939d9c418ec0fe017703b0
  | 4 => 0x4206f1c66e719e39e00600820f7f0001dad800
  | 5 => 0x73c0810070401021001810040ff7edac000000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 63 gbPos gbNeg, 0xeeeaeaeaeeaac888eeeaeaeaeeaac888eeeaeaeaeeaac888eeeaeaeaeeaac888eeeaeaeaeeaac888eeeaeaeaeeaac888eeeaeaeaeeaac888eeeaeaeaeeaac888, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_13633
namespace PEqualNP.Outside.L_meta_13633
open PEqualNP.Outside.L_meta_13633.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_1_0 : Interval s1Atlas 1 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_1 : Interval s1Atlas 1 0 1 := bs1_1_0
theorem alls1 : ∀ k ≤ 1, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_1 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 10 := bs2_3_0
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
theorem bs3_3_0 : Interval s3Atlas 3 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 10 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 12 := bs3_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 1 := bs3_5_0
theorem alls3 : ∀ k ≤ 5, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 4 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 12 := bs4_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 1 := bs4_5_0
theorem alls4 : ∀ k ≤ 5, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 4 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 12 := bs5_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 1 := bs5_5_0
theorem alls5 : ∀ k ≤ 5, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 1 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 15 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 93 := block_range (n:=93) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 93 := bgb_4_0
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
theorem bgb_5_1056 : Interval gbAtlas 5 1056 47 := block_range (n:=47) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1103 := (concat (concat (concat bgb_5_0 (concat bgb_5_96 bgb_5_192)) (concat bgb_5_288 (concat bgb_5_384 bgb_5_480))) (concat (concat bgb_5_576 (concat bgb_5_672 bgb_5_768)) (concat bgb_5_864 (concat bgb_5_960 bgb_5_1056))))
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
theorem bgb_6_1152 : Interval gbAtlas 6 1152 86 := block_range (n:=86) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1238 := (concat (concat (concat bgb_6_0 (concat bgb_6_96 bgb_6_192)) (concat bgb_6_288 (concat bgb_6_384 bgb_6_480))) (concat (concat bgb_6_576 (concat bgb_6_672 bgb_6_768)) (concat (concat bgb_6_864 bgb_6_960) (concat bgb_6_1056 bgb_6_1152))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 68 := block_range (n:=68) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 68 := bgb_7_0
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 5 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 2 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 34, 38),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 6 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 9 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeeeaeaeaeeaac888eeeaeaeaeeaac888eeeaeaeaeeaac888eeeaeaeaeeaac888eeeaeaeaeeaac888eeeaeaeaeeaac888eeeaeaeaeeaac888eeeaeaeaeeaac888
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 9 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) (SBf 1) :=
    slice_correct (ms:=fixRows 14 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008372970 * 2 ^ 32 + 4004169864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
theorem binaryLower (low : Lower true fullRoots fullWord 9)
    (gs : List Gate) (o : Nat) (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (h : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x)=posted x) : 9 ≤ gs.countP (fun g => !isNot g) := by
  have pg : proper fullWord := proper_of _ (by decide +kernel)
  have out := getRep (u:=true) (execute gs fullRoots) o
  rw [eval6 gs o legal h] at out
  unfold PEqualNP.Outside.L_meta_13633.Model.Repr at out
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

def mono : List Gate := [⟨.and,[2,5]⟩,⟨.or,[4,5]⟩,⟨.or,[0,6]⟩,⟨.or,[2,4]⟩,⟨.and,[0,7]⟩,⟨.and,[1,8]⟩,⟨.and,[1,3]⟩,⟨.or,[10,11]⟩,⟨.and,[9,12]⟩,⟨.or,[13,14]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,15⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 9) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372970 * 2 ^ 32 + 4004169864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372970 * 2 ^ 32 + 4004169864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
    refine ⟨⟨mono, 15⟩, monoShape, ?_, fun x => monoEval x⟩
    change mono.length ≤ s
    have hm : mono.length = 10 := rfl
    change gs.length ≤ s at hsize
    omega
end PEqualNP.Outside.L_meta_13633

open PEqualNP.Outside.L_meta_13633 in
theorem PEqualNP.Outside.L_meta_13633 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372970 * 2 ^ 32 + 4004169864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372970 * 2 ^ 32 + 4004169864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
