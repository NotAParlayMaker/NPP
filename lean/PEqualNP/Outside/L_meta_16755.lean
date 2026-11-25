import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_16755.Model
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


end PEqualNP.Outside.L_meta_16755.Model

namespace PEqualNP.Outside.L_meta_16755
open PEqualNP.Outside.L_meta_16755.Model
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

end PEqualNP.Outside.L_meta_16755

namespace PEqualNP.Outside.L_meta_16755
open PEqualNP.Outside.L_meta_16755.Model
def gbK8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x3580262b790b6753a0cdcc22d80d10000b00c4000011e19f239b8f25b0007400284aa000c9a0163140b800004e0020840420c244bff42fe42fd42fc42fe32fd32fc32ff41bf41fe41fd41bd41fc41ff21fe21fd21fc21ff40fe40fd40fc40ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x241ec32483fea2905fd4520ff28a41fd51483f8a2905f14520ffa0a41bf41483fc82907f50520dea0a41fc41483fe62907f8c520fe98a41fc31483fe42907bc8520ff10a41fd21483da42907f08520ffa0241fe40483fa80907f10120ff98241fe30483fa60907fc8120fd90241fe20483dc40907fd5020bfaa041fe54082fca8107f55020beaa041fc54082f8a8107fd4c20bfa9841fe53082fca6107f54c20bea9841fc53082f8a6107fd0c20ff21841fd43083f886105f94820ffa1041fe42083fa84107f10820ff99041fe32083fa64107f0c820ffa8841fe51082fca2107f54420bea8841fc51083fe82106fd0420ff20841fd410837a82107f10420ff98841fe31083fa62107f0c420ff90841fe21083fa42107f08420bf28041ff40083fc80107f50020fe20041ff30083fc60107f4c020fe18041ff20083de40107f88020fd10041fd20083da40107e48020ffaa6217f54c43fca9885f95310df2a6213e54c43faa9885f55310deaa6213d54c43f8a9885f15310ffa96217f52c43fca5885f94b10fea96217d52c43f8a5885f14b10ffa1621fe42c43fa85887f10b10ff19621fd32c43f865887fd0710dfa0e21fe41c43ec83887f50710dea0e21f541c436a83887f10710ff90e21fe21c43fa43887f08710ffa0621fe40c43fa81887f10310ff90621fe20c43fa41887f08310ffaa4217f54843fca9085f95210feaa4217d54843f8a9085f15210ffa94217f52843fca5085f94a10fea94217d52843f8a5085f14a10ffa1421fe42843fa85087f10a10ff19421fd32843f865085f54610ffa0c21bf41843fc83087f50610dea0c21fc41843fe43087f88610fe90c21fc21842fca1087fd0210ff20421fd40843f881087fc8210ff10421fa20843fa41087e48210fe10421ff10843ee21087ec4210ffaa2217f54443fca8885f95110feaa2217d54443f8a8885f15110ffa92217f52443fca4885f94910fea92217d52443f8a4885f14910ffa1221fe42443fa84887f10910ff19221fd32443f864887fd0510dfa0a21fe41443ec82887f50510dea0a21f5414436a82887f10510ff90a21fe21443fa42887f08510ffa0221fe40443fa80887f10110ff90221fe20443f440887f48110fc90221fc20443fe20887ec4110ff08221f610443fea8085fd5010ff2a0217e540437ca8084f95010feaa0217d540437aa8084f55010fe2a0217c54043fea4085fd4810ff290217e52043dca4085b94810fea90217d52043daa4085b54810fe290217c52043fe84087f90810fea1021fc42043fc64087f4c810fe190217e51043fe82086fd0410ff20821fd410437a82087f10410ff90821fe21043fa42087f08410bf28021ff40043fc80087f50010fe20021ff20043fc40087f48010fe10021ff10043ee20087f84010fd08021fd10043ea20087e44010
  | 1 => 0x950086f2a010ff14021ffa9681fe52d02fca5a07f54b40bea9681fc52d03fe85a07f90b40fea1681fc42d03fc65a07f4cb40fe19681ff51d03fca3a05f94740fea8e817d51d03f8a3a07fd0740dfa0e81fe41d03fa83a06f50740fe20e81ff21d03fc43a07f48740fe10e817d54903fea5207f94a40bf29481fd52902faa5207f14a40ffa1481fe429037c85207f50a40fe21481bc42903fc65207f4ca40fe19481ff51903fca3205f94640fea8c817d51903f8a3207fd0640dfa0c81fe41903fa83206f50640fe20c81ff21903fc43207f48640fe10c817e50903fe81206fd0240fda0481ff52502fea4a07f94940fea9281fc52502f8a4a07fd0940ff21281fd42503f884a07f8c940fe99281fc32503fea2a05fd4540ff28a81fd51503f8a2a05f14540ffa0a81bf41503fc82a07f50540dea0a81fc41503fe42a07f88540fe90a81fc21503fe80a07ed0140ff20281be40502fca8207fd4840ff290817e52103dca4205b94840fea90817d52103daa4205b54840fe29081ff42103fc84206f90840fea1081fc421037884207f8c840fe99081fc32103fea2207f94440bf28881f651102eca2207f54440bea8881f551102eaa2207f14440ffa0881bf41103fc82207f50440dea0881fc41103fe42207f88440fe90881fc21102fca0207fd0040dfa0081fe40103f480207f50040dea0081f940103fea9905fd5320ff2a6417e54c83faa9905f55320fe2a6417c54c83fea7907f94f20bf29e41fd53c82faa7907f14f20be29e41ff43c83fc87907f50f20fe21e41ff42c83fc85907b90b20fea1641ed42c83f885907fccb20f799641fe32c83fa65907f0cb20f619641ff51c83fca3905f94720fea8e417d51c83f8a3907fd0720dfa0e41fe41c83fa83906f50720fe20e41ff31c83fc63907f4c720fe18e41ff21c83de43907f88720fe90e41ed21c83f843907fd0320ff20641fd40c83f881907fcc320ffaa4417f54883fca9105f95220feaa4417d54883f8a9105f15220ffa9c417f53883fca7105f94e20ef29c415e53883faa7105f54e20eea9c415d53883f8a7107fd0e20ff21c41fd43883f887105f54a20ffa1441fe42883fa85107f10a20ff99441fe32883fa65107f0ca20ffa8c41fe51882fca3107f54620bea8c41fc51883fe83106fd0620ff20c41fd418837a83107f10620ff98c41fe31883fa63107f0c620ff90c41fe21883fa43107f08620bf28441ff40883fc81107f50220fe20441ff30883fc61107fc8220f790441fb20883fea8905fd5120dfaa2413f54483fca8905f95120feaa2417d54483f8a8905f15120de2a2413c54483fea6905fd4d20ff29a417e53483faa6905f54d20fe29a417c53483fe86907f90d20fea1a41fc43483fe84907f90920f721241fd42483da84907f10920ff99241ef32483fc64907f4c920fe19
  | 2 => 0x7fea520ff94a41bf29483fd52906faa520ff14a41ffa1483fe42907fa8520ff10a41ff19483fd32907f86520df94641ffa0c83bf41907ee8320ffd4241ff284837e50907faa120df54241fe28483ff52506fea4a0ff94941fea9283fc52506f8a4a0ffd0941dfa1283fe425077c84a0ff50941dea1283fc425077884a0ff8c941fe99283fc32507fe82a0fdd0541ff20a83be41507fea0a0dfd4141ff28283fd50507f8a0a0df14141dfa9283be525077aa4a0ef14941df19283bd325077864a0efd4541dba8a83bf505077ca0a0ef54141de282837e541067ca820ffd4841ff290837e52107faa420df54841fe29083ff42107fc8420ff50841fe21083fe32107fa6420ff0c841bf28883ff411077e8220ff90441fb20883fd411077a8220fd50441ffa8083fe50106fca020ff54041bea8083fc50107fea990dfd5321ff2a6437e54c87faa990df55321fe2a6437c54c87fea790ff94f21bf29e43fd53c86faa790ff14f21be29e43ff43c87fc8790ff50f21fe21e43ff42c87fc8590ff50b21fe21643ff32c87fc6590fb8cb21fe99643ed32c87f86590ffd0721dfa0e43fe41c87fa8390ef50721fe20e43ff31c87fea190ff94321bf28643fd50c86faa190ff14321ffaa4437f54887fca910df95221df2a4433e54887faa910df55221deaa4433d54887f8a910df15221ffa9c437f53887fca710df94e21fea9c437d53887f8a710ffd0e21ff21c43fd43887f88710df54a21ffa1443fe42887fa8510ff10a21ff99443ef32887fc6510ff4ca21fe19443ec32886fca310ffd0621dfa0c43fe41887fa8310ef50621fe20c43ff31887fc6310ffc8621f790c43f721887fea110ff94221bf28443fd50886faa110ff14221ffaa2437f54487fca890df95121feaa2437d54487f8a890df15121ffa9a437f53487bea690d7d4d21ff29a437e53487faa690df54d21fe29a437c53487b8a690d714d21ffa1a43fe43487fa8690ff10d21ffa1243fe42487fa8490ff10921ff99243fe32487dc6490ff4c921f699243fc32487fe8290efd0521ff20a43fd414877a8290ff10521ff98a43fe31487fa6290ffc8521fb90a43fe21487dc4290ffd4121bfa8243fe50487faa090ff14121be28243ff54086fea810ff95021bf2a043be540867ca810ff55021beaa043bd540867aa810ff15021be2a043ff53086fea610ff94c21bf29843de53086bca610ff54c21bea9843dd53086baa610ff14c21be29843ff43087fc8610ff50c21fe218437e52087fe8410ff90821fea1043fc42087fe6410fbcc821ff19043fd32087f86410fb0c821bf28843ff410877e8210ff90421fea0843bd41087f88210ffcc421ff18843fd31087f86210ffc8421f790843fe21087ec4210ff48421f690843f521087fea010ff94021bf28043fa50086f4a010ff54021bea8043f
  | 3 => 0xa808004000080000080040280700c05c0800104e01000805006000010020000540100009604000000004004028000040200f00c00007c170060160180280200a0140100100009c0080a00c0440f0050080280080000006400009006008018040020300080100a01403013004000038050280a00101e00e0280000108c0141b0010080240000e014034028040220000080400401c02000006038000020060180000004c048018000040040001d0000080200e00800010800002030010020140140280204c008038000180200080700800002800000000040000020e80880a0120000380a018058000060220140382002c00401001066050018060260001a81602e000020030020040f80001001ffea7a17f94f42bf29e85fd53d0afaa7a17f14f42ffa1e85ff51d0bfca3a15f94742fea8e857d51d0bf8a3a17fd4342ff286857e50d0bfaa1a15f54342fe286857d5490bfea7217f94e42bf29c85fd5390afaa7217f14e42ffa1c85fe4390afca5217fd0a42dfa1485ef4290bfea3217f94642bf28c85fd5190afaa3217f14642ffa8485fe5090afca1217f54242bea8485fc5090bfea6a15fd4d42ff29a85fd5350bf8a6a15f14d42ffa1a85fe4350bfa86a17fd0942f7a1285fe4250b7c84a17fd4542bfa8a85fe5150bfaa2a17f14542be28a85ff5050afea0a17f94142fea8285fc5050af8a0a15f95042ffa9885fe5310afca6217f54c42bea9885fc5310bfe86217f90c42fea1885fc4310afca4217fd0842dfa1085fe4210bdc84217f50842dea1085ed4210bfea2217f94442bf28885fd5110afaa2217f14442ffa8085fe5010afca0217f54042bea8085fc5010bfea9195fd5232ff2a4657e548cbfaa9195f55232fe2a4657c548cafaa7197fd0e32ff21c65fd438cbf887195f94a32ffa1465fe428cbfa85197f10a32ff99465ef328cbfea3197f94632bf28c65fd518cafaa3197f14632ffa8465fe508cafca1197f54232bea8465fc508cbfea8995fd5132ff2a2657e544cbfaa8995f55132fe2a2657c544cbfe84997f90932fea1265fc424cbfc6499778c932ffa8a657f514cbfca2997f54532fe28a657c514cbfea0995fd4132ff28265fd504cbf8a0995f14132ffaa0657f540cbfca8195f95032feaa0657d540cbf8a8195f15032bf29065ff420cbfc84197f50832fe21065fe320cbdc64197f4c832f699065cd320cbfea2197f94432bf28865fd510cafaa2197f14432ffa8065fe500cafca0197f54032bea8065fc500cbfea5a0ff94b41bf29683fd52d06faa5a0ff14b41ffa1683bf42d07fc85a0ef90b41fea1683bd42d07f885a0ef10b41ff19683fd32d07f865a0ffd4341ff286837e50d07faa1a0df54341fe28683bf52d077ca5a0ef54b41de29683be32d077a65a0ef0cb41dfa8683be50d077aa1a0ef14341beaa4833d549
  | 4 => 0x92f9c60911424d04000b91d7de3c7ccdd8291ca8c9a3480009040000000000f05e8a08410000bd89740018280018c0000000d308f824c78d8c9f70dcd41d908b29cd8ab5228bb8dd40e037ce502894b901108df51dc1588000bb1e1411ccee1596599e02606e93d5db8021880ed90f8000ffc001eb2160a408b04c9c242c43d40011cc0005adb009f86b9a7157c0012c80001801a18e8000a28e485e58f0940af2250d5c0000000022f0ad99d8d98000000001d5d6e0d91a4d28d650b05bb048cf20000000934861ff19597b0000f19051a1cfd8d8a1d4891ee0df00000016d8560001bd800184970dd082300016798a49b0339b9ca68045b5d1316d1d98f100013f9564780fe1ce8d68000f48301b4071a1f90e04d1ac0d1cf083a0551c98000001bac0007e0e993f2011f1a1dcac5b740002f4e696849a8e29b71241ed0000001808b40000002360b3d6189a005519c2144712d1c55791119da0f2814459d3d10c004a2a1ba50906ac0006d14c80018983d1671cc10cc000001f41b814e0980001cbcee1611c280004a02c800108910400071c388994000b01781fb8164170000961709c454e8621312320464b25fb00000981c10f000000089c001abd7253842c1c215ed0d0d7d0787620fdd340015080015905ec000002005c481e0958a183b1b940005816282b15f9c117d9a208008584e0a79ffd559931d4c0023511ac409f981d8000f30001750a982f2130c78c807100017e50c4ead8116208f5d18acda19fe0b60f760905f5759a91a09c660f20990ad0d8aa07911a881c8881d0e800fc0000000002406800000000050000080980080c080000000040000000000800204406002000028068010060040780401e0000600a000040138040860000900300a04804027000000030000040540080100e0000100b01e03c160050180100100000001c058000000040080202c0100e0000200a0008000000080000a0440040400001a0ec010100080000780000001c02809002004188250000000000300000001807000034040040000280001100e0000100b0020540882100202c00000000010068000160000280600400000015004014000070000700100200a0040300306200406004010004108080020040600000804000000072000078090120980101103206c018000002000000000002c0000c00011c0180100a01c0c80c06a0000201103400c0e80f00e0000d00400200001811002004038000000b01980a0120a80d8010040880000100c00000800012000000000300141602902a0340400e0040180400503c0080000404201c0e80001801c02824000000020010120380000400c0040001300e0180200e002000060020300080100403c004010000000000701100000000823022014120000040041080300002c00815016000080010640280
  | 5 => 0x7a0619f30000000000000001d1137cd0c000d70fe9a6537841847400000110013d970000490000d28789a00b31e1c23923000187d148dca1485213c5bd0378e70e880020b8d004e99185d15949f0000330001a34000a9188a031ed80000000014a13d8f64000000fc52d4000900744a20cc0b0cda9320002189329688da0db0b689890b0001cca318facc45115428192138abd219295fa803c93c5080c0918f601b13910044d9c90fa4e411c10689e13ac0015c85dd178570b99461205c4e2c01fd8d1400a601e9681408000000f5831e2d00010815c17140002540011bd35085c0001606a0000c009b9b649c00844789c8568f9c00109c001a28001c180002ba2d8b85f4846d018f51de8d244a8f942d5c35b908d95a2231d00de94ec0022890e8000278541b116fc3d990559a009a606b0f385a4b490983a9348d190000002090a1d71e20395b4d0c97c1c31a394d852dae02d0115a10c31e606819a1c386b42680782da1094b0c11981fe98a1d661d9a30ad5e1a2013e59c8e21a2e2612d8a10001f586f87793a88218fd5bd4917103ec250050001481309ec0a385c47045d830556ccd91d1e000000005f22e8a705112998bddf8351c5c429e6800110db442ea1a0931851f0e104e44318a65c6a3688fe10d49c0000000016b98696f808203845d2908a55f51886a61720784f5788a8a0a15fd1b503049c001d3c001368000119820000001554830041bc1a821812807d000000012cce4a551208f0000000000000c8c0003c06c4000e002992f0000001bf1261b28000b9c000000001639b080011b05a8aea020ff59b11b97943400001f400006073c4b000000178d2dc0ba24897cab87305a1d75630320b2d9e9540a58e396991090400111ddb21fc86d8d6538de89d1cbe61e93a4c60ea8246278880631b58bdd0b9d6848a1d1538ca9160591d260812694121ba300371691fc14500097444607259559b83863308bc00223a1b08195843e4b82100b15af85e1d840000000000a0be1ee98a9bb40f61c0b19b495e8bf0799f6a070c75f04f8c439768368be91e00006620d0001f004545f96a0000c9113808cf85ab12e18712703f88c20e1f600005ccca4f79ad0f5c0020c9a78000218e58d10391b999100000021180000008280000006cc000001f08001760ad2110450001b880000698000004595722680000000000000004ec155740ff0001a561920a87480013a1210ec1e24b461f00010fc3e02400008a9159e71cd0db8000fb9c78000000cf80023580001994701b800099d7c98b4fa8200928000fb1dfc001ea84fc00000004c000fa0001d30000001df16c8ce1a480016c0f4c00091e0284f1388b116f57d1d8d5b9f28000d840007d5b302e5e79a59d6c0009ed371439028639d211e89e4228f4588c1694180000fa0589d129db8453
  | 6 => 0xcc348ac09155500000004810497b8500314001dd80000ec7f95b12ac0020d91c8210b39e800000d000106000100839cb8c328001ac80017e15a8811421675998000001608d08f420c15f0259891e50001ef17f0cfd2b16020b0001dd1569985e38f6d4993989d95d05bcc285c1de0ea1fb5ef8740448bc8eb9cf931a1e074c5885fcf68b21d8018a069879fa173c53d5d80c9c720419686988b6240000d82328039e094595206592581a8f715313b5e115298fa140440de0b089210960ea2084300000016698d4000360700000001e2cb78151aa80002cde99c2c87a000d7966155cc9c0001420155193b8280000518001cd4001e400013e9884d38001e5997800120c0007722111e5440ac8001021301b7c001951e280009dc000135e3116800190c2e1a25289b8c311915ea1b18001580d213e12b99a9111f79832298b71818f989992a49d5f2233884173870d4a92a1c81e496f1220f889917307f0f90dc4aa8f808097a06bc14c691f902711d97a5a5c534dbd9d1488001920000ed068959ca309850842bd4794c12a8b1c00038c2ec000598002221a69b54000c08ba8b500000893b093816c0001791ec6e1c1ca488519c12081c8059acd375ad86015751a58e05c9d781f8a80e9575c0016b05585b4d6c948d51500ba03c8750fd148c6700003a589dcf0000001ca04c1ffa2a9b6c0018d86691517040023080004b8000b88001a14000c392e80014f85b9af19285b103878439979dd5512a1c9c89aba0492c07685486c000000009d8b8484001bf80000d82a00017487393cc5300018b03e8a504680016e9fd1b7998a2ca29c1f1fd810d2397e8b58cb86d4b359f0c700000000014d1ad6290138839938cb1be91960f8c897f9b68c18df87c012a0507e800061000001a12064124800158c00118cfbd734fb54f0001341b60072311798721d2d1fc001448000001700002280001f11331efc0000003087c80008952bc002271338e917722b8968709a5044c8d0e323408c9a402fdd91729778849b50c50000000d6000000090c8a0578000000cf0002044e61ac4d580010d4ff811171cab0124bc0000000000d49b393c84e4dd0ca0cf5634e15141f80609da9ae8400000001859cb0000fc0001578030000001ff5ba2229d440006c91d4c68094249c4095079c526061ec93c13811f1c58ec8001bb8e18908979838220c40af9fec000b4d4300297180e90b4000970e080019f820c421c513edd5072ce79d41db05d52c58400001049e86a9469561d89eec43d7553950a40a8c20bf9cb9ee62591919907dd1710711f8eb19615e1d387e500c64a2e12cc2f83808b9a461289242a942c1019001087a825cf55c08159c0105954a2b17a8149895434000000714e9dc6c4f9eb80002dcbd1d28001c3dbe12b4001510000a00cea088090000000000000
  | 7 => 0x15c30d940650d41835aa07d8cdd1a1e0def6151d59ce15e4e103592001303f0728494f00cd0000734444cc9e91a98120000ef8fc8678001d491c56488ad5a4000001a3c8987b0c583ddf38ae18ac0000b1640ef10bca147b939c002199bc96a9e3487000092e2f8204000c9447d199720499cb43b9278001362018ee8002218000000bd4868f7c0006f135a179adda89cc40021a9d61181251f89ccc8e882c21c000c49dc90a9ba8dc08e194852a168ea4d14628759861214b
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x9410433e5250410eb949410432e5250410cf54941043ad5250410cb549410433c5250410edd85410433e5150410cd945410427f65104109f59441042be6410410cf950410433d5410410db948410436d5210410be98041042f960104109f597210433e54c8410cf553210435e53c8410d754f210436e52c8410db54b210427f65884109f59621042be6488410af592210433e5488410cf552210435e5388410d754e210436e5288410db54a21042fa6088410be582210427f6548410cf951210433d5448410b7d8d21042dc6348410d794d210435d5348410db949210436d52484109fd94210427d6508410af99021042bd6408410cf950210433d5408410b798c21042dd6308410d794c210435d5308410db948210436d5208410be98021042f960084109f992500427d64940109f98a500427d62940109f586500433f4194010cf506500427d65d0010cf953400433d54d0010db94b400436d52d00109fd96400427d6590010cf952400433d5490010db94a400436d5290010bd98640042f561900109fd95400433e5450010cf551400436e5250010db549400427f65100109f994400427d65100109f194400433e5410010cf55040042ee6210010bb588400436e5210010db54840042f66110010bd58440043b940100109f597200433e54c8010cf553200435e53c8010d754f200436e52c8010db54b200427f65880109f596200433e5488010cf55220042de6388010b758e200435e5388010d754e200436e5288010db54a20042f66188010bd586200437a50880109fd9520042bf6448010af191200433e5448010cf551200435e5348010d754d200436e5248010db549200437a50480109fd94200427e65080109f594200427c6508010cf950200433d5408010d794c200435d5308010db948200436d5208010bd98420042f56108010af99310042bd64c4010cf953100433d54c4010db94b100436d52c4010edd0710043b541c4010dd59710043b664c4010ed593100437754c4010ed953100437554c4010ed553100433554c4010f994b10043e552c4010cf952100433d5484010db94a100436d5284010bd58610043765184010be596100437965840109e59610043ba5484010ee552100437b5284010fa94a10043795284010fa54a10043695284010be586100437a5184010fc94610043bb4184010ee506100427f6544010cf951100433d5444010db949100436d5244010edd0510043b54144010bdd95100437765440109dd9510043775444010ed95110043755444010ed55110043355444010f994910043e55244010bdd8110043765044010bed95100437b65440109ed9510043ba5444010ee551100437b5244010fa94910043795244010fa54910043695244010bed8510043f36144010de94510043f25144010eed0510043b94144010
  | 1 => 0x426d6594810dbd52520436e5494810eb952520432e5494810db55252043ad5494810cb552520436c5494810dbd4e520436e5394810f394e520434e5394810dbd92520436e6494810db592520436c6494810dbd8e520436e6394810db58e520436c6394810db986520436c6194810db982520436c6094810cf951520433d5454810d794d520427f64548109f191520427f63548109f18d520436f62548109fd85520427d61548109fd81520427d6054810dbd95520436f5454810db95152043ae5454810cb951520436d5454810eb551520432d5454810db151520436f5354810db94d52043ce5354810d394d520436d5354810f354d520434d5354810dbd91520436e6454810db591520436c6454810dbd8d520436e6354810db58d520436c6354810db985520436c6154810db981520436c6054810db04152042be6414810af590520433e5414810cf55052042de6314810b758c520435e5314810d754c52042ee6214810db548520427e6414810cf990520423e64148109f590520433d64148108f590520427e6314810d798c520425e63148109f58c520435d63148109758c520427e6214810db988520426e62148109f984520437661148109f980520437a60148109e980520427f65d08109f997420427d65d08109f197420433e54d0810cf553420435e53d0810d754f420436e52d0810db54b420427f65908109f996420427d65908109f196420433e5490810cf552420435e5390810d754e420436e5290810db54a420427f65508109f995420427d65508109f195420433e5450810cf551420435e5350810d754d420436e5250810db54942042fb6050810be181420427f65108109f994420427d65108109f194420433e5410810cf550420435e5310810d754c420436e5210810db548420427f658c8109f996320427d658c8109f196320433e548c810cf552320435e538c810d754e320436e528c810db54a320427f654c8109f995320427d654c8109f195320433e544c810cf551320436e524c810db54932042f7614c810bd185320427f650c8109f994320427d650c8109f194320433e540c810cf550320436e520c810db54832043cd320c8109f992510433e64944108f992510427d6494410cf592510423d64944109f98a510427d62944109f597410433f54d0410cf953410433d54d0410cf153410436e52d0410db54b41042bd65d0410cf597410423d65d0410cfd4b410433e52d0410eb94b410432e52d0410cf54b41043ad52d0410cb54b410433c52d0410cf947410427f65904109f59641042bd6490410cf952410433d5490410db94a410436d5290410dd94641042fa6090410be582410427f6550410cfd51410433e5450410cf551410433c5450410db949410436d5250410dd94541042bf6550410cfd95410423f6550410cfd4
  | 2 => 0x6348510dbd49214436c5248510ed50521442fb6048510be181214427e6508510af99021442bd6408510b798c21442dd6308510ed50421442fa60085109f997404433f54d0110cf15340442f661d0110bd58740443b541d01109f996404433e5490110cf55240443b541901109fd95404427d65501109f195404433f5450110cf15140442f76150110bd18540443b541501109f994404433e5410110cf55040442ee6210110bb58840442f66110110bd58440443b541101109f997204436f52c8110db14b20442f661c8110bd58720443b541c81109f99620442de6388110b758e20443b54188110be996204437a6588110bed8e20443da6388110be58e20443d96388110b658e20442f96288110de94a20443785288110be98620443bb4188110fc90620443b94188110fc50620443b141881109fd95204427d65481109f19520442bf6448110af191204436f5248110db14920442f76148110bd18520443b54148110be195204437865481109e19520443bb6448110ee19120442fb6348110be58d20443eb6248110fad49204437a5248110de14920443e85248110fa90920443e94248110facc920443e83248110fcd8520442f86148110fc18520443bb4148110fc90520443b94148110fc50520443b14148110fac8520443e921481109f99420443b54108110be98020443e92008110af99310442bd64c4110ed50710443ba64c4110ee59310442fb62c4110be58b10443bb41c4110fc90710443b941c4110fc50710443b141c4110edd0610443b54184110bdd9210442f56484110fcd4210443f22084110fc48210442ee62d5010bb58b540427e62d5010db98b540426e62d50109f58b540436d62d50109b58b540427e61d5010dd987540427e60d5010de983540427d6595010cfd52540427e62950109f58a540423d6595010cfd8a540433e6295010cf58a540433c6295010cf986540433c6195010cf982540433c6095010cfd91540427f62550109f189540427f61550109f585540427f60550109f581540433f6555010cfd89540433e6255010cf589540433c62550108fd85540433e61550108f585540433c6155010cf981540433c6055010cf04154042be6415010cf55054042ee6215010bb588540427e6415010cf990540423e64150109f988540436e62150109b988540427d6215010db588540426d62150109f984540437661150109d984540427e6015010de98054042be64d4810af593520433e54d4810cf55352042de63d4810b758f520427e64d4810cf993520423e64d48109f593520433d64d48108f593520427e63d4810d798f520425e63d48109f58f520435d63d48109758f520427e61d4810dd987520427e60d4810de983520427d6594810cf952520433d5494810dbd4a520427e64948109f592520427e63948109f58e520
  | 3 => 0x110bb189544433f64551109fd89544436f62551109bd89544427c6255110db189544426c62551109fd85544437761551109fd81544437b60551109f994544433d5415110cf990544427e62151109f588544427e6115110dd584544427c61151109f980544427c60151109f993524427d64d49109f98f524427d63d4910dbd4a524427e64949109f592524427e63949109f58e524427e62949109f586524437561949109f58252443796094910afd9152442bc6454910b7d8d52442dc63549109fd91524433f64549108fd91524427c6454910cf191524423c64549109fd8d524435f635491097d8d524427c6354910d718d524425c6354910dbd89524427f6154910ddd85524427f6054910ded81524427e6514910db548524427e64149109f590524427e63149109f58c524436e62149109f984524427c61149109f980524437960149109f180524427f65d09109f997424427d65d09109f197424436f52d0910db14b42442f661d0910bd587424427f65909109f996424427d65909109f196424433f5490910cf15242442fa6090910be582424427f65509109f995424427d65509109f195424427f65109109f994424427d65109109f194424433f5410910cf150424436f5210910db14842442f66110910bd58442442fa6010910be580424427f658c9109f996324427d658c9109f196324435f538c910d714e32442fa608c910be582324427f654c9109f995324427d654c9109f195324427f650c9109f994324427d650c9109f194324436f520c910db14832443cd320c910bd98432442f5610c910be98032442f9600c9109f997414433f54d0510cf15341442fa60d0510be583414433f65d0510cf997414433d65d0510cf197414433f52d0510cf94b414433d52d0510cf14b41443ba60d0510ee583414427e6590510af59241442f66590510dd99641442f56490510ad59241443765490510dd15241442f660905109f195414433f5450510cf15141442fb6050510be181414433f6550510cf995414433d6550510cf195414433f5250510cf949414433d5250510cf14941443b76150510eed8141443b86050510dd19541442746550510edd9141443b75450510dd95141443745450510ed15141443b74250510ed90941443b54250510ed10941443f36050510bd18141443f06050510edd9541443376550510ed19541443346550510edd8941443b66250510ed58941443b46250510edd4941443b65250510ed54941443b45250510ed8c941443b53250510ed0c941443b76050510ecd8141443b66050510ed58141443b46050510ec181414427e6510510af99041442f66110510ed504414427e65c8510dbd4b214436c52c8510ed50721442fa60c8510be583214427e6588510af99221442bd6488510ed506214427c6548510b7d8d21442dc
  | 4 => 0xd587528437a60d4a10dbd4a528427e6494a109f592528427e6394a109f58e528437a6094a10afd9152842bc6454a109fd91528433f6454a108fd91528427c6454a10cf191528423c6454a109fd8d528427c6354a10dbd89528436d5214a109f990528427d6414a109f98c528427d6314a10db98852843756114a10de980528427f65d0a109f997428427d65d0a109f197428427f6590a109f996428427d6590a109f196428433f5490a10cf152428436e5290a10db54a42842fa6090a10be582428427f6550a109f995428427d6550a109f195428436e5250a10db549428427f6510a109f994428427d6510a109f194428433f5410a10cf15042842fa6010a10be580428427f658ca109f996328427d658ca109f196328435e538ca10d754e32842fa608ca10be582328427f654ca109f995328427d654ca109f19532842f7614ca10bd185328427f650ca109f994328427d650ca109f194328436e520ca10db54832843cd320ca10be98032842f9600ca10cf953418433d54d0610be98341842f960d0610cf997418433d65d0610cfd4b418433e52d0610cf54b418433c52d0610ee98341843b960d0610cf951418433d5450610bed8141842f86050610cfd95418433c6550610cfd49418433e5250610cf549418433c5250610edd8541843bb6050610ee181418436e52c8610db54b21842fa60c8610be58321842be6488610af59221842df6348610b718d218436e5248610db54921842fb6048610be18121842be6408610af59021842de6308610b758c21842f96008610cfd53408433c54d0210cf952408433d5490210bd98640842f56190210cfd51408433c5450210cf950408433d5410210bb98840842ed6210210bd98440842f56110210dbd4b208436c52c8210b798e20842dd6388210db94a208436d5288210bd98620842f56188210be59620843796588210bed8e20843da6388210be58e20843d96388210b658e208437a5288210fa94a20843e95288210de14a20842fa6188210fc98620843f16188210eed0620843b94188210afd9120842bc6448210dbd49208436c5248210bed95208437b6548210eed9120843b86448210bed8d20842f96348210fad8920843eb5248210de94920843785248210fa14920843ea4248210fa50920843eb3248210fa0c920842f86148210eed0520843b94148210fac8520843e92148210db948208436d5208210bd98420842f56108210fa48020842be64c4210af59310843b741c4210ed50710842f565c4210dd59710843b664c4210ed593108437754c4210dd55310842f965c4210de59710843ba64c4210ee59310842fb62c4210be58b10843bb41c4210ee507108427e62d51109f58b544433f54951109f992544427e62951109f58a544427d6195110dd586544427d6095110de58254442ef6255
  | 5 => 0x42c427d6510b109f19442c433e5410b10cf55042c42f66110b10bd58442c427f658cb109f99632c427d658cb109f19632c433e548cb10cf55232c435f538cb10d714e32c436e528cb10db54a32c427f654cb109f99532c427d654cb109f19532c433e544cb10cf55132c436e524cb10db54932c427f650cb109f99432c427d650cb109f19432c433e540cb10cf55032c436f520cb10db14832c43cd320cb10bd98432c42f5610cb10cfd5341c433e54d0710cf55341c433c54d0710af59741c433d65d0710cfd4b41c433e52d0710cf54b41c433c52d0710cf95241c433d5490710be98241c42f96090710dd59641c43765490710ed95241c43b55490710dd15241c42f66090710fc98241c43f16090710cfd5141c433e5450710cf55141c433c5450710afd9541c433f6550710cfd4941c433e5250710cf54941c433c5250710edd8541c42f76550710ddd9541c43b76450710edd5141c43765450710ed95141c43365450710ed55141c43745450710ed15141c43b74250710ed90941c43b54250710ed10941c42f46050710edd9541c42b76550710cdd9541c43b76250710ed98941c43b56250710ed18941c43b75250710ed94941c43b55250710ed14941c43b63250710ed4c941c43b43250710edd8141c43b66050710ed58141c43b46050710cf95041c433d5410710ed50441c42fa6010710be58041c433e54c8710cf55321c436f52c8710db14b21c43b541c8710af99221c42bd6488710cf95221c433d5488710db94a21c436d5288710ed50621c42fa6088710be58221c433e5448710cf55121c42df6348710b718d21c436f5248710db14921c43b54148710af99021c42bd6408710cf95021c433d5408710b798c21c42dd6308710db94821c436d5208710ed50421c42fa6008710be58021c433e54d0310cf55340c42f661d0310bd58740c43b541d0310cf95240c433d5490310ed50640c433e5450310cf55140c42f76150310bd18540c43b54150310cf95040c433d5410310bb98840c42ed6210310bd98440c42f56110310ed50440c43b94010310cf95320c433d54c8310db94b20c436d52c8310bd98720c42f561c8310ed50720c433e5488310cf55220c42de6388310b758e20c43b54188310afd9120c42bc6448310cf95120c433d5448310db94920c436d5248310bdd8520c42f46148310ed50520c433e5408310cf55020c43b541083109f98b548427d62d5210dd587548437a60d5210cfd52548427e62952109f58a548433f64552109fd89548427c6255210cf55054842ee6215210bb588548433e64152109f988548436e62152109b988548427d6215210db588548426d6215210dd584548437a6015210b798f52842dd63d4a109f993528427d64d4a109f98f528435e63d4a109798f528427d63d4a10d758f528425d63d4a10d
  | 6 => 0x35d63940209758e500833f4194020cf506500827d65d00209fd96400827d6590020cf952400833d5490020bb98a40082ed62900209fd95400827f65100209f994400827d65100209f194400833e5410020cf55040082de6310020b758c40082ee6210020bb58840082f66110020bd584400827d65cc020d7d4f300827f658c0209f596300835e538c020d754e30082ee628c020bb58a300827f654c020afd9130082bc644c020d7d4d300827e650c0209f594300827c650c020bb98830082ed620c020dbd53200836d54c8020db94f200836c53c8020db54720083af41c8020eb50720082de6388020b758e20082ed6288020db94a20083da6388020f658e20082f96288020de94a20083ea5288020de54620083bb4188020ee506200827f6548020afd9120082bc6448020bbd95200836f65480209bd9520083af6448020eb191200836f5448020db551200836e5348020db14d200836d5148020ebd0520083ad4148020bbd81200836e5048020fad0120083e84048020fa8c120083e93048020bed95200837b65480209ed9520083bb6448020ee19120082fb6248020fad89200837a5248020fa94920083eb4248020fa10920083ea3248020fa4c920083795148020eed0520083b94148020fac8520083e921480209f98b54c427d62d5310dd98754c437960d5310cfd5254c427e62953109f58a54c43766195310ed98654c433f6295310cf98a54c433d6295310cf18a54c433e6195310cd98654c433c6195310cfd8254c433d6095310cfd9154c427f62553109f18954c433f6555310ed98554c433f6255310cf98954c433d6255310cf18954c433e6155310cf18554c433f6055310cf58154c433d5415310cf99054c427e62153109f58854c43766115310de58054c42be64d4b10af59352c433e54d4b10cf55352c427e64d4b10cf99352c423e64d4b109f59352c433d64d4b108f59352c427e63d4b109f58f52c437661d4b10de58352c433e5494b10cf55252c436f5294b109f99252c427d6494b109f98e52c427d6394b10cf95152c433d5454b10b7d8d52c42dc6354b109fd9152c427c6454b109fd8d52c435f6354b1097d8d52c427c6354b10d718d52c425c6354b10dbd8952c42be6414b10af59052c433e5414b10cf55052c42de6314b10b758c52c436d5214b109f99052c433e6414b108f99052c427d6414b10cf59052c423d6414b109f98c52c435e6314b109798c52c427d6314b10d758c52c425d6314b10db98852c43766114b10de58052c427f65d0b109f99742c427d65d0b109f19742c433e54d0b10cf55342c42f661d0b10bd58742c427f6590b109f99642c427d6590b109f19642c433e5490b10cf55242c427f6550b109f99542c427d6550b109f19542c433e5450b10cf55142c42fb6050b10be18142c427f6510b109f994
  | 7 => 0x414c208f990530827d6414c20cf590530823d6414c209f988530836e6214c209f98453083766114c209d984530827d6114c20dd58453082756114c209f980530837a6014c209fd97430827e65d0c209f597430827c65d0c20cf953430833d54d0c209fd96430827e6590c209f596430827c6590c20d794e430835d5390c20bb98a43082ed6290c20be98243082f96090c209fd95430827e6550c209f595430827c6550c20cf951430833d5450c20d794d430835d5350c209fd94430827e6510c209f594430827c6510c209f992520827d64948209f58e520827d65d08209fd96420827d6590820cf952420833d5490820db94a42082fa6090820be582420827f6550820db949420827f65108209f594420833e5410820cf55042082fa6010820be580420827d65cc820db94b320827f658c8209f596320835e538c820d754e32082fa608c820be582320827f654c8209fd94320827d650c820d794c320835d530c820db94832083cd320c820be98032082f9600c820af99251082bd6494420ddd46510827e6494420cf992510823e64944209f592510833d64944208f592510827e63944209f58e510827f64544209f191510827f63544209f18d51082be6414420af59051082de6314420b758c510837551144209fd97410827e65d04209f597410833f54d0420cf953410833d54d0420cf153410833f65d0420cf997410833d65d0420cf197410833f53d0420cf94f410833d53d0420cf14f410833e52d0420cf947410833d51d04209fd96410827e65904209f59641082bd6490420dd946410837551904209fd95410827d65504209f195410833f5450420cf951410833d5450420cf15141082ef6250420bb18941083765150420dd54541082fb6050420be181410833f6550420cf995410833d6550420cf195410833f5350420cf94d410833d5350420cf14d41083af6250420eb189410833e5250420edd85410833e5150420ed94541083365150420cf54541083b55150420cd54541083bb6050420ee181410827f65104209f994410827d6510420af990410827f65cc4209f997310827d65cc420d794f310835d53cc4209fd96310827e658c4209f59631082be648c420af5923108376518c420dd546310827f654c4209f595310827c654c420d794d310835d534c420bbd8931082ec624c420dd9453108375514c4209fd94310827e650c4209f59431082be640c420af59031082ee620c420bb58831082fa600c420be580310836e52c8420dd947210837551c8420be98321082f960c84209f59621082be6488420af592210827f6548420b7d8d21082dc6348420db94921082be6408420af59021082de6308420b758c21083765108420dd54421082fa6008420be580210827e64940209f592500827e6394020d798e500825e63940209f58e5008
  | 8 => 0x20f30c83148377510c520dd14431482fa600c520be580314827e65c8520cfd53214833c54c8520bb997214836e65c8520bbd9321482ed64c8520ebd5321483ac54c8520bb98f21482ec63c8520dbd4f214836d53c8520db14721483af41c8520eb50721483eb60c8520bb98321483e860c8520af99221482bd6488520cfd52214833c5488520bb58a21483775188520dd14621482fa6088520be582214833f5448520cf15121482df6348520b718d21483775148520dd14521482fb6048520be18121482ef6448520bb59121483af5448520eb15121483cf6348520bb98d21482ec6348520f318d21482cc6348520dbd4d214836d5348520f9d8521483e75148520db14521483e45148520ebd0521483ad4148520fad8121482ec6048520fa181214827e6508520af99021482bd6408520cfd50214833c5408520b798c21482dd6308520bb98821482fa60085209f997404833f54d0120cf15340482ee62d0120bb58b404827e6590120cfd52404833c5490120eb90a404827f65501209f595404827c6550120cfd51404833c5450120bbd8940482ec62501209f994404833f5410120cf15040482de6310120b758c40482ee6210120bb58840483ae4210120bd98440482f56110120ee500404827e65cc120cfd53304833c54cc120d7d4f304835c53cc120bb98b30482ed62cc120f30cb304833f548c120cf15230482ee628c120bb58a304827d654c1209f195304833f544c120cf15130482ef624c120bb18930483cc324c120cfd53204833c54c8120eed5320483b854c8120fa90b20483e942c8120faccb20483e832c8120be58720483bb41c8120ee50720483eb21c8120fa487204833f5488120cf15220482de6388120b758e20482ef6488120bb59220483af5488120eb15220482ee6388120f398e20482ce6388120f358e20482ed6188120ebd0620483ad4188120fad42204827e63d50209f58f540827e62d5020db98b540827e61d50209f587540827e60d5020de983540827d6595020cfd52540827e63950209f58e540827e61950209f586540833f64550209fd8d540827c63550209fd89540827d62550209fd85540827c6155020cf55054082de6315020b758c54082f66115020bd584540827e6415020cf990540827e6315020d798c540825e63150209f58c540835d63150209758c540827e6215020db988540826e62150209f984540837661150209d984540827d6115020dd584540827561150209f980540837a60150209f993530827d64d4c20db98b530827e61d4c209f587530837a60d4c209f596530835f5394c209f992530827d6494c209f986530827d6194c209fd91530827c6454c20d7d8d530827f6254c209f589530827f6154c209f18553082be6414c20af590530835d5314c20bd98453082f56114c209f990530833e6
  | 9 => 0x994424833f5410920cf15042482ee6210920cfd53324833c54cc920d7d4f324835c53cc920be98332482f960cc920db99732482ef64cc920bb59332483af54cc920eb153324836f53cc920f3d4f32483cc53cc920bb58732482ee60cc920fa98332482ea60cc920fa583324827e658c920cfd52324833c548c920d794e324835d538c920bb98a324833f544c920cf151324835f534c920d714d32482fb604c920be181324827e650c920cfd50324833c540c920d794c32483cd320c920bb994324836e650c920bbd9032482ed640c920ebd5032483ac540c920bb98c32483ce630c920dbd4c32483ce530c920db54c32483cd530c920d354c32482ed610c920bb980324833f54d4520cf153514833f64d45209f993514827d64d4520cf193514827e63d45209f58f51482be6494520af592514833f5494520cf15251483775194520afd9151482bc6454520cfd51514833c5454520b7d8d51482dc6354520af99051482bd6414520cfd50514833c5414520b798c51482dd6314520dd544514827e6414520cf990514823e64145209f590514833d64145208f590514827e6314520d798c514825e63145209f58c514835d63145209758c514836f3214520db0c8514837960145209f997414827d65d05209f197414833f54d0520cf953414833d54d0520cf15341482ee62d0520bb58b41483ae42d0520eb50b414833f65d0520af997414833e65d05208f997414833d65d0520af197414833c65d05208f197414833f53d0520cf94f414833d53d0520cf14f41483ae62d0520eb58b41483af32d0520eb0cb414833f51d0520cf147414827e65905209f596414827c6590520af592414833f5490520cf15241482ee6290520bb58a41482fa6090520be582414827f65505209f995414827c6550520cfd51414833e5450520cf551414833c5450520eb90941483ad4250520cfd9541482be6550520cf995414823e6550520cf59541482bc6550520cf195414823c6550520cfd4d414833e5350520cf54d414833c5350520eb98941483ad6250520ebcc941483ac3250520edd85414833f5150520cf145414827e65105209f594414827c6510520af990414833f5410520cf15041482ee6210520bb58841482fa6010520be580414827e65cc5209f597314827c65cc520cfd53314833c54cc520d794f31483cf32cc520ddd47314837451cc5209f996314827d658c5209f19631482be648c520af592314833f548c520cf152314835f538c520d714e31482ee628c520bb58a31483cc328c520be98231482f9608c5209fd95314827e654c5209f195314833f544c520cf151314835e534c520bbd8931482ec624c520f3cc9314827e650c5209f594314827c650c520af99031482bd640c520cfd50314833c540c520d7d4c314835c530c520bb98831482ed620c5
  | 10 => 0x882ee628c220bb58a308835e53c8220d754f20882ed65c8220db597208836f54c8220db553208836e53c8220f394f208834e53c8220f354f208836d51c8220ebd0720883ad41c8220be597208837965c8220f694f20883d953c8220be58720883bb41c8220ee507208827e63d51209f58f544827e61d51209f58754483af62d5120af587544833f63d5120cf98f544833d63d5120cf18f544833f62d5120cf58b544833f61d5120cf987544833d61d51208f587544833c61d5120cfd83544833d60d5120cfd52544827e64951208f992544827e63951209f58e544827d6295120db58a544827e61951209f586544827d6095120de582544833f64551209fd8d544827c63551209fd89544836f62551209fd85544827c61551209fd81544837b60551209f994544833d5415120cf990544827e63151209f58c544827e6215120db588544827c62151209f984544827d6115120af994544833e65151208f99454483ad6215120af584544833f6315120cf98c544833d6315120cf18c544833f6215120cf588544832d6215120cfd84544833e6115120cf584544823d6115120cf184544833f6015120cf580544833d2015120cfd53534833c54d4d209f993534827d64d4d20db58b534827e61d4d209f58753482be6494d20af592534833f5494d20cf152534835f5394d209f992534833e6494d208f992534827d6494d20cf592534823d6494d20db58a534827e6194d209f58653483796094d20afd9153482bc6454d20cfd51534833c5454d20bdd8553482f46154d209fd91534833f6454d208fd91534827c6454d20cf191534823c6454d20dbd89534827f6154d20ddd8553482776154d209f18553483746154d209d185534827f6054d20ded81534827e6514d20cfd50534833c5414d20d754c534827e6414d209f590534835e6314d209f188534827e6114d209f584534827f65d0d209f997434827d65d0d209f197434833f54d0d20cf15343482ee62d0d20bb58b434827f6590d209f996434827d6590d209f196434833f5490d20cf152434827f6550d209f995434827d6550d209f195434833f5450d20cf15143482ef6250d20bb18943482fb6050d20be181434827f6510d209f994434827d6510d209f194434833f5410d20cf15043482ee6210d20bb58843482fa6010d20be580434827e65d0920cfd53424833c54d0920be98342482f960d09209f996424833f5490920cf15242482ee6590920db99642482ed6490920ebd52424836e5490920db15242483ac5490920cb15242482ee6390920bb58642482ee60909209f195424833f5450920cf15142482fb6050920be181424836c65509209b19542483af6450920ebd51424836e5450920db15142483ac5450920bb18d42482ef6150920fad8142482ec6050920fa18142482e860509209f
  | 11 => 0xfa6010e20be580438833e54d0a20cf553428835e53d0a20d754f42882fa60d0a20be583428833f5490a20cf152428835e5390a20d754e428833e5450a20cf551428835e5350a20d754d42882fb6050a20be181428833f5410a20cf150428835e5310a20d754c428835e53cca20d754f32882fa60cca20be583328835e538ca20d794d328835d534ca20bed8132882f8604ca20d794c328835d530ca20f34c832882de63d4620b758f518835e53d4620d754f51882be6494620af592518835e5394620d754e518837751946209f992518833e64946208f992518827d6494620cf592518823d64946209f98e518827d6394620de982518835e5354620d754d518827f64546209f191518827f63546209f18d51882be6414620af59051882de6314620b758c518835e5314620d754c518837551146209fd97418827e65d06209f597418833f54d0620cf953418833d54d0620cf153418835e53d0620d754f418833f65d0620cf997418833d65d0620cf197418833f53d0620cf94f418839e53d0620c794f418833d53d0620e754f418831d53d0620cf947418833d51d06209fd96418827e65906209f596418835e5390620d754e41883765190620dd54641882fa6090620be582418827f65506209f595418827c6550620cfd51418833e5450620cf551418833c5450620d794d418835d5350620bbd8941882ec6250620dd94541883755150620cfd95418833e6550620cf595418833c6550620cfd4d418833e5350620e794d418831e5350620cf54d418839d5350620c754d41883af6250620eb18941883b76150620cf94541883b65150620cd945418833d5150620ed545418833551506209fd94418827e65106209f594418835e5310620d754c41882fa6010620be580418827f65cc6209f997318827d65cc620d794f318835d53cc6209fd96318827e658c6209f59631882be648c620af592318835e538c620d754e31882fa608c620be582318827f654c6209f595318827c654c620d794d318835d534c620bbd8931882ec624c6209fd94318827e650c6209f59431882be640c620af590318835e530c620d754c31882ee620c620bb58831882fa600c620be580318835e53c8620d754f21882be6488620af592218835e5388620d754e21883765188620dd54621882fa6088620be58221882df6348620b718d218835e5348620d754d21883765148620dd54521882fb6048620be18121882be6408620af59021882de6308620b758c218835e5308620d754c21882f96008620d794f408835d53d0220cf952408833d5490220d794e408835d5390220bb98a40882ed6290220d794d408835d5350220cf950408833d5410220b798c40882dd6310220d794c408835d5310220bb98840882ed6210220bd98440882f56110220ee500408835e53cc220d754f3
  | 12 => 0x107209fd9731c827e65cc7209f59731c835e53cc720d754f31c83cf32cc7209fd9631c827e658c7209f59631c82be648c720af59231c82ee628c720bb58a31c83cc328c7209fd9531c827d654c7209f19531c835e534c720d754d31c82ef624c720bb18931c83cf324c7209fd9431c827e650c7209f59431c82be640c720af59031c82ee620c720bb58831c83cc320c720be98031c82f9600c720dd94721c837551c8720be98321c82f960c8720bbd9321c82ed64c8720bb98f21c82ec63c8720db54f21c836e51c8720f994721c83e551c8720ebd0721c83ad41c8720bb98321c83ea60c8720fa58321c82be6488720af59221c82df6348720b718d21c82ef6548720dbd9521c82ef6448720bb59121c83cf6348720bb98d21c82ec6348720f318d21c82cc6348720db54d21c83e76148720db94521c83af4148720eb50521c82ec6048720af99021c82bd6408720b798c21c82dd6308720dd94421c83755108720be98021c82f96008720cf95340c833d54d0320bb98b40c82ed62d0320cfd5240c833c5490320eb90a40c833e5450320cf55140c82ef6250320bb18940c833f5410320cf15040c82de6310320b758c40c82ee6210320bb58840c83ae4210320bd98440c82f56110320bb98b30c82ed62cc320f30cb30c82de63d5220b758f548827e63d5220d798f548825e63d52209f58f548835d63d52209758f548836d62d52209f987548827d61d5220de983548833f54952209f98e548827d63952209f986548827d6195220cfd91548827f63552209f18d548827f61552209f185548833d5415220b798c54882dd6315220bd98454882f56115220cf990548827e6315220d798c548825e63152209f58c548835d63152209758c548836d62152209f984548837661152209d984548827d6115220dd58454882756115220de980548827e64d4e209f593538827e61d4e209f587538837a60d4e20d7d4e538827e6494e209f592538827e6194e209f586538835f5494e20d7952538835d5494e20d7152538835f6494e20d7992538835d6494e20d7192538835f6294e20d758a538835f6194e20d7986538835d6194e20d7186538835e6094e20d7182538827f6454e209f191538835f6354e209fd85538827c6154e20d7d95538835f5454e20d7951538835d5454e20d7151538835f6454e20d7991538835d6454e20d7191538835d6254e20d7d85538835e6154e20d7585538835c6154e20d7981538835c6054e20d754c538827f65d0e209f997438827d65d0e209f197438835e53d0e20d754f438827f6590e209f996438827d6590e20d794e438835d5390e20bb98a43882ed6290e209fd95438827e6550e209f595438827c6550e20d794d438835d5350e20bed8143882f86050e209fd94438827e6510e209f594438835e5310e20d754c43882
  | 13 => 0xee10540102de63d5320b758f54c827e63d5320d798f54c825e63d53209f58f54c835d63d53209758f54c836e62d53209f98754c827d61d5320de58354c833f54953209f98e54c827d6395320db98a54c827e61953209f58654c833f64553209fd8d54c827c63553209fd8554c827c6155320cf55054c833e64153209f98c54c827d6315320db98854c827e61153209f58454c83796015320af99353c82bd64d4f20d7d4e53c827e6494f209f59253c827e6194f209f58653c827f6454f209f19153c827f6154f209f18553c835d5314f209f99053c827d6414f20db98853c827e6114f209f58453c83796014f209fd9743c827e65d0f209f59743c835e53d0f20d754f43c82ee62d0f20bb58b43c827f6590f209f99643c827d6590f209f19643c833e5490f20cf55243c82fa6090f20be58243c827f6550f209f59543c827c6550f20bbd8943c82ec6250f209fd9443c827e6510f209f59443c827c6510f20cf95043c833d5410f20d794c43c835d5310f20bb98843c82ed6210f20cf95242c833d5490b20be98242c82f96090b20db59642c836e5490b20eb95242c83ad5490b20db15242c82ee6390b20bb58642c82ee6090b20fa98242c83e96090b20bbd9542c836f6550b20ebd9142c836e5450b20db15142c82ec6350b20bbd8542c82ec6050b20cf95042c833d5410b20be98042c82f96010b20bb59732c836d65ccb20bbd9332c82ed64ccb20db54f32c82ed61ccb20bb98332c835e538cb20d754e32c82fa608cb20be58232c835e530cb20d754c32c83cd320cb20be98032c82f9600cb20bbd9032c82ed640cb20f398c32c83ce530cb20db54c32c83cd530cb20d354c32c82ed610cb20bb98032c83ea600cb20fa58032c82be6494720af59251c837751947209f99251c833e64947208f99251c827d6494720cf59251c823d64947209f98e51c827d6394720dbcca51c836c32947209fd9151c827c64547209fd8d51c827c6354720af99051c82bd6414720b798c51c82dd6314720dd54451c827f65d07209f99741c827d65d0720cfd5341c833e54d0720cf55341c833c54d0720bb98b41c82ed62d0720eb90b41c83ad42d0720cfd9741c833e65d0720cf59741c833c65d0720cf94f41c833d53d0720cf14f41c83ae62d0720eb58b41c83af32d0720eb0cb41c833e51d0720cf54741c827f65907209f99641c827d6590720bb98a41c82ed62907209fd9541c827d65507209f19541c833f5450720cf95141c833d5450720cf15141c83ae4250720eb50941c82fb6050720be18141c833f6550720cf99541c833d6550720cf19541c833e5350720cf54d41c833c5350720eb98941c83ad6250720ebcc941c83ac3250720edd8541c833e5150720cf54541c83bb6050720ee18141c827f65107209f99441c827d6510720bb98841c82ed62
  | 14 => 0x82511036e5254440db549511033e64544409fd89511027c6254440cf909511033c4254440ddd9551103b66454440ddd4951103765254440f994951103665254440dd54951103e55254440d954951103745254440ed90951103b44254440dd99151103366454440ddd8951103766254440dd58951103746254440ddd0951103764254440cd90951103754254440dd10951103344254440dd8c951103753254440dd0c951103766054440dd18151103744054440bb98851102ed6214440db948511036d5214440bd98451103755114440cf953411036e52d0440db54b411037651d0440dd54741102fa60d0440be58341102be62d0440cf94b41103ae52d0440cb94b411033d52d0440eb54b411032d52d0440cf94741103b651d0440cf54741103b551d0440cd54741103ba60d0440af58341103b960d0440ae583411027d6590440af592411036e5290440db54a411037551904409fd95411033e5450440db949411036d5250440dd94541102bf6550440cfd9541102bc6250440cf94941103ae5250440cb949411033d5250440eb549411032d5250440edd85411033e5150440ed94541103365150440ed54541102bf6050440af990411036e5210440db54841103765110440dd54441102fa6010440be580411027f65c84409f997211027d65c8440afd9321102bc64c8440d794f211035d53c8440db94b211036d52c8440dd947211037551c84409fd96211027e65884409f59621102be6488440af592211035e5388440d754e211036e5288440db54a21103765188440dd546211027f65484409f595211027c6548440afd9121102bc6448440b7d8d21102dc6348440d794d211035d5348440db949211036d5248440dd94521103755148440bed8121102f860484409fd94211027e65084409f59421102be6408440af59021102de6308440b758c211035e5308440d754c211036e5208440db54821103765108440dd54421102fa6008440be580211033e4294040cf10a501033f4194040cf506501036e52d0040db54b401037651d0040dd54740102be62d0040eb94b40103ad52d0040af58740103b651d0040cf54740103b551d0040cd54740102bd6490040cf952401036e5290040db54a40103765190040dd54640102f96490040de95240103ba5490040fa94a40103e95290040ee90a40103b84290040fc94640103f15190040eed0640103b941900409fd95401036e5250040db54940103765150040dd54540102bf6550040cfd95401023f6550040af18940103ae5250040eb54940102bf6150040ed945401033d5150040ed54540103355150040afd81401033e5050040bed95401037b65500409ed9540102fb6450040eed91401037a5450040ee95140103ea5250040fa54940103bb4250040ee50940103f25150040fc54540103ba415004
  | 15 => 0x502f96090540ddd4541503745150540bed8141502f86050540cfd49415033c5250540edd85415033f5150540edd4541503375150540cf14541503b45150540eed8141502bc6050540ee18141502b860505409f99441502be6410540ed504415027e65c85409f597215027c65c85409f996215027d65885409f19621502be6488540af592215036f5288540db14a215027f65485409f995215027c6548540b7d8d21502dc63485409f994215027d65085409f19421502be6408540af59021502de6308540b758c215036f5208540db14821502fa6008540be58021503bb41d0140ee507405033c5290140af586405033f5190140eed4240502de63d4840b758f52102f661d4840bd587521036f52948409f98e521027d63948409f986521027d6194840eb192521036f5394840db94e52103ce5394840d394e521036c6494840dbd8e521036e6394840db58e521036c6394840dbd86521036e6194840db586521036c6194840db982521036c6094840d794d521027f63548409f18d521027f61548409f185521036f6554840eb191521036f5354840db94d52103ce5354840d394d521036d5354840f354d521034d5354840db991521036f6354840db98d521036d6354840db18d521036f6154840db985521036d6154840db185521036e6054840db181521036c4054840b798c52102dd6314840d794c521035d5314840bb988521036d5214840bd98452102f56114840d794f421035d53d0840db94b421036d52d0840be98342102f960d08409f596421035e5390840d754e421036d5290840af596421033d6590840af98e421039e5390840e754e42102be6290840eb94a421033d5290840eb54a421032d5290840af58642102bd60908409fd95421035e5350840d754d421036e5250840d794c421035d5310840db948421036d5210840be98042102f96010840af98c421039e5310840e754c42102be6210840eb98842103ae5210840cf54842103ad5210840af58442103ba6010840af58042103b96010840ae580421027f658c8409f996321027d658c840af99232102bd648c840d794e321035d538c840db94a321036d528c840be98232102f9608c8409fd95321027d654c8409f19532102bf644c840af191321036e524c840db549321027f650c8409f994321027d650c840afd9032102bc640c840db948321036d520c840f34c832102ee62d4440bb58b511036e52d4440db54b511036e5294440db54a511037751944409f98a511027d6294440ed99251103775294440dd94a51103e65294440d994a51103755294440f954a51103655294440dd14a51103b64294440ed10a51103746494440ddd8a51103766294440dd58a51103746294440ddd0a51103764294440dd50a51103744294440dd8ca51103753294440dd0ca51103766094440dd1
  | 16 => 0xe65c87409f59721d027f65887409f99621d027d6588740af99221d02bd64887409fd9521d027d65487409f19521d02df6348740b718d21d02fb6048740be18121d027f65087409f99421d027d6508740af99021d02bd6408740b798c21d02dd6308740be98021d02f96008740b798f52902dd63d4a40dbd4a529027e6394a409f58e529027e6194a409f586529027f6354a409f18d529027f6154a409f185529036d5214a40db94a429036d5290a40be98242902f96090a40af98e42903ae5290a40cf54a42903ad5290a40af58642903ba6090a40af58242903b96090a40db949429036d5250a40bed8142902f86050a40af594429033d6510a40af98c42903ae6210a40cf54842902bd6110a40af580429027f658ca409f996329027d658ca40af99232902bd648ca40d794e329035d538ca409fd95329027d654ca409f19532902bf644ca40af191329027f650ca409f994329027d650ca40afd9032902bc640ca40db948329036d520ca40f34c832902fa600ca40be580329037751946409f98a519027d6294640cf591519027f62546409f189519033e4254640cf10951902ee6214640bb58851903755114640af597419033d65d0640af98b419033e52d0640cf54b419033e51d0640af58341903765190640dd54641902fa6090640be58241903765150640dd54541902fb6050640be18141902bc6250640cf949419033d5250640edd85419033e5150640ed94541903365150640cf54541903b55150640cd54541902bf6050640eed8141903b860506409fd97219027e65c86409f59721902bf64c8640af193219036e52c8640db54b219027f65886409f996219027d6588640af99221902bd64886409fd95219027d65486409f19521902bf6448640af19121902df6348640b718d219036e5248640db549219027f65086409f994219027d6508640af99021902bd6408640b798c21902dd6308640be98021902f96008640af597409033d65d0240af98b40902bd61d0240cf54740902f965d0240de597409027e63d49409f58f525027e61d49409f58752502de6394940b758e525036f5294940db548525027e63149409f58c525027e61149409f584525027e65d0940dbd4a425036c5290940be98242502f96090940dbd49425036c5250940bed8142502f860509409f994425027e658c9409f596325027c658c940dbd4a325036c528c9409fd95325027e654c9409f195325036f524c940db149325027e650c9409f594325027c650c940af99032502bd640c940f34c832502fa600c940be580325033f64d45409f98b515027d62d4540ddd4651502ef6254540bb189515037551145409f988515027d62145409f99741502be65d0540cf997415033f52d0540cf14b415033c51d0540af98341502bd6490540ddd4641503745190540be98241
  | 17 => 0x4021de95250087ba5494021ce95250087795494021ee55250087395494021de152500877b5394021de94e50087da5394021d694e50087795394021f654e50087595394021de14e50087eb3294021fa0ca50087bb4194021ee50650087eb2194021fc88650087e92194021fc486500877b6494021de99250087796494021de192500877b6394021de98e50087796394021de18e500877b4394021de90e50087794394021de10e50087786294021ded0a500877a4294021de50a50087784294021decca500877a3294021de4ca50087783294021de186500877b4194021ced06500877a4194021de50650087394194021de106500877b3194021de8c650087793194021de0c6500877b2194021de88650087792194021cf951500873d5454021d794d500875d53540219fd91500867c64540219fd8d500867c6354021dbcc9500876c3254021cfd05500873d4154021dbc85500876d2154021ded95500877b5454021de95150087ba5454021ce95150087795454021ee55150087395454021de151500877b5354021de94d50087da5354021d694d50087795354021f654d50087595354021de14d50087eb3254021fa0c950087bb4154021ee50550087eb2154021fc88550087e92154021fc485500877b6454021de99150087796454021de191500877b6354021de98d50087796354021de18d500877b4354021de90d50087794354021de10d500877a6254021ded09500877a4254021de50950087784254021decc9500876b3254021de8c950087793254021de0c950087683254021de985500877b4154021ced05500877a4154021de50550087394154021de105500877b3154021de8c550087793154021de0c5500877b2154021dac85500877a2154021de48550087692154021de08550086be6414021af590500873e5414021cf55050086de6314021b758c500875e5314021d754c50086fa6014021de540500876f5294b409f98e52d027d6394b409f98652d027d6194b409fd8d52d027c6354b409fd8552d027c6154b40db54852d036e52d0b40db54b42d02fa60d0b40be58342d036e5210b40db54842d02fa6010b40be58042d027f658cb409f99632d027d658cb40be98232d02f9608cb409fd9532d027d654cb409f19532d027f650cb409f99432d027d650cb40af99032d02bd640cb40f34c832d037751947409f98a51d027d6294740cf99151d027f62547409f18951d03755114740dd94741d037551d0740be98341d02f960d0740cf94b41d033d52d0740cf94741d03b651d0740cf54741d03b551d0740cd54741d02be60d0740ee98341d03b960d0740afd9541d033f6550740cf94941d033d5250740edd8541d03b75150740cf94541d03b45150740af18141d03765110740dd54441d03b54110740be98041d02f960107409fd9721d027
  | 18 => 0xd354c32087e6610c821bb58432087e5610c8219f992510873e64944218f992510867d6494421cf592510863d64944219f98e510867d6394421dbcca510876c32944219f597410873f54d0421cf953410873d54d0421cf153410875e53d0421d754f41086bd65d0421cf597410863d65d0421cfd4f410873e53d0421e794f410871e53d0421cf54f410879d53d0421c754f410873c53d0421cf94b41087af32d0421eb0cb410873e51d04219fd96410867d6590421af592410873e5490421cf552410875e5390421d754e41086ee6290421bb58a410867f6550421cfd51410873e5450421cf551410873c5450421d794d410875d5350421afd95410873f65504218fd95410873f5350421cf94d410879e5350421c794d410873d5350421e754d410871d5350421cf14d410873e5250421ebcc941087ac3250421edd85410873e51504219fd94410867e65104219f594410867c6510421af990410873e5410421cf550410875e5310421d754c41086ee6210421bb588410867d65cc421cf953310873d54cc421d794f310875d53cc421f3ccb31087b541cc4219fd96310867d658c421af99231086bd648c421cf952310873d548c421d794e310875d538c421bb98a31086ed628c421f30ca310867f654c421cf951310873d544c421d794d310875d534c421bbd8931086ec624c421f3cc9310867e650c4219f594310867c650c421cf950310873d540c421bb98831086ed620c421f30c831087b5410c421cf953210873d54c8421d794f210875d53c8421eb95321087ad54c8421bb98f21086ec63c8421dbd4f21087ce53c8421db54f21087cd53c8421d354f21087af41c8421eb50721086be6488421af592210873e5488421cf552210875e5388421d754e21086ed6288421db94a21087b74188421ed50621087b66488421ed59221087b65488421ed55221087d65388421f554e21086f56288421dd94a21087e65288421f9cca21087e432884219fd95210873e5448421cf55121086df6348421b718d210875e5348421d754d21087b74148421ed50521086ef6548421dbd95210866f6548421eb95121087ad5448421f3d8d21086ee6348421bb18d21087cc6348421b318d210876f5348421f394d210876d5348421f354d210874d5348421bbd85210876e5148421ebd0521087e64148421eb50521087e54148421e950521086f76548421ddd9521086776548421ed95121087b55448421f5d8d21087d46348421f594d21087d55348421bdd8921087e76248421dd94921087e65248421f990921087e54248421af99350086bd64d4021cf953500873d54d4021b798f50086dd63d4021d794f500875d53d4021cf952500873d5494021d794e500875d5394021ded42500867e64940219f592500867e63940219f58e500873f4194021cf506500877b549
  | 19 => 0x3530873d64d4c218f593530876e62d4c21dd987530867e60d4c21de983530867a60d4c219f583530877960d4c219e583530867d6594c21cf952530873d5494c21d7d4e530867e6494c219f592530867e6094c219f582530865d6594c21d7d52530875e5494c21e7952530871e5494c21d7552530879d5494c21c7552530875c5494c21f318a530875f6494c21d7992530875d6494c21d7192530875e6294c21d718a530875e6194c21d7186530875f6094c21d7982530875d6094c21d7182530873e5454c21cf551530867f6454c219f191530875f6354c21db189530867f6054c219f181530875f6554c21d7d51530875e5454c21e7951530871e5454c21d7551530879d5454c21c7551530875c5454c21f3189530875f6454c21d7991530875d6454c21d7191530875e6254c21d7189530874c6254c21d7985530875c6154c21d7085530875f6054c21d7981530875d6054c21d718153086be6414c21af590530873e5414c21cf55053086de6314c21d754c53086fa6014c21be580530867e6414c21cf990530863e6414c219f590530873d6414c218f590530867e6214c21db988530866e6214c219f98453087766114c219f980530877a6014c219e980530867d6014c21de58053086796014c219fd97430867e65d0c219f597430867c65d0c21cf953430873d54d0c21d794f430875d53d0c21bb98b43086ed62d0c21bd98743086f561d0c219fd96430867e6590c219f596430867c6590c21cf952430873d5490c21d794e430875d5390c219fd95430867e6550c219f595430867c6550c21cf951430873d5450c21d794d430875d5350c21bbd8943086ec6250c219fd94430867e6510c219f594430867c6510c21cf950430873d5410c21d794c430875d5310c219f992520867d64948219f58e520867d65d0821cf953420873d54d0821d794f420875d53d08219fd96420867d6590821cf952420873d5490821d794e420875d5390821bd98642086f561908219fd95420873e5450821cf551420875e5350821d754d420867f65108219f594420873e5410821cf550420875e5310821d754c42086f66110821bd584420867d65cc821cf953320873d54cc821d794f320875d53cc821bb597320876d65cc8219b59732087ae54cc821eb553320876f53cc821f394f320876d53cc821f354f320874d53cc821bb587320867f658c8219f596320873e548c821cf552320875e538c821d754e32086ee628c821db94a32086f6618c821bd586320867f654c821cf951320873d544c821d794d320875d534c821db949320867f650c8219f594320873e540c821cf550320875e530c821d754c32087cd320c821bd98432086f5610c821db594320866d650c821eb95032087ad540c821bb98c32087ce630c821dbd4c32087ce530c821db54c32087cd530c821
  | 20 => 0x86ee62d0521bb58b414873f65d0521cf997414873d65d0521cf197414873f53d0521e7d4f414871f53d0521cf94f414873d53d0521cf14f414879c53d0521c714f41487ae62d0521eb58b41487ae32d0521eb4cb414867e6590521af592414875f5390521d714e414867f65505219f595414867c6550521cfd51414873c5450521d7d4d414875c5350521bbd8941486ec6250521cfd95414873e6550521cf595414873c6550521cfd4d414879f5350521c7d4d414873e5350521cf54d414873c5350521e714d414871c5350521ebd8941487ac6250521eb8c941487ad3250521edd85414867e6510521af990414875f5310521d714c414867e65cc521d7d4f314875c53cc521bb98b31486ed62cc521f34cb31486be648c521af592314875f538c521d714e31487ce328c521ed506314867d654c5219f19531486ef624c521bb18931487cd324c521ed505314875f53c8521d714f21487b741c8521ed50721487d753c8521f514f21487e632c8521f94cb21486be6488521af592214875f5388521d714e21487ae6488521eb59221486ef6388521bb58e21487cf5388521db94e214876c5388521f314e214874c5388521f9d4621487af4188521eb50621486ed6088521d7d4f504875c53d41219f993504867d64d41219f98f504867d63d4121cfd07504873d41d4121b798e50486dd6394121d7d4e504875c5394121ded4250486bf6454121af19150486df6354121b718d504875f5354121d714d504875f5314121d714c504877950141219f990504867d64141219f98c504867d6314121cfd04504873d4114121b798f54086dd63d5021be98354086f960d50219f98f540875e63d50219798f540867d63d5021d758f540865d63d50219f98b540876e62d50219f987540877661d50219f983540877a60d50219e983540867d60d5021de583540867960d50219f596540873f54950219f98e540867d63950219f982540867d60950218f596540873f6395021cf98e540873d6395021cf18e540873e6295021cf18a540873e6195021cf186540873f6095021cf982540873d6095021cf182540873f64550219fd8d540867c63550219fd81540867c6055021cfd95540873f6355021cf98d540873d6355021cf18d540873e6255021cf189540873e6155021cf185540873c2155021cfd81540873e6055021cf581540873c6055021af990540873d5415021b798c54086dd6315021be98054086f960150219f990540873e64150218f990540867e6315021d798c540865e63150219f58c540875d63150219758c540867e6215021db988540867e6115021dd984540867e6015021de980540867a60150219f580540877960150219e58054086be64d4c21af593530873e54d4c21cf55353086fa60d4c21be583530867e64d4c21cf993530863e64d4c219f59
  | 21 => 0x3254221cfd05508873d4154221dbc8550886be6414221af590508873e5414221cf55050886de6314221b758c508877950142219f98f544867d63d51219f983544867d60d5121cfd5254486de6395121b758e544867e64951219f98e544875e63951219798e544867d6395121d758e544865d63951219f58a544876d62951219f586544877561951219f982544867d6095121b7d8d54486dc6355121bed8154486f86055121cfd91544867f6355121d7d8d544865f63551219f18d544875c63551219718d544867f6255121dbd89544867f6155121ddd85544867f6055121ded81544867b60551219f181544877860551219e181544867e6515121cf550544873e64151219f98c544867d63151219f980544867d60151219f993534867d64d4d219f983534867d60d4d21d7d53534875e54d4d21d7553534875c54d4d21f3d8b534875f64d4d21d7993534875d64d4d21d7193534875f62d4d21d758b534875f61d4d21d7587534875f60d4d21d7983534875d60d4d21d7183534875f5394d219f992534867d6494d21db58a53487756194d219f982534867d6094d219fd91534867c6454d21dbd89534867f6154d21ddd85534867f6054d219f181534867e6514d21d754c534867e6414d219f590534875e6314d219f980534867d6014d21b7994534875e6514d2197994534875f5414d21d7950534875d5414d21d715053487cd6214d21d7d90534875e6414d21d7590534875c6414d21d7d88534875f6114d21d7584534875d2114d21d7d80534875e6014d21d7580534875c6014d219fd97434867e65d0d219f597434867c65d0d21d7d4f434875c53d0d219fd96434867e6590d219f596434867c6590d21d7d4e434875c5390d21bb98a43486ed6290d219fd95434867e6550d219f595434867c6550d21d7d4d434875c5350d219fd94434867e6510d219f594434867c6510d21d7d4c434875c5310d21bb98843486ed6210d21bd98443486f56110d219f997424873f54d0921cf153424875f53d0921d714f42486f661d0921bd587424867e6590921cf952424873d5490921d7d4e424875c53909219f195424873f5450921cf151424875f5350921d714d42486f76150921bd185424867e6510921cf950424873d5410921d7d4c424875c5310921d7d4f324875c53cc921bd98732486f561cc9219f996324875f538c921d714e32486ee658c921db996324866e658c921bb58e32487cf538c921db94e324876c538c921f314e324874c538c921bb98632486ed608c921d7d4d324875c534c921bdd8532486f4614c921f3d8d32487cf534c921db94d324876c534c921f314d324874c534c921f9d8532486ec614c921f918532486ef604c9219f994324875f530c921bb98832487cd320c9219f997414873f54d0521cf153414875f53d0521d714f414
  | 22 => 0x221cfd91548867f63552219f18d548867f60552219f181548873f6555221cfd8d548873e6355221cf58d548873c6355221cfd89548873d6255221cf985548873c6155221cfd81548873e6055221cf581548873c6055221cf550548873e64152219f98c548867d6315221db588548877661152219f980548867d6015221af99353886bd64d4e21cf953538873d54d4e219f993538873e64d4e218f993538867d64d4e21cf593538863d64d4e21dd987538867e60d4e219f583538873e5494e21cf552538875f5394e219f992538867d6494e219f982538867d6094e21cf951538873d5454e219fd91538867c6454e21d7d8d538867f6054e219f18153886be6414e21af590538873e5414e21cf550538875d5314e21be98053886f96014e219fd97438867e65d0e219f597438867c65d0e21cf953438873d54d0e21bb98b43886ed62d0e219fd96438867e6590e219f596438873e5490e21cf552438867f6550e219f995438867d6550e219f195438873e5450e21cf55143886ef6250e21bb189438867f6510e219f994438867d6510e21cf950438873d5410e21bd98443886f56110e21cf953428873d54d0a21bd98742886f561d0a21cf952428873d5490a21cf951428873d5450a21bdd8542886f46150a21cf950428873d5410a21cf953328873d54cca21d794f328875d53cca21bd98732886f561cca21eb95332887ad54cca21f394f328876d53cca21f354f32887e661cca21bb58732887e561cca21cf952328873d548ca21d7d4e328873e544ca21cf551328875e534ca21d754d32886f7614ca21bd185328873e540ca21cf55032887cd320ca21bb594328876d650ca21eb95032887ad540ca21f398c328876f530ca21f3d4c328874f530ca21db54c32887cc530ca21bb584328873f54d0621cf953418873d54d0621cf15341886bd65d0621cf597418873f53d0621cf94f418873d53d0621ebccb41887ac32d0621cf952418873d5490621bb98a41886ed6290621cfd51418873e5450621cf551418873c5450621afd95418873f6550621cfd4d418873e5350621cf54d41887af3250621eb0c941887b76150621cf950418873d5410621bb98841886ed6210621cf953318873d54cc621f3ccb318873e548c621cf55231886ee628c621bb58a31887cc328c621ed506318873e54c8621cf55321887b741c8621ed50721886ed65c8621db59721887ae54c8621eb55321886ee63c8621bb18f218876f53c8621db54f21887af41c8621eb50721886f565c8621dd59721887b654c8621ed55321886be64d4221af593508873e54d4221cf553508873e5494221cf552508877b50942219f992508867d64942219f98e508867d6394221cfd06508873d4194221cf951508873d54542219fd91508867c64542219fd8d508867c6354221dbcc9508876c
  | 23 => 0xf54b41106bd6490441cf95241106f56490441dd95241107b654904419fd95411073e5450441afd95411073f65504418fd95411073e5250441cf54941106bf6150441cf94541106f76550441ddd9541106776550441bdd9141107b76450441dd95141107b65450441cd951411077b50940419f98a501067d6294041cfd06501073d41940419fd89501067c6254041cfd0550107764154041cf50550107754154041bb98850106ed6214041de540501067e63d53219f58f54c876e62d5321dd58754c867e60d53219f58354c873f54953219f98e54c867d63953219f98254c867d6095321cfd9154c867f63553219f18d54c867f60553219f18154c873d5415321cf99054c867e63153219f58c54c876e6215321dd58454c867e60153219f58054c875f5394f219f99253c867d6494f219f98253c867d6094f219fd9153c867c6454f219fd8153c867c6054f21d754c53c867e6414f219f59053c876e6214f21dd58453c867e6014f219f58053c867f65d0f219f99743c867d65d0f21bd98743c86f561d0f219fd9643c867e6590f219f59643c867c6590f21bb98a43c86ed6290f219fd9543c867d6550f219f19543c867f6510f219f99443c867d6510f219f19443c86ee6210f21bb58843c873f54d0b21cf15342c873e5490b21cf55242c86f66190b21bd58642c873f5450b21cf15142c873e5410b21cf55042c86f66110b21bd58442c875e538cb21d754e32c86f6618cb21bd58632c876e538cb21f394e32c87cd538cb21db14e32c86ee618cb21f998632c87e5618cb21bb58232c86ef654cb21dbd9532c87cf634cb21f3d4d32c876e534cb21db14d32c87cc534cb21d314d32c86ec614cb21bbd8132c875e530cb21d754c32c87cd320cb21bd98432c86f5610cb21cf95341c873d54d0721bb98b41c86ed62d0721cf99741c873d65d0721cf94f41c873d53d0721cf14f41c87ae62d0721eb58b41c87ae32d0721eb4cb41c873e5450721cf55141c86ef6250721bb18941c873f6550721cf19541c873e5350721cf54d41c873c5350721ebd8941c87ac6250721eb8c941c87ad3250721edd8541c86ee62cc721bb58b31c87cd32cc721ed50731c86de6394321b758e50c877b50943219f99250c867d64943219f98e50c875e63943219798e50c867d6394321d758e50c865d6394321cfd0650c873d4194321afd9150c86bc64543219fd9150c873f64543218fd9150c867c6454321cf19150c863c64543219fd8d50c867c6354321cfd0550c873d4154321de54050c867e63d52219f58f548876d62d5221dd987548867e60d52219f583548873f54952219f98e548867d63952219f982548867d6095221cfd8e548873e6395221cf58e548873c6395221cfd8a548873d6295221cf986548873c6195221cfd82548873e6095221cf582548873c6095
  | 24 => 0x41506be6090541af582415067e62d41419f58b505077b5094141bbd8950506ec6254141bb98850506ed6214141de540505067e6214141db988505066e62141419f588505076d62141419b588505073e4214141cf10850506be63d4941af58f52506be60d4941af58352506be6394941af58e52506be6294941cfd4a52507af5294941af58652507b56194941ad58652506be6094941af58252506bf6354941e7d8d525069f6354941af18d525079c6354941a718d52507af5254941cf94952506bf6154941edd8552506b76154941afd8152507bb6054941aed8152506bc6054941ee18152506b86054941af99452506be6314941af58c525073f5214941eb948525073d5214941eb54852506be6014941af58052506bf658c941af99632506bd658c941af19632506bd638c941e7d4e325079c538c941af98a32507af328c941af98632506bd618c941af98232506bd608c941afd9532506be654c941af59532506bc654c941e78c932506bf614c941edd8532506b7614c941af18532507b4614c941ad18532506bf604c941af18132506bf650c941af99432506bd650c941af19432506be620c941ebd4832507ac520c941eb8c832507ad320c941e34c832506be610c941ed98432506b6610c941af58432507b5610c941ad58432506be600c941af58032506be62d4541af58b515073f52d4541cf14b51506be60d4541af58351507b762d4541ed98b51507b562d4541ed18b51507b752d4541ed94b51507b552d4541ed14b51507b632d4541ed4cb51507b432d4541edd8351507b660d4541ed58351506b560d4541ed18351506be62d4141af58b50507b761d4141cfd4750507b751d4141af98a50506bd6294141cf94a505073c5294141ed58650507b75194141af982505073f5094141eed4250506bf6254141ebd8950506af6254141af18950507ac6254141ab18950507b76154141edd4550507bb5054141cf94150506be6514141af98850507ae6214141ab98850506bd6214141eb58850506ad6214141cf948505073c5214141ed584505073f5114141edd44505073f5014141ee940505073d5014141ee54050507395014141cf98a541073d6295041cf982541073d6095041dbd4a521067e63948419f58e521067e60948419f582521067f63548419f18d521067f60548419f18152106de6314841b758c521076d5214841be98052106f96014841cf953421076e52d0841db54b42106f661d0841bd587421067d6590841cf952421067f6550841cf951421073e5410841db948421076d5210841bd98442106f561108419fd96321067e658c8419f596321073e548c841db94a321076d528c8419fd95321067d654c8419f195321073e544c841db949321076d524c8419fd94321067e650c8419f594321073e540c841f34c8321073e52d0441c
  | 25 => 0x79d538cb41ebcca32d06be618cb41af58632d06be608cb41af58232d06bf654cb41af99532d06bd654cb41af19532d079e324cb41afd8532d06bc614cb41afd8132d06bc604cb41afd9432d06be650cb41af59432d06bc650cb41eb94832d07ad520cb41eb8c832d07ad320cb41e34c832d06be610cb41af58432d06be600cb41af58032d06be62d4341af58b50d07b561d4341af98a50d06bd6294341cf94a50d073c5294341cfd4250d07bb5094341afd8950d06bc6254341eed4150d073e5054341af98850d07ae6214341ab98850d06bd6214341eb58850d06ad6214341cf94850d073c5214341ed58450d073f5014341ee94050d073d5014341ee54050d07395014341dbd4a529067e6394a419f58e529067e6094a419f582529067f6354a419f18d529067f6054a419f18152906de6314a41b758c529076d5214a41be98052906f96014a41db94a429076d5290a41bd98642906f56190a41db949429076d5250a41bdd8542906f46150a419fd96329067e658ca419f596329076e528ca41db54a329067f654ca419f595329067c654ca41db949329076d524ca41bdd8532906f4614ca419fd94329067e650ca419f59432907cd320ca41bd98432906f5610ca41af597419073d65d0641cf94b419073d52d0641bd597419077565d0641bd583419077b50942419f98a509067d6294241cfd06509067f62542419f189509073f4154241bb98850906ed6214241de540509067e63d49419f58f525067e60d49419f583525076f5294941b7d8d52506dc6354941bed8152506f86054941db548525067e63149419f58c525067e60149419f580525067e65d0941af997425073e65d0941af98f42506bd63d0941cf14b42506be61d0941af98342506bd60d0941af592425076f5290941db14a42506f66190941bd58642506be6390941af58e42506be6290941cfd4a42507af5290941eb14a42506be6190941ed98642507b56190941af98242506bd6090941dbd49425076c5250941bdd8542506f46150941afd8d42506bc6350941ebd8942507af5250941cf14942507ac5250941edd8542506bc6150941ed18542506bf6050941af181425067e6510941af99042506be6510941cf99442506be6310941af58c42506be6210941eb988425073f5210941af98442506be6010941af580425067e658c9419f596325067c658c941afd9232506be648c941af59232506bc648c941d7d4e325075c538c9419fd95325067e654c9419f19532506bf644c941af99132506bd644c941af19132506f7614c941bd185325067e650c9419f594325067c650c941afd9032506be640c941af59032506bc640c941dbd48325076c520c941f34c832506f6610c941bd58432507b742d0541ed90b41507b542d0541ed10b41506f560d0541af98a41506bd6290541edd46
  | 26 => 0x54c8329bd95320caef634c832db94d320cbce534c832f3d0d320cbce434c832f350d320cbcc434c832bb185320caef604c832f3d95320cacf654c832d3d95320cbcf644c832f3991320cbcd644c832f3191320cbcf544c832f3951320cbcd544c832f3151320cbcf614c832f3985320cbcd614c832f3185320cacc614c832f3d81320cacf604c832f3981320cbcd604c832f3181320cbcd32d4432af992510cabd6494432f34ca510cb7751944329f992510cb3e64944328f992510ca7d6494432cf592510ca3d64944329f982510ca7d6094432f34c9510ca7f64544329f191510cb6e3254432db4c9510cb4d32544329fd81510ca7c6054432af990510cabd6414432f34c8510cb755114432be980510caf96014432f34cb500cbcd3294032ded42500ca7e64940329f592500ca7e61940329f586500cabf6454032af191500cbcd32540329fd91500cb3f64540328fd91500ca7c6454032cf191500ca3c64540329fd85500ca7c6154032af990500cabd6414032f34c8500caf66114032bd584500cb795014032b798f52d06dd63d4b41dbd4a52d067e6394b419f58e52d067e6094b419f58252d067f6354b419f18d52d067f6054b419f18152d076d5214b41db94b42d076d52d0b41bd98742d06f561d0b41af98f42d06bd63d0b41cf94b42d07ae52d0b41eb54b42d06be61d0b41ed98742d07b561d0b41af98342d06bd60d0b41af59642d073d6590b41af98e42d06bd6390b41cf54a42d06be6190b41af98242d06bd6090b41afd9542d073f6550b41afd8d42d06bc6350b41ebd8942d073e5250b41af18542d06bf6050b41af18142d076e5210b41db54842d06f66110b41bd58442d06be6310b41af58c42d07ae6210b41eb94842d073d5210b41eb54842d06be6110b41ed98442d07b56110b41af98042d06bd6010b419fd9632d067e658cb419f59632d06bf648cb41af99232d06bd648cb41af19232d075e538cb41d754e32d067f654cb419f59532d067c654cb41afd9132d06be644cb41af59132d06bc644cb419fd9432d067e650cb419f59432d06bf640cb41af99032d06bd640cb41af19032d076e520cb41db54832d07cd320cb41ded4250d067e62943419f58a50d073e4294341cf10a50d067f62543419f18950d06ee6214341bb58850d07795014341af98f52d079e63d4b41a798f52d06bd63d4b41e758f52d069d63d4b41af58752d07b561d4b41ad58752d06be60d4b41af58352d06be6394b41af58e52d073f5294b41ebd4a52d06be6094b41af58252d06bf6354b41af18d52d07af5254b41cf94952d06bf6054b41af18152d06be6314b41af58c52d073f5214b41eb94852d073d5214b41eb54852d06bd6114b41ed58452d06b56114b41af98052d06bd6014b41afd9632d06be658cb41af59632d06bc658cb41e794e32d0
  | 27 => 0x32cf550548cb3e6415232d758c548cb6e62152329f984548ca7d61152329f980548ca7d6015232cf953438cb3d54d0e32bb98b438caed62d0e32cf951438cb3d5450e32bbd89438caec6250e32cf952428cb3d5490a32b798e428cadd6390a32cf950428cb3d5410a32b798c428cadd6310a32eb508428caed65cca32db597328cabe6494632af592518cb7751946329f992518cb3e64946328f992518ca7d6494632cf592518ca3d6494632dbcca518ca7e60946329f582518ca7f64546329f191518cb5f32546329fd81518ca7c6054632af990518cabd6414632dd544518cafa6014632be580518cabe64d4232af593508cb7b50942329f992508ca7d64942329f986508ca7d61942329fd91508ca7c6454232dbcc9508ca7f61542329f185508cb7950142329f987544ca7d61d51329f983544ca7d60d5132cfd52544caf66195132bd586544ca7e64951329f58a544cb6d62951329f986544cb7661951329d986544ca7d6195132dd586544ca7561951329f982544ca7d6095132cfd91544ca7f6255132dbd89544ca7f61551329f185544ca7f60551329f181544ca7e6515132cf550544cb3e64151329f984544ca7d61151329f980544ca7d60151329f997424cb3f54d0932cf153424cade63d0932b758f424ca7e65909329fd95424ca7d65509329f195424cb3f5450932cf151424cadf6350932b718d424ca7e6510932eb508424cbcf528c932b7586324ca7e64d45329f593514ca7e60d45329f583514cabe6494532af592514cb775194532af990514cabd6414532dd544514cafa6014532be580514ca7e6414532cf990514ca3e64145329f590514cb3d64145328f590514cb5e32145329f980514cb7a60145329e980514ca7d6014532de580514ca7960145329f993504ca7d64d4132d78cb504ca7e61d41329f587504cb7b5094132afd91504cabc6454132bdd85504caf46154132de540504ca7e64141329f590504ca7e61141329f584504ca7e62d5032db98b540ca7e61d50329f587540ca7e60d50329f583540ca7d6595032cfd52540ca7e61950329f586540ca7e60950329f582540cb3f64550329fd85540ca7c61550329fd81540ca7c6055032cf550540caf66115032bd584540cafa6015032be580540ca7e6415032cf990540ca7e6215032db988540ca7e6115032dd984540ca7661150329f584540cb7561150329d584540ca7e6015032de980540ca7a60150329f580540cb7960150329e580540ca7e64948329f592520ca7d65d08329fd96420ca7d6590832cf952420cb3d5490832b798e420cadd63908329fd95420ca7f65108329f994420ca7d65108329f194420cb3e5410832cf550420cade6310832b758c420caed638c832b358e320cb6e538c832f394e320caee618c832bb582320ca7f654c832bbd95320cb6f6
  | 28 => 0x58650d0a7f63543429f18d50d0a7f61543429f18550d0ade6314342b758c50d0af66114342bd58450d0b795014342be9835390af960d4e42d7d4e5390a7e6194e429f5865390a7e6094e429f5825390a7f6154e429f1855390a7f6054e429f1815390b5d5314e42bb98a4390aed6290e42af5974290b3d65d0a42af5874290abe60d0a42bb5974290b6d65d0a42bb5834290b7751946429f98e5190a7d63946429f9825190a7d6094642cf5915190a7f63546429f18d5190b3f42546429fd815190a7c6054642b798c5190add6314642dd5445190afa6014642be5805190ade63d4242b758f5090ade6394242b758e5090b7b50942429f98e5090b5e63942429798e5090a7d6394242d758e5090a5d63942429f9865090a7d61942429fd8d5090a7c63542429fd855090a7c6154242de5405090a7e61d4d429f5875350a7e60d4d429f5835350b5f5394d42be9825350af96094d42d754c5350a7e6114d429f5845350a7e6014d429f5805350b5f5390d42d714e4350aee6290d42bb58a4350aef6250d42bb1894350aed60d0942ebd4a4250abd6190942cfd935150a7e63d45429f58f5150b3e42d45429f9835150a7d60d4542ddd465150adf6354542b718d5150afb6054542be1815150b7551145429f98c5150a7d63145429f9805150a7d60145429f98f5050a7d63d41429f9875050a7d61d4142b798e5050add6394142ded425050b7950141429f98c5050a7d6314142cf9085050a7e61141429f5845050b5f5394c429f9865310a7d6194c429f9825310a7d6094c429fd855310a7c6154c429fd815310a7c6054c42d754c5310af66114c42bd5845310afa6014c42be5805310b5e53d0c42d754f4310aee62d0c42bb58b4310a7d6590c429fd954310aee6210c42bb5884310abd61d0842af9834210abd6490842cf9524210aed6490842db9524210bae54908429fd954210abf6550842cfd954210a3f6550842afd894210b3e5250842afd854210abc6050842bbd954210b6f65508429bd954210aef6450842ebd914210b6e5450842eb9514210baf4350842eb50d4210b7751944429f98e5110a7d63944429f9825110a7d6094442cf9915110a7f63544429f18d5110b3f4254442cf5095110a7f60544429f1815110ade6314442b758c5110b755114442be9805110af96014442ded425010a7e63940429f58e5010a7e61940429f5865010a7f63540429f18d5010b6e4254042db5095010a7f61540429f1855010ade6314042b758c5010af66114042bd5845010b795014042be983548caf960d5232d758f548cb6e62d52329f987548ca7d61d52329f983548cb7a60d52329e983548ca7d60d5232de583548ca7960d5232cfd52548ca7e61952329f586548ca7e60952329f582548cb3f64552329fd85548ca7c61552329fd81548ca7c60552
  | 29 => 0x40010010001000001000000070004003000c001000000000240050008003000400100340000010016000800000000010000000000000000000000014000000000200180000000000002c000000800200200000000005000000000000060000001000800a000c001000000200000000050004002800200240060004000000001c000000c0004000000400300080000010000000c003000000100000000000000000000400080010018003000400200080000000003000400100000000000000000000700040000000007000c0030000001000000000100070014000000c0080000000000000100040000000004000800a000000300000060000001000c001000000000500040008000000000000000020004007001c0000008006000000100040020000002002000100280000008000000400200040090000000000000500180030024007000400200000000004001000800000140000004001000000500000010000000000800000040000000001000000200000100008000000800100040000000000000800200040000000001000000200140020000004001c0000004000000c001002c00400140000040000001c001000800100040050004002000000000000000008001004400200080020004000000000300080000008001000000100000000020005001c00400000040000001003000100240000000000001c000000c00200000000004000000c002000800100040000008000000000200140020018000000800300000020014001000400000000000000004000400a00000040000000000000100040020034000000400800000080008001000800000080000010004000800000200010000006001400000000000004000000000000340060004005000000000080020010002000801c000400200040020000000001400400000000000001000000a000c000000000000100060040000000400400080010004000000000400100000004002005800200080000000001001c000000000100000000000002000000e000000100040000004002000000200000050000001000400100080010074000000c0000000003000800000000050004000000800500100000014002000800000080050000001000c0000010002000000000140010000011000c0020004000000000000000000028000000c00200000000014001000c00000080040018000000c00500000000066f661d4f42bd58753d0b5f5394f429f98653d0a7d6194f429f98253d0a7d6094f429fd8553d0a7c6154f429fd8153d0a7c6054f42d754c53d0aee62d0f42bb58b43d0ade63d4742b758f51d0b7751947429f98e51d0a7d63947429f98251d0a7d6094742cf99151d0a7f63547429f18d51d0a7f60547429f18151d0b755114742ded4250d0a7e63943429f58e50d0a7e61943429f
  | 30 => 0x20000006001c00b000000100180030018001000000c000000900500000008004000000200000010030000000000300000000008009000400300080000004005000800000100000018000000000000000020000000000000a00000000014003000800a0000000000400100000030000001000400200000010008006000400000040050000015000000f000800000240020028000000400100000000008007000000c0000005000000100000010000000001400000240060000003000400800040020000001000c00500080010000000000c00300000020074000006c0030004003000400000040010040000000400000080030000002000000400000040004001003800000000010008003000400300000010008001000000c0014002000000100040070004003000000f000000e000800000000000018000000c00000040010000000000000000000010004000000000100000090000000001400900000000004004005400b0008006000000c0004000000000000000010004000001000700080000004000000400400000050008003001400300140060000004002000100040040008004000c000001000300000000004000001c0040000000003800100080040020001000400000100020008004001c001000c0040004000001400300080040000004001c00300100010000012002400200040030004000000400300040010000000000000500080020000000000000300040060004000000400000040020000001000000a0000000001400100000020014000000800000000000008003000000e0004000000401a0000002000c000000400a003c005000800300100000000001000000800040080010009000400000040010000005000c006000400100340060000005003000600500020004000000000800240010008004001c009002800000000010000003000000000000000004001000000400140000000007000c0000004000003800400000040004000000400000040100000001000000000000000000001000400400040060000001000c0020018001000000b00000000008000000000700140010000002002800100000020014000000400500000030004000000c0010004000000400200180010000000001000000080000000001000001300040060004001001000b0004000001c011000000400000010000001001800000000030004004000000000040000000003000c0000014014000400000040160004004000c0030008000000800b0020002000c0020014002000400200000040004000000c0000000001000800f000400f0008000002000500000000008000006000b002000300080010000000002400400180050008000000000000000060000000000c006000000e0024001001000000140070008002000c001000000100
  | 31 => 0x140000000002000c0020000004000400800240010000000000400600000040004000000800700000010004000000000000080000000001000c0000010000001400400000060024003001c00100000000000002002400300000060008000000000200000010004000000800000080000004005000400000000000000000000000900180000000000000400100180000000002000000100000010000001000800000040060004000002400200000040000000000000100000000000005000800000000000020000000000100140000000000000c00400080000004000001800700140000000000000400200000000000002000000200000040004000003400300000000008000000000000140000014001000800400100000000000001000200080050004004000c0040000004000c008003c00200040000030001001800000040010000012000000400100010014000000c0040000000001c0010000003000800300100050000001000c0010000000000000000040000000003001c006000800000340000000005000c0000004000000c005007000000000000010001000400000040020000008000000100200000004002000400100080000000000000000000000060000001000c000001400000180080008000000000000040000000001000800b00100050000004000400200000070000004001c0010010005002c000006000400100000000000001c00100100040000002000000300180010004001001800200100020008000002c0000000000000400600100040000000000000f0008000000000000040000000003000c00000000000000004000000000080000008000000000200000000000005000c0090008000000c005000c00e000000100080020000000000400000040010000000000400500000190004001000800000000030030001000c004000400000000050008001000401200080000000004000000d00040020014000000800000000070054000002c0000024000000400000140000000001000000100080020000000000400700180000000000000000000200000034001000000600340020000003000c0080008000000c002000000000000040000006001c0000004001000c0000000001000000000000000010001002400000000010008002000c0000008000000400f0004003000800100080000020007001400600880030008002000c0020024002001000100000060004007000800300000010014006002800000000040004000000000b001c000000400200040040000001000800300000010000000001c001000c002000c00000000010020005000800300000000000003001c0000018003000c0000000001000000600140010014000000800200040020000000000000400000000000000000000100140020010000000c0
  | 32 => 0x300000040008003002c0010014000000c003000800100000030000002000000000040010004001001000100000000014000000000000640210014001000c002000000000000010000000000000800040020000007000000000080020004008000000a00000020000000000800e000000000000000000000001c0000004004000000100040000000002000000200000000000000000400c0000000000000000040000028000000c0090000003000000900000010008001001800200000000000009004400000040020010001000000400100070000000000000100000000000001000400600000000004002000800700040000018003000000100000000000000000800100180000000000000800000080090004002000c0010010001000c00500000000008000001c001000000100040000000000000000e00080000010000000c000000000b001c00100080050004001000400500040000014006000400500040010004000000000b0000002001800d0004000001400500000030004000001000000000040004004001c00600100020000000000000500140050004003000000000000020000000000000100000010000005000000000080050010002000c00200100010000000000c000000000200000000004002000800000040000008001000000200000070000002000000300080050000000002000200040010048000000000600040010030002000000500000010000000000c0000004000000000000040030008000000000100080000004000001000300000000008002000000000100010018000003000000000000008006001400000000010000001000c004000800000180000030007000c004002000000000110000000001400100000060008000000000100240020010005000400000240020004002000000300000000000006001000000080030014005000800000000000014002000400300140010004002000000a00080070000000000000200000010000001000800100080000000002000c00200040010000001000c00000040020018001000c002000000500000020030001000800000040070004000001c0010010003001400100000000000005001400200080010004000001800600100060000003000c0010000004000c003000000300000000018001000800100000000018001000400000000060004001000400000040000028000000800000080020000000002800b000400000080060008000000000000180070050000000800100000010004003000400200100060000001000c003000800000000040010000000c003003c00600080040000000002000200180000000004000000000040000010003000800000000000008000000800000080010000007000000000040000004000001000100080000000008000c0000
  | 33 => 0x19a200000000002b6000000000001fb604c00000001f7689aa8ba84e2038000110476e87d600000005f180005b60000c2d16172d7900271fae4a000000000016a100000000000000259c0000000000000011038f16420000000000000000000000000000a8d930e000200000020b8000000029f00006f1800000000000000a250001b4800000000000000607800098daefa0000000000000051aaf4c27110dc3d207660a79dda00017c26f600001450f0600003cf0000dd4000000000000000001a3a60a8000600800000008ea02f237a9320000b23849d0019cc089206a86caa5680002b04000286d0911e340001a4a3788b288eb400022b1dfe56940000000dcc938170d0000bb10000000a58119c00000000000000973a0b1000000000001180000000b9e169a000000000000009e32b08296209055824ee01cebbc75b1c244530cb6000235e0a92f17b14800000000000000000000000000019720000000b558c32a14219c29519520000bd400028dc3f507dc0001c660000000805a556000023a65c40004a1800034ea7ec5cc283641bad1e7ef00000000000664a2e1890844a00021060001db82de95d683e10ca000033a00000008b5800000000000000004001c00500040040004000000800000080000010000000000000040060000002000000100040020000002000400400000000010000000400000000000000001000c006000000300000030000001000800000000010000008001000200000000008001000400600000000000000000c00500000000004002000000b000c000000c0000000000000c0050000001001000100000040000000000800200000060014002000000200000040010000001c003000c000001c0010000003000400200000000000001000000000000010008001000c00100100000014001000400c005c00100200000000001000c0010014000000c0010030002000c002000000000040000010004000800600000020000000000c000000000100240010000001000000000000020010006001c000000000000080070000005000c0020018007001c00400040000004002000000200040020020000000400a000000000000020008004001000f00000000028007000c00000180000008001002c0000010000003000b0010000001400200000070000003000400300000000000001001c0020000001001800000000000004001000400700300000008000001c001002000400080030000000001c0060008013001800000000000098000000c000000800000000000000002000800100000030008001001c003000000000000040000004000400100040000004000000800000040000000010000000100080090024001000000b000c005000400000140020010005000000000140030008005000c0090010
  | 34 => 0x3d0d7a25517c38ca2c160001f8a0000000718800000018a36ed8000000000095e7039000017c3e51a208061c6c99985126c5800000028ea1cc800036b800000008f092300000000000c0a80000001b0e3ce8271bb10ddaa3f2d0a00009aa00022ee0001a050001cec4bd2fa03e1000000000008664b6c0000000000000000024c66ac80003efad7c0002c1e0000000736000049c0612874920e7f800005bc989d62e00009df00000000000c3a918200028310000355094c000107ae5e0001f4321e94b01f68000bd180000000000455c00000013761a02d06000134e96aa4517858000992000064b4000000257e83a00000b9962b62949a60002552305288c000000005ae39224556760002780c05000044600000001b34afa2168000000012d800000000000002c2f6138000baba3a60000ec295d4000000171c9f64db200012140002962000029100025d470380000001f2300009180000f3500015fb000188619f820c649c8bfa25000000000000000c89000000025b5c8e00012c0000000051c0c640270b93000033cad3117e00006660002f7a73680000000000000000000000001250000000000092da23a8f9c0007d140000002e5a0001646000000000000000001b8900020ac000105833d0000ab89f4f00013f000000004d308d8a9895a059489c100000585e68af2000000000000000000000c3f80000000000000000000027400002c98b1f139c079c00000022be97200008b940003d5c00079e2e983b480005558000037c0000000000000000000000000000000235000000000002e6df4e4c4dbecb5a0f2448f80009dd000000000003e8000053d21e257dc000405800000025bebfb03698baa0e5092ad200000e4038da63034980000000c5c000272e0002dab0002f3c000000000000000001760a88af28b53035ab98014e698800066aab06560214432ca74800000008188000459000021c80000000000000000086400002e4276700002db0000000000000000009f68daadfe46a231db3e00003bf9e68b6997a600025043564000000130d00000004998000051e31b0001c3600000000000000679800085a87d8277000000003644bc000000000005a70000000000000023d6000000000030709c48000000000017fdab42ed80000002b740770104b062eca1e48d40b69026200522b63a4a5240001cd2bb82efc57aea4457199cd000183ea4600002e3ee8a00017ac26d1eb801316cead380ad265b0c8a8901cd3cc14491360b4e000000000029b2a3b93b039400000001c580002f6a0000000000129b8d2c0008e60000b68d11a31a00000000000313a5cb1fa19b409681f60000dce1d302bc9c92158039060c00000000000a49753800094380002c88000000000044f05f06586e134a023fe00000000002e9400000005de0000
  | 35 => 0x6769a71455b22d410440001f0607e000090b0bee9242f46bd800000000000a104ab872434a2937b62a7830000280498000007800005471bfa4baabfe7c38f558cf800000029354678000000142000000003f2400047f637117e800061a000067b800000000008a726fe1ae9ad200016a354811f49e10e94ba11bca00000000b4082f000000017f21be30900005788cdd0000000000000000021bc2062a7b9161ed68282c8abc38bdaa46966c4bf800000028ed0001112054a43c98a0000bad00000000000000000079ba89a94f8000000194dc14000000000000001cdfb88910e0000000000000040a00cdaaf2aa0ab9800058e88cea1ba8e6000035b0001bab43780005dd15149b41d1860b99b20ff07c477d240a6accfc1116e3ea86247f83f69bf42eb0eb0b5dadce04c80000000000aa380000000000694800030d80000000000000000000000008c30000000000000011610000bee2af8bff0000000000000000000002bfafdea75000000000004f00000345a7dc00004e81bc0000643c0ac05da8bebbc8000000000090fc00000000000000000a12800030d238e0000770041400090e800000000000000000000035022e800061d0000000261c60400000002b506c9a864b3f80000000000795099b0000000909a39c8078000a00800040523a500008232e2d5f138b137027828f2000006ab4d0000000123a4f6303870a0fce000000007094be0001b7093a80000ab4000000000000000000000b98461adf282b40001930000080ea0b000032a528e3abac480005850d35152000062380000000000000000000000000001b2e00000009240f200e2000000000000000adb00000005c180004e16db00000a0e8b9d45a4212a08af8000000010000000000000000000024a40000000000000000000000001e2c051174070129ea05c80001021af837b246a854cba000000000000000000000000027da00003d20000000000000000000000002e3a00000000000000000000000011d420923820000000a68849c0001e4092587d766d96570002238000305830680000001b50000229e8ff0000000000020d4000000000098aac7a000000000000008c19be200000000002470000000000000000002f060002e1200000000000000310da68206800000017708d004b2000000028caa4805925900000000923800000f800019780000002917000000001c1f8800002ffc292e9c8cc22eb00000005f29d8c000000000018f4b0c6c270000c9eaaf80000604d460000eb41b28000a772fcb449de8200009ffa3940008b68000496800000000009d1800035c98f049c800000000009c700009208228000000000006c8610c000000000000000009210000000000000000000000f5200000000002316000000000000000001ede40c00000002a762c00000000
  | 36 => 0x12e2000216e899188900020b60d45b36000000000000000001af28cd80008ea2e46a60c8e864530926408000aee2f0d7438000b6e0000000000017c8000ada0000000170b0000000a8046b701acbc38a000000002d140001e4a000000000000007b2800000687f660a0000719000000000003cd000032300000000000b7d0000000000015d000000000000000000000188798829fa1039d7c0001e5e0000000000209600023f216c40000000000000000000010f00002f78000000044ec00064b00000000bcd000000000000006850000000271602180000000000000000000000009e795ba90e000061818380000000000231422a5b52b1a21d404305a8ae7c0000001d88b6b400000000000000d4a0002f84734665ea7d128d055c0000000000517b04405e012e000296e7fe4000b5780000f30000000000000000000000d0e0b48dd8a7c00000a0871a1d7ab7e0b201264408ac658117df85c22a2c43852e0001ca30000000000240e000000038c02ec000039539b0000000000000000009dd8000000000003780000002dfc2871b54b67993c436800000000000001bda09600000002bb09b219360000000af4000009f426d00fc0000ee97ee2224000a74afae00016ca00000006c6aada801c0000000d56bba800051193a000000000002c2200017a40c3e77800007343a4241e073a2df8ea86191ef4000ab5848e227c0003450a8a000000000022e600000f800009ed78b80009b63028bf982290000000000129600000001d818f5377000000004520000638000000095ba1eec2e000028b8bfc44f8b54000000000017f804b000066103e03f18c5835f1c4c00006580000b01abf1f2840c8000abce3e83a2000000021260600fdbb781fb9821870c59c9d1e698190a0275f08a70800000000006a58000000000039d800064600009f51c081eaabec000033e7410c9d8cb84683cc9fde8448c5312b2fdc60705a29db80006d800001dd1d100000b340000000000272c0c2a9f70002e5800000007f8400000014aeabc0000000000000000007819f81103c000000066e86bad043c10d32980909f00002014b99ecc96b0000a7200000001abe00027ba87080009bb907ca6712a02a1941c32e178cb49976e09b8000a50abdcbf20000609000047900000000000000000020a2b91ad518d884b5da47a1800044280000000ba8183cea80000000000057f36e000006400000000e3e000098222f800092280004659a5a4dbc0000f0177256db0e87e0000047c04c22f2a534000059a000000087c20d86ec8c95000000000000000000000000166eb45cfd0911226c8811869000070db7618224e093e400000000000d706444000a701b2c70600000000000000303382c12286402898bc4c45a00029c4a7f966414fc23800000004358a2c5432160000108
  | 37 => 0x15e1d4205fc0000000000572800000019ea00000000001d464789048000075254c9bcb000000006200000000b9a00027278f11c2a4c3000008992e78ed80008948000843264c9d5a92e00001cf00023d20001392a652d6b5d4979dbd3504c17f800025480003d6400000027d82a82bee00000008cdc0001f429264241f4d5785940b408000000275aadca032a6d1a649ac00004b283e462780000000000000000005e8000000000052d2fd3000000000001d4081948022f40006fdc6ea63dc000000000000000007215283337c00000003de9c9888c97bc2f23fab06400000a400000000000b88000075600000002261256000000000009120000f2bc28800000000003260d1855a99ba00000007ab88400e5000054d8000a9c6e56a1680000eb800000000006e5000074b9ef681122f64ee2d66000283200000009cc877c24d800030995f873840001048dbe60e557ea13897a03e9c06aa6800092f153464a000088b9aee9d4d3e00000000519942600000ea8dd800024e8ada41d0f659638f008d5400082082980000a9600000000000f1600021300000000a5a800078980000000000000000000000000001c3a000000000000000000000029a65800000000000000000028f0000fa6443211c50cc7586094c480000000000252c0e807ea64350ad596000000005c422da19eabb1ff844c6a290000a280000000350610aadfc66c0c7800000029b800000002708b4800000001d50b2e00024782804000be79c161fd479862d000000000000000000000057b000151a000000087f80000808000c3f00006e1000031146cf79c80004a7230a08f00006b9000063cc00000000008680000616dcd40fc8d7e8738000a28000000000007e780000000000000000000021d5af8a27870f89a46b41c489a1000000000008f796fa0000000000008e11d952c02e44070000000000000000003800002f1486d80002320000000000039440005946f3e00000006c21832754285e1ff86102f9800000000000002d980002c4c63c400000000000002de2188ac34000000000000009ca678200000007aa8aacba786940e18310a2d1d6498753ea27adc34055950ec138e46000079e000039c5bf27c960c08c0134aba603f200a9db07f300004ae53c0d9c000123644e00001988000b3b800000021da7279f66a451954add4cb42610000a5a0000bcc800000021628c120d14c70000000000075201a30ff918e000000000009320000000812944e14700002d718840002b9c34c152f4ff0ec01ee9b04000000000000000000a34000132255c0000a12000000006d100000000000000000000000001020000a23000222286525168039f220001327644c00096319d88be0f786c4400000000000000ba650a2b76a40d8a200012846b88000a69000000020fe026800000
  | 38 => 0xa2e72200020a6000225600000000002a1f20f8000c0c800000000004df2b000000fdcaa780002feb0e418c30106e40bf674b00000d2400058680001780000000000000000000000000000016f00000002ba23da00009c700017f175300000d61e320002f1100000000000000000168a000000008d853600027083971e36000223207f0d1b8c059d10001caa0bd280000000009bf000004d000000000000001a8a08280b8a4c26b4c04a1a20001d409508000000000044805980002d2400025c673d11ab4780000388000063200005e0176a2aaa35c59280000000cfe000000000000004c0213e81800005fbc0000000000426400000014fa28158dd000000075e82428968000000000000000000000000000000000000009d504ca000000069b26ae2018c4205400ce4740ae60000000a2f1acc017241627796ec75601ac00020d20002d4600000000000aa8000237f0000000015400000000004440000000000017acda88bf961f9fb800045000cb00000003338000000201c000000000000000000000000000072b000000000005150000000000000000e3000000000013411054000939800082a0b3bc21800097b16600001f5700000006b94e785cd1af4000000094ea9e04de537e00003aab109644000000000000c009e800000000000948000159060e6c7000000000000001fc60000000afa800099d000000025c4bea000000019cca90a5c141e149cb28b06e0000b3213300003ad8d4d00000be0001c09a6480000000000000030628e4000000302600000000001c8400000007dd00004970000abbc0000000a4c782907e0000000417ada20279c120000000000000076d00000000000b8a8068bcaae14000000000000008d4000058e000071f169d0000000658000000000008d8a14a241287b88b0000bda14ba7f2001847587a20044c56687d8db2bbc0004ba2b38229a7fca7a4fe0000000050880000002597a62a6b6b25826aab4147c0001499000000000013de00000000001d050000000000097900012c81938000000000000025de0000e2e68580000000000000000067e0000431981300008587d58000000100c00000002a90000bb5439a000021888d1dd870f15fe3966fb65a94d2463561a9000287896e88de00022025cf81b410f80004fd87fa75980000000000000000000000002c6965c0001ee479f0000000227e322000000029820001a2e96700000000000b5a49d2c250d200000000be5a37eaf79ad64e52554053c00000019f600000000002f8a716a0f200009e40002047b9ad3ae00030a8762908c0b258dc37f0000a44800049400000b7884a0000b83045007c00021660000000ae79c380000000430c000000003c00007760be400076c80009a4111458d670a92b250089d80000000000224c00000006bd30ec000c2680
  | 39 => 0xb17000086200000000000000000153818ec0001008000717149a5708fa227a26aab232b420002d8f54900000002cc0a35800000000000000390b42154a9cc2b2ebf6124459f8fbc2e049585a4800002240000000000000000000000007d100e887980009a6809800000004a900000001ae70001f7590700007cba98813c8e3250905665c1400000023be20899e50000000384a2ec000185500000000000000ad90000000000031487d20002148000010a00000000001bff6ef800000028d800012f23181924500c0000000000000232c7c9d4de0000000ad006761b24344000145168680008b9000000000000000000000177a119060600000003858000339d79477a80000000aca000000000015e853080000000c7a0001b3000013f94fb87085f39e306f391da98c47c278680000000000519d3cc5739e9c0c5c00000022b2bc7af4014a970e0000000b9a40000001ae6000000000000002cdafcd000000000000000001b4c9eb196c00016b238400008009fbf1878000bb9000047f00000002f7c000311056ae0d48930826055654e6eea7506e38e4900013320001a80000012faa6089956090bfa47a600a1f1c210000000000152783b00008bfe8c881aacca00007ee00002da48e0000000000069c21f200006fa8d680005d780008ce14a09830d2aaf301a80000c6216bc000000000000000000000000067886c6531374000000000021644eb400056f45c6590108a7efa7e2000211800012048848f1c0720000000000000028fe09ed7321e810ba851ab6abaaa5b734f9cf84544c1d1891f2fba140001a98000afe02578ec800000000007a488c2000288a3920cbea89cde00001985677800007304541619a45ba0ca0600027cb0a5db142e10520b5403f733a800093c0c22337000020a80009152208bdc000069180000000000a8680002d4000000000001aa8ac29f383a881daa5c106687200000001488000b8808bc0001b3a0000000000000001d95f25b59d12000000000000000000a720000000bf396dc000194e00000000000000000000096d000000019dc0000ea2bb4000000000005ba80000001be40000064000000000000000fe085c00008b80001a40bd8813f4be000019e07ec178a3c0000000085e28ab0000000000000063f1c916be841400000002f5a63e00027be000000000025403d6800000027360a8800000006926790000000169b71a2ca0a211678c1727bd8fe80c407c2f8c58d80008ed0b183bdade60001f1e00000000000000000100f000000000005760000000000000000016a64afa465b9467646df10ac00000ef455000079826c4b2180008e591e60001130000000022cc0002330000000000000023460000b66be880005fb2f360000000b6bae86abb99e291880002e8c000a6dcdca037000042b908000000004
  | 40 => 0xd390000000000000000000000000000319c00000000000002853aaa89383d8e7f8a39de50282159e67a0ca031119ec4da8cdaa668d09bc801a93fc1921003ee25bd22df75b10b7480495fa3a585d237d82780002f090e30000000112247d8000000000000000000002ffc000000000000000000eb2000000000000000001246000000091a0000b7b09341861d38000000051e168cadcc00094a80000001f20abec0009b9000000000001b3069c000293aa3be8ecb0e9b6e24b05ab0ba17376c78c3f5731ef415f8f5300000000000000084d6c000000008d100003b223ec0002fb224c2d106bf8000223400000000000000000000000000000000001fdc2de40000000000900562c000301a00018667cc8c122742fd1645c000523000057b80000000000b71ed8836887ca0000000000230ea4e4096b2704c651b8000160855f0000a7e0000e58000000000000007fd0000000000025b152200000000002d5800000000000000a75987100000002398000000000000003c80000e75000088e00000009d0c00000000000002d9a31e0660656800000000005c130a9665aa0900000000000d3c00000001358000420c0000000000000000000000000000000b12800000000003bb15d4000000022c94a40000000baf89a200011160000000000149600028885548c8600000004c2c0005639b4202841df8f9a97e00013fb40d26d43312a1d61b000031d800000000000000000000000048d05507e69ebe00002d50000000172ae76000096a75f80000d080000000000b3e998c46e919a1926a0a8b8ab16714000000000003236e5403800000c480000000000000275f00000000000000000000049f000000000221de8170380800000018da2c526229621c0a4748ad16c3c0007ecc000b72a8fd8742d7516f11be4b70000000283800024ecbb3849300022fa48a4000aed4f730002aa80d65f6c0000000000000000000000001a820000000000000000003010000000000000086e82a042399200000bc58868cc8b48a0549280000b0806b1a662f6ca010d54a3e95949d78000000160f3bc00000000000b5299fa7fedd86a31800807280000000508000000000000000000000000000000029103ee9a11000187a00000000000000987a176000000000000004128e064d58b46ad9ac5c1429f2a3150000606c0000e900007378000000266c000000056ed129000000000013b2000288e52f14ce919c0008d380000002b6b83699f0000066a9948ce1000185e02ac0000000000000212800000000001f8c8f523b00000000000144200000000000000b0100000001b729970f7a34b800000000000700b1c00009feade120c000000000025b65c0800004a240258f93660deaf00a4ce2a4805000000028a86268000000000071b800008c0dc2a7daac60001
  | 41 => 0x80000000000000000060164500000182000133a000164e00023726d58e1800a0530000000000024e81b900006048000c0f000069e20fd28adbd07040dc100012266bfe2e800000002000a034b19fe7b7906505f3e94b0000000a801e020000000000032b00000000001b4e036800000000003b3032279c06ae00016de29a889b00008d07b0990c0c994055210db081785547fc833429c15f69ce14e46468e8697e8b299709d74c3784aa82cabc457e700ea14aea4000000065bc000000000000010fbac380000000000000000000000000000c8e1731ada0c380009e8800000000004d2000000000009bc000000000006ee24880002422724000003500008c4000000000009d86e28919000000025f27d48000c3b81d80001eda0000ce62f380005904000b2f0000c33ab6f1eac00075500000a4c00009225e26e6694700000005fe800065a543d00000000002d74000212a000294c42f1a8c3dc5b7a0001384000000000000006d79be8000000000000001b713520000000985ccfba38c0000975c3200000001d40e22000000000006339c600001fc2c020d2a760410059c000000000000003200e7ab09400017d0000000000000000004d181a60000269000174200029e218b000066a0d745858a5a2408f4030e8af1ba021c62a125b8300c3b091f07f4aa597860002bb4169223c37c8bcc0000274a5680006629064a45800059143a53ab22008030714000191db1d8000a8800002e75c7a5fd80008278000000309c0000000222a4a20000000000072a3dec0f009066e60000000000000000000000000000058a5e600017140000000502000000000000002b5a3d417ae791122e02c8cba305c0000a75a4c752a5e90002030000000033a432c8f880000002e1800016a000003e26d024fe51e9cb400020bd79700001aed83c43821e8725abc6a778d9e9cf00006f9400098620e67758000214af8e337a0d5c24089e4330000570d299b5b966a21a927618fa49449600000b00000293987610d005388700008250000aea8000000000099280000000a4000000000000000000208f17912ee000000000022fb00000000000000000161c90b17c88cbefea9da4d42b770e9e635926813d800000016b40db800004180000000000550c1945530daa0000aa2000000042cc0003d1400000016e8000125e00000007d50000501000000000005ce80001dc80000002ade000000066000005e400000000c7765d9d4b548da22bce0000bd5000076a0000000000000000000002e6700000000002c210002480152a89f4c58000ab482001ae14b8a810000774906b0b5a90c00000000000000000163204880000001b5c0000cee5df127e9d31ffa1d9000032080000002866b631aca4ac8000c22995800000000000000a7197de0001d146001b150000000494afb4
  | 42 => 0x3e7800000000000000000000284c00000000000000185c0008e2800000024720000000000186a2a74000507816ab60000000015f0000000051040000000000656c0000001c44666400000000000001e9ab840000000000000000000000000131c00003c5359763ada8a0b01e40000000000045900000000002ac410bc0008b405de000204c20b70be6ba000000003aba34800000000001d700000000e0000010b1057000061c8000b9a8000b98e37527e000000000000000000665e2960000000a6f170000000000000000378ea03727103cb808f5623f2545034c000000000050f800000000c256c5eee0000000302800000029fc1f180006ab1bf606bc0002ac04a2000225800000004881aa8593187e000000000000008372f340970000000000000000006e960707a59f640002eac869000061c00000d98e890002dde0002c560002abb1269ad400014762b742fa0002f9c654e77058b8000000000000011bcc4080004088988000229a808caae1a12d7100000000e3800006e4000930000000000004de80000000000000000062ead1a7b88000904921800017124d6096600000000002cd6a59a6a600000000001b586720000564800000000000002c0c0000000000000095e800088500008d4aba200000000000b9e01b0d1f00000001e92b803b1aa38462a8395240f3f39f01799a180000000ac400021b80000000430607c974c7a70002e0a7799611a6e921e000000064240000000000624ae993e60bf800000fe00000000000ef43bc800000007888da15c80000000000244000000000000000619000009cc00046a80004ff536800000000002436793a94a0688d12000000070b0c3063e13f396080006f5a9495d60de8000000017a0000ba80000a406d650001096be08000000000056c8000c3b2b070000000599800062846d0b8d027c488800000019428ab0000a53623600000002912c92a078f5c8ee810e5950c2002280b50001f7f0f585840000ee865d708400017e200000000000000000000000012240002f520000000000276500000000002cf26104000aa980000000adc2ec80005192a6464b9b0935ba33b6e088ca4cf1a9e0001e66224afc07cf0044626f06c962c0005e2800003c80003c9d33e569e1e08c8800000028c200000405d520cea41a8ac4af14355f31957b9c80004c8d5e431ad0c96f70558441b04254787d49c0965ab9723ff64ac8ab0001ba2060cfc27800000000000070c000039c21988a1a5772a22e244681a03328c000000144349b9aae04f492e46b8d6c2ef05044c10000000022a0002cbe0000eee7bf80009602a7055ba818a7ecc1511897d136d01e800000000001f7b41d858862d8000b1e0b5a4b800000001e4c00000000fa00000000000397800051f80000811925149800097b8000000000000c
  | 43 => 0xc181ad40e60000dc00000000a3da49c903d36e00000001eb000032a21fc76400000000c380a52ed600000002b4800024580008458318660e8330002d720000000000142c8e904e00000000b85aea800003e63f98000273800000014941cc40004a980000000000bfca1407ea0000000000018dd4500001c0000019ae0000000787a2667b1afc7ac14ca600000004bad96e000025e63181ae7c08d447f6058a0002ef050c983a00009ca389111caac0000000000000000000000000c00800000014b20000276000000000000b0000000000000000002ec200000000002f102208000000000094691c605756e287280008a21f9169ce9e64a3ea267dbd71a25f99ac3140a8fa4800003ebe92a910850c000000000000000002f3a022dc2d9699202bf1800075e2cf6bc216f60ef86d80001a6a610aae85b92a409619f5b93480008bc12ff0001f9d61600000000000974ad8e00000560001a340002ae40000a98000267a0000000000000074a1ea06ac215633800608e20d9633dc11d60580006ece7880000000ab2800009fd1f200015e054e97b2691e93d0001c234f409460002fcf3dfe7b60001bad000100445e915e000077ebc12132b361444000000071c800061004910000000bb300007f40000000000000001d00000c948b38c4c00003ee92f8dba73b8cc64338000000089c00000001d88000000266a00000000000000000000000020d700000000001294bac00000000000297000026a00005ff000023100007f2819c00000003f5c000000002e000000052b0000829000012e80008a5000055981fa1e422b059e8d00285400083d80006290000000000080893a40000000000000000011de000090e00021920000c741d9c000634acb20000000000043012f26c0b072844000293e717a36946200003fb18ae000212e600e87e123651c582a4b0000033620da5d92be16a2000000041b421003600129d294820001fa636d9910bf40000ae8100a3610cf277080000000000000264204aaafa000000000011c700011c200000002380b649ce80003ae00000001b0139a4765904019aaa8870b00006d755040000c6c000778d9d40000000000000000021100001801b5024b40002d6c13e09f26c29939000000000005b60001b0c0000ac00000d8a61e20f408524923270d36a9c8000a9642ae7d606c03fa095d000000000000001310000ac42b8b4524000000000000011840000c403a6000000023f35d11ade122c3ea000228aa7927c433c0000000202830a186b2efccaa1d19d7015e80007650000000031a18200004f89320000050ea20000025c8000619df4a00018c449316aa6e1994816530789e9800016019be70511ac5a2c0001325b008bc832408facc82e393c400000001be24aeacc1f145262b840c14eae0000000ab6026
  | 44 => 0x9c40fac06000168d000000000000000001a7e00000000000afc283449858a16d20000778000265444d459079a8000000000000000003f5857d078a0d613a8a9c3804a684e323560f4ca1d358a17226b8beabf080000000000ba200005f6000065f16503813006aa400009ba068e7e70ba4b61000083c03ac411a2c2b0f8000000231c0001a185d200009fa80005220000000142e648800000000000c66c660000000a5e0000000000000016a95aeaad44630000bb48dbca561bfc04906da01180000002d606a600000000000000000001880000000000c0d0000baf0513000150a00026375cb800039f9f6a7cd179bb74899e97900001cf800039a1823b8e0da02538ba20002042000000000019af817d1ee9bd13b654f8000004c000814983b050000000000003038000000000020c9f25951dea448040008198c0965a800084380000001c9400000000000000000000028680ec577000013b0000674800033898a80001c1a1a6209a000000000020ee8b65fe900017b09198000000167c831000078e00000000000a67800000000000000000000015a000165667f02150000000000310a49a9a66000200447ea0b38e880000001a6e84a59510da280aa8f078632b80007ea80000000000000152a25c23c203d40001c3800000016060002f74805c000000133100011780002a9c00009b60001329a592a5f9e18000329e406281c30d9b70d8600000009e2a4a624183001cf0f1f11e83624bf172500023783d8843241ca82612d669400026de5300a0078eadbc222c0000000a3e0000000690c0000000000c15247a8cd2be4000067d0000a3a6ce4f6cad880f3099c000565473a0000d9031b4b8a157a42451290b015711628ad58b9000000082480003418000c10307c00000000002996a894000000000023b980c88f80000838000bae88c6b6c8000a1ace4f03b80004bf68d0000255e4ea00ca079530ab4a00000000000000000047f800049e264400000000000000000000040a9b92625800058d00000000b969726142b19000000000002052798000000037c27a0000000062dc000982800000000000000000804000021a0000304172800016800002027627000015f184f0000ab418b8000140800000000002bd0538000000008d307a1ec0000000045c8fb80000000094bc30560af505ae000000084b00000000000b90800019700000000a1800013c600016e0770000000008a861f19900000d8d00018fe000000000000008c806342ba80006c40c010d7434ba40800079e99b0aa180000000000b4c293c000078e43f1123000291f8aa80000001ab6290c000000143a80ea348632916018f0d6d37a80003e94000000000000000000000000000173895d800072080a057b192600000003212ac0a8d293f000194a1a19fee000267837f974600
  | 45 => 0x7cc54b00015fc000112a000000000024b995f00008861b6a000057211d00006229aa7894c0000000000a3a44f00000000be5c0000000d1c00000000df8000c39800000031000f50000b092598363800037e0000adb9dae3488d6000017fe0002b8235a00000002c361ef00003eda89689400000001bf3000273ea6c041a838a6929419474b932616105c0007e380000000000000225c9d987bf00020194cd80004ce0e1e3f898cc000239b0000000a2da6e08b100000002ce2a66d5de00000000000000ace8000000000000000000000d0c6dd00004e984f400000000000000a330000af2c1de00000003cf00000000000000263ca83000000000005160dac00000000000000000000077a271000000000000000301000000000000000000636441c49d0000a3eccb10000b3e7b80f9a73c836ba33c2b40002aea31a8720bc61dfa9c8d02c00000006f24000090c97c0001fbd16d28e100000005a900000ab0000a4880002a4800029d172d11580004cd00000cbb01e000000000026caa5c08100000a7100000000000000000000000000000000000000000000000000001d80000031c778000000018d353a0f587ba25a92fa14d04e29576000000000016b07881cbbb392cae00000000000000c0dc0006bc08dc0000000399cd07000000000000000000000a068000000000068750980002b8600027b74041bde5af8a46000000040e80006690000a2425950000000000000000000000002f9a2bdc00000000000000000b4f00004950000c221fd25a0880539680000000000000289e5e82d387c01f5100016c2000000058302cd00005b800022de8e4000000006568878d9a4d4000000000000d380003e6eb6d3358000bd80000c0280006f11aa400012de0000000000000000000007c28000000018a5331d620000000000000005a000011b80000000000000080e000310cc1d06090000f02a58400096166f261414c474d8887707207343a0c72c001e10ad100008b5c0000002ed4000000000028cda94800000000007c710b8933000000003c2000000081a00000000000056000053f1ace5f002f000008a20001ec4000000000000000002e0c00000005b313f4bc89a361b392d402d2c0a58cc3961910547000215c934191c000286a00000000000088ad1887602cd59a0001a582b9000000000006fbce5d742a6986f01feca485afc9de8372bba09924e3ad7390130aa884296c0000f975f5000000006325742bf400019fe8858eda68e1c98bfba34ab3980006f48442596c9ba5ab0fcdac280006ba998e1af28f43df9d5a8cca5f000000001f0c057a6da9f964f800000000000000000000174c62600003c21c702f78000a6b80004a48000a570000000000000016fe00001baa338a6e860000000000000001d84bb1800061880004e62dea0000b
  | 46 => 0x9a6a7a14dc2dc000000021fa0000000000000068927c6000080db69580600000004bd40009b38000000000000000004694e560000000ac7ce4c418093e3e0abfc7bf0cd80002eee8a3957c81e84952290a8d0000a2400000000001e488090000000000048c2c2e74011c86e20000c0d40003839d0c35983560001530948a8b010a9c22113e7cc485c0009a29daa0001966a9400003b2ab36000000059d000098983270002ab200021d8000000000005c80768f8b21580000001d960000000000034f739af72000000017094d89d740000b125dc80257505c8a7041e58b804148beca2e00000000000402000000000000000000000016c0000000000000064d552eb0a693800000000a58000b8b00001ba2860bc9237069122a04f2876800018e8032000000000001e1170894780006a40dd00000fa400000000000000b8726880000000b4d80006e000ae3169c92000000079900006afd0fe869800023ea4f4102800000001460000000000000000018e000000000001dfc4858f96000275c000000021f92b8a998000565800068f9518000000000000005dfa70e284e5463f32646000000000000000000a3c9e3800000000000000000068400000000004bd800019cac72133aa121ee01b2a4da6a0bf8005233487f7828ac530002e59641428eaf25b2b00000003cb000087200000000ea4a76000000000007de280800025e80e982a831f8000000000000030565988a5e000000000000000001e460000000b8100005e3800016a8000481800068017aa00000006671ddc000000000001bb98480000000000000051a000000000007b20000854c1805b008f5d3c0001dcc00000000000c7d000000000006b0000000000012e900000000002c0e110529ea37a5100000000000000013f811a00000000002c1d0001b2017990c500000000fe4000000089a00000000000000000000000000006ae0815ae28186795a86258080007d780008021e9e82f0a7821d00006149b9800027340000000905236e5700000b6b148a5f10000000000080b909319eab34b2c27c8257a3a90000b122e48000000014530351946682a845823108a7b2e0000000000002b870002e7000000007ab00007608000566220a16980002c326ac53980007580000613000e00000000002ede0001dd061d4eba69e8e4749b2d48372000000000009371f1a0000000000295e00000000000a9bb0c00000000000000074e000231f4111172095400007ac5eea0a93440000d6481d00000002ea65f900001990000000301845a000000000000002c2a50e169891fa7e0a0930d018ac00016300002b3c000673d1522942d1c084a892386abb60000000000289b09240009449c9a44790b2b8f2169038a5ea66f0ac1c2325630f8411e1534025000292c8e32faa0000e0800017160002fbe0
  | 47 => 0xb75132600001a7000000020f24b2658cf050b5000054080000000ca2816000000000000002e64b95cc7c00000004e7c82714f0000000000009f80000000000a7f40008f1c00025307e49262a567ce8bd200002a9bfd8c6c903276f0000000000000006e0c631c8993b02013c8b912c90151599a6a44cfaa55061cb3530525edac59b63414aa83cbc20ec84467da19d600022f5000051e6cb66400001c9d524400023900000000e7325dc0024f583a7b768b2600020ca0000000000204ea505f3142a9d06bc492d89a593559c7aa0266e66ba247aa05000000000030c6000000000027f2b459092122800064547fd0000000000000046980005410000000000000000000b08000a6649b200015ac0001c4095c9894000042e00000000002870000000000000007ec0000695000000000000000000000000042840005838b7873e800099800000000de6b708000a969ed80000000000000044f528c8b705920f10000000199400003c667e5ce767296f51ca26350002a182f62bca0000000ad480006f3400000010e4930945b0001cc200009d6000000000000000001ca063505ac3eb0000173865a292260855eaaf4c3f5bea80a400037d0b6e7e10000bfe0565a5a40000002dc6b5e0000b5b400097684701a80000000000066985d00001784ba099326241d44ada50060000d94645aac868c0000082000000000007d200000000e4400000001018000000011f4d789370000000267000019183d07fac02c8f7e38b916c0000000baa000112472c2ca493e2604524ad1915c01920ca2312883800000011d86ef296508786529ee00003fbc00065040004cb2c12b67e8250000000abe40004c49f50749189f9650ab28f3ad2c4b6ac326e9004ab2a000000000005c8c9630000000640c000282841612e280690a05f16679de400000004eb000000006391abd96216cafa615a8000bf58000957c00000006169df9ff60000f8633d80000001ca429d813600000008bb6ab81a7800000000000000000000000000000001ccc00064fc00073898990001ce52c0df21b671a0e25ba57858a80000000c4a97600000001a1e0001a74000000000006aca9515d23d509db00020648a12bc807a95af6074000000253000020407559e0e236e94e2c780000001929b26b0c200000004340000000000000018b00001a8681b833800015a2bd427aa0000000000000000013720000000000000077c1f332450a1400025600c59fcf000000000000000000c92b4fa5264ddd586be922200000d6a946000000000000000000000000000000003fe688f414092a678e7e668715544d900001341aec8450b9900019233d450c400025a400020ff96b9fdb4254000311ab8c243152684bce6600103b4572c00060540007b4000056d00000001dc40a0c000000000000000005be2
  | 48 => 0x1668a738000bb0088500003d141500005c5569ea4200002282f662980000000208414000007c100000000c1e6da01ec000253c51315d8000055a276061aac69089734d100bf2469d317828c00028790002f5e00026766541ee60000000000011c0001b18000053e0002e904ad24db20e0000a6300000e610a0000000065640000000000000000000000000000af6007000072d8000bd900000001f610001edc0000000123e3ca1950000559000000000006e58faa7850000338e4d64ed2c0818aa728983d1a430b8a6fa5c80008f18d2c00027f06810000000255c90d1b0b3f94000a09d5784e5a7a8bfa30ba7a10f695239be0adc00000658000a610ad62f201b64495e120001136c132da1095a76a0000444b312d1800019883a9800081156c61d200001418000000000000000009e680001f66a3a4900000ae765a3000000000000000366e8c834293211c80000001a0200012327f5037867d44ad00000008629d20c1a00000000000aee80000000a207a2800044e608c000178825903930002904971f03b00000000000b94709800000002467ac9da093f30f6000000079d0a8e75a80000000000b644d3800000000a200000002e55000000000000000000ee60db026b422c000542000000011b07a02fbc8f31094202195f2f1a6da000236600000000000f2252a2a780000000000246c57262ca34200000c26ef40000000000256c0000000000000044a000000017d600000000000c0803d8409af988aa00000000000000a20876a0001baaac754060000000715871845c00000000000a520000000040d63400003fd8f4a55a068c0001ac672f002600022ae0002b98108299f0001d3033f01f4431c000000000000000000000000000183360d8000242b076000000068a02ee129044e0000000000000065f8000000000000000000000000000239e00000007cd4000170000000005ad00000003e28000000000000000000002f5a2b380000b2ecac0002dbe0000304000035700010ab74c8b7600030bc2ae8bf4582c00000000007f68000b22000000029da0001955000000025a000053e0dee059a386ae92a749f4aee29d4ad1298362d862980005ca800000011c07a607025640be4000047e346840b0001c74000000016590242d8912c01200002b4000095d2b0c00000009ae00001042c9e0001c1ebdfad6a00000002584000120021a660a3a000000002680000000000000000000000000a59ca9a0330bab0000000000184a913800000000003efd4680002bd30002308000000093d8000225800000015120002dba400400066186d6000000000000000002cd00001ac581580005e592b0000287400013420002d0c00000000002fcac080000c238e34000000000001c6000000035200008f901b00000880147c0000002d52909c000
  | 49 => 0xb4a864a95400000000000b1800000000000000000000024de500822089180003c4800000000004ef00003908f684db11b4998928a8bf000060801dd0f340000001a84a472c28000000000000000000000584000000000001b980003d909c810f044000000002ee000003965fe7bc000000000007ee042400010791125288205edf8643878a00000000000000000064200000000001de264bcd82ba6c000499000000008f807d6a062988d5c09526416a89a2a009c0007a9889086310ea16e8bfe2c3800023d140c5d88000000000056a00003981f94000000029b102e67100000001b7e92a80005318000af5a7c28900000798830c00010ec5352f4a0000cad984272a9c3037c0000000000000000000009cde1a821902f800000a9000039200000002178000bdb800000000009170b060000000434a09b000000000000007ad800000000000000000ac800000000000afe8f2e58f20ae00023009d3ac480000000378661b000139a6e7800000028d4553a15a0000000000000098180000000000000000043005070ac0000390e25e0000ec109b2c82b29ab6c5025bf2031a508c2010268758000a5d00001a414180fbc00082d14720001e3c0000816000000000e00000002a32000134017451eaa17000000014f23e223590000000653c866416ab9aafd9fe8bc28c020ba88866c497e002a83303a293781b66b88341176cb732d4ea654ffe609a3c8a0b8a1e00011370000842000168e1eb9f7d43d8000b37a4a885e8563bb600000001d68a40012d00000008fd98ee0bf6e6ea1e909e0000000000000098903f0000000000029f800000000000000000000072f8c16677c00015b8000000266e000000000000002ec03402c81f300000000b1464da48a835c3828f4e5c2710445e58e261189629f7a59a045800002dc0000000000000218e00006b3000000039b8000023283e00012aa0001a1b0000000000079c0001ac000000000002174b9f2fe2823494000000007a2000008ee650000213a0002d67000000065c118b802c000000299013700000000000000000000017a22dc80009d600000000000a4c4846000000072c800000000002be80006a20e8c04f0000aad8000000000021313880001fcc1b800000000000889996d0eb5a250000de438e1fb7150400000000008f4000000000000dd0804912245ea540848bffaa1025284315d70000180800099f800000000008e1c00069d4ad30000000301c0000000b560000000000095001d000022c40000000000000000048290814cc0e1c7e400000001fe52948224bbf80006c900001c000003f907e65848000558a6565978c3cb2a8000659c000000218600014e26f8cf92aa912007f880000001ea2000000000000002ee800031c000013780000000000692479a0000000000040c65dc000000
  | 50 => 0xd8000988d2122522d9289f0f100001b3e7ed0000000000000010f2000000000000001c9800000000006f9942a0001dce3830bbe0001a5600000007f0810099680005148000a22698e0000000000000019d09b00001989ab091b2000260e0000000c1a800000029ccb06c35200000000ae8d3f2488a9400018568054f410002bd20304dc600000000001b3c6eb80000000000712ae6296d4c2a2c0a6c68a601ee521a9a0a7b8000000154086c000000005e72bb80a8b1380b65c923ef6449d34000234c65e1a41bcb04fc104c000000043ab7e56960cca91369700003e7172c000000000000000b805e9635d52100000000002fd27d72bda00027fe958454f2c400006221f2d6ff40000034945ae38000000000000000000000ed8000000000000000a9800000000000002fe480b2a1418340000000000000005ac07101566049f04fe00000000000b9400000000ae02899bd424d499400019c07dc40000001ff0000000000003489c680000002aed000000000006c200024ca63453dcac7a5960000000000174aab31308324000000000002e31f188c081a5000007a7d198be00000002511f407572a5e0000000000000000021f87468000ae4800000018ac0000b04000197f0b280000000000000154256e000000018ea000252e972800000025b210fe1843f61766ad62d3200000000001bf800000000000b2a3850000000000060d141ab2d00000000000000000060100000a727e856c1938718256400015cd1c1400000027d664d030300006d200030fb6b080825cf00003391bb03340a80afc108800000004e880007c9831500000000000000000000000030a600000000002886000000000000000000fae73a000000000000001dc60002b022afc8d994a001e340887050d000099c9eb0b8f8290a518910c2da0340000f29b72000000016f00002846005aa2c42bc0000001a9a00000007b4800000020e028495ad52a88e2188037039ad190bfc0a41c3c0fa81ed25840000000962a4607df159c000041897800000001efa8b48000647c00064100000000d551bd80004ab0d345402fcc000000081b000053f91660000000000092400000009be00003d0d1809ec155a0002e1a00021f60000d4300000002d8021626b2b24000000077b2ec80000000766017157440000000682239d3100000000180c00000027064be478c24807c80002c0000026a40002f560002e5b0002c4f860ad9900018802b209ec8ddd0f40000000b510da797da5a00001dac694044d00000008fd21220000428c371e902a42ae000028f82888289000000000000004c66a7a000000000010180001cfc19f05498818fee0000f5e4da4000264000023952480002b1c0000c960000000257e9446110ab5200ea4c9eca0788e5c648000018d0000c1c43880005418000000000
  | 51 => 0xaa00019cea31000000000001c599f241980000000000970000000000000002b5c3da8e62000000000017da91580004c680001c12ff409c99ad916ab7aa5f15f40000000738011100006a200024467a380000c51ccc12240006590c0012d10d47d567948075208000092f3be8000b2e800000000004538000000000000022ccafc800000000000000000b654a167dc10b4396e1de000168497e000065d0dde9eb80003a800005f8c76e87313540fb608e9efd46c0001c6a240304633a15a443626cc21f0d78028c5ec0a2800006b4e6a0002b8f0000999000000a84f2f0b5f49a422ce8b8d804df0b428e89c1088a8c8a400000002a28000000071080000001db6000000000000006fe703600000000000000000169000000000580000655adf60000e28a4a00003b82b770002c5f88a0b8500000005f8632a0000000000000043e2b56292863196c000000000004f396da000000039d000000000000000000a8b8000486800080f9440c0c2cf468f000089e800087a80002812f906f9efac00009dd00000000001535bd62fc404e88b4233d4b6b742c74138800000003f30000000000044c4559b4a9f28000bbb2a600000cb0aca0000913000000000003e30000000240b4ec4000000180a2a080007811e2825d80003cec000000000039cb00800005f6c2b2dc456a871eaa51dc8273000000005ea3ed0000000161e00000000000000000000044e8e9aa8c0000000000021b900d5b98000b69c2323ce12d28d08d92a91a1207b3a31e728835e4fe9a7645d12d6acbe56524a00008330000c3580000138e8e00000000000000000058ec2c05d892695bca4edba63c292f3a55a82838e88347ba8cc21fc80008308000233553c00000000000000000044800000000001814000000000001e30002102000000000000001391e22255aaf21bf80000002272000000000000009e48cac00029ca000000025e00000000000b701b020001d9a93e8000000000045a8000b6d800000900000000f0c00000000000000124800000001f2000000041700000001f920000000527a7720002a68000000000000000000000454000000030e00000bc4b140384a8346964f4a01ab050a2a468adfa0001cd60000488a9b96f40002c840000000000000000029526e690fa000000079b19469eae42a1a6a4f25f74000aa01550279878211b000000018f2393958c000000000000000001ebc1bd0b71000000000000000002a4a14d0000000135c000000000000000000ff2c0b00000003112000000075c800063380008db12420144000000000000025700946ce027f06b401f84d423d869b0000000b3a196800000001bf0000000198b0000000a84c00000000000002c540f7dc4e42a00008fc0688731122c4188f8133e2ba818064e20f2800000000007f92b265ae26beab
  | 52 => 0x2950001bc2000000006a800023c9b9c55c9eba0000aed53d8b30000250a28a5460b921feaa6940007222548847a13652980000aaabae00e91f800012108c9800024203ec0000f21a7fc0005ed26bc6a80ad45af081c0000000b34800000000000000000000000000019e000018af00027c5395dfbba04000000000000002bc70001ca800000001b8915a7c300003f20a640002e52000209c6a49cca45b28763b58000000000000000000000000000034c00000004c529aa00000000000524000210100000000000000000000000000008f940006af0000a95cd800000d76000000000000000000000263a7680001fb23916f4262b4000000000088a95881e980000001318000000000016a885300000000fb282e9f8200000000000000bc080000000000000000052896f73f0000000000000000000000000000000000001f866a99b389a786adb3c107a4ee95447862cb635483fa814400087d2cb88c6a6ea5fc1cea2f89324883182c4484812000179e0002bc289b9cc600008b000000000000000000000014b0000000000000000000000000733800000012899f00000000000000000006a70000000000000000000000e2600006148e1000000006706068f997200860265c000151000000000006b60000000283b0000000c0599c23464c6e0002b94000170a3330f2a4510000283113400000000f380000420000927a668000000000018c00000f80000000000000000000000514c0004a88000000000000017be00003763af00007f3974e000000000000000b4daf653b164800000007421d92a2b8aeb15480000001a4e4d2acfc13b8ade935018e3f7824eb252d0e00019f45189e2400028122ad9622000000000000007ce000005bb066222103890810363a00edebae0b382f413860ea507b00009290000efc00004040001cb800016c80000000a3a00000000000000000000002f6000000000000000520000bee8c3e00003530000000b624000024ad907d31f77326a6a200008af86c80005c400000003062000112e9a3a7d06e28c9f6a387e20002bbe3d8000065780000002f164a4241a369aaad0000000c360000b8c00003014fb735320c89a0800000000005368000adf6538498800000028e20000ffac010a31503800000000000000000aeb188cc179b64b1b2af50999fae20c2e8e9d0b10667415b5b36979c7831cc8a600cec0adb04a3b3aa3e26f80005ae44f79aa000000000000000000822aa15000227400020db7c4800065ea28c73f800053200000000000000000017e0c290000000000000000029f2bcc17a87ffb0c05ef2ef860627fa0002edc00000001a90f14a299f0d0000a1706f8000ad2000023f80000000000000000092e190790c2c3800010ee00007b600003b8a9fb0966ffa0fa30b1574a071e0800000000001a
  | 53 => 0x311000000061dd6246718000000048600029d02d281bcaa3233c2750a56914a072093c1e110e000000d0000ab38e52b161782000000097300000002e68000000072300001c70000250c9e291b98e68ae91920002a2300015a600000000001dd413e800000000000000000000141260362682e1d05627d250200000000001726000000097ae16d0ca49eead780000000fb808b8bc700014300001f5a000000000000000000000000006e0000000063c000958a046c2b9c4611786d41d6a6d21c1c562ba4a47b0001df80000dd680a9d1c91d241874f939e5c6030815598ec47a0516000276200009ea0001082430accc2250942602cb16035ae1e2661410000000020080000001d9e00000d25ad40000000000000000000000000ebe56a432000000000000001da23dc0000000072c000000000000007c5800000028550000000000000000026fa9742a1c9e9000000023e300009b81f325a833e5fba11f0fcb96895334b11176000098a4ad91ec2df000000000002168ebe00003b67ff40008dd168f175800000000007390f6e8c90270557a3f8a16000000000000002a580000000ae14e84000046a0002006000255800000000000000000000000000000000000a1a000000000004928000561000000000a500002fe35427cf573d01a0fd0000000000022b45cfa0d290a77c9f7e00000000712150000091a00000003cdd85d0001b3266e0f0e4f9800000020804fb0042931063a28fe38597d0000000176810b0000000045117700002ed29ac12c2f4e000000000028aa00030f808fe4032c221240616e9a26002220002c104e9c00000000000000000be4a0de000268c4c7800000015e6a32ac467d080007bc80000000000301800008b04a80002d7e0000000000000000000009fd00000000ad5b6518822ebd3fe000048200000004fc800098b985400000000000b420000000189800077d80004ea800051218fa7030000000000000000003dd00006d100000000000b33a3e0810f0ab98e9d22061000018a00004f5123c00005a03479d76ac6080a8af254c0d180004b9109a00000000000000b8ca8eb000000020b800097f0000a41400000000005c8209800022826170000000000000016202acdf723b128200000000000088400000000002614000000054c66f60002bce000082ca39205aa500071000096b96780008ee0acc000000000000003c600005a7c3da00000009d1000025a40005ee0000b618000000000098d2cc6676b03e50d80007148000000021c0002353b09a33100023e1000136213692fa000185a73d8000b6829150000000a1500000000b407e60000000000000000000000000000261a8ce800000014140482d70000000062a899a00000001ea20ea853800004f80005710ff42f2c00000000002580f4c0000000bb6b0980
  | 54 => 0x3bc00020d96e82e06c12217e8eb2486534aea217517a1000000020780000eddb220340000581ecea87904500a1aa0e79d80000000000000255ab6d1108be50bae61f6f805a18000b1a8d8828cc0005eeaf213d19b06000000000000000e287400a06e4e000000000000000000000898000000017dcc0b80000000000000000000024e451580004521b7302e9f2403856d41cc091799919f7905c0005e7ee7a11814caa9b0636074854031fd6d0a4468428d62c40bdd80000000d5a000000028093807d82ba3bc680000932b895f04b6a119800016f80000000000000054600015a90002b9630b53714529eec44c80007e882d84ae82e28aa264e0000000a0e9f62000032080f2b900001dca00000001801b280000000000000027e8000a955f0687b097d4a38fd272988503dc98480e88000000193a0000000000000000000000000000000000000000000001eb47d0400000000000001bf594517bf55611dc00000000000eeaa43b0cab6a88da0000000975ad00a6a12d09ac871201e09260178f26b188b24b0f000010021dc647859e000000017680000000000000217c72291cc64c1c2075496264a6ac702f030f43a0800000002640001ec8232c00000000000001713000000000000000000000adf218876715ea0000000b200d8c0002b4a0001cae0000000000000000028a2234af980002cec959c4903d994eeb1100004bb400004e2f5c000039e00000001ff1618b178668ab70000651000050f1a0c37ea3730000000000205c000132a65f529800001fe7de8000000000069222c026540002595ffc0000000be18e9c0000561000243e00001abaaba79c3440000652ea3174080000002100ae8400000000004f0800069f15468080000000131500017567908dbdc0ea7f6000000000002cc6b1000000000003b400000000000a6f86c683000001300000bb9a8e009023ae9512934044800065eeab43b706f2576830b9c946ecc03084ec2800005002bc00000000000048c0002d3aabe000000000006db0000538000000000000000000000000041a80006d8aa1e00000000000780000132e0d34000000000065ac00020950ef144000000015d97f9800023b000089c0000000155c000000000000003ec00303e390a4000000041c000041a00000000000000000000000003928000bc707100002c6e0001ac800000006eb00001828000000000000000000f6171f05780000002d540000000000130500000001e50000aca92cc8ae121c2be5142a0880000000000000196500001a00002a826dd80000354ffc943000000000002358ef800000004a0ad64451800071e0000889000072e928599f1d5e000000000000000001c0b7458b3c79696b614ca1aa93625db27002b2ba580000001cf06020ee20000ca43e40000bcb9c543d3c000b60a
  | 55 => 0x9a0000449a2f146e00000000000000215449e8000000000077780000000000150a69c000000000024ba00002270a480008700000aab0000902000033500003f8e2c60000000319800000009c356fb0d40001c2e8bbc00000007a9000072e630aa88acf000035bc000000192a7b50000000219600000000001691995c00000001a40000807000000000000009ecc36a399017e247029a00000000000000000242ebbd8000000000000000000b18000000000022b80004d69525bf52c1f1f7a5dd12590e642f8000000000000008c54e417d03f10000000000000000003561dbc000000000000008098b7e00000004b080000000000000175a00000000002a92a3c00006418be01f8074400000005a2011300016948422a4e6d6aaba734083a0000000000000000000000c080000002f4400000000000000000160028d800000000000000000000283c0000000b5e8000000000098c9a08681800000013066b800009e59dee000000000017920000dd2000000000000009b8ad96bfe8000000000000000000b70bdc2fc28c08ef00000002eb60002899428a7b41d2915800006b6410ae2e00023dc0000000000000000000009a0000000000727aa00004e6c4843538000b5bde5800000001bb9b4694d80000b906beac50b4401500000002bb2249c00064dc0001d0800064225bc0000000b902d5c30330723dda8b200000008668000b4b8000a9f000000030b2c31000002421ac79facc27948000603800038a8036a619f36000109c000000000012ec0000000000154869c9adc697800094c802a309dba82110000000000007e307e9ef30242fc800000006c7050ac7e68b064036913285acc7ce9128426b7c000012815ae0001d26112d8bc0000a2f000002085b0000a98400000022e0b99800000000003c6800000000005458000299800000000008ba637c000000002880001c18f3e000000026f1bee000190b78f888f83196302dec0002da1a57b7b80000000000812018c00000000d812ce05d0000000000000022c878a97645fa80003228f369598820892800000013be0001faca1004a600006210000000a0586041a2831183f24ce5fa000000000003fe000083a504eb7254d645644367a5279046616ae53aa8da62c961d2d30479000280c98b00108ad00000000000000000007a4000895049e8a9800000000000000f7c05b461b3f289da5c7893d271400000015286f20f098a4800000000004555b669649d2a00020be32f0000a0c0198c3c80003662fb800017980002a332568ba5bc9ac1a8910af0000000000028563994e8756e5c86040d01e898915c000201100000005aeed4200000008d900000001f3e057e1345fd0000b758000000000000003820000000854a520b0b0ad857553024d81a0a0db40002e082843aa90b6657093c
  | 56 => 0x544215e00023d800000000001bf0000140a000000000000000000000000000000020509c80000000054e00011ce1398b0a0001a123b5000063d800000000000002c5a00020c100004c8027c5810001fa44fdd01c000091dc16889587100000001d6e000309e00000000000000000008400000000001cdc0000000000187300011c400020360000059c330154000056881d4354c3e8000ac8856c00000000002a2a11e0000a290543700aa6a000000066629632d600000000000b589a100002e0800017e671d800072e4000000000000000000002e61000000098e0a9e0b3a39a0000f8f0000000000000067743f6404ad5a25ed416bac8f1e1530000acb254a00000000000b972a9800000008a145f00000000000a3fd86e00004be57be0889f9145c0ae0a387c41ef80fc4000000098c000000028c2a8a7870000b9f806600000009b08ae200003dcaf340000000000203106c00000000000000000000000027000001b78b83ade8000297a76f8abc0002b3e0000000a05211a0002d8500017f24080307000000000000000003082146000034f46c480e400000000001c28000a1b1fd6000000084116701e946b233280008e0000000010a6b9d076c5bb806946d9776000000090c9a261f009c67e59a3200000000af80006392fda14a000000000000002e6c30dc05034a41e67a300150002f884aa08782bb0d9f2ae0b52000000000000000000000000000082aa1b400000000ee4000000000000000000000f448d80f2800000007de40000002b324fa1b8c0001a13b8d80006f3000000000008e50000000297690000000002afe000000063a5ec000000009eb40000000000adc70222618cc08bd0c616fc711400000000000000000000000000007e800000000ee4000000000001d66a530e20940f420001fa300000000002a1676c0b2c0000000b8980000001736000000000007360000000000000083925ab1ce26d6a038e540000000000000037130d200000005c31f6e6ae91ca7cfc2fc00018e700000000000d5ec36958a00000009bb000088c07be8c6185300000000000b8600018a049398deb08c00025d1fc04f6800000004584038000000000014e80002908000000000029e9f2c7f1003d0001073b3726703429d3a2571bb4000000091d8000000000045b800000000000000000000000c000014c8d50c55893800000006debec
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x862e645482104316b22a4108219398d5208410c9ac6a90420863a54980210431caa4c0108219694e6008410cb2a7300420866952980210431d2a2c0108218e5516008410cb4a6b004208659535802104335292c0108219a549600841087ee8b14a00843c7458a500431aaa4c3200211ddd56190010c6aa8b0c800846e72d944004236b96ca200211b9ca65100108dae53288008475715944004237390ca200211b5c865100108daeb310800862e549884004316aa4c4200211bdd56210010c5ca8b10800862d545884004237bb4a4200211b5da5210010c9cc7290800864d639484004237bb2a4200211b5d95210010c9cc6a90800864d63548400431aaa4c2200219994a6110010ccaa5308800863654584400431aaa2c220021999496110010ccaa4b088008639655004004394a928020021179cf65880108bae7b2c400845d7598e200430f2a4c7100218755263880108beeab1c400861e5458e200430eaa2c71002117dda53880108baed29c400845f7654e200422ebb2a7100219398e5288010c9ac7294400864e6354a2004326b1aa5100218d5526188010c6aa8b0c400866552586200432cb1ca1100210f9da5448010878ed2a2400843e76551200421e3b2a89002187d925348010c38c929a400861f6454d200430e322a6900218bd925248010c58c9292400862f645492004316322a4900210f9d2650801087ae9328400845e73994200422eb9cca100210f9d0650801087ae8328400845e73194200422eb98ca100218d5526108010caaa7308400863554584200432aa9ac21002199949610801087aed2a6200843f765531004317324a5880218b59252c4010c5cc8a96200862d6454b10043932928388021c954941c4010c6acb326200863565593100423abb6a9880214ddd954c4010a6aecaa620087255494b1004392aa2a588021d154d52c40108eaed28c200863965952100431cb2aa9080211e5db5284010ab2e7a9420086696594a1004334b2aa508021ca9515284010e52a8a94200874a5354a10043a4a9aa5080211e5da5184010a72eba0c200863965d061004394a9683080214edd54184010c72caa0c200872952506100429ab8aa8880214d5d74144010c6ecba0a20086376550510043932928288021c954941440108ecedaa2200853575951100431bb2ca8880218dd955444010ccecb2922008725549491004333b2aa488021c95515244010e8aa6a92200863554d81100431db2ca8880218ed9554440108f4eda92200855973d4910042b4baca4880219ad965244010cd6caa92200872a545491004394aa2a488021d294d5244010e92a6a92200866952d8510043b0a96c2880211e9da5144010e62a928a200853975d05100431db2e8288021ca54b4144010a76eaa0a200863b655051004394a928288021cc9454144010
  | 1 => 0x420422eb9ccb21021179cc65908108bae632c840847a70196420422f39ccaa1021175ce65508108bce632a840845d73195420431caa6c0a10219654f6050810cd2a5b02840847975181420432ca98c0a10219a54860508108bce7328840845d73994420422f398ca21021175cc65108108ece2328840847a70194420421f3a4cb190210f5d2658c81087ce832c640843d74196320423d380cb190210f9d2654c81087ae932a640843e74195320421eba0ca990211e9c0654c810a98e6a92640863554d853204332a96c2990211d5d4614c810c6aa830a640843e74994320421eba4ca190210f9d0650c81087ae8328640847671194320423d380ca19021535ce520c810a9eea990640854d754c83204327b2a641902193595320c810e1ca8990640870d544c832042e238a64190218d9c664944108bee6b14a20845c7358a5104297396a9a08214b5cb54d0410a5ce42a6820852d72153410421ebb6a5a0821479cf52d0410a3ae7a96820862d6594b410438729ca5a08218b59552d0410e1ca6a96820870d5354b410421ebb0a5a0821479cc52d0410a3ae6296820853a7014b4104334a94c1208218e5516090410cd2a4b04820852e72d514104296b96a8a08214d9c7545041087cec2a2820852e721514104296b90a8a08214d9c45450410a6ce928a820853771d95410421f3b6a4a0821479cf5250410a3ae7a92820853671d494104296baca4a08218bd965250410e1ca7292820862f65549410438729aa4a0821c354d525041087cec292820851e73149410428eb98a4a08214b9c85250410a6ce2292820853a701494104393296c2a0821c954b6150410a6ced28a820843f765504104317324a4208218b9915210410cd2a5300820863a545804104334a92c0208210f9d3658841087ae9b2c420843d75992210421fbaac9108210fdda548841087aed2a4420843f76552210421ebb2a910821879925388410c3ac929c420861e6454e210430eb22a7108218b9925288410c5ac9294420862e6454a2104316b22a5108219654e6088410cd2a5304420847b75582210432ca9ac1108219a5496088410c3ca9b1a420861d54d8d210430f2a0c6908218755063484108bced29a420845c7694d210422f3b2a690821171d95348410c9ec7292420864c639492104327b1aa4908219318d524841087ce9b28420843d74d94210422f39eca10821175cf65084108f2e0b28420843d75990210421fbaac8108210fdda540841087aed2a0420843f76550210421ebb2a810821175d66308410c3ca9318420861d5498c210422fbaac610821879516308410c3aa8b18420845f7694c210422ebb4a610821879925308410c3ac9298420845f7654c210422ebb2a610821879915308410c3ac8a98420862e649482104316b24a4108219398e5208410c9ac729042
  | 2 => 0x82902212e1d94148110c70caa0a40887a24250520443d0a128290221acdd94148110b64eca0a40885b07650520443583b28290221ac1954148110d66c6a0a40886b16350520443d13928290221e85c94148110f46c4a0a40887a35250520443d02928290221e8cc94148110f4064a0a408866865c8520443d0a0e42902219a1952148110b90e690a40887a141485204431b32a8210221365ce6008110d628330040887a141480204426db9ac5882216cdd941c4110d66eca0e20886b3625071044358b128388221745ce2084110c9cc7316a80864e6358b5404326b1ac5aa0219a58a60d5010a5ce5aa4a80852d72d525404297390c12a0214b5c86095010a5ce5b22a80852d72d91540429c382c4aa0214b9c86055010a5ae4302a80843f765505404316aa4c42a0218b5516215010c5cc9310a80864e639885404317322c42a0219398d6215010c9ac6b10a808666629845404332b14c22a0219a58a6015010c3ca931ea40861d5498f520430f2a2c7a90218755163d4810c3cc931ea40861d6498f520430f322c7a90218759163d481087ce930ea40843d74987520431ab24c3a90219658e60d4810a5ce9a94a40852d74d4a52042a739ea529021535cf5294810a9ce7aa4a40854d73d5252042a7398a929021535cc5494810a5ce9a9ca40852d74d4e52043872a4a729021c35525394810c9ac631ca40852e749865204296ba4c3290214b9d06194810a5ae830ca40854e7318652042a6b98c329021539ce6094810a9ae7304a40852e74d895204296ba6c4a9021539cf6254810a9ae7b12a40845f73585520422e39ac2a90210fdd16054810878e8b02a40846e76d5152042a739ea8a9021535cf54548108dcec2a2a40854e7315152042a6b98a8a90214b9d35354810a5ae9a9aa40870e5494d5204386aa4a6a9021c39515354810e1aa8a9aa4085687059152042b238ac6a90219358c6354810a5ce930aa40852d7498552042973a0c2a90214b5d06154810a9ce630aa40854d7318552042a739cc0a9021535ce6054810a5ce8082a40852d7404152042a6b9820a90210f5da541481087eecaa0a40861e5498c520430eaa4c629021879516314810c3aa8b18a40845d7694c520430f324a6290218759253148108beeca98a40861e6454c520430eb22a6290218b9526214810c5aa9310a40864e539885204326a9cc4290211bdd95214810c5cc8a90a40862d64548520432731aa4290219358d5214810c3cc9318a40861d6498c520430f322c629021875916314810c5cc9310a40862d64988520432731cc4290219358e621481087ce9308a40843d74984520431ab24c2290219558e6114810c74c9300a40863964980520432d31cc0290219658e60148108bce732e840845d73997420422f398cba1021175cc65d08108ece232e840845e73996
  | 3 => 0xd1650c910878e8b28648843e74194324421eba0ca19221535cc520c910a9cea990648854c754c8324425aba4c2192211d1d5610c910d8a64b086488478755803244334292c0192218e15160d0510a6ae3b2e828852f725974144296392cba0a214b9c865d0510a5ae432e828843f7654b414421e3b2a5a0a2147dcd52d0510a38e6a968288638655834144274b90c0a0a214bdc96550510a58e4b2a828853771595414421fbb2a4a0a210f1d95250510a3ee6a92828851c73549414429b3aec2a0a218d1976150510c72ca30282885a972181414423b3b0a8a0a218d1964250510b64e121282885b170909414431a32884a0a216c9c04250510b62e021282885e17218141442d8b86caa0a214d5c36550510e62e1b2a828853675989414429abacc4a0a218d1966250510b64e131282885b170989414429bbaac4a0a214d1d56250510b2ee6b1282885947358941442d9b82c4a0a216c1c16250510c68ca31282885b27018941442d8b80c4a0a2165dcd5250510b28e6a9282887255214941442d938464a0a216c5c23250510a6eea9928288534754c9414429b3a864a0a214d5d43250510f0a6419282885b2700c941442d8b8064a0a218d1976050510d60cbb0282885b172d81414429b3acc0a0a216c9c26050510d66c130282885a77258141442d2392c0a0a214d9d46050510b4ce430282885a57218141442d93b0c0a0a21ac9d86050510b64ea30282887327518141443d1390c0a0a216c5c86050510f42e430282885a172181414431b32a8390a21365ce60c8510d628330642886b141583214432631ea490a219318c5248510c68caa0a428869763505214434a31a8290a21c91494148510d6283b02428869663504214434ab1a8210a21ac5066008510a68eaa0e808852c72552404431b32a83202211bdc965501108d8e4b2a808843e76151404429a3aa82a02218dd954150110a72e12a0808843f765504044296392a8202218d9516110110c6aa8b0880886366550440443533128220221a9589411011096ae930e408863665506204434b31a8310221a558d4188110d32c7a0c40886d163906204434cb1a8310221ac9854188110da2c6a0c40886b37650620443583b28310221ac9954188110e64caa0c40886b36350620443c931a8310221ac58d4188110f22c6a0c40886916350620443d1b928310221e81c9418811087ee8b2a408843c74595204422fb9aca90221171cd654811096ae2322408862c64d492044316320a4902212d5d0614811096ceca0a40884b476505204431c32ec8902218e1946448110b62e232240884787558d20442e539ec4902211e9d85248110ad0eaa12408856a75cc9204433432e64902219a1943248110d92c619240885e1710c9204426cb98c2902216c5d06148110974eda0a408863865d0520442d8ba4
  | 4 => 0x5aa9310818862e5458840c4316aa2c4206218d5526110310c6ca8b0881886355458440c43533128220621a95894110310d62c2a00818854c7354b20c425aba4c390621879526388310c3aa931c418861e5458e20c430eaa2c710621a598d4188310d2ac6a0c418843d75d9120c421eba8c8906212d5c4644831087ced2a2418843c7655120c42a639aa4906212d5d0614831096ceca0a41884b47650520c421fbb2a82a4219398e6215210c9cc6b10a90864d635885484333312c22a421995896115210a9ce7a94a50862d7219152842a739ec4a94211bdd95214a108bce632e850845d73197428422f39ecb21421175cf6590a108bce732c850845d739964284296b90a9214214b1d15290a109b2e7304850845e73995428422eb9ccaa1421179cc6510a108bae6328850863854580428421f3a6cb194210f5d3658ca10cb2a7304650843f74595328421e3a2ca994213c5c0614ca1087ee8b28650843c74594328421f3a0ca194210f5d0650ca10a9ae7290650854f754c832842a6baa6419421711c5320ca10a3ce7a96830851d73d4b418421fbb2a5a0c218e55060506109d2e4302830852e721954184296b90caa0c21479cf5250610a3ae7a92830843c7654941842d4b90c0a0c21365ce60c8610c98c7292430864c63549218421f3b0a8a04210fdd95410210c6ca8b0881086355458440842a739ea5904219398e5288210c9cc6a9441086596598e208432cb2ac710421b458d6188210d32c7a0c41086996350620842a739ea4904211b9d85248210c76ca32241084f07158d20842e539ec490421729cf5248210bc2e3a92410847a7614920842753b0a4904215a1d54248210ad4eb99241086c9630c9208426cb98c2904212e9db4148210970eca0a41085c8734852084237bb2a410421b85852008210c6acb326210863565593108431cb2cc9884218e59564c42109b6e6b16210864f63d895444317b20c4aa22193d8c6255110c98c6312a88866862d81544421fbb2a82a2214b1c954151108dce4300a88846d72180544421fba2c1292210f1d16094910c3ec9b1aa48861c64d8d524430fb20c6a9221871906354910c58c9b12a48864c63d89524432a31ec2a92218e19360549108deeca90a48852c7454852442a639aa4292210f9d2611491087ae9308a48843e74184524421eba0c229221179cc61149108bae6308a48845e73980524422eb9cc029221179cf65d09108bae7b2e848847475587424422f39ecb21221175cf65909109b2e7304848847875582424422fb9acaa1221171cd65509108f6e0b2a848845f73594424422e39aca21221179cc65109108bae63288488474755844244332292c2212211e1d56010910c70a8b00848843e74d96324421eba6cb192211e1d5608c91087ee8b2a648843c74595324423bb8aca992210fd
  | 5 => 0x85367118a54c4297390c32a6214b5c86195310a3ee6b12a98851c7358954c429db82c4aa6214b9ca6155310a5ae530aa98852f7258154c4296392c0aa6210fdd95415310c3ca9b1aa58861d54d8d52c430f2a0c6a9621875506354b10c98c7b12a58843d7695052c421fbb2a829621879526314b10c3aa9318a58861e5458c52c430eaa2c6296211bdd95214b10a98e6a90a58864d6354852c430f324c629621875926314b10c3cc8b18a58861d6458c52c4326392c6296219358e6214b10c74c8b00a5886396458052c432d31ac0296219658d6014b108bce7b2e858845d73d9742c431b2a2c3a1621179cc6590b108bae632c858845f7359542c422e39acaa16218e5506050b108bce6328858845d7319442c431b2a2c2216210f9d2658cb1087ae932c658843e7419632c421eba0cb19621535c8538cb10a98e6a94658843e7499532c421eba4ca996210f9d0654cb1087ae832a658846e7694932c42a639aa4996210f9d2650cb1087ae9328658843e7419432c421eba0ca196211b5db520cb10a9ae6290658854e754c832c42a63aa641962193d95320cb10c9aca990658870e544c832c4386aa264196212d5d2610cb10c6aa930865886355458432c4362992c2196210f5db52d0710a3ee6a96838851c7354b41c421ebb0a5a0e21479cc52d0710a3ae629683886395498241c421f3b0a8a0e210f9db5250710a3ee6a92838851c7354941c421f3b0a4a0e21479cc5250710a3ae629283885b170d5141c431bb2aa8a0e211d9d8545071096cec2a283885357590941c429bbaa84a0e216cdc14250710a6aeb31283885377558941c42cbb9ac4a0e21651cd6250710b66e0b1283885b07058941c425b3b6a4a0e2165dcd5250710b28e6a9283884b67614941c42cb398a4a0e21655cc5250710e4aa42928388537754c941c429a3aa64a0e214d9d43250710a6aea1928388785320c941c431bb2ec0a0e218dd956050710b4ee4b0283885a47258141c42d3390c0a0e21695c86050710d62c0302838843f7655041c431d2a4c020e21ac5056010710a9ae6296438843d7599221c421fbaac910e210f5da548871087eecaa4438854c7354a21c4358a0ac110e21879536348710c3aa9b1a438861e5418d21c430eaa0c690e219318f52487108dcec292438854d7314921c4326318a490e21a5d8d4148710d28c6a0a43887245250521c421ebacc810e210fdd5640871087aed2a0438843f7655021c430f2a4c610e21875526308710c3ca8b18438861d5458c21c4326b1ca410e211bdd95208710a98e6a90438864d6354821c434b31a8210e21a558d4108710e4aa4a08438863a5498021c431caa4c010e218e9516008710c72a8b00438866a5258021c4334a92c010e21ac5056008710c6ca8b0e818863554d8540c42d838282a06218b9526210310c
  | 6 => 0x30821f3a4c2298410f5d26114c20c6cc9308a61063564984530831b3a4c2298418d5d26114c20c6cc8b08a610635645845308333312c2298418d9d16114c20c6ae8b08a610639649805308338b0cc0298411d9c465d0c208eae232e861046e72996430823b388cb218411d5c46590c208deeab14861047a70995430823b388caa18411d5c46550c208ece2328861047571194430823d380ca21841179cf65908208bae7b2c841063954982420821f3a6cb190410f5d3658c820cb2a7304641054d7254c32082a6b9ca41904153dd5320c820c6ce3324a21043e7418d510821eba0c6a88411ddd95114420c6ac8a88a21065563544510828f398a9a0841475cc54d0420a5ce42a6821053571d97410828f398cba0841475cc65d0420a6ae232e821043e7614f410821ebb0a7a08414d9c453d0420a6ae229e821045f73595410822e39acaa0841179cc65504208bae632a821053671d51410828f398a8a0841475cc5450420a5ce42a28210536711514108236baec4a08414d9d25150420c72a8302821053571995410828fb9acaa0841471cd6550420a6ee2b2a821051e73195410828eb98caa08414b9c86550420a6ce3a9a821053571d4d410821f3b0a6a08410f5d85350420a6ce229a82105357114d4108296baec4a08414d5d76150420a6ced28a821063676945410829b3b2a2a08414d1d95150420e4ec4a8a8210724625454108398a8ec0a08414e5d46050420c72ca30282106a8621814108398a88c0a08410f9d3658c42087ae9b2c621063564946310831ab22a3188410f9d0654c42087ae832a621064e531893108326a98c4988413a5c0624c420cc8c528a621043e74d94310821eba6ca188419318e5248420c6ac9288421065563944210831ab22a2108419558d5108420ce2a3300421061e63d06500830eb1e83280418798d4194020c3ac6a0ca01045e73d96400822eb9ecb200411bdd562900208bce7b28801045d73d94400822f398ca20041175cc6510020c3ca8b18801061d5458c4008316aa4c4200418d9516110020c6aa8b08801064e5398a3008326a9cc5180410f9d0650c02087ae8328601046f755883008296ba0a790041595c453c8020e4aa2a0e401046d7694a200832731ca5100411e5da5288020e62a2a0c401062f65d912008317b28c8900411b9db54480208dcec29a401052d7414d20082b2b88a6900418bd974148020958eca0a401062f655052008392a8a8290041539ce5048020ad2ea20240107295410120082e4b988090041785c44048020ad2eb18240105a8744c120083a429a60900418ed976448020c76ca32240105c973d8920082b4bae84900415add53248020c76cba0a40104b876505200831db2a8290041cc5454148020ec2a390a40105cb73485200828f39ec52a621475cf6295310a6ce3b14a98
  | 7 => 0xa18a410f9d6640c520878eab20629043f76d50314821ebb6a818a410fdd8540c52087aec2a0629062f5498831483162a4c418a418bd51620c520c58a8b10629064f53588314832629ac418a4193594320c520ccac5a88629074432144314831daa4c018a418e152600c520c76a8b00629063854580314832da9ac018a419614d600c520d9064b00629067351580314822f39ccb90a41175ce65c8520a6ae22a642904ce7399721482a6b9ccb90a411b9d764c85209d0e0b26429062e6515321482d2b88a990a413a9c263c85208daeda9e429046f7654f214832631aa790a41591c553c8520a9ae628e429052e75d0721482963aa8390a41339ce60c8520ad4ea306429043e75992214821e3aac910a410f5db548852087aec2a4429061f54d8d214830e2a6c690a4187d506348520c38a831a429065463d45214832a318a290a418e1536048520c70a830242904cc735912148274382c890a41339ce63485209d4e131a429064e7518d2148326ba8c690a41a3d506348520d18a831a429046e76d4d214832631ea690a419318d5348520ac8e2a9a42906c463d4521482a6b98a290a419318c5148520e4ea828a42906c46314521482973ae8290a41a318f4148520a58eaa0a429068c63505214839228a8290a41b218f6048520d96c6302429043f76d50214821ebb6a810a410fdd8540852087aec2a0429053571150214830faa4c610a41871526308520c3ea8b18429061c5458c214831daa4c010a418e1526008520c58a9316809062e6590a4048317aa0c4a024187d526310120c38a9318809061f5458c404830e2a2c6202418bd526210120c58a9310809062f5458840483162a2c4202418b9964210120c6ea9308809063454984404831baa2c2202418d1516110120d4c84b0880905387550040482d43928020241ac5854010120c58a9316609062c5458b304832629ac5982418bd52628c120c58a9314609062f5458a30483162a2c5182410fdd1654c120878e8b2a609043e76d51304821e3b6a8982410f9d8544c120878ec2a2609064d650c9304829c3aa8390241b858721c8120b90e690e409061f5498e204830e2a4c71024187d516388120c38a8b1c40904ce73d922048347aa4c710241a31526388120d1cc7a0c409052c75506204834731a8310241a95854188120d94c7a84409045d73983540821fbb2a82a041875516315020c6aa8b08a81061e6458c540832731cc42a0419358e6215020cacc7308a810655639845408333314c22a0418d9916115020cacc6b08a810655635845408333312c22a0418d9d16115020cb2c7300a81067161980540821f3a4c3a98410f5d261d4c2087ce930ca61043d74986530821f3a0c2a98410f5d06154c208beeca98a61061d6454c530832aa9ac2298410f5c66414c2087ee2b20a61062d649885
  | 8 => 0x660cc920d56a930664906a8549833248274b8cc199241551c5538c9208bcec29a649070f544c832483862a264192411b9d7640c9209d0e0b20649062e6515032482e4b84a6192411bdd9530c920ac8e2a9864904cf7654c3248387aa2a619241c3151530c920b88e2a9864905cb7054c32482a7bb2a61924193dd9530c920e1ee8a98649070c7454c32483a3b8aa619241531c5530c920e88e2a9864905447154c32482a7b82a619241d2dc1530c920c9aa6b08649053571d93514829ab88c9a8a410f9d263d452087ae931ea29043f7458f514821e3a2c7a8a410f9db545452087cec2a2a29061f54d8d514830e2a6c6a8a4187d506354520c38a831aa29053571d50514829ab88a828a4187d526314520c38a9318a29061f5458c514830e2a2c628a411ddd95114520aa8e6a88a29061e6498c514830eb24c628a41879916314520c3ac8b18a29064f7258c5148326392c628a41951c563145208daed990a29064d63cc85148326b186428a418e9916014520c72c8b00a29065a63580514832cb1ac028a418b15262d0520c58a8b1682904e87058b41482963aa85a0a416a1c142d0520a3ce7b2e829051d73d97414829ab8ecba0a414d5c465d0520c5ae432e829063571197414821f3b4a7a0a410f5da53d052087eeca9e829043c7654f414829bb8aa7a0a414d1c553d0520c58cb316829062c6558b41482d4382c5a0a418b99732d0520b54e1996829062e650cb4148386a9865a0a41479cc51d0520a3ae628e829045e73196414822eb98cb20a418bd526290520c76a9304829043e76951414831632c84a0a414b1d54250520c58caa1282905a870509414821f3accaa0a414d5c66550520c6ae332a829051f73595414828e39acaa0a414ddc56550520a76e0b2a829062d72195414821f3b4a6a0a410f5da535052087eeca9a829043c7654d414829bb8aa6a0a414d1c55350520a6ce229a82905357114d41482973acc4a0a418b1966250520b4ae3312829052c75589414831632ac4a0a41631cd6250520b4ee2b1282905a870589414831632e64a0a416a9c33250520c58ca192829070d530c941482d2b8864a0a41479cc5150520a3ae628a829045e73194414822eb98ca20a410f9d6641052087aedaa0829062c54988414831c2a4c020a410fdd165cc520878e8b2e62905557314731483a3990a398a410fdd1658c520878e8b2c629043e74196314821eba0cb18a410f9d6648c520878eab24629043f76d52314821ebb6a918a410fdd8548c52087aec2a46290535711523148364192c118a410f9d3654c52087ae9b2a629053571151314822f3b4a698a418bd53624c520c58a9b1262904ea70d893148317aa0c498a418b150624c520c9ca631262904ce76cc9314832632e6498a410fdd1650c520878e8b28629043e74194314821eba0c
  | 9 => 0x2a6b00831043e74d96318821eba6cb18c4187992538c620c3ac929c631061e6454e318830eb22a718c419654e608c620cb2a6b04631064e53d893188327298c498c419354c624c62087ce9b28631043d74d94318830f324a618c4187592530c620c3cc8a98631061d6454c318832729cc418c419354e620c620c9ca6b10631064d53588318832ca9cc018c419694d600c620cb2a6b00631061e6494e218830eb24a710c41879915388620c3ac8a9c431063564946218831ab22a310c419654e6088620cb2a6b04431045d75d8d218822eba8c690c41179da53486208b8eca9a431045d7694c218830f324a610c41875925308620c3cc8a98431061d6454c218832d29ac010c419654d6008620c9ca7314811064e5358a408822ebacc62044117dd563102208baed298811045f7654c408832729cc4204419354e6210220c5aa8b10811064e535884088326a9ac4204419594e6110220caaa7308811063654584408831aaa2c2204419594d6110220caaa6b088110719535004088358b0a80204419394e628c220c9ca6b14611054e73d532088326b2ca7904419359553c8220e1ca7a0e411070e535072088392a8a83904419659653c8220cb2caa9e411058e73d8b5448296b96c7aa2414e5c363d5120a3ce7b16a89051d73d8b544828f398c3aa241475cc61d5120a5ae430ea89053970187544828f39ec1aa241475cf60d512087eecaa0a89052d72d8c5448296b90c62a2414d9c46315120a6ae2318a8905397018c544828f39ec42a241475cf6215120a6ce3b10a89053571d885448296b96c22a2418b58b6115120c5ac4b08a89051e73184544828eb98c22a2414b5c86115120a72e0308a89043e74987534821eba4c3a9a410f5c66494d2087ee2b24a69062e6458a534821f3a4c329a410f5d26194d20c74c8b04a69043e76d51534821f3b0a8a9a418dd536154d20c68a9b0aa69063754185534831a2a0c2a9a410f5c76454d2087ae2322a69063764d85534831a326c2a9a418ddd36154d20c68e9b0aa69043e74185534821eba0c2a9a418dd906154d20c68c830aa69066762185534831b3a0c2a9a418d5d06154d20ce2e030aa69045f7654c53482aa38aa629a410f9d26114d2087ae9308a69047671d97434823ab8ecba1a418b15262d0d209d0e0b16869047771595434823a38acaa1a418bd506250d208f4ebb02869063b54181434823b388ca21a411d5c46510d20c58a9310869062c54588434831c2a4c021a411e1d56010d20c70a8b00869063854983424831732ea9212413a9c2639092099ce7304849063b54181424831632ec8a12411b9d85450920d56c830284904ea7518142483353a8c0a1241aad506050920d50a830284904e97118142483162a4c4212418e15260cc920c70a8b0664904ea70d9332482753acc1992419a9d
  | 10 => 0x64d5318931c82673b66498e410f9d3650c72087ae9b28639064d650c831c8364192c018e411bdd953c8720c98c6a9e43904ce7398321c826639ac890e413a1c16448720c9eca31a439064d7518d21c8365380c690e41b25c06348720c98c6a9a439064c6394521c834631e8290e41a318d4148720ce2a2b00439051e73d5240c821f3b4a8a06410f5db5410320a3ce7aa081906375458440c831a2a2c220641a99096110320c9cc6b16a910659639835488334b14c1aa4410fdd95415220c6aa8b08a91064e635885488326b1ac42a4419598e6115220caac7308a91066562984548831b322c22a4419598d6115220caac6b08a91066562584548831b3a2c22a4410f9d261d4e2087ae930ea71043e74986538821eba4c329c41559c45494e20aaae22a4a71054d72d9253882ad380c929c41479d36294e20a3ae9b14a71051e74986538828eba4c329c4153dc96194e20a3ce830ca71051d7418653882a6b90c329c41569c06194e20a3ce8304a71051d7418253882ab388c129c41555c46094e2087ce830aa71043d74185538822f3b6a8a9c41179d85454e20aace22a2a7105557115153882ac382c8a9c4147dd16254e20a38e8b12a7105577158953882aa38ac4a9c41479d26154e20a3ae930aa71055a7098553882a7b92c2a9c41479d06154e20a3ae830aa71054d7218553882ad380c2a9c4117dd95314e208ece232e871047571197438832729cc521c419394d6290e20cb2a7b02871065953181438832d29ac021c414d5c45490a2087ced2a2851065953d81428832ca98c0a14410f5db5410a20a6ae22a0851065a53583328832ca9ec099441879925394620c3ac929ca31061e6454e518830eb22a728c418d9c66494620c74c9304a31063964982518822ebb4a628c41879925314620c3ac9298a31045f7654c518830f322a628c418759153146208eeeca88a31063564544518822f39ccba0c41175ce65d0620a3ce7aa6831051d73d53418828f398a9a0c41475cc54d0620a6ae3b2e831051e73997418828eb9ccba0c41479cc65d0620a3ae632e831053571197418822f39ccb20c41175ce6590620cb2a7304831065953582418822f398caa0c41175cc6550620a3ce7aa2831051d73d51418829b38ea8a0c41479cc5450620a3ae62a2831053671151418832729ec4a0c419394c6250620a6ce928a831051e73995418828eb9ccaa0c414d5c66550620a6ee2b2a831051e73195418828eb98caa0c414d9c75350620a6ae3a9a831070e53d894188387298c4a0c414d5d76150620e2ca7b0a831071553d85418838b29ca2a0c41c554e5150620a6ced28a8310636769454188399384a2a0c41c594d5150620e2aa6a8a831053676545418829a3b2a2a0c41c9d895150620e48c4a8a831045e73994418822eb9cca20c419654e6010620cb
  | 11 => 0x1022e39aca90881179cc65484408bae632a422045d75d8d211022eba8c690881179da53484408b8ed29a422045e7654d211022e3b2a69088193d8e5248440c98c7292422062f645492110327b1aa4908819318d5248440caec728a422065463945211031bb22a2908818d1915148440caec6a8a4220654635452110334a96c0908819c54760484408bce7b28422045d73d94211022f39cca10881175ce65084408baeb318422045f7558c211022fbb4a610881175da5308440c3cc9298422061d6494c211022fbb2a610881175d95308440c3cc8a98422061d6454c2110317324a4108818b5925208440c9cc7290422064d639482110317322a4108818b5915208440c9cc6a90422064d63548211031ab24a2108819598e5108440caac7288422063664544211031ab22a2108819598d5108440caac6a88422065a53980211032ca9cc0108819a54a6008440ce2a3300422065a53580211032ca9ac0108819a9496008440cd2a4b004220672515802110338a8ac010881c354d52d0040c6ac2a8e8020726525474010392a92a3a00818d98951d004087aed2a480204797695240103a4a9aa520081d8549519004087ae3b2a802062f659494010317b2aa4a0081c354d5250040c6ecb28a802043e76545401031bb0aa2a00818dd955150040e4ca4a8a802072552545401031b3b2a2a00818d1895150040e60e0a8a802066b659494010335b2aa4a0081d254d5250040974eda128020673659454010339b2aa2a0081cc9515150040ec2a4a8a802053975905401025d3b082a00819358e62d5320cb4c6b06a99066a6258354c828f39ea92a641479cf645532087eecaa0a99051e74d4e53c821f3a4c329e410f5d26194f2087ce830aa79043d7418553c822fbb2a629e410f9d26114f2087ae9308a79047671d9743c823ab8ecba1e419354e62d0f209d2e530487904767119443c823ab88ca21e41339ce6090b208dcec2a2859063a5458042c8275386c9996419694d600cb20a9eeca98659064f7654c32c82a638aa6196419354d610cb208daec194a39043e74d8d51c821eba6c6a8e411ddd951147208bce7b2e839045d73d9741c822f39ccba0e41175ce65d0720a3ce7aa6839051d73d5341c828f39ecba0e41475cf65d0720a6ae3b2e839051e7399741c828eb9ccba0e414d5c465d0720e1aa6196839051e73d5141c828eb9ea8a0e418ed5060507209d2e430283906aa4218141c828f39ccaa0e41475ce6550720a6ae332a83905377159541c829bb8aa6a0e414d1c55350720a6ce229a83905357114d41c82d2b8cc4a0e41631cd6250720b4ee2b1283905a87058941c8386a9864a0e41695c43250720c74ca30283905a97218141c8355310c0a0e410f9d265cc72087ae932e639043e74d9631c821eba6cb18e4193d94328c720c9ca63126390
  | 12 => 0x190812e5c0640c840a9ae7290642054f754c832102a6baa641908193d95320c840c9aca990642064e6394b5110326b1ca5a88819398d52d4440c9ac6a96a22056672d4651102b2b96a32888117dcd62944408b8e6b14a22055673d4a51102aab9ea528881d194e5294440e4cc9294a2207465354a51103a2a9aa528881c91d15294440e4cc8a94a2205567314a51102aab98a528881c954a4294440b62e0214a22053674d8a51102abb9ac528881551cd6294440a6ce8314a2205567318a51102aab98c5288815c9c06294440e8a64194a2205667218251102b2b90c128881179cc62544408bae6312a22053571909511029ab8884a88814e5c042544408eceda92a22055673d4951102aab9ea4a8881d194e5254440e48e9292a2207266494951103a329aa4a8881d154d5254440e48e8a92a22072664549511023b3b0a4a8881559cc5254440aaae6292a22053575909511038b29c84a8881c554e4254440e4ca5212a22072552909511038b29884a8881c554c4254440e4ca4212a2207255210951102d8b8084a88814d9ca6454440e62e1322a22053674d89511029a3a2c4a888155dcd6254440aa8e6b12a22057070589511029b3a0c4a8881559cc6254440aaae6312a22057270189511029abb484a88814d9ce4254440a6ae1212a2205727010951102b8b8084a88814ddd84254440a6aec212a22053673109511039339084a8881cc9c04254440a6ae0212a220731701095110298b8084a88814d9d23254440a6ae9192a220572708c951102b8b8464a88814ddd13254440a68e8992a220537740c9511029a3a064a8881d14c83254440acce4302a2205657218151102b339080a8881595c840544408daed290a22064e639485110326b1ca4288811bdd95214440c9cc6a90a22064d635485110333294c2288819954a61144408eeeca88a220666625445110332b12a2288819c54560d0440e1ca7296822062e6254b411038729aa5a0881c354d52d0440c5eeca968220726525474110392a92a3a08818d98951d0440e62a33068220635515834110398a8ac1a08812edd560d0440c76eab0682206aa525834110354a92c1a0881ac94560d0440c72a2b0682206b1515834110318a8ac1a08812e5c06250440e1ca7292822070e535494110386a9aa4a08818b1d95250440e4ca5b0a822072552d854110393294a2a0881c954a5150440c6ecaa8a8220726525454110392a92a2a08819a54a6010440cd2a4b00822067251580411022f39ccb90881175ce65c8440972e0326422062f6454b211031a322a390881179ce65884408bae732c42204b970992211030f324a710881875925388440c3cc8a9c422061d6454e2110317324a5108818b5925288440c5cc8a94422062d6454a211031ab24a3108818d9915188440c6ac8a8c422045f7359521
  | 13 => 0x60d0740e62a2b0683a05357194941d029bb8aa4a0e816c5c3515074096cec28a83a06b14158041d022fb9aca90e81171cd65487408bce7b2843a045d73d9421d02a739ea529481179cc6154a408bae630aa52046f76548529023bb8aca994811d1c5654ca4096ae232065204b97019032902a6b9ca41948153dd5320ca40a9aea99065204b874580329022fb9ac528c81171cd6294640a58e4b22a32053571109519023bbb2a228c814d9da5150640c6ced28a832073151d814190398a88c0a0c81179ce65c86408bae732e432045f73595219022e39aca90c819318e5248640c98c6a92432045e73d94219022eb9eca10c818d58551d0240c9ac7a94a4a046f76548525022fb9ac229281171cd6114940a9ce7a9264a047671194325023ab88ca192810f9d6640c940c9cca99064a064c654c8325022f39cc5a8a81175ce62d45408eeeca88a2a073351d814150399a88c0a0a812e9d46050540c74ea30282a06aa721814150354b90c0a0a818e1486050540c76a230282a063665504415022fb9acb10a81171cd6588540970e0b2442a062d6414a215022f39cca90a81175ce65485408bce632842a045d731942150316b26a410a819358f5208540c9ac629042a066b525802150334292c010a818d5875190140a9ce7a94a42054d73d4a52102b338ea529081595c752948408bee6b0ca42045c7358652102b338ea729081595c75394840a5ce9b1ca42056a70d8e5210326b18c7290814b9d26194840a9ee6b0ca42054c7358652102973a0c329081539cc6194840a9ae630ca42056a7018652102a739cc129081535ce60948408bce630aa42045d7318552102b338ea6a9081595c75354840e18c929aa42070c6454d52102973a4c6a90815a9c26354840a58e8b1aa42064d6318d52102973a4c2a90814b1d16154840a9ee6b0aa42054c7358552102b4382c2a90814b9d06154840a9ce630aa42054d7318552102b5380c2a9081539ce6054840a9ae7302a42054d73101521022ebb4a62908117dd95314840c9ca7310a42064d539885210237bb2a4290819398d5214840c9ac6a90a42065653984521032aa9cc2290819954a6114840caca6b08a420655535845210332a92c2290819a54960d0840972e131c842061d6554e4210316b2ca521081c394d5290840e1aa6a94842062d52586421025db82c3210819654e6010840cb2a6b00842066a525804210386a9aa421081aa9896010840976eab00842063b75580421034d29ac021081a654d6010840d54a4b0084206a952580421023b38ccb190811d5c6658c840c3cc8a9c642061d6454e3210316b24a5190819654e608c840cb2a6b04642066a52582321023b388ca990811d5c4654c840972e0322642062f6454932102a639aa4990811d9c6650c8408eae3328642043d75d90321025ab88c8
  | 14 => 0xec18ca010d3a740c6500869cba063280435a9c83194021ad2e418ca010d3a74886500869cba4432804356dcd2194021ab0e690ca010c5e73191500862eb98c8a8043531cd2154021e4a8290aa010c7a76d5150086ad39ea8a8043565cf54540218f4ec2a2a010d5a7315150086acb98a8a80431e9db5354021a74e9a9aa010d3974d4d500878d2a4a6a8043c65525354021e90e529aa010f1a5454d500878caa2a6a8043d21c953540218f4ec29aa010d3a7414d500869cba0a6a80435a5d73254021e54a9992a010f2954cc950087a529e64a8043d254f3254021e54a8192a010f29540c950087a529864a8043d254c3254021a72eba0aa010f1a53d05500878ca9e82a80434edd54154021e34a6a0aa010f195350550087952a642a8043ca5532154021e94a790aa010f4953c855008798aa442a8043d454e2154021ad6ea90aa010f2a544855008794aa242a8043721cd2154021e94a690aa010f495348550087d0a0a42a80435cdd52154021e62a890aa010f515348550086b4392c8a8043569cc6454021ab2e6322a010d6a7219150086b9388c8a80435a9cb6354021a76e8b1aa010d387458d50086b4392c6a80435c1c56354021ad4e5a1aa010d6972d0d50086b938e86a80435c5c74354021ad6e4a1aa010d687250d50086b938884a80435c5c44254021ad2e3992a010f49320c950086b938864a80435c5c43254021e94e6192a010f4a630c950087a4b1864a8043d89c43254021ad2e2192a010f61710c9500869d3a4c2a80434e5d26154021e5665a0aa010f2832d0550086b539482a80435a5ca4154021e5664a0aa010f28325055008799b8a82a8043cc9854154021ad4e420aa010d697210550087a599662a8043cc5073154021a74e918aa010d39748c550086b539462a80435a5ca3154021e906518aa010d6b724c550086b439262a8043d2cc931540218f4ec18aa010d3a740c5500869cba062a80435a9c83154021ad2e418aa010f48320c55008798a0862a80435a9cf2154021ad0e790aa010f2b41c855008794a0e42a80434e9d22154021a72e910aa010f314188550086adb9a42a8043561cd2154021e628290aa010f4b7348550086b539a42a80435a1cd2154021e90e690aa010d487348550087b1b8a42a8043cad052154021ec48290aa010f294148550087b0a0a42a8043c85052154021a74e810aa010d397408550086ad39842a8043565cc215402187aed2a0a010c3f76550500870f2a4c628043875526314021c3ca8b18a010e1d5458c500862ebb4a628043879925314021c3ac9298a010c5f7654c500870f322a628043875915314021c74a9300a010e3954980500872d29cc0280439654e60140218f6eca80a010e3a64540500871cb22a0280439698d5014021cb2c6a80a010c6f7654852d023bbb2a228e81cc546
  | 15 => 0x4e535883108726a9ac41884393594320c421b8ae21906210e35655043108752b128218843e10c9410c421ad2e1a9e4210c6f7654f210872731aa790843c395153c8421e1aa8a9e4210e4f7654f21087263b2a7908434b5d741c8421e1aa7a0e4210d2f755072108786a9a83908430f5da548842187eecaa44210e1e6494e210870eb24a710843879915388421c3ac8a9c4210c6d7694a210878aa9a8310843c555153884218eaed2944210e1e54d8d210870eaa6c690843879506348421c3aa831a4210c5e7694d210862e3b4a690843179d95348421c6ecba0a4210e3765505210874a31a8290843c554d4148421c9ee7b2a4210e4c73d952108717b2ca8908438bd955448421c9ecbb1a4210c6d7598d210866739cc69084393d946348421c9aea31a4210e8e5418d2108746aa0c6908431b9db5348421c98c7a9a4210d6970d4d21086663b4a690843535d65348421c9ecb29a4210c6c7654d210872631aa690843331d95348421c9ecaa9a4210f0e5454d2108786aa2a69084393dd95348421a9ceca9a4210d4c7654d21087263b2a690843131d95348421c9aa7b0a4210e4c639452108696bae82908438bd974148421d18c7a0a4210f0d53d0521086d2ba48290843b118e4148421e8aa720a4210d2f755052108717b2a8290843a318d4148421e1aa6a0a4210ec46350521087a2a9a829084369dd54148421e4eeaa0a4210ea7655052108793b2a8290843e1d8d4148421d4cc6a0a4210ea46350521087c231a8290843a118d4148421e4ea6a0a4210f86535052108792a9a8290843e154d4148421e0aa6a0a4210e5773d95210872a39eca908438dd965448421c6ecaaa24210e5765d8d210872bb28c69084395d965348421caecaa9a4210f155454d21086d2ba6c490843b118f6248421e8aa72924210e1e5498f500870eaa4c7a80438795163d4021c3aa8b1ea010e1e6494f500870eb24a7a80438799153d4021c3ac8a9ea010d3a74d42500869cba6a128043569cf5094021ab2e7a84a010c3f7458e500861e3a2c728043569cf5494021ab2e7aa4a010d5a7315250086acb98a9280434e9d35394021a72e9a9ca010f1a5494e500878caa4a728043c69515394021e32a8a9ca010f487254e500869d3a0a7280434e5d05394021ad2eb994a010f4953cca50087a4a9865280434e5d74194021e34a7a0ca010f1953d06500869dbaa8328043c694d4194021e32a6a0ca010f4953c8650086b5baa4328043721cd2194021e92a690ca010fa14148650086b9baa4328043569cc6494021ab2e6324a010d6a7219250086b9388c9280435a9cb6394021a76e8b1ca010d387458e50087a499065280434e9d06194021a72e830ca010d5a7318650086acb98c328043ccdc54194021a74e918ca010d39748c650086b5b9263280435a1c931940218f2
  | 16 => 0x863abacc3a18439554e61d0c21c6ca8b0e8610e5553587430863d384cb218431e5c26590c218f4e032c8610c7970196430863d384caa18431e5c26550c218f4e032a8610c79701954308716aa6c4a18439354f6250c218daea3128610e4d53189430863d384ca218431e5c26510c218ece23288610c7a70194430863cb80ca218438d5516190821caaa73088410e3654584420872aa9ac221043939cd65cc821c5acb2a66410e2d6555332086b4b86a7990439359653cc821e1ca8a9e6410f0d5454f3208726a9ac3990439554d618c821c9eca9906410e4d654c832087872a26419043c3551320c821c6aa93086410e3554584320872b29ac219043535d6630c821c9acb3186410d6970d4c32086a6baca6190431bdd9530c821c9cc6a986410f0e5454c3208786aa2a61904353dd9530c821c9eeca986410d4f7054c3208637baac2190439354d610c821d8cc6b086410c6d760ca510868f39ea9a0843475cf54d0421a74e1aa68210d3970d53410868f398a9a0843475cc54d0421a74e02a68210d3970153410861ebb6a7a08434e9c353d0421a72e1a9e8210e1d6594f410870eb2aa7a0843c31c953d042187aec29e8210d3a7014f410869cb80a7a08434b5d732d0421c5acb9968210f0d53ccb4108696ba865a08438b59432d0421e1aa61968210e4d5398a4108716aa2c5208439354d6290421a3ce7aa28210d1d73d51410869d386a8a08434e5c3545042187cec2a28210d1e73151410868eb98a8a08434e9c05450421a72e02a28210c3e76d4d410869d386a6a08434e5c35350421a3aeb29a8210e1f6594d410870fb2aa6a0843c31c95350421e28e2a9a8210c3e7614d4108697390a6a08434d9c45350421a74e029a8210d397014d4108696bae64a08438bd973250421e1aa79928210d2d750c94108717b2864a0843c354c3250421b4ae21928210f1653d85410878aa9ec2a0843179ce65104218bae73288210c5e73194410862eb98ca208430fdd95410421c3cc92988210e1e6454c4108726a9cc4208438b9516210421c9aa6b108210d4d75ccb3108726b2e65988438d59541cc421e2aa6a0e6210f8732507310861f3a6cb188430f5d3658c42187aeb3246210c3f75592310861fbb4a9188430f5da548c42187eecaa46210c3d76552310870f324a71884387592538c421c3cc8a9c6210e1d6454e3108726a9cc5188431bdd5628c421c9aa6b146210e4f650ca31087172a6c4988438b553624c421c9ca7b126210e4d53d8931087172a0c4988438b550624c421c9ca63126210e4d5318931086673b66498843535d7324c421c9ecb9926210c3e74994310861eba4ca188430f9d0650c42187ae83286210c3f76950310861ebb4a8188430fdd9540c42187aecaa06210e2e549883108716aa4c4188438b951620c421c5aa8b106210e
  | 17 => 0x8a43e18c9418c521c9ea63126290e4c53189314872632a6498a43711c5324c521c68caa0a6290ea46250531487c29928298a43c514d41c8521c3cc9a9c4290e1d64d4e214870f320a710a43875905388521c9ac629c4290e4d7614e2148787320a710a43c35905388521e18a7a0c4290f0c53506214872629ac110a43179ce64d41218bae7326a090c5e76d4d504870fb26a6a82438719353541218bcec29aa090e1f6414d504870e320a6a82431edd95014121a70e8a80a090e4d6398b540872d31cc1aa0439658e60d5021cb4c6b06a810e59635835408735312c1aa043479cf5495021a3ae7aa4a810d3a70d52540869cb86a92a0434b9cb6395021a6ce3b1ca810d1e73182540868eb98c12a0434b9c86095021a6ce2304a810d1e73d91540868eb9ec8aa0434e9c36455021a72e1b22a810c5e73181540862eb98c0aa0434b1c96355021a58e4b02a810d1e73181540868eb98c0aa0434b9c86055021a6ce2302a810c3f76550540870eaa4c62a043875516315021c72a9300a810e3954580540870f324c62a043879916315021c9ac7310a810e5563984540871d324c02a0439698e6015021cb2c7300a810e3a64580540872d31ac02a0439658d6015021cd4c4b00a810e7261580540871d2a4c1a98438e55260d4c21c74a8b06a610e3954583530871d324c1a98438e59260d4c21c74c8b06a610e39645835308735312c1a9843479d35394c21a3ae9a9ca610d5a70d4e53086acb86a7298430fdd16094c21878e8b04a610d5a70d5253086acb86a929843569c05494c21ab2e02a4a610d1e74986530868eba4c329843479d06194c21a3ae830ca610d5a7018653086acb80c329843539ca6094c21a3ee8b04a610d1c74582530868f3a6c6a9843475d36354c21ab4e1b1aa610d5970d8d530862f3b6a8a9843569c35454c21ab2e1aa2a610c5e7615153086ad380a8a9843565c05454c21e1ca8312a610f0d5418953086a7394c8a9843559c66454c21a98e4b22a610d1e74985530868eba4c2a98439318a6154c21a3ce830aa610d1d741855308726310c2a9843569c06154c21ab2e030aa610d1e74085530868eba042a98439318b6054c21a9ce5302a610d1f74581530868e3a2c0a9843531c96054c21aa8e2b02a610c3d76950530861fbb2a829843879526314c21c3aa9318a610c5f7654c530870f322a629843875915314c21c74a9300a610e3954980530872ca9cc0298438e9516014c21c72a8b00a610e59535805308717324c4298438b5926214c2187ce9308a610c3d74984530871ab24c2298438e9926014c21c72c9300a610e6a62980530871d322c0298438e5916014c21cd4c4b00a610e7261580530863d384cba18431e5c265d0c218f4e032e8610c79701974308636bacc5a18439354e62d0c21c5ca8b168610e4d5358b430
  | 18 => 0x30ca21b8ce3a986510d4d76d4c3288726bb6a619443c39d3530ca21e1ae9a986510f4671d4c32886a6b86a619443719c4530ca21b92e02986510e4f53584328861ebb6a7a0c43c3d4c32d0621c5aa93148310c3e76151418861f3b6a6a0c43c3d4c3250621b4ae21928310c3f7655041887172a4c420c430f5da548c62187eecaa46310f8432506318866639acb90c4353dcd65c8621c5acb2a64310e2d65553218872631ea790c439398d53c8621c6acb2a64310e3565553218861fba2c7284430f1d16394221c9ec6192a110c3d76950508861fbb2a828443879526314221c3aa9318a110e1e5458c508870eaa2c6284431edd95014221cb2c6a80a110c5e73983544862eb9cc1aa2439398d6295121cacc6b0ca890e4c63d89544872db1ec0aa2439618f6055121c76c8302a890e5b63181544872c318c0aa2439ad886055121cd2e4302a890c3f76550544869c382a82a24356dc154d4d21ab0e0aa6a690d1e74d8b534868eba6c5a9a43479d360d4d21a3ae9b06a690e5b6098353486a6b90c1a9a4317dd95314d2187ee8b00a690c3c74580534862ebb4a829a4317dd95414d21ab6e0aa0a690d587055053486a6b96c829a43535c86414d21aaae2320a690d5a7019053486acb80c829a43479d36214d21a3ae9b10a690d5a70d8853486acb86c429a43535cb6014d21a9ae5300a690d1f74580534868e3a2c029a43479d06014d21a3ae8300a690d4d7218053486aab88c029a43965806014d218eae3b2e8690c7a70d96434863cb86cb21a439314e6290d21c98a6b148690c7b70595434863c382caa1a431e9c06510d218f2e03288690e4c53988434872629ac421a439514e6110d218e8eab088690e5453584434872a29cc3a12439514d61d0921a70e0aa48490c3e76151424861fbb2a8212434e1c15410921ca8a730e6490e4f73996324872732ea7192439314e618c921c98a6b046490e575318532486a73aec6992431b9d8534c921a9cec29a6490e4e7614d3248674b80c299243b1d8c614c921c98a7b026490e4c5398b414872629ac5a0a43479cf65d0521a3ae7b2e8290d3571d97414868fb9acba0a43471cd65d0521a76e0b2e8290d3870597414878629cc5a0a43c314d62d0521a5ceb1968290f0c538cb414878629a65a0a43175cf65505218bee6b2a8290e4c53d894148726298c4a0a43479cf6550521a3ae7b2a8290d1f73595414868e39acaa0a434ddc56550521a6ee2a9a8290d1e7514d414878ab88a6a0a43c314f6250521e18a63128290d2e758c9414878629c64a0a43c314d3250521b48e29928290d3675d85414871a32ec2a0a43c5d4f6150521e28a7b0a8290da672d85414870f326a620a439314e62cc521c98a6b166290e1e64d4e314870eb26a718a4387990538c521c3ac829c6290d4e758ca314878a29a831
  | 19 => 0x6a96a2a0db37054b51506d8382a5a8a832ddd932d4541968ec996a2a0cb6760cb515065abb065a8a83e14c832d4541b4ce4306a2a0da572183515064fb9ac5a8283271cd62d4141b62e1a8ea0a0e8f63d895050747b18c4a8283a318c6254141d4ec5b0aa0a0ea462d855050753b16a2a8283a918b5154141d50c5a82a0a0e2c62941505074731cc428283a398d6214141d1ac6b10a0a0ea8705885050716b14a4282834e5c05214141d4cc4b08a0a0ea5625845050717316a2282838b58b5114141a72e1a88a0a0ea662d445050752b16a2282836c5c3511414187eeca80a0a0d2c72540505065dbb2a0282836a1c95014141a76eca80a0a0e3b765405050795b92a0282834e1c95014141e50e4a80a0a0d28725405050795312a028283ca5895014141e66e2a80a0a0f3161540505062f39cc129083175ce60948418deeca90a420e4d635485210734a92c0290831e9c0654c8418f2e032a6420d4c735493210727b2a641908393595320c841e1ca89906420c3d76952411063abb4a9208831edd95014041cd2c4a80a020c5e7398354c862eb9cc1aa6430fdd95415321cccc4b08a990c5f7654c53c861fba2c029e430f1d16014f218f4e1b2c8790c7970d9643c863d380ca21e431e5c06510f2187cec2a28590c3f7655042c86e2b8ea6996431b9d8534cb2199cec29a6590d4e7614d32c87273b0a699643d15c4534cb21c98a630a6590ce97018532c872629ec099643b14c9610cb21e18a69968390f0c534c941c86d238a64a0e43e14c941cc721c3cc7a0ca190e1d63d0650c870f31a83286438758d4194321a6ae2322a190e2e7219150c8716b90c8a86438d9c46454321c6ae2322a190c3e76d0550c861e3b282a86431edd95014321a5ae5b1ca910d367118e548868f39ec52a443475cf6295221a3ce630ca910d1d73186548869d380c32a4434e5c06195221a3ce6304a910d1d731825488696b90c12a4434d9c46095221c72c0304a910c5e73181548862eb98c0aa4434bdc96355221a76e0b1aa910d387058d548868fb9ac4aa443471cd6255221a76e0b12a910d3870589548868f39cc2aa443475ce6155221a74e130aa910d3970985548868fb9ac0aa443471cd6055221a5ee4b02a910d1e73181548868eb98c0aa4434b5c86055221a6ce2302a910e3960181548861fbb2a82a4439958a6115221c6ac930ea710c3f74582538861e3a2c129c430f5da5414e2187eecaa0a710c5f7654c538871d2a4c029c438e5526014e21c74a8b00a710e3954580538872ca9ac029c438b95262d0e218f6e0b2a8710c78705954388716aa0c4a1c438d9516110e21c6ca8b0e8510e3554d85428871aaa6c2994438d550614ca21e1ca89906510f0d544c83288716b2ca8194438b595540ca218daeda986510ccd76d4c32887872a6a619443c35535
  | 20 => 0xe73d8950d064eb9ec4a8683a398e6214341d1cc6b10a1a0e8d6358850d0716b14a4286834e5c05214341d4cc4b08a1a0ea56258450d061fbb2a0286832edd95014341a76eca80a1a0e3b7654050d0795312a028683ca5895014341e62c2a80a1a0c5e73982529062eb9cc1294831bdd95214a41c9ac6a90a520e6952580529063d380ca994831e5c0654ca41a98e6a926520cf1701853290727b2a641948393595320ca41b88e29906520ec532584329063dbb2a0284839a58950142418deeca90a4a0d4c7354852506b4382a4292832d9c660d094193ce730484a0c9d73982425065b38cc1212832d9c4605094196ce330084a0cba70d92325065cb86c9192832d9c6644c941968e2b2264a0cb6741853250678b80c2992831edc1650c9418f0e0b2864a0c7a70194325063cb80ca192832d9c7640c94196ce232064a0cba70190325065cb80c8192838b590520c941a9ae629064a0d4e754c832506a63aa6419283711c5320c94196ce930864a0ec532584325062fb9ac5a8283171cd62d41418f6eca80a0a0d6872540505072731cc4282839398d6214141c9ac6b10a0a0e2f7458850507163a2c4282838b58a4214141a72e0210a0a0cb57198f525065ab8cc1a9283a9d49619494196ee0b0ca4a0c9e73982525064eb9cc129283a318f5254941d2ec7b0aa4a0e9463d855250753a96c2a92832d5c36154941d36c7b02a4a0e9863d815250759b0ec0a9283acdc76054941d36c6302a4a0e98631815250759b08c0a9283aad486054941c74a4302a4a0eb171181525065bb8ac629283695c6521494187eeca90a4a0d38705485250657bb2a429283631cd5214941b4ee2a90a4a0da870548525065ab8cc0292832d5c7658c941974e1b2c64a0cb970d96325065bb8acb192832d9c6608c94196ae330464a0cb571d95325065bb8aca992832edc1654c941970e0b2a64a0cb675d85325065ab86c2992832e9c0614c941972e030a64a0db170185325065b3a8c2992838d9d4614c941d2c6430a64a0eb270185325065ab80c299283ac5c0614c941962e030a64a0cb671181325065ab88c0992832d5c7650c94196ee2b2864a0cbb70594325065c382ca192832e9c0650c941972e032864a0e2d6514832506c6b98a419283635ce320c94195eec99064a0da4714c832506c7bb26419283a3dd9320c941b1cea99064a0d8c754c832507c3b8a6419283631c5320c941f08e299064a0d84714c832506c7b826419283e14ca610c94196ceb30864a0e3675984325065ab84c219283a34c9610c941f0a64b0864a0cb4755843250753a92c219283a9149610c941d4c64b0864a0ea5325843250742992c2192832ddc1610c94196ce330064a0cb571980325061fbaac0192830f1d5600c941b2ce7b16a2a0d9573d8b5150753b14c5a8a8365dcd52d4541b28e
  | 21 => 0xb1aaa2c22a0658e5516015032c6cc8b08a81966662584540cb1b3a2c22a0659c9866015032ce2c3300a81963a64580540cb35312c02a0659c9856015032ce2c2b00a81961d5498e420ca36bb4a7190653a5c0614c832c9aebb2a64194ce71d95320ca66b86ca99065939db654c832a9ae3b2a641954d75991320cae338cc899065715c6644c832a9eeab2264194ce76d51320ca673b0a899065c3550544c832b8ce22a264195c571151320cae5380a899065725c0544c832a9aeb30a641958e74985320cac6ba4c29906553dd5614c832b1ce830a641958d74185320cae5380c299065725c0614c832c9aea30a641968e74185320cb46ba0c299065b29c0614c83299ae030a64196c970185320ca64b80c299065339c7604c832a9aeb302641954f75581320cac7ba2c099065631d1604c832b8ee2b0264195c471581320ca67bb265a8865331d93294432d1cc8994a21968d644ca510cae238a65288658d9c66494432998ec992a2195c4714c9510cab338c64a8865591c53254432c9eec992a21954c764c9510cb263b264a8865d1dc53254432a98e2992a219744714c9510caa238a64a886553dc1325443287ce8302a21943d74181510ca67bb26428865a39913214432d1ac8990a21947776544510cb1ab22a228865b24ca6014432d9264b00a21967151580510ca67bb265a806533dd93294032b96e0994a01943e74986500ca1eba4c3280652d5c4645403299eec992a01968f644c9500cb4632264a806572dc1325403287ae3b22a01947671191500ca3ab88c8a80654d5c46454032c5ce4322a01962d72191500cb1b388c8a80650f5c46454032c6ae2322a01943571191500cb1cb80c8a80650f9d0615403287ae830aa0194cf764c8500cb473226428065a35913214032d8a65308a0196c532584500ca3dbb2a0280658e5915014032e9264a80a01967161540500caa739ea529683179ce6094b418bae7304a5a0c6f7654852d064f39cc121683275ce6090b418f4e1b2c65a0c7970d9632d065d386c9196832e5c3648cb41c3cc8a9c65a0cba7019032d065cb80c819683535ce520cb41a9eea99065a0d4d754c832d062f39ec4a8683175cf62543418f6eca80a1a0e966358752d074ab1ac3a9683639cf5294b41b4ae3a94a5a0c9e7398252d064eb9cc129683639cf5254b41b4ae3a92a5a0c3f7654852d0657bb2a429683a99496114b41d4aa4b08a5a0cba70d9632d065cb86cb196832d5c6658cb4196ae232c65a0e1e6554e32d065ab8cca996832d5c4654cb41974e030a65a0cb97018532d065ab8cca196832d5c4650cb41974e032865a0cb97019432d06c6b9ca4196832bdd9320cb41b1eec99065a0e8f764c832d06c7baa6419683635d5320cb41b18e299065a0d8f704c832d0746992c2196830fdd5600cb41878eab0065a0c9
  | 22 => 0x800c00200a0000010018003002803800000300000040000000000000000000000001c00e005000800400200500000180020000028004000000003000000000100280040000010008018002002001000401a000001801800200200000300000010018000000001000000801a0020010000008010000004000a02a006800000e0000020010002000000800c00000600200200020010000014000000002800400800000380100060010030010004001001000c00a004000800000400a00b001c00600000b001000400f004800402c003002000800c001000000001400900680000020230008034000004000000001c0090020000004000001800c00e00100000000000120000140014001000801800000e001000400200f0000014000002004002c0060000020000008007000001800e00000a801001800f001003400c007007801c030006003003400000800380140040040038004022004001001800000200280080040070038008030001005800000c00200000040000000030000026000005803c00a00200080000060060000008000013003803c002003003000400400e0038000004004aace3a9ca7a145f7654c53d0aab39ea328e85179cc60547428bae6302a3a14777654451d0a3dbb2a028685569c35394e428f4e030aa721479701855390a2fbb2a629c854e1c16454642a6ae3a12a321477765445190aad39ea12848587dd16394242c38e8b1ca12145e731855090a2eb98c2a84851edd95014242cb6a6b04a6a145f7654c5350a3d384c7a8a851e5c263d4542a6ae3216a2a145e739835150a2eb9cc1a8a851ddd95114542cb2c7a84a0a147b765405050a3d380c2a98851e5c06154c428beeca98a621655535845310b2ca9ac0298850f5da54908428daed2a4842143d71d954210a3d380c6a88851e5c06354442a6ae3a12a22143f765095110a9bb8a84a8885179cc60544428bae6302a221477765445110b2ab1aa2288859c54560144428bce630aa02145d731855010a3dbb2a0280859658d5014042ce2c2a80a02164d6398b548cb2cb1cc1aa465965ce60d5232cd4c4b06a91953a70d52548ca9d386c8aa4650fdd95415232c9ac7310a91961e5458c428caab38e64a8c650f9d3605463287ae9b02a31947776544518ca9d3a6a1284650f9d2619423287ae930ca11943e74185508ca1eba0c2a84651edd95014232c6ea8b0ca89966562986544cb1b3a2c32a2650fdd95415132a6ae3320a89943f74583514ca1e3a2c1a8a658d59351945328eeeca88a29963671990514caaab8c6428a658e9926014532c72c9300a29963a64580514cb1cb22c028a65968c960145328ece3326a09947571993504ca1f3a4c3a82650f5d261d41328f6eca80a09943e74984504ca1eba4c2282651d9c460550328eae2302a81943f76550540c
  | 23 => 0x802400001000100020000038000002010001002400e0010000000024006002001007c00100200340220070000004004002000803c0000000000004006002002800000a000000801c00c00000a0010002000000003c00000000000240040000128024006004003800000c00000700080020060020048012002000002000a004002800001e001007805800000000280100000000000004010050000006400e008001001000c006005000401200000080040000030050008002006000000c01000a0008004000001000000000e00500000200000000028028028008008800400e0050020018002000009002801e01b003000c01a001001004401c0050000000002007015001000a00c00a000c0080030018008016000000000400000000080080000080008000000004007001800001700000080420030008000012018001808c01c00000980300080000040000030001019001000000c00080040040050020024000000005800c0060030018010000015003000002e02e0048064000007003000400001a0050000002001000800c00000500180000040120008000004005000800000000000200100060000030008004004000000001200100400000060000030008006004002800401a00a000001c00c00f0038024000005003004c00800d000801c00001b002000402e003001002c030012000000c0000070010010014019000001c038002001800c01400200180000100100008018026003000000000e003000001c02600000300000000000018000022001008000000c00000180540040000000008004008002000400202300f002003200f000000800401b002000000e0000010054000001000001800000000080140040020010010000004001800401c00b001000c0060160010014004000000001003c0210008004000000000002c00000000380100260020078010022000003000000000a001001400401500080000020000038030000007002000800000100200000000120010000026000003000001000d003001002000800100040000000028000000008000001c0000040028000012008001800800000200080000000000068004006000000000001c0010038000004000000002800200c000802400c000000801c00c005000001802c00000f802800e0060028040012015002001000a011001000c0220180000068004001000003400c0010000000004002000800000800b007803c002008002000000a0000010000006001001003000200c007800800400f005000401a001002800401000300600180020000018004028001001000401c00f000001800e00e000002800000000b002c000000003801000200300100400020010008000000001001002800e006002000000200000280bc05000300180240060060000000000006000000400a
  | 24 => 0x586856b0002a4d9b40001ed095800006cbe51366000497308a06f12b000247a16c00097a479a1b1090000351000130ebd9746000027600015f0e3da125476ff6c2c12417bea9b4985bc00065c9fb343e00021868b4cde0000000d3c00041f10f1748e0ed751bd006c67e79d408484148e4731af1d48ff294a5cc25d00002e31098004000007800c0120180028000000045000007001e0050000000010001000800000e0040050004006001001800c01000000080180040000000014000004004802000600400b802800200200000300020060008080024019004000801600100480080000030018000014003000000c008009008802800e00a0018000004003001801800e00200600080020070030008004004008800c05800e0000000002000002000400e00a0000000000006002000000000100000580000000008000002008007801c0000050050000004000000000000000200100040040000020000014001012800000000000000000120030088018022026007800800000700200340000060008018002000000800c002000000800c000000004000c006000000005003800e0000040000001000002c00200100000b4000001001802000a0060010000000002000000c00a00c00e00180040040008010004007001800c00a002008802c008001000001801c019003800000000b0008000002000000002c006000000001c002002003000801000d003000802c00d011000000000000200180000040050010012000000001800000100b800000e002001000402a001001006c000004002000c0000020000000002003004802400201d006808c00e000000000000000400180f400000a00c00080020000038000004001000001c006001001009c000009002001c01a0010008010030013001802401c00d0008010004008005803800000d0008000006000002801001000100b001000c0070008024002002005801c014004000812c0040010000098006008005801000c00000200000020040000000000000001808000200000300040040050018008002004000002000201d004004c00400000080140080000008000000000000000400a0010038008004002000800400a00000380000160000000004012002001005c000003000000000c01400200180360030018050008000004800000a000001000400200200380440040000000000000000006000002400d00100000000030010008002003000803403a0030018010012000001000000000a00280180040100028014008001000003800800300000300180020020004038006002000c024007000801800e0070000024006002008000801200300100080060010018004002001000002802e0010008030008007000000800600000200b40000140010010000007013000403e00d002801000000f000
  | 25 => 0x3cf80000006ef5a400000000000001e0600080ee7fc0000000000d3c00000082129609cc5744750002719b5a2461892b0800074200021c085900052300bc0004613c711dc3ec0af56006900000d53268a1dba88f72f9093c86a3395d7052d5394003fe0e95b5498816886708f898a4710b612803266a10daca9c3fe5a319b57b6e64070a2c477857d0000000254a8400d00009ca000000000183a000576587a000b0c2878000e4ca92b951a55422bbb25e2b374d800046f0e4caa226e11a32e061e8cb0898d069687956c280e098414e2a135700f982914f1fa91b80002b9a5bc43625c250a26c4cae18307026d9e70003c3400191a0001c1b0008dc0005980bf9682000000115800095d5fc14100002c95eccfe1c90872820d7284061e3cf1b7a1c3827801595946e005e5fd830cd50956db09f248de0000001e98ef20003bf9865b807f08001e508f600051c9e5bd16cf9288001200039f68e422c49800000005b48a6ea142b8b4635600021c15fc00090f16927a00006ed0002e759fe00004302329d87f641004dc0000e6000389469497e42000003785290ff317806116cddf06f4836a7e80000015f4aabbd3ba412d21ff49e16600009cd000049893400074e80010060000002db52207c074ba7045880004782ade360485000000039b96068f2ad5a2e9d274200000002f600000010ca7090000000000350000000000015f68dccd45fb527000000025cd792268b70000000233800000000016b8226000e374d4396174a764495b138b2aea918e0d1c7d6bcb00000005eadf93ff0000f210004b1825d5f0e670001ccc7245ff605812017447a0e08728d76d186b58000000000000054052358b05a00015420000780000bee4ce43b0aa80002b200008c50664e93ca6f899b81e12ec2eb5b1cd1b5af0314c8ecd5406ef4846e18c80f97bc313a506710e8134ecf80e28ec0bf2c095e205caec0dd8041cb90e44ac3324a9f8c541ae14f996ccc4a260bd2f1d2e6244d0b971da7a0ab422cd617a6b222f1a8bdc74a896b801cdc1674d0000000d581a65d58000aa600030fade483ad9d000021754e00065c58c0214e033fb40000e0bff19012bd9761d0931800000000008bc0015f83ce6542f9d00ccbf3020000dbea0c68580011e44bd0002224618e8e3862c502ba5fd5371c8133e000073c0fcc440002ce3484c7ee7a5181f3942caa632095d87ae61c71120c02744d310280498a60003d71cf5bfa5b84603830000af410f800000007b800026848ba2e41e80000002bbb3b9bf4fe687e0002c18000b6e0f28ebc488b00000166d7946892b10102aa44a85f0105c140a6a8d5396ab4a7b2303a7305c236e0231884b7cce2957b19c752b2125806105aa8582840001a65353702b2bcebe00069fec68180671589190d10000055e8c141ecd16511876
  | 26 => 0xb20006645e1000000071f00000007b27ebddb17773a6d3701e800017ea8728720c80000000000000418bf600030f0e3621d0d9800000eba02dd841faee0002522c100000005c58000a9400021955f1932e080000001158b2f65e150a6894f780014fc07631823bd5645990cb291c4ac9a4514b7fb9f900b2045bba86d1145b7077aa960007692fdc6558baae136700002aa0000001e941f0d8600034200a2bf744ea0dc1948a4714190967cca2000372c65831b5294c2884a1fd0be00d9d6090660800010d215a0f331ad025e8938700011aa00001cc001c808922498000a0e0000000fa55a05692b618244c400042053d433613d3f9579895ce52dc42635152df7527a40c3e0e7130f0e147b8dd06d2af040000003a4810c0003cdf289711ca09c7593268059aa2008d804616a044800156968e20f4531e6553e97600037250944b15b9800000063933521db0c00001bb0b0cd0e2ac000046a7de3380000001c2200000a87f7c020006fb28c400081e0000000000000000172401ce4b0002a8c0006ce8a335fd8d7c8e6d130992289502ff0440e536e300034cccf84493e104fd0e623e0003ad8000ca942d01688e96830001a8d0da000628b16d09d13849c80015a83015da99a05cab0927b80004d29d973902ecef41fa1e924240003756aeb008000c7a4408b2dca13f3105a8280f44f36450b6d34ca0800014961fa00000007b06ac0006a080004bec421d600000000001ce0620000b20211198c0006962ed165168ad3e0002189a72ce1cb8935c000a9468135647f6a9c0002154000a4b6458000b0400054406dd10a00062aa7f400037689f282c80d101a950000000a183461b714cc78b47207415df1ea0e788e4d5ca62541ac700008cc0000001bda51853288b861299e5963af1428d6c382911cda0a744c70000bbc4da3a180000000ce72b32553462192d127241c608365e800198468200000015680003aa00000a37ff0359cc0748cd6381842400000000028f2f007da0000000000a2fcaf08258506cde8280016fc00051f00000681270001403c5c0005b1400000011d046c5c155400040c99d40002ab00012a9726000000000000000000000000000000003a095a90000000dd20008e066880007fe3743a0834000000000000009d60000000000c700000001380000000000100c0007e2346aefe81e5d580038780007dd0ee000000043a0000000000a974168000000adc000000120e38600000018e2000548b89c0002b42f39f80be00000000000000000000351c0000004920001844411f1d8ca4000e6f034000185c0001aeb23d26095b17d80011ac69d36db0352fa222200ade96dea6dd9692340d4a61226489558c40d0dd9691bf04b80214191c36a070000a5c8b200000000002160000002e353ca00000000014c80000001be9c8a00
  | 27 => 0x30241481c69e19e8398e7d566916804191809adda95827674c20a339c892539bc5851e84295818000000a65f492ccc000a441e3a24d5348e611c0e40000968672400000078c21699d800046a0000000906000637a51d031d5270b36d80006e862d182a8017ad01f173dcf80000003ac8000aa800006080009ec08b0ad525471300026044d60f12bd97b450bcac142944d216b72356aecd3c0c130000cac39f22d55118f8fbea3aec8b39813c1c23f7834940216febeb7f05c0cfa48900000005b43b933a4efa18e004f4b9996a6a509895d9a02801b438f0d524b752b835c39156f4412d356c6e6000004008d01f300000014522ee13f0b5000000044aa09daf68e98001ed40005446c580018c2000474b03ced0c6c0002455b1493809189f578a2004c28000f822248a61a7c7563fd6d7f020c005a33dbb33d68d49d56706a2e4e00013aae6955d54b69db7d47183d0065c0001db00070f8ae00003e1000098ea2825900024840006b100003ec00000043e34d0000405800000072ade10001bb800033e4b59e44000000660ad24000cfa800242fa5dc7d206f41f50478dc212664c969ed73c1eec00000000000000004e4000000138000017d103000000039f06d125031168c94340000000003648000a7352127a4000172000180c00029a00000000003550000000003d2f060b1c105655b1cb8298066b0a40919b0e2dcab2964d707c858a392800173c3f761609ca4e4ea7175800065e0003b680005754f8027400154feb5462aaa56476612bca11409e03aee722898963e19dd2167744088545926476a03498b8b1d8f077800000010f43f6698800002600055d0aa4000418000088087e7a400020f2e5fdb3acb1b190582d371a8000000cd20bb36000000e8800255c88490453580006d4000000000192e3732812784a42b70000215017fa8f259373ca5080f3940000b78ea82084001928a77000000000045700029785be0005ec1a6052028a23ac75400000000014b800000047f000000075a0001fa16f088e54176203b6e46352badceeadbd2861c180006ab1ea07510091cea93221f116000179b69000005c33ec0000005645751b21704cd3072c00184e0001dc000018e80b0000aa0000000000000154aae407980010d60540002ff046c1c0dc500017a20000000634a821574298001d360006400000000bf90000000632bc8000000000000023e8001be859ddfe85ac572dc20c5394918460d1e53640598cc96caa2a1cae0000002244000b2900023421a80000002344ffb00000007c854e01d21380000005770000000bf800000015d40000003f72c4dd767d570d03b868404d0000000bac6f1000000020537e00023c54924e326600012b200025f886831b9a556b000182231d000000089ec04290265800007509215f800000071e83
  | 28 => 0x70c34a0300b306563ea000596cf59cb46c91bb816d8ec580da8276cecf4940002eeb6ea36136b0f98d3600024409f116c0000000000eb63e4dfa80007d4679008400000075900030a43f0dfe3fd1cb946c23289e043899edbc0061d1c000540400800049267187f0000860c5c6b980007122b70460b3b9e2db7673a49938837d3f616c1c326e509b2a740008103db0f18f36867800000041c46261807902320000000c180000005c835f8a603a103c59c0f887e93e6932198152445026f8446c2b37e10718e60966a68285ae459a3120cf15c9000619800038b00000015b89c463300000000008680f880000000000000000f90e9410a8000000229b5c1b64000732522cc9651ba3b2d732eab265ea0002fc60002bca462bad874c460002f910ee19a000264c033e0700003710237edbcf02954826628000000000017000000035785c563800165c087631800000027a00009eabe8823130908cd880002096e55b28000577841095d69e757a40802c00038acedc67b6d20002035562cf080033f15720000001980000859695059000000073580000980003e79ddc0437a34b716210720000000c21b08a4e3172bc65229ad6911b00b17a563ea000008a9346758c2d3b01be4680185a148472aa8bdd296b47875265106226c3b5ae181ced463ae2ea99e0bc9845558d82407b00022781300002c300014b800000036a6d1654c4693898bc2758677118d2a845d21a1941ab000008a00004f268f460c000c3400073b379ccba13155af6811b2b1e1a48fd17cc04000000002240000001b3032800000001d864f9f20e7195c00000000014bb9200006d1afc406300006206755d20000cb800046a45c31a894adfc3345b480015707d31d948a800000000037c800051600037c43bee025fa73f31f83f10e1ba89ade3e3881b374000000000000000000017600011600000bdaa4962e0590c54001b1e00006a73394a2c315b8b8540005e51ca0ef9bbee2d23580000008c300009b51d86de47fa6b8c040002172ec0e78071000003e00093b00036988e4c5780022ac9bedc80ec2fd0ce400b2fa800000000000013f1d400002e426915aab6200000000000004630000c8f00000000000000005240000000c39709000000000071b2e64000a786620b59aae90816551fb264cd92ecab9d0e29953c196846daa8667695a0000e5c2689bac4ec5150e25e80900cededf80010540003da00000efa3a4099820000bece6b80017d40000002cad7ca0000000000edca7a3fc00000000003bda67400000000018409b2000000000000000067a9b5cca6748800343473c0003c9128800049853923a8d34ab8ead8d69a6c922000036921a7214cb80013f2e0f014e414000dff8b10000bd8a9d874ee8d31800042d6140df65855cb9954fcabf00000646000aa40001e880000
  | 29 => 0x3c08239c4818ef2216a80ac8be69698e99f132227da0bda9825b55445c528c4fe1441d8c24043601e05e47c486f0000000000ad700020300000000002a299f6b6d800306c3de4cd00012e80004dd4c90001702cdb0000af09a00000f4800072c0000002010aa8b7d5b282143d00000002cec0000002a780000000007098240cf60f08000000d26000558009a00000000000015180004670e205622b3000000000061d0000001ad20000000000000dd2000318083c99b00032d600010c5aead6cf05bcf97f4b040009c80001919098b0e012aab8682000723869a50c000117c000424a041d4122d2620000002d0048a813e122fb4fc8a6f0fcac4563065107201f84e20002d78001aa000052a9028000000000189c2447861e000012360001041e4cd408c77161418c587466d81b84a8a00021431c8e6cb943ee23a1466118bec31159f71016c3b92803151f55d921d7bf4b620a1b443f5c743f814cd1b0ae35936d699ee00028286a4b648e88fe3a06000a5f40d82c86879f026534ac78688329b91615453fba137af5b01b5544e3850cdfc8c57605cdc723e8dab043c2669f14a6acf17427c767b15e0e3c87f6348b1955e7ab0a8a0f9770196bc3c200bf4080af88935d62e7329b234dc602cf2d9a556fc64482100f8c87c02315307587f89dc6b41cb54ec0524288f3c7647f19b00e9ce9cda765d3a940fa000000027167228f1818508000acf5e7b590a86ebe0000000dec00052c35c45c49000003028000346491b6048c809345d2dd938a0000420ef58cf0000001cb0c2c0000210efc03736273628fce562e725d890c496788540490ef20c93420a928dea0654f98cdc000a5206793e3a920cc1872558a7cb6664faaf83ad6a439b86e0dce0df20594e509e691055275cebab8f38d21cea06000000238c0001532ba02f1902b619db0e2c6f800022f90ed3009986dd80012eec0556d000000016e40d00003b42ea126eea4000bac0001738000000000345400041200000008da00040d40006ef3ad22826718cc000620359d659a1a00038a8e98a71000301c0001d580036629149b83880001a3b0004ef800009200d99880a8fa20005cb146d06c0003cb00000000005e340018700f985e8290000000000000092444e3be1d4c9cc7176ba79304568bd14a8a580006498a213c52dac9e58eb110e702322dd1c757dc00000019100000003e636cdaa24130000c840007e700032140002ce00000003174ed41ab8bc000d9b4daa26e00011a00000004d9658599137895ad6a00013f47321a012549dc49455e0029518f0870800025916f800a80000000658246eeb6e8008a4d4ff946995491945934c011264043c2a60fee5577409c50fa48082b0b334f09278932240451a6142781a1494e09280030640007ac72aeb4435063d660358c4a66261149
  | 30 => 0x868c00020d241338f2f6c4f05ca22abd6dda15f856c0a600000034502f5af23f58719cd4694233fab810537162500006ebd4b75c186f40611c28e25055be34c74d2054ffd5d45a636a13740c8001211323e00000000013661d32dcb3a233ccfd00000048e8d2543a3318730db51209e560001813978461a207b9000089d71853eb711fd579c68e6a700018a44ee52e978b2c4b310273730000aab54ab6582bcafd55920140000000000d9902e97800000005060001c7000c16529c08bb4a400000030527bc4a211e1e42dac8436be6f228ac0000000000000000000000000021fc5067003a00006184ff39c19c132a35d19980000f40000000f5449124b2f0c0000000001cd05b27f2156a2e135e5d4daf881c11f42662c000000038016d00000000000d561c899608692a0000bae8d4056e23c0000f6c1d201b14e86e09911307be0000003a78c6c7e663060a016224015bc4e56d43aa720a9d502b1063a29cec00000006f0a95ce8dfa50a96100003e70d4c0000005c1379106456d00018000b4000000072afe8000169a1897712c24541cea1a86c8e2b68180008d8a283538e44fe749c0001c65bfecb50000a0fadc52f2daad50e5bbba01b8001b8e7618d7b65cf1400025480000000003aa9478000000263853c00000071f16b00e81cd72a02a4808e3347c098000000029d800153d0d34ac0d110bc5671b3b88ca6ae76989ab2c00000065980000000000000f34cfab3460a1b90000e870f3b4d50e3eb400018adc0036f00025246b6b2a0ae29317c200000000010f696a0000001a340000571224ac0bdaecc375c000e06061161c00028b051b3cc29a000387a87141cd1d3e81acd1f4564beb03b09a806d53495a812ac1f5c70ae73e829403e0bbc5486b5538041cbb6bd6c6db5d8132b152b569006d23522d6bab49996d30000000d2e9b2680312160a00000d4001458ac90e961189ac44007e1b35791af04fba7880e74c436c01fbc920416a52a3e878c3f4da0466ce94a54a223f4f0a1ccc4414e80006231a701a60000081f15ad88390006a41448000bc086306b1acce1046b8f11604e9f2f711e022a0002c80bfe36c000000346b76425817f85053ec3e9b42378c7766e6643ae90a4532743550b09de0000c9ad1063403945985b016cb350a396a4000dc30002106c6269926e04b7cdc85d113148939ce436ea84a1ccc94f36a37a40585c23ecb8296e8a094b639a4c0c82500036b84a0eb332700001c077600020e0000b9f000000136cd76808971483f000000000000000cf44397d09cc894fda4e8c6e5b645728d59e4cf280003740000006df250ce1650000011fc0000000002ed000019080000000006b014900004908c82250001ac48bc683000000022f0ff750111a6c25300001882a376be21d54d0aebba80bc994063c6ef2e6d3b4
  | 31 => 0xa0000000001689dd90000d8c0000000000001b260000000000000532675052944e000084f30dd2a8be800311c0008a512f23e470e0001f68ecc000b806ee05617129c370680007c02e600000014244db026e7440000003b8b4b10e908f00023ec000000611800000023b69900010300005840867aca0000000000dd8a7b5ab96fc4bad9e73f9ce21a22113780000000425800028849c4fa00019e148a93716842350920002fd8cd8387bc902c00c4e960003ba30f9c9a416c0f8001a1ec3d000000000000021085a400000000000004fe7db425aaf000042ff212db152bcec0000000000000653367cd0249f5a19f14000e80000058d0952b61338001c400000003151a2600040cc001b3400044b39948e029347724fc0aa3a267566250c256d26180000000001ea80000000006da00013cee3400000000001eb00000004482df8000000e1a00f25c8fe9bac00000024780005a8c8e0000000b2400008703c600000000000000f2456a3940c47e145c87926b20000fdb0b4000d5452a000000028ee193788000dcd0001148bb702f80000000000000b5eefc260a7c0000a840000000c60001ac00d95b200000009ab72f200902c0826ce2218f1a80e000103952010d00000000006132c88000000aed000000000000003b81b0ebc000082c07800057a112ca6c00000000025948660000001e3b5ed672bb0974536294e5d4217c9800ad4ae03587b0af13262f5448409156f090a81227b7148d517983cb30dba4554d30472dad704e0a2255de23186c3b41cd2a2e63cbde48b9a7000079759b28bb8dc00035b80a55e60f535784448491c435e0dec3798a10000eb800000000002cd16a6c500019d0cdc1bdc8600000001b241e1f789ce0224a91804b6253c2f12f19aaa0007552c9400045e314b988000a5a6d89bddbe000000000000405e018697a596400035300000005cc1e083e200010817e124b3841e02e00242cce5a63060000d7a0004c586480000000c18000a225492ee8a380002a202208840005993d8800000097900000b8258000000195986e000000019c0008a34be00017fc6bf67eddcd67ec1c58b338c7e400041640000001c180022d00008cf0003315bd6443380b8fd7223d346680255a44c91b633783b9e8a0280000dd2482b0a80017d232443cb7442feea644c261963626a379a99c00044621934a0edece855fa18d694000164000065ce87d4080003b7eab0002ded80c00063e0000000ab600000016a45dcace9fec192149727b8e193acb76708000000b531f8247400041ef49830770a000000153400037f3fea6dd9e878f0a916f498c6590cc19f8000aca2e31d5804ec914de02a170600028532b8896c9b6d099ac30c0003a524bd0ac5921449755d7443d00023240002f9c2198c85f286649ab74d3344788001c7054020cd4d
  | 32 => 0x1d8307e517dde948d6b200049b1ebc48e82e3dd0749cd10001a68000466c560003030518d232c023b4f789f80d6a3bd3727b346d272dc62cb60000000000112ec18bb4d723e550e98a1caa9130bbb9e4958dab7308858a7f00000013d856b6a102eba58f5200049f33bb3cc826746b47c0009eb73d86586e46cb3433a6110502457cb19582c1ee66629b43224711f414653baa215500f6db8a4f238c20243da9274ef2f5c6ae7444339c905309481f62ce888292026286d430a00056c952000050900028e156e53d382326152c035000115f6a2310529955882c538551f7040008005bf800158a0002b932944e8465302a1f49f27515471e680001291942fafb88c884d53624000bc593300000000004609e24c16000496859c83b28be890f30000dec3a780000006f9280afda000105000000188600000000006608440ba2ab5b5e7ed00027b800023083ae1ae00034864900517e6de623cb406dc00007430000c402146f9ae70cbea24309154001a1023e314d025e5f64a60a08000d8d2e753f61d20000318001af40005f19aa81f211bba41dc01eb7c310bad2c00000014eabfd3f8444071341dbdc0000a1a59dd46c4c0ca5298d240001518d7c0009bf00037948aa00004e8e2999442444a0e08332a1054cb5b576e15600000003009ca244f0800000790239fbba3841140e81d200076200004d1bf6617157000000048400000000001870c597e094049e546800153c6c34755680b500000174028d14a800001cd400016a404f6baa3a2c519d0334000e683d8000186ae59168163400073153946e439070a75cace1802e1d5b40fb9cee49b46f98bc00c165150478870880769c08e82f00006a2072d9fc1d12f9a3ad344b4f000010e8cce9900001a5181c9a348224000000048500000005175d31009a0d00048b36b146800058fb58480c3fad72863d962000000017d5582300ee93fc2b21f5d662c6400032d00038119b08b7000130400000e8000cec0005894089e7000041a0000000000110e0ba34632067f60aa819222e85000157d6ced4f0538000242000092ae1d8b2bd04fab57dc129d4076836c5fa00020a8e997be25256c2f5067ac2a0000001bd443954d57918c859744c80000009ca9918000df0d271d1afa125c98240a394d4040005190fe43ee7cb2d591c745400000019cc0000001274000000193a28b3bc000342a968b2992caf72b0cee590600067f6894c90c82583b6e0a166cf73a855057ad0c325071c62a2dd00cafb020d08a4a1083600052b80030bd0440004b8071f99088400000000001684af85f52b58c40003719b72c7500015c101400026a92043742f40000000e001c963daba174ea5b3f2c75d772ac815800e87a2b602c19ba853200011e10dcd8e0000df70ec597b580001ad0000000140925400042b0001c584a
  | 33 => 0x3b624b0ba63b88e01b544ebbdc25999953a058e5f931a80000006a180012660000000000000db200000000000001990250ab88aae8718b4000c860000cf3c1c0000000bc4000000217800194611f6269b681fe2680002c9cecace5f4e259839777e114000151d2c2125c001a088346509b041603782ebcae37809ea41d800033eb924651b757620b84e7814a62875745faf83806d206523558cbccd40000000aba06f000116c0000000000000000000043c2460000000001ee1bc07bf26c2a148540007418ec44585d3ac608f41d66f40002bf800007f8000ba464a410000000000000000014c55cca0f0000000847a4300000010a400031d969cc4a8af1378000000407b9d2bb8bbe3794c791d80006884de80017ac65239c8d006960325710819c2ec8464e000000054980000010c800008b5970956b423278500000000000306921c0000251c48000bd585f21348fc6ca6ba000117630740b6ca13421452300000000d112ac000166e5168002c8ce0440567280000ae0005a2c00025a3334d600013204a300001866cabdd50f1cfd30600003fb124000c180001d992a60003de8000020b4e69f80013c81a24c880000000005a1c0009c248e295af3400023f00000006498aa5879598e2200057db33e0000006d4827db040000000b017859720d396785d00000000aec3427232f41ea00dc7be7522c4141a0005028000509000178000000000000024f594e00000012404303de4564001432bfbb4029f54b2000731b2f8ae27822e69ac890c0006ed800112eaf603c05d4000ae39a8972c000d244eaa8015030fa4fd0d1536044560f0181b32c7e040aef03bc8e74e4e3d400060f1faab4c97c00000029f6000e6d211563d47a000000000000000000000000000000b02fbc00091a4d481981b01bf562012c604a6344391a47921ca8d8ab811c213500031fcf42e5d678ea1afe800033480992ea95987bb7bd09bc6d1008e340005d005bb6a38ee0001a199fa00000018b35780008f67192555617eac494a5694783810fa34e89e877b8001969a0295100025140428ade3cab74ca80000001f5d84a00006461d60000283a00000000b0d05632c00004b531a0000000adb0000000f0e71558eec04312cb4610abb678a16f44f9ca4508e8f44d29e58aeb488002ebc3e107200008098d0c5f74576311babeb0002e114fe40800e372800000027439380309bb0000000fe2cc71eeb569d7eb3d2038000b3e000000318981c0000001914000798000000063ecdf0002acc0000006bc0e6d95ad452c0811629000017c00017b452557a800000000000013a93ace212ffc9682fc00000025fc78400000
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x52154021d40735052154021f03735052154021d22735052154021d20735052154021f00735052154021d00735052154021944815d5320ca40a4581195320c940c89735c86050540e09535496010840d12535c04254440d11535c04254440d22525c04254440d21525c04254440933805da4254440931809ce4254440d22725c04254440931801d13254440931801d03254440e095354960d0440e225254560d0440e215254560d0440a318019151c8440a31809915188440b21821c15150040a448154d610cb20a1a83d506050720b048154c3250720d05535c43250720a1a839946050720a1683d516110320e11535854010220c31745c06154d208e1811c1640c920d07541c5530c920d04541c5530c920d07741c5530c920d04741c5530c920c45861c5530c920d06841c5530c920d05841c5530c920d41801c5530c920a448154d610c920a15811516314520a258119662d0520a0f8654c32d0520b048154c32d0520c28651c14250520c0c651cd6250520c28651c16250520c28659c332505209a1819c33250520a0c8654c3250520b048154c3250520d05535c4325052094587cc851cc520a2581150624c520c26655c454c8520c44631c553c8520c44631c5534852084d8718c5148520e075418c5148520c0e7518f4148520c0c7518d4148520b05831454148520e04631454148520a15811516308520ca0725854010120c0c7598d4188120c24755854188120a18835946050420e20625446050420c24765454148020d09545cc4048020d21545c44048020b098414d3048020b418114d3048020c3076545414802084c87595320cb10a44854c9610cb10e05544c9610cb10b04835485250710d05735485250710b04854c83250710d05754c83250710aa0825806050710b05831494148710e0463149414871084c8758d5208710b04835494108710e05635494108710a48835496008710e215250560087109c1801c5320ca10ac08158c3248210a44854c9610c910a28825946050510991839c24250510c30655c04250510991839c26250510c30655c06250510b04835485250510834865d43250510b04854c83250510993835cb6050510d82735c86050510d81735c86050510c917350660c8510e04631494148510a31809516110110a24825516110110a91831d94188110a25811905248110c30655c46448110a488558c3248110cc1635c432481108b08758d4148110a308558d4148110aa2869c94148110aa0865c94148110ca0765c94148110b20855c94148110b80835c94148110ca076d894148110b8283d894148110e81630c94148110c48651cd2148110aa0865052148110e20655052148110d80735052148110c91735066008110a938358941c4110a448158c6354810945851c5320c810c45651c5320c810d05541c5320c810
  | 1 => 0x2d42801c53254432945801c53254432d41801c53254432941801c53254432a85811913254032c26725c46454032c25725c46454032c31715c06454032e09644c95014032e41325855014032989801c5320cb41a84814c9610cb41e09635895014341e22625855014341e21625855014341c45651c5320ca419c1801c5320ca419c1801c5320c941a44854c9610c941c92325c0614c941a2880594520c9419a1801c5320c941989801c5320c941b81801c5320c941c85861c5320c941986851c5320c941d06851c5320c941d82801c5320c941985801c5320c941d81801c5320c941981801c5320c941984874ca610c941a84814c9610c941984874c9610c941a8583149610c941c87874c9610c941a84874c9610c941c84874c9610c941a86854c9610c941a84854c9610c941a87804c9610c941a8683d8a62d4541a87864c832d4541aa1811c16214141d0b731c95014141d08731c95014141928879895014141d08739895014141928875895014141d08735895014141e09635895014141c33765855014141d20725855014141e21625855014141c46765c4534cb21c48535c0614cb21d04531c532507219a1801c53250721c26725c46454321a18835806055221d05549c7530ca21c45769c7530ca21d05749c7530ca21a0d86d4c32d0621a0e86d4c3250621d07535c43250621915811d16014d21c19745806014d21c51715806014d21a4685d8c614c9219a1801c53250521d04539cb6150521b06858c9418c5219c1801c5324c521e0453189414c521e04654c9414c521c48625c06154c21a458598d610c821d04721c55350421b11801c55350421d05535c43250421b0585cc941cc421e0565cc941cc42184f87d97324c421c45655c4320c421e0553589410c421e05650c9410c421c48635c35348421c0c769515348421c0c76551534842184e869d95348421c0d7518f4148421a0c8654f4148421a448654e4148421c0f7518d4148421a0c8654d4148421a448654d4148421a868398d4148421e058518d4148421c877518d4148421e077518d4148421e0463d4d4148421b2180d4d4148421a848694d4148421b058594d4148421a248654d4148421a848654d4148421e078654d4148421b068654d4148421b048654d4148421e048654d4148421a048654d4148421c857418f62484219488754d2194021d80735052194021f01535052194021d04735052154021d0a541cd2154021d09541cd21540219488794d21540219488754d2154021d23755052154021d80735052154021f02535052154021f01535052154021b408158c3254021d42735c43254021b21810c94154021f0332507315402194a87cc93154021b41810c83154021d21725043154021f00325043154021d10735052154021d0873d052154021d40739052154021d087350
  | 2 => 0x16cb23d0483eed134ca6388510b80942a0040afd0000048c8300102000b109f0386c273060000086074000006f800c1000c502cf03f6c088cbfa910643c001ca6610400070d73863a2e8002f093204b603cef3404a3a47600ca301ca9038c4800000006136473800afbb066aed0a0c491480741b0f50fc003f8304403b1b8000becaa0826000003841717c111ec2c224003726a40c13370553b5082787223c5e0006538c0026010000db288c8328f10163e00000000d500005000000000000092478a8a848b000bf0004e2001e398002ccbe00059001182643d310fb0011b0007f060f300077001152ac9c3fcf910d0e0ac360a0a02a0d24848a131164440c47c9a11c35134a7b8a95080b939c34000000000d3000000038000711ac000000a4711a000db8420042c0035829000140ccd8059051880021400000b4000e012c39322b7000df250001e45025c3c100aa35f170947323000000c2bf2fa0049f0488e10800000320004c800443f0080ca0031800018e5000150000000113368000010bc30cc33c00152220a8000002d0000000112000000001eab87c21000160ce000c31d4dd32470190cb000e800119000ee1188cb7eaf23ad4489012fa8711424010ac14c9b3787d124f71e0691b4570dc63308f61bc5c00000000a529c4f1f8e480000410bd084003a868158f8400964910d000f23ac60000524248d41cb00007a00088174b8000670082f274c72400033419864e407c1a000002b4540000000000474b54505a00008000300000040483c1e14020000000058080816080000400000001802000185402008001406000042c00040080600038080606010200001000000c000f00012040102406030d0080205020081a00030000807038100209078001207028000006000202c020005c1801010000205008140010030003401000245008d05545c4544c832d09545c0544c832c0d759d0614c832c0d755d0614c832c49759c0614c832c49755c0614c832c8a745c0614c832c89745c0614c8328c9801d93294432c85641c532944329c1801c532944329c1801c53254432961801c53254432949801c53254432b05841c53254432b41801c53254432946861c53254432c46861c53254432d06841c53254432d05841c5325443
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x72e00c8600609804458f02135b1804254e9f4050000000470c3614e0820341a43710911163ccda142431003a080280188d0a9620591801c53294432c814230038a64a886590184600714c9510ca5032040a64b0865a0e10595801c5320ca41c40c350038a641928388186600714c8325063032043a6530864a0ca0640814c9610c941c0443ac6b12a028283420975896154050507800e6b12c2a80a0a0e4014d801c53250721a034b6a6b8864a0c43900726007154d41087400c6c06a6a0a4210c81a5a8654d4148421a804baa6a0a43280435009794d4148550086a012ea9a8290aa010e01619841c5530c920c20c330038aa619241901846007154c32483040cac0ce19928290501259535c43250520902cc0c628a8290a41104985d5320c941c4240930b1aa4a08438858024d525056008710a204aac6b886490221820762157250520443100ec41ae4a0a40886201da83d894148110a404bac619282902216009558c32505204431010c39a8290a4088700194735052148110
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
  | 5 => packedAt gbK5 (274944+((h/2585+packedAt gbK5 (238754+(h % 2585)*14) 14) % 13626)*14) 14
  | 4 => packedAt gbK4 (203770+((h/1442+packedAt gbK4 (185024+(h % 1442)*13) 13) % 5713)*13) 13
  | 3 => packedAt gbK3 (18579+((h/111+packedAt gbK3 (17580+(h % 111)*9) 9) % 440)*10) 10
  | 2 => packedAt gbK2 (2705+((h/13+packedAt gbK2 (2627+(h % 13)*6) 6) % 50)*7) 7
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xff87fffc0ff1f1c3e38fc7fff1f8383c19f793
  | 1 => 0x7f83e3ff1fffffc03f1f8e07e3ffffc6648ff
  | 2 => 0x7ffc03ffe01fe3ffc01ff007fc03fc3878f1c
  | 3 => 0xf800003ffffe003ffffe00007fffc003f80fe0
  | 4 => 0xffffffc00000003fffffffff80000003fff000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x10908c04602222006082412330488898089391
  | 1 => 0x41020048808080080110884402121220224026
  | 2 => 0xb231149124654055a401520954812589858d18
  | 3 => 0x2065a922494064a6caa4001269258112d80ec0
  | 4 => 0xc44630038d89893b1349a49c00060623776000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 31 gbPos gbNeg, 0xfeeaecc8feeaecc8feeaecc8feeaecc8feeaecc8feeaecc8feeaecc8feeaecc8feeaecc8feeaecc8feeaecc8feeaecc8feeaecc8feeaecc8feeaecc8feeaecc8, gbN, gbR, (fun _ _ => 0), gbI⟩
end PEqualNP.Outside.L_meta_16755
namespace PEqualNP.Outside.L_meta_16755
open PEqualNP.Outside.L_meta_16755.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeaeeeafeeaecc8feeaeeeafeeaecc8feeaeeeafeeaecc8feeaeeeafeeaecc8feeaeeeafeeaecc8feeaeeeafeeaecc8feeaeeeafeeaecc8feeaeeeafeeaecc8
theorem fullBound (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have low := boundgb certgb
  have lift := lift_ok (u:=true) (ms:=fixRows 32 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 5 zero,1,33)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 5 zero,1,33)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276809450 * 2 ^ 32 + 4276808904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_16755.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,1]⟩,⟨.or,[1,5]⟩,⟨.or,[4,7]⟩,⟨.or,[1,2]⟩,⟨.and,[3,9]⟩,⟨.or,[4,6]⟩,⟨.and,[1,2]⟩,⟨.and,[10,11]⟩,⟨.and,[0,8]⟩,⟨.or,[12,14]⟩,⟨.or,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4276808904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4276808904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_16755

open PEqualNP.Outside.L_meta_16755 in
theorem PEqualNP.Outside.L_meta_16755 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4276808904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4276808904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound allgb)
