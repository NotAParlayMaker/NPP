import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_12347.Model
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


end PEqualNP.Outside.L_meta_12347.Model

namespace PEqualNP.Outside.L_meta_12347
open PEqualNP.Outside.L_meta_12347.Model
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

end PEqualNP.Outside.L_meta_12347

namespace PEqualNP.Outside.L_meta_12347
open PEqualNP.Outside.L_meta_12347.Model
def gbK8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2720580000000b8000811000000f8034a490000980000000d8d320800b001800000911880e14ea80024000009400000000000000a0f1c00001087888000000210054000007018026300180028001000200002061c0000000080ff43bf43fe43fd43bd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x841fe31083fa62107f0c420ff90841fe21083fa42107f08420bf28041ff40083fc80107f50020fe20041ff30083fc60107f4c020fe18041ff20083de40107f88020fd10041fd20083da40107e48020f490041ff54c42fea9887f95310bf2a621fd54c42faa9887f15310be2a621ff53c42fea7887f94f10bf29e21fd53c42faa7887f14f10be29e21ff43c437e87887f90f10fea1e21bd43c43f887887fd4b10bfa9621fe52c42fca5887f54b10bea9621fc52c42f8a5887fd0b10ff21621fd42c43f885887fccb10ff19621fd32c43f865887fd0710ff20e21fd41c43f883887fcc710ff18e21f631c43fa63887d4c710fe18e21ff21c43fc43887f48710fe10e21ff40c43fc81887f50310fe20621ff30c43fc61887f4c310fe18621ff20c43fc41887f48310fe10621ff54842fea9087f95210bf2a421fd54842faa9087f15210be2a421ff53842fea7087f94e10bf29c21fd53842faa7087f14e10be29c21ff438437e87087f90e10fea1c21bd43843f887087fd4a10bfa9421fe52842fca5087f54a10bea9421fc52842f8a5087fd0a10ff21421fd42843f885087fcca10ff19421fd32843f865085f54610ffa0c21fe41843fa83087f10610ff98c21fe31843fa63087f0c610ff90c21fe21843fa43087f08610bf28421ff40843fc81087f50210fe20421ff30843fc61087e8c210fe98421f930843f861087fc8210ff10421fd20843f841087fc4210fb88421fb10843fea8885fd5110dfaa2213f54443fca8885f95110feaa2217d54443f8a8885f15110de2a2213c54443fea6885fd4d10ff29a217e53443faa6885f54d10fe29a217c53443fe86886fd0d10ff21a21fd434437a86887f10d10ffa92217f52443fca4885f94910fea92217d52443f8a4885f14910ffa1221fe42443fa84887f10910ff99221fe32443fa64887f0c910ffa0a21fe41443fa82887f10510ff98a21fe31443ec62887f4c510fa98a21fc31443fe42887f88510fe90a21fc21443fe80887f90110fea0221fc40443fe60887f8c110fd18221fd30443f260887f0c110ff90221fe20443fa40887f08110ff88221fb10443fc20887d84110ffaa0217f54043fca8085f95010feaa0217d54043f8a8085f15010ffa98217f53043fca6085f94c10fea98217d53043f8a6085f14c10ffa1821bf43043fc86087f50c10dea1821fc43043fea4085fd4810ff290217e52043faa4085f54810fe290217c52043fe84087f90810fea1021fc42043fe64087f8c810fe99021fc32042fca2087fd0410ff20821fd41043f882087fcc410ff18821fd31043f862087fc8410ff10821fd21043f842085f94010ffa0021fe40043fa80087f10010ff98021fe30043fa60087f0c010ff90021fe20043fa40087f08010ff88021f710043fc20087e84010fe88021f510043f220087c44010
  | 1 => 0xe304c3bc60987fd5030bfaa061fe540c2fca8186f950309f2a061fd540c2faa8186f550309eaa061fc540c2f8a8185f94c30ffa1861bf430c3fc86187f50c30dea1861fc430c3fea4187f94830bf29061ee520c2dca4187f54830bea9061ed520c2daa4187f14830ffa1061fe420c3fa84187f10830ff99061fe320c3fa64187f0c830ffa8861fe510c2fca2187d94430bb28861fd510c2faa2187d54430baa8861fc510c3fe82187f90430fea0861fc410c3fe62187f8c430fe98861fc310c3fe42187f88430fe90861fc210c2fca0187fd0030ff20061fd400c3f880187fcc030ef98061fe300c3f460187f4c030ee98061f9300c3fea9905fd5320ff2a6417e54c83faa9905f55320fe2a6417c54c83fea7905fd4f20ff29e417e53c83faa7905f54f20fe29e417c53c83fe87906fd0f20ff21e41fd43c837a87907f10f20ffa1641fe42c83fa85907f10b20ff99641fe32c83dc65907f4cb20f699641fc32c83fea3907f94720bf28e41fd51c82faa3907f14720ffa0e41fe41c83fa83907f10720ff98e41fe31c83fa63907f0c720ff90e41fe21c83fa43907f08720ffa0641fe40c83fa81907f10320ff98641fe30c83fa61907f0c320ffaa4417f54883fca9105f95220feaa4417d54883f8a9105f15220ffa9c417f53883fca7105f94e20fea9c417d53883f8a7105f14e20ffa1c41bf43883fc87107f50e20dea1c41fc43882faa5107fd0a20ff21441fd42883f885107fcca20ff19441fd32883f865107fd4620ff28c417e51883faa3105f54620fe28c41ff41883fc83107f50620fe20c41ff31883fc63107f4c620fe18c41ff21883fc43107f48620fe10c417e50883fe81107f90220fea0441fc40883fe61107f8c220fd18441fd30883f261107f0c220ff90441ef20883f641107fd5120bfaa241bf544827ea8907f95120bf2a241fd54482faa8907f15120be2a241bc5448278a8907fd4d20bfa9a41fe53482fca6907f54d20bea9a41fc53482f8a6907fd0d20dfa1a41fe43483fa86906f50d20fe21a41ff42483fc84907f50920fe21241ff32483fc64907b8c920fe99241ed32483f864907fd4520bfa8a41fe51483faa2907f14520be28a41ff41483fc82907f50520fe20a41ff31483fc62907f4c520fe18a41ff21483fc42907f48520fe10a41ff40483fc80907f50120fe20241ff30483fc60907e8c120fe98241f930483f860907fc8120fd90241fe20483dc40907fd5020bfaa041fe54082fca8107f55020beaa041fc54082f8a8107fd4c20bfa9841fe53082fca6107f54c20bea9841fc53082f8a6107fd0c20dfa1841fe43083fa86106f50c20fe218417e52083fe84107f90820fea1041fc42083fe64107f8c820fe99041fc32083fea2107f94420bf28841fd51082faa2107f14420ffa0841fe41083fa82107f10420ff98
  | 2 => 0x3faa5205f54a40fe29481ff42903fc85206f90a40fea1481fc429037885207fcca40ff19481fd32903f865207fd4640ff28c817e51903faa3205f54640fe28c81ff41903fc83206f90640fea0c81fc419037883207fcc640ff18c81fd31903f863207fc8640ff10c81fd21903f843205f94240ffa0481bf40903f681207fd4d40bfa9a81fe53503faa6a07f14d40be29a81ff435037e86a07f90d40fea1a81bd43503f886a07fd4940bfa9281fe52503faa4a07f14940be29281ff42503fc84a07f50940fe21281ff32503fc64a07f4c940fe19281ff51502fea2a07f94540fea8a81fc51502f8a2a07fd0540ff20a81fd41503f882a07fcc540ff18a81fd31503f862a07fc8540ff10a81fd21503f842a07fd0140fda0281fe405037c80a05f95040ffa9881fe53102fca6207f54c40bea9881fc53103fe86206fd0c40ff21881fd431037a86207f10c40ffa9081fe52102fca4207f54840bea9081fc52103fe84207f90840df21081fd42103f884206f10840ff99081fe32103fa64207f0c840ffa8881fe51102fca2207f54440bea8881fc51103fe82207f90440df20881fd41103f882206f10440ff98881fe31103fa62207f0c440ff90881fe21103fa42207f08440bf28081ff401037e80207f90040fd20081fd401037a80207e50040ffaa6617f54cc3fca9985f95330df2a6613e54cc3faa9985f55330deaa6613d54cc3f8a9985f15330ffa1e61bf43cc3fc87987f50f30dea1e61fc43cc3fea5987f94b30bf29661fd52cc2faa5987f14b30ffa1661fe42cc3fa85987f10b30ff99661fe32cc3fa65987f0cb30ffa8e61fe51cc2fca3987f54730bea8e61fc51cc3fe83987f90730fea0e61fc41cc3fe63987f8c730fe98e61fc31cc3fe43987f88730fe90e61fc21cc3fe81987f90330fea0661fc40cc3fea9185fd5230ff2a4617e548c3faa9185f55230fe2a4617c548c2faa7187fd0e30dfa1c61fe438c3fa87186f50e30fe21c61ff528c3fca5185f94a30fea94617d528c3f8a5187fd0a30ff21461fd428c3f885187fcca30ff19461fd328c3f865187fd4630ff28c617e518c3faa3185f54630fe28c61ff418c3fc83187f50630fe20c61ff318c3fc63187f4c630fe18c61ff218c3fc43187f48630fe10c617e508c3fe81187f90230fea0461fc408c3fe611877cc230fd98461ff544c2fea8987f95130bf2a261fd544c2faa8987f15130be2a261ff434c37e86987f90d30fea1a61bd434c3f886987fd4930bfa9261fe524c3faa4987f14930be29261ff424c3fc84987f50930fe21261ff324c3fc64987f4c930fe19261ff514c2fea2987f94530fea8a61fc514c2f8a2987fd0530ff20a61fd414c3f882987fcc530ff18a61fd314c3f862987fc8530ff10a61fd214c3f842987fd0130ff20261fd404c3f880987fcc130fd98261f
  | 3 => 0xa418db94831fea90637d520c7daa418db54831fe29063ff420c7fc8418ff50831fe21063ff320c7fc6418ff4c831fe190637e510c7fe8218ff90431fea0863fc410c7fe6218f7cc431ff18863f6310c7fa6218f74c431fa98863ff500c7fca018df94031fd280637a500c7faa018df54031fca806379500c7f8a018ffd5321bfaa643fe54c86fca990ff55321beaa643fc54c86f8a990ffd4f21bfa9e43fe53c86fca790ff54f21bea9e43fc53c86f8a790ffd0f21dfa1e43fe43c87fa8790ef50f21fe21e43ff42c87fc8590ff50b21fe21643ff32c87fc6590fb8cb21fe99643ed32c87f86590ffd0721ff20e43fd41c87f88390ffcc721ff18e43fd31c87f86390ffd4321ff286437e50c87faa190df54321fe28643ff54886fea910ff95221bf2a443fd54886faa910ff15221be2a443ff53886fea710ff94e21bf29c43fd53886faa710ff14e21be29c43ff438877e8710ff90e21fea1c43bd43887f88710df54a21ffa1443fe42887fa8510ff10a21ff99443fe32887fa6510ff0ca21bf28c43ff41887fc8310ff50621fe20c43ff31887fc6310fd8c621fe98c43f531887f86310ffc8621f790c43f721887fea110ff94221bf28443fd50886faa110ff14221ffaa2437f544877ea890cfd5121ff2a2437e54487faa890df55121fe2a2437c5448778a890cf15121ffa9a437f53487fca690df94d21fea9a437d53487f8a690df14d21ffa1a43bf43487fc8690ff50d21dea1a43fc43487fe8490ff90921fea1243fc42487fe6490ff8c921f719243fd32487da6490ff0c921ffa0a43fe41487fa8290ff10521ff98a43fe31487ec6290ff4c521fa98a43fc31487fe4290fdc8521ff10a43ee21487fea090dfd4121ff28243fd50487f8a090df14121ffaa0437f54087fca810df95021feaa0437d54087f8a810df15021ffa98437f53087fca610df94c21fea98437d53087f8a610df14c21ffa1843bf43087fc8610ff50c21dea1843fc43086fca410ffd0821ff21043fd42087f88410ffcc821ff19043fd32087f86410df94421ffa0843fe41087fa8210ff10421ff98843fe31087fa6210ff0c421ff90843ef21087fc4210fd88421fe90843ed21087ea4210f948421ffa8043fe50086fca010ff54021bea8043fc50087fea7a07f94f40bf29e81fd53d02faa7a07f14f40ffa1e81bf43d03fc87a07f50f40dea1e81fc43d03fea5a07f94b40bf29681fd52d02faa5a07f14b40ffa1681fe42d03fa85a07f10b40ff99681fe32d03fa65a07f0cb40ffa8e81fe51d02fca3a07f54740bea8e81fc51d03fe83a07f90740fea0e81fc41d03fe63a07f8c740fe98e81fc31d03fe43a07f88740fe90e81fc21d02faa9207fd4e40ff29c817e53903faa7205f54e40fe29c81ff439037e87207f90e40fea1c81bd43903f887207fd4a40ff294817e529
  | 4 => 0x5f54032fca806579500cbf8a0197fd4f41ff29e837e53d07faa7a0df54f41fe29e83ff43d077e87a0ff90f41fea1e83bd43d07f887a0ffd4b41ff296837e52d07faa5a0df54b41fe29683ff42d07fc85a0ff50b41fe21683ff32d07fc65a0ff4cb41fe19683ff50d07fca1a0df94341fea86837d50d07f8a1a0df55241ffa9c83fe53906fca720ff54e41bea9c83fc53907fe8720efd0e41ff21c83fd439077a8720ff10e41ffa9483fe52906fca520ff54a41bea9483fc52907fe8520ff90a41df21483fd42907f88520ef10a41ff99483fe32907fa6520ff0ca41bf28c83ff419077e8320fdd0641ffa8483fe50906fca120ff54241bea8483fc50907fea6a0dfd4d41ff29a83fd53507f8a6a0df14d41ffa1a83bf43507fc86a0ff50d41dea1a83fc43507fea4a0dfd4941ff29283fd52507f8a4a0df14941ffa1283fe42507fa84a0ff10941ff99283fe32507fa64a0ff0c941ffa0a83f741507fc82a0ef90541ffa82837f50507fca0a0ff54141fe282837c50506fca820ffd4c41ff298837e53107faa620df54c41fe29883ff431077e8620ff90c41fea1883bd43107f88620ffd4841ff290837e52107faa420df54841fe29083ff42107fc8420ef90841fea1083fc42107788420ffcc841ff19083fd32107f86420df94441ffa0883bf41107fc8220fd90441fea0883bd41107ea8220ffd4041ff280837e50107faa020df54041fe28083ff54cc6fea998ff95331bf2a663be54cc67ca998ff55331beaa663bd54cc67aa998ff15331be2a663ff43cc77e8798ff90f31fea1e63bd43cc7f88798ffd4b31ff296637e52cc7faa598df54b31fe29663ff42cc7fc8598ff50b31fe21663ff32cc7fc6598ff4cb31fe19663ff41cc7fc8398ff50731fe20e63ff50cc7fca198df94331fea86637d50cc7f8a198ffd5231bfaa463fe548c6fca918ff55231beaa463fc548c6f8a918df54e31ffa1c63bf438c7fc8718ff50e31dea1c63fc438c7fea518ff94a31bf29463fd528c6faa518ff14a31ffa1463fe428c7fa8518ff10a31ff99463fe328c7fa6518ff0ca31bf28c63ff418c7fc8318ff50631fe20c63ff318c7be6318fdcc631ffa8463fe508c6fca118ff54231bea8463fc508c7fea898dfd5131ff2a2637e544c7faa898df55131fe2a2637c544c7fe8698efd0d31ff21a63fd434c77a8698ff10d31ffa92637f524c7fca498ff54931fe292637c524c7fe8498ff90931fea1263fc424c7fe6498ff8c931fe99263fc324c7fe8298ff90531fea0a63fc414c7fe6298fdcc531ff18a63de314c7fea098dfd4131ff28263fd504c7f8a098df14131ffaa0637f540c7fca818df95031df2a0633e540c7faa818df55031deaa0633d540c7f8a818df15031bf29863ff430c77e8618ff90c31fea1863bd430c7f88618ffd4831ff290637e520c7dc
  | 5 => 0x943df29287bd5250f78a4a1efd4543df28a87bd5150f78a2a1efd4143df28287bd5050f78a0a1df950439f2a0877e5310ffe8621efd0c43ff21887de4310ffa8621ef50c43eea1887ff5210ffca421df94843fea90877d5210ff8a421ffd4443ff288877e5110ffaa221df54443fe28887ff5010ffca021df94043fea80877d5010ff8a021ffd4f42ff29e857e53d0bfaa7a15f54f42fe29e85ff43d0b7e87a17f90f42fea1e85bd43d0bf887a17fd4742ff28e857e51d0bfaa3a15f54742fe28e85ff50d0bfca1a15f94342fea86857d50d0bf8a1a15f55242ffa9c85fe5390afca7217f54e42bea9c85fc5390bfe87216fd0e42ff21c85fd4390b7a87217f10e42bf29485ff4290b7e85217bd0a42ffa8c85fe5190afca3217f54642bea8c85fc5190bfea1217f94242bf28485fd5090afaa1217f14242ffa9a857f5350bfca6a17f54d42fe29a857c5350bfe86a16fd0d42ff21a85fd4350b7a86a17f10d42ffa1285ef4250bfc84a16f90942ffa8a857f5150bfca2a17f54542fe28a857c5150bfea0a15fd4142ff28285fd5050bf8a0a15f14142bf2a085ff5310bfca6215f94c42fea98857d5310bf8a6217fd0c42dfa1885fe4310bfa86216f50c42fe218857e5210bfe84216fd0842ff21085ee4210bfa84216f50842f6a1085ff5110bfca2215f94442fea88857d5110bf8a2217fd4042ff280857e5010bfaa0215f54042fe28085ff54ccafea9997f95332bf2a665be54cca7ca9997f55332beaa665bd54cca7aa9997f15332be2a665ff43ccb7e87997f90f32fea1e65bd43ccbf887997fd0b32ff21665fd42ccbf885997fd4732ff28e657e51ccbfaa3995f54732fe28e65ff50ccbfca1995f94332fea86657d50ccbf8a1997fd5232bfaa465fe548cafca9197f55232beaa465fc548caf8a9195f54e32ffa1c65bf438cbfc87197f50e32dea1c65fc438cafca5197fd0a32ff21465fd428cbf885197fcca32ef99465ef328cbfea3197f94632bf28c65fd518cafaa3197f14632ffa8465fe508cafca1197f54232bea8465fc508cbfea8995fd5132ff2a2657e544cbfaa8995f55132fe2a2657c544cbfe86996fd0d32ff21a65fd434cb7a86997f10d32ffa1265fe424cbfa84997f10932ff99265ef324cbfc6499778c932ffa8a657f514cbfca2997f54532fe28a657c514cbfea0995fd4132ff28265fd504cbf8a0995f14132ffaa0657f540cbfca8195f95032df2a0653e540cbfaa8195f55032deaa0653d540cbf8a8195f15032bf29865ff430cb7e86197f90c32fea1865bd430cbf886195f94832ffa1065fe420cbfa84197f10832ff99065df320cbfc64197b8c832fe99065dd320cbda64197fd4432ff288657e510cbeca2195d94432fea88657d510cbeaa2195d54432fe28865ff500cbfca0195f94032fd280657a500cbfaa019
  | 6 => 0x200000400600c00800201c00401600c01202600200000801e00200800a03203400e00001c00e04c00602e00600200203400400000200000201000000403400000609200200000e00200601200000c01600200201200600200000800200a00200c00000402000400400000200a00000000401200001600a00602000a00400600200003401a00001802001e00200001802c00204a00e01601000600002600000000600800e00800c00200200001400000000200400400801c00a00400200600200000200200600400200600601200000000a02c00001400200200000200a01a00800200200600000001e00603001802400402000a00600000e01e00200000000c00000000400200c00a01e00a00401000200002600000000000400e01800600800201000600800001e01400200200000000601600200001200000200200000200c00000400202000c01400c00402600200602c00a00002e01200401000200c02c00600400200005000200400001201400203200002000400200000200800800001001e02400000000400002200604a07800200401000400000600000000a00200e04800000400400800802600202600c00001a00200200000800a00200400000002402400000200200c00001000400a03e00000000000000000800000400800200a03a00200000400a03200400a00401a01800002400000000200400e00600200400201201e00400000200000000a00001004001200401200000e00600200200c00200601400002e00a01200400e01e00600000c00400202600800001200800000200000202200800a00800000202a00400801801000200c02a00000600000200202a00000000000001401a00000200a00400400804600000e01600200000600800002401400200600e00002c01400800200000200001400405201000c00200200000400c03600800400000601800200003000400600000002200e00200800006601202a00800c01600a00001a00400000800e00c01200200600000803a00e00000000602201205603801602400e004002006004020003ff52d0ffca5a1df94b43fea96877d52d0ff8a5a1ffd4743ff28e877e51d0ffaa3a1df54743fe28e87ff50d0ffca1a1df94343fea86877d50d0ff8a1a1efd4b43df29687bd52d0f78a5a1efd4743df28e87bd51d0f78a3a1efd4343df28687bd50d0f78a1a1df552439eaa4877e5390ffe8721efd0e43efa1c87ff5290ffca521df94a43fea94877d5290ff8a521ffd4643ff28c877e5190ffaa321df54643fe28c87ff5090ffca121df94243fea84877d5090ff8a121ffd0d43efa1a87fe4350f7c86a1ffd4943bfa9287fe5250ffaa4a1ff14943be29287ff5150efea2a1ff94543fea8a87fc5150ef8a2a1ffd4143bfa8287fe5050ffaa0a1ff14143be28287bf5350f3ea6a1efd4
  | 7 => 0x54fd00000010f406c0000000019e0340c28000875bb000000012000102cb24a45cd86e0000ae841d6e9885640044000001a0c7554348c02089847b0be92ccf4594533d2d12952e9c153b4000000f3c13d8e1b58000000000000000000904d40384000000000000000f00638000f606a40010e40000018180000000000017e14a000000094c000000628cc985c000dd0a7c000000000f082b4270e5c499838e44b3583d5b1c513e0bf565c000524000309585310fa5444df1440000fcd73536c001a3cde570c24d9ed920001b895200011217d4000d08c5d4912dda98d4cf69c01820d519bc8ac20c2382640001a0000f389b800086492c29836804d2049240008d95f4001650a859d9158000000cf522167588cc805a12347ad739094ec4000c0c26c001474a180000000018418940016ed7c480159193ca5c7d15b4eb0000759754d804e11d47b80006503301ac000890000bb5d140000000001d995c00099c001788fd8174001d58e28000db16080003fc000348420000860118000000d34001cad58cadc0003c423cd99355cb8e701c957c001aa10c54cc00011019d4b80001a9d4126c001974aac0f08bc000e8ced0000000000ed4000001080c900015580006b094800064400172c00000033d4f9824678001904568000e789c8000000cc5be13590c8e011d0000001bc5b0d9f84a4b3d0883d16b05dc6147fdb78004dc44750d80001dd1b10b4ea8a64398c44000cec000001b10e2c0010117694d8d600000019c4158f05d000000008504680007d400061c00105d8dd2458545881cdc8c7c8741b31a103cd20da316bc0b00597203c0bdda84ff8051d2c0014f073124d2fd949b14df88d571000045c0011dd4d47c00017a93bc5f0dcc0000014c9059d54da181c765774ce955c4e5c780f80007dcf2c0240002f1638000001b187a132d0f00002dc7200000016b80006dc000a687685d0f81b456a9321c0566c5ec000000400000000318ee8000cd037cef4514e64000b04470000729d4511d67128414cbc07a9bf069455156c2b17f8c3d990bc99c13e92891481e48f8cb0d8d031b80194bb106d5c851c125068001209458000e3c4894080ec328001168848ee093c9f4945ca85409c5688ca17f48c9110c50344f4c601bd87840d14fd2bc5fc028ff000000000400600000200e00200001000400203600200000a00000000000200400000000c01000007400200801201400c00a01200400200000200400200600202a01a00400201800000001400c02801e01e01800001800401001c00a00000201800200200201e00201c01201000000200802e01c01001800a00004801000400000200401c00200a00e00001a00400e00400c00000600000601e00c02e01800000000000400a00600001600000004a00800800601802201400001c004000000
  | 8 => 0x4d6cf55d3049d485d95d600c0a9c9ec1289a89f109d761cc586c00088854d8f13680000013ec0007ecedcbadc3c0014600010b133578c0e079c6748686a8a75875d38994d283f5b4870d0f894161800000000000053c000001161b98978935d7c000000000000d0c000e31cd0c1010072cdec50198cb98e683907e8a20000cddb51690001c440015f07bc6cd8ec000d65ca4000000001af95cd03c00136107800052028d5f80015a00000017e4bcc1e8000360ff400013800000000000125d960c040005cd80c000e880000015d44c00001f15391e50485b9b90eac85cb59ab80000a17a400095c131ae800015400000060da400000014b1274000000f2169554c781b2c0000000dc44c5c4ca5b658b8000001cec000921805464001c0c00000173d49c000d2d8d40000014ac34c001ce0000074000000e911f8001b69480fe1cc00019f0cf0001b1cddc00d4a5b3c2855e1339b7184400040c365588000dfc000000ba928ce49c9518c83000000000055948ca041a4001931074c151f512d50dae471835d7483786c85653a0000885ac44151e03f9c25a4cc71890e41b200017452384bd3ac43cdbc00087d849514b1885450d7b16f87b4609a70fbc4653d46d4b55d49c38f9d6cd1b900c98d7913d9c3042c000218c7d2f4bb9379c842615ac00159c8055e559810c180acd300fe97004c801cfc14000001b15c01b4000b6186105552db4c0008d0000f70c2c000b000000011a9d88bf90a90280701510a43c8000c61c7c001d25a040012247713b01680c82f9911d0c799561aa9c74a8d4d0000000001cfc000000001a785e8c79a1d8c1bac00007d5d0c540004505ac0016447101ec774ee400135c0000016206e94b5b356e491d979d8c65c00063c00021dc896b42c4001828001038001a5c74c000505bb4000000d5d7ac0003a484cb9c3d8cf9c680019083d51b4001268839725c10e1462c6f14e1699a94ab0b6db9dad1131374f485797705b5c594dd67859124873962c0a438cd9d71c8e12e4a4844130d3c02d19859c92558986711d81f8658f6d250909a2881c9dc29c374000c1d3816c90e80006bc0016c576d210aed498534fa962841000126454975c9518bd9fca88430b08c6d779314001b94f1510113c000f244b0f782cd61c8ecb495102bc68400056052d87c00194dc2cb14e25cd489551d2f9654a950d40009000000000009e9cf066522d488001acdd64b754715306c4e591a56fc8cc9a147800000113999469d7ec000000e7c8b48e80000640001fcaa0010d71128d7d7c9bc13294ec4b800160c508dd8001a540013a4c48b51d5c0000009e427c16097c841b8c0000009c12c14045984d96a0490000cb4fa00a8d857a0b2c001c64000000a500000000000000000007f80008150040002f4001989280000000ad1564ae5869d3d4
  | 9 => 0x4c001b38000c6800167c7e40000000002882246e43ec0000002fc3e4000460001bb9a2c000efd80802d82c0000000006f5cb4000001bf80005f4bed96c3b00005c8404544e1cb68e18b7cdc80ac4e83547e0e800011ad23d5a80000003bd9a10a1bcd83518800000000142cb808801bd1a000000055c000db5504001180f1cc240000019e4de00000019cc0007014c5969ab4990a61c9c0000010080012d40009192141d58006b8fc8088d245d8b0d7fce509596f000058d9a9b0192c4f49cd9d44ad318000b8c0012a988121d95145d2b86fc7f07f45d5da046d7647a4f34001298528b44e7483577d0ccb897d80006d8000001d1043866dc1d8e51086546484d41780019290dc4f1cf479127d958778458f103e00000954480016dc4cd1f0001a49785014b64000000000f50aa5d7075d8f8f28000d8933147c060d54000e614e880c0005e0ad9045c6d5780000018adda4cb9ba40000003f126000000117941d1ecfd4294698e38091cb1389810000c8c001814aa8da56d507c000080188000001af0d1414517169c3e9d1c000a41bfc48c5c022815dd74cc0f842585819b4b286118a535174075000000000039c248c40001889d0400101d0d000000088c001cdcc59544000001500ab4bf0001184ce119c0019b97b4cd51fd39400134584d3e58309992a400117c0012000005751c8ebc2e80013045a404020011d270000000f90000000000000f5d938000914ed87456492b17cc9556603215b8114ac0c7457d74d864a798fc3ad9340013900f5385c9175190c000000f0d79822c0006d068c25d0019d083c00030ce983814197f0734000001218f8c71c008000000ce4f7c211469a744c40011bd668164ca8d108dd6a4abdd986344dda80314240255424b5ca4ca98000278d747893b85113fd95515cc88c8517462468076cbbd0e15689306b4205780c35795a08c64001c280000015bc938d1d5fd228000a1c0012d968c9d8a3cfddaa44a8c4c6896e00b447c0780008b9164c200002c90fc8718d8b40000820014000000000001c600012f164c4800cdd9d97d16d914d9498140dd50a25624a5817c018c002140000000000fc0011500018c57b8cbc000001ac8000389d78001b6c24400000144c000ef005d548da8000000e04030844000000000000000000000eb8d59534000000e9464c000000000000000000034715134bd8d31a14ef80008e5070000000001a38e11c5c0000003500008282a4000bd49e0961259635ad400108cea137d630001a352e056c2d9a010342d5090000fad0bdc08604000ba0dc0001a60df53c46210414953f14a92900019640002e4f743a0000ffc000000291b756107d937000000016d29d140be4d0431d10cf408f1144a907610c1c54e0da9c0e88f5230de8274f300bc89ca085bc135664001190af03109d
  | 10 => 0xc4a2832d1c19400005b08a80013492eca70dadd915dd7580001718f40d8bd09101418c80b86f80000e400002059d0203389b57e908481803d5700001480000000000000018d19dc0005858a93f59a5be54311e92c9c704ed9b153d240105a89ca0f19870b841c03b8001ab00006180019e91c42518a0000968be17dc6c0000000000001970408000000c950ad4c0000000d3c0002ad4f4000001925731659a65d69ad808c7093c92c55098e87043040012b40012a04fd0199adac191d6d89b1c2155078d43c39400036d615684fb02b86acb910ed414001ae11cd6f53d04f8b940004b5a6cb4c000001bed119c98bc4370d488a5ba0d00fb8640af4231154a31a59124928691438971da95944a02ec098661b7c1c4c98725cc8f58a10b388b1d6ca15525b04a55429c49859bf40013a8afc484c31afdc40000a000015e809c0693648c4d44d21d20000000519d089bd0b8ad4000001554000000001cf8001b08ec063163dbc80000017d02e138d8b58b00016ac055ba9279b54001abdbd4000001c80db9451bddaec2c090c001714000000a397280008fcc38038000234324f89d4c000bfc000000001be9c4c86c0000000d55a40000001b80015d8ab8000000300ecc594c08d3914d0980009d0e855ec001541a246ec0017c18cdc188240001840017091981f40000009643349f9a19a4400000000000139d399604ba4000444000358000000000000000424000ec92ac085cbc668554fe47942a0190ea5b25b84f98f64108f94001b5c73d3080000000016c0000000a0c000000eec000ccc001ce4000571a91998ac8ac49fcb70a80a2ceb5b293419f53cd31d1046a1d29b61d81adc82da68d68e4d900cd87cccac0008983dc000000a6c001421324e2179c00096cc9cb102a8e544182680000003a946d5809a4fb4c19bbd4e4494539b40001528d190513dcb1d7bdd34b31680281c353f8000af8001af56d0000d79518e6cfc4fec3b4001d8412ce35410001879a50dd4a35aad8502205311148a09ad704000000000000859a7d99d4bc0000000000000005e40008795c4808cfc001bd067c00018c04800000000189c000000b78434000ae10640001e0001ccc47957400134d60000077c000989ce8001024974e08000811a8c000000001981d18198001919718454001194000000000000000000b205f8448000000e9c4285a84d0000749060000001a201d0d907c4001
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xe310435d538c410dd94631042fa608c410be582310427f654c410dd945310427f650c4109f59431042be640c410af590310435e530c410d754c31042ee620c410bb58831042fa600c410be580310427d65c84109fd96210427d6588410db94a210436d5288410be98221042f960884109fd9521042bf6448410af191210427f65084109f594210436e5208410db54821043e52108410be98021042f960084109f992500427d64940109f98e500427d6394010cfd0e500433d43940109f98a500427d62940109f586500427d65d00109fd96400427d6590010cf952400433d5490010bd98640042f561900109fd95400427f65100109f994400427d65100109f194400433e5410010cf55040042f66110010bd584400427d65cc010af99330042bd64cc0109fd96300427d658c010d794e300435d538c010bd98630042f5618c010de942300427f654c010de941300427f650c0109f994300427d650c0109f19430042be640c010af590300435e530c010d754c30042ee620c010bb58830042f6610c010bd584300427d65c80109fd96200427d6588010db94a200436d5288010bd98620042f561880109fd9520042bf6448010af191200427f65080109f994200427d65080109f194200436e5208010db54820042f66108010bd58420043e92008010dd597100437753c4010dd54f10043b743c4010ed50f10042f56184010dd94610042f96584010de59610042796584010ded4e10043795384010eed0e10043b94384010be58610042f16184010de94610043f251840109fd9510042bf6444010af19110042f76544010ddd9510042776544010edd9110043b46444010ddd4d10043755344010edd0d10043b54344010bdd8110043765044010fcd0110043f24044010fc50110043f04044010fccc110043f23044010fc4c110043f03044010fcc8110043f22044010fc48110043f02044010bed95100437b65440109ed9510043bb6444010ee191100437b5344010de54d10043bb4344010ee50d10042fb6144010fcd85100437a5144010fc94510043f34144010fc90510043f14144010fc10510043f33144010fc8c510043f13144010fc0c510043f32144010fc88510043f12144010fc08510043f36544010bcd9510043736544010fcd9110043b36444010fc99110043f16444010fc19110043b06444010fcd5110043f25444010fc55110043f05444010fcd8d10043f26344010fc58d10043f06344010fcd4d10043735344010fc94d10043f15344010dc54d10043f05344010fcd0d10043b34344010fc90d10043f14344010ec50d10043f04344010fcd8910043f26244010fc58910043f06244010fcd4910043f25244010fc54910043f05244010fcd0910043f24244010fc50910043f04244010fccc910043f23244010fc4c910043f03244010
  | 1 => 0x427a6014c109fd97430427e65d0c109f597430427c65d0c10cfd53430433e54d0c10cf553430433c54d0c10cfd97430433e65d0c10cf597430433c65d0c10cfd4f430433e53d0c10cf54f430433c53d0c109fd96430427e6590c109f596430427c6590c10af592430435e5390c10d754e430427f6550c109f995430427d6550c109f195430433f5450c10cf951430433d5450c10cf151430435e5350c10d754d43042f76150c10bd18543042fb6050c10be181430433f6550c10cf995430433d6550c10cf195430439f6350c10cfd4d430433e5350c10e794d430431e5350c10cf54d430439d5350c10c754d430433c5350c10edd8543043b46150c10eed8143043b86050c109fd94430427e6510c109f594430427c6510c10af990430427e64d48109f593520427e63d48109f58f520433f43d4810cf50f520427e61d4810dd987520427e60d4810de983520427d6594810dbd4a520427e64948109f592520427e63948109f58e520433f4394810cf50e52042bf6454810af191520427f6454810cfd91520423f64548109f191520433c64548108f191520427f63548109f18d520433f4354810cf50d520436f62548109fd85520427d61548109fd81520427d6054810af99052042bd6414810b798c52042dd6314810db548520427e6414810cf990520423e64148109f590520433d64148108f590520427e6314810d798c520425e63148109f58c520435d63148109758c520433f4314810cf50c520427e6214810db988520427e6114810dd984520427e6014810de980520427f65d08109f997420427d65d08109f197420433e54d0810cf553420427f65908109f996420427d65908109f196420433f5490810cf152420436e5290810db54a42042f66190810bd58642042fa6090810be582420427f65508109f995420427d65508109f195420433e5450810cf551420436e5250810db549420427f65108109f994420427d65108109f194420433f5410810cf150420427f65cc8109f997320427d65cc8109f19732042be64cc810af593320435e53cc810d754f320427f658c8109f996320427d658c8109f196320436e528c810db54a320427f654c8109f995320427d654c8109f195320435e534c810d754d320436e524c810db54932042f7614c810bd18532042fb604c810be181320427f650c8109f994320427d650c8109f19432042be640c810af59032042f6610c810bd58432042fa600c810be580320427e64944109f592510427e63944109f58e510433f4394410cf50e510427e62944109f58a510427d65d04109fd96410427d6590410cf952410433d5490410be98241042f960904109fd95410427f65104109f594410433e5410410cf55041042fa6010410be580410427d65cc410af99331042bd64cc4109fd96310427d658c410d794
  | 2 => 0x6510110cfd50404433c5410110ee500404427e65cc110af99330442bd64cc110cfd53304433c54cc110d7d4f304435c53cc110bd98730442f561cc1109f996304433f548c110cf15230442fa658c110de99630443bb548c110ee15230442f9638c110de94e3044378538c110eed0e30443b9438c110ded4a3044379528c110fcd8630442fa618c110fc18630443f2318c110fc4c6304427f654c1109f595304427c654c110cfd51304433c544c110d7d4d304435c534c110bdd8530442f4614c110be1953044378654c1109e19530443bb544c110ee15130443db634c110f6d4d304437a534c110de14d30443d8534c110eed0d30443b9434c110ded493044379524c110fcd8530442f8614c110fc18530442f0614c110fc8c530443f1314c1109f99430442be640c110af590304433f540c110cf15030442ee620c110bb58830442f6610c110bd58430442fa600c1109f997204433f54c8110cf153204436f52c8110db14b20442f661c8110bd587204427e6588110cfd52204433c54881109fd95204427d65481109f19520442bf6448110af191204433f5448110cf151204436f5248110db14920442f76148110bd185204427e6508110cfd50204433c5408110fa480204433f54c4110cf15310443bb54c4110ee15310442fb63c4110be58f10443bb43c4110ee50f10443f231c4110fc4c7104433f5484110cf15210443b75484110ed15210442f76384110bd58e10443b74384110ed50e10443f35084110fc8c210443f130841109f98f540427d63d50109f98b540427d62d50109f987540437661d50109f983540437a60d50109f596540433f54950109f98e540427d63950109f98a540427d6295010cfd91540427f63550109f18d540427f62550109f189540427f61550109f585540427f60550109f581540433d5415010b798c54042dd6315010bb98854042ed62150109f990540433e64150109f98c540435e63150109798c540427d6315010d758c540425d63150109f988540436e62150109b988540427d6215010db588540426d62150109f984540437661150109f980540437a60150109f993530427d64d4c109f98b530427d62d4c109f987530437661d4c109f983530437a60d4c109f59653042be6494c10af592530435f5394c109f992530433e6494c108f992530427d6494c10cf592530423d6494c109f98a530427d6294c109fd91530427c6454c10d7d8d530427f6254c109f189530427f6154c109f585530427f6054c109f58153042be6414c10af590530435d5314c10bb98853042ed6214c109f990530433e6414c108f990530427d6414c10cf590530423d6414c109f98c530435e6314c109f988530436e6214c109b988530427d6214c10db588530426d6214c109f98453043766114c109d984530427e6014c10de980530
  | 3 => 0x910cf50d524436f62549109fd85524437761549109fd81524437b60549109f994524433f5414910cf150524436d52149109f990524427d64149109f98c524427d6314910cfd0c524433d4314910db988524427e61149109f184524427e60149109f180524427f65d09109f997424427d65d09109f197424433f54d0910cf153424427f65909109f996424427d65909109f196424433f5490910cf152424427f65509109f995424427d65509109f195424433f5450910cf15142442f76150910bd18542442fb6050910be181424427f65109109f994424427d65109109f194424433f5410910cf15042442f66110910bd58442442fa6010910be580424427f65cc9109f997324427d65cc9109f19732442be64cc910af593324433f54cc910cf153324436f52cc910db14b32442f661cc910bd58732442fa60cc910be583324427f658c9109f996324427d658c9109f196324433f548c910cf152324435f538c910d714e324436e528c910db54a324427f654c9109f995324427d654c9109f195324433f544c910cf151324436e524c910db549324427f650c9109f994324427d650c9109f19432442be640c910af590324433f540c910cf150324435f530c910d714c324436f520c910db14832442f6610c910bd58432442fa600c910be580324427e65d0510cfd53414433c54d0510be98341442f960d05109f996414433f5490510cf152414427c6550510cfd51414433c5450510bed8141442f860505109f994414433f5410510cf15041443b541105109f99731442be64cc510af593314433f54cc510cf153314435f53cc510d714f31442fa60cc510be583314427e658c510cfd52314433c548c510bd9963144376658c510edd5231443b4548c510bd58e3144376538c510dd14e31443b7438c510ed50e3144377528c510dd54a31443f3608c510bd98231443f0608c5109f195314433f544c510cf151314435f534c510d714d31442fb604c510be1813144374654c5109d19531443b7544c510ed15131443d7634c510f5d4d3144376534c510dd14d31443d4534c510edd0d31443b5434c510ddd493144375524c510fcd8131442f4604c510fc18131442f0604c5109f99431442be640c510af590314433f540c510cf15031442ee620c510bb58831442f6610c510be980314427e65c8510cfd53214433c54c8510dbd4b214436c52c8510be98321442f960c85109f996214433f5488510cf152214427c6548510afd9121442bc6448510cfd51214433c5448510dbd49214436c5248510bed8121442f860485109f994214433f5408510cf15021443e521085109f997404433f54d0110cf15340442f661d0110bd587404427e6590110cfd52404433c54901109fd95404427d65501109f195404433f5450110cf15140442f76150110bd185404427e
  | 4 => 0xed81544427e6515110cf550544433e64151109f98c544427d63151109f988544427d62151109f984544427c61151109f980544427c6015110af994544433e65151108f99454442bd6315110cfd8c544433e6315110cf58c544423d6315110cf18c544433f6215110cf988544433d6215110cf188544433f6115110cf584544433f6015110cf580544433d1015110cfd53534433c54d4d10cfd93534427e64d4d109f593534433c64d4d109f98b534427d62d4d10af99253442bd6494d10cfd52534433c5494d10d7d4e534427e6494d10cf992534423e6494d109f592534433d6494d108f592534427e6394d109f98a534427d6294d109f58653443756194d109f58253443796094d10afd9153442bc6454d10cfd51534433c5454d10bbd8953442ec6254d109fd91534433f6454d108fd91534427c6454d10cf191534423c6454d10d7d8d534427f6254d10dbd89534426f6254d109f189534436c6254d109b189534427f6154d10ddd85534427f6054d10ded81534427e6514d10af99053442bd6414d10cfd50534433c5414d10d754c53442ee6214d10bb588534427e6414d10cf990534423e6414d109f590534433d6414d108f590534435e6314d109f988534436e6214d109b988534427d6214d10db588534426d6214d109f98453443756114d109f184534427e6014d10de580534427c6014d109fd97434427e65d0d109f597434427c65d0d10cfd53434433e54d0d10cf553434433c54d0d10cfd9743442be65d0d10cf997434423e65d0d10cf59743442bc65d0d10cf197434423c65d0d10cfd4f434433e53d0d10cf54f434433c53d0d109fd96434427e6590d109f596434427c6590d10af592434433f5490d10cf15243442f66190d10bd58643442fa6090d10be582434427f6550d109f995434427d6550d109f195434433f5450d10cf951434433d5450d10cf151434433f6550d10af995434433e6550d108f995434433d6550d10af195434433c6550d108f195434439f6350d10cfd4d434433e5350d10cf54d434433c5350d109fd94434427e6510d109f594434427c6510d10af990434433f5410d10cf15043442f66110d10bd58443442fa6010d10be580434433f54d4910cf153524427e64d49109f593524427e63d49109f58f524433f43d4910cf50f52442be6494910af592524433f5494910cf152524436f52949109f992524433e64949108f992524427d6494910cf592524423d64949109f98e524427d6394910cfd0e524433d43949109f98a524427d6194910dd586524427d6094910de58252442bf6454910af191524433f5454910cf15152442df6354910b718d524427f6454910cfd91524423f64549109f191524433c64549108f191524427f6354910d7d8d524425f63549109f18d524435c63549109718d524433f4354
  | 5 => 0x528427e6414a109f590528427e6314a109f58c528433f4314a10cf50c528436e6214a10dd584528437a6014a109fd97428427e65d0a109f597428427c65d0a10db94b428436d52d0a109fd96428427e6590a109f596428427c6590a10cf952428433d5490a10bd98642842f56190a109fd95428427e6550a109f595428427c6550a10bed8142842f86050a109fd94428427e6510a109f594428427c6510a10cf950428433d5410a10db948428436d5210a10be98042842f96010a109fd97328427e65cca109f597328427c65cca10af99332842bd64cca10be98332842f960cca109fd96328427e658ca109f596328427c658ca10db94a328436d528ca109fd95328427e654ca109f595328427c654ca10db949328436d524ca10bdd8532842f4614ca109fd94328427e650ca109f594328427c650ca10af99032842bd640ca10bd98432842f5610ca10be98032842f9600ca10cf953418433d54d0610be98341842f960d0610cfd52418433c5490610cf951418433d5450610bed8141842f86050610cfd50418433c5410610af99331842bd64cc610d794f318435d53cc610be98331842f960cc610d794d318435d534c610bed8131842f8604c610af99031842bd640c610bb98831842ed620c610be580318436e52c8610db54b21842fa60c8610be58321842bf6448610af191218436e5248610db54921842fb6048610be18121843e52108610cf952408433d5490210bd98640842f56190210cf950408433d5410210bd98440842f56110210ee50040842be64cc210af593308435e538c210d754e30842f6618c210bd58630842f9658c210de596308437a538c210f694e30843d9538c210de14e30843bb438c210ee50e308437b528c210de54a30842fa618c210fc98630843f1618c210bed95308437b654c210f6d8d308437a534c210de14d30843bb434c210ee50d308437b524c210de54930842f8614c210af99030842bd640c210d794c308435d530c210bb98830842ed620c210bd98430842f5610c210db94a208436d5288210bd98620842f56188210afd9120842bc6448210db948208436d5208210bd98420842f56108210fa48020842f565c4210dd597108437753c4210dd54f10843b743c4210ed50f10842f965c4210de59710842fb63c4210be58f10843bb43c4210ee50f108427e63d51109f58f544427e62d51109f58b54442bd63d5110cfd8f544433e63d5110cf58f544423d63d5110cf18f544433f62d5110cf98b544433d62d5110cf18b544433f61d5110cf587544433f60d5110cf583544433f54951109f992544423e64951109f98e544427d63951109f98a544427d62951109f586544437561951109f58254443796095110cfd91544427f63551109f18d544427f62551109f189544427f6155110ddd85544427f6055110d
  | 6 => 0x376534c710dd14d31c43b7434c710ed50d31c4377524c710dd54931c42f4604c710af99031c42bd640c710d794c31c435d530c710bb98831c42ed620c710be98031c42f9600c710db94a21c436d5288710be98221c42f96088710afd9121c42bc6448710db94821c436d5208710f948421c42fa6008710be58021c433e54d0310cf55340c42f661d0310bd58740c433f5490310cf15240c433e5450310cf55140c42f76150310bd18540c433f5410310cf15040c42be64cc310af59330c435e53cc310d754f30c42f661cc310bd58730c435e534c310d754d30c42f7614c310bd18530c42be640c310af59030c42ee620c310bb58830c42f6610c310bd58430c436e52c8310db54b20c42f661c8310bd58720c42bf6448310af19120c436e5248310db54920c42f76148310bd18520c43e92008310bb98b54842ed62d52109f98f548427d63d52109f98b548436e62d52109b98b548427d62d5210db58b548426d62d5210dd587548437a60d5210cfd52548427e63952109f58e548427e62952109f58a548433f64552109fd8d548427c63552109fd89548427c6255210cf550548433e64152109f98c548427d63152109f988548427d6215210dd584548437a60152109f993538427d64d4e109f98b538427d62d4e10dd587538437a60d4e10af99253842bd6494e10d7d4e538427e6494e10cf992538423e6494e109f592538433d6494e108f592538427e6294e109f58a538437a6094e109fd91538427c6454e10d7d8d538427f6254e109f18953842be6414e10af590538435d5314e10bb98853842ed6214e109f990538433e6414e108f990538427d6414e10cf590538423d6414e10d798c538427e6214e10db988538426e6214e109f588538436d6214e109b58853843756114e10de980538427f65d0e109f997438427d65d0e109f197438433f54d0e10cf953438433d54d0e10cf153438433f65d0e10cf997438433d65d0e10cf197438433f53d0e10cf94f438433d53d0e10cf14f438427f6590e109f996438427d6590e109f19643842fa6090e10be582438427f6550e109f995438427d6550e109f195438433f5450e10cf951438433d5450e10cf15143842f76150e10bd185438433f6550e10cf995438433d6550e10cf195438439f6350e10cfd4d438433e5350e10cf54d438433c5350e10edd8543843b46150e109fd94438427e6510e109f594438427c6510e10be98043842f96010e10af99352842bd64d4a109f993528433e64d4a108f993528427d64d4a10cf593528423d64d4a109f98f528427d63d4a10cfd0f528433d43d4a10dd587528437a60d4a10dbd4a528427e6494a109f592528427e6394a109f58e528433f4394a10cf50e528427f6454a109f191528427f6354a109f18d528433f4354a10cf50d528436f6254a10db548
  | 7 => 0x494f10af59253c435f5394f109f99253c433e6494f108f99253c427d6494f10cf59253c423d6494f109f98a53c427d6294f10dd98653c427f6454f109f19153c435f6354f109fd8953c427c6254f10af99053c42bd6414f10d754c53c42ee6214f10bb58853c427e6414f10cf99053c423e6414f109f59053c433d6414f108f59053c435e6314f109f98853c436e6214f109b98853c427d6214f10db58853c426d6214f10dd98453c43796014f109fd9743c427e65d0f109f59743c427c65d0f10cfd5343c433e54d0f10cf55343c433c54d0f10cfd9743c433e65d0f10cf59743c433c65d0f10cfd4f43c433e53d0f10cf54f43c433c53d0f109fd9643c427e6590f109f59643c427c6590f10bd98643c42f56190f109fd9543c427e6550f109f59543c427c6550f10cfd5143c433e5450f10cf55143c433c5450f10bed8143c42f86050f10cfd9543c433e6550f10cf59543c433c6550f10e7d8d43c433f5350f10cf94d43c433d5350f10cf14d43c43bb6050f10ee18143c427f6510f109f99443c427d6510f109f19443c42f66110f10bd58443c42be64d4b10af59352c427e64d4b10cf99352c423e64d4b109f59352c433d64d4b108f59352c427e63d4b109f58f52c433f43d4b10cf50f52c437661d4b10de58352c436f5294b109f99252c427d6494b109f98e52c427d6394b10cfd0e52c433d4394b109fd9152c427c6454b109fd8d52c427c6354b10cfd0d52c433d4354b10dbd8952c436d5214b109f99052c427d6414b109f98c52c427d6314b10cfd0c52c433d4314b10db98852c43766114b10de58052c427f65d0b109f99742c427d65d0b109f19742c436e52d0b10db54b42c427f6590b109f99642c427d6590b109f19642c433e5490b10cf55242c42fa6090b10be58242c427f6550b109f99542c427d6550b109f19542c42f76150b10bd18542c427f6510b109f99442c427d6510b109f19442c433e5410b10cf55042c436e5210b10db54842c42f66110b10bd58442c427f65ccb109f99732c427d65ccb109f19732c42be64ccb10af59332c42f661ccb10bd58732c427f658cb109f99632c427d658cb109f19632c436e528cb10db54a32c427f654cb109f99532c427d654cb109f19532c436e524cb10db54932c42fb604cb10be18132c427f650cb109f99432c427d650cb109f19432c42be640cb10af59032c42f6610cb10bd58432c42fa600cb10be58032c433e5490710cf55241c42fa6090710be58241c433e5410710cf55041c43b54110710be98041c42f96010710af99331c42bd64cc710d794e31c435d538c710be98231c42f9608c710dd59631c4376538c710f594e31c43d5538c710dd14e31c43b7438c710ed50e31c4377528c710dd54a31c42f6608c710fc98231c43f1608c710bdd9531c4377654c710f5d8d31c4
  | 8 => 0x20bb1893108376514c420dd54531082fb604c420be181310827f650c4209f994310827d650c420af99031082bd640c420bb98831082ed620c420be98031082f9600c420dd947210837551c8420be98321082f960c84209f596210827f6548420afd9121082bc6448420dd94421083755108420f948421082fa6008420be580210827e64940209f592500827e63940209f58e500833f4394020cf50e500827d65d00209fd96400827d6590020cf952400833d5490020bb98a40082ed62900209fd95400827f65100209f994400827d65100209f194400833e5410020cf55040082ee6210020bb588400827d65cc020af99330082bd64cc0209fd96300827d658c020d794e300835d538c020bb98a30082ed628c020de942300827f654c020de941300827f650c0209f994300827d650c0209f19430082be640c020af590300835e530c020d754c30082ee620c020bb58830082f6610c020bd584300836f53c8020db54f20083af43c8020eb50f20082ed6288020db94a200837b5388020de54e20083bb4388020ee50e20082f96288020ba58a200837a5288020fa94a200827f6548020afd9120082bc6448020bbd95200836f65480209bd9520083af6448020eb191200836f5348020db54d20083af4348020eb50d20082ef6048020db94120083eb4048020fa90120083e94048020fa10120083eb3048020fa8c120083e93048020fa0c120082fb6548020ded95200827b6548020eed9120083b86448020ded4d20083795348020eed0d20083b94348020bed8920083eb6248020de94920083ea5248020fad0920083ea4248020fa50920083e84248020facc920083ea3248020fa4c920083e83248020fac8520083ea2148020fa48520083e82148020fad9520082eb6548020dad9520083eb6448020ead9120083ea6448020fa59120083e86448020ea19120083eb5448020fa95120083e95448020fa15120083eb6348020fa98d20083e96348020fa18d20083eb5348020dad4d20083ea5348020fa54d20083695348020fa14d20083eb4348020ead0d20083ea4348020fa50d20083a94348020fa10d20083eb6148020fa98520083e96148020fa18520083eb5148020fa94520083e95148020fa14520083eb4148020fa90520083e94148020fa10520083eb3148020fa8c520083e93148020fa0c520082ee62d5310bb58b54c427e63d53109f58f54c427e62d5310db98b54c426e62d53109f58b54c436d62d53109b58b54c437661d5310de58354c433f54953109f98e54c427d63953109f98a54c427d6295310cfd9154c427f63553109f18d54c427f62553109f18954c433d5415310cf99054c427e63153109f58c54c427e62153109f58854c43766115310de58054c427e64d4f109f59353c427e62d4f109f58b53c437661d4f10de58353c42be6
  | 9 => 0x983530827d6594c20af99253082bd6494c20d7d4e530827e6494c20cf992530823e6494c209f592530833d6494c208f592530827e6194c209f586530827f6454c209f191530835f6354c209fd89530827d6254c209fd85530827c6154c20af99053082bd6414c20d754c53082f66114c20bd584530827e6414c20cf990530823e6414c209f590530833d6414c208f590530827e6314c20d798c530827e6214c20db988530826e6214c209f98453083766114c209d984530827d6114c20dd58453082756114c209f980530837a6014c209e980530827f65d0c209f997430827d65d0c209f197430833f54d0c20cf953430833d54d0c20cf153430833f65d0c20cf997430833d65d0c20cf197430833f53d0c20cf94f430833d53d0c20cf14f430827f6590c209f996430827d6590c209f19643082bd6490c20d794e430835d5390c209fd95430827e6550c209f595430827c6550c20cfd51430833e5450c20cf551430833c5450c20d794d430835d5350c20bbd8943082ec6250c20bed8143082f86050c20cfd95430833e6550c20cf595430833c6550c20e7d8d430833f5350c20cf94d430839e5350c20c794d430833d5350c20e754d430831d5350c20cf14d43083af6250c20eb18943083bb6050c20ee181430827f6510c209f994430827d6510c209f19443082be6410c209f992520827d64948209f98e520827d6394820cfd0e520833d43948209f597420827f65908209f596420833e5490820cf55242082fa6090820be582420827f65508209fd94420827d6510820cf950420833d5410820be98042082f960108209f59732082be64cc820af593320827f658c8209f596320835e538c820d754e320836e528c820be98232082f9608c8209fd95320836e524c8209fd94320827d650c820af99032082bd640c820d794c320835d530c820bd98432082f5610c820be98032082f9600c820ddd46510827e64944209f592510827e63944209f58e510833f4394420cf50e51082bf6454420af191510827f6454420cfd91510823f64544209f191510833c64544208f191510827f63544209f18d510833f4354420cf50d51082be6414420af59051082de6314420b758c510837551144209fd97410827e65d04209f597410833e54d0420cf553410827f65904209f996410827d6590420cfd52410833c5490420bb98a41082ed6290420dd94641083755190420be98241082f960904209fd95410827d65504209f195410833e5450420cf55141083765150420dd545410827f65104209f994410827d6510420cfd50410833c54104209fd97310827e65cc4209f59731082be64cc420af593310835e53cc420d754f310827f658c4209f996310827d658c420dd9463108375518c4209fd95310827d654c4209f195310835e534c420d754d31082ef624c4
  | 10 => 0x14827c65cc520af99331482bd64cc520cfd53314833c54cc520bb98b31482ed62cc520ddd47314837451cc520be98331482f960cc5209f996314827d658c5209f196314833f548c520cf152314835f538c520d714e314827f654c5209f995314827c654c520cfd51314833c544c5209f994314827d650c5209f19431482be640c520af590314833f540c520cf150314835f530c520d714c31482ee620c520bb5883148377510c520dd14431482fa600c520be580314827e65c8520cfd53214833c54c8520cfd52214833c5488520ddd4621483745188520be98221482f96088520afd9121482bc6448520cfd51214833c5448520ddd4521483745148520bed8121482f860485209f994214833f5408520cf15021483e521085209f997404833f54d0120cf15340482ee62d0120bb58b404827e6590120cfd52404833c54901209fd95404827d65501209f195404833f5450120cf15140482ef6250120bb189404827e6510120cfd50404833c5410120ee500404827e65cc120af99330482bd64cc120cfd53304833c54cc120d7d4f304835c53cc120bb98b30482ed62cc1209f996304833f548c120cf15230482fa658c120de99630483bb548c120ee15230482f9638c120de94e3048378538c120eed0e30483b9438c120fad8a30482fa628c120fa18a30483ea328c120fa4ca304837b518c1209fd95304827d654c1209f195304833f544c120cf151304835f534c120d714d30482ef624c120bb18930482f8654c120de1953048278654c120eed5130483b8544c120f6d8d30483db534c120de94d3048378534c120f614d30483bb434c120ee50d30483eb624c120be18930483e8624c120ba18930483ea324c120fa4c9304837b514c1209f99430482be640c120af590304833f540c120cf15030482ee620c120bb58830482f6610c120bd58430482fa600c120cfd53204833c54c8120eed5320483b854c8120bed8f20482f963c8120eed0f20483b943c8120fa8cb20483e932c8120cfd52204833c5488120ebd5220483ac5488120bbd8e20482ed6388120ebd0e20483ad4388120fad4220483ea3088120fa4c2204827e63d50209f58f540827e62d5020db98b540827e61d50209f587540827e60d5020de983540827d6595020cfd52540827e63950209f58e540827e61950209f586540833f64550209fd8d540827c63550209fd89540827d62550209fd85540827c6155020cf55054082de6315020b758c54082f66115020bd584540827e6415020cf990540827e6315020d798c540825e63150209f58c540835d63150209758c540827e6215020db988540827e6115020dd984540827661150209f584540837561150209d584540827e6015020de980540827e64d4c209f593530827e62d4c20db98b530827e61d4c209f587530827e60d4c20de
  | 11 => 0x3c5414d20d754c53482f66114d20bd584534827e6414d20cf990534823e6414d209f590534833d6414d208f590534835e6314d209f988534836d6214d209f188534827e6114d20dd98453482766114d209f58453483756114d209d58453483796014d209fd97434827e65d0d209f597434827c65d0d20cfd53434833e54d0d20cf553434833c54d0d20cfd9743482be65d0d20cf997434823e65d0d20cf59743482bc65d0d20cf197434823c65d0d20cfd4f434833e53d0d20cf54f434833c53d0d209fd96434827e6590d209f596434827c6590d20af592434833f5490d20cf15243482ee6290d20bb58a43482fa6090d20be582434827f6550d209f995434827d6550d209f195434833f5450d20cf951434833d5450d20cf151434833f6550d20af995434833e6550d208f995434833d6550d20af195434833c6550d208f195434839f6350d20cfd4d434833e5350d20cf54d434833c5350d209fd94434827e6510d209f594434827c6510d20af990434833f5410d20cf15043482ee6210d20bb58843482fa6010d20be580434827e65d0920cfd53424833c54d0920be98342482f960d09209f996424833f5490920cf152424827c6550920cfd51424833c5450920bed8142482f860509209f994424833f5410920cf15042483ad42109209f99732482be64cc920af593324833f54cc920cf153324835f53cc920d714f32482fa60cc920be583324827e658c920cfd52324833c548c920bb996324836e658c920ebd5232483ac548c920bb58e324836e538c920db14e32483af438c920eb50e32483eb608c920bb98232483e8608c9209f195324833f544c920cf151324835f534c920d714d32482fb604c920be181324836c654c9209b19532483af544c920eb15132483cf634c920f3d4d324836e534c920db14d32483cc534c920ebd0d32483ad434c920fad8132482ec604c920fa18132482e8604c9209f99432482be640c920af590324833f540c920cf15032482ee620c920bd98432482f5610c920be980324833f54d4520cf153514827e64d45209f593514827e63d45209f58f514833f43d4520cf50f514836e32d4520db4cb51482be6494520af592514833f5494520cf15251483775194520afd9151482bc6454520cfd51514833c5454520b7d8d51482dc6354520cfd50514833c5414520dd544514827e64145209f590514827e63145209f58c514833f4314520cf50c514827e65d05209f597414827c65d0520cfd53414833c54d05209f996414827d65905209f196414833f5490520cf152414827f65505209f995414827c6550520cfd51414833c5450520bbd8941482ec6250520bed8141482f860505209f994414827d65105209f194414833f5410520cf15041482ee6210520bb58841482fa6010520be580414827e65cc5209f5973
  | 12 => 0x10620be98041882f960106209fd97318827e65cc6209f59731882be64cc620af59331882fa60cc620be583318827f658c6209f996318827d658c620dd9463188375518c6209fd95318827d654c6209f19531882ef624c620bb1893188376514c620dd545318827f650c6209f994318827d650c620af99031882bd640c620bb98831882ed620c620be98031882f9600c620dd94621883755188620be98221882f96088620afd9121882bc6448620dd94521883755148620bed8121882f86048620f9484218833e5490220cf55240882ee6290220bb58a408833e5410220cf55040882ee6210220bb58840883b94010220af99330882bd64cc220d794e308835d538c220bb98a30882ed628c220be5963088379658c220de94e30883da538c220f654e3088378538c220eed0e30883b9438c220be98a30883ea628c220fa58a3088379518c220bed95308837b654c220f6d8d308837a534c220de14d30883bb434c220ee50d30882f8624c220de54530882be640c220af590308835e530c220d754c30882ee620c220bb58830882f6610c220bd58430882ed65c8220db597208836f53c8220db54f20883af43c8220eb50f20882f965c8220de59720882fb63c8220be58f20883bb43c8220ee50f208827e63d51209f58f544827e61d51209f58754482bd63d5120cfd8f544833e63d5120cf58f544823d63d5120cf18f544833f62d5120cf58b544833f61d5120cf987544833d61d5120cf187544833f60d5120cf583544833f54951209f992544823e64951209f98e544827d63951209f58a544836d62951209f986544827d61951209f58254483796095120cfd91544827f63551209f18d544827f6255120dbd89544827f61551209f185544827f6055120ded81544827e6515120cf550544833e64151209f98c544827d63151209f988544827c62151209f984544827d6115120af994544833e65151208f99454482bd6315120cfd8c544833e6315120cf58c544823d6315120cf18c544833f6215120cf588544833f6115120cf984544833d6115120cf184544833f6015120cf580544833d2015120cfd53534833c54d4d20cfd93534827e64d4d209f593534833c64d4d209f987534827d61d4d20af99253482bd6494d20cfd52534833c5494d20d7d4e534827e6494d20cf992534823e6494d209f592534833d6494d208f592534827e6394d209f58a534836d6294d209f986534827d6194d209f58253483796094d20afd9153482bc6454d20cfd51534833c5454d20bdd8553482f46154d209fd91534833f6454d208fd91534827c6454d20cf191534823c6454d20d7d8d534827f6254d20dbd89534827f6154d20ddd8553482776154d209f18553483746154d209d185534827f6054d20ded81534827e6514d20af99053482bd6414d20cfd5053483
  | 13 => 0xcf55340c82ee62d0320bb58b40c833f5490320cf15240c833e5450320cf55140c82ef6250320bb18940c833f5410320cf15040c82be64cc320af59330c835e53cc320d754f30c82ee62cc320bb58b30c835e534c320d754d30c82ef624c320bb18930c82be640c320af59030c82ee620c320bb58830c82f6610c320bd58430c82f661d5220bd587548827e63d52209f58f548836d62d52209f987548837661d52209d987548827d61d5220dd587548827561d5220de983548833f54952209f98e548827d63952209f986548827d6195220cfd91548827f63552209f18d548827f61552209f185548833d5415220cf990548827e63152209f58c548836d62152209f984548827d6115220de980548827e64d4e209f593538836d62d4e209f987538827d61d4e20de98353882be6494e20af592538835f5394e209f992538833e6494e208f992538827d6494e20cf592538823d6494e209f986538827d6194e20de982538827f6454e209f191538835f6354e209fd85538827c6154e20af99053882bd6414e20d754c53882f66114e20bd584538827e6414e20cf990538823e6414e209f590538833d6414e208f590538835e6314e20db588538827e6114e20dd98453882766114e209f58453883756114e209d584538837a6014e209fd97438827e65d0e209f597438827c65d0e20cfd53438833e54d0e20cf553438833c54d0e20cfd97438833e65d0e20cf597438833c65d0e20cfd4f438833e53d0e20cf54f438833c53d0e209fd96438827e6590e209f596438827c6590e20be98243882f96090e209fd95438827e6550e209f595438827c6550e20cfd51438833e5450e20cf551438833c5450e20bbd8943882ec6250e20cfd95438833e6550e20cf595438833c6550e20e7d8d438833f5350e20cf94d438833d5350e20cf14d43883af6250e20eb189438827f6510e209f994438827d6510e209f19443882fa6010e20be580438833e54d0a20cf55342882fa60d0a20be583428833f5490a20cf152428833e5450a20cf55142882fb6050a20be181428833f5410a20cf15042882be64cca20af593328835e53cca20d754f32882fa60cca20be583328835e534ca20d754d32882fb604ca20be18132882be640ca20af59032882f6610ca20bd58432882f9600ca20af99351882bd64d4620ddd46518827e64946209f592518827e63946209f58e518833f4394620cf50e518827f64546209f191518827f63546209f18d518833f4354620cf50d518837551146209fd97418827e65d06209f597418837651d0620dd547418827f65906209f996418827d6590620cf952418833d5490620bb98a41882ed62906209fd95418827d65506209f19541882fb6050620be181418827f65106209f994418827d6510620cf950418833d5410620dd944418837551
  | 14 => 0x9353c836e62d4f209f98753c827d61d4f20de58353c82be6494f20af59253c835f5394f209f99253c833e6494f208f99253c827d6494f20cf59253c823d6494f20db98a53c827e6194f209f58653c827f6454f209f19153c835f6354f209fd8553c827c6154f20af99053c82bd6414f20d754c53c82f66114f20bd58453c827e6414f20cf99053c823e6414f209f59053c833d6414f208f59053c835e6314f20db98853c827e6114f20dd98453c82766114f209f58453c83756114f209d58453c83796014f209fd9743c827e65d0f209f59743c827c65d0f20cfd5343c833e54d0f20cf55343c833c54d0f20cfd9743c833e65d0f20cf59743c833c65d0f20cfd4f43c833e53d0f20cf54f43c833c53d0f209fd9643c827e6590f209f59643c827c6590f20bb98a43c82ed6290f209fd9543c827e6550f209f59543c827c6550f20cfd5143c833e5450f20cf55143c833c5450f20bed8143c82f86050f20cfd9543c833e6550f20cf59543c833c6550f20e7d8d43c833f5350f20cf94d43c833d5350f20cf14d43c83bb6050f20ee18143c827f6510f209f99443c827d6510f209f19443c82ee6210f20bb58843c833e5490b20cf55242c82fa6090b20be58242c833e5410b20cf55042c83ad4210b20be98042c82f96010b20af99332c82bd64ccb20d794e32c835d538cb20be98232c82f9608cb20db59632c836e538cb20f394e32c83cd538cb20db14e32c83af438cb20eb50e32c82ee608cb20fa98232c83e9608cb20bbd9532c836f654cb20f3d8d32c836e534cb20db14d32c83af434cb20eb50d32c82ec604cb20af99032c82bd640cb20d794c32c835d530cb20bd98432c82f5610cb20be98032c82f9600cb20af99351c82bd64d4720ddd4651c827e64947209f59251c827e63947209f58e51c833f4394720cf50e51c827f64547209f19151c827f63547209f18d51c833f4354720cf50d51c836e3254720db4c951c837551147209fd9741c827e65d07209f59741c837651d0720dd54741c827f65907209f99641c827d6590720cf95241c833d5490720be98241c82f960907209fd9541c827d65507209f19541c82ef6250720bb18941c827f65107209f99441c827d6510720cf95041c833d5410720bb98841c82ed6210720dd94441c837551107209fd9731c827e65cc7209f59731c82be64cc720af59331c82ee62cc720bb58b31c827f658c7209f99631c827d658c720dd94631c8375518c7209fd9531c827d654c7209f19531c8376514c720dd54531c82fb604c720be18131c827f650c7209f99431c827d650c720af99031c82bd640c720bb98831c82ed620c720be98031c82f9600c720dd94721c837551c8720be98321c82f960c8720afd9121c82bc6448720dd94421c83755108720f948421c82fa6008720be58021c833e54d032
  | 15 => 0xc36e524c430db549310c376514c430af990310c2bd640c430cf950310c33d540c430bb988310c2ed620c430db948310c36d520c430dd944310c375510c430be980310c2f9600c4309fd97210c27e65c84309f597210c33e54c8430cf553210c36e52c8430db54b210c37651c8430dd547210c27f65884309f996210c27d6588430cf952210c33d5488430db94a210c36d5288430dd946210c37551884309fd95210c27d65484309f195210c2bf6448430af191210c33e5448430cf551210c2df6348430b718d210c36e5248430db549210c3765148430dd545210c2fb6048430be181210c27f65084309f994210c27d6508430cf950210c33d5408430db948210c36d5208430dd944210c3755108430f9484210c27e64940309f592500c33f4394030cf50e500c27d65d0030cf953400c33d54d0030db94b400c36d52d0030dd947400c37551d00309fd96400c27d6590030cf952400c33d5490030b798e400c2dd6390030db94a400c36d5290030dd946400c37551900309fd95400c33e5450030cf551400c36e5250030db549400c3765150030dd545400c27f65100309f994400c27d65100309f194400c33e5410030cf550400c2de6310030b758c400c36e5210030db548400c3765110030dd544400c3b94010030af993300c2bd64cc030cf953300c33d54cc030e7d0f300c39d43cc030db94b300c36d52cc030dd947300c37551cc030e7993300c39d64cc030e7953300c39d54cc030f394b300c3cd52cc030f5947300c3d551cc030cf952300c33d548c030b758e300c35e538c030db94a300c36d528c030dd946300c375518c030ee952300c3b9548c030be58e300c37a538c030f694e300c3bb438c030ee50e300c3ea528c030de54a300c3e9528c030da54a300c3f2518c030de546300c3f1518c030dc546300c27f654c030cf951300c33d544c030e7d0d300c39d434c030db949300c36d524c030dd945300c375514c030b7d95300c35f654c03097d95300c39e544c030e7551300c3ce524c030f3549300c3d6514c030f5545300c2df604c030d7941300c3da404c030f6501300c2fb654c030ded95300c27b654c030ee951300c3b9544c030bed8d300c3db634c030de94d300c3da534c030eed0d300c3da434c030ee50d300c3d9434c030e650d300c3ea524c030de549300c3e9524c030da549300c3f2514c030de545300c3f1514c030dc545300c2f661d5320bd58754c827e63d53209f58f54c836e62d53209f98754c837661d53209d98754c827d61d5320dd58754c827561d5320de58354c833f54953209f98e54c827d63953209f98654c827d6195320cfd9154c827f63553209f18d54c827f61553209f18554c833d5415320cf99054c827e63153209f58c54c836e62153209f98454c827d6115320de58054c827e64d4f209f5
  | 16 => 0xe65108309f594420c33e5410830cf550420c36e5210830db548420c2be64cc830af593320c33e54cc830cf553320c36e52cc830db54b320c2fa60cc830be583320c27d658c830cf952320c33d548c830db54a320c27f654c830cf951320c33d544c830db949320c2be640c830af590320c33e540c830cf550320c36e520c830db548320c2f6610c830bd584320c2fa600c830be580320c2be64d4430af593510c33e54d4430cf553510c2ee62d4430bb58b510c36e52d4430db54b510c33e5494430cf552510c36e5294430db54a510c37751944309f992510c27d6494430cfd0e510c33d43944309f98a510c27d6294430ddd52510c3765494430ed952510c3365494430dd552510c3b55494430cd552510c3745494430edd0e510c3b54394430ddd4a510c3765294430f994a510c3665294430dd54a510c3e55294430d954a510c3745294430ddd92510c3766494430dd592510c3746494430dd18e510c3774394430cdd0e510c3764394430dd50e510c3354394430dd10e510c3776294430dd98a510c3756294430dd18a510c3774294430dd90a510c3754294430dd10a510c3773294430dd8ca510c3753294430dd0ca510c3766094430dd182510c33e5454430cf551510c36e5254430db549510c27f64544309f191510c33f4354430cf50d510c27f62544309f189510c3776554430ddd51510c3765454430ed951510c3365454430dd551510c3b55454430cd551510c3745454430edd0d510c3b54354430ddd49510c3765254430f9949510c3665254430dd549510c3e55254430d9549510c3745254430ddd91510c3766454430dd591510c3746454430dd98d510c3774354430cdd0d510c3764354430dd50d510c3354354430dd10d510c3776254430dd989510c3756254430dd189510c3774254430dd909510c3754254430dd109510c3773254430dd8c9510c3753254430dd0c9510c3766054430dd181510c3743054430af990510c2bd6414430cf950510c33d5414430bb988510c2ed6214430db948510c36d5214430bd984510c37551144309fd97410c27e65d04309f597410c33e54d0430cf553410c36e52d0430db54b410c37651d0430dd547410c27f65904309f996410c27d6590430cf952410c33d5490430db94a410c36d5290430dd946410c37551904309fd95410c27d65504309f195410c33e5450430cf551410c36e5250430db549410c3765150430dd545410c2fb6050430be181410c27f65104309f994410c27d6510430cf950410c33d5410430db948410c36d5210430dd944410c3755110430af993310c2bd64cc430cf953310c33d54cc430db94b310c36d52cc430dd947310c37551cc430be983310c2f960cc4309f596310c33e548c430cf552310c36e528c430db54a310c375518c4309fd95310c33e544c430cf55131
  | 17 => 0x50309f98a540c27d62950309f986540c27d61950308f596540c33e6395030cf18e540c33f6295030cf98a540c33d6295030cf18a540c33f6195030cf986540c33d6195030cf186540c33e6095030cf182540c33f64550309fd8d540c27d63550309fd89540c27c62550309fd85540c27c6155030cfd95540c23f6355030cf98d540c23d6355030cf18d540c33f6255030cf989540c33d6255030cf189540c33f6155030cf985540c33d6155030cf185540c33e6055030cf181540c33c3055030af990540c33d5415030bb988540c2ed6215030bd984540c2f561150309f990540c33e64150308f990540c27e6315030d798c540c27e6215030db988540c26e62150309f588540c36d62150309b588540c27e6115030dd984540c27661150309f584540c37561150309d584540c27e6015030de980540c27e6494c30cf992530c23e6494c309f592530c33d6494c308f592530c27d65d0c30cfd53430c33e54d0c30cf553430c33c54d0c30af597430c33d65d0c308f597430c33e53d0c309fd96430c27d6590c30af592430c33e5490c30cf552430c2fa6090c30be582430c27f6550c30cfd51430c33e5450c30cf551430c33c5450c30afd95430c33f6550c308fd95430c39f6350c30cf94d430c27f6510c309f594430c2be6410c30cf950430c33d5410c30be980430c2f96010c30af993520c2bd64d4830cf953520c33d54d4830bd987520c2f561d4830cf952520c33d5494830dbd4a520c27e64948309f592520c33f4394830cf50e520c27e61948309f586520c36f5494830db952520c3ae5494830cb952520c36d5494830eb552520c32d5494830db152520c3af4394830eb50e520c36f6494830db992520c36d6494830db192520c36c6394830dbd0e520c32f4394830db90e520c36d4394830cb50e520c36c4394830dbd86520c36e6194830db586520c36c6194830db982520c36c6094830cf951520c33d54548309fd91520c27c6454830cfd0d520c33d43548309fd85520c27c6154830dbd95520c36f5454830db951520c3ae5454830cb951520c36d5454830eb551520c32d5454830db151520c3af4354830eb50d520c36f6454830db991520c36d6454830db191520c36e6354830dbd0d520c32f4354830db90d520c36d4354830cb50d520c36c4354830dbd85520c36e6154830db585520c36c6154830db981520c36c6054830db0c1520c2be6414830af590520c33e5414830cf550520c2ee6214830db548520c2f66114830bd584520c27f65d08309f997420c27d65d0830cf953420c33d54d0830db94b420c36d52d08309fd96420c27e65908309f596420c33e5490830cf552420c36e5290830db54a420c27f65508309f595420c27c6550830cf951420c33d5450830db949420c36d5250830bed81420c2f860508309fd94420c27
  | 18 => 0xcf195434c39f6350d30eed81434c3b86050d309f994434c2be6410d309f993524c27d64d4930cfd0f524c33d43d49309f987524c27d61d4930dbd4a524c2bf6454930af191524c2f76154930bd185524c36d52149309f990524c27d6414930cfd0c524c33d43149309f984524c27d6114930de580524c27e65d09309f597424c27c65d0930dbd4b424c36c52d09309f996424c27d65909309f196424c33f5490930cf152424c2fa6090930be582424c27f65509309f995424c27c65509309f994424c27d65109309f194424c33f5410930cf150424c2de6310930b758c424c36f5210930db148424c2fa6010930be580424c27e65cc930af993324c2bd64cc930e750f324c36f528c930db14a324c2fa608c930be582324c39d434c930dbd49324c36c524c930bed81324c2f8604c9309f994324c2be640c930af590324c2f6610c930bd584324c2fa600c9309f993514c27d64d4530cfd0f514c33d43d45309f98b514c27d62d4530ddd46514c2bf6454530af191514c2ef6254530bb189514c37551145309f990514c27d6414530cfd0c514c33d43145309f988514c27d6214530de580514c27e65d05309f597414c27c65d0530ddd47414c37451d05309f996414c27d65905309f196414c33f5490530cf152414c2fa6090530be582414c27f65505309f995414c27c65505309f994414c27d65105309f194414c33f5410530cf150414c2de6310530b758c414c3775110530dd144414c2fa6010530be580414c27e65cc530af993314c2bd64cc530e750f314c377518c530dd146314c2fa608c530be582314c39d434c530ddd45314c374514c530bed81314c2f8604c5309f994314c2be640c530af590314c2ee620c530bb588314c2fa600c5309f997214c27d65c85309f197214c37751c8530dd147214c2fa60c8530be583214c27e65885309f596214c27c6588530dbd4a214c36c5288530be982214c2f960885309fd95214c27e65485309f195214c2bf6448530af191214c27e65085309f594214c27c6508530b798c214c2dd6308530dbd48214c36c5208530ddd44214c3745108530f9484214c2fa6008530be580214c27e65d0130cfd53404c33c54d0130b798f404c2dd63d01309f996404c33e5490130cf552404c27f65501309f595404c27c6550130cfd51404c33c5450130b7d8d404c2dc63501309f994404c33e5410130cf550404c2be64cc130af593304c3ba64cc130ee593304c3bb43cc130ee50f304c2f962cc130be587304c39f438c130e750e304c3db508c130bb98b540c2ed62d5030bd987540c2f561d50309f98f540c35e63d50309f98b540c36e62d50309b98b540c27d62d5030db58b540c26d62d50309f987540c37661d50309d987540c27d61d5030dd587540c27561d50309f983540c37a60d50309f596540c33f549
  | 19 => 0x1528c27c6454a30cf191528c23c6454a30cfd0d528c33d4354a309fd85528c27c6154a30db548528c27f65d0a309f997428c27d65d0a309fd96428c27e6590a309f596428c33f5490a30cf152428c2fa6090a30be582428c27f6550a309f595428c27c6550a309fd94428c27e6510a309f594428c33f5410a30cf150428c2fa6010a30be580428c2be64cca30af593328c36e528ca30db54a328c2fa608ca30be582328c36e524ca30db549328c2fb604ca30be181328c2be640ca30af590328c2f6610ca30bd584328c2f9600ca30ddd46518c27e64946309f592518c33f4394630cf50e518c27e62946309f58a518c37a6094630afd91518c2bc64546309fd91518c33f64546308fd91518c27c6454630cf191518c23c6454630cfd0d518c33d43546309fd89518c27c6254630dd544518c27f65d06309f997418c27d65d06309fd96418c27e65906309f596418c33f5490630cf152418c2fa6090630be582418c27f65506309f595418c27c65506309fd94418c27e65106309f594418c33f5410630cf150418c2fa6010630be580418c2be64cc630af593318c376518c630dd546318c2fa608c630be582318c376514c630dd545318c2fb604c630be181318c2be640c630af590318c2ee620c630bb588318c2f9600c6309fd97218c27e65c86309f597218c2fa60c8630be583218c27f65886309f996218c27d6588630be982218c2f960886309fd95218c27d65486309f195218c2bf6448630af191218c2df6348630b718d218c27f65086309f994218c27d6508630f9484218c2fa6008630be580218c33f54d0230cf153408c33e5490230cf552408c2de6390230b758e408c33f5450230cf151408c33e5410230cf550408c2de6310230b758c408c2be64cc230af593308c39f43cc230e750f308c2dd65cc230d7597308c39e64cc230e7593308c2f965cc230de597308c3ba64cc230ee593308c3bb43cc230ee50f308c2f962cc230be587308c27e62d51309f58b544c27e61d51309f587544c33f54951309f992544c27d6395130d758e544c27e62951309f58a544c27e61951309f586544c27d6095130de582544c2ef6255130bb189544c2f76155130bd185544c33f64551309fd8d544c35f63551309fd89544c36f62551309bd89544c27c6255130db189544c26c62551309fd85544c37761551309dd85544c27c6155130dd185544c27461551309fd81544c37b60551309f994544c33d5415130cf990544c27e63151309f18c544c27e62151309f588544c27e61151309f584544c27e65d0d30cfd53434c33c54d0d30be983434c2f960d0d30cfd97434c33e65d0d30cf597434c33c65d0d30ee983434c3b960d0d309f996434c2bd6490d309f195434c33f5450d30cf151434c2fb6050d30be181434c33f6550d30cf995434c33d6550d30
  | 20 => 0xc27f6550b309f59542cc27c6550b30cf95142cc33d5450b30bed8142cc2f86050b309fd9442cc27e6510b309f59442cc33e5410b30cf55042cc2de6310b30b758c42cc2be64ccb30af59332cc33e54ccb30cf55332cc39d43ccb30db94b32cc36d52ccb30be98332cc2f960ccb30cf95232cc33d548cb30cf95132cc33d544cb30e750d32cc2be640cb30af59032cc33e540cb30cf55032cc36e520cb30db54832cc2f6610cb30bd58432cc2fa600cb30be58032cc2be64d4730af59351cc33e54d4730cf55351cc33e5494730cf55251cc37751947309f99251cc27d6494730cfd0e51cc33d43947309f98a51cc27d6294730cf95151cc33d54547309fd9151cc27c6454730cfd0d51cc33d43547309fd8951cc27c6254730af99051cc2bd6414730cf95051cc33d5414730bb98851cc2ed6214730dd54451cc27f65d07309f99741cc27d65d0730cf95341cc33d54d07309fd9641cc27e65907309f59641cc33e5490730cf55241cc27f65507309f59541cc27c6550730cf95141cc33d5450730bed8141cc2f860507309fd9441cc27e65107309f59441cc33e5410730cf55041cc2de6310730b758c41cc2be64cc730af59331cc33e54cc730cf55331cc39d43cc730dd94731cc37551cc730be98331cc2f960cc730cf95231cc33d548c730cf95131cc33d544c730e750d31cc2be640c730af59031cc33e540c730cf55031cc2ee620c730bb58831cc376510c730dd54431cc2fa600c730be58031cc27f65c87309f99721cc27d65c8730cf95321cc33d54c8730db94b21cc36d52c87309fd9621cc27e65887309f59621cc33e5488730cf55221cc3765188730dd54621cc27f65487309f59521cc27c6548730afd9121cc2bc6448730cf95121cc33d5448730db94921cc36d5248730dd94521cc3755148730bed8121cc2f860487309fd9421cc27e65087309f59421cc33e5408730cf55021cc2de6308730b758c21cc3e52108730cf95340cc33d54d0330b798f40cc2dd63d0330cf95240cc33d5490330cf95140cc33d5450330b7d8d40cc2dc6350330cf95040cc33d5410330ee50040cc35d63d52309f98b548c27d62d52309f987548c27d61d5230de983548c33f54952309f98a548c27d62952309f986548c27d6195230cfd91548c27f62552309f189548c27f61552309f185548c33d5415230cf990548c35d63152309f988548c27d62152309f984548c27d6115230de980548c33e54d0e30cf553438c2fa60d0e30be583438c33e65d0e30cf597438c3ba60d0e30ee583438c33e5450e30cf551438c2fb6050e30be181438c33f6550e30cf195438c39f6350e30eed81438c3b86050e30dbd4a528c27e6494a309f592528c33f4394a30cf50e528c27e6194a309f586528c37a6094a30afd91528c2bc6454a309fd91528c33f6454a308fd9
  | 21 => 0x64cc440af593311035e53cc440d754f311027f658c4409f996311027d658c440afd9231102bc648c440dd9463110375518c4409fd95311027d654c4409f19531102bf644c440af191311035e534c440d754d3110376514c440dd54531102fb604c440be181311027f650c4409f994311027d650c440af99031102bd640c440bb98831102ed620c440be98031102f9600c4409fd97211027e65c84409f59721102be64c8440af593211036e52c8440db54b21102fa60c8440be583211027f65884409f996211027d6588440af99221102bd6488440dd94621103755188440be98221102f960884409fd95211027d65484409f19521102bf6448440af191211036e5248440db54921103765148440dd545211027f65084409f994211027d6508440afd9021102bc6408440f9484211033f4394040cf50e501033e4294040cf10a501033e4194040cf10650102bd63d0040cf54f40102be62d0040af98740102bd6490040cf95240102f96490040de95240103ba5490040eed0e40103b94390040ee90a40103b84290040ee90640103b841900409fd9540102bf6550040cfd95401023f6550040afd8d401033d5350040af18940102bc6150040afd81401033e5050040bed95401037b65500409ed9540102fb6450040eed91401037a5450040ee95140103ba4350040ee10d40103bb4250040ee50940103bb4150040ee505401035e63d53309f98b54cc27d62d53309f98754cc27d61d5330de58354cc33f54953309f98a54cc27d62953309f98654cc27d6195330cf98e54cc33c6395330cfd8a54cc33e6295330cf58a54cc33c6295330cfd8654cc33e6195330cf58654cc33c6195330cfd8254cc33d6095330cfd9154cc27f62553309f18954cc27f61553309f18554cc33f6555330cf98d54cc33c6355330cfd8954cc33e6255330cf58954cc33c6255330cfd8554cc33e6155330cf58554cc33c6155330cfd8154cc33d6055330cf55054cc33e6415330d798c54cc27e62153309f58854cc27e61153309f58454cc3796015330cfd5343cc33e54d0f30cf55343cc33c54d0f30af59743cc33d65d0f30cf95243cc33d5490f30be98243cc2f96090f30cfd5143cc33e5450f30cf55143cc33c5450f30afd9543cc33f6550f30e7d8d43cc33e5410f30cf55043cc2fa6010f30be58043cc2be64d4b30af59352cc33e54d4b30cf55352cc33e5494b30cf55252cc36f5294b309f99252cc27d6494b30cfd0e52cc33d4394b309f98652cc27d6194b30cf95152cc33d5454b309fd9152cc27c6454b30cfd0d52cc33d4354b309fd8552cc27c6154b30af99052cc2bd6414b30cf95052cc33d5414b30db54852cc2f66114b30bd58452cc27f65d0b309f99742cc27d65d0b30cf95342cc33d54d0b309fd9642cc27e6590b309f59642cc33e5490b30cf55242c
  | 22 => 0x5409f996215027d65885409f19621503775188540dd146215027f65485409f995215027c6548540afd9121502bc6448540dbd49215036c5248540ddd45215037451485409f994215027d65085409f19421502be6408540af59021503e52108540be98021502f96008540eed0f40503b943d0140af58e405033f5390140cf14a405033c5190140eed42405035f5394c409f98a531027d6294c409f986531027d6194c40cf991531027f6254c409f189531027f6154c409f185531035d5314c40bb98853102ed6214c40bd98453102f56114c40cf953431035e53d0c40d754f43102fa60d0c40be583431033e53d0c40e794f431033d53d0c40e754f431031d53d0c40af98b43102be61d0c40ee98343102bd60d0c40ee58343102b960d0c409f59643102bd6490c409fd95431033e5450c40afd95431033f6550c40e7d8d431033e5350c40af18943102bc6150c40afd8143102be6410c40d794c431035d5310c40be98043102f96010c40dbd4a521027e63948409f58e521033f4394840cf50e521027e61948409f586521027f63548409f18d521033f4354840cf50d521027f61548409f18552102de6314840b758c521036d5214840bd98452102f56114840db94b421036d52d0840be98342102f960d08409f59642102bd6590840cf59642102bd6390840cf54e42102be6290840cf54a42102be6190840af582421027f6550840db948421036d5210840be98042102f96010840af58c421033d5310840af98842103ae6210840eb948421033d5210840eb548421032d5210840af98442103ba6010840af58042103b96010840ae580421027f65cc8409f997321027d65cc840af99332102bd64cc840d794f321035d53cc8409fd96321027e658c8409f59632102bf648c840af192321036e528c840db54a321027f654c8409f595321027c654c840afd9132102bc644c840d794d321035d534c840db949321036d524c840bed8132102f8604c8409fd94321027e650c8409f59432102be640c840af59032102f6610c840bd58432102fa600c840be580321037751944409f98e511027d6394440cfd0e511033d43944409f98a511027d6294440cf90a511033c42944409fd8d511027c6354440cfd0d511033d43544409fd89511027c6254440b798c51102dd6314440bb98851102ed6214440dd544511037651d0440dd54741102fa60d0440be583411027d6590440af596411033d6590440af58e411033d5390440af98a411033e5290440af986411033d5190440af582411027f6550440dd94441103755110440be98041102f96010440af58c411033d5310440af988411033e5210440af98441103b66110440ed944411033d5110440ed54441103355110440ee98041102bd6010440ee58041102b960104409fd97311027e65cc4409f59731102be
  | 23 => 0xf580419027f65cc6409f997319027d65cc640af99331902bd64cc6409fd96319027e658c6409f59631902bf648c640af1923190376518c640dd546319027f654c6409f595319027c654c640afd9131902bc644c640dd9453190375514c6409fd94319027e650c6409f59431902be640c640af59031902ee620c640bb58831902fa600c640be580319027f65c86409f997219027d65c8640af99321902bd64c8640dd947219037551c86409fd96219027e65886409f59621902be6488640af592219036e5288640db54a219027f65486409f595219027c6548640afd9121902bc64486409fd94219027e65086409f59421902bf6408640af190219036e5208640db54821903765108640dd54421903e52108640be98021902f96008640af597409033d65d0240af58f409033d53d0240af98b40902be61d0240be597409037965d0240cfd93535027e62d4d409f58b535027e61d4d409f587535035f5394d40bbd8953502ec6254d40bdd8553502f46154d40d754c535027e6214d409f588535027e6114d409f584535027e65d0d40af997435033e65d0d40cf14f43502be60d0d40af592435035f5390d40d714e43502fa6090d40be582435035f5350d40d714d43502fb6050d40be181435039f6350d40cfd4d435039f5350d40c7d4d435033c5350d40e714d43503bb6050d40af18143503b86050d40ae181435027e6510d40af990435027e63d49409f58f525033f43d4940cf50f525027e61d49409f587525036f5294940bd98652502f56194940db548525027e63149409f58c525033f4314940cf50c525027e61149409f584525027e65d0940dbd4a425036c5290940be98242502f96090940dbd49425036c5250940bed8142502f860509409f99442503ad42109409f997325027d65cc9409f19732502be64cc940af593325036f52cc940db14b325027e658c9409f596325027c658c9409fd95325027e654c9409f195325027e650c9409f594325027c650c940af99032502bd640c940dbd48325036c520c940bd98432502f5610c940be98032502f9600c9409f98f515027d63d4540cfd0f515033d43d45409f98b515027d62d4540bb98a51502ed6294540ddd46515037551145409f98c515027d6314540cfd0c515033d43145409f988515027d62145409f99741503775190540dd14641502fa6090540be58241503775150540dd14541502fb6050540be181415027e6510540ed504415027e65cc5409f597315027c65cc540af99331502bd64cc540ddd47315037451cc5409f996315027d658c5409f196315027f654c5409f995315027c654c5409f994315027d650c5409f19431502be640c540af59031502ee620c540bb5883150377510c540dd14431502fa600c540be580315027e65c85409f597215027c65c8540dbd4b215036c52c8
  | 24 => 0x51d033d43947409f98a51d027d62947409fd8d51d027c6354740cfd0d51d033d43547409fd8951d027c6254740dd54451d037651d0740dd54741d02fa60d0740be58341d03765110740dd54441d03b54110740be98041d02f960107409fd9731d027e65cc7409f59731d02be64cc740af59331d027f658c7409f99631d027d658c7409fd9531d027d654c7409f19531d02fb604c740be18131d027f650c7409f99431d027d650c740af99031d02bd640c740bb98831d02ed620c740be98031d02f9600c7409fd9721d027e65c87409f59721d02fa60c8740be58321d027f65887409f99621d027d6588740be98221d02f960887409fd9521d027d65487409f19521d02bf6448740af19121d027f65087409f99421d027d6508740af99021d02bd6408740f948421d035f5394e409f98a539027d6294e409f986539027d6194e40cf591539027f6254e409f189539027f6154e409f185539035d5314e40bb98853902ed6214e40bd98453902f56114e40af597439033d65d0e40cf94f43902be62d0e40af98743902bd60d0e40d794e439035d5390e40be98243902f96090e40d794d439035d5350e40bed8143902f86050e40e7d8d439033e5350e40e794d439033d5350e40e754d439031d5350e40af18943902bc6150e40afd8143903bb6050e40ee18143902f661d4a40bd587529036f5294a409f98e529027d6394a40cfd0e529033d4394a409f986529027d6194a409fd8d529027c6354a40cfd0d529033d4354a409fd85529027c6154a40db548529036e5290a40db54a42902fa6090a40be58242902bd6390a40cf54e42903ae5290a40cf54a42903ad5290a40af98642903ba6090a40af58242903b96090a40db949429036d5250a40bed8142902f86050a40af594429033d6510a40af58c429033d5310a40eb988429033d5210a40af98442902bd6010a409fd97329027e65cca409f59732902be64cca40af593329027f658ca409f996329027d658ca40afd9232902bc648ca40db94a329036d528ca409fd95329027d654ca409f19532902bf644ca40af191329036e524ca40db549329027f650ca409f994329027d650ca40af99032902bd640ca40bd98432902f5610ca40be98032902f9600ca40bb98b51902ed62d4640ddd46519027e63946409f58e519033f4394640cf50e519027e62946409f58a519033e4294640cf10a519027f63546409f18d519033f4354640cf50d519027f62546409f18951903755114640dd94641903755190640be98241902f96090640af58e419033d5390640af98a419033e5290640ed946419033d5190640ed54641903ba6090640af58241903b96090640dd94541903755150640bed8141902f86050640af594419033d6510640af58c419033d5310640af988419033e5210640ed984419033d5110640a
  | 25 => 0x6ee628c421bb58a3108776518c4219fd953108776514c4219fd94310867e650c4219f594310867c650c421af99031086bd640c421d794c310875d530c421bb98831086ed620c421be98031086f9600c421dbd4f210876d53c8421ebd0f21087ad43c8421bb58a210876e5288421ddd4e21087755388421edd0e21087b54388421bd58a21086e56288421dd94a21087e652884219fd9521086bf6448421af19121086ef6548421dbd95210866f6548421ebd9121087ac6448421dbd4d210876d5348421ebd0d21087ad4348421bbd85210876e5148421f9d0521087e64148421f950521087e44148421f9cc521087e63148421f94c521087e43148421bdd95210877765484219dd9521087b76448421ed19121087775348421dd54d21087b74348421ed50d21086f76248421f9d8921087765248421f994921087e74248421f990921087e54248421f910921087e73248421f98c921087e53248421f90c921087e76548421b9d9521087676548421f9d9121087a76448421f999121087e56448421f919121087a46448421f9d5121087e65448421f955121087e45448421f9d8d21087e66348421f958d21087e46348421f9d4d21087675348421f994d21087e55348421d954d21087e45348421f9d0d21087a74348421f990d21087e54348421e950d21087e44348421f9d8121087e66048421f958121087e46048421f948750087e52194021ded42500867e64940219f592500867e63940219f58e500873f4394021cf50e50086bf6454021af19150087e521540219fd91500873f64540218fd91500867c6454021cf191500863c64540219fd8d500867c6354021cfd0d500873d4354021af99050086bd6414021b798c50086dd6314021f948450087795014021d7d4e53d027e6294f409f58a53d027e6194f409f58653d033e6454f409fd8953d027c6254f409fd8553d027c6154f40d754c53d035e53d0f40d754f43d02fa60d0f40be58343d033e53d0f40e794f43d033d53d0f40e754f43d031d53d0f40af98343d03ba60d0f40ee58343d02bf6550f40cfd9543d039f6350f40cf94d43d02bc6050f40d794c43d035d5310f40be98043d02f96010f40dbd4a52d027e6394b409f58e52d033f4394b40cf50e52d027e6194b409f58652d027f6354b409f18d52d033f4354b40cf50d52d027f6154b409f18552d036d5214b40db94b42d036d52d0b40be98342d02f960d0b40db94842d036d5210b40eb50842d02fa6010b40be58042d027f65ccb409f99732d027d65ccb40af99332d02bd64ccb409fd9632d027e658cb409f59632d027f654cb409f59532d027c654cb40bed8132d02f8604cb409fd9432d027e650cb409f59432d02be640cb40af59032d02f6610cb40bd58432d02fa600cb40be58032d037751947409f98e51d027d6394740cfd0e
  | 26 => 0xd50219f583540867d6595021cfd52540867e63950219f58e540867e60950219f582540873f64550219fd8d540867c63550219fd81540867c6055021cf55054086de6315021b758c54086fa6015021be580540867e6415021cf990540867e6315021d798c540865e63150219f58c540875d63150219758c540867e6215021db988540867e6115021dd984540867e6015021de980540867a60150219f580540877960150219e580540867e64d4c219f593530867e62d4c21db98b530867e61d4c21dd987530867e60d4c219f583530867d6594c21af99253086bd6494c21d7d4e530867e6494c21cf992530863e6494c219f592530873d6494c218f592530867e6094c219f582530867f6454c219f191530875f6354c219fd81530867c6054c21af99053086bd6414c21d754c53086fa6014c21be580530867e6414c21cf990530863e6414c219f590530873d6414c218f590530867e6314c21d798c530867e6214c21db988530866e6214c219f98453087766114c219d984530867e6014c21de980530867a6014c219f58053087796014c219e580530867f65d0c219f997430867d65d0c219f197430873f54d0c21cf953430873d54d0c21cf153430873f65d0c21cf997430873d65d0c21cf197430873f53d0c21cf94f430873d53d0c21cf14f430867f6590c219f996430867d6590c219f19643086bd6490c21d794e430875d5390c219fd95430867e6550c219f595430867c6550c21cfd51430873e5450c21cf551430873c5450c21d794d430875d5350c21bbd8943086ec6250c21bdd8543086f46150c21cfd95430873e6550c21cf595430873c6550c21e7d8d430873f5350c21cf94d430879e5350c21c794d430873d5350c21e754d430871d5350c21cf14d43087af6250c21eb18943087b76150c21ed185430867f6510c219f994430867d6510c219f19443086be6410c219f992520867d64948219f98e520867d6394821cfd0e520873d43948219f597420867f65908219f596420873e5490821cf55242086f66190821bd586420867f65508219fd94420867d6510821cf950420873d5410821bd98442086f561108219f59732086be64cc821af593320867f658c8219f596320875e538c821d754e320876e528c821bd98632086f5618c8219fd95320876e524c8219fd94320867d650c821af99032086bd640c821d794c320875d530c821bd98432086f5610c821be98032086f9600c8219f992510867d64944219f98e510867d6394421cfd0e510873d43944219f597410867f65904219f596410873e5490421cf55241086ee6290421bb58a410867f65504219fd94410867e65104219f594410867c6510421cf950410873d5410421bb98841086ed62104219f59731086be64cc421af593310867f658c4219f596310875e538c421d754e3108
  | 27 => 0x21bd98443486f56110d219f997424873f54d0921cf15342486f661d0921bd587424867e6590921cfd52424873c54909219f195424873f5450921cf15142486f76150921bd185424867e6510921cfd50424873c5410921eb508424867e65cc921af99332486bd64cc921cfd53324873c54cc921d7d4f324875c53cc921bd98732486f561cc9219f996324873f548c921cf15232486ee658c921db99632487af548c921eb15232486ed638c921db94e324876c538c921ebd0e32487ad438c921f9d8632486ee618c921f9186324867c654c921cfd51324873c544c921d7d4d324875c534c921bdd8532486f4614c921db195324866c654c921ebd5132487ac544c921f3d8d32487cf534c921db94d324876c534c921f314d32487af434c921eb50d32487e7614c921bb18532487e4614c921b9185324867e650c921af99032486bd640c921cfd50324873c540c921bb98832486f6610c921be98032486f9600c9219f997414873f54d0521cf15341486ee62d0521bb58b414867e6590521cfd52414873c54905219fd95414867d65505219f195414873f5450521cf15141486ef6250521bb189414867e6510521cfd50414873c5410521ed504414867e65cc521af99331486bd64cc521cfd53314873c54cc521d7d4f314875c53cc521bb98b31486ed62cc5219f996314873f548c521cf15231486f6658c521dd99631487b7548c521ed15231486f5638c521dd94e3148774538c521edd0e31487b5438c521f9d8a31486f6628c521f918a31487e6328c521f94ca314867f654c5219f595314867c654c521cfd51314873c544c521d7d4d314875c534c521bbd8931486ec624c521bd1953148774654c5219d19531487b7544c521ed15131487d7634c521f5d4d3148776534c521dd14d31487d4534c521edd0d31487b5434c521f9d8931486f4624c521f918931486e4624c521f98c931487e5324c5219f99431486be640c521af590314873f540c521cf15031486ee620c521bb58831486f6610c521be98031486f9600c521cfd53214873c54c8521edd5321487b454c8521bdd8f21486f563c8521edd0f21487b543c8521f98cb21487e532c8521cfd52214873c5488521ebd5221487ac5488521bbd8e21486ed6388521ebd0e21487ad4388521f9d4621487e63188521f94c6214873f54d4121cf153504867e64d41219f593504867e63d41219f58f504873f43d4121cf50f504876e32d4121db4cb504877631d4121dd4c750486be6494121af592504873f5494121cf152504877b5094121afd9150486bc6454121cfd51504873c5454121b7d8d50486dc6354121cfd50504873c5414121de540504867e64141219f590504867e63141219f58c504873f4314121cf50c504867e63d50219f58f540867e62d5021db98b540867e61d5021dd987540867e6
  | 28 => 0xd0f21887b543c8621af99350886bd64d4221ded42508867e64942219f592508867e63942219f58e508873f4394221cf50e508867f64542219f191508867f63542219f18d508873f4354221cf50d50887763154221dd4c5508877950142219f98f544867d63d51219f983544867d60d5121af58f544873f63d5121cf98f544873d63d51218f58f544873c63d5121cfd8b544873d62d5121cfd87544873d61d5121cfd83544873e60d5121cf583544873c60d5121cfd52544867e64951218f992544867e63951219f58e544867d6295121db58a544867d6195121dd586544867e60951219f582544873f64551219fd8d544867c63551219fd89544876f62551219fd85544877761551219fd81544867c60551219f994544873d5415121cf990544867e63151219f58c544867e60151219f58054486be6515121cf994544863e6515121af58c544873f6315121cf98c544873d63151218f58c544873c6315121cfd88544873d6215121cfd84544873d6115121cf484544873f6015121cf980544873d6015121cf180544873f54d4d21cf153534873f64d4d219f993534867d64d4d21cf193534867e60d4d219f58353486be6494d21af592534873f5494d21cf152534875f5394d219f992534873e6494d218f992534867d6494d21cf592534863d6494d219f98e534867d6294d21db58a534867d6194d21dd586534867e6094d219f58253486bf6454d21af191534873f5454d21cf15153486fb6054d21be181534867f6454d21cfd91534863f6454d219f191534873c6454d218f191534875f6354d219fd89534876f6254d219fd8553487776154d219fd81534877b6054d219ed81534867c6054d21de18153486786054d219f99453486be6414d21af590534873f5414d21cf150534875d5314d21be98053486f96014d219f990534873e6414d218f990534867d6414d21cf590534863d6414d21d798c534876d6214d21dd584534867e6014d21de980534867a6014d219f58053487796014d219e580534867f65d0d219f997434867d65d0d219f197434873f54d0d21cf953434873d54d0d21cf153434873f65d0d21af997434873e65d0d218f997434873d65d0d21af197434873c65d0d218f197434873f53d0d21cf94f434873d53d0d21cf14f434867f6590d219f996434867d6590d219f19643486bd6490d21cfd52434873c5490d21bb98a43486ed6290d21bd98643486f56190d219fd95434867e6550d219f595434867c6550d21cfd51434873e5450d21cf551434873c5450d21cfd9543486be6550d21cf995434863e6550d21cf59543486bc6550d21cf195434863c6550d21e7d8d434873f5350d21cf94d434873d5350d21cf14d434867f6510d219f994434867d6510d219f19443486be6410d21cfd50434873c5410d21bb98843486ed6210d
  | 29 => 0xc867d64943219f98e50c867d6394321cfd0e50c873d43943219fd9150c867c64543219fd8d50c867c6354321cfd0d50c873d4354321db8c950c876d3254321de54050c86fa60d5221be583548867e63d52219f58f548876d62d5221dd987548867e60d5221de983548867a60d52219f583548877960d52219e583548873f54952219f98e548867d63952219f982548867d6095221cfd91548867f63552219f18d548867f60552219f181548873d5415221cf990548867e63152219f58c548876d6215221dd984548867e60152219f580548867e64d4e219f593538876d62d4e21dd987538867e60d4e219f58353886be6494e21af592538875f5394e219f992538873e6494e218f992538867d6494e21cf592538863d6494e21dd986538867e6094e219f582538867f6454e219f191538875f6354e219fd81538867c6054e21af99053886bd6414e21d754c53886fa6014e21be580538867e6414e21cf990538863e6414e219f590538873d6414e218f590538875e6314e21db58853887766114e219f980538877a6014e219e980538867d6014e21de58053886796014e219fd97438867e65d0e219f597438867c65d0e21cfd53438873e54d0e21cf553438873c54d0e21cfd97438873e65d0e21cf597438873c65d0e21cfd4f438873e53d0e21cf54f438873c53d0e219fd96438867e6590e219f596438867c6590e21bd98643886f56190e219fd95438867e6550e219f595438867c6550e21cfd51438873e5450e21cf551438873c5450e21bbd8943886ec6250e21cfd95438873e6550e21cf595438873c6550e21e7d8d438873f5350e21cf94d438873d5350e21cf14d43887af6250e21eb189438867f6510e219f994438867d6510e219f19443886f66110e21bd584438873e54d0a21cf55342886f661d0a21bd587428873f5490a21cf152428873e5450a21cf55142886f76150a21bd185428873f5410a21cf15042886be64cca21af593328875e53cca21d754f32886f661cca21bd587328875e534ca21d754d32886f7614ca21bd18532886be640ca21af59032886f5610ca21be98032886f9600ca21cf952418873d5490621bb98a41886ed6290621cf950418873d5410621bb98841886ed6210621ed50441886be64cc621af593318875e538c621d754e31886ee628c621bb58a31886f5658c621dd5963188776538c621f594e31887d5538c621dd14e31887b7438c621ed50e31886f6628c621f998a31887e5628c621bdd953188777654c621f5d8d3188776534c621dd14d31887b7434c621ed50d31886f4624c621af99031886bd640c621d794c318875d530c621bb98831886ed620c621be98031886f9600c621bb597218876d65c8621dbd4f218876d53c8621ebd0f21887ad43c8621bd597218877565c8621bdd8f21886f563c8621ed
  | 30 => 0x7a6154031ded05500c77a4154031de505500c7784154031decc5500c77a3154031dc8c5500c7793154031dc4c5500c7783154031af990500c6bd6414031cf950500c73d5414031bb988500c6ed6214031db948500c76d5214031be980500c7795014031be98354c86f960d53219f98f54c867d63d5321db98b54c877561d53219f98354c877a60d53219e98354c867d60d5321de58354c867960d5321cfd5254c867e63953219f58e54c867e60953219f58254c873f64553219fd8d54c867c63553219fd8154c867c6055321cf55054c873e64153219f98c54c867d6315321db98854c877561153219f98054c867d60153219f99353c867d64d4f21db98b53c877561d4f219f98353c867d60d4f21af99253c86bd6494f21d7d4e53c867e6494f21cf99253c863e6494f219f59253c873d6494f218f59253c876e6294f219f98253c867d6094f219fd9153c867c6454f21d7d8d53c867f6054f219f18153c86be6414f21af59053c875d5314f21be98053c86f96014f219f99053c873e6414f218f99053c867d6414f21cf59053c863d6414f21d798c53c876e6214f21dd58453c867e6014f21de98053c867a6014f219f58053c87796014f219e58053c867f65d0f219f99743c867d65d0f219f19743c873f54d0f21cf95343c873d54d0f21cf15343c873f65d0f21cf99743c873d65d0f21cf19743c873f53d0f21cf94f43c873d53d0f21cf14f43c867f6590f219f99643c867d6590f219f19643c86ee6290f21bb58a43c867f6550f219f99543c867d6550f219f19543c873f5450f21cf95143c873d5450f21cf15143c86f76150f21bd18543c873f6550f21cf99543c873d6550f21cf19543c879f6350f21cfd4d43c873e5350f21cf54d43c873c5350f21edd8543c87b46150f219fd9443c867e6510f219f59443c867c6510f21bb98843c86ed6210f21cf95242c873d5490b21bd98642c86f56190b21cf95042c873d5410b21eb50842c86f66110b21bd58442c86be64ccb21af59332c875e538cb21d754e32c86f6618cb21bd58632c876d658cb21db94e32c87ce538cb21f354e32c876c538cb21ebd0e32c87ad438cb21bb98632c87e6618cb21f958632c86ef654cb21dbd9532c87cf634cb21db94d32c876c534cb21ebd0d32c87ad434cb21bb18532c86be640cb21af59032c875e530cb21d754c32c86f6610cb21bd58432c86fa600cb21be58032c873e54d0721cf55341c86ee62d0721bb58b41c873f5490721cf15241c873e5450721cf55141c86ef6250721bb18941c873f5410721cf15041c86be64cc721af59331c875e53cc721d754f31c86ee62cc721bb58b31c875e534c721d754d31c86ef624c721bb18931c86be640c721af59031c86ee620c721bb58831c86fa600c721be58031c86be64d4321af59350c877b50943219f9925
  | 31 => 0x90431db94a410c76d52904319fd95410c73e5450431cf551410c76e5250431db549410c67f65104319f994410c67d65104319f194410c73e5410431cf550410c6de6310431b758c410c76e5210431db548410c7b54110431af993310c6bd64cc431cf953310c73d54cc431e7d0f310c79d43cc431db94b310c76d52cc431e7993310c79d64cc431e7953310c79d54cc431f394b310c7cd52cc431cf952310c73d548c431b758e310c75e538c431db94a310c76d528c431ed952310c7b5548c431bd58e310c776538c431f594e310c7b7438c431ed50e310c7e6528c431dd54a310c7e5528c431d954a310c67f654c431cf951310c73d544c431e7d0d310c79d434c431db949310c76d524c431b7d95310c75f654c43197d95310c79e544c431e7551310c7ce524c431f3549310c6df614c431d7945310c7d6414c431f5505310c6f7654c431ddd95310c677654c431ed951310c7b5544c431bdd8d310c7d7634c431dd94d310c7d6534c431edd0d310c7d6434c431ed50d310c7d5434c431e550d310c7e6524c431dd549310c7e5524c431d9549310c6be64d4031af593500c73e54d4031cf553500c6ee62d4031bb58b500c76e52d4031db54b500c73e5494031cf552500c76e5294031db54a500c77b50940319f992500c67d6494031cfd0e500c73d43940319f98a500c67d6294031ded52500c77a5494031ee952500c73a5494031de552500c7b95494031ce552500c7785494031eed0e500c7b94394031ded4a500c77a5294031fa94a500c76a5294031de54a500c7e95294031da54a500c7785294031f6cc6500c7f23194031f64c6500c7f13194031ded92500c77a6494031de592500c7786494031de18e500c77b4394031ced0e500c77a4394031de50e500c7394394031de10e500c77b6294031de98a500c7796294031de18a500c77b4294031de90a500c7794294031de10a500c77b3294031de8ca500c7793294031de0ca500c7786194031ded06500c77a4194031de506500c7784194031decc6500c77a3194031de4c6500c73e5454031cf551500c76e5254031db549500c67f64540319f191500c73f4354031cf50d500c67f62540319f189500c7763154031dd4c5500c77b6554031ded51500c77a5454031ee951500c73a5454031de551500c7b95454031ce551500c7785454031eed0d500c7b94354031ded49500c77a5254031fa949500c76a5254031de549500c7e95254031da549500c7785254031f6cc5500c7f23154031f64c5500c7f13154031ded91500c77a6454031de591500c7786454031de98d500c77b4354031ced0d500c77a4354031de50d500c7394354031de10d500c77b6254031de989500c7796254031de189500c77b4254031de909500c7794254031de109500c77b3254031de8c9500c7793254031de0c9500c7
  | 32 => 0x19f990540c73e64150318f990540c67e6315031d798c540c67e6215031db988540c66e62150319f588540c76d62150319b588540c67e6115031dd984540c67e6015031de980540c67a60150319f580540c77960150319e580540c67e6494c31cf992530c63e6494c319f592530c73d6494c318f592530c67d65d0c31cfd53430c73e54d0c31cf553430c73c54d0c31af597430c73d65d0c318f597430c73e53d0c319fd96430c67d6590c31af592430c73e5490c31cf552430c6f66190c31bd586430c67f6550c31cfd51430c73e5450c31cf551430c73c5450c31afd95430c73f6550c318fd95430c79f6350c31cf94d430c67f6510c319f594430c6be6410c31cf950430c73d5410c31bd984430c6f56110c31af993520c6bd64d4831cf953520c73d54d4831be983520c6f960d4831cf952520c73d5494831dbd4a520c67e64948319f592520c73f4394831cf50e520c67e60948319f582520c76f5494831db952520c7ae5494831cb952520c76d5494831eb552520c72d5494831db152520c7af4394831eb50e520c76f6494831db992520c76d6494831db192520c76c6394831dbd0e520c72f4394831db90e520c76d4394831cb50e520c76c4394831db986520c76c6194831dbd82520c76e6094831db582520c76c6094831cf951520c73d54548319fd91520c67c6454831cfd0d520c73d43548319fd81520c67c6054831dbd95520c76f5454831db951520c7ae5454831cb951520c76d5454831eb551520c72d5454831db151520c7af4354831eb50d520c76f6454831db991520c76d6454831db191520c76e6354831dbd0d520c72f4354831db90d520c76d4354831cb50d520c76c4354831db985520c76c6154831db0c5520c76f6054831db981520c76d6054831db181520c6be6414831af590520c73e5414831cf550520c6ee6214831db548520c6fa6014831be580520c67f65d08319f997420c67d65d0831cf953420c73d54d0831db94b420c76d52d08319fd96420c67e65908319f596420c73e5490831cf552420c76e5290831db54a420c67f65508319f595420c67c6550831cf951420c73d5450831db949420c76d5250831bdd85420c6f461508319fd94420c67e65108319f594420c73e5410831cf550420c76e5210831db548420c6be64cc831af593320c73e54cc831cf553320c76e52cc831db54b320c6f661cc831bd587320c67d658c831cf952320c73d548c831db54a320c67f654c831cf951320c73d544c831db949320c6be640c831af590320c73e540c831cf550320c76e520c831db548320c6f6610c831bd584320c6fa600c831be580320c67e64944319f592510c73f4394431cf50e510c67d65d0431cf953410c73d54d0431db94b410c76d52d04319fd96410c67d6590431cf952410c73d5490431b798e410c6dd63
  | 33 => 0x85544c67f6055131ded81544c67b60551319f181544c77860551319e181544c67e6515131cf550544c73e64151319f988544c67d62151319f980544c67d60151319f997434c73f54d0d31cf153434c6f661d0d31bd587434c73f65d0d31cf997434c73d65d0d31cf197434c7b661d0d31ed587434c67e6590d31af592434c67c6550d31cfd51434c73c5450d31bdd85434c6f46150d31cfd95434c73e6550d31cf595434c73c6550d31e7d8d434c7b76150d31ed185434c67e6510d31af990434c67e64d49319f593524c73f43d4931cf50f524c67e60d49319f583524c76f5294931afd91524c6bc6454931bed81524c6f86054931db548524c67e64149319f590524c73f4314931cf50c524c77561149319f980524c67d60149319f997424c67d65d09319f197424c76f52d0931db14b424c67e65909319f596424c67c6590931cfd52424c73c5490931bd986424c6f561909319fd95424c67e65509319f195424c67e65109319f594424c67c6510931cfd50424c73c5410931b798c424c6dd6310931dbd48424c76c5210931bd984424c6f561109319f997324c6be64cc931af593324c79d43cc931dbd4a324c76c528c931bd986324c6f5618c931e750d324c76f524c931db149324c6f7614c931bd185324c67e650c931af990324c6bd640c931bd984324c6fa600c931be580324c67e65d0531cfd53414c73c54d0531b798f414c6dd63d05319f996414c73e5490531cf552414c67f65505319f595414c67c6550531cfd51414c73c5450531b7d8d414c6dc63505319f994414c73e5410531cf550414c6be64cc531af593314c7b664cc531ed593314c7b743cc531ed50f314c6f562cc531bd583314c79f438c531e750e314c7d7518c5319f993504c67d64d4131cfd0f504c73d43d41319f98b504c67d62d4131ded42504c6bf6454131af191504c6ef6254131bb189504c77950141319f990504c67d6414131cfd0c504c73d43141319f988504c67d6214131bb98b540c6ed62d5031be983540c6f960d50319f98f540c75e63d50319f98b540c76e62d50319b98b540c67d62d5031db58b540c66d62d50319f987540c77661d50319f983540c77a60d50319e983540c67d60d5031de583540c67960d50319f596540c73f54950319f98a540c67d62950319f982540c67d60950318f596540c73e6395031cf18e540c73f6295031cf98a540c73d6295031cf18a540c73e6195031cf186540c73f6095031cf982540c73d6095031cf182540c73f64550319fd89540c67c62550319fd81540c67c6055031cfd95540c73e6355031cf18d540c73f6255031cf989540c73d6255031cf189540c73e6155031cf185540c73c3155031cfd81540c73e6055031cf581540c73c6055031af990540c73d5415031bb988540c6ed6215031be980540c6f9601503
  | 34 => 0xcc6f9600cb31cf95341cc73d54d0731b798f41cc6dd63d0731cf95241cc73d5490731cf95141cc73d5450731b7d8d41cc6dc6350731cf95041cc73d5410731ed50441cc6be64d4331af59350cc73e54d4331cf55350cc73e5494331cf55250cc77b50943319f99250cc67d6494331cfd0e50cc73d43943319f98a50cc67d6294331cf95150cc73d54543319fd9150cc67c6454331cfd0d50cc73d43543319fd8950cc67c6254331af99050cc6bd6414331cf95050cc73d5414331bb98850cc6ed6214331de54050cc75d63d52319f98b548c67d62d5231dd987548c67e60d52319f583548c73f54952319f98a548c67d62952319f982548c67d6095231cfd91548c67f62552319f189548c67f60552319f181548c73d5415231cf990548c75d63152319f988548c67d6215231dd984548c67e60152319f580548c73e54d0e31cf553438c6f661d0e31bd587438c73e65d0e31cf597438c7b661d0e31ed587438c73e5450e31cf551438c6f76150e31bd185438c73f6550e31cf195438c79f6350e31edd85438c7b46150e31dbd4a528c67e6494a319f592528c73f4394a31cf50e528c7766194a319f982528c67d6094a31afd91528c6bc6454a319fd91528c73f6454a318fd91528c67c6454a31cf191528c63c6454a31cfd0d528c73d4354a319fd81528c67c6054a31db548528c67f65d0a319f997428c67d65d0a319fd96428c67e6590a319f596428c73f5490a31cf152428c6f66190a31bd586428c67f6550a319f595428c67c6550a319fd94428c67e6510a319f594428c73f5410a31cf150428c6f66110a31bd584428c6be64cca31af593328c76e528ca31db54a328c6f6618ca31bd586328c76e524ca31db549328c6f7614ca31bd185328c6be640ca31af590328c6f5610ca31be980328c6f9600ca31cfd53418c73c54d0631cf952418c73d5490631b798e418c6dd6390631cfd51418c73c5450631cf950418c73d5410631b798c418c6dd6310631af993318c6bd64cc631e7d0f318c79d43cc631b7597318c75d65cc631e7993318c79d64cc631bd597318c77565cc631ed993318c7b564cc631edd0f318c7b543cc631bd58b318c6f560cc631ded42508c67e64942319f592508c73f4394231cf50e508c67e62942319f58a508c6bf6454231af191508c67f6454231cfd91508c63f64542319f191508c73c64542318f191508c73f4354231cf50d508c67f62542319f189508c77950142319f98b544c67d62d51319f983544c67d60d5131cfd52544c67e64951319f58e544c75d63951319f98a544c67d62951319f586544c77561951319f982544c67d6095131bbd89544c6ec6255131bed81544c6f86055131cfd91544c67f6355131d7d8d544c67f6255131dbd89544c66f62551319f189544c76c62551319b189544c67f6155131ddd
  | 35 => 0xe524c841db54932106f7614c841bd185321067f650c8419f994321067d650c841af99032106bd640c841bd98432106f5610c841be98032106f9600c841cfd0e511073d4394441cf90a511073c4294441af58f411073d53d0441af98b41106be60d0441af592411073e5490441bd59241107765490441ed95241107b74390441ed50e41107b64290441ed10a411067f6550441afd95411073f65504418fd9541106bf6350441cf54d41106bc6250441afd85411073e5150441af18141106f76550441ddd9541106776550441bdd9141107b76450441dd95141107b65450441ed90d41107b44350441edd0941107b54250441ded42501067e63940419f58e501073f4394041cf50e501067e62940419f58a501073e4294041cf10a501067f63540419f18d501073f4354041cf50d501067f62540419f18950106de6314041b758c50106ee6214041bb58850107795014041d798f54cc67e62d53319f58b54cc77561d53319f98354cc67d60d5331cfd5254cc67e62953319f58a54cc67e60953319f58254cc73e6395331cf18e54cc73f6295331cf98a54cc73d6295331cf18a54cc73f6195331cf58654cc73f6095331cf98254cc73d6095331cf18254cc73f64553319fd8954cc67c62553319fd8154cc67c6055331cfd9554cc73e6355331cf18d54cc73f6255331cf98954cc73d6255331cf18954cc73f6155331cf58554cc73f6055331cf98154cc73d6055331cf18154cc73d5415331cf99054cc75e63153319f98854cc67d6215331dd58454cc67e60153319f58054cc73f54d0f31cf95343cc73d54d0f31cf15343cc6bd65d0f31cf59743cc73e5490f31cf55243cc6f66190f31bd58643cc73f5450f31cf95143cc73d5450f31cf15143cc6bf6550f31cfd9543cc79f6350f31cf95043cc73d5410f31bd98443cc6f56110f31af99352cc6bd64d4b31cf95352cc73d54d4b31cf95252cc73d5494b31dbd4a52cc67e6494b319f59252cc73f4394b31cf50e52cc67e6094b319f58252cc73e5454b31cf55152cc67f6454b319f19152cc73f4354b31cf50d52cc67f6054b319f18152cc6be6414b31af59052cc73e5414b31cf55052cc76d5214b31be98052cc6f96014b319fd9742cc67e65d0b319f59742cc73e54d0b31cf55342cc67f6590b319f99642cc67d6590b31cf95242cc73d5490b319fd9542cc67d6550b319f19542cc73e5450b31cf55142cc6f76150b31bd18542cc67f6510b319f99442cc67d6510b31cf95042cc73d5410b31b798c42cc6dd6310b31af99332cc6bd64ccb31cf95332cc73d54ccb31e750f32cc76e52ccb31db54b32cc6f661ccb31bd58732cc73e548cb31cf55232cc73e544cb31cf55132cc79d434cb31af99032cc6bd640cb31cf95032cc73d540cb31db94832cc76d520cb31bd98432cc6f5610cb31be98032
  | 36 => 0xd41cf997435073c53d0d41af98743506bd6490d41d7d4e435075c5390d41bd98643506f56190d41d7d4d435075c5350d41bdd8543506f46150d41e7d8d435073f5350d41e7d4d435071f5350d41cf14d435079c5350d41edd8543506bc6150d41ed18543506b46150d419f99443506be6410d419f98f525067d63d4941cfd0f525073d43d49419f983525067d60d4941dbd4a52506fa6094941be582525076d52149419f98c525067d6314941cfd0c525073d43149419f980525067d60149419f997425076f5290941db14a42506f66190941bd586425076f5250941db14942506f76150941bd185425067e6510941eb508425067e65cc9419f597325067c65cc941af99332506bd64cc941dbd4b325076c52cc9419f996325067d658c9419f196325067f654c9419f995325067c654c9419f994325067d650c9419f19432506be640c941af590325076f520c941db14832506f6610c941bd58432506fa600c941be58032507b743d0541ed50f41506bd6390541cfd4e415073c5290541edd46415067e63d41419f58f505073f43d4141cf50f505067e62d41419f58b50506ee6294141bb58a505077b5094141de540505067e63141419f58c505073f4314141cf50c505067e62141419f588505073e4114141d7d4e531067e6294c419f58a531067e6094c419f582531073e6454c419fd89531067c6254c419fd81531067c6054c41d754c53106ee6214c41bb58853106fa6014c41be580531073e54d0c41d794f431075d53d0c41bd98743106f561d0c41cf94f431079e53d0c41cf54f431079d53d0c41c754f43106be62d0c41ed98743106bd61d0c41ed58743106b561d0c41af983431067d6590c41af592431067f6550c41cf95143106bf6550c41cfd95431079f6350c41cf94d43106bc6250c41afd8543106bc6050c41af990431075e5310c41d754c43106f66110c41bd584431076f52948419f98e521067d6394841cfd0e521073d43948419f982521067d60948419fd8d521067c6354841cfd0d521073d43548419fd81521067c6054841b798c52106dd6314841db54852106fa6014841be580521076e52d0841db54b42106f661d0841bd587421067d6590841af596421073d6590841af58e421073d5390841af98a421073d5290841af58642106be60908419fd95421076e5210841db54842106f66110841bd58442106bd6310841cf54c42106be6210841eb98842107ae5210841cf54842107ad5210841cb54842107b66110841af58442107b56110841ad58442106be60108419fd97321067e65cc8419f59732106be64cc841af593321075e53cc841d754f321067f658c8419f996321067d658c841afd9232106bc648c841db94a321076d528c8419fd95321067d654c8419f19532106bf644c841af191321075e534c841d754d321076
  | 37 => 0xaf18543d075e5310f41d754c43d06f66110f41bd58443d076f5294b419f98e52d067d6394b41cfd0e52d073d4394b419f98252d067d6094b419fd8d52d067c6354b41cfd0d52d073d4354b419fd8152d067c6054b41db54852d076e52d0b41db54b42d06f661d0b41bd58742d076e5210b41db54842d07ad4210b41bd98442d06f56110b419fd9732d067e65ccb419f59732d06be64ccb41af59332d067f658cb419f99632d067d658cb419fd9532d067d654cb419f19532d06f7614cb41bd18532d067f650cb419f99432d067d650cb41af99032d06bd640cb41bd98432d06f5610cb41be98032d06f9600cb41ded4250d067e63943419f58e50d073f4394341cf50e50d067e62943419f58a50d067f63543419f18d50d073f4354341cf50d50d067f62543419f18950d07795014341d7d4e539067e6294e419f58a539067e6094e419f582539073d6454e419fd89539067c6254e419fd81539067c6054e41d754c53906ee6214e41bb58853906fa6014e41be58053906bd65d0e41cf597439073e53d0e41af98b43906bd61d0e41af983439075e5390e41d754e43906f66190e41bd586439075e5350e41d754d43906f76150e41bd185439079f6350e41cf94d439079e5350e41cf54d439079d5350e41c754d43906bc6250e41afd8543907b76150e41ed18543906bc6050e41be98352906f960d4a41dbd4a529067e6394a419f58e529073f4394a41cf50e529067e6094a419f582529067f6354a419f18d529073f4354a41cf50d529067f6054a419f181529076d5214a41db94a429076d5290a41bd98642906f56190a41af58e429073d5390a41eb94a429073d5290a41eb54a42907b66190a41af58642907b56190a41af982429076e5250a41db54942906f76150a41bd18542906bd6510a41cf59442906bd6310a41cf54c42907ae6210a41cf54842906bd6110a41af980429067f65cca419f997329067d65cca41af99332906bd64cca419fd96329067e658ca419f59632906bf648ca41af192329076e528ca41db54a329067f654ca419f595329067c654ca41afd9132906bc644ca41db949329076d524ca419fd94329067e650ca419f59432906be640ca41af59032906f6610ca41bd58432906fa600ca41be58032906bd65d0641cf59741906bd63d0641cf54f41906be62d0641af98341906f565d0641dd59741906ee62d4241bb58b509077b50942419f98e509067d6394241cfd0e509073d43942419f98a509067d6294241cf90a509073c42942419fd8d509067c6354241cfd0d509073d43542419fd89509067c6254241de540509073f64d4d419f98b535067d62d4d419f983535067d60d4d41d7d4e53506ef6254d41bb18953506fb6054d41be181535075d5314d419f988535067d6214d419f980535067d6014d419f99743506be65d
  | 38 => 0xd510cb6e3254432db4c9510ca7f60544329f181510cb776554432ddd51510cb765454432ed951510cb365454432dd551510cbb55454432cd551510cb745454432edd0d510cbb54354432f5cc9510cbe63254432f54c9510cbe53254432ddd91510cb766454432dd591510cb746454432dd98d510cb774354432cdd0d510cb764354432dd50d510cb354354432dd10d510cb766254432ddd09510cb764254432dd509510cb744254432ddcc9510cb763254432d98c9510cb753254432d94c9510cb743254432ddd81510cb766054432dd581510cb746054432af990510cabd6414432cf950510cb3d5414432bd984510cb755114432be980510caf96014432af993500cabd64d4032cf953500cb3d54d4032bd987500caf561d4032dd947500cb7551d4032cf952500cb3d5494032dd946500cb755194032ded42500ca7e64940329f592500cb3f4394032cf50e500ca7e61940329f586500cb7b5494032de952500cbba5494032ce952500cb795494032ee552500cb395494032de152500cbbb4394032ee50e500cbdb3294032fa8ca500cbd93294032fa4ca500cb7b5194032de946500cbf25194032dc946500cb795194032fc546500cb715194032de146500cb7b6494032de992500cb796494032de192500cb786394032ded0e500cb3b4394032de90e500cb794394032ce50e500cb784394032de18a500cb7b4294032de90a500cb794294032de10a500cb7b3294032de8ca500cb793294032ded86500cb7a6194032de586500cb786194032cf951500cb3d5454032dd945500cb7551540329fd91500ca7c6454032cfd0d500cb3d4354032db8c9500cb6d32540329fd85500ca7c6154032ded95500cb7b5454032de951500cbba5454032ce951500cb795454032ee551500cb395454032de151500cbbb4354032ee50d500cbdb3254032fa8c9500cbd93254032fa4c9500cb7b5154032de945500cbf25154032dc945500cb795154032fc545500cb715154032de145500cb7b6454032de991500cb796454032de191500cb7a6354032ded0d500cb3b4354032de90d500cb794354032ce50d500cb784354032de989500cb7b4254032de909500cb794254032de109500cb7b3254032de8c9500cb6a3254032de4c9500cb693254032de0c9500cb7b6154032de985500cb796154032de185500cabe6414032af590500cb3e5414032cf550500caf66114032bd584500cb765114032dd544500cafa6014032de540500cb5f5394f419f98a53d067d6294f419f98253d067d6094f41cf99153d067f6254f419f18953d067f6054f419f18153d075d5314f41d794f43d075d53d0f41bd98743d06f561d0f41cf94f43d079e53d0f41cf54f43d079d53d0f41c754f43d06be61d0f41ed98743d07b561d0f41afd9543d073f6550f41e7d8d43d073e5350f41
  | 39 => 0xcb3c6095032cfd91540ca7f61550329f185540ca7f60550329f181540cb3f6555032cf98d540cb3c6355032cf989540cb3c6255032cf0c9540cb3f6155032cf985540cb3d6155032cf185540cb3f6055032cf981540cb3d6055032cf181540cabe6415032cf550540caf66115032bd584540cafa6015032be580540ca7e6415032cf990540ca3e64150329f98c540cb5e63150329f988540cb6e62150329f984540cb7661150329d984540ca7d6115032dd584540ca7561150329f980540cb7a60150329e980540ca7d6015032de580540ca7960150329f992530cb3e6494c328f992530ca7d6494c32cf592530ca3d6494c329f597430cb3f54d0c32cf953430cb3d54d0c32cf153430cabd65d0c32cf597430ca3d65d0c32cf94f430ca7f6590c329f596430cabd6490c32cf952430cb3d5490c32bb98a430caed6290c329fd95430cb3f5450c32cf951430cb3d5450c32cf151430cabf6550c32cfd95430ca3f6550c32e7d8d430cb3e5350c329fd94430ca7d6510c32af990430cb3e5410c32cf550430caee6210c32bb588430ca7e64948329f592520cb3f4394832cf50e520ca7d65d0832cf953420cb3d54d08329fd96420ca7d6590832cf952420cb3d5490832b798e420cadd63908329fd95420cb3e5450832cf551420ca7f65108329f994420ca7d65108329f194420cb3e5410832cf550420cade6310832b758c420cbad4210832af993320cabd64cc832cf953320cb3d54cc832e7d0f320cb9d43cc832e7993320cb9d64cc832e7953320cb9d54cc832cf952320cb3d548c832b758e320cb5e538c832eb952320cbad548c832bb58e320cb6e538c832f394e320cbaf438c832eb50e320ca7f654c832cf951320cb3d544c832e7d0d320cb9d434c832b7d95320cb5f654c83297d95320cb9e544c832e7551320cadf624c832d7949320cbce424c832f3509320caef654c832dbd95320ca6f654c832eb951320cbad544c832bbd8d320cbcf634c832db94d320cbce534c832ebd0d320cbce434c832eb50d320cbcd434c832e350d320cabe64d4432af593510cb3e54d4432cf553510cafa60d4432be583510cb3e5494432cf552510cb7751944329f992510ca7d6494432cfd0e510cb3d43944329f982510ca7d6094432ddd52510cb765494432ed952510cb365494432dd552510cbb55494432cd552510cb745494432edd0e510cbb54394432f5cca510cbe63294432f54ca510cbe53294432ddd92510cb766494432dd592510cb746494432dd18e510cb774394432cdd0e510cb764394432dd50e510cb354394432dd10e510cb746294432ddd0a510cb764294432dd50a510cb744294432ddcca510cb763294432dd4ca510cb776094432dd982510cb756094432dd182510cb3e5454432cf551510ca7f64544329f191510cb3f4354432cf50
  | 40 => 0x43cca32eb50f328caed61cca32bb583328cb7751946329f992518ca7d6494632cfd0e518cb3d43946329f982518ca7d6094632afd91518cabc64546329fd91518cb3f64546328fd91518ca7c6454632cf191518ca3c6454632cfd0d518cb3d43546329fd81518ca7c6054632dd544518cb7b50942329f992508ca7d6494232cfd0e508cb3d43942329f986508ca7d6194232afd91508cabc64542329fd91508cb3f64542328fd91508ca7c6454232cf191508ca3c6454232cfd0d508cb3d43542329fd85508ca7c6154232de540508ca7e61d51329f587544ca7e60d51329f583544cb3f54951329f992544ca7d6395132d758e544ca7d6295132db58a544ca7e61951329f586544ca7e60951329f582544caf76155132bd185544cafb6055132be181544cb3f64551329fd8d544cb5f63551329fd89544cb6f62551329fd85544cb7761551329dd85544ca7c6155132dd185544ca7461551329fd81544cb7b60551329ed81544ca7c6055132de181544ca7860551329f994544cb3d5415132cf990544ca7e61151329f584544ca7e60151329f580544ca7e65d0d32cfd53434cb3c54d0d32bb98b434caed62d0d32cfd97434cb3e65d0d32cf597434cb3c65d0d32eb98b434cbad62d0d329f996434cabd6490d329f195434cb3f5450d32cf151434caef6250d32bb189434cb3f6550d32cf995434cb3d6550d32cf195434cb9f6350d32ebd89434cbac6250d329f994434cabe6410d329f997424cb3f54d0932cf153424cade63d0932b758f424ca7e6590932cf952424cb3d54909329fd95424ca7d65509329f195424cb3f5450932cf151424cadf6350932b718d424ca7e6510932cf950424cb3d5410932af993324cabd64cc932eb993324cbad64cc932ebd0f324cbad43cc932bb587324caed60cc932e7d0e324cb9d438c932f3d4a324ca7e64d45329f593514cb3f43d4532cf50f514ca7e60d45329f583514cb775194532afd91514cabc6454532bed81514caf86054532dd544514ca7e64145329f590514cb3f4314532cf50c514ca7e60145329f580514ca7e64d41329f593504cb3f43d4132cf50f504ca7e61d41329f587504cb7b5094132afd91504cabc6454132bdd85504caf46154132de540504ca7e64141329f590504cb3f4314132cf50c504ca7e61141329f584504caf661d5032bd587540cafa60d5032be583540ca7e63d5032d798f540ca7e62d5032db98b540ca7e61d5032dd987540ca7661d50329f587540cb7561d50329d587540ca7e60d5032de983540ca7a60d50329f583540cb7960d50329e583540ca7d6595032cfd52540ca7e61950329f586540ca7e60950329f582540ca3d6595032cf98e540cb3c6395032cf98a540cb3c6295032cfd86540cb3e6195032cf586540cb3c6195032cfd82540cb3e6095032cf582540
  | 41 => 0x429fd8d5010a7c6354042cfd0d5010b3d43540429fd855010a7c6154042b798c5010add6314042bd9845010af56114042de5405010b5e63d5332db58b54cca7e61d53329f58754cca7e60d53329f58354ccb3f54953329f98654cca7d61953329f98254cca7d6095332cf98e54ccb3c6395332cfd8a54ccb3d6295332cfd8654ccb3e6195332cf58654ccb3c6195332cfd8254ccb3e6095332cf58254ccb3c6095332cfd9154cca7f61553329f18554cca7f60553329f18154ccb3f6555332cf98d54ccb3c6355332cfd8954ccb3d6255332cfd8554ccb3e6155332cf58554ccb3c6155332cfd8154ccb3e6055332cf58154ccb3c6055332cf55054ccb3e6415332d798c54ccb6d62153329f98454cca7d61153329f98054cca7d6015332cfd5343ccb3e54d0f32cf55343ccb3c54d0f32af59743ccb3d65d0f32cf95243ccb3d5490f32bb98a43ccaed6290f32cfd5143ccb3e5450f32cf55143ccb3c5450f32afd9543ccb3f6550f32e7d8d43ccb3e5410f32cf55043ccaee6210f32bb58843ccb3e54d0b32cf55342ccade63d0b32b758f42ccb3e5490b32cf55242ccb3e5450b32cf55142ccadf6350b32b718d42ccb3e5410b32cf55042ccbad4210b32af99351ccabd64d4732cf95351ccb3d54d4732cf95251ccb3d5494732ddd4651cca7e64947329f59251ccb3f4394732cf50e51cca7e60947329f58251ccb3e5454732cf55151cca7f64547329f19151ccb3f4354732cf50d51cca7f60547329f18151ccabe6414732af59051ccb3e5414732cf55051ccb755114732be98051ccaf96014732af99350ccabd64d4332cf95350ccb3d54d4332cf95250ccb3d5494332ded4250cca7e64943329f59250ccb3f4394332cf50e50cca7e61943329f58650ccb3e5454332cf55150cca7f64543329f19150ccb3f4354332cf50d50cca7f61543329f18550ccabe6414332af59050ccb3e5414332cf55050ccaf66114332bd58450ccb795014332d758f548cb6e62d52329f987548ca7d61d52329f983548ca7d60d5232cfd52548ca7e61952329f586548ca7e60952329f582548cb3f64552329fd85548ca7c61552329fd81548ca7c6055232cf550548cb3e6415232d758c548cb6e62152329f984548ca7d61152329f980548ca7d6015232cf953438cb3d54d0e32bb98b438caed62d0e32cf997438cb3d65d0e32eb98b438cbad62d0e32cf951438cb3d5450e32bbd89438caec6250e32cfd95438cb3c6550e32e7d8d438cbaf6250e32eb189438cb3f54d0a32cf153428cb3e5490a32cf552428cade6390a32b758e428cb3f5450a32cf151428cb3e5410a32cf550428cade6310a32b758c428cabe64cca32af593328cb9f43cca32e750f328cadd65cca32d7597328cb9e64cca32e7593328caed65cca32db597328cbae64cca32eb593328cbaf
  | 42 => 0xe9835190af960d4642ddd465190a7e63946429f58e5190b3f4394642cf50e5190a7e60946429f5825190a7f63546429f18d5190b3f4354642cf50d5190a7f60546429f1815190b755114642bd9875090af561d4242ded425090a7e63942429f58e5090b3f4394242cf50e5090a7e61942429f5865090a7f63542429f18d5090b3f4354242cf50d5090a7f61542429f1855090b795014242cfd935350a7e61d4d429f5875350a7e60d4d429f5835350b5f5394d42bdd855350af46154d42bed815350af86054d42d754c5350a7e6114d429f5845350a7e6014d429f5805350a7e65d0d42af9974350b3e65d0d42cf14f4350abe62d0d42af5924350b5f5390d42d714e4350aee6290d42bb58a4350b5f5350d42d714d4350aef6250d42bb1894350b9f6350d42cfd4d4350b9f5350d42c7d4d4350b3c5350d42e714d4350baf6250d42af1894350bac6250d42ab1894350a7e6510d42af9904350baf43d0942eb50f4250abd6390942cfd4e4250baf52909429f98f5150a7d63d4542cfd0f5150b3d43d45429f9835150a7d60d4542ddd465150afa6094542be5825150b7551145429f98c5150a7d6314542cfd0c5150b3d4314542cf9085150a7e60145429f5805150a7e63d41429f58f5050b3f43d4142cf50f5050a7e61d41429f5875050af66194142bd5865050b7b5094142de5405050a7e63141429f58c5050b3f4314142cf50c5050b3e42141429f9845050a7d6114142d7d4e5310a7e6194c429f5865310a7e6094c429f5825310b3e6454c429fd855310a7c6154c429fd815310a7c6054c42d754c5310af66114c42bd5845310afa6014c42be5805310b3e54d0c42d794f4310b5d53d0c42bb98b4310aed62d0c42cf94f4310b9e53d0c42cf54f4310b9d53d0c42c754f4310bae62d0c42af58b4310bad62d0c42ab58b4310abe61d0c42af9834310a7d6590c42af5924310a7f6550c42cf9514310abf6550c42cfd954310b9f6350c42cf94d4310abf6250c42af1854310abc6050c42af9904310b5e5310c42d754c4310aee6210c42bb5884310b3f4394842cf50e5210abd63d0842cf54f4210abe61d0842af9834210abd6490842cf9524210aed6490842db9524210bae5490842ebd0e4210bad43908429fd954210abf6550842cfd954210a3f6550842afd8d4210b3d5350842afd894210b3e5250842af1854210abc6050842bbd954210b6f65508429bd954210aef6450842ebd914210b6e5450842eb9514210bae4350842eb10d4210b7751944429f98e5110a7d6394442cfd0e5110b3d43944429f9825110a7d60944429fd8d5110a7c6354442cfd0d5110b3d43544429fd815110a7c6054442b798c5110add6314442dd5445110afa6014442be5805110b7b50940429f98e5010a7d6394042cfd0e5010b3d43940429f9865010a7d6194
  | 43 => 0x5050ebc6254143eb1895050eac6254143afd855050fb76154143add855050ebc6154143ed1855050eb46154143eed415050f3e5054143af9945050f3f5314143e7d4c5050ebe6214143af5885050f3e5214143cf1485050ebe6114143af5845050f3e5114143cf1445050f3f5014143ee9405050f3d5014143ee5405050f395014143cf98a5410f3d6295043cf9865410f3d6195043cf9825410f3d6095043af5924310f3e5490c43b75924310f5e5490c43e79524310e7f6550c43cf9514310ebf6550c43cfd954310e3f6550c43afd8d4310f3e5350c43b7d954310f5f6550c4397d954310edf6450c43e7d914310f5e5450c43e79514310f1e5450c43dbd4a5210f3f4394843cf50e5210e7e61948439f5865210e7e60948439f5825210f3f4354843cf50d5210e7f61548439f1855210e7f60548439f1815210f6d5214843bd9845210ef56114843be9805210ef96014843ddd465110f3f4394443cf50e5110e7e62944439f58a5110e7e60944439f5825110f3f4354443cf50d5110e7f62544439f1895110e7f60544439f1815110eee6214443bb5885110f755114443be9805110ef96014443ded425010f3f4394043cf50e5010e7e62940439f58a5010e7e61940439f5865010f3f4354043cf50d5010e7f62540439f1895010e7f61540439f1855010eee6214043bb5885010ef66114043bd5845010f795014043d7d4e53d0a7e6194f429f58653d0a7e6094f429f58253d0b3e6454f429fd8553d0a7c6154f429fd8153d0a7c6054f42d754c53d0b5e53d0f42d754f43d0aee62d0f42bb58b43d0b3e53d0f42e794f43d0b3d53d0f42e754f43d0b1d53d0f42af98b43d0bae62d0f42eb58b43d0abf6550f42cfd9543d0b9f6350f42cf94d43d0abc6250f42d794c43d0b5d5310f42bb98843d0aed6210f42ddd4651d0a7e63947429f58e51d0b3f4394742cf50e51d0a7e60947429f58251d0a7f63547429f18d51d0b3f4354742cf50d51d0a7f60547429f18151d0b755114742ded4250d0a7e63943429f58e50d0b3f4394342cf50e50d0a7e61943429f58650d0a7f63543429f18d50d0b3f4354342cf50d50d0a7f61543429f18550d0b795014342d7d4e5390a7e6194e429f5865390a7e6094e429f5825390b3d6454e429fd855390a7c6154e429fd815390a7c6054e42d754c5390af66114e42bd5845390afa6014e42be5805390abd65d0e42cf5974390b3e53d0e42af58b4390abe61d0e42af9834390b5e5390e42d754e4390aee6290e42bb58a4390b5e5350e42d754d4390aef6250e42bb1894390b9f6350e42cf94d4390b9e5350e42cf54d4390b9d5350e42c754d4390abf6250e42ebd894390bac6250e42af1854390abc6050e42af5974290b3d65d0a42af58f4290b3d53d0a42af9874290abe60d0a42bb5974290b6d65d0a42b
  | 44 => 0xef56114a43be9805290ef96014a43ddd465190f3f43946439f98a5190e7d62946439f9825190e7d6094643cfd0d5190e7f62546439f1895190e7f60546439f1815190eee6214643bb5885190f755114643be9805190ef96014643ded425090f3f43942439f98a5090e7d62942439f9865090e7d6194243cfd0d5090e7f62542439f1895090e7f61542439f1855090eee6214243bb5885090ef66114243bd5845090f795014243e7d4e4350ebe6290d43af58a4350ebe6190d43af5864350ebe6090d43af5824350e7e61d49439f5875250e7e60d49439f5835250f6f5294943bdd855250ef46154943bed815250ef86054943db5485250e7e61149439f5845250e7e60149439f5805250e7e62d45439f58b5150e7e60d45439f5835150f775194543bbd895150eec6254543bed815150ef86054543dd5445150e7e62145439f5885150e7e60145439f5805150e7e62d41439f58b5050e7e61d41439f5875050f7b5094143bbd895050eec6254143bdd855050ef46154143de5405050e7e62141439f5885050e7e61141439f5845050ebe62d4d43af58b5350ebe61d4d43af5875350ebe60d4d43af5835350f9f62d4d43e798b5350f9d62d4d43e718b5350f9f61d4d43e79875350f9d61d4d43e71875350f9f60d4d43e79835350f9d60d4d43e71835350f3f53d4943e7d4f5250ebe61d4943af5875250ebe60d4943af5835250f9d6394943e7d4e5250ebe6294943cfd4a5250faf5294943af9865250ebd6194943af9825250ebd6094943e7d8d5250f9f5354943ebd495250f3e5254943afd855250fb76154943add855250ebc6154943ed1855250eb46154943afd815250fbb6054943aed815250ebc6054943ee1815250eb86054943af9945250f3f5314943e7d4c5250f3f5214943eb9485250f3d5214943eb5485250f2d5214943af9845250ebd6114943af9805250ebd6014943cfd4f5150f9f53d4543af98b5150ebd62d4543af9835150ebd60d4543e758e5150f9f5394543af98a5150ebd6294543cf94a5150f3c5294543af9865150f3f5194543edd465150ebe6094543af5825150f9f6354543e7d4d5150ebf6254543ebd895150eaf6254543af1895150fac6254543ab1895150fb75154543cf9455150ebf6054543eed815150ebb6054543af1815150fb86054543ae1815150ebe6514543cfd4c5150f9f5314543af9885150ebd6214543cf9485150f3c5214543cfd445150fb65114543cf5445150fb55114543cd5445150ebe6014543af5805150f3f53d4143e7d4f5050ebe62d4143af58b5050ebe61d4143af5875050f9d6394143e7d4e5050ebe6294143af58a5050f3e5294143cf14a5050ebe6194143af5865050f3e5194143cf1465050ebe6094143cfd425050fbb5094143e7d8d5050f9f5354143afd895050faf6254143abd89
  | 45 => 0xb00240000028009000c010001800a000800100140000004002000000100000020000007000c002003800400040010010006000c002006c00a0010006000800200000010008003000800900040010000001000000300000010000004000800400000040000002000000800040070008000000800500000070018002000400100080000008006000000100080000000000000c001001000300040040000006002000d000800600000010004004000c0050010001000400b000c001005c0000004000000c0010028001000000000000000004000000000400000000010000002c001001400000080020000005000400f000c0000000002000400600000020004006000400100000070000000000000500000020000002001400500040020000001000000000140000004003000c00100040060010001000000100080080010007003c00b0008005000400500040020000000001000300040010000007000000300100090038001000f6f5294b439f98652d0e7d6194b439f98252d0e7d6094b439fd8552d0e7c6154b439fd8152d0e7c6054b43db54852d0f7751947439f98a51d0e7d62947439f98251d0e7d60947439fd8951d0e7c62547439fd8151d0e7c6054743dd54451d0f7b50943439f98a50d0e7d62943439f98650d0e7d61943439fd8950d0e7c62543439fd8550d0e7c6154343de54050d0f9d63d4b43af98752d0ebd61d4b43af98352d0ebd60d4b43cfd4a52d0faf5294b43af98652d0ebd6194b43af98252d0ebd6094b43ebd4952d0f3e5254b43afd8552d0ebc6154b43afd8152d0ebc6054b43e758c52d0f3f5214b43eb94852d0f3d5214b43eb54852d0f2d5214b43af98452d0ebd6114b43af98052d0ebd6014b43e758f51d0ebe62d4743af58b51d0ebe60d4743af58351d0ebe6294743af58a51d0f3e5294743cf14a51d0f3f5194743edd4651d0ebe6094743af58251d0ebf6254743af18951d0fb75154743cf94551d0ebf6054743af18151d0f9d6314743af98851d0ebd6214743cf94851d0f3c5214743cfd4451d0fb65114743cf54451d0fb55114743cd54451d0ebe6014743af58051d0f9d63d4343af98b50d0ebd62d4343af98750d0ebd61d4343af98a50d0ebd6294343cf94a50d0f3c5294343af98650d0ebd6194343cf94650d0f3c5194343cfd4250d0fbb5094343afd8950d0ebc6254343afd8550d0ebc6154343eed4150d0f3e5054343e758c50d0ebe6214343af58850d0f3e5214343cf14850d0ebe6114343af58450d0f3e5114343cf14450d0f3f5014343ee94050d0f3d5014343ee54050d0f395014343af5974390f3d65d0e43b75974390f5d65d0e43dbd4a5290f3f4394a439f9865290e7d6194a439f9825290e7d6094a43cfd0d5290e7f6154a439f1855290e7f6054a439f1815290f6d5214a43bd9845290
  | 46 => 0x1002000100000020004002000001e000000100000030004001000000500000000004002002800000140010000000001c002000000500000050000000001c00000240000008001000400700040000000000000800800580020000000000c003000000100080000000002000000f0000003000001200000090000002000800000000010040000000001a000000200180000004000000000e000c005001c01b0000002000800000040010028003000400200000010004001002400200100000000002000000200000000000024000400b00000000000006001c0040004000001800b001000000000000004001002000000080060000000000400200000000034004000c0000004001000400200000000000002003800000140100004002000c000000000800040050008000000400a0000003000c000001000000040010020004000400000180070008003000800300040000010000001000400040030000000001400400040000024001000000b00040000014000000c00200140000000000001000000340000000011000000500000000008002001000b000000000300000000000000c000000000a00000060028000000000800000060008000000000000000090000003000000000080010004000001c000000c000000000000000010010009000800100040000080003000000f00000090004001003800400040000010003000800600000000000002000c00000000000000002000c0000000001000c00600000010000001000400000040000004006008400400000010034003000800100000020008002000000200040000000006000400800140030038001001400b00040000000001000c00000180050004000000c000000c00300100060018002005800000000040008004000000000200040000006000800100080090008000001c009001800000000000020001002001200040050000001000000100000020000009000800f0000003000000000080010014001000000a00000100000007000000200040010000003000800100180020004000001800300080240000000002c0000024002000000700000000028001000c003000000e001000300080010028000000400400000030000000000000000000040014003000400100000000008001000c000000000200240070004000000c0020000004000000300000010000008000800a000c00f0000000000000500140050008000000400000080000000001000401500040000004000000000d000000100040000000000000400000080000008008000800100000000010001000400400040040000001000400100000040008000000400000000050008003001c0000000003000400000180020000000000000600000020008004000400000100000004007000400100100080018002000c00
  | 47 => 0x10010002004c00100440000000000001800100040050000000000400800200090000009005000100000020010000000c000002000100080000008000000400800140000020007000c00500040000000001004800000340030000000000400000200030000001000000800000000008000000800e000000100100000040007000000900140010000003000400500000170004015000000300000020018004001800100200010008000000400400000030000000000c00000000020004001001000000240020000003000000000000050014001000c002000000000000000004000000000700000000000000000400700000060024000003400000040000000002000c002000000000280020000000000000100040000000002000401100040000000000000000000000080024006000800600040000004005000400000040000004000000c006000000e00040000040019000c0000000001000c000001c000000c00000080000004000000000400080030000009000c0040004000001800000240010004000000800100100000000006002400100140000000000000800400000030020000001400800100020000001000c00300040080008001001c00c0000000000000300140010000006001000200100040000000001800000000020000000000000600040000004005003000c00180000034010000400000000000000007000000600000040018002000000000100000004005000400000080020004000000401100100040000008001000600200070008002006800000000000010000000c004002800000080000030003000400800200000000010001c000000001000100030034000000400100040030000000000000200000000000000000000200140030010000001000300040040004003000000a0004001000c00000000000000000003400600000000004005000c00400000020000000000000100180000024005000000a000000b0038001000c00c000000000600010008004000400b000400500380190000004001000300040040008003000400200000020000004002400700040010010000001000300040000000011000000b0000005003000000400040004000000000100000000000000000000600400010000004000000a000401500100010004000000c000000c0020000003000c00300000020008004000400300000030000000000800100000000004003002400f0034009000000e000000100140080040000002800000000050000006000800400040020000004000c00300300000004000000000400000020010000000c004000000100040010004000003000c0014002001c00000100020008001000000e00240020014008001c0000004001000c000000400000100040038006008c000000c00600000020078000000000300
  | 48 => 0x1001400000140020000000000400400100000004000000400100040070018002003c000000000100180000000002000000300040020018008000400600100030000000000000000000040000002000000000040040000004000400000040000014000000800000040000000004000000d000800000040010000005000000000500090000000000400500000040000006000000b00080000030000000c003000000100040060000000000800400000000000000000800200080010010003000800000040000040000000400100140000014000000c008000c0050000000000000b000400000080090014000000400000000000000006003000300200000010000001000500000030000000001c00000140040008000001000000000000000003002c000000000900000050000003002001200040030018001001800c0004000001c00300140010000001002801000740000000002000000000080020000002002000100140070000001000800000080050008014000000d000000000000040008001000800000040050004004000000300000010000003000800000040000000003002c000000000b001000700100020004007000c000000c0030000002000400100080000000001000000200140000014009000800000200050008004000401900000090000005000000400100020000002002000000000000010014000000700200010004004000000900000000000006000000000040010000001000c001001000200000040004001004000400080010030003000400700000020000001001000000040050000009000000a00080020010002000400d00000000000000000c008000400c0008001001400b000000000080050000004000c0030014002000000200000000034004000000000400050038000001c002001c000001000000040010018001000c006000c006000400000040000008002000400500000030000004002c00300080010004000001c00b00000020004002000400000000000000002000000800040000000000000000300000010000001002800000000010000006000c00200580070000000000c00200000020018008004c00400140000000000001400a00000020008008001400000040020024000000400000000090000000000c0010000000000000d0000004002000000040090004000000400000000010018001000000c0000002000000000000000018002000000300000000008013000800600000050000000002c0010000000000400f00000000004001000000000000020014005000400000000020008003000c0030004000001c0030008002000000100040030004000000000200000080000001002c0000004000000000000280000000000000000600080000018001000800400000020000006005400700300
  | 49 => 0x2000000000240000000004001800100040040038002000c001001400300000080038002001c00000000020008008001400a000c00300000040000004001000000080020008001000800100000020008000000400000080010010000000c000000c00200100000000002000000e00400010000000000400f003400000000000004002003c00000000040004005005c006001801400000040008000002400f0014003001c00200000080014000001000800000060000006001000d00040010014001000000000200010008001000800f000c000000c00a00240000004003000c010000800300040050008001001400400040000014003000000100040020000004004c0060000000000800700040060000002000c009004c00a003c0110000008000400400280070004002000c0040000006003c00000000000004000000000500080030018000000001000000000020003000400a005800000000030000001000c00900140040014006000c00500100110008002000400d0024000000c003000400300080030000006001c002000000100080000020005000000300040000018002000000200000020000000000000200480000000000000000a00140130024000000400000000080008000000800800040000000005000c00100000080010001001c00a00240030000001000000600040010000000000000e00200070010000002c008000c0040004004000000700100010008000002400800140000000001000000000080000008001000c00700000070010007000000000080000000000001400000000030000004002800200000000030004000000700300000008001000000a0000002000400500180070004001000c006000000000400020000000001800300240000000000000000b0044000000c00400480010000001000c00100040000004000002c00000000050004001003800300040000004001000000100000030000000000c000000400800080000008005001c000000000e0000000000c002000c003000000200000000000000000800200080090000000001c00200040080010000000c0010004000001801d0000004001000100000000008000000000e000000000100040004000000c0000000001000000000040090000007000000400400010000014000000000040090010001001800500140000000000001000400180050000000001001a000000000000000008000000000000000240000002000800300000020004008003c000001c00100000050014000000c0050008007000c00000040000000003001400200000000000001000400200140000000002000000000040010010009000000100080050000002000c003003c0090000016001000200100000004000000c0010034001000000200280030004006000400000040050
  | 50 => 0x4000000000900080010000007000c00100380000000003001c00a00000100004006000c000000000400040010008000000400f000400b0038000000000900080010008000000c0020000000000c000000400200000000000002000c0000000000000400400040010014000001400000000010000003001000000180090038006001000500000010000002002c00900140000008000000000d00000170000000000000a000000300080060010008000000d0000001000400a00040000008003000c0020018004000c002000c000000000500080050018013000000500080000010000000000600100070000000000c0020008001000800200180010000000005c005001c000001c001001400100080010000005000c0030000005000c0000000001000000900000020004005000c0000004010000801100080030000006000c00000000020014000000400100240070000000000001a000000300380020008001001400100040010008001001400000000010008001000800c001000c00100010014002000000400000060000003001c009001400800080060010001000000a001000a000400000400020008000001000400000020020011000800000180020000000000000000080030008006001000000000010000008000800100000010008003000400d001400000080060000000000400b001401b0004000000400600040010008004000000000040010000001000800300140010000002000c000000c0000000000001c00100040000028002000000b000000c0014008000c002002c00100080030040000000800100040060000000000c000001400300200100000000003c00000000000000005000800200040030000000000800000000050004002001000b0028008009800800040000000000001c00d0000000000c0000000001000c00c0000005002400200000020004003001c000000c006002000000000030000006000000600080010000002000000200000000004000000400200200000000005000000000080000004001002c0050024000003400e001000e00000020000002000c0010000000000000300000060004006000000000040000000003000000a000800600080010000000000800000040030008003001400000340060000000000400e000001100000010028003001400000040000008004003c005000c0000004002000001b00000060000000000000000180030000003005c0000004002000c0010028000000800100000020000002000800000200000000000004800200180040000005000000c000000600480000004005000000000200020000002000000200000010018003001400000880080000000002000300080000000000000000000000000008000001800600080000000000001000000000060000
  | 51 => 0x2f8917530590fc16b400006d91a4e000057d04c994e74bfc0000000000000000000000080e09c40000000000027389290a93a415072c16dc0000fd418003c688252645139a5fc89f501fb362e5f8c0d122fb2e7400280000a3a000000000002330000000000001d801c600000000103320ee66901df000000000280d1818f9000016fcfaf000000001c680000f16227000000e5000000000000a6480000000000000000000e9c0000000000010008a80000232800006e3d074800000005dd48dc1468000084e4d260252324097940000000495e165400004c6000000000001ce241301f3d10c9d172ecc460817f878900d63ffc5759480479060303f81c1a0d5e4e0cdcb0611000021041da8ab00000000000000002f9a587c000000027e04b34c8680001c18000006580000000325d2a500002c3c2a3cfc609a20b4c00008c280002b200000000121c000000008c4076c1cd80000f9c098d009c9785043800000000804069000014e8009cb3d981b00000000000223d00002ac48fa8000055c0000000000047a600008259cae00000000952917c00000000d59875400000000d1600000000000132e00002f6c00001f98000000033c46b880003c0000000000000000000000000000043836a92d89bb000000000d8800001eaa000118780003f78162053080001e1400006471ce041e06490d86152c27e27c053188518060c69d869886ed2980518400019981bd25e9008700000cac3e8c0000fed33cc0000e8d1de92ab400000000000384800003bc800000007890e3708250000000000000000df248fc00000000000000000011e6000000008f000000000000100d195628e800000940000000094cc000208a21d47524212212425464d50f4b000038da0000358053200001edc70900000ecc528c46c8ca93f0a14a93300ef33a7467542ae0d733dee32106a896780000000000000003746000000004c92410000000000003cd29188346007f2e640000e0e80000000407800016af134e00000000c0306680238000028e4632000121c00001b347110ecc9d6829a885940d00008000000300000010020000000000c0000006000c0000004000000800000100000028000002000700140000028005002c000000400200000010008000000000000040000000001001c00000080090014000000c00100080190000001003400000080000000000002c004000800000000000004005000c0000004004000000000100000000000001001300040080008009000000000000000038000000400100000000004000001c0010014001000000100240010000007003c0000000008000000500000000000005001800000080010008003001000000080010000000001400100000060004003000000100000010008013000800800040020000007000c0010008001
  | 52 => 0xce4689bd00004d20b588000182a92892039a2217740e446570000000002a1153257400000001007800011e420e477300000f066d94000000000000000000000048280000fb82104482200000000000433c963c00000002f8e00000001ade000000000000000236e00012a80000000000010d5000027e600001fc000009f2715cf5e8000000000006f080002d8c0000000122b1cf00a6cfca1ecf302a00000001c7f00000000000225918d07f2c000254800000000840000000000000ab0800000000000000000000000000f71054e0000164c0000000122e441400000004cc610a109f0000145854b80000000000000000002637475a0210097848b215e55dd109122c10b6295c2e88000000000000000671000069a40001abc4c6a4ad0b31a0821f30650109e1ec4349600001e700002f3089e423c85a300008d6800008c2000044ecff0000000000000000143d0000000047a000000000000948031d139e0000aa08354279e000000015ed4196893021e8000454e63d11099bf7000000000000540183200000000000204e88e84eb04361ea25c44cd4800004aa73200000000205049d0000187b2f1687200c08000000012dc000185e33763850000000036000a2cb711e3517d600000000aaf02ec57a47bb8aa337f4898800013cc15f60000a750000000070250d3896400000cd4a16083c00006070c02907e128284c00000a7b12a86b2007019ac42e45230bd400003090086c00017a5422e000000000000000666c00000000e5489e000022b10c105db49689be4000047c4d3b943e02b0000000000000488959077381cb26100000bac00000000353c0000a350000000000000000c8a0000000213648868fcc08c1cbf217a5590978824a416291e06080a0f1d3c84a800021f83dc20000cd080920000000023a000000000001032038327da0ac03e50410415e0ca4238186a000016ed245085a000058a400008730f6600011b68000000000010a880004250000000000000000000000000002c006db86bf89110b2e19dc01a91900000294101a00c72edc0000cc2155e000091f4de39ea6000091840000000269c00002ea000048d21761327993b0000817c2480000343069f49d89e1f00004c04a4b23c107085d6815b106f305831440001eba2ef8077c000047e000000002c81e2c000086c00001f1c2ad485b800004f3000000007cd906500003c24000159f25b60000f570000000000001ac0000000040680001401000000000000000000054c08290000152a976cfc681650000000000000000000957d2d0000022e23528eea000000001ca0cbd9b2b00008b2ccf3800010d88f78337223f38c47fa01c900000000000069b9366122865bc72b142d4cc21e145cca59104ca13740001b3914464ae84d324520000250d2690000421414188558ff7
  | 53 => 0x1d0a0000000089a15a00d04cea223600000000156141125ae76690f6130a000033c006896e540ba410c6f7967200005e10e1c856412660000df500001cb07b9000012b53a4074b11bf8000000069401f60bc718740000000195428421dd098c803705e87ee0f671799237872f00000000327c0c6c9a00000329809d8cfb09c63f0c7a90000128a10280000698000000005bb400012a43aae00000000000000022a8b2d203d1156000111193820e7a195c4e08000464e7de0de58e8b48f676e02318662350430dcf6c07160c0844940000000147c00000000000000000000001f51000038ec00011eb20ba000000000002dae00011728a5e05981b248b680001db492a800000002d9600000000000277a26f075e8305000065f0ac991282630000106125a1000040d8d758000000061944ec97471ae40000f930e000000542410f0acc36166760000000000aa00009598bab00004e68000000000001834f929afe0e4057f800004bc00007df9236a06b224298380001fe9180e51c80ca8000252855a40001f0d3d1e0d680001b7d00000000aaa000016c823b800000000d1251ac00000002d803a7d17805212b3610ccff201fa13f082800000000314800005f121a5054e0000000000000006584000000000008714eaa9e873b0e3cd400024631d2e27710a98f70000000000000000000000000001c3b035079b0a7f869000000000af38e6646562e28db78000115290b4000140c00001084000000000000000dae0000205e2c51239800009ec7158281a37b00000000c46000000000000000000009280000000000000006390000000035f40000f5a8b6d4ac2321c00000001284000000023ed499e394800015ee4c3c765c000000001da85840000d2633f40000000260800000000f1705af2f420000000207f000000000f292020f9a608800018783ec830146a210e40f523db4b9180000000776412a1f7603c600000f10000082e46682f20d873eba5b24a969ca20c784fe41289ff300001a791461368002a0000000000000000000b9a80003a6e78f400000000000000000000001a920000000000000001e980001f4400000f648c0a4f3266a18e51ca8dc531b03fc076f977912686b64b6d88d335c63b0c912000017f269c0e24800044ca4e900001f0300000000000000046140000000000000006630a700000000028ec000000000000000000010600000000c70000021ba6e20000208447d600008830000000000000000e4303625b78b9221d518d80000433000000006d30776a49800007bb516d000000000000000000000000000ce394300000000118e8ab629ae73680000000000045b800000000000000001d01550000000000000004c7a1b1c55680000000000000002563c50635400000000f9224400001dc00000534
  | 54 => 0xb45d30c5226660000d02000043e6590cb099b5e467800006429ed912500000000000006ea639c0001bef0000000000000000000524cbd987f2000060e8bbd203f00000000000000025522e240000000090800009f20a5c157c47349c386c10000000033390632e1a628400006a90b2c000009900003fb87d389890d7a0f7093905a382af00007f3032a92d84c6600011fa800025840000f920000000027c800000000000000000000000000365c3cd8000000000000002134000086e4da50000151c8230000077f000069cc00000003f8298904809e8200000000000000000000001118a4cd4a885ae0ee30a9709e84e184970f4b000000012c71ecd329e7b48ef121ea437e69e850387960000000020f80000e6800006b1151649aa00008e4913d12540000939000000002568000131a0dc0876c00001072c58000000000002ce8360ce810502000000010e800402d9e00000000000000e000000020720596000117700000000000000009260058452908f9f4c29880000d232575000042387bb130e00004fb86aa05fa15c832a0000261a00000000576800016c25ad0dcf91c42fec21aceda9deb000000000000551000040f80000000000000009dd129b00000530000000028064b705a098ee43f2617c0000000097e384000000001aee000000000000000643c0519dbb2ec80000d6b198d3d3c06e8fa487e147b68f246e91dc31e5610dcb3725cd29cc57f027383ed4b2e34880000aec382c00009de000000000000c8e00001ab000000000000000000000000e743cfe1d601cfa0b8309415487c609d340422a2850d85ae0eda0000000000023540420b500052424200001df800034aa360835b16b50ea6660000015a83a2800011fd039e2cc000005838000282067583138000022c000000017d600005b0ce989705000071dc000000000001ce4e0a00001df0025012e0e3a04583ce0989800018ac4a7800c265239ba0000d05000000007e78000000000000000ecd80001be421dc97907883f200000ae708e43fa481b44851d2807b412e000009c93fee0000000000048d80e280000000146c94846418a204cb607f841b91fd42fe8b44cb2841600003648fe18dcf16de5cf8000000011500000000000000001ac800012411c8c7384c530a86000004e8000000000000000000053803de0ccc9d40000000000007d39540000066ac000000019fe7e580000000000000000000000000000010c400000000039c0000000000000000000bd60000000040500000000000000025e4000035c02a18000362c000000000d81fd000000002659349e000126180000000000000010160e360c9d1fc10760000211ce2a9ddc2e6042ec0000000377a2300000084a000076953261afc14e076b9237901d2746000130005ed0534000000008bf000000008dc800
  | 55 => 0x4820000000043208da000000025301fe864b0df82108022a0b1c0000000000000000001d81374e179c00008f500005718b482602000079e06e6904624125410cb88000178a5468f22000000004c8d1f50f5212fc8a28cd40ff33af84b9100ba293175a00000000d1900006a00000211d0000000084f00000efa00000000524000054a415d1b1f000002000001e370000000000014b10000660904c800000001f6ca9500001b2621240001918000000009210000000000007d688b6233286e80001367000008d4b44800000922785246000000000000eb020f9034c0000a38800039b601a0a188000204c71ccf7f0000178c00000000000000049a4885800000000000e561ab927e800012b9a48735b00000d34226e2e000000000111d000000000749fdb2adc3968932a0853b822ff8175089237300000000050c000000000001ac61b58629cb228000000085a871924b500001e34db214ac2b5a4360cb100001e32000039195a9000000000001e954cd2842c98f13ce45f27858e2d053f0b380000000069b35be4c940000d3400000000249045e208e09d51de992119441d0c3d194ed31e42728d7c91c5250400005a604ff2f56000000000000b040c4915e1e5c1d845ba800000001a5200009fd800010ec6458000030a00006ffc00004f2362800000000bf312000000000255e0000000000000000000000000000000000000000006b3000075600000000000000005c5a111000048d4f238000000062209f4800000000000000000000008234ec802e000000000000000000004d750e500000d4286707ef858b000020a8000149928047e3c65e80000cbe8f3c2fd874b000016f8efd0f6f34f003ac9cf931f12380000150a2ff0000456c3c78000023a00000001cb90000249400000000000351d29880000000522c4b000002c8e1684a710a272f5a58f463106d23dfa0fc800009803920123062f1e2f00005ef8000244c059c7258275037106ba000000012bf000000000001278000000009f7925c000067b4000000037fa57a8c881ede20e032e8c7514cb30b053e07ad14811daa46c09500000000000000000ec9000000000000122308600006de00000e2400000000b034ba433545a0150f2e2e737c923225b4c1294a0ccca2c112760dcc656035c2f786800000147700002ddc00022e20000286800002df3cc24c100b7000000006f7030a80000000743800000004be4000000017bf0000000000000003b1400011b49c4f313862252e9840a0c1e0c7c000000042d20c1000013b031b81120f03000018120a1400019311884000000000003dea0000eca909d000000000001ec548527a64af00478372804b4e7f0000000000000000000000000012f1800032840000000000034a8000000017940000873c0000183000053589c915f712122c
  | 56 => 0x37d00000000fb380000972000047f000000000000000000000006ee400000004b92000000013dd000026d060b800048400000bdd8ad9370400000001b9711a2348c00008f840724700ccd248608aa000000024e100007f547cd00001b086ac01b09c92495809f41b014fa04d44ba0bf20e4f0366457c92416ef3d508bcc0000c5023b650aca020d912dec25c8000213f45001468000050900001aec9fb800000000444ef816ee00000000c17000008c2101037c10b00b1a000000018ef158e0000b3fa0b50ec600005ea000002588270cf49f6a207e0fa8863a0913776772c31780002c2439a133313f50000130c000177600000000f2d07e600000000b72133b4534483c236000023f0706496c97673b647eb8cc19040337e5375067053c27b0232c00003c700001734c9d0fd82f963a9cedb800004d83bf801e000009aa00006ed800000000000b4883bc4aca02e428c82d335a200000000000000000004be800000004054c990df143ae0ba46689adb276c6c5446a000049087a6044e0ba50000000120301f10c142558354136e2c8c0000749a66520ea000016b80003b920000ca5a5590d7a35300000000087200000a50cc100000000b2880000ed229c4b7a00000a1c5684000073c16e859a0bdb916b25be258c8ab0cc91b2c25d000014bf2afa36380000000226491400000261000000000000b5b3a883c3c6e389cc00000000ba200002ed003c440ba647000083b909b85610000000010a1a7400000000000000046d08b103279c250000085cf45000005f40000d93800042560000b50800000004394730254341b60000105113c408c79b802680b114702750dbc0000000016280001de42652647503814732e3400000b91a58052a189800017d8000062d00000d6000001c88000088700000000a12146c2f2a00000000000231c000000005c7496425e1281a004193a4d5400007bc36f43f78e06000000008a243ca9f3400001d18000045a1b7a00003070000000061d46400000000096cc92e8000304a28ac00000000000000000000001a3c04f4b99a16f361e21fc57b809e244481303ab9ca7341e585c000209a46ca445077480003ffa00000000b9d000076ccbb0800000000001212000000001ad4000000000002c28000000020485728cc98000239800012e0255d332284b0f5da222463e1f9cfb8948f1d1045000001f9c1f248358000000025aa00000001b5933e60000000000000003f5c0000000000056e11ba1f0f41aa18a4b0c811442c800002bc18ab00000000000224100005c4c75e1210114a0001047248f383e450c0000000000097f419287b6000040b4a890fea343e000000000002cd40000000073e4c841c7c29a000000006d2c9ce85eb076600000258cbe00000a10c5d800037320000feb80
  | 57 => 0x3003d066eb06f6074208043b18fae000023bc4408000218500003c881b5000008465ac80d28000226c00004cf806f00000000ce48000000024480000000000000000000000000023988eb820e32500000de08000225a4f70a9c024d431400000000000000000000002465158048e0000130b000070d0e8ca4f700000000c5780000b321a50000117405ac0000527a0e7472000000000ede00000000000000000000000a2f80003fdc000000000000fa26d74000152f292e06ed325a255250a000103395a50a1a5940e87a162000081980f51f2e20f80000f588000000000000000a9e2d18507ce8617b50000238cd4680000000000004500000000000000022281b84524800015db2876001069d936f34a6871ca220000000000000001e90000000000000cfc43ec0e1c000009f00005dfc00018fb48420000000000020f28978f83082d1a7c6f64493a44900000facabd00d30000892800000000000000088c800029f6942c80000000640120854098db3e9082e92b11ed300000f111360000244e94311b780003be60000000036b0bee11a522315823c2200004fe89713a5c014ce0d800001e621a4b0a0000000007650388a0a00000000000000049b27dece9d8808000091b80a70a6d461655d4000243c3ea60e3c000184239a805a914280004a328c5c4fd01d81e6c96490ff1dca0000605073ea6070be68e98bce800013140d5c00003c519b0000000000004370000000000000000686cee38000000000002e40a170ace6fc87281f73354e45cc16a80000ec20000000000000000000000196900002d580000000092a6cd8000000000001fcc24700b41f1000000000b654c8009000a9921d4734855c237005e398478e400023782796633cfea1a6e29644e5c0000dc10000118050f8659396271d80000f964448000000000003fde66581791a430000945400000001b8032c4000000017de802c000205b321c43240001ba200000000ebc955200000bb434c1eb3000076d8b7980000000000058d8dfa40040000000186e1a2a19705358000308027e40000000000000012d9000024fe000000000001396000130a15081980522813310a7024c35e40001ee500002e7842419ce294a09ac0000000000000000000a1300000000f899ad722c2200c00008c8000000009d7000049c00000000056f0fb051e0da0000045680decb081d1123963298fba800000005df486a80f632b000006e7037a3824055000016702c18000000000000000959d2119ac34a4c0000fab24a002464198ad201c5000038740000000000089a800000000000000000006d323d800000000000000067f878280000a8893e429b0399112c5dac0330000000000000000862000077f08ad1dea000016e4000000000007040db308ef13d473c0000000006fc18b0000000000000
  | 58 => 0x74891330c21137c0000353800000005dc02f0800000006e0c88990833d860a44e9380bc465400012d79fd8299e633000006dc179060f81ba1d823c1a114094f96c2098a00000000d6d00006d508fc8000000076ac5940000000024b08a9000016f00c4c0b00fca3d425650731149a00000000e41867e2e7e000119900003a640000000221b3f6a0000dab120d36826fd80000be0068417c11d600000000670400000001ac80000ac2961a0000741037e0000000000009afa4260000000000015510000000123c859a0e1200000000000000089380000000137600000000202000000006ab000000006990caf000049ce0000dfc80000c6a0000ca2994a01224b4c3bd8000000039dd23d00004a5c5a6c0ea80001eb2728000000004b988b6cd658b582594000000000000000000000007ab3a9a6074607216c0a140f040000c3c0000000093821c4318800000000000494a70e045f08e5181a2aacacb8000030e00000001f2700000000bc684e9043a0000e7e000044b4892400000002e900000000157b000000011468000000000000001f9100006518000165336840000a32065300002938000000038f2347423d000000008874c360d3f38003504f6b03e11c7c77f45b10b2e1450756c13200000000546cabb10f7417e00004c2967500000000000000040440000046086e00002824000000000000000d988f6a02a08bd4aab000000008ff80000000000099ac0000000000006a8b2f8da5031c3d7cbb890b63e568c50000000031a811700001ca900006c0c00000003f12192130b20f10a985bfcc3905ff08965d78c2b1809000096649a10ed23ad877108e92306328200012c3800000006510000000005c200000000a6f320e96a88160c0c082a45e0fb29e192f6467b00000ffb000000005f205a4000077f800009db2fea0000c00237011c200000001fd328e0607806f8e2600004ab929925fc0000070c0002281486e3f2000004f540640174000002800000000eed8b862e126da0000000046aa000000011f41f864e3c2328000000052884fa979100002608000000005e200012ad246b00008f15205941e3e648a3920916c849160000000137e134a000091b0f03040c84980000000147a2dec07d9e2900000000000000043ac000103407182fb874588e10000010e00001a695b5000050388e7892d42ea0d18000235e371a000055c0000000060d81dd8e02201244bcbe994ba337046d800002d21b4487803190e8a12e600003d5000000000000d7c051f0000000116fa5d50000000000003440000066cde78cf4366e0000000170b2a6858100002664043e93c8000000000000000bff24fb400c4e9903d12172bc60320c65828100003b7055a8268000000003e800002c220000fb1948d28784bbc909123008a642c4000015900006968fd02
  | 59 => 0xb520d000d38000000000003f6497515f30000000000011bb0000402c00000003a7200001d6a65634662230c0400e6249a8ec08438fa0000069480001b9311704c587bfa2640712000098a08fa00004f0000003c6159c2f5c0000000000000009d28b3c0000900c525000000000000b7d169f00007bb90c9000000002070dbb00002872890cf081e6a020826b0bb48840000053dd2d80000451e248800000000000000116113e30bf800000000000000009fcf6306e648108f540000000000000007781126233c447c000000000001320000239d0f24228c953195732a40000a2c8d2100002aa415410500000637c000000017440000ea280002128000084200002c380000cce8000000000000000f850000000000018e80e6e2e0c00000002c7611380001eb4277c13e11e196160000000000000004bd000005ce000021c0911c782000037a04dccfe7819804f48bc8000075e1ec0490ce9197602e3c6b54fda1df9119e31d018000000000899c56c00003a7e000000011b12e56810400009a800004754cef928f2e3a00000000000000000008a400004cce00000000000000000008c600000000174c00000000000595c56e800008842f98ce80a843926410800000000c8e92f800000000000557c00000000000860930d87054be84c304451ec1032496f044208f74a98439ca618000000000007f00fd639fa8d8c00025eb3fcc2a643cea4020c441d2400005b5000057440000000188c0000000000000000001087800000000000fdb800000001c4060f1b7e042a098c78984af46e482790fd0cec304262c040695c500566f6c00017873bac74148cb8af84c404faca42a3f21bac1f8cffa06fe000000007c98835138491d08ca80000000229c284038819c61644d6800000000000004c80000000762c0ab97ed0abc969cfc9a11c052c0000b9387f9000000009959023034e000000000003d700000e5b08c500000000000000000000000000000030e00000ba806130768878c0000fdc39688984ac0119f357041647491625024e0000d9780003d4600000000000000000000a90000000000007329eff38fa36a4d8901ed00007e100001a06047c0e740120fbc00001f4c37a800000007418911a1cc23c665c0000197a1b20416d0ef1cc5075c142cf651a4a1da28be126700004b50000000022172708000000000001866000113d800000007098d9311d400000000000229d00000000000000017e8583400015ae185214e4000000022fc000000000001a5600000000b380a3a7e2800000000b2422b00000000188800000001520000000002d29c51234a00007c080001d66000000011d6216a23b05950780200c4f151fb0ddc0000000000000000000000000005db00000000ba6800006867998e309c2800008e0400004454bce397c0000b0b0ec8
  | 60 => 0x344c1e49dce044e1eb4b1c05df0ab486d514207c1000007a0ea1193c1bd454dc0ba950731ee4cf088712d4249432250721f462b9250750fe96ba39544008c4b8a4641261bcd2da00003ef45de12f50c88243e016d28b09b9259600586849e84000000000000000169c1a9828b1f1e0aee2524cf1822d127a894c9ae152b27b20000045a00e1d7e000093e00000000000131d000000006420d4a069f371852a475106cd06c80000000000006ec084c1b1958a2c46369000000003b461160cdaa43129bc94287860767272a5f7c2ff187e00006f504cf0e013ff60000162a51c4c4c5748000000000000758bc2800000000000000070800000000baa0000000009f8596067d15a600000001ba13c3000001b3a05e29e040b80000db02a1c567400020df171a04c400013b900005fdc1c015c30f7658d06a7182d0000000000000000000000000000002b384d4c1a28bbf4b0c00000000a870000699800000000e4c967cea190ff3ede70c88591aa519362f38f55000017c6000000000000000343800016fc03f06e19180a67047101cb802b00000bac2d08f378000000000000000583263633acefc149e0000800c6338000113634183ec80002c300000000129300004538000000000007a6c5249f800000149c000000000000000bea80000000289467000001432000000000002dd63a54def0000250c00005e019de00002c7489f10553256837086995811e300000a170f1b1d0e00003e000000f64000091e800008f80000000000003fe0d287a20000296668840000000000000000000000000000000e895da00000000000111700004c7000022ec37c61930d440000092e2ed080900002bbc9840ad5800000000000000000014102ab850a00001c5897d8c8a800046c809880001bee159024340000000000031500000000029a0000000000019860000000000000000000000137100000000f5f1eef0000000000000001dc0264905c8c65156600002399ac100004aa12dd9f6c2dd02860000000002201bb858a969c3f9a96f89a5240f3bf6402800000000000377847b009713f80000e4f893519cc045c0000000372a5174c8f806c00000bc0a3d0000118873c439380003f4a103cf2515b306207d6876e91c721fa337532c0916434205889701f0b00000f448ba8000000060dc60c182800008f8000000003b440000000023d0000492400019f245fa03bcce41de84bda2528c1223cd3814170400022e8000040a8000000000002298a20140f27b43de9198800000005274d8d07992b5440ac149000001b48f1c000000001c415f4c3f92f30f8451040b326381cc207d400012e6000053cc00006514a4e87450c586c800003d5c3dd1d721e9e2ec47d900002312190492b1db900008d850a581e0391c77b4b191c4d0d4a9088000000000003bac3d8
  | 61 => 0x3ce84e0400000003aa20ce40001b5a0000000009297121f081520529800027860000dba8e4b000075000000000000000000001cf300122fb400000000000445878383511340385839608a14620388078e0000440c43088ae00002cba6ba0000000000002a80c080f7917943e983a40000000037a00000000000027f8218809c2e361f20d9d00000292000065a904c0cc61b90fc1039829b60000000258a37368a910fa2275465c81f0d239a6107a0932124e0e840000000056b807c3adc00003fd221f1f6c1a48a3300000000000000016f701d40000be30000000000007590000000059880000000000010ac000095800006b3932b952636d419280001bfe000000002988000000021f470e171c325a0000000000000001e5003c822b158a5b8c1a3806400002a00c3b20430000000099a241a2cf200011b71d640000553800000000000000130f8196000005c04dd11772bbe33b8000244d19ea8efc000212529406c2400014ad45ae0001277172f3b5841b80000000357e0af06bf000000000a70000137f392e000022183cf2f825aa0000238b072e49f893a990b000000008ab8e640000208c00000002480000015b9f1f00002a200000f562c9c000000000002cf86444c8ba14d00002bc8625036c21402b0c6521acd0000000048600004b6e77d111a15fa1ed27df095f23401d4c19ec8dd000036c065a90e4861f2dea48f800001c200000000000000000000000000085f1e8a7ee800023ce000068ac53000002ede000000006850d0e0000000257200000000000000021880000d651ba939600254fd4975b26742bfc270800041ae9560caea4f83e7800005480a3c0000000072a800007fc531c0000c8d135a780427f000027665fa80000000000000010178000000074f037f800037d20000e298b3122f200000000000211252bc25f07312b7628300001f690000000000017fb0000000000015dd0000384c0001b25000078f000023aa28f652f02d3a6413e6a29fc000200a2c1045a4000194925ea6a6d29f9bd800002a9c000000000008220ab6834b268c719400000002600000124a8eb626b2644800023570000000000000003d405220000083f3004000075814063df8257c00018d30dd2000000002570786000043e222b09c88cd84e1a508274e9940e9c05c909025d640001c9814ce0cb84d1877100006034000019a000015b4000000011ba28048c205592dcc263c000068b2b5e870c000000000000d20eb680004ad288ec000000000004be80000000000000000001bbf13e25678000127727a65050b7e8f9942042774dea99ad3cea5a14eb515f12ea40a4082f975d0f8c2a4499b00000ad800012581cbd15544dac00007f400008d0ca6900000e42000000000002ec43e74de4197239506214000000045c800002ba8967000
  | 62 => 0xce00000000000037c00003a20000000000000000000367849b443220a406a05e68034800000000000d0192051272000000000000000068c00023b6000033a80000211214a000000000003e9a0000fdc80002f2c5a9400000000000000000000000000496c4898ada0000000077422be40180d6c00000000000337c0c20b09498252f89920000262a000036f800029c80000cb21fa2030400000000000409e3a507d80000444200007721c5f09140b008aa800000004fe8000000014f0000000000000000000000000000000000006da02928f800000000000000000008468f7130a00a1c0000a7714b00000f918000000000000000eba25e866c8cf8a49f1e0275cc0001cba00001c5400017010ac400000002389000085f89e90bb3230e0000c178000000043b0000156c0e52000000024403922000000000001a86649c8bd0ea5000025d8c7810a20000000000000000000000049c0f0d33b60000c1e8000309866143c31b92000028a80000000000000000000000000000000001b8b21ec665c4ba800000da0000d9f24cc2b78261852915c03a3899a03a015d71274067c521090f0604479c35f80002b6e02dcff10d9d44ee00000001c04210c904cc308000409200008d38000000001ec0001ec02f80000127d1d2b22a6271416d87d203180e140002489408e0000f02800000000000925800027fe0000000000017ec255c46f90f93ade7e5400005c310de70845081fa4239c0ba06b5132d25f035d894b9cc600005aa4253800000000000000000045983e4439c053e0c0448185af1a5116e03584137162617546248252a1e644c000000f582bf00000000000000000000000000000000000000000035f294e83f0000000000003e0c7e709213e6c00000001ad40000451d05298160000000038a10a13bc25c9409500a1492847e81b4a24b0000747400000004b0800000001ce40e262b2cacc00c00f0200003058e0b2f3696591698e4e2ae47f28ff802a93116000063819fb000000009008039000000003b918b53a5e50d8ed41c5400000000fd6039a000076f000000003e6000011c10e9d3552000000000001ba200006ed0f24000005ccfb90000000057d862e0000000054051bb00003bee3c091ae800000000000000197636da18b8000132e38ce00000001e4300000000ed00000115e0000d17857c0ae00000cb60af41f1430fd1a98000095c00000001b7b0000000044f8b530de81b6812f16f01b4c0018eeba0f6000031cc00021a441e820c4f91016f00000000f7499ae00006ca429d1c4e29f854341968821447089d90a403790084685cd4f86db32be00000001487000000005fa80000000823c0000000476a00010a0185c3e2455a000000000000000000009e000000000242800000005534f7905d500007a00d3880000000000000
  | 63 => 0xab0daf0000303c00000000000955881097633cec91dc36e98c1145273a81ca153523680000000000005040000e38800012fe7e38f23174520d600009379fa60000734c0000000000096e4bf89c7c40c04d880bf001b49460001242867404da0000c81a36c288c0000dd317d9000000005ef0a483b24000046b000011ae4330860000000007db4cfa83f7135e960c0000000233617940002333109e86348718c322fa82fe0d9200001a30280c38600c5188613588ffa3d7358e30a00000000316c265d1df25290000000093080000000000081a8cb6409a372043696844b5c2c0023e800000000000000000007b000d800000000000000129c0000385200004db0000000000000000000000000000001bce1c7000012a580000000000000007eb302496f4000096200000000000175600000000000000000000001196800014b60000e238000355619002f500001d125134f7c000011662d5c00021ed093000010310000388420c0c1502713c424dd0c99800000002ce902c800000000000595800000000000000000032ce030c94407df00008160d62164249107128000000000006b980000000083800000001a4d0000564872200001fec0000000000042ba76988780000484a00000000b7a0000000104f80000000624c4f68989000000000002342212c2180aa5a05035262974c4d9da40602000045a889818e27b68a3f25420000000000000000000064cc65000015940001256a2cf39344064000000003a863790ee80004c4a13b87d28f500cc00000598014713324de400000000f5c0000ec480741558000000000003c70953c0e300000000000128880002ee44dec0000000000050dc00022ce045c00bc0000e350000000000007b500005d7c00000000000924457398012990969466b25c72ea22c8d1ec9d3500003e7d07d1daf3ad6000000000002a048b9835592c13d1a3fbce8000001a240000fc5854f335498749be096907d044b086c998f023662c84d093e8380a1b44ac418040000433c0001b130000515004d0000000010d04e210291a1013c4ba087a834ba2630000000004ba8ae000010de000051700001c8b1c5601f8b108270282a458c69694f21d3449306168cad11861f2cd590bc44ab868a4704069c3d4e69c8aa609f7008a282c00000000000808cea30000049200009150fae000000009d101f200002d7c0000f1d0000005000000003c960000000000016644f8090396fb00000000d9102be00005564d42941c2a7422f40000000264200011319914143a000081280003d380aec52a00000000000107e80004bd200000001e7d10c62d8d24d800000000dc0e521a90000035bc0001887000013500001587000064bd12c145525568944ed3800000000000f32245723b8000000004ca113c6e1c000004100008e3000022c604
  | 64 => 0xc1068784780194081074f9200995a00003cec6d40dc400004430000187a000000000000000417c41d0000082731064b743e1892008983ff80000000000011d80001486344673d0670a56e00003ecc30b1b2810165c8845a0aea4aae3a700000000464400011919b21000063e9123256b29382218308000000000000df300004ae02b3c00900003aa000007c58000000008852c097261fa61d6904a8be8000038b902404a200000cd800000000000050450f1b6c00007c58fd58000000083dcb46894f00003b3c0000000000000005718fd202bc5180a2808714926379c9c48ff20000000086b199243e02514f8100000000000000017db49fe0000106000000000000000217b2a2e6f4800006c20000134062980000000795c00000003f300000000000045ba7e0c1f3174b00000000b120000382600000000000000070184b29b49192c8b650ce8083299c3b60dab800011b800000000000000000000000e4d14f200005f7066c0000786c095856e1eb851a468888db1db62e384ac800000000000deb0ae900005c6046a9a1d2e067e7c0000d1f380e6eb8000000023ec4a540000d6900005798000170234385cb00001ae73e724cbc0001688000001d858f0000059a1c7494380001666208802895ef000049d8000195935a600000000be10000000000018fe000006b4c73063d00000000669800025025e04d22213a3c4e000071480000000000000024ec158c97e800004fc062e0000e260000050c000000000000bd800008d68000000000000000000227213a000008d24c88670c6279fa81b1a2f30d9500000000000000000000000000107a8ef94cde000023a8a9c0000828921808b225ec000037b8f6c0a6a60d00001a2a211000005740000031262f82c01a6f1b7c0000bc41b3f378c941cdafa36708885664000031c181401187c8180a174679a00d80ad6357c71a8000149f095a0000f6400000a5e85280001eec09cc88a4be91586212e79f8b87800039e42a307fd0b1200005ca0bdc1186413a0000bf786b40000352c000052d4192000047886e810e400000000000000000000000000000000000000caa30e806906749e3f00000000000000000000000ef180004a3a5d4c37d8447001a2238748a5450000729800025d849da1f5521f86eb182842407fa8000000000009b180000000331800000000000281418c029d009400000000fab40266925257000004b40000ae4000028305b4c0000c0249d22a50000000019020000000000000000000d0a80000000995400025e64a00000000000004b5a3864f579dbd445432bc7ed87ff0b1c853014617e244fe63483ad9acc42ec2e84d1301bd248841cc0000b9800005db0000000012d022b881e05ce18be414c34e948923d263b00000000260e0000cfa0f4100005d5cb3f06441dea00003
  | 65 => 0x2d1125f24c400002508a9300006ecc00010b42b4e4a34000164900000000c1e00000000000000e800036a08d4441e9251056a0000f8d00001b946134000007a192a000000014cd1688782400006030800290c0001b790ac07708c5d18b8483c0000000144215728df4000000000000000000020914ac365000004de2d98519d3060bdd3fec12cc86590482bca0de02611f50009e3abc9af01c424f64f1cf738000166e0000000000000002080cd8800024e600009318eb51b980dbc0001f1400005e4800000000000000130900000daa0000000003400000000000000000000000883873f447c13f484600002d724b8901895a30000717458f9a75014442704d48522028013110dd800000005ab00000000000000000000000000077c40001e223614089877e9d9815ea00007070ee200b4000000014cc00000000000126c0000932d2929a920000000092c9777000010ece4e80002d0e00005aa21eb000088144a8141b1a14931ca68124f2b880bac871000039de0000ece90f300006580ecb1f7901ea0001248000000000000056055f0000000000009b800000000a5d938508240000000214e00006d380001317000000004799f553cc40d4c00000002d2c18d0000000000000cf8000166131e62e30000094600007cb12cd85ac00005080000000000002c182540000000000000000000000000000000000000098ace318000000073600001b4529507c643b98db90c0c75d40002045000059a40000000153a90e90e11e6500000000a8e800000000000000000027583adc0000e0635ee0000bb98000000064d4b1e000000008ecca3b0000000000009df8000000000010350547118e00000000000000000000001cab1abe000000007bd40504de10f780001f4400000000a34000004ecb0480002b580000eef11da00000000000000000004698a4714340000920904591d9367a73e8890053b41cc3f9926e0f470b28433400005012caa00012069d7e39ec807c328000000008f5929b80000000000116481b83e6e000112214003e2e0150b9000ce25640f2902500000eec6a740000fe9000000008aa046b00008431004800000000000d7e9f0c00000000217800035ea574cf948000000058e41ef000037ae4a2c60d1b4647962a892610d7c00000000a521c3c0ce000011050000234441b4553203b0c3a7a3800007de000003b0fd50b8822c00000000189f039200006da00084b00000000000002bac0000000250e0000000035d0bbd4a1e25a8000000037d88e340000000084a18485620366000000000c880000cf477bc000000000000000be1800000007cc4000234b1d760964e6580002406482c00000001d1c3ba8000000000008c1c8f813702be0000000000002a3019d8000000000c263380001b0e31fa0000f3d9037035e90f400000b23
  | 66 => 0x135000051b84c4000000000000000000000004d2c6671a2425780000383a5e2000040ec90f000000007b80000000000004cc800008f90000000000000003798444000000004a8e000001f00002f5c2890cee95f5387e00000ae800040a45e786370000000000012e200000000805516408eb13342ca4e65074a0000000114f800000001d642da0cd2000000000000ac102e224202560000000028e4785901000008860226973c47ca37f000000001d820a9126a181f000042dc5371e600000737800011bf248a00012300000000080e117f10b3062800000001db40000000069500000000000057d0bf000003ca443f013c000000000b68000355e000000013912c5a0000000000000005e7c20a000049bc3d00c4c000015e07b700000e5e16c00000000018800000000000000013d00000b0180003186000088180000a200000000000333d4000000000004740000000019ef3c6200000921eac0000019c00000000bd008940261ef0374a0000f200000000000000002005000019a000022b01ad8192cc0d24833b260294bf7000010e87ccc000164027a21a3cb6297381af00000c4800003860502000004b6000000011900c9c000070f8000070d31a2000038210611e9895e51550000198e255480892c300005b48b45864e0000000000000003dec042800000002c6c16c425d00003d0214800810bf208546aed0d31d0b05840a340001a1900000000b18033d15b64a0107f923b0000000036612c50000127d0b0000037880fc42048000237a400c0a41bb7000079cc4cc138e13a400000000000476200000000000000000000000b723aa4311c0001ed100000000000166b3ca46498d55173b106c230519200000000175ce4a800043b2000034d000040ec6478000072f000087a40000e5b456e0000636a0ed3166355ca1d0362416e26dcd1715e838c8000008d000000001b0c16780000000000000019c200000000894800000006b94000000220e40001060263e0d9e000000002e200001e1090d1652315a0000bfe10fb18c2903103780010c503500f0108700000000000022ed37ce6dcc18718c900000000a9b000018b00000d318000191600000001e93261a66f51a2a31841e448c4d1e00000000000030c8b4b0000000000000000000969800020a600000000afc098b0000501c0000000000068c489a00003ed0101c0000000000000012b180002bb83c40278000033f20000000000000006b08000008615fc5114000196b00000001197800012a28f68e17180e3b5a0f7d27300000000167800000001c6e5704a238c0b3a2448e470d8013442a4eecb410da10000000075480002b7257645fd00004a8037c04b30000000047dc9939f611d0c8b5000000000e48000074d8576142a42e11cd85f445aa6f80b7f0000456c6cd4
  | 67 => 0xc058138a21308c306cc8c4100000000164206128945d5423900cd0fb40a500000000176035743c70000000000002580b1601f81f140000d1a252c2df50a2000024c846cc89225f33c1c60fcd7a24b12f603f884bb800000000000000000032461f3800015cf00000000fa79de500000000000238400000000b41a2730f7c49ad2919fa727208ad4bcb8586476454f4d511a594096729419306b906d00000977000024a000004440000000036e000000000000000083619cc45d2000071888e2064681f80000000404a551894d00000c56000000000003cda752c0001e1c083c48a0acd000000000001080800004528834a9f03cb0000260d18a8c8226a42240e851d5a449e0a8d26495141770312000000d73178355434705a031c645184410b26170e8840535000038d06cc006c83d428ae20ac268a6361f761470c1994122e3e2af40000000000000000000000000073fc59c80000000504d2789845000000004f706c60ec484341b71101397c5158000168a0000000038f0000000000000000000000035686a3000000000000b0587f82fa253b85cb838e35120000000000000000918fb02053459470206cf11e4453000010af000000005f24a9d817b10d001c0e9300000b8432e000001e900000001019800000000000f7d07dd0000110499805533f8c00000001dff00007f740899f9a39a255bd2f70abf0dac2bc4b388000390461dc0002063080618dc77d818a282c5d180000000184044206af0000000000000000000243259504f38000466a000000000000000000005799ff0926857cbe419b6096a5a48a910000000000011590e7c00008aa40000352470687b8526871141f04bf0f6e800026f492e43c8109137ca063ccbc22271d8070b400017de2c3a0000000265f094c94e52341c1c2b7c7b5cda40e341e0c8ae480715552e2c3df8cb70b0100004abc84d9bad039c730063c913a4c0c55e4de9a35416445f853268dba4bb400000001a3f00005c3000013c113606ef00000c3504546b1400015d8000048580000000000015ecdd5800043646204e448ea434da3fb11d106880000000008900001960452cf658000498c6da41d519301ec26b24d20a22526041fb4a319eeb219454fc4338ced09b20bbd09725241f687dac0000e2d00000000e4e000032a00000000097009a63c7cf2400000000037108aa3fb00000a94e291020000000010800000000000000000d81305600004f204b4000000012b026041496699d00b0bdb08581b64608904e4aec5a980001e1d3df23cf000000000000000000000000000000000000002b7a32ad32404cb000052f4381021035a46c0800000000ca826d4000000000005c2883011a31422392400005983a480000e0898a01f522610000000048ce333c0000824473200008d58000000053e40000000
  | 68 => 0x4a6000016c9d7b03d800000001cc10ed400000000000275682b0000000034d600000001b723f2e0000e3a978f07fa8c692bda19026540000000205a4074399c0000b0f00000000000000019a88c0d0000000000071c903707523e960000000000c000059d800002930000000000000003840000000000003c9a196d04b852e039a04e000000aa25a4000024302f343ee17783fa80003b3853192f7800000008b700001d3310ba00000000000119403dcbf580004c30785c88aa555159293692cd04bb00008f50000055d33dc92dc0e79547331201a897580000000494cd531f57000000000000d3610b80000f9f0000000000005731589000000012ee8146275210b53250725440847280000eff1e749708d1c994e020a000000023770000000000000000000304c0000000221a71d0000089300005528d9a1c5004506ed8f87079346a4763852c87fc342658a0000262828a46bbc8a205bc26b408200740b5110988a0800023a700004b1800014e5000032c80001b38000000000000000000058c45c900000000782800012bd0000000011f8fb500002c4c0000a2f00001d4000000d4000000007f39b62000034340001e13000092581b69aa005f21d3400018174738363c74000004b7456c8000054b182479c52558f750000907cbff800044f45464c6d1596440e06146dba036306444dc122a4eb35c4043101015480a083414000000028147214e0f06380000154000000000000372c7a996654c9c0000cbf0b0e31fe4c148c784300000000053e8163036a86d83980f1e4638008d0bb94351f581e1c15105f800006d54000000000005a8ca7584c7000010740000000000038605900000276400000000000000000007389c94000000000000585000000000000e7300005bc807915f2000010a40c0000000005f3cee9a39710ac1a640001c1800007e84f680eb11b3896241d5a2f74a1a44785b380003b6267dce6723ff2b4000000000d6b2f5800001d4000049327d480000134000091d800000000b7013bcfd6a26d120e0000ecf22bd22e00c200000b93309e00000000ed6000000002008000017a5fcc00012e30000252cd489ff832e82a68e4f11f336886064666969935b43ab0000108a00008150e59800045c05acc00010c10dbc5d089ef823a00009284a88803819ca8df00002178000039bc000000037200e340000000194200000002232281a4124000262f00004a48aa282fc09803371254250902423c540000bbc37be000111982ee27160000000000000002cd0c898ef4000094f0000083342c665440000e0f0000000093c91fc2b8450fca48118b2fb415f90758a413daa00007b28b4f00000000880000032020000a8180004856000122e000004b6956c0000000000000000001a5c217c00000000000327275fc79500003b286dd
  | 69 => 0xce2000000000000000000007ec000040c890e00004ae000007b13252201d274095b2b609038a5b8717000000009b2000000005cb80000000357a00005a308e014cc80b433580004ade4e5000002d8000043183450000000063b4000000000006bfceb8202b427a37e52be8fa434ae000018d09e30aae6a60b8411ed38809199071a35b37805e24e679b8a13f64a2400009d51e248aa005b21af000000012ca188d05f042b82c78000000018fc5ed0000455e60180002226000000000000000031a4d5cb668556041a0000000000000000000000000035d46728feb00001404000000025de42b639c874c888f4bb8000050e103a4624385400024f6299478d8000000e00001ddc00000000736245400019a200000c580000cc500c40000186110a000080dc0001d6300004f8828f21da20f400008d0000000000000ff900002906640800000000ff654cc0000d9549a600011cc0c260000000000000000cd471b0ca3935b0d700000ce29dec12040000c4c9bc214623b30f2c0000000000000000000047023b46f001f9261e00000001ee800000001328800000003724f27920a000059346f59fe10e827ab400012a22aca6e7000000002e3285f512020a1475c3a84cdba0a91736104410221542008967800000001cfc000000018952cbc1c0c85c800000000000b4e986b0000152929681ab111a4e5800021290490000000003b2497468b400020e2483600011718f34013a017cdb887fd4b4498f0e7400000000000057120d941c2000000019d1404818c07670f3e40e88fe523f00003af091909e50459000051242f01e7018c83798d56000000002d40000034002f018a905a10fe10f691a863501e4254e0fec21f1a3a2ab851d51a79e9f0000024c00000000000739c00022a200000000d4618e100008e907478000131c90d4000000000007a440000a620cd2000062c800046769885143a055000018e8c10081f42ac66e87e596bf038287d4000041811b40000ac780004400000097da52b0514000000004bd000000010760390063270f4e5c000000000000000000038041c3c00006181fba5c40000000030b40e9400000004afc7c0129f02e41ad05b5400009ef4a260000000093c0b664aece0b9ea90000000019d000000004bf4f97819e40108a446f712550000000000000000000000000002430000318c00001db2afe1b100660b84214686c510121e500003b8c063000000000000f9413b51a72754c000185417340000000255400005f9c5880a550000612c930151f011239e861e98c8061a00000000000074c5958f7d800000008098e6183cd33b40000b6a079a0000000072e9aa41aa02ed44b59399363c0000561248d47a4980423d85741f98709c9c01aba055a315459ea50515ec0f9d2e28000000000000000000077a00006ee800
  | 70 => 0x4ee916c0000000000000007e7800033d00000ecf8000308c0000f84000019de141c00000001f42000000000000532398d1dc800018f41370f3580002d7c0000000000000008cdc0001022000000000c801b91c8a1730a941bf124a46ccc00013f8192245c8d7910ed1f7a201423f85a92c140f4840f0c2303e0669c00017e819fc0000720a0cc3aca10648188000038e5a5c00000003e080000000220c000005b0c7aa0ae1c7a00000000000000000000000000000000000000000000000012d486f24acc000038080001a020000000000000000000973800003580000f648130000069800000d320000267526506a423a0747826d997f003824752c40f25091e30905c024f52e6e52d800016440fd4801c4df80000f88000000017310fe200005bf800001ca00008f2912a4a82000054b253533a4033c513136148387fa8a7a94511b360000b1d17dd311c0000e188d200ba490140001c46062a05447c325c3000018d8e430a22398e3b5000022302d280000000000000001b28000000000000c2ce2092c416d4000000021c1028832641b2800021dc2f70e909c3a0000831800000001dae2ffcb83000049a05c5528f8000304683104b78c6f000003b89ab23dd2ce6000007f87a4000000000000903159a75700000f2f000000000000000000038fc9f91b53000047600000000189831fc0000000000020a4000000000002658000233e218620b000000003610757817600000f4250a4429800000000000e4012aa33f050a849b9f620e387898000000048aa00000001f45228a46c900c1863000013046940525163013b41d88000000098b896807e81f628e581120f73156800012c99a5f0054000000019b433b800000000000000049a889396dc0fc814500e0000034bc362483ea4db086a6e14da18dfe28120000d228530067600001e1242737ba0000e508000405c969009f93261ab80fe93088633350c20b81f2a3ec167e3d9c36b8d8a1cd239ec35e22fa104c95b489f87d63f6c0000d4d10ac15161b2c05d8000000051fd13820a710f00000fbb8000000000000000000000059e80000c8613a00558ca98088368e1b6085207a02b161dd47b91fff0000521032f086a3f7c32941448ca32d828ca402b80000510000000000000dc62a843290da30f5e810076c9c8714a23ab860b1a6c112a00011f38000058c538c06522ae100c1d3c17185aa3b8a44cc5e90fe110a4459c5410000000061903be109916f834ccc9e93fc420a0c88000000049e04f08401048d1860349486d9f9d35e284180000bd040f00000266a37e0000005c3060a7a472809e00001d471efa7f1c00000002c9017d800015e12b18671822d80000000883c00000000a6699245821c8c2bfe3618f6124c5269a6cec24b018600008304000161b482e000128f265e138000
  | 71 => 0xdd800019e10c48401448c0c3e000069f800016b700000000000000040366dac000261713d200004448c3439765e8c54c235c258089d0dd9163749de00000000a320da01c2d160000007a61514b17800000004d107ad9e94000068dcab1800026589358000000000002ac800000000000000000019860000000130e00000000000000022093b523260c2e8468126c000115f8247135c3de060e944c00000000d009e4e0000000000000000000000106525d62afc7780913167d00006488fd88000258e8e3cfe712c8290470dce5b8ecd2a1400008b5079f02c20000000021a15c00000dd78de31ecc1cb47aa000000000000d8e800007f20064000000000000000000000024dc07680000000421c614c967a2ea00000b68fd900000000000000011090000000000000001b6c43705e58ab725585ff4000000015a20000dba000000000b251e50b910000000000000001eb016e8afe800047684838000040b18080000b70146f284c8b4000018bd4516673d090000000000000000010f1fca254c000000046c00930aca9c8113e61b8470d1e8600000000000000000000bdc04b000021b481e526e85bd25f270382e300002ef67420e8a8000462619fc102800000005b1000000000000717083220cd00000000f66132023524ff432197e52400050c22fa01e00000000b9ca1e12df0830c00003a70000345c000000027fc0ae00000000000080f8ffd23f4000000009389c600bb48cd05728ffc00005a4c80c21be1a701e300000000000000000001f183c3c000000023470000000000000000000879c0078000235e00000000c08000000000001fc400001bf4000000000000778000000045a40000d45242e00000000000244a1144000000011c800000000000137d000096b0fe88000318c0000000247c0000798c000000000000000000000001c2000000000300000088c000000000003e1cb688df5094024c4000000000000000000234118ae62fc00000000000912c0000000232250141950b2f0000437c0000c4d00003bc8000000049880000706800012321d44e7c00001e103920f3c870e081c593c00001c806600000000000000001a808311e490000340c00025d9000019cc00000000000040c2f7122948e02ee451980000000000024d800021a000000000cda39324d3c00005462c6a000000f18734484222cde49765000000000000000364029c80000cb9021a61040c580002ad617e4b4724bd44d20000703800008ae000124700003f461825271a5bf0b3e857125b15eb0eba31ec16f1a9e2fc02de4b008fe42088122078000002ba04dd522402e500008788c9f8832000000010f905a83bdc7f7c81a000008d41870000000000004d401909e3b00008c08f20800039461a3400002c135c20000ee6000002be065d1c2879e000099a931d80
  | 72 => 0xed33cac6a0cb748f173532864423396df25d2186912b0f4e09a40000eb0a03c000083ec3bd073a02d2080041f000000006ad921f17a710c25368f3e00000a50000000015ba000055cc000249200004598000076e48e450cc0000e6e2cda31d4eab033c01f097fc23300000de00001062925a410c0000000000000004cdd29ea3c23efa8d280000000000006f0fd800003eb000000718512000000002b3217a402400000000000000000000001d8c00004cc44b606834a8c000000012130aaa94a85dd83ef48e20000b5102320000559c127a21e132200004bc908138f400006939298000044c04258000114000000000f9c2f94179800008b900006a390d70000000000007d78dae13c4000000000001246000114c867200005ed033c0d880000199000000003ca22b50e6800000432000000000001a1e2c9489880003e3600005090000000075640000000112803252fb98cd3c5467f00000ad215781fd879913c833281d70e241620402238245770000225c0000000000000006bc0000155b000000006838000000020110a2a3863ae2000000021bd2d5c00010be2585381e374c8a10000000074c03f2800014c80000000000039ac39ac0001e4514fc5aec6b380002a0c00000000eb918026d44f2a9f470000000032310aa3cb26764be202f636fe85b4e3d8eab0000000091e17cc3ff800010d101793ca000000001fda4a2e000000018ac489e0000000035e00000000cf2000000000000000051514804c0c0001a14000086b0da78ec4000085040000c2b3de838900239d8500000000f5c80000000000000000000000000000000004128088886419b9120c2edc3cc1d8300002d640000dab30060000ccf983800003d780000000188a04a4e2ca5f9180c000000021030fee99680000952432e0000427000000000000991000000000000f8e891f00007950000035600000000bba18c727705b7400018523c16583c00000004bea6228adf87e92ff4339c31d80000000700ccbe80003e1280500000000379400000000b21354600000001a5b0000744c0000000074000000002428485412a8000000019bc6258fd79443213e00000001c431d1a85e46359a0d344094d039d922f1f9a77447be114900000000d4b8d3d034237d09c980001b62895000000004a082744ca1800049000000c5523594b3800000ce00001a7479e84ed00000000133800003310c2e7a944f30000000089c400003db00002578000123a00003630e84945800000000b551d69208a33110c70a2e26824254000000031507520869247f2cb82ec85b4896d09ae00000000000040e00000000000178420a00002662173e0000000197346743d0c8d708160af4989c0001f1000000000000234900000000bc10dff11740000ff69b4d000000000000bd9000000006259f8118384
  | 73 => 0x88be8097a2c5407d800000000000000000022ad1132000070b80fa00007d7c00002c40c0a775400020920000810864f179026b026551169a8f2f8400009d0000031ae27b044287ef363800000000000347a8cfd1c9219f202837f4fe4800000005ac0c92800547cc2910b5696d64ca855c49da0ea82aba3169163a1ab1a5c0b9c000000037ea0000d08000000000e700001d5f007e0000000251248bc44610ec02d40000000048581cc0dde8f70592000039b2066400004ec102498280d706b10b9e03400002132010a723d05b0aef2a380000f21170442348ce409b82e639ca70cd204a119203e8ff044b9e0c07ea6ea8e768000000000000000000426236800000000000000006f284490000000047e084d0000773400000000000000000019d700000000a2d0581473c3174cca9a653f845430f75031e39cc740cf4b8e422a64204c68000002d5651b442a0000203830b08e9a1d4256c000022a093f4b90646c000000001840001336000015c259303b0185b00006844b909b63000085546dd80000000877000000001e7200002a080000000391c2ee8000103a66986bd94170000911000002b9000000004fa26294af80000e578d02000081cd311129905ea00000001fc5221e00002130d2f20b400000001d660000000000000000000000011894dc00000000080000015120000c23a0d2303000000001c0d2b625750c4d0e6a2ff055107dc006300000f80000000013be0000e648ba70e8e1f1c378917d00001a8868a0000000031d800003b72e9c3ea0000234600006cb800000000000000000005ad000039451fe800000000e8c0000e831ee804f80000000000060d49760dd826ca51a881e867c29ec8138d9900000000563800015cb3ae85a550c49de64bbe592c21e06213f900fc000003a2119c00011a68000000000004a6000003a488bc0000000000097c01ca8000000025b80a28000000000000000000000029a0000000000003e5496f180f00002fc506380004832239c2b28cd93c46000024f07782a8600000000000102a12708bb201006aa00009e200003aba419c057253600001eb0f9f854d093a7d6525e258d06501b0000008801fd63900000000046ea00010d01b0700000e4c7a480002fe02f4d1c507a239d26b00017200d017c38f0a801c2c000000001c11ee625180000522a4e521ae0000bdd20190000980c0000000000024149568697084e5d0c000000000008604000220e16e24e846e800004058000112380003cbe96e0000245f00006b80891856b2f0c5a3c0000000168a0000764044a22bc6a0501505ca00000000d21000003644e792a48000479868a000020800000000122880001dd800000000000467a000070f04d8175842f05f602d000004844abe000004762dd4fb7016b000053d05000d8b03a0000060d8
  | 74 => 0x25c14c58851cc488000000024c0000130637d000000001963167600000002268000090007df1667302685cd0361e20174000000000b81000000004ec20cf00004e347409a0c3a5a5fb069e165b139c77480000cbb42760000dd000001574000000000003d183ae000009aa0000000063e00001336077400002c328a60000fa0000049fc54f112f8ea3071800000001247000041a0000000044f87774a2d82500000000000000000d9c615c82e162e0e0082f480685053da82534dfa0000000000000000000000000007629d2919e474d821d02ab00004f5000011a121d0004467c9e1239b82f2440d00003cba09d0cd9a3b846f2161cc7c0b49450c5c3861280004a3661f47410f7b1264796ce359dc844287ecc000153910688700ea70000000000010ff800039aa4ddc00023210000000070f80000000000000017bd1b3e0000000000041b400004f5800000000570862800000000000a778000000025ec41d9af34c727f64dda90d44612148c820865d267c32cc5b995cc06587ac09580857027258fce808081452a000000011d1000085d00000bd542b001d4206908b153600011a424b3231a98352b4252206e400000000ffd000078b400014b43b2290d00001d880cb488580000c94475626c8cb31ddf20fe8e8cb638f301cec66bceb10000000000005ec000031ca00006e31d4108ac69ec4751e9d2d0094bc0001a3400000000ac20bea00000000000000004064d240000000000090ec000084347e00000000000011f611000001736000016c05c80e700bde42fc99412c907585a040001bda00005ec4976925e000000004a20883041e48c881811a8076c12247e890a82c44000108905c4127c13dc024000016d800011d0830f000000003188000000000000000000000000000000c4e0000000000005b63bea0001275000000001a8c000193700002154bfc97f438f085980001d7600004eb4000110400003cc413d80000cc264d9135800000000000f908f2c39083bdc6fd9c880000167400006960000000000018eb331c44880301cb5296a11bd051a4a9452c00013151ce3000000000000ca70772000007a03f4050000000000000442278c8000198142a40000af2235000000000000000030b24a70f1980001baa3bf0000017f00007d5000003e3000000000001ff93fd647748ac004425420000000000013565f98ed099e047be4f24000000023003b40bd018440000000125a003323308ef080b899c00004b58000011e02400000000000015768b0c0000000000098141c084a401fa81d40db85712da06ea00000000036c02907a30000000000000000446000000000000000000000000000000000000006349bfc000021e800021a3304e1e4400000002f7254900000000000050647260c9f16900000000000008c4661c5a68a0d3f10
  | 75 => 0x4c740000000000015a8000119d3b6029d521799d3000000000000b1700000000827a1d34a0c00008f7880126c09388000000000001bb00000000000036600000000000002a4464a6150b8a00006b3000038d20000620138c172a63a497f234e317267945fe900806fe8f18b5b24d102ce33900bba21c116290745888f8004608dac3e60000419053a4dd88000108447c8c8618dd01362194000254e44ba03782b18e33000000006740000000022742678b5c0000963033c80000000846066d8000448a00008b215601d200000ce01c2b07160000f079f92000000002801eb203ce376400009472970000000000002c66144513e8000011a601c00000000000000000022ab000000000000ead1f5400000001a27000071989f08000325430a88a6978e00a0945061b1ccc4780421517b02aa04e60000000194d35c84894e3f07fe43d0911454289c7457682407fca39100006ad40058000175e00003c5a27e0d5a000088e233817be0000000112b193462084c098860000000000011df41a000011888000000000000001e1a0000000087c0000232c544000023d8463c241108a10e633d6187918200001ac686d11b88d59079046506248480454a000013919791844000000000310000000011e000000007634000000012f888800001521000010300000000066400000999007000000012a9a5cf000000008411e5e060e4938000244e226a6f3461895b449fa54952881c011aea92fd30c83b0214c6400aa494b936463f8c000139b1a367eecca41e2b1c6c68d40fb942219947530f6f8da70000512d184000027ae65d4c82800039d68fa491b80ba00004530a118c27000038a00e98164049c16100a5876f238640e48f1154247c22e50000253a14d80000000154f0c4a203c531800000006c180000000000092688c920dd1924895c000166c000026cc95c800010307b1c7ed2410000000000000e050000388823889614cdc43380000b761e4026c4000226f10f200008bd9cd7325c000124b80000000000082f0f1100006f843cb82201ec63da059f0e6d00006ab8000000011d220400001cb2171e3e507df800000006df1150800009566ee00001a3b00000000b4c00000000000000000000000000110d0000000000005238000267217c401680000000104c8a7810b23d447a08009112000069f0948a208352c1998371000039363d900001d8619f600000001d84000045441e0189e0000192442c8000163245041f100903e9470a8a13a34439ee36b4c8491ac18b62720a7e80000000628800007a545280f7000003d73d446bb8c339dbe00000000aa80000318a037400000000ab03894d58a4c036b690288689e7217a20000000000000007d0d0cc8000449a6fad0ef8000000041a800012e5000085ac0000000464a0000000
  | 76 => 0x680004b2a00011f7129d0000082c63c000000000000cde101b1faa5e0c5329fc000000000834800009f4000000000002fd2000073a8359000000000000464000000000000000000000002fa8000000067f40000be9000087489a180003bce446c01d80000000596400000000000056c0000000000000000000f9e48a800000001c5e00008de8c2a800000000000ce580000000000000023ba00008da8e9521bc0000781c000000000005d29281122108ba000000008cc29a23bb8d2000000000000000023050000000000006aa02d0746c00017a20ad008bc000000000004f791c3800012b81efc362800000000000617000037743cf400020aa0cca82a000000004b6c15c80620573000094605aa972a01fc000009b18f6000085640002109035234d40000000231497410d980002db46210806159100006620fbfa1460fae62b8b378000196e4f34dc71f740000114400016d9000022dc799922d199889488e08000000096ac00000001edc3d3400000001e4669207e313e548b413ec10b237343f60a7c1348a8305f622c04179a9c1fdc4f6c00006752ae070bc000266d000035205db13090000000102b800000003bc42e800000000000000000001c5446d400001090000000125d8000000000001f720bb123c82b504d9c5b22c447ec0000b6829823d8800000000000000008085ab000000000fa00001e941cad09c0f210e986b3c46300000000000000000f000008b7800009292b060000c3899900000000000021220c4690613099b1b43c80000f5b22ac21523458000191915bc000000024323a7a2c34502178a45ac335c47ea4414788000000007d44aa230e493e96e100008ea03430000238c897032c222c3afa95dcba616a703dc1e709c402fd40b80674271a15a307202ac2b49f6627d80000e0a800000008edc00010570000774000000003fbc00000000000000000006d984df1f7400002e000000bb8799c8bf9e2526e455d00ba207b00000000000000022b23e08456802027aa3b1ccc500000000983c0000000000061b4b208000000061a43410eb40000000080980001a20343015a20d1278c000042c00002bf6000066414fe000084bcfde9c45334a5ebca89800000000000a48a196422c34108ff1811373c38293230b0c3e0e092d2b50000422088f0b838000000000012a90c2f124805e8dc205e21f8000000000642365a58391f8a2500000424d1c01056000000001199a873f360000452073307ba0000c681f990000000000001422c5600000000bc3000000000000de231e259992198c1f4b16571c6f9a123119a526d12408d02efc48b80f080000000000000000000000000129d800020b0486cef92135475e48cc1be196812ba0000000040501f20000000068100000000000000009b40000afc80000fb80000a788000000
  | 77 => 0x3000007871a62000000980000000438c79dc12c0a370c4082c896d259d087e41e00000000000009e44a700001b0a0000000069320a252ac74621cd41d47e1c7e220b0298a0000000054200000000000232632b60000000000046b03d207c7000000000000e7c800000000000000000000000000d82800037a261a0000207739ea6a2cff2a1330000000040d95a200000001321800042360000ddf1150125e0000a9194382d0c841cd5a000000008b600000517191808dc000145e000053b07fc175c0ed66d600001e9200007adc97b80002f4c00000000afc17f66bb42660000000009f00001cee3b7e865470887a71aa403543b814aa000082f000023a934707fb033692571c4e94680000ff13542000114186140d6e87f11779f2025c271607a110e10000000000000000e1400005df000029b20000d3c8000000017f4d4a80002d486308b760000108c7c14039928e000000008b6000000000000000000047a000003b28cf82e524850000000001047810c5b81d700001ed03f700000000000000024a73622000059a80000eaa14a51d2931119ee193402c9c70386c2e1458e20650d2a0000d868dc3395a297cb6c00003e5a000000006ae000017a4f4d211e45660000966000005ba850cb65115d39140a78000203027305c50e11800041d05e4cc301be200000000000000000000000000000000006d48000000040a28bd020300000000000067d000000000000aa9800032aa45a12e598e2000043c4ebd25d42b1a3e252f000002d3400000000e4a00003af923a8b051bbe3c9c000187c2cee8e4c73f800000000000ce6800000003534000000000204ce0648136d04c06848f850000000000000001ba4000000000000be719260000000000000007c54a8f0000172c93d0f9da09600000000000063e31ac00005b3257f000000000000000000000000001183000092e0000000030160ce084780000000623c9d79d6700000000000000000fa5e70000230d41e6000024889e500005be4bb50000000000000000b270000861ceed000009d66200c8d01b400007310ff3800017520000f2625ec000043ac00000000000000000000000000000000003e41f8a00001419dba454600a4abc000019a000006ea000013bc94800000000000036d4000034f19e600000000000000000010c30e2f26d4000087900000c0e000065000000000000000012b14472592805c220b000000000000000147e8a780388c771f1a1b94d6e8000355032f02f90000151a00010558000267a8004d049d182b6c00009f3a0e50484261c941885e00000000f1d00003ffc0000874800046cc000000000000000000000000003de22cd80000000000000000000000452000000000e03222200000000a2141fc000045e00003aee0000b968c38160473ed0a8131004be0000df
  | 78 => 0xf3015a179a702cf1f0aa4191443d4c60262d05642818a4a02121cf200005b712f029c21d7c210000000860acc0000dd70000968d229800000000000a5700003346000000000000000000122c800024b00000000000000000000000257847c4426803282fe065e5194dce9a3e29be0ebc0000e230000000000023d100000000000000000000390af1073500002ea109680000cde69a800000001bf0459467b00004308528435f0b6b29aa6a110d42404191e0000b010cfd4c645d2507783113aa8000015e861b4bae3f050ca1f114a02293003925822ac46ab52e8a18342261630184983014e61b9c21c0000107451f4e1a8000011e49a00000000000008d8f0187ec36080000000000015be000000000000000467002e0000000000000000000000000003488d801e4c04b80001b61000068388269ab726d800000000000000000000000000000000004a416bc00001e08b1f00000df453092e31428003e50bc8f7229c197e18b4b3224d8296014dc90c1ee300006e040000000101800003bf199c153e2144de2829827ec8c380000fb90000000063f01fd41b078d0000147900008b84f9e94e8320c000000009403d7e0000000000003cc16c800001dc3768678899f9bf300000000000000000006814af62356477640e05528000090600007e807323052016020da2fc000000f520b1d4a00007af0d7b00000e8a5b3800000000a262b550c7a2e70bb200000000000000000004f8135105b828b472b95571bee7a2446f07061d9695b077b0c7d00002aa0fdf8d53268e31991f21934363200005e7984e0dd437d90cda65d1cb80000de18000000061989670d1c15e62fdc7b596072e9e0000d1b198b21244edcb02a1a90000000101a94d8429e000008c800000008a5ccf800000d0835f43c5184940fa488105980001f9297ec20d103235d200011b100002ab0000021116e714f886dc0001193365800008568b4a1e7e7b6c000000031b200000001daa000090e4000000043303b947968f283146143c82a24fc21de00001ea8ded085c00007c780001c0800006b2800000000cdc00000000ed0220419f949800000000549034c292a0000685800006482ff027297c534ac24ac00020de00000000000000007422f94e3780000d580000bc000001ae800002e59dd80000000036a08d8089e0000000231600000000b2c000037f000005d70000000000011fb9e30485895e89338000269841c4000002500000ea4d128e540dec403ca98800025fe02fc0001ff530de866803c0736240873b000000000000542c000000000005f5d22100001d5400000000c604a587bccb0a800037f63cb800012b724a80000b9e800009528bc4cdf1f424c603490efb0b1a00000fa474c000040d2000061d8377000000011cf8000000012680000000000000002c4800036
  | 79 => 0x6294000000000000000db3811c459a0000e8f800000ee8600d05800035d800000000cb4096200000000000304c68691c71f5b00008bac08f9b9a21742468c4a15a61a584d15022000000006678a1922370000834d0f88af93152733425190f40562269000021ce14ec0000000000039a46e4522c13693e54809d0938891096407cc91a120c132000000000000000000000001fd00000000000000000000000000000000000000000025ce00000000010830300004998d6e000030760000665880900dc296800019b0283497c427000000fc400000000cc227a00000059a6230af235b80000000015a2df8c58a1683b9e7a20c310d451dde64284eb800014609534000000021f48d7c000228800002c2000016bd46987440000047700000e180000f144902000106a2598370000011008000000069fc000000005a200000be801a000049e8e1100000000356c00000002c0c88d400000000000121c00024360000000000000000aa8681c00000004bf068200001627000046904fb084400002d74000000004de0000000000000008cb11490000000064e0c3c800022340000b4f0000000008608df220300000b282a4a634000028382ad852b00007f8c0000000000000000000fc7000000000001e8511fe48540000000052e026000000001f840000000000000000000000051b00001c64f0a1eab000000000000a6928168b140000000493c45bc000217141126becff88000294c2b71139107b346400001d2201c435a5120e2597a90000053c77d00001d400ee8e83800000000001070000023c20000296000000000000a8a8000000000010a48d42000000000000c720000178c0000000320800003dc80000b3600000fe13d64c7e0000cbb8000000002d4f9d1a160000000118d8000000022eca31000000000000000000036e00000cb680002f18000000000002e680000ba0142507f8000000016f100008fbc30085260000000000003d63a4a000043a84521bc8394c0000000142c5754000000048ac00000001d4f10708630fa0800000000a98c7e24df000000010a1259000000000000000049ae0ffc000057f4b94994c000000000000000d0102a000007434c28800000001f807aea0830000627448d9b891d940000000000013fe12640df9b010000000040883490000000104080004574396400017aa00000000000023947d0000000013aa051e74d000015050000000000000004ae200000000f3700000000ab30000493a000000000000000000000000000a7a864c19597ce000000007109d8f17820298c1880322b9a000047400000000872c000000047c6000000000d61686000000008450468794c74b144e014e00003000b8215fa38e50b803b80000000000000001b7e6680f45800000003b8502b00004536513c7db8f97494c0f309
  | 80 => 0x18265710b39284132888b92da8ce2000000000001e1500002e900000850403a000000000000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x863965d0e100431cb2a8708021c654d43840108f2ed28c200863765d91100431bb28c8880211d9db5344010c6ecba1a20084b47650d100431bb2a8688021c554d4344010ae2eb98220085b274cc110042d8ba66088021d454e3044010ae2ea18220085b2740c110042d8ba06088021789c83044010bc2e418220085b37448110042d83a240880218ed976444010c76ca322200847a76d4d100431db2e86880212e1d94344010c76caa1a20087195350d100423d3b4a2880215c5d73144010b64e998a20085b174cc510043a8a9c62880215c5d43144010b64e818a20085b1740c510042f13906288021785c83144010b66e890a20085b0744851004338baeca880215c9db6544010ce4edb2a200857173d951004359b2ec888021ccd976444010b62e7b2220085717599110042d93a4c8880215cdd56444010b64ec32220086b2761911004359b28c888021ccd946444010b62e632220084f276d5110042793b0a888021cc5505444010ba4e62a220085d17315110042f1390a888021785c85444010ae2eb31a20085b27498d10042d8ba4c688021ac1926344010ae6eab1a20085b37458d10042d83a2c68802178dc96344010bc0e4b1a20085b27418d10042d8ba0c688021ac1906344010bc4e431a20085e17218d10042793b6a6880215c9db5344010ce4eda9a200873364d4d1004398326a6880215c5d65344010b64e929a20085b17494d10042b93b2a6880215c1d95344010e66c8a9a20087306454d10043a9b9aa688021d4d8d5344010ea0c6a9a20084f27614d10042b93a8a6880216c9d05344010b62e829a20085e27214d10042f0b90a6880216c9db4344010b60eda1a20086b365d0d1004399b2e8688021ccd4f4344010e62a7a1a20085727590d10042b8bac86880216c5d24344010ea2a721a20084f37650d10042783b28688021d454d4344010d66eca1a20085b27650d10042d83b28688021ac1d94344010960eca1a20086b36550d1004399b2a8688021e4dcd4344010e66a6a1a20087925350d1004398a9a8688021e454d4344010e22a6a1a20085727510d10042b8ba886880216c9d04344010d60c9b1220085717598910042d93a4c4880216c5d26244010ae6eab1220085b37458910042d83a2c488021ac1916244010ba6e6b1220085d0735891004370b10c4880213c9db5244010b66e8a9220085b07454910042793b0a4880216c9d05244010b62e829220085d27314910042e8b98a488021d854852440109e4ed21220084f17690910042b9baa84880215c1d54244010ae4ea21220085717510910042b93ae64880215c5d73244010b64e999220085b174cc910043a8a9e64880213cdd932440109e0ec9922008751534c910042793b064880213c5d83244010ae4ea1922008571750c910042d93a064880216c5d03244010
  | 1 => 0x430421f3a4c7a90210f5d263d4810c3cc6a1ea40861d6350f520421f3a4c7290210f5d2639481087ae7b22a40843d731915204316b90c8a90210f9d0635481087ae831aa4084767118d520423d380c6a90210f9db4354810878eda1aa40843e7650d520421e3b286a90210fdd16154810878e8b0aa40843f74581520421e3a2c0a90211bdd95214810c5ac8a90a40864d63548520421eb9cc8290210fdcd641481087ce9318a40843d7498c520430f324c629021875926314810c3ce9318a40861d7498c520430f322c629021875916314810c3ce8b18a40861d7458c520421fbb686290210f5db4314810c3cc7a18a40861d63d0c520421fbb286290210f5d94314810c3cc6a18a40861d6350c5204316b24c4290219358e6214810c6ac9308a40865563984520431cb24c0290219658e60148108bce632e840845d73197420422f398cb21021175cc6590810a3ae62a4840852d7215242042963a2a5210211d5d661908109e2e130c8408479759824204278b8cc1210211d9c665508108f4e132a840843f74595420422f398caa1021175cc655081087ced2a2840845e73194420422eb98ca210211d9c465108108f4e0328840843d76d50420421ebb0a821021475cc5410810a5ae42a0840843e74d97320421eba6cb990210f9d065cc81087ae832e640847671197320423d380cb990218759253cc810c3ac8a9e640843f74596320421e3a2cb190210f9d0658c81087ae832c640843f74595320421e3a2ca990210f9d0654c81087ae832a6408475751853204332a90c2990213c5c0614c8108f2ea3026408669521813204278b88c0990210f9d3650c81087ae9b28640847571594320423cb82ca190210f9d0650c81087ae8328640847671194320423d380ca190211d5d6610c8109e2e13086408479759803204278b8cc0190210f9d2639441087ae931ca20846e72d964104236b96cb208218e55260904108f6eab04620843e74d94310421eba6ca188211b9cb650c4108dae5b28620847970594310430eb24a61882187591530c410c9ca6b10620864d53588310432ca9cc0188210f9d3658841087ae9b2c42086695298221042b2b8aa4108210f9d2639401087ae931ca00843f74586500421e3a2c3280211b9cb65900108dae5b2c800863554986400422f398ca20021175cc65100108dce4328800846d72194400423bbaac3180210f9d3650c01087ae9b28600846e72d943004236b96ca180211d5c5650c01087ce8328600843d741943004237390ca180211b5c8650c010c3ac9298600861d6454c300432729ac4180219354d620c010caaa7308600843e74d96200421eba6cb100219954a618801087ce8328400843d74194200422f398ca10021175cc6508010ad2e0a90400847576d4f100438aa9a87880211d5da51840108f2eda9c20
  | 2 => 0xca982210f1d1654c1108dee4b2a608846c72595304431a2a6c2982218d150614c110c70cbaa2608863865151304423d3b0a6982215a5c8534c110e36a829a608853a75d0d304431c32e86982214e1d5434c110c70caa1a60887185350d304423c3b2a498221561cd524c1109e4ea30a6088672751853044359aa0c298221ac150614c110d668630a60886b143185304433832c62982215c1d5314c110ce0ca98a6088791434c5304421fbb6a8182210f5db540c11087eec2a0608843d761503044317aa4c4182218b152620c110c5ea8b10608862c54588304431baa4c2182218d152610c110c6ea8b08608863454584304431a2a4c3902218d15161c8110cc8a4b0e408843e74d95204421eba6ca902210fdd16548110878e8b2a408845f73595204422e39aca902210f9d7644811087cea322408843e76d51204421e3b6a8902210f9d85448110878ec2a2408872b5448020443942a240102214e1d543c4110da2c718e20885347550e1044368b1c61082210fdd95415010c3aa8b18a80862d54588540430f322c62a021879d16315010c9cc7310a80864d639885404317322c42a0219398d6215010c9ac6b10a808655639845404332b14c22a0219658e6015010cd2c5300a80843f7458b530421e3a2c5a9821879ce6494c1087ce8312a60843d74189530421f3a6c2a98210f5d36154c1087ce9b02a60843d74d81530422fbb2a629821875915314c10c9aa6b10a60861d6498c5304317324c4298218b5926214c10c5cc8b10a60862d64588530432731ac4298218d9926114c10c6ac9308a608666629845304332b14c2298218e9926014c10c72c9300a60866a629805304334b14c0298211b9c865d0c108dae432e860852e721534304296b90a9a1821475cf65d0c10a3ae632e860852e721974304296b90cba18214b9c853d0c10a5ae429e86085367114f430429d380a7a18211b9c86590c108dae432c860847671196430423d380cb218211bdc96550c108d8e4b2a860846e721954304236b90caa18210f9db5450c10a3ce7aa2860851e731514304297390a8a18214b5c85450c10a3ce929a860847575185430431aaa0c2a18213c5c06150c108f2ea3028608639541814304278b88c0a1821475ce6550c10a3ee6b2a860852f725954304296392caa18214b9c86550c10a5ae432a860851d75d8d430421f3b4a6a1821475d65350c10a3ced29a860861e7694d430428f3b2a6a1821471d95350c1087cec29a860851e7314d4304297390a6a18214b5c85350c10a6ce229a860853a7014d430438aa9ec2a18214d5d46150c10c6aca30a86087155318543042d8b80c2a1821c654f6050c10a72ea302860863965181430438ca98c0a18216c5c46050c10d60c2302860843e74d944304237390ca218211b5c86510c108ece2328860847a70194
  | 3 => 0xc765909108f2e1b2c848845f73595424422e39acaa12214b9cb54509108ecebb0a84884f270d85424431baa0c2a12211e9d760509109e4e3b02848863b54181424422f398ca21221175cc6510910a5ae42a0848863454984424423a3aac2212218d15161109109e0e0b08848863854980424423c3aac0212218e15160109109e0e2b00848843e74d97324421eba6cb992210fdd165cc910878e8b2e648843e74197324421eba0cb992210f9d664cc910878eab26648843f76d53324421ebb6a9992210fdd854cc91087aec2a6648851d73153324423a3aac3992213c1c161cc9108f0eab0664884f071583324421f3a6cb192210f5d3658c91087ee8b2c648843c7459632442a6b90a719221531cd528c91087ce9b2a648843d74d95324421fba2ca992210f1d1654c9108eee2b2a648847b70595324428eb98a8992211b9da524c9108d8eca92648854c73549324421f3a6ca192210f5d3650c9108eae3b28648847970d94324421fba2ca192210f1d1650c91087ce8328648843d741943244237390ca192211d9c4650c9108f4e0328648843e75990324421e3aac8192210fddb540c91087aedaa0648843f76150324421ebb0a8192211b5db520c910c6ea9308648863454984324423a3aac2192218dd51610c910c68a8b086488657535843244333a92c21922199149610c9109e0e0b08648863b54980324431c2a4c0192211e1d5600c910c76a8b00648863854580324432da9ac0192219ad49600c910cd0a4b0064884f071580324431c2a4c1a0a218ed506050510a68eaa0882885b070504414421f3acc998a210f1d564cc51087eedaa6628843d76d53314421fbb0a998a210f5d854cc510c6cca2a462885657214e314429b3ae8718a214d1d5438c5108eeeca9462885547354a31442b93a8c118a218e153604c510c70a830262884767614d31442b2b90a698a21c5d50534c510a6ceba1a628863465d0d314429a3aa8698a218d195434c510e28a6a1a62884747654931442aa39aa498a213c9d4604c510ce4ea30262886b35418131443582a0c098a21acd0c604c510d6286302628843f76d50314421ebb6a818a210fdd8540c51087aec2a0628862f5498831443162a4c418a218bd51620c510c58a8b10628863b54980314431c2a4c018a218e15260c8510c70a8b06428866852583214421f3aec890a210f9d4644851087cedaa2428843c76d51214421f3b0a890a210f1d85448510e4ea8908428872454484214431a2a4c3a02218dd506150110a70eaa0080885b071500404421f3acc9982210f1d564cc11087eedaa6608843d76d53304421fbb0a9982210f5d854cc110c74ca2a460885697214e304429d3ae87182214e1d5438c1108f6eca9460885587354a30442b93a8c3182215c1d5318c11087ce9b2a608843d74d95304421fba2
  | 4 => 0x5ae5b06a88843f765505444297390c62a2214b5c86315110a6ae2318a8885397018c544428f398c42a221475cc6215110c5ac4310a88853571188544429cb80c42a221475cf64d4d10a3ae6326a68843e7498b534421eba4c5a9a210fdd162d4d10878e8b16a68843e76d51534421f3b0a8a9a218bd536254d10c58a9b12a68862f5418953443162a0c4a9a218bd936254d10c58c9b12a68862f641895344316320c4a9a2193d8c6254d10c68c9b0aa68866462d85534431c326c0a9a219a18b6054d10a3ae7aa0a68851d73150534422fbb2a629a21531c95314d10c5ea9310a68862c549885344317aa2c429a218b1516214d10c5cc9310a68862d649885344317322c429a218b5916214d10c6cc8b08a688635645845344333312c229a21995896114d1087ce8308a68843d741845344237390c229a211b5c86114d10c74c8b00a688639645805344335312c029a219a5896014d10ce2c2b00a68843e74180534421eba0c029a211b9c86014d108dae4300a68846e72d974344236b96cba1a21475cf65d0d10a5ce5b2e868852d72d97434428eb98cba1a21875cc65d0d10a5ee4a9e868852c7254f4344297390a7a1a214b5c853d0d108dce432c868846d72196434431baa4c321a211d1d56190d109e0e0b0c868863b54982434423c3aac121a213c1c56090d108dee4b2a868846c72595434423bb8acaa1a211edc16550d1087ced2a2868843c76551434421f3accaa1a21475ce6550d1087ae732a868861d73995434428fb9acaa1a214bdc96550d10a58e4b2a868853771595434429db82caa1a210f9da5350d1087eeca9a868843c7654d4344297b92a6a1a214b1c95350d1087cec29a868852e7214d4344296b90a6a1a210f9d06510d108dce4328868846d72194434421f3acc821a210f5db5410d1087eec2a0868863454984434423a3aac221a213c1c16110d10c70a9300868847875580434427838ac021a210f9d263d491087ae931ea48843d73992524421fb9ac9292210f9d2639491087ae931ca48843f76d0e524421ebb687292210fdd9439491087aeca1ca48863664586524431d322c1292210f9db545491087cec2a2a48861f54d8d524430e2a6c6a922187d506354910c38a831aa48843d73d91524421eb98c8a922187d936354910c38c9b1aa48861f74d8d524430e3a6c6a92210f9d0635491087ae831aa48861f6418d524430e320c6a9221879d06354910c3ae831aa48864d7218d524432ab88c6a9221965c0635491087ceda1aa48843c76d0d524430fb1e86a92218718f435491087ceca1aa48843c7650d524430fb1a86a92218718d4354910c98c7b12a48865463d85524432c31ec0a92211bdd95214910a98e6a90a48843e7498c524421eba4c6292218798d4314910c3ac6a18a48845e73d97424422eb9ecba12211d5
  | 5 => 0x852d7214d43c431d328c0a1e211b9c86510f108dae4328878843d7399352c421fb9ac9a96210f9d263d4b1087ae931ea58843f76d0f52c421ebb687a96210fdd943d4b1087aeca1ea58863a6458352c433930ac1a96214b9d35294b1087ce931ca58843d7498e52c421f3a0c6a96210f5d06354b10a5ce9b12a58846f7654852c421f3a4c6296210f5d26314b10c3cc6a18a58861d6350c52c433930ac029621179cc6510b108bae6328858843e74d9732c421eba6cb996210f9d065ccb1087ae832e658843e7499632c421eba4cb196210f9d2654cb1087ae932a658843e74d9432c421eba6ca196210f9d0650cb1087ae8328658863a5458041c42b2b90a718e211d9d8534c710acae429a63887145350d31c423b3b6a498e219654d600c710cd4a4b00438852e72d5240c421f3b4a8a06210f5db5410310a5ce5aa0818862c6494920c4316322a490621995486148310cccc4b0ea908669629835484338b0cc1aa4214b9cb5495210a5ce5b22a90843f765505484338b0cc02a4219c58660d4e10c74c9304a70863964982538421f3a6c4a9c210f5d36254e108beeca98a70862e649885384316b24c429c218b9916214e10c5ac8b10a70863664584538431ab22c229c21999896114e10ccac4b08a708669629805384338b0cc029c211b9ca65d0e108dae532e870852e72d534384296b96a9a1c21475cf65d0e10a5ce532e870852d72997438428eb98cba1c214b9c853d0e10a5ae429e870846e721964384236b90cb21c211b9ca6550e108dae532a870852e72d514384296b96a8a1c218dd506150e10a3ae732a870852e729954384296b94caa1c2147dcd6550e1087ced29a870843e7614d4384297390a6a1c214b5c85350e10c6cca30a870846e721944384236b90ca21c210f5ce64d4a1087ee6b26a50843e7498f528421eba4c7a94210fddb43d4a1087aeda1ea50843f7650f528421ebb287a94218d99161d4a10ce2c3306a50852e74d4a528421f3a4c7294210f5d26394a1087ce831aa50843d7418d52842973a6c4a94211bdd95214a1087ce9318a50843d7498c528430f31a86294218758d4314a10ce2c3300a50845e73194428422eb98ca214210f9d365cca1087ae9b2e650843e74197328421eba0cb994210f9d2658ca1087ae932c650843e74995328421eba4ca994210f9d3650ca1087ae9b28650843e74194328421eba0ca194214b9cb549061087ced2a2830843d76d504184297396a820c218b1925248610c58c8a92430866952181218431b2a2c2204215a5c8538c2108f4ec29a61085697214d308438c29a86984211e9db524c210caaa6b086108666525842084297390c7aa2214b5c863d5110a6ae231ea8885397018f544429ab8ec5aa2214e5c362d5110c5ec5316a88852e72d875444296b96c3aa2214b9cb60d5110a
  | 6 => 0x82d4b9ec8900415a5d66448020b54e9322401056b7559120082d53b0c890041aa9d86448020d56ca322401072b6519120082d4b98c8900413a9db54480209d4ec2a240107295415120082e5398a890041725cc5448020bc4e22a240105e17115120082b4bacc6900416a9d26348020b52e931a40106a86498d20082b5baac6900416add16348020b50e8b1a40105e37158d20082f038ac6900416a9d06348020b52e831a40106a86418d20082f1388c690041785c463480209d4eda9a401056a76d4d20083353b6a690041cad935348020e50c9a9a40105697594d20082d53a4a6900416a5d25348020ad4eca9a40105687654d2008395b22a690041ca1915348020e96e6a9a401074b6354d20083a431aa6900413a9d85348020ad4ea29a40105aa7414d20082d4ba0a690041789c45348020bc2e229a40105aa76d0d20082d43b68690041aad974348020e56cba1a401072b53d0d2008394a9e86900415a9d64348020ad2eb21a40105a97490d20083a4a9c86900413add943480209d0eca1a40107495350d2008355bb286900416a9d94348020b50eca1a40106a87650d20082543b28690041aad954348020e56caa1a401078b7350d2008395a9a8690041e294d4348020e52a6a1a40107895350d2008384a9a86900415a9d44348020ad2ea21a40105aa7410d2008354326c2900415a5d66148020b54e930a40105a97498520082b5baac2900416add16148020b50e8b0a40106a86458520082e5b9ac290041721cd6148020dc2c230a40104ea76d4520082d5ba2a2900416a1d151480209d4ec28a40105aa7414520082d4ba0a290041729cc5148020b92e628a40107615114520082753b482900413a5da4148020ad6eaa0a40105687550520082b53a882900415a5d44148020ad4eb98a401056975cc520082d53a662900416a5d33148020e92a798a40104eb764c520082743b26290041d254d31480209d4ec18a40104e9760c520082b53a862900415a5d43148020b54e818a40105a9740c52008332b14c3aa6219a98960d5310ce4c2b06a98852e72d5254c4297396c8aa6210fdd95415310ce4c2b00a9886726158353c431b324c329e218d5926194f1087ce9b12a78843d74d8953c422fbb2a629e218b9926214f10c5ac9310a78862e6458853c4316b22c429e219958a6114f10c74c8b00a7886396458053c4335312c029e219a5896014f10ce4c2b00a78846e7299743c4236b94cba1e214b9cb54d0f10a5ae5aa6878851d73d9743c4297394cba1e214b5ca65d0f10a3ae632e878852e7214f43c4296b90a7a1e211b9c86590f108dae432c878846e7299543c4236b94caa1e214b9cb5450f10a5ae5aa2878863b5418143c428eb9ccaa1e214b9ca6550f10a5ae532a878851f7359543c421f3b4a6a1e210f9d85350f10a5ce429a878
  | 7 => 0x7a18411b9c86590c208ece232c861047571196430823d380cb218411ddc56550c208e8e2b2a861047671195430823ab88caa18410f9db5450c20a3ce7aa2861051e73151430829b388a8a18414d5c45450c20a3ce929a861046d751894308316aa0c4a18413a5c06250c208f2ea3028610639541814308274b90c0a1841475ce6550c20a3ee6b2a861053771595430829a38acaa18414d9c46550c20a6ae232a861051d75d8d430821f3b4a6a1841475d65350c20a3ced29a861061e7694d430828f3b2a6a1841471d95350c2087cec29a861051e7314d4308297390a6a18414d9c45350c20a6ae229a861053a7014d4308386a9ec4a18414b5d46250c20c5aca312861070d5318943082d4b80c4a1841c654f6050c20a72ea302861063965181430838ca98c0a18416a5c86050c20d50c4302861043e74d944308237390ca218411d9c46510c208eae2328861047a70194430821f3a4c7290410f5d26394820c72a9304841047b75582320821f3a6ca190410f5d3650c820c3ac9298641061d6454c320832b29ac2190419554d610c820cb2a7300641043e7498e510821eba4c7288410f5cf645442087ae6322a21063571191510821f3a0c6a88410f5d0635442087ceda1aa21043c76d0d510821f3b286a88410f1d943544208eeeca88a21063564544510832ab1aa228841475cc5490420a6ae22a482104e97098a410829a3a2a3208413a5ca60904208bce632a821045d73195410821f3b4a8a08410f5db5410420a3ae62a0821053571150410821f3a6cb988410f5d365cc420c3ac929e621061d6454f310821fba2cb188410f1d1658c42087ee8b2a621043c74595310821f3a0ca988410f5d0654c4209d2e03126210664625453108274b90c0988419c544604c42087ce9b28621043d74d943108274b84c4188413a5ca600c42087ce931ca01043d7498e5008316aa4c520041179cc65100208bae6328801046f7558a300821f3a6ca180410f5d3650c02087ce8328601043d74194300830eb24a61804187591530c020c9aa7310601065653584300832aa9ac218041c354d43c80208daed29440107195350e200823cbb4a5100418bd976448020c5eca322401046e76d4d2008317b2e86900412b1d94348020c5ecaa1a401070d5350d20082b4bae60900416a9d33048020b52e99824010749538c120082b4ba860900416a9d03048020b52e818240105e2710c120082f0b8860900418ed976448020c76ca322401047a76d4d200831db2e86900412e1d94348020c76caa1a40107195350d20082b4bae64900416a9d33248020b52e99924010749538c920082b4ba864900416a9d03248020b52e819240105e2710c920082f0b8864900416add12148020b50e890a401066975d9520083353b6ca900415a5cf6548020d56cbb22401072b65d912
  | 8 => 0x45410520c58a9310829062c545884148274382c420a418e1526010520c70a8b0082904e872580414821fba2cb98a410f1d165cc52087ce832e629043d74197314821f3acc998a410f1d564cc52087eedaa6629043d76d53314821fbb0a998a410f5d854cc520a3ae62a662904e87058b3148274392c198a410fdd1658c520878e8b2c62905557114e314821f3a6ca98a410f5d3654c520a3ae62a2629043f74594314821e3a2ca18a410f9d0650c52087ae8328629043e75990314821e3aac818a410fddb540c52087aedaa0629043f76150314821ebb0a818a418bd52620c520c58a9310629062f5458831483162a2c418a4193d4d620c5209d0e0b10629066562d443148332b10a218a418ed52600c520c70a9300629063b54580314831c2a2c018a4196d4d600c5209d0e4b00629067351580314833828ac018a418e1526088520c70a8b04429043e75d91214821f3a8c890a410f9db544852087cec2a242907275448421483922a24210a418b15262d0120c5ea831280905387550040482d439280202410f9d664cc120878eab26609043f76d53304821ebb6a9982410fdd854cc12087aec2a6609063a6515230482b8b88a7182414e9d7438c120a70eaa1c609056a7518a30482b43aa65182410f9d3654c12087ae9b2a609043f74595304821e3a2ca982418b153624c120c58a8312609063865d51304831c328a8982411e9d8534c120ae2e229a609071b5414d304829d3ae86982418e197434c120a70eaa1a60906386550d304838c29a86982413a9d4624c120cd4ea31260906ab5418930483542a0c498241aad0c624c120d52863126090668658c930482b43aa64982419a195324c120f1286992609043f76d50304821ebb6a8182410fdd8540c12087aec2a0609062f5498830483162a4c4182418bd51620c120c58a8b10609063754984304831a2a4c2182418dd51610c120c68a8b0860905387550f2048364b1c65902414b1d54388120d92c7184409043f76550540830eaa2c62a0418d5516115020c3cc8b18a81061e7458c5408326b1cc42a0419598e6115020caac7308a81063664584540832b31ac22a0419558d6115020cccc4b08a810659639805408338b0cc02a0410fdd161d4c20878e8b0ea61061e73992530821f3a6c4a98410f5d36254c2087ce830aa61043d74185530822fbb2a629841875915314c20caaa6b08a61061d6498c5308317324c4298418b5926214c20c6cc9308a610635649845308333314c2298418d9916114c20c6ac8b08a610656635845308333312c2298418e9926014c20c72c9300a610672619805308338b0cc0298411d9c465d0c208eae232e861053671153430829ab88a9a1841475cf65d0c20a3ae632e861053671197430829ab88cba18414b9c853d0c20a6ce229e86105357114f430829d380a
  | 9 => 0xae2318a8905397018c544828f398c22a241475cc6115120a5ae4308a89063561184544829cb80c22a241475cf64d4d20a3ae6326a69043e74987534821eba4c3a9a410fdd161d4d20878e8b0ea69043e76d51534821f3b0a8a9a418dd536154d20c68a9b0aa69063754185534831a2a0c2a9a418b1936254d20c6ec9b0aa69063464d85534831bb20c2a9a418d1906154d20caec630aa69066762185534831c326c0a9a419c1876054d20a3ae7aa0a69051d73150534822fbb2a629a41551c55314d20c6ea9308a69063454984534831baa2c229a418d1516114d20c5cc8b10a69062d64588534821f3a0c429a410f5d06214d20c6cc9308a690635649845348332b14c229a418d9916114d20c6ac8b08a69066562584534831d322c029a418e5916014d20cd2c4b00a690672615805348338b0ac029a411d9c765d0d208eae3b2e869051d73d97434829b38ecba1a414d5c765d0d20a3ae632e869061d73197434829bb8aa7a1a414d1c553d0d20a6ce229e86905357114f434823b388cb21a411d5c46590d20c5ea9314869046c7558a4348274382c521a418ed526090d208f0eab0486904e8725824348237b92caa1a411ddc56550d208e8e2b2a869047b70595434821f3b4a8a1a410f1d95450d2087ceb32a869051d73995434821eb9ccaa1a41875ce6550d20a3ee6b2a869052f72595434829bb8acaa1a414d1c56550d20a76e0b2a869043e7694d434821fbb2a6a1a410f1d95350d20a6ee2a9a86905347154d434821f3b0a6a1a414d9c45350d20a6ae229a869043e74194434823b388ca21a411d5c46510d2087ceb320869043d76d50434821fbb0a821a418b1526210d208d8eab1086904e870588434831c2a4c021a411e1d56010d209d0e4b00869063854983424831daa0c0a12414b1d54210920b50e0a10849043e75993324821e3aac9992410fddb54cc92087aedaa6649043f76153324821ebb0a9992418b994548c920acae229c649052e75d0e32482963aa87192415a9d4608c920c70a9b0264906385418132482373b0a699241595c4534c920e1ea829a649052e75d0d324831632e86992414b1d5434c920c58caa1a649070c5350d32482753a8c0992419a9d4604c920d56a830264906a8541813248355a18c099241aa50c604c92087eedaa0649043d76d50324821fbb0a8192410f5d8540c920c6ea9308649063454984324831baa2c2192418d151610c920c76a9300649063854980324821f3a4c7a8a410f5d263d452087cedaa2a29043e76151514830faa6c6a8a41871536354520c3ea831aa29061c5418d514823bbb2a228a41551cd511452087ce9318a29043d7498c514830f31a8628a418758d4314520a6ce3aa282904ea70d894148317aa0c4a0a413a9cb6050520c76a8302829045e73194414822eb98ca20a414d5c
  | 10 => 0x73343545300c3a921aa298061cc50d514c030ea286a8a601871143545300c333312c3aa6419a98960d5320ce4c2b06a99053671d5254c829b38ec8aa6410fdd95415320cd4c4b00a99066a6258353c8317324c529e418b5926294f2087ce9b0aa79043d74d8553c822fbb2a629e418d9926114f20c6ac9308a7906366458453c831ab22c229e41999896114f20c74c8b00a7906396458053c8335312c029e419c9856014f20ce2c2b00a7904767199743c823ab8ccba1e414d9c754d0f20a6ae3aa6879051d73d9743c829b38ccba1e414d5c665d0f20a3ae632e87905367114f43c829ab88a7a1e411d9c46590f208eae232c87904767199543c823ab8ccaa1e414d9c75450f20a6ae3aa2879063b5418143c828eb9ccaa1e414d9c66550f20a6ae332a879051f7359543c821f3b4a6a1e410f9d85350f20a6ce229a87905357114d43c831d328c0a1e411d9c46510f208eae2328879063a5458042c82b2b88a7196411b9d8534cb20acae229a659070c5350d32c832ca9ac0196414d9d3519472087ce931ca39043d7498e51c821f3a0c6a8e410f5d063547208eeeca88a39043e74d9731c821eba6cb98e410f9d2658c72087ae932c639043e74d9431c821eba6ca18e414d9c7549032087ced2a2819043d76d5040c829b38ea8206419958a61d5220cd2c5306a91067161983548829b38ea92a4414d9c7645522087eecaa0a910669629805488334b14c1a9c418e9926094e20c72c9304a71043e74d85538821eba6c2a9c4117dd95314e20c5cc8b10a71062d64588538831b324c229c418d5926114e20ccac5308a71063664584538831ab22c229c41995896114e20cd2c5300a71067161980538823b38ccba1c411d5c665d0e20a6ce3aa6871053571d53438828eb9ecba1c414d9c665d0e20a6ae332e871051d73197438829b388a7a1c414d5c453d0e208ece232c871047571196438823b38ccaa1c411d5c66550e20a6ce3aa2871053571d514388317aa0c4a1c41475ce6550e20a6ce332a871053571995438828fb9acaa1c410f9da5350e2087cec29a87105367114d438829ab88a6a1c418b9946250e208ece2328871047571194438829b38ea9214410f9da5450a2087aedaa0851053671d50428829b3a6a328c410f9d2639462087ae931ca31043e7418d518821eba0c6a8c411ddd9511462087ce9b2e631043d74d97318821f3a4cb18c410f5d2658c62087ce9b28631043d74d94318831a324a290c418d1915148620c5ca8b1081105717114e308823d3b0a6984415c5c4534c220e30a6a1a611064d535883088296b90c7aa2414d9c463d5120a6ae231ea8905397018f544829b38ec5aa2414d5c762d5120a5ae5b0ea89053970d87544831bb0cc3aa2414d9c760d5120a6ae3b06a89043f765505448296b90c62a2414d9c46315120a6
  | 11 => 0xc31ab22a3988619a54a60cc430cd2a4b06621867151583310c21ebacc8188610fdd5640c43087aed2a0621843f76550310c236bacc4188618b952620c430c5aa9310621846f75588310c3172a2c4188618b551620c4308daed290621862e64948310c316b24a4188611bdd9520c430c5cc8a90621862d64548310c31b324a2188618d592510c430cccc5288621866562944310c31b322a2188618d591510c430cccc4a88621866562544310c31d2a4c0188618e552600c430cd4a5300621866952980310c338a8cc0188618e951600c430c72a8b00621866a52580310c334a92c0188619c945600c43087ce932e421843d74997210c21f3a4cb108610f5d2658843087ee8b2a421843c74595210c21f3a0ca908610f5d0654843087aebb22421843d75191210c21f3b4a8908610f1da544843087cecaa2421843c76551210c317b24a4908618b1925248430c5ec8a92421862c64549210c327b1aa490861591c55248430c6ec928a421863464945210c31bb22a2908618d1915148430caec6a8a421856472545210c334a96c0908619c5476048430cd2a4302421867151181210c21f3a4ca108610f5d26508430acae3290421856572944210c2b3baa4210861595d52108430cceca908421866565484210c3932a24210861c95512108430c3aa8b1c801861e5458c400c32731aa4200619358d5210030cacc6a88801865563544400c31cb2a8020061a658d4010030e52a4a00801873151500400c21ebb4a9980610fdd954cc030c5cc9296601862d6494b300c317322a5980618b59152cc030e1a86a96601863664947300c31ab24a3980618d99151cc030c6ac8a8e601871543547300c386aa2a598061c555151cc030e8aa4a8e601845d7694e300c23cbb4a7180614e5d7438c030a76eaa1c601872a5454a300c394aa2a518061cad0d528c030e5286a94601876152946300c3992a2a318061cc551518c030ec4a4a8c601876152546300c399a1aa318061cc50d518c030c3ecba1a601861f6550d300c386a1aa498061c550d514c030c3ecb2a2601861f65551300c327b2ca49806193d95524c030e1aa8a92601865765945300c32bb2aa298061c5551514c030e8aa4a8a601863b65951300c31db2aa898061665d2534c030a72eba1a601863b65d0d300c2ccba486980614edd5434c030c76caa1a601859b7550d300c38dbaa8698061a6d95434c030e36caa1a601866b65949300c3c4a1ca498061c650d524c030cd6caa92601872a54549300c394aa2a498061e250d524c030e96c6a92601872b43549300c3a521aa498061ca50d524c030e9286a92601870943549300c339b2ca298061e450e514c030ec2a528a601871943545300c339b2aa298061cc951514c030e62a8a8a601879143545300c3b1292a298061d8549514c030ea6c6a8a6018
  | 12 => 0x990619a54960cc83087aeb320641843f75590320c21ebb4a8190610fdd9540c830c5cc9290641862d64948320c317322a4190618b591520c8308eaeb308641863654984320c31aaa4c2190619994a610c830ccaa5308641847775584320c31b2a2c2190618d551610c830ccca4b08641866552584320c31d2a4c0190618e552600c830cd2a5300641863a54580320c31caa2c0190619a949600c830c5ca9316a21862d5498b510c3172a2c5a88618b55162d4430c5cc9296a21862d6494b510c317322a5a88618b59152d4430a6ce9a8ca21853574d46510c2b3396a328861595cb519443087ee8b14a21843c7458a510c2b3396a928861595cb5494430acce42a4a21856572152510c29abae87288614ddd54394430a6ce9a94a21853574d4a510c3932a4a528861c95525294430e4e87294a2187254394a510c3932a2a528861c95515294430e4e86a94a2187254354a510c29b3a0a5288614d5d05294430a6ce831ca2185357418e510c2b3390c728861595c86394430e2ee6a1ca2185377458a510c29a3a2c528861995886294430a6ce9994a21853574cca510c23abb065288614d9d03294430a6ae8194a218572700ca510c2b8b8065288611d9db5454430acce5aa2a21856572d51510c23b3b0a8a8861599c85454430acae42a2a21853575d0d510c29bbaa86a88611d9db5254430a6ce9a92a21853574d49510c3932a4a4a8861c95525254430e4e87292a21872543949510c3932a2a4a8861c95515254430e4e86a92a21872543549510c23b3b0a4a88614d9d05254430a6ae8292a21857070591510c29b3a4c6a88614d5d26354430ae4e121aa2185717090d510c38bb9a86a88615c9c04354430ae2e021aa21853774589510c29a3a2c4a8861551cd6254430ae0e0b12a21866562189510c2b9b8284a88615c1c14254430a6ce9992a21853574cc9510c2b938664a88615c5c332544308ecec192a218536740c9510c29aba064a88615c9c03254430ae2e0192a218536740c1510c29aba060a8861599c83054430acae4182a21843d76950510c21fbb2a8288618b9526214430c5aa9310a21862e54588510c316aa2c4288611b5da5214430c5cc9290a21862d64948510c237bb2a4288618b9915214430c5ac8a90a21863654984510c31aaa4c2288619994a6114430ccaa5308a21847776544510c31b322a2288618d5915114430cccc4a88a21866562544510c237394cba08611b5ca65d04308dce532c821846d72996410c237390caa08611b5c86550430c72a9b02821866952d81410c338a8ec0a08619a5486050430ce2a2302821846e72994410c236b94ca208610f5d664cc43087eeab26621843d76953310c21fbb2a9988618b99252cc430c5ac9296621862e6454b310c316b22a5988618d99251cc430c6ac928e62186366454731
  | 13 => 0x5114530a68e8a88a29856472544514c21fba2c428a610f1d162145308dee4b28829846c72594414c237390ca20a611b5c86510530caac6288829863854580414c33828ac020a61c550c514c530d3286302629843e74995214c21eba4ca90a61275cc644853087ee8b28429843c74594214c21f3a0ca10a610f5d06508530acae2290429856572144214c2b33aa4210a61591d52108530d8ac6908429866852580214c33828ac010a614b1c95490130a68e2aa4809843e76151404c29cb84a8202610fdd95410130a58e4aa0809853471550404c333314c3aa0619958a61d5030cccc4b0ea81866562587540c334b14c1aa0619c58660d5030a5ce5aa4a81852d72d52540c29b38ea92a0614d5c75495030a5ce5b22a81852d72d91540c29b38ec8aa0614d5c76455030a70e0b12a81853870585540c21fbb2a82a0618b5526215030c5aa8b10a81863554984540c31aaa2c22a0618b9926215030c5cc8b10a81864e63588540c31b324c22a0619998a6115030ccac5308a81863664584540c32b31ac22a061999896115030ccac4b08a81866962980540c338b0cc02a0614b9cb54d0c30a5ae5aa6861853671d53430c29ab8ea9a18614b9c854d0c30a5ae42a6861853671153430c29ab88a9a18618e5516090c30a5ce5aa2861852d72d51430c29b38ea8a18614d5c75450c3087cec2a2861852e72151430c296b90a8a18614d9c45450c30a6ae22a2861851f73d95430c21fbb2a8218618e9516010c30c6ca930ea41863554987520c31b2a2c3a90618d55161d4830a5ce9a94a41852d74d4a520c2b338ea529061595c7529483087ee8b0ca41843c74586520c2b338ea929061595c75494830acce22a4a41856571152520c296bae87290614bdd54394830a5ce831ca41852d7418e520c2b3388c729061595c46394830e1ee6a1ca41852f74586520c2963a2c3290619958461948308dcedaa2a41856671d51520c2b2b8ea8a90611b9d85454830acce22a2a41856571151520c296bae86a90614bdd54354830ad0e0b22a41852e7498d520c296ba4c6a90615a9c24354830ad2e121aa41870f7350d520c2b538086a90615a5c04354830a5ee8b0aa41852c74585520c2a639ac2a90615a1c16154830ccac230aa41852e740c1520c296ba060a90610f5da541483087eecaa0a41862e54988520c316aa4c4290611bdd95214830c5cc8a90a41862d64548520c31b2a4c2290618d5526114830ccaa5308a41863654584520c31aaa2c2290619954961148308ece332e841847571997420c23b38ccb210611d5c665908308ece232a841847571195420c31caa6c0a10619a54b6050830cd2a4302841847671994420c23ab8cca210610f5d664cc83087eeab26641843d76953320c21fbb2a9990618b99252cc830c5ac9296641862e6454b320c316b22a5
  | 14 => 0xe8b0ca59843c7458652cc21ebb4a8296610fdd95414b308deeca90a5986365498452cc31aaa4c2296618d9516114b30c6aa8b08a5986655258452cc23bb8acaa16611d1c56550b30a58e4aa285986395418142cc296b94a821661879516310b3087aeb326659843f7559332cc21ebb4a9996610fdd954ccb3087aeb320659843f7559032cc21ebb4a8196610fdd9540cb30c6ca930865986355498432cc31b2a2c2196618d551610cb30ccca4b0865986655258432cc31d2a4c0196618e552600cb30c74a8b0065986395458032cc334a92c0196610fdd16294730878e8b14a39843d7695051cc21fbb2a828e618b9526214730c5aa9310a39862e5458851cc316aa2c428e611ddd95114730ccac4a88a39846f7259541cc236392caa0e614d1c55450730c72a830283985357195041cc30f2a2c620e610f5d664cc73087eeab26639843d7695331cc21fbb2a998e610f5d6640c73087eeab20639843d7695031cc21fbb2a818e618b952620c730c5aa9310639862e5458831cc316aa2c418e619958a510c730ccac4a88639863a5498031cc31caa4c018e618e951600c730c72a8b0063986715158031cc21f3a4cb90e610f5d265c873087ce932c439843d7499621cc21fba2ca90e610f1d1654873087ce832a439843d7419521cc21ebaec890e610f5d4644873093ae6322439843e7695121cc21e3b4a890e610f9d95448730878ecaa243985647154921cc2b2392a290e610f9d2650873087ae9328439861d5498c21cc30eaa2c610e6199d952108730ccaca90843987265448421cc392aa24210e61b158d2108730c3ca8b1e819861d54d8d40cc21fbb2a82a4619658e6015230c72a8302871843e76d0d528c21e3b286a94611bdd95214a308ece3b2c851847571d96428c296b90a8214618e1516010a3087ceda1aa31843c7650d518c23bbb2a228c611b9cb65906308dae5b2c831853571150418c31c2a2c020c610f9d365c863087ae9b2e431843e74d96218c21eba6cb10c610fdd16548630878e8b2a43184d97018d218c21fba2ca10c610f1d1650863087cec2a2811843f76550408c30eb2cc9984618759564cc230c72cb326611863965593308c317b20c4aa26199d8b6155130cc8c5b0aa89863764185544c333b10c2aa261991886155130cd0c5b02a89867061d81544c21fbb2a82a2614b1c95415130a68e2aa0a89863854583434c28eb9ecba1a614bdc965d0d30a58e4b2e869853771597434c29a38acba1a618e19560d0d30a3ee6b2a869851e75d8d434c30e32ec6a1a61669c36350d30c72ca302869846f76548524c2963a2a429261591c5521493087ee8b08a49843c74584524c23bb8aca212611d1c565109308ece2328849847571194424c326b18a4212618e1516010930cd0a4b00849870d43149324c34ca18c0992611ddd9
  | 15 => 0x67525865250237bb2a4292814e1c143149408eee2b2e64a047471597325025c382c9992818b59052cc9408ece232864a0475711943250316b26a41928199d49610c940cc8a4b0864a066b525803250334292c0192819958b51945408eeeca88a2a05387050c5150237b92cb98a811b1c965cc540970e0b2662a0635641473150237390ca18a811b5c8650c540c6ac9a8862a066562d443150332b10a218a819cd45600c540ce0a2b0062a04ba70d9121502b338ea490a818bd905248540acce5a8a42a063764145215022f398ca10a81175cc650854087ceb32042a066665484215033232a4210a818758f53901408ece2312a620475711895310237390c2a98811b5c86154c408beeca98a62064d53588531032aa9ac229881c654e60d0c40e32a6b0686204bb75583431031dbaac1a18818e54d60d0c40972e031286204b970185431023b388c6a90811d5c46354840a58e4a1aa42046f765485210326b1aa429081995496114840976e0b1c842061d6354e421025cb84c3210818758d5310840a5aeb310842052f765484210317bb2a4210818b58d5210840976eab00842063b75580421031ca9ac0210812e5c264cc840c3cc8a9e64204b9701923210316322a5190811ddc5654c8408e8e2b2a642047671195321023ab88ca990818b191524c840cb2a6302642066952181321023b38eca190811d5c7650c8408dce431aa22046d7218d511029a38a86a88811ddd95114440caac6a88a22066562544511025db82c7208818758d5390440972e1314822061d6354c411029abacc2208814ddd95110440c6eeca88822063563544411025dbaac0208818edd56010440c72a6b0082204b970993311030f322a7988812e5c0648c440c68c8a8c622046f725953110236392ca988811b9c8654c4408dae432a622063464545311032ca98c0988819c544604c4408dce5b28622046d72d94311022f398ca90881175cc6548440972e0322422062c649492110316322a490881591c55248440c68c928a42206346454521102b2392a2908810f5d7640844093ae632042204b9701902110333b2a4210881995952108440c3ac6a9e802043d76952401023cbb4a9200810f5cf655004087ceca9a802061f6354d401029cbac86a00812e9d84350040974eda1280204ba76d054010297390c72a6614b5c86395330a6ce231ca9985357118e54cc28f398c52a6618b5886295330a3ce630ca9986356118654cc297394c6aa6614b5ca6355330a6ce331aa9985357198d54cc29bb8ac4aa6614d1c56255330a76e0b12a99862d6218954cc297b92c2aa6614b1c96155330a76e0b0aa9986356118554cc297b92c0aa6614b1c96055330a6ee2b02a9985347158154cc21fbb2a82a6619698d6015330c72a9304879843e7615143cc21fbb2a821e618e9526010f3087e
  | 16 => 0x86b3baac890843699d86448421d4cec3224210ea7651912108793b28c890843695cc64484219ccedaa24210ce6761512108792aa0a890843719cc5448421b8ae62a24210de27015121086f0b80a890843595d66348421b4ce931a4210da57498d2108752324c69084359dd56348421b4ee8b1a4210da47458d21086f1b82c690843781c16348421b4ce831a4210da57418d2108752320c690843789c06348421bc2e031a4210ce676d4d21086b33b6a690843999db5348421e4ec9a9a4210f2464d4d21086b2baca690843699d25348421b4ae929a4210d667654d21086b23b2a690843c9d915348421e48c8a9a4210f477354d21087a3b1aa690843d118d53484219ccec29a4210d667514d21086d33a0a690843695d05348421bc4e029a4210de17014d21086d33b68690843691db4348421d4ecba1a4210f2765d0d2108793a9e8690843c954f4348421acceb21a4210d657590d21086d2ba48690843d154e43484219ceeca1a4210ce47650d21087a2a9a8690843a9dd94348421b4ceca1a4210da47650d21087523b28690843291d94348421d4ecaa1a4210f276550d21087c3b9a8690843c9d4d4348421f0ca6a1a4210f255350d21087c2a9a8690843c154d4348421accea21a4210d657510d21086d33a08690843a91936048421acaeb3024210da67498121086d2ba4c09084359dd56048421b4ee8b024210da4745812108752322c09084371dcd6048421b88e6b024210ee1601812108673bb243a80430f9d2639402187ae931ca010ea764485500875232242a80430f5cf645402187ae6322a010e3970191500861f3a0c6a80430f5d0635402187ceda1aa010c3c76d0d500861f3b286a80430f1d943540219ceec908a010ea6644845008752b224228043b198d2114021d8ac6908a010c7b76540500871cb22a0280439658d5014021ec242a80a010c5f7654c53d038ca9cc1a1e81c654d60d0f40c3ac6a1ca5a046f7654852d023b38eca196811d5c7650cb40c3ac6a1ca3a04777654451d0237396ca18e811b5cb650c740a58e4b22a72053471591539022fbb2a629c81c654f6050e40e32a6302872056671d4a529023b388c6a94811d5c46354a408deeca90a52061d6354c4290297b92a6214811d9c6658ca408eae332c652047671d94329023ab8eca19481599cb5194640c5ac4214a32046e7218d5190236b90c6a8c811ddd95114640c3ac6a9883205377154c419029ab8ca420c811b9ca658c6408dae532c632046e72d943190236b96ca18c81275cc6408640972e032043205657194821902b2b94a210c8159dd52108640acaea90843204b874580219030eb1aa7a04811d9c662d4d408eae3316a6a046e729875350236b94c3a9a8117dd95314d40e36a7b0286a071b53181435025d3a8c0a1a818e9d46050d40c76a630286a06
  | 17 => 0xa0439558e6115021cb4c7300a810e5963980540871d322c02a0439698d6015021cb2c6b00a810e6a62580540873930ac02a0430fdd160d4c21878e8b06a610e1e73992530861f3a0c0a98430f5d06054c218beeca98a610e1d6454c530872ca9ac029843875926314c21c5cc9310a610e2d64988530871b324c2298438d5926114c21c74c9300a610e39649805308735314c0298439c9866014c21c74c8b00a610e3964580530872d31ac0298439a9896014c21ce4c2b00a610c7a70197430863cb80cba18434e9c054d0c21a72e02a68610d1d73d97430868eb98cba18434e9c065d0c21a72e032e8610d2e7214f430869b388a7a18434e9c053d0c21a72e029e8610c6e72196430863b388cb218431e9c06590c218f2e032c8610c7b70595430863c382caa18431e9c06550c218f2e032a8610c3e76d51430868f39ea8a1843479cc5450c21a74e02a28610d3970151430868f3a4a6a18431b5d46250c21c5aa83128610ce571189430863aba8c2a18438d5506150c219cae430a8610d1d73995430868fb9acaa18434edc16550c21a70e0b2a8610d3a70195430869cb80caa1843475d76350c2187ced29a8610d1d7594d430868f3b4a6a1843879da5350c21a3ceca9a8610d1c7654d430861f3b0a6a1843479cc5350c21a5ce429a8610d367114d430869d380a6a18434e5c05350c21e1aa7b128610d2d751894308716b28c4a1843c354c6250c21b4ae23128610f1553d85430869aba8c2a18438d5946150c21e2aa630a8610da5721854308752310c2a18430f9d36510c218dce43288610c7671194430863d380ca218431e5c06510c2187ce931ca410c3d7498e520871aaa4c3210431ddd5618c82187ce9b286410c3d74d94320870eb24a61904387591530c821caaa73086410e5a53580320872ca9ac0190430f9d2639442187ae931ca210e2d5498a410862f398ca20843175cc65104218deeab146210c3e74d94310861eba6ca188430f9d0650c42187ae83286210e1d6494c310870eb22a6188439354e620c421cb4a6b006210e59535803108786a9a87908431b5da5288421e2aa6a1c4210c757694a2108717b2ec8908438bd9464484218dceda9a4210e2f65d0d21086563b286908438bd954348421e1aa6a1a4210d6575cc521086d33a66290843695d33148421e8aa718a4210d65750c521086d33a06290843695d03148421bc4e018a4210de1700c5210871bb2ec8908438dd9464484218eceda9a4210e3765d0d210865a3b286908438dd954348421e2aa6a1a4210d6575cc921086d33a66490843695d33248421e8aa71924210d65750c921086d33a06490843695d03248421bc4e01924210de1700c92108732baeca90843999db6548421acae7b2a4210ea765d912108793b2ec890843695cf6448421acaeb3224210da674991210
  | 18 => 0x5d0d21c3ae632e8690d3b7054f434869c382a7a1a434e9c053d0d21a72e029e8690c7a70196434863cb80cb21a438bd526290d218d8eab148690ce47158a434871baa4c321a431d1d56190d219c8e4b0c8690c6f72595434863bb8acaa1a431edc16550d218f0e0b2a8690c3e76951434861e3b2a8a1a430f9d66550d21a3ae732a8690c3d73995434870eb9ccaa1a4347dcd6550d21a5ee4b2a8690d3771595434869db82caa1a434e1c16550d2187ced29a8690c3f7654d434861e3b2a6a1a434edc15350d21a70e0a9a8690c3e7614d434869d380a6a1a434e5c05350d2187ce83288690c7a70194434863cb80ca21a430f9d66410d2187aedaa08690c3f7615043487162a4c421a431b1d56210d219c8e2b108690e3454984434863a3aac221a43391c96110d21c68a930e8490e375418542486963aa8421243691c5421092187ceb3266490c3c75593324861fbb6a9992430f5db54cc92187eec2a66490c3d761533248717328a9192435a5c0538c921a5ceba1c6490d2c7550e32486b33a8c3192438d153614c921c68a830a6490c6e7614d32486b4b80a699243c3d50534c921a5ceba1a6490e2c65d0d32486963aa86992438b195434c921e18a6a1a6490ce67518532487333a8c299243a9d50614c921d48a830a6490ea7431853248752a18c2992430fddb540c92187aedaa06490c3f76150324861ebb0a8192438dd52610c921c68a93086490e3b54980324871c2a4c0192438ed51600c921c70a8b006490e2c5498b4148717aa0c4a0a434d1d54110521b48e4a088290c3e75993314861e3aac998a430fddb54cc52187aedaa66290c3f76153314861ebb0a998a438d994548c521ae2e029c6290d3675d0e314869a3aa8718a43599d4628c521ac8ea9946290c3e74d95314861eba6ca98a430fdd1654c521878e8b2a6290e2c54d8931487162a0c498a438d197544c521c68ca2a26290c767614d31486b8b80a698a43c5d50534c521a6ceba1a6290e3465d0d314869a3aa8698a438d195434c521e28a6a1a6290ce67518931487333a8c498a43a9d50624c521d48a83126290ea7431893148752a18c498a4399196324c521ac8ea9926290e64654c931487c2a1a6498a430fddb540c52187aedaa06290c3f76150314861ebb0a818a438bd52620c521c58a93106290e2f5458831487162a2c418a438ed52600c521c70a93006290e3b54580314871c2a2c018a434d1d543c8521d8ac71964290d2c7550e2148762b1c6310a430f9d263d412187ae931ea090c3e76d51504861f3b0a8a824387d536354121c38a9b1aa090e1f5418d504870e2a0c6a82431edd95014121ab0e6a80a090c3e7498c504861eba4c6282438798d4314121c3ac6a18a090c3f76550540870eaa2c62a0438e5516015021c3cc8b18a810e1e7458c5408726b1cc42
  | 19 => 0x132a8790c797099543c869d386a8a1e434e5c35450f21c6ea830a8790d1d7399543c869d384caa1e434e5c26550f21a3ee6b2a8790c3e7694d43c861f3b0a6a1e434e9c05350f21a72e029a8790e366518543c863d380ca21e431e5c06510f21c6ca8b088590d697014e32c86373b0a6996435a5c0534cb21e18a6a1a6590e555358432c869d386a920e430f9da545072187aedaa08390d3a70d5041c869d3a6a1286430f9d2639432187ae931ca190c3e7418d50c861eba0c6a86431edd95014321ccac530ea910e6962983548873930ac1aa4434e9c35495221a74e1b22a910c3f765505488732b14c22a4439958a61d4e21c6cc930ca710e3564986538861f3a6c0a9c430f5d36054e218beeca98a710e2e645885388716b22c429c439958a6114e21c74c9300a710e39649805388734b14c029c438e9916014e21c72c8b00a710e6962580538873930ac029c431e9c265d0e218f2e132e8710d3a70d53438869cb86a9a1c43475cf65d0e21a74e132e8710d3970997438868eb98cba1c434e9c053d0e21a72e029e8710c7a70196438863cb80cb21c431e9c26550e218f2e132a8710d3a70d51438869cb86a8a1c438bd506250e21a3ae732a8710d3a70995438869cb84caa1c4347dcd6550e2187ced29a8710c3e7614d438869d380a6a1c434e5c05350e21c5cca3128710c7a70194438863cb80ca21c434e9c35490a2187ced2a28510c3d76d50428869d386a8214438b9516210621ae2e029c6310c767614d31886b8b80a698c43c514d434c621c9aa6b106310d3a74d42508861f3a4c7284430f5d2639422187ce831aa110c3d7418d508863dbb2a0284434b5c863d5121a6ae231ea890d3a7018f544869cb80c7aa2434e9c362d5121a72e1b16a890d3a70d87544869cb86c3aa2434b5cb60d5121a6ae3b06a890e3b60983544861fbb2a82a2434b5c86315121a6ae2318a890d3a7018c544869cb80c62a243479cc6015121a3ae6300a890d2d72180544869ab88c02a2438e5806015121a3ae7b26a690d1d73193534861f3a4c1a9a430f5d260d4d2187ee8b06a690c3c74583534861f3b6a8a9a430f9d85454d21c76a9b02a690e3854d81534871daa0c0a9a438e1506054d21c58c9b12a690e3464d85534871db26c0a9a438e1936054d21c76c8302a690e3864181534872db18c0a9a439ad886054d21ce6c2302a690d1d73d50534868eb98a829a4317dd95314d21ab0e0a98a690e3b54980534871c2a4c029a438ed516014d21c70a8b00a690e2e645885348716b22c429a438d9916114d21c6ac8b08a690e6562584534871d324c029a438e5926014d21cd2c5300a690e7161980534871d322c029a438e5916014d21cd2c4b00a690e7161580534863d386cba1a431e5c365d0d21a3ae7b2e8690d3a70d97434869cb86cba1a43475cc6
  | 20 => 0xb4394a500c794a1ca528063ca9515294031e52a8a94a018f2b4354a500c794a1aa5280634e9d05294031a72e8294a018f61528c6500c6adbaa63280635cdd53194031f228698ca018f61524c6500c69d3a0c7280634e5d06394031ad4e431ca018d697218e500c78db9a87280634edd16294031a70e8b14a018e696218a500c69d3a665280634e5d332940318f2ec194a018d3a740ca500c69cba065280635c9c43294031ae2e2194a018d3a74cc6500c69cba66328063c550d31540318f4edaa2a018d6a72d51500c6b4b96a8a80631e9d85454031ad4e42a2a018d6972151500c69cbae86a80634edd543540318f4eda92a018d3a74d49500c69cba6a4a8063ca9525254031e52a9292a018f2b43949500c794a1ca4a8063ca9515254031e52a8a92a018f2b43549500c794a1aa4a80631e9d85254031a74e8292a018d3974149500c78caa662a8063d254b3154031e64a918aa018f31548c5500c7b129462a8063d854a3154031ab6ea98aa018f19544c5500c7a4a9262a80635cdd53154031e64a898aa018f31544c5500c7c8a1a62a8063d89493154031ec2a498aa018d7071591500c69d3a4c6a80634e5d26354031ae4e321aa018d717190d500c78db9a86a80635c9c44354031ae2e221aa018d3b74589500c69c3a2c4a8063561cd6254031ae0e2b12a018e6962189500c6b9b8a84a80635c1c54254031a74e9992a018d3974cc9500c6b938e64a80635c5c732540318f4ec192a018d3a740c9500c69cba064a80635c9c43254031ae2e2192a018d5a73105500c6acb9882a8063cc5044154031a74e998aa018d3974cc5500c78ca1e62a8063ccd0e3154031e628718aa018f19434c5500c7a9b9a62a8063ccd0d3154031ea48698aa018f31434c5500c7a8a1a62a8063c450d3154031a74e818aa018d39740c5500c6b539062a80635a5c8315403187aed2a0a018c3f76550500c7172a4c4280638b5526214031c5ca8b10a018e2d54588500c636bb4a4280638b9925214031c5ac9290a018c6f76548500c717322a4280638b5915214031c74a9300a018e3954980500c735294c0280639a54a60140318f6eca80a018e3a64540500c71cb22a0280639a9895014031cd2c4a80a018e666258754c8738b0cc1aa6439a98960d5321a74e1aa4a990d3a70d9154c861fbb2a82a643999896115321cccc4b0ea790e2e6498a53c8716b24c529e430f9d36054f2187ae9b02a790c5f7654c53c871b322c229e438d5916114f21cccc4b08a790e3a6498053c871cb24c029e439c5866014f21c74c8b00a790e396458053c8735312c029e439c5856014f218f4e132e8790c797099743c869d386a9a1e434e5c354d0f21a3ae7b2e8790d3a7099743c869cb84cba1e43475cc65d0f21a74e029e8790d397014f43c863d380cb21e431e5c06590f218f4e
  | 21 => 0x696ba0c7290635a9c06394831ad2e031ca418f0f7350e520c697ba2c1290634b1d16094831cd2c0304a418c6e76d51520c6b5386a8a90635a5c354548318dcec2a2a418d6a70151520c6b4b80a8a90634b5d74354831a5eeaa1aa418d6471591520c6973a4c6a90634b5d26354831acce321aa418d657190d520c787b9a86a9063599c44354831acae221aa418d2e740c5520c696ba062a90634bdd16054831a58e8b02a418d4c73581520c6b238ac0a90639a580605483187aed2a0a418c3f76550520c7172a4c4290638b55262148318deeca90a418e2e64548520c716b22a4290638e9526014831c72a9300a418e6952980520c71d2a2c0290638e5516014831cd2a4b00a418c7a70997420c63cb84cba10631e9c265908318f2e132c8418c7a70195420c63cb80caa10638d5536150831ccaa5b0a8418e6552185420c63d384ca210631e5c2651083187aeb3266418c3f75593320c61ebb4a9990630fdd954cc831c5cc92966418e2d6494b320c717322a5990638b59152cc831ccaa4b0e6418c3d75990320c61fbaac8190630f5da540c83187eecaa06418e2e64948320c716b24a4190638b991520c831c5ac8a906418e3654984320c71aaa4c2190639954a610c831c6ca8b086418e3554584320c733292c2190631e5d6600c831c74a93006418e3954980320c735294c0190639a54a600c8318f6eab006418e3a54580320c71caa2c0190639a949600c831cd2a4b006418e1d5458e410c70f2a2c6208639398d5210431c9ac6a908218e3565504410c74ab1a8220863c9549411043187aed2a66218c3f76553310c717324a5988638b59252cc431c5cc8a966218e2d6454b310c786a1aa598863c355152cc4318baed29c6218c757694e310c69abae87188634ddd5438c431e4ca8a946218f255454a310c793a1aa518863c950d528c431c3ecba1a6218e1f6550d310c786a1aa49886387d96544c431c3ecaaa26218e4f65949310c727b2aa498863c3551524c431c6ecb2a26218e3765551310c6caba4a6988634d5d7434c431c6ecba1a6218d957490d310c69bbaa86988638dd95434c431b2eeaa1a6218f177550d310c74bb2a8698863c5d95434c431ccecb2926218f8543949310c78aa1aa49886399d95524c431e4ca8a926218f2554549310c7c2a1aa498863d1d8d524c431e4e86a926218f4643549310c792a1aa498863d150d524c431e0a86a926218e2e5498b500c716aa4c5a80638b95162d4031c5aa8b16a018e2e6494b500c716b24a5a80638b99152d4031c5ac8a96a018d3a74d42500c69cba6a1280635a9cb5094031ad2e5a84a018c3f7458a500c61e3a2c5280635a9cb5494031ad2e5aa4a018d6a72152500c6b4b90a9280634e5d74394031a76eaa1ca018d3a74d4a500c69cba6a528063ca9525294031e52a9294a018f2
  | 22 => 0x6630f5da54ccb3187eecaa66598c3d7599032cc61fbaac8196630f5da540cb3187eecaa06598e365498432cc71aaa4c2196638d951610cb31c6aa8b086598e655258432cc71d2a4c0196638e552600cb31c74a8b006598e395458032cc735292c0196639a549600cb31c3ca8b1e8398e1d54d8d41cc61fba2c5286630f1d1629433187aed2a0a198c3f7655050cc7172a4c4286638b5526214331c5ca8b10a198e2d5458850cc63dbb2a0286639a589501433187eecaa0a918e5563984548c71aaa0c2a1c630f9db4354a31878eca1aa518c6f76548528c63d386cb214631e5c36590a31a5ae42a08518e3454584428c61f3b0a8a0c630fdd95410631c3acb3266318e1d65593318c71ab2cc998c638d59564cc63187ceda1aa118c3c7650d508c63dbb2a0284638bd906255131cc8c5b0aa898e6b62d81544c734316c0aa2638ed906055131cd6c4302a898e6862181544c739b08c0aa2630fdd95415131a58e4aa0a898d3870550544c71a2a2c3a1a63475cf65d0d31a5ee4b2e8698d2c72597434c69db82cba1a634e1c165d0d31c68cab0e8698d1f73595434c68f3aec6a1a63871976350d31b2ce3b1a8698e3565185434c637bb2a4292634b1d15214931ad0e0a90a498c3f74580524c61e3a2c0292631edc165109318f0e0b288498c7a70194424c63cb80ca212639358c5210931c68a8b088498e6452584424c786a18a499263a550c614c931a58e4aa48298d3870552414c61f3b0a8a0a634d5c6541053187eecaa08298d2c72550414c69c382a820a631edd95014131a70e8a80a098d6872540504c61fba2c4282630f1d16214131ccac530ea818e6a62983540c734b14c1aa0639a98960d5031cd2c4b06a818e7261583540c697396a92a0634b5cb5495031a74e1aa4a818d3970d52540c697396c8aa0634b5cb6455031a74e1b22a818d3970d91540c69a38ac4aa0634d1c5605503187eecaa0a818e2d54988540c716aa2c42a0638e5526015031c72a8b00a818e2e64988540c717322c42a0639398d6215031ccac5308a818e3a64980540c735314c02a0639a58a6015031c74c8b00a818e5a63580540c735312c02a0639a5896015031ce4c2b00a818d2e72d53430c696b96a9a18634e9c354d0c31a72e1aa68618d2e72153430c696b90a9a18634e9c054d0c31a72e02a68618e3554586430c697396a8a18634b5cb5450c31a74e1aa28618d3970d51430c61f3b0a8a18634b9c85450c31a5ae42a28618d3a70151430c69cb80a8a18630fdd95410c31c6ca8b088618e3a54983520c71caa4c1a90638e95160d4831c72a8b06a418d2e74d4a520c696ba6a5290635a9c35294831ad2e1a94a418c3f74582520c61e3a2c1290635a9c35494831ad2e1aa4a418d6a70152520c6b4b80a9290634b5d74394831a5eeaa1ca418d2e7418e520c
  | 23 => 0x14032ce4c2a80a01967161540500ca2fbb2a629e83c554e61d0f41e2aa6b0e87a0e1d6350e52d0637bb2a4296831e9c3650cb418f2e1b2865a0e1d6350e50d063dbb2a0286834b1c96454e41a70e0b22a720c5f7654c539078aa9ec2a1c83c554c6150e41ad4e1a94a520c7a7018d529063cb80c6a94831bdd95214a41c3ac6a988520d2f7254c429063d384cb194831e5c2658ca418f4e1b286520c7970d94329070eb1aa7a0c835a9cb5094241c5ac4214a120c6e7218d5090636b90c6a84831edd950142418f4e1316a6a0c797098b5350637394c1a9a831b5ca60d4d418beeca98a6a0f1753d85435078ba98c2a1a832d9d46150d41c6cea30a86a0e37531854350735a92c1292831bdd95214941a68e2a18a4a0c7b70597325063c382cb992832d1c564cc941c5ac829664a0c7a70194325063cb80ca192838b593520c941ccea4b0864a0e64525843250735a92c0192839a149600c941c3ac7a9c82a0e6962d42505063dbb2a0282834d1c543141418f4e0312a620c79701895310637390c0a98831b5c86054c418beeca98a620e4d53588531072ca9ac029883c554e61d0c41e2aa6b0e8620cb775587431071bbaac3a18838d54d61d0c4196ae23128620cb571181431063d380c6a90831e5c06354841a58e4a1aa420c6f765485210726b1aa4290839a549601484196ee2b1c8420e1d6354e421065ab8cc1210838758d5310841a5aeb3108420d2f765484210717bb2a4210838b58d521084196eeab088420e3775584421071aa9ac2210832d5c664cc841c3cc8a9e6420cb5711923210716322a5190831edc1654c8418f0e0b2a6420c7a70195321063cb80ca990838b191524c841caaa630a6420e6552185321063d386ca190831e5c3650c841c3ac6a9e8220c3d76952411063abb4a9208830f5cf655044187ceca9a8220e1f6354d411069abac86a08832d9d8435044196ceda128220c6e7218d5010636b90c6a80834e1c143540418f6eca80a020e59635405010734b12a0280834b9c86395331a5ae431ca998d3a7018e54cc69cb80c72a663479cc6295331c5ac4314a998d1e7318254cc71cb00c12a6634b9ca6355331a5ae531aa998d3a7098d54cc69cb84c6aa6634ddc56255331a76e0b12a998d387058954cc716b10c4aa6634bdc96155331a58e4b0aa998d3b7058554cc69c382c2aa6634bdc96055331a58e4b02a998d377158154cc71cb00c0aa6630fdd95415331cacc6b08a998e355498643cc61f3b0a8a1e630fdd95410f31c6ca93088798c3f7458252cc61e3a2c1296630f5da5414b3187eecaa0a598c6f7654852cc71d2a4c0296638e5526014b31c74a8b00a598e395458052cc734a92c0296631edc16550b318f0e0b2a8598d2c7255142cc71aaa0c2a16634b5ca5410b31c3ca8b188598c3d7599332cc61fbaac999
  | 24 => 0x992a21953574cc9510cb8aa1e64a8865c9d0e3254432e4a87192a219715434c9510cba3b9a64a8865c9d0d3254432e8c86992a219725434c9510cba2a1a64a8865c150d3254432a6ce8192a219535740c9510ca9bba2c0a88654d1d16054432aa8e6b02a21956472581510cb38b00c0a88650f5da541443287eecaa0a21963654984510cb1aaa4c2288651ddd95114432c6cc8a88a21963564544510cb1d2a4c0288658e5526014432ce2a3300a21963a54580510cb1caa2c0288659c5456014432c6ca930ea01963554987500cb1b2a2c3a80658d55161d4032c6cc928ea01963564947500cb1b322a3a80658d59151d4032a74e9a84a01953974d42500cab938ea1280655c5c7509403287ee8b0ca01943c74586500cab938ea9280655c5c75494032ae4e22a4a01957171152500ca9cbae87280654edd54394032ab6ea994a01956b754ca500cbc4a1a65280654e9d35194032a72e9a8ca01973254946500cb98aa4a328065ccd0e5194032e628728ca01973254546500cb98aa2a328065ccd0d5194032e6286a8ca01976232546500cbb0992a3280654e9d05194032a72e828ca01953a7418e500ca9cba0c7280655c9c46394032ae2e231ca01971b7350e500ca9d3a665280654e5d33294032a76e8b0ca01953874586500cb38b08c328065c350d32540328f4edaa2a01957271d51500cab8b8ea8a80651e9d85454032ae4e22a2a01957171151500ca9cbae86a80654edd54354032e32a9992a01972a548c9500cb94aa464a806556dd53254032e32a8992a01956b754c9500cb952a264a8065ca5513254032f1286992a01947a76d45500ca9d3a6a2a80654e5d35154032e64a928aa01973154945500cb99a1ca2a8065cc50e5154032ec46528aa01976132945500cb992a2a2a8065cc5515154032e6686a8aa01973143545500cba9992a2a8065d88c95154032ea264a8aa01976132545500ca3d3b0a2a80654e9d05154032a72e828aa01956872591500ca9d3a4c6a80654e5d26354032ad4e521aa0195697290d500cb8db9a86a80655a9c84354032ad2e421aa01955a73109500caacb9884a8065ca5084254032a74e9992a01953974cc9500cb8ca1e64a8065cad0e3254032e5287192a019719434c9500cba5b9a64a8065cad0d3254032e9486992a019729434c9500cba4a1a64a8065c250d3254032a74e8192a019539740c9500cab938864a80655c5c43254032a76e8b0aa01953874585500caac39ac2a80655a1c96154032ce2c230aa01943d76950500ca1fbb2a8280658d9526114032c6aa9308a01963654584500cb1aaa2c2280651d5da5114032c6cc9288a01963564944500ca3bbb2a2280658d9915114032c6ac8a88a01963a54980500cb1caa4c0280659c9466014032ce2a3300a01947b76540500cb1d322a0280658e59150
  | 25 => 0x70550544cb162a2c5a1a65475cf65d0d32a6ee2b2e869953471597434ca9db82cba1a654e1c165d0d32c58cab16869951f73595434ca8f3aec6a1a65871976350d32b1ce5b1a869962d65189434ca9a38aa9212654e1c1549093287cec2a2849952d72950424ca1fbb2a8212654d1c55410932a70e0aa0849947776544514ca9a3a2a228a655c1c1511453287ee8b00a29943c74580514ca3dbb2a0282654e1d15014132ae0e2a80a09943f74584504ca1e3a2c2282659998961d5032ce4c3306a81967161983540cb35312c1aa0659c98560d5032ce2c2b06a81953671d52540ca9ab8ea92a0654e9c35495032a72e1aa4a81953671d91540ca9ab8ec8aa0654e9c36455032a72e1b22a81952c72585540ca96392c0aa0650fdd95415032c6aa9308a81963554584540cb1caa4c02a0658e5516015032c6cc9308a81963664584540cb2b31ac22a065999896115032c74c9300a81967261980540cb38b0cc02a0658e9916015032cb4c6b00a81966a62580540cb3930ac02a0659c5856015032a6ce3aa6861953571d53430ca9d386a9a18654e5c354d0c32a6ce22a6861953571153430ca9d380a9a18654e5c054d0c32c5aa8b14861953671d51430ca9ab8ea8a18654e9c35450c32a72e1aa2861943e76151430ca9b388a8a18654d5c45450c32a74e02a2861953970151430ca1fbb2a8218658b9516210c32c3aa8b1c841961e5458c420cb16b2a8421065a358d421083287aed2a6641943f76553320ca2ebb4a7190651b5da538c832a5aeba1c641952f7550e320cb0fb2e869906587d95434c832c3ecb2a2641961f65551320cb17b2ca8990658bd95544c832b1ae929a641952d75d0d320cb17b2e8699065635d2434c832a5eeaa1a641962f6550d320cac7baa8699065c3dd5434c832d1ecaa1a641970f6550d320cb1d2a4c1a88658e55260d4432c74a8b06a21963954583510ca9b3a6a3288654d5d35194432ae4e1a8ca21957170d46510ca1fba2c1288650f1d16094432ae4e1aa4a21957170d52510cab9380a9288655c5c05494432a6aeba1ca2195377550e510caabbaa652886559dd53294432f0a86994a2195367418e510ca9aba0c7288655c9c06394432ae2e031ca2197177350e510ca9b3a665288654d5d33294432a6ee8b04a21953474582510cb38b00c128865c350d32544328ecedaa2a21957270d51510cab8b86a8a88651d9d85454432ae4e02a2a21957170151510ca9abae86a88654ddd54354432e2aa9992a219726548c9510cb92aa464a886555dd53254432e2aa8992a219567754c9510cb932a264a8865c95513254432f0a86992a21956472591510ca9b3a4c6a88654d5d26354432acce521aa2195657290d510cb8bb9a86a8865599c84354432acae421aa21955673109510caaab9884a8865c95084254432a6ce9
  | 26 => 0x9c392a028287ca1c95014143a50e4a80a0a1f33715405050e9c38aa028287cc1c55014143a60e2a80a0a1c3d769524310e2ebb4a9218871bdd95214843ccaa4b08a421e69525805210e3bbb2a228887995895114443ce2a2b00a221c7b765405010f34b12a0280879c58550140438beeca98a7a170d5398b43d0b86a9ac5a1e858758d43947428eeeca88a3a161d6350e50d0a3dbb2a0286854d1c56454e42a70e0b22a72145f7654c5390b86a9ec4a1c85c354c6250e42c3ac6a9e852157270d465190a3d380c6a8c851e5c063546428eeeca88a32157271d425090a3b388c6a84851d5c463542428f6eca80a12147a709875350a3cb84c3a9a851d9c660d4d428eae3306a6a145f7654c5350b87a9ec4a1a85c3d4c6250d4295cea31286a162e751894350b17a98c4a1a858758f5390942ce6a2b04a2a1477765445150a963928628a859c58750941428f6eca80a0a152c7250c5050a3d380c2a98851e5c06154c428ece2302a621475711815310a2fbb2a6298859554d6114c42cb2a6b00a62170d5398b4310b86a9ac5a18852bdd562d0c42c5eeab16862162d5358b4310a56b90c2a18852b5c86050c42c3ac6a9e842143d769524210a36bb4a9210850f5cf655084287ceca9a842161f6354d4210a96bac86a10852b9d843508428f4e031aa2214797018d5110a9a38a86a88851ddd95114442caac6a88a221671515805110a3b388c6a80851d5c46354042a70e0a1aa02147b765405010b2cb1aa0280859c5855014042a6ce231ca9995357118e54cca9d380c72a6654e5c06395332a3ce630ca9996356118654cca8f398c12a6658e5806095332a6ce331aa9995357198d54cca9d384c6aa6654e5c26355332a6ee2b12a9995347158954cca9db82c4aa6654e1c16255332a5ee4b0aa99953b7058554cca9c382c2aa6658d5846155332a5ee4b02a9995377158154cca9a38ac0aa6658e580605533287eecaa0a99964e6358854ccb16aa4c521e650f9d85450f3287eecaa0879962e5498843ccb0f2a2c7a1665875536350b3287ee8b04a39943c7458251cca1ebb4a828e650fdd954147328eeeca88a39963a5498051ccb1caa4c028e658e9516014732c72a8b00a3996715158051cca1fba2c3286650f1d1619433287aed2a0a19943f7655050ccb1b2a4c2286658d5526114332c6ca8b08a1996355458450cca3dbb2a0286659c585501433287eecaa0a91964d63988548cb16aa0c4a1c650f9d85450a3287eecaa0851961d65993328cb0eb2ac9994658b59664cca32c5acab26651943e76d0d518ca1e3b286a8c651ddd9511463287ceda1aa11943c7650d508ca3dbb2a0284658dd906155132ccec430aa89967361d81544cb3830ec0aa2658ed906055132cd6c4302a89967361181544cb38308c0aa2650fdd95415132a68e2aa0a899538
  | 27 => 0x300280040020060050016000000801000000100c800800201100100040100070030008000002027801c004000000000c010009000001002a01b008802008a042003000800200001c801000400200400000380010030000002001000805c00600f0008088002001016801800e002002000005c000007802c024004008004c02c00a8deeca90a5a1c777654451d0e3dbb2a0286870fdd95214b4395eeca90a5a1d2f7654852d0f17bb2a429687c358d5214b43c5ac4290a3a1d357114851d0e1fbb2a228e872ddd95114743a6eeca88a3a1e377654451d0f8ab1aa228e878b5885214343a72e0290a1a1e356114450d0e9cb80a2286870fdd95014343976eca80a1a1d3b7654050d0f1dbb2a028687c658d50143438deeca90a521e65525845290f34a92c0294871ddd95114643ccac4a88a321e71515805190e3dbb2a0284879a5895014243ce2c2a80a121c6f765485250eb238aa4292875a1c152149438eeeca88a2a1d64725445150eb8382a228a871edd95014143ad0e4a80a0a1d70715405050f47b14c5a9a87a5d8661d4d43d36c1306a6a1e9763d855250f4ba9ec2a9287a5d8c6154943d2ea630aa4a1ea7521855250f1b290c2a9287a6d8f6054943d66c3b02a4a1eb061d815250f4da9ec0a9287a6d8c6054943d66c2302a4a1eb0611815250f4da98c0a9287aad486054943c74a4302a4a1d2d72d4c5250e1fbb2a4292874d1c55214943a70e0a90a4a1caf765485250ed238aa4292876a1c15214943a5eeca90a4a1e2f765485250f87b9aa429287c9dc55214943a58e2a90a4a1f24715485250e9238aa429287cadc15214943a58e0a90a4a1f28705485250e94382a429287a3d8f6254543d1ea7b12a2a1e8f631895150f47a98c4a8a87a918b5154543c58c528aa2a1e9b63d815150f55b16c0a8a87aa18b6054543d36a7b02a2a1e9b631815150f55b10c0a8a87aa1886054543d36a6302a2a1eb3511815150f1d288c0a8a874d5c75314543c5ac4290a2a1d35711485150e1fbb2a228a874b1c95114543a70e0a88a2a1cb7765445150ed2392a228a876c1c15114543a6eeca88a2a1e37765445150f8bb9aa228a87c9dc95114543a68e4a88a2a1f24725445150e92392a228a87ccdc15114543a68e0a88a2a1f30705445150e98382a228a87a3d8f6254143d1ea7b12a0a1e8f631895050f47a98c4a8287a5d8f6154143d4ec5b0aa0a1ea462d855050f4ba9ec2a8287a5d8c6154143d4ec430aa0a1ea4621855050f4ba98c2a8287aa18b5054143d60c3a82a0a1e2c629415050f1a30ca0a82874e5c35314143c5ac4290a0a1d39701485050f1ab08a2282874e5c0511414387eeca80a0a1d2c725405050e9a38aa0282872edd95014143b50e4a80a0a1db0715405050e9dbb2a0282878edd95014143e36e6a80a0a1f2b725405050e
  | 28 => 0x2004002000000e000000002001e00a0000000010006003800001c000005800c02200000400200100000000000022018002000800200b00b805400c03200580300420000058070004013001805005c000000005c00c00c003800000000100300000040030000010008007000006c008000005800000a0010018000008003000000c00e003000000000600400000100000110008174010005002006c0a0000001800400800701e0068002012007000800000000080000060140000000016003001006c0100060078024008017001000001a001000800400e0060008070054000000000000a0130008000004002000000000c0020008000008011005000000c00100000f0000001000802c0000610028010000024030005c0be01f001806c06c004000800000003100a001402a0120008020000012000800c0020010000008000006006000404c045002006c00400301000e400601a000803800600a00100440020010000020000042007808400e00b0128000024000008800c0000000018000000001007007804a0a4009001008000e0030034006018014001c0000030138000088007000000c032000006001400200100a0028008006001000803c00500000080360040000038000004005810402600900a804000000b001804c00201f00a000400c000004000c0040000000050004003000801004e000000000000e009008000401c0000078014016011000001800001e00b800003a00000780000b8000000000c00e012001801000000901980940040010088024002002000004400e00000300c000000b00a00280040060030028034012002801c00e001000800c02c0040010098014002000000000000a004800c00403b000001800a00a00900240280060130018014027003000401400f00d800c000003000004400e00700c80040b00010000000002008001007400a01200a000c00200f0030004022002005800800800a010800000a026000800400c0070018020004000000002c016001003800c0060180000008006004000801800a000003000001c005003801401a018003800401a0000038034004002002000001a0040080004000004000803000600900200140260050108000008067005800402e0050008008028010008803401200200880d8010005000001800800a0008004002001005003c000003003806002000e001800400400f00580d40020050000010000014004000400001d000800800000e008000400a037000803805e001004000000002902400000000080070000014008000001000400a003800000a000001000403600400100040140000030004008000002800400c000000007800400300680000120020030038004017000801c00600300f8008000000003800c08200f00680080000010050000014000003800c0000040
  | 29 => 0x20014008000000000401000204b000802c01d00000ac000001000800400c002002003000a00200880000740000020024018004000000401a003002800801000000180040000060018008010002002001000000a0048000004001008802c00a0050100010000002001006800000000b803c010001002800000a01b00d0048010001002009402e004000800000200000a000002c00500b8008004000000800000a007009001000400400a000404001300e800400200000180240120010008000002001000000800001d006005c00400000000140280010148018018000000003401e00d00d804000a00a00c0000010001001000c00400000c0000000028011001400600000e000000000000b80080020000068004000002004800400202807f004c02000100f802010200000180080100120000004028000003802c0000020068004000006009007c000009000800402e00001c000c008016003015c09000b002802000000d000801c006002001001400201d000806001400f00d001400c002000000000201c0008014004004008800c00a00d03d00800120090000008002000000800000000b00000d800a01600a803c00c001002000c00400700a003c0000000190010000001002001003c00100d00040120040010080004003000000400209400180440020020008000008004005806c00c009000800000000200000a000400002f80400000100038000018004001808400e00200200180020000018008000016007003000000700780940100020010000012000005800000000500000000060030000018040013009800802400b00100140120000018024012008003000401c002009801c008023008001400000000b800c010006008000c00600001380040040000070000072007000000800201b009800400402501c003c00803900a8010006000007800003e000039802000000000000f0018009000000400400000a0000042021016801c0000000018004002008009001000400700b001000000c0088000002002007001805a00a0018000014017004805000200000580040000160030088002001005003c038000007000c01c0020050070002010000000400c00400280040000040070058004000001000000005a008800000c00401100000100030000008012001000001000001a003008400a0000030004080000009000c01a01a0000028010005000000400a01000f0000006001000002c002002002800006400b0030000008000015006000c012004800802e00403f001801a01f00f000000200100880000a20060008000006000000803000600e00400d8030001001003402a000007000000e00b000806800000a0040008084022000000400800000080040000030000000002008001001000800300180100b000900180140000020008218
  | 30 => 0x31ed000000002021f18335322879c0000000000000003d04e500011291a14c2c1160000356c7810a3c0002ad47bc000035f15481fe0c14853101453630cca031284cf60918f862ff435d3eb4000117c3a53a3c39c299000030080350238445000095a00006bd000064d25882ac2b58cdd23588593e90dbe4290f5d34a4923426d1b642b813e3670bed1db914133987fe2b6c2ba289c72346505f50f9116747083e941c09ac031415f3b3c8a13cfc8c9224441c070c72f132825331250e6413c9ea081451a22a0fba280007f37e0f0b40dca5d2cc806a1f8837b2d546541a2c000464855a051c0001960fcc333c8c730c879d1d180000b901ef3f8c12000003c6000038e4348ef0000016500007132e54dd821e4f1b3089207455c0003e00c8604a465c2f2054740a80042be8b4900001910000000000000030849b1000000005085e00dfc14f2668fe70118d72203c53342e84bb3f7c9a422a8aeb06a015741ed218443c71f42cc17d0c303241e1cf3c4334096047839f09cc5bb112ca51000030609b48b0077852a33ec0000fb09081f2c42414a08fd26d498a00009413f6cd6724dc3323ef800042e496e08c400043208a938b0e1a188054f3fc00fb083c70828ac8e0001cd4618008430000c9246a01f23a4cca73fd8ed021211ea38b859a00000000070000330c638134014416080000000d6403d800000000002df4ada000000000006a11bb8b5e24851c30db874b00005be215ce9538710be260104912949b245fc0001818feb42bccb93a44f2e2b701f527d436209f4000378400000000000000cf800008d334380000ba4f8d29c0a952a7498714bc7991ef8a531550dcb0960f1704b0000000000000000732968912000073c37c48ca042c00000000000000fef14e40003d587ac40ed12b0ca0a04362904147200003ed849b40b80ab3f480001bb0018007800c00a001005000c064008000001000e015000000800a01c0010004006001000800c01c0070018004002002000001001a0050030040022000000801800600000b8004000009003801000a001000000001c0030000004000007000000400200300c0000004010002800802e00f000000c070000008003401e00100100100020030018048000003004000001a000012800c00000d0058008000001000000802601300000080000000038044000000001000000400c000002800a005000801405c00b0000008000046001001000e012001803c00602e0000000002000000800c074004011000000003001d802c03600300180040080040010004012010000001400c0030048000000004000800c00e003000003400c001001000000000100000040080000000004000005001800002200a0030000004003005002400000600001940000040000000000000000001c016004001000800000f
  | 31 => 0xb45871710000414029a27a0cd23c44000387485c1130a383978b3c00004fe272c0000000c032e3077d00000000000d47461808c24b514d000000027fc71a31046d400007f308cc92b00003492f78ed340c494e0e680252c7c266063c000039c0003d940eb46f4d2b3ffc77a1b0c3820000fee0e341f00d701a412510f2379c0002af9043057021d090cea202e8cab000092e15ec56b473004a28c469f3b102dd1f4c8020bed1073cf819f0000738000007e0db440c45500001f0c59c2bdd0090df0e5047d41df30c4699116c55004e0fc500005460ee08ba1f3c72518b8bba250ca7703f80000000ed50000a6b3ab8000295c0000000000215057a42644f92d0c01137187c93bfd0c22b0c673331411d21687ec3f3cbb13a48601458cd1b4378bef3f88c7a038c785451c00014d0e153528a9b127cd3e31d85ff1d705650fb8f2719f42840bb8f7327e059f1330049018c261000015139900000b0022110c4d260b0c6e847ac22d42e02f6171489c026ce591d38dfd08046dc1fac46e32c4596198014043e844a09d447400000892e2801f0d504120904ebd439cf4e42046d300e42b223ec3d41d0d0932608d3841b868a24a91a32cf40000000b5b2728950108400017b4c1215a91b107f0ea73da473e000000000003e535087c13a250683ca8733305800000000001e5478b38dcba6000116c303014326ac01518406b80000cba3e580003d6882f10b090108600c034b4f5e184d02111ecba1440ceb72a850c5080053c000055e02bc82c00003000108f0c09950750330973054844f1e611d61dc90a50000a3a42f06640000869358c000363c24211c45bd01a0000000000002b50e94428c0500000001d8c0000ca49d01844e410f68a97000118d2918d1a3e2c45a35d4c1800000003c8c84f35f841d3ebc000273c0002ae400017f901506d04c700000002f5800033040003f248b614047a20604d093b1c2d702080002a5895100885dc1ce410e18949480ef02130ffd21113803c02cc40000000cee00008dc2cbcb6d3e1474533f8e2a000000023d00003d5d1930001117000118e026073736b908b1d311db037800004c4000399800006940000c9c6390408ea517c4ade04d05422dd0000000000044cca940000de03f810a644ec39430503d9327823a0ee858a2c8c42739d43e20fd4304470498d2f8c85e257d0ce2f685231b18000000106c00000003d549f7000024a00002c13cb4760095cc6b462845444947f419d0bd22e200d046fc6332fa80002bcd07f00000001318e7a00000004814000181c99e3100dd426310c63c64f6a01c000000000b505ec68821c850813e071e455400b3280d912a4024c05e4f7a3210cd645f85da34d04571cf4c8200000003c98aa700000001f9c1674234807000050b437c000163c58e1df09e12c9ca6d407438
  | 32 => 0x3e21b82541eccd451a9800044105582400bc60d08319396cc8b40bc70b0400bfe3f081781930f3b1bc03f61d2805f1688586000070d21044b1000046c2f74000000010400a800027340ae07701bc20b85ae36a106129d40003c808801798e310000ab3233812f1fa0bc529286f63eb8b4d37382d9317caee26dca1d1298873153492526bc4b02c5ce631d54a2f1ff521e384c0622ba0fcd0b189553d886a30354f0e2e2c00000008c818ed177185c00037a4fa20e40226182919c265000040e4ee406e90ab19fcba33a0c02b3b8508f28d09db114c5a73f40f33423806c1d4cd2332041120744e4724b01630b58c2a3cf44810000b9f36ec2e305fc5832e70cbb1378d410f0413047404ea34ec9721c0ca692f289e603491d413889c62470c9716445a82b4077815a08f10000e5c328466745780002260da20000f2907243461e58e722cd4fc1032ca611abcf010f7d00347440001d482f8000000000001e31d091fe000022f00007a100007e30254091178c4b81758a050000000000000030b8000000000000000010000c1d00008964228520000000011102620ad8000145106d222000000000000000c4c3044f151ad8a783c40701000000027808a2156cd1f3a84e250784d2e055048500011fa452c72748943250ea076f08d43360000696353800000010ca37244f632900000e10e070000b90296417e0ef4cd03f742ea00686d038c89c200006f40000e450cb4f0304fc14630e4e6b000089a04dc00007d065e1e8c39541447750bd46f740048b32d40a6f31e49ce1b60fdc36d44d33e4c00013346292854cf501bcaa6448c86b2a644022a100a81390f0515fc2fa421000025808c11f511e11bfd1133264f2c00000000000ee900b84a900010c40000e8b43d4ae300000000e60ead0f44a010000844483848d1ca85ac3ff0de30591110361508c00005e20000000131048c038920f00001f13764b30000000035647b723b03b5000000007948261190761000000034000003b7c80a487400034881bd118878e1734bec40fc6e119406a7218c6090a88d3f08a49d133cc56f1a387263c3cf9f39488051bf0dfc205863242842123c1c81305848a729f4ca8426912001e4c1338841d50000762288818e147c96a09440003ad4fb90e5904431fcbd908f40131d2029135990f40000c5b312104d3e40ee6362c0003d48ba70000a322660b9611dc1ea19bd20938a4bfb2fc05a10dd494726fc2760cfc6e6375409c0d3c26f03e08d5134408f06e4d7300848ab162c73b0fac67a0a0c1eb44fcdf2044c0d91d0032c15b894a2f383432f545fd237c2aa35ecda7383800046f0b202914ae60000f1d00011f32664e6e0000000465c0770c44000259829e18b4d6b3010981057806d0000de42a28ae138641e20000ac80e4921424990171bd4186173816f19
  | 33 => 0xb4a375c6d720b400042d4cb32e34dec09c02061f0821645a514a057476c34dc7f01b245ad1c00dd2299ce6f44889460864000417ce562e2522445246772c40d114798e2f17b82e529342b907fc20b00000000000f3600000003b746690000a50409489b1c3cd210fc472238a00002dc11cb19ec0000af9004000005339f07d500004801e3000045c4d50000091120f40f50a980181be47f900000000058c853c2069724a000011fc3e01f844c8000039e00000e11cfc23b0000000000031a28b0294155c00018d8cf70d14c4e2b4467147b8b48285c8352d3113233e8f1424d000032f431d2770b823f9053b1f2025d1054c010f4c9b0160109e16e50483fd48931a880140fc8e9f04f49f34434f6328440dc341ce181f3487e2a1c01b010c9a328302bd02ecc5e1f009df0c59026296c0db0640edc0024b7b0810e9e03e4809092c3930a28fe91c547a72aa10dd27b000043545b61e802d20f38e0a3d249893ecd02c2bf008704e823031402850a540bc087c000290c000000000000000001304000086c6ad01550ed000000024549292418d6c1a6c96d314410936d88f710249cc45310d41850bbd05d00c90b5063f205cef512f0000040ca240450bae130ce5d2ca8b0d000061c0e04caa0000caf00000000000000000018b2c44acc20309312bd5085311479206308272ef02a41b9119d0de8c9411a43a21a746980000000129cd860bdc00025e4cea110c9d2000000042f5164000000002c40000000f6f0000000000063c1e7d11104c8e5713cc83b000000038cd2212d611dc234400029240001700282000117d1838acb3d6d15a45a8e6a000018848100642d2cc9509f91d521a03a306c80541f585f632d877e3e38c4208dd0293a2835e418d0803ddc2b5098ce223c70fb2278c94d2490ab80000a1040c059e2160efa104cc6640accc20000cd800000000000ec138c00003c78af91e9800000002ab2fac48200000002fc80001d9454337b8aa517a45842aa40ce2278ee846682f404403fc37440ed3968f310fe840e0ed08de0fb4a4e39a4f4b07cca441be006b2c74b840000c933f4412e1f4400021a80000000afd21904e132c8d7700000002560000279d0180000d4f36b120a000115b4280000061400001308b21e6c88e0f5c00034083a94260b5a4684a060758fa1126845c05a0c3c2ee47de02807c515b40000aa40000cecacd2e140002cf8a0d1ed91180f08000000856210b411516143e720880000d80cef3cac364223403e2f341330ec48fa30650c700c4db8130007a44b88180001227285051b1064f1a27602f1035c000312c0001ebc0000da8c7306580002e180000488e2d380cee32768d8800dc9391fd8b922d384d6074d1b343cc3993b2c6a917e8ec921c4000000000043bc2d31f1c0000bf0ee23a8007200005b135790
  | 34 => 0x80e141c0001d98bb2462ced4000106b14e00002a48000428c93c00011732970b0c14980003380000000000043dc00031dc00032dca134030b2211786cd04648bf06c46120034d96206515134e83a70add1023224c0b0000f6c3e0d0ff2a3cb54000041114104b92b282470fe020817b0cec4820000000000005a45f2018400033944061adc32200cc0002774b342930a262b1c55f00000000000ac52414801000000023c80002f5c6651040a3c2c3848a3954bf32a4c0000000bff2c0880d05e875e255cd9f3d28220291c00043f825b07602592efcfb1225400000010970cd11ed314ca0b3fcc8e81898a650878dfb35246a0180905300011a200005c60000e944764861407000012e800048400230001216247cc3f3b208e5136875d1bf45b52ca522831b0e3b157400042c8b0720400000000ccc000061d0000a630000af20000f6b000080b0000ec00dc800048c51da0000a3506000741d44f4746bc62c3684efd30d470e234000031909e21484d35434c5ca3d20ba93260dab2610d563b0c8db3034d5245804b30e3c1ae47a42272a30a620df461605ac1e41f3865b0a34e35198d12d14401530000dd3450c121143453e2880ed71d049aa17ccad83f205c92d885e70000da63e70c8f00003be000000042a8729309c90e0a0510b000099022e50cb3ce80002d0800000002e010d078044e819a0c8c5a92fe07dd20a435048483591e784a20b6800013e830e325848e1c585751ab10961ddc11f3e208993eb01bb21dd2030204914393000040f40003dc0b6346c025c1f940000000d5d0428def469400035f4800000116800008bb41a4de535a4ea90b408be312846f3dd8ef92f7000000000003dd4a2d2ebc0d6342036b05685df00000000284bf930380004224b9109ecb0927bc82a46e40ee2a04b682c604830e2d11243882ad21b48f90d44ebf0eb0b4130690600560938208cf352f9856006d4ee523c00002cfce4836f08b541bc45615b0c063584c78171c0572c540002a386d946c8d0a011cca910a8010239085202d00410bc81d716bc0860648d4d0da0fa7080c76730d00b818110381ba858c049852b1ee4274457027926540e53d9d181218879a39b4d9b10d4f95000036f14c07200000e052be11e4027812a25ecd1e3bb8000153078911c8ff7311cf0a0000bb61428d79295114f00006fb3e24b0527c40b73e74c4d1a94ef448bcd0c142418d2e4cdc4022c1a32c0cc1f47110db233c33d0000a8d00005880000c56055921a0000ea32d58de60cac000153882100006f20b1c90d01742503150bf41aa0747003cf340db061a0b611141f282b83b480000000b3a0774c362f0865711e81750000d401fa455545d8000355cba03bf88ea48b11e810e09c8000007c30bc0002ccc7bb30003c939840b3000000016f0a3b00003c700003330
  | 35 => 0xd84da442200002eb0000000067500009363a6cad741f007536088ad1d7cf242dcc57d368c0000000c1e00000000000bb72e78d9218643d5394cd5800011ae00009f63a18df4000065112bc1fd0430aac47805d700010e000000001d611831b68969000084642ed1b400000002710aea0b3cef2166523027f087617407540c2007b222920b26484041e400000d4c000000097e0000eec41001b3197507a0000a761bc4000293cc7e0000e09192c0003d30d8e31bd1a423680003a90000118400006783573af80002ea883c0830cbc3d849c53fe916d24ec000118c9ed41d05970000000119866e3ce4000049468124f8d620c0c4b546a4fec0000e1022bc00000003151ac91ac217c66800000003b3894514907f100000000000c5a41d90b40f2c00003740000000abf446c0002144b6f1c6c50506a414841e402600007e40c788890bf80602958cd4372800035b4d8d00008eb15c00000a7c9f93655022000020700000002c9802f00002380f480001d5810831d4c722b18391371c77035bd1c500000be0f1052245749fb14780000cf80003ad89673d709a20294260000054a29b8820073868c000002c45e48860a5d1160000fd308889d7399d1a0166cc8e00d07823a40fab176c00036c4000000048800000002fdcb6c20e4000000025e172000000004732f402643d0800000000001a007e02c00d943ae8abd000100d08385fc2f1c7211624a361f7000028700000e9800000007a900004cf307044207041a700004473a3000045bc4360000be40000000043c0004809013486cf813194bdb35d8b8e01443792094ded4540fe527543202d70f4312d0bf60080c38132473a42182af08e412309c8347407c00a23606ca34f05374514dfa34c897d2d4825a3240b1a2d001a62464d1836a856313545452f4c2ec071464f47188d9005c76845480301c2883e0dc40da013826b009c64043901c42d941af2274c100a64a5202345180a31027429c573002076436b441f2808c3036dc35b228c04407b40001a448a046ec0004728eb30bcc0b021d4af0170ce7747c4000136c00000000003ce000006a83f43bb464731a870c2724ffd00000003a10000000000022b8f740000f91188832f09dcf8a09a48f3361c0d1219800006b50722b64f411790e172f2c5d23d189bc00d86840d686154360e433aecbb512406493d148bd46303b038349593d10f8212a83ef2b1071d3fd0310021427115f0eab16510870000878267c0003fa02c20000759000000035100a40000ec50091217328d1881144fc42ad80004344000164c84a2db8c5c2ae811123d906600005533d7c0000000b8348640002e5c00000000002abc3af00000000000b3700000783be0b1c06e00001fd457141f400038484fb46643cc106cba51dad0d03734cd920e000037405350890232249c
  | 36 => 0x3f72e00000000087a43b0c91105920000000000de05d540400003ac010d26cc7d93458749343d142135000009e055c12a0000242c63a3fb513114750eb430c7f72a44b5f1280af148a81cc03f4ac203f091e26210fc1b048c02f9522b26b812821080001180000000072c2a8cc8700003013ef0000000094f0efc0004018b0a3b7837e0a406e934a0c7d33fcd980fc11fc23a4f8c2b50e781b3caaa0000e9d2f300004854000227c0003db40000000e343de0e2b0000a0711b4d101584255010038a2020c1500002bb17dc0004244b141efc6e30b14850041844e2250cfd318862b13fc9f200009090000a0e37d840a1445073000048941688600298d0d15206e2355414c1a08b5911f82dc0f8cdb205b4374092400045580004158a2338e400007e000018f81ec2aac00000010dc47b0fa03dc4e3d0c1c2a704908741a7906a356865303c09d93fc8e4e39d8e5f25b019701147d73388498438cbab181466c0dcd0423234c3e3ee09491b78fb708accdc2e6c8d435809442ee0e0001640c33e78b7c44244591bf88c30e6c8a4160414d340cb2125bc527149450e2df8d6e2eb4c0a24691002f048c6360ce8029e85ab1d349b9405112628a8975178485d12f410102687932d1464615e0e70427d11f2f3c127290022c0ce8933143c2402ad087c4454cf043849bb38802b13454c2420a03c50f0cca50f3d0281920e020c344ac306ca7e19643b20850363303ce4b17ed17805b053f34d910546e08370d9ccdb02fd15813a0e853c84cc81690d30393513e0d00499152432e02750ac04d4e40466c3663c4830b2618ce119c8e491ffc3e802a894c406c5cf335ceb816c90652dd89ee11d84d22fa100f1dfc4d73b6411807d84001e9400010b885b000072827f45f82e50f7f44f42520ab886c2c0423c2794d044078c9a052876a411c01d28dc00007b88fc19a80c800007da00000002cac000187c00047348e6066c0001b2047c000097620d000031d07ed34bc3130a1c7ee06f91ce40b48f503c4d80311099c000000000011803b811ad37fc00000000000000ec6488862736d084b0000d014870000000000038186d11f1000012587b822f097416cc1733abcb570dc0fb5000000007e4c4602109d4266c000367901a3ac40001dd0b461b580004624a3f1e2109c169400000005dd0000b0441c48a5122cb25144c0000a205f424087ae28f8deb375800012b500800000000b7c9a6377805b25dc00011547db4830a9e39e51590000f4f2a9078f1fe80000000ce8220c00030ec9f40000b8f000000011e44ec474c0480000aa01500000247496b024000013140000c0844d4028d65190d20100001f71db4397488d0cf46e80921f6103403500002b7c000000000029f08ff25f08c52fd400010882bc000000010f800000000000000000395051900002b0
  | 37 => 0xd2eecd3947f4a801cc0293000000043a800000000000000000477913803e83a41c148a63bec64a04f000010ecf323850fea2b8068700008cb00000002b0400003104ed0000a1e1fec000000000001b800000000003520d1900000001aa835600006cb052c3e13f50000000021a33e4804000084021ec576000000047e428600001cb064c000000046b10ccbd44288f53334508315911df09b112f0d60e8d11e000011c0c281b740003cdc5d1000000037f841e02e455128c0bf101c49532d901d44114b381ad11cf237400014b8000279053145f09913c3430a305c83a43c107e00001b01b9400000002c809a921313989543324e362a2cfbd25706ef20c012b221cdcc11209a7310c8b134480ea411917a233001e0ad10fb339c2343baccc70d350000b7895d13b840126a50e810a06df20fd22d3e50b7531a00d8125c182408cfbf349498339fc00013dc54b000091025a10022f84d060ee498e00000002700f98019cecc4365185287c0a70e800001a2505832d08ef2c900000ff400042d91d736748e31b6c6561648056263c7df08a06903f780e820c4e713f687d03f590192410a1b22e0fb01254eb42d4cd7c0000b9d2f100cd0000b44000009f0000c8c1cb4df53c2408018d01590000e9c000000009383dd2d4467e3530c611c1000044d000006847ad23f897003280001ad4cc436a4df91f9828b0000000000000035a89934044d7a0c600000000000000000000000000eac0000000d1300004393f0000033c83de0000a4b0b6c1761a700c70000000000045032c05d84834c63447811c10bce0400a47071b482672c6c529246ca821bacc67060c0002aec48717a918403c89072c6513c088c0052ac9094402cbb32de83521b9cbee295492f3bf071225e8ab0387c81420905f00dd87fc02d802d34f41fb42742cc479ce4a41385ef15dc88b19e0acf07a0fe138e853a206cccb0b346fa3cbcd2a033c4dd415ce68191000026b46791e5c42000000000b3823e3a08bb40afc00021340000000b69424069a4880ad240f02c90b2c000292000000008904394000213800000000001cc4d5c308c6ab417890f376c38036682e11aec387364c87f38903cd3a686bf4520ff93ea0d27114857e0e18bd134749632e883bb068843c2a70b39449ca5f262c6940b10e733cc0ae71068fc71a0c7ba133844617a036929d058d4510e5116e82893da04dc0d111d222dc865424861e05dc71446980000000a0f1750a832e68c2d1a34ae200007f246544c244dc17c13f071719480c613c422e24fc2362b4c1d9328800e085cebc0000cae00002e600007a4415105c211c0000000ba80000c090624b4f0000ae9267441712f83ea1ea8000000000000001cd3b347910b441c022b014534ccf642daca120000000478c0003e10ed820cd19837700001d6c000000
  | 38 => 0xa45441d68add00007440000000000000008fc3ca1cd90b0368013b155860c3c100000000a9811d504b46440002d80a9a38e0f063aa08d71dd8db92ddca332ca0f001e34ddf12b89c30e7433c0ca8e08350ca7f47fcfa332d4da5335475747e09610458e581b1514e301c90329a0dbf2f246ae3d5042630f4df72ac50d62f9cad52c2c608357c3ad23e04cb0c6ceac0bf44a319990cc03b0abc0c98dc83fed08223b8a9f3908eaa2704e3c35c510e44901663e6d1282de004d3bbc71906286a401943d847eca7137c022a00000000f403b339ec00000004b713c800000000000000a5e13d4ef60c5d0551fe0ef302206863e6851229b015012782f933f00000718000110515f46d51ab00f4cda36244bf2068eb94300d1735fc80318c400011011f005a8d1c463c4ef29a85744474e3f1c400832cd893d000000001f4000000000000006ce24d45b01dc400000003aa21c032100009a1274ce2331f00ff000046702b094233189b40000ab739887b23b9c16e225cc5227e81d20accc833c60ef11cac03a10e84f0000000000000000000b6748cc0001e100001cc8fc30000000215860d00009160a4894b2c4c0063f18b2c10208120000b5d0d2d11c31b861b0ed86ed14b097f1b080c203a4389461c0001a4c5b709b849c320031200fc6953fc4fd830200b23768ce4401ca19399510820c89560e844ab11a848f238851c4418d742310a2543b8aae46a800342b47094368662066067030940663b6c00004b51f62b384e9087064513d11f236cc280334d0c90d301c834802a0000113015c8ccd3154e1b2b90922041cc71046815513ac95e1b1cb6a2070e7423b4f7d450053d15e40001e282ff2c3c77b0000bc300004e343d8b723d601d02ec11c01da45bf14081fa1f482454464845079c34a29e40a22248b1e337d172261488100650333220aff3830eea24c829c2dfc6b9103d0640708e443ac8afe1ef4be0045c71c39f496542540503878e872ff0917373d04a34b025f0250b084015121030481e0958f7e28e45a026f8de840905eb18dc14e3dc81843e945c100006e0440400000009de0580fbb000004b1248e6008449e92868fa900005de3de493a000059d0fe4a0a33785320b9c7830a8c1993bdcb71156413629ecf9728a48491fa85901d40c3a1ac522e3e640e645ac8843a5cc57102cdc017306031af11f424c0c9b1f301e04080000000065f3788fce05c40000000b2d3b28a8843f44b60000dc5290417208341db3f5c99625e082b02f47a83b5850636644d844a8e111c080001cd4a8924308e735a088c000081d2c18000101c3fb1a480000000000067106744e487d182c72e40d8f6045ecd0b0bb512c0ff8f921e50a283a0465a47743ae18c07180bbc5d30000642354cae5223d077000003b00011e52f00000467800000f10f9000049
  | 39 => 0x219c403000038c0000d3109e80000674d8400011c93544000000000002a499746dc5e539b02443c7cba41fbcc690d3805a2590724469c0323d985cb145427f327c9a025000003f6454136c0bfa3a2121f201830933a4e460f6cfcb3c88ceb01704490a5910c393c4b221541392ab47ab0d941b6198429817e4f0240c9196221513532b516503bcaed03cc0e42f609130a6c4fd29cc655165474f3e98b8745d46be31609bd1e180a341e0e98246116e0b54f13079846810c83f32cb8a210a951d83270624313c4862694430139cf87254815b093caef00004a43ed01940d210b7389d1900a745c231ec0002348a661c441da34500e01210c6d16a83553b080001ed410544d85b406acaf4000031f48180002f8850c2bd88b4026456645d0f282e04d814584a60186052d000043720d8f8f000038516980df0000fd53d004931174e7e26a0ddd0b8895b085400023090123180dc2073c7062e64f501bcc6ba0bc000009f016235e0b4727c0cbf3df00000ddcb6107a420a47bc3881400170103400047dc86f3804425435c3b733d0dc112440000148c290c3d2293c9501645889d640d4000000024800000000000df31a3cbe91ec4314000104c082464e000000032f8e0f33b467c108c08a159c41400011703630a85309821029c80582a885b82b2442b19d8cca168c00c0d043dc13641870f9800033c4cce0000ffe2de40000cdc64100000000c70149416cc5923340002e6043f0f580002cec000000111a28b800010a4b161b0000000000000000bdf000000000486283d6400027f8a1600010a82c4847d1acc0000000e9630ad0620001182000103a1194000213004f0f20d2400006cc18bc41818d4c9d000063d46f82a8000000026e8d970bace0b43c4000000059800010a910f4a421ac06210000a862ef80002b00e26403890a025cdea3a98dbd0000f4d071cf7b43047730000a3d00002e82bec5d91de4cac1b551c71ec00000000ce300002683550daf271cd05000000042fcf6e3300c5d238433026d800006dc02835c11532960aec4148e8e30dc33901d919f3858ff8017881141742a132e123222081bf0b29166248028e26e011b207d1e23ea8038370c33130800d3024cfca32990f82860f513b685031cd060f1b10fe638f8d4b31c062a0000a090000815065400000010b10001146050400036e851700004df3c58225093400019acd9007280692d98000000000003dc00027ac0000000000188c0003b440000ce01ac0001226068105914589712820e9915
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xd5348421b418018d5348421c447654d43484218a6869d94348421c2476d4d4348421c847694d4348421b058594d4348421c247654d4348421c847654d4348421e077654d4348421d067654d4348421d047654d4348421e047654d4348421c047654d4348421c84641cd6048421ac08358060484218a687d912154021e21644855014021e41634855014021a45831952108540a24815886255330a24825846155330924875512108730e055458d2108730e09635494010030e11635454010030f014354a514c030f0143949514c030f0143549514c030a3281d506050f20a32819946050f20b058114d434cb20a2681d506250e20a26819946250e20b118114d434c220c15735846115120a15831516114d20b058114d434c920a288550c604c920b118114d434c120a288550c624c120b088550d324c120d087550d324c120e086550d324c120a24815946250c20d09535c06250c20a30815946050c20d09535c86050c20a29851886050c20c29751886050c20e09531886050c20c0c7654d4348020c187654d4348020d09545cc5448020d21545c45448020a89831906348020ca0645c463480208a8865d25348020c28761915348020b09831915348020b098418d5348020e086418d5348020b418118d5348020c487654d43480208aa869d94348020c2876d4d4348020c887694d4348020b098594d4348020c287654d4348020c887654d4348020e0b7654d4348020d0a7654d4348020d087654d4348020e087654d4348020c087654d4348020c88641cd6148020ac08358461480208aa86dd15148020d21745445148020d41735445148020949831d541480208a8865d33148020d097454f3148020a2a82d506050f10a2a829946050f10b058214d434c710a2682d506150e10a26829946150e10b098214d434c210c0d735886215110a0d831516214d10b058214d434c510a308550c604c510b098214d434c110a308550c614c110b108550d314c110d107550d314c110e106550d314c110a24825946150c10d11535c06150c10a28825946050c10d11535c46050c10a31851846050c10c31751846050c10e11531846050c10c147654d4344010c187654d4344010d11545cc5444010d21545c85444010a91831906344010ca0645c863440108b0865d25344010c30761915344010b11831915344010b118418d5344010e106418d5344010b418218d5344010c507654d43440108b2869d94344010c3076d4d4344010c907694d4344010b118594d4344010c307654d4344010c907654d4344010e137654d4344010d127654d4344010d107654d4344010e107654d4344010c107654d4344010c90641cd6244010ac08358862440108b286dd15244010d21745485244010d41735485244010951831d542440108b0865d33244010d117454f3244010
  | 1 => 0x185ca1504464d07d0c041a05d1c72000002c003e800d6002380060001180000bc399a02a00001500625002009e0b00250003b000f0000600001625e002900069252b0003e269c0b6a2582ccfc0152828a08d000883c000022d2a0051a6000c10409174024b871220000100360f5f07400565d99c009243800e20022000004c4480070003d801209f1586800610280000000000000000023d4e0e5bad538001d000f2002989800002f99956191603526001b800008100000003f32000c4510004882ad001b040c0000000011242e0000032800005c1ca58eeb41e8245000001646cae271d1846a378cc18a9001d918a600280ea451aa0c287a2c000f8004e8b8004318885365d4f181326d2480000bd31800a4291922896005928400073f800b400000005a00000016c55098005e27542fcdc883c0415e002ba1000aa15108040100002040100c0c010600402050000004000300c0e460000004010380c02060081000000002006010d81c0600000000606008040012000080200008081203068000605008140000c0f7658d5214b43c177658d5114743c1b7658d5014343d2071dc15214943d23711c15214943d20711c15214943d2072dc15114543d23721c15114543d20721c15114543d2072dc55014143d23721c55014143d20721c55014143a30805846155332a30815806055332d05735084254432f01434c95194032f01434ca5154032f01434c95154032d09735084254032a28805886255331a28825806055331e05635494110431f01435493194031f01439493154031f01435493154031d11735044154031a3280d506150f21a32809946150f21b098014d434cb21a2a80d506250e21a2a809946250e21b118014d434c621c19735806015121a19831516014d21b098014d434c921a248550c614c921b118014d434c521a248550c624c521b048550d324c521d047550d324c521e046550d324c521a28805946250c21d05535c46250c21a30805946150c21d05535c86150c21a25851886150c21c25751886150c21e05531886150c21c0c7654d4348421c147654d4348421d05545cc5448421d21545c05448421a85831906348421ca0645c063484218a4865d25348421c24761915348421b05831915348421b058418d5348421e046418
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x71a8a0019806b8000080b0052441040a41481931917018d21087008ecc18c8a9a4210e801918018d5348421a034b4eca9a8690843404975516348421cc290326322e231a40106021d9831915348020d003230231aa69004140a969d95350d200828112cba2a798a401052064c645c86344010c083b306322a688021a00646086354d100428252d3b2a6a1a20085042597454f3244010
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
  | 7 => packedAt gbK7 (770+((h/14+packedAt gbK7 (672+(h % 14)*7) 7) % 88)*7) 7
  | 6 => packedAt gbK6 (58869+((h/633+packedAt gbK6 (51273+(h % 633)*12) 12) % 2506)*12) 12
  | 5 => packedAt gbK5 (419878+((h/3280+packedAt gbK5 (373958+(h % 3280)*14) 14) % 15719)*15) 15
  | 4 => packedAt gbK4 (248529+((h/1553+packedAt gbK4 (228340+(h % 1553)*13) 13) % 5593)*14) 14
  | 3 => packedAt gbK3 (12285+((h/65+packedAt gbK3 (11700+(h % 65)*9) 9) % 283)*9) 9
  | 2 => packedAt gbK2 (1090+((h/5+packedAt gbK2 (1065+(h % 5)*5) 5) % 22)*5) 5
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xff83fff03f1f8fe1e3c7fc7fc70707f863f49f
  | 1 => 0x7fc1fffc01ff1fe03f8ff8ff807f8399c78e7
  | 2 => 0x7ffe0ffffe001fffc00fff1fff8003e1f8f07
  | 3 => 0xf80000fffffffe1fffff0001ffffffc7e00ff8
  | 4 => 0xffffff000000001ffffffffe00000007fff000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x30b842118a25104060c12c12c111138821b48b
  | 1 => 0x5109c422864a028601485485482270908c58a5
  | 2 => 0xa2108e451403250aa400992192702122168d06
  | 3 => 0x421088201000110a12000024848405400250
  | 4 => 0xc463180e389c49ddd3a4e24800c0c607fb6000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 31 gbPos gbNeg, 0xfee8fe80fee8fe80fee8fe80fee8fe80fee8fe80fee8fe80fee8fe80fee8fe80fee8fe80fee8fe80fee8fe80fee8fe80fee8fe80fee8fe80fee8fe80fee8fe80, gbN, gbR, (fun _ _ => 0), gbI⟩
end PEqualNP.Outside.L_meta_12347
namespace PEqualNP.Outside.L_meta_12347
open PEqualNP.Outside.L_meta_12347.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 15 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_96 : Interval gbAtlas 3 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_192 : Interval gbAtlas 3 192 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 195 := (concat bgb_3_0 (concat bgb_3_96 bgb_3_192))
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
theorem bgb_4_4608 : Interval gbAtlas 4 4608 52 := block_range (n:=52) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 4660 := (concat (concat (concat (concat (concat bgb_4_0 (concat bgb_4_96 bgb_4_192)) (concat bgb_4_288 (concat bgb_4_384 bgb_4_480))) (concat (concat bgb_4_576 (concat bgb_4_672 bgb_4_768)) (concat bgb_4_864 (concat bgb_4_960 bgb_4_1056)))) (concat (concat (concat bgb_4_1152 (concat bgb_4_1248 bgb_4_1344)) (concat bgb_4_1440 (concat bgb_4_1536 bgb_4_1632))) (concat (concat bgb_4_1728 (concat bgb_4_1824 bgb_4_1920)) (concat bgb_4_2016 (concat bgb_4_2112 bgb_4_2208))))) (concat (concat (concat (concat bgb_4_2304 (concat bgb_4_2400 bgb_4_2496)) (concat bgb_4_2592 (concat bgb_4_2688 bgb_4_2784))) (concat (concat bgb_4_2880 (concat bgb_4_2976 bgb_4_3072)) (concat bgb_4_3168 (concat bgb_4_3264 bgb_4_3360)))) (concat (concat (concat bgb_4_3456 (concat bgb_4_3552 bgb_4_3648)) (concat bgb_4_3744 (concat bgb_4_3840 bgb_4_3936))) (concat (concat bgb_4_4032 (concat bgb_4_4128 bgb_4_4224)) (concat (concat bgb_4_4320 bgb_4_4416) (concat bgb_4_4512 bgb_4_4608))))))
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
theorem bgb_5_9792 : Interval gbAtlas 5 9792 49 := block_range (n:=49) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 9841 := (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_96 bgb_5_192)) (concat bgb_5_288 (concat bgb_5_384 bgb_5_480))) (concat (concat bgb_5_576 (concat bgb_5_672 bgb_5_768)) (concat bgb_5_864 (concat bgb_5_960 bgb_5_1056)))) (concat (concat (concat bgb_5_1152 (concat bgb_5_1248 bgb_5_1344)) (concat bgb_5_1440 (concat bgb_5_1536 bgb_5_1632))) (concat (concat bgb_5_1728 (concat bgb_5_1824 bgb_5_1920)) (concat (concat bgb_5_2016 bgb_5_2112) (concat bgb_5_2208 bgb_5_2304))))) (concat (concat (concat (concat bgb_5_2400 (concat bgb_5_2496 bgb_5_2592)) (concat bgb_5_2688 (concat bgb_5_2784 bgb_5_2880))) (concat (concat bgb_5_2976 (concat bgb_5_3072 bgb_5_3168)) (concat (concat bgb_5_3264 bgb_5_3360) (concat bgb_5_3456 bgb_5_3552)))) (concat (concat (concat bgb_5_3648 (concat bgb_5_3744 bgb_5_3840)) (concat bgb_5_3936 (concat bgb_5_4032 bgb_5_4128))) (concat (concat bgb_5_4224 (concat bgb_5_4320 bgb_5_4416)) (concat (concat bgb_5_4512 bgb_5_4608) (concat bgb_5_4704 bgb_5_4800)))))) (concat (concat (concat (concat (concat bgb_5_4896 (concat bgb_5_4992 bgb_5_5088)) (concat bgb_5_5184 (concat bgb_5_5280 bgb_5_5376))) (concat (concat bgb_5_5472 (concat bgb_5_5568 bgb_5_5664)) (concat (concat bgb_5_5760 bgb_5_5856) (concat bgb_5_5952 bgb_5_6048)))) (concat (concat (concat bgb_5_6144 (concat bgb_5_6240 bgb_5_6336)) (concat bgb_5_6432 (concat bgb_5_6528 bgb_5_6624))) (concat (concat bgb_5_6720 (concat bgb_5_6816 bgb_5_6912)) (concat (concat bgb_5_7008 bgb_5_7104) (concat bgb_5_7200 bgb_5_7296))))) (concat (concat (concat (concat bgb_5_7392 (concat bgb_5_7488 bgb_5_7584)) (concat bgb_5_7680 (concat bgb_5_7776 bgb_5_7872))) (concat (concat bgb_5_7968 (concat bgb_5_8064 bgb_5_8160)) (concat (concat bgb_5_8256 bgb_5_8352) (concat bgb_5_8448 bgb_5_8544)))) (concat (concat (concat bgb_5_8640 (concat bgb_5_8736 bgb_5_8832)) (concat bgb_5_8928 (concat bgb_5_9024 bgb_5_9120))) (concat (concat bgb_5_9216 (concat bgb_5_9312 bgb_5_9408)) (concat (concat bgb_5_9504 bgb_5_9600) (concat bgb_5_9696 bgb_5_9792)))))))
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
theorem bgb_6_1824 : Interval gbAtlas 6 1824 75 := block_range (n:=75) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1899 := (concat (concat (concat (concat bgb_6_0 bgb_6_96) (concat bgb_6_192 (concat bgb_6_288 bgb_6_384))) (concat (concat bgb_6_480 bgb_6_576) (concat bgb_6_672 (concat bgb_6_768 bgb_6_864)))) (concat (concat (concat bgb_6_960 bgb_6_1056) (concat bgb_6_1152 (concat bgb_6_1248 bgb_6_1344))) (concat (concat bgb_6_1440 bgb_6_1536) (concat bgb_6_1632 (concat bgb_6_1728 bgb_6_1824)))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 5 zero,inputs.getD 4 zero]
def fullWord : Sig := 0xfee8fee8fee8fe80fee8fee8fee8fe80fee8fee8fee8fe80fee8fee8fee8fe80fee8fee8fee8fe80fee8fee8fee8fe80fee8fee8fee8fe80fee8fee8fee8fe80
theorem fullBound (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have low := boundgb certgb
  have lift := lift_ok (u:=true) (ms:=fixRows 32 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 5 zero,3,35)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 5 zero,3,35)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276682472 * 2 ^ 32 + 4276682368) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_12347.Model.Repr at out
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

def mono : List Gate := [⟨.or,[4,5]⟩,⟨.or,[2,6]⟩,⟨.and,[2,6]⟩,⟨.and,[1,7]⟩,⟨.or,[3,8]⟩,⟨.and,[2,3]⟩,⟨.or,[9,10]⟩,⟨.and,[0,12]⟩,⟨.and,[1,10]⟩,⟨.or,[13,14]⟩,⟨.or,[11,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276682472 * 2 ^ 32 + 4276682368) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276682472 * 2 ^ 32 + 4276682368) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_12347

open PEqualNP.Outside.L_meta_12347 in
theorem PEqualNP.Outside.L_meta_12347 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276682472 * 2 ^ 32 + 4276682368) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276682472 * 2 ^ 32 + 4276682368) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound allgb)
