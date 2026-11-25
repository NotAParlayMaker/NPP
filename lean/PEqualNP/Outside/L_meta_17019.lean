import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_17019.Model
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


end PEqualNP.Outside.L_meta_17019.Model

namespace PEqualNP.Outside.L_meta_17019
open PEqualNP.Outside.L_meta_17019.Model
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

def SBf (j : Nat) : Nat := [6, 6, 7, 7, 6, 6].getD j 0

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

end PEqualNP.Outside.L_meta_17019

namespace PEqualNP.Outside.L_meta_17019
open PEqualNP.Outside.L_meta_17019.Model
def s0K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x1180a02800bf43bd43be40bc40de30dc30
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x2270a0a1e610030
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 6
  | 3 => 2
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (i*5) 5
  | 4 => packedAt s0K4 (i*16) 16
  | 3 => packedAt s0K3 (i*27) 27
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s0K5 (6+((h/1+packedAt s0K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s0K4 (102+((h/2+packedAt s0K4 (96+(h % 2)*3) 3) % 8)*4) 4
  | 3 => packedAt s0K3 (56+((h/1+packedAt s0K3 (54+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0x3fffc0fffffe0c1ffffe0fff07fffe00f3f3fc
  | 2 => 0xc1ffff03f07fffe0f83ff0fff8780fff4c7ccf
  | 3 => 0xfe0ffffc007fffff003fff0fff800fff8f8f0f
  | 4 => 0xfffffff800fffffc0000ffffff003f00ff0
  | 5 => 0xfff0000000000ffffffffff000000003fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x84204628a0101005284e0113008a621811b15c
  | 2 => 0x94448a1904a484a05a1290a54850a4a94454c5
  | 3 => 0x8a914406949094b04252a0a950149528a8b0a
  | 4 => 0x294e20924c0dae729681888ce6658063e00ea0
  | 5 => 0x318c38e38e71cf9ce739ccc0c4460183ff6000
  | _ => 0
def s0Atlas : Atlas := ⟨5,rawDecor 62 s0Pos s0Neg, 0xfcccfcc0fcccf000fcccfcc0fcccf000fcccfcc0fcccf000fcccfcc0fcccf000fcccfcc0fcccf000fcccfcc0fcccf000fcccfcc0fcccf000fcccfcc0fcccf000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_17019
namespace PEqualNP.Outside.L_meta_17019
open PEqualNP.Outside.L_meta_17019.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0xa0046200820de43dd43be40bc40de30dc30
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x202b0a0a1e610030
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 6
  | 3 => 2
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (i*5) 5
  | 4 => packedAt s1K4 (i*16) 16
  | 3 => packedAt s1K3 (i*27) 27
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (6+((h/1+packedAt s1K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s1K4 (104+((h/2+packedAt s1K4 (96+(h % 2)*4) 4) % 9)*4) 4
  | 3 => packedAt s1K3 (56+((h/1+packedAt s1K3 (54+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x7fffff01fffe0c1ffffc1ffffe0ffe00f3f3fc
  | 2 => 0x81f83ffe0fffffe0f83fe1e03ff0ffff4ccc7f
  | 3 => 0xfe003ffff07fffff003ffe003fff0fff8f0f8f
  | 4 => 0x3fffff800fffffc000003ffff003f00ff0
  | 5 => 0xffffc00000000fffffffffffc0000003fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xc30011c21041003184c02238e0112181151bc
  | 2 => 0x24425224642884a06a1521449290a4a944c455
  | 3 => 0x1094a4488351094d042a5409252a09528b0a8a
  | 4 => 0x596738914a1dae76b683111239ccc063f00f60
  | 5 => 0x618630e18c61cf98c733999c01888183eea000
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfaaafaaafaa0f000faaafaaafaa0f000faaafaaafaa0f000faaafaaafaa0f000faaafaaafaa0f000faaafaaafaa0f000faaafaaafaa0f000faaafaaafaa0f000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_17019
namespace PEqualNP.Outside.L_meta_17019
open PEqualNP.Outside.L_meta_17019.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x90c00b800000296188c00f0040e803c00c00340101100002241a38a014c492a726090a2066ca993e2ce000e2050600e58000818419b000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x38440002b00681183ebd1b0320000d00cc03a3c384014a293aa0aec3202c4d6b236400044cd403c0685cb60ea00247aa4a1c7c758ae223059258240000055fb42e01b8f02080008300501000e3c08106142808408322b7a92876c5250eeea2a1dd14543bda8287785050edca421db54843bda8285785050abca6215754c42bba8a6574514ca7ca8194f55032af29e835d53d06dca5a0db54b41b7294836d52906f4a120de54241b7a92636c524c67ca818cf55031b7290636d520c6f4a018de54031afa9a435c53486f4a010de54021b7a92816c52502bca6205754c40b7290816d52102eca2205d544409f2a6613d54cc2dca5985b54b30b7294616d528c2eca3185d546309faa2413c54482eca2105d544209faa2213c54442bea6885714d10b7a92216c52442dca4085b54810
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 40
  | 4 => 64
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s2K6 (i*5) 5
  | 5 => packedAt s2K5 (i*16) 16
  | 4 => packedAt s2K4 (i*27) 27
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s2K6 (6+((h/1+packedAt s2K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s2K5 (718+((h/13+packedAt s2K5 (640+(h % 13)*6) 6) % 53)*7) 7
  | 4 => packedAt s2K4 (1875+((h/21+packedAt s2K4 (1728+(h % 21)*7) 7) % 77)*7) 7
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfffffe03ff8307fc3fe0fffff83fe0138fe7c
  | 1 => 0xf01f83ffc1ffff83fc3ff0780ffc1ffecf338f
  | 3 => 0xffe003fffe003ffc003fff800fffe0030fc3f0
  | 4 => 0x3ffffffffffffc000000ffffffff003ff
  | 5 => 0xfffffc0000003ffffffffffff0000003fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x614510238411500cc04642a8e590aa2818563c
  | 1 => 0x24c214448ca11281441a523122948c984b3285
  | 3 => 0xc28b5a891875b5b4222d6b224b5ac8530dc3d0
  | 4 => 0x8b1463122144295aaa8108048c631163b0016a
  | 5 => 0xc18421c31862e6333318c4700420183e6a800
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeeeeeaaeecc0000eeeeeeaaeecc0000eeeeeeaaeecc0000eeeeeeaaeecc0000eeeeeeaaeecc0000eeeeeeaaeecc0000eeeeeeaaeecc0000eeeeeeaaeecc0000, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_17019
namespace PEqualNP.Outside.L_meta_17019
open PEqualNP.Outside.L_meta_17019.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x40e225c59e004c00c30587840000005248ce9a2001300000000d00500a12a011250418d83321d200389c01f14804831541c8153003042000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0xf0012080001c0001b1b6ae071e003df86007403730e80000090013688c0000001700000000000b013300018a8009c0002c00000760c02b00000052a8969712000007c34830003003914659000005ea522a841f4ca4021006802000bca07002c0000102040840014007000001504002800620001b7a92876c5250eeea2a1dd14543bda8287785050edca421db54843bda8285785050abca6215754c42bba8a6574514ca7ca8194f55032af29e835d53d06dca5a0db54b41b7294836d52906f4a120de54241b7a92636c524c67ca818cf55031b7290636d520c6f4a018de54031afa9a435c53486f4a010de54021b7a92816c52502bca6205754c40b7290816d52102eca2205d544409f2a6613d54cc2dca5985b54b30b7294616d528c2eca3185d546309faa2413c54482eca2105d544209faa2213c54442bea6885714d10b7a92216c52442dca4085b54810
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 40
  | 4 => 64
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s3K6 (i*5) 5
  | 5 => packedAt s3K5 (i*16) 16
  | 4 => packedAt s3K4 (i*27) 27
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s3K6 (6+((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s3K5 (718+((h/13+packedAt s3K5 (640+(h % 13)*6) 6) % 53)*7) 7
  | 4 => packedAt s3K4 (1875+((h/21+packedAt s3K4 (1728+(h % 21)*7) 7) % 111)*7) 7
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xfffffe03ff8307fc3fe0fffff83fe0138fe7c
  | 1 => 0xf01f83ffc1ffff83fc3ff0780ffc1ffecf338f
  | 2 => 0xffe003fffe003ffc003fff800fffe0030fc3f0
  | 4 => 0x3ffffffffffffc000000ffffffff003ff
  | 5 => 0xfffffc0000003ffffffffffff0000003fffc00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x614510238411500cc04642a8e590aa2818563c
  | 1 => 0x24c214448ca11281441a523122948c984b3285
  | 2 => 0xc28b5a891875b5b4222d6b224b5ac8530dc3d0
  | 4 => 0x8b1463122144295aaa8108048c631163b0016a
  | 5 => 0xc18421c31862e6333318c4700420183e6a800
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeeeeeaeaecec0000eeeeeaeaecec0000eeeeeaeaecec0000eeeeeaeaecec0000eeeeeaeaecec0000eeeeeaeaecec0000eeeeeaeaecec0000eeeeeaeaecec0000, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_17019
namespace PEqualNP.Outside.L_meta_17019
open PEqualNP.Outside.L_meta_17019.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x602084a0005f741f441fb40f840f710f510
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x8036082204d15110
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 6
  | 3 => 2
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
  | 4 => packedAt s4K4 (104+((h/2+packedAt s4K4 (96+(h % 2)*4) 4) % 10)*4) 4
  | 3 => packedAt s4K3 (56+((h/1+packedAt s4K3 (54+(h % 1)*2) 2) % 4)*2) 2
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xfe0fffffc07e0c1e3e1ff0fffff83e008e3fcc
  | 1 => 0x3ff03f83ff800fe03fe1ff0f80ffc000f3ccf0
  | 2 => 0x3fffc003ffffffffc001fff000ffffff03f0ff
  | 3 => 0xc0000003fffffffffffe000000fffffffc00ff
  | 5 => 0xfffffffc00000fffffffffffff000003ffff00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x926285504704dc06068a34568e5d2a288615cc
  | 1 => 0x94a58a54891cece01aa8d54712ad6850b2ccf0
  | 2 => 0x84113191228452a4001666224318c99037055
  | 3 => 0x118a2c6224508a54accc000448c63162dc00aa
  | 5 => 0x210c300038610399311188887000018369aa00
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xfeeafeeaf000f000feeafeeaf000f000feeafeeaf000f000feeafeeaf000f000feeafeeaf000f000feeafeeaf000f000feeafeeaf000f000feeafeeaf000f000, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_17019
namespace PEqualNP.Outside.L_meta_17019
open PEqualNP.Outside.L_meta_17019.Model
def s5K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x28600a00430f741f441fb40f840fa10f910
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x236082204e15110
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 6
  | 3 => 2
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
  | 4 => packedAt s5K4 (104+((h/2+packedAt s5K4 (96+(h % 2)*4) 4) % 11)*4) 4
  | 3 => packedAt s5K3 (56+((h/1+packedAt s5K3 (54+(h % 1)*2) 2) % 4)*2) 2
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfe07ff83c0fe0c3e3e1ff0ff80f83e009e7ccc
  | 1 => 0x3ff83fffff000fc03fe1ff0fffffc000e38ff0
  | 2 => 0x3fffc003ffffffffc001fff000ffffff03f0ff
  | 3 => 0xc0000003fffffffffffe000000fffffffc00ff
  | 4 => 0xfffffffc00000fffffffffffff000003ffff00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x92b285544e24dc0e168ab456925d2a288e3ccc
  | 1 => 0x94518a50821cecc00aa855470ead6850a285f0
  | 2 => 0x8211319144845524001666224318c9903d055
  | 3 => 0x11462c6228908aa4accc000448c63162f400aa
  | 4 => 0x2184300030e103393111888870000183596a00
  | _ => 0
def s5Atlas : Atlas := ⟨5,rawDecor 31 s5Pos s5Neg, 0xfeecf000feecf000feecf000feecf000feecf000feecf000feecf000feecf000feecf000feecf000feecf000feecf000feecf000feecf000feecf000feecf000, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_17019
namespace PEqualNP.Outside.L_meta_17019
open PEqualNP.Outside.L_meta_17019.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xa401a00816803a0c712664410050dca001e0000800d921362b1a090a112ae008c0003600080000178b0cc800a7000b077279d9500d402220c132100a8c1c745c6273e34c8000000000000000560c381821404000040850002380850000001007fd5001fe54007f55001fc54007fd4c05fe53007f54c05fc53007fd0c05fe43007f50c05fc43007fd4803fe52007f54803fc52007fd0803fe42007f50803fc42017fcc803fe32007f4c803fc32007fd4401fe51007f54401fc51007fd0401fe41007f50401fc41017fcc401fe31007f4c405fc3100ffc8401fe21007f48403fc21007fd4001fe50007f54001fc50007fd0001fe40007f50001fc40017fcc001fe30007f4c005fc3000ffc8001fe20007f48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x42004ff88210027f44108013fd2084001fc9042004ff08210027fe2108013f71084007fd8842000ffd9510005feca880037f65440013fb2a2000ff99510045fcca88003fd65440017eb2a2000ff19510045f8ca880037c65440013e32a2000ffd9110005fec888003bf64440015fb222000ff9911003dfcc888003fd64440017eb222000ff1911003df8c888003bc64440015e3222000ffd5110007fca888003fd5444001fe2a22000ffd8d10005fec68802bfe63440057f31a2000ff58d10005fac68802bfc63440057e31a2000ffd4d10057fca688003fd5344015fe29a2000ffd0d10057fc8688003fd4344015fe21a2000ffd8910005fec488027fe62440037f3122000ff58910005fac488027fc62440037e3122000ffd491004ffca488003fd5244013fe2922000ffd091004ffc8488003fd4244013fe212200affcc91004ffc6488003fd3244013fe1922000ffd451001ffca288003f65144001fea8a2000fd5451001ff8a288003ff4144001fba0a2003ff90510007fa828800ffc4144001fa20a200affcc51001ffc6288003f63144001fe98a2000fd4c51001ff86288027ff2144007ff10a2000fd88510007fa4288003f52144007fe10a2000ffd4110007f6a088013fe5044001fea822004ff14110007f0a088003ff4044009ff2022000fe90110007fa8088003f94044009fe202200affcc110027fc6088003fa3044001fe9822000fe4c110027f86088027ff2044009ff1022000fe88110007fa4088003f92044009fe1022003ffc411001ff62088013fe1044009fb0822004ffd9410025feca08013fe65040117f3282004ff59410005faca08013fc65040097e3282004ffd9010025fec808013fe640400f7f3202004ff59010005fac808013fc64040097e3202000ffd5010007fca808003fd5404001fe2a02004ffd8c10025fec608013fe63040057f3182004ff58c10005fac608013fc63040097e3182000ffd4c10037fca608003fd530400dfe2982000ffd0c10037fc8608003fd430400dfe2182004ffd8810025fec408013fe62040037f3102004ff58810005fac408013fc62040097e3102000ffd481002ffca408003fd520400bfe2902000ffd081002ffc8408003fd420400bfe2102006ffcc81002ffc6408003fd320400bfe1902003bf9841001ffea20800ffe5104007fea882003ff1441001ffe820800ffe4104007fea082003ff1041001ffe620800ffe3104007fe9882003ff0c41001ffe420800ffe2104007fe9082003ff08410025fcc008013ff5004009ff2802004ff54010027f8a008013ff4004009ff2002004ff50010027f88008013ff3004009ff1802004ff4c010027f86008013ff2004009ff1002004ff48010027f84008013ff1004009fb8802004ff84010027f42008013fd1004009fa8802003fe44010
  | 1 => 0x3fe4148001fea0a4000ff1052007ffe6290003fe3148001fe98a400fff0c52000ffe4290007fe2148003fe90a4001ff0852000dfec090003ff5048009ff2824000ff54120027f8a090003ff4048009ff2024000ff50120027f8809003fff3048009ff1824000fe8c120007fa6090003f93048009fe1824001ffc812000ff64090013fe2048009f71024004ff08120027d84090007f82048007ffb2e2003bfd971001ffccb88022fe65c4007feb2e2000bf5971001ff8cb8800efc65c4007ffb262003bfd931001ffcc98801efe64c4007feb262000bf5931001ff8c98800efc64c4001ffaa62000ff95310007faa988003fc54c4007ffb1e2003bfd8f1001ffcc78800afe63c4007feb1e2000bf58f1001ff8c78800efc63c4001ffa9e200eff94f10007faa78803bfc53c4001ffa1e200eff90f10007fa878803bfc43c4007ffb162003bfd8b1001ffcc588006fe62c4007feb162000bf58b1001ff8c58800efc62c4001ffa96200dff94b10007faa588037fc52c4001ffa16200dff90b10007fa8588037fc42c401dff996200dff8cb10007fa6588037fc32c4007ffa8e2003ff9471001feca38800ffd51c4001faa8e2003ff1471001ffe8388003f741c4007ff20e2003ff5071001ff8838800ff441c4007ff98e2003ff8c71001fec638800ffd31c4001fa98e2003ff0c71001ffe438800ffe21c4007fb10e2003ff48710007ea438800ffc21c4001ffa862004ff94310007faa188013fc50c4001ffa062004ff90310007fa8188013fc40c401dff9862004ff8c310007fa6188013fc30c401bff9062004ff88310007fa4188013fc20c4009ffb2c2004bfd9610027fccb08022fe6584009feb2c2000bf59610027f8cb08012fc6584009ffb242004bfd9210027fcc90801efe6484009feb242000bf59210027f8c908012fc6484001ffaa42000ff95210007faa908003fc5484009ffb1c2004bfd8e10027fcc70800afe6384009feb1c2000bf58e10027f8c708012fc6384001ffa9c200cff94e10007faa708033fc5384001ffa1c200cff90e10007fa8708033fc4384009ffb142004bfd8a10027fcc508006fe6284009feb142000bf58a10027f8c508012fc6284001ffa94200bff94a10007faa50802ffc5284001ffa14200bff90a10007fa850802ffc4284019ff994200bff8ca10007fa650802ffc32840017eb0c2000ffd461001ffca308003fd5184007fe28c2000ffd061001ffc8308003fd4184007fe20c200cffcc61001ffc6308003fd3184007fe18c200bffc861001ffc4308003fd2184007fe10c2004bf98210027fea108003fb5084009ff2842004ff54210027f8a108013f85084009ffa042004ff90210027f48108013fd4084001fca042004ff10210027fe6108013fe3084009fd1842004ff4c210007f26108013fc3084009ff9
  | 2 => 0x30017fca69800bde534c005fea9a6000f754d30017f8a69800bff434c005ff21a6002ff50d30017f88698003ff624c0017fb126011ff9893000dfcc498003fd624c023fe3126001bf18930007fea498047fe524c001fea926011ff14930007fe8498047fe424c001fea126011ff10930017fe649800bfe324c005fe9926002ff0c930007fec298002ff614c001ff30a6000ff58530007f8c29800efc614c001ffa8a6000ff94530007faa298003fc514c001ffa0a6000ff90530007fa8298003fc414c005ff98a6002ff8c530017fa629800bfc314c023ff90a6000ff88530007fa4298047fc214c0057fb026000ffd4130027fca098003fd504c009fe2826000ffd0130027fc8098003fd404c009fe2026002ffcc130017f66098013fe304c009ef1826004ff0c130027b8609800bf8304c023ff9026004ff08130027fecb10012ff6588009ff32c4008bf99620027facb10002fd6588009fe32c4004bf19620027fec910012ff6488009ff3244007bf99220027fac910002fd6488009fe3244004bf19220007fea910003fe5488001feaa44000ff15220027fec710012ff6388009ff31c4002bf98e20027fac710002fd6388009fe31c4004bf18e20007fea710043fe5388001fea9c4010ff14e20007fe8710043fe4388001fea1c4010ff10e2000dfac510007ff5288003ff2944001ff54a2000ff8a510007ff4288003ff2144001ff50a2000ff88510007ff3288003ff1944001ff4ca2000ff86510013ff6188009ff30c4003bf98620027fac310002fd6188009fe30c4000ffd4620007fca310003fd5188001fe28c4000ffd0620007fc8310003fd4188001fe20c4010ffcc620007fc6310003fd3188021fe18c4001ffc862000ffc4310007fd2188003fe10c4004bf98220027fea110013fe5088009fea844004ff14220027fe8110013fe4088009fea044004ff10220027fe6110013fe3088009fd1844004ff4c220007f26110013fc3088009ff9044004fbc822000ff64110013fc2088009fc1044000ffd9520005feca90003fe65480117f32a4000ff59520005faca90003fc65480117e32a4000ffd9120005fec890003fe644800f7f3224000ff59120005fac890003fc644800f7e3224000ffd5120007fca890003fd5448001fe2a24000ffd8d20005fec69003ffe63480057f31a4000ff58d20005fac69003ffc63480057e31a4000ffd4d2007ffca690003fd534801ffe29a4000ffd0d2007ffc8690003fd434801ffe21a4004bfd892000ffea490007fe5248003f72924001ff54920007daa490007fc5248003ffa124001ff9092000ffa8490007fc4248003ff9924001ff8c92000ffa6490007fc3248001ffb0a4000bfd8520007fcc290003fd6148001fe30a4003bf18520007fea290003fe5148001fea8a4000ff14520007fe829000
  | 3 => 0xe28a8007ffd0540007fc82a0003fd415000ffe20a8016ffcc540007fc62a0003fd315002dfe18a8015ffc8540007fc42a0003fd215002bfe10a8000ffd4140027fca0a0003fd5050009fe2828007ffd014003ff680a0013fe4050009df2028016ffcc140027f860a0057ff2050009fe1028004ffd9440025feca20013fe65100117f3288004ff59440005faca20013fc65100097e3288007bf9904003ffea82001ffe541000ffeaa08007ff15040027fec620013fe63100057f3188004ff58c40005fac620013fc63100097e3188000ffd4c400a7fca620003fd5310029fe2988007ffd0c4003ffc862001ffd431000ffe2188004ffd8840027fcc420006fe6210009feb108000bf58840027f8c420012fc6210001ffa908013ff94840007faa42004ffc521000fffa108007ff9084003ffa842001ffc4210029ff9908013ff8c840007fa642004ffc3210009ffb088004ff9844001dfcc220013fd61100017eb088004ff18440007fea220003fe5110001fea888000ff1444003ffe822001ffe4110001df2088007ff5044003ff8822001fbc4110029ff9888000ff8c440007fa6220053fc3110027ff9088000ff88440007fa422004ffc21100097f3008004ffd4040007f6a020013fe5010009fea808004ff14040027f0a020013ff4010009dfa008004ff90040027f48020013fd4010009dea008007fe50040027fe6020013fc3010009ff9008004ff08040027fecb18012ff658c009ff32c6008bf99630027facb18002fd658c009fe32c6004bf19630027fec918012ff648c009ff3246007bf99230027fac918002fd648c009fe3246004bf19230007fea918003fe548c001feaa46000ff15230015fac71800bff538c005ff29c6002ff54e30017f8a71800bff438c005ff21c6002ff50e30017f88718013ff628c009ff3146001bf98a30027fac518002fd628c009fe3146004bf18a30007fea51804bfe528c001fea946012ff14a30007fe851804bfe428c001fea146012ff10a30017fe651800bfe328c005fe9946002ff0ca30027fec318013fe618c0077f30c6004ff58630005fac318013fc618c001ffa8c6000ff94630007faa318003fc518c001ffa0c6000ff90630007fa8318003fc418c005ff98c6002ff8c630017fa631800bfc318c025ff90c6000ff88630007fa431804bfc218c0097f3046004ffd4230027fca118013fd508c009fe2846004ffd0230027fc8118013fd408c009fe2046004ffcc230027be611800bfb308c009fe1846004fe0c230027fe4118013fc208c001ffb2a6000bfd9530007fcca98022fe654c001feb2a6000bf59530007f8ca98022fc654c001ffb226000bfd9130007fcc89801efe644c001feb226000bf59130007f8c89801efc644c001ffaa26000ff95130007faa898003fc544c0097fb1a6002ffd4d
  | 4 => 0x2fd65d000fbeb2e80009f5974003ff8cba001efc65d000fffaa68007ff9534003f7ca9a001ffd54d0001deaa68007ff1534003ffec7a001ffe63d00057f31e8007ff58f40005fac7a001ffc63d00057e31e8000ffd4f400d7fca7a0003fd53d0035fe29e8007ffd0f4003ffc87a001ffd43d000ffe21e8007ffd8b4003ffcc5a0006fe62d000ffeb168000bf58b4003ff8c5a0006fc62d0001ffa968019ff94b40007faa5a0067fc52d000fffa168007ff90b4003ffa85a001ffc42d0035ff9968019ff8cb40007fa65a0067fc32d000fffb0e8007ff9874001dfcc3a001ffd61d00017eb0e8007ff18740007fea3a0003fe51d0001fea8e8000ff1474003ffe83a001ffe41d000ffea0e8007ff107400d7fe63a0003fe31d0001fe98e801aff0c7400cffe43a0003fe21d0001fe90e8019ff08740007fea1a0003fb50d0009ff2868000ff54340027f8a1a0003f850d0035ff9868004ff0c3400cffe41a0013fc20d0009ffb2c8004bfd9640027fccb20022fe6590009feb2c8000bf59640027f8cb20012fc65900017eb248000ffd524003ffca920003fd549000ffe2a48004ffd8e40027fcc72000afe6390009feb1c8000bf58e40027f8c720012fc6390001ffa9c8018ff94e40007faa720063fc539000fffa1c8018ff90e40007fa872001ffc4390009ffb148004ff98a4000dfcc520013fd62900017eb148004ff18a40025f8c520003ff529002fff2948000ff54a400bff8a52001fff429002fff2148000ff50a4003ff88520063ff329002fff1948000ff4ca400bff86520013ff6190009ff30c8003bf98640027ecc320002f66190009feb0c8000bf58640027eac320002f56190009fe30c8000ffd4640007fca320003fd5190001fe28c8007ffd0640007fc8320003be4190001fea0c8007ff10640007788320063ff3190001ff18c8000ff4c6400c7f8632005fff2190001ff10c8000ff486400bff84320012fe6090009ffa848004ff94240027faa120013fc5090009ffa048004efd024003ff68120013ff3090009fe1848004ffc8240027f84120003ff65500017fb2a8000ff99540045fccaa0003fd65500017eb2a8000ff19540045f8caa0003ff545000fff2a28000ef95140007faa8a0003bd545000ffe2a28000ffd8d40005fec6a005bfe63500057f31a8000ff58d400b7f8c6a000afc6350001ffa9a8016ff94d40007faa6a005bfc535000fffa1a8016ff90d40007fa86a001ffc4350001ffb128000bfd89400affcc4a0006fe6250001feb128015ff1894000df8c4a0003ff525002bff2928000ff549400aff8a4a001fff425002bff2128000ff5094003ff884a005bff325002bff1928000ff4c9400aff864a0003ff61500017fb0a8000ff98540007fac2a0003fc61500077e30a8000ffd4540007fca2a0003fd5150001f
  | 5 => 0x4a50047f8a528003ff429403fff214a000ff50a500fff88528083ff329403fff194a000ff4ca500fff86528013ff6194009ff30ca003bf98650027fac328002fd6194009fe30ca008ffd4650007fca3280037e5194001fea8ca008ff14650006f8a328003ff4194001ff20ca000ff50650007f88328083ff3194001ff18ca000ff4c650107f8632807fff2194001ff10ca000ff486500fff84328012fe6094009ffa84a004dfd4250047f6a128013ff3094009fe184a004ffc8250027f84128003ff64540017fb22a000ff99150007fac8a8003fc645400f7e322a008ffd5150007fca8a8003fd5454011fe2a2a000ffd8d50005fec6a807bfe63540057f31aa000ff58d500f7f8c6a800afc6354011ffa9aa01eff94d50007faa6a8023fc5354001ffa1aa01eff90d50007fa86a807bfc4354001ffb12a000bfd89500effcc4a8006fe6254001feb12a01dff1895000df8c4a8023ff525403bff292a000ff54950047f8a4a8003ff425403bff212a000ff509500eff884a807bff325403bff192a000ff4c9500eff864a8003ff61540017fb0aa000ff98550007fac2a8003fc61540077e30aa008ffd4550007fca2a8003fd5154011fe28aa000ffd0550007fc82a8003fd4154001fe20aa01effcc550007fc62a8003fd315403dfe18aa01dffc8550007fc42a8003fd215403bfe10aa008ffd4150047f6a0a8013fe5054009bf282a01effcc150027f860a8077ff2054009fe102a008bf99450027fec828013fe641400f7f320a004ef990500057cc828013fd64140017eb20a004ef590500057ac828013fc6414011ffaa0a008dfd5050047fca828023fd5414001beaa0a008ff15050027fec628013fe63140057f318a004f798c50015bcc628013fd63140017eb18a004f758c50005bac628013fc63140097e318a008ffd4c50047fca628023fd5314011fe298a000ffd0c500e7fc8628003fd4314039fe218a004ffd8850027fcc428006fe6214009f7310a001bb98850027fac428002fd6214009f6b10a000bb58850027f8c428012fc6214011ffa90a008ff94850047faa428023fc5214001ffa10a01bff90850007fa842806ffc4214039ff990a01bff8c850007fa642806ffc3214009ffb08a004ff9845001dfcc228013f661140017b308a004ff58450005fac228013f561140017ab08a004ff18450047fea228023fe5114001bf288a008ff54450047f8a2280237c5114001ffa08a000ff90450007fa8228003fc4114039ff988a000ff8c450007fa6228073fc3114037ff908a000ff88450007fa422806ffc21140097f300a004ffd4050026fea028013fe5014009fd280a004ff54050026faa028023f95014009ff980a004ff0c050027fe4028013fc201400fffb2e8007bfd974003ffccba0022fe65d000fbf32e80009f9974003ffacba0
  | 6 => 0x3fe1944203bf9862101ffea31080ffe5188407fea8c4203ff1462101ffe831080ffe4188407fea0c4203ff1062101ffe631080ffe3188407fb18c4203ff4c621007ea631080ffc3188407ff90c4203fbc862100fee431080ffc2188407fa10c4203ffd822101ffcc110812fe6088407feb044200bf5822101ff8c110893ff3088449fe1844201ffc822100ff84110803ff65484017fb2a4200ff99521045fcca90803fd65484017eb2a4200ff19521045f8ca90803ff64484017fb224200ff9912103dfcc890803fd64484017eb224200ff1912103df8c890803ff5448401ff2a24200ff55121007f8a890803ff63484017fb1a4223ff98d21015fcc690803fd63484017eb1a4223ff18d21015f8c690803ff5348447ff29a4200ff54d2111ff8a690803ff4348447ff21a4200ff50d2111ff8869080eff6248403ffa924201ff9492100ffaa490807fc5248403ffa124201ff9092100fdc8490807fd4248401f6a124201ff1092100ffe6490807fe3248403fe9924201ff0c92100dfec290803ff5148407ff28a4200ff5452101ff8a290803ff4148407ff20a4200ff5052101ff8829088fff3148407ff18a4200fd8c521007fa6290803f53148407fe18a4201ffc852100fee429080ffe2148407f710a4203ff0852101fd84290807f42148401ffb024200bfd8121007fcc090803fd6048401fe3024204bf1812111ffe609088ffc3048403ff9024201ff08121047fec9a8023fe64d400f7f326a008ff59350005fac9a8023fc64d4011ffaa6a008ff95350047faa9a8023fc54d4011ffb1ea008ff98f50015fcc7a8023fd63d40017eb1ea008ff18f50015f8c7a8023ff53d4011ff29ea008ff54f50047f8a7a8003ff43d4045ff21ea000ff50f50117f887a8023ff62d4011ff316a001bf98b50047fac5a8002fd62d4011fe316a001bf18b50047fea5a8023fe52d4011fea96a008ff14b50007fe85a8087fe42d4001fea16a021ff10b50117fe65a8087fe32d4001fe996a021ff0cb50047fec3a8023fe61d40077f30ea008ff58750005fac3a8023fc61d4011ffa8ea008ff94750047faa3a8023fc51d4001ffa0ea000ff90750007fa83a8003fc41d4045ff98ea000ff8c750007fa63a808bfc31d4043ff90ea000ff88750007fa43a8087fc21d4045ff986a004ff0c35010ffe41a8013fc20d40017eb2ca004ffd9250027fcc92801efe6494009feb24a000bf59250027f8c928023ff5494001bfaa4a000ff95250007faa9280037d5494011fe2a4a004ffd8e50027fcc72800afe6394009feb1ca000bf58e50027f8c728012fc6394011ffa9ca020ff94e50007faa728023fc5394001ffa1ca020ff90e50007fa8728083fc4394009ffb14a004ff98a5000dfcc528013fd62940017eb14a004ff18a50025f8c528023ff529403fff294a000ff5
  | 7 => 0x2080ffd4110407dea088207fd5044101ffe622080ffc3110407ff9088203ff0844101ffec02080ffe60104097f3008203fe98041005f4c02080ffd60104017eb008203fe58041005f2c02080ffc6010451ff9808228ff0c04113ffe402089ffc2010407ffb2c6203bfd963101ffccb18822fe658c407feb2c6200bf5963101ff8cb1880efc658c407ffb246203bfd923101ffcc91881efe648c407feb246200bf5923101ff8c91880efc648c401ffaa46200ff95231007faa918803fc548c4057eb1c6202ffd4e31017fca71880bfd538c405fe29c6202ffd0e31017fc871880bfd438c405fe21c6203ffd8a3101ffcc518806fe628c407feb146200bf58a3101ff8c51880efc628c401ffa946226ff94a31007faa51889bfc528c401ffa146226ff90a31007fa851889bfc428c405ff9946202ff8ca31017fa651880bfc328c4077f30c6203ffd463101ffca31880ffd518c407fe28c6203ffd063101ffc831880ffd418c407fe20c6203ffcc63101fbe631880bf7318c407fe18c6203fd0c63101ffe431880ffc218c407ffb046203ff98231025fcc11880ffd608c4017eb046203ff18231017fe611880bfc308c44dff9046226ff08231007feca98802ff654c401ff32a6208bf99531007faca98802fd654c401fe32a6208bf19531007fec898802ff644c401ff3226207bf99131007fac898802fd644c401fe3226207bf19131007fea898803fe544c401feaa26200ff1513101dfec69880bff534c405ff29a6202ff54d31017f8a69880bff434c405ff21a6202f790d31017fa8698803dd434c405fe21a6200ffd8931005fec498897fe624c4037f3126200ff5893112ff8c498806fc624c401ffa926225ff94931007faa498897fc524c401ffa126225ff90931007fa8498897fc424c405ff9926202ff8c931017fa649880bfc324c4057fb0a6200ffd453101ffca298803fd514c407fe28a6200ffd053101ffc8298803fd414c407fe20a6202ffcc531017ee629880ffe314c407ef18a6203ff0c53101fb8629880bf4314c44bff90a6203ff08531007fec098802ff604c401ff3026200ff58131007f8c098812fc604c405ff9826202ff0c13112ffe4098897fc204c407ffb2c4203bfd962101ffccb10822fe6588407feb2c4200bf5962101ff8cb1080efc6588407ffb244203bfd922101ffcc91081efe6488407feb244200bf5922101ff8c91080efc6488401ffaa44200ff95221007faa910803fc5488407ffb1c4203bfd8e2101ffcc71080afe6388407feb1c4200bf58e2101ff8c71080efc6388401ffa9c4224ff94e21007faa710893fc5388401ffa1c4224ff90e21007fa8710893fc43884037eb144201ffd4a2100ffca510807fd5288403fe2944201ffd0a2100ffc8510807fd4288403fe2144201ffcca2100ffc6510807fd328840
  | 8 => 0xf0874103ffec1a081ffe60d04097f3068207ff58341005fac1a081ffc60d045dff986822eff0c34116ffe41a08b7fc20d0407ffb2c8203bfd964101ffccb20822fe6590407feb2c8200bf5964101ff8cb2080efc65904017eb248200ffd524103ffca920803be5490401feaa48200ef5524103ff8a92080fff6390407ff31c8202bf98e4101ffac720802fd6390407fe31c8203bf18e41007fea7208b3fe5390401fea9c822cff14e4103ffe87208b3fe4390401fea1c8207ff10e4101ffec52080ffe62904037f3148203ff58a41005fac52080ffc62904077e3148200ffd4a4115ffca520803fd5290457fe2948207ffd0a4115ffc8520803fd429040ffe214822cffcca4115ffc6520803fd3290457fe1948203bf9864101ffea32080ffe5190407fea8c8203ff1464101ffe832080fbf419040ffba0c8203ffcc64101ff8632080fff2190407fe10c8203ffd824101ffcc120812fe6090407feb048200bf5824101ff8c1208b3ff3090459fe184822bffc824115ff84120803ff65504017fb2a8200ff99541045fccaa0803fd65504017eb2a8200ff19541045f8caa0803ff545040fff2a28200ff5514103ff8a8a0803ff63504017fb1a822aff98d41015fcc6a0803fd6350455fe31a8202bf18d41007fea6a08abfe5350401fea9a822aff14d4103ffe86a08abfe4350401fea1a8207ff10d41007fec4a0802ff6250453ff3128201bf98941007fac4a08a7fc62504037e3128200ffd494114ffca4a0803fd5250453fe2928207ffd094114ffc84a0803fd425040ffe212822affcc94114ffc64a0803fd3250453fe1928200ffd454101ffca2a0803fd5150407fe28a8207ffd054103fee82a080ffe4150407df20a822affcc54101ff862a08a7ff2150407fe10a8200ffd8141005fec0a0803fe6050401feb028200ff18141025f8c0a08abff3050455fe1828229ffc814114ff840a080fff65104077fb288203ff99441045fcca2080f7e65104013f3288203ff59441005faca2080f7d65104013eb288203ff1944101df8ca2081efe641040fffaa08207ff9504103f7ca82081ffd5410401deaa08207ff1504101ffec62080ffe63104057f3188203f798c41015bcc62080ffd63104017eb188203f758c41005bac62080ffc63104077e3188200ffd4c41147fca620803fd5310451fe2988207ffd0c4103ffc862081ffd431040ffe2188203ffd884101ffcc420806fe6210407f73108201bb9884101ffac420802fd6210407f6b108200bb5884101ff8c42080efc6210401ffa908227ff94841007faa42089ffc521040fffa108207ff9084103ffa842081ffc4210451ff9908227ff8c841007fa642089ffc32104077f3088203ffd4441007eea22080ffe5110407fea888203ff1444101fe8a22080fff4110407dfa088203ff9044101fec82
  | 9 => 0x4077e314a208ffd4a5119ffca528803fd5294411fe294a200ffd0a5119ffc8528803fd4294467fe214a234ffcca5119ffc6528803fd3294467fe194a203bf9865101ffea32880f7f5194411fba8ca203ffcc65101ff8632880fff2194407fe10ca203ffd825101ffcc128812fe6094407fd304a200be9825101ffac128802fd6094407fcb04a200be5825101ff8c1288d3ff3094469fe184a233ffc825119ff84128803ff64544017fb22a200ff99151007fac8a8803fc645440f7e322a208ffd5151006fea8a8803fe5454401feaa2a200df55151047f8a8a8803ff63544017fb1aa232ff98d51015fcc6a8803fd6354465fe31aa202bf18d51047fea6a88cbfe5354401fea9aa208ff14d51007fe86a88cbfe4354401fea1aa232ff10d51007fec4a8802ff6254463ff312a201bf98951007fac4a88c7fc62544037e312a208ffd495118ffca4a8803fd5254411fe292a200ffd095118ffc84a8803fd4254463fe212a232ffcc95118ffc64a8803fd3254463fe192a208ffd4551047eea2a880ffe5154407bf28aa232ffcc55101ff862a88c7ff2154407fe10aa200ffd8151005fec0a8803fe6054401feb02a200ff18151025f8c0a88cbff3054465fe182a231ffc815118ff840a8822fe6514407ffb20a203ff9905103dfcc82880ffd64144017eb20a203ff19051047fea828823fe5414411feaa0a208ff1505101ffec62880ffe63144057f318a203ff58c51005fac62880ffc63144077e318a208ffd4c51047fca628823fd5314411fe298a200ffd0c51187fc8628803fd4314461fe218a203ffd885101ffcc428806fe6214407feb10a200bf5885101ff8c42880efc6214411ffa90a208ff94851047faa428823fc5214401ffa10a22fff90851007fa84288bffc4214461ff990a22fff8c851007fa64288bffc32144077f308a203ffd445101efea22880ffe5114407fb288a203ff5445101efaa228823f55114407ff988a203ff0c45101ffe422880ffc2114407ffb00a203ff98051025fcc02880ffd60144017eb00a203ff18051187fe60288c3fc301445fff900a22fff0805103ffecba081eff65d040fff32e8208bf9974103ffacba0802fd65d040ffe32e8207bf1974103ffea9a081ffe54d040ffeaa68207ff1534103ffec7a081ffe63d04057f31e8207ff58f41005fac7a081ffc63d04057e31e8200ffd4f41177fca7a0803fd53d045dfe29e8207ffd0f4103ffc87a081ffd43d040ffe21e8207ffd8b4103ffcc5a0806fe62d040ffeb168200bf58b4103ff8c5a0806fc62d0401ffa96822dff94b41007faa5a08b7fc52d040fffa168207ff90b4103ffa85a081ffc42d045dff996822dff8cb41007fa65a08b7fc32d0401ffa8e8200fdd474101ffca3a0803fd51d0407fe28e8200fd14741177fe63a080ffc31d045bff90e8203f
  | 10 => 0xc8a1003ff545080fff2a28400ef95142007faa8a1003bd545080ffe2a28400ffd8d42005fec6a10dffe63508057f31a8400ff58d421bff8c6a100afc6350801ffa9a8437ff94d42007faa6a10dffc535080fffa1a8400efd0d421bffc86a1003fd4350801dea1a8407ff10d4200dfec4a1007ff5250803ff2928401ff5494200ff8a4a1007ff425080ff7a128401ff9094200f7c84a1007fc4250803de2128401fb1094200ffe64a1007fe3250803fe1928400ffd8542005fec2a1003fe6150801feb0a8400ff1854201df8c2a10dfff315086ffe18a8401ffc854200fde42a1007fc2150801ffb028400bfd8142007fcc0a1003fd6050801fe3028404bf181421bffe60a10dffc3050803ff9028401ff08142007feca99002ff654c801ff32a6408bf99532007faca99002fd654c801fe32a6408bf19532007fec899002ff644c801ff3226407bf99132007fac899002fd644c801fe3226407bf19132007fea899003fe544c801feaa26400ff1513200dfec69900bff534c805ff29a6402ff54d32017f8a69900bff434c805ff21a6402ff50d32017f88699006ff624c803ffa926401ff9493200ffaa499007fc524c803ffa126401ff9093200ffa8499007fc424c803ff9926402fbcc93200ffc6499007de324c803fe1926401f70c93200fd86499007cc324c801ffb0a6400bfd8532007fcc299003fd614c801fe30a6403bf18532017fe629900bfc314c803ff90a6401ff08532007fec099002ff604c801ff3026400ff58132007f8c099012fc604c805ff9826402ff0c13200ffe4099007fc204c811ffb26a208ff9935103dfcc9a8823be64d44015f326a208ff59351005fac9a8823bd64d44015eb26a208ff19351047fea9a88237f54d4411ff2a6a208ff55351006faa9a8823fc54d4411ffb1ea208ff98f51015fcc7a8823fd63d44017eb1ea208ff18f51015f8c7a8823ff53d4411ff29ea208ff54f51047f8a7a8803ff43d446dff21ea200ff50f511b7f887a8823ff62d4411ff316a201bf98b51047fac5a8802fd62d4411fe316a201bf18b51047fea5a8823fe52d4411fea96a208ff14b51007fe85a88d7fe42d4401fea16a235ff10b511b7fe65a88d7fe32d4401fe996a235ff0cb511b7fe63a880ffc31d446bff90ea203ff08751047fec1a8823fe60d44097f306a208ff58351005fac1a8823fc60d446dff986a236ff0c3511affe41a88d7fc20d44017eb2ca203ffd925101ffcc92881efe6494407feb24a200bf5925101ff8c928823ff5494401ff2a4a200ff55251047f8a92880fff6394407ff31ca202bf98e5101ffac728802fd6394407fe31ca203bf18e51047fea7288d3fe5394401fea9ca208ff14e51007fe87288d3fe4394401fea1ca234ff10e5101ffec52880ffe62944037f314a203ff58a51005fac52880ffc6294
  | 11 => 0x2ff0c943007fec2a1802ff6150c01ff30a8600ff58543007f8c2a180efc6150c05ff98a8602f7cc543017f862a18efff2150c77fe10a8600ffd8143005fec0a1803fe6050c01feb028600ff18143025f8c0a180bff3050c05fe182863bffc81431dff840a1806fe65d4811ffb26a408ff9935203dfcc9a9023fd64d48017eb26a408ff19352047fea9a90237f54d4811ff2a6a408ff55352006faa9a9023fc54d4811ffb1ea408ff98f52015fcc7a9023fd63d48017eb1ea408ff18f52015f8c7a9023ff53d4811bfa9ea408ff94f52047faa7a90037d53d4811fe29ea400ffd0f521d7fc87a9003fd43d4875fe21ea401bf58b5200ffca5a90077e52d4803f7296a401db94b5200ff8a5a90077c52d4803ff216a401ff10b5200ffe65a9007fe32d4803fe196a408ffd8752047fcc3a900efe61d4811feb0ea400bf58752047f8c3a90ebff31d4875fe18ea401ffc875200ff843a9023ff60d4811ff306a404bf98352047fac1a9002fd60d4811fe306a43affcc3521d7f861a9007ff20d4803fe106a401bfd9552007fec8a9002ff6454801ff322a400ff59152007f8c8a901efc6454811ffaa2a400dfd5152007fca8a9003fd5454801beaa2a408ff15152007fec6a9002ff6354873ff31aa402bf98d52007fac6a90e7fc63548057e31aa408ffd4d52006fea6a90e7fe5354801fea9aa400df54d52047f8a6a9003ff4354873ff21aa400ff50d521cff886a9006ff6254803ffa92a408fbd495200ffca4a90077e5254803fe292a401df1495200fd8a4a9007fe4254803fe212a401ffcc95200ffc64a9007fc3254801ffb0aa400bfd8552007fcc2a9003fd6154801fe30aa403bf185521cffe62a90e7fc3154803ff90aa401ff08552007fec0a9002ff6054801ff302a400ff58152007f8c0a9012fc6054873ff982a439ff0c15200ffe40a9007ef2054803fe102a407ffd974203dfecba101ffe65d08117f32e8407ff59742005facba101ffc65d080f7e32e8401bf9934203ffea9a101ffe54d080fdf2a68407ff553420077aa9a101ffc54d080fffb1e8407ff98f42015fcc7a101ffd63d08017eb1e8407ff18f42015f8c7a1003ff53d0871ff29e8400ff54f421c7f8a7a101fff43d080fdfa1e8407ff90f4203ffa87a1003bd43d080ffe21e8401bf58b4200ffea5a1007fe52d0803fea968401ff14b4200ffc85a1007be42d0803f72168401ff10b4200f7885a1007ff32d0803ff1968401ff0cb4203ffec3a101ffe61d08077f30e8407ff58742005fac3a101ffc61d0871ff98e8438ff0c74200ffe43a1007fc21d080fffb068407ff98342025fcc1a101ffd60d08017eb068407ff183421c7fe61a10e3fc30d0803ff9068401ff08342007fecaa1002ff6550801ff32a8408bf99542007facaa1002fd6550801fe32a8408bf1954200dfe
  | 12 => 0x150097f300a807ff58054005fac02a01ffc6015081ff980a840ff0c0541fffe402a0fffc20150057f32ea608ffd9353047fcc9a981efe64d4c11feb26a600bf59353047f8c9a9823ff54d4c11bfaa6a608ff95353047faa9a98037d54d4c11fe2a6a602bf58f53017fca7a980b7e53d4c05ef29ea602d794f53017f8a7a980b7c53d4c05ff21ea602ff10f53047fec5a9823fe62d4c037f316a608ff58b53005fac5a9823fc62d4c037e316a608ff94b53047f8a5a98fbfe42d4c7dfe216a602ffccb53017fc65a980bfc32d4c11ffb0ea608ff9875301dfcc3a9823fd61d4c017eb0ea608ff18753017fe63a980bfc31d4c7dff90ea63eff08753047fec1a9823fe60d4c097f306a608ff58353005fac1a9823fc60d4c05ff986a602ff0c3531f7fe41a98fbfc20d4c057fb2aa600ffd9153005fec8a9803fe6454c01feb22a600ff1915303df8c8a9823ff5454c01bfaa2a600ff95153007faa8a98037d5454c11fe2a2a602bfd8d53017fea6a9823df5354c05ff29aa602df94d53017f8a6a980b7c5354c05ee29aa602ff90d53017f886a9803ff6254c017fb12a63dff9895300dfcc4a9803fd6254c7bfe312a601bf189531effca4a9823fc5254c7bff212a63dff10953017fe64a980bfe3254c05fe192a600ffd8553005fec2a9803fe6154c01feb0aa600ff1855301df8c2a980bff3154c05fe18aa63dffc85531eff842a9803ff6054c017fb02a600ff98153007fac0a9803fc6054c097e302a602ffcc153017be60a980bfc3054c7bff902a63dff0815303ffecba181eff65d0c0fff32e8608bf9974303ffacba1802fd65d0c0ffe32e8607bf19743015fcc9a181fff54d0c0fff2a68607ef9534303ffaa9a1803bd54d0c0ffe2a68602bf58f43017fea7a180bfe53d0c05fea9e8602ff14f43017fc87a180bbe43d0c05ef21e8602ff10f430177887a181fff62d0c0fff3168601bf98b4303ffac5a1802fd62d0c0ffe3168601bf18b431e7fca5a18f3fc52d0c0fff2168607ff10b43017fe65a180bfe32d0c05fe1968607ffd874303ffcc3a180efe61d0c0ffeb0e8600bf5874303ff8c3a180bff31d0c05fe18e863cffc87431e7f843a181fff60d0c0fff3068604bf9834303ffac1a1802fd60d0c0ffe3068602ffcc343017f861a18f3ff20d0c79fe1068600ffd9543005fecaa1803fe6550c117f32a8600ff59543005facaa1803fc6550c117e32a8602bfd9143007fea8a181ffe5450c01df2a28600ff551430077aa8a181ffc5450c057fb1a8602ffd4d43017fca6a180bfd5350c05fe29a8602ffd0d4303fbe86a180bfe4350c05df21a8602ff10d430177886a180bdc4350c01ffb128600bfd89431dffcc4a1806fe6250c01feb12863bff1894300df8c4a18effe5250c77fe292863bff9094303ff884a180bff3250c05ff192860
  | 13 => 0xe01200200003c00400001a00000200400000e00400a00401201000200a01201402202001a05600802200200400001802a00200000801000000200000800400000400000000600800c00400600a00e00003602202201c00802401800200000800800600000800e08ffd8f54047fcc7aa00afe63d5011feb1ea800bf58f54047f8c7aa00afc63d5011ff29ea808ff14f54237fc87aa01ffc43d5011ffb16a808ff98b5400dfcc5aa023fd62d50017eb16a808ff18b5400df8c5aa023fe52d5011fe296a845ff90b5403ff885aa11bff32d508bff196a845ff0cb54047fec3aa023fe61d50077f30ea808ff58754005fac3aa023fc61d508dff98ea846ff0c75422ffe43aa117fc21d5011ffb06a808ff98354025fcc1aa023fd60d50017eb06a808ff18354237fe61aa11bfc30d508bff906a845ff08354005facb2a01efe649500fffaa4a807dfd52540477ea92a0033f549500fffb1ca807ff98e54015fcc72a01ffd63950017eb1ca807ff18e54015f8c72a113fe5395011fe29ca807ff90e5403ff8872a01fff629500fff314a801bf98a5403ffac52a002fd629500ffe314a801bf18a5421ffca52a023fc529500fff214a807ff10a54227fe652a10ffe3295087fe194a807ffd865403ffcc32a00efe619500ffeb0ca800bf5865403ff8c32a113ff3195089fe18ca843ffc865421ff8432a01fff609500fff304a804bf9825403ffac12a002fd609500ffe304a844ffcc254227f8612a10fff2095087fe104a808ffd51540477ea8aa01ffe545500fbf2a2a800ffd8d54005fec6aa10bfe63550057f31aa800ff58d54217f8c6aa00afc6355085ff29aa808ff14d54217fc86aa01ffc4355001ffb12a800bfd895420ffcc4aa006fe6255001feb12a841ff1895400df8c4aa107fe5255011fe292a841ff9095403ff884aa10bff3255083ff192a841ff0c954007fec2aa002ff6155001fbb0aa800bdd8554007fcc2aa003fd6155001fe30aa803bf18554007e8c2aa002f46155085ff98aa842ff0c55420ffe42aa107fc2155001ffb02a800bfd8154007f6c0aa002fb6055001ff302a800ff58154007f8c0aa012fc6055001fc302a800be18154217fe60aa10bfc3055083ff902a841ff08154045fcca2a01efe641500fffaa0a807dfd505403ffca82a01fbe541500ffeaa0a807df550540477aa82a01fff631500fff318a802bf98c5403ffac62a002fd631500ffe318a802bf18c54047fca62a023fc531500fff218a807ff10c5403ffec42a01ffe62150037f310a807ff58854005fac42a01ffc62150037e310a808ff94854047f8a42a01ffe421500ffe210a840ffcc8541fffc642a0fffc321500fffb08a807ff9845401dfcc22a01ffd61150017eb08a807ff18454207fe622a103fc311507fff908a83fff0845403ffec02a01ffe60
  | 14 => 0xe03e00200e00200e02200801200e00005600200a01c00003800000601203200801a00000402800200000400200000400400200001405200600001a00400001800c00001400a01600004601001c00c01e00001000000400600600c00a00600600001c00400400200800401600002e01a00201e01000200c06e00401000600800200803600a06001200400400000000001601e00402800401c0040020b800800001206401c00005600a00403601e02200a00000001608c00000000600001e00000402e03001e00000000000000e00600203608000a00e00e00000e00400000800200002e00002401003000600e08e00800000000000e00800000a01400200600001601800001800000400200200400a00000c01c00000802801000000000400000800401602002400600200200400400201800000e00001e00200606400201801200c00000e00800a00800000000600600203204202403000e04403000800000400200800800800000401000400000001601000400401800601e0100100000a001a01c01200000001801000e00a01c00a01c00600000400200e00c00400400402401401600000000200401400000600200000c02400002200600a00201401003800c01401400201002601800a00401800201800400000000001200000601a00000e00400801e00600205201400200401e03e0000520b800000a0b00000000000020220a200c00000600000600400400000000800200200804200000600c01600c00a00a00a03a00203a00600200c00800200800201400000000c05c00001e00c00400000a00600204000a06a00000000203000000200400601000400002000e00200c00000002a00c00201600000600000000400600200c00600200000400a00802201600001200400601000a00000400603a00600e00201600202c00001e00200800000200e00000801c03c00c00200800000000402600200400201001800001e00200803400200400201800600a00000200200200e00a00602401000800600600000202801c00000a00000601e00001600800000400001a00000400000200c00001600001000000200401001401000000200c01600000a00e00002000001a00400200200800e00200a00200400001204400600400400000a00000000600600600e00200e00a00600a01a00005400605800200000200000000000000801e00000000000000c00800e01c00c00001c00800601201000402000001600400000400006000200000c03c00000400401800e00200400203c00202a00400000001600001200000000201a03a00000200200206400400400200007200200400400000600400000001000000200800000200402000404000204c00400a00001800200600000400800001400000e00400200001800800000200600200007c00000c00a
  | 15 => 0x4b00003793881a300003881c60002e100006f60003bf85c4ba40000002b9d37266d0798d58134a45200aba01962461451780488000000235cce2a2957294341605dc06d0ef8e366a801e03f878a3eb1751c4c7e805435a034951460e5512d5520e0ba4359f705de7e4031a8107084cd49322dd2106444c68b6d5184134c727b07fc04a1ccab688ccab916aa4d8cb8909545a384ab689021d13e88329c24d41f6d32ab7800b8054fb044630e9dd029607c552079077e1394eb80e531e0004c108e51040003e6a51c38e5d834e0760b1a13c00018504a88a444ca4592185e72f28e8d0ac5a7102000165c11200c8c2039ab531d680004964144e09a4897c0003271af957085c5e52c68ca039f176800000488125f938c980ad20f1829c6d0a791a70bf47c24965d20360c404ff3d725ad78c2ba00000000001db4198f5400000000000000004c700026200006df52819d00000004370e88a9a4821f018dc1441112ca80013280002180f743582a50000000000000000000000048d5188f240204d21331bec0002d328d0000000ba010b80000000000001da085e7145449a040009062a2053d74617743920955fa2e55e2a7a085800018ca3280002fc20e01402b00002aa9c896b02d00c624e0000bf444e18d96b298c1a10c8112e9cb4a29668b6ca680002b4c0000000000f900000f10001a185ea98514b000011c0001ab80000008272b10000248b8125e854000000005300000000000ab0c0d2925a500019f8000c015a59e853c02ee4b383055fe0ea1ae000000027658b9c8463400024280005b22e434c25293023b84a5a03c59e7c20e5ac014484440102cb16dabc42cc2c046e8000453988400200401200a00c00000802a00400000202401201200803c01c00001002600604601001600400000200e00400200a00201200000002400003a00000000e00e00000200c01203c00200000205401802600001200200400400c00000202002200000000000000000201803c01c03a06000001200606001800800000000200600000200804400600402c00e00000200201600400800200400000e01800000800200000000000001402600200401800000200400204e01e00400800800c01000005800601200600201400001e00000a00001c02000200a02200006600400200000200000200000000802400c00200000c00001201c00a00400401403400600004400001400200001600000201200600000201800202c00604802000200202201800600001000a00000000c00000400600201200000200000c00000000e00000200000e00401400000200200200200202201601800000802800200400602401600400400800200000400200800e00000400200600800600000a00000000001600800a02400000600c02600201806a01800200000002604c00000c0
  | 16 => 0x11c619d1960f0800000054a24b08c42565b1a298000a743a510d0ebe53e1f7a0684b60000000a1882c000000013532e3c000000000001c000000014ee00000026bc82a75000027b882e0003a1800155072f2d00a146f41a20860ddc1c243e1bf05d9776bce2338df0b008c74e3240050417803c27e552a9122e7a33cbd68dc1390d0400060b16693d8a166d21a19d891f210b06ca3205aeae346482b533000045f1eb0000108264300c0000000001840000bb500013bc89e4ce07ead1935c2221e8af349ce00050695f00000000b20724bf81bf2a300000009875b40d2d17e92850e08a10a8aa3295a1606603653fa00016ec25011bab611fca3d00000012b25da03da7c83bc1951cb0b485189275c8adcc9929aa00000000003a835ba970000bb85509d982682413d012c50847a2492000000092a48e098cb80000379205d33e00041626a4e720000aa12a9068bfc0002af8416bb400002653949a70aa8774000000593000103a31c0000000e9c7e0403a19cf9888018e899c1da0cc00000000009ce00023800004e54fb0000f1e17b26a9a68ef6a175a38b442a400000001b40000001a300000000004f3800000023a4330c6d18c4e41e9a5b89c2a09000a55070682f0fa11b80127fe3fea6983a23f958483c8e2c000327800133488453c134400005a2fa9d8c4f6828087818917a8a11f3a218e22bef20297a039ebea2941db04bcb0c1662decd3e88529e979800029d22400014f80003d2800128668b4b6a7842461f32ae9e1161452e4f52554c14b3b00029b80000b50000000ca6633570214837c5630001a0c5548f42e722e8b0812b0002a98b7a2ad0732c180005f400002a000000058c116cfe47051d702596f854051092bcb8a0ac245006ca8a48f0b984c51a01295ee230d4f656d25184c8430b1d44a917159c2b922e82713b896901f135c984bc960120545d608d02f9be928255e5bf808492037d23400006f23a02e8abe566aa580d58158d207ab00025a0c3c63223a0e012c8a2059500005125524fc0e550360005c7076507e000000000015e77258b13184dc00041aa024e3807900021b00e838600020c169200050e864003857a49b800140400047900000005a90000001106b3155d2e30b0400014f1ce000050e0c30000e2a63107ca0e4c4e5760000000cf835002e00000009c357b8000af20005fca58c0003a70c12ef0cdc8d41cc0a34acc20600020f400074416c146d1be000511a8c8a903660000000c2203344400000007c93f3000000000021b88fc00025559a1ef08fa2a82a8aff45081ca0610880dc020722d0d8cdee63028000c8bb200042c800000025829600bc4b47103820090c9629c12e09e4a828e606e989962212c35d9ae4000823085000000000037e968c00066c3d789a006c00000000017d227344884a0f945
  | 17 => 0x6d90001c914c42c60000000000000468a6d142c4a94740bed47e5364f11984000a993a41d3176660458c97b8a1e6bf39527b57260000000d7502ca9c00006e0de20002658178000b9f14428946180003d48000840000000259400047c410abb55a8461026133143c85d0001e1d3f41445ec2d352d86755d312c8b3221e2d42678e463ac46912600004f34b7ac80e046f3548932800007d157886c7d2bbe5908000f1884400000001242dc0a289215aaba831625786525f01791a1c5f4ba75ba0a685625384712e58e622b40e718540ee30e0d0294d72e3692f92f84580b804dc17c40004f92cb830c3dc000322a3780000003c323fc3428055898b2cb068190f38694cfe1a609325385f25272c2a790000b5636b116508a87a42326112f01b256623dcf7053246ea7d07ec9345c48f1c0001af0f6a9291b4208304a82970e81411a1239124be22511a4c61a4785b506f51fa5bc59787084ca33d14c95c857a03d3558780d801845aa033c0006cb2e480fc31622f04a906879e86536f1d1c4420004ab172800080805013696e26d43949b0d6165a1456aad50a69460000a9c0009733db00005f065f2a3895d22e639432231478c25957799d81464574df2fe08be0002ea877cbd884a015adf400000000000000000000000dfc88200000000012ee56024d2e9455c7df1c523095e68930001b9028400000019e4a4056100004e00d8bec2f7854c8d279d2af94a93267ba113ad6c0b09d4000000000019c47a9620ce077d31c11bcfde000123ac70fca84312293f40000000001d80000a4300029d400001e0002c100000000001f9c8481510002b280004eb000007d1ca8634ae228c4000002df96e80000000000000000098000000000020c0000000000000000025008446a2cb199c0009c800000000008a20ac80748a80000001c2c0007d400025101b806158700006445e94ee839513ebaf0000af8000a1f000204800000000000000000000001a6c0000000880000dec0003cf97e8e020000001b74da057e1d580015821b059f0de0fdc38200000007d4181246298ce9a0001f997b4c9a2a40001ac909a84059120d8e600001f600010e2b100001f1465097d0000000000bee25688909162334799a815ea32100023ec88e00019f00016bc4392440788a6a75a4f989a48e62900001f2cc18afa21d89bd21e00023188a9324000438191d652000024000032e3d941680000007ea0000000d8e00000019501e8a0e000124d44e00041f147ca420000002d9577211716a00000000fa000000000000030687f03c20b6520970d2aea0f2140b7d42000011b082400026a1e68000fe6b755fba4fcdf20000000000b245530e30000c307550b700011e28b62dc8704de800042a8000782000049874c31c0000cc000000053707aa444e1400000026708648604f28
  | 18 => 0x285400083b0000000a20b720001ba40007340000000fea34d03d2ec019ca4c2f09cd44e076d00029500b2a6548707bc2c64a10001d440005420bca2b97a02c100022b058ea4d197a9f80002e82b2a938e6c0000000d1000000038017f42d261b00000001f60001c8a748000afb0ad2f3ca6660506306cc0fe3353348d9c00084e0eb07e80001b90000f718080000002258dfeb4a0000fc40006fc434800133674649f2ea4de08f05d88b09136a3e01185f0a460001718d1c00000053e90000004402dd8000bfc7270a390acf3649927e0fe877254e24da23cb1836a00001cc542000185aad03688b93da8634f1c311201a82d00c4453d180013f897a3c29d615c284f23d00000aabfe000125538a6572251b380002b00000d60f28bbf1590b7833e9cf05e1a8c5b45de4609c300000000002e84b4c5044f4921116a2e230b903d12835b400a00cc8420d0001a953a0a030d20b753a200000020e83a4a4b40f2ef500401109ba2c40001f65829ccd0bc2ca42f9858c267a60000d64a2e0005bf182173c05b47b00014220000e800000004492678000000878485ad30000000000284839800000000480000002360e990201bc1a7a8310b68413b2153000000036e00000000001ea00003ea0002d980000006bd2368cec0000000001c1c000b481518000cfa6c800002282ce3334e4a8b000049e0c99f1000094f023000130617d2358a3cbe6a73000178d1308ab1489420c5eaeb0002be000034800014bc000b303398000000000000045806a75b11185fca1222e0c38f98188a5539e84604fc2bb000142892479900014440002784ad0d440003c83928dc4b3a76f54dab2ce34b8542494088369cd28ea9b013a0531c80524334b950d697180d411f3551da525a03b1f198b90000d318a0afd6785dd2cf11940d659f2218a2c8ea06f4ef2a141760d0000114c2087e30ff9a10f240702d5246418e29554906c55580005579d580007a749580015b80495eda5341025d60000018d6a35e066819cd1065e3d8a1f8b705a23aa09b04da9ad00794980000384a126c012200006d80004a20a41c38000694a600d400004d68bb25d0ad8e923605170e946be9bc0000c050fa0f7472286175a7322b2089923e36b5ec9b6cc3270354f031564821c25403e15ccbf14ec2e70202aab0000438000000281a54476abda5572684e0c8a5283af545e6a44000046c9dc80a07b00006ec00000000000007b027800010225f80f424ec4f462d09100012805f90e19fe54324500002f9957a0221d212b0d780002c812e12c00000000000000000353aeb122a23b00021f0b3812a0000ff4000b5a0ad8c8c00000038caa58600065489ad447684dd00019c80006fe3569b5d7a652200017a80000000002e414269300980ab145600055885d133265b00010896d6a3536c00000a4
  | 19 => 0xa34c0b08e844521b61320e6c24e4710b280b4cc48fc57a1a88c8067a301ab1894c0c00ed07ac1de0571618650e7e93a0db9904fd20ca30fa010fdab52491a2e0c000001ce9ba079697148124c96d29d355e2140e301211988c9d2ccb7055986d4718ad606b163800052400600000000004369d9400067700019a1180656455245136c8b410e8000000875348907970c00049aaadd31265900000000007ad000000000000405f2998000753000000000000000000000747204ba0001380b282c315c555a9703eb2d713b26c100000000009f028307e476c0004059d48414bde593800107863d27015dc000b023a7a99153000027a8fb90549fd3c59a30d007900000000e8a88d14a0001732000000150d56c9762fda4788168510002b1133a44e00008384a402a58d81f89fc8370000100c769da0001bbd5209bf21e8b840007aa31f000000000003480c160658903909c40003d000000000000003b51b44c784c12f1203098853400023bc5fe000000000000000000000000006254ad8e3cee000007e0000d66a8600000000000002fb800136e9f7023acdc00040e0002fa16ce51200029213d6717536ace169eb0d0218580a303db102800000000026ca8500002f03ba94ecc740140002ce4d2c326000208094e0005008b80000a2f00005c945a00025c800150262400018a8b684ed00027985fc42a48dab0c4865cc587a96903881f0f296b0c52acf2fb097d27a0000001f4d2eaaaa3241fa10ee0000c8953c00008200000000005135db9f6428c0000550ffc00008b00026f4c500000000000000b66599a8881d00004bfacac4c00000c180000000001cd0c4152e0000bd00017ac78a00012dc0008e900000001d20002d680007ea5751a29fac43e00040710100003d23bf15a800039327500006d800004196287161f2298800000037204484bc42a00000000000006a612480000004d04be0acc000000473ab6438a5302a52e6cd6202e11e25f93f65935db0f6166c3ed5f182fd31673a5ee8c4d4fe52d3c028686da76e0f517200000c95140f78a3856c4868110a1865a23807c413e06e519affc0005b7213800000092023d80008786652e39b4c2ccbab0001e90ff83320e202780009c752f01380001fd2e20a980cc8d61158000bc8000216a7f86aabe400005c000008f0f4800013624c0000fc000025d1a000003fca8f3942b9017a2423fd8808406016000000076e0005c10e24f7a13f000083c00000037280014a40800001b3000a70e00010fc000b2d37506795dc0000002d7c00040c1d98000d483880002f9c000bf206b8e15680090543aea8d5221a0001fc540c00000000001c838e1ba8000faeac00f800000007ec46980001a87915b010d80000000000000000000373000140a00000000011d8adb4c30320cb0000000075132265d5f8
  | 20 => 0x9000102628e321a69515ead12c080001d60001d7a5e400064c41300000000003e40000738773274846951c00000000a4000000022800114088c35804f45526ec5b08c7806800009f2b7d2be42146ca54cd5816a077101860a2405ce8620d5e8ee51d0cd829cb145bb9b240001400a095f430a6a129d14f0b96455000125c60e30600019906a49db15a80011640005790cf0ef890324186289a69f55c523e0938489300a93d5ae13b18c1c7501a6634978eec500ab0096af8034e0000af28f15ba7765d7000105c9b33dc95a4cc05732e69fe150452936d0c9547076705b82a4caa000000000015600052d8418000a4200008e0c6a000001a3380000003bc00012025ff4ea88f405079535b1cac9f676b0001f48f660003bc800006e49f1268ee8b7c7dd2559de96883aa16402d049402c5338000820000013ae508c000053d0001682b84292a2a01c00971c918189e49df00006e80005150001edc728000000000000000022c10297ea00000018d15400004911a14a2cb570000000f1200058380000000000000000000bfb09d174d7f453f00016c49f068a4d201a0000000418ad0800030428a1ec800089e5711a08d120004660e0400072e5e1930d37499037aac787ae27d04396c85ee000000000116679e1492d40000000000000071a11300021201108fa2c8a5307c45d016716bc8664b626f91c94be2835f690d473c7d529c82b82061193dd8f388ac8bc0429f4484cacd0c0222c000aa54d18000e76000000163c0000003bb80000004312b72a0c21236f028928108e70d000000144c00028f1c3d400b642b40000fc23702400a5c00048700005292e433f5e100000000001cb800169c2620af80012144b40000c592a0000362a0e03f005d0000db854000059180014ba00008e000125cbe528080000000000739be00960002570bd826ca885c78c3d3640ec00000995ec0002118000ffe0602d5a494000b982e099ec00000000000000003cc00000000000b123208c47b4bdf5c909dc4200000b787dc31e0000000658000000000000042c0000000664b0e125173af1c00000000000000000000002f200002e95c19e04c34931214aac8d3a000000000083e61c000137000072d3aba6d53fe962195a4e43aa4f1434075c0261620001b9d3627de311ac54a924e21f4000000032e10885b520a0000002ee808286a54d2730e2466b16b291cca200000015506720000002e2c3f600000000000000002ba00000002a2307a9a853028148c0000bb60000000ea55767cf0002de55000000e402e422a000574a81c20e96142b80007e40000001a3445a4f424a080400000014da4cc000a564dd9ab8e7c1ec1621a51208ac83111a38d1e6c408e9d7445847908f2ec94ae0b31271a554100d54471e34960ade36aab14c048763acaa345d821931f9e6058
  | 21 => 0x1ad1e08c2479c23bae345e891000029195d47fa3a110350b48eb54992d56dc2f113e0ef02d8ba25b12cf4336b6f32507700000002ab9cf10de5500001fdd32c3381439b0867462b2bc16506040752ac80008fe1922ac26003cc16b000045168650515e15bc0006b808126b021a00054205a08223373c1a1e4000000375a1302b83343652bc4ab8b5d3a092cd5e01ae03b05f8cf000000500006485df00000000000000a683440007090188000000362000159c98a000000000000000d005acc800004f52880397ae84b44511440000002b580002baafe000100800000046c0000f2e3fc00d221d67e00037724748bc0df1eb2a74464b9a4a408c06c84bc518002000000000000002409290000000f2c0000000001340025000000000000000023340000004d580000006e23c99c7d5920002eb8d844ea7c713fa0c889a7885b60520000b1f240a5ec000aa9000093c26a4d8000000149287f0781bb400022523b0c486920004111998000ac73cd1244f7e4a40829b34200bd42760001468beb5f9955947200005c136c0000000001f697a200000022c000014c2731dc40c8bd20001f007880003e09fd85920a100000012a4317000000143600000030000000002d800007f087b46aa2240e260753929acafe0005381060eb82130431cdd6101bb5a2a8ec00e7ce2cda6297828cb46228dc9ee2353af2a7c4289210000000e108ea0000000a320001e196b861449d0a180010e85d45bd021000000055fa8a92b0ac24d10f94c8c8db59293a04240004398ec084a7d00000cb47eea610000000b6a0001efa4f00007a83930000e9655a44e92940002ab22906247f6bc00baa9bd3ac0a51d90ec50c42b700011f8000a71046000080e6e11299fc06a68ed00000015d82e613a16914d23bd20410b8d8c4de5e610e03520003718000cd44d400000005700000001a7889871e4ae902400001800000017ec30957e1a5c794b123e184cc0000004b51ef88246ba00000010c20000d5162c6e6a3624300013de00000000000000003a029641fe00000000017109f15680c54d9e4d60001074000000000192400076159d29d82ae000414a900e580000001108cde652000000105644b3da0000000aa718fa09047c57034c80011520005e58000000000130800065429f0001f886a87c62bd800000000000024693c6000000000025c29300022690304bb05
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xe715941001cfd715941001cfc715941001e7e515941001e7c5159410024ff7059410024fe7059410024fd7059410024fc70594100267e50594100267c5059410026f71059410026f51059410004ff7559010044fc7559010024ff7459010026bf7459010004ff7359010014fe7359010014fc7359010004ff725901000cfe725901000cfc725901001cff715901001cfe715901001cfd715901001cfc715901001ebe415901001ebc4159010024ff7059010024fe7059010024fd7059010024fc7059010026be4059010026bc4059010026fa105901001ef91059010044ff76d5010024fe76d5010004fd76d5010024fc76d50100467e65d50100067d65d501003cff7695010024fe7695010004fd7695010024fc769501003ebe6495010006bd64950100073f5495010004ff7655010024fe7655010004fd7655010024fc76550100467e65550100067d655501003ebe6455010006bd6455010005f7715501001df47155010005fb7055010025f8705501003cff7615010024fe7615010004fd7615010024fc7615010004ff7558c10044fc7558c10004ff7458c1003cfc7458c10024ff7358c10026df7358c10036de5358c10036de4358c10004ff7258c1000cfe7258c1000cfc7258c10006de3258c10036dc3258c1001cff7158c1001cfe7158c1001cfd7158c1001cfc7158c1001ede3158c1001edc3158c10024ff7058c10024fe7058c10024fd7058c10024fc7058c10026de3058c10026dc3058c10026f71058c10026fa1058c10026f51058c1001ef91058c10044ff76d4c10024fe76d4c10004fd76d4c10024fc76d4c100375e53d4c10004ff7654c10024fe7654c10004fd7654c10024fc7654c10016de6354c10006dd6354c1003cff76d0c10024fe76d0c10004fd76d0c10024fc76d0c10004ff7650c10024fe7650c10004fd7650c10024fc7650c10016de6350c10006dd6350c10004ff7558810044fc7558810004ff745881003cfc7458810004ff7358810014fe7358810014fc7358810024ff7258810026ef725881002eee525881002eee4258810006ef325881002eec325881001cff715881001cfe715881001cfd715881001cfc715881001eee215881001eec2158810024ff7058810024fe7058810024fd7058810024fc7058810026ee2058810026ec2058810026f71058810026fa1058810026f5105881001ef91058810044ff76d4810024fe76d4810004fd76d4810024fc76d481002f6e52d4810004ff7654810024fe7654810004fd7654810024fc765481000eee6254810006ed625481003cff76d0810024fe76d0810004fd76d0810024fc76d0810004ff7650810024fe7650810004fd7650810024fc765081000eee6250810006ed6250810004ff764c810024fe764c810004fd764c810024fc764c81002fcc324c810
  | 1 => 0x110007f12150110005fa768c110026fa768c11023dfa758c110025f8758c1100077b658c11000778658c110025fb748c110005f9748c110007bb648c110007b8648c110055f9738c110016fa638c110016f8638c110005f9728c110006fb628c110006f9628c110027f3718c11001dfa718c110025f8718c110027f0718c110026fb618c110027f3618c110007f2518c110007f1518c110007f3418c110007f0418c110057f2318c110057f1318c110007f2218c110007f1218c110014ff764c110054fd764c11001cfc764c1100067f654c1100067c654c110006bf644c110006bc644c110006df634c110016dc634c110005f7714c11001df4714c110027f0104c11001df8764c110016f8764c11001cf8764c11023dfa754c11023df8754c1100077b654c11000778654c110005fb744c110005f9744c110007bb644c110007b8644c110025fb734c110027db734c110007db634c110016fa634c110016f8634c110057d8634c110057da534c110007d9534c110005fb724c110006fb624c110006f9624c110007f3714c11001dfa714c11001df8714c110007f0714c110026fb614c110027f3614c110007f2514c110007f1514c110007f3414c110007f0414c110057f2314c110057f1314c110007f2214c110007f1214c110005fa7688110026fa768811023dfa7588110025f875881100077b6588110007786588110025fb7488110005f97488110007bb6488110007b86488110025fb7388110005f97388110006fb6388110006f9638811004df9728811000efa628811000ef86288110027f3718811001dfa7188110025f87188110027f07188110026fb6188110027f36188110007f25188110007f15188110007f34188110007f04188110007f23188110007f1318811004ff2218811004ff1218811000cff764811004cfd764811001cfc76481100067f65481100067c6548110006bf6448110006bc6448110006ef624811000eec6248110005f7714811001df47148110027f0104811001df8764811000ef8764811001cf8764811023dfa754811023df875481100077b6548110007786548110005fb7448110005f97448110007bb6448110007b86448110005fb7348110005f97348110006fb6348110006f96348110025fb7248110027eb7248110007eb624811000efa624811000ef8624811004fe8624811004fea5248110007e95248110007f3714811001dfa714811001df87148110007f07148110026fb6148110027f36148110007f25148110007f15148110007f34148110007f04148110007f23148110007f1314811004ff2214811004ff12148110024ff75594100267f7559410004ff745941003cfc7459410004ff7359410014fe7359410014fc7359410004ff725941000cfe725941000cfc725941001cff715941001cf
  | 2 => 0x6bf64d4110006bc64d411001df671d4110005f571d411001dfa76d411023efa76d411001cfa76d4110025fa75d411023efb65d41100077b65d411023ef965d411023f7865d4110005f974d4110007bb64d4110266fa64d4110266f864d4110007b864d4110006b864d4110005f973d4110005f972d411001dfa71d411023ff271d411023ff171d411001df871d4110026fb61d4110027f361d411023ff251d411023ff151d4110007f341d4110007f041d4110007f231d4110007f131d4110007f221d4110007f121d4110044ff7654110004fd765411001cfc76541100067f65541100467c6554110006bf6454110006bc6454110005f7715411001df47154110027785054110005fa7614110026fa761411023dfa75141100277a751411023efb65141100077b65141100067b651411023ef9651411023f786514110027ba7414110005f97414110027b97414110005b97414110007bb641411025efa641411025ef86414110007b86414110006b8641411023f7b5414110007795414110027da7314110005f97314110027d97314110005d97314110027ea7214110005f97214110027e97214110005e9721411001dfa7114110027f2711411001df27114110027f17114110025f87114110026fb6114110027f361141102577a511411023ff2511411000772511411023ff15114110257785114110007f34114110007f04114110007f23114110007f13114110007f22114110007f1211411001cfe76d011001cfc76d01100057e75d01100057d75d01100067f65d01100067c65d0110006bf64d011003ebc64d011001df671d0110005f571d0110005fa7690110026fa769011023dfa7590110025f875901100077b6590110007786590110005f97490110007bb649011003efa649011003ef86490110007b8649011003eb86490110005f97390110005f9729011001dfa7190110027f2719011001df27190110027f17190110025f87190110026fb6190110027f36190110007f25190110007f15190110247f3419011024fba419011024fb84190110247f04190110007b04190110007f23190110007f13190110007f22190110007f1219011003cff7650110004fd765011001cfc76501100067f65501100067c6550110006bf645011003ebc6450110005f7715011001df4715011001df8765011003ef8765011001cf8765011023dfa755011023df875501100077b6550110007786550110025fb7450110027bb7450110007bb645011003efa645011003ef86450110007b86450110007ba5450110007b95450110005fb7350110005fb7250110007f3715011001dfa715011001df87150110007f07150110026fb6150110027f36150110007f25150110007f15150110247f34150110247f04150110007f23150110007f13150110007f2215
  | 3 => 0xc76505100067f65505100067c6550510006bf645051003ebc6450510005fb7050510025f87050510005f6761051001ef6761051001df7751051001f767510510005f5751051001f757510510005757510510007776510510276f66510510276f46510510007746510510006746510510245f6741051001fb67410510246f76410510007b76410510006b76410510246f56410510247b46410510247b65410510007b5541051001fd67310510005f5731051001fd57310510005d5731051001fe67210510005f5721051001fe57210510005e57210510025f6701051001ff27010510025f2701051001ff17010510025f4701051001ef7601051001ff3601051026fb6401051026fb44010510005f6768c51001ef6768c51001df7758c510005f5758c51000777658c51000774658c510245f6748c51001df4748c510007b7648c510007b4648c510055f5738c510016f6638c510016f4638c510005f5728c510006f7628c510006f5628c51001ff3708c510025f6708c510025f4708c51001ff0708c51001ef7608c51001ff3608c510024fc764c5100067f654c5100067c654c510006bf644c510006bc644c510006df634c510016dc634c510005fb704c510025f8704c51001ff0104c510025f4764c510016f4764c510024f4764c510005f7754c510005f5754c51000777654c51000774654c510245f6744c510245f4744c510007b7644c510007b4644c51001df7734c51001fd7734c510007d7634c510016f6634c510016f4634c510057d4634c510057d6434c510007d5434c510005f7724c510006f7624c510006f5624c510007f3704c510025f6704c510025f4704c510007f0704c51001ef7604c51001ff3604c510005f6768851001ef6768851001df77588510005f57588510007776588510007746588510245f6748851001df47488510007b76488510007b4648851001df77388510005f57388510006f76388510006f5638851004df5728851000ef6628851000ef4628851001ff37088510025f67088510025f4708851001ff0708851001ef7608851001ff36088510024fc76485100067f65485100067c6548510006bf6448510006bc6448510006ef624851000eec6248510005fb7048510025f8704851001ff01048510025f4764851000ef47648510024f47648510005f77548510005f57548510007776548510007746548510245f67448510245f47448510007b76448510007b46448510005f77348510005f57348510006f76348510006f5634851001df7724851001fe77248510007e7624851000ef6624851000ef4624851004fe4624851004fe64248510007e54248510007f37048510025f67048510025f47048510007f0704851001ef7604851001ff3604851001cfe76d411001cfc76d41100067f65d41100467c65d4110
  | 4 => 0x8910005df7358910055dc735891004eec6258910004ff75589100067f75589100047f7558910044fc75589100067c75589100447c7558910004ff7458910006bf7458910004bf745891003cfc7458910006bc745891003cbc7458910004ff7358910006df7358910004df7358910014fe7358910014fc7358910006dc7358910014dc735891004cff7258910006ef725891005cff7158910006f7715891006cff7058910006fb7058910044ff76d4910004fe76d4910004fd76d4910044fc76d49100067f65d49100467c65d4910006bf64d4910006bc64d491004f6e52d491001df671d4910005f571d4910004ff7654910004fe7654910004fd7654910004fc76549100067f65549100467c6554910006bf6454910006bc6454910005fb7054910025f8705491003cff76d0910004fe76d0910004fd76d091003cfc76d09100067f65d09100067c65d0910006bf64d091003ebc64d0910025fa70d0910005f970d0910004ff7650910004fe7650910004fd7650910004fc76509100067f65509100067c6550910006bf645091003ebc6450910005f7715091001df47150910004ff764c910004fe764c910004fd764c910004fc764c9100067f654c9100067c654c910006bf644c910006bc644c91004fcc324c910024fe76d4510024fc76d45100067f65d45100467c65d4510005be74d4510005bd74d4510006bf64d4510006bc64d4510025fa70d4510005f970d4510005f6769451001ef67694510005f57594510007776594510046f66594510046f46594510007746594510046746594510245f67494510007b76494510007b46494510005f57394510005f57294510025f6709451001ff27094510025f2709451001ff17094510025f4709451001ef7609451001ff36094510287765094510287745094510024fc76545100067f65545100467c6554510006bf6454510006bc6454510005fb7054510025f87054510025f47654510046f47654510024f4765451001df7755451001f777554510007776554510046f66554510046f46554510007746554510245f47454510007b76454510007b46454510007775454510007755454510005f77354510005f77254510007f37054510025f67054510025f47054510007f0705451001ef7605451001ff36054510024fe76d0510024fc76d05100067f65d05100067c65d0510006bf64d051003ebc64d0510025fa70d0510005f970d0510025f676d0510246f676d0510024f676d0510245f775d0510005f575d05100077765d051027ef665d051027ef465d05100077465d05100067465d051001df674d0510246f764d0510007b764d0510246f564d0510247b464d0510005f573d0510005f572d0510025f670d0510247f270d0510247f170d0510025f470d051001ef760d051001ff360d0510024f
  | 5 => 0x467c65d5110006bf64d511003ebc64d511001df671d5110005f571d511003cff7695110004fe7695110004fd769511003cfc76951100067f65951100467c6595110006bf649511003ebc64951100073f5495110025fa7095110005f97095110004ff7655110004fe7655110004fd7655110004fc76551100067f65551100467c6555110006bf645511003ebc6455110005f7715511001df47155110005fb7055110025f8705511003cff7615110004fe7615110004fd761511003cfc76151100067f65151100467c6515110006bf641511003ebc641511001df67115110005f57115110025fa7015110005f97015110014fe76d8d100067f65d8d100067c65d8d10006bf64d8d10006bc64d8d10056de63d8d10044fe75d8d10004fd75d8d1003cfe74d8d10004fd74d8d1000cfe72d8d10004fd72d8d1000cfc72d8d10006de32d8d10056dc32d8d1001cfe71d8d10024fd71d8d1001cfc71d8d10056df31d8d10024fe70d8d1001cfd70d8d10024fc70d8d10056df30d8d100057f7558d100057c7558d100067f6558d100067c6558d10005bf7458d10005bc7458d10006bf6458d10006bc6458d10056dc6358d10005ef7258d1004dec7258d10004ff7558d100067f7558d100047f7558d10044fc7558d100067c7558d100447c7558d10004ff7458d10006bf7458d10004bf7458d1003cfc7458d10006bc7458d1003cbc7458d10054ff7358d10006df7358d10004ff7258d10006ef7258d10004ef7258d1000cfe7258d1000cfc7258d10006ec7258d1000cec7258d10064ff7158d10006f77158d10074ff7058d10006fb7058d10044ff76d4d10004fe76d4d10004fd76d4d10044fc76d4d100067f65d4d100467c65d4d10006bf64d4d10006bc64d4d100575e53d4d1001df671d4d10005f571d4d10004ff7654d10004fe7654d10004fd7654d10004fc7654d100067f6554d100467c6554d10006bf6454d10006bc6454d10005fb7054d10025f87054d1003cff76d0d10004fe76d0d10004fd76d0d1003cfc76d0d100067f65d0d100067c65d0d10006bf64d0d1003ebc64d0d10025fa70d0d10005f970d0d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100067f6550d100067c6550d10006bf6450d1003ebc6450d10005f77150d1001df47150d1000cfe76d89100067f65d89100067c65d8910006bf64d8910006bc64d891004eee62d8910044fe75d8910004fd75d891003cfe74d8910004fd74d8910014fe73d8910004fd73d8910014fc73d8910006ef32d891004eec32d891001cfe71d8910024fd71d891001cfc71d891004eef21d8910024fe70d891001cfd70d8910024fc70d891004eef20d89100057f75589100057c75589100067f65589100067c6558910005bf7458910005bc7458910006bf6458910006bc645
  | 6 => 0xe76d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110006be63d9110006bc63d9110006be62d9110006bc62d9110007b571d911024fbb70d911024fbb10d9110297b610d9110297b410d911024fb810d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006be53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006be52d9110006bc52d9110006bf32d9110006be32d9110006bc32d9110296bf71d911024ebe71d9110006bd71d9110006b571d911024ebc71d911024ebe51d911024ebc51d9110006bf31d911024ebe31d911024ebc31d9110006bf21d911024ebe21d911024ebc21d911024ebf70d9110296be70d9110006bd70d9110296bc70d9110296be50d9110296bc50d9110006bf30d9110296be30d9110296bc30d9110006bf20d9110296be20d9110296bc20d911024ebf10d9110296be10d9110296bc10d91100057e75991100057d75991100067f65991100067c6599110006bf64991100057f75591100057c75591100067f65591100067c6559110004ff75591100067f75591100047f7559110044fc75591100067c75591100447c7559110006bf7459110004ff7359110014fe7359110014fc7359110004ff725911000cfe725911000cfc7259110004ff7159110006f77159110004ff7059110006fb7059110004fe76191100067f65191100067c651911003ebe6419110006bd6419110005be7619110006be7619110004be7619110006bf65191100073f65191100063f6519110006be6519110006bd6519110006bc65191100073c65191100063c6519110006be6319110006bc6319110006be6219110006bc621911026fb77119110007b9701911028fbb101911026fb6101911026fb4101911028fb8101911003ebf751911003ebe751911003ebd751911003ebc751911003ebf731911003ebe731911003ebd731911003ebc7319110006be5319110006bc531911003ebf721911003ebe721911003ebd721911003ebc7219110006be5219110006bc5219110006bf3219110006be3219110006bc321911003ebf711911003ebe711911003ebd711911003ebc711911028ebe511911028ebc5119110006bf311911028ebe311911028ebc3119110006bf211911028ebe211911028ebc211911003ebf701911003ebe701911003ebd701911003eb9701911003ebc701911026ebe501911026ebc5019110006bf301911026ebe301911026ebc3019110006bf201911026ebe201911026ebc201911028ebf101911026ebe1019110006bd101911026ebc1019110044ff76d5110004fe76d5110004fd76d5110044fc76d51100067f65d5110
  | 7 => 0x95100067c52d951001cfe71d951001cfc71d9510024fe70d9510006f970d9510024fc70d95100447e76d95100067e63d95100067c63d95100067e62d95100067c62d95102877771d95100077970d95102a77b10d95102877610d95102877410d95102a77810d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067e43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067e42d95100067c42d95100067f32d95100067e32d95100067c32d95102867f71d95102a67e71d95100067d71d95102a67c71d95102a67e41d95102a67c41d95100067f31d95102a67e31d95102a67c31d95100067f21d95102a67e21d95102a67c21d95102a67f70d95102867e70d95100067d70d95100067970d95102867c70d95102867e40d95102867c40d95100067f30d95102867e30d95102867c30d95100067f20d95102867e20d95102867c20d95102a67f10d95102867e10d95102867c10d95100067f6599510005be7499510005bd7499510005bf7459510005bc74595100067f7559510004ff7459510006bf7459510004bf745951003cfc7459510006bc745951003cbc7459510004ff7359510014fe7359510014fc7359510004ff725951000cfe725951000cfc7259510004ff7159510006f77159510004ff7059510006fb7059510004fe76195100467e65195100067d65195100057e76195100067e76195100047e76195100067e63195100067c63195100067e62195100067c62195100077571195102577b70195102577b101951029f76101951029f7410195102577810195100467f74195100467e74195100467d74195100467c74195100467f73195100467e73195100467d73195100467c73195100067e43195100067c43195100467f72195100467e72195100467d72195100467c72195100067e42195100067c42195100067f32195100067e32195100067c32195100467f71195100467e71195100467d71195100467571195100467c71195102567e41195102567c41195100067f31195102567e31195102567c31195100067f21195102567e21195102567c21195100467f70195100467e70195100467d70195100467c701951029e7e401951029e7c40195100067f301951029e7e301951029e7c30195100067f201951029e7e201951029e7c20195102567f101951029e7e10195100067d101951029e7c101951003cfe76d91100067f65d91100067c65d9110044fe75d9110004fd75d9110014fe73d9110004fd73d9110014fc73d9110006be43d9110006bc43d911000cfe72d9110004fd72d911000cfc72d9110006be42d9110006bc42d911001cfe71d9110006f571d911001cfc71d9110024fe70d9110024fc70d911003cb
  | 8 => 0x6dd6354e10005fb7054e10025f87054e1003cff76d0e10024fe76d0e10004fd76d0e10024fc76d0e10025fa70d0e10005f970d0e10004ff7650e10024fe7650e10004fd7650e10024fc7650e10025fa7050e10004ff7558a10044fc7558a10004ff7458a1003cfc7458a10004ff7358a10014fe7358a10014fc7358a10026ef7258a1005eee5258a1005eef2158a10024fc7058a10026fa3058a10026ee2058a10026ec2058a10026f71058a10026f51058a10044ff76d4a10024fe76d4a10004fd76d4a10024fc76d4a1005f6e52d4a10025f870d4a10004ff7654a10024fe7654a10004fd7654a10024fc7654a1000eee6254a10006ed6254a10005fb7054a10025f87054a1003cff76d0a10024fe76d0a10004fd76d0a10024fc76d0a10025fa70d0a10005f970d0a10004ff7650a10024fe7650a10004fd7650a10024fc7650a10025fa7050a10004ff764ca10024fe764ca10004fd764ca10024fc764ca1005fcc324ca10025fa704ca10024ff7158610024ff705861001efb1058610026f61058610026f41058610026f810586100467e65d46100067d65d4610005be74d4610005bd74d461001f7651d4610025fa70d4610005f970d4610044ff76546100467e65546100067d6554610005fb7054610025f8705461003ebe64d0610006bd64d0610025fa70d0610005f970d061003cff765061003ebe6450610006bd645061001fb44150610005fb7050610025f87050610014ff764c610024fc764c610016de634c610006dd634c610005fb704c610025f8704c61000cff7648610024fc764861000eee6248610006ed6248610005fb7048610025f87048610025f976d42102aef976d42100277a75d4210026fb65d42102aef965d4210005f974d4210266fa64d4210026f864d4210005f973d4210005f972d421001dfa71d421001df871d4210025fb7650210006fb76502102adfa75502102adf87550210027bb745021003efa6450210026f86450210007ba5450210007b95450210005fb7350210005fb725021001dfa715021001df87150210025fb764c210036fb764c2102adfa754c2102adf8754c210005fb744c210005f9744c210027db734c210016fa634c210026f8634c210067da534c210007d9534c210005fb724c210026fb624c210006f9624c21001dfa714c21001df8714c210025fb764821002efb76482102adfa75482102adf87548210005fb7448210005f97448210005fb7348210005f97348210026fb6348210006f96348210027eb724821000efa6248210026f8624821005fea5248210007e9524821001dfa714821001df87148210044fe76d951003cfe74d9510004fd74d9510014fe73d9510004fd73d9510014fc73d95100067e53d95100067c53d951000cfe72d9510004fd72d951000cfc72d95100067e52d
  | 9 => 0x4705471001df576d07102c6f576d07102c5f775d0710005f575d071027ef665d071001ef465d071001fb674d071001ef764d07102c6f564d0710005f573d0710005f572d0710025f670d0710025f470d071001df7764c710036f7764c710005f7754c710005f5754c7102c5f6744c7102c5f4744c71001fd7734c710016f6634c71001ef4634c710077d6434c710007d5434c710005f7724c71001ef7624c710006f5624c710025f6704c710025f4704c71001df7764871002ef77648710005f77548710005f575487102c5f674487102c5f47448710005f77348710005f5734871001ef76348710006f5634871001fe7724871000ef6624871001ef4624871006fe64248710007e54248710025f67048710025f470487100467e65d43100067d65d431001df671d4310005f571d4310044ff76543100467e65543100067d6554310005f7715431001df471543100057e75d03100057d75d031003ebe64d0310006bd64d031001df671d0310005f571d031003cff765031003ebe6450310006bd6450310005f7715031001df47150310014ff764c31001cfc764c310016de634c310006dd634c310005f7714c31001df4714c31000cff764831001cfc764831000eee6248310006ed6248310005f7714831001df471483100267f7559610004ff745961003cfc7459610004ff7359610014fe7359610014fc7359610004ff725961000cfe725961000cfc7259610024fc7059610026f87059610024f870596100267e50596100267c5059610026f85059610026f71059610026f51059610004ff7559210044fc7559210026bf7459210004ff7359210014fe7359210014fc7359210004ff725921000cfe725921000cfc7259210024fc7059210026be4059210026bc4059210044ff76d5210024fe76d5210004fd76d5210024fc76d52102be7f65d52100467c65d5210025f870d52102bf7850d521003cff7695210024fe7695210004fd7695210024fc769521003ebe6495210006bd64952100073f5495210025fa7095210005f97095210004ff7655210024fe7655210004fd7655210024fc76552102b67f65552100467c655521003ebe6455210006bd6455210005f7715521001df47155210005fb7055210025f870552102b778505521003cff7615210024fe7615210004fd7615210024fc7615210025fa7015210005f97015210004ff7558e10044fc7558e10004ff7458e1003cfc7458e10026df7358e10066de5358e10004ff7258e1000cfe7258e1000cfc7258e10066df3158e10024fc7058e10026de3058e10026dc3058e10026fa2058e10026f71058e10026f51058e10044ff76d4e10024fe76d4e10004fd76d4e10024fc76d4e100675e53d4e10025f870d4e10004ff7654e10024fe7654e10004fd7654e10024fc7654e10016de6354e10
  | 10 => 0xc120027eb624c12008fea524c120007e9524c120005fb714c120006fb614c12001e7f7559710004ff745971003cfc7459710004ff7359710014fe7359710014fc7359710004ff725971000cfe725971000cfc7259710024fc715971001e7e515971001e7c5159710004ff7559310044fc755931001ebf7459310004ff7359310014fe7359310014fc7359310004ff725931000cfe725931000cfc7259310024fc715931001ef47159310024f4715931001ebe415931001ebc415931001ef4415931001eb4415931001efa105931001ef91059310044ff76d531001cfe76d5310004fd76d531001cfc76d53100467e65d53100067d65d531001df671d5310005f571d531003cff769531001cfe7695310004fd769531001cfc76953102d6bf649531003ebc64953100073f549531001df471953102d7b44195310004ff765531001cfe7655310004fd765531001cfc76553100467e65553100067d65553102cebf645531003ebc6455310005f7715531001df471553102cfb44155310005fb7055310025f8705531003cff761531001cfe7615310004fd761531001cfc761531001df67115310005f57115310004ff7558f10044fc7558f10004ff7458f1003cfc7458f1001edf7358f10076de4358f10004ff7258f1000cfe7258f1000cfc7258f10024fc7158f1001ede3158f1001edc3158f1001ef62158f10076df3058f1001efa1058f1001ef91058f10044ff76d4f1001cfe76d4f10004fd76d4f1001cfc76d4f100775e53d4f1001df671d4f10005f571d4f10004ff7654f1001cfe7654f10004fd7654f1001cfc7654f1001df67154f1003cff76d0f1001cfe76d0f10004fd76d0f1001cfc76d0f1001df471d0f10004ff7650f1001cfe7650f10004fd7650f1001cfc7650f10016de6350f10006dd6350f10005f77150f1001df47150f10004ff7558b10044fc7558b10004ff7458b1003cfc7458b10004ff7358b10014fe7358b10014fc7358b1001eef7258b1006eee4258b10024fc7158b1001ef63158b1001eee2158b1001eec2158b1006eef2058b1001efa1058b1001ef91058b10044ff76d4b1001cfe76d4b10004fd76d4b1001cfc76d4b1006f6e52d4b1001df671d4b10005f571d4b10004ff7654b1001cfe7654b10004fd7654b1001cfc7654b1001df67154b1003cff76d0b1001cfe76d0b10004fd76d0b1001cfc76d0b1001df471d0b10004ff7650b1001cfe7650b10004fd7650b1001cfc7650b1000eee6250b10006ed6250b10005f77150b1001df47150b10004ff764cb1001cfe764cb10004fd764cb1001cfc764cb1006fcc324cb1001df6714cb1001df77654710006f7765471001f777554710046f6655471001ef465547102c5f47454710007775454710007755454710005f77354710005f77254710025f67054710025f
  | 11 => 0xf6f75549200076f6554920046ee6554920046ec65549200076c65549200076f54549200076d54549200076f53549200076d5354920007eb7054920025ee7054920025ec7054920007e8705492000eef605492000feb6054920044fe75d8520004fd75d852003cfe74d8520004fd74d8520014fe73d8520004fd73d8520014fc73d8520024fd72d852005ef621d852005ef521d8520024fe70d8520006f7619852004df970985200057f75585200057c7558520005bf7458520005bc7458520005df735852007ddc735852006dfb705852001ef66118520006f56118520004fe76d4520004fd76d4520044fc76d4520005be74d4520005bd74d452000dee72d4520005ed72d4520004fe7694520004fd769452001cfc76945200067f65945200467c6594520025fa7094520005f97094520004ff7654520004fe7654520004fc7654520004fe7614520004fd761452001cfc76145200067f65145200467c651452000dee7214520005ed7214520025fa7014520005f97014520004fe76d0520004fd76d052003cfc76d0520004fe7690520004fd769052001cfc7690520006bf649052003ebc6490520025fa7090520005f97090520004ff7650520004fe7650520004fc7650520004fe7610520004fd761052001cfc76105200057e75105200057d7510520006bf641052003ebc641052007dde7310520005dd731052000dee7210520005ed7210520025fa7010520005f97010520004fe768c520004fd768c52001cfc768c520006df638c520016dc638c52000dee728c520005ed728c52001ef6618c520025fa708c520005f9708c520004ff764c520004fe764c520004fc764c52000cfe76d412000cfc76d41200067f65d41200467c65d412000dee72d4120005ed72d41200277a50d4120044ff765412000cfe76541200ecfd765412000cfc76541200067f65541200467c6554120005ef725412000dec725412000cfe76d012000cfc76d01200057e75d01200057d75d0120006bf64d012003ebc64d012000dee72d0120005ed72d012003cff765012000cfe76501200acfd765012000cfc7650120006bf645012003ebc6450120005ef725012000dec7250120027e820501202ddfa768c120026fa768c12008df9738c120016fa638c120016f8638c12000dfa728c120025f8728c120026fb628c120027eb628c120097ea528c120007e9528c120005f9718c120006fb618c120014ff764c12000cfe764c12008cfd764c12000cfc764c120006df634c120016dc634c120005ef724c12000dec724c12000df8764c120016f8764c12000cf8764c120025fb734c120027db734c120007db634c120016fa634c120016f8634c12007fd8634c12007fda534c120007d9534c120007eb724c12000dfa724c12000df8724c12008fe8724c120026fb624
  | 12 => 0xf72d952000cfe72d9520024fd72d952000cfc72d95200fe7f52d95200fe7d52d952001cfe71d9520004fd71d95200067f65995200edf97099520005df735952007ddc735952010dfb70595200067f7559520004ff745952003cfc7459520004ff7359520006df7359520004df7359520014fe7359520014fc7359520006dc7359520014dc73595200ecff7259520006ef7259520004ff715952001cfc715952010cff7059520006fb70595200fcfe76195200467e65195200067d6519520005be7419520005bd741952003cfe76d9120044fe75d9120004fd75d9120014fe73d9120004fd73d9120014fc73d9120024ff72d912000cfe72d9120024fd72d912000cfc72d91200bebf42d91200bebd42d912001cfe71d9120004fd71d91200057e75991200057d7599120006bf649912007dde7399120005dd73991200adf970991200cdfb7059120004ff7559120044fc7559120006bf7459120004ff7359120014fe7359120014fc73591200acff7259120006ef7259120004ff715912001cfc71591200ccff7059120006fb70591200bcfe761912003ebe6419120006bd6419120044ff76d5120004fe76d5120004fd76d5120044fc76d51200067f65d51200467c65d512000dee72d5120005ed72d512003cff7695120004fe7695120004fd769512003cfc769512003ebe6495120006bd64951200073f5495120004ff7655120004fe7655120004fd7655120004fc76551200067f65551200467c655512003ebe6455120006bd6455120005f77155120005f47155120005fb7055120025f8705512003cff7615120004fe7615120004fd761512003cfc761512000dee7215120005ed7215120014fe76d8d2007ede63d8d20044fe75d8d20004fd75d8d2003cfe74d8d20004fd74d8d2007edc53d8d2007ede43d8d20024ff72d8d2000cfe72d8d20024fd72d8d2000cfc72d8d20096df32d8d20096dd32d8d2001cfe71d8d20004fd71d8d2007edc31d8d2000cfd70d8d2007edf30d8d200057f7558d200057c7558d2007edc6358d202e5fb7058d20004ff7558d200067f7558d200047f7558d20044fc7558d200067c7558d200447c7558d20004ff7458d2003cfc7458d20094ff7358d20006df7358d2008cff7258d20006ef7258d20004ff7158d2001cfc7158d202e4ff7058d20006fb7058d20044ff76d4d20004fe76d4d20004fd76d4d20044fc76d4d20006df63d4d20016dc63d4d2007f5e53d4d2000dee72d4d20005ed72d4d20004ff7654d20004fe7654d20004fd7654d20004fc7654d2003cff76d0d20004fe76d0d20004fd76d0d2003cfc76d0d20004ff7650d20004fe7650d20004fd7650d20004fc7650d20006df6350d20016dc6350d20005ef7250d2000dec7250d20025ec7654920046ec7654920024ec765492000def7554920
  | 13 => 0x9220044ff76d5220024fe76d5220004fd76d5220024fc76d52202be7f65d52200467c65d522003cff7695220024fe7695220004fd7695220024fc769522003ebe6495220006bd64952200073f5495220004ff7655220024fe7655220004fd7655220024fc76552202b67f65552200467c655522003ebe6455220006bd6455220005f77155220005f47155220005fb7055220025f8705522003cff7615220024fe7615220004fd7615220024fc7615220004ff7558e20044fc7558e20004ff7458e2003cfc7458e20026df7358e20086de5358e20086dc4358e2008edf3258e2008edd3258e20004ff7158e2001cfc7158e20086df3158e20024fe7058e20024fc7058e20026de3058e20026dc3058e20026fa1058e20044ff76d4e20024fe76d4e20004fd76d4e20024fc76d4e200875e53d4e20004ff7654e20024fe7654e20004fd7654e20024fc7654e20016de6354e20006dd6354e20005ef7254e2000dec7254e2003cff76d0e20024fe76d0e20004fd76d0e20024fc76d0e20016de63d0e20006dd63d0e2000dee72d0e20005ed72d0e20004ff7650e20024fe7650e20004fd7650e20024fc7650e20004ff7558620044fc7558620004ff745862003cfc7458620004ff7358620014fe7358620014fc7358620026f7715862004ef6215862004ef52158620024fd7058620024fc7058620026fa3058620026f61058620026f41058620044ff76d4620024fe76d4620004fd76d4620005be74d4620005bd74d462001cff7694620024fe7694620004fd769462001ef66194620006f56194620025fa7094620005f97094620004ff7654620004fd7654620024fc765462001ef66154620006f5615462001cff7614620024fe7614620004fd7614620025fa7014620005f9701462003cff76d0620024fe76d0620004fd76d062001ef661d0620006f561d062001cff7690620024fe7690620004fd7690620025fa7090620005f97090620004ff7650620004fd7650620024fc765062001cff7610620024fe7610620004fd76106200057e75106200057d7510620085de7310620005dd731062000dee7210620005ed721062001ef66110620006f56110620025fa7010620005f9701062001cff768c620024fe768c620004fd768c62001ef6618c620006f5618c620025fa708c620005f9708c620004ff764c620004fd764c620024fc764c620016de634c620006dd634c620005ef724c62000dec724c62001ef6614c620006f5614c620025fa704c620025fb764c2202eefb764c220027db734c220016fa634c220026f8634c220087da534c220007d9534c22000dfa724c22000df8724c220005fb714c220006f9614c220044fe76d952003cfe74d9520004fd74d9520014fe73d9520004fd73d9520014fc73d95200067e53d95200067c53d9520024f
  | 14 => 0x4fd76d4930044fc76d4930015de73d4930005dd73d49300075d53d4930006ef62d493000eec62d493008f6e52d4930004ff7654930004fe7654930004fc76549300075d5354930004fe76d0930004fd76d093003cfc76d0930004ff7650930004fe7650930004fc7650930005df7350930015dc7350930006ef625093000eec6250930044fe75d8530004fd75d853003cfe74d8530004fd74d8530024fd73d853000cfe72d8530004fd72d853000cfc72d8530066f631d8530066f531d8530006f76198530055f970985300057f75585300057c7558530005bf7458530005bc7458530005ef725853008dec7258530075fb705853001ef66118530006f56118530004fe76d4530004fd76d4530044fc76d4530005be74d4530005bd74d4530015de73d4530005dd73d4530004fe7694530004fd769453001cfc76945300067f65945300467c6594530025fa7094530005f97094530004ff7654530004fe7654530004fc7654530004fe7614530004fd761453001cfc76145300067f65145300467c6514530015de7314530005dd7314530025fa7014530005f97014530004fe76d0530004fd76d053003cfc76d0530004fe7690530004fd769053001cfc7690530006bf649053003ebc6490530025fa7090530005f97090530004ff7650530004fe7650530004fc7650530004fe7610530004fd761053001cfc76105300057e75105300057d7510530006bf641053003ebc6410530015de7310530005dd731053008dee7210530005ed7210530025fa7010530005f97010530004fe7688530004fd768853001cfc7688530015de7388530005dd7388530006ef628853000eec628853001ef66188530025fa7088530005f97088530004ff7648530004fe7648530004fc7648530014fe76d4130014fc76d41300067f65d41300467c65d4130015de73d4130005dd73d41300277a50d4130044ff7654130014fe76541300f4fd7654130014fc76541300067f65541300467c6554130005df7354130015dc7354130014fe76d0130014fc76d01300057e75d01300057d75d0130006bf64d013003ebc64d0130015de73d0130005dd73d013003cff7650130014fe76501300b4fd7650130014fc7650130006bf645013003ebc6450130005df7350130015dc7350130027d830501300267f7559620004ff745962003cfc7459620004ff7359620014fe7359620014fc73596200ee7f52596200ee7d5259620004ff715962001cfc7159620024fe7059620024fc70596200267e50596200267c5059620026ef2059620026ed2059620004ff7559220044fc7559220026bf7459220004ff7359220014fe7359220014fc73592200aebf42592200aebd4259220004ff715922001cfc7159220024fe7059220024fc7059220026be4059220026bc4059220026fa105
  | 15 => 0x66110630006f56110630025fa7010630005f9701063001cff7688630024fe7688630004fd768863001ef66188630006f56188630025fa7088630005f97088630004ff7648630004fd7648630024fc7648630005df7348630015dc734863000eee6248630006ed624863001ef66148630006f56148630025fa7048630044fe76d953003cfe74d9530004fd74d9530024ff73d9530014fe73d9530024fd73d9530014fc73d95301067f53d95301067d53d953000cfe72d9530004fd72d953000cfc72d95300067e52d95300067c52d953001cfe71d9530004fd71d95300067f65995300f5f97099530005ef725953008dec7259530115fb70595300067f7559530004ff745953003cfc74595300f4ff7359530006df7359530004ff7259530006ef7259530004ef725953000cfe725953000cfc7259530006ec725953000cec7259530004ff715953001cfc7159530114ff7059530006fb7059530104fe76195300467e65195300067d6519530005be7419530005bd741953003cfe76d9130044fe75d9130004fd75d9130024ff73d9130014fe73d9130024fd73d9130014fc73d91300c6bf43d91300c6bd43d913000cfe72d9130004fd72d913000cfc72d913001cfe71d9130004fd71d91300057e75991300057d7599130006bf649913008dee7299130005ed72991300b5f970991300d5fb7059130004ff7559130044fc7559130006bf74591300b4ff7359130006df7359130004ff725913000cfe725913000cfc7259130004ff715913001cfc71591300d4ff7059130006fb70591300c4fe761913003ebe6419130006bd6419130044ff76d5130004fe76d5130004fd76d5130044fc76d51300067f65d51300467c65d5130015de73d5130005dd73d513003cff7695130004fe7695130004fd769513003cfc769513003ebe6495130006bd64951300073f5495130004ff7655130004fe7655130004fd7655130004fc76551300067f65551300467c655513003ebe6455130006bd6455130005f77155130005f47155130005fb7055130025f8705513003cff7615130004fe7615130004fd761513003cfc7615130015de7315130005dd7315130025dc7654d30046dc7654d30024dc7654d30015df7554d300175f7554d300075f6554d30046de6554d30046dc6554d300075c6554d300075f5454d300075d5454d30007db7054d30025de7054d30025dc7054d30007d87054d30016df6054d30017db6054d3000cfe76d893008eee62d8930044fe75d8930004fd75d893003cfe74d8930004fd74d8930024fd73d893000cfc73d893008eec52d893008eee42d893008eee32d8930086ed32d893001cfe71d8930004fd71d893008eec21d8930014fd70d893008eef20d89300057f75589300057c755893008eec62589302f5fb7058930004fe76d4930
  | 16 => 0x8440006f56148440025f976d40402fef976d4040025fa75d40400277a75d4040026fb65d40402fef965d4040265fb74d4040265f974d4040266fa64d4040027ba64d4040006f961d4040007ba41d4040267b841d40400267f7559630004ff745963003cfc74596300f67f53596300f67d5359630004ff725963000cfe725963000cfc7259630004ff715963001cfc7159630024fe7059630024fc70596300267e50596300267c5059630026df3059630026dd3059630004ff7559230044fc7559230026bf74592300b6bf43592300b6bd4359230004ff725923000cfe725923000cfc7259230004ff715923001cfc7159230024fe7059230024fc7059230026be4059230026bc4059230026fa1059230044ff76d5230024fe76d5230004fd76d5230024fc76d52302be7f65d52300467c65d523003cff7695230024fe7695230004fd7695230024fc769523003ebe6495230006bd64952300073f5495230004ff7655230024fe7655230004fd7655230024fc76552302b67f65552300467c655523003ebe6455230006bd6455230005f77155230005f47155230005fb7055230025f8705523003cff7615230024fe7615230004fd7615230024fc7615230004ff7558a30044fc7558a30004ff7458a3003cfc7458a30026ef7258a30096ee5258a30096ec4258a30096ee3258a3007eed3258a30004ff7158a3001cfc7158a30096ef2158a30024fe7058a30024fc7058a30026ee2058a30026ec2058a30026fa1058a30044ff76d4a30024fe76d4a30004fd76d4a300976e52d4a30004ff7654a30004fd7654a30024fc7654a30005df7354a30015dc7354a3000eee6254a30006ed6254a3003cff76d0a30024fe76d0a30004fd76d0a30015de73d0a30005dd73d0a3000eee62d0a30006ed62d0a30004ff7650a30004fd7650a30024fc7650a30004ff7558630044fc7558630004ff745863003cfc7458630004ff725863000cfe725863000cfc7258630026f77158630056f63158630056f53158630024fc7058630026fa2058630026f61058630026f41058630044ff76d4630024fe76d4630004fd76d4630005be74d4630005bd74d463001cff7694630024fe7694630004fd769463001ef66194630006f56194630025fa7094630005f97094630004ff7654630004fd7654630024fc765463001ef66154630006f5615463001cff7614630024fe7614630004fd7614630025fa7014630005f9701463003cff76d0630024fe76d0630004fd76d063001ef661d0630006f561d063001cff7690630024fe7690630004fd7690630025fa7090630005f97090630004ff7650630004fd7650630024fc765063001cff7610630024fe7610630004fd76106300057e75106300057d7510630015de7310630005dd7310630095ee7210630005ed721063001ef
  | 17 => 0x24fc7059440026f87059440024f870594400267e50594400267c5059440026f85059440026bf4059440026bd4059440004ff7558c40044fc7558c40014fd7458c40024ff7358c40026df7358c400a6de5358c4003edf4358c4003edc4358c40004ff7258c4000cfe7258c4000cfc7258c400a6df3258c40004ff7158c4001cfc7158c400a6df3158c40024fc7058c40026de3058c40026dc3058c40044ff76d4c40024fe76d4c40004fd76d4c400467e65d4c400067d65d4c400a75e53d4c40004ff7654c40004fd7654c40024fc7654c400467e6554c400067d6554c40016de6354c40006dd6354c40005fb7054c40025f87054c40004ff7558840044fc755884000cfd7458840004ff7358840014fe7358840014fc7358840024ff7258840026ef725884009eee525884003eef425884003eec425884009eee3258840004ff715884001cfc715884009eef2158840024fc7058840026ee2058840026ec2058840044ff76d4840024fe76d4840004fd76d48400467e65d48400067d65d484009f6e52d4840004ff7654840004fd7654840024fc76548400467e65548400067d655484000eee6254840006ed6254840005fb7054840025f87054840004ff764c840004fd764c840024fc764c840016de634c840006dd634c84000eee624c840006ed624c84009fcc324c840004ff7558440044fc7558440004ff7358440014fe7358440014fc7358440004ff725844000cfe725844000cfc7258440026f7715844003ef7415844003ebc415844003ef44158440026f85058440026fa405844003ef94058440026f61058440026f41058440044ff76d4440024fe76d4440004fd76d44400467e65d44400067d65d444003dbe74d4440005bd74d4440307b441d444001cff7694440024fe7694440004fd769444001ef66194440006f56194440025fa7094440005f97094440287785094440004ff7654440004fd7654440024fc76544400467e65544400067d6554440005bf745444003dbc745444001ef66154440006f56154440005fb7054440025f8705444001cff7614440024fe7614440004fd761444028fb4411444029f78501444003dbd769044028ebd769044003ebf6590440006bd659044003dbe719044003fb6719044003ebf619044028ebd6190440295bf7090440295bd7090440296be609044003fba6090440297b8509044001cff768c440024fe768c440004fd768c44001ef6618c440006f5618c440004ff764c440004fd764c440024fc764c440005bf744c44003dbc744c440016de634c440006dd634c44001ef6614c440006f5614c44001cff7688440024fe7688440004fd768844001ef66188440006f56188440004ff7648440004fd7648440024fc7648440005bf744844003dbc744844000eee6248440006ed624844001ef6614
  | 18 => 0xe75d8d40004fd75d8d40024fd74d8d40014fc74d8d40006be54d8d40006bd54d8d400b6de43d8d4000cfe72d8d40004fd72d8d4000cfc72d8d4001cfe71d8d40004fd71d8d4003cfd70d8d400b6df30d8d400b6dc6358d40004fe76d4d40004fd76d4d40044fc76d4d4003dbe74d4d40005bd74d4d400073d54d4d400b75e53d4d40004ff7654d40004fe7654d40004fc7654d400073d5454d40024fc7650d40006df6350d40016dc6350d40005fb7050d40025f87050d4000cfe76d89400aeee62d8940044fe75d8940004fd75d8940024fd74d894000cfc74d8940006be54d8940006bd54d8940014fe73d8940004fd73d8940014fc73d89400aeee42d894001cfe71d8940004fd71d894003cfd70d89400aeef20d89400aeec6258940004fe76d4940004fd76d4940044fc76d494003dbe74d4940005bd74d49400073d54d49400af6e52d4940004ff7654940004fe7654940004fc76549400073d5454940024fc7650940006ef625094000eec6250940005fb7050940025f87050940004ff764c940004fe764c940004fc764c9400afcc324c940044fe75d8540004fd75d8540014fe73d8540004fd73d8540014fc73d854000cfe72d8540004fd72d854000cfc72d8540296bf6498540006f761985400057f75585400057c755854026ebf641854001ef66118540006f56118540004fe76d4540004fd76d4540044fc76d454003dbe74d4540005bd74d45400073d54d4540006f761d454001ef461d4540004fe7694540004fd769454001cfc76945400067f65945400467c6594540025fa7094540005f97094540004ff7654540004fe7654540004fc76545400073d5454540004fe7614540004fd761454001cfc76145400067f65145400467c651454003dbe7414540005bd7414540006f7611454001ef46114540025fa7014540005f97014540024fe7690540006f7619054001ef46190540025fa7090540005f97090540024fc7650540006f7615054001ef46150540005fb7050540025f87050540004fe768c540004fd768c54001cfc768c540025fa708c540005f9708c540004ff764c540004fe764c540004fc764c540004fe7688540004fd768854001cfc7688540025fa7088540005f97088540004ff7648540004fe7648540004fc764854003cfe76d414003cfc76d41400067f65d41400467c65d414003dbe74d4140005bd74d41400277a50d4140044ff7654140004fd765414003cfc76541400067f65541400467c6554140005bf745414003dbc7454140024ff75594400267f755944003cff745944003cfe745944003cfd745944003cfc745944003e7e545944003e7c5459440004ff7359440014fe7359440014fc7359440004ff725944000cfe725944000cfc7259440004ff715944001cfc715944003ebc4159440024fe7059440
  | 19 => 0x464001ef66154640006f5615464001cff7614640024fe7614640004fd761464001ef66114640006f56114640025fa7014640005f9701464001ef66190640006f56190640025fa7090640005f97090640296bf6590640006bd659064003dbe7190640296bf6190640297b6619064024ebd6190640297b56190640297ba7090640295bd709064024fb9709064003ebe6090640297ba109064001cff765064001ef66150640006f5615064003fb44150640005fb7050640025f8705064026dbd761064003ebd761064003f3e751064003f3d751064026ebf6510640006bd651064003f9e731064003f9d731064003fae721064003fad721064003fb6711064026ebf611064026fb6611064024ebd611064026fb56110640006b56110640007b7511064024fb4511064003dbf701064003fba701064026dbd701064003fb97010640005b9701064003fba601064026fb7101064026fba101064001cff768c640024fe768c640004fd768c64001ef6618c640006f5618c640025fa708c640005f9708c640004ff764c640004fd764c640024fc764c640005bf744c64003dbc744c64001ef6614c640006f5614c64001cff7688640024fe7688640004fd768864001ef66188640006f56188640025fa7088640005f97088640004ff7648640004fd7648640024fc7648640005bf744864003dbc744864001ef66148640006f56148640044fe76d954003cfe74d954003cfc74d9540014fe73d9540004fd73d9540014fc73d954000cfe72d9540004fd72d954000cfc72d954001cfe71d9540004fd71d95400067f6599540266fb6099540005f77159540005f471595400067f7559540004ff7459540006bf7459540004ff7359540014fe7359540014fc7359540004ff725954000cfe725954000cfc7259540004ff7159540006f77159540004f7715954001cfc7159540006f4715954001cf47159540004ff7059540006fb7059540004fb70595402b67e50595402b67c5059540004fe76195400467e65195400067d651954025efb6019540024fe76d5140024fc76d51400067f65d51400467c65d514003f3e54d5140025fa70d5140005f970d5140005be769514003ebe7695140005bd7595140046be6595140046bc65951402d6bc6195140025be7095140025bc709514003ebf609514003fbb6095140024fc76551400067f65551400467c6555140005f77155140005f47155140005fb7055140025f87055140025bc7655140046bc7655140024bc765514003dbf755514003f3f75551400073f6555140046be6555140046bc65551400073c6555140007b77155140007b471551402cebc6155140007bb7055140025be7055140025bc7055140007b8705514003ebf605514003fbb60551402b73e50551402b73c5055140014fe76d8d400b6de63d8d40044f
  | 20 => 0x26fa1058a40044ff76d4a40024fe76d4a40004fd76d4a400bf6e52d4a40004ff7654a40004fd7654a40024fc7654a4000eee6254a40006ed6254a4000cff7650a4000eee6250a40006ed6250a40005fb7050a40025f87050a40004ff764ca40004fd764ca40024fc764ca400bfcc324ca4001ef7759864001ef6759864001ef5759864001ef4759864001ef7749864001ef6749864001ef47498640006f754986402c6f65498640006f554986402c6f4549864001ef7739864001ef6739864001ef5739864001ef47398640006f75398640006f65398640006f55398640006f453986402c6f74398640006f64398640006f543986402c6f4439864001ef7729864001ef6729864001ef5729864001ef47298640006f75298640006f65298640006f55298640006f452986402c6f74298640006f64298640006f542986402c6f44298640006f73298640006f63298640006f53298640006f43298640026f77098640026f67098640026f27098640026f57098640026f47098640026f75098640026f65098640026f55098640026f45098640026f74098640026f64098640026f54098640026f44098640026f73098640026f63098640026f53098640026f43098640026f72098640026f62098640026f52098640026f42098640004ff7558640044fc7558640004ff7358640014fe7358640014fc7358640004ff725864000cfe725864000cfc7258640026f77158640006f73158640006f43158640006f72158640006f42158640024fc7058640026f61058640026f41058640006f77558640006f67558640006f57558640006f47558640006f57458640246f47458640006f75458640246f65458640006f55458640246f45458640006f77358640006f67358640006f57358640006f47358640006f75358640006f65358640006f55358640006f45358640246f74358640006f64358640006f54358640246f44358640006f77258640006f67258640006f57258640006f47258640006f75258640006f65258640006f55258640006f45258640246f74258640006f64258640006f54258640246f44258640006f73258640006f63258640006f53258640006f43258640026f77058640026f67058640026f47058640026f75058640026f65058640026f55058640026f45058640026f74058640026f64058640026f54058640026f44058640026f73058640026f63058640026f53058640026f43058640026f72058640026f62058640026f52058640026f42058640044ff76d4640024fe76d4640004fd76d464003dbe74d4640005bd74d464001ef661d4640006f561d464001cff7694640024fe7694640004fd769464001ef66194640006f56194640025fa7094640005f97094640004ff7654640004fd7654640024fc7654640005bf745464003dbc745
  | 21 => 0x97094740004ff7654740004fd765474003cfc76547400467e65547400067d65547400073d5454740005fb7054740025f8705474001cff761474003cfe7614740004fd76147400467e65147400067d651474003dbe7414740005bd741474001cff768c74003cfe768c740004fd768c7400067e658c7400067d658c740004ff764c740004fd764c74003cfc764c7400067e654c7400067d654c740016de634c740006dd634c74001cff768874003cfe7688740004fd76887400067e65887400067d6588740004ff7648740004fd764874003cfc76487400067e65487400067d654874000eee6248740006ed62487400467e65d43400067d65d434003dbe74d4340005bd74d4340265f976d434030ef976d4340025fa75d4340266fb65d43402677a65d434030ef965d43402677965d43400067965d4340267ba74d4340265f974d434030fb974d4340005b974d4340026fa64d4340267ba54d434030fb954d4340006f961d4340044ff76543400467e65543400067d6554340005bf745434003dbc7454340027785054340027ba405434025df97614340026f976143400277a751434025efb651434025f7a651434030ef9651434025f796514340006796514340025fb7414340027ba741434025df97414340027b97414340005b97414340027ba641434025f7b541434025fba541434025f79541434030fb95414340007395414340027da7314340027d97314340027ea7214340027e97214340027f27114340027f17114340006f961143400077a511434030f7851143400267f7559640004ff7359640014fe7359640014fc7359640004ff725964000cfe725964000cfc7259640004ff715964001cfc7159640024fc70596400267e50596400267c5059640026bf4059640026bd405964003efb4059240026be4059240026bc4059240026f840592400467e65d52400067d65d524003f3e54d5240025fa70d5240005f970d5240044ff76552400467e65552400067d6555240005f77155240005f47155240005fb7055240025f8705524003fbb4055240004ff7558e40044fc7558e40026df7358e400c6de5358e400c6de4358e40004ff7258e4000cfe7258e4000cfc7258e40006de3258e400c6dc3258e40004ff7158e4001cfc7158e40024fc7058e40026de3058e40026dc3058e40026fa1058e40044ff76d4e40024fe76d4e40004fd76d4e400c75e53d4e40004ff7654e40004fd7654e40024fc7654e40016de6354e40006dd6354e40014ff7650e40016de6350e40006dd6350e40005fb7050e40025f87050e40004ff7558a40044fc7558a40004ff7358a40014fe7358a40014fc7358a40026ef7258a400beee5258a400beee4258a40006ef3258a400beec3258a40004ff7158a4001cfc7158a40024fc7058a40026ee2058a40026ec2058a40
  | 22 => 0x974003e7d745974003e7c74597400067f73597400067e73597400067d73597400067c735974003e7f435974003e7e435974003e7d435974003e7c43597400067f72597400067e72597400067d72597400067c725974003e7f425974003e7e425974003e7d425974003e7c42597400067f32597400067e32597400067c32597400067f71597400067e71597400067d71597400067c715974003e7f415974003e7e415974003e7d415974003e7c41597400067f31597400067c31597400067f21597400067c21597400067f70597400067b70597402b67e70597400067d70597402b67c705974003e7f405974003e7e405974003e7d405974003e7c40597400067f30597402b67e30597402b67c30597400067f20597402b67e20597402b67c20597402b67e10597402b67c105974003dbf7655340006bf765534003f3f7555340046be655534003f3e65553400463e655534003f3d655534003ebc6555340007b77155340007b471553402cebe6155340007bb7055340025be7055340025bc7055340007b87055340025b870553402b73e50553402b73c5055340004ff7558f40044fc7558f40024fc7458f4003ebe5458f40006bd5458f4003edf7358f4003edf4358f4003edc4358f40004ff7258f4000cfe7258f4000cfc7258f40006de3258f400d6dc3258f40004ff7158f4001cfc7158f400d6df3158f400d6df3058f40044ff76d4f4003cfe76d4f40004fd76d4f400467e65d4f400067d65d4f4003dbe74d4f40005bd74d4f400073d54d4f400d75e53d4f40004ff7654f40004fd7654f4003cfc7654f400467e6554f400067d6554f400073d5454f40005fb7054f40025f87054f40004ff7558b40044fc7558b40024fc7458b4003ebe5458b40006bd5458b40004ff7358b40014fe7358b40014fc7358b4003eef7258b4003eef4258b4003eec4258b40006ef3258b400ceec3258b40004ff7158b4001cfc7158b400ceef2158b400ceef2058b40044ff76d4b4003cfe76d4b40004fd76d4b400467e65d4b400067d65d4b4003dbe74d4b40005bd74d4b400073d54d4b400cf6e52d4b40004ff7654b40004fd7654b4003cfc7654b400467e6554b400067d6554b400073d5454b40005fb7054b40025f87054b40004ff764cb40004fd764cb4003cfc764cb400067e654cb400067d654cb400cfcc324cb40004ff7558740044fc7558740024fc7458740004ff7358740014fe7358740014fc7358740004ff725874000cfe725874000cfc725874003ef7715874003ef7415874003ef4415874003efa405874003ef94058740044ff76d474003cfe76d4740004fd76d47400467e65d47400067d65d474003dbe74d4740005bd74d47400073d54d474001cff769474003cfe7694740004fd76947400467e65947400067d6594740025fa7094740005f
  | 23 => 0x3ebe6490450006bd64904500073d5490450166de6390450006dd639045015eee6290450006ed629045001ef66190450006f56190450025fa7090450005f97090450004ff7650450004fd7650450024fc76504500057f75504500457c755045003ebe6450450006bd6450450156de6350450006dd635045014eee6250450006ed625045001ef66150450006f56150450005fb7050450025f8705045001cff7610450024fe7610450004fd76104500457e75104500057d751045003ebe6410450006bd64104500073d54104500e5de7310450005dd7310450146de6310450006dd63104500ddee7210450005ed721045013eee6210450006ed621045001ef66110450006f56110450257745110450025fa7010450005f9701045026fb8401045001cff768c450024fe768c450004fd768c450006be648c450006bd648c450016de638c450006dd638c450136ee628c450006ed628c45001ef6618c450006f5618c450025fa708c450005f9708c450004ff764c450004fd764c450024fc764c4500057f754c4500457c754c450006be644c450006bd644c450016de634c450006dd634c45012eee624c450006ed624c45001ef6614c450006f5614c45001cff7688450024fe7688450004fd7688450006be6488450006bd6488450126de6388450006dd638845000eee6288450006ed628845001ef66188450006f56188450025fa7088450005f97088450004ff7648450004fd7648450024fc76484500057f75484500457c7548450006be6448450006bd644845011ede6348450006dd634845000eee6248450006ed624845001ef66148450006f5614845003e7f749974003e7e749974003e3e749974003e7d749974003e7c74997400467f73997400467e73997400467d73997400467c739974003e7f439974003e7e439974003e7d439974003e7c43997400467f72997400467e72997400467d72997400467c729974003e7f429974003e7e429974003e7d429974003e7c42997400067f32997400067e32997400067c32997400467f71997400467e71997400467d71997400467c719974003e7f419974003e7e419974003e7d419974003e7c41997400067f31997400067c31997400067f21997400067c21997400467f70997400467e70997400467d70997400467c709974003e7f409974003e7e409974003e7d409974003e7c40997400067f30997402be7e30997402be7c30997400067f20997402be7e20997402be7c20997402be7e10997402be7c109974003e7f7559740024fc745974003e7e545974003e7c5459740004ff7359740014fe7359740014fc73597400067e53597400067c5359740004ff725974000cfe725974000cfc72597400067e52597400067c5259740004ff715974001cfc7159740006fb705974003e7f745974003e7e745
  | 24 => 0x47398450046f75398450046f65398450046f55398450046f45398450006f74398450006f64398450006f54398450006f4439845001ef7729845001ef6729845001ef5729845001ef47298450046f75298450046f65298450046f55298450046f45298450006f74298450006f64298450006f54298450006f44298450006f73298450006f63298450006f53298450006f43298450026f77098450026f67098450026f27098450026f57098450026f47098450026f75098450026f65098450026f55098450026f45098450026f74098450026f64098450026f54098450026f44098450026f73098450026f63098450026f53098450026f43098450026f72098450026f62098450026f52098450026f42098450004ff745845003cfc74584500467f54584500067d5458450004ff7358450014fe7358450014fc7358450004ff725845000cfe725845000cfc7258450026f77158450046f751584500467c5158450046f45158450006f73158450006f43158450006f72158450006f42158450026f61058450026f41058450046f77558450046f67558450046f47558450006f77458450006f67458450006f57458450006f47458450046f75458450046775458450046f65458450046f55458450006755458450046f45458450006f77358450006f67358450006f57358450006f47358450046f75358450046f65358450046f55358450046f45358450006f74358450006f64358450006f54358450006f44358450006f77258450006f67258450006f57258450006f47258450046f75258450046f65258450046f55258450046f45258450006f74258450006f64258450006f54258450006f44258450006f73258450006f63258450006f53258450006f43258450026f77058450026f67058450026f47058450026f75058450026f65058450026f55058450026f45058450026f74058450026f64058450026f54058450026f44058450026f73058450026f63058450026f53058450026f43058450026f72058450026f62058450026f52058450026f420584500457d76944502567d76944500057d74944500473e64944500473d64944500475e63944500475d63944500476e62944500476d62944500457e71944500477671944500467f61944500477661944502567d61944500477561944500067561944502857f70944502877a70944502857d70944502577970944500057970944502867e60944500477a60944502877710944502877a109445003cff76d0450024fe76d0450004fd76d04500457e75d04500057d75d045003ebe64d0450006bd64d0450176de63d0450006dd63d045016eee62d0450006ed62d045001ef661d0450006f561d045027f7451d0450025f870d045001cff7690450024fe7690450004fd76904502557f75904500457c7590450
  | 25 => 0x8c50026dd5058c50026dc5058c50026df4058c50026de4058c50026dd4058c50026dc4058c50026df2058c50026de2058c50026dd2058c50026dc2058c50026df1058c50026de1058c50026da1058c50026dd1058c50026dc1058c5003cff76d0c50024fe76d0c50004fd76d0c500457e75d0c500057d75d0c5003ebe64d0c50006bd64d0c500073d54d0c50016de63d0c50006dd63d0c501e6ee62d0c50004ff7650c50004fd7650c50024fc7650c5003ebe6450c50006bd6450c500073d5450c50016de6350c50006dd6350c501deee6250c50005fb7050c50025f87050c5000cfd7558850004ff745885003cfc74588500467f54588500067d5458850004ff7358850014fe7358850014fc7358850024ff7258850026ef7258850046ef5258850046ec52588500deee42588500deec4258850006ef32588500deee32588500deec3258850004ff715885001cfc71588500deef21588500deec2158850024fc7058850026ee2058850026ec2058850026fa1058850046ef7558850046ee7558850046ec7558850006ef7458850006ee7458850006ed7458850006ec7458850046ef54588500466f5458850046ee5458850046ed54588500066d5458850046ec5458850006ef7358850006ee7358850006ed7358850006ec7358850046ef5358850046ee5358850046ed5358850046ec5358850006ef4358850006ee4358850006ed4358850006ec4358850006ef7158850006ee7158850006ed7158850006ec7158850046ef5158850046ee5158850046ed5158850046ec5158850006ef3158850006ec3158850026ef7058850026ee7058850026ec7058850026ef5058850026ee5058850026ed5058850026ec5058850026ef4058850026ee4058850026ed4058850026ec4058850026ef3058850026ee3058850026ed3058850026ec3058850026ef1058850026ee1058850026ea1058850026ed1058850026ec105885003cff76d0850024fe76d0850004fd76d08500457e75d08500057d75d085003ebe64d0850006bd64d08500073d54d08501c6de63d0850006dd63d085000eee62d0850006ed62d0850004ff7650850004fd7650850024fc765085003ebe6450850006bd64508500073d54508501bede6350850006dd635085000eee6250850006ed6250850005fb7050850025f87050850004ff764c850004fd764c850024fc764c8500057f754c8500457c754c850006be644c850006bd644c850016de634c850006dd634c85000eee624c850006ed624c8500dfcc324c850005fb704c850025f8704c85001ef7759845001ef6759845001ef5759845001ef4759845001ef7749845001ef6749845001ef5749845001ef47498450046f75498450046f65498450046f55498450046f4549845001ef7739845001ef6739845001ef5739845001ef
  | 26 => 0x26be2099050026bd2099050026bc2099050026bf1099050026be1099050026bd1099050026bc1099050026bf7459050046bf5459050046bc5459050004ff7359050014fe7359050014fc7359050006be4359050006bc4359050004ff725905000cfe725905000cfc7259050006be4259050006bc4259050004ff715905001cfc7159050026f87059050026be4059050026bc4059050026f84059050026fa1059050046bf7559050046be7559050046bc7559050006bf7359050006be7359050006bd7359050006bc7359050046bf5359050046be5359050046bd5359050046bc5359050006bf7259050006be7259050006bd7259050006bc7259050046bf5259050046be5259050046bd5259050046bc5259050006bf3259050006be3259050006bc3259050006bf7159050006be7159050006bd7159050006bc7159050046bf5159050046be5159050046bd5159050046bc5159050006bf3159050006bc3159050006bf2159050006bc2159050026bf7059050026be7059050026bc7059050026b87059050026bf5059050026be5059050026bd5059050026bc5059050026bf3059050026be3059050026bd3059050026bc3059050026bf2059050026be2059050026bd2059050026bc2059050026bf1059050026be1059050026ba1059050026bd1059050026bc10590500457f76550500067f76550500457f74550500473f745505003e7e64550500473e645505003e3e64550500473d645505003e7c64550500475e63550500475d63550500476e62550500476d62550500077771550502557c71550500077471550500057471550500477661550500477561550502b57f70550500077b70550500057b70550502b77870550502b67e60550500477a60550502b7784055050014fd7558c50004ff7458c5003cfc7458c500467f5458c500067d5458c50024ff7358c50026df7358c50046df5358c50046dc5358c500e6de4358c500e6dc4358c50004ff7258c5000cfe7258c5000cfc7258c500e6df3258c50006de3258c500e6dc3258c50004ff7158c5001cfc7158c500e6df3158c500e6dc3158c50024fc7058c50026de3058c50026dc3058c50026fa1058c50046df7558c50046de7558c50046dc7558c50006df7458c50006de7458c50006dd7458c50006dc7458c50046df5458c500465f5458c50046de5458c50046dd5458c500065d5458c50046dc5458c50006df7258c50006de7258c50006dd7258c50006dc7258c50046df5258c50046de5258c50046dd5258c50046dc5258c50006de4258c50006dc4258c50006df7158c50006de7158c50006dd7158c50006dc7158c50046df5158c50046de5158c50046dd5158c50046dc5158c50006df2158c50006dc2158c50026df7058c50026de7058c50026dc7058c50026df5058c50026de505
  | 27 => 0xc72d8d50006de32d8d500f6dc32d8d5001cfe71d8d50004fd71d8d50044fd70d8d500f6df30d8d500f6dc6358d50005ef7258d500edec7258d50024fc7654d50006df6354d50016dc6354d50005fb7054d50025f87054d50004fe76d0d50004fd76d0d5003cfc76d0d50004ff7650d50004fe7650d50004fc7650d5000cfe76d89500eeee62d8950024fd75d895000cfc75d895003cfe74d8950004fd74d8950014fe73d8950004fd73d8950014fc73d89500eeee52d8950006ef32d89500eeec32d895001cfe71d8950004fd71d8950044fd70d89500eeef20d8950005df73589500f5dc73589500eeec6258950024fc7654950006ef625495000eec6254950005fb7054950025f87054950004fe76d0950004fd76d095003cfc76d0950004ff7650950004fe7650950004fc7650950004ff764c950004fe764c950004fc764c9500efcc324c95003cfe74d8550004fd74d8550014fe73d8550004fd73d8550014fc73d855000cfe72d8550004fd72d855000cfc72d85502aefb50d85502aef850d85502867f6598550006f76198550005bf7458550005bc745855029e7f651855001ef66118550006f56118550024fe7694550006f7619455001ef46194550025fa7094550005f97094550024fc7654550006f7615455001ef46154550005fb7054550025f87054550047785054550004fe76d0550004fd76d055003cfc76d0550006f761d055001ef461d0550004fe7690550004fd769055001cfc7690550006bf649055003ebc6490550004ff7650550004fe7650550004fc7650550004fe7610550004fd761055001cfc76105500457e75105500057d7510550006bf641055003ebc64105500f5de7310550005dd73105500edee7210550005ed7210550006f7611055001ef46110550025fa7010550005f97010550004fe768c550004fd768c55001cfc768c550004ff764c550004fe764c550004fc764c550004fe7688550004fd768855001cfc7688550004ff7648550004fe7648550004fc764855003ebf759905003ebe759905003ebd759905003ebc759905003ebf739905003ebe739905003ebd739905003ebc7399050046bf5399050046be5399050046bd5399050046bc539905003ebf729905003ebe729905003ebd729905003ebc7299050046bf5299050046be5299050046bd5299050046bc5299050006bf3299050006be3299050006bc329905003ebf719905003ebe719905003ebd719905003ebc7199050046bf5199050046be5199050046bd5199050046bc5199050006bf3199050006bc3199050006bf2199050006bc2199050026bf7099050026be7099050026bd7099050026bc7099050026bf5099050026be5099050026bd5099050026bc5099050026bf3099050026be3099050026bd3099050026bc3099050026bf2099050
  | 28 => 0x8a5000cff7654a5000eee6254a50006ed6254a50005fb7054a50025f87054a500477b5054a5003cff76d0a50024fe76d0a50004fd76d0a500457e75d0a500057d75d0a500073d54d0a50004ff7650a50004fd7650a50024fc7650a500073d5450a50004ff764ca50004fd764ca50024fc764ca500057f754ca500457c754ca500ffcc324ca50004ff7458650006bf7458650004bf745865003cfc7458650006bc745865003cbc74586500067f54586500067d5458650004ff7358650014fe7358650014fc7358650004ff725865000cfe725865000cfc7258650026f77158650024fc705865023efb5058650026f85058650026f61058650026f4105865001ef66194650006f56194650047775194650025fa7094650005f970946500057d74946500457e71946502867f61946502877661946502a67d61946502877561946502877a70946502857d70946502a77970946500467e609465028777109465001cff765465001ef66154650006f56154650005fb7054650025f8705465029d7d76146500467d76146500057d741465004776711465029e7f61146502a67d61146500457f701465029d7d70146500477a601465003cff76d0650024fe76d0650004fd76d06500457e75d06500057d75d065001ef661d0650006f561d06500077451d065001cff7690650024fe7690650004fd76906502a57f75906500457c75906500073d5490650004ff7650650004fd7650650024fc76506500057f75506500457c755065001cff7610650024fe7610650004fd76106500457e75106500057d751065003ebc64106500073d5410650105de7310650005dd73106500fdee7210650005ed721065001ef66110650006f561106502a7745110650025fa7010650005f9701065001cff768c650024fe768c650004fd768c65001ef6618c650006f5618c650004ff764c650004fd764c650024fc764c6500057f754c6500457c754c65001ef6614c650006f5614c65001cff7688650024fe7688650004fd768865001ef66188650006f56188650004ff7648650004fd7648650024fc76486500057f75486500457c754865001ef66148650006f56148650014fe73d9150004fd73d9150014fc73d915000cfe72d9150004fd72d915000cfc72d915001cfe71d9150004fd71d91502be7e50d91502be7c50d9150006bf6499150005f77159150005f4715915003ebe6419150006bd6419150266fb6019150024fe7695150006bf649515003ebc64951500473f5495150025fa7095150005f97095150047785095150024fc7655150006bf645515003ebc6455150005f77155150005f47155150005fb7055150025f87055150014fe76d8d500f6de63d8d50024fd75d8d50014fc75d8d5003cfe74d8d50004fd74d8d500f6de53d8d5000cfe72d8d50004fd72d8d5000cf
  | 29 => 0x3cff76d0b50044fe76d0b50004fd76d0b5003ebe64d0b50006bd64d0b50004ff7650b50004fd7650b50044fc7650b5003ebe6450b50006bd6450b50005fb7050b50025f87050b50004ff764cb50004fd764cb50044fc764cb5010fcc324cb50005fb704cb50025f8704cb50024fc7558750004ff745875003cfc7458750004ff7358750014fe7358750014fc7358750004ff725875000cfe725875000cfc7258750046f77158750046f75158750046f4515875003cff76d0750044fe76d0750004fd76d075001cff7690750044fe7690750004fd769075003ebe6490750006bd6490750025fa7090750005f97090750004ff7650750004fd7650750044fc7650750005fb7050750025f8705075001cff7610750044fe7610750004fd76107500457e75107500057d751075003ebe6410750006bd6410750115de7310750005dd731075010dee7210750005ed721075001ef46110750025fa7010750005f9701075001cff768c750044fe768c750004fd768c750025fa708c750005f9708c750004ff764c750004fd764c750044fc764c75001cff7688750044fe7688750004fd7688750025fa7088750005f97088750004ff7648750004fd7648750044fc7648750046fb50596500267e50596500267c5059650026f85059650026bf7459250004ff7359250014fe7359250014fc7359250004ff725925000cfe725925000cfc7259250004ff715925001cfc7159250024fc7059250026be4059250026bc40592502bd7d76d52500467d76d525003e7e64d525003e7c64d52502a57e71d52500457f70d52502bd7d70d52500477a60d525003ebe6495250006bd64952500473f5495250025fa7095250005f9709525003cff765525003ebe6455250006bd6455250005f77155250005f47155250005fb7055250025f870552500477b505525003c7f76552500457f74552500473f745525003e7e64552502b73e64552502b73d645525003e7c64552500077771552502a57c71552500077471552500057471552502b57f70552500077b70552502b77870552500467e6055250004ff7458e5003cfc7458e500067f5458e500067d5458e50026df7358e50106de5358e50004ff7258e5000cfe7258e5000cfc7258e50004ff7158e5001cfc7158e50024fc7058e50026de3058e50026dc3058e50014ff7654e50016de6354e50006dd6354e50005fb7054e50025f87054e500477b5054e5003cff76d0e50024fe76d0e50004fd76d0e500457e75d0e500057d75d0e500073d54d0e50004ff7650e50004fd7650e50024fc7650e500073d5450e50004ff7458a5003cfc7458a500067f5458a500067d5458a50004ff7358a50014fe7358a50014fc7358a50026ef7258a500feee5258a50004ff7158a5001cfc7158a50024fc7058a50026ee2058a50026ec205
  | 30 => 0xd72d0d21004ff7650d21004fe7650d21004fd7650d21004fc7650d2101dec765092103eec765092101cec765092100def745092100faf7450921007af645092103eee645092103eec6450921007ac6450921007ae5450921007ad5450921007af4350921007ad4350921007e7715092101dee715092101dec7150921007e4715092100eef615092100fe7615092100cfe76d452100cfc76d45210067f65d45210467c65d4521005be74d4521005bd74d452100dee72d4521005ed72d452101f7651d4521044ff765452100cfe765452118cfd765452100cfc76545210067f65545210467c6554521005ef725452100dec725452101fe4215452100cfe76d052100cfc76d0521006bf64d052103ebc64d052100dee72d0521005ed72d052103cff765052100cfe765052114cfd765052100cfc7650521006bf645052103ebc6450521005ef725052100dec7250521315f6768c52101ef6768c52112df5738c521016f6638c521016f4638c52100df6728c52101df4728c52101ef7628c52101fe7628c521137e6428c521007e5428c521005f5708c521014ff764c52100cfe764c52112cfd764c52100cfc764c521006df634c521016dc634c521005ef724c52100dec724c52100df4764c521016f4764c52100cf4764c52101df7734c52101fd7734c521007d7634c521016f6634c521016f4634c52111fd4634c52111fd6434c521007d5434c521007e7724c52100df6724c52100df4724c52112fe4724c52101ef7624c52101fe7624c52112fe6424c521007e5424c521005f7704c521044fe75d8121004fd75d812103cfe74d8121004fd74d8121014fe73d8121004fd73d8121014fc73d812101cfd72d8121006f631d8121006f531d812106efa20d8121006fb60981210057f75581210057c7558121005bf7458121005bc7458121005df735812111ddc7358121026fa6018121006f96018121024fc7559350046bf7459350046bf5459350046bc5459350004ff7359350014fe7359350014fc7359350004ff725935000cfe725935000cfc7259350004ff7159350006f77159350004f7715935001cfc7159350006f4715935001cf47159350006fb70593502b67e50593500467c5059350024fc7558f50004ff7458f5003cfc7458f50046df7358f50046df5358f50046dc5358f50004ff7258f5000cfe7258f5000cfc7258f50004ff7158f5001cfc7158f50116df3058f5003cff76d0f50044fe76d0f50004fd76d0f5003ebe64d0f50006bd64d0f50004ff7650f50004fd7650f50044fc7650f5003ebe6450f50006bd6450f50005fb7050f50025f87050f50024fc7558b50004ff7458b5003cfc7458b50004ff7358b50014fe7358b50014fc7358b50046ef7258b50046ef5258b50046ec5258b50004ff7158b5001cfc7158b5010eef2058b50
  | 31 => 0x822101ef63158221006f5315822101efb705822104efa205822101efb105822101ef81058221044fe76d952103cfe74d9521004fd74d9521014fe73d9521004fd73d9521014fc73d952101cff72d952101cfd72d952119e7f52d952119e7d52d9521024fe70d9521004fd70d95210067f6599521005be7499521005bd749952111dde7399521005dd739952118df571995211adf771595210067f7559521004ff745952103cfc7459521004ff7359521014fe7359521014fc735952118cff7259521006ef72595211acff7159521006f77159521004ff7059521024fc705952119cfe76195210467e65195210067d651952103cfe76d9121044fe75d9121004fd75d9121014fe73d9121004fd73d9121014fc73d9121006be43d9121006bc43d912101cff72d912101cfd72d912115ebf42d912115ebd42d9121024fe70d9121004fd70d9121006bf649912114df57199121005df735912111ddc735912116df77159121004ff7559121044fc7559121006bf7459121004ff7359121006df7359121004df7359121014fe7359121014fc7359121006dc7359121014dc735912114cff7259121006ef725912116cff7159121006f77159121004ff7059121024fc705912115cfe76191210057e75191210057d751912103ebe6419121006bd6419121044ff76d5121004fe76d5121004fd76d5121044fc76d51210467e65d51210067d65d512103cff7695121004fe7695121004fd769512103cfc7695121006bf649512103ebc64951210073f549512100dee7295121005ed7295121004ff7655121004fe7655121004fd7655121004fc76551210467e65551210067d6555121006bf645512103ebc6455121005f7715512101df47155121005fb7055121005f8705512103cff7615121004fe7615121004fd761512103cfc761512100dee7215121005ed7215121014fe76d8d2111ede63d8d21044fe75d8d21004fd75d8d2103cfe74d8d21004fd74d8d2111ede53d8d2111edc43d8d2101cff72d8d2101cfd72d8d21136df32d8d21136dd32d8d2100cfd71d8d2111edf31d8d21024fe70d8d21004fd70d8d2111edc30d8d21005bf7458d21005bc7458d2111edc6358d2131df77158d21004ff7558d21044fc7558d21004ff7458d21006bf7458d21004bf7458d2103cfc7458d21006bc7458d2103cbc7458d21134ff7358d21006df7358d2112cff7258d21006ef7258d2131cff7158d21006f77158d21004ff7058d21024fc7058d21044ff76d4d21004fe76d4d21004fd76d4d21044fc76d4d2111f5e53d4d21004ff7654d21004fe7654d21004fd7654d21004fc7654d21006df6354d21016dc6354d21005ef7254d2100dec7254d2103cff76d0d21004fe76d0d21004fd76d0d2103cfc76d0d21006df63d0d21016dc63d0d2100dee72d0d21005e
  | 32 => 0x79d4350931014fe76d4531014fc76d45310067f65d45310467c65d4531005be74d4531005bd74d4531015de73d4531005dd73d453101f7651d4531044ff7654531014fe7654531194fd7654531014fc76545310067f65545310467c6554531005df7354531015dc735453101fd43154531014fe76d0531014fc76d0531006bf64d053103ebc64d0531015de73d0531005dd73d053103cff7650531014fe7650531154fd7650531014fc7650531006bf645053103ebc6450531005df7350531015dc7350531044fe75d8131004fd75d813103cfe74d8131004fd74d813101cfd73d813100cfe72d8131004fd72d813100cfc72d8131076fa30d8131006fb60981310057f75581310057c7558131005bf7458131005bc7458131005ef725813112dec7258131026fa6018131006f9601813101e7f7559621004ff745962103cfc7459621004ff7359621014fe7359621014fc735962118e7f525962118e7d525962101cfe715962101cfc715962101e7e515962101e7c5159621004ff7059621024fc705962101ef71059621004ff7559221044fc755922101ebf7459221004ff7359221014fe7359221014fc735922114ebf425922114ebd425922101cfe715922101cfc715922101ebe415922101ebc415922101eef215922101eed2159221004ff7059221024fc7059221044ff76d522101cfe76d5221004fd76d522101cfc76d52210467e65d52210067d65d522103cff769522101cfe7695221004fd769522101cfc76952212d6bf649522103ebc64952210073f5495221004ff765522101cfe7655221004fd765522101cfc76552210467e65552210067d65552212cebf645522103ebc6455221005f7715522101df47155221005fb7055221005f8705522103cff761522101cfe7615221004fd761522101cfc7615221004ff7558e21044fc7558e21004ff7458e2103cfc7458e2101edf7358e21126dc5358e21126de4358e2112edf3258e2112edd3258e2101cfe7158e2101cfc7158e2101ede3158e2101edc3158e21004ff7058e21024fc7058e21126df3058e2101ef71058e21044ff76d4e2101cfe76d4e21004fd76d4e2101cfc76d4e21016de63d4e21006dd63d4e211275e53d4e2100dee72d4e21005ed72d4e21004ff7654e2101cfe7654e21004fd7654e2101cfc7654e2103cff76d0e2101cfe76d0e21004fd76d0e2101cfc76d0e21004ff7650e2101cfe7650e21004fd7650e2101cfc7650e21016de6350e21006dd6350e21005ef7250e2100dec7250e2101df7764c621326f7764c62101fd7734c621016f6634c62101ef4634c621127d6434c621007d5434c62100df6724c62100df4724c621005f7704c621004ff7558221044fc7558221004ff745822103cfc7458221004ff7358221014fe7358221014fc735822101cfc715
  | 33 => 0x6215823101efb7058231056fa305823101efb105823101ef81058231044fe76d953103cfe74d9531004fd74d953101cff73d953101cfd73d95311a67f53d95311a67d53d953100cfe72d9531004fd72d953100cfc72d9531024fe70d9531004fd70d95310067f6599531005be7499531005bd749953112dee7299531005ed7299531195f571995311b5f771595310067f7559531004ff745953103cfc7459531194ff7359531006df7359531004ff725953100cfe725953100cfc72595311b4ff7159531006f77159531004ff7059531024fc70595311a4fe76195310467e65195310067d651953103cfe76d9131044fe75d9131004fd75d913101cff73d913101cfd73d9131166bf43d9131166bd43d913100cfe72d9131004fd72d913100cfc72d9131006be42d9131006bc42d9131024fe70d9131004fd70d9131006bf6499131155f57199131005ef725913112dec7259131175f77159131004ff7559131044fc7559131006bf7459131154ff7359131006df7359131004ff7259131006ef7259131004ef725913100cfe725913100cfc7259131006ec725913100cec7259131174ff7159131006f77159131004ff7059131024fc7059131164fe76191310057e75191310057d751913103ebe6419131006bd6419131044ff76d5131004fe76d5131004fd76d5131044fc76d51310467e65d51310067d65d513103cff7695131004fe7695131004fd769513103cfc7695131006bf649513103ebc64951310073f5495131015de7395131005dd7395131004ff7655131004fe7655131004fd7655131004fc76551310467e65551310067d6555131006bf645513103ebc6455131005f7715513101df47155131005fb7055131005f8705513103cff7615131004fe7615131004fd761513103cfc7615131015de7315131005dd731513101ddc7650d3103edc7650d3101cdc7650d31015df7450d310179f7450d310079f6450d3103ede6450d3103edc6450d310079c6450d310079e5450d310079d5450d31007d77150d3101dde7150d3101ddc7150d31007d47150d31016df6150d31017d76150d3100cfe76d893112eee62d8931044fe75d8931004fd75d893103cfe74d8931004fd74d893101cfd73d893112eee52d893112eec42d893112eee32d8931126ed32d8931014fd71d893112eef21d8931024fe70d8931004fd70d893112eec20d8931005bf7458931005bc745893112eec625893132df77158931004fe76d4931004fd76d4931044fc76d493112f6e52d4931004ff7654931004fe7654931004fc7654931005df7354931015dc7354931006ef625493100eec6254931004fe76d0931004fd76d093103cfc76d0931015de73d0931005dd73d09310079d43d0931006ef62d093100eec62d0931004ff7650931004fe7650931004fc7650931
  | 34 => 0x8041006fb2058041006f8205804101efb105804101ef81058041006fb7558041006fa7558041006f97558041006f8755804103efb745804103efa745804103ef8745804103efb545804103efa545804103eba545804103ef95458041006b9545804103ef85458041006fb7358041006fa7358041006f97358041006f87358041006fb5358041006fa5358041006f95358041006f8535804103efb435804103efa435804103ef9435804103ef84358041006fb7258041006fa7258041006f97258041006f87258041006fb5258041006fa5258041006f95258041006f8525804103efb425804103efa425804103ef9425804103ef84258041006fb3258041006fa3258041006f93258041006f8325804101efb715804101efa715804101ef8715804101efb515804101efa515804101ef9515804101ef8515804101efb415804101efa415804101ef9415804101ef8415804101efb315804101efa315804101ef9315804101ef8315804101efb215804101efa215804101ef9215804101ef8215804101e7f7559631004ff745963103cfc74596311967f53596311967d5359631004ff725963100cfe725963100cfc725963101cfe715963101cfc715963101e7e515963101e7c5159631004ff7059631024fc705963101ef71059631004ff7559231044fc755923101ebf7459231156bf4359231156bd4359231004ff725923100cfe725923100cfc725923101cfe715923101cfc715923101ebe415923101ebc415923101edf315923101edd3159231004ff7059231024fc7059231044ff76d523101cfe76d5231004fd76d523101cfc76d52310467e65d52310067d65d523103cff769523101cfe7695231004fd769523101cfc76952312d6bf649523103ebc64952310073f5495231004ff765523101cfe7655231004fd765523101cfc76552310467e65552310067d65552312cebf645523103ebc6455231005f7715523101df47155231005fb7055231005f8705523103cff761523101cfe7615231004fd761523101cfc7615231004ff7558a31044fc7558a31004ff7458a3103cfc7458a3101eef7258a31136ec5258a31136ee4258a31136ee3258a3111eed3258a3101cfe7158a3101cfc7158a3101eee2158a3101eec2158a31004ff7058a31024fc7058a31136ef2058a3101ef71058a31044ff76d4a3101cfe76d4a31004fd76d4a31015de73d4a31005dd73d4a3100eee62d4a31006ed62d4a311376e52d4a31004ff7654a31004fd7654a3101cfc7654a3103cff76d0a3101cfe76d0a31004fd76d0a31004ff7650a31004fd7650a3101cfc7650a31005df7350a31015dc7350a3100eee6250a31006ed6250a31004ff7558231044fc7558231004ff745823103cfc7458231004ff725823100cfe725823100cfc725823101cfc715823101ef
  | 35 => 0x1eec715884101eef515884101eee515884101eed515884101eec515884101eef415884101eee415884101eed415884101eec415884101eef315884101eee315884101eed315884101eec3158841006ef7058841006ee7058841006ed7058841006ec705884103eef405884103eee405884103eed405884103eec4058841006ef3058841006ec305884101eef105884101ee7105884101eee105884101eed105884101eec1058841044ff76d484101cfe76d4841004fd76d48410467e65d48410067d65d484103dbe74d4841005bd74d48410073d54d48411d6de63d4841006dd63d484100eee62d4841006ed62d484113f6e52d4841004ff7654841004fd765484101cfc76548410467e65548410067d65548410073d54548411cede6354841006dd635484100eee6254841006ed6254841005f7715484101df47154841004ff764c841004fd764c84101cfc764c8410067e654c8410067d654c841005bf744c84103dbc744c841016de634c841006dd634c84100eee624c841006ed624c84113fcc324c841005f7714c84101df4714c84101df576d4441276f576d444101df675d444101f7675d444101ef765d444101f7665d4441276f565d444101f7565d44410067565d4441305f774d4441307b674d4441305f574d4441277b574d4441005b574d4441306f664d444101fb664d44413077754d4441307b654d44413077554d4441277b554d44410073554d444101fd663d444101fd563d444101fe662d444101fe562d4441005f570d444101ff260d444101ff160d4441026fb7598041026fa7598041026f97598041026f87598041026fb7498041026fa7498041026f97498041026f8749804103efb549804103efa549804103ef9549804103ef85498041026fb7398041026fa7398041026f97398041026f87398041006fb5398041006fa5398041006f95398041006f8539804103efb439804103efa439804103ef9439804103ef84398041026fb7298041026fa7298041026f97298041026f87298041006fb5298041006fa5298041006f95298041006f8529804103efb429804103efa429804103ef9429804103ef84298041006fb3298041006fa3298041006f93298041006f83298041026fb7198041026fa7198041026f97198041026f8719804101efb519804101efa519804101ef9519804101ef8519804101efb419804101efa419804101ef9419804101ef8419804101efb319804101efa319804101ef9319804101ef8319804101efb219804101efa219804101ef9219804101ef82198041004ff7558041044fc755804103ebe5458041006bd5458041004ff7358041014fe7358041014fc7358041004ff725804100cfe725804100cfc725804101efb705804103efb405804103ebc405804103ef84058041006fb3058041006f8305
  | 36 => 0xe635504103f9d635504103fae625504103fad62550412cdbf7155041007b77155041005b771550412cdbd71550412cfb471550412cebe615504103fb661550412cf3f51550412cf3d51550412cfb45155041007bb705504126dbc7055041007b87055041005b8705504103fba605504103fb96055041004ff7558c41044fc7558c4103ebe5458c41006bd5458c4101cff7358c4101edf7358c41146de5358c41146dc5358c4103edf4358c4103edc4358c41004ff7258c4100cfe7258c4100cfc7258c41146df3258c41006de3258c41146dc3258c4101cfc7158c4101ede3158c4101edc3158c41004ff7058c41024fc7058c41146df3058c41146dc3058c4101ef71058c41006df7558c41006de7558c41006dd7558c41006dc7558c4103edf7458c4103ede7458c4103edc7458c4103edf5458c4103ede5458c4103e9e5458c4103edd5458c410069d5458c4103edc5458c41006df7258c41006de7258c41006dd7258c41006dc7258c41006de5258c41006dc5258c4103edf4258c4103ede4258c4103edd4258c4103edc4258c4101edf7158c4101ede7158c4101edc7158c4101edf5158c4101ede5158c4101edd5158c4101edc5158c4101edf4158c4101ede4158c4101edd4158c4101edc4158c4101edf2158c4101ede2158c4101edd2158c4101edc2158c41006df7058c41006de7058c41006dd7058c41006dc7058c4103edf4058c4103ede4058c4103edd4058c4103edc4058c41006df2058c41006dc2058c4101edf1058c4101ed71058c4101ede1058c4101edd1058c4101edc1058c41044ff76d4c4101cfe76d4c41004fd76d4c410467e65d4c410067d65d4c4103dbe74d4c41005bd74d4c410073d54d4c41016de63d4c41006dd63d4c411475e53d4c411f6ee62d4c41004ff7654c41004fd7654c4101cfc7654c410467e6554c410067d6554c410073d5454c41016de6354c41006dd6354c411eeee6254c41005f77154c4101df47154c41004ff7558841044fc755884103ebe5458841006bd5458841004ff7358841014fe7358841014fc735884101cff725884101eef725884113eee525884113eec525884103eef425884103eec4258841006ef325884113eee325884113eec325884101cfc715884101eee215884101eec2158841004ff7058841024fc705884113eef205884113eec205884101ef71058841006ef7558841006ee7558841006ed7558841006ec755884103eef745884103eee745884103eec745884103eef545884103eee545884103eae545884103eed5458841006ad545884103eec5458841006ef7358841006ee7358841006ed7358841006ec7358841006ef5358841006ee5358841006ed5358841006ec535884103eef435884103eee435884103eed435884103eec435884101eef715884101eee7158841
  | 37 => 0x454103cfc76545410067f65545410467c6554541005bf745454103dbc745454101fb44154541044fe75d8141004fd75d8141014fe73d8141004fd73d8141014fc73d814100cfe72d8141004fd72d814100cfc72d81412c6f741d81412c6f441d8141006fb60981410057f75581410057c7558141296bf6418141026fa6018141006f9601814103e7f749944103e7e749944103e3e749944103e7d749944103e7c74994410467f73994410467e73994410467d73994410467c739944103e7f439944103e7e439944103e7d439944103e7c43994410467f72994410467e72994410467d72994410467c729944103e7f429944103e7e429944103e7d429944103e7c42994410067f32994410067e32994410067c329944101e7f719944101e7e719944101e7d719944101e7c719944101e7f419944101e7e419944101e7d419944101e7c419944101e7f319944101e7e319944101e7d319944101e7c319944101e7f219944101e7e219944101e7d219944101e7c21994410467f70994410467e70994410467d70994410467c709944103e7f409944103e7e409944103e7d409944103e7c40994410067f30994410067c30994410067f20994410067c209944101e7f109944101e7e109944101e7d109944101e7c109944101cff755944101e7f755944103cfe745944103cfc745944103e7e545944103e7c5459441004ff7359441014fe7359441014fc73594410067e53594410067c5359441004ff725944100cfe725944100cfc72594410067e52594410067c525944101cfe715944101cfc715944101ef4715944101cf4715944101e7e515944101e7c515944101ef45159441004ff7059441024fc705944101ef7105944103e7f745944103e7e745944103e7d745944103e7c74594410067f73594410067e73594410067d73594410067c735944103e7f435944103e7e435944103e7d435944103e7c43594410067f72594410067e72594410067d72594410067c725944103e7f425944103e7e425944103e7d425944103e7c42594410067f32594410067e32594410067c325944101e7f715944101e7e715944101e7d715944101e7c715944101e74715944101e7f415944101e7e415944101e7d415944101e7c415944101e7f315944101e7e315944101e7d315944101e7c315944101e7f215944101e7e215944101e7d215944101e7c21594410067f70594410067e70594410067d70594410067c705944103e7f405944103e7e405944103e7d405944103e7c40594410067f30594410067c30594410067f20594410067c205944101e7f105944101e77105944101e7e105944101e7d105944101e7c105944103dbf7655041006bf765504103dbf755504103f3f7555041046be655504103f3e65550410463e655504103f3d655504103ebc655504103f9
  | 38 => 0x1eec2158a41004ff7058a41024fc7058a41044ff76d4a4101cfe76d4a41004fd76d4a4103dbe74d4a41005bd74d4a410073d54d4a4115f6e52d4a41004ff7654a41004fd7654a4101cfc7654a410073d5454a4100cff7650a4100eee6250a41006ed6250a41005f77150a4101df47150a41004ff764ca41004fd764ca4101cfc764ca41005bf744ca4103dbc744ca4115fcc324ca41004ff75582410067f75582410047f7558241044fc75582410067c75582410447c7558241006be5458241006bd5458241004ff7358241014fe7358241014fc7358241004ff725824100cfe725824100cfc725824101cfc7158241246f7415824101ef4415824101efb705824101efb105824101ef81058241044fe76d9541014fe73d9541004fd73d9541014fc73d954100cfe72d9541004fd72d954100cfc72d95412d6be41d95412d6bc41d9541024fe70d9541004fd70d95410067f6599541306f76199541005fb7059541005f870595410067f7559541004ff7459541006bf7459541004ff7359541014fe7359541014fc7359541004ff725954100cfe725954100cfc7259541004ff7159541006f77159541004f771595412cebe4159541004ff7059541006fb7059541004fb7059541024fc7059541006f87059541024f87059541004fe76195410467e65195410067d6519541336f7611954101cfe76d514101cfc76d51410067f65d51410467c65d514103f3e54d514101df671d5141005f571d514101cfc76551410067f65551410467c6555141005f7715514101df4715514103fb44155141005fb7055141005f87055141014fe76d8d41156de63d8d41044fe75d8d41004fd75d8d4101cfd74d8d41156de43d8d4100cfe72d8d41004fd72d8d4100cfc72d8d41006de32d8d41156dc32d8d4103cfd71d8d41156df31d8d41024fe70d8d41004fd70d8d41156dc6358d41005ef7258d4114dec7258d41004fe76d4d41004fd76d4d41044fc76d4d411575e53d4d41004ff7654d41004fe7654d41004fc7654d4101cfc7650d41006df6350d41016dc6350d41005f77150d4101df47150d4100cfe76d894114eee62d8941044fe75d8941004fd75d894101cfd74d8941014fe73d8941004fd73d8941014fc73d894114eee42d8941006ef32d894114eec32d894103cfd71d894114eef21d8941024fe70d8941004fd70d8941005df7358941155dc735894114eec6258941004fe76d4941004fd76d4941044fc76d494114f6e52d4941004ff7654941004fe7654941004fc765494101cfc7650941006ef625094100eec6250941005f7715094101df47150941004ff764c941004fe764c941004fc764c94114fcc324c94103cfe76d454103cfc76d45410067f65d45410467c65d454103dbe74d4541005bd74d454101f7651d4541044ff7654541004fd765
  | 39 => 0xe7358b41014fc7358b4103eef7258b4103eef4258b4103eec4258b4116eef2158b41004ff7058b41024fc7058b41044ff76d4b4103cfe76d4b41004fd76d4b410467e65d4b410067d65d4b4116f6e52d4b41004ff7654b41004fd7654b4103cfc7654b410467e6554b410067d6554b41005f77154b4101df47154b41004ff764cb41004fd764cb4103cfc764cb4116fcc324cb41005f7714cb4101df4714cb410467e65d47410067d65d474103dbe74d4741005bd74d4741305f576d474127ef576d474101df675d4741306f765d47413077665d474127ef565d47413077565d47410067565d4741307b674d4741305f574d474127fb574d4741005b574d474101ef664d47413077754d47413077554d4741005f570d4741044ff76547410467e65547410067d6554741005bf745474103dbc745474101fb64154741335f5761474101ef5761474101f767514741336f7651474127ef5651474101df77414741335f5741474101fb66414741005f57014741004ff7558341044fc755834101cfc7458341004ff7358341014fe7358341014fc7358341004ff725834100cfe725834100cfc725834103efb705834103efb405834103ef8405834101e7f7559641004ff7359641014fe7359641014fc7359641004ff725964100cfe725964100cfc725964101cfc715964101e7e515964101e7c5159641004ff7059641024fc705964103ef7415924101ebe415924101ebc415924101ef441592410467e65d52410067d65d524103f3e54d524101df671d5241005f571d52412d5bd769524103ebd7695241046be6595241046bc659524103dbf71952412d5bd719524103fb66195241295be7095241044ff76552410467e65552410067d6555241005f7715524101df4715524103fb74155241005fb7055241005f870552412cdbf7655241046bf7655241044bf765524103dbf755524103f3f7555241046be65552412cf3e65552412cf3d6555241046bc65552412cdbf7155241007b771552412cfb4715524103ebe61552412cf3f51552412cf3d5155241007bb7055241295bc7055241007b87055241005b87055241004ff7558e41044fc7558e41006be5458e41006bd5458e4101edf7358e41166de4358e41004ff7258e4100cfe7258e4100cfc7258e4101cfc7158e4101ede3158e4101edc3158e41004ff7058e41024fc7058e41044ff76d4e4101cfe76d4e41004fd76d4e4103dbe74d4e41005bd74d4e410073d54d4e411675e53d4e41004ff7654e41004fd7654e4101cfc7654e410073d5454e41014ff7650e41016de6350e41006dd6350e41005f77150e4101df47150e41004ff7558a41044fc7558a41006be5458a41006bd5458a41004ff7358a41014fe7358a41014fc7358a4101eef7258a4115eee4258a4101cfc7158a4101eee2158a41
  | 40 => 0xc95118fcc324c95103cfe74d8151004fd74d8151014fe73d8151004fd73d8151014fc73d815100cfe72d8151004fd72d815100cfc72d8151006fb6098151005bf7458151005bc74581512867f6518151026fa6018151006f9601815101ebf7459051046bf5459051046bc5459051004ff7359051014fe7359051014fc7359051004ff725905100cfe725905100cfc725905101ef4715905101e7f515905101e7d515905101ebe415905101ebc415905101ef4415905101eb44159051004ff7059051024fc70590510467c5059051004ff7458c5103cfc7458c5101cff7358c5101edf7358c51046df5358c51046dc5358c51186de4358c51004ff7258c5100cfe7258c5100cfc7258c51186df3258c5101cfc7158c5101ede3158c5101edc3158c51004ff7058c51024fc7058c51186df3058c5103cff76d0c5101cfe76d0c51004fd76d0c5103ebe64d0c51006bd64d0c51004ff7650c51004fd7650c5101cfc7650c5103ebe6450c51006bd6450c51016de6350c51006dd6350c51005f77150c5101df47150c51004ff745885103cfc7458851004ff7358851014fe7358851014fc735885101cff725885101eef7258851046ef5258851046ec525885117eee425885117eee325885101cfc715885101eee215885101eec2158851004ff7058851024fc705885117eef205885103cff76d085101cfe76d0851004fd76d085103ebe64d0851006bd64d0851004ff7650851004fd765085101cfc765085103ebe6450851006bd645085100eee6250851006ed6250851005f7715085101df47150851004ff764c851004fd764c85101cfc764c851016de634c851006dd634c85100eee624c851006ed624c85117fcc324c851004ff745805103cfc7458051004ff7358051014fe7358051014fc7358051004ff725805100cfe725805100cfc725805101ef65158051046f5515805101ef4415805101efb7058051046fb50580510467c5058051046f8505805104678505805101efb105805101ef8105805103e7f755974101cfc745974103e7e545974103e7c5459741004ff7359741014fe7359741014fc7359741004ff725974100cfe725974100cfc7259741006f771597412cebe415974103ebc4159741004ff7059741006fb7059741004fb7059741024fc7059741006f87059741024f87059741004ff7558f41044fc7558f4101cfc7458f4103edf7358f4103edf4358f4103edc4358f41004ff7258f4100cfe7258f4100cfc7258f41176df3158f41004ff7058f41024fc7058f41044ff76d4f4103cfe76d4f41004fd76d4f410467e65d4f410067d65d4f411775e53d4f41004ff7654f41004fd7654f4103cfc7654f410467e6554f410067d6554f41005f77154f4101df47154f41004ff7558b41044fc7558b4101cfc7458b41004ff7358b41014f
  | 41 => 0x6f97458251006f8745825123efb5458251006fa5458251006f9545825123ef85458251006fb7358251006fa7358251006f97358251006f8735825123efb5358251006fa5358251006f9535825123ef85358251006fb4358251006fa4358251006f94358251006f84358251006fb7258251006fa7258251006f97258251006f8725825123efb5258251006fa5258251006f9525825123ef85258251006fb4258251006fa4258251006f94258251006f84258251006fb3258251006fa3258251006f93258251006f8325825101efb715825101efa715825101ef8715825101efb515825101efa515825101ef9515825101ef8515825101efb415825101efa415825101ef9415825101ef8415825101efb315825101efa315825101ef9315825101ef8315825101efb215825101efa215825101ef9215825101ef82158251014fe73d9151004fd73d9151014fc73d915100cfe72d9151004fd72d915100cfc72d9151024fe70d9151004fd70d9151006bf6499151005fb7059151005f8705915103ebe6419151006bd6419151306f761191510057e76d51510467e76d515103e7e64d515103e7c64d515101d7e71d515101d7c71d51510467f61d51510477761d51512be7c60d515101cfe76951510057d7595151006bf649515103ebc64951510473f549515101df67195151005f5719515101cfc7655151006bf645515103ebc6455151005f7715515101df47155151005fb7055151005f8705515101c7c76551510457f74551510473f74551510073f645515103e7e645515103e7c64551510073c645515100777715515101d7e715515101d7c71551510077471551510467f61551510477761551510077b70551510077870551512b67c6055151014fe76d8d51196de63d8d5101cfd75d8d5103cfe74d8d51004fd74d8d510067f54d8d510067d54d8d51196de53d8d5100cfe72d8d51004fd72d8d5100cfc72d8d51044fd71d8d51196df31d8d51024fe70d8d51004fd70d8d51196dc6358d5101cfc7654d51006df6354d51016dc6354d51005f77154d5101df47154d51004fe76d0d51004fd76d0d5103cfc76d0d510457e75d0d510057d75d0d510073d54d0d51004ff7650d51004fe7650d51004fc7650d510073d5450d5100cfe76d895118eee62d895101cfd75d895103cfe74d8951004fd74d89510067f54d89510067d54d8951014fe73d8951004fd73d8951014fc73d895118eee52d8951044fd71d895118eef21d8951024fe70d8951004fd70d895118eec625895101cfc7654951006ef625495100eec6254951005f7715495101df47154951004fe76d0951004fd76d095103cfc76d09510457e75d09510057d75d09510073d54d0951004ff7650951004fe7650951004fc76509510073d5450951004ff764c951004fe764c951004fc764
  | 42 => 0x4515965101ebf7459251004ff7359251014fe7359251014fc7359251004ff725925100cfe725925100cfc725925101cfc715925101e7f515925101e7d515925101ebe415925101ebc4159251004ff7059251024fc705925103ebe6495251006bd64952510473f549525101df67195251005f5719525103cff765525103ebe6455251006bd6455251005f7715525101df47155251047775155251005fb7055251005f87055251004ff7458e5103cfc7458e5101edf7358e511a6de5358e511a6de4358e51004ff7258e5100cfe7258e5100cfc7258e51006de3258e511a6dc3258e5101cfc7158e5101ede3158e5101edc3158e51004ff7058e51024fc7058e5101ef71058e51014ff7654e51016de6354e51006dd6354e51005f77154e5101df47154e51047775154e5103cff76d0e5101cfe76d0e51004fd76d0e51004ff7650e51004fd7650e5101cfc7650e51016de6350e51006dd6350e51004ff7458a5103cfc7458a51004ff7358a51014fe7358a51014fc7358a5101eef7258a5119eee5258a5119eee4258a51006ef3258a5119eec3258a5101cfc7158a5101eee2158a5101eec2158a51004ff7058a51024fc7058a5101ef71058a5100cff7654a5100eee6254a51006ed6254a51005f77154a5101df47154a51047775154a5103cff76d0a5101cfe76d0a51004fd76d0a51004ff7650a51004fd7650a5101cfc7650a5100eee6250a51006ed6250a51004ff764ca51004fd764ca5101cfc764ca5119fcc324ca51026fb7598251026fa7598251026f87598251026fb7498251026fa7498251026f97498251026f874982512aefb5498251006fa5498251006f954982512aef85498251026fb7398251026fa7398251026f97398251026f873982512aefb5398251006fa5398251006f953982512aef85398251006fb4398251006fa4398251006f94398251006f84398251026fb7298251026fa7298251026f97298251026f872982512aefb5298251006fa5298251006f952982512aef85298251006fb4298251006fa4298251006f94298251006f84298251006fb3298251006fa3298251006f93298251006f83298251026fb7198251026fa7198251026f97198251026f8719825101efb519825101efa519825101ef9519825101ef8519825101efb419825101efa419825101ef9419825101ef8419825101efb319825101efa319825101ef9319825101ef8319825101efb219825101efa219825101ef9219825101ef82198251004ff745825103cfc7458251004ff7358251014fe7358251014fc7358251004ff725825100cfe725825100cfc725825101cfc715825101efb7058251006fb3058251006f83058251006fb2058251006f8205825101efb105825101ef81058251006f9755825123ef87558251006fb7458251006fa7458251
  | 43 => 0x9351046bf5459351046bc5459351004ff7359351014fe7359351014fc7359351006be4359351006bc4359351004ff725935100cfe725935100cfc7259351006be4259351006bc4259351006f77159351004ff7059351024fc7059351046bf7559351046be7559351046bc7559351006bf7359351006be7359351006bd7359351006bc7359351046bf5359351046be5359351046bd5359351046bc5359351006bf7259351006be7259351006bd7259351006bc7259351046bf5259351046be5259351046bd5259351046bc5259351006bf3259351006be3259351006bc3259351006bf7159351006b77159351006bd71593512cebc7159351046bf5159351046be5159351046bd5159351046bc5159351006bf31593512cebe31593512cebc3159351006bf21593512cebe21593512cebc2159351006bf7059351006be7059351006bd7059351006bc7059351046bf5059351046be5059351046bd5059351046bc5059351006bf3059351006bc3059351006bf2059351006bc20593512cebf10593512cebc10593510457f76553510067f76553510473f745535103e7e64553510473e645535103e3e64553510473d645535103e7c645535100777715535101d7e715535101d7c715535100774715535101d7471553510077b70553510077870553512b67e605535101cfc7558f51004ff7458f5103cfc7458f510467f5458f510067d5458f51046df7358f51046df5358f51046dc5358f51004ff7258f5100cfe7258f5100cfc7258f51006de3258f511b6dc3258f511b6df3158f51004ff7058f51024fc7058f511b6df3058f5103cff76d0f51044fe76d0f51004fd76d0f510457e75d0f510057d75d0f5103ebe64d0f51006bd64d0f510073d54d0f51004ff7650f51004fd7650f51044fc7650f5103ebe6450f51006bd6450f510073d5450f51005f77150f5101df47150f5101cfc7558b51004ff7458b5103cfc7458b510467f5458b510067d5458b51004ff7358b51014fe7358b51014fc7358b51046ef7258b51046ef5258b51046ec5258b51006ef3258b511aeec3258b511aeef2158b51004ff7058b51024fc7058b511aeef2058b5103cff76d0b51044fe76d0b51004fd76d0b510457e75d0b510057d75d0b5103ebe64d0b51006bd64d0b510073d54d0b51004ff7650b51004fd7650b51044fc7650b5103ebe6450b51006bd6450b510073d5450b51005f77150b5101df47150b51004ff764cb51004fd764cb51044fc764cb51006be644cb51006bd644cb511afcc324cb5101cfc7558351004ff745835103cfc7458351004ff7358351014fe7358351014fc7358351004ff725835100cfe725835100cfc7258351046f65158351046f55158351046fb7058351046fb5058351046f85058351046f7515965101e7e515965101e7c515965101ef
  | 44 => 0x34ebd43d9132014ff72d9132014fd72d9132346bf42d9132346bd42d913201cfe71d9132004fd71d9132024fe70d9132004fd70d91321dcfd7699132006bf64991321dddd73991321bded72991321e7cc329913203cff76591321e5df73591321c5ef72591321dfcc3259132005f77159132005f47159132004ff7559132044fc7559132006bf74591321e4ff7359132006df73591321dcff7259132006ef7259132004ff7159132006f77159132004f7715913201cfc7159132006f4715913201cf47159132004ff7059132024fc7059132344fe76191320057e75191320057d751913203ebe6419132006bd641913233fcc3219132044ff76d5132004fe76d5132004fd76d5132044fc76d51320467e65d51320067d65d513222fcc32d513203cff7695132004fe7695132004fd769513203cfc769513203ebe6495132006bd64951320073f549513221fcc3295132004ff7655132004fe7655132004fd7655132004fc76551320467e65551320067d655513203ebe6455132006bd645513220fcc3255132005f77155132005f47155132005fb7055132005f8705513203cff7615132004fe7615132004fd761513203cfc76151321ffcc321513201cfe76d853231fcc32d8532044fe75d8532004fd75d853203cfe74d8532004fd74d853200cfd73d8532014fd72d853232ef631d853231ef621d8532024fe70d8532004fd70d8532137cc3298532006f76198532005bf7458532005bc745853212fcc3258532317cc321853201ef66118532006f56118532005fa7018532005f97018532024fe76d81322e7cc32d8132044fe75d8132004fd75d813203cfe74d8132004fd74d813200cfd73d8132014fd72d813201cfe71d8132004fd71d81322f6fa30d81322e6fa20d8132097cc3298132006fb60981320057f75581320057c755813208fcc32581322dfcc3218132005f67118132005f57118132026fa6018132006f9601813203ebf759935103ebe759935103ebd759935103ebc759935103ebf739935103ebe739935103ebd739935103ebc7399351046bf5399351046be5399351046bd5399351046bc539935103ebf729935103ebe729935103ebd729935103ebc7299351046bf5299351046be5299351046bd5299351046bc5299351006bf3299351006be3299351006bc329935103ebf719935103ebe719935103ebd719935103ebc7199351046bf5199351046be5199351046bd5199351046bc5199351006bf31993512d6be31993512d6bc3199351006bf21993512d6be21993512d6bc219935103ebf709935103ebe709935103ebd709935103ebc7099351046bf5099351046be5099351046bd5099351046bc5099351006bf3099351006bc3099351006bf2099351006bc20993512d6bf10993512d6bc109935101cfc7559351046bf745
  | 45 => 0x87055142014fe76d8d421bede63d8d42044fe75d8d42004fd75d8d4200cfd74d8d42006be54d8d42006bd54d8d421bedc53d8d421bede43d8d4203cfd72d8d421e6df32d8d4201cfe71d8d42004fd71d8d421bedc31d8d42024fe70d8d42004fd70d8d421bedf30d8d421bedc6358d42005f77158d42005f47158d42004fe76d4d42004fd76d4d42044fc76d4d420467e65d4d420067d65d4d4203dbe74d4d42005bd74d4d420073d54d4d42006df63d4d42016dc63d4d421bf5e53d4d4200dee72d4d42005ed72d4d42004ff7654d42004fe7654d42004fc7654d420467e6554d420067d6554d420073d5454d4233dbe76d0d4203ebe76d0d4203dbf75d0d42005bd75d0d42006bf65d0d42006bd65d0d421ddbd73d0d42016be63d0d42016bc63d0d4200dbe72d0d4200dbc72d0d4203ebf62d0d4203faf62d0d421e7af21d0d4200cfc7650d42006df6350d42016dc6350d42005ef7250d4200dec7250d4200dbc7650d42016bc7650d4200cbc7650d42005bf7550d42005bd7550d42006bf6550d42006bd6550d4203dbf7350d4203f9f7350d420079f6350d42016be6350d42016bc6350d421bf9c6350d42007af7250d4200dbe7250d4200dbc7250d421dfac7250d4203ebf6250d4203faf6250d421bf9f3150d421dfaf2150d42044fe75d8542004fd75d8542014fe73d8542004fd73d8542014fc73d854203cfd72d8542006f731d8542006f431d854216ef621d8542024fe70d8542004fd70d8542006f76198542005df73585421bddc735854201ef66118542006f56118542005fa7018542005f97018542044fe75d8142004fd75d8142006be54d8142006bd54d8142014fe73d8142004fd73d8142014fc73d814203cfd72d814201cfe71d8142004fd71d81420cefa20d81421bdde7398142005dd7398142005f67198142005f57198142006fb6098142026fa6018142006f96018142044fe76d953235fcc32d953203cfe74d9532004fd74d953200cff73d953200cfd73d95323667f53d95323667d53d9532014ff72d9532014fd72d953235e7f52d953235e7d52d953201cfe71d9532004fd71d9532024fe70d9532004fd70d95321ecfd76995320067f65995321eddd73995321cded72995321f7cc3299532044ff76595321f5df73595321d5ef72595321efcc3259532005fb7059532005f870595320067f7559532004ff745953203cfc74595321f4ff7359532006df73595321ecff7259532006ef7259532004ff715953201cfc7159532004ff7059532006fb7059532004fb7059532024fc7059532006f87059532024f8705953235cfe76195320467e65195320067d6519532005be7419532005bd7419532357cc321953203cfe76d9132347cc32d9132044fe75d9132004fd75d913200cff73d913200cfd73d913234ebf43d9132
  | 46 => 0x8f42004ff7158f4201cfc7158f421c6df3158f42004ff7058f42024fc7058f421c6dc3058f42044ff76d4f4203cfe76d4f42004fd76d4f420467e65d4f420067d65d4f4203dbe74d4f42005bd74d4f420073d54d4f421c75e53d4f42004ff7654f42004fd7654f4203cfc7654f420467e6554f420067d6554f4203dbe7454f420073d5454f42016de6354f42006dd6354f42005ef7254f4200dec7254f4203dbf7650f4236ebf7650f42005bf7550f42005bd7550f4203ebf6550f42006bd6550f4203f9f7350f42016be6350f42016bc6350f4200dbe7250f4200dbc7250f421c79f3150f42004ff7558742044fc755874200cfc7458742004ff7358742014fe7358742014fc735874203eee425874203eed425874203ef7715874203ef7415874203ef4415874214ef62158742004ff7058742024fc7058742004ff7558342044fc755834200cfc745834203ebe5458342006bd5458342004ff7358342014fe7358342014fc7358342004ff715834201cfc715834203efb705834203efb405834203ef840583420aefa2058342044fe76d9542014fe73d9542004fd73d9542014fc73d954203cff72d954203cfd72d954221e7f52d954221e7d52d954201cfe71d9542004fd71d9542024fe70d9542004fd70d95420067f659954220dbd749954222dbf7459542005df73595421bddc7359542005f77159542005f47159542005fb7059542005f870595420067f755954222cff7459542006bf7459542004ff7359542006df7359542004df7359542014fe7359542014fc7359542006dc7359542014dc735954220cff7259542006ef7259542004ff7159542006f77159542004f7715954201cfc7159542006f4715954201cf47159542004ff7059542006fb7059542004fb7059542024fc7059542006f87059542024f8705954221cfe76195420467e65195420067d651954200cfe76d514200cfc76d51420067f65d51420467c65d514203f3e54d514200dee72d5142005ed72d51421fdbe769514203ebe769514220dbd7595142046be6595142046bc6595142005bd739514200dbe729514200dbc729514203ebf629514203faf62951422d6bc619514221faf2195142044ff765514200cfe765514220cfd765514200cfc76551420067f65551420467c655514203f3c5455142005ef725514200dec725514203fac4255142005f77155142005f47155142005fb7055142005f8705514200dbc7655142046bc765514200cbc765514203dbf755514203f3f75551420073f6555142046be6555142046bc65551420073c6555142005bf7355142007af725514200dbe725514200dbc725514220fac725514203ebf625514203faf625514220f3f525514220f3d5255142007b77155142007b471551422cebc615514220faf2155142007bb7055142007b
  | 47 => 0x457f74551520473f74551520073f645515203e7e645515203e7c64551520073c64551520057f73551520076f725515200d7e725515200d7c725515220f6c72551520467f62551520476f62551520077771551520077471551520077b70551520077870551522b67c605515220f6f2055152014fe76d8d521cede63d8d5200cfd75d8d5203cfe74d8d52004fd74d8d520067f54d8d520067d54d8d521cede53d8d521cedc43d8d52044fd72d8d521f6df32d8d5201cfe71d8d52004fd71d8d521cedf31d8d52024fe70d8d52004fd70d8d521cedc30d8d521cedc6358d52005fb7058d52005f87058d523557e76d4d520467e76d4d520057d74d4d520067f64d4d521ed7d73d4d520167e63d4d520167c63d4d5200d7e72d4d5200d7c72d4d520467f62d4d520476f62d4d521f76f20d4d5200cfc7654d52006df6354d52016dc6354d52005ef7254d5200dec7254d5200d7c7654d520167c7654d5200c7c7654d520057f7454d520067f6454d520457f7354d520475f7354d520075f6354d520167e6354d520167c6354d521cf5c6354d520076f7254d5200d7e7254d5200d7c7254d521ef6c7254d520467f6254d520476f6254d521cf5f3054d521ef6f2054d52004fe76d0d52004fd76d0d5203cfc76d0d520457e75d0d520057d75d0d5203ebe64d0d520073d54d0d52006df63d0d52016dc63d0d5200dee72d0d52005ed72d0d52004ff7650d52004fe7650d52004fc7650d520457e7550d520057d7550d520073d5450d5203cfe74d8552004fd74d85520067f54d85520067d54d8552014fe73d8552004fd73d8552014fc73d8552044fd72d85521aef621d8552024fe70d8552004fd70d85521cdde7398552005dd7398552006f76198552005fa7098552005f9709855201ef66118552006f5611855203cfe74d8152004fd74d8152014fe73d8152004fd73d8152014fc73d8152044fd72d815201cfe71d8152004fd71d8152006fb30d8152006f830d815210efa20d8152006fb6098152005df73581521cddc7358152005f67118152005f57118152026fa6018152006f9601815203e7f755974200cfe745974200cfc745974203e7e545974203e7c5459742004ff7359742014fe7359742014fc735974203ebf435974220e7f525974220e7d5259742004ff715974201cfc7159742004ff7059742024fc705974203dbf7655342006bf765534203f3f755534203f3f6555342046be655534203ebc655534203f3c6555342005bf735534200dbe725534200dbc725534220f3f525534220f3d5255342007b77155342007b471553422cebe6155342007bb7055342007b87055342004ff7558f42044fc7558f4200cfe7458f4200cfc7458f4203ebe5458f42006bd5458f4203edf7358f421c6de5358f4203edf4358f4203edc4358f421dedf325
  | 48 => 0xe54d8143006bd54d814303cfd73d814300cfe72d8143004fd72d814300cfc72d814301cfe71d8143004fd71d81430d6fa30d81431ddee7298143005ed7298143005f67198143005f57198143006fb6098143026fa6018143006f9601814300cfc7559352046bf7459352046bf5459352046bc5459352004ff7359352014fe7359352014fc73593520467f535935220ebf4259352004ff715935201cfc7159352004ff7059352024fc70593520457f76553520067f76553520473f74553520473f645535203e7e645535203e7c64553520473c64553520057f735535200d7e725535200d7c72553520077771553520077471553520077b70553520077870553522b67e605535200cfe7558f5200cfc7558f52004ff7458f5203cfc7458f520467f5458f520067d5458f52046df7358f52046df5358f52046dc5358f521d6de4358f521eedf3258f52004ff7158f5201cfc7158f521d6dc3158f52004ff7058f52024fc7058f521d6df3058f520457f7654f523767f7654f520057f7454f520067d6454f520475f7354f520167e6354f520167c6354f5200d7e7254f5200d7c7254f521d75f3054f5203cff76d0f52044fe76d0f52004fd76d0f520457e75d0f520057d75d0f5203ebe64d0f52006bd64d0f520073d54d0f521e76e52d0f52004ff7650f52004fd7650f52044fc7650f520457e7550f520057d7550f5203ebe6450f52006bd6450f520073d5450f52016de6350f52006dd6350f52005ef7250f5200dec7250f521df6e5250f5200cfc7558752004ff745875203cfc74587520467f54587520067d5458752004ff7358752014fe7358752014fc7358752046f77158752046f75158752046f4515875218ef62158752004ff7058752024fc705875200cfc7558352004ff745835203cfc7458352004ff7358352014fe7358352014fc7358352046ee5258352046ed5258352004ff715835201cfc7158352046fb7058352046fb5058352046f850583520eefa205835203cfe76d9152014fe73d9152004fd73d9152014fc73d9152044fd72d915222ebf42d915201cfe71d9152004fd71d9152024fe70d9152004fd70d9152006bf6499152005df73591521cddc7359152005f77159152005f47159152005fb7059152005f8705915203ebe6419152006bd64191521fd7e76d51520467e76d515203e7e64d515203e7c64d51520057d73d515200d7e72d515200d7c72d51520467f62d51520476f62d51522be7c60d515222f6f20d515200cfe769515220d7d7595152006bf649515203ebc64951520473f549515200dee7295152005ed729515200cfc7655152006bf645515203ebc64551520473c5455152005ef725515200dec7255152005f77155152005f47155152005fb7055152005f8705515200d7c765515203e7c765515200c7c7655152
  | 49 => 0x874303ede435874303edd4358743004ff725874300cfe725874300cfc725874303ef7715874303ef7415874303ef44158743156f63158743004ff7058743024fc7058743004ff7558343044fc7558343014fc745834303ebe5458343006bd5458343004ff725834300cfe725834300cfc7258343004ff715834301cfc715834303efb705834303efb405834303ef840583430b6fa3058343044fe76d954303cff73d954303cfd73d95432267f53d95432267d53d954300cfe72d9543004fd72d954300cfc72d954301cfe71d9543004fd71d9543024fe70d9543004fd70d95430067f6599543215bd7499543235bf7459543005ef72595431ddec7259543005f77159543005f47159543005fb7059543005f870595430067f7559543234ff7459543006bf7459543214ff7359543006df7359543004ff7259543006ef7259543004ef725954300cfe725954300cfc7259543006ec725954300cec7259543004ff7159543006f77159543004f7715954301cfc7159543006f4715954301cf47159543004ff7059543006fb7059543004fb7059543024fc7059543006f87059543024f87059543224fe76195430467e65195430067d6519543014fe76d5143014fc76d51430067f65d51430467c65d514303f3e54d5143015de73d5143005dd73d5143205be769514303ebe7695143215bd7595143046be6595143046bc6595143015be7395143015bc739514303ebf639514303f9f6395143005bd72951432d6bc61951432279f3195143044ff7655143014fe7655143214fd7655143014fc76551430067f65551430467c655514303f3c5455143005df7355143015dc735514303f9c4355143005f77155143005f47155143005fb7055143005f87055143015bc7655143046bc7655143014bc765514303dbf755514303f3f75551430073f6555143046be6555143046bc65551430073c65551430079f7355143015be7355143015bc73551432179c735514303ebf635514303f9f63551432173f53551432173d5355143005bf7255143007b77155143007b471551432cebc61551432179f3155143007bb7055143007b8705514300cfe76d89431deee62d8943044fe75d8943004fd75d8943014fd74d8943006be54d8943006bd54d894303cfd73d89431deec52d89431deee42d89431deee32d894301cfe71d8943004fd71d89431deec21d8943024fe70d8943004fd70d89431deef20d89431deec6258943005f77158943005f47158943044fe75d8543004fd75d854303cfd73d854300cfe72d8543004fd72d854300cfc72d8543176f631d8543006f721d8543006f421d8543024fe70d8543004fd70d8543006f76198543005ef72585431ddec725854301ef66118543006f56118543005fa7018543005f97018543044fe75d8143004fd75d8143006b
  | 50 => 0x1cfe71d9153004fd71d9153024fe70d9153004fd70d9153006bf6499153005ef72591531edec7259153005f77159153005f47159153005fb7059153005f8705915303ebe6419153006bd64191532057e76d51530467e76d515303e7e64d515303e7c64d51530157e73d51530157c73d51530467f63d51530475f63d51530057d72d51532be7c60d51532375f30d5153014fe76951532157d7595153006bf649515303ebc64951530473f5495153015de7395153005dd7395153014fc7655153006bf645515303ebc64551530473c5455153005df7355153015dc7355153005f77155153005f47155153005fb7055153005f870551530157c765515303e7c76551530147c76551530457f74551530473f74551530073f645515303e7e645515303e7c64551530073c64551530075f73551530157e73551530157c73551532175c73551530467f63551530475f63551530057f72551530077771551530077471551530077b70551530077870551532b67c60551532175f305515300cfe76d89531eeee62d8953014fd75d895303cfe74d8953004fd74d89530067f54d89530067d54d8953044fd73d89531eeee52d89531eeec42d89531eeee32d895301cfe71d8953004fd71d89531eeef21d8953024fe70d8953004fd70d89531eeec20d89531eeec6258953005fb7058953005f8705895303cfe74d8553004fd74d85530067f54d85530067d54d8553044fd73d855300cfe72d8553004fd72d855300cfc72d85531b6f631d8553024fe70d8553004fd70d85531edee7298553005ed7298553006f76198553005fa7098553005f9709855301ef66118553006f5611855303cfe74d8153004fd74d8153044fd73d815300cfe72d8153004fd72d815300cfc72d815301cfe71d8153004fd71d8153116fa30d8153006fb20d8153006f820d8153006fb6098153005ef72581531edec7258153005f67118153005f57118153026fa6018153006f9601815303e7f7559743014fe7459743014fc745974303e7e545974303e7c54597432167f53597432167d5359743004ff725974300cfe725974300cfc725974303ebf4259743004ff715974301cfc7159743004ff7059743024fc705974303dbf7655343006bf765534303f3f755534303f3f6555343046be655534303ebc655534303f3c6555343015be7355343015bc73553432173f53553432173d5355343005bf7255343007b77155343007b471553432cebe6155343007bb7055343007b87055343004ff7558b43044fc7558b43014fe7458b43014fc7458b4303ebe5458b43006bd5458b4303eef7258b431e6ee5258b4303eef4258b4303eec4258b431e6ee3258b43004ff7158b4301cfc7158b431e6ef2158b43004ff7058b43024fc7058b431e6ec2058b43004ff7558743044fc7558743014fc745
  | 51 => 0xa52181542fef8521815425efb4218154006fa421815425ef84218154006fb3218154006fa3218154006f83218154026fb7118154026fa7118154026f97118154026f871181542fefb51181542fef8511815425efb411815425ef84118154006fb3118154006f83118154006fb2118154006f8211815403e7f5458c5403ebe5458c5403e7d5458c54046bd5458c5403cff7358c5403edf7358c54046df5358c54046dc5358c5403edf4358c5403edc4358c54004ff7258c5400cfe7258c5400cfc7258c54006de3258c54206dc3258c54004ff7158c5401cfc7158c54206df3158c54004ff7058c54024fc7058c54206df3058c5403e7f545885403ebe545885403e7d5458854046bd5458854004ff7358854014fe7358854014fc735885403cff725885403eef7258854046ef5258854046ec525885403eef425885403eec4258854006ef32588541feec3258854004ff715885401cfc71588541feef2158854004ff7058854024fc70588541feef205885403e7f545845403e7d5458454004ff7358454014fe7358454014fc7358454004ff725845400cfe725845400cfc725845403ef77158454046f75158454046f4515845403ef7415845403ef44158454004ff7058454024fc705845403ebe5458054046bd5458054004ff7358054014fe7358054014fc7358054004ff725805400cfe725805400cfc7258054004ff715805401cfc715805403efb7058054046fb5058054046f8505805403efb405805403ef84058054014fc7559353046bf7459353046bf5459353046bc5459353216bf4359353004ff725935300cfe725935300cfc72593530467f5259353004ff715935301cfc7159353004ff7059353024fc70593530457f76553530067f76553530473f74553530473f645535303e7e645535303e7c64553530473c64553530157e73553530157c73553530057f72553530077771553530077471553530077b70553530077870553532b67e6055353014fe7558b53014fc7558b53004ff7458b5303cfc7458b530467f5458b530067d5458b53046ef7258b53046ef5258b53046ec5258b531f6ee4258b531f6ee3258b53004ff7158b5301cfc7158b531f6ec2158b53004ff7058b53024fc7058b531f6ef2058b53014fc7558753004ff745875303cfc74587530467f54587530067d5458753004ff725875300cfe725875300cfc7258753046f77158753046f75158753046f45158753196f63158753004ff7058753024fc7058753014fc7558353004ff745835303cfc7458353046de5358353046dd5358353004ff725835300cfe725835300cfc7258353004ff715835301cfc7158353046fb7058353046fb5058353046f850583530f6fa305835303cfe76d9153044fd73d9153236bf43d915300cfe72d9153004fd72d915300cfc72d9153
  | 52 => 0x8554006f65318554276f45318554336f74318554006f64318554336f4431855401ef7721855401ef6721855401ef5721855401ef47218554276f75218554006f65218554276f45218554336f74218554006f64218554336f44218554006f73218554006f63218554006f4321855401ef7701855401ef6701855401ef5701855401ef47018554276f75018554276f45018554336f74018554336f44018554006f73018554006f43018554006f72018554006f42018554006f761d8154006f461d8154014fe73d8154004fd73d8154014fc73d815400cfe72d8154004fd72d815400cfc72d815401cfe71d8154004fd71d8154006fb30d8154006f830d8154006fb20d8154006f820d81540077975d815430fbb74d815430fbb54d81542677a54d81542677854d815430fb854d8154006fb63d8154006fa63d8154006f963d8154006f863d8154006fb62d8154006fa62d8154006f962d8154006f862d8154006fb61d8154007f361d8154006f361d8154006fa61d8154006f961d8154006f861d8154007f061d8154006f061d8154266fb75d815430efa75d815430efb74d8154266fa74d815430efb54d8154266fa54d8154266f854d8154006fb73d8154006fa73d8154006f973d8154006f873d815430efb53d8154006fa53d815430ef853d8154266fb43d8154006fa43d8154266f843d8154006fb72d8154006fa72d8154006f972d8154006f872d815430efb52d8154006fa52d815430ef852d8154266fb42d8154006fa42d8154266f842d8154006fb32d8154006fa32d8154006f832d8154006fb71d8154006fa71d8154006f971d8154006f871d815430efb51d815430ef851d8154266fb41d8154266f841d8154006fb31d8154006f831d8154006fb21d8154006f821d8154005f67198154005f57198154006f76198154006f46198154006fb6098154005f77158154005f47158154006f76158154006f46158154006f76118154006f46118154026fa6018154006f96018154005fa7618154006fa76181542b77b7518154007b974181542ffbb541815425f7a541815425f7854181542ffb85418154006fb6318154006fa6318154006f96318154006f86318154006fb6218154006fa6218154006f96218154006f86218154006fb6118154007f36118154006f36118154006fa6118154006f96118154006f86118154007f06118154006f06118154026fb7518154026fa7518154026f87518154026fb7418154026fa7418154026f874181542fefb541815425efa5418154006f9541815425ef85418154026fb7318154026fa7318154026f97318154026f873181542fefb5318154006fa53181542fef8531815425efb4318154006fa431815425ef84318154026fb7218154026fa7218154026f97218154026f872181542fefb5218154006f
  | 53 => 0x4ff725865400cfe725865400cfc725865403ef7715865403ef7415865403ebc415865403ef44158654004ff7058654024fc705865403cfc7458254004ff7358254014fe7358254014fc7358254004ff725825400cfe725825400cfc7258254004ff715825401cfc715825403efb705825403efb405825403ef84058254014fe76d8d54216de63d8d5403cfd75d8d54044fd74d8d54216de53d8d54216de43d8d5400cfe72d8d54004fd72d8d5400cfc72d8d54006de32d8d54216dc32d8d5401cfe71d8d54004fd71d8d54024fe70d8d54004fd70d8d54216dc6358d54005ef7258d5420dec7258d54005f77158d54005f47158d54005fb7058d54005f87058d5400cfe76d895420eee62d895403cfd75d8954044fd74d8954014fe73d8954004fd73d8954014fc73d895420eee52d895420eee42d8954006ef32d895420eec32d895401cfe71d8954004fd71d8954024fe70d8954004fd70d8954005df7358954215dc735895420eec6258954005f77158954005f47158954005fb7058954005f87058954014fe73d8554004fd73d8554014fc73d855400cfe72d8554004fd72d855400cfc72d8554006f731d8554006f431d8554006f721d8554006f421d8554024fe70d8554004fd70d85543077775d8554007b574d855427fb754d85543077654d85543077454d855427fb454d8554006f763d8554006f663d8554006f563d8554006f463d8554006f762d8554006f662d8554006f562d8554006f462d8554306f775d855427ef675d855427ef774d8554306f674d855427ef754d8554306f654d8554306f454d8554006f773d8554006f673d8554006f573d8554006f473d855427ef753d8554006f653d855427ef453d8554306f743d8554006f643d8554306f443d8554006f772d8554006f672d8554006f572d8554006f472d855427ef752d8554006f652d855427ef452d8554306f742d8554006f642d8554306f442d8554006f732d8554006f632d8554006f432d8554006f770d8554006f670d8554006f570d8554006f470d855427ef750d855427ef450d8554306f740d8554306f440d8554006f730d8554006f430d8554006f720d8554006f420d8554006f76198554005fa7098554005f97098554005fb7058554005f8705855401ef66118554006f56118554005f67618554006f676185540077575185542cfb77418554277b75418554337765418554337745418554277b45418554006f76318554006f66318554006f56318554006f46318554006f76218554006f66218554006f56218554006f4621855401ef7751855401ef6751855401ef4751855401ef7741855401ef6741855401ef47418554276f75418554336f65418554006f55418554336f4541855401ef7731855401ef6731855401ef5731855401ef47318554276f7531
  | 54 => 0x2d00480090004000006800100180030058001001800100000140000006001c002000800f006801f000c00000640000054000000c000000c00300240000068000005c0000000001001800c001c00000000160000005002c002001400d00000030008000000000200000000004007002c00900100000004002004400303cfc7558f54046be5458f54046bd5458f54046df7358f54046df5358f54046dc5358f54236de4358f54004ff7258f5400cfe7258f5400cfc7258f540467f5258f54004ff7158f5401cfc7158f54004ff7058f54024fc7058f54236df3058f5403cfc7558b54046be5458b54046bd5458b54004ff7358b54014fe7358b54014fc7358b540467f5358b54046ef7258b54046ef5258b54046ec5258b5422eee4258b54004ff7158b5401cfc7158b54004ff7058b54024fc7058b5422eef2058b5403cfc7558754004ff7358754014fe7358754014fc7358754004ff725875400cfe725875400cfc7258754046f77158754046f75158754046f45158754004ff7058754024fc705875403cfc755835403c7c7558354046be5458354046bd5458354004ff7358354014fe7358354014fc7358354004ff725835400cfe725835400cfc7258354004ff715835401cfc7158354046fb7058354046fb50583540467c5058354046f85058354046785058354046bf545965403e7e545965403e7c545965403ebc545965403f3d76d525403d3d76d52540463d76d52540473f73d52540473e73d52540473d73d52540473c73d525403f3f63d525403f3e63d525403f3d63d525403f3c63d52540473f72d52540473e72d52540473d72d52540473c72d525403f3f62d525403f3e62d525403f3d62d525403f3c62d52543873f32d525437f3e32d525437f3c32d52540473f71d52540473e71d52540473d71d52540473c71d525403f3f61d525403f3e61d525403f3d61d525403f3c61d52543873f31d52543873c31d525437f3f21d525437f3c21d52540473f70d52540473e70d52540473d70d52540473c70d525403f3f60d525403f3e60d525403f3d60d525403f3c60d52543873f30d52543873c30d525437f3f20d525437f3c20d525403cfc7458e5403e7f5458e5403e7d5458e5403edf7358e54226de5358e5403edf4358e5403edc4358e54004ff7258e5400cfe7258e5400cfc7258e5403ebf4258e54004ff7158e5401cfc7158e54226df3158e54004ff7058e54024fc7058e5403cfc7458a5403e7f5458a5403e7d5458a54004ff7358a54014fe7358a54014fc7358a5403ebf4358a5403eef7258a5421eee5258a5403eef4258a5403eec4258a54004ff7158a5401cfc7158a5421eef2158a54004ff7058a54024fc7058a5403cfc745865403cbc745865403e7f545865403e7d5458654004ff7358654014fe7358654014fc7358654
  | 55 => 0x3802c0000008001c00b00c40060018000000400000000000000002000000000040070000003000000100000000018004001c01e0000009001000400000050000002004000300100000004006002c000006c019001000400280000028000000000000040120000001001000100a0009000000100040020014001005400a0000000000c007001c00200000140008019002c009000400c000000000040000078003002401300000000038004000000400000010000002000000c00000060000000002c01e00180230004008006c0020010002001800f001400000400020014003000c00100280030008005002400000480000004005000c002001400200300020008007006400b00140080010000005c001001c001002400b00080050014000000800b000c000001000000280000014000000800600ac001000000000b00010020005000800500dc002000c0060014006001400100140060010006000400000000110000006000c00500040000014005000c007002400000380000000000003001d000000000080030008003001000e001000000f80010010000002c000001000000600000000000005c00a004c029001c00c00140000018001000000f0000002000000800580000028003001401a001400a008c003000400a00000020004000000c00000040000038002000c002000000000040050000008007800e000000a0000004000000c001001a000400400080100000005002400d0000005000400000080000018008001000300440050004002001c00700000070000000000000f0000000007c00400000080070000000000a0018011004800c00180030024000001400000140030008002008400a000800a007800000140070050006000400000100020038002007c006006000000040000000001000c00100180030000005000001200a800000200120000007000800000000080004007000c00000480020034007000c00e000c00a00000000040008003400200080080000002002800b0000001000400100540010000002000c00000140010058005000c0000088000001402b0008009002c0060004001004400d0024004000401600180000000001000000c000000000340040070010000c0010024000003801d0000000000c0030020003000000000140060000007004c000000800d0028006006400a000c001001c04200500000010025008c000000000200400050004000000c00c0018000000000b000000b0004001000c006000c00400e8000000000b000000b0000001000c00d00400010024002000000a000c001003401e000c0020014001001400000180000038000000800100000000024002000000f00100000000000000001c004000e00f8007000000300000020028004000800000580150004000000000f00080010000011000c
  | 56 => 0x400500200040014000004800b001c0000000007005c001000800500000100018001003000200080130000008000000100c000500080040014022002802a0000019000400100200000004000000c00100000020000000003c00700180020000000003000400280070014000000000b000c00e00d4038000800100040040000008005800700000010000000000000b00040010000000008800f000c0040000000001001b00480040000000000400800000010034003000000100080030000011000000e002000200040040004006000800c001c000001c000000001000000010000002000400900240080010001000c0000004002000800a00000040000000000c003000c009001c00100000060044004002800a0000006000c00e000000000000040014000000c00a0010000000401100000010008003001800100080000000000000400200000100004001000000000000000000002001c00000140010028002005c00b000000100000000020003000c000000001a0080008000001300a4001002004f00000010034003000800a0038002000800300780000000000001c0020000024001c002004c0030088009000400000240000018004000801900000080000002001400000140000014000000400400000000000009001400000000130000004001c00b00000010000000000400500040010000002003801e00180130018006008800100c0002007400200000000054006000001d0000001007c0030014000000401f0004000000c0020000000001c00100000010010008002c000000000500a40000068000000001500300090004000001400300100000018000002000a00200070000009001800900b80110010006002c0040008008000400a00000060008001000800400000040000000002c0000034019000c006000800200040010000001000402000200070030001000000200300040050003008c001003c01e000000a002c001001000000000000000002003c00e0064000001800200040120024006000400000340000000001002c00b0000001000801400180000010007000c0030024016000800f00140030000002000c00300040280088015001400c007800300040080000000000000000080260000006005400200c00060018006000c00500440070004000000001c00040070014002002c006000000400040000010003000000a001c004000c00600200000018009000000100000000028000000400b0000000000000d0008001001401100080000000007008c001000000300440000000006000400e0018001001c019002400000040010020001002000600080000000002002000b000400000a4008000400300240030024000000400000340120008000001800a001c0010060007000c000000000200040030000000001c004005c000
  | 57 => 0x90000005002c00200100020044000000800500000160000000000400000100030004000000400f000400300180010014001000000000040050004001003801400000000008000000000000000000004017000c0010010000001800200040040024006000400100000080028000000000100080000000008005c001000000000000010010000004c0060018014000c003000000500000000004015000400a001c0050058000000400000180080008006000800200040010000012000400100140000074000000c009000800000000030030008000000a001c00200000030004006005c0020000003001000a003800b00080060004013002c0010000014000c0100028001000400e003000000000010008003000000e00040000008007002400900000000000001001c00e002c004001000000240000028000001400100080000010007000000100040070024011001400500000010018003000000000000030020011000000000000010004007001000000000010000000001800d000c0280014000001c003000400f00500090000014000000000380000000005000000000040080000000000c000000c002005c00000080060008001000000400040090004006000800000300000008016000c001001000b0004000000000000000020000006000000400180000074000005400200000080000002002800a001401000000090000006002c00100140000004007000400100180020008005000400100240030000008000400c005000500080000008003000c004000c001000000200040000000000001401400000000000008001800b0008008002800000100030004017000800100640030000029005400300000030018001007c00200300190030007000800a0004000000c00100340090034002001400b0000004001000200040110030000000000400000050020006000000400340000000016000000500800000018005000c00000000000008005000800b000c005006800000540040008002000c0000004004000400100040030030004006c00000640050000005000001e00140180000008005c00700000010010008005400000040040008000005400100b4004000800e001400a002800500080040044001000400600280000014004000000f000c00000000160014001003000200100000004004001000200040060008002000001d0044007007000d00180000000000004800700000000028001002c002009c0010014000003c00000040010000000001000400ec002004c00a000000e0000019000800000000010024010000c00000140070018002002800000240090000002003000000680030020003001000000100000000008000c00000040010018004000000b00800020000000000400100100000000004001400000000030020000000
  | 58 => 0x401000000010008000000001f003400700080170008004000400b000400700000010000000003400d000000f000000000080000000000000c00000040000058003002c000000401a00140040008000001402a0000015000800100400000008001003000300040040014001001400600a0000001c011000c00300100030024002000000a001000100040090020000014801b00280010004000001400a002800f0008022004c00200c00000004002000406c0000000005c00e0010001001800000dc00d001c000000c0000004001000400000000040040000001400700040090004000000c00a000c00300080000010000000c0050004014000c0060008014001000500440050000005001001b004001a000400800140040008001000800b00200020004012001401d000000400000000010001004000200080000000003001c0030014002007c000000000c0028000000800000000040078007000400300180020004002000000a00040020000003000800b001002c001800f00180000034001000800400040040010004000c0000000006001c0030000000006c00200000000010025000800300000000020000000c000001801600380000064001000000d000c003004c000000c0030008002000c001000400c000000d00000000004000007000800000040018007000000a0020024000400400280000000000002c00000100040004000001c00b0008000001800100140020004014000000000000020000001001400100000080008003004000c003800e000c000001c0080014005008c0000008003000800f0038005000000100380050014001000400900140010018002000c006000800700240000024000000c00a00140050014001000800300200080030006006c004000000c004000e000400a0008005004c0000050001000000a00000040038001000000c00080000000000000800300040150004000002c0020008001001800100340080004002001000000000020004000000401d003c001000c00300000060010004001400200000010004007000800000000190004016000c00d00040000030001000800100180020004004001c004001400100140010008002000c000000c006002000c002c008001c004000000600000090000001000000e000800200180090008003001400100080050050003000800100500000088005000000000300000008000001c0120004003001c00000080000000004001c00000100030014005013c000001c003001000500000000018007005c00c00000000000001000c006003c01100000000010003001800d001400000000040020009002000000000090010002000c00a00040010000000000401a001400000000050014006006400700100010004000001800300e0000000000200000040034008004401
  | 59 => 0xc000c002001c00c00040040004006000c0020028001000000e0004001000000b003c002002000f0008005001400c00040030020003000400c000000a00140000000000000000700540040000000000c0030020006000000000380010000001004000100100010004006000800b003400000040010010005000000300000000000009000c00b0008001000400200000040008003007402700a00020004008001c004000c00400080010000000006c008001403c003c000000002200080090000002000400200040010018000000c00800000040000001001c00a00000010018007000800e0084009000c007000400b001000900000000020004000401000100000058000000000000480030020019000000b000400600000020070001000c0060020001000400e00540000020000001c004000000900580010004016002c00300300000000002000000100000030034002000c003000002100000040000003000400000f4000000000b000800100140000024001000c0040004000000000100040080000008000c00a00240000040006000000200000020004001001000100140000000007000400600e000100440000014000000000100100000004005000401000280000000001000400500100050024001000400000040040000001000800d00440000000000000c012000000700000010028005001c003000800400040040010000002000600000000000000000c000000000200280020010003008c005001c028000000200000030034000000000d00000060078002000400000340100004005001401b000000900200000020000002400a00ac0020008000000c00100300080004000001c00000080060000002001400300100040008001000c0000008017000c00a00140010074001005c00200000010014007006c00e001c000003800100040030004000001c0000018003003002300000010008011000c0010004001000c0000024002000c00000000030000001001000400000000004009002400500040170014046003c0070034000002400b000000200100060004000000c004000c00500180000004001000000000000010004000000c0040010006001400a000001d000c008000000600300000024001001c00c001800c000002e000c00700000020004000001c0080004000000000000000020008011000000d000000900000050000003000001a000400200100010004004000801a000000d0030001000000d000c0000004006000c00000000040018001000000a001c00200740050000009001400a00100080004004001c0010004000000000700000080004000006800500080030024008001800900040000000001002800500000070004009000000a0004016000800400340290020001000c0020000000000000a0000000001800100
  | 60 => 0x3a3c0001133000039b800000000f6400000000000002b48702e6cded2340000000000000c680d0c5c106c92077174e5bec0000000148a5b2cd2717ce2306091099d9a0a000085cc000247f21fa0000da919571866000116f11c1139e00000000000242a000000005130b6e0000234940126f271601e186dc3fe000006720cd71bba000000002520000278d23080833e9c0000e051cfd3ff26c3c83d8000000000003c98ff1112e61ac2241d131d706ff8c69125343ca41f91190adc06ec8aac96b0715108e0001032934818640000dfa12fb12968ec4d5680083af6087c000238d000017f4000186e1ebe70e800015352f426d8d1c9008b132e4a1847b210548ac130801f19271d5e066840da34b03948a440ce0420000026b86f094f8139200002ba023535163ee917c95bc00007c74173113145da8884000224514b6310cd919e2d11cc00350c91af333dc36b4c5998f9419a38c8bf300001aa6112cb991b752c4e12845158000170491acfed12fc2efc1dec7bd04e01f5e6bb41aa9d7f000000000490e6d09aa00008f909622f7c00010d48341000007109530d540a2a5814818817e0fd6128859d0a12095833f40b82027313e6b40b3b06eb0000282474c8000000000001e88000000039900001c64000064702268000000088f904e97ac113052ac0000000357032100000584000000006d7800002fa0000000086f05d81b081360b392edc8f7c0fb800000000000bca8000044c2cc000022d8246c31e441494b2000004b8cc50000086a64646be84e412be69dd1ed80002a3444840001d8c179c40480000000000031d44d8954e1b90000002c1ffb47546fe0cfe86a9000038150c22304000000009b507231b603670db680002e680690000000018563260957a17f39f015340ab98802b0a1dcd2441a2b265c839458221b2208a366800009963612461c220800000002c488b20382000035ad142a1b919a26f0455c8000000040b4fc50c4c00003d64000033200000000000000011660000e758000000000000000de53fc6000107e1a6200005e34a6b9161258e3adc00022c13ed85be809b1265199234850ba8db43d9c0aac7b7883e34f40000000246943502b7c00017180000000c00300200000008000000000100100000000001000c0080000001001c0030040028003000400340090000000000c0210008000000c0000008000001c0080008002003c001000c0040004001007c000001c0080030000000800c00080040000009000000c00000160050000002800100340010000001004c003000800b0030010000001200000000004005001c001004800000340170004001000000000000000014001002c0120004000002c00300100010000036004c002000000300100080008002004c00000040030000005004c002001c001002000000000
  | 61 => 0x80000000000088741f9861406503fc856ca17122a210445a79598151a25f49991a8307421048048a3d23a0a82f91320dbc04481cc44131eec1f547848931184819fc2714000213123b23828000000033e60000b2ba036384e000086c01af000000000000fa341de38a85ee090f31aa3e24000000030487e64d65024c3c3c3df07a30c2a3f5a0be4daf93492854742030b8000000082680001ca9258259504a8229339d4547c00000f7000071cc000000003001c589a990930000000000006c3000014504d012951d26522ce4f99112d145514039862f2f6632c8f5098130edc0b58bd0000000007ac47e880000618000019f9d392e9e46c40000000082a4c64411981d051c7bd89720000122800000110000000044e80000000000074600001e0c000004fc54892ea000041bc362000000007dc800009c23cce0000e5a0e5e16307a40000000000000000000000000003e011c500000000560c0000ca431fa0000000000015760000eda00000000000000000000000000019592e2190200000001b1e000045fc65d800010a47e60ea300002ac656a000000000dd287c40000000048400000002031000000008aa0f92147c26880000d85076c803cb339e500000094000000000000000011b000041d800000000000087200000000be61d8800006f49e87366c645438791ab11c6000015f23252b560000da01861045647f060300f5000001a0000149b1c7e0000e628dd0271c0afc25e0b4637964ddc1bc19db000074589621a3d462e1ff0fc2124700000001198800000003bf4e729c4039e063f82290e3300622664d04991b42668ea039c1c364396001800000af1aae079ce420807185c01b4794000015f200000001fed306e3f800001fab00000000a9d102900008dcc00003530000502442a04d60d960d64cac0e452c5e5e001d316fe3ec45b4c30c141828f486fc00000a20c687610765032608ca0000d17221a3aa601bc0639ef801e822b0f191fc815a04a24fe80060000023e0d9d8090000049dc000103200000fecbb189b2000019dc4ce953e0000242c87f0000296a00003861c5600000000000000000007e00a031ade0000000000014eb0000793c0001e9511fa00006ef9bd2298800000000000219c60f05f192de22b200001010000000000000000000000000003df06a33ebc25d400016be1e880000763000034aa00009a2a20e3ada38d411419b40d3255a079292e943dc4160ac4197846263694a6788120000000066e89a52eb24b64385000038a80000dd504ef2bce74ec39c9c9e22200000000114000005bfc160942300007a291d5a10719bc00009e217013154000083f801741f63f1800000000f98411cf73800025c600010518f7241863ce4196811403781624c870000276a6acc78d0a521dfc370840f0985000091780000a69
  | 62 => 0x147a0000f4ea11230527954b578345318445e4b7200002294924092e9008139835809e100000b742f94d4816b20ec47d3515a06c00f8e22ec4358af405ee784c9bd1ac300002790000024139fc8678a5192b7418e3b88c381ef43a50854c87c11f7247e5d444fd2415236c09e0925a2221fb455cc7858dab42588f98f910cf02c5c4ea08b287af00001a8483b060a4648330823e988d46a8177cf9e0e80272c3cf8aa016462e94320c2928cfc0f6600000000b7511608280813143416be59b8d4f8ed24900700ceb18c8614021f6c366017728387afc000029700000000d8c82fe0cf864282f48f820fc000001a790903c627f9d0ab0e772494487523c07603114825855e0f901a080000629127e09d06e40000000009b22d34ccd018137222e8400000001ae87f14b490e2041ac87489f00000000065d4000000028002c74000230f461a0000c961fcf05d40000c8f888909926d306038000173a0c3c1c409de4342000015e9402000004240001b310bbc2bacd038a5a00004a88000000007ea00006bb0f7e122c000000980002c500c00f128000269a27d06de800035000000000143618d86868000072f2106000000007f23f060bbc000177c000014a8c00936544a800004e500000000651ca089f0b227836fd1bf00002d9a00000000d8700003a740001f9517d05f94b120a55000011a00000b23165658600000d9e00002e98ef7000000005b1400023ef000029ac47a87e112de5ab8000006b3ecc00012179d8300002188e53962c1dfe6280fd4000024de91e8b3a958f16cc6b18b28101a20ca30f4cc309d0091e3cccd9b80000f628108d65876548e03bb0f9a0e860000648c0b11f49477e17200000000000000003be000030126b6c12d1f2d263c26f0ea61eef06b864d466a0000000091ec7720000416e1b3d20605e8220627f400018c5000069a0a0583c400006580b9983040000381c0002130000000005c28000000000000000c7e0000000071b01592a22000118e8375187886584c193e620864040791108c0ede4dc48d123870c764a38cc7912a3c9a9224efd0274371823cd13b2477226e8808dd7000013b219707441bd1370c55f0fa10000000000000000b5200000634e65852400000000af50963000000000001309000006f400000000000512c0000e633cb249d8000128800000000a4997921dd66e88000097f00000000a3c000016262f502ad000013d884600ba8b281ffe04d01799b00402e0044000196f33b21e6010521b028d400011c29b7225282e8c30222c63c1c260415a03522c887e5825317fc000063301b0219d2abe4a7cccc1e3d00000000000000000000001002128c1c082e4d05500000000000059b8b083c7462248c40d7301964958a2f055d417e3230fd180002472000082704ee0000000089597710f9a19c
  | 63 => 0x805510541000035644b70f8b055000008108edc1288087000019ff17f265005a096200f2e17546a106d214a6526824d03de35627098ffe03b4485224444be00003cfa0000c1b0000212c0000000000000000000000000039e884e0be312d2000000010719b4e478e00009ad0000062c8e5823e0f4b00000000b5c23c309722a285c500d4253c1bfc7b80000000000000001f7e1280552c99b0000073811504aa800000005dd455e8000000011b4ef500000000797c000000000008c1459e1c172bc257000002142000034746d0845f000054342b200003dc63ac0a9487540000628c5149074384a0000000000006a82b2c00013aa00005c2478480002e0e000000000000b8a0000000000031d600010450720364e0000b9b81b13dbc0000acf127c0818591c1401b9c2266656c000000022c00188000186f000018188618a420c3e0f6800011c41bec909cb4f96bd184a0fc4000083d43e61518a6415ba06ce0000f6622d038c04e4000022971bf446bc5ed1dcd01c200000ab187f387e4d00df69dfe077e42bc00015e50000000000018a9389e16640948eef0fd404788d20155440e0000db98ffb0a520000000000000000000ea1a148227026c10a623683350146400009e546004828c3e83cb168e0000000178600000000000057539500000cc58000000000000001100046264cc0001dc20f4400001dc91f42a381de48ee800000008540f6e8000000000000001ee20000393918c88be3e9e4a60d4100d806246d582a997ee44e854300fd20003f347c4c10991820e564ffc0000000149c00002048000475800000001921247474c8c061190417457c000023f33d0830600000374176003f00000000000000000000a9900000000000122f45340000de397892c6686ac38186df419233840000fa0000009c8cc800e3000000000001c210000725d02792ed07087850000248b054c3a103c10811000000010fc8ced00008424718800044fa00004140000435a39e0c5203dc32c68100ae501d10ad2000000015ac1f883ed00000cd600000000000132000003d3d210129d370621d49bf23831f50676029b017c1da24be048c0bec00000000ae600001a5047346c30000099c86b0ffb800023906310000000001a080d4000000036b40000eeb8b1f47ec000000000001c066460b3c0ba937142950e150e22325c0db03f813720000000037aa29e000069940000dd12ac000000000000343a394c0000000000083e00000000450c0000bac18ed2ec4000106f847800006c30bd20000421a632c000210f21e221a4000000011ae24b48281d9b08563d088c89420000019d06758d5501b40000e7d02560000426908b8aba26881a3cfe9800023a0711ce4d222800a68d8886294f142c6000000000001f9e8edc000122e0d3c6908000166b1a5e6f7d120800
  | 64 => 0xc800004eb0000169c000000010b909b92a82000000013340c86874477900002ee6052891c1f753a20331c2881cd1272a0000ee61a4046f400000000000000058d800000002c560000b7593610000000116b968b0000121102f22fa430e277c13d00002be6841803910d03ace15bcbc41c793e700000c45800000000000000000017a20000b8e149d1d526bc000011fd000000008a7800000000c084ee80003b34000020e117132200c78a9f945246de299c8efa28834d865ed127820121080ae4a5010e335ec5eec1429bfb3bda61350e39ace0bba3444a749e6139941e00e3380000000564071a06ae1c5215306a2119800001b3864f96d200008b30b308b45000000000000fef00005f8cf0aa45100008798f13000000003aac000111403107c68aeea1de077653183cf9d81086053b50a3865b3d2c38ac7371e8d3c5641a04608b3310b68d90aec01ef0dde0a8c06317d8225a8b24c9780003a24000059000000000643c51c800006120000b92127b000018700000000155e5874cbb80842d0e00000000000036a0198db6163b28a000003a2000000000000000000047a088488b9000022d8470800000002b8e3b143880c9c00007d7000000000000042cda480000fde0000000157f38f83e34af91fa90000000000000090fec50dc000049f430200008490000000066dc00000000000561045e000000005308912000006d04478bc7000038ca000037d80000000000000015c600000000cca000048de000036f00000358180473f820926600000c3186780000855c24507d546565cf90e6000000006ed8097801942cc129429ba25f303e19cc53f1aa343120000eb61e983fe4000069588eb348e5b752490ee934b800010c10ef10000000100f15ad0d7c000054305761278776c00004c600000c2c9110a4f40d66b4800000002c0e00010f0a01328d2818c00000003c840000b3695a600003edcfdd93ce148037e495d000000000000d1316df12001c6091f11e62c920a30ff9800000002d20afe8000000040b071613b7294241f03c78ad1471671fc10200003688000049f00000000152c7d6161438646f984c21d7400002d2ca448aef00004af013d9d4e00fe236d10b82db4742267cb4486b422ce33480e6232920aa00007b09ec32fc41d589b71d5627a66da8000000006864fb018e1e6c434c740c328211d077a1a10531084a05660000deb000019427cec2878273416a00006ea00000ada08a8442031404c200008ea1a56364c62607810f832b0200000001cc4169800007ec000016540000ccf84c325de77a0bf08c3f15b612090a4800004220400ead1a4d197c213120b9d0e47720c8d01f11a62fa68d649ac8d2a00161f9458d164c1ee290685f818e947748c30c06800011de0000f6a814c13487b3c50700750000049c1d815c9000072
  | 65 => 0x3b8000000010dc582000003ac17c43578e049fa100007d58c6c8000106e6c7000011c0264a42c8000118b351087a01658000000007c01d392b93b0a3a6c00019f934dc8954000112000007f708c9a2d10b386c180001c33161e77cc0840b8624506b9cdd812d1128a00000000000162a5b84aeb8000000000010d3971b1cf60000aca0000000067f072b1f07000000002440000274e0000ea10d50064a7b70a2a08cf13340000000000000000000083920221e62c45091059f221e74a91b48b3202a637cc0000000017a00000000000036c000030b0eb31c00255c162a22b2e9c8e9c00011d5221624a0b428da70000097402219c302b0853c7cb06fe391423b8e3d9daa12127e383cb09640b1632e45038000048a6a5923680fe2d606c906fe9d1f000000010350e0c37bc03140000000000053dc00018ea00000c40000213d2cf273d85c48000233e5f24d5107a70afe7dac954800032ac34f8fc580000bb803ccbc599b305422dac9c38000009c677c0000000488291245e321ba0000251ca43156f029c19587b68e940000228116689d20f788b0811d94042d36000086d0000467c0e508439f7c0aa800000000000345e0a480000000000034b84da800045de65f47238ac035be2095003184901be29f41cf1acf1ac20e6480a236504a651f47818a1b30568c404b804d70b502ed016384933fdc525098713584472000060b1bd03e620000000000023d63ab0a18947e000058b40000d62429c0000c208000308600005218000053a00004eb087b00000000d8d87343b443ef834900001946000000000000000000122117b204703930d7d1bcd2c201710000000000004f582380d912bb20b547c411d70000334ca271463480253d8ee0842425c05d700fa167e0a12872044e93033c220300d3a00000a7a00007b51d78348885b8e26004320a45cd4741966500005d7800008e9190a0000efb00000f2a68cc938000026b60000000085100000000993800000000000e9e16ed41ba08500000a50188068846ee2028341a6a14d8d009b2d72000000015c43e66000000005db0000000099e8778000000004db0000480a8628bf20f7d2aca72c8e6380000000000032c1f2a19b646ec00002b80000000000017de2732549cb871f2000006a6c000000013568b1c0000000211483c000001ad000046f4000224a29a2000002b9dbb3eaa4d90f8b80002a7a0000ab30ae716fe00010158bd9145c63dc16d07c128e87b289009f0e30f45c54f59051c48646f88d4796c629321258f3499e6154671f400000004504244800003aa03fe7d7400000003b7a8dd0b1113f4338466802fd000000000000098875c2d3a07b825007ec000083b8eaa83e10b42187400023af3bc20108000000044fe32a4f56800000006340b4b11500000000122907681a2600003a617
  | 66 => 0x78c2f0a000000005113af22040fbd000000003d280000000000001f400005c62ffc468515d87ae10022ca431c8e161bf85ec476e9f7b1638000000000000000097c00001d307948c080001cf544b000011b380003c92152000013a6000060689aa1835005c2b04fc9235b2b347bf068f1cda183c2fd048509513d6a5098c9680000d766d50000021800001e38272826648ba79c40000c9431780000dd618710fbc679400021c40000000000008c41d30486c0001aa92ce80a24be2800043105b0caab9e16447e65c835b16591e785de06b505260752345c76718080466569406b80002cd2000066580000a0400000000d5a00003461211856a0960368c00003bc1d3c0000000000000005c28e720a971ca071a4000244544ca0000e6b87c0331c2c3815da3f1372a113c85c00000000669c0000f77000000000001fe01c3a8b486d980001008014452f911a1c362c280000a8921740000198171312d68a54ed997290000000039094732910180800013d72b5c6838f841ae02238093cd408868435c552846624240bc4020425d156931ac438512b0f143e0c45f0dd69bb9147805acefa92f747d24070ed58f8146d48085157189d140677402bb951521224fe4ed7a1a0065435a4c541b4a04ec59f4f00200e24d25f7494380001dee000122500200b940000e1203d93c9c41a8cbe000032be0d0878c95390e7a12350fb941237462f606a005d041b220c82a01d4f1b6465310ff8000111a0ab400000004326000029a097a3aa44260eaea0e20f8624d87ea8e6206dc85711470e022f7a2ebc55a03e9043a4414947a1020aa40df4b7e863c24984dcd1198000000000004381020321a27a0000039d2b245158000000000006f3c00000003194286892f1bec41448aa4eaf8c9e192400000000afb19881cd48d71f120d8e65c086608da475c63ecfa21d9d31420000000004d33880000ca50982457084b8a111aa50000452cfa599a507c48a7062b24303bd618000000781413e08348b698c737740000ddea34909700550c260968056e00002d90e15357400002b8050b022c0000908800040ba4168173a00d48be52710f497100ecc7714000000046be00009889c5205b053b8e530aa91fd88250ccb882a04d66858bd3927122dc3d342ec00001dec000000016e643360ba08f7992b14dc8e7c12da37f16c2907468603eb04ae53bc61a00071e7a4efce438000214a1878fd324060000642cf791aff41c026dc1f78000305e0000000246a21ee52f517b800038cc1820a0f06b200000128000000000005ebc6910f8a17e69164d368148419c27dc435023c00000000a0680002d6867e80001a7d000067ac547000000008a8056a00001b480000000000009bc000006993b6435e8154c901e0620544cdc01d154200006df4daf00002c040098ee2130d176c0
  | 67 => 0x82e0d551407315e1ea40001077432000002f2936926963dd4b58869039e200000000000000082cc000000003227dcd14580002f303d78a79000005bc846c5400c0b1b800e30000237d0000000000000001eaa7834d0000003b3800003ab91dc3ebe00000001de000007ba0000000000000000000247225cc641421d00000000000000000002e608a8c00005b000006c88545a1640c7075e8e3c18f02522738c11187e3000000000349720269e0000a340a9800001a38cb38000130003bc0000da8213664d81908000083a5978cfd9ef919ec2080cd7800033e200011f0000019ee84e49d89a1c46860000138815d2d4014a0bf8247e32f40000e0280003f0c6860bed99ce20843818bea8ccf05dc69e47ac146c22c61910ed4800030c48de470f81da22b86c84e3d0c97000000003dd19be0a781f4822e1ec5413600000001b3d44dc627000000003cec54b800000003bfe2d9ca73a37b27124ff8eab901937c85944cef23dc27385904e3785833ece41843fc90300b7255101489bd3154211c40b718bf0d0402f80000ba418b822b876a944d38c65654ff1071a26ea34fc82ea14439b65b9c5b89fb42ab23f201961e240b8013a83a2813d480e39186be002d1a8a590ccf4812629244cd4ba280000204668898e812c334839e8ec58e43473c013002d188847ee4a8507d070221d8878c0001b6700005054f88000027d447590eaa3eb000032b069b0dc72be2010000015df2b2e0000000000000000a18f489da4304027c80001c9c35dc90c4e9788a2341024c045200002caa61dcf33007c3fc200004c71bc8146a8ae400001b00000387000002a5430c338c553800040a85f28000148042a405040000c0016b40b382b9050c30a051b4000216a119a4d440000aaa15e20dc0464964e0e3200000001652000000000000b2d090a807c93e9bf1472e14748ba052118ee56746b384fe00002ee90248aed13ae4acc183a2963f1a428c79213b900005d0c80100001f0c0000000038a000067e00000a2616ee0000ca80000487c45883649a450000199d0ad0a0a454c3c7c0f298c9000069740000000051400008380000000082d8bd70000336a0000000124600000000e5113f3000000007fc05b80000743000017f611c200007e724791fba0c1800000001e2028500001e4405a629c9201000000008d1902c12f20f3c00001d6a1d0000048c8000000000000000445800000005aa495c000000000000001026400001c00000000000006fe4000000004da26a8f2d0a08350c4f140000ae800002c84532800006e473240000b243c503aa0428039a0b2200008c7000039d02f08298807708f24d31171894d0000000086b10a137d43b80f9e8f160000000000000001a70000115b0000396c44591678b3e1f3a000000000002870247c0000f950000000042e0
  | 68 => 0x82cd423214d4000056737ce3f9c00003813f780000295a14d00008c5080b0d8802e607b069a1e8f23968cd8253800009ce51c467107940870812c883a21b1c5c19091b5a455214088205709fd4444000000000b6242ee7bc0a1d88ff1f9448dc21419324108000085e18d12a70728511c1d3131320000000024a00007d451bc158b00000000ff48000000000000000000328600000000000267e000082506ca1792000094c85660b8e00011510b5d352e8190c460000188c3044718021a439200001ea9931449689b4f2e8e6f000090f4000214b3aa800000000d8329fe75f00001ab923367f4416e9e7f248a3a94000172c0000000000000000a84000000000003a2e000000008f72f4c55ad085034a3c0e7cdcbb42201039a7bf8e0a0c7642000000160000000000000cd80dce00004894000078d088c00000000298224a0e0c60c8000000000010f0000000004bf4bbb06e436161d340000000122a252449a09f306981efc4ab17a809200338f37076d1256379c00001c6210c28c0c36805c366800009e0818f258c62e00cb1b680c2a79288e192db2fa26904a1e222502c2636c25a1c8140c08cb899e0000000087ec000073e1a4833650050b5715906d9824c8f41020c63342541d092c708a645e60bd03652263c06c800026fe8350313979039204ad0dd91b6b361a18dc696a23a235400000e91cb100002d4000000003f280000000011737de29041680ef433c243c877c0f56383661f8889123009b4860d1360a0d28de7bb444c815e271a2db045b10b02e8c42149468f05256c7aa496606b12d1c0000d16106c479c0000ff20f2735760000cae000000000000000238c01ec4ac48f8024708a26e14000000037aa8f2823a000016a613b400000001be20b7cae70e4d491e76080000000000029640000000032084e885f0c4d000055c4de60ebc15060000000000027447ef80e711c6000000002d88d6e00008bd105407ad2bf673781579b57053283fc02391112ac47eb86db91920e5c24c4cc2050e13fc7fd465a8b72180416081ad85453c2e46142db0c5811645acc5e0875817ba17087638c4b2ee46c9482b83f82b6224a8e3a97f52842400ce11800000007ba4c7221b1000000002da800001900f4ce430b2f00000000c2e180a394855ec469858f07980000623800036d23a90dbe0a4a0000612ca3280a814b0307c1708c4f042c5e44000000021da0000000150e0f8834080002263000022d4000000000000000e878ec10000279828f80001f1e6594b1a0000218e2e3062f812b438043bc69a893939324728c948d0316c0288c53e000033743cc0a148b4915aa0000e2f209e1aee11ecf2b92a72b3e1eec1d79ab746744508adf010a2ef670f84071e6b07dc1d6468910dc0ec80124640000030808760baf96a11536857cfb881d818e2
  | 69 => 0xe00000001c5530744ac09b81f19113683d51ef0d0f3b0c342434a000000007fbc43d000036f00000d1b84643da44a140a890392f6891340001097005e000000000001fec00001ab0000071e326c01f800020fa68e4685071420766918ae19ce137787221088180f000000000000000000000006a60000000053a000020973f647fc511e97d2112419fc0880630451e1c74d8399610cde465053600002546844c25e800019680de468d80000e2e28e0e2c800047823fa522420672d32000000000000000759402f0467260e7f5cf6883b845368a9c6249eb3332242b8082a093044e4e9475b1bb348585968309939b18da5a205558498100c51aca6e93ad00000714a30900f3b26114c7e68000000013b07ee0000200870000cc0ead0a58000003d83a51f84659000023470152000071e000021804c20b7812f13baa17e0233122c46bc4c5c44287b63e903d6c9268d7f32dc3728711a48e180a4e3cad5080a278662b840d099b00008e40ddd835a000006551ce84a4080e2e38bab06e734528e4513816fc0418192cdfe0000000000000002389000013c80001cbf00000dcc8698f2100003af896c151200000000000000000000000d7101f53f82429905399393a48000065c0bee436c54040000c5e1dcc0000bd51f900000000034ba1e400007068eb50160060200000530000072003c492798e740861ba0a820d1f36f26b3011488382014229517214bb3f487f2c2cf22b2267c30e42a20ab61f7e6a800001ac200003468ce4078a00004b840001b8400000000104000027907bd447a217e02f400010038fa93f388d8000000003c3600004af000000000000000244b000025045dc98c148e600000002108181e8d4809f03d0076e00544e19d3e000011ac00004fa0000000055f13de0000008c0000d982e506388cb40fcb1c2067c90fd0000123800000000000000004700000ed4207011d46500d2316ec000000012a0000046d4c9e0d06022685f400019cf3adc00004908056062e00002588de3181449b80000111440c0000076877221c0000000018d40906000037b036548165e88a95819200001f3844600001e6a0000c6787df24264f740000a023b300000000100531603bcc000000000000000000000027c48c0c40e13f1000000001f001a226465f2c88413e1000021d8000000000000c8000023fa0000000000004e100008f14b8d16c80d5a1df80000e260c6a5e0c00016bb00000000000240035de000120684e610288cd03f414fd2c2e46d0ec0160d02e861509ab196c1fea3a8c28b9d29216c12cc335a3ee03cc4624ecc839301781d851b19ed93d1883a11d1a13f2e2e822c7728efb10780d1c5409e7e2b381844dc107b928868ddd058141d2bc407a461695a400000000000021945a600000001537318c27b8000240a2f803b0860b
  | 70 => 0xc838600000000a7c9ebb2e766f5112322132dd8000000003f60a3c90a0c1f23d5370210ecdfd00001528263400020713a9a0000c1814fa16b20000fd60da63d36307460996e8000000006ba8000146473bc0002235399c0674fa0908229a025740000b31000032942c2800035b87ce46ea9e04200c5920d6080ca237285b409e184a215a8f5800004233e2800000000000112c2bd4fcf0943260a77e40000dbe348600001c90fb9444e2d706c9800022083e30da4232f15f018d8b2c100c30200000225178419b4000000000000d001360205800000000000000156100008f1000013be000067b0614000018e03cbcf28800000000ff496003851f5c19250490ed637e4817c3d30f3100000000000224e00004984b0499d100006a540001c4d249c000000008c534fe4a2877d012d13e0544000e1caa2b3600003c8a2f322bc39680000e58000078a4c5f1f822dd4000072f8d52295286005521099265029fc5de1b9848e200010dc009e0f167b00f179ad941d61251102147945ac0000000032700000000000000004a29230706800028be000107888a7459049cc959154f31ba3420b1e0752050e83b48df148c255a53290aa02b1173238f40c31b2f3ad26cacb3194db086210a9016a06e199a573c5c9072c3c1200006b78b3f23c230c09c09a0603c862f4d789a3c2d6c00011e788fb0000412c4e0929b00008db8000000000000000ffc20cb32044658aa60147000036e0000000000002200031a1ca0efa0000759198210fa1824e798000079c00002da1bc633c08dd45b9845817d40000c4b0b2c485600001191a3f143e00011ca00000000000000000002e981de871398b10000000027a0f9103826f246cb0b7824a4163065d000000000000000203900000000efd8000180650a05b400000000712cd751d3a065287182eb86232eb67ee441a9b1600000000150244e2476774800000001fa429e042787d74798080ca169f502c7c6a7893c969e42c4197cbed14ea3b6a83000000000149a5c44000122a0dc400000c58d7b2ea0141c260901f00001a800001c2917882308ce094821e308f090908d3b1dc681150361c5333a63e383199bdc18b41b8ce71193d436660a0aad958d1d5c2670a2994ec12b887bc9758dc605c04a5c8a09e6a05367a18d0110811e225358e7b804500520ddc0001dcb11968b1088b80000000289518d015f0000000000002fd1e5c6f08bfd1e231e244da0d24000041a080b84819e4500007dfc8609de541c8730923a8a1900005ec0000000012185ee041720fd2ace000000005303f364d70137a197000000001e380000000000000009ad41cc318400001e8000000000000d0e00000000e0783d200000000f82a0560000043c000171932ec893433c800047b02208000123c00004910000000000001200a991d352be
  | 71 => 0xba5850631b45b280001ee03fbc0000c5c833b12e65fa8660842641326fdc36680000000704c95f94d845e259f051503c036262060e5c12550000000000000003cac6d5465f8d16273a3c8d004997146162f1c8f296bf34622154869000002928f4c5060f080cda12a86c708ca3ec283544c51faa125c0000c6724040000790c84a9e391ece1a3120a0cc30c9472e8df280003a400cf4fb49e6346da7cc000002ed006a0fb0f94995204405354c809a221bb21f9c4ff9ba706a2506c1200000049a4dd8c8000000000000073c8ebb00006dd0b8b0000000000006c4a434000000002ca849d109c7f98eb0056c45788af8fe6095234a42a1c0361506397800000000000000000001f9000000004c591c31bb500006e3cc1182e427a278ec4078b6328b089e02a880002a3c0cd8e57000020305e9400002252aa43cc8ad18878000000000000966424a91991ae233b00008020f5e20af0a9e74d8f238000000000000b6070700004f4869816f4305c876c5af00000dae2cd40001a28000025c8a8384f5000000004b398fc2412572c00000003cd0000117b000000a834cc0000000295800005ab1d373ff4446c6d4837f47fa7b1c0000c7d0c1e82845aa02e900000000bf78bb50af42e704f51c513c6c356020c14bf04ea8ca87b48a6833527798fda9f6a09ba2c580001f8718dc521462d9a67378a876820300002fe882b43980e87461c0000aba00000000000103c0000302e27bc32a94cc419e1dd096e1c3003320c442301f7721760000e0f80002c160000bde0ecc000000000001df0000005d8d01895a00008900635a1550cba6c401ffa0f226164aed02c982124426768584a40f34f000dc65e001b459c2df8ba904c53a22485ca8980000000780c7838ba038102364000039513200000e5f1dde0000463472c800044544628000000044c28f200d491d21f863b64f52884540022278c3c030d10486db8396971d375e84986b918e50000000089c972e0000592800019cd00003498f37847711ac8d98ada203a00000fd08068830324a8e88b388b7b0b4c22ac13c860b4922248823b1a0f0000839ce79000021ea00006dd80001ce02e94000050a19aa13ac0000a2714ac863800005580000000000000003c200000382000039460001196887e3ae4040cfb7a0192b127aad185132940fe500cc9a18a5346c000000000000000894cc132003189005e096f8ea23d705130a2c9e603590253c69e9a3837c61bf44741c61422a7ee8d318b2719c09100ee3a095380c5a8ce8d18e6376e41a4bea1ff436c810a4ac380000f584b68000000000000000046800000000b885d11c762c3e52a8a7a8000102c8014b1911fb3a3809384431ea316a200000000c571072505cefe07b5482246c0aa4182d0000909919996f515988c8c0b30b580114000087
  | 72 => 0x5807c628724f340001e48292c86f5173132c3d0a3a986eb87d30ac200011469130241c2bc0000000000000000f0c153438500000000179e1a9423f000000002f1e30e8141102507b647e80001e9729b48bf8000168f0ee04cc4000208e000069d80e3a2b300002b240000a4c000000000001a2300000000aac00004378181c0000000000000004e20e89000000006a58000000000004ac9cd50fcc2ab89f3800030ce0000afa00000000000000000004844473c838800000000000cc90145097c8d4ca9e0000077463700b195803eca3e14507950f3a1a25c4000122700001bb12321e7c41388864abea07a18400c4c6348799003e00008948000000000000000a9c0e905fb41168c0e38320000549046c0a363f64e800e90445c1a9d13794140000050d17e1ebd14660000ca10d001bee78b807e90a20000505800023950000258112194b63b400dac0000f9b000044ec000000043f80000d471c16308e5cc400012f042863db019111990c7a25e482b151919be3b2c000026e2daa340511d949500000a9c0000135000027a47de00003e6a6cb4000000030c800681ee8296000000009c195d30f360000fc29d7627960000f7d9da8459420ec00000000000000038682592d34153871d8cbd17a455dc74715051f620bec48f07c92a2e1780ade90c60000000039505a2077c0344c9d117734a6186d193921237ae4d80f561fc022920c5494e200c16f8782ca2d874b1680897074d00001d7a000000005182d4c6a3405393d0012e5484dc69dba4506384463d8bff1acc06780001890160e2eb4d30918f2b325c308ef053e46b02ee0000010100001c945ba0b6f3fa480dcfff800000000ecc326800000007de46a30000191a5fcc8551747091c0000d4a021527ca061cb601442000051d4aaa0d7900d40000e16124000000aa400015fc1bdc64c11078a0648368318f0d12923cee89109aba0f43b240f7ca3b1dc003766424a1817cc20ce1e70b13168c1af4059c57f0000198c269c90d016f1c96000117520290000000070b868b00004d780001d91000000009be8fc7337617344cf001431760f14d80a44f40de0000e8a096d07ca03546e2911901b647b000011ad000081043a3800000003604268a25e3e580000392021e42080000000155e34c00cdcea580001b360000ba0800031f4000000014a70cae837860900321f76000000004c0185e480031d0481234e0000000000000000000e34126015343730b9c800018e400006f300b0488e0000dce800036144ec918385d33d603ae878a8559152613cc92897c3358009a47d808e500006bd05698000000000004e3800000006eac53d80002bea06e81031ccf388a423c9d9a0d819e48b000120a1d43fc6658e6913ee1006724c44a08aa21be4c10b8f8000072e0000709800045aa687c000220000
  | 73 => 0x87c44f5011800041784a051540000287c0000000002821680000b92803400005334e95974d02f247b865581f22f26457400000001b40675c000211f25561d6923420ae024676dc4de94f400001dd82ce843f20b65064c6c1672152a000000000003d7c6198ca30af64690189429799ac1510501500591e8310a3cdc90606a61d868908eea0f1b294c6fb8d6380001cb65bb88171ec82cb6503cb4b8ff013246e7c60aa311403a27880c280180f70000000008d51bea44c80000000158838f8afd08e40d745fa00e492d33e7c4be85d610e71c1217d0e9e936d0b5c00010ac8eed37682c0c000032f115e339ce05992427243c04a8b0baa214e69cd0a5119d0bc21ff48c20711433000009ed93100fc4132c9641d6629fc000062700b51ff400006378000000000010e71a6b425404c09c287280000133400000001ce60001138800025920000000000003ec5d7400015d100001750000000000000370e808fc022e60348000201a1d6807cc0df916f302c1ae41989c181848204cd3809cd0f5667bcbb285052fee0000f8b015b000091808a7125f29448fc85f9000000001a690d180002bb800000000000000064a000000000000314512c8e21346a00000000e0e31ea00006c200000000000078700003bd22b68cb590c93ea678fc7d2800011e41100aa880000000000000012831f3e166c37306d3421c471495e80000000515400000003218715c0001eb6220c0c74f2f10f0237851006e792d5327c3de47b0233915200ad4b12800019b81c0400013d500005854a2e0171373400000ed851202646aacfb708c01462804054620460d2a173c2be0000034600000000c5030b000002191ae1428a2f7ccde121e0000374c3ed228714bc840ca3705f747f837103191ee448260000000000031e20000bb600000ece0000b8916d82cd819f883582493e1e168c21391a8196e809804b05ec300a21203f20b01009600000000000273431ccb5284560000047c0001b7f2e4c000077e1de43d847ae8ba407dd2d062184beca2f242804bb8db89c4a0c7c2f6c729050d2eae0000f940000000000000000000051e000120c89e1000006ac5410000000000000000000410200003320cf300000000000000044126ad846fa27e00007d309da152200000c7c9911ec41c3076c00000e7e2c420af0a4220862ccc8cdd0ae88712ee80000043907a333c48581071e193f4e066c3ba800038e801c4c618c26200079ec1a01ddf353269300001d87132208e8336247600008ae8c2ca35a24688c240d011ba358a1994349906e17d646a4000144f19988144207a4182eb44c00024199937248834bff815207645388e770eb13e1a6c204d499a137c212b84109c8b217a363000009b30000104043300000000000057e80003c8225180001e9e08de3f5ce3600003f841edc3
  | 74 => 0x3e941f58616111300008e8000017cd367c000085205d2404a5ad44fd8000000000010e08000000073651be24440f907a9c0371cd037e63dd8000070e3f667c28adf980042026a483e111e22a2830a4d53090e25961920ada82aa28a26ca0cd8800011bc3a589280ab128e470b8f230000097e525ce0e03fc160a3d1c7f195471be800487930aee00007c300609cd3236480f4820916820362de40001b412686000088617b700000000000122324cc6b747d0a3122b72113002d82ca2756000000000002b8a0950000999b0f8a7f1d1300000234633e498f800000005d4cb968a2400004ee000005d60000859d1148000156e84708f682b617f42860f138fdf1cba0000f751abd04b80000d49800042c0638411c80002c2678c000005860b56604477094c300006d740001f5420502fdceb405b33abc0000d029a2715bc4a0800004873f88295cf4e00000000214ca409eaf0f0e8fec000229d000037a80001a5f18d4000000004f800005f0922195b22e3c8898fd7a1273b645d100d4000000000ab81b489011a281b94b35000046c207a8000081501567b4c63222e13e1239d40000e5436c055589e6000011b80000e1d800000008b68ed88000000000002c992e7475a264d094085900002f140618000092460e0000177700002fbcd6d1d41053e0960d5a88f0336c60c90858e2d1a38000000000000000720c0001205034e15cc9ec08653a4480900002335331200000000000300628d0000157928c41c98722036d00f202a84bb8c8b240e13fc22a8aff227e88308ad9318047a07584c59fb7340882f400002b000002a3c000173c382403243e58533173e88dc45a0e9c47ba249515619ad04c0046c0000920228e00009ef8e4907b0180cbb5941f2ff28bf47e9a0c435cc2d5491a989300003dcc0000000000000006b8800011a04fa02c0000025d857b49ea0000485c38205d900003c800000f328000000002b0fc794132c06000019980003ab86724cbf8fdb234a6a7471c16cf332600000000698217201406dd02ba3d3255d4ac5014b2318409d064098700000000000042d224885bc000191a3e7468810d523f8145a4d089f818141b2a823c0000000080a0000e9380000fe60000c841f681294081c3a8886c000000000001009000032744470000000000002c68d7033b83664a5285fe3e5c4c5102606a50cc01ea004c8a2f2ae4179ca489944085c3cd0b84047e03120d400000de83418891c45b9bc344783790800869b41846e780000c012c021be80001e02209e3f1416e0db900000720e581bc00000000045c95462602209c81795e041487c9400009b8308c53801cd9ec91b3a0000ca681dd0c0a2b340000000268e2fa500d80003c380001116000011c001e0eb98849120443880000000055870410ac125c460235586ad814f0
  | 75 => 0x153c74b43a480000000000000000250ccc2a94d2480000e74713800007d022a60238c77a2513ea400004cc062825840000add800005fe00000001d6f000000006b601502fd8000000006a246a016fc6511cc343864c3c8aa800017022aa000007bd00009255242824834968734000000030d85f1000013520000203400001fc021a575505d8ad8123642cc83a96d9408e1ad46da898900007f0c7ae0a793d480f1800023be368a07540dc0bb125ec87151eca487275c29a857485af14b83a350561f3630723864f6c1e70363a0d78ce01acd43ce191cc16191614e6158ca419860476c3f881511680254a0000952042c468286540000e1a423c615ca3809a100008f885eb911f3872359447119a6479628ec0001d8d2ba40f9c12f1249000000000000c2200003298000000017ac00000001a5a000043e8d33000017506d84b078d80278c49fc64502f148ca7f3483c0ec8072229c118a8dcb35d20000e768d68000000000001c1e302416b0b68961223f276fc0000c4222587540aa99d4721560b0c000221e14de00002d29033298a5fac010874f00e8776400016e5157044d80000ede1b628e640231af7288200000000000374083f8000000025fc248c000000011a465b47dc16c91db476500000000068834e419223b314c27d608ba987315860000649a085035c365c3fa1bd917aa419100114de3a5c7418a0500000000829825a85970aac2ff8b9780001ffc20fc17912a83980000000018ac000034e82f59f03000018400001243099800008f500003c6e3eb40820de20de41acc000140e088600008a285d111900000040228c00fc0000000000000000570075125b0000000016782222950000106d1c1500002ab4a1d00033ec80000f04071320e47410ad995de2ce60510000221113d672344169a110166090d030988300006d442fe1c4100000c6c70f06f4411a7e24fbc1f2327b445482de103c40ec59a1128041302425c349d19a100f64363cdd09ba929620000389022c443054c09eca19123987c840001914179a3c3000000ae000035447d100000000000000000004384682c69e079d29f66f282b7037e000020b08dfa2921bb45aace93183b159e0000e7e19c50a7402e514f8000199c000000009bb454a09fc344952511f40000a7e0000159c000089a0fa400008abc000000000000cf00001d512d88869060d88bf2ef4245c58611220c5c644896a167f0afa91680000eb90000000000012cf00000000000085811d48cfc00000004710000000023450000000000023ea00000000d2f00893e6407c45858aa0000000009e503640000000000009050af03590e90921f0808805093c028d000071dc42200003e36000113e0e5c1c721798f7b8ffc0000000004300003cea74fc000175500000000000000000003dd0000000000007e80
  | 76 => 0x8f160b942bf03bc088aa03308c65aa0000135d032e5fe0822013901c06038d0088ce3630000094b14b03d82046053b80000ea05e58346915841d20000f7880000000000014a233200000000660049120b28bb01fd19070000000035e0000388c17d8b8007f1049682c49f90000070e37ece3f0f5a481c1790e70027d3ffa2e1c2179bb102b41c88580003c11ba22400568b8f2d0403900461637295e7a5058304d40a5a2270d9ca2e227782d943ec845741124aa893393ef3c0a862c79d800000008788000000000001be40000a3639ce00000000000000000004fa800021d6235001d937c22d67b845711e7346e200001180c1a33026268569168100000f251de190330d04c84df59f270508601856111e4000006a904191e72e560000000008f32b4436d08d1d700c9c03e0648a0f900005b50c5b9d7148663d406afa2f00fda5e74c1f93c003c285d8a80058a14c08e002ab98a22694787c82f064f3b4e0a7000023930000515c0000c8f0000000000009fc34a065f80000000000035b400000000000741c000206600000590caa96f106066d947200f990f540001036836610ae0e2c6db1b8800008d58a5c0c9a27607c0400014c7442c2f9ccf409ce3e8639051fa076b265e69f04588ff40bd47e5c4f01b4f00000208b118a1e00002e68000026227ee000017a800022d27a04000000048ce89a47538685483c8c1807300001bd87bb800006a43e56752076680cc00003628d9a90cb32084be4000149030e800010b49b46291c189800023702bdc244020b240942227474da80000218850b04062436297c45f8794800021e80001228169000003b7c2592114000032200ee0d8221a285b0dc59eda21dc06089a09d9730ca1c1922c08f9302a00000890e720000000000017810d3815400000bca2cc4774c0000000000023f800000002c360000bf01b940000373400018f21fd68a50dc380000ed200000000000000049e8a799a1b1458272cbb819d00000695c1c68000000052b40000bf84498117800009c6083e00a8bca000010322b94b1a891d00006c100000ae400006b4c00002fc0abc1b74c701a7b2d840000e188000051600009dd80002b4e0000c2a83a239567facf2da3d4471c2cd8a300a1500002da4cb9891905a458c020d8c1032f21dfd09f172100008ef43418b800000778c197059810da000014f000000000000a99800000004680f2a00000130597cf800a1700007df4df800001ed066e017b08462e0c8f008f48e8127b8474c000218d000000007740000284e6ce0d4d0000370020205e980000000710873413880000412027ea3e30000000000000000000000000000003ab00e24164a07c000000000000000000039c4e5e8000456061e4ec70b4a131000000000000000091f400000000dac70d400010e8200e24cc0001b17
  | 77 => 0xe36042d6c8471b2c0b4e70f05089fe5000000000000000061026e84d40b973cf4151d08b16de0d9073a4e42a3f000f4022029c8ef909e2000072898f4000000000000c783b12808000014332db67b6c49e8000402c00000000a160daa00000000000161a15a0dbb06d043ba51ecb3d1c8c0866197859a0a201d6a77dd21e120d2b266600c53043c14da8e3ced684d31c4a4768000177900820000eee800021522a5849900000000000081a18271152000026200000bc6000000014f01012000087215fe477668e8866890414e2924c7a187a3110e2fb459d8ca800000000000073f1bbc073cbeb84420fee1bb425b0549000029900498d4815645ea498111262a301f3cefa21410e3c0a682cb00a00000326400008ed0000000000000002b1800000000000361c212ca33034e000078890f6918648a87259231810e01421c249dd144a224650b8f1f00c40d3a2924af597c11fac35f8812176a1db04a00cdea1d626d83fb514496ac213c1a282f79a59265a34dcc6f055c40d06204071207444923bd4e4a9d643426723d069822e00004840297000011ce6520000136f483e737509220e1403837243aa932b17664e90e2186ee15085d9c02f9c37000042d47a9938b208042dc5be8caf0b521948027800033c600000001f2415ee00000000000000037b4b26a0d70c427248cf69e62000000007a8a2672e700a043ee1a2a1f343d5000024832adc539410b837c0a767e04fad147744d669c8a64800040b65aa8a930e42426821d000020730b3437fc1ea0c650c5682d0b74901500000b3000023303b4a685043b9dc6000034c800019d6338e0000000094800000f34d180000000037bcb43131b35c80be8099a0980eee2a14ec51703367883d822e8a13354272442bc921407841b607db17e9220259bc000188721288430000000017c26c7cfed80002cac75009189d7701d80a4c2ca000009c62d08b32000027182b190bc194500001c9c0001ed000008e04f0ea25d0e8610dc00015a2117a00010fa08d1092a89dcdee90133eec5e1c68c870800605d807d5939403285df4d7c000007486950ab6246c2162241c00217b900000000d7d81a60000703842b16532100244c9351d33000000009fe041a0000000086a94ba1a621ccc53d1e2a244c8c7cdbf003d35188ba4ee50dfe08140f591e3149e04366c48000000024ae2468000157a0e8c72bc182a1d73dcc69280c19dd11450000093a000001ac02eca521ed41e3858e87241f0213b0765476d85ee0c8c227ce400d4f099e11fc000003900004518c0e228400006ac000009e700004d40f6686e13d240000b0611280976000000003f02dae3538cc180a500002e20bd68c4a00000000511185b0244000000006f338b847d5028072943b800001eb800031c60f050ec9536000006e48fc085e0b92742
  | 78 => 0x58e85994f28f885ac6f580000000000033d80000000399c58d8000000084d4bcf8000000000000000000311c000000010d9000000000000283290e1984a041f2f10c042205db8000000000000000cb108d43850edc00003f6247cd1ab991e40e4652c9fa870b071c5e7007f813b07da86f8cee87883e8a46b05c80000162e0000d5f800018382d1000000002c388344ecf8000000073500000000192a32d92298000000056dc531937845b20000000115f0000000007901b40234000000008ec00000000a2400000000000000013fb000000000000000356800000000dc119ea2fd90db8c7c000000000001f3f19f049a11399a893dbe72947cb942b07ee73e491499ae0cc60b500001bd800001034cea08812aaa000000005f5000076f118b09b4118c71a8000073b00000000cf21d30000008fcb71849728fe08d000001b228927a810088a74000003a50271e8800002f809cb9c6d2bc63f051409cc8324c65510ef8000061445e879512f400000000e410e7647c814587e6000034e20000000000030840000f8f218f0000000045696f323fe68c86ca1c34206e03a05dd86ab2e7a2ce09670d4903c60000000000000008b740001398000020d8897016a2cc000000000508000000000001fca3d680000f8e19ca1ff20000df0000c2ed288c435b85ce09ec43fcc9c0aea1e00867cfe7123d2bf24270cfb05f221ae5be4f53079041984dec7b300003b2c5fecf79a2e5236e6ff405c232645ce7588ed18318385a3d88e28205746985b04aae1e783d721e9055600de09f82bcc0381886434a8d3d1ff9fdf299c52602a181fe2d266b943200d8b23382b1cbdf8c0d268c748c7a01c07087a1abc8ff1144016e4fad2231853258a5bbc0c9a0f304423de0b1e8aa615c06e2400019bf2bc876210e99aae1d7e00000001b2000000000c4f0dd62bd01ff8ae09523416441b4ad7a170281875845b702f4389031e894d06b82e0a8c6d20407d40ad62d9000023e706f44e00d8aa2b12ba02884aa1800017bc000000010fc3cb80000000000042f458a411b9c1d203a30f824d9e89312e24b01d8840300003c111f290cf00006544915903a359228e88118000052a46cd18c06513b9271680160ac500007dc00000000388819e887d800046a200000001882428c1b0400000003be44c9000000001f3c00005080e913e3e83dcb202275118e62d84ba0fe40ee277e038f89612fa04fe8b5d23f9452090e8b9b16912334292cadb2482273e45e0c420c5432cc75246839ed71ef632a89c200161fdc3b00306820525581d8ca4786871d146bb09fb1e83105633e88fb09a304fc57d81481e4c196058000e823e82a3a00003101d3825168b151568ad624848b7c9e4981b1d1e6dec57d04a90af67db51f602f824b41b806828d4741b88a00af313552e8055e120b1b8
  | 79 => 0xcc30be5118d82a39844280f20fec9c0d3faa05fc68a9cc11dd400003e50a37278e8ff80518a4400000000ddc0000000021006aea03c00005e64edc855b29a8078000022fb06ae80a863a0ce9023a000067a1c8e157e342d11b16040a7e0000c8e8a3f00000518764943d00006e4cc2288d8171614c81520000000036b0d9f800041524130b2e80001e1430211771208300485e4000114c00004198b7b01df000000000000000418a00000000000000078d000013a921d411843c209582b606a44b4a000026144f90936800030327c60000000010ce806030c977f058c0fa020022a12e745db4493800030b4000072780001ac600005df800034d4146840580b4202231802458000000059c0e10000029cc00000000000000013a400006533cda492000014bc000000000001b971e1e0000692887934fc00000000000000084bc0001d5b000045d86a686ac10861ec0eee0841445e89889c5248140c421688f01efd00002b98000000000004ce0886800021d26fa0d3a9b9b000000000000e6647da2f000000000067257a48e3888f06b086d4c69a2b71be06be4316903f4276733491989be0b760154ec797d60f422a752312328001e0464a0d142503f25090844941023c6170d0268cea0e3680bc000000000001690c48a2ff0b0e1604965095425262c88e6315da0b980000700a26821165590643a0db140020003789aeb42563640e249714208c5e3075018d743d4916c7ea0f4907c66af9190129016203e9811f00000000000058f246e2fe41aa049a8e55482400003c30000203c36b831106bf368653000001b141bb61b6c00010c23ab20000796910e273c895c33801c0426c66304bd8000000050d416b837b098e7ff800023d100000000e92984e000068545bd020f00005adce8d8cb300009084674085d0c48770ce8103ab067c220c0c7075f293e24dd0a885f02674456847887053f3e272063f8dd216da000041d0000269c63b0000000032b200000000662000078284bf221f0000000116580000000447400019cb43760000c35161a317400002461a5830ba54a87d9a439000068d0123000033c4003800000003128000112d96ce0014109456e9ff62d5a8c7096b93bd2a04645cb0c9bce439e3dacdbb993f2a508dc8b5109f13bd872b0a5a1053237043740fd81b70c1c33b867d90de24408fd43a500951cfa000026d899413b80430fdb012833ce607913da20a000055c11da0000105e000074b9bc4058871ad00a9ad40000768400017232cee0800f320bab0000000002c8000230060c4000093800002c9800005da385e6fd8d5900000e6413dcd168ed72d2a2fecaa81d7e485a6094d9d0061449022440328f3630f60840f510e65165c2ff1060a3d71c9439b0dfaa308355e0d884ad800010047464da6800035785ed89fe89d343d65b
  | 80 => 0xb18a08722144d882aa9f6034c866c80000c44318047c4207204a335630e0bb096a7338c0750d34924104d009542b100003ec62bc91a11ea82c7e329c0001807232a55351d9243f3b5c367cb938a9f40fc13e400015d400002420439834b2fb8118804e202c0b1065244b51f46374c9218e4a0b02365c00000001b5b18aa22843fa8000217e15f8ab694b7000000001d1a403332a11e88560000000000000000fd0331a412400022f80c9803acac898443ad68840ecf248a375036a878e9eb743183a14494809d186e33280000449288a0000449a1f00f0a325861aa07d00007f1913c826a22040000000027742401640d289c02264c54ec39ba1f238e23f943da068110be3d5c98d04df0bb25a60e8a82670b2414040000a75173c81d4d42148a2c9e000110aa0b92f8e0dbc0591c110a44602c02922a443683634e7d926c3f1010891d49e382e84455cd719444476a30c4000000034320e58000000034240000be79c0c1edc5e2918f1b9933aa48704a61d4a304479d0d4c1ad12b4283a8c83067d3a583760bdaa044017400011f092d0096e817066c18a700005bc86109aac468845ed15e92e50000398481f02d103f0149c00002700de0319c7a4000024b060d00000000201c00003c919370000254ccd19b533fd00000f1080000fa24ba0000000010f85dbc2df0e0b09f62c510918b8d31f08b6c74f9cd800000000000074248b80000622982a0c348d7400018b200005bdc00000000000098c0000ad743388348e44876c467000000000df800001f60000000000000000000000044e4000048303ea177a6e944e886713f4a3188000031a350e6de87aea3b80ca826fc37c1dc800006d2c0000398175c0534e3109ed082e8814e5982e329a62b2800012c310c86538ac70000100a4fb4ea204ab333a0000c3a9e5220a2395c6bc0e823c963f789799645068c0000e761e8200004f8c746071c000067a80000f450cd217e474a9afe29961d0040b8f3838567c980b4976636c40000000156a0c540000fc88ce600000000000202200007aa824f000000005190a900cc5000000004ed00000000323809c17642c0c00004bb120b1bc0909473a06aa0d103224b2e0ff712841bf0000232100000000690000000004990334018a3e08000022d9e2043f04ebd0d100cf3d168b70e661a8a28ce04dc24305653d5c615877391d11e2e480ce2e849c0000764104400000000000123a196217e22920d54097814ba291ccc40b3d00001fec84e8000000010d075500002c7206307e484592f461a445a7000045a838a000022e041200b947868d0d0b5a000057e18c82430318c1ff000040604fe08a69fea18820d3483187362a92050889f092f08dc62d4730161e46d84964411089502da55f91121dda0bf63571161854a209a4d9c7ce223406923d38b6399
  | 81 => 0xf873fd87358000000003b2546ce9a0000113480ec00004ad47600000d7908342b902f2d02402c2010a7dd08b51a5b40b42e6018c8833038610d8f88835d28641400bcd228a377c0c380bd8000213e1410000150b00003d4860200001cd24e8000000102d78887004a000001ca3ef4e6f9c04088a19d80c200000000000122623da0d8c6489034a48d30f84350000009f1a8281e400009860ff00000a960da20d2c3ed401b13330f060000000000036b000000001cad1f6452cca6f8cf119ca000011797e72a1222991d2a41c29a46efc00023c945541a7c6a1874e0000275060a17970000000049d239b00003e9c2f8995e1fe62da90299148127606ccedb002700001e80000019f353802c51168000000027e419c19d2177c10508cb85bd17fa85ed0c2800000003c8000298e820c473fc000234a347c0ac88e70f98465882ac5c8800000007e7481599f727041e683689aa701f400780001c9835ea16380000ed0233c7a0081b18f3343c45f47f0800048f81e242641afd1c1e5758839a26a186c7efd0991c5f06be42342b01a170a707e4cf75800019de00000002435257c716cd74144716e069bcca0833a270c62b40000a510fd25734445225a25ea7ef4fd1162a3448000039e0000000020c400021940000000000005710000000000000000000000000000001cf80000c491cb52a1400009af9b6f39763b4c0000000000000000000000000082300001c9d117465d0f1a9ce620be06840001e79000040d494219532ffa2d0c6049fdd075c3f9807d800030a44dd03ae8ab000ba07f403b099502ca8578b700212473856180b4161140248bd5029000021ca0b200000000076a0bac00015762a5e33fc49f800000005c2c0000000000077bc0001de233ea5fc4d1d83711e2675d514c000035aa7c54000041900006fa5052898c0b823c78f4f8f9309b8075c0000a044460794c36c83e401f289e8073967b19d800010cd11273fac00008ab11092b848948f079b5905b20a20244845a034a81ec000168430a271c8375020b27425b70318863f35b049d4c3b07fa10fe72dc7358000000041800000b83095e0000da11985109a7ee11a687532c140d20cce03e62d981fb896e8038000000001b50000226a5908916800029c8111d215131c000000000001e720000880c000045000c88ad4cb515db387077381b19aa40c5266a8f498000134c43287a61363148c405c444161622305234acb0d272f0409949e780cd42d002d89950f94022a592c611867500001e94000000047083240f6b21f50000000000000003f608d54000155a1ffa00000002032066a54c47678c271632287032c8000362200007bf9b331a52000000003f909a0000000012ff000076b079d0b253d8c56e00000ea1312a00007f50bcf43ec7b2c0001c01262677c42d015ec0abe0
  | 82 => 0x3d8c000219927223fa0fa380dd01846c0c0000cd00000000000004a300005b40439233d00000000a6e017200004170dcb1bdb3df4560860615032df003c021080000000314cc95006746ec483c4920c66000080fccff0a0b00000d84c0c12062dc4140cc3493932b4062d02ff862c37fe049400000000000000071d1f8c3972613c61d979b000027540000000081000000001e010000708800000002b5200000000000066852b91c106bd1e0c22a0b9f8969425258383229de726722498a71a3a626187f24ed31170412257bd0fe912f179022e0d621afc013416a8502a34e32d207ac0000000000077580e59e9a00001078c2f000003da7514d6b8b96003a100482a243b00003e10c390dc3017e26bc362a0ca04f84724576000003bc04800000863464449acb8103cf27d2661ceec00001a582b8c461a41005e025b0278000036b80000000000042c20000a920be421ec0000d9900002f560000656881f172a00000000e6a327657fcc199306074084dc0df0e240000000000000000cb400007961272427852e44fb0bc300001ffcc1e8e2f000032b8efe80000804000030621ec42f838480001c9b00004810421076a42ca71c0a969eff40e01d6d24a170f156a17b400006da00007f60da38e920000000000022230000132823917224070253901a16da08e600000000cc8311e04e910594e100008e688641f402d1a5a9000000000000299800001c235ac2acc00000a4425a4760000131500004ab80001b30000075f49b30000479a00001c0014013b6921074581240000000009500003eb600007b2844400005ee90400f2b0000530400000000000516800021d4457e2434f1e189b3cb0000085418ab00000000000000000000000db80612486e1d780001a4f00000000c898d1018ba27e0000103d000066e4edf21740750408800017df1be441e504100003c6670f4b95066a36540000c7f89c046787b941cf881d000000cc00000000000172c2f9800037484c485c21f59000026b0c770000000068944b280000cdc1904c0200003d1c0000cf805232302773c90c8eee42b65d508b3126321cc5d245fa844e18b229d91759c6e2a1055751d218df22867d5c37b86d424a850fc95a800003c400008eda2e826d650bc0000520000067d122b80000000320800000000e82000000000000000517445180000000000079f8e3709a4536480598f609c465749668
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc3c649d740440950f90cbae808801f0f19175d01102a43fc3ecba02200087d87d9740440110ff0e32e80880021f61c65d01100061f3aec9a022000c3d75d93404400f968c8b8e80880127c20676901102a6b938ecb2022000c7a761964044095ae4e232c808800e3e219749011003d5d436c92022000cba76d924044093b64e3b2480880038ed9464901100071c328c9202204dbb08119240440a3b64e232480880027c61e5190110004f9c3aa32022048bb084546404409b7630e20c80881276c61c4190110295d9430832022049eb28610640440a3b64ec20c8088137ac9d8419011024f99428832022049f31851064044001e66ca20c8088003cc194419011024fc9418832022049f91831064044093f450420c8088127e8608419011001cf9c3c6320220009f3874c640440917610898c808800e7ce1e2190110004f9c3a432022048bb08448640440010ff0abb280880221f21576501102945fc22eca02204ac74711954044093968e3b2280880031d19771501102a63c3b6caa02204ac78761954044093970edb22808801f2e1d864501100071c328c8a022007cb87695140440093710eaa28088002ae219545011003e5c3b2a8a02204ddb3741c540440013e50f28a808811f5c1d65150110004f843aa2a022000f31545454044001c70ca324608800ab620d628c110024f943ca318220049f28710630440016e30a20c6088002f460c418c110005f0c10831822000bd3834863044001bc2e490c60881531e1db654c1102563c3b0ca98220039f281dd130440071f10cba260881272e1db644c1100074c31ec89822051cb8761913044001c70ca32260880127621d534c1100147c43ac498220009f287945304408fae0eb28a60880027ca1c414c110005b8c28829822000db37410530440017a30620a6088002f8608414c110005e8c1c429822000de3728853044001c70ca3244088006ba2096388110024f943ca310220049f28710620440016e30a20c4088002f460c4188110005f0c10831022000dd1734c620440017c70498c40880123da1b71481102a63c3b6ca902204ac787619520440073e503ba2408800e3e219744811024e5c3b6c89022000ea862d9120440a3970ec32240880038e194644811001c7c432e69022047978855cd20440031f10eb1a40880127a21d5248110004f943ca29022047d707594520440013e50e20a4088002dc6144148110006d9ba0829022000bd18310520440017c30420a408800374dce3148110005f0c146290220608f7815d954040071e902bb2a8081323ee0176550100247c402ecaa0200487c8759554040098f0e0b2aa8080122f21d64550100246f43c64b1820048dc8758d53040091b90eb1a86080123ba1f32588100247643ac4a9020048ec87589420400199865bb26408003330c9764c810
  | 1 => 0x50e326a0881332e61c64d4110004f8c3e83a8220009f18710750440016e30a20ea0880036c5d041d4110005e8c1883a822000be18210750440a10ff0abb2a0880022fe11765411003c5e422eca822054c7471d9550440a3968e2322a0881378e14064541100063bb2ee2a822000cb464dc5504408f8f0cb3b0a0880127c2067614110285b840eca2822054d7271d9450440a14f30fb28a0881531e61f65141102871d3a6ca2822050e3974d9450440a1cb4e7b28a088143965cf651411028735396ca2822050e6972d9450440a1ce4e3b28a0881439c5c7651411025c7c432e8282204bcbb865d050440019710cba0a0880034ed95741411023e9c32ae82822000db3815d05044001b6102ba0a0880132ed857414110026d9b0ae82822047db2515d0504408fb62a2ba0a0880026ee1f641411026d5d436c82822000e3b65d905044093b64e3b20a0880026e61c64141100071db28c82822000e386519050440a3b64e2320a088136aee1c641411026e5d438c8282204dab98719050440979730e320a0880022e61c641411025f1d428c8282204be39851905044099974ea320a0881378e9d4641411026f4d398c8282204de9973190504409bd54e4320a088137aa5c8641411026f59388c8282204deb17119050440e3c74a2320a0881c78e14464141100053c432a8282204be386455050440956e102aa0a08800356d95731411023eac32ae62822000d9b645cc5044001b30c8b98a08811f56d517314110006acaa2e62822000dd2815cc5044001ba302b98a08801336d857314110026e9b0ae62822047dd2515cc504408fba2a2b98a0880035ad95721411023eb432ae42822000dab645c85044001b50c8b90a08811f5ad517214110006b4aa2e42822000de2815c85044001bc302b90a0880133ad857214110026f1b0ae42822047de2515c8504408fbc2a2b90a088142dc61e5114110256b8c3ca22822053b72869445044095ce50d288a0881535c9da5114110287393b4a22822050f327494450440a1e62e9288a088003ccd92511411000798324a22822050f527394450440a1ea2e7288a088143d89ca5114110287b0b94a228220009f187d0450440016e30ba08a0880036c5d34114110006e8b9e822822000de172d0450440013e30e208a088002dc6144114110006d8ba0822822000f315410450440017a306208a088003745cc4114110005f0c10822822000de17210450440073e70f188a0880036c5d23114110006e8b9c622822000de1728c450440013e70e988a088002dce153114110006d8ba2622822000dd1734c45044001bc2e4988a08800e7ce1e2114110006d8ba4422822000dd1738845044001bc2e5108a0880027ce1d2114110005b9c2a422822000db1744845044001ba2e6908a088003785c921141102a43f434eba022007
  | 2 => 0x3659451029eb9380cb28a2000e3465d9251440a5b64e1b24a2880032d9d864945100071a328c928a204ddb27019251440a18f0e1b2aa2881372e1c064545100065c326e0a8a2050c7476d9551440118e8ec32aa28814b2d1db645451026e5a3b0c8a8a2000e346519151440118e8edaa2a28800e5d21d54545100053a432a8a8a2008c747655151440a1ae6ea382a28813f1d19575d0510024f8402eba0a2050c7676d9741440a78ecec32e82880038d19065d051027e3b438cba0a204fc75871974144001c6ecbb26828814f1e1c065505102965c386c8a0a2000c7865dc14144091968c93b082880127c20276105102747a432ea20a204ec77865d441440018e90cba882881234d1917510510006b9c02ea20a2000d70805d441440078eec0ba8828800f5cd817510510246b9202ea20a2048d71405d441440012ef0fb28828812a9da1b6510510286b9386ca20a2000975871944144001c68c8328828814f5c9c065105102553bc38ca20a204ac768719441440954eb0e328828813b1d61c65105100043ac38ca20a204ee3684194414409dc6b08328828813f1d9d065105102571b3a0ca20a204ae56731944144095caae6328828812b999c8651051025732b90ca20a204ae72701944144095ce2e032882881cb8d90065105103971a200ca20a2000d3575d904144001c6ecbb2082880038d1976410510296d9386c820a204dab587d9041440a596b0fb2082881278d9d7641051024f1abaec820a2049e9673d904144093d2ae7b208288127a99cb641051024f52b96c820a2049eb270d904144093d62e1b208288002ad21954105102771a32aa820a204dbb0805504144001aaecab988288003551957310510006cbb22e620a2048d94645cc4144091b2ca8b988288003655517310510006e9402e620a2000dd1805cc41440079aec0b98828800f74d817310510246e9202e620a2048dd1405cc4144001acecab908288003591957210510006d3b22e420a2048da4645c84144091b4ca8b908288003695517210510006f1402e420a2000de1805c841440079cec0b90828800f78d817210510246f1202e420a2048de1405c84144001c68ca324628800ab520d628c510024f9406ea98a20048f4865d531440a18e8edb2a62880039518f654c51029e3a3b0ca98a2052cb476d91314409b968ec32262880038d194644c51001cea43a8698a20028f4875893144001c68ca3244288006b92096388510024f9406ea90a20048f4865d521440a18e8edb2a42880039918b654851029e3a3b0ca90a2052cb476d91214409b968ec32242880038d19464485100247a432e690a20489b4845cd21440031e90eb1a428800e7921d42485102665c322e9a8220039f0815d35044093974edb26a0880038ed9764d411028e5d3b0c9a822000e3865193504409997
  | 3 => 0xda9a20008bf845db534400f17908bb6a6880038794f64d4d100070f298c9a9a20048f4865c7534400f17d09bb2a6880022f6137654d100043fc2aeca9a20008bf845d9534400f17908bb2a6880023be097654d1000c76412eca9a200287e87d9553440a18f0e1b2aa6881372e1c06454d1001c7d436e0a9a2000cb864dc153440091eb033b686880021fe1576d0d100443e42aeda1a20028bc845db43440071f10cb8686880221fa177650d100043ec2eeca1a200087f855d943440110f90abb286880022fe117650d1000477c12eca1a20018ec825d943440958e8e232a868800a2fa1f6450d1024e5a38ec8a1a20048f686dc543440018e8cbb8a86880021fa1f65589100062e39ecab12200087e8719562440018b8e632ac4880030fd9774589100061e32ee8b122000c3f651d16244001878ca3a2c4880022fa1f64589100061fbaec8b122000c3c75d916244001938e7b22c4880022fa1c64589100061fba8c8b122000c3c751916244001938e6322c48800317d9773589100062e32ee6b122000c9f64dcd6244001938c9b9ac4880221fa1f755891003c5f43ee8b122000c3f75dd16244001878ebba2c4880030fdd474589100061e3a8e8b1220028de87dcd62440018beebb9ac488003171d773589100064fba6e6b122000c9c74dcd62440018beea39ac488003171d473589100064fba0e6b122000c9c741cd6244001998e7b92c48800e3e60276d491000c3e42aeda9220008bf845db524400f17908bb6a4880038b94b64d491000717290c9a9220048f4865c7524400f17d09bb2a4880022f61376549100043fc2aeca9220008bf845d9524400f17908bb2a48800237e0d76549100146e41aeca92200887c851d952440030fd0fb2aa4881431e1c3655491026e5c380c8a9220038fa86dc15244001970c9b82a4880123d60676d09100043fc2aeda12200887c855db424400317908bb6848800e3e21970d09100443f42eeca12200087d85dd942440010ff0abb284880221f21576509100045fc22eca1220008df835d942440051b906bb2848801e2f21076509102563a388caa1220018be87d914244093968e3b2284880123da1b71509100063a32ee2a12200887e85dd932440010fb0bbb2648801e2fa13764c9100045ec26ec9922000ccc329d932440010ff0abb264880221f215764c9100045fc22ec99220078bc845d932440011bf06bb264880023be09764c91000666190ec9922000e4c32d953244001c986432a6488003a30cb644c91000746190c899220528be869d3514400187ecb3a6a2880230f19674d451026c5e432e9a8a2000c3f655d35144011878caba6a28814a2fe1f64d45100045ec3ec9a8a20078bf87193514400117b0e326a2880127c20276945100247a432eb28a2008a7686d9651440018ecedb2ca2881435c9c
  | 4 => 0x44400156b02196c88814aaea0032d91100055cc0065b222000a3f855c364440014790ab86c88801f0f192759911003e1e322eb3222000c3e75d92644400187aebb24c8880021fa1f65591100043f438cab222000c3f75dd16444001878ebba2c8880031d1d771591100063c3aee0b2220048f5819d8644400117f0eb20c8880028fe1564191100051e42ac8322204dab5819d8644409396d033b0c8880030f9db65191100071cc06ca32220008bd87994644400117f0eb28c8880030f9d865191100071ac08ca3222072e377119464440e7c7700328c8881cf8ec4065191103971b080ca3222072e341019464440e7c7020328c8880028fa1663191100051ec2cc63222000a3e85988644400147b0b310c8880038ed9570191100071c32ae03222051ab68194c644400156b03298c888136aea0253191100055cc04a632220078be8714c644400117b0e298c888146ada0652191100055ac0ca4322204daba80948644400157301290c88801e2fa1c52191100045ec38a432220078be870c8644400117b0e190c8880028fa1432191100051ec28643222051ab6810c8644400156b02190c888136aea0032191100055cc00643222000a3f8544064440014790a880c88800e3e60276d511023e3c284edaa2200787c855db544400147b0bb26a8881272d9c764d51100247a432e3aa22008c74655c7544400196ec8b8ea8880123d60676951102465a20ced2a220078bc845da544400147b09b2ca8881431e9c365951100051f436a92a22008a3c86d52544400187cedaa4a88801f0f1db549511001c7c432e12a22000c7b655c2544400f970c8b84a8880023de0576551100047dc02ecaa220038f4811d954440091f1003b2a88801e1fa1f65551102a63a38ecaaa22050c7870d95544401117d0fb22a8881272d1c764551102965c386c8aa220048f686dc554440018eecbb8aa88813f1d19771551103065a326e2aa220038fa86dc154440c38f0cbb82a8881332e19370551100247a432e22a22007cb4645c454440071f10cb80a8880021fa1f6558d1000636396cab1a200087e8719563440018d8e432ac6880030fd977458d100061e32ee8b1a2000c3f651d16344001878ca3a2c6880022fa1f6458d100061fbaec8b1a2000c3c75d916344001958e5b22c6880022fa1c6458d100061fba8c8b1a2000c3c751916344001958e4322c6880031bd977258d100063632ee4b1a2000caf64dc96344001958c9b92c6880221fa1f7558d1003c5f43ee8b1a2000c3f75dd16344001878ebba2c6880030fdd47458d100061e3a8e8b1a20018ee87dc963440018deebb92c6880031b1d77258d1000657ba6e4b1a2000cac74dc963440018deea392c6880031b1d47258d1000657ba0e4b1a2000cac741c9634400199ee6392c68800e3e60276d4d100143e42ae
  | 5 => 0x80123721d6354e100247d406eca1c20048f8805db52840011bf06bb2a50800a3720d7654a100247c402eca9420048ec8758952840091f501bb285080123ea03764ca1029c3fc3acba8c204d8bf8759341840991f70cba6a1081332e99174d42102acbc42ae69042000c5d7394f65440014eb0329eca880029e60253d95100051f420a7b2a2000a3d8414f65440018dae5296ca880029d60652d95100053cc04a5b2a2000a3e8414b654400147b08296ca880028fa1263d95100051ec24c7b2a2000a3e8498b654400147b09316ca881429d60774d95102a53cc06e9b2a2000c3d741d365440a94f3003a6ca881529e60373d95100051f424e7b2a2000a3d849cf65440018bae639eca881529da0473d95102853ac08e7b2a2050a7a801cf65440a94f30039eca880021fa1c43d95100043ec3887b2a2054a7980dcb654400147d09396ca880028f61272d951000636b90e5b2a2054a76811cb65440a14eb02396ca881429ea0072d95102a53cc00e5b2a200087e8710b65440010fb0e216ca880021fa1c32d95100043ec3865b2a2000a3e840cb654400147b08196ca881529da0432d95100053ac0865b2a2050a7a800cb65440014f300196ca880028fe1171d95100051e422e3b2a2000c3f659d26544011878cb3a4ca880030fd9574995100461e32ae932a2000c3f75dd1654400187eea3a2ca880032d1d371595100065c3a6e0b2a20038f9809d865440010ff0eb28ca880028fe1165195100051e422ca32a204aa79809d865440a18f5013b0ca880028fa1263195100051ec24c632a2000a3e84988654400147b09310ca8812a9da0643195100053ac0c8632a2053a7a8090c65440014f301218ca880221fa1c43195100043ec388632a204aa768190865440014eb03210ca8814e9ea0242195100053cc048432a200887e8710865440010fb0e210ca880221fa1c32195100043ec386432a2000a3e840c8654400147b08190ca8812a9da0432195100053ac086432a2053a7a800c865440014f300190ca880028fa1443d91100051ec2887b222000a3e8510b644400147b0a216c8880038e60365d91100071ac08cbb222000a3e8598f644400147b0b31ec8880028fa1662d91100051ec2cc5b222000e37655c76444001c68cab8ec88814aad60775d911024d5cc06ebb222000c3d751d764440a556b023aec88814aad60773d91100051f42ce7b222000a3d859cf644409356d0239ec88814aad60473d91102955d400e7b222049ab9801cf644400117d0e29ec8880022f61c53d91102955ac0ee5b222000a3e859cb644400147b0b396c888126ada0472d91102955ac08e5b222052aba801cb644409357300396c8880022fa1c52d91100045ec38a5b2220008be870cb644400117b0e196c8880028fa1432d91100051ec2865b222049ab6810cb6
  | 6 => 0x47bc0aecaa440038f4815d954880091f100bb2a9100122f21d64552200246e43ac6a9c40048df8758f438800f1df0cb9687100133c9c1619462001e3b30aea20c4003cd6615cc41880079ccc2b9083100031d5d561106200066ab9ac220c4000ce57258441880099e4e0b0883100123ea03764c6200247a43ac298c4000c5d7394f65480014f30129eca900028f61053d95200045fc22e3b2a40078bc845c765480051bd0fb9aca9000317dd473595200066639ee4b2a4000cd873dc165480010ff0eb28ca900029720d65195200045fc3ac8322400787c855db54480011bf06bb6a89000a3720d76d512002476432e5aa240078be849da54480071ed033b2a8900023d60676551200046fc1aecaa240028dc835d954480011ef02bb2a89000e3d20576551200047dc02ecaa2400787e87d9554480111790eb22a8900031dd9471551202763a328e2aa240018fa86dc154480c38f0cbb82a8900123b21972151200062e318eab1a400887e87dd563480018b8ebb9ac6900031b1d77258d200063c3aee0b1a4000a5d85d8f53480091d90cb96a69000333d8d72d4d200043fc2aeca9a40008df835d953480011df04bb2a6900023ee017654d200043fc2aeca1a400887c855d943480011ef02bb2869000e3d2057650d2003c6f43ec6a1a40048ee86dc9434800165b0832aa4900231b1db5454920046363b2a8a924000a6c8654d52480017c302382a4900023de1d61185200247c404ed28a40038f8865c2514808f8f0cab84a29000237e0d76145200146e41aec28a4008c6c655c851480071f10cb80a2900231e19570145200043fc2aed20a400887c855da41480011bf06bb4829000a3720d769052001c7c432e120a40038ec829d841480091f1013b082900032bd91721052001c7c432e020a4000cbb645c041480071ed033b4629000e3e219708c5200066db1ae118a4000c6f65dc950480015b10ca9a60900027a21d524c120007a4a9aa498240078bc845da54c40091e902bb4a98816b2d10576953100445ec26ecaa62059cb441dd954c40091e902bb2a98800e1f21d655531001e3a38acaaa62061c7a65dc154c40091ed03bb2a7880123d20576d0f1000477c12eca1e20018ec825d943c40091e902bb2878800e3721d6350f100247b40eeca9620048f4815db42c40011bf06bb2858800a3720d7650b100247a40aeca1620038ec8758942c40091ed03bb2658800f1ddd7765471027c7bc32eba0e204fc76655d741c40b136908b9a43881421fe1d65d43102945fc3ac9a062003cb47159140c400f0f90abb6a9080123e20176d52102be3c282edaa4200787d85dd954840ad8f0a1bb2a9080123e20176552100245e43ac8aa42004cb87059154840c196cc9b8aa9080123e20176d4e1000477c12eca9c20018ec825d953840091f100bb2a70
  | 7 => 0x78655c354500091790cbaca8a00031dd9471551402763a328e2aa28061c7865dc15450097c76c032aa8a013f2d1db71551402765a3b0e2aa28061cb876dc15450009970ec382a8a00036c1c470551402647dc02ebb0a80008f78758461500014e90ab08c2a001e2f21276d45402ce5a30ae9a8a8000c3e7655351500b3c68c2aa6a2a00032d5d361d454023e3c32ae128a8000c3c765515150007968c2ba0a2a00231e19570145402447ac3ec320a805687d87d975050099976c0ba6a0a00030fd9774541403065a20ee2b2880008ef825d953100031d904bb2a6200123e2017654c400243e43acaa988004cd87058d53100011bf06bb2a42000a3720d76548400247c402eca90800487c8759552100099d0e0b12a4200123721d634c84000d66412c699080048ec87589321000559906b1264201431e14375584400445ec22eda888060cb4415db511000f87ce8b2ea2201838d10565d44402863c282ed2888004cf27058651100a1ce0a0b0ca2201472d105761444029e3c282ec2888052ab88059641100011df04bb262200063b209764c44003e4e3a2c698880048f48758531100011bf06bb2422000a3720d764844003e563a2c490880048f487585211000f0f90abb6a91801e1f61776552300047bc0aecaa460038f4815d9548c0091f100bb2a9180122f21d645523002679382c328c6003c76615d4418c0079acc2b98831800f3998572106300063abaac220c6000cd573584418c0019cae4b0883180133c9c161106300247d406ec90c60048f487585218c0018dae5296ca980029e60252d95300051ec20a5b2a60008bf845c7654c00f17908b8eca980063ba1f725953000637ba8e4b2a6000ccf731c9654c0019d0e5b82ca980021fe1d651953000536412ca32a60008bf87590644c00f0f90abb6a8980023be0976d513000c76412edaa260048dc865cf544c00f17d093b4a89800e3da0676551300047ac0cecaa260008ef825d9544c0031d904bb2a8980023de05765513001c7a40aecaa260008fb805d9544c00f0fd0fb2aa8980222f21d64551300063bb28e2aa2604ec74651c5544c0051f50db82a8981871e19770551300246e432e62a26000b1d84195534c0118b8edaa2a698023171d95454d30005e8c08e0a9a6000c6c621d5624c0014db0bb16a498003335cf62d49300062e3b2a6a9260008f787584614c0071f10cb84a29811f1e195709453000477c12ec28a60018ec825d8514c0118b8cab98a29800e3e21970145300463c32ae028a600087f855da414c0110f90abb482980023be09769053000c76412ed20a60038f8865c2414c0071b9073b0829800327d91731053001c7c432e020a6000cbb645c0414c0071ed033b4429800e3e219708853000675b12e110a6000c5f65dcd504c00f0f90abb6a91001e1f61776552200
  | 8 => 0xe4b28a1a015b9c9c565143402b738b8aca28680049bb865d050d0097a74caba0a1a012f4e59574143402b59dc3aa8286804cd3b8755050d00af6770caa0a1a017f8ee19541434025e9cbb2a82868056e397655050d00ade34e6aa0a1a015bc65cd54143402b795392a82868056f297255050d0001e6702aa0a1a0003cc20554143402b79938aa82868056f317155050d0001972e8b08a1a00029e61a51143402647dc32e1aa48004c787059554900011eb0db8aa9200023d618715524000666196ec9948000ccc325d932900b1c6ca9aa4c32013e3de1d549864001c7a43aa930c8000af38055261900095e100aa4c32000395d4e53986402c55b420a730c8000ab58414e6190001ccea5294c320162ada1052986400055ac20a530c80038f6870ca61900011eb0e194c3200029da1432986400053ac286530c8058ab6840ca619000156b08194c320003b14c83298640025794006530c8000af1800ca61900091f501baac320012bca0031586400257940042b0c8004af280dd561900018eeeb3aac320002ad61275586400055bc22eab0c8000a77855d161900014e90aba2c3201238d953545864027c7bc3aa8b0c804e8f48755161900015e700aa2c320012bc20154586400053b42ce6b0c8000a75859cd619009156d0939ac320002ad61273586400055bc22e6b0c8004af2801cd61900015e30039ac32000395d4e53586402455b420a6b0c8000ab58414d61900095e50121ac320002bc60243586400053b42ce4b0c8000a75859c9619009156d09392c320002ad61272586400055bc22e4b0c8004af2801c961900015e300392c32000399d4a52586402455b420a4b0c8000ab58414961900095e501212c320002bc60242586400047b43864b0c80008f5870c961900014ed0a192c3200029d61432586402455b42064b0c8000ab5840c96190001d8a64192c320012bca00325864000578c0064b0c8059cb6615d351900014ef0ab0ea3201232d9d161d46400065aba2c3a8c8004cf27058651900079e4c2b84a3200033c58570946402465a3a2c2a8c8049cb4415d851900079e4c2b80a3201276c105701464001e7930ae120c8049db0415c241900019e2c3b8283201278d9d5611064024f1abaac220c8049e96735844190093d2ae6b088320127a99c9611064024f52b92c220c804deb2705844190093d62e0b088320002ad61b511064026e5db2ae020c8000cb9655c0419009bb64c2b8083201376c585701064001e7930ae118c80048f4875853190091968e8b0a632000f3c98570886400247a40eec90c80048f4875852190091968e8b0a43200031ddd471595400065bba0e2b2a800787d85dc165500019e6e3b82caa00033c1c770595402b63d42ee0b2a804cc7985dc165500010ff0eb28caa00029d205651954003d1e426cbaa28008c
  | 9 => 0x638c45002675382c5188a000cb9645c231140019b2c6b8462280033a589708c45001e7930ae1188a0048dc83dd931140018beeab1a62280123d21d614c4500063bbaac2988a004cba7059221140099b4e0b1c42280133a9c162884500065cb22e1108a000cd9635c221140019d2c4b84422800f3c985708845002476416ec908a0048f481dd921140018deeab1242280123d21d61484500063bbaac2908a00887e870ca65d00010fb0e194cba001e8fa1032997400051ec206532e8000a76810ca65d00014eb02194cba015e9ea0032997400053cc006532e8057a7a800c665d00014f30018ccba015e9ea0021997400053cc004332e8000c5f7394d65d00014f30129acba001e8fa10535974000637b94a4b2e8000a798094965d000f47d08292cba000317dce73597400053b40ce6b2e8000a75819cd65d00ad4f50139acba00029e60273597400053dc02e6b2e8007a3e841cd65d000147b0839acba00031bdca72597400053b40ce4b2e8000a75819c965d00ad4f501392cba00029e60272597400053dc02e4b2e8007a3e841c965d000147b08392cba00021fa1c32597400043ec3864b2e8007a3e840c965d000147b08192cba00029da0432597400053ac0864b2e8056a7a800c965d00014f300192cba001e8fa1371597400053cc04e2b2e8000a7b805c565d00ad4f50018acba00029e60031597402b53d40042b2e8000a798008565d00ad4f50fb82cba00029de0570597400053a40ae0b2e8007a3e84cc165d000147b09982cba001e8fa1320597400051ec2640b2e8007a3c85dd954d000f87eebbb2a9a013f8d99771553400065bbb0e2aa6804ee36651c554d0001976edb82a9a01878e99770553402b59c428e0aa6805fe3a651c154d0001b66e2382a9a00036c1c470553400461f32ae9a9e8008c3f7655353d00050f90eb2aa7a015b1e1c16554f400061fbb2a8a9e8056d387055153d00018f2cbb82a7a00230f99574d4b400461fbb2a9a96800187c8759552d00ad8f0e0b2aa5a00030fdd95454b402b69c382a8a968000c7965dc152d000199865bb265a0003330c9764cb4000726194ca9968000e4c3259532d000f87ce8b2ea3a00230f99574d47400061eb2ae9a8e8000c3d7655351d00ad8f4e0b2ca3a011f1e99570947400063cb2ae128e800787c85dd951d00ad8f0e0b2aa3a00030fdd954547402b69c382a8a8e8000c7965dc151d00c38f0a0bb0a3a00230f995741474030e9c282e828e8008c3e655d350d00ada70a0ba6a1a01869ee1d65d434025e3dc3acba86804c9bb865d350d00bf9770cba6a1a01334e99574d43402669cb2ae9a868000db3815d350d0001b6102ba6a1a01331edc165543400061eb2ee8a868056e3a7459450d00adc72e8b28a1a015b969cd65143402b72cb9aca2868056e6a7259450d00adcd2
  | 10 => 0xb08a056e354055161140114ed0b39ac2280029d61673584500453a42ae6b08a004af2801cd61140015e30039ac2280229da1743584500053ac2e86b08a000e3554d0d61140095e50121ac228002bc60243584500071aaa286b08a008a768510d61140014eb0a21ac2280229da1672584500053ac2ce4b08a008a74855c961140095e500392c228002bc60072584500453b42e84b08a000a7585d096114001c6aa9a12c228012bca02425845000578c0484b08a000e355450961140114ed0a212c2280029d61442584500047b43864b08a0008f5870c961140114ed0a192c2280029d61432584500055b42064b08a000ab5840c96114001d8a64192c228012bca00325845000578c0064b08a00097b805d251140018eae8b0ca2281439c9c1619445025738b82c3288a050d3a645c251140a1a72c8b84a2281435698d7094450286acb1ae1288a050d6a625c251140a1ad2c4b84a2281435c9857094450286b8b0ae1288a007c3e645d741140012f700bae8228023179d563d04500062ebaac7a08a008c6e7558b41140018daeab1682280231d9d561d04500063abaac3a08a004cba70592411400187aecaa482280038755163904500266d382c7208a000e2d5458a41140099d4e0b14822812b1ddd561904500071aaa2c3208a00097b855c24114001972c8b8482280034e55170904500066cb1ae1208a000ce9625c241140079e4c2b8482280122f21376504500061fbaac8a08a000c77755854114001972c9b8282280033c587705045001c3ec2aec208a0028de835d841140031dd04bb0822812b1d145761045026e5c202ec208a007c3e645d441140018bcc6ba882280031b9897510450254ba40aea208a003c76615d4411401187ceab2082280030f5d564104500064f39ac8208a000cae72590411409b57100b2082280132e9c164104500061ebb2a8208a0008df865cc411400f93cc8b9882280032759173104500068eaa2e6208a000cce625cc41140079acc2b98822800237e1d63104500046ec3ac6208a008c5e7558c41140018baeab18822800387551631045000667392c6208a004cda7058c41140011df0cb90822801f2b991721045000656b22e4208a000d2d545c8411400199cc6b9082280033358d721045001e7330ae4208a0008ef8758841140011db0eb1082280231b9d5621045000636baac4208a000e2d54588411400199ce6b108228003335cd621045002675382c4208a008c767558441140018eaeab0882280038d55161104500066b39ac2208a000cd57358441140019cce4b088228003395c9611045002679382c2208a007cba645c04114001972c8b8082280034e55170104500066d31ae0208a000cd9635c041140019d4c4b8082280033a589701045001e7930ae0208a000cf1615c04114009974e0b246228013369c1
  | 11 => 0x140114bd0a392c628072976147258c500054f420e4b18a000a9d841c9631400199ae4392c628002b5a047258c500056ac08e4b18a004ada801c963140395b300392c628012b6a024258c500056cc0484b18a008a5e8510963140014bb0a212c628012b6a027158c500452e42ae2b18a004ada801c563140395b30038ac62802297a172158c500052ec2e42b18a004ada8008563140015b30010ac62801f0f99175d0c5003e1fbb2a9a18a008c5e7558f43140018baeab1e86280038755163d0c500245e43ac8a18a000c3f765514314001c3aa8b1a86280032e5937050c500069caa6e0a18a000cd963dc143140114dd0b3a2c428012ba201745885004537428e8b10a01ba6d851d16214011c5f08aa2c4280038b9d1545885000716ba2a8b10a000e67815516214001cc902aa2c4280039ae0154588502b734402a8b10a056e2f4055162140adc5a80aa2c42815b9a84154588500453642ae6b10a004ae8805cd62140114dd0a39ac42806e9b614735885000557420e6b10a000aad841cd621400199ae639ac428002b9a04735885000572c08e6b10a004aea801cd62140375d30039ac4280229ba17435885000536c2e86b10a000e2d54d0d62140095d50121ac428002ba602435885000716aa286b10a008a6e8510d62140014db0a21ac428012baa0271588500453642ae2b10a004aea801c562140375d30038ac4280229ba17315885000536c2e62b10a004aea800c562140015d30018ac42801f0f99175d085003e1fbb2a9a10a008c5e7558f42140018baeab1e84280038755163d0850046373aac5a10a000c6d7558b4214001c5aa8b1684280122f21d64508500061fbb2a8a10a000e1d5458d4214001c5aa8b1284280032e59370508500069caa6e0a10a000ce962dc1421400199865bb26428003330c9764c8500247c402ec990a000e8c329913214001d1864b2264280123721d634c8500062fbaac6990a001acc8258d32140091d90eb1264280031bdd5624c8500156641ac4990a000cd963dc132140019d2c5b8264280229da1443984500053ac2887308a008a768510a61140014eb0a214c22800e3da1c32984500047ac3865308a008a76850ca61140014eb0a194c228002ada1032984500055ac2065308a000ec5320ca61140095e500194c228002bc60032984502543e43aa8b08a008a7685cc561140095e50018ac2280229da1721584500257940042b08a008a7485dd161140114ed0b3a2c2280229d215745845002578402e8b08a008a76851d1611409d8e8ea3a2c228002b5a0c74584500056ac18e8b08a000ae6821d161140015cb043a2c228012bca0074584500063bc3aa8b08a000a748755161140018e90eaa2c2280238de1154584500071bba2a8b08a000e34745516114001ce700aa2c22815b9c20154584502b71ba02a8
  | 12 => 0x34b551721065001e7330ae420ca000c7575584419400156f08b0883280038d55161106500066ab9ac220ca000ce57258441940099e4e0b0883280034e55170106500045fc22ec98ca0078bc845d931940011df04bb263280063b209764c6500247a43ac298ca0008bf845d9219400f17908bb2432800237e0d76486500146e41aec90ca0048f48758521940a98eeca38ac8a80022fe1d64191500055a40ac8322a000cb7641c554540cd968c838aa8a81332e193705515000666194ec992a000ccc321d93254099976c03a2c2a80023de1d61185500055a422c230aa000cf3615c251540070f90b3b082a80030f5d764105500063abaec220aa000cbb645c041540019e6c2b8082a801e2fa1c32990500045ec3865320a008a3e850ca641400147b0a194c828002ada0432990500055ac0865320a004aba800ca641400157300194c828012aea0031990500055cc0063320a004aba8008664140015730010cc828012aea0243590500451f42886b20a004aba80909641401147d0a212c828012aea0273590500055cc04e6b20a004ab8805cd641401147d0a39ac8280028f61473590500255d404e4b20a000ab9809c9641400957100b92c8280228fa1472590500051ec28e4b20a0008be870c9641400117b0e192c8280228fa1432590500051ec2864b20a000ab6810c9641400156b02192c828012aea0032590500055cc0064b20a004ab880dc564140095750138ac82814b2e1c271590500451e42ae2b20a004ab8805c5641401147d0a38ac828002a7a0c71590500054ec18e2b20a000aae821c5641400155b0438ac828012aea00715905026e5c380e2b20a008a3e85cc5641400147b0b98ac828012aea0031590500055cc0062b20a008a3e85c85641400147b0b90ac828012aea0021590500055cc0042b20a007a3c84dd9541401187ee9bb2a82815b1e1c376550503071b326e2aa0a066e36641c55414001ae0e038aa82812a5de1871550502563b430e2aa0a04e975861c554140958eb0c38aa82813b4d99071550502769ab20e2aa0a04ed56631c5541409daaac638aa82813b599887155050276b2b10e2aa0a04ad72801c55414095ae30038aa8281531d9807155050276b9300e2aa0a074d73401c554140e9ae08038aa8281338e9937055050006b9b8ee0aa0a000d7071dc154140ada74c9b82a82815b4e59370550502b6ad31ee0aa0a056d5963dc154140adad4c5b82a82815b5a58b70550502b6b930ee0aa0a056d7161dc154140114bd0b3a2c628012b62017458c500452f428e8b18a01ca5d851d16314011c3f08aa2c628003879d15458c500070eba2a8b18a000e57815516314001ca902aa2c62800396e015458c502b72c402a8b18a056e1f4055163140adc3a80aa2c62815b968415458c500452e42ae4b18a004ad8805c963
  | 13 => 0xc76412ed2a262038dc865ce544c4091f5013b2a8988023e602765513100477c12ecaa262018ec825d9544c4011ef02bb2a8988023ee0176551310247c402ecaa2620787c87595544c41117d0fb22a89880a3da1b71551313065a326e2aa26200cbb641c1544c497970c8382a89880e3721973151310058ec28c8a1a6207c9c76951434c40f938ecaa28698802f46007150d3100656310e8b126200c9c7650d424c4018becbb9aa2988023ee1d601813103c5e422ed2a442088bd84dd954884071e902bb2a9108023ee0176552210247c402ecaa4420387c8759554884071bf0eb1ea71080297e1563d4e2104477c32e5a9c4200ccd635cb53884071b90eb1a87108021fe1d65195210051ec2887b22420087f855c364484110f90ab86c89080a37a1f73591210064fba0e6b224200ccc73dc964484019a8e7b8ac8908022fe1d64191210054e41ac8322420787e859db544840f17908bb4a89080237e0d76951210146e41aed2a242038ec865ca54484091f5013b2a8908023e60276551210046fc1aecaa242028dc835d954484011ef02bb2a8908023ee0176551210247c402ecaa2420787c87595544841117d0fb22a8908063da1b71551213065a326e2aa24200cbb641c15448497970c8382a89080e3b21972151210064e318e8b1a42078be87dd16348401938e9b9ac6908032b1d37258d210065a3a6e2b1a42008bf845d9534840f17908bb2a6908023ee017654d210247c402eca9a42088de87d8d53484071dd0db92a69080e3b21972d0d210045fc22eca1a42008df835d943484011df04bb286908023de057650d2100596c28c8a124207cac76951424840f958ecaa28490802ab2194350921005f0c00e2a124200c6f65dc951484015a90ca1a62908027921d424c521007c2a1a8498a42008fb87580604849f96b09b8ac9a80033cdc770593500067838ee0b26a0008ef825d943d40031d904bb287a80023de057650f5001c7a40aeca1ea0028bc8759143d40012f30bb8287a80032e5937050f500046fc1aeca16a0028dc835d942d40011ef02bb285a800e3d2057650b5000c5e43ac8a16a00097985dc142d4001972c9b8285a80025e617704cb500065cb22e120ea008c3e7559041d400156f02b2083a801f2799173107500064eb22e620ea007cae645c841d400195ac8b9083a801f2e99170107500065cb22e020ea04b8fb865c254940c18eeedb8aa92819b1ddd87155250006b8380e2aa4a054c76861c554940a98eb0c38aa9280025e603754ca502965ac0ee8b0ca05487e87d51619400f878e9aa2c32801f0f1d154586502a53a40aa8b0ca004cf27058651940a1ce0a0b0ca32811e3e61b70546502a69a20ae828ca000c7575587419400187aecaa4832800f1d98575106500061ebb2a820ca000d1d545cc41940079acc2b988328
  | 14 => 0xc325d932104071e902bb26420803930ca654c84100726192ca99082038dc8758d321040193ee8b1a6420806b3209634c84101c7643ac49908200caf74589321040559906b1264208033558f714c84100672b16e29908203a778759751104078ef0eb2ea2209838d9d165d44412771aba2cba8882599b7865d3511049f96f0cba6a2209674d99574d44412ce9ab2ae9a888259d96635d351104b3b2ac6ba6a2209676998974d44412ced2b12e9a888259db2605d351104b3b62c0ba6a22096acde1d54d44413369bc3aa9a888259b3786553511049fc6f0caa6a2209674d5d954d44412771abb2a9a888259f166355351104b3e2ac6aa6a220967c998954d44412cf92b12a9a888200f33805535110401e6100aa6a220967cc98154d44412cf98b02a9a888200c75655c3511040136f08b86a22080396d4e539804103d5d420a73008200ab98414e6010401cd6a5294c02081eaea1052980410055cc20a530082048fa870ca60104011f30e194c0208029ea1432980410053cc28653008207aba840ca601040157308194c020803b24c8329804101d79408653008200af1810ca601049b1790eaa2c02080ebca04305804101d7940840b008207ab884dd5601040f575093aac02081eae211755804101d7840aeab008207aba841d56010497970e83aac020802b6a0c75580410056cc18eab008200aea821d560104015d3043aac02080ebca0475580410065dc3aa8b008200ab88755160104019710eaa2c02081f8ee1554580410071dbaaa8b008200e38755516010401d6702aa2c020967ac20554580412cf1da8aa8b008259e3951551601040f5750939ac020802ae612735804103d5c422e6b008203af2811cd60104015e30239ac02081eaea1353580410055cc26a6b008200e3954d4d6010401cb6a729ac02080ebca06535804100578c0ca6b008200e395454d601040f5750829ac020802ae610535804103d5d424e4b008200ab9849c9601040f57108b92c02080ebca04725804100578c08e4b008207aba84d49601040157309a92c0208038e553525804100735a94a4b008203af28194960104015e303292c0208038e551525804103d5d420a4b008200ab98414960104011f50e192c0208023e61c32580410053d42864b008200a79850c9601040f57508192c020802ae61032580410076499064b008203af2810c960104015e302192c02081e2f21176952310445ec26ecaa462038f4815d9548c4011f700bb2a9188123e201765523101c3e43acaaa46200a6f8558b528c40199ae6b16a5188021fe1d65195310051ec2885b22620087f855c3644c4110f90ab86c8988063ba1f725913100657ba0e4b226200ccf731c9644c4019c8e5b8ac8988022fe1d641913100556412c8322620787e859db544c40f17908bb4a8988023be09769513100
  | 15 => 0x1b8aa8209676c583715504130f1d32ee0aa08200db371dc154104bfc74ca382a8208036cdc47055041006d8388e0aa0824d9bb861c1541049b9750c382a82092e6e618705504126e5cc30e0aa0824bd3a651c15410497a72ca382a82092f6698c705504125eccb18e0aa0824bdaa621c15410497b52c4382a8209376ca04705504126ed8c08e0aa0824bdb2611c154104ebb66a2382a8209d76c14470550410062fbaceab188207a9e849d563104075a902baac62081ea7a107558c411454ec20eab188207e1f855516310401c3ceaaa2c620803875d55458c410074bc0aa8b188259e948155163104b3c3ea2aa2c620967875455458c410074dc02a8b188200e988055163104b3d2e20aa2c62081ea72117258c4101d6a40ae4b188200a5e851c963104014bb0a392c62081ea7a107258c411454ec20e4b188200ccd721c963104075ad02392c6208a2b56047258c410056d400e4b188200ad9801c963104075ad03292c620802b56065258c4103d4f420a4b188200a9d8414963104075ad03382c62081ea72117058c4101d6b408e0b188228ad5811c1631040f53d09902c620802a76132058c4101d6b40840b188200ad58108163104018bca6bb6a62080a97a0d65d4c410461f32ae9a988208c3f7655353104014bf0ab1ea62081f279d163d4c410064eba2c7a988200e1d5458f53104071e902bb2a62080e1f21d6554c410061fbb2a8a988200e1d5458d53104018eacbb8aa6208034d5537154c410066ab1ee2a988200c6f759d5621040f55d093aac42080eb9205755884103d57420eab108227aad841d5621040fc5f0aaa2c4208038b9d5545884100716baaa8b108200ea78155162104b3d4902aa2c4209678bd4554588412cf16a8aa8b108200eab805516210401d5100aa2c420967a9c41545884103d56422e6b108203ae4815cd62104014dd0a39ac4208029b614735884103d57420e6b108227aad841cd621040199ae639ac42080eb9a04735884113d72c08e6b108200aea801cd62104015d30039ac42081eaba13535884100556c26a6b108200e2d54d4d6210401c9ea729ac42080eb9a06535884100572c0ca6b108200e2d5454d621040f55d0829ac420802ab610535884101d7340ce0b108207aac845c162104075cd02382c42089eb9604705884103d5742660b108200aad84cc162104075cd02182c420802b9604305884100637292eda908201a6e82597521041187ccaba6a4208230fdd954d484103e4f3a2c7a908200c9d7458f5210401c3aa8b1ea4208039394963d484100537c2ac5a908207cae7458b521040195ae8b16a4208038b55162d484101c7a40aeca90820387c87595521040187eecaa2a42080387551635484100716aa2c4a908200c7565dc55210401a6aa9b8aa4208033958b715484100666196ec9908200cc
  | 16 => 0x650c5100c76412eca18a2038bc875914314407968e2b22862880f351c56350c510046fc1aeca10a2028dc835d942144071790eb22842880f2d1c5645085101e7238ac4a10a2038dc8758d321440359904b1a642880e3b21d624c8510156641ac4990a249cb441dd160144019e6e3b82cba09331e617705974100679b88e0b2e82008ef825d953d04031d904bb2a7a08023ee017654f410247c402eca9e820287c8759553d04018eacbb8aa7a080237e0d7654b410146e41aeca9682008fb805d952d04091f100bb2a5a08061f21d6554b410063ab2ee2a968207c3e7459751d04b3c6882b2ea3a093e9de1d65d47413363bc3acba8e8260e367459751d049fc6ae8b2ea3a08039ce0165d474100738402cba8e82609b7865d351d049d96f0cba6a3a09831ddc565547412cc5ec36e8a8e824fd70505c051d04c11ef0cb8ea9209872eddb70552412fe5dbb0e0aa48200db0711c154904a59730c382a9209531e60375582412945f43ca8b048208c3c759516090411878eaaa2c12094aae20154582412965db20e0b2a8200cf371dc165504018f6ea382caa08032edd0705954100679b88e0b2a820087f8759465504014f100b28caa093f1d19771551410063db28e0aa2825fc78651c15450497b6082382a8a0803330ca764c94100666190ec9928200c3f655d351504c196ec2ba6a2a08030fd97745454127e3bb08eab0282008fb8758060504014f10ab00c0a08221fa1c32994410043ec38653288207a3e840ca651040147b08194ca2080e9da0432994410053ac08653288200a7a800ca65104014f300194ca2080e9da0430994410053ac08613288203a768108265104014eb02104ca2080317dce535944103d1f420a6b288200c6f72949651040f47d08292ca2080317dce735944101d3b40ce6b288200a75819cd65104074e902b9aca2081e8fa1073594410051ec20e6b288200c6f729c965104074ed03392ca208029d606725944101d3a40ae4b288207a3e841c9651040147b08392ca208021fa1c32594410043ec3864b288207a3e840c9651040147b08192ca2080e9da0432594410053ac0864b288200a7a800c965104014f300192ca2080e9d207705944101d3b40ce0b288207a3c845c165104074e902b82ca2081e8fa1070594410052f418e0b288200a5d831c165104014dd04382ca208029b608705944101d3b408e0b28824ac74711c1651040f47d09982ca208028f613305944101d3b40860b288200a75810c1651040f47d09902ca208028f613205944101d3b40840b288200a7581081651040f4790bbb2a82081f0fdd776550412ce5a38eecaa08259b3485dc5541049fc6ccbb8aa8209666d61b71550412ce9b32ee2aa08259d3565dc554104b3b2cc7b8aa8209676558f71550412ced3316e2aa08259da562dc554104b3b64c
  | 17 => 0x26a200ab7815c964d441147d0a392c9a88028f61472593510045f43864b26a2008bd870c964d441147d0a192c9a88028f61432593512cd5b40864b26a200ab5810c964d440157500192c9a8802ae60032593510055dc02e2b26a200ab8805c564d441147d0b98ac9a88028f61731593510451f42e42b26a200a3d85c8564d441147d0bb82c9a8802ad60670593510055bc0ae0b26a259ab6810c164d440156b02182c9a8966ada0420593510055ac0840b26a207a3c84dd954d441187ee9bb2a9a88031dddb71553513071b326e2aa6a266e36641c554d4499c74c9b82a9a88035c1c770553510063dbb0e0aa6a24be3a641c154d4401ae0e2382a9a881f0f99175d0f5103e1fbb2a9a1ea2028bc8759143d44b3968e2b2287a88030fdd95450f512ce9a38aa8a1ea20097585dc543d440196ac9b8a87a881f0f99175d0b5103e1fbb2a9a16a2018bc8759142d44b3968e2b2285a88030fdd95450b512ce9a38aa8a16a20097585dc542d440196ac9b8a85a8803330cb764cb5100666192ec996a200e8c3299132d4401d1864b2265a899a3de1971952510047cc36e0aa4a2008f9861c154944bfae6a2382a928803330cb764ca5100666192ec994a255e3b5495260944991f70eaa4c128802bce05549825101d7840aa9304a255e5b5394e60944ab4f50a21cc1288029e61443982512af35a94a5304a255a7a8510a60944014f30a214c1288123ea1c32982510047cc3865304a255a7a850ca60944014f30a194c128802aea1032982510055cc2065304a200ec9320ca60944075e502194c128802bc60432982510053cc2e60b04a203af2810c160944014f30b902c12880ebca0420582510055dc22eab04a200ab8845d560944075e503ba2c1288029e61674582510053dc2ae8b04a247e3b5495160944971f10eaa2c128802bce05545825101d7840aa8b04a247a7a859cd60944014f30b39ac128802aea1273582510055cc24e6b04a200a7b855cd60944075e50239ac128802bc604735825123f2da9ca6b04a203af28194d60944015e30329ac12891e9ea1443582510053cc2886b04a247a7a859c960944014f30b392c128802aea1272582510055cc24e4b04a200a7b855c960944075e502392c128802bc604725825123f35a94a4b04a203af28194960944015e303292c12891e9ea1442582510053cc2884b04a2008fa870c960944011f30e192c12891e9ea1432582510053cc2864b04a200aba840c9609440157308192c128803b24c8325825101d7940864b04a200af1810c9609440117f0eb20c8a8802ae20164191513065a326e2aa2a200cbb641c15454497970c8382a8a89838dd8464551513063a3b6e2aa2a24cc7876dc154544978f0ec382a8a88035c1c470551510047dc3ac0302a200ab88458060544c38f0a1b82c8288023be097
  | 18 => 0x8019b6e7b82caa1003361cf705954200679b8ee0b2a8400cf071dc165508019b6e6382caa1003361cc705954200679b88e0b2a8400cf0711c165508010ff0eb28caa10031bd97725514227e5a3b6e2aa2844ecb4761c554508c3970edb82a8a117f2e1d87055142006d8388e0aa28400cd4631c563508050fd0b3b6a6a100a9720d65d4d4200c5e432e9a9a8400a5d85d8f535080193ae9b1ea6a10038755363d4d4203c76432e5a9a8400d2d545cb535080199ec6b96a6a100a1f21d6554d420154e41acba1a84018bc865d543508051790eb2a86a10023ee0175d85420247c402ebb0a8400af1800c761508011ef0eb08c2a1002b520d61185420461f3aaa9b0284008fb87580605080117f08b8eca9901e2f21171d95323c726196cb32a6400dc832dc1654c801b9064382ca991df17dd773595323b637baee4b2a6400c7b751c1654c8019b6e6382ca990033adc870595320043fc3aca32a6400a7880594654c801b18653a0ca990230f99574195320061eb2ae832a6400d8c325d0654c8010ff0ab86c8990221f21570d9132006e2196e2b226400dc4321c5644c80196ee838ac89900335dcc715913200673b90e2b226400d4c329d4644c80f87cc8ba8c899003530c975191320045fc3ac83226400c3d75590644c80156902b20c89901e1fa1676d51322bd3c402cbaa264078be849da544c8b556902b24a8991bfc30cb549513200666196ecaa264038f6819d9544c8011eb033b2a8990123ea0276551320047cc04ecaa264008df835d9544c8011df04bb2a8990023de05765513201c7a40aecaa264008fb805d9544c8091f100bb2a899003330c8765513203c3e43acaaa26456a7880595544c8111790eb22a899166ad2056455132006e2196e2aa26400dc4321c5544c801b9065b82a899003720c8705513200666194ec2a26400ccc325d8544c8011f700baec2990123e20175d8532006c6196e8b0a6400d8c321d1614c8011ef0eb08c299002ad2116118532006e4194e030a6400dc8325c0614c8079e4c2b80c2990033c58570185320047bc0ae9b0264038f4815d3604c801a9865baac099003530c87558132006e2194e23026400dc4325c4604c8099e4c0b88c0990023ee1d60181320053c42ac03026400cf171580604c80f17d0e194c9a88022f61c32993510451f42865326a200a3d850ca64d44b556d02194c9a8802ad60432993510055d40065326a200ab9800ca64d44b556d02184c9a8802ad60430993512d55b40841326a200ab58108264d440156b0321ac9a88228fa1443593510055ac0c84b26a208a3e8510964d44b356d0339ac9a8802ad60673593510055d404e6b26a200ab9809cd64d440156f02b9ac9a88228fa1473593510051ec28e6b26a259ab6819c964d440156b03392c9a8802aea0272593510055cc04e4b
  | 19 => 0x23ee1d62181540056dc1ac4302a800ad88358860550015e702b10c0aa002bc2056218154006793b6c2302a800eb184d846055001d62e9b08c0aa0023e61e61181540047dc3ac2302a800cf2761846055001ce30a308c0aa1d39cdd461181543cf59c20c2302a800eb17418460550f3d66a8308c0aa1d39c95061181543a7382a0c2302a879eb05418460550015e702aa0c0aa002bc20554181542ff2da9ca6302a85fe6b5294860550091f50e190c0aa0023e61c32181542fd3d42864302a800a79850c8605509757508190c0aa002ae61032181540057940864302a800af1810c860550bf4f50b988c0aa0029e617311815425d5d42662302a800ab984cc460550091f50e188c0aa0023e61c31181542fd3d42e42302a800a7985c84605509757509908c0aa002ae61321181540247d43842302a8008f987084605501187ee9bb2a9a98035c1c470553530045fc3ac8322a660c7476dc55454ccd8e8ec38aa8a99331e1db705515325e3c3b0e0aa2a600d70711c15454c019d0c4382c4a981f0f9d154d85530047bc3ac230aa6008f7815d36054c071e902ba6c0a98029e61720d815300578c0841b02a6008fb875806054c015d104b00c0a981f0fdd77655343006d8388e0aa68670c3f75dd16550c031dd0fb92caa180333dcc725954300673b96e2b2a8600ce472dc56550c019cee438acaa1803391c8715954300675b96e0b2a8600ce872dc16550c019e6e3b82caa18033c1c7705954300675b90e0b2a8600ce8721c16550c019e6e2382caa18033c1c470595430043fc3aca32a8600c5f65dcd5450c9f968edb8aa8a193b2d1d8715514330e5c3b6e0aa2865fcb8761c15450c01b60e2382a8a18033918871589430047dc02ebb0a86048f8805d76150c015e30010ec2a18023de1d611854300572412c230a8608c3e755536050c011f70eb00c0a18230fdd37655352006b8388e0aa6a40187e85dd943d48032d904baa87a900a2f21d6450f520070eaa2c6a1ea40096d85dc943d480195ac9b9287a90034b5537250f5200666b1ee4a1ea4008bf8759064548c18e8edb8aa8a919b1d1d871551522663c3b6e0aa2a44bc78761c15454801ae0e2382a8a90033618c7058d520145f424eda1aa40187c865d743548018baebb1e86a90038755363d0d5200696aa2e5a1aa40187c865d5435480f87ce8aa6c2a90023de1d61185520047bc0ae9b02a4038f4815d360548014f30b986c0a9002bc60430d81520047dc3ac0302a400ad883580605480f87eebbb2a9a10036c1c4705534200c5f426eca9e840287c8759553d080f1b90eb1aa7a1003875516354f4200636b2ee4a9e8400d2d54dc953d080335904baa87a11bf0fdd774595420146f43ee6b2a8400ccc73dc965508019aee7b8acaa1003351cf71595420066bb98e2b2a8400cd4731c5655
  | 20 => 0x3ac28e5b0aa860ab6841cb615509f56b08396c2aa13f99d4a52d85540047b43865b0aa8008f5870cb615509f4ed0a196c2aa0029d61432d85543055b42065b0aa800ab5840cb61550015e500196c2aa002bc60032d85543053ac2ee1b0aa84fab584dc3615509f56b08386c2aa0023da1c30d85540047ac3861b0aa8008f68708361550011eb0e106c2aa0033cd86709855401e7830ce130aa800cf3615c261550079e0c2b84c2aa0023de1d611855400579c02c230aa800af08058461550b356b093b0c2aa0023d61e631855400579404c630aa800af18098c61550011ef0eb18c2aa002b9e09631855400572412c630aa800af38058c61550015e100b18c2aa0023d61e621855400579404c430aa800af18098861550011ef0eb10c2aa002b5e0d62185540056a41ac430aa800af38058861550015e100b10c2aa13b95d4e531855427733a94a430aa8038f6870c861550011eb0e190c2aa13a9da1432185540053ac286430aa866ab6840c8615500156b08190c2aa002bca00321855400578c006430aa84ea7685cc061550014eb0b980c2aa19aada1330185540055ac266030aa8038f6870c061550011eb0e180c2aa13a9da1720185540053ac2e4030aa866ab684c80615500156b09900c2aa00e3da1c20185540047ac384030aa800a7985cc360550015e502186c0aa002bc60430d81540053cc2e41b02a800af28108360550015e302106c0aa002bca0663d815400578c0cc7b02a800aeb8258f60550015d104b1ec0aa002bce0563d81540057840ac7b02a800af28198b60550015e303316c0aa002b6e0d62d81540056c41ac5b02a800af38158b60550015e102b16c0aa0039c5d761d815400758c26c3b02a800e71851876055001ce2ea30ec0aa1329e61773d81540057940ce7b02a800af1819cf60550c34f50a39ec0aa1329e61473d81542655d420e7b02a861ab9841cf60550c3cb6a729ec0aa1329e61772d81540057940ce5b02a800af1819cb60550c34f50a396c0aa1329e61472d81542655d420e5b02a861ab9841cb60550c3cd6a5296c0aa0023ea1c32d81540047cc3865b02a861a7a850cb60550014f30a196c0aa132aea1032d81540055cc2065b02a800af2810cb60550015e302196c0aa1329e61771d815430d5cc26e3b02a84ca79851c760550011f50e18ec0aa0023e61c31d81540047d43843b02a8008f98708760550099e0c138cc0aa0133c18171981540067938ec1302a800cf171d8260550011ed0fb0ac0aa0023da1c61581540047dc3ac0302a800af38158060550015e102b00c0aa15a9e61676181540047cc3cc6302a800af28198c60550015e303318c0aa0023ee1d631815400575c12c6302a800ae88258c60550015e702b18c0aa002bc20563181540047cc3cc4302a800af28198860550015e303310c0aa0
  | 21 => 0x400100200b00200100500f00101100000900400300000d00100700100001100200a00200600702600000000700800200900000400101200900200200300800900000000000400000401000200000700100a00200100100704000000500000700003501700001000000000500000a00800100b00100700100200300200000b00000002200300100000000a00000000200000100300301703600200001000100600000a00300c00200000000103a00001900800800000300000000500100000000200401c00100900100200700000300900002000000600100100b00700200400501300200e01400001100700600800d00900100300d00600600a00000000900000500a00600a00000000200300300100000701200400500100c00000700100000200000000100000000000000400200000300a02b00200000000001c00000001000500c00a00000401100300200000200000000000001900000200500500000200000000100001300500001100000302000100000b01100100000601b00000101200b00001400000300000305e00500100101200001100000000100104300200900b00a04900000000001300100000100000000000100000c01100600302600301b00f00500100300000000000600500200100301700100000100201800100800100000c00000000000000702500d00500100b01600100301600f00300000000201300400901e00001401000100000200200900002800101a00000500a00300600400100001000d01600000000000100403301a00400400200800000100c00000200200500200c00000201400500000900000001200d00700300400000400500000000000701800800200501100100300300000000000800000502500000900000000200d00100d00400700000001300100002700900a00100500000000400000301900100600401900500900c00100300e00100700300400000400100100800100200000702900000000700400200100000700000000600600400300400100602c00100000001000200000200a01000000000101001200000000400000000500c00500b00e00300f0030010270000010052ec2c65b1aa800a6d85ccb62550014eb0b98ec2aa002bca0031d855400578c0063b0aa800a7585c8761550015e50010ec2aa002bc60021d855400579404c7b0aa800af18098f61550015cf04b1ec2aa002b920963d855400579c02c7b0aa800af08058f61550015e501316c2aa002bc60262d85540056bc1ac5b0aa800ad48358b61550015e700b16c2aa002bc20162d855427d5ac26e7b0aa800af2809cf61550015e30139ec2aa13e9da1473d85543053ac28e7b0aa860ab6841cf615509f56b0839ec2aa13f95d4e53d855427d5ac26e5b0aa800af2809cb61550015e301396c2aa13e9da1472d8554305
  | 22 => 0x4a00022fd58222b40d0001332a77598175cfcc8b65788d346380003180fe00008420000000ffa65424825d4f3610f3e000780004ae0b09c4c0009e05ba9fd07c045116bad5884266a301a5cc000000000288c00000016f1de45a68ef0bb81546202ca42a0018a484ec05ea2215c84ca10c28d498a3f3166923077442037404088bc5580760cf864ab1c0c415ac17482a13d0a002ca972522800169055419b11a966aa4413009dd2444130d1800102e16e525ad5000000006b0dc81980000000000000000000158c250160236800110a76f0f480000000ea00000000009231bb1a2c5f6381441000112c61e0002a085e21b95679524f767303a509e48fe54a5180f2458e8971fe263430872c0001d2400041b04d13684ba7934181f907c242401714b8fce4bd0000a509343390001dcd4922230cc80005b6b673c400000824fa509809cc0e00000000000884f1238800086800000400f00000700300300a00100800000000000900001000000000001c03900300000000e00000400200d01000000d00900000000e00801500300700300900000200000200302100800000700000600800200000000b00701200200a00b00000100500300100100300000800001400400100802800100500300300700801700300700200c00700303000100000000100500001600400300000100300000200100900300200200000f00102200400300100a00900300500b00300500600000200500000000d00501600000201f00e00000100d00600100000200201501200000400100600100000400300100000604a00600000b00e00200000001802200a00100500100301800600000000200001300500100001a00200100001300200100001400d01b00000200200700000100000400100100d00001001600100f00400a00200100c00200500600700001900100000000200000100300900000300700300000b00f00000000100500000200e00000000002500300800200100200e00a00000500e00b00200c00b00400100800200100a00300000600100400100200500100100800100000500400b00000000000200700200200100400b00300000300900200300000300a00600700001200900100700300200100200700000100300900700a00000000400200100500500000601000100000000c00800000500d00100200001100300902d00002b00f00400e02300500100a00000200400800501500300100700200100002100100c00100f00000000000000a00000e00d00000500000800000100800000000200100a02001200400100a00200300900300200900100300700100000300100000100000c00000000100300000300501400c00000000000100100100300000000000c00d00f00202100000100400300100200401200700500000100600400500100600100800
  | 23 => 0xd88af467f59d2bc8290628307a67c1f04e344c1ad122e84e4be9b8d2725be42e08583c68eb1171968170570003a1b930222c18b092c4264154679aacd300001690c313c643f0a517e0000a762f686395a000039a80007187cd59610b40006514ea8160000b1d10300000000002438c2c0ca6ca4fb88804425e9000198c0006d14c800000000000000000a2a313000000000062a28807a019c0000000ba8830a8a00016014c642f43b0b4400000007d1fa9466b5100000006ac0004a300000000001ee8000e84000515824d0520000000000000000018a36034eae322700000006450000f2c94815f2ad8000000387000150c93c0d92b4a0f40002a600000009ac6574e503040006e5402800000022d0000e5c00075400019050baa970000a90f621c810a0eec2b04de1440000a368b322f800032c2cf39000000003444fa15811645d90ab9a8cff085000000000004df1da2a1114c292000299000095f0000cc8a6e95134c9aa8dbc000000135541e4b6135800086c000000169cf8200049b1e40b1e00029100010587120001c349fc9de18c800027644331f000167e7ef11d1b9000030000006551d894b1f628640008d01df85491803a80a594d89087b4456ac880f890e000000125400000009cd0b0aaa0a391e96507643ea800061a8a148228d0bea1d51ccaa809c219c0002d7c0002c921c8000000000000000117813135ca288ae873e1c22c84000a6c17fa89c15a4630bf800000024400000000004c1010a4f89160000bf00000002f554a000081e8003f59dc111e07624a251d06a9711c00a88e88a04550825c5647314c49a7c73aa8f3bfa39499e12f00022e816a77a315965c35e0c214b00001a42e90000000000000407a1a438a6844081184f9000000000006fc2ef4ba2b700022aa2e3287481825954f8318dea13d5ae8ecc3ce3332d8ab00e0800016a018154e0980c7813cb423512bc8000f184b30cb8c286687012e6a4908b20002b60000a345a359916816e256814dab8505600000000004da6ad02a25515a88e30000b949b800038502a80009914051ac517040635622ac6bca2a12c00000004e93cf9e14cd61cf0bb00005222020000d24e1c9984e69a8867a88a3f12d0c770b0b1710f693489c557401bc57c09b4e080b474421029d2608000000000000000000000023d821a9450de0dccd4026652c87b0b3826223d8a0c95096455a80001ce168282aafca4a25e00000015000a006d1c14fc60005621c7d3dc201000184caca8e108400002824dd4bc9fdc0000b71d18000000a080001ca800076b0e900002723e73eb81c02b23cd4639d4c0000004b2ad5c9d699b0002bad2b00000f8875818e4783909260000000073169926aab40d800011ee4c300009c00007b55b58c184600ab1b3a3a0a6421c2ed17394ea04b1980500a10b
  | 24 => 0x3fb00006fc000b7f37b25a8d2e49643aad6936814c4eb109c00012c3a7a07408e1db0fb29610cc8b10d98a602ac7af0dc000000000034191d055c59641c9740ef858c02296d08e6b0333f04645e06f307d800000000039b8d08000099340a398a5600000003100009f2000232960c0320002b5c0002b138423cd48000025a27611766f2428a808000312000000000000000a8000000a4804015780006cf0000000000a680000000932aa60001aa426e88900021b41863ff02e0000000328108a06114846e30a998858264e3a39fd40001e45a3a8f08320004a9ac084844600002af106800035201200007410001b6d6d296e4d727f43a247658999e000000053c900c0001e20002280c6e3bc1d30cdd2e021b000000041200018b9f809e8b522858000000172000139cd2681e13497fc03a8db02f8000000a1117a23c80000002f9002000000003986841167ab1a29004076a7f44a80a00000d10fd9e5c54a4c837796b80a400028880002f4b2640724cc3929da0000000f5294032c927ce9c00000029752a000027100000007b800000009120a72fe8ba03140f5033072c0f6a5134e0fd0dfe44c17cade4e3ca9a4cf08013e63a744327f8fec7861ce26c4f469e7000000169c3f60d900000ea59f50380000009f6438a3c00004971db8920d70000000028400000000013b505000028a018930c7091ac80e13b20000000a8c00000032d97a0ca64790c48000bfc3dc37824ec0008f1000237800000000028c40740000000000000000000299800000057a84e03620000000000f663b200000000000000001eb0e7a24634527c00ae4b93010f08c4294f08f8000f487dc5368468ae434f093000070ca010001c006da2670002b7cea001417617800545b62ae9af85ccaea00014800000001610000d8e000000000119025600000000002b94ae92e0000a3d00f800000000000000000000000002c380ac9ec43f13dcf4c9d24ae00012fe0002e600d0000adb0ffac1568a0000001bac1f800000000000000002d280ad4d67dd03480000000000000f1cd9233a000208c00000048d10c8a044c62eaa8dcbf416c3fd91480008633700fa006c12b0000ded25e00000001295f268726c03349d40000001a396cc00035d235124c07900018155527020001c991547a725600000000000000874eb80683ea03807ee4f600029a90020002b0ab644681244bf0740eb074c17700000006a537700016f6000154829800000000000000004111481ccc1585030001d20000a4a01e1a313b83ea1e723ec8ce39a00021bcadc85e000021c51442657b223885241a1dc9b84000b1f2e4000000008110c8000ebe00000023a49440002d1093088c0003c0800119a6cb00c1929128000000000000072f14a817451e3a438c800000000038dacd16003ab480897c00079e2539
  | 25 => 0xa9891acb120db161d4187954b10da4ed495a27e0a10e9696000003bc96a0004bd1d946861133d00830d7898344188780008261682beca8000000024fc00009d231000081667355c083c0002e412a0000df685726813500000000000ec400000000018293cca8536126e08d2228477212c000601000070523a1a8000069071e36e4ee98d51a4a4f00000001c401600016ccd90121011a0851f8a21000112cec661a26c8000e2066d00000000003964e9874c56e15e42400002202ab20e000078000022e100800000016c1c3c0000003ef000083e8e2000061c0009e24b41438fdc35c376800000000032000016c4a424339f614fc00019496c030446b00009140442081de8404df48454a50e4c0000000001e28902b3c5b500003f400045aa6e834c93d2d581fc0007bc2118e94000757430a82c2b691921f2050b2674000007f4000685577224947eb2452687a8be600014980009fa2b60298fe400078b4daa30d54868647d1f6c612711000054c0fa2a85bd2365310b313e9a2b800004000000015560004d827e0c32276283133836a67142620c41960d31ba8000e063200001fa546c83f52f0be800000038a9dd165c19a4671788dc4000000258d40c8ea289228d39008658c0b84a4c53b564265416600004296b14ca0005589870704b6e41d179111a03f1bc1c71008000002071d56e8fd00026f167aa173f080008508b94f20000000000091000152a00053d80000008a9000269400002500000000005352e880689541ae35aaa4561e7893c2176c9a431b3bb01e00000001c4986000095e3ca0f6502c00053009b80000ed57eaa60dd489d4d0973c6a0b6f00018c87520001c69f38a966cd19d9d78eda5b21f6ac7800040d0002b18bec82d18a886800000036b98f498800006807f8d8a0000002ad905c0592d420f16bc00029882d87c64ad4dd8da00ee1294250000000000482800029260829407d4bac5f7000202c63a984000241c6ca5bd1580b5422e5f10001ee87cc0004df84315da00000001789249142468afd192000000134409a97828e833cf4234a1bc8000000321000000000018633624313da46c084aba5396b44000000c00078d2c5800000019d3390000e0c84632a9e706460000000f101e06b60002df0fa2b4d33e1b4950e0003fc84450fa9ab23207610ac55300000012688412c280000006560001840a9aaf0000266826c000000199c6cc94200018e40000003bd80000000bf24280000000002648000000000162a24470624e3d51ea000000035fa08800065c1191b3800438a57108f1486000000053498e6d61d81a24e7200028b9b640e42ce1d02dcc07a14500021488100000002db40000003e3000120000000024ac3e096953795c488e92c4d480013d026f30000004e272500000013383d144d05894f008e09a005c000
  | 26 => 0xab5808d9c9c8582550a72c1c0008f40ea24953a800043da8e0942000588000051a66500027f115e00030a1cec000b8217910c53fe4930c928241d0527000055132c5c30000000cf42c632e94cd22a7fa2cc982cd9802941b9a488ca374125048cffc0ff00005f400098b4d900000a00dd290a835242a3b5a1113ca604e502180008deaca00008f80006500000f6c0002da546849c65e69d0359fc400002c3c780f93920003ed00000386b200001a80000002ad28516d8327354147d2b214351108c51c0a184c52374fb27181d7035c00045a21818b80000001298d84bf624932324b82660ca2a616e40000a423ea8b55e800002d14647306940000d896d000052fa6dc0000000708c106ba0000001e394a000008310e834000054092ac0005042a90bcd45c32a000035113c09646b9e60fac8f921bab1c7206600000000fca0002848fb8000aba02618440005441be2ca4a7c9b3002a7855e6b5c38d1798ad495b4202c0565a5eb1e79bf82249064d60c505b24481e1800000009140a885cb7e19f05a000000000055c9b987de000000096862291f000000000000000014fcb96aec5be84e9018592507139830230321728c80000000001a6c0004142862c80000591269806c9e0556175aa8d02677e1b511f85b8000566952118c1de59180015869ce09000003ca20b000000000000013d8e7c5960003b496792ec1bd4df22a000033f5b80000c6c475369a194c86b632ef23044a2b830001fc032017b0fc17d0b820002c700000009d708a09a8200abe0e50a84de827211c259d29841d40909d4288a6940c924508663f4038d048b6b3603881b55f0ad300000004fa23618780006ae6c4211000000000046d00012500b128c1dd43ee64c4c615143cc2044409048b5218c52a85980000000001d98ee40000c0289000000037880000000000850bd800048e000261cf0491b31d98b53280113fe00009ae0004b6800086600058ca7006045c70f72aec6a82270001618000a3e0000000000000500295d5929030e607f040691c43415f4e4878751415f8a58a1e000002450e0002ceaddcd6011d29a12a4c0879a04a83c8a1a4861b22d18a1445022e96240180ee4e800009e443544200004d0a7d2b6ab448e449d1ac13d439a99d23b80005f85e30001ddc0000001e526807c427f0be0000e503013c1a95042a29f013260000089c4841ed87a469e4480acd18831f17f2c586a400000013ed536609000000170257710925b000072e45a00008d05c95179610482a92586000000000037380bc0000b20f78f4cdf858325d827127097b48b216c8a88e71d6000000045845f0a050f43d41cdaca8ed87a50d280000003f24381e885f07b01be8ad48aa929000028cc66a4711d80cd4b427e00000000001f41c5913406a36c000211c6fe0000fc800047257f2e2
  | 27 => 0xe80004f80bc147075d0d6000000000093859539112c8060a8b0000c396a01dd00000013d40003d6800041a0f94810a24e524db01b86f8000afe5148f9402022a11aaa787fa8061432bf0bc29a751d1cf11008791ad800104800015d2440eaca1b244041ca000000002230f9875527215f0ef0a965b018883564572dd0ed5282a5b4939a541caa4c30d8000000ab245b8000b5e5f90ba0000000b3b000000000000000780000000004d682316c82504e7a1350d800002d977095e0000001d68f727c914c800000093c3c8ab7482e84f12d919863c0000002744e166311071e6477ca391a4133027e19b327915825432247f1948a1e0d54a20000a7055f0788dac7425ea00013a0f6420a52900011a69aa26020444c683e30ba2b15fe0002c121f134466600000005860130a88660f3a7803a92008db06583322dd89623d04e180000008c530b05680846ae48928b07b065e3b3ab4817c1320000c145684a525b93e158467900000000004e0085845800006c597a168558000544a2c0e863e90a7ac35010ab300027d426a000251a1880001554e200000003af3e821fd2ee00043b89b0db458a2abaa38f5c8f51eb0af4000642412800066a0001e40c1cdd86d514f018d03817100000000002dd0101d353e2a1c0000d3000011507b0000af660d4a714a40001b41ca0a9c0005c40718000f840e91ca85a876c9db054060c87098f22026bc35a73442210ac00000000000000000001ad29c452e3de485a17ce702852021db864832c3e18af05be6270002d0000054e54329d0f7c87432f959036e74533d926cf7a6253dfab2d3d2567113156561470c488902513e855000130926e11859c16040a297c2502d5433c68d0d60001012a125ba02b80920000ef8000000000000089081c000000285962252d50aa7ec6706d02cda7bcc74aef279a6d83228c241920cc8a60001e2a70966610513c174d0e417958ba5aca787174dc99a0d006fd04808bc80a15d15d95d548c5013e7a5483860940002390f9480d55400010920c9127800091e23d29799d14dc8bd18c20bc00068f3b89a6800000034b2c6c75a1694ef96ece6c7c503723e069c07a4852534cdc5131112ac000062c2e005ccb1a5ca0000000518b720ae21a868e59825f953d0f00003308e78b484cb4fc8c200000fe0002c9d116aaf595ae00c9293a1c4081ce0e24d307000000000059c959800093136e2d8459059a52e264914a10e054989828490941027955200004aba44c0000000b8207ce460000002b615f400000016a80005fc0b3ac94aa22e042980006a66d4000105955843c0491edd59c6c145380006e20001660c9960820553910947d629a2e10ff88f80dc0ec95882c60db2ec03dd136a0531e1a9d10e81b0e30780d5e6c62bb12f07246bd4a42b9cfd872d0929fa14a64952f72b587a
  | 28 => 0x1a5827948260606c000046e3f01621750000b5b28e0000cd200008187ace2c00010f80000c237a00000002600002f80000974b144cba1cc1080002452370a725425129a440c81503b400000000000c2aab4e8c000000000130aa9c0b6800028c0bb3f92bdcb6a71d000188c0005ad5bc0000d662af00002216128cb04f806504e66f4018a746aa0003aea8403260003e2154018a00050f80002f04cd00007845402740720ae037443d4f5889490400000024b40002e31d500384b811e48c1650ec000000021800000005628cac00007e3959f7c00051e32412f9698074000000169e000000000154a507449800157a5160000b015323c1546000000064d3121cc8f2c3df52b0a71434993291890d2dea205a59b000009a646617bc00008a02313e5406a7a49800009dca6147fac2121e3911a3271d23c55556f00000001f3277a37c5da55c361830166e5881a002bc25a36f0000b5800067057311253986b75ac80005fa04e0001f1c78c00001200e42ea2642a3a7e8000000000187400063833ba4c953a37005283ac0000c800000004c2000000062c00000000000000000000000000dba00000000010760001eb84701122330000cf0000000141179d55c4b037c16e16822e72051df521a2f755102886c0a7c00009000003850002b680005e50d50208380257203a9cc55a6903ff8000634ae032399d800019400026f4b7800000011100000004aaad247e232e00000280160002a305911aa0002082c680005ec0092d94eb683600027181be573374988000008d000000000062f295187d51023f42c8d7d2c200000000000001ed53386a41e81bb00000012ac0de24180000000000e710780000000ee23b46ee6f731a2480d040b92e926a00006123258000000247468800150608336f95e065a0005660000ec23fa3f9800027873a00000001fa1c256a99f4b20265079871080016f30611282081f200000004520b034404b8bbe000238191000000025300007eaa700000000000a933ac80006c600033a84f8e7e714432000000016b00000000000000ed019c0000005a9800162aa0a000250c662a263f69f2c00008f00000000009492400000000b7e2a0a264ade18d2229e489fe7510000000c5228b0d11104d425dd59f110800043b2151a980005b7527263800000d1290e393463cc35d80010706f95729f480000004b300000003e429
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x4c207a6e008c0092686c609e1824407000a258823aa0000046502e1c94aa2a4274000000000cb69c4e003e3454720e1e16960000000002a65cae00b4002638007600002ca87c786a6688005a00982822a4529a640030448eac48005ec2bc141284c03c1a00ba000000080610be62b8003690868056047e00324a00b0008a00b20a0002090208160100060106090000040001000007000108010d02030a020402050070355163dc943d4801c0d54d8d72d4d420050e241655d0654c80183575205641913200471660321c5544c8011c9980c870551320052c251615c0614c801870855c560181323a70c990711c154d44f3c32651c47055041006a4204805516310401c155458f7154c41006a8204805516210401c255458b71548413de4ce1c8055351104018b08121d54580410058664c755516010401629921d554580410062c21f8155160104019848750d424c521005a1259435093148401c15545cd6110650007095517258441940f7c32641c0715505000694200815516314001c195458f7050c5000698200815516214001c295458b70508500061c200875516114001615931d154584500058964874551611400187087e01545845000706551635c24114001c295458970904500060761d5458c4114001c0d5458d72104500060b61d545884114001c0d545cd621045000705551735844114001c25545c9611045000706551635c04114001c295458970104500070c551615c041140f3c32651c470553403ce8ce188155050d00019488754d524c1200059225953549304800124d980c8654c910004a36603219132440e5c327019464945100055464c805d441440015619220175105102541da5b87d9441440018358719065105103d70c9c064194414400143597197641051000705190655cc414400149496551731051000709190655c841440014a4965517210510006645d18310750440019a17460841d41100056464c815d050440015a19220574141100060e61f65190504400183987194641411039f0c9c4651905044001c1865191731411000516259545cc5044001c286519172141100051a259545c850440f5a328619251141100065461573d045044001961855cb41141100064c6157410450440019318755041141100058c2595410450440019917460c4114110006c45518310450440011d1985cc411411000654615731045044001d11545cc4114110006685d1821045044001b21546084114110006705cd8210450440011e1985c8411411000658615721045044001d21545c841141100067060d721045044001953855cd311411000658e157248450440e7c3271194649011039f0c9d865106404409b0b89721954501100064c21d54545404400163096551515011000664dd18310530440019a3746084148110
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x2000101c4b028a84986000800061090e4b286a12629080304887259535493048001818c392caa0822822000a842995460c411411000622330aa2e6208a088002c10a6551731045044001510532a8c10822822000e4055173608411411000624330aa2e4208a088002c20a6551721045044001c80aa306b90822822000c0c21c965515150110
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x20430000601198299545cc4114110005800b655173608411411000602198299545c84114110005800b6551835c84114110
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x4
  | 3 => 0x2
  | 4 => 0x1
  | 5 => 0x4b
  | 6 => 0x4c
  | 7 => 0x5
  | 8 => 0x6
  | 9 => 0x94b
  | 10 => 0x94c
  | 11 => 0x124b
  | 12 => 0x124c
  | 13 => 0x138b
  | 14 => 0x138c
  | 15 => 0x98c
  | 16 => 0x128c
  | 17 => 0x9cb
  | 18 => 0x12cb
  | 19 => 0x10b
  | 20 => 0x10c
  | 21 => 0xa0b
  | 22 => 0xa0c
  | 23 => 0x130b
  | 24 => 0x130c
  | 25 => 0x180b
  | 26 => 0x180c
  | 27 => 0x14b
  | 28 => 0x14c
  | 29 => 0xa4b
  | 30 => 0xa4c
  | 31 => 0x134b
  | 32 => 0x134c
  | 33 => 0x198b
  | 34 => 0x198c
  | 35 => 0xb0c
  | 36 => 0x140c
  | 37 => 0xb4b
  | 38 => 0x144b
  | 39 => 0x28b
  | 40 => 0x28c
  | 41 => 0xb8b
  | 42 => 0xb8c
  | 43 => 0x148b
  | 44 => 0x148c
  | 45 => 0x184b
  | 46 => 0x184c
  | 47 => 0x2cb
  | 48 => 0x2cc
  | 49 => 0xbcb
  | 50 => 0xbcc
  | 51 => 0x14cb
  | 52 => 0x14cc
  | 53 => 0x19cb
  | 54 => 0x19cc
  | 55 => 0xd0c
  | 56 => 0x188c
  | 57 => 0xd4c
  | 58 => 0x1a0c
  | 59 => 0xe8b
  | 60 => 0x18cb
  | 61 => 0xecb
  | 62 => 0x1a4b
  | 63 => 0x74b
  | 64 => 0x74c
  | 65 => 0x104b
  | 66 => 0x104c
  | 67 => 0x194b
  | 68 => 0x194c
  | 69 => 0x1a8b
  | 70 => 0x1a8c
  | 71 => 0x94e
  | 72 => 0x94d
  | 73 => 0x130a
  | 74 => 0x14a
  | 75 => 0x14d
  | 76 => 0x198d
  | 77 => 0x289
  | 78 => 0x28e
  | 79 => 0x184e
  | 80 => 0x14c9
  | 81 => 0x10a
  | 82 => 0x1489
  | 83 => 0x2c9
  | 84 => 0x134a
  | 85 => 0x124e
  | 86 => 0x1049
  | 87 => 0x1a89
  | 88 => 0x138d
  | 89 => 0x104a
  | 90 => 0x194a
  | 91 => 0xcb
  | 92 => 0x168b
  | 93 => 0x8c
  | 94 => 0x150c
  | 95 => 0x10e
  | 96 => 0x19cd
  | 97 => 0x180e
  | 98 => 0x24b
  | 99 => 0x16cb
  | 100 => 0x20c
  | 101 => 0x154c
  | 102 => 0x2cd
  | 103 => 0x58b
  | 104 => 0x178b
  | 105 => 0x160c
  | 106 => 0x5cb
  | 107 => 0x17cb
  | 108 => 0x164c
  | 109 => 0x40c
  | 110 => 0x44c
  | 111 => 0x1a9953
  | 112 => 0x1a9954
  | 113 => 0x10152
  | 114 => 0x2c291
  | 115 => 0x14112
  | 116 => 0x2c155
  | 117 => 0x10296
  | 118 => 0x1a1654
  | 119 => 0x1a57d3
  | 120 => 0x17da53
  | 121 => 0x28116
  | 122 => 0x282d1
  | 123 => 0x142d5
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 3077
  | 6 => 9366
  | 5 => 2948
  | 4 => 98
  | 3 => 12
  | 2 => 4
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
  | 2 => packedAt gbK2 (i*92) 83
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
  | 2 => gbHint (packedAt gbK2 (i*92+83) 9)
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 9 => packedAt gbK9 (16+((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 2)*1) 1
  | 8 => packedAt gbK8 (1700+((h/20+packedAt gbK8 (1560+(h % 20)*7) 7) % 88)*7) 7
  | 7 => packedAt gbK7 (126149+((h/1025+packedAt gbK7 (113849+(h % 1025)*12) 12) % 4062)*13) 13
  | 6 => packedAt gbK6 (493276+((h/3122+packedAt gbK6 (449568+(h % 3122)*14) 14) % 12364)*15) 15
  | 5 => packedAt gbK5 (185716+((h/982+packedAt gbK5 (173932+(h % 982)*12) 12) % 3891)*13) 13
  | 4 => packedAt gbK4 (7116+((h/32+packedAt gbK4 (6860+(h % 32)*8) 8) % 129)*8) 8
  | 3 => packedAt gbK3 (992+((h/4+packedAt gbK3 (972+(h % 4)*5) 5) % 18)*5) 5
  | 2 => packedAt gbK2 (372+((h/1+packedAt gbK2 (368+(h % 1)*4) 4) % 10)*3) 3
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffff0f83e0ffc1ff803e0f80053238fc9e7ccc
  | 1 => 0xf803f003ff07fe0ffffff0000ac3cf30e38ff0
  | 2 => 0x3fffc0007fff0003ffffff30c0fc303f0ff
  | 3 => 0x3fffffff80000003ffffffc0ff003fc00ff
  | 4 => 0x3ffffffffffffffc000003ff00003ffff00
  | 5 => 0xfffc000000000000000000003ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x687b0381642ac85684974a82801218548e3ccc
  | 1 => 0x708b3000a5214a4723ab5a050042cb30a285f0
  | 2 => 0x211154a40005ad62090c632993040dc103d055
  | 3 => 0x4222a94ad6b0000412318c562c0b7002f400aa
  | 4 => 0x440ce7318c631885c0000183fb00003596a00
  | 5 => 0x8780006010802100600000603feda6a8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeefeeafeecf000feeefeeafeecf000feeefeeafeecf000feeefeeafeecf000feeefeeafeecf000feeefeeafeecf000feeefeeafeecf000feeefeeafeecf000, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_17019
namespace PEqualNP.Outside.L_meta_17019
open PEqualNP.Outside.L_meta_17019.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 2 := bs0_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 6 := bs0_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 1 := bs0_5_0
theorem alls0 : ∀ k ≤ 5, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 2 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 6 := bs1_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 1 := bs1_5_0
theorem alls1 : ∀ k ≤ 5, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_32 : Interval s2Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 64 := (concat bs2_4_0 bs2_4_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 40 := (concat bs2_5_0 bs2_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_0 : Interval s2Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_6 : Interval s2Atlas 6 0 1 := bs2_6_0
theorem alls2 : ∀ k ≤ 6, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
  · exact alls2_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_32 : Interval s3Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 64 := (concat bs3_4_0 bs3_4_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 40 := (concat bs3_5_0 bs3_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 1 := bs3_6_0
theorem alls3 : ∀ k ≤ 6, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
  · exact alls3_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 2 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 6 := bs4_4_0
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
theorem bs5_3_0 : Interval s5Atlas 3 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 2 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 6 := bs5_4_0
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
theorem bgb_2_0 : Interval gbAtlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 4 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 12 := block_range (n:=12) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 12 := bgb_3_0
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
theorem bgb_4_96 : Interval gbAtlas 4 96 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 98 := (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96))
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
theorem bgb_5_2944 : Interval gbAtlas 5 2944 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2948 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 (concat bgb_5_192 bgb_5_224)) (concat bgb_5_256 (concat bgb_5_288 bgb_5_320)))) (concat (concat (concat bgb_5_352 (concat bgb_5_384 bgb_5_416)) (concat bgb_5_448 (concat bgb_5_480 bgb_5_512))) (concat (concat bgb_5_544 (concat bgb_5_576 bgb_5_608)) (concat bgb_5_640 (concat bgb_5_672 bgb_5_704))))) (concat (concat (concat (concat bgb_5_736 bgb_5_768) (concat bgb_5_800 (concat bgb_5_832 bgb_5_864))) (concat (concat bgb_5_896 (concat bgb_5_928 bgb_5_960)) (concat bgb_5_992 (concat bgb_5_1024 bgb_5_1056)))) (concat (concat (concat bgb_5_1088 (concat bgb_5_1120 bgb_5_1152)) (concat bgb_5_1184 (concat bgb_5_1216 bgb_5_1248))) (concat (concat bgb_5_1280 (concat bgb_5_1312 bgb_5_1344)) (concat bgb_5_1376 (concat bgb_5_1408 bgb_5_1440)))))) (concat (concat (concat (concat (concat bgb_5_1472 bgb_5_1504) (concat bgb_5_1536 (concat bgb_5_1568 bgb_5_1600))) (concat (concat bgb_5_1632 (concat bgb_5_1664 bgb_5_1696)) (concat bgb_5_1728 (concat bgb_5_1760 bgb_5_1792)))) (concat (concat (concat bgb_5_1824 (concat bgb_5_1856 bgb_5_1888)) (concat bgb_5_1920 (concat bgb_5_1952 bgb_5_1984))) (concat (concat bgb_5_2016 (concat bgb_5_2048 bgb_5_2080)) (concat bgb_5_2112 (concat bgb_5_2144 bgb_5_2176))))) (concat (concat (concat (concat bgb_5_2208 (concat bgb_5_2240 bgb_5_2272)) (concat bgb_5_2304 (concat bgb_5_2336 bgb_5_2368))) (concat (concat bgb_5_2400 (concat bgb_5_2432 bgb_5_2464)) (concat bgb_5_2496 (concat bgb_5_2528 bgb_5_2560)))) (concat (concat (concat bgb_5_2592 (concat bgb_5_2624 bgb_5_2656)) (concat bgb_5_2688 (concat bgb_5_2720 bgb_5_2752))) (concat (concat bgb_5_2784 (concat bgb_5_2816 bgb_5_2848)) (concat bgb_5_2880 (concat bgb_5_2912 bgb_5_2944)))))))
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
theorem bgb_6_6112 : Interval gbAtlas 6 6112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6144 : Interval gbAtlas 6 6144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6176 : Interval gbAtlas 6 6176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6208 : Interval gbAtlas 6 6208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6240 : Interval gbAtlas 6 6240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6272 : Interval gbAtlas 6 6272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6304 : Interval gbAtlas 6 6304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6336 : Interval gbAtlas 6 6336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6368 : Interval gbAtlas 6 6368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6400 : Interval gbAtlas 6 6400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6432 : Interval gbAtlas 6 6432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6464 : Interval gbAtlas 6 6464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6496 : Interval gbAtlas 6 6496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6528 : Interval gbAtlas 6 6528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6560 : Interval gbAtlas 6 6560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6592 : Interval gbAtlas 6 6592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6624 : Interval gbAtlas 6 6624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6656 : Interval gbAtlas 6 6656 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6688 : Interval gbAtlas 6 6688 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6720 : Interval gbAtlas 6 6720 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6752 : Interval gbAtlas 6 6752 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6784 : Interval gbAtlas 6 6784 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6816 : Interval gbAtlas 6 6816 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6848 : Interval gbAtlas 6 6848 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6880 : Interval gbAtlas 6 6880 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6912 : Interval gbAtlas 6 6912 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6944 : Interval gbAtlas 6 6944 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6976 : Interval gbAtlas 6 6976 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7008 : Interval gbAtlas 6 7008 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7040 : Interval gbAtlas 6 7040 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7072 : Interval gbAtlas 6 7072 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7104 : Interval gbAtlas 6 7104 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7136 : Interval gbAtlas 6 7136 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7168 : Interval gbAtlas 6 7168 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7200 : Interval gbAtlas 6 7200 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7232 : Interval gbAtlas 6 7232 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7264 : Interval gbAtlas 6 7264 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7296 : Interval gbAtlas 6 7296 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7328 : Interval gbAtlas 6 7328 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7360 : Interval gbAtlas 6 7360 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7392 : Interval gbAtlas 6 7392 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7424 : Interval gbAtlas 6 7424 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7456 : Interval gbAtlas 6 7456 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7488 : Interval gbAtlas 6 7488 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7520 : Interval gbAtlas 6 7520 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7552 : Interval gbAtlas 6 7552 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7584 : Interval gbAtlas 6 7584 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7616 : Interval gbAtlas 6 7616 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7648 : Interval gbAtlas 6 7648 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7680 : Interval gbAtlas 6 7680 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7712 : Interval gbAtlas 6 7712 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7744 : Interval gbAtlas 6 7744 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7776 : Interval gbAtlas 6 7776 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7808 : Interval gbAtlas 6 7808 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7840 : Interval gbAtlas 6 7840 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7872 : Interval gbAtlas 6 7872 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7904 : Interval gbAtlas 6 7904 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7936 : Interval gbAtlas 6 7936 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_7968 : Interval gbAtlas 6 7968 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8000 : Interval gbAtlas 6 8000 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8032 : Interval gbAtlas 6 8032 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8064 : Interval gbAtlas 6 8064 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8096 : Interval gbAtlas 6 8096 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8128 : Interval gbAtlas 6 8128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8160 : Interval gbAtlas 6 8160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8192 : Interval gbAtlas 6 8192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8224 : Interval gbAtlas 6 8224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8256 : Interval gbAtlas 6 8256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8288 : Interval gbAtlas 6 8288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8320 : Interval gbAtlas 6 8320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8352 : Interval gbAtlas 6 8352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8384 : Interval gbAtlas 6 8384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8416 : Interval gbAtlas 6 8416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8448 : Interval gbAtlas 6 8448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8480 : Interval gbAtlas 6 8480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8512 : Interval gbAtlas 6 8512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8544 : Interval gbAtlas 6 8544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8576 : Interval gbAtlas 6 8576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8608 : Interval gbAtlas 6 8608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8640 : Interval gbAtlas 6 8640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8672 : Interval gbAtlas 6 8672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8704 : Interval gbAtlas 6 8704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8736 : Interval gbAtlas 6 8736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8768 : Interval gbAtlas 6 8768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8800 : Interval gbAtlas 6 8800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8832 : Interval gbAtlas 6 8832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8864 : Interval gbAtlas 6 8864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8896 : Interval gbAtlas 6 8896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8928 : Interval gbAtlas 6 8928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8960 : Interval gbAtlas 6 8960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_8992 : Interval gbAtlas 6 8992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_9024 : Interval gbAtlas 6 9024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_9056 : Interval gbAtlas 6 9056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_9088 : Interval gbAtlas 6 9088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_9120 : Interval gbAtlas 6 9120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_9152 : Interval gbAtlas 6 9152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_9184 : Interval gbAtlas 6 9184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_9216 : Interval gbAtlas 6 9216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_9248 : Interval gbAtlas 6 9248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_9280 : Interval gbAtlas 6 9280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_9312 : Interval gbAtlas 6 9312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_9344 : Interval gbAtlas 6 9344 22 := block_range (n:=22) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 9366 := (concat (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)))) (concat (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 bgb_6_384)) (concat (concat bgb_6_416 bgb_6_448) (concat bgb_6_480 (concat bgb_6_512 bgb_6_544))))) (concat (concat (concat (concat bgb_6_576 bgb_6_608) (concat bgb_6_640 bgb_6_672)) (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 (concat bgb_6_800 bgb_6_832)))) (concat (concat (concat bgb_6_864 bgb_6_896) (concat bgb_6_928 bgb_6_960)) (concat (concat bgb_6_992 bgb_6_1024) (concat bgb_6_1056 (concat bgb_6_1088 bgb_6_1120)))))) (concat (concat (concat (concat (concat bgb_6_1152 bgb_6_1184) (concat bgb_6_1216 bgb_6_1248)) (concat (concat bgb_6_1280 bgb_6_1312) (concat bgb_6_1344 (concat bgb_6_1376 bgb_6_1408)))) (concat (concat (concat bgb_6_1440 bgb_6_1472) (concat bgb_6_1504 bgb_6_1536)) (concat (concat bgb_6_1568 bgb_6_1600) (concat bgb_6_1632 (concat bgb_6_1664 bgb_6_1696))))) (concat (concat (concat (concat bgb_6_1728 bgb_6_1760) (concat bgb_6_1792 bgb_6_1824)) (concat (concat bgb_6_1856 bgb_6_1888) (concat bgb_6_1920 (concat bgb_6_1952 bgb_6_1984)))) (concat (concat (concat bgb_6_2016 bgb_6_2048) (concat bgb_6_2080 (concat bgb_6_2112 bgb_6_2144))) (concat (concat bgb_6_2176 bgb_6_2208) (concat bgb_6_2240 (concat bgb_6_2272 bgb_6_2304))))))) (concat (concat (concat (concat (concat (concat bgb_6_2336 bgb_6_2368) (concat bgb_6_2400 bgb_6_2432)) (concat (concat bgb_6_2464 bgb_6_2496) (concat bgb_6_2528 (concat bgb_6_2560 bgb_6_2592)))) (concat (concat (concat bgb_6_2624 bgb_6_2656) (concat bgb_6_2688 bgb_6_2720)) (concat (concat bgb_6_2752 bgb_6_2784) (concat bgb_6_2816 (concat bgb_6_2848 bgb_6_2880))))) (concat (concat (concat (concat bgb_6_2912 bgb_6_2944) (concat bgb_6_2976 bgb_6_3008)) (concat (concat bgb_6_3040 bgb_6_3072) (concat bgb_6_3104 (concat bgb_6_3136 bgb_6_3168)))) (concat (concat (concat bgb_6_3200 bgb_6_3232) (concat bgb_6_3264 bgb_6_3296)) (concat (concat bgb_6_3328 bgb_6_3360) (concat bgb_6_3392 (concat bgb_6_3424 bgb_6_3456)))))) (concat (concat (concat (concat (concat bgb_6_3488 bgb_6_3520) (concat bgb_6_3552 bgb_6_3584)) (concat (concat bgb_6_3616 bgb_6_3648) (concat bgb_6_3680 (concat bgb_6_3712 bgb_6_3744)))) (concat (concat (concat bgb_6_3776 bgb_6_3808) (concat bgb_6_3840 bgb_6_3872)) (concat (concat bgb_6_3904 bgb_6_3936) (concat bgb_6_3968 (concat bgb_6_4000 bgb_6_4032))))) (concat (concat (concat (concat bgb_6_4064 bgb_6_4096) (concat bgb_6_4128 bgb_6_4160)) (concat (concat bgb_6_4192 bgb_6_4224) (concat bgb_6_4256 (concat bgb_6_4288 bgb_6_4320)))) (concat (concat (concat bgb_6_4352 bgb_6_4384) (concat bgb_6_4416 (concat bgb_6_4448 bgb_6_4480))) (concat (concat bgb_6_4512 bgb_6_4544) (concat bgb_6_4576 (concat bgb_6_4608 bgb_6_4640)))))))) (concat (concat (concat (concat (concat (concat (concat bgb_6_4672 bgb_6_4704) (concat bgb_6_4736 bgb_6_4768)) (concat (concat bgb_6_4800 bgb_6_4832) (concat bgb_6_4864 (concat bgb_6_4896 bgb_6_4928)))) (concat (concat (concat bgb_6_4960 bgb_6_4992) (concat bgb_6_5024 bgb_6_5056)) (concat (concat bgb_6_5088 bgb_6_5120) (concat bgb_6_5152 (concat bgb_6_5184 bgb_6_5216))))) (concat (concat (concat (concat bgb_6_5248 bgb_6_5280) (concat bgb_6_5312 bgb_6_5344)) (concat (concat bgb_6_5376 bgb_6_5408) (concat bgb_6_5440 (concat bgb_6_5472 bgb_6_5504)))) (concat (concat (concat bgb_6_5536 bgb_6_5568) (concat bgb_6_5600 bgb_6_5632)) (concat (concat bgb_6_5664 bgb_6_5696) (concat bgb_6_5728 (concat bgb_6_5760 bgb_6_5792)))))) (concat (concat (concat (concat (concat bgb_6_5824 bgb_6_5856) (concat bgb_6_5888 bgb_6_5920)) (concat (concat bgb_6_5952 bgb_6_5984) (concat bgb_6_6016 (concat bgb_6_6048 bgb_6_6080)))) (concat (concat (concat bgb_6_6112 bgb_6_6144) (concat bgb_6_6176 bgb_6_6208)) (concat (concat bgb_6_6240 bgb_6_6272) (concat bgb_6_6304 (concat bgb_6_6336 bgb_6_6368))))) (concat (concat (concat (concat bgb_6_6400 bgb_6_6432) (concat bgb_6_6464 bgb_6_6496)) (concat (concat bgb_6_6528 bgb_6_6560) (concat bgb_6_6592 (concat bgb_6_6624 bgb_6_6656)))) (concat (concat (concat bgb_6_6688 bgb_6_6720) (concat bgb_6_6752 (concat bgb_6_6784 bgb_6_6816))) (concat (concat bgb_6_6848 bgb_6_6880) (concat bgb_6_6912 (concat bgb_6_6944 bgb_6_6976))))))) (concat (concat (concat (concat (concat (concat bgb_6_7008 bgb_6_7040) (concat bgb_6_7072 bgb_6_7104)) (concat (concat bgb_6_7136 bgb_6_7168) (concat bgb_6_7200 (concat bgb_6_7232 bgb_6_7264)))) (concat (concat (concat bgb_6_7296 bgb_6_7328) (concat bgb_6_7360 bgb_6_7392)) (concat (concat bgb_6_7424 bgb_6_7456) (concat bgb_6_7488 (concat bgb_6_7520 bgb_6_7552))))) (concat (concat (concat (concat bgb_6_7584 bgb_6_7616) (concat bgb_6_7648 bgb_6_7680)) (concat (concat bgb_6_7712 bgb_6_7744) (concat bgb_6_7776 (concat bgb_6_7808 bgb_6_7840)))) (concat (concat (concat bgb_6_7872 bgb_6_7904) (concat bgb_6_7936 (concat bgb_6_7968 bgb_6_8000))) (concat (concat bgb_6_8032 bgb_6_8064) (concat bgb_6_8096 (concat bgb_6_8128 bgb_6_8160)))))) (concat (concat (concat (concat (concat bgb_6_8192 bgb_6_8224) (concat bgb_6_8256 bgb_6_8288)) (concat (concat bgb_6_8320 bgb_6_8352) (concat bgb_6_8384 (concat bgb_6_8416 bgb_6_8448)))) (concat (concat (concat bgb_6_8480 bgb_6_8512) (concat bgb_6_8544 bgb_6_8576)) (concat (concat bgb_6_8608 bgb_6_8640) (concat bgb_6_8672 (concat bgb_6_8704 bgb_6_8736))))) (concat (concat (concat (concat bgb_6_8768 bgb_6_8800) (concat bgb_6_8832 bgb_6_8864)) (concat (concat bgb_6_8896 bgb_6_8928) (concat bgb_6_8960 (concat bgb_6_8992 bgb_6_9024)))) (concat (concat (concat bgb_6_9056 bgb_6_9088) (concat bgb_6_9120 (concat bgb_6_9152 bgb_6_9184))) (concat (concat bgb_6_9216 bgb_6_9248) (concat bgb_6_9280 (concat bgb_6_9312 bgb_6_9344)))))))))
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
theorem bgb_7_2208 : Interval gbAtlas 7 2208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2240 : Interval gbAtlas 7 2240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2272 : Interval gbAtlas 7 2272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2304 : Interval gbAtlas 7 2304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2336 : Interval gbAtlas 7 2336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2368 : Interval gbAtlas 7 2368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2400 : Interval gbAtlas 7 2400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2432 : Interval gbAtlas 7 2432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2464 : Interval gbAtlas 7 2464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2496 : Interval gbAtlas 7 2496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2528 : Interval gbAtlas 7 2528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2560 : Interval gbAtlas 7 2560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2592 : Interval gbAtlas 7 2592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2624 : Interval gbAtlas 7 2624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2656 : Interval gbAtlas 7 2656 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2688 : Interval gbAtlas 7 2688 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2720 : Interval gbAtlas 7 2720 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2752 : Interval gbAtlas 7 2752 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2784 : Interval gbAtlas 7 2784 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2816 : Interval gbAtlas 7 2816 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2848 : Interval gbAtlas 7 2848 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2880 : Interval gbAtlas 7 2880 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2912 : Interval gbAtlas 7 2912 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2944 : Interval gbAtlas 7 2944 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2976 : Interval gbAtlas 7 2976 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_3008 : Interval gbAtlas 7 3008 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_3040 : Interval gbAtlas 7 3040 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_3072 : Interval gbAtlas 7 3072 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 3077 := (concat (concat (concat (concat (concat (concat bgb_7_0 (concat bgb_7_32 bgb_7_64)) (concat bgb_7_96 (concat bgb_7_128 bgb_7_160))) (concat (concat bgb_7_192 (concat bgb_7_224 bgb_7_256)) (concat bgb_7_288 (concat bgb_7_320 bgb_7_352)))) (concat (concat (concat bgb_7_384 (concat bgb_7_416 bgb_7_448)) (concat bgb_7_480 (concat bgb_7_512 bgb_7_544))) (concat (concat bgb_7_576 (concat bgb_7_608 bgb_7_640)) (concat bgb_7_672 (concat bgb_7_704 bgb_7_736))))) (concat (concat (concat (concat bgb_7_768 (concat bgb_7_800 bgb_7_832)) (concat bgb_7_864 (concat bgb_7_896 bgb_7_928))) (concat (concat bgb_7_960 (concat bgb_7_992 bgb_7_1024)) (concat bgb_7_1056 (concat bgb_7_1088 bgb_7_1120)))) (concat (concat (concat bgb_7_1152 (concat bgb_7_1184 bgb_7_1216)) (concat bgb_7_1248 (concat bgb_7_1280 bgb_7_1312))) (concat (concat bgb_7_1344 (concat bgb_7_1376 bgb_7_1408)) (concat bgb_7_1440 (concat bgb_7_1472 bgb_7_1504)))))) (concat (concat (concat (concat (concat bgb_7_1536 (concat bgb_7_1568 bgb_7_1600)) (concat bgb_7_1632 (concat bgb_7_1664 bgb_7_1696))) (concat (concat bgb_7_1728 (concat bgb_7_1760 bgb_7_1792)) (concat bgb_7_1824 (concat bgb_7_1856 bgb_7_1888)))) (concat (concat (concat bgb_7_1920 (concat bgb_7_1952 bgb_7_1984)) (concat bgb_7_2016 (concat bgb_7_2048 bgb_7_2080))) (concat (concat bgb_7_2112 (concat bgb_7_2144 bgb_7_2176)) (concat bgb_7_2208 (concat bgb_7_2240 bgb_7_2272))))) (concat (concat (concat (concat bgb_7_2304 (concat bgb_7_2336 bgb_7_2368)) (concat bgb_7_2400 (concat bgb_7_2432 bgb_7_2464))) (concat (concat bgb_7_2496 (concat bgb_7_2528 bgb_7_2560)) (concat bgb_7_2592 (concat bgb_7_2624 bgb_7_2656)))) (concat (concat (concat bgb_7_2688 (concat bgb_7_2720 bgb_7_2752)) (concat bgb_7_2784 (concat bgb_7_2816 bgb_7_2848))) (concat (concat bgb_7_2880 (concat bgb_7_2912 bgb_7_2944)) (concat (concat bgb_7_2976 bgb_7_3008) (concat bgb_7_3040 bgb_7_3072)))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 28 := block_range (n:=28) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 60 := (concat bgb_8_0 bgb_8_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_9_0 : Interval gbAtlas 9 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_9 : Interval gbAtlas 9 0 1 := bgb_9_0
theorem allgb : ∀ k ≤ 9, ∀ i < count gbAtlas k, checkRow gbAtlas k i = true := by
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 6 := by
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 20, 21),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 5, 21),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 24, 25),(inputs.getD 1 zero, 16, 18),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 20, 21),(inputs.getD 1 zero, 16, 18),(inputs.getD 2 zero, 17, 21),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 32, 33),(inputs.getD 1 zero, 36, 38),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 6 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 20, 21),(inputs.getD 1 zero, 16, 18),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 20, 21),(inputs.getD 1 zero, 16, 18),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefeeafeecf000feeefeeafeecf000feeefeeafeecf000feeefeeafeecf000feeefeeafeecf000feeefeeafeecf000feeefeeafeecf000feeefeeafeecf000
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277075690 * 2 ^ 32 + 4276940800) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_17019.Model.Repr at out
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

def mono : List Gate := [⟨.or,[2,3]⟩,⟨.and,[0,5]⟩,⟨.and,[5,6]⟩,⟨.or,[4,8]⟩,⟨.and,[2,3]⟩,⟨.and,[0,6]⟩,⟨.or,[7,9]⟩,⟨.or,[1,11]⟩,⟨.and,[12,13]⟩,⟨.or,[10,14]⟩,⟨.or,[7,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4276940800) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4276940800) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_17019

open PEqualNP.Outside.L_meta_17019 in
theorem PEqualNP.Outside.L_meta_17019 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4276940800) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4276940800) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
