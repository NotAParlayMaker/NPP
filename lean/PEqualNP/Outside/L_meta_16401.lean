import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_16401.Model
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


end PEqualNP.Outside.L_meta_16401.Model

namespace PEqualNP.Outside.L_meta_16401
open PEqualNP.Outside.L_meta_16401.Model
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

end PEqualNP.Outside.L_meta_16401

namespace PEqualNP.Outside.L_meta_16401
open PEqualNP.Outside.L_meta_16401.Model
def gbK8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x600039c29fb80000a9d02c89b0337a4a00404c2f08d4b2b750313e620b25483461a64c58800e080041040210223ff42fe42fd42fc42fe32fd32fc32ff41fe41fd41fc41ff21fe21fd21fc21ff40fe40fd40fc40ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x241fd42483f884907b10920ff99241ef32483fc64907f4c920fe19241ec32483fea2905fd4520ff28a41fd51483f8a2905f14520ffa0a41fe41483fa82907f10520ff98a41fe31483fa62907f0c520ff90a41ef21483fc42907f48520f690a41fc21483fe80907f90120fea0241fc40483fe60907f8c120fe98241ff20483f640907f88120f710241ff54082fea8107f95020bf2a041fd54082faa8107f15020be2a041ff53082fea6107f94c20bf29841fd53082faa6107f14c20be29841ff43083fc86107f50c20fe218417e52083fe84107f90820fea1041fc42083fe64107f8c820fe99041fc32083fea2107f94420bf28841fd51082faa2107f14420ffa0841fe41083fa82107f10420ff98841fe31083fa62107f0c420ff90841fe21083dc42107f48420fe10841ec21082fca0107fd0020ff20041fd40083f880107fcc020ff18041fd30083f860107fc8020f790041fe20083f440107f48020f690041f920083fea9885fd5310ff2a6217e54c43faa9885f55310fe2a6217c54c43fea5885fd4b10ff296217e52c43faa5885f54b10fe296217c52c43fe85887f90b10fea1621fc42c43fc65887f4cb10fe19621ff41c43fc83887f50710fe20e21ff21c43fc43887f48710fe10e21ff40c43f681887f90310fea0621fc40c43f081887fc8310fd90621fe20c43fa41887f08310fc10621ff54842fea9087f95210bf2a421fd54842faa9087f15210be2a421ff52842fea5087f94a10bf29421fd52842faa5087f14a10be29421ff42843fc85087f50a10fe21421fe32843fa65087f0ca10bea8c21ff41843fc83087f50610fe20c21ff21843fc43087f48610fe10c217e50843fe81087f90210fea0421fc40843fe41087f88210fe90421fc20843fe21087dc4210fd88421ff54442fea8886fd51109faa221fe54442fca8887f55110beaa221fc54442f8a8886f151109e2a221ff52442fea4887bd4910b7a9221fe52442fca4887f54910bea9221fc52442f8a4887b14910b629221ff42443fc84887f50910fe21221fe32443fa64887f0c910ffa0a21fe41443fa82887f10510ff90a21fe21443fa42887f08510ffa0221fe40443fa80887f10110ff90221fe20443fa40887f08110ff88221fb10443fc20887d84110ffaa0217f54043fca8085f95010df2a0213e54043faa8085f55010deaa0213d54043f8a8085f15010ffa90217f52043fca4085f94810f7290216e52043faa4085f54810f6a90216d52043f8a4085f14810ffa1021fe42043fa84087f10810ff19021fd32043f864085f94410ffa0821fe41043fa82087f10410ff90821fe21043fa42087f08410bf28021ff40043f680087f90010fea0021fc40043f080087fc8010fd90021fe20043fa40087f08010fc10021ff10043ee20087f84010fd08021fd10043ea20087e44010
  | 1 => 0xf31087fc6210ff4c421fe18843ff21087de4210ff88421fb10843fd21087da4210fd48421ffa8043fe50086fca010ff54021bea8043fc50087fea5a07f94b40bf29681fd52d02faa5a07f14b40ffa1681fe42d037c85a07f50b40fe21681bc42d03fc65a07f4cb40fe19681ff51d03fca3a05f94740fea8e817d51d03f8a3a07fd0740dfa0e81fe41d03fa83a06f50740fe20e81ff21d03fc43a07f48740fe10e817d54903fea5207f94a40bf29481ee52902dca5207f54a40bea9481ed52902daa5207f14a40ffa1481fe42903fa85207f10a40ff19481fd32903f865207fd4640ff28c817e51903faa3205f54640fe28c81ff41903fc83206f90640fea0c81fc419037883207fc8640ff10c81fd21903f843205f94240ffa0481bf40903f681207fd4940bfa9281fe52503faa4a07f14940be29281ff42503fc84a06f90940fea1281fc425037884a07f8c940fe99281fc32503fea2a05fd4540ff28a81fd51503f8a2a05f14540ffa0a81bf41503fc82a07f50540dea0a81fc41503fe42a07f88540fe90a81fc21503fe80a07ed0140ff20281be40502fca8207fd4840ff290817e52103faa4205f54840fe29081ff42103fc84207f50840fe21081fe32103fa64207f0c840ffa8881fe51102fca2207f54440bea8881fc51103fe82207f90440df20881fd41103f882206f10440ff90881fe21103fa42207f08440bf28081ff401037e80207f90040fd20081fd401037a80207e50040ffaa6417f54c83fca9905f95320feaa6417d54c83f8a9905f15320ffa9e41fe53c82fca7907f54f20bea9e41fc53c82f8a7907fd0f20ff21e41fd43c83f887907fd0b20f7a1641fe42c83fa85907f10b20f621641ff32c83de65907f8cb20fe99641fc32c83d865907fd4720ff28e417e51c83faa3905f54720fe28e41ff41c83fc83907f50720fe20e41ff31c83fc63907f4c720fe18e41ff21c83de43907f88720fe90e41ed21c83f843907fd0320ff20641fd40c83f881907fcc320ffaa4417f54883fca9105f95220df2a4413e54883faa9105f55220deaa4413d54883f8a9105f15220ffa9c417f53883fca7105f94e20ef29c415e53883faa7105f54e20eea9c415d53883f8a7107fd0e20ff21c41fd43883f887105f54a20ffa1441fe42883fa85107f10a20ff99441fe32883fa65107f0ca20ffa8c41fe51882fca3107f54620bea8c41fc51883fe83107f90620fea0c41fc41883fe63107f8c620fe98c41fc31883fe43107f88620f710c41fd21883f843107b08620bf28441ff40883fc81107f50220fe20441ff30883fc61107fc8220f790441fb20883fea8905fd5120ff2a2417e54483faa8905f55120fe2a2417c54483fea6905fd4d20ff29a417e53483faa6905f54d20fe29a417c53483fe86907f90d20fea1a41fc43483fe84907bd0920ff21
  | 2 => 0xcbdc64197f4c832f699065cd320cbfea2197f94432bf28865fd510cafaa2197f14432ffa8065fe500cafca0197f54032bea8065fc500cbfea5a0ff94b41bf29683fd52d06faa5a0ff14b41ffa1683fe42d07fa85a0ff10b41ff19683fd32d07f865a0ffd4341ff286837e50d07faa1a0df54341fe286837d54907fea520ff94a41bf29483fd52906faa520ff14a41ffa1483fe429077c8520ff50a41fe21483bc42907fc6520ff4ca41fe194837e51907fe8320efd0641fba0c83ff50907fca120df94241fea84837d50907f8a120ffd4941bfa9283ef52506dea4a0ff94941fea9283fc52506f8a4a0fb14941b629283ff42507fc84a0ff50941fe21283fe32507fa64a0ff0c941ffa0a83f741507fc82a0ef90541ffa82837f50507f6a0a0ded4141ff28283fd50507f8a0a0df14141fc282837850506fca820ffd4841ff290837e52107faa420df54841fe29083ff42107fc8420ef90841fea1083fc42107788420ff8c841fe99083fc32106fca220ffd0441dfa0883fe41107ec8220ff50441dea0883f541107fea020ff94041bf28083fd50106faa020ff14041ffaa6437f54c87fca990df95321feaa6437d54c87f8a990df15321ffa9e43fe53c86fca790ff54f21bea9e43fc53c86f8a790ffd0f21ff21e43fd43c87f88790ffd0b21ff21643fd42c87f88590ffccb21ff19643fd32c87f86590ffd0721ff20e43fd41c87f88390ffcc721ffa8643fe50c86fca190ff54321bea8643fc50c87fea910dfd5221ff2a4437e54887faa910df55221fe2a4437c54887fea710dfd4e21ff29c437e53887faa710df54e21fe29c43ff43887fc8710ff50e21fe21c437d52887fe8510fbd0a21ff21443fd42887f88510fb10a21ff99443ef32887fc6510ff4ca21fe19443ec32886fca310ffd0621ff20c43fd41887f88310ffcc621ff18c43ff21887de4310fdc8621ffa8443fe50886fca110ff54221bea8443fc50887fea890dfd5121dfaa2433f54487fca890df95121feaa2437d54487f8a890df15121de2a2433c54487fea690dfd4d21efa9a435f53487fca690df94d21fea9a437d53487f8a690df14d21ee29a435c53487fe8690ff90d21fea1a43fc43487fe8490ff90921fea1243fc42487fe6490ff8c921fe99243fc32487fe8290ff90521fea0a43fc41487fe6290ff8c521fe98a43ff21487ee4290ff88521f710a43ff50486fea090fed4121bda8243fe50487faa090ff14121be28243f850486f0a090ffd5021bfaa043fe54086fca810ff55021beaa043fc54086f8a810ffd4c21bfa9843fe53086fca610ff54c21bea9843fc53086f8a610ffd0c21ff21843fd43087f88610df94821ffa1043ef42087fc8410ff50821fe21043ec42087fe6410fbcc821ff19043fd32087f86410fb0c821bf28843ff41087fc8210ff50421fe20843f
  | 3 => 0xc00400000001401000001800000000000400000000000000400000003c02802800c00801000001000002800c00000000002c00000400806001000800000000400406000c01c02800000800002000001000800802800405000000000400000401400400400000c01400000000402002000400400c01000000c01c00c00400802400000400800000000800000800c03400800800801400000000002000c00402000000000400000c00800000801801002400800401400402800803800001c00001c00c04400000000003800000000400000400000000000402800400000000800400401c00400000400401000c00400401402000000002400002000000c02c01400803000000400400000801c00000000003000000003c00800c00400c00800000c00003000001800400400400c03401001403800400801c00c00800c00401000803000802401403c00800400002800400400400001800001800400400000800803c02000000000c00000001800002800800800400800c004004000010004004008000020020013fea7a17f94f42bf29e85fd53d0afaa7a17f14f42ffa1e85ff51d0bfca3a15f94742fea8e857d51d0bf8a3a17fd4342ff286857e50d0bfaa1a15f54342fe286857d5490bfea7217f94e42bf29c85fd5390afaa7217f14e42ffa1c85fe4390b7c87215f94a42ffa1485bf4290bde85217fd4642ff28c857e5190bfaa3215f54642fe28c85ff5090bfca1215f94242fea84857d5090bf8a1217fd4d42bfa9a85df5350abea6a17f94d42fea9a85fc5350af8a6a17714d42ae29a85ff4350bfc86a17f50d42ffa1285ef4250bfc84a16f90942ffa8a857f5150bfca2a17f54542fe28a857c5150bfea0a15fd4142ff28285fd5050bf8a0a15f14142bf2a085ff5310bfca6215f94c42fea98857d5310bf8a6217fd0c42ff21885be4310bfa86217f10c42de218857e5210bfe84216fd0842ff21085ee4210bfa84216f50842f6a1085ad4210bfea2217f94442bf28885fd5110afaa2217f14442ffa8085fe5010afca0217f54042bea8085fc5010bfea9195fd5232ff2a4657e548cbfaa9195f55232fe2a4657c548cafaa7197fd0e32efa1c65fe438cbfa87197f10e32ee21c657e528cbfe85197f90a32fea1465fc428cbfe65197bcca32ffa8c65fe518cafca3197f54632bea8c65fc518cbfea1197f94232bf28465fd508cafaa1197f14232ffaa2657f544cb7ea8994fd5132ff2a2657e544cbfaa8995f55132fe2a2657c544cb78a8994f15132ffa1265fe424cbfa84997f10932ff19265de324cbfea2995fd4532ff28a65fd514cbf8a2995f14532ffa82657f504cbfca0997f54132fe282657c504cbfea8195fd5032ff2a0657e540cbfaa8195f55032fe2a0657c540cafca4197fd0832f7a1065fe420cbfa84197f10832f621065fe320
  | 4 => 0x758000ba0000a5914c0000005b4338000b21699d011d00000002452b1aa00000021280000014dd2111ea249f41388001479c6d18c0017b5be0870000000000001db21e0000000001a187318f9d7c348258ad0938a10000000b98001fe8000001f380004c8000000191a302789100007c800044800075c001b50000380295a103600009b80000021b9320001fe01148e2169a84be0000000000ac9344002130065644000918000000000000b40a00000000000000bc80800000003880016640000880015e0000ade100b588d8000409120b317211640000002500a80001346a8969265b0d16c105b45fb40011c800000000000000000039c001e45235b30000000c6400124c7a09880010a1a20000000000000948001368000000b61058a49261351a5c00000032048c0016380000009d800000016e010000000000001af4001371cf00022211800000006e800000167521c000000001eb447d06c0014883b85388612882c46387498183a9df9308b48901e007b0000cb5dd14290052e5db8000000001bb4000000cd40006680000008c5081130000000254c88000000000f300000000010b02f5978970000000480000001a094900013b80000000010fc0000020f9808000bd16100000014c8028d28000b88fec110000001ba40000014e80000000000000000000003b0001a560e82f9ed16e9ed8cac7e1708420000000000000000000f50001bcc000000000000000b28001695a38c69d38031078d0c000001b09cc80000d00017480000000019700000018780003f9710000a314812300000000018493d99456d800004c000941e100000000000000000000002ae12000125000000000108800021c0003f4001c7c00017d55139c000e40000b10000000db88485302300000000000000000000011b043932801000400401003800400002800801800400000402001801000400001802400001000c00001000c03000801000801800800000801800003800400001000000800000000400c00000005401c00400401800400804400002000400000000400000c01801000c00800000004c00400000400400800c00002401c00001c01000401c01000400400000801401001400400002400003000000800001801401000404000000c00800c00404000400800000000001800000402800800800000000003400000800800c00800801000c00000003000800000400400000000402000405c00800800000002000800000002800000400000000001800000000000400c00c00c00400000400800400000000c00000400000000c00c00003003400000000002000002403c00402401000800800401001800400000000001800001005001400400c00c00000402400c00c0000040c800400400800c00400000001c00800000000400400000401001400c00000
  | 5 => 0x15a92800002e80012700000000018248a8000002050000001de07e8001b397e4ad40002cc000ee1469f11ce9f896540000001590c1a81c88000000001e50002160210000bc0000508001024000000000020fd9cb9fd9b4c600001f09ff8001d99e68000000d1800000000208c000001ca9a740019380000019800013f02081c892913da7dfd07813a95d0000b6c000ac09d02b8000bb80000000000019a8000000001525bd4002058000b8554185059c00140115503c000000000b3d815b041283c800000122c000001f6a1788d04e0000ec8000000000800711c10000001030001c600a1051ce01261b0e00001a2e0790361e83dcdf8545fc8671e218b14c5e59e18cc57307ad4080010e0002211f4815da921895b49f90980000019185ad5c000000195c5b9cb1b1d2143f0000001be5718001860001564000001b2c0004e54b8000300410001a1cb75e39dc0139020000000b78ffc000714435178d70000000000000000a517d40007ec000000000690000001d60740000000a38000000a6a1a06186600015e800045d8a80009a12d80001d0000f5e1a9d780000004a0000000868a91c0901d02dea8ca1d58000000b693ecce80000003e80008800000010157800000012d0000000000001a448a1310ee5888d80000000cd81e1628001a4c000000000001c8c000000000990694688000684b2d3487280000000000012b8750b09ec0001ec9690001bd0c380000000005bc0912a9228000e4c00000193dbec0000001e84b01794d61d94300001a9aa8001a28ef4a29d6a1d0df0000700001764000df40000012c00009300a4168001ca40000000000000000000021380000000003ec0014b418875400068d4204880004c07f0b02108000001fa80000000000b8561dc86fa0c99c80000019540019e800077014c000b500002ca0940000d8000000000f25019a600000fc8ec001e88000a78fb000117c7887040000002400015141b000000000076000000000000143800000152d4589789c00000000015704749604f1fc0ae1f00000000001190000001ac14ec000000ce0000000980a040011c00193c88662192e84580b20d00000006785b079dea08f120c4e9ef8000bf00012f4000f800000000013140000095f80000015587b4cc044d5a20800000000000000000000020a876c3ad9988580000010298c01487780003100000000000000003c00000000000000000000000000017c00000100011890d84d8be4e283e151d7e15f0a61750f900000006121c800000043c30ca418300016200007da1c1b9d8d1a00e700000020900012ec000000000000000f2000000000124158976a1987a48780b40000016f8c9d324c29b592453988512a00020b00017916318b95b8239ee9ee1d6c0000018640000000000018e00000000004dc000001661068
  | 6 => 0x2bdf800000016f4908631a40000eecc4e14969c6e57d04b9c95c19d28808215a78bd8d14bb00011e00000000000005a1b91d88e202ec0007c0000000001b1010c000001d5c0000000010e80000400018c8000000e48d081b8000edd94c9a61400002a1a6c0014d112c0009f0cbceb0830001d10001c84000001ff10900000ac5681f00011600000000019a1531449f60f185c046c001eb85cc000000629e316804d1eb0cf94b04ec5edab122411cfa16e5fb9e288f593560800000040000000125c001c5c6a0000d6c0010840000000014aa17c04482d009100d845f0000d891380011840010c8000d51e91471fa1700d385d8000000000d354f06e1c40001118000000000000d5800125923c288000e39a590f80000018100017403a0518001508000f880006d80016d11445006a4001fc4001bad4e0000cc8000000000000000000fb9e8000087cea14ac718000ea8398000001300ee8000a6d5d968486c000f10768000495c90000000001c7954a2400018217700020894cc000000abc8b2238000000000000d740016e1d50001c98164e80a204fdbbd948fc8c30511108001c69ad8ef8000c085798e8951d198706fc0000000014f8a884846d0da1a3c000000000874001c38000a98c5071c000001fac00000000000000114893c0015c981d4a45d4000000000558000000890cf00000000018f00002d1d40000199f785e8f0c000000af80000015608e42a56f00c8001a511d9600db2159e60820000e99a71d76019b185546f5b40201f90000001c9cd1c0005910b80017bd290000e10001041af8c48fd10f11f0001ef000024d248000001268000000000000608d100005a85899e19c19082dd4d80e02b413c050995bc51a9d647f86f0b7d758000811ae8000000000000000001ee4f713c09ac5c4000000001890000620cb80005e4001b7020400095c000000001304049f321804f40019f1b80000000efe068d00a16230e18001c59f58174000000000ae4ec0000000f6e1900011b8f04a70001f285d0cb0ff09ea0717b0002228000af0000000001a14fc0d40f79b61e99010000d999f800059803925597c000e69591b00314ab0001170d60888fe20c1911a99d907380020980013e0790d2000000000099c001451d483680000000019900000007a9b34000000000000000aa88c110c000680000e5ca64478000ae9046208000daa200c217cced8699d70000001651518000340000b38a55c800006580014406c0001a64ef10748b803c001460ed02fd0399747fd0603d9ca18387980017ada888f8001578c18ff9e70001c7035111c580959499930001c220a0d49ae00012c84700018d80000008982d80019d84f934069d950aa1728b90268a5d5289449b0329921159ad0000000000000000000000000000000b2611000000180c5e06ec0
  | 7 => 0x1fb192dcf888d67029c0020d8f08249bdd7f8000000000450001001dd8150000001a2453c001bb00780980004300007d000130c001e952f9ab806126c70907c001b49b3d0d0b18000000001e7db280005514a00001c0d2dcc0001f980000000000000014bd5817b9e9dd080000000000000000003a458c571ac8001135e412f0001bf15b0b708dd984001899958121a35358000f49279aec0016a16b9e7a0e0650000070c61b788fc00000000188000005cf1d378998c000e870c441669c02119778000ab96c1338f540000015393b0000000000000001b24000640c98378001f208395c4f005489c8154468001658b811419400c1bc8001124e79b68bf800067cf688c80011140020402a8c5ce30ab48d4c91b206b1d30f993e95200000000001300011f8fe40009d4cd00009a8001e08000ca4d300000009350480bc0000017353f84660316edc30e447b81001f82e507136132d198674000001104c70270308000000428000e900020f011a150001bf8000001411a480000f8000e583d151020cdd99b0e08f61840de8000000f140017c80012fda68828e88c8115c000001af054dda119400000165db88ed4000c36021219d551698a00009e00017a9c74000000000000000000001c480551a00000019b8000ba8002039238000000000000dc8000000001900000f29799208eb938c0000000002299251500001700013301089542181a012c000e51c297a13a60605c8000001f503716780000017e800000217134c000161ba04900020b97c5760d7dfbca74001c50000fe91293de02818196d801569968f65110000001e85bb9de8ca85f9648ad9381df17d8000e61d20305618a182204445a4145b98505501988be9d81ea4359b15220000000000ccdcac000000391e482800000000005200008e80018296400000000010a8528001cd8acc2e01da00141c8843e4330c113942616a8e54542049964aec0f16c8498594a094c1960000454461788000000001afcdd0000fa9da967cde17f00008cc0000013180596882f0000000000000000720000841895f193914180021f80002d5ba825c39586992800100c0000021f1bd8298c5564c001e8cd90000a806b8d78001be9200dc0000c40142009858000ac43192e06c8f58000f380019d04182b0f40819bc0000920000c58dc40000002906484a8001598068001334000ff40000000013a1cd05dcc79f700000013d16dd6b00002c1299738000000d6800000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xb40043ba42d0010ee10b40042f961d0010de94740043bb41d0010ee507400427f65900109f596400433e5490010cf55240042ee6290010bb58a400436e5290010db54a40042f66190010bd58640042fa60900109fd95400433e5450010cf551400436e5250010db549400427f65100109f994400427d65100109f194400433e5410010cf550400436e5210010db54840042f66110010bd58440043b94010010be594400437965100109e59440042fa6410010ee990400437b5410010ee95040043795410010ee55040042fa6210010fa94840043e95210010fc98440042f96110010fc584400437a5110010ee90440043b841100109f597200433e54c8010cf553200435e53c8010d754f200436e52c8010db54b20042f965c8010de59720042fa64c8010be19320043ba54c8010ee55320042fa63c8010be18f20043da53c8010f654f200437b52c8010fa94b200437952c8010fa54b200436952c8010fad0b20043e842c8010faccb20043e832c8010be587200437a51c8010fac8720043e921c80109fd96200427d6588010af99220042bd6488010cf952200433d5488010b798e20042dd6388010d794e200435d5388010db94a200436d5288010bd98620042f56188010be982200427f6548010cf951200433d5448010d794d200435d5348010db949200436d52480109fd94200427e65080109f594200427c6508010cf950200433d5408010d794c200435d5308010db948200436d5208010bd98420042f56108010fa48020042f96508010de59420042796508010be99020042f86408010ee95020043b95408010be98c20042f86308010f694c20043d95308010be98820043ea6208010ded4820043ea5208010de54820043e95208010fc98420042f96108010fc584200437a5108010fa88420043e82108010cf953100433d54c4010db94b100436d52c4010dd59710043b654c4010ed55310043e652c4010f954b10043f340c4010fc10310043f320c4010fc083100433e5484010cf552100436e5284010db54a10042f56184010dd94610042f96584010de59610042796584010be99210042f86484010ee95210043b95484010be98a10042f86284010fa94a10043e95284010be586100437a5184010fc946100427f6544010afd9110042bc6444010cf951100433d5444010bbd8910042ec6244010db949100436d5244010bdd95100437765440109dd9510043b76444010ed19110043b65444010ed55110043e76244010f918910043e65244010f954910042f76044010dd94110042fb6544010ded95100427b6544010eed9110042fa6444010be19110043b86444010ae19110043ba5444010ee55110043eb6244010be98910042f86244010fa18910042e86244010fa94910043e95244010bed8510043f36144010de94510043f25144010
  | 1 => 0x436e6354810db58d520436c6354810db985520436c6154810db981520436c6054810da181520436c1054810af99052042bd6414810cf950520433d5414810b798c52042dd6314810d794c520435d5314810bb988520436d52148109f990520433e64148108f990520427d6414810cf590520423d64148109f98c520435e63148109798c520427d6314810d758c520425d63148109f988520436e62148109b988520427e6114810dd984520427e6014810de980520427f65d08109f997420427d65d08109f197420433e54d0810cf553420435e53d0810d754f420436e52d0810db54b42042fa60d0810be583420427f65908109f996420427d65908109f196420433e5490810cf552420435e5390810d754e420436e5290810db54a42042fa6090810be582420427f65508109f995420427d65508109f195420433e5450810cf55142042df6350810b718d420435e5350810d754d420436e5250810db54942042f76150810bd18542042fb6050810be181420427f65108109f994420427d65108109f194420433e5410810cf550420435e5310810d754c420436e5210810db54842043ad42108109fd96320427e658c8109f596320427c658c810cf952320433d548c810d794e320435d538c810db94a320436d528c810be98232042f9608c8109fd95320427e654c8109f595320427c654c810afd9132042bc644c810cf951320433d544c810db949320436d524c810bdd8532042f4614c810bed8132042f8604c8109fd94320427e650c8109f594320427c650c810cf950320433d540c810db948320436d520c810f34c8320427e64944109f592510427e62944109f58a510427d65d0410cf953410433d54d0410db94b410436d52d04109fd96410427d6590410cf952410433d5490410db94a410436d5290410be98241042f960904109fd95410433e5450410cf55141042ef6250410bb189410436e5250410db54941042fb60504109fd94410427d6510410cf950410433d5410410db948410436d5210410be98041042f960104109f597210433e54c8410cf553210435e53c8410d754f210436e52c8410db54b210427f65884109f596210433e5488410cf552210435e5388410d754e210436e5288410db54a21042fa6088410be582210427f6548410afd9121042bc6448410cf951210433d5448410b7d8d21042dc6348410d794d210435d5348410db949210436d5248410bed81210427f65084109f594210433e5408410cf550210435e5308410d754c210436e5208410db54821042fa6008410be580210427e64940109f592500427e62940109f58a500427d61940109f597400433e54d0010cf553400436e52d0010db54b40042f965d0010de597400437b54d0010ee953400437954d0010ee553400433954d0010be98b40043ea52d0010fa54
  | 2 => 0x52101109f997204433f54c8110cf153204435f53c8110d714f204436f52c8110db14b20442f661c8110bd587204427e6588110af99220442bd6488110cfd52204433c5488110b798e20442dd6388110d7d4e204435c5388110dbd4a204436c52881109fd95204427d65481109f195204433f5448110cf151204435f5348110d714d204436f5248110db14920442f76148110bd185204427e6508110cfd50204433c5408110d7d4c204435c5308110dbd48204436c5208110cfd53104433c54c4110dbd4b104436c52c4110eed53104437a54c4110de15310443b854c4110ce15310443eb52c4110de94b104437852c4110fa14b104436852c4110cfd52104433c5484110dbd4a104436c5284110edd5210443b45484110f9d4a10443e45284110fcd4210442ee62d5010bb58b540427e62d5010db98b540426e62d50109f58b540436d62d50109b58b540427e61d5010dd987540427e60d5010de983540427d6595010cfd52540427e62950109f58a540423d6595010ee182540433f6295010cf98a540433d6295010cf18a540433e6195010cf186540433e6095010cf182540433f64550109fd89540427c62550109fd85540427d61550109fd81540427d6055010de181540433f6555010ee181540433f6255010cf989540433d6255010cf189540433e6155010cf185540433e6055010cf18154043386055010cf04154042be6415010cf55054042ee6215010bb588540427e6415010cf990540423e64150109f988540436e62150109b988540427d6215010db588540426d62150109f984540437661150109f980540437a6015010af99352042bd64d4810cf953520433d54d4810b798f52042dd63d48109f993520433e64d48108f993520427d64d4810cf593520423d64d48109f98f520435e63d48109798f520427d63d4810d758f520425d63d48109f987520437661d48109f983520437a60d48109f596520433e5494810cf552520436f52948109f992520427d64948109f98e520427d63948109b596520436f5494810db95252043ae5494810cb952520436d5494810eb552520432d5494810db152520436f5394810db94e52043ce5394810d394e52043e86094810dbd92520436e6494810db592520436c6494810dbd8e520436e6394810db58e520436c6394810db986520436c6194810db982520436c6094810cf951520433d5454810d794d520427f64548109f191520427f63548109f18d520436f62548109fd85520427d61548109fd81520427d6054810de181520436f6554810dbd51520436e5454810eb951520432e5454810db55152043ad5454810cb551520436c5454810dbd4d520436e5354810f394d520434e5354810db54d52043cd5354810d354d52043e86054810dbd91520436e6454810db591520436c6454810dbd8d520
  | 3 => 0x910ddd85524427f6054910ded81524427b60549109f994524433f5414910cf150524435f5314910db548524427e64149109f590524427e63149109f58c524436e62149109f984524427c61149109f980524427c6014910bb994524436e65149109b994524436f5414910ebd50524432f5414910db950524436d5414910db15052443ac5414910cb150524436f5314910f3d4c524434f5314910db94c524436d5314910db14c52443cc5314910d314c524436f6414910db990524436d6414910db190524436f6314910db98c524436d6314910db18c524436f6114910db584524436f6014910db580524436d10149109fd97424427e65d09109f597424427c65d0910cfd53424433c54d0910d7d4f424435c53d0910dbd4b424436c52d09109fd96424427e65909109f596424427c6590910cfd52424433c5490910d7d4e424435c5390910dbd4a424436c52909109fd95424427e65509109f595424427c6550910cfd51424433c5450910b7d8d42442dc6350910d7d4d424435c5350910dbd49424436c52509109fd94424427e65109109f594424427c6510910cfd50424433c5410910d7d4c424435c5310910dbd48424436c5210910eb50842442fa6010910be580424427f658c9109f996324427d658c9109f196324433f548c910cf152324435f538c910d714e324436f528c910db14a324427f654c9109f995324427d654c9109f19532442bf644c910af191324433f544c910cf151324436f524c910db149324427f650c9109f994324427d650c9109f194324433f540c910cf150324436f520c910db14832443cd320c910be98032442f9600c9109f997414433f54d0510cf153414436f52d0510db14b41442fa60d0510be583414427e6590510cfd52414433c5490510dbd4a414436c52905109f195414433f5450510cf15141442ef6250510bb189414436f5250510db14941442fb6050510be181414427e6510510cfd50414433c5410510dbd48414436c52105109f997214433f54c8510cf153214435f53c8510d714f214436f52c8510db14b21442fa60c8510be583214427e6588510cfd52214433c5488510d7d4e214435c5388510dbd4a214436c52885109f19521442bf6448510af191214433f5448510cf15121442df6348510b718d214435f5348510d714d214436f5248510db14921442fb6048510be181214427e6508510cfd50214433c5408510d7d4c214435c5308510dbd48214436c52085109f997404433f54d0110cf153404436f52d0110db14b40442f661d0110bd587404427e6590110cfd52404433c5490110bb98a40442ed6290110dbd4a404436c52901109fd95404427d65501109f195404433f5450110cf151404436f5250110db14940442f76150110bd185404427e6510110cfd50404433c5410110dbd48404436c
  | 4 => 0xf19132842f7614ca10bd185328427f650ca109f994328427d650ca109f194328436e520ca10db54832843cd320ca10be98032842f9600ca10cf953418433d54d0610be98341842f960d0610cfd52418433c5490610cf951418433d5450610bbd8941842ec6250610bed8141842f86050610cfd50418433c5410610db94b218436d52c8610be98321842f960c8610dbd4a218436c5288610afd9121842bc6448610b7d8d21842dc6348610db949218436d5248610bed8121842f86048610dbd48218436c5208610cfd53408433c54d0210cf952408433d5490210bb98a40842ed6290210bd98640842f56190210cfd51408433c5450210cf950408433d5410210bd98440842f56110210dbd4b208436c52c8210af99220842bd6488210b798e20842dd6388210db94a208436d5288210bd98620842f56188210dbd49208436c5248210db948208436d5208210bd98420842f56108210bd597108437565c4210be597108437965c4210de953108437854c4210de94b108437852c42109f98b544427d62d5110cfd8b544433e62d5110cf58b544433c62d5110cfd87544433d61d5110cfd83544433d60d5110cfd5254442ee6295110bb58a544427e64951108f992544427e6295110db98a544426e62951109f58a544436d62951109b58a544427d6195110dd586544427d6095110de58254442ef6255110bb189544433f64551109fd89544436f62551109bd89544427c6255110db189544426c62551109fd85544437761551109fd81544437b60551109ed81544427e6515110cf550544433e64151109f988544427d62151109f984544427c61151109f980544427c6015110af994544433e65151108f994544433f6215110cf988544433d6215110cf188544433f6115110cf584544433f6015110cf580544433d1015110cfd53524433c54d49109f993524427d64d49109f98f524427d63d4910dbd5352443af54d4910cbd53524436e54d4910db553524436c54d4910eb153524432c54d4910dbd4f52443cf53d4910d3d4f524436f64d4910db993524436d64d4910db193524436f63d4910db98f524436d63d4910db18f524436f61d4910db587524436f60d4910db58352442be6494910af592524433f5494910cf15252442de6394910b758e524435f5394910dbd4a524427e6494910cf992524423e64949109f592524433d64949108f592524427e6394910d798e524425e63949109f58e524435d63949109758e524427e62949109b98a524427d6194910dd586524427d6094910de58252442bf6454910af191524433f5454910cf15152442df6354910b718d524435f53549109fd91524433f64549108fd91524427c6454910cf191524423c64549109fd8d524435f635491097d8d524427c6354910d718d524425c6354910dbd89524427f6154
  | 5 => 0x41c433c5450710bbd8941c42ec6250710be18141c433e5410710cf55041c42fa6010710be58041c436f52c8710db14b21c436e5288710db54a21c42fa6088710be58221c42bf6448710af19121c42df6348710b718d21c436f5248710db14921c42f86048710db94821c436d5208710be98021c42f96008710cf95340c433d54d0310bd98740c42f561d0310be59740c437965d0310ded5340c43ba54d0310de55340c43b954d0310be98b40c43ba42d0310ee10b40c43f261d0310be58740c43f161d0310eed0740c43b941d0310cfd5240c433c5490310bb98a40c42ed6290310cf95140c433d5450310bdd8540c42f46150310cfd5040c433c5410310ee50040c42f96510310de59440c43ba6410310ded5040c43bb5410310de55040c43b85410310be98840c42f96110310ee90440c43b84110310db94b20c436d52c8310bd98720c42f561c8310be59720c437965c8310be99320c42f864c8310be98f20c42f863c8310ded4b20c43ea52c8310de54b20c43e952c8310fad0b20c43e842c8310faccb20c43e832c8310fc98720c42f961c8310fc58720c43eb21c8310fa48720c42be6488310af59220c42de6388310b758e20c436f5288310db14a20c436e5248310db54920c42f76148310bd18520c436f5208310db14820c43e92008310be59420c43796508310be99020c42f86408310be98c20c42f86308310fa98820c437b5208310fad4820c43795208310fa14820c42f96108310fa88420c43e82108310bb98b54842ed62d52109f98b548436e62d52109b98b548427d62d5210db58b548426d62d5210dd587548437a60d5210cfd52548427e62952109f58a548433f64552109fd89548427c6255210cf550548433e64152109f988548427d6215210dd584548437a6015210af99352842bd64d4a10b798f52842dd63d4a109f993528433e64d4a108f993528427d64d4a10cf593528423d64d4a109f98f528435e63d4a109798f528427d63d4a10d758f528425d63d4a10dd587528437a60d4a10dbd4a528427e6494a109f592528427e6394a109f58e528427f6454a109f191528427f6354a109f18d528436f6254a10db548528427e6414a109f590528427e6314a109f58c528436e6214a10dd584528437a6014a109fd97428427e65d0a109f597428427c65d0a10db94b428436d52d0a109fd96428427e6590a109f596428427c6590a10cf952428433d5490a109fd95428427e6550a109f595428427c6550a10b7d8d42842dc6350a10bdd8542842f46150a109fd94428427e6510a109f594428427c6510a10cf950428433d5410a10db948428436d5210a10eb50842842fa6010a10be580428427f658ca109f996328427d658ca109f196328435e538ca10d754e328427f654ca109f995328427d654ca109f19532842bf644ca10a
  | 6 => 0x36e2194020db086500827d65d0020cfd53400833c54d00209fd96400827d6590020cf952400833d5490020b798e40082dd6390020bb98a40082ed62900209fd95400833f5450020cf151400827f65100209f994400827d65100209f194400833e5410020cf55040082ee6210020bb588400827d65cc020d7d4f300827f658c0209f59630082be648c020af592300835e538c020d754e30082ee628c020bb58a300827f654c020d7d4d300827e650c0209f594300827c650c020bb98830082ed620c020db953200836c54c8020db94f200836c53c8020bb987200836d51c8020af99220082bd6488020b798e20082dd6388020bb58a200836e5288020ee99220083b96488020f698e20083d96388020be58a200837a5288020fa94a20082fa6188020fa88620083e821880209fd9520082ef6548020dbd95200826f6548020db951200836c5448020db94d200836c5348020bb185200836d5148020bbd81200836e5048020fa90120083e94048020fa8c120083e93048020bed95200837b65480209ed9520082fb6248020fad89200837a5248020fa94920083ea4248020fa50920083ea3248020fa4c920082f86148020fa88520083e821480209f98b54c427d62d5310dd98754c437960d5310cfd5254c427e62953109f58a54c42ef6255310bb18954c433f64553109fd8954c436f62553109bd8954c427c6255310db18954c426c6255310ded8154c433d5415310cf99054c427e62153109f58854c43766115310de58054c427e64d4b109f59352c427e63d4b109f58f52c437661d4b10de58352c436f5294b109f99252c427d6494b109f98e52c427d6394b10afd9152c42bc6454b10b7d8d52c42dc6354b109fd9152c433f6454b108fd9152c427c6454b10cf19152c423c6454b109fd8d52c435f6354b1097d8d52c427c6354b10d718d52c425c6354b10dbd8952c437b6054b10db54852c427e6414b109f59052c427e6314b109f58c52c436e6214b10dd98452c43796014b109fd9742c427e65d0b109f59742c427c65d0b10dbd4b42c436c52d0b10be98342c42f960d0b109fd9642c427e6590b109f59642c427c6590b10cfd5242c433c5490b10be98242c42f96090b109fd9542c427e6550b109f59542c427c6550b10b7d8d42c42dc6350b10bed8142c42f86050b109fd9442c427e6510b109f59442c427c6510b10cfd5042c433c5410b10dbd4842c436c5210b10eb50842c427f658cb109f99632c427d658cb109f19632c435f538cb10d714e32c42fa608cb10be58232c427f654cb109f99532c427d654cb109f19532c42bf644cb10af19132c42fb604cb10be18132c427f650cb109f99432c427d650cb109f19432c436f520cb10db14832c43cd320cb10cfd5341c433c54d0710cf95241c433d5490710be98241c42f96090710cfd51
  | 7 => 0x214c20db988530827e6114c209f584530827e6014c20de980530827f65d0c209f997430827d65d0c209f197430835e53d0c20d754f430827f6590c209f996430827d6590c209f196430833e5490c20cf552430827f6550c209f995430827d6550c209f19543082ef6250c20bb189430827f6510c209f994430827d6510c209f194430833e5410c20cf550430835e5310c20d754c430839d4310c20bb98843082ed6210c20be98043082f96010c209f992520827d64948209f58e520827d65d0820db94b420827f65908209f596420833e5490820cf55242082fa6090820be582420827f6550820b7d8d42082dc63508209fd94420827d6510820cf950420833d5410820db94842083ad4210820be98042082f960108209f597320836e52cc8209fd96320827d658c820d794e320835d538c820be98232082f9608c8209fd9532082bf644c820af191320827f650c8209f594320835e530c820d754c320836e520c820f34c832082fa600c820be580320837751944209f992510827d64944209f98e510827d6394420afd9151082bc6454420b7d8d51082dc63544209fd91510833f64544208fd91510827c6454420cf191510823c64544209fd8d510835f635442097d8d510827c6354420d718d510825c6354420de18151082be6414420af59051082de6314420b758c510837551144209fd97410827e65d04209f597410833e54d0420cf55341082ee62d0420bb58b41082fa60d0420be583410827f65904209f996410827d6590420cfd52410833c54904209fd95410827d65504209f195410833e5450420cf55141082df6350420b718d41082ef6250420bb18941082fb6050420be181410827f65104209f994410827d6510420cfd50410833c54104209fd97310827e65cc4209f597310835e53cc420d754f31082ee62cc420bb58b31082fa60cc420be583310827f658c4209f996310827d658c420d7d4e310827f654c4209f595310827c654c420afd9131082bc644c420d794d310835d534c420bbd8931082ec624c420bed8131082f8604c4209fd94310827e650c4209f594310835f530c420db94b210837651c8420dd54721082fa60c8420be583210827d6588420bb596210836d65884209b596210836e5488420db152210836e5388420db14e21082ee6188420db54621083eb6088420bb58221083e860884209fd9521082bf6448420af19121082df6348420b718d210836e5248420bed8121083765108420dd54421082fa6008420be580210836e5408420db150210836e5308420db14c21082ee6108420f998421083e65108420db54421083e55108420fa98021082ed6008420fa580210827e6494020cf992500823e64940209f592500833d64940208f592500827e6394020d798e500825e63940209f58e500835d63940209758e5008
  | 8 => 0x209f994414827d65105209f194414833f5410520cf15041482ee6210520bb58841483ac4210520ddd4441483745110520be98041482f960105209f997314827d65cc5209f197314837751cc520dd147314827e658c5209f596314827c658c520d7d4e314835c538c520bb98a31482ed628c520f30ca314827f654c5209f995314827c654c520afd9131482bc644c520bbd8931482ec624c520bed8131482f8604c5209f994314827d650c5209f194314835f530c520d714c31482ee620c520bb58831483cc320c520ddd443148374510c520be98031482f9600c5209f99721482ee65c8520db997214826e65c8520bb99321482ec64c8520bb98f21482ec63c8520db14721482ee60c8520bb58a21483775188520dd14621482fa6088520be58221482bf6448520af19121482df6348520b718d21483775148520dd14521482fb6048520be18121483af6448520bb99121482ec6448520eb19121482ac6448520f3d8d21482ee6348520bb18d21483cc6348520b318d21483e76148520f9d45214836c5148520f914521483eb6048520bb18121483e86048520ba181214827e6508520bb988214827e65d0120cfd53404833c54d0120bb98b40482ed62d0120eb10b404827e6590120b798e40482dd6390120bb98a40482ed62901209fd95404827d65501209f195404833f5450120cf15140482ef6250120bb18940483ac42501209f99440483b940101209f997304835f53cc120d714f30482ee62cc120bb58b30483cc32cc120af99230482bd648c120bb98a30482ed628c1209f595304827c654c120bbd8930482ec624c120f30c930483eb42c8120fa10b20483eb32c8120fa0cb204837851c8120fac8720483e921c8120af99220482bd6488120b798e20482dd6388120bb99220483ae6488120ab99220483ad6488120bb19220482ee6388120f398e20482ce6388120f358e20482ed6188120db14620483eb5088120b798f54082dd63d50209f98f540835e63d50209798f540827d63d5020d758f540825d63d50209f98b540836e62d50209b98b540827e61d50209f587540827e60d5020de983540827d6595020cfd52540827e63950209f58e540827e61950209f586540833f64550209fd8d540827c63550209fd89540827d62550209fd85540827c6155020cf550540827e6415020cf990540827e63150209f58c540827e6215020db988540827e61150209f584540827e6015020de98054082be64d4c20af593530827e64d4c20cf993530823e64d4c209f593530833d64d4c208f593530836e62d4c209f987530827d61d4c20de983530827d6594c20d7d4e530827e6494c209f592530827e6194c209f586530827f6454c209f191530835f6354c209fd89530827d6254c209fd85530827c6154c20d754c530827e6414c209f590530827e6
  | 9 => 0x58c544827e62151209f188544827e61151209f584544827e64d4d209f593534836d62d4d209f987534827d61d4d20d7d4e534827e6494d209f592534836d6294d209f986534827d6194d20de58253482bf6454d20af19153482f76154d20bd185534827f6454d20cfd91534823f6454d209f191534833c6454d208f191534836f6254d209fd8553483776154d209dd85534827c6154d20dd18553482746154d209fd81534837b6054d209f994534835d5314d209f990534827d6414d20d798c534827c6214d209f984534827d6114d209fd97434827e65d0d209f597434827c65d0d20d7d4f434835c53d0d20bb98b43482ed62d0d20be98343482f960d0d209fd96434827e6590d209f596434827c6590d20cfd52434833c5490d20bb98a43482ed6290d20be98243482f96090d209fd95434827e6550d209f595434827c6550d20bbd8943482ec6250d209fd94434827e6510d209f594434827c6510d20cfd50434833c5410d20d7d4c434835c5310d20e750c434827e65d0920cfd53424833c54d0920be98342482f960d0920db997424826e65d0920dbd5342483af54d0920db55342483ac54d0920bb98f424836e53d0920db14f42482ed61d0920bb98342483ea60d0920ba98342483e960d09209f996424833e5490920cf55242482ee62909209f195424833f5450920cf15142482df6350920b718d42482fb6050920be181424827e6510920cf950424833d5410920eb50842482ee6510920db99442482ee6410920eb990424836f5410920eb950424836d5410920eb550424832d5410920bb98c424836e5310920db14c42483ae4310920eb10c42482ed6110920bb980424835f53cc920d714f32482fa60cc920be583324836e65cc920bb99332482ec64cc920db953324836c54cc920dbd4f32483cf53cc920f314f32482ed61cc920bb98332483ea60cc920ba98332483e960cc9209f996324835e538c920d754e32482ee628c920afd9132482bc644c920d7d4d324835c534c920bed8132482f8604c9209f994324835e530c920f34c832482ee650c920db99432482ee640c920bb190324836e540c920db15032482ee630c920f398c324836f530c920f394c324836d530c920f354c324834d530c920f3d0c32483cc430c920bb58432482ee600c9209f993514827d64d45209f98f514827d63d4520ddd4651482bf6454520af19151482df6354520b718d514837551145209f990514827d64145209f98c514827d6314520dbd08514836c4214520dbcc8514836c32145209f997414827d65d05209f197414837751d0520dd147414827e65905209f596414827c6590520cfd52414833c5490520bb98a41482ed6290520eb10a414827f65505209f995414827c6550520b7d8d41482dc6350520bbd8941482ec6250520bed8141482f860505
  | 10 => 0x18833d5490620d794e418835d53906209fd95418827d65506209f195418833e5450620cf55141882df6350620b718d418835e5350620d754d41882ef6250620bb18941882fb6050620be181418827f65106209f994418827d6510620cf950418833d5410620d794c418835d5310620be98041882f960106209fd97318827e65cc6209f597318833e54cc620cf553318835e53cc620d754f31882ee62cc620bb58b318827f658c6209f996318827d658c620cf952318833d548c620d794e318835d538c6209fd95318827d654c6209f19531882bf644c620af191318833e544c620cf551318835e534c620d754d31882ef624c620bb18931882fb604c620be181318827f650c6209f994318827d650c620cf950318833d540c620d794c318835d530c620be98031882f9600c620cf953218833d54c8620d794f218835d53c8620cf952218833d5488620d794e218835d5388620dd94621883755188620be98221882f96088620db95221883ae5488620cb95221883ad5488620db152218836e5388620f394e218834e5388620f354e21883e65188620db54621883e55188620fa98221882ed6088620fa58221882bf6448620af191218833e5448620cf55121882df6348620b718d218835e5348620d754d21883765148620dd54521882fb6048620be181218833e5408620cf550218835e5308620d754c21882ed6508620db594218836e5408620eb950218832e5408620eb550218836c5408620db94c21883ce5308620d394c21883cd5308620f9984218836d5108620bb580218833e54d0220cf553408835e53d0220d754f408833e5490220cf55240882de6390220b758e408835e5390220d754e40882ee6290220bb58a408833e5450220cf551408835e5350220d754d408833e5410220cf550408835e5310220d754c40882ee6210220bb58840883b94010220cf953308833d54cc220d794f308835d53cc220cf952308833d548c220bb98a30882ed628c220cf953208833d54c8220d794f208835d53c8220bb597208836d65c8220db95320883ae54c8220cb95320883ad54c8220db153208836e53c8220f394f208834e53c8220f354f20882ee61c8220db54720882f965c8220de59720883ba54c8220ee55320883da53c8220f654f208837a51c82209f98f544827d63d5120db58b544827e61d51209f587544833f54951209f992544827e63951209f58e544827d6295120db58a544827e61951209f586544827d6095120de58254482df6355120b718d54482f76155120bd185544833f64551209fd8d544835f635512097d8d544827c6355120d718d544825c63551209fd89544836f62551209fd85544837761551209dd85544827c6155120dd185544827461551209fd81544837b60551209f994544833d5415120cf990544827e63151209f
  | 11 => 0xde6315220b758c548833e64152209f98c548835e63152209798c548827d6315220d758c548825d6315220db588548827e61152209f584548837a6015220af99353882bd64d4e20cf953538833d54d4e209f993538833e64d4e208f993538827d64d4e20cf593538823d64d4e209f987538827d61d4e20de983538833e5494e20cf552538835f5394e209f992538827d6494e209f986538827d6194e20d7d52538835e5494e20e7952538831e5494e20d7552538839d5494e20c7552538835c5494e20d7d92538835e6494e20d7592538835c6494e20d7d8a538835d6294e20d7d86538835e6194e20d7586538835c6194e20d7982538835c6094e20cf951538833d5454e209fd91538827c6454e20d7d8d538827f6154e209f185538835f6554e20d7d51538835e5454e20e7951538831e5454e20d7551538839d5454e20c7551538835c5454e20d7d91538835e6454e20d7591538835c6454e20d7589538835f6154e20d7985538835d6154e20d7185538835e6054e20d718153882be6414e20af590538833e5414e20cf550538835d5314e209fd97438827e65d0e209f597438827c65d0e20cf953438833d54d0e20d794f438835d53d0e20be98343882f960d0e209fd96438827e6590e209f596438833e5490e20cf552438835e5390e20d754e43882fa6090e20be582438827f6550e209f995438827d6550e209f195438833e5450e20cf551438835e5350e20d754d43882ef6250e20bb189438827f6510e209f994438827d6510e20cf950438833d5410e20d794c438835d5310e20e750c43882ee6210e20bb588438833e54d0a20cf553428835e53d0a20d754f42882fa60d0a20be583428833e5490a20cf552428835e5390a20d754e428833e5450a20cf55142882df6350a20b718d428835e5350a20d754d42882fb6050a20be181428833e5410a20cf550428835e5310a20d754c42883ad4210a20cf953328833d54cca20d794f328835d53cca20be98332882f960cca20cf952328833d548ca20d794e32882bf644ca20af191328833e544ca20cf551328835e534ca20d754d32882fb604ca20be181328833e540ca20cf550328835e530ca20d754c32883cd320ca20af99351882bd64d4620cf953518833d54d4620b798f51882dd63d4620d794f518835d53d4620cf952518833d5494620d794e518835d5394620ddd46518827e64946209f592518827e63946209f58e518833e5454620cf551518835e5354620d754d518827f64546209f191518827f63546209f18d51882be6414620af590518833e5414620cf55051882de6314620b758c518835e5314620d754c518837551146209fd97418827e65d06209f597418833e54d0620cf553418835e53d0620d754f41882ee62d0620bb58b418827f65906209f996418827d6590620cf9524
  | 12 => 0xccb20db15332c836d53ccb20bb58732c82ee60ccb20d794e32c835d538cb20be98232c82f9608cb20afd9132c82bc644cb20d794c32c835d530cb20f34c832c82fa600cb20be58032c82ee640cb20bb19032c836e540cb20db15032c83ce630cb20f394c32c836d530cb20f354c32c834d530cb20f3d0c32c83cc430cb20bb58432c82ee600cb20fa98032c83e9600cb20af99351c82bd64d4720b798f51c82dd63d4720ddd4651c827e64947209f59251c827e63947209f58e51c836f4294720db10a51c836f3294720db0ca51c827f64547209f19151c827f63547209f18d51c837b6054720dd54451c827f65d07209f99741c827d65d0720be98341c82f960d07209fd9641c827e65907209f59641c833e5490720cf55241c82ee6290720bb58a41c83ac42907209fd9541c827d65507209f19541c82df6350720b718d41c82ef6250720bb18941c82fb6050720be18141c827f65107209f99441c827d6510720cf95041c833d5410720bb98841c82ed6210720eb10841c827f65cc7209f99731c827d65cc720be98331c82f960cc7209fd9631c827e658c7209f59631c835e538c720d754e31c82ee628c720bb58a31c83cc328c7209fd9531c827d654c7209f19531c82bf644c720af19131c82ef624c720bb18931c82fb604c720be18131c827f650c7209f99431c827d650c720d794c31c835d530c720bb98831c82ed620c720f30c831c837651c8720dd54721c82fa60c8720be58321c82ee64c8720bb19321c82ee63c8720bb18f21c836e51c8720f994721c83e551c8720bb98321c83ea60c8720fa58321c82bf6448720af19121c82df6348720b718d21c82f86048720bbd9521c836f6548720ebd9121c82ee6448720bb19121c83ac6448720ab19121c83cf6348720bb98d21c82ec6348720f318d21c82cc6348720f9d8521c836e5148720fad8121c82ec6048720fa18121c82e86048720dd94421c83755108720be98021c82f96008720cf95340c833d54d0320bb98b40c82ed62d0320eb10b40c82de6390320b758e40c82ee6290320bb58a40c833e5450320cf55140c82ef6250320bb18940c83ac4250320bb98b30c82ed62cc320f30cb30c82de63d5220b758f548827e63d5220d798f548825e63d52209f58f548835d63d52209758f548836d62d52209f987548827d61d5220de983548833f54952209f98e548827d63952209f986548827d6195220cfd8e548833e6395220cf58e548833c6395220cfd8a548833d6295220cfd86548833e6195220cf586548833c6195220cf982548833c6095220cfd91548827f63552209f18d548827f61552209f185548833f6555220cfd8d548833e6355220cf58d548833c6355220cfd89548833d6255220cfd85548833e6155220cf585548833c6155220cf981548833c6055220cf55054882
  | 13 => 0xcf94841102be6110440ed98441103b65110440cf54441103b55110440ee98041102bd6010440ee580411027f65c84409f997211027d65c8440af99321102bd64c8440db94b211036d52c8440be98321102f960c84409fd96211027e65884409f596211027f65484409f595211027c6548440afd9121102bc6448440b7d8d21102dc6348440db949211036d5248440bed8121102f860484409fd94211027e65084409f594211036e6294040db58a501033e4194040cf106501033e52d0040af987401033d51d0040af592401033e5490040bb98a40102ed6290040be592401037a5490040ee95240103ea6290040fa58a40102fa6190040ee90640103b841900409fd9540102bf6550040cfd95401023f6550040cf94940102bc6150040cf54540102bf6050040cf94140102fb6550040ded95401027b6550040bed9140103bb6450040de95140103ba5450040eed0940103b94250040be18540103ba4150040ee105401027e63d53209f58f54c836e62d53209f98754c827d61d5320de58354c833f54953209f98e54c827d63953209f98654c827d6195320b7d8d54c82dc6355320cfd9154c827f6355320d7d8d54c825f63553209f18d54c835c63553209718d54c836c62553209fd8554c827c6155320cf55054c82de6315320b758c54c833e64153209f98c54c835e63153209798c54c827d6315320d758c54c825d6315320db98854c827e61153209f58454c83796015320d7d4e53c827e6494f209f59253c827e6194f209f58653c82bf6454f20af19153c827f6454f20cfd9153c823f6454f209f19153c833c6454f208f19153c827f6154f209f18553c82be6414f20af59053c835d5314f209f99053c833e6414f208f99053c827d6414f20cf59053c823d6414f20db98853c827e6114f209f58453c83796014f209fd9743c827e65d0f209f59743c833e54d0f20cf55343c82ee62d0f20bb58b43c827f6590f209f99643c827d6590f209f19643c833f5490f20cf15243c835e5390f20d754e43c82ee6290f20bb58a43c827f6550f209f59543c827c6550f20cf95143c833d5450f20d794d43c835d5350f20bbd8943c82ec6250f209fd9443c827e6510f209f59443c827c6510f20cfd5043c833c5410f20e750c43c82fa6010f20be58043c82ed65d0b20db59742c836f54d0b20db55342c82ee63d0b20db94f42c836c53d0b20bb58742c82ee60d0b20cf95242c833d5490b20be98242c82f96090b20b7d8d42c82dc6350b20cf95042c833d5410b20eb50842c82fa6010b20be58042c836d6510b20eb99042c836f5410b20eb95042c836d5410b20eb55042c832d5410b20bb98c42c836e5310b20db14c42c83ae4310b20eb10c42c82ed6110b20bb98042c83ea6010b20fa58042c82ed65ccb20db59732c82ee64ccb20bb19332c836e54
  | 14 => 0x81425027e6510940eb50842502be6510940cf99442502be6310940cf14c42502be6210940eb988425033f5210940eb94842503ad5210940af58442502be60109409f996325027d658c9409f19632502be648c940af592325035f538c940d714e325039c438c940be98232502f9608c9409fd95325027e654c9409f19532502bf644c940af191325027e650c9409f594325027c650c940afd9032502bc640c940dbd48325036c520c940eb10832503cd320c9409f98b515027d62d4540ddd4651502ef6254540bb189515037551145409f988515027d6214540cf908515033c42145409f99741502be65d0540cf997415023e65d0540af98b415033c51d0540af98341502bd6490540ddd4641503745190540be98241502f96090540bbd8941502ec6250540ddd4541503745150540bed8141502f86050540ebd8941502bc6250540eb18941502ac6250540edd8541503b75150540cf14541503b45150540eed8141502bc6050540ee18141502b860505409f99441502be64105409f997215027d65c85409f19721502bf64c8540af193215037751c8540dd147215027e65885409f596215027c6588540af99221502bd6488540dbd4a215036c5288540eb10a215027f65485409f995215027c6548540afd9121502bc6448540b7d8d21502dc6348540bed8121502f860485409f994215027d65085409f19421502be6408540af590215036f5208540db14821503ac4208540ddd4421503745108540be98021502f96008540ee90b40503b842d0140de14740503bb41d0140ee50740502ee6290140bb58a40502be6290140eb98a40502ae6290140eb58a40502bd6190140cf14640503bb5090140b798f52102dd63d4840dbd4a521027e63948409f58e521027e61948409f586521027f63548409f18d521027f61548409f185521036d5214840db94b421036d52d0840be98342102f960d08409f596421033e54908409fd9542102df6350840b718d421033e5410840db948421036d5210840eb50842102fa6010840be580421027f658c8409f996321027d658c840d794e321035d538c8409fd95321027d654c8409f19532102bf644c840af191321027f650c8409f994321027d650c840af99032102bd640c840db948321036d520c840f34c832102fa600c840be580321037751944409f98a511027d6294440bbd8951102ec62544409fd89511036f62544409bd89511027c6254440db189511026c6254440de18151102ee6214440bb58851103755114440cf953411037651d0440dd54741102fa60d0440be583411027d6590440af596411033d65904408f596411033e5290440af986411033d5190440eed8241102bd6090440ee182411027f6550440cf95141102ef6250440bb18941102fb6050440dd94441103755110440be98041102f9601044
  | 15 => 0x9027c6354a409fd85529027c6154a40dbd95529036f5354a40db94d52903ce5354a40d394d529036d5354a40f354d529034d5354a40db591529036f6354a40db98d529036d6354a40db18d529036f6154a40db985529036d6154a40db185529036e6054a40db18152902de6314a40b758c529035e5314a40d754c529036d5214a40d794f429035d53d0a40db94b429035e5390a40d754e429036e5290a40db54a42902fa6090a40be58242902df6350a40b718d429035e5350a40d754d429036e5250a40db54942902fb6050a40be181429035e5310a40d754c429036d5210a40eb508429027f658ca409f996329027d658ca40d794e329035d538ca40db94a329036d528ca40be98232902f9608ca409fd95329027d654ca409f19532902bf644ca40af191329036e524ca40db549329027f650ca409f994329027d650ca40af99032902bd640ca40db948329036d520ca40f34c832902ee62d4640bb58b519036e52d4640db54b519036e5294640db54a519037751946409f98a519027d6294640db949519036d52546409fd89519027c6254640bb98851902ed6214640db948519036d5214640dd544519036e52d0640db54b419036e5290640db54a41903765190640dd54641902fa6090640be582419033e5290640eb94a419032e5290640eb54a41903b65190640cf54641903b55190640ee98241902bd6090640ee58241902ef6250640bb189419036e5250640db54941903765150640dd54541902fb6050640be181419036e5210640db54841902bd6510640cf594419033e5210640eb948419032e5210640eb54841903b66110640cf54441902bd60106409fd97219027e65c86409f59721902be64c8640af593219035e53c8640d754f219036e52c8640db54b219027f65886409f996219027d6588640d794e219035d5388640db94a219036d52886409fd95219027d65486409f19521902bf6448640af19121902df6348640b718d219035e5348640d754d219036e5248640db54921902fb6048640be181219027f65086409f994219027d6508640d794c219035d5308640db948219036d5208640be98021902f96008640db94b409036d52d0240af597409033d65d0240cf94b40903ae52d0240cb94b40903ad52d0240af987409033d51d0240be597409037965d0240fa94b40903e952d0240de947409027e63d49409f58f525027e61d49409f587525036f5294940b7d8d52502dc6354940bdd8552502f46154940db548525027e63149409f58c525027e61149409f584525027e65d0940dbd4a425036c5290940be98242502f96090940af98e425033c5390940af98a425033f5290940ebd4a42503ac5290940af58642502be6090940ee98242502ba6090940ee58242502df6350940b718d425036f5250940db14942502fb6050940be1
  | 16 => 0xe6448421bb19121087ac6448421ab19121087cf6348421bb98d21086ec6348421f318d21086cc6348421bbd85210876e5148421fad8121086ec6048421fa18121086e86048421bdd95210877765484219dd9521087b76448421ed19121087d76348421f518d21086f76248421f9d8921087765248421f994921087f36048421fc181210877b50940219f992500867d64940219f98e500867d63940219fd91500867c64540219fd8d500867c6354021dbd09500876c4254021dbcc9500876c3254021dbc85500876d2154021af99050086bd6414021b798c50086dd6314021de540500876f5294b409f98e52d027d6394b409f98652d027d6194b40b7d8d52d02dc6354b409fd8d52d035f6354b4097d8d52d027c6354b40d718d52d025c6354b409fd8552d027c6154b40b798c52d02dd6314b40db54852d036e52d0b40db54b42d02fa60d0b40be58342d02bd6590b40cf59642d02be6390b40cf94e42d033d5290b40af58642d02be6090b40b7d8d42d02dc6350b40db94842d036d5210b40eb50842d02fa6010b40be58042d02be6310b40cf94c42d03ae6210b40eb94842d033d5210b40eb54842d032d5210b40af58442d02be6010b40ee98042d03b96010b409fd9632d027e658cb409f59632d02be648cb40af59232d039c438cb40db94a32d036d528cb409fd9532d027d654cb409f19532d02bf644cb40af19132d036e524cb40db54932d027f650cb409f99432d027d650cb40afd9032d02bc640cb40eb10832d03cd320cb40be98032d02f9600cb40bb98b51d02ed62d4740ddd4651d027e62947409f58a51d033e4294740cf10a51d027f62547409f18951d037b6054740dd54451d037651d0740dd54741d02fa60d0740be58341d02be62d0740cf94741d03b651d0740ed54741d02be60d0740ee98341d03b960d0740bbd8941d02ec6250740be18141d02bf6550740cfd9541d03af6250740af18941d03ac6250740ab18941d03b76150740cf94541d03bb6050740af18141d03b86050740ae18141d03765110740dd54441d02fa6010740be58041d027f65c87409f99721d027d65c8740afd9321d02bc64c8740be98321d02f960c87409fd9621d027e65887409f59621d02be6488740af59221d036e5288740db54a21d03ac42887409fd9521d027d65487409f19521d02bf6448740af19121d02df6348740b718d21d02fb6048740be18121d027f65087409f99421d027d6508740af99021d02bd6408740db94821d036d5208740eb10821d02de63d4a40b758f529036f5294a409f98e529027d6394a409f986529027d6194a40dbd4e529036e5394a40f394e529034e5394a40dbd92529036f6394a40db98e529036d6394a40db18e529036f6194a40db986529036d6194a40db186529036e6094a40db182529035e5354a409fd8d52
  | 17 => 0x4c21de980530867a6014c219f58053087796014c219e580530867f65d0c219f997430867d65d0c219f197430873e54d0c21cf553430875f53d0c21bb98b43086ed62d0c219fd96430867e6590c219f596430867c6590c21cfd52430873c5490c21d794e430875d5390c21bb98a43086ed6290c219fd95430867e6550c219f595430867c6550c21cf951430873d5450c21d794d430875d5350c21bbd8943086ec6250c219fd94430867e6510c219f594430867c6510c21cfd50430873c5410c21d7d4c430879d4310c219f992520867d64948219f58e520867d65d0821bb597420876d65d0821dbd53420876d54d0821bb98f420876e53d0821db14f42086ed61d0821bb983420867f65908219f596420873e5490821cf55242086ee6290821bd98642086f561908219fd9542086df6350821b718d420867f65108219f594420873e5410821cf55042087ad4210821bd98442086f56110821db594420866d6510821bb99042087ae6410821dbd5042087ae5410821db55042087ad5410821cb55042086ee6310821db94c420876c5310821eb90c42087ac4310821f998442086ed6110821f958442086ee60108219f59732086ed65cc821db59732086ee64cc821bb193320876e54cc821db153320876f53cc821db54f32086ed61cc821bb983320867f658c8219f596320875e538c821d754e32086ee628c821bd98632086f5618c8219fd9532086bf644c821af191320867f650c8219f594320875e530c821d754c32087cd320c821bd98432086f5610c821db594320866d650c821bb99032086ec640c821db950320876c540c821bb98c32087ce630c821dbd4c32087ce530c821db54c32087cd530c821d354c32087cf430c821f310c32087e6610c821bb58432087e5610c821bb980320867e64944219f592510867e63944219f58e510876f4294421db10a510876f3294421db0ca510867d65d04219fd96410867d6590421cf952410873d5490421bb98a41086ed6290421eb10a410867f6550421b7d8d41086dc6350421bbd8941086ec6250421bed8141086f860504219fd94410867e65104219f594410867c6510421cf950410873d5410421bb98841086ed6210421eb108410867d65cc4219fd96310867d658c421d794e310875d538c421bb98a31086ed628c421f30ca310867f654c421afd9131086bc644c421bbd8931086ec624c421bed8131086f8604c4219f994310867d650c4219f19431086ee620c421bb58831087cc320c421bb99321086ec64c8421bb98f21086ec63c8421bb98321086ed6288421db94a21086f56288421dd94a21087e65288421f9d0a21087e44288421f9cca21087e432884219fd9521086bf6448421af19121086df6348421b718d21086fb6048421be18121086ef6548421dbd95210866f6548421ebd9121086e
  | 18 => 0xde553504877854d4121ee153504873854d4121ded4f50487db53d4121d6d4f504877a53d4121de54f504877853d4121f614f504875853d4121fad8b50487f321d4121fa887504877b64d4121de993504877964d4121de193504877b63d4121de98f504877963d4121de18f504877b43d4121de90f504877943d4121de10f504877b62d4121ded0b504877a42d4121de50b504877842d4121deccb504877a32d4121de4cb504877832d4121ded87504877b41d4121de907504877941d4121de107504877b31d4121de8c7504877931d4121dec87504877a21d4121af99250486bd6494121cfd52504873c5494121b798e50486dd6394121d7d4e504875c5394121ded4250486bf6454121af191504873f5454121cf15150486df6354121b718d504875f5354121d714d504873f5414121cf150504875f5314121d714c504877950141219f990504867d64141219f98c504867d6314121db88450486fa6514121de994504877b5414121eed50504873b5414121de95050487795414121de15050487b85414121ce150504877b5314121f6d4c504875b5314121de94c50487795314121de14c50487d85314121d614c50487e96214121fcc8450487ea2114121ded90504877a6414121de59050487786414121ded8c504877a6314121de58c50487786314121ded0c504877a4314121de50c50487784314121ded88504877b4214121de90850487794214121de108504877b3214121de8c850487793214121de0c8504877b6114121ded04504877a4114121de50450487784114121decc4504877a3114121de4c4504877b2114121de884504876a2114121de484504867e63d50219f58f540867e62d5021db98b540867e61d5021dd987540867e60d50219f583540867d6595021cfd52540867e63950219f58e540867e60950219f58254086df6355021b718d540873f64550219fd8d540875f635502197d8d540867c6355021d718d540865c6355021db189540867f60550219f181540873d5415021b798c54086dd6315021be98054086f960150219f990540873e64150219f98c540875e63150219798c540867d6315021d758c540865d63150219f988540876e62150219f984540877661150219f980540877a60150219e980540867d6015021de580540867960150219f993530867d64d4c21db98b530877661d4c219f983530867d60d4c219f596530875f5394c219f992530867d6494c219f982530867d6094c21afd9153086bc6454c219fd91530873f6454c218fd91530867c6454c21cf191530863c6454c21d7d8d530876c6254c219fd81530867c6054c21af99053086bd6414c21d754c53086fa6014c21be580530867e6414c21cf990530863e6414c219f590530873d6414c218f590530867e6214c21db988530867e6114c21dd984530867e601
  | 19 => 0x1534867c6454d21cf191534863c6454d21dbd89534867f6154d21ddd85534867f6054d21ded81534867b6054d219f18153487786054d219e181534867e6514d21cfd50534873c5414d21d754c534867e6414d219f590534875e6314d219f980534867d6014d21b7994534875e6514d2197994534875f5414d21e7d50534871f5414d21d7950534875d5414d21d7150534879c5414d21c7150534875f6414d21d7990534875d6414d21d7190534875f6214d21d7d84534875d6114d21d7484534875f6014d21d7980534875d6014d21d7180534867f65d0d219f997434867d65d0d219f197434873f54d0d21cf153434875f53d0d21d714f434867f6590d219f996434867d6590d219f196434873f5490d21cf152434875f5390d21d714e434867f6550d219f995434867d6550d219f195434873f5450d21cf151434875f5350d21d714d43486ef6250d21bb189434867f6510d219f994434867d6510d219f194434873f5410d21cf150434875f5310d21d714c434879d4310d21bb98843486ed6210d219f997424873f54d0921cf153424875f53d0921d714f42486f661d0921bd587424867e6590921cfd52424873c5490921d7d4e424875c53909219f195424873f5450921cf15142486df6350921b718d424875f5350921d714d42486f76150921bd185424867e6510921cfd50424873c5410921d7d4c424875c5310921eb508424873f54cc921cf153324875f53cc921d714f32486f661cc921bd587324867e658c921cfd52324873c548c921d7d4e324875c538c921afd9132486bc644c921cfd51324873c544c921d7d4d324875c534c921bdd8532486f4614c9219f994324873f540c921cf150324875f530c921f34c8324867e65d0521cfd53414873c54d0521d7d4f414875c53d0521bb98b41486ed62d05219f996414873f5490521cf152414875f5390521d714e414867f65505219f595414867c6550521cfd51414873c5450521b7d8d41486dc6350521d7d4d414875c5350521bbd8941486ec6250521bed8141486f860505219f994414873f5410521cf150414875f5310521d714c414867e65cc521cfd53314873c54cc521d7d4f314875c53cc521bb98b31486ed62cc521cfd52314873c548c521d7d4e314875c538c5219f595314867c654c521cfd51314873c544c521bbd8931486ec624c521cfd53214873c54c8521d7d4f214875c53c8521edd5321487b454c8521f5d4f21487d453c8521cfd52214873c5488521d7d4e214875c5388521ebd52214876e5488521db15221487ac5488521cb15221487cf5388521db94e214876c5388521f314e214874c5388521f9d4621486ed6088521cfd53504873c54d4121d7d4f504875c53d41219f993504867d64d41219f98f504867d63d4121ded5350487bb54d4121ced53504877a54d4121
  | 20 => 0x87cd53cca21f998732886ed61cca21f958732886ee60cca21d7d4e32886bf644ca21af191328875e534ca21d754d32886f7614ca21bd18532887cd320ca21bb594328876d650ca21bb99032886ec640ca21db950328876c540ca21f398c328876f530ca21f3d4c328874f530ca21db54c32887cc530ca21f3d0c32887cc430ca21bb58432886ee600ca21cf952418873d5490621bb98a41886ed6290621eb10a41886df6350621b718d41886ef6250621bb18941886fb6050621be181418873e5410621cf55041886ee6210621bb58841887ac4210621bb98a31886ed628c621f30ca31886ed65c8621db59721886ee64c8621bb19321886ee63c8621bb18f21886ee60c8621bd597218877565c8621ded42508867e64942219f592508867e63942219f58e508867f64542219f191508867f63542219f18d508876f4254221db109508876f3254221db0c9508876f2154221af99050886bd6414221b798c50886dd6314221de540508867e63d51219f58f544867e60d51219f583544873f63d5121cf98f544873d63d5121cf18f544873f62d5121cf58b544873f61d5121cf587544873f60d5121cf983544873d60d5121cf183544873f5495121b798e54486dd6395121be98254486f960951219f992544863e64951219f98e544875e63951219798e544867d6395121d758e544865d63951219f58a544876d62951219f586544877561951219f982544877a60951219e982544867d6095121de58254486796095121b7d8d54486dc6355121bed8154486f86055121cfd91544867f6355121d7d8d544865f63551219f18d544875c63551219718d544867f6255121dbd89544866f62551219fd85544877761551219fd81544877b60551219ed81544867c6055121de181544867860551219f994544873d5415121cf990544867e63151219f58c544867e60151219f58054486be6515121cf994544863e6515121cfd8c544873e6315121cf58c544873c6315121cfd88544873d6215121cfd84544873d6115121cf484544873f6015121cf980544873d6015121cf180544873f54d4d21cf153534867e64d4d219f593534867e60d4d219f583534875f54d4d21e7d53534871f54d4d21d7953534875d54d4d21d7153534879c54d4d21c7153534875f64d4d21d7993534875d64d4d21d7193534875f62d4d21d758b534875f61d4d21d7587534875f60d4d21d7983534875d60d4d21d718353486be6494d21af592534873f5494d21cf152534875f5394d21be98253486f96094d219f992534873e6494d218f992534867d6494d21cf592534863d6494d21db58a53487756194d219f982534877a6094d219e982534867d6094d21de58253486796094d21afd9153486bc6454d21cfd51534873c5454d21bed8153486f86054d219fd91534873f6454d218fd9
  | 21 => 0x5490f21cf55243c867f6550f219f59543c867c6550f21bbd8943c86ec6250f219fd9443c867e6510f219f59443c867c6510f21cf95043c873d5410f21d794c43c875d5310f21e750c43c86ee6210f21bb58843c873e5490b21cf55242c86f66190b21bd58642c86df6350b21b718d42c873e5410b21cf55042c87ad4210b21bd98442c86f56110b21d794e32c875d538cb21bd98632c86f5618cb21afd9132c86bc644cb21d794c32c875d530cb21f34c832c86f6610cb21bd58432c873e54d0721cf55341c86ee62d0721bb58b41c873f5490721cf15241c873e5450721cf55141c86df6350721b718d41c86ef6250721bb18941c86fb6050721be18141c873f5410721cf15041c86ee62cc721bb58b31c86be64d4321af59350c86de63d4321b758f50c86be6494321af59250c86de6394321b758e50c877b50943219f99250c873e64943218f99250c867d6494321cf59250c863d64943219f98e50c875e63943219798e50c867d6394321d758e50c865d63943219fd9150c867c64543219fd8d50c867c6354321de54050c86de63d5221b758f548867e63d5221d798f548865e63d52219f58f548875d63d52219758f548876d62d5221dd987548867e60d52219f583548873f54952219f98e548867d63952219f982548867d6095221cfd91548867f63552219f18d548876f62552219fd81548867c6055221cf550548873e64152219f98c548867d6315221db588548877661152219f980548867d6015221af99353886bd64d4e219f993538873e64d4e218f993538867d64d4e21cf593538863d64d4e21dd987538867e60d4e219f583538875f5394e219f992538867d6494e219f982538867d6094e219fd91538867c6454e21d7d8d538867f6054e219f181538875d5314e219fd97438867e65d0e219f597438867c65d0e21d794f438875d53d0e21bb98b43886ed62d0e219fd96438867e6590e219f596438873e5490e21cf55243886ee6290e21bb58a438867f6550e219f995438867d6550e219f19543886ef6250e21bb189438867f6510e219f994438867d6510e21cf950438873d5410e21d794c438875d5310e21e750c438873e54d0a21cf55342886f661d0a21bd587428876d65d0a21dbd5342887ae54d0a21db55342887ad54d0a21bb98f428876e53d0a21f998742886ed61d0a21f958742886ee60d0a21cfd52428873c5490a21cf951428873d5450a21b7d8d42886dc6350a21bdd8542886f46150a21cfd50428873c5410a21eb50842886ed6510a21db59442887ae6410a21dbd5042887af5410a21cbd50428876d5410a21eb15042886ee6310a21db94c42887ae4310a21eb10c42886ed6110a21bb980428875e53cca21d754f32886f661cca21bd58732886ee64cca21bb193328876e54cca21db15332887ce53cca21db54f328
  | 22 => 0x141de54850507785214141fa14850507685214141fcd0450507ba4114141ded90505077b6214141de98850507796214141de188505077b4214141de90850507794214141de108505077a3214141de4c850507783214141ded84505077b4114141de904505073a4114141de504505076f52948419f98e521067d63948419f982521067d6094841b7d8d52106dc63548419fd8d521075f635484197d8d521067c6354841d718d521065c63548419fd81521067c6054841b798c52106dd6314841db54852106fa6014841be580521076e52d0841db54b42106f661d0841bd587421067d6590841af596421073d6590841af98e421073e5390841af98a421073d5290841af58642106be60908419fd9542106df6350841b718d421076e5210841db54842107ad4210841bd98442106f56110841af98c421073e5310841af98842107ae6210841eb948421073d5210841eb548421072d5210841ed98442106bd6110841ed58442106be60108419fd96321067e658c8419f59632106be648c841af592321079c438c841db94a321076d528c8419fd95321067d654c8419f19532106bf644c841af191321076e524c841db549321067f650c8419f994321067d650c841afd9032106bc640c841eb10832107cd320c841cf90a511073c4294441af98b41106be60d0441af592411073e5490441bd59241107765490441ed95241107b64290441ed10a411067f6550441bbd8941106ec6250441bed8141106f86050441afd95411073f65504418fd9541107af6250441af18941107ac6250441ab18941106bf6150441cf94541107bb6050441af18141107b86050441ae18141106f76550441ddd9541106776550441bdd9141107b76450441dd95141107b65450441f9d8941107e46250441fcd8141107f06050441ded42501067e62940419f58a501067f62540419f189501073e4254041cf109501073f4154041cf50550106ee6214041bb58850107795014041b798f54c86dd63d5321be98354c86f960d53219f98f54c875e63d53219798f54c867d63d5321d758f54c865d63d5321db98b54c877561d53219f98354c877a60d53219e98354c867d60d5321de58354c867960d5321cfd5254c867e63953219f58e54c867e60953219f58254c873f64553219fd8d54c867c63553219fd8154c867c6055321cf55054c873e64153219f98c54c867d6315321db98854c877561153219f98054c867d6015321af99353c86bd64d4f21be98353c86f960d4f21d7d4e53c867e6494f219f59253c867e6094f219f58253c867f6454f219f19153c867f6054f219f18153c875d5314f219f99053c867d6414f21db98853c87756114f219f98053c867d6014f219fd9743c867e65d0f219f59743c875e53d0f21d754f43c867f6590f219f99643c867d6590f219f19643c873e
  | 23 => 0xb50842906bd6510a41cf59442906be6310a41cf94c42907ae6210a41ebd48429073d5210a41eb14842906bd6110a41af980429067f658ca419f996329067d658ca41af99232906bd648ca41d794e329075d538ca41e710e329067f654ca419f595329067c654ca41afd9132906bc644ca419fd94329067e650ca419f59432906bf640ca41af190329076e520ca41db54832907ac420ca41f34c832906bd65d0641cf59741906be62d0641af98341906f565d0641dd597419077b50942419f98a509067d62942419fd89509067c6254241cf909509073c4254241cfd0550906ee6214241bb588509077950142419f98f525067d63d49419f983525067d60d4941dbd4f52507cf53d4941d3d4f525076f64d4941dbd8f525076e63d4941db58f525076c63d4941dbd87525076d61d4941dbd83525076e60d4941db583525076c60d4941b798e52506dd6394941d7d4e525076f5294941be98252506f96094941b7d8d52506dc6354941d7d4d52506fb6054941be181525075f5314941db548525067e63149419f58c525067e60149419f58052506ee6514941db994525076f5314941f3d4c525074f5314941db94c525076d5314941db14c52507cc5314941d314c525076f6414941dbd8c525076e6314941db58c525076c6314941dbd84525076d6114941db504525076f6014941db980525076d6014941db180525067e65d0941d7d4f425075c53d0941db14b425075f5390941d714e425076f5290941db14a42506f66190941bd58642506df6350941b718d425075f5350941d714d425076f5250941db14942506f76150941bd185425067e6510941d7d4c425075c5310941dbd4842507ad42109419f996325067d658c9419f196325075f538c941d714e325076f528c941db14a325067f654c9419f995325067c654c941afd9132506bc644c941dbd49325076c524c9419f994325067d650c9419f19432506be640c941af590325076f520c941db14832507cd320c941dbd4b415076c52d0541f9d4b41507e452d0541dbd4a415076c5290541ebd4a415073c5290541eb14a415072c5290541edd4641506bd6090541dbd4b505076c52d41419f98b505067d62d4141eed93505077b52d4141fad4b505076b52d4141de94b505077952d4141de14b50507e852d4141da14b50507f341d4141ee907505077b64d4141ded8b505077a62d4141de58b505077862d4141ded0b505077a42d4141de50b505077842d4141de8cb505077932d4141de0cb505077b61d4141ded07505077a41d4141bb98a50506ed6294141dbd4a505076c5294141ded4250506ef6254141bb189505076f5254141db149505076f5214141db148505077950141419f988505067d6214141cf90450506fa6514141de99450507b96414141ded4850507eb5214141dad48505077a5214
  | 24 => 0x420cb6d5410832eb550420cb2d5410832f398c420caed6310832f358c420cacd6310832db94c420cbcf4310832eb90c420cbac4310832f310c420cb8c4310832bb984420caed6010832bb992320caec648c832bb58e320cacd638c832db94e320cbce538c832f3d0e320cbcc438c832bb986320caed608c8329fd95320cabf644c832af191320caef654c832dbd95320ca6f654c832ebd91320caee644c832bb191320cbac644c832ab191320caef634c832db94d320cbce534c832f3d0d320cbce434c832f350d320cbcc434c832bb185320caef604c832f3d95320cacf654c832d3d95320cbcf644c832e3d91320cbce644c832b3991320cbcd644c832f3191320cacc644c832e3191320ca8c644c832f3d51320cbce544c832f3551320cbcc544c832f3d85320cbce614c832f3585320cbcc614c832b3185320cbcf604c832b3d81320cbce604c832f3581320cbcc604c832f34cb510cbcd3294432ddd46510ca7e64944329f592510cb6f4294432db10a510ca7e60944329f582510cabf6454432af191510cbcd3254432bed81510caf860544329fd91510cb3f64544328fd91510ca7c6454432cf191510ca3c64544329fd81510cb7b60544329ed81510ca7c6054432de181510ca786054432af990510cabd6414432f34c8510cb755114432be980510caf96014432af993500cabd64d4032f34cb500cabe6494032af592500cbcd3294032ded42500ca7e6494032cf992500ca3e64940329f592500cb3d64940328f592500ca7e61940329f586500cbcd32540329fd91500ca7c6454032dbd09500cb6c42540329fd85500ca7c6154032f34c8500cb795014032b798f52d06dd63d4b41be98352d06f960d4b41dbd4a52d067e6394b419f58e52d067e6094b419f58252d067f6354b419f18d52d067f6054b419f18152d076d5214b41db94b42d076d52d0b41bd98742d06f561d0b41b7d8d42d06dc6350b41db94842d076d5210b41eb50842d06f66110b41bd58442d067f658cb419f99632d067d658cb41d794e32d075d538cb419fd9532d067d654cb419f19532d06bf644cb41af19132d067f650cb419f99432d067d650cb41af99032d06bd640cb41db94832d076d520cb41f34c832d06ee62d4341bb58b50d06ee6294341bb58a50d077b50943419f98a50d076e62943419b98a50d067d6294341db58a50d066d62943419fd8950d067c6254341de54050d06de63d4a41b758f529076f5294a419f98e529067d6394a419f982529067d6094a419fd8d529067c6354a419fd81529067c6054a41db548529076e5290a41db54a42906f66190a41bd58642906be6390a41cf94e42907ae5290a41cf54a42907ad5290a41ed98642906bd6190a41ed58642906be6090a41b7d8d42906dc6350a41db949429076d5250a41bdd8542906f46150a41e
  | 25 => 0xb7b50942329f992508ca7d64942329f986508ca7d61942329fd91508ca7c6454232d7d0d508cb5c4354232dbcc9508ca7f61542329f185508cabe6414232af590508cb7950142329f987544ca7d61d51329f983544ca7d60d5132cfd8b544cb3d62d5132cfd87544cb3e61d5132cf587544cb3c61d5132cfd83544cb3e60d5132cf583544cb3c60d5132cfd52544ca7e64951328f992544ca7d6295132db58a544ca7e61951329f586544ca7e60951329f582544cb3f64551329fd89544cb6f62551329bd89544ca7f61551329f185544ca7f60551329f181544ca7e6515132cf550544cb3e64151329f984544ca7d61151329f980544ca7d6015132af994544cb3e65151328f994544cb3f6215132cf588544cb3d3215132cfd84544cb3e6115132cf584544cb3c6115132cfd80544cb3e6015132cf580544cb3c60151329f997424cb3f54d0932cf153424cade63d0932b758f424ca7e6590932cfd52424cb3c54909329fd95424ca7d65509329f195424cb3f5450932cf151424cadf6350932b718d424ca7e6510932cfd50424cb3c5410932eb508424cb3f548c932cf152324cb9f548c932d7952324cb5c548c932e7152324cb1c548c932f3d4a324cb3f54d4532cf153514ca7e64d45329f593514ca7e60d45329f583514cabe6494532af592514cb3f5494532cf152514cb775194532afd91514cabc6454532cfd51514cb3c5454532bed81514caf86054532cfd50514cb3c5414532dd544514ca7e64145329f590514cb5e32145329f980514ca7d6014532cfd53504cb3c54d41329f993504ca7d64d4132d78cb504ca7e61d41329f587504cabe6494132af592504cb3f5494132cf152504cb7b5094132afd91504cabc6454132cfd51504cb3c5454132bdd85504caf46154132cfd50504cb3c5414132de540504ca7e64141329f590504ca7e61141329f584504cafa60d5032be583540ca7e62d5032db98b540ca7e61d50329f587540ca7e60d5032de983540ca7a60d50329f583540cb7960d50329e583540ca7d6595032cfd52540ca7e61950329f586540ca7e60950329f582540cb3f6455032db189540ca7f61550329f185540ca7f60550329f181540cb3d54150329f990540cb3e64150329f988540cb6e62150329f984540ca7d61150329f980540ca7d60150329f992520ca7d64948329f597420caed65d0832db597420cb6f54d0832db553420cbcf63d0832bb58f420cbcc63d0832db94f420cbcf43d0832bb987420caed60d08329fd96420ca7d6590832cf952420cb3d5490832b798e420cadd6390832bb98a420ca7f6550832b7d8d420ca7f65108329f994420ca7d65108329f194420cb3e5410832cf550420cade6310832b758c420cbad4210832bb594420cb6d65108329b594420caee6410832eb990420cb6f5410832eb950
  | 26 => 0x390842eb90e4210bac4390842bb9864210aed60908429fd954210adf6350842b718d4210abf6550842cfd954210a3f6550842e7d8d4210abc6350842e718d4210a9c6350842afd894210b3e5250842af1854210abf6050842bbd954210b6f65508429bd954210aef6450842ebd914210b6e5450842eb9514210bcf6350842bb18d4210bcc6350842b318d4210baf4350842eb90d4210bad4350842eb10d4210aec6150842bbd814210baf6550842abd954210b2f6550842ebd8d4210b8f6350842eb98d4210bad6350842eb18d4210aac6350842e318d4210a8c6350842ebd4d4210bae5350842eb54d4210bac5350842ebd854210bae6150842eb5854210bac6150842ab1854210baf6050842abd814210bae6050842eb5814210bac6050842eb50b5110bad4294442ddd465110a7e63944429f58e5110b3e4394442cf10e5110a7e60944429f5825110adf6354442b718d5110bad4254442bed815110af860544429fd8d5110b5f635444297d8d5110a7c6354442d718d5110a5c63544429fd815110b7b60544429ed815110a7c6054442de1815110a786054442b798c5110add6314442eb5085110b755114442be9805110af96014442b798f5010add63d4042eb50b5010ade6394042b758e5010bad4294042ded425010a7e6394042d798e5010a5e63940429f58e5010b5d63940429758e5010a7e61940429f5865010bad42540429fd8d5010a7c6354042cf90d5010b3c43540429fd855010a7c6154042eb5085010b795014042d758f548cb6e62d52329f987548ca7d61d52329f983548ca7d60d5232cfd52548ca7e61952329f586548ca7e60952329f582548cb3f6455232d7d8d548ca7f61552329f185548ca7f60552329f181548cb3d5415232be980548caf96015232cf990548cb5d6315232db988548ca7e61152329f584548ca7e6015232de980548ca7a60152329f580548cb7960152329e580548cb3e54d0e32cf553438caee62d0e32bb58b438cb5d65d0e32d7d53438cb9e54d0e32d7553438cb9d54d0e32f398b438cadd62d0e32f358b438cade61d0e32b7583438cb3f5490e32cf152438cb3e5450e32cf551438caef6250e32bb189438cb3f5410e32cf150438cb9d4310e32b7594438cb5d6510e32e7990438cb5f5410e32e7d50438cb1f5410e32d7550438cb9c5410e32b7588438cade6110e32b7580438cb3e5490a32cf552428cade6390a32b758e428cb9c4390a32b7d8d428cadc6350a32cf950428cb3d5410a32b798c428cadd6310a32e710c428cbad4210a32bb597328cb6d65cca32db953328cb6c54cca32af993518cabd64d4632be983518caf960d4632ddd46518ca7e64946329f592518cb5f4394632d710e518cb6f32946329f982518ca7d60946329fd91518ca7c64546329fd81518ca7c6054632dd544518c
  | 27 => 0x429f58650d0a7f63543429f18d50d0a7f61543429f18550d0ade6314342b758c50d0b795014342d7d4e5390a7e6194e429f5865390a7e6094e429f5825390a7f6154e429f1855390a7f6054e429f1815390b5d5314e42be9805390af96014e42bb98a4390aed6290e42eb98a4390abd6290e42eb58a4390abd65d0a42cf5974290abe63d0a42af9874290abd60d0a42bb5974290b6d65d0a42db94f4290ade63d4642b758f5190afa60d4642be5835190b7751946429f98e5190a7d6394642cf90e5190b6f42946429f9825190a7d60946429fd8d5190a7c63546429fd815190a7c6054642dd5445190b7b50942429f98e5090a7d63942429f9865090a7d61942429fd8d5090a7c6354242cf90d5090b6f42542429fd855090a7c6154242b798c5090add6314242de5405090a7e61d4d429f5875350a7e60d4d429f5835350b5f64d4d42d7d8b5350b5d62d4d42d7d875350b5e61d4d42d75875350b5c61d4d42d7d835350b5e60d4d42d75835350b5c60d4d42d7d4e5350b5d5314d429f9845350a7d6114d429f9805350a7d6014d42b79945350b5e6514d42d7d905350b5f6214d42d75085350b5f6114d42d79845350b5d6114d42d71845350b5f6014d42d79805350b5d6014d42d71805350b5c53d0d42d7d4e4350b5c5390d42bb98a4350aed6290d42bbd894350aec6250d42d7d4f4250b5c53d0942f3d4f4250b6c53d0942f314f4250b4c53d0942d7d4e4250b5c5390942e7d4e4250b3c5390942e714e4250b1c5390942ebd4a4250b5f53d4542d714f5150a7e63d45429f58f5150a7e60d45429f5835150ade6394542b758e5150b5f5394542d714e5150b775194542b7d8d5150adc6354542d7d4d5150b5c5354542bed815150af86054542d7d4c5150b5c5314542dd5445150a7e63145429f58c5150b6f4214542cf9085150a7e60145429f5805150b5f53d4142d714f5050a7e63d41429f58f5050b6f42d4142cf90b5050a7e61d41429f5875050ade6394142b758e5050b5f5394142d714e5050b7b5094142b7d8d5050adc6354142d7d4d5050b5c5354142bdd855050af46154142d7d4c5050b5c5314142de5405050a7e63141429f58c5050a7e61141429f5845050afa60d4c42be5835310b5f5394c429f9865310a7d6194c429f9825310a7d6094c42db1895310a7f6154c429f1855310a7f6054c429f1815310b5d5314c42d794f4310b5d53d0c42bb98b4310aed62d0c429f5964310abd6590c42cf5964310abe6390c42cf54e4310baf6290c42af58a4310bac6290c42af9864310abd6090c429fd954310aef6250c42bb9884310aed6210c42eb9884310abd6210c42eb5884310aad6210c42cf90e5210b3c4394842af98f4210abe61d0842af5834210abd6490842cf9524210aed6490842ab5924210b6e5490842eb9524210aee6
  | 28 => 0x5000c00100000010000004000000000000070000001000c00c0008001000000200080010018001001000200000000000007000000500040030004000000000000000040000002001800000300000000001000800000040050014000000000000000010010000001000500080010000002000000200040000000007002400200080000024008000000900000000004000000800300040000024000002800000100010008001005c0040000001002000a0018002002000100180060010000000c0010000000000c002000000500080060038002000400a000c000000400300000040004008001000c0018001001c0020000000000c0030000008000000100200030018014000400300000020004000002800000000090008001000000000080020010002000000200040010000000004800000000000000000001000100000010000013000000000200010014001000800000340040020007000c0080000001000000100080000018002002000000040050004002000c002000c009000c00000040060010009000000500080010000003000000400040020000000002801900080040004001000400200040000000000000c00100080040014000000c002000000300040050004001000000300100000008000000400100000000014000000000200000020008000000000100000020008004000400900080010000002003800300040000004007000400000000060000001002c00500040010000001000000100040000030001000800100040040000003000800100100000004001000400100080080010000000400000100160050003000c00700140000000006000000a0014004001800100040050010001003c00000000000020001000000000040110000000000400100080010028000002000f000400b0008003003c00600040030048000001800000000010008000000000d000400100040120008002000400500000020028000000400a00140000004003000000300000010000013001c00400000000014003000000600040000008007000c001000c00000180000004000000000000300030000000001000100200000004004000c00300000080000000000400100080000000007000000a00580010000007001400500000020000007007000900a00010000008001400100940000010008000c003000000400000040000003000000000300030004000d7d4e53d0a7e6194f429f58653d0a7e6094f429f58253d0a7f6154f429f18553d0a7f6054f429f18153d0b5d5314f42be98053d0af96014f42bb98b43d0aed62d0f42b798f51d0add63d4742be98351d0af960d4742ddd4651d0a7e63947429f58e51d0a7e60947429f58251d0a7f63547429f18d51d0a7f60547429f18151d0b755114742ded4250d0a7e63943429f58e50d0a7e61943
  | 29 => 0x800000000020034003000c00000040000018003001000200000020010000004400000000020018011001c003004800000000060010002000000100240000004000000c0060000008000c000003000400080090018000000400200040100004000000c00000000010000000000400000040030000007000800b001c00000000110004010000000000100000000002001400100040030048002002c0010010000000c003000000100040030000005000400300080050010005000001400000000040000000c0020000001000000000080020048004000402200400000034001000000200000120000006000000300100050000000001c00300180000000000004c00000080020004000000c000000000300340130000004000400100080060000000001000100040050000000000c000001c000008c000001401300100040008003000800800200070000005001c00c000800600000000018003000400000540040000000001800c0000009000000a000402000140010014000001800200140090008005000800000000040008000002c0020000000000c001001400d000000800000050004000000c0030000000000000c001000700240000000000000000400080050070009000400400040000000001001000000000000008002005000000080000000000006800300180000000001000400100000000000001000c006000c00200000030008001000801900000010000000001400000080020000000000400200040020000000000c00000080050004006000800000040080004003000000a000400400140030050001000c000000c00200000090000004000000100080000000000000c00400040010004001000000000000000018002000400700380010010000000800300180020000001001c001000c000000000100080000014001001c0090008000000800000080090004007000000300000040034000000000000000090014004000000100100000020000000000e00000010050013005c00000440000004000002000000040140008000000000200180000024001000800200000000008001000000000480000038000001400000000030018000004000000140010004006000000000040100014001002000a001c00100280020010000000c00000000000044001000000200080010000007000400600000060008001000400000000060010007000800600000120068001000800100040010000000001c0010000003000000100180030008000000c004000000e00040050010002000c00c00040030000001002c00b00000010000000000000e00000060014000000000d000400000280030000004002400200000020000000000c0010000008000000000480000048003002400d000000000100040008000001800100000000004001003c
  | 30 => 0x12002000d00000000010000000000000040010064000000000200040000004000000000600140000000000002c001000000200180010000002000400300040000000000000c00300040000000001000000000040000000007005000200040050000000005400400580040010000000000200000010000001002000700140000000002000000000000000008001000000100040060004007002000000000040028000000c009000400000140030004000001000100000000000003000400200000050004003000c003000000000000020058000001000000000000018002000000800040030004002002400200000020004000000c00100000000064003000c0000000000000000100040010024000000c00500000000000007000c0010004009000800500080000018000000c001000000000240000010001000000000200040014002000400000000020000000000400000000040024001000000000000010004000000800500080020010009002c000000000400040000018001000000a000c00900080010000000000000400040010004000000400d00000000028001000400000040040000005001c001000800000000030000005000c006000000300000060000006001000c0000001002c0100004000000800100180060004008000c002001c00000040000000000000000400080080000001000400e001002200040000000007000400100100060004000002400700140100000008000000500200110010000000c001004800200080160000004002400b000000100080040018000000800200300010010000000801a000800b00080010004000000000000080050000000000400f000000200000010000010005c0050008000000000100040040008003000c0030000005000400000040000014002001400000000010000007000c0000000000000401e000400200040010040003000000000040000000009000400b001800300100000018001003800000040080008000002c002000c0010000000000000600040000000008001c01e00080010000001000c0030008007001c014000800100000030008003001400000080020010005000400000400000000000000400a00280020004001000400000040010000000000000700180030008000000000b001401200280000000000001400100000020020000000c004000000000140000000000000000500000000008003001000300000000008000000c0000008002000000e000000000300010008000001c00400300010004002000000600080020020000001800a0004002000000400040080010008002400000080010014002000400100140020008000000000c000000100000000000000000000200200000000014000000000000000004001000c002000000100180000018001000c003
  | 31 => 0x2000400f000000000040000014002001000300340090004000000c00b001400200200050000004000c001000000800040000004003001800100000030014001001400000140010030001000800000040000000001000c000001000100080000000000001800200000050018002001000a00180010004001000000100080080000000000000100000030034001000800000040020000000000000000200010004002000800300080040014001002400b001000700040000000005000000100000020014000001c000000400100080000004000000800200040050000001000001600040000004003000c006000000e00000010008007003401700000010018001001800f0008000000c008001c000000000100000000000005000000d000c000000000500000000014000000400c001400f00000090000000000000000000010000000000000400040060000002001400300080000030001001800000340030030000001c00000000000000000001c00100080000078005000c0000008003000400400100080010000000c0020010000002c00000000050004003000c001000400400200040004000000c0030000002000000100000000010007001800000000040000002000400f000c000002000000040020000004000000c001000a00040190004002000400500440020000005000000000240010018003000c00100040000010000000400000140030000000002000400080020000002000800400040000000000000000000000010000000000c00000140000010004001000f002800000000070008005000000c0008000001000000040000018003001000100540000010004000000000000050000011000400000000000010001000c004003c000003c005000000e0020004000c0000004004001400100040010004005001800700000000010000000400400000020020006003c0140014001000801700040020000000000000100180020000000000400200180000000003000400300140000004003000800200100010000001000000000000040000003000000d000c007002400000040000000006000000000140020008001000000400280160000000001800400140080004000000800500040190000000000000000280000000000002c001000000100040020020003000c00000000050000001001400000240040000002000400000000020008005000000000000070008000000400000080000018003000000000000040004000000000000040010000001000800100000000000000000c000000000b000c01700000020000001000c0010060011002000000080000004005000000200080020008000000c004001800100080040028002000000a0000005000001f00340010004002000800000000070000001002c00400040000000002001
  | 32 => 0x958969e0000d4e00007f40001d6a000000000000000001ac62e6ae6c00001e600000003e440000000000018a0aa000000000000004ff282e1199bd009180000000f2e30290a1367896621f0000699918e3492c6458f28b221dd6768a5040000000000b3c000000000000000008495f805cf00002a08bb2ae8c20e000195a0000000000000092cc0001c540008fb000000025c24dc00000000000000000000000004d0217ab1e0000000000000017165d4c24b0001176000251a558a79a553812685200000b29a708081163bbf47785350747000176c928223c93109340001d9a72005266649b4c71f10f300004803248000163400000080636ae4000833000000000002119dac12c15a00000000000226600000000002357312cc5d000000000000005ed800094880000000000000236e000000000000000000aee00024b8000198e000188e000153d948033b0000ed000029740001a2d00000002f18000000170700000007be00007fc8faf1fe800017a94b0a2c400000028253a417d820aaea80000f9e971ad2000016441b011de3c62f1c9d116f8000058e7758000000000000000009b60f4020c819c586a1ac23c1f74843140a54a8d80000246600000000000000000000000021de2c0c0000556e0e1e70ce034189fc000000000000000000000000297e00001ab00026367550000000000000027b90768f3200014f42c02992bc900005e20286000001e79a973185166223318a877b78003000000400000000000000001800100b000500000000050001000000000080040014001000c00200040020014002001c00200000020000001003c00000100020000000000000100040030000002000800100140040004008000400200080000000011000000600080000004001002400000200000020006000c00200080000008004006c0010000002000001a0004002000400c0000001000800200200080000000000c000000000300140070000003005c00500080120004001000000100040000000005000c001000000100040050000002002000c001c0030000002002c00000000050000000000400900080000038005003000e000c006001000c000400000080020004008000000500040030000000000000a000000c0004015001c00100000010024001000400000300030008002000000200000080048000000000200000020008007001c003002400200000090010003004000000140000000001000400200040080028000000c0120000000001400500040110018001000c00800000020000001000000b000800000000230010002002c00900140000000000001000300000040000002003000000040020008000000802000100000014000007c001000000100400010010005000c00c0018002000000000380000000015001c007000800
  | 33 => 0x200000000e90000155033e9700000976849e00000008349042a1428490f5e85c348eb3e2f50000bac1dc4000250819300000001a8b373800003f0000000000039782b205416640001d412f884ba00023221cd8700000000000000000000000ada0000000000000000000002b3200000bb06f80000000922000000000295ce000000000000004ee1d5300000003be073982c800000004e91a4c00055722104d58c720f1504b000029e46310d00000000000060a90f800000000006c3a61400000000000345b5f8000000000075d05b655e80008059a5e000228b00000000000ccc68c800000000000002ddc9bd43729ff04d7000006600000008a49fe60000000a982b4e4c780004be2bde34800000000000ad900000101d636e8c000760c0002c82df85f44000925a1d40000000000000000000003e2e9e222300002c700000000c0600005ca0002eb277f4df44211d5921a02bb5f02cc49ee29301ba13fa04b8ceea27818ead689988cd4b4a1320698a3f00000002c3a0002b0617513a8bb5ab22b8219840cc0000000135e667800000011c82ff0cd800002ab6b72bfc070e39e000000000008c67bf000000017a0000122b00014d271781f3000000090826105518000000117e000000000011890001c2c9e52ca23098000000153800021420000d644de400000000009fe17bc3ed584c5eb06440001d753b5c00000020a0aa81656060c00069505604f3c0003bb453d60d2c3b56492609999a3cb3c2da141b4e087ce00004e2000000019105580e673e99d282b2852c7da12ee45a11b25cd1bfe5068000000067c592dabf000000098597c4000015a122e2ba0000af3490e5d8b780814789800000000001474da657d9a3467c20720001cf50000000b1a000000028c897e0000000000000020ea78218fc000132ca611a6048d8000314193e2bd4000b5d4000000216800009ce326acaa8c9800000000009fc80000e153122908afe20121ba4860834352dfd076215756090bca5318db68629a2ab27800404f15da6f32e14aed148c000019076c80003751d8d81e00000002dc400000004fb257c0001bdab1ca69f000257869445c6841a88ca1f00001ac000003600000000000000000046e8000af884c0a06e9c431fc797b6d43126ada316b0f00000002256ae7163f736990c22ad7a116f91ca2272b136c88a04442800048310d82e1991e90519fd4c6a5e4a7382484b39ae72839a158e2845ea3140008302938b5ba1c42e3ca9600009f229b23640dc000069180000002609ac69bc848bc5523ee400063a97d4a5685f20001d8f2d48000361c840b4880dc00028240001d2fbab000050d8000000000097de3520e280005bb2a4761900003b500000000000000085e000000000007918b99d9454b5cc200017e80000a1400001740d30000000259300
  | 34 => 0x8b8207471301b858b9bc289500000000257000000001a2bc407889881d600003298e002b720a6a29800000000000002dea0000000000267a7511e340000000b858c7766d04f231395b136f0000000189e7b9823200019781508000070000000000002ba4514338d14e0001b4a32080005961ec21a81c944b80e7ab37902080a23982e5953a0002cecab615fc0000f0e60f8d684e265e3334800000025e842498ee8849dff000000000000004260000833892e93c9efd0001c080002ae63cf152e11c25563aa9b8520f20b7a8fda49ad2076a6231f0c8c4ab620ada4b61a20858aa10f023989d937b31a2c09a2db47c986f81a9956440c10003dee90e94c91300924a129878000087400017027f441ac00000008fe03300006552672ac6ca2856d9561228c30425dc5f33e9098a00000003619d0d0000dbd9c3919c0d71ce45838000998a688244219647f210f078d6a234880004250000b349ad000018c915f86ecb2190f0000000052f2550b399ce06dc85abbc200001e380000002e2e55ed410253289a7e3834d40840006be8000a21c9182ab8000bd8800066200000001402000286a000000000024da000000000000005d34000a968000000000059c6f300000000000192e0000848000048c3dfc00000000000001d6000005d021800000002282000000023b00002898000afa8c54971062840d004baeb02f404be9da0000309ae900008d5800000000000000f6c8ec8000436aaf40001a750000000000000000002ac00000000000000000000000000000000000000000028001c6aca426b5dd24240000681a0f80000000e45000180ab07604444f00000b38f22b048000a1300000000000034a8e1357800000002a4719191b00000008689ac400019e4000000023f0000b4e030c0000000487c0001a381860f52aa8156a2a0bc68000801800000022ee000000000000000000a34ba200009f4033800000004bec000827066c7574de013c461e0a2a2c2b9e06ba1a6dd1e82c2c6a00027b280da1d29992505000000076a6a6800000006dd000017bd20b2cb4ee99dc80007ea636c0000000870a8d600005ba0000000a960000994c4563ea47ac97a80000000fcc380a400abb84db23114f000000000e3400000024560002b2d0000000a6080002c1120842329f0a0218b60a605580e50ecfa82c000b0b88129ae0000ba080001274f6e6770000000064f820c0004828000680800063c044c0002dc83c80d53af981de92423886bc0be846a04c746f177a000000021984b905040000000000b91ab2c0000000000000035d825e5a81ed636592a6aa90ab6000128036682500d50445000000091e8000000000000000005b4ad4c9128000600400000017480002503000000069aa70100000004298000000054a5428000b3faa5e000061200021
  | 35 => 0x2b7a00013bc34a000079092640001dec0002d988fa68784cda1c6000000000000000000000a04d4422a8ae62000000000000000000a7d2bfdba0b4d27150cf0000bbaa804430a33c00011e800029b00001b7e0000000563aac0b2b037a9cc4000000031000000000002b82000000047c2338b2e0000bd50000817400089e25a300021322db887b000000083922500000f1c0000000000021c15c1e230001b3c3d1c00000000008601b56358a54c8f024ed5300000ad4800017900008910c3800000009af800013f029db79212260e28da8222a7e8d1823b0000000917a1940a71dc061f83776880f4a0000000b6fa1f84e0850c8a98b0822954ea000000000000000001ae2000156a00000000000000000091d0001614ba0000000000004ad14a80000000000036c7db80008e712e6000043cb4b00000c6000000006df0000c006fe000015b9c0f00e2b44b4c089a17c1faa00008b97f10b6417a2e703fb201e8170000000000013840000000000000000000017fa0000000afd0000000000000000000002b4a44196ea0000000a2a8000000000064e024ca2fdc8c0679bce71c8000000000000012517060ea619fc0006c722740f2677a89b2e3cb141fdc00000000000000b7c000000000000000fa8000000000004da29e2944a659b6281d85f70e31637ac640009e0109c00010e836a8000000000000000000000000238a8429c9001028600005d800000000c79a6680001e341607b61a8e47980000000000ac7043641d9cd60002630000173a0000000000101c25e0cd43500d117d398202f0eda895c0c877bba72600916c66ebaaa3000000000000000001eac91500006eea6bf000046723380004574000b629a2442900f9750842352d23485b116105721e6895299b81d0400000002d78a907b400024cc4391629a5a000078717b80000a3e92b4bad20f80001c49b79659aa2e96684ad6d4c00009500001388d568d318faa63186f1e20dca04080e554bc0000000975a6826ab00f14a200013c00001b1127780000001d1800000000000000000000024a00000b580000000000000245022e800000009ee0000000496851862ec00030808a60002980b4b9e4c261877a19e052435803ba394800000000000002f160000000000000000000000001f889c700000138000761c0006d80000a5ea0f6815ad7000000000000000000204000013c40000f0800003a2461a5ce0000cc2004c00000017980000b0d5f9000076f5e9a8cb80009db1aae93219d926080003f3580c16192a2542c00000000000e480005f595a488d04d200000006ea40000002ed70002228000221a90c90286879346b5d9e2c0da93d438e0916a7bc09a494290a00002fe0002c33000000014b400000000000000000000180489e800000000000000000b3d800055100000
  | 36 => 0x17860d9292e973c000681800000027ce00014520000000aac00001c6993a72728b39bf40000000b6c05d47c975880002bc275e00000000001dce000000000000006aa025556421f0000000000009c08d8a28e0851a1c90a0c40573e3900000000bbf9bc66e709500001b7800027a200000000002018ae48000307800000016fe3d98000a80211407f8c3c3f880000bc05030846bed0002b2800000002be5d1400013432bee864a390000000000016e400041a1a4200000008125a9762e800094b0563b9111c4000154a61c8000493a4125701090a88c000bd0000082f67c040ec00056f4b34a3b834446dad6ab5f0391494a12c2e10f5e0000b896560000000240c00006600000000000000077e800000013080001dc64488000000291a4f9292c1a4442e51917ce000000041d1ab200000000001306691c000291085076f27c223417d300000004bf400000000004d980000001dbe3974ac600020f000027ff78340000bb40000c080000000000a6e8f8a0001f1000002a000000009f9040c00380001fc950d0381c46b1286aaa361e8e2f58c8fa920ce9bc4951770c82fc4c5983c3eaec260000000b6c1be3548e1beac098588c954adb7d837ca0b1af52591d199f602243810bde2de87463ff2a1a9c3c64a0002366121556e000193cb97c000a6b14e6000254629607fc5a1230e000062c3184d797a880007aa80000002d46037ce5a70f15d026c8000000000000000007cb05069cad210000063aa58838e15dc000000203e8d10000000032631a4eb8bd2a6749ab400052ea57400004f60002a156be1bd90001c0411d40a000000000000000000000000027c10001d4e63a400000000000b91c82a2400006fca1955899b280000000ace02693621cb6538810c0000000af09cb4354800000024187fb20cfa340c6873e2b40817a6209570f26a4c991903402df9c5055b6529f8a4b000002ef91596e11a50271800000000008e10000aa2965097f000000000000000bb89ed8cf261a8000a5b8000039957f00024e40002b8e85e2f1051b2ba617240004a480000000f1aa3e8f0c5d703f48378000a8a1192000250449597f638e40000000000b9e98c813183cb8b396d008e000071fa23840885101db15c958e4ef22798d0876e0c1069f8216b8880ca406a582000000000015942bd916c07a6ee0000000000000000000000000000074a8000527800000000000000000000117a00022de0002e8e9508000000000038ba35e00000000000b020000000000000026e8000521800000000000000000000000062440000000000000000000000280001ceb0000000000000000000001071996a7900000000000145800000000008132320aae8fce00000000000000354000013f800010c6b42b258b3833c00009ae59c5ba906d49b8400000000000000
  | 37 => 0x253c544168a00001489438000b5600000ed0000098400000009f00002060000268600018c00000000000000043200000000ae800023be09f8000000242693240001520f728472f3cb03058763e039300004140000000a1500003ea8a68aba12d28810000bbe8000000010125d00001c30000b0a40007370000bad000000000004fd0000a2580003e0265655c83961ab41f19218a9e8438da456bc9423291679b6a400000000005858fc9738a1f7a699d89412800b3bf981ab020ba62990e329e409e402755e47655a191cfd5feb22021a1b586ef5aca28c666c6837220258000190e559800000000007e700000000000000054685880e900006082720000000250c0001d5242a27c68afa658000000000000007248d420001ee80000b600001f7600000009d3c00075c141600024460002e6e16c984916109b810c02420000000badc00000000000001cc80161e6e0000000000000000001aa550a24e2a9294e4b6800000000004f7958a00024d856cd2ae000122a0651d40000000000000000000000000000000013424880738000000034f00001a4862d9b8162a000013a0002880181af0633fa84705f874ea1d0ae456f274838624ba1c100002a10000b3e800078e400000011a400000009cfc0000000d320a083980001d240001faea4108cc6db9e604431eae49f00007999216438837b770ac9a88c094a0c59f5c0c18c7eb51149b366513600005833f4c00000024ca0002f4c000054b9cc2b0a000000000016630001a2e52da25e8690000a7e4b811c082d200000000001b5a0002c0e00024fc0001fd83b791d6762ab860000000000000014eeec45b898ac3ef000053c8000000128400014a41d158560000000000000000000003e4c0000002bf800015d17f2a3967919f982b40000000167e288a806b96423a000151f0000000000189c19c800000000000000000000000040e54f892c23f256a5e5e2fe051b4e82c940e3de14141c4588f48bf3b1d800005c8000000000022e0000000000046221e8000000048b25d68258dc831b0104a062d9539a9e00b0940001d8c777b7180000001354000277bb9da78dab6af0014f0140a4f800009b10b8aa7800054a000063a00006b280000000000000148081915489b7400036d000063900de5141e7a0350d7000013a400010862400000000052f58b19e960713e839416244d6800088500009dd80000001e4e3f28000000051c5b91db4000000024a4abeb11c000b65d2000000098873c88196e834200000009f980000001f8200021b000022f300000000000000ac7400096300008d81d5000000000071934390633401680009f489a6000206c1b793265ada70013815be0ee0dec000042299780007f78000832e49b9e91fd68c4000010a800000000000002dca06ea0949ea00007a20000
  | 38 => 0x13a382909d60b6800000004e1800067e800065c80009a84a2a4dec0000001800786155002cc59a1df8bf60d6105f68a64aaaa70000957a94800026f43d19255a718a2030690ae43d800020790bc0000000254800071600006cb897644d000094480002c901738421ee400007c5b47047e41bce680000972000000000000000000000263a6a00002d0400018150000000a450000b1215d2af02b8ca85cf1197fa9c76ad0e5c1ec2efc00000000000cac0000c73243000015e9b2ca561d130178e4b3ba00001be84123660e0600000004889e3c8c0850f0000000000000000000000000e724da595fa5080000001d8c0811eda6d7196439109e83b9197a2e2c000000180e5c380a600000007d429ea8d29f7c08b80008f6000067b1c6600000000002703000014e00000009c757d000000000001b10638164cad0ed10b6e4000416c000396000082121e210bcfe12001ec46740c931f6821e67f2eae73d82f924226cab841e966851fe02c4838629328920279f36790c0000d793ae82b2b94b001b6c764a0fe860a1503d92f2e1b1957071e25a18ddc7d85e000002f564944ed97f800028ea303133f92d1d102772c5630b19be11e8000681c00088c8000bd10c434dc82b916a623600000009c4c79000027020000000000000075a06ea00018aab3d000000019767e500005a0c00000000009d698942ed40007a8000077c80001209150630800037085f800000000000000000000000000000428000000232ab300ad8a879114000108e000000000000000002c280001ac80002c8c22a800095980004aa88260126a7a4c000000000cba059a2760ca29aa7a18d8e9a782f8ae80f3a0001c541a1af2aa9080007fe89f816a997404fe9f41b0902a594880c3ed827c34d00005b72061498c000a7153ba54e6513000000000015de0000000b3a00001648000097c0002758000523a5f6b7328cc26f150633b0000000000074b2a46966000047ea02624503d5000007f26a0000a10093ea47897c0001d1100009ca00018a68598000103c0007d321cd0001e7e012ab740000fbb0001e3575a42a10c51cd8165279c4198c6a00003e500000005f7a38245b8e1218700e409d211a0001f02b109c6a00000006860a3600009ae00014ae00000000000000000247c00011aea9c000000009600000000183d37425e837d757c05680b0c3d85c8008187d76e0000402000000000000008ba000000010fe00000000000d1c00000007804000000000043ca74e00004d84cc229a527123a000281a41e0000419c00000000009ce65ad8d4c0000002c1e57a1eb300000003fd95e200010e000007b300000000000000b696c228f7db82910061a00000009ca80001b300008318ec420716ba8f3c0002a6000091311a69af5bb8bce841d0d59d8434ac000a8a9d5c5cc2770acf
  | 39 => 0x25e200000000002e8c1308a4b5f34e200001a74000000020340000000000411e9d30000a9a10115a2000000000000005762a5b37c02c849194d02b00000a558000000000037680000000f42159000038c03e87a414820002c2f26f400000000000002894315c00000021367e80d3a000000056a000000013be0f0e41e56fcf7600006394640000132d408acd4ac80b89dde000000058ed0d5000115abbd8000ac326de0000000000135300024ea23c88bf0001b160000000000134a70a000075f4000b9d0cdf00000000002ec8000233e6916f58000261c00000000461b7a000294c24c66b00001178000000000000090000000bbb80baa3d2bd805d913a2a80000ab3951e00026e81288000413487e0002cb4000047446f9f0649ce80098caef933ae844000149ab9a9640ad4253a0a48a1a7ba951a241070e1e898bc574e738b962303ad984beb70085489807530000f31000000012620d4a9a9dcd000132496b0015b799456178802a0000000000115c1b61fee000000000001158048ae700000004408af19279efea2d02344022d06000000047ba65a36805ee29827ec6d02ca69cd915f00000000000000000000000000003b597e9000129688591e22b883520000000000000038f412c0c15778000103e0002cb69f4c6221fa1854000000029180000001fda00000000000f510000000000000000000009bdc000a1f8000000000000000003de96f0b172c1f4e300000002e5400000000000000000207c37bcf0600000009352188b89225a3d412e22669c340000000798ad940001ddf2c04000b82800000005a217b27500000000000000057ec00018d4000b382d78b55aef411526f67614000000000091ba78eb370f3078190dcaef1e0cac42652000111a7430aa600010ee30c000055a0000a2ee24825726e72244000968ad1e00000005ff0000000000025b0000000000000000008ff916000001d04ffa11104c89207d22920073d6a86ec047c578c000448068b4ce9c3868f8b7b8908000792280a853800000000008069e5937e8000952000013e00000000000a4900001e2a2b8129d27a48b4a8c00000000002a2228b40003a100007daa2f60000000a892dac755ce4041bac9c1252a279a4a35400010ea0002cd400018f7000000000000000f32737000000004f90ca34520a21239146a0a9fea6f8a0bf00029a40000eef6dc18dc00009486a31e2400020e000021a70000000000000091c800084e87400eb8dd01d8025254d87747db0000744a01c9cf800071b031e98100006ad4000000000031e800005a9afe62b8a489b5c0e830fc4ac8d2c1d10002ef791600003bf0504743cf34a6f800041c00000998000045eca00000000a4e8134290000000000000000000b1440004baa08d3a18000584a85e2258000086dcbc1f7226274ca4a
  | 40 => 0x78adbbc0000000a0d8a0c0000000b5880000000f2c00009b458780009cb02eb000000000000003f9126c0000000579cb587d681a61a88000967c000b738000000196a000000000000003ef493200000fe58f9ae80000000000000000000006719822370000073ca7623870e470000fcb64716f212919004439a76000221e0000442050c0005e51044b7ea698000000014c1c500e680001dba2bc8bfa0b400013f0601800000000004d605a0000221800019aa23a0c5631d9f622f9000005b8cce0000000000000000017e09bc8d2569869b640f00000001e3e338800000000006842b544f2a3f02b50d8417685b4a4605b700000000000000000221c2c4003000029f80000000000000000000000001d3c682400000009920000000a4f0000ae602220001320000140400021d69440000000000000000000000000a228764134000071289fe00001a4194074ab6e9d3700027bb000000000026d613ac0001a900000000000404a9819379fa400000000058000000031100016b80000d0e0002c6e000000000020ca8b227840000000b68d0500000d1e00000000001af200007ee67ec5b800027ae6fb008c7bd83ce0001d4800004d9543000080b95cc0000000357c0000000000a8f1b52000260700024a600012740001d6d63d01ce00026fc00012d400000000cca10b08d80003ab000000015c3000192c293c00019926ec7a6c00000024ef11a235cbd206480000000000000000008be000000000000000002c045198000000120456ba51c00000000000000000000000000000000000000000000009aa168694abd90a060000c8600011b40000000418000078a9c9a14a00002cf40000001638a8200000000000a870000000000000007a7000000003d8000000000000000005579ba8000000091d8ab2000000007e81f98db68ec05712c4a5485d61d6a7063fba4cb5f24996bc81f348b585a69b38fea74e064620e978400007625fb000000000002a00776aba80009040387b8300002d429083d105364bcc0d79a71c0e00000460001ca09220bd028b83de0002c2b0002abc2ba800018f5eb80002d8200029cd00013144040e3690f1032b948732bc79376171e5686fb8388199ad420000000000000000000000e8c00061c111852598d80000f1000019c208e4000a0700000000000131000000021744f30000223e79329fe442000275f31b603243300008ee807c000032400002e06728b304bc09b698b8000483800070f800060240000000000000215c8228000bb61a4b5d32cfc0af286e67527fe8d0800002580005e7c000bcb2d086a71c2430f96608118cca4c30a758bb0c140e99527963aea28291ba47752f4f0edaa31795814217225f58de20b886b80006780752497966e00
  | 41 => 0x8617c8a2b5abb1676b161b6526978c9a941bd8d100000000617043800029940001baaa498000000000011180009da00000000000000000000000003b98000ba709d100022c0b68a5aa0000e7e694c360967a6ea7b88192739cf2b0ba139a08340004300bc0b09d55a000000050388440001f4659a0000a381e0984d1d5e4da8ec629d872213519b11ab96329a750527149a3078286f08f82df2280a516a731ebe89a10363a31c1eadec0beb2b911c0a01ff8000067bb12c2109348aec2f3d1543ee27ba2ea800072a80000dd40000000000000000000027520000eb6000000000000000000000000000000000002b3000000000001fb000000000000000f007b52bec6618789364000000000000000b548fd9816479000000006898f91d34813800003b0000000169200000007d29cbe627d9605b012a88668d6646b16c2000200038388806ce2cd600000005168000b2f80000002e2a00019d817f96be60c99a446807651944000030070aa8996a49beabe04029b7b78fd79ea77000073f5f222a4232c00017db000000000000001c18582352a474a7a00000002adc000187a0002e8a2de58f5000048d0654d1a04800005d900007a611cc0000000842aa800000dee5a0a86300019521cf800045c800000018bd000000012a4000613800000000000e700007f500000001ce1a05800000007132e447c4000170800009c40000000138c0000a0c00000022f4000000000000000000cdc000000053b266c0001267087d8ff85466062948c5e73b2aac560267000014308fe8000b1c1d2e72e058017f526e000073d15d80000000b424b95504021000000000004a726120002a108cca498ab780002fc27e09a525a87562d022fbab9e8f1ad80b690fc01fd800000000009bb80003ca4000880800000008bc000246a21e95dda31a31e1d7000071b947041c41807088f9b24c03aa0000c780000000000096800000000000000734068fb9a000000004ae47019f60000000000000000001d200000000002ece63bdb3276180006e20d47000000007280000002ac4582946eb668f95a8480000000b0fac3800000000000000fb2ad72284a5c11f403187999e809894b1966ba04ab6c195ee4a00018748f5445bab403d0000252e2510f255d69f421e9220a29f24d60002a64000000000000000b000003771772000000069f148841b1ddc0001c909d280005d8834a1d11c5c0002b6e683800000000002b800000000000650800071580002708000000067a54587ea9a9129000000000000000a21886e328845c219000000000000002d9f8ad1dd88f7000000029cb0000e4360e8e960002608000210d400957ea2b80000002ba10002c2a17c40000002a070001df0aea12820000b1a000000000029b40000000000000048bab8700000002fc97c6ba504cc00000
  | 42 => 0x3942b399611a1000000005401960502a925a6c000000000019705f1c0000001ed00000bbc41e80007cf8000316190608fab849268cb66f9a723b674a701d5982aab480424399bb41489338237107c1e0284a5c8868c73baa900000c94b2925fbb94227c3eb4a5d0000000a04551c14800000001a5a45a80000000f6855f0000000143e32c2222819979370ba6fe46087305171cc65499da8730000000000006c81d3a53120900001ae3753270b47396499cb400094da6d486a8000b53800014004b4000056a000000047d938e460214682ced52a7cda367f91802533a4a4569a9664cc8bfe4c712f223580000002b3f325c05f0000de49f70000000064d000000092ba6dc6450dcf0d38000000175030100008b4a329000155f00003470000fc8143400067fc000159800030481f600000005c09cac89840004f822a800000003ca0000314800035dc30b14b884c7661d4a1101f9a0d99ca600028c2065970072892e83e683e2112a04db439bc74590f588441bf72d99eb2aedaabe6b041623efa04a0000000000000006a11420000000000000000021289a9c0007fa1608000000004c00000000c7000029d90000000bd680001d216d4000000000000000000000867800000000006a8c00000006b48dc4000143800000002788ca016c000000000000000001fc095b80000fc0000000000000000008c65c36000290242820e87040000000000036ea7880469b0814d11d8a3247c20000902000000087c8000b26433474c00000000000000000072e800000007c06a78000000005400000005c140000001f140001b4800026d500024c60001c3a0002c137638000738c0008e8800000019620000b1818526f3b4e8000000000000006e400004782dda3ef00000009b414f63ac000097200000002a623b600009f78000000065e000000000000000000000bbe0dfc00006001709704057943c268064986f03d898613d080eadda3daa22c3e34ec803108a99b356466712123974ae2664587b5813e6b5378ad7290e003e0002c1634f80009212124a4d00004d9c00054fe85ab3324a26f92ede713952500002c20001e50b3913a250d04970000000acdc000000000093ac114930a9ee8a18000111cc2872c2e3696c9f2e98d07d282057667bc8000000000000024c748c00006cd2c6677e000002b216a29540000000000822d0590000000246c00066b000000000005c7000035d080f63793c603bcc6022b4f822300e102249e1e0000f9286300004898000a2da798000244e9fd8237a0c80000001f24769a36abb9aa740001876b20000000028ac9e3000000000000f1a0da000000006c000000017dd4bfa17e4a928dc00021b626fc4d61c580000001ba7000000022400005974000000214a2524000b5d00006a4400040b14d87e3000642d248e8a2ad125
  | 43 => 0x15df00000005df8000000000000000000000000000243a5b6126200010d6000000000025df56e186257a40006202d929b0197e0000786a9160759ed57109675432657a41c98a003a27b1e22000072e01d07a80002a67a4d80008ff0000189c0002b9a0a70001a4c00001e45e718b487a800000000005ad135f316e46883083fa00000000000000000000000000000a523e200026b40000000591400073340006e3ae0200000000c0e17c4a686ce00011a200000006a100000002c104b70000b7f80f00001f72189a22e6d99dba24499da340aeec5e323d48f79680892822a052a9fabc2800000022ea6d04a743cd800044a800000000008b50000000000098988308eaa5f010a000066c000000000000000000000287242d800000000000ae1d36000296c00000000000000000000051daa2d00000000000000000000000024e2649a402000130a00000000002f5e0272dfc5799556af4ad60b110de634d82c14749116a2209a2618db5b00026551414000000010e000000000000006662a7300000000ad6c624258b2eba191c65728000079400f89000001ac5e8a19e649c40b63b40000ca06275e546d416e65a19cce6641bb28839d664be89cc6a580000000000000000013c2374aa5069a0000ab800026c100018469ef69c12cb26cc064ed910002f34413283175f2e426468000000054e5aa9a561e4ed930001f1e7ce800030625969a100bc649055e9d080325c49bbe000037e0a051042dc52c200022720001f2a000000094040000000000afc81cc51185de9b68be600023d0879875400000007e79d2200000000000000ae6813114ac0148388000a7461dc0a59e7228ca9d2249436864082ef78e06bea3497eb0f98e2a00000005c800002e9c00007200006a48000000016800000001d9800000000000002722a8f800092ac00000023302d10e821839fb25f9800000003c417640001628d2c0001d3f23d000000000000000000000150e95a80006668000ac780000000b800000000456c81003203c20620000759e79f0000000b54124a972c0001c70d92ac900004d40000000000091201169019a9082c528e000000000000b1042d9a533fc108226054fade0f2a0f71a78aa8a3e800001ea4a500006121694000291c0000000000000094280000000e3b00009f4000000010200000001f669e980006b7800000000000000ab400000000000000869800004e143a00000000f3584f000000000000000000af71574000ad780000000000b86800013900008c0405cb8e17be7f3000099b80000001128075aa5047fa6484120ca52d00d7288eaa5c41915c2a0a1792b90115845100009400c8c0001a4a95c8000000000000000000002e060000000000124500000009799d06872a0f23e9c00000019d293a19a00001fc20001e4400022d80001
  | 44 => 0xc0002f72ed400015593be8202b8e95535e393186c30d7e988c4ce4a8000068e8000267a2ae000000000000002490a1c8dc8e6520b00008c9000000025d0205a77e7238c02000000000012ef5f64000000000000019f445a400000023940001a680000000af1a3d7000049000000000fb800056ac0000000000000000028e00001ed80007b80a2b11a6dee2329212bc3800000000006b4ad8449f8000972800077d88060e0268c000298a9e7a3f83e844b61c80000393400000024b58f1000002a0bfaa15629e84f27ac78840000002bee3221860000089765a0bc112117d2aff800068982304df00001b6800000000000000000000000011240000000000000000049da5343e59c0c841000062c2ac60002d9b267c05db0627569f318521061a1730eade25019e4093da6ae2b090462e50d6ba4a921b274848796f0bab25c24fd40b803160c2c144a2800015c637e3dfa0ec2470d460000630a5fc0000000000000000000018a00000000a0d11946bb80006b840f48f5a5a000000000002a8e00000000bcc000298505a7c594623535d4600000000000ee5000181233ea74d000108f0000ca800000000000000000299e1eb6cb28cdcedcbbfe7545c198d200019402a18000000000000000000001d5600000000002da00000000000117c084800001c86a8093a2f89745e9c011092a52f9eb60000e1a0001b26000000074383cf3a50000000000000000009c5889e000159c6184e780001a5b0002c9800008b282a1fa20002077555c000a582a0200008a242f400068a06ac0001bdc8d0164851615cb3020b06bb00a6e0001b5e4339a642a4566fac4561c00010fa0001a370001cf41b21c420668434b7a21e49c29e4a65703a883e142e2ec2f048162d2aaf7288eb0fea0aa819fbc7bc15c53a695ee821a6549779ab06482819676d8904ac97ae58d03f27ca0cc08fb9c020001b8a9f8800047b163d000000003e800000000007a129400002bd40000000000000000000000b640000000284249c0000000000000090600000006d900003072b3b2928000229058500000000001b580000b5c0000000065c7be1220000000000000000000000000b978000a95aa6e7bb139c36a13c3000000031700000000f1651100000000047aae20fc00000000b61a489dbc07e79e248c2f6a069000198cb8a19ea294189a4ea94995562aecb1800005ab2db2b23a2d0000039e8bf05ae0000264000170a00022cc66e63c2815c00000000001d32a9219f445963f40008721ece00000000000000000000000000000000000b52000000000000002717480866e000000028c1688b6de0047c6800070480004c12f3e000000000000004770d5c6a8a9e00000000000128b00003b20002f280000000b2080c260524032dd063e55482f200000523322a190000000274c000
  | 45 => 0x7efa3da59980000000f941258ce57d100000000000a6baae01808782759400000025a50000bb40000000000199400000005612164000074300000000000c6e81e800054c00004bf0c8d1d7c000166c61100000003a7a4f033f4000765800066c80000001cdf00000000000a6700002720000c8100000008109b96000000080a82ec004400073a9e206228f030000cb8000000000018440000ffe0001e0e24980006788000a571e82abf80000000e26068ab889e580000000c991780eda00000002e3000000010f8000238638598e744e00003a9000000000002c7930775bc0004a199ccbc0aecc0eb05cc0000000000198d0002eaa0000e0a4f5a480000211d21080001670200489000013280006a61d0937ac00086a0000aa1826210180000000000abe97d52d22b768ec03460000fd100002be1e2eb7e82ea8302858d5a21380b90001cfa000000000000000000d123379b1e0001e76b67000024bc000b36010600008a000023270000000000001a00007927682ceaade40000000000a2dc00000021ec0001781aaaae2002206d09295e1d00015b28b9000048c80004f9a7e80000000a138000103ab08208921d33d067e5130bcc7799d6e2e8168e6c002a20002a4e000013301914944d700004fb8958000112637d800002d0000243a08233f00000000000000000000000007a920f37ed00009f2aee80000000000205f4490382b3ca0d03b9da4db975f08b2a262a185800000000004826a4b8bc8000867000013b10800001d9e3a200001eaa946000132845480008cada8905f14d667440000002f32a2bcec03ee80000000d300001600000000000017df29f9cd96a2092c92c8ecd34b8aa863400000001dd2b014d0103c80000001de000014eea3a2e60000000007b800091800001a1cf5a8dac000b0c19a7a149da562c8000210d2ba5da9aac51c84aa794862b000000000000006d866240001398285d63035e90ac371928c034dae400014dc54d088e4fc82260001c600002d3c000000000000000000000bafa78b00000003a28000000017a7f18000614682600001641ef0000b0f4000000000000000000000000000039f90b80000000000000000000000000000000314cd78000199900000000000fe6a74100c99a1808000117033a136e17d169000300001cf000000025f401e000000025520002a30b6b83d100020f41c2185b59089e081511b800000009ef800033d800093b2b340000b3c98b0f86ad040925a583ea8d3c638611c000403ac3e000057500010d4195069f695c000b13800079900007c800004884000928c37fa300f540000000000000017980000002bf00000000000000000000005a30000000219057c24c3bd800000000b3a461c000000000089ba09ea66280c7ee1e92a8528f8653802e37595e0aec8eeb512200c397
  | 46 => 0x72a1c98b9c982975e4f60000a700000164000001300008dd877000029c8000000000000000001bd800027cd000000000003a00002f2294c2b1482b973857100000000000000000071200006290ebd4b307100002d400000000000287a0000000000225233e16cc000124800000000001728a311fe2962800000000003bd62aa3b3191800021d0082000000000005390e2884480000000ece4f480000000000000000000026c200000006fd00004c0a704ac840008700000487800018352ac3a80000434c00017d53f60000820a9c40000002cce0002c06a05ef0c22c10ec0cb01036bd121a00018421e6000000000000002b46b18c000000106a000000094f80005a700004528e9c64cad66020ab6000013c2437800000018e24400000104165ea12cd31000267c3340000096800044fab7262090aa000000033a800003ac00000000000000000598800051f800000028662d380000002200000000013eadb3000249d00000000000dbe6410000b69c0007b20000000000000000001e8c0000002bca00bd92243240000001a5d0001f6400000000000a5a000000076c000036c1754b622c397ed888200000007348f980000000b06a9c31630b999a3a5bebb7000000004648f3aad668ee2b2368800000003ec711006a9cf0946ba7642cb1d2aa600007cd269000000000dd000000000000350442d390001a39000000050800003ae8f520000000000200a37c80008039eb417d800000000000c7c00000000000002cc8b4f800030b8000000000060b0000a2e252700000000e04000000000073cc000000030836840000001e3634dddae689d79a9ab0ade46a94ca53fa6ff60b80000c80f79000000079d445a84c04f3000019980924340001fa60002be800016da0001aa6000060902f5cde0000aba0de000000027fa00001ae2fd078c7a4c0002351b0400015dc00000008580000000000067c937516f00003aa0000000000000004dd00027aa0000000000000000029ecbb2830706b6d6400025584589ab87590000353dce86ec40000000e60ac988c88142d6881babe46858000000000027600f8b6d800000013052478ab0053082e533123e6d180002e38e7468213ce3fc9ca8a7c9be03f71dfc73982e694993b200000000000000082cc36a37ae9218dc000a90d6fc8e69bd6b461aa4462a815b971f5809ba74c12540003f3d69a94a8fa00002b258b18e4cb968d0a13aa27065b0c907af004500018400980f04b63af5c82680d694e00000001a994d80f5666294289cd48ee4c4183638b036f784884a00000004bd80008458000000000000000000000b7014e0000000000072903fc7b0217f246aa200000000000064eaec0c5aa0e06683e400000002d37ba599de00000001cecafc0f1c0001a5c00000001b1000000000029d80001a65000000
  | 47 => 0xee216e782000000057e80002bd286000000000002ad306beec675b1e0f85515d60de529854b16bc7279a62a1896fab2f000061a0e3f7dfa1eeac10000000000000000000000000000049c6f1000038300000000000663cdfe3fc1b7723e828e0000000a81669a0acd75800000000000000417617000000002d683feb092470000000012e06800000000ab900000002ba21224000ace8e64000222694a0000a20870d7e10000780c000000000089900000001c7a020400000009d490218b900007fe12942ea00019c02174000927c0000000000000000031252880000000000000000014220cfc00000027101e6800000010ba0001214000098c0000bec00023392edc0002f386e108adc0600010621e12e040001dca0000000524000000000000000000000174450000009600000000000000001366ca86368530000000151b4cf14de3af8578000000000012570002f1851a8000110ea0c000000000000001958e33b52aa0e8f0d4b820a0122000286c000194c9cd0fac00004dc0000000693d71e4456a7c626080e190837600000006a28c5f2d180262d89c203b827b496d9a0173bc9fa07a2ad43c4ec19000186c86c9f180880000000037497cc0009a988a8812c9be7331c686eec00097b8f3e2a20a6a9be4000a75c00035200000000f1e61b80001f2c00000000007e42c2c0000c0e00028e2670c000800800069e8d8c0b18ce60000000acd934e5d5a35100015aa5d168685df07965ba174e5e90036795ec0a63ee6aa11b97ca36e140c4b59dfe4278a8121d00009dd129e8c50d0c0001f78908aa160000348000000000000006798ce100000004bb000034cc0001189272000271a21d87149c6171f000000000000002daa35a00000008a000000000156a90242a95f8f7076000004100000b9f199d7808b2673e6927b87966a000000075e8529a6380000002cee0000111000000000002da00000000000794ba8000000000000001826afd800000000000000eb430d509a167ec7e0000000000000000000002434856221000000000000000000000000053a184b0001672b7405d7aee800093026ba0000e224de8b0ebad82aa6964000000000000021ce00000001f30000768aac2b5dccd65298afa00000002741aec6e9a3cc0a8c5880000000000000000000000b72d3200000000000000000202214a887842880007c28dde8d8d5f89f500000002304a824020000065c00010140000000000132a48d0000a350000000000000000000000a5f0000b056fd9a220e0c000bb8912ebc9a6c8108010050b1b1800018f6b56a8b5a94aac800005d800023185211a527fd8ffa54f8fc6555271f59946c4ad58ba90001c1c17e8340b6e17ea85b1d3ea996b2e20618a27671c404ed0ef681a8000ac5dc2a84fa6a300017c21ee1d0a6d5220c0001d5a02
  | 48 => 0xc297f2ba68000222843a5c6095426517820001514597027649a97469f7eef26cfa78a5501c8a89767ea188000024e80000512f4e077000000000009db9daa0001b98aad000000000000001f700000dae00000001c90000000046ba8ca2066328b7e3c48f85273ce312f600005cfa876000000000013d900017b00001714000000012c953c450230c00000002390000159459eb3ce6cf0000000349862eac4a01400000004d100002b11d26481895e00029cf509936c8760000561800010c800000014aa00b1d1c06d800087d0000000031a00000000001f0002c9ba20000c8400004f4bd495ba00002b00001aaa32a8000000000000000000b500000000db20000b4c00000000000000000032e9580000000000000023673df04720001f7a000000068103b081880006786158a0b400000027b093ea912a86da3d000000000023ca05e0000848510800000001d40000000000003680003e312be0bba18407859e7000020fb96dae900000000000000a0357b11aca45a00029fc000000032594fc39b80000000a731f1800084ba5e58578ba471d8c410000dd8a120eae7859b87a3040004e10000000000054760bc33903906fa98ec0000000142193615880006eac00000000004530000b9f88c27310000a0e98cb5ce5abc0000b3600023b690d800068ada0c3c50cef64a84913fa17b213267ee3d7296457180009a586994741f5e000000000000003b64000000156c000000004a400000000005e28000aa0e46c72614e00000c484092a5d939977600009153c35896310930eaf69d2b6540ba834e00003f6c0009bc01c400008d20f9c8240001aba00015d46e300008c000005678a665f325445da0000000235b524991221a846c15f1270128056827dac49aeb86778b7006e000000023600000ef032226121b800000002e6000006ce9b800000001ad800012f018428e800051e800010f89335c90000000081a6c907510aa008e3eb9f0e1acc0002f4400096985126359e74000133e6bf08526900c4627aa33d00003620002e641bc800000000000001eca0001636950209800021da7742898000222465217e289f9fc878e9ea8b11800000014788b280004cd00000002cba8a5a67667fa8020000000000000096d000000006945420dc4000000000028ce49500009e44000848000097b141e21c965500000006330000000000000000009938fd406d28a41e965a40000000699c00000013a60001c006e000009f10000155a7bc0f49ebaa118b8a7d0000050e2258a32e51d38f0bb6addc00000013803128d9c5485884b329c860002c4ca3a4460b5b04c535309171098336abf02286912c90600c0006b814ab2971fa80000000a040000417895a2b6915e0000000af32d26000295098dec5e6829dc876400003bc0000000000003a91e023aa5f29fc00
  | 49 => 0xa70800030c80008ea0e6600027d63bb905c000237a6f5000000000006fa0000a2e4c2448700000001937000104e1a16ae20000cbc1964448154000045d0000000181e00024beb008000b572dd67fd277dba980860002708000000096426a5405a6db5bd2e0049022fa7e1a4eeb5e84e6000000000000001a35c2664a1a41b84a4dca728000255a71173c6f4d78c66c3a61a5e04d8ab809b8c0006fe8ba2ae400000000000109c0009c86a540002600000121700000008f840009de000000000000000000000118400000000001f52000073a7c4878f8880000adc014500000000001ed2000144e1a5ae322e4c000bc5000000003507e4a54e67b80002ca80003f6273330a98881c6096e0000000a16289c0000000000000000000004bd14606f2480a2a500005f6a46400000000000742000000096e0f9d1248000b2280000001a00000000008a47c70001b90000071e56c0012bb4800000029a873500000000000a44000007b00000000000b1500000000000000000000029fe66dac0fb93aa4c08f456c00020106da0000000000000000000000d00000000003459e858828c36b699f800024fe00017960001dcb09294b20001b7c1ae224c0224b78163db4e0000000858523f0ef80000062d0c113ab6aa088486000000042dc0007458000a3c80000000000940ab3099000003bedac2ad6036e051867400000006ddaa39830c000000018a56b40005cb8ef43228838751eaf662f80000000000190c00000004de9aa400001d80006600000565833a5049736a5a8000a754f248510c640000aaa00000000000c3457aae985e9a9f7000000000000007c1277c7ff267e3f4009000000006b300001425e943f493f89ac800062e10581af26bb77d0a4e94184258972b00b4d8000ad640000000c741f3a60c9038fde63ae76a80d02d1b38ae34a8e0a1eab28d7c571e61a000231c000000007c800093e0a8e00018f100019d659d0000a2c000000026d3000094e9940000056196e3c2800000017b400000000000244000239200000000000000b34088d3879f960002ef00000000000000000001fb72582ccb65a2da00027b70001d1b00000000000000000000073f827a000000000008ae00006fc35622c47eb00000002b23008a59c0000000a91282f00018286df53e23ed13784d92ddeb9300000000d6700000000000000b6980aa00000008d5400000006e032bae725a600007960000000256cb640079863959a0000000000000078ddd1ab4290c6000000000007cfaf2000071686406bdaaf000000a41f0c0003b4864b000000000000004c8a05200018bf3b2809300027290000159bb09da40000b14624a4440000e7600017cf76d8a2c6c521406e18000194800000001b2af3800000000000449b42000000019680007d587a00d6a66049629220
  | 50 => 0x248200000008bc0000000159800017aa0000000000165b9c3630a00000d9000000080229d6120c49f42f800027897261b480005969de733c60be5952976422876852b077c99e2f4654908b38f9945e00008864ec000000015430caa64c966c0005d484bb000164a6ceaa820000000a8bc1bc23e000000026d20000bbf0000000ba1220802d99a6bbeca560001c16018592300000008a200001ea4000a94dc1a0002ab297740ae00000000001112a2f1c620000000083257a532187c8f21582aa2123c00000000000d6e2c31b06000040a76080009d82306b959b13906a3a01b700000002b96000185000000000000000000031c6510000000000021b23ae6b380000000e480000000111266a7fc129d44b26025462e9e9cb8fb18e9219217f26824ba47a649995f4a620d6a58a00b04658f6028f26a80001fb03b08000ace61560000000ad30af8000173b4b9000000000002e214403bde60e89aac110a32d5419c2e48b4a2d8684e142ab0de728961800000023d331345ce58080000002906000029a781263979b27631bf80000f8000000017feb1e825c7768596000297c000000084011c26accbc20000c4470500000000000000148a06300000000000305800000005c40000000b16800000000003e22786000111e6ed9bfc2e1c8f68c5c48a41c822c0000ff40000e140002a3a7a7ac7c18a800088f988348a214178b80000000000bae0bac00028201a41f600002dc26ecdcf00000d1600000004eb00007968b3e59b00009ade6fb000255a1cb132e48e0a080002aa562656de4ac0033327a76497500000000000000000000022469c640000000b90000185a00000000884000000000000007f08c2089400011f200000003b880000000000b578000b2c000000002b7b8f9ec6239800087f167c0002c3296c2cf8b0e0e4e6cc0eec25899827ac103a260079ea21099c8ac11b000000003ba890f9cbc000a6f0e3400000000000000961000000000000002aae00000000000000000000000000000000000000000000000000000000200aa3400d000000026e28fd1f3000000000000000000000056d00004b40000000000000000000001156000000039280000f000007a9890a81f98febb686e2000000022200008780000198a11e6b9acc2b368bba6e496ae000295e00002a5000000024f000035b16ce00000000000d189cc8d546afa4f400000000001a12000247e5e40b320fd87ca00017ee000215a00000000001b124c2ddf7af426c4202203000000003a8800000012c800000008d3af38000255451f119e000271e70c041e415e18693044e895da1fa1034574816800000020fa1a7800071d0000293527b2c58000000000050529a200000000000000bb92b5711dae1c08f03e300014fb74224302b585898dc2b2f054800000015634158
  | 51 => 0x61800010fcac54e4601b2b2078a5ef454c80003edcff886d060c39090d200028ca75143a1000238c96bcd440001f3c0fe011e000063b00023588ad92ca81c0c4c24acc9c93801fc631a73b000139e000007a344c00000000006b50cc4adf03da7394e243e701980000b7c0000c2212a2d1abd98240a40000000002c40be800075cc000000000000000001534094a5e00001a7668a000000000000000001d761ec9e100002048b678000000000000000fba6408ac6198000000212a19d82700001edcb99a9db8da400018413966a9475e2a4a3590001bad6d11f0b9d0000036b1b9a0002c20000259298e9bc00000c7c00000000959d3984602f60001dee323ac35a02cf39039c8e012680000002bfa3189a13000000079f0000000137e00020eea1c00009148000abe248a151000022d80006218000b1b0000000245c00000000001aa032600005888000000236802bdb361058a620550ebc63c9bdea3c2792493000077a290c000000000000000001bca000000054000000000000672053e000045218d0b28000048f51d0b5665f00003ac900b87f812812ad8786fc1de1000041a9eccf384bc43e4543c00000000005d288de000190a78c0fc2000000001800008d1d0b01a0a0b600000b86c686ee26416f6b0b66e514799ce5cc800006b0604aea845057dc0000000087000135259e0c6f80f00002f2c00000000001690fa30000a540dc5c84617a5fa00000003e38300946000059c2eba69c8000000222a55e154c0002af2000144a452057318c800000000000000549a8840005c32d1424d8617a8d90b221721f67be8af24d3c7285cb1cb22dc8a9c1b99d202e0e5cda49637c00027206868000baf000000019ae5fd07e200017f05a9a74194780001f400005ac124214280000001ffe0000c800000000ab300007a3066a0000000a39945498f00000000000a810000000015785b9d550ae842c9d99fd2a2800006042bb86b60bc800000000000fb02a5d19a0000000aad800000015220002298000021507c0c1b625c11c0000bc4000163a54800000000000000000064c00000002a3549a02dd37aa0dc00000000000737647400000000000000000ac60000409960c1ee99ba98e026a6daa91600000000002a4a9f68d8a00015ec4e417ba9d71908000000014ea176b40000000000000000000033800000000000002349b2123366a69cd7081a08c000055c7f387e43de0fd6aa597d74d55ce916c2856166000062a1f1c83587c85dbc00000000000000abc000134c00019b3a77ad99000259579c0f48000000000000001468000476863c01dd72f00000008a880000000000a3d80003b8400000018e6000000034e504fbd5800000004242890ad2a03916600000000000862b6a80000001e2893380000002ae102440000000000b2340000000000
  | 52 => 0xc2a2a8e35810000000171a00000000001006b634000918ae2c0000000a9e25880000000697c000000000000001df282800000000006688870000231a00000003be400000000004d0400000000009b6400014c80009340000526000000000006c28000000292800001e078641d40000d8200008b474019f300029543f801a0000000032fa9d400021350002e906670b2292f23eaa7d8000000107e55d000020d80001770000ae24000000000024b608e5b81dea24e0fa200000008ce80009d85082a670000049c0009be1de2702a4ac34d631129e8000a0f000000000000829b0216b0772a0500006312a766129a8025a91ea92fc000000259463940000c6c0000001ad65939a580000ed50000000000000000000002e8c0000ad00000000dd200000006558000070960641ec0000002642b13572a00001f400020cd000012a9b98000a07a51400000008eb00000c38000000000000002880000000aa629e60000000000005095905726e507de01c16d62d793680002f502fa981d086000000000000000000060a38e216800053e80000760de8000153100011d434aa972000000084980000000e924061502a860d0400000001f811322f80000b71cf7d0002cc6b45ab2b38e87d600018da000062563380009490dcd9af000064d6e18af580002f490889c30000b7b0d9426b0aaca874c399864b820000fc4991a3a6000000000021988e000000000000839a1a00001b9e00000001f50b0a740842100000000000000741000027680000002b2a21e40000001b5900023501891f5400000000000dcc000000000000001f98e6c00028a8000208000004eeaef927500020680e10000750e5dc6b95d782e7ac920001cfc0001e5c00001c500014240000000a998000000000040107ab9a4000000000001cd008a000189b2e5ea72afdc3c89ce9770a89647896b938a1f062e200005a80bc674629c80003cccf844971a824adaa2c00000009f2000000006f4b148e3e99112bc0616c1c000000055e5aeaaa30a10000203800000a2a2fadd2297a9b29a89ac05b2230f336958c00023ed000276d8a4199f00013dc1abe8fe1bc48410a7db31a725c708d14000000000000000006e56c34000000011a80004b7804872b907351a00005f700007731d495e8a65c4f68f4c0001110285633f5d08e7c0002ed00001d726eb2a6c39c13489a00b92613454c87314180dcccb400348da3d8a4161a70f740000000bcd8000000000031980006971946636d85966f2e300002a9a07e23bc0a9a3b800015ac1874f4e6350e9892480001fe11f857c8df805c03d343d158800000000000e56b4900004078e540cf5de4824800000000005448000035524475852b8000000000000000000000000264a7a0041f68e07757ee905400020d8b0d9a439adab8a1d85e1a1eb812466a
  | 53 => 0x2c5892a0bae90282d074c63f9b102dbc00000005b2a29c0000cb23f69198b75240400000000000000b7d13eaa2eaf4200000005d2c60b00000006f4800049e00000000000693a6c67cc800059e800000014c200013925070000000000075f85d2b98400011cc46d00020c49b921520b78fc75bb93c843117404b603d698fad8c3a01a735d9c6ca1a2a71273280e2a7b42ae00000006a18000000000060600008ab1ba500020c8000000000010380000000528157612994daa28800000009b00002dd85ea0000000094069b897e0f2a5c
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x84ba7418f200432cb2aa790021c655153c8010cd2cb296400872a5454b2004394aa2a590021d294d52c8010e92a6a9640085697510b20042b4ba865900211e5da51c8010ad2eb90e400856b7548720042d43a24390021721cd21c801087ce9b2c400843d74d96200422f39ecb10021175cf658801087aeb324400843f75592200421fbb4a9100210f5da548801087eecaa4400843d76552200422ebacc710021879526388010c3aa931c400845f7558e200430f2a2c7100218755163880108beed29c400845d7694e200430f324a7100218759253880108beeca9c400845d7654e200430f322a710021875915388010c5cc9294400862d6494a200432731ca5100219358e5288010c5cc8a94400862d6454a200432731aa5100219358d5288010ccaa4b0c400843e74994200421eba4ca10021179ce65080108bae7328400843e74194200421eba0ca10021179cc65080108bae63284008666525842004334b2a4010021ca5512008010e92a6900400847975190200431cb2ca8100218e59554080108f2ea31840086596594c200432cb2aa610021c65515308010cd2cb310400866965948200423dbb2a4100219a9895208010cd2caa9040087295454820043a4a9aa4100211edd56108010970e8b0840084d8735842004371312c2100213a5da2108010cd2cb1084008669650842004370b0842100211d5da51840108f2ea324200863965952100431cb2aa9080211e5d46284010cd2cb29420086696554a1004394aa2a508021d254d52840108f2ed28c200843e76951100421e3b4a8880210f9d95444010878ecaa2200862e54d891004316aa6c4880218b9506244010c5aa8312200846e7694910042363b4a4880218bd925244010c58c9292200864f63949100432631ca4880211b9d952440108d8eca92200862f645491004316322a48802193d8d5244010c98c6a92200863774d95100431a3a6ca8802199dcb6544010cc8e5b2a200863765d91100431bb28c8880218dd965444010c6ecaaa2200866765d891004333b28c488021a91906244010d88c63122008667659491004333b2aa4880218edd36544010c70e9b2a200866b72d951004334396ca880218ed9764440108f2eb32220084ba749911004275394c8880218ed946444010970ed2a2200863b65951100425c3b2a8880218ed955444010cd6cbb1220086a864d89100423cbacc4880212e9d262440109b4e731220084ea729891004335b28c488021aad906244010d50c831220086cb631891004364318c488021aa9506244010d52a831220084e8769491004335b2ca488021aa1925244010d90c729220084e8765491004335b2aa488021aa1915244010e52a8a9220086c86354910043a4a9aa4880211e9da5144010c70c928a2008668629451004358324a288021b818a5144010
  | 1 => 0x42042d5b8284210210f9d2658c81087ae932c640843e74196320421eba0cb190211e5d6608c810c72a9304640865953982320431caa2c1190219654d608c810cd4a4b04640843e74995320421eba4ca990210fdd1654c810878e8b2a640843e74195320421eba0ca990210f5d7644c81087aea322640843e76951320421e3b4a8990210f9d9544c810878ecaa2640862f649493204316324a4990218bd91524c810c58c8a92640854c735493204332a96c2990211d5d4614c810cd2a5b02640847975181320421f3a4ca190210f5d2650c81087ce8328640843d74194320423d380ca19021535ce520c810a9eea990640854d754c83204327b2a641902193595320c810b18e8990640870e544c83204386aa26419021711c5320c810b96e0990640846f725925104236392c9288210fdd16294410878e8b14a20845f7358a510422e39ac5288218e5516090410c5ca9b12820862d54d8941043172a0c4a08218b55062504108dced292820846c769494104327b1ca4a08219318e52504108dceca92820846c765494104327b1aa4a08219318d5250410c74a9b02820863954d814104335296c0a08219a54b6050410cd2a5300820863a545804104334a92c0208219a549608841087ced2a2420843c76951210421f3b2a8908210f1d95448410c3ca9b1a420861d54d8d210430f2a0c6908218755063484108bced29a420845c7694d210430fb24a6908218719253484108bceca9a420845c7654d210430fb22a690821871915348410c5ec9292420862c649492104327b1ca4908219318e5248410c5ec8a92420862c645492104327b1aa4908219318d5248410c74a9b02420863954d81210432d29ec0908219654f6048410cd4a5b02420866952d81210431caa4c0108219654e6008410c72a8b004208659535802104335292c0108210fdd16194010878e8b0ca00846f725865004236392c3280218e59654d0010e52a929680086696554b4004394aa2a5a0021d254d52d0010a72ea216800847976947400429cbae83a00214edd541d0010b50e4a0e800846e72d964004236b96cb200211b5d66290010c5ca9314800862d5498a4004237baac5200218b9516290010c5aa8b14800846f7694a4004236bb4a5200219398e5290010c9ac7294800846f7654a4004236bb2a5200219398d5290010c9ac6a948008635545864004237394ca200211b5ca65100108dce4328800846d72194400431b2a2c2200218e5954010010e52a4a00800863965990400431cb2ca8200211edd95410010c74c8aa08008639655504004334b2ca4200219a5955210010e52a8a90800874953548400423dbaac2200213a1c96110010d64c8b0880084b976904400431cb2c82200218e5944110010d62c2208800847975193200426d398c9900218e59554c80108f2ea31e40
  | 2 => 0xa529021539cf5294810a9ae7a94a40845f73592520422e39ac9290210fdd16394810878e8b1ca40854e73d5252042a6b9ea929021ca1c15494810a9ce62a4a40854d7315252042973a6a7290214b5d35394810e1ca929ca40870d5494e52042b5386c92902153dcd6494810a98e6b24a40862d6419252042b5386c7290214bdd16394810a58e8b1ca40864d6318e52042973a4c1290214b5d26094810a9ce7304a40854d7398252042973a6c4a90214b5d36254810a9ce7b12a40854d73d89520421fba2c2a90210f1d161548108bee6b0aa40845c7358552042373b6a8a9021539cf5454810a9ae7aa2a4087287055152042373b0a8a9021539cc5454810a9ae62a2a40852e74d4d5204296ba6a6a9021c39525354810e1aa929aa40870e5454d5204386aa2a6a9021ca9506054810e52a8302a40874a5318152043a4a98c0a90215a9c26454810a9ee6b22a40854c7359152042b238ac8a90215a1c16454810c5ac8322a40856a7098d5204297ba2c6a90214b1d16354810ac8e2b1aa4085687058d5204326b18c6a90214b9d26054810a5ae9302a40854e7398152042a6b9cc0a90219a9846054810cd0c2302a40852e740415204296ba020a9021535cc105481087aed2a0a40843f76550520430f2a4c629021875526314810c3ca8b18a40861d5458c520422ebb4a629021879925314810c3ac9298a40845f7654c520430f322a629021875915314810c5ca9310a40862d54988520432729cc4290219354e62148108deeca90a40862e645485204316b22a4290219398d5214810c9ac6a90a40861e6498c520430eb24c629021879916314810c3ac8b18a40862e649885204316b24c4290219398e6214810c9ac7310a40863964980520432cb1cc029021179ce65d08108bae732e840845e73197420422eb98cba10211e5d660d0810cb2a7306840866952983420431d2a2c1a10219654d60d0810cd2a4b06840845e73996420422eb9ccb21021179cc65908108bae632c840847975982420431caa4c1210219654e6090810c72a8b048408659535824204335292c121021179ce65508108bae732a840845f73595420422e39acaa1021179cc65508108bae632a840852c72551420422ebaec6a1021879536350810c3aa9b1a840845d7518d420430f2a0c6a10218755063508108bced29a840845c7694d420422f3b2a6a1021171d95350810c9ec7292840864c6394942042963a2a4a102193d8d5250810c98c6a92840863554d854204332a96c2a10211d5d46150810c72a9b02840866952d81420423cba8c0a1021179ce65108108bae7328840845e73194420422eb98ca210211e9c06510810a5ae52a0840852d749484204297baa84210214b5d54210810c5ecaa10840862d6550842042c639a8421021c394d4210810e1aa6a1084085a471508
  | 3 => 0x8c5250510c98c6292828863854d814144335a96c0a0a219a14b6050510c76a83028288638541814144335a90c0a0a219a1486050510c70a93064288658539832144334294c190a218e15160c8510cb0a6b06428866852583214421f3aec890a210f9d4644851087cedaa2428843c76d51214421f3b0a890a210f1d854485108bcebb1a428861f54d8d214430e2a6c690a21179d46348510c3ea831a428861c5418d214422f3b6a690a21171db5348510c3ec9a9a428861c64d4d214422f3b0a690a21171d85348510c3ec829a428861c6414d2144317b26a490a218b1935248510c9ec7a92428864c63d492144317b20a490a218b1905248510c9ec6292428864c63149214431daa6c090a218e1536048510cb6a7b02428865853d812144334296c090a218ed506048510c70a8302428865b53181214432c298c090a219ad486048510cd0a43024288634549874044317aa4c5202218b1526290110c5ea8b14808862c5458a4044237bb6a5202211b5db5290110c9cc7a94808864d63d4a4044237bb0a5202211b5d85290110c9cc6294808864d6314a4044237396caa02211b5cb65501108dee4b2a808846c725954044332296c2a02218dd506150110cc8a430a808866452987204421fbb6a9102210f5db548811087eec2a4408843d76152204430faa4c710221871526388110c3ea8b1c408861c5458e204422fbb6a710221175db5388110c3cc9a9c408861d64d4e204422fbb0a710221175d85388110c3cc829c408861d6414e2044317326a5102218b5935288110c9cc7a94408864d63d4a2044317320a5102218b5905288110c9cc6294408864d6314a204421f3a6ca902210f5d365481108bce7b2a408845d73d95204421fba2ca902210f1d165481108bee6b2a408845c73595204431a2a6c2902219514f6148110c68a830a4088654531852044333a90c2902215a9ca54c4110e50a9a96208853a7494b10442ad39ca588221cad5052c4110e50a8296208874b5314b10443a4298a588221c91505284110e88a6294208864e6398b540432731ac5aa0219358d62d5010a5ce5aa4a80852d72d52540422fb9ac52a021171cd6295010a74e1b14a80851f7358a540428e39ac52a0218b5886295010a5ce5304a80852d729825404297396c8aa0214b5cb64550108dee4b0aa80846c72585540429d384c4aa02147dcd6255010a38e6b12a80853471589540429c382c4aa0218b5886255010a5ce5302a80852d72981540431d308c0aa0218e184605501087eecaa0a80862d549885404316aa2c42a0218b9926215010c9cc7310a80862e64588540432731ac42a0219358d6215010cd2c5300a80861e5498f520430eaa4c7a90218795163d4810c3aa8b1ea40861e6498f520430eb24c7a90218799163d4810c3ac8b1ea40852e74d4a5204296ba6
  | 4 => 0xdeeca90a48852f7454852442963a2a42922153dcd5214910a98e6a90a48845f73590524422e39ac8292210fdd16314910878e8b18a48852e749885244296ba4c429221539ce6214910a9ae7310a48843e74980524421eba4c029221179ce60149108bae7300a48862e65d505244236bb4a829221539ce5414910a9ae72a0a48846f7655052442a7b9aa829221531cd5414910c5cca2a0a48864e65d4c5244387aa6a629221c315353149108daed298a48852e7494c5244296ba4a6292211bdd95314910a5ee8a98a48852c7454c5244387aa0a629221c31505314910a9ee6b20a48854c735905244316b20c8292215a5c06414910a5ee8b18a48852c7458c5244326b18c6292215a5c06314910a5ee8b08a48852c7458452442a7b9ac229221531cd6114910a5ee8880a48852c7444052442a7b9a2029221531cd10149108bce7b2e848845d73d97424423cb86cba122117dcd65d09108b8e6b2e848845e73d96424422eb9ecb212211e5c365909108bee6b2c848845c73596424422f39ecaa1221175cf65509108bce732a848845d73995424422fb9acaa1221171cd65509108eee2b2a848847b705954244297396a8a1221179d76350910c3ea9b1a848861c54d8d424422f3a8c6a122187d506350910c38a831a848845e76d4d424422e3b6a6a1221179d853509108b8ec29a848852e74d494244327b1ea4a12219318f5250910c9ec6292848864c63149424422f39eca21221175cf65109108bee6b28848845c73594424423db82ca212214b5c85410910a5ae8290848852e7550842442963aa84212218b9954210910c58caa10848858c735084244387a9a8421221c314d42109108f4eb300848863854980424432c29cc0212219a14a60109108f0eab00848863854580424432c29ac0212219a149601091087ce9b2c648843d74d96324423cb86cb192210fdd1658c910878e8b2c648843e74d95324421eba6ca992210f9d2654c91087ae932a648843f74595324421e3a2ca992211ddc5654c9108f6e0b2a648843e75d91324421f3a8c8992210f9db544c910878edaa2648843e76151324421e3b0a8992218bd93524c910c58c9a92648854e73d493244317b20a4992218b190524c91087ce9b28648843d74d94324421fba2ca192210f1d1650c9108f6e0b28648854d7314832442a73aa6419221531d5320c910c9cca990648864c654c832442c63a26419221c3d51320c910e18a8990648847a75980324431c2a4c0192219a14a600c9108f0eab006488638545803244334292c0192218e15260d0510cd0a53068288638545834144334292c1a0a211b9d76250510c5ea9b12828862c54d8941442373a8c4a0a218bd506250510c58a8312828846e76d4941442363b6a4a0a2193d8f5250510c98c7a92828846e7614941442363b0a4a0a2193d
  | 5 => 0x854e73d4a528422fb9ac929421171cd6494a1087ee8b1ca50843c7458e52842973a6c4a9421539cf6254a108deeca90a50845e73197428422eb98cba1421179cc6590a108bae632c850845e73995428422eb9ccaa142117dcd6550a108b8e6b2a850845e73d94428422eb9eca21421179ce6510a108bae7328850852d729504284296ba4a4214214bdd54210a10a5aeaa10850858c7350842842d238a84214210f9d0658ca1087ae832c650843e74995328421eba4ca994210fdd1654ca10878e8b2a650843e74d94328421eba6ca194210f9d2650ca1087ae9328650854d7394832842a7baa6419421535d5320ca10b18e899065085c4714c83284297396a920c210f9da5450610c5ca8312830862d54189418431d2a0c0a0c218e550605061087aedaa0830852e72d5041842973a6a510c21539cf52886108dced292430862c64949218432631ca490c218b1915248610c98c6a92430866a521812184334a90c090c211b5db5208610a5ce9a90430854e73d482184297396a9a04218b9526290210c5aa9314810852e72d51408421f3b0a8a04210fdd95410210a5ce9a96410854e73d4b2084317324a5104219398e5288210c5cc8a94410864e6354a20842973a6a490421539cf52482108dcec292410846f76548208429c3a2cb884215a1c965c4210a3ce7b16a88851d73d8b5444317b14c5aa2214b9cb61d5110a5ae5b0ea88862f5498a5444317aa2c52a2219398e6295110c9cc6b14a88864d6358a5444335312c12a2218bd936255110c9ec7b12a88862f641895444327b18c4aa2219318c6255110cc8c5b0aa88866b62d815444334316c0aa2210fdd95415110a5ee4aa0a88852c725505444297394c82a2214b5ca64151108bee6b10a88845c735885444237394c02a2211b5ca6015110a3ee6b10a88851c735885444316b10c42a2214e5c06215110a5ee4b08a88852c7258454442a739ca9a9221535ce54d4910a9ee6aa6a48854c735535244387aa6a7a9221c315353d4910a9ce7b26a48854d73d935244317b24c9a92214b9d363d4910a5ae9b1ea48864f6398f52442973a6c3a92214b5d361d4910a9ce7b0ea48854d73d87524430faa4c729221871526394910c3ea8b1ca48861c5458e524430f326a729221875935394910c5cc9a94a48862d64d4a524432731ea5292219358f5294910c3cc931ca48861d6498e524430f322c729221875916394910c74c8b04a48865a63582524421f3b6a8a92210f9d85454910c3ea9b1aa48861c54d8d524430faa0c6a9221871506354910c3ec9a9aa48861c64d4d524430fb26c6a9221871936354910c3ec831aa48861c6418d5244317b26c4a92218b1936254910c9ec7b12a48864c63d89524431a326c2a92219518f6154910c76c9b02a48863864d81524432db1ec0a92219618f60549108
  | 6 => 0x8236bb4a5100418b9925288020c9cc729440106996458e200823cbb4a510041b898621880208dcec2a2401046e7614d20082963a2a290041531cd5148020cc8c2a8a401052e7494120082a739ca0900415a5d64048020b92e720240107285450120082b4bac60900416a5d23048020e90a698240105a974d8920082e4b9ec4900415add54248020b96e6a12401056b754c920082d5ba264900415a5d62148020dc0c310a401064f63d8954c4317b20c4aa62193d8c6255310c98c6312a98866b62d8154c4334316c0aa6210fdd95415310a58e4aa0a98845f7358854c422e39ac42a62187d936354b10c38c9b1aa58861f6418d52c430e320c6a96218b1936254b10c98c7b12a58863b64d8152c431c326c0a962196d8f6054b10cb0c7b02a58846f7654852c42963a2a429621531cd5214b108bee6b20a58845c7359052c421fba2c6296210f1d16314b108bce7b2e858845d73d9742c4335a94c1a1621179cf6590b108bae7b2c858863b5498242c422f39ccaa1621175ce6550b108bee6b2a858845c7359542c422fb9aca21621171cd6510b108bce6328858845d7319442c4296b90a8216214b5d05210b10a5ceaa10858852c7550842c42c639a84216216adc14210b1087ce9b2c658843d74d9632c432da9cc1196210f9d2654cb1087ae932a658843f7459532c421e3a2ca996210fdd1650cb10878e8b28658843e7419432c421eba0ca19621535cc520cb10a9cea990658854c754c832c42c63a2641962172dc1320cb10a58e4aa4838843e7615141c4317aa0c4a0e218b1506250710c70a8302838843f7655041c4296392a820e214b1d15288710a98e6a94438862c64d4921c432631ea490e211b9d85248710c58c8292438864c6314921c4334290c090e211bdd95208710a58e8a90438854c7354821c4296392a9a06216a1c954d0310b50e4a0e818862f5498a40c43162a4c5206210f9da5450310a58e4aa2818843d76d5040c4274392ca206211e5db5410310972edaa081885b271d5040c42d9388a8206213a1c96110310972ed208818852c7454b20c42a639aa590621369cc64c8310974e831e41885a87454b20c42e439aa5906216a1d121c8310b90e690e418862e64d4a20c432731ea5106218b9905288310c9cc6294418846e7694920c42963a2a490621531cd52483108daeda9041884b87459420c426c39aca106211e5db52083109d2eda9041885e271d4820c42f1388a4106212e1d161083109b0e6b0841884e97688420c432731cc5aa4219398d62d5210c9ac6b16a90866a629835484334b14c1aa4214b9cb54952108bee6b14a90845c7358a5484297396c8aa4210fdd95415210c3cc931ea50861d6498f528430f322c7a94218759163d4a10c74c9306a50863964983528432d31cc1a94219658e60d4a10a5ce9a94a50
  | 7 => 0x390241721cd21c8120ec0a290e40904ce731922048347324c710241a35926388120d1cc8b1c409062e641462048327318a310241995845188120d54c9a8440906ca63d42204832731cc5aa0419358e62d5020cb2c7306a81051e73d525408236392c72a041479cf64550208b8e6b12a81043f76550540822fb9ac22a041171cd61150208bae7300a81062e6498b5308316b24c5a98418e59260d4c20a3ce9a9ca61051e74d8d530821fba2c4a98410f1d16254c208beeca98a61043f74584530821e3a2c2298410f9d26014c2087ae9300a61047a701964308237b92caa18411b5d46250c209d2e0312861046e72994430823b388ca218411d5c46510c20a3ae72a0861051d7494c430828fbaa8621841475d54310c20b18e4a18861046f75588430823cbacc02184117dcd64948208b8e6b24a41043f7458e520821e3a2c7290418e55260908208bce7b28841045d73d944208296b92a8210414b5d25210820a5eeaa10841058c73508420832ca9cc1190410f9d3650c82087ae9b28641054d7254c32082a6b9ca41904153dd5320c820b18e8990641045f73592510822e39ac9288410fdd16394420878e8b1ca21061f64d8d510830e326c6a884187d906354420c38c831aa21063b64181510831c320c0a884196d8c6054420cb0c6302a21047776544510822f39ecba0841175cf65d04208bce732e821045d739974108237baac5a0841479cf5490420a5ce5aa4821045f73595410822e39acaa08410f9da5450420c3ca831a821061d5418d41083172a0c4a08418b5506250420c74a8302821063954181410821ebb6a820841479cf5410420a5ce5aa0821043e74d97310821eba6cb988410f9d265cc42087ae932e621046f7558b310828f3a6a7188410fdd1654c420878e8b2a621061c6494d310830e322a6988419394c624c420c9aa6312621065a53181310832ca98c098841175db530c420a3ce9a986210668705962108236bb0a9108411b5d85388420a58e8a8c421054c7354621082b4baec1108419a5976088420c58c9292421064c6394921082963a2a210841531cd5108420c3cc931ca01061d6498e500830f322c728041875916394020c5cc910ca01064e638865008236bb043280418b9902194020c9cc610ca01051e73d534008297396a9a0041179cf65900208bae7b2c801061e5498e400830eaa4c7200418b9526290020c5aa9314801051e73d514008297396a8a00414e9c3545002087cec2a2801045e73d94400822eb9eca20041179ce65100208bae7328801043f765504008237baac420041479d353cc02087ce9b2c601043d74d96300830f324a71804187991538c020c9ca7314601064d5398a300828f3a6a6980410f9d2650c02087ae9328601046f755883008237bb2a3900414b1d151c8020a98e6a8e4010666615472
  | 8 => 0x54310d20b18e4a18869054c7355342482b238aa9a12411b1d561d09209d4eb306849066a75983424828e39aa9212414d1c5549092087cec2a2849061f5418d424830e2a0c6a12414b5ca541092087eecaa0849051c73550424829a38aa821241631cd4210920b52e12a0849046f7655042482a639aa821241591c5541092095eecaa0849058c7355042482d238aa8212416adc15410920a5eecaa0849062f765504248387b9aa8212414b1cd5410920e18e6aa0849050c735504248393b8aa8212414b1c55410920e48e2aa08490524715504248297b82a821241cadc154109209d4e1318849046d7694c4248296ba0a6212414bdd64310920b52e1218849052d7510c42483862988621241331cd61109209d0e0b0884904ce739804248275380c9992411b5da54cc9208d8eab0e64904ea7598332483353acc199241471d1538c920aa8e2a9c649061c64d4d324822f3b0a69924187190534c920b18e899064904ea7099032482373a8c8192411b5da540c920a9ae62a064905c97094c3248237bb2a6192414b1d1530c920ac8e2a9864904cf7654c32482c63a2a619241711c5530c920b96e0a98649054f7654c3248327bb2a619241c3dd1530c920a98e8a98649070c7454c32482863a2a619241d1dc5530c920a98e2a9864907447154c32482a238aa61924153dc1530c920e96e0a98649054f75d0c32482e4b868619241535d4430c920e18a821864904ac745843248274382c2192412b9d2600c9208eeeca88a2905347454451482aa39aa228a4117dcd64145208b8e6b20a29043f7458c514821e3a2c628a415a9c34214520c5ac8210a29056a70cc85148326b186428a413a1c162905208bce732a829045d73995414822fb9aca20a41171cd65105208bce6328829045d7319441483162a2c420a41331cd6210520c5aca2108290724421444148354212c020a413a1c1628c52087ce932a629043d74995314821fba2ca18a410f1d1650c52087ce8328629043d7419431482563a2c418a419314d620c520c9aca1906290744321443148364192c018a413a9c264c85208dcea32642904ea7098f21482373a8c790a412b9d260c852099ce7306429063464d45214832a31ea290a418d1905148520ca8c628a429067051d8121482573a4c890a41339ce64485209d4e1322429068c64d8d21482573a4c690a41339ce63485209d4e131a429068f6418d2148346320c690a41a91935148520d88c7a8a429062c641452148326318a290a41a91905148520d88c628a42906a864d81214836431ec090a41aad906048520d50c830242906cb631812148364318c090a413a9d46048520cd4ea302429062c5458b404826639ac5a024117dcd6550120c5aca21280904ac7458b304832629ac5982410fdd1654c120878e8b2a609064d650c930482d43a24
  | 9 => 0xae932c631043f74595318821e3a2ca98c410f9d0654c62087ae832a631043d75d91318821eba8c898c410f9da544c620878ed2a2631043e76551318821e3b2a898c4187d92534c620c38c929a631061f6454d318830e322a698c418b953624c620c5aa9b12631064e53d8931883172a0c498c418b550624c620c9ca6312631064d53189318831d2a6c098c418e553604c620cb4a7b02631065953d81318831d2a0c098c418e550604c620cb4a6302631065953181318821f3a4ca18c410f5d2650c620c72a9300631063954580318832d29ac018c41539cc5488620e1ca929c431070d5494e21883872a2a710c41c99525188620e8ca728c431062e54582218832729ac110c410f5d7644862087aea322431043e76951218821e3b2a890c41175d76348620c3ca9b1a431061d54d8d218822eba8c690c41879506348620c3aa831a431045e7694d218830fb24a690c418719253486208b8eca9a431061f6454d218830e322a690c418e9536048620c72a9b02431065a53d81218832ca9ec090c418e9506048620c72a8302431065a53181218832ca98c090c419c9446048620c5acb2a0431062d655502188236bb0a810c41539cc5408620c9acb298431070e5494c2188386aa4a610c41935955308620e1ca8a9843107265498421883a329cc210c418b9516008620c9ca6b00431045d7598e408830f2a4c7204418755263902208beeab1c811061e5458e408830eaa2c720441175da53902208beeca9c811062e5498a4088316aa4c5204419394e6290220c9aa7314811062e5458a408832729ac5204419354d6290220c5ca9310811064e5398840883172a2c4204419394d6210220e32a6a00811043d76952308821fbb2a9184418b952628c220c5aa9314611064e5398a30883172a2c5184418b551628c220c9ca6b14611062d659532088316b2aa990441539cc54c8220c9acb29e411070e5494f2088386aa4a7904419359553c8220e1ca8a9e411062e54987208832729cc3904419998551c8220c72cb2a6411063965553208832cb2ca7904419659553c8220e32a8a9e411054c7358a544830fb20c6aa2419318f6255120caec7b0aa89065463d85544831bb20c2aa24195d8c6155120ca8c630aa89066762185544833830ec0aa2410fdd95415120a38e6aa0a89053471550544822fb9ac22a241171cd6115120a58e8b14a69062c64d89534831bb26c2a9a418d1936154d20c6ec830aa690634641855348333b10c2a9a419c1876054d208beeca98a69051c7454c53482aa38aa629a410fdd16114d20878e8b08a69047671d97434823ab8ecba1a411d9c76590d208eae3b2c869047875582434823bb8acaa1a411d1c56550d209d4e1b12869047970d94434823bb8aca21a411d1c56510d20a3ae62a0869051d7414c434828f3aa8621a41471d
  | 10 => 0x55a70d9253882a7b92c929c41875906494e20a9ae4324a71051f7458a538828e3a2c529c41535cb6194e20a3ee8b0ca71051c7458653882a7b92c329c41561c16194e20ab4e030ca71051e74982538828eba4c129c41479d36354e20a3ae9b1aa71045e76d51538822f3b0a8a9c41569c26454e20a9ee4b22a71061d64191538828fba2c4a9c41471d16254e20aaee2b12a71055471589538828fba2c2a9c41471d16154e20a9ee4b0aa71055870585538828f3a4c0a9c41475d26054e2087aed2a0a71043f76550538822fbb2a629c41879915314e20c3ac8a98a71065953983438831d2a2c1a1c419654d60d0e20c72a9304871063954582438832d29ac121c41471cd5450e20a38e8a9a871062e54d894388316aa6c4a1c419394f6250e20c9aa7b12871062e541894388316aa0c4a1c419394c6250e20c9aa6312871051d73950438828eba4a621c4147dd54310e20a3aeaa18871061f6550c438830eb2a8621c41631c94310e20c5ca9310871064e5398843883172a2c421c419394d6210e20cb2a7306851063a54583428832ca9ac1a1441175d76350a20c3ca9b1a851061d54d8d428822eba8c6a1441879506350a20c3aa831a851045e7694d428822e3b2a6a14418e5536050a20b18e6a10851070e535084288386a9a84214418e55260cca20c72a8b06651065a53583328821ebaec8994410f5d4644ca2087ced2a2651043c76551328830fb24a69944187192534ca20c3ec8a9a651061c6454d328832ca9ec099441631d1320ca20e1ca8990651070d544c8328830f2a4c7a8c418755263d4620c3ca8b1ea31061d5458f518830f324a7a8c418759253d4620c3cc8a9ea31061d6454f518822fb9ac928c41171cd649462087ee8b1ca31043c7458e518821ebb4a828c410fdd95414620c3ca9318a31061d5498c518830f2a2c628c418755163146208baed298a31061e6494c518830eb24a628c4117dd95314620c3cc8a98a31061d6454c518823bbb2a228c41179ce65d06208bae732e831062e5498b418832729cc5a0c418b95162d0620c9ca6b16831045e73996418822eb9ccb20c4117dcd65506208b8e6b2a831045e73195418822eb98caa0c41175d76350620c3ca9b1a831061d54d8d418822eba8c6a0c41879506350620c3aa831a831045e7694d418822e3b4a6a0c41179d953506208b8eca9a831062e54d89418832729ec4a0c419354f6250620c5ca8312831062d541894188327298c4a0c419354c6250620c74a9b02831063954d81418832d29ec0a0c419654f6050620c74a8302831063954181418832d298c0a0c419654c60506208bce7328831045d73994418832ca9cc020c418e9516010620cb2a6b00831043e74997318821eba4cb98c418b95262cc620c9ca7316631062e5458b318832729ac598c410f9d2658c62087
  | 11 => 0xc83172a0c4a1e418b5506250f20c9ca6312879064d5318943c821ebb6a821e41475cc5410f20a38eaa18879061f6550c43c830eb2a8621e41631c94310f209d2e5300879054c7355342c8236bb0a7a16414b5d053d0b20a38e6aa4859051c7355042c82c639a84216418e9516010b208deecaa0859054c7355042c82c639aa8216414bdd95410b20c5eecaa0859070f7355042c829639aa821641c31cd5410b20a18e6aa0859052c7155042c8296ba0a6216414bdd64310b20e1ca7218859052d7510c42c838629886216416a5c04310b208deeab0885904cc7358442c8274382c221641339ce6010b209d4e0326659046d7615332c82a6b98a9996414b1d153ccb20a38e8a9c659051c7454c32c82c63a264196419694d600cb20a9ae62a0659052c7454c32c82c63a2a61964153dd9530cb20c9eeca98659070f7454c32c82a63a2a619641c31d1530cb20a18e8a98659054c7154c32c82a7bae8619641c3953430cb20a9aea218659070c5410c32c82e4b8086196411bdd5610cb20958e8b0865904e87058432c82573a4c0196411ddd951147209d2e5306839045e73d9641c822eb9ecb20e41179ce65907208bae732c839051c7355241c8316aa4c520e418bd9442907208bee6b2a839045c7359541c828e39aa820e41331cd6210720c5aca21083904e97298331c821f3a6cb18e410f5d3658c72087ce932c639043d7499631c828e3a2a718e419354e628c720c9eca194639043f7459531c821e3a2ca98e41471d1530c720958e8b10639064d650c831c82573a4c190e41339ce60c8720c5ecbb2243904ce7399121c8275384c890e418bd946448720c9ecbb1a439068c64d8d21c82573a4c690e413a9c26348720c9eca31a439068f6418d21c8346320c690e418b1925148720c98c728a439066b65d8121c8354326c090e41b218f6048720d56c830243906a86418121c8365b18c090e41b218c6048720cd4a2302439051c7355340c826639ac5a0641471cd5450320c5aa831281904ac7458b30c832731ac5aa4419358d62d5220a3ce7aa4a91051d73d52548822fb9ac32a441171cd6195220a74e1b1ca91052f7258e548830eb18c72a4414b5c86395220a3ee6b14a91051c7358a5488296b96c32a44147dcd6195220a38e6b0ca91052f72586548829c382c32a4414e9c06195220a3ce7304a91051d73982548828f39ec8aa441475cf6455220a74e131aa91052f7258d548830eb18c6aa44147dcd6255220a38e6b12a91053771589548829a38ac4aa44147dcd6155220a38e6b0aa91052f72585548829c382c2aa441479ce6055220a3ae7302a91043f76550548830eaa4c62a441875516315220c3cc9318a91061e6458c548832731ac42a4419658e6015220cd2c5300a91051e74d4e538828eba6a729c410fdd16194e20878e8b0ca710
  | 12 => 0xa04818b59552d0240e1ca6a96812062e52987409031b30aa3a04819a59652d0240cd2caa9681207495354b4090237bb2a429281531cd5214940ac8e2a90a4a045f73584525022e39ac2292810f1d56190940974eb30484a063a75982425032631ea4a12819318c5250940b18e6a1084a04ba7098c4250296b90a6212816a5c2521094095eeca9084a058c7354842502d238aa4212816adc15210940938e6b0884a04b870584425024f39cc021281a610d608c940974e1b2264a047771594325023a38aca192812e9c3640c94087cea32064a054d731483250316b288419281c314c420c940a9cea99064a054c754c832502c63a264192811ddd95114540ac8e4a88a2a045f73588515022e39ac428a814e9c24214540c5ac4210a2a04ba7098b4150257394c1a0a819918b5150540cc8c428a82a067051d814150347b18c4a0a81a318c6250540d48c5a8a82a062c621454150352310a2a0a81aa18b6050540d56c430282a06a862181415025d3a8c0a0a818e9d4605054093ce7b2642a04ba70d93215021f3a8c990a812e1c164885408bce732a42a045d73995215022fb9aca10a81171cd65085408bce632842a045d73194215024e39ac810a818b590520854095aec21042a062d651082150392210a210a81aa1096008540b50e4a0e80a073051507405034731cc520281a398d6290140c5cc428c80a0635611464050355316a120281539cf52948408deeca90a42052f7550842102c639a84210812e5c0644c84087eeab20642054d7394832102a7baa6419081535d5320c840b18e8990642045f7358a511022e39ac52888193d8f6254440c9ec6312a22064c631895110335b10c0a88819a18860544408eeeca88a220638705964110296392a3208814e5d76090440c72cbb04822062e541894110296392a220881179cf65c84408bae7b2e422045e73997211022eb9ccb908810fdd564c84408bee6b2a422045c735952110316324a4908819318e5248440c58c8a92422064c635492110335290c0908819a5486048440c9cc7314a02064e6358a5010326b1ac5280810f5d8419404087eeca8e802052c72547401031b30aa3a00810f5da54900408f2ed2a480206c96358a401035930c83200814b1c95150040c68c2a8a80205a972d91401029dbaa84a008166dcd4250040a72eb20a80206b061905401022fb9ac32a641171cd6195320c3ec831aa99064f6318954c8326318c4aa6410fdd95415320a38e6aa0a99061d5458c54c830f322c62a641931c96315320c9ac7310a99065a6358054c8335312c02a6410fdd16194f20878e8b0ca79061d7319153c822fbb2a629e41471d15314f20c3ac8a98a79062c7259053c8316b24c429e418e9916014f20a38e6aa6879051d7315243c828e3a2a721e410f9da5450f20a38e6aa2879051c7454d43
  | 13 => 0x6250740d18c631283a062c6294541d031db2ec0a0e81aa18b6050740d56c430283a06a86218141d031d288c0a0e81279cf64c8740974e1b2643a04b97498321d022f39ecb10e81175cf65887408bce732c43a045d7399621d0317322a510e81531cd5288740c5eca21443a045f7359521d022e39aca90e81271cd6408740a98e6a9043a062d6510821d02a739ea529481535cf5294a408bee6b0ca52045c7358652902b5386c7294814bdd16394a40a5ae831ca52064d6318e5290296ba6c3294814bdd16194a40a9ee6b0ca52054c7358652902b4382c3294815a9c06194a40a9ce7304a52054d7398252902a7b9ac8a9481531cd6454a40acee2b22a5205647159152902b5384c6a94814bdd16354a40c9ac631aa52052f7458552902a7b9ac2a9481531cd6154a40ad0e0b0aa52054e7398152902a6b9cc0a9481175da5314a408beeca98a52046f76548529032731aa4294819358d5214a40cb2a73048520659535824290335292c121481175d76350a408baea31a852045e7694d429022e3b2a6a148193d8e5250a40c98c7292852064f63549429032631aa4a14819a54b6050a40b18e6a10852070e535084290386a9a84214819654e608ca40cb2a6b04652066a525823290317b24a4994818b192524ca40c5ec8a92652062c6454932902a639aa4994818b992520ca40c5ac9290652054d7394832902a7baa6419481535d5320ca40c9eca990652064d654c832902c63a264194819398e52d4640c9ac7296a32064e6354b5190326b1aa5a8c8117dcd62946408b8e6b14a32046d76948519032731ca428c819358e52146408deeca90a32064e635485190326b1aa428c811ddd95114640e1ca7294832070e5354a4190393294a320c818b94960906408daebb12832046d7518941902373b4a4a0c8193d8e5250640c98c7292832046c765494190327b1aa4a0c819318d5250640cd4a5b02832066952d814190335290c0a0c819a5486050640ce4a2302832062d65948419038729ca420c818b5955210640e1ca6a908320726529844190317292c020c81179ce65c86408bae732e432061e6494f219030eb24a790c818b99252c8640c5ac9296432045e73996219022eb9ccb10c8117dcd65486408b8e6b2a432045e73195219022eb98ca90c81175d763486408baea31a432045e7694d219022e3b4a690c8187d925348640c38c929a432045e7654d219022e3b2a690c8187d915348640c38c8a9a432062f649492190316324a490c8193d8e5248640c98c7292432062c645492190327b1aa490c819318d5248640cb4a7b02432065953d812190335296c090c819a54b6048640cb4a63024320659531812190335290c090c819a54860486408bce7328432045d73994219032ca9cc010c819654d6008640cd4a4b00432062d6594b409038729ca5
  | 14 => 0xecaa08410f0f73550420869639aa821043c31cd5410821a18e6aa08410d2f705504208636bb0a6210434b5d05310821ad2e02988410d2f7590c420878729c86210434b5d44310821e18a62188410c6f75584420866639ac2210433a1c161108218daeb3008410cce739804208636ba8c9990433a9c064cc8218daec2a66410d4d7315332086b4b80a9990434b1d153cc82187ce9b2c6410c3d74d96320868e3a2a719043471d1530c821b18e89906410c6d751903208636bb0a819043535cc540c821ad2e02a06410d4d7598c32086a6baca6190431bdd9530c821a58e8a986410d8c7454c32086a7bb2a61904393dd9530c821e1ee8a986410d4c7454c32087863a2a619043431d1530c821a9ee0a986410d4f75d0c32087872a68619043535d4430c821e18a82186410c6f7558432086563a2c2190433a1c1610c8218daeb3006410cae74980320862f39ecb20843175cf6590421a38e6aa48210e2d5498a4108696ba885208438bd9442904218bce63288210c5d73194410868e39aa820843331cd6210421a5aea2108210e2d65108410861f3a6cb188430f5d3658c421a38e8a9c6210e4d5398a3108727b2865188430f9d0650c42187ae83286210cac745883108726b2864188432b9d260c842199ce73064210c6d7694a210863abb4a5108438bd9764484218daeb3224210cae74991210866739cc8908433a9c26448421c5eca3224210e4f65d8d2108746326c6908431b5d6634842195ce931a4210cce7398d2108675384c69084393d946348421d1ec831a4210e8c6418d2108716324a2908439318e5148421cd6cbb024210ea864d81210876431ec0908439ad946048421d56c83024210ea8641812108765b18c090843b218c6048421cd2ea3024210e3765d91210871bb28c89084395d976348421caeca31a4210ea464d89210876231ec4908439cd976048421ce6ca3024210eb0641812108768318c090843b8d886048421ad4e1a12a010d6a7010950086b538664a80435a9c03254021ad4e190aa010d2c7448550086a639a42a80435a1c121540218f6eca80a010e3964540500872cb1aa02804317dcd6194b408b8e6b0ca5a046f7654852d02a639aa4296819358d5214b40a98e6a9685a051c7354a42d02a639aa421681631cd4210b40a38e6a9085a058c7354842d0297bb2a4216818bdd95210b40e1ee6a9085a052c7354842d038639aa421681431cd5210b40a58e2a9085a043f7558442d024e39ac2216812e1c16110b4093ce730085a061f6510e32d038621ca519681531cd528cb40c58c929265a062c6454932d02a639aa4996812e9c3640cb40c5aca21065a054c754c832d0327b2a641968193595320cb40b18e899065a04b97498032d0354212c0196811ddd9511474095ce530683a062f65d8941d0317b28c4a0e81a3d8c
  | 15 => 0x5e7614d504870fb20a6a82438719053541218f6eca80a090d3b74540504869c3a2a02824356dcd5014121ab0e6a80a090d6970884504871d32ea8282431e5da5414121ab4e72a0a090d5973950504863dbb2a82824356dcd5414121ab0e6aa0a090e3a65150504872d32ea628243c6d535314121e30a9a98a090c797694c504869d3a4a6282434e5d253141218f6eca98a090d3b7454c504869c3a2a628243969945314121e36a8298a090f185414c5048795aa2c428243ca1516214121e96a6b10a090f485358850487982a64228243d414f2114121e56a9108a090f285488450487a5a9c4228243d214e2114121ab4e7b20a090d5973d9050486b4b96c8282435a5c86414121a74e9b18a090d3974d8c50486b4b96c6282435a5c86314121ad6e4a18a090d687250c504878ca1886282435a9c84314121ad2e4218a090d3a74d88504869cba6c428243569cf6214121ab2e7b10a090d5b7350850486ac39a84282435cdc54214121ae0e2a10a090f2942108504869dba264282434e1d13214121ae6e2990a090d70714c850487a499064282435a9cb4114121ad2e5a08a090c7b7650450486adb9a8228243561cd4114121ad6e4a08a090d687250450486b539662282435a5cb31141218f6ec988a090d3b744c4504869c3a262282435adc93114121ad0e4988a090d3b74484504869c3a2422824356dcd2114121ab0e6908a090c5e73982540862eb9cc12a04387d906355021c9ec6312a810e4c63189540861fbb2a82a043471cd5415021c3aa8b18a810e3954580540870f322c62a043931c96315021c9ac7310a810e5a63980540872cb1cc02a0438e9916015021cb4c6b00a810e59635805408735312c02a0430f9d26094c2187ae9304a610e1d73191530870e326c6a98438bd906254c21c58c8312a610c5f7654c530868e3a2a629843875915314c21cb2a6b00a610e2c725905308716b24c4298438e9926014c21c72c9300a610e3a64580530871cb22c0298439a9896014c218f4e032e8610c7970197430868e39aa9a18431b5d662d0c218f4e032c8610c7970196430868eb98a9218434e5c05490c21a38e8a9c8610c3f74595430862fb9acaa18431e9c06550c218f2e032a8610c3e76951430868e39aa8a1843471d15350c218daea3128610e2e541894308716aa0c4a18439394c6250c21c9aa63128610c7a70194430863cb80ca218430f5db5410c2187aec2a08610d1d73150430869cb80a821843175db5310c21a3ceaa188610d1c7550c430870fb2a8621843875954310c21b18e4a188610d4c735534208636bb0a7a10434b5d053d0821ad2e029e8410c5e73d96420862eb9ecb21043471cd5490821a38e6aa08410d8c735084208696bacc8210434b5d654108218deecaa08410d4c7355042086c639aa8210434bdd95410821c5e
  | 16 => 0x868eb98a821a43475d05310d21a3ceaa188690d1c7550c434870f32a8621a43871954310d21b18e4a188690c6e7598843487162a4c421a439314e6210d21c58a8b108690e4c53588434871a2a4c3a1243179d76350921c3ea9b1a8490e1c54d8d424862f3a8c6a124387d506350921c38a831a8490c5e76d4d424862e3b6a6a1243179d85350921c6ea830a8490d2c7550842486c639a8421243c3d4d4210921e18a6a108490e5453987324861f3aec8992430f9d4644c92187cedaa26490c3e76151324870fb26a69924387193534c921c3ec829a6490e1c6414d324872ba98c299243631d1320c921e1ea89906490f0c544c832487162a4c5a0a439314e62d0521c58a8b168290e4c5358b414862eb9ecaa0a4317dcd65505218bcebb1a8290e1f54d8d414870e2a6c6a0a43179d46350521c3ea831a8290e1c5418d414862f3b6a6a0a43171db53505218bcec29a8290e2c54d894148727a9ec4a0a439314f6250521c5ea83128290e2c541894148727a98c4a0a439314c62505218f4ebb028290e3b54d81414871c2a6c0a0a4396d4f6050521cb0a7b028290c7a75181414871daa0c0a0a438e1506050521cb6a63028290e585318141487162a4c598a439314e62cc521c58a8b166290e4c5358b314861fba2ca98a430f1d1654c52187cedaa26290c3c76d51314861f3b0a898a430f1d8544c521c5ea9b126290e2c54d893148717aa0c498a438b150624c521c9ea63126290e4c5318931486a739ca910a435a9c25488521e18a9a9c4290d2e7494e21486b5384a710a43c3d505388521e18a829c4290e2c54582214872629ac110a4317dcd64d41218b8e6b26a090c3f7458f504861e3a2c7a8243569ce54d4121ab2e72a6a090d5b7355350486ac39aa9a8243c6d5353d4121e30a9a9ea090d3a7494f504869cba4a7a82434edd153d4121a70e8a9ea090f1b5414f504878c2a0a7a8243ca15362d4121e90a7b16a090f285488750487a429c43a824356dcd64d4121ab0e6b26a090d6b72593504869dba2c7a82434e1d163d4121ad6e4b1ea090d6b7250f50486b439287a8243c650c43d4121ab6e6a16a090d587350b5048794a1085a82434edd132d4121a70e8996a090f49320cb504869d3a6c3a82434e5d361d4121ab4e7b0ea090d5973d87504863dbb283a824356dcd41d4121ab0e6a0ea090d6b7250750486b439283a82431edd931d4121a76e898ea090d38744c750486b5b9263a82435a1c931d4121c3ea931ca090e1c5498e504870faa2c728243871516394121c3cc9a9ca090e1d64d4e504870f320a728243875905394121c74c9a84a090e3964d42504872d31ea1282439658f509412187cedaa2a090c3e76151504870faa6c6a8243871536354121c3ea831aa090e1c5418d504862f3b6a6a824387d935354121c38c9a9aa090c
  | 17 => 0x84430f5d36354221c5ec8212a110e4f630c950886b538642a84431edd95014221a5ae5b1ea890e1f6398f544868f39ec5aa243475cf62d5121a3ce7b0ea890d1d73d87544869d386c3aa2434e5c361d5121a3ce6306a890d1d731835448696b90c1aa24387d526395121c3ea8b1ca890e3b54982544871daa2c12a2439398d6295121cb4c7304a890e59639825448734b14c12a2439a5ca6095121cb4c6b04a890e5963582544870fb26c6aa24387d906355121c9ec7b12a890e4c63d89544871db26c0aa24396d8f6055121cb0c7b02a890e6b62d81544871db20c0aa24396d8c6055121cb0c6302a890e6b621815448739b08c0aa2430fdd95415121a3ee6aa0a890d1c73550544869db82a82a2434e1c15415121a3ce7320a890d1d73990544869d384c82a2434e5c264151218bce7300a890c5d739805448697b92c62a2438758c6315121a5ae4318a890d1f73588544868e39ac42a24347dcd6115121a38e6b08a890d3b70584544869c382c22a243479ce6015121a3ae7300a890d2d729805448696b90c02a243569c254d4d21ab2e12a6a690d5b7055353486ac382a9a9a43535cb64d4d21c3ec9326a690d1e74d8b534868eba6c5a9a43479d361d4d21a3ae9b0ea690d5a70d8753486acb86c3a9a43479d060d4d21a3ae8306a690d4d72183534870f326a729a43875935394d21c76a9304a690e3854982534872da9cc129a438ed516094d21c70a8b04a690e5b535825348717322c529a438e9926094d21c72c9304a690e69629825348734b94c129a438e9916094d21c72c8b04a690c3e76d51534861f3b0a8a9a438ed536054d21c70a9b02a690e3b54181534871c2a0c0a9a438bd936254d21c58c9b12a690e3b64d81534871c326c0a9a439ad8b6054d21c76c8302a690e38641815348735b10c0a9a439cd846054d218beeca98a690d1f7454c534868e3a2a629a4356dc15314d21ab0e0a98a690d1e7498c534868eba4c629a43569c26314d21ab2e1318a690c3e74980534861eba4c029a43879975414d218baed2a0a690d5a7095053486acb84a829a4317dd95414d21ab6e0aa0a690d5870550534870f328a829a4353dc96414d21c3ac8320a690d4d72190534868fba2c229a43471d16114d21ab6e0b08a690d5870584534868fba24229a43471d12114d21a3ce9300a690d1d7498053486a6b94c029a43535c86014d218f4e1b2e8690c7970d97434863db82cba1a431e1c165d0d218f4e1b2c8690c7970d96434863db82cb21a431e1c16590d218f4e1b2a8690c7970d95434863db82caa1a431e1c16550d21a3ce7aa28690d1e74d4d4348717aa6c4a1a438b1536250d21c9ea7b128690e4c53d894348717aa0c4a1a438b1506250d21c9ea63128690e4c53189434863d386ca21a431e5c36510d218f6e0b288690c7870594434
  | 18 => 0x4904418eaed2a48220e2f65d894110717b28c4a0883a3d8c6250441d18c63128220e3b65d814110754316c0a08838ed946050441d56c43028220ea862181411071cba8c0a088399d976250441cceca3128220ea7641894110739b2ec0a08839cd946050441d66c83028220ee062181411069d38484a80834e9c04254041a74e1a0aa020d2c72505501069c38282a80831edd95014041cd2c4a80a020e4e6398b54c8726b1cc5aa6439698e60d5321cb2c7306a990e6a6298354c872d31ac1aa6439658d60d5321cd4c4b06a990d1e73d5254c869d386a92a643479cf6455321a74e1b22a990c3f7655054c862f39cc02a643175ce6015321a3ce9a9ca790d5a70d4e53c862fbb2a629e430f9d26014f2187ae9300a790c7a7019643c863cb80cb21e431e9c36510f218f2e1b288790c7a7099443c863cb84ca21e43475ce5410f21a3ae92988790d1f7550c43c868ebaa8621e43631c94310f21b18e6a108590d8c744c832c868f39ea920e434e9c3549072187ced2a28390e1e5418d41c870eaa0c6a0e438b9506250721c5aa83128390e3a5418141c871caa0c0a0e430f5db5410721a3ce7aa08390d3a70d5041c869d3a6a128643569cf5094321c70e0b24a190e1e6498e50c870eb24c728643879916394321c3ac8b1ca190c5e73d9150c862eb9ec8a86430f9d3635432187ae9b1aa190c7b7654050c872731ac5aa443479cf54952218bce7304a910c5d73982548868f39ec8aa4430fdd95415221a98e6b10a910d1e74d4e538861f3a4c129c430f5d26094e21a3ce9b1aa710c5f7654c538863d386cba1c431e5c365d0e218f4e1b2c8710c7970d96438868eb9ca821c43475d25310e21a3eeaa188710d1d7550c43886c63928621c43539cf54d0a218daeb3068510d1e73d52428861f3b4a8a1443879506350a21c3aa831a8510c3d76d50428868f39ea821443631cd4210a218daedaa08510d4e73d504288656bb6a821443639cf5410a21b4ce3aa08510d2d76d504288716bb6a8214434b9cf5410a21e1ce7aa08510d0e73d504288786b9ea821443c99c75410a21a5ae1aa08510da6711504288696ba4a6214434b9d44310a21e1ca62188510ccc735844288674382c221443339ce6010a219d4e03266510c6d75983328868f3a6a71944387192534ca21c38c8a9a6510d8c744c832886a6b9ca8194431b5d8540ca218daeda986510d2e74d4c3288666bb6a619443639d3530ca21b8ce3a986510d4d76d4c3288726bb6a619443539d3530ca21e1ce9a986510d0e74d4c3288786ba6a619443d19c7530ca21a9ae1a986510dc67114c32886a63ae8619443539d4430ca21e1ca82186510cac745843288674382c2194432b9d2600ca21c5ca8b108310ccc7358841886573a4c190c43339ce60c86218bce7b22a110c5d73d91508861f3a6c6a
  | 19 => 0xd298a4a0d6a7094c52506b4b84a6292831bdd95314941ad6e0a98a4a0d687054c5250697ba2c6292834b5d06314941c9ac6318a4a0d4f7358452506a639ac2292835adc16114941ad0e0b08a4a0d4f7350452506a639a82292834b5d26014941a9ce7300a4a0d4d739805250696ba0c0292839914a61909418bcebb1a84a0c5e7518d425062f3b6a6a1283179d85350941c9ec7a9284a0e4c63d494250727b18a4a12839318c5250941ccea430a84a0d8c735084250787a9a8421283c314d42109418f6e0b2c64a0c7870596325063d386ca992831e5c3654c941c5ec9a9264a0e2c64d4932506a739ea4992838bd90524c941c58c829264a0c7b70594325063c382ca192830f9d6640c941c5cc829064a0e2d6414832506a6b98a419283539d5320c941a98ea99064a0e4e654c8325072632a6419283631d1320c941e1ea629482a0f0c5314a4150716292c120a8317dcd62d41418b8e6b16a0a0f4b53d4b50506ad39ca5a8283565ce52d4141ab6e6a96a0a0d587354b50507a5a98a5a8283d214c52d4141e56c8296a0a0f2852907505069dba2c5a828356dcd62d4141ab0e6b16a0a0d5b7350b50506ac39a85a8283ca50842d4141a76e8996a0a0d38744cb50507a499065a82835a9cb61d4141ad2e5b0ea0a0e4e63d4a5050726b1ea5282839398c5294141c9ac6294a0a0e6a62d425050734b16a1282831b9db5254141c9ec7a92a0a0e4c63d4950506373b0a4a828393d8c5254141c98c6292a0a0c7b7654050506b5b92a0282835a1c95014141a72e1208a0a0e6a65d4850507a5a9ea428283ca59352141418f2ed290a0a0d5a7394850506acb9ca4282831edd95214141ab6e6a90a0a0d58735485050735328a428283d2d4c5214141e90a6290a0a0f296414850507b02968228283cad4a4114141e50a5208a0a0d6a72d9050506b4b96c8282834e5d36214141ab4e7b10a0a0d5973d88505069cba0c42828356dcd4214141ab0e6a10a0a0d737150850506b838a8428283ca5084214141a76e8990a0a0d38744c8505069d3a064282834e5d03214141e9264190a0a0d6b7250450506b43928228283179ce60948418bae7304a420c6f7654852106a639aa4290839358d5214841cd2a4b00a420d4c7354b421068e39aa521083531cd5210841b18e6a108420d2d75988421068e39aa421083631cd5210841a5eeca908420e2f765484210787b9aa4210834b1cd5210841e18e6a908420d0c735484210697b82a421083271cd6110841970e0b088420c3d75980421064f39cc02108387d94438c841e18872946420d4c7354a321063d380ca990831e5c0654c841c58c92926420e2c6454932106a639aa4990830f5d7640c841974e1b206420e2d6510832106a63aa641908393d95320c841c9aca9906420d8c744c83210657394c1a08830f5da5
  | 20 => 0xc64951320ca67bb2a899065331d9544c832d18c8aa264194ce76151320cb46320a899065c3550544c832d18c9b0a641954d75985320cac73a4c299065635d2614c832d1ec930a641968c64985320caa7baac29906563dd1614c832b18e8b0a641968c64585320cae5b82c299065721c1614c832d1ec830a641968c64185320ca673a0c299065335c0614c832d1ec9b02641968c64d81320ca673a6c099065339c7604c832a9aeb302641958e74981320cac6ba4c099065a3192604c832a9eeab02641958f74581320cac63a2c099065a3d91604c832d18c8b0264195c771581320cae238ac099065a3190604c83299eec996a21958c744cb510ca663b26528865631d13294432b88e2994a21947b70592510ca3c382c928865c310c429443287ee8b04a21943c74582510ca663b264a8865631d13254432d1ec8992a21968c644c9510cae238a64a8865b24cb6054432d9264302a21963b64d81510cb1c326c0a88658ed906054432c70c8302a21966a72181510cb34b90c0a886533dd93214432b18e8990a21968e644c8510cb46b2264288651ddd95114432d9265300a2196c932580510ca67bb265a8065631d132d4032d1cc8996a01968d644cb500ca67bb26528065631d13294032d1cc8994a01968d644ca500cae5b8265280654e9d35094032c70e0b24a0194cf764c9500cac63a264a806572dc13254032e1886212a01943e74185500ca1eba0c2a806533dd93214032b18e8990a01947b76540500cba4992a028065539cf5294b41ad4e1a94a5a0c6f7654852d06c639a84216831e9c3650cb418f2e1b2865a0c7a7099432d063cb84ca19683535ce520cb41a9eea99065a0d4d754c832d06c63a264196835a9cb5094341c9cc7314a1a0e4e6358a50d0726b1ac528683179cf62543418bae7b12a1a0c7b7654050d06a739ea529483179ce6094a418bae7304a520c6f76548529061ebacc1214839318e5250a41c98c6a928520d8c735084290696b94a6214832b5db5210a41b1ce7a908520da671d4842906d3388a421483271cd6110a41970e0b088520c9e73980429063d386cb194831e5c3658ca41974e1b206520d4d7394832907173288419483c394c420ca41a9eea9906520d4d754c832906c63a264194832b9ca60d06418bce7b12a120c5d73d895090717b1084a84834e9c341542418f6eca80a120d4e73d9352506a6b9ec9a92834b5d363d4941c9ec731ea4a0d4e73d8752506a6b9ec3a92835a9c361d4941ad2e1b0ea4a0d2d7418352506a7398c1a9283535cc60d4941c9cc7a94a4a0e4d63d4a525072da9cc1292839ad4a6094941cb6a6b04a4a0e6b52582525072da9ec0a928396d4c60549418deeca90a4a0d4f7354852506a639aa4292835adc15214941ad0e0a90a4a0c5e73980525062eb9cc0292839399753149418dae
  | 21 => 0xb87396a821c65479c75410e32a3ae1aa0871958e72150438caccb80a821c65879516310a32b1ae4218851958c73508428cab4b80a99946587590439463287ce8302a31943d74181518ca3bbb2a228c650fdd16194232878e8b0ca11961f6410d508ca3dbb2a0284658e5915014232a5ae5b0ea89953a70d87544ca9cb86c3aa2658ed8260d5132a5ae4306a89943f76550544ca3db82c22a2651e1c16115132a74e1b10a89953970d88544ca97b92c22a2654edc16115132a70e0b08a89952d72184544ca9d380c22a2654e5c06115132a5ae5b00a89952d72980544cb1cb00c02a2658715263d0932c38a8b1e849961c54d8d424cb0faa0c6a1265871506350932a58eaa10849958c73508424ca1f3a4c1a8a650f5d260d453287cedaa2a29943e76151514cb1daa6c0a8a658e1536054532c76a8302a29963854181514ca3bbb2a228a655c1c1511453287ee8b00a29943c74580514ca1f3a4c3a82650f5d261d413287cedaa2a09943e76151504cb1baa6c2a82658d1536154132c6ea830aa09963454185504ca3dbb2a0282655c1c5501413287ee8b08a09943c74584504cb35312c1aa0654e9c35495032a74e1b22a81964c63189540ca1fbb2a82a0651edc161150328f0e0b08a81956970d53420caa6baec7a1065725c063d083299ae730e84194cf73583420cb0eaa4c7210654b5d66410832ad2e1aa0841952d75950420ca37bb2a8210654bdd95410832c5eecaa0841970c73550420ca9638aa8210654bdc154108328deeab1884194cf7558c420cb27baac621065331c5631083299ee0b18841964d65d0c420cb86aa686210654bdd64310832c5acb218841958e7390c420cb46b1c86210654b5d44310832c5aca218841964d6510c420cb873288621065a35944310832e1aca218841960d6510c420cb4621cc221065a310d60108329d2e0324641946d7694e320cb473268719065a3190438c832c5ecbb22641946d75991320ca573a4c8990658bd94644c832d1ee6322641968d73191320cb16324a699065a3192534c832d18c9a1a64194ce7690d320cb463248699065331d9434c832d18c8a1a641968c6410d320cb26baeca99065339d3654c83299ce3b2a64194cd70d95320cb273b6ca99065a3d97644c832e1ecbb22641954d75991320cac73a4c899065335d6644c832c9aeb32264194ce74991320ca473a4c899065339c6644c83299ae1322641954f75591320cb46b20c899065a39d0644c83299ce232264194cd70191320cac73b0c899065a39d8644c832d1eca322641970f65191320cb47ba8c899065a35d4644c832d1ee2322641968e71191320cb46b88c899065a31c4644c832d1ee0322641968e70191320cb46b80c899065a31c0644c83299cedaa2641968c64d51320cae5386a899065725c3544c832998ed2a2641968
  | 22 => 0x285569c35394c428beeca98a62152d75d8a4310ad4b80c5218852b5ca6190c4295ee4b0486214af755884310b17baac4218852b1c56210c4295ee0b10862143d769524210a36bb4a921085a398e4390842c3ecbb1a842161f6518d4210b47b90c6a1085a35c86350842c9ecbb1a842164f6518d4210b47b20c6a1085a3dd06350842d1ca831a84214ae76d0d4210b4631e86a1085a318e4350842d18c6a1a842162d75d954210a5739ecaa10852b9c7655084295ae1b2a842162e76d954210b47b2ec6a1085c3d976350842a5aeb31a842158e7398d4210a97baac6a1085a358c635084295ce231a84214ad7018d4210ac73b0c6a1085a39d86350842d1eca31a842170f6518d4210b47ba8c6a1085a35d46350842d1ee231a842168e7118d4210b46b88c6a1085a31c46350842d1ee031a842168e7018d4210b46b80c6a1085a31c0635084295ceda9a842168c63d4d4210ad5386a6a10856a5c35350842958ed29a842168c6394d4210a563b2a6a1085a318d535084295cec29a842168c6314d4210b86a98a6a1085a318f6150842a5aeb30a842158e739854210ac6b9cc2a1085a3d8e6150842d18c730a842152f755854210ac7b9ac2a1085631cd6150842d18c6b0a84215ab705854210ad4382c2a1085a3d8c6150842d18c630a84214ae731854210a56b80c2a1085a3d8f6050842d18c7b0284214ae73d814210a5738ec0a10854b5d66050842b1ce7302842158d739814210b4631cc0a10854bdd56050842b1ee6b02842158c735814210b47b1ac0a1085a318d6050842b4ee2b0284215a4715814210b46318c0a10852bdd942d4442b18e6a16a2214ac7650a5110ac639a8528885691c542944428f6e0b1ca2214787058e5110a2fb9ac128885171cd6094442958eca12a22158c735095110b47b1a84a8885a318d4254442b48e2a12a2216a942d815110b54a10c0a888596d8f6054442cb0c7b02a22165b631815110b2c318c0a88858e9d06054442c72e8302a22166a721815110b34b90c0a88852bdd94214442b18e6a10a22168e635085110b46b1a84288851ddd95114442d5285300a2216a9425805110a57bb285a8085631cd42d4042d1cc6a16a02168d6350b5010a57bb28528085631cd4294042d1cc6a14a02168d6350a5010ad5b828528085569cf509404295eeca12a02158c735095010ad5b8284a8085179cc61540428bae630aa0214af765085010ac639a84280851edd95014042e5284a80a02164d6398b548ca3db82c32a4651e1c1619523287eecaa0a91963954580548cb26b1cc42a4659658e6015232cb2e7300a91963a64580548cb35312c02a4654e5c05490e3287ced2a2871962e54189438cb16aa0c4a1c650f5db5410e32a72e02a0871945d76d50438ca4ebb6a821c65639cb5410e32a3aedaa0871961d76d50438c
  | 23 => 0x2800200700100080340060010004006008000800002c009000801c000000002800c03c005003002000e00000000140000040000000002002003800400000300c8010000003000800c000000000801000e0140068000002000000800000a00c004002400200000080000060080000010020000001000000400000c003800200d0028040002000008800c00000000000040100000018000002009000803c0160040018004030004002000c00200c001000c02601e001800400c0100000000024003000800400001200000040060000008000002001001001400000401100000160000098004028002005000000400b0030000002008003000800e02f001000007000100100000040160000014008007002000400c00a000000000c00200c0018028001000800000201800700140080000000014000006000006c000001000800400a006000000c0000000010048008003000002000a000001800805a00c000800400800f0008000002001000004401a00100300000040170018014008002000804001400a000000000200000400300120020010018004003006802000a00c00000180000090018044006000004800400400e004801000c0030008014000003000800000200000c8028014001004802800a01500b8078016001000004400a000006000003a0000130090036000004000002c00700080100080040068008002000004000400c00600000040020050018094000030002000800400f0078010002000004003c002000029001802800100280040080058f6e0b0ca7a14787058653d0a2fbb2a629e859654d6014f428bce6302a3a145d7318151d0a3bbb2a228e8517dcd61943428b8e6b0ca1a147b7654050d0b2cb1aa0286851edc16194e428f0e0b0ca72145f7654c5390b2ca9ac029c85179cc60546428bae6302a321477765445190a2fb9ac328485171cd61942428f6eca80a121659635405090a8eba6c3a9a85535cb61d4d42ab4e1b0ea6a155970d875350b2db04c1a9a85475d060d4d42a9ae4306a6a145f7654c5350a3db82c229a851e1c16114d42ab4e1b20a6a155970d905350aad386c429a85565c36214d42a3ee8b08a6a154f725845350aadb82c229a85561c16114d42a3ae8308a6a154d721845350aad380c229a85565c06114d42a3ae9b00a6a154d72d805350a8eba4c029a85535ca6014d42cb2c0300a6a164c5398a4350b27a98c4a1a85179ce60d45428bae7306a2a145e76d4d5150a2f3b0a6a8a8596d4f6054542cb0a7b02a2a165b531815150b2c298c0a8a851ddd95114542ae0e0a88a2a145f735805150a2e39ac028a85179ce61d41428bae730ea0a145e76d4d5050a2f3b0a6a828595d4f6154142ca8a7b0aa0a1657531855050b2a298c2a82851edd95014142ae0e2a80a0a145f735845050a2e39ac228
  | 24 => 0x1c00000c001c004001004800003000300a805c072014001001800400b000000c026021001003000002d003800c00000200100d8002010000000402600b001804c006005000004400a00000200140120000008008002007000000001a00d009000000e00000780380000120000010000007000802801200001a00000020070018018002004002002001a00c001002000a0000000068034001000000800c0110008004012002001000800c000000800000000e001000000400900080080000050018010000000000002000200e001001000e00a003000000201000080000040040010008012003001801000000a0028000008002000001000a008002001000200600100040020010028008000002000000c064017005800001e009000002c0020040030030006006005000c0060010008000004001000001c0000000058010000000000800801800900380280000000028000006003004000000e0050000014000003000804400201500680040020070030000006015005001000c0000010078014002000805c00200e004802800a000000000401e001000000401400b001800001a00000300f800a004000800000000e00280040260010058008000009000000000001b005003400e000000001c0000020050004008006000001000200000280dc00001500000000020020030034000000003000407c0020008010002001002801800400a0030008000004000001400a003001800801400d0000004040001000800800a0030010000006005000800000c00b005001c01a00c001000c00401200200000040000040010004000005002002800c0020014004007001801c00202c000800003001c002800c002006001800000601f000800c00600000100800040000000004008001006800400c0000000030008006004800800800e0000000000005006800400601300000440000240000000006009008005800000000900240020040048000016004006800001800000480140020030060008000003000000400400100c00140120020000000008003000000c002004006009800400200100040080030000000008003002000800400600000440020150038054004000007000800600600a001c008000002000800000b0010004002007002800400600a000800c02a0010008004000003000000000a000000001001200300280080160100070008006006007800000c0010010000000000002001c000004002800001000d002000801000e000000c00a009000800800800000b801400000b01a001000201b0070000008021000001400000e001800000400100000100060030000050062000000000400000000b00080000000000010020003000800401200800000300300020000004000005000000800e006000000800c0010000008006000005000c01200
  | 25 => 0x8a981e4000ce285b1af3c39e5e1c30559b78f9491500000000170931a1000054f00000032c9182000000000028c51200019b1e4611580033188620000000cb461e00000016b211476700000000005410002fe157825faad8000000390001c000000006000000e0020048008002004001000001800000200200040080040024016000002800c00c0000000040010000001802c0080050000018034000001002801c000000801800001a00b001001a01700100000040270008000022000004002c002001004803c000007000000c004006000000400000100a000400600400f000000200a001003400e004003800800c0010000028006007001802400400000180000000000000048006008004000004c00f000800400200700000040000000048020030001000002400e007004005c00000200800140020010020004012013004803c01e001007000000200a003800c002000000001800000b00200040000010040000002001000801000c00e00080700140030020014022002003800000a000000001801000100080080020040008008016000007000001c000015001801a00b00600100040020000010000000001802c0000000008034002019003000802000e007000c000002000000c00e0010038000000008002000004a00200000040160030190008000001005001000e00900180180040010048008002008003001800400000500180060050030008000001003800000000500000a400c00a0028024002000001000800000500480040000040000000008001004000801e00400000340000090038020006000001000400600a03380380060020010000002000002800000000400a80000020010000000006000001801003a01f005800400800000080040060040028014000000001811800001100a800400c002005002001200b008000c00a0370000004000004003801000200f0088008008001003000c00a022000000801e000003001000600100000000040060020004006009002000800c001000800c01e006000803800200800c0004004000005000000200101980380020070058000000000002800c006003006001002600000200040100000008000006000007000c004000001000800c01d000801000e0020000094000005000000000800300000140000010008008006001000000000000400200000020070020004000002002000c010006001001c00600300080100120010040068002003003003c00200000000340000090028048002000000801c02c0040010008000005001000c014014001801400001f01e002000201b0000000002001004000800c00000080100300020000008000000000001400e000002800000000d0018014002005000000400000b00000600000000028044004004000001400c009000002001000100000
  | 26 => 0xfe2a5c00009c8002a380006584068e891469e303256b05c8103000300c67a000701d60c00000006cc00095612934e0b681a00006ab243cdc090b000181d23f00005300011505726a900000007d908e85359bc78200000017009820170000010000000000039aaf9d1d03987c602e8000000000000000000031c19a0000455e103988002e95e40014000056cf706e40001bb424067c4567855928c0068e800188cb7914e1d64000cf0230a1148dedc022f9b493232881482ee1179067000311508f588e54ebb4458ac000000013881a81e8092da36cc1aba06150ccb5b18736715d460d5efe6002dc000000318463aba060eba500000f694638a13069455c437b14da000572b54d96c4c415600000001bb3b68001a325c014a618597b00012794a60000000a828ed05f39d000071f4f685164b882127439c8000a4c050e911c139644baafea47e0f02134ef2b4c0000000004f1c0015c458caf23a2834660200000018e60004a8000001bcdd00032100001bd2c028b1bb0aa71bf21e0000000000326d110395d343980808f474575b5a42b75a3fdb818903a3f6bd0000beb4520001fd00000006be8000b130cd765a254000a9e440af44e840000772d1ddd60006f7800000000061a9e0537c6fe66b02ce1f6bb32e78245ac400026d9a94aaa043000162de00ea95ac5b14276cd200001982a45f31088001d7866446d90d74e69f715028685835501fc0558414e0c4da89255a1a2e2d793540e021b222da8509aa6336c34accbe40820ec000e1600034223c5c661a657adf26d544760002798000be1a52d1b400000018112440003778000000000e7f4d31cd028419c00039e1d544e02c71e519bef3b1d438d4bb80fc00034e8260d0d6411262d02bc033eb4a8e7c07965a4000000f4c0002a14ac658801938488ca0ba371a3e93542a195a23140feca712cda446882e564098403d6c3814ee5c827456c4b10307282dce1d88c5d1d85b7557a9053ad37bd25175d8e8e765e12239bfc8f0887db56d5ea5742ce0e0d0ca269bd4b0870b506800000056000030a9bf290cc72adc40000009b2c492c900000004fc0f50c82d0c8e7b85cf7695f25f672800000021f03742fc0000002a983d0b856e58000fe600004181148f61704398344610000022c000a800004eb00000006130ea80013600004e030cc000e62989127286400079c0000e55a265ceb8b800013d17f249e00006f040bc85a2c2bd00013e709ec28708a23d8b700000034c00000000000000000dc16810c51dfa00000018a400087c0e906fc00094416381795d00000002c6d38a36a0003ca001fa8900000008b6330dae915168446e74c9759d002df6d60000e007218001749a009e89411cb160a4892c480000000002d0c0003f8a813f10c34e9ee3253b3d3c0002ad8000000bd06ce70d00000
  | 27 => 0xbfd21080008760df3a2b23db62e130002d2012e869216136509c8144d9b71c0008281a32438f962681e335cc000000000000000000000009a8e0a78f5bf353c22227c124342416814927a00000001ef1b9800000000000000000000000b100018bd0002534000f9a00032c9824da9000000191c4b60b70000dc48780000f5400126e0006b180009904d319c2618b8a00057d31fd19700007baa3db2e46a4c62260539f0a0d4b9f0581bbe5e65c5812c70c43d22e81546f66bfabb245e7ff2b9adfcc28ceb3b83cb40c67c8062a89413e0be91a92684bc8d400004b12d853458500000007985e46c680001c892bf5d40005218000d7000000067ea645bf200064600000000370067bcd5fc6210ecb2a4a660e967b27ec78a7f771a1b11405bf7037d8c52671eea75301c7f8000423800070f7152f304d0262a1943500004ee0003d7ed7c43f00000005c51e886d1d58691b400003b58b399c223a0a99aac5ce0004178c851e06a4458000013b19e707a61de6a1635aaa430bcd64e3cd0001a72472d4a12bca0f9ade4419598fa9dd1aea49c0000004162ffd0b4e04e3d0110a36eb30000c30105000000049000025000027577320000000000000a2a0002c160000004a5897c000000293e99c00000000021c12a4d3570700615920241b0ab995384e626a25cc80400055880011ae000000069c6360000c52aa80000000002c3dd6232f30b03e97c2e8844180005bc00031a2a1c9d825ac02109967aa532c0af26000a9500003f559a5da2b680000000002c6800000014c2a431880003236773791db4e1d45a66fdbd64350d6d6f8000f3127b80000000000df09b15168e865d07d40240f83d006c07129fcec8a0a9bc500048c85006e0669030a4b8e5201d0c60001ba0f141cd98dd2538e167f95140000004cb0000000ca100034f8996d0f8001bc047c1ca00008ded72f1d827ab8c40d55e25a277bac0b6a6860ca68b4e3b094389044fdb709e0bd899cadd2625cf1a2eec4001797c0009b3f50800128c08d6f3f2f000000001f80005ac7e60230000000046c5f000097079e0001b3dd70f4e08c800116c000660498fb36e4d016b970000000000000000000000000000007ee4d2813000000036d077c0000000a380010d87dc1f4b8ad72c47e0e4ced0742af3419ed5000036b33cbd18bba0c4d609af116f99f284036c6f05250003920cda7cf1fe4000c06010c6339a6000286244013a00000000002610acdd13d39461420000197d25400058c76db0f4bc04d70f51ef16ac7a9b6800000000000eb8368000edd00018b946ebee0be80014a200077b000000000071f0000073cca4cc000000000019b00000007f50000710ed0000593b17de92c5b1d31ee8000cc071e92f5972938500240dddd00005fdd6125ab3c81a7824000c190000da4000265c
  | 28 => 0x642e286b0ef49cb0acd57c00037da12919c0006ee000092c23b23600000000000000c1400068b2038fdc22db90709606c00042f6b8a028c64738082f75018b6364dd8001d9e6513fc4898dd8d050000000fca0002cc8d0d4d481a49b47910c077300000000000007040001062a66714800114e0003c4a764000c918000000bfc00032bba940002c947c9a4131f0000000001acae9e72393b4f9847513c338af320003a0aee58bc0bb8029d2864527e1c6226c16bde70000af907cde3b9dbc0979005c35a98f5c6fe2d193000107e3f98000bfd15aa8d00037a03f02183807cc8fd6c1c46e3a4917687b00012dc0f88d63e7c62de4ab151b380004c30000002ad00000002f0b33f56aaec31db68d1f0e672667d346ae4d7c523b84c3884927f21600c0b5931ab8dba9403b000209833ef3f0979158cca9946bc0000000c30000277097e846c5c23dc000d4d0003a2c0008eb0000654000a2f319b0099d1213f30503d738bf308e08fd95e93580027ab1aa1860037144000cb130900014a894375f264048aace68c09c4000b3200024480000000000a9a246902147ceea7aa1e980000004aee8d25d000000000077aa87000059740ac000a92ed2256968d214d320003313954000000000000000000006ba28900069e892378ef411d0233c0001369c3a4c5c5400026c3d1514a5921ad00017929586b21f5800062226fb729c234b933da712dbd48f43bc1ac986d0403a40015d68170001c78000325baa80012ceb6b14c1e10460e1420980015bc1b62fdf0b1b5021c2240134000000263a27922870361bb0b5d56df2ee235dd72666e65eb54402a2f366a80000007d3596a49b5b47ccf71bbee00000000008a1d74204800000019cc20724a5902344812f3800000000066da01c00000000013a400002a19368180a203c49f2064a50aff0c980018ba5030001b44752000668ac080581ff106b2c1025a5c4d61d316ce00056b93049efbf150500002f28360acac8a0006b11c7800182489a342acd44ceb3f01350b9e9600000038e91b7551000146423ec57000000000069d00000010f1e305112dbc00039f514bc1439c3de5e2bb7800000004a2be20000000c037940005ce0bb8001d440002b50ebc0000000001ab41360006be0001b9800000004b4e9297d64f8001c8cdfea810fa1dce0000001891dac000513a2809786ac1f8ad30000a1f2b424580000001de8b840a1c8906a8a28e80de4c89a83c0539843f935ac53229992d01d5460e2354d933d1381a2c1980008bab910002c4849a530102c5e91936f50003ce400000000dbbf3128381000055481a336800006e00052115c1c240080005b08000da60005830d4105c2338b49a6800000027835b531acd4641adc135026432e39939244450aeb2584e6be21cc0f085629f30000fc00000005b4de5e
  | 29 => 0x70054eb21126579cf0007500759040acb1c552932c061d6670b10728d40595adccc69380e968ca2000ee40000b126380005e607b466b00048d8909d86a8a8001cc0000a4f0003c3400091c00010780000000000001982d4c09ac82e6582f00a8b4482180003e12da47dc8f24373b311c400f3f6898a000111c4817556120006fa90a8e449b9468971948ee4bc7f3ab82d0cfe28386e14dc424a39a931b9a3b5492074dc626e74be148d8d48750820cb93bc6c67a20864976e9f2db1ca77d2b7d15687c19220000002ae88220002c8800087095a00000017d40880000a15488000000000000019c9e180015060000000c1ddb00003530000082b20e7114ada68b924b814fc3a261f5bc37a800066f4018000774498000000171871403635640004b08000f7c0004ca3918001e36c161c0c0000000000003bdd04697b0f5f6c032ca386c308dc7ae1e15ba0ee5022021dd12d941615623e70da0a27aef2fb1274b3aefe667adec52e6c81324cdd58ab1767419743e4ee514de118ace421a612751168a825726fc8a17a744aba331484e6791b5b7589fe63952a5a402c72427ca3980c89ec5981d957f43401bb1a28f4866a069707c7b29fa63396d530ad41a682b083b43ae19221bc4441091681ae919200000000014f200029680013a00000000000cfc19b0c88de683e4a467a0035620224315b18155a013000031f4b46086eb9d1c723333136b8ce00000000000000000002fd000190a0000000000001000189c000000ef8e59b1c419e0001a71f04a1a4dd534800167c83d43d5534000da9000395996800056509289c44990f1800054448e02926a31a96cb3ad8001a5c84480025780002a977fdc4c5c615f405a63829e09e0000188950afc0000000be4a5d6fe296000003458b0cf0d6602f0ca00005f0b68576c484000e19000000021100000000013f2b1f480326401317b04aa3b8aa65eb612000034000012c7634f3e06d1b02d00ce81580370001a423ab8000000d840003e4bb192640002e5a80cd36df60002648709bc600025b800064200000017da0001a58fcc6596ca00000010108a242a2048000e7b0002d616b90000000001c83d3580018e40000c708940000000000000000840e43640379600000055b9e700001ede5b8000de98fc65dcfd794d01a302006b3534c60328eec48827400010dc000000000080a000790000379a4de216392acec0007b2000046b9d4471586b2715a2522800185c48900040780013aed760788000c9000000000000000001a40000f6a5930000fc80001e00002340c9611e0000b300000005cab3b56e2bd42ed80003d98e90001cbc454ccec9a898400005413e615c9f49ce6cfb0c973000000004cc14287459c000000038e80000000000002f83894f5c72a6324000a6a9c5e74aa28000000455ebc53d2031
  | 30 => 0x2d7800033f15b1a0c00000073180017280003cb8476c40214ab880012340000000000000333f7cab6d4eeec16c4a74c00025e8003af57620000082f6ad8e00050a40004a72abc7537f39ce00016a800000009480000019e2cd35a78694204a01e9319acf0a000411000170446f800000194bdf765940010a02920003334d7a47d79b0000818000000356000008943f0c199c0000000000142edba3163718ef00002d5dc04420c415eb05c99f6a9d6e18e28ab8bcb73880018c63a543387d06684423fe000000000000037480007da000000133a00000000000000001ba80000000002de349c066f27115ca9d2c61835fb00008bc00000037b4000c6f1261d98dbe8405320000d9a7f01a49f8d5760d200000017ba00000028b4000aac3d8a6ac45699528616e800037d05787700008c400000000000000000000952ac700000015e96dc00016d007400006040017b44b3800000012b34a000109582600040cc001e680004e49c100000005089d510310000d1319853a00042180001ce0006fd000000015c16b8030acb000651400013a419741b14a000ac3800036a000000000000179c378800000021437a76c9ce8d98cae00000000000000000000000aae0000000324de62fd8000397920b3a80718e7b894a100985280866923bfc5f86c35c685d8fa7e752319c5db5ea013e227216403b73218c29c9eed7379b6d882cedc78f4fe4e107722e080015aac7c3dfa7c9a0653800005fd496d2877a0805630e1f095aca40b0d50503a435a9298a429c0019e60305b351f1d58d830e0127cb41e8272e9e0c0007c70340488e66ed553aa7ad9503830045d1896033129926802907c8d691d7ab5326307439309a285e0001da8000000000074200000000000000000003ccc0000003102dc19dc6fe496bd4a5c4bbe7ec3260001b3c7ac02b06850646b0271a11114c0006a5800000045900034d242d0000000fd443a5c213d940516625c37e0c805827e8c1222e498a5781f60209c9c66259d43c9d72ee800003580000007058001948c17000012c000cf75a20000000e3672801c548c0cb800256cfb02d47340bb80005442f50001958829083800182a00000033e85340002f3f16b2e562761717b400055914a998452b00058413b80005c839b1f9c000020000000147a2076fd80018b95643edb22d5ee75f2d03b38d46e2c0b237f63e28f378b816c49c0fe00038fd10a69629d363c0000000002e3cfa443900000002913bfe533ad00000503bd171c6aacad6d103d1be8ab37203bbd29a5d32d691a1ae007d05123bdb241c703bba90ffd007466ad446060000000000ee80000001f7400039540f142809426b63b800090a2bc31f24840003ef68140014c00cecfb17787a654c0000c4600011780037ab1589043d44000ce700006310c
  | 31 => 0xb845caf279d21a6aac2f545f91a4eae00019a6c4e7fc999c60317e1080d8705e4d0000000026e37800000000037c6ed2000559395d6b83bc39a8d89920364012a6854361ec04d22ce000b190001ba4000c9a5282a4064700000000008ccb6d0002f6e000570510000000000000000000000000000000000e8c2d58bec0005170000000b4e7200e7c000000d4e00000000000006eb1ae02ead0a000335c0000004a020a7be04b118f80018e41c233f8001a884530fe9c49e60e271e0dc980aeabd1f58661c3cd743dcbb20a1cca565f53018b22db1b18000b5559be8080000000001b28001ca220558a17dcacff4012ac00110e000370ba6d23e7c60000000ea22ca2722ae120e9ef051a62400000012b54587b64770e7675ed300001be21900009fd4bf3cb0ec60002ffa46036ee3c0000000000cbf242c34f83c9bd4f40964f97386c3402a49f611090d3c7db762dd3f4abf4e861374dc51908007f6bb730341d4119f259f14549bdb68e2e5ca0510b43b8b00fe228d7448e143a00b51924ba0924422f639760c60dc25e7a0d5a34215000347c03c0000000001da000053d00015d20492d407e480c0003cacdb855ccd8020c000f6e000000350cf68e163d83a1ccf060e0593ad483a0005cf29f072fab62fd6aa0b08645661d66c89ac52052b4540009ad03a00000001d28003cf8000c2f6022b805744b516901021de66357b3bae000c65be8210a5010691199ef5b309204ef9def2b8b37000304417c2361b7b040be819728827908800004d7522807a00072915083ecd9a6df2879368e0166cf1dea2215705a7861a4644909380007da98ef06c3b1e5208e65bc0012540000000d9826c00000035ea56a00000013ccf560001c5da5dbc35a200002b1d468df4ed9ecd8ea9e50990f106ac7d585c30f041c99e297a4ca4bb8895fa953d1846f771c80002cc0005dd808800000059e120c99a2a0e17730a8e409c161ba048f4ae78664b0fda84800609a3d3e500028f80013640e106a000198a0003cb41697debd7f7d80013e30005ff00000e4e8e1382ac1ac200000015533260006c5b6e14fe0000001f78000e070833520a761cabd78001a8e00000025e826900047e988cf22200098c0e01fe00068f0c6083111374d08b29b4f1e0002c945fa32700000000000006f9a8c5cb05945420aa8486526612a30c64f71100012898da4a51a880016261c80ba3b8015c07a4e68001bf155a62d31a72c2000446328e00000056b0000bdec87000151800000077e0000faa3296f18aec1160000010b654acb222e629f944b11873626be00c00000036040003d2067c00068e00061d16dadd01892960389bfa0590f4ba9d54a160730a0382008911108ee00003bf2599c8a44e00023020ec7262e96ceba11abe62f10580009462d173940009ce0000ea341851e00
  | 32 => 0x75b31358dcd3f0002eb8602a0c0001e85956ec2445962a0005098000000bc68c5a9b929d526e34bd1b0980000001e0b24aba2393f9999c8b45000199000000063c65f0ccb0ba00000030ac644c310b0a24d3bfb3d8001dd83fc508a3afd0c10fb0363c95acfc20dc65aad19e02d6a6fa66bd876e380001490e960003c9800000015440a800d278c0150a000000012e323356d0e40000003b9800044777d0000404f0b47b0000000000473b6117f6570e058000029d85629b051cfa2321408001c20e1b2d48ffc166c76000183c000c554cd046c180dbf5a0800050800050200006b60006da3b4db206490e28d518840a82d8b6b540a304177a1e44fa4cac880b98516258000000026a0002df940f6623da6dcadd40004e8000377bde2b0b675ebd06ed47f383302465b9e239386e4b632e229021f32da3846e2b019861540abd83ac82e57a3c335b8efa2eb7579b9443e75c38c02d9e30de9e1fa45cf5a2f95f43c497b0e6a44b94518d2c215b327a9450b65839d614000ebf4ec0001bf7b3648f6fe400034125b6d80d2414e00000ce06a523e0700000008cad3ea126000178000000069e947069af5c00076c3d280006165bac1640019b80003eec249ce01017333438548bce8ef27803a7f01e430436eea2ed2f62348383db56a28f98267cc80c6800096ce021750290000b500a095f993c29b015b394000e050001ea1afc00000000000006602c50000000d0ea1d000000000053826c4d44043800343763a87ee5fea8d29876057393f5774e900002f70ff200000000000001ac36d80000000000ed99359402f16aa319486c0004a88000000d0bb292a7c000eed4210000000000774b7a42d83ce1fdbcf513ee6d4edf444f2457900022c4c2279b01ec0000f6a3600007339b2000466582cabee0a5511ba8e50000029800000000000000000001cc5f820b4e72b0e07ca34c000a964b64001bb20003bf2a4400044419cb3989a44a980000015520000000a59426c6c1a9038c5500001a62eac000d466ca8e3750c0005f3ac93cf2000219b15a000e222fc2fa2a8e4845ab98619b71c94083b44406000000000094200073340007fa00000017b84b700000016cda4acd1c5f73e0df20006a0ae3800000061c800025f6c046e80000000001c70ac279ef1c00029796ec29f000030f0563aac7180001bb08c00022ca00007600017240008d96bcb060886ef00000b2058a20f0002709e9455d4b2832bc6eba43c34ce8e1c0a728e9e38625bb26fb4a2430ee6f35398a9cfc816255360139eb0040de0704cc43d48e96e40005a78648c940006015cf800196bf376c3b574e04e5556c1d7992a6fea93b5ed20cca33c5087a07dcf5000362159800a63db23566650604cbc5495849e2250000e9a90843f8ecd27e04244311d27104e3cfaaa805ee000204a6
  | 33 => 0x731d6084b2ba8000000000000000000000069bab40160d083bcb578a03b39086ae6c713b866fbc0000006260002c05aaa8d3b00000000077f00008e5814bcaa2b97354103e76de8de5d2e1654264efb686af9110eca07ca42959333109e20000000f1d1fe73f70e1452000edf5d6a0dcc32000000000000068e4402d68a253fa80031600000000b3bbb943ada4000125c3ab3b2679000078000000039d125e8fb73119695e09b65adc001bb6956000100dcd26447651208d00e5a93c800038cb535392d146222544dc009d057ccc1e88a851ca58dc55bac8d041e60239a51d3a8d9dd6045879a48d29b1154bc494813fa5a004b00049b19da8b8ea86ffa8c847800019419409920000000dec446478492706d04e00075d9cf56182bf083c000172d3c43dfa61b5c8aa6d331f9532000000312035a61b3a237e18968b535921944ec0112d52f643e62cd000225976c0000000000000a5b00036ac00000069004f9a587e800000009f052219f127011ea8c0000e65754df17950fd8d5cbe3a57194c59e7620001afc1946e635d8154758110375b63918e68d27b050d49a53e257e14c3c4e3bd1e0000000ef85df881965ea234f3922c00f41fc293150e6e0007034000daea5520806c523c000294ab90f3a044a8489814909cb56781c3a44b7a25f186f480000000252400000024db7b20009992bf80000000e428e01975eade0cbb11e51b087d2311014f443e13ef4e68302576195067442f2135362948a94e003332b0d22271f5cd0000963ec56452264fde1af67e2d8ca783dd24dcdd1e561d85a50900fc864f128aea42da52a62509180006c16f0b1e26347b998c91c054c1445b6311c000855627032c0005dfd6f883090ebb000039767c004e4bf8000adc396800004a73cf0778075a117a9b740603ef317c93000342cd5000000006f0b7a31568a13f0fc06382cb1c83c0668972d0448000e8f78c9d58000ea60610eb60720001d5000000000000024a0368b4b378ab715900006f6c0012cc9d1000313c6260bf00010dfd2c7533e180000003d6000000000080500000017a69bc6585a4c000a0b4932bed3da00022812c872e70f000265342c7f86ae3c3d185bd020a2b64de8b6200023d597688a042a0181b2471800000000018262b000174e423800303ce6400044100b69bc5a42a90000000c6b77517413380000000000000e4a0003884000be6000021c00000000000000001b3000000185228300011accb6dc9000000141ca613feb7b8396000216b867c84126782000000038010a000053fd0f00700007d40000002ddc612b840000000b6400000000000009fe0000000f0eb6e0001330dc43cc28aa88400084b800254d202bdee98a70cd3c00000b8989b4ed99100f77e00042734c8001bc497500001a80000006c60e8c55e9a948480000000
  | 34 => 0x5ca61108f4c63cc23bba00400021700036a97948bd800112cb3c96b614c00191ccc3650c6ad84641a779338c000c682f482f1b64000000000000078c45e1a3003e0006151c7f030000270800000026e800000001d6be00034d807c31e1e52234d4012a41c9dbc5b06d652f889b54216f524a9acdb218812b2769b90de06320001517d5a0501c64a96cb8e99a704000e5e42638fa72209003f0ef83ce0003d51951788b2332a800000011700000000003866a84000a7ab2c2beb1400000003fb0f2c0f03909592a20d6c28e4c41814836000000302ec8000b000355c00042b000000092f731000052c0000002be36858882ec6219ed3e26e5b5270ed9004e6b3c6a0853870e50d707ec5e877105e800115c3f4426cf25524be536a253ddd82ab0001878071316000000084b48ac35a00141aa450003cf0b348c1eb4800175ec6eee78a444a64151a2800000000000000000005900003c450600800000a79ca659510225dc3642410002d5689c60655c8452df4000123a3280000193908514a1e000000000000039c00032600008e402ea890b0e95959d000015a0005d4000169238d5970ec0f4c40b3814000a2bcf90000000b3800028d0e90aee6a92532cee41581d36aa529e2cc9d3ca88a40000006c523b57bec36000265d2e8876495a808947e2f42098a00002fa7101241a9d6ef5d327c4ce0f030cf6d914de0000e09f5000044f4b50000dfe00000010c02e68a155f80016542cb1c59028e5c0000fba854bf2bcd0662b11baaeb72ec80000008c48000eb56220006cb00016e4e4400008d00000002ac0001c8a2e00003a4c34b0000000001702f24000260400071c4fa2e1d7d615e0398000531aee0ffd58400000041a000109072b0148000beaa780000100a0be5415c9ff9a610158002e2c0008b746d2f792a8cc73be0000000c018003509ade54e114400042500042e216400010c800000000000077116c17c00000000346000ca8e855130000bf409f8000000871092aef000009f904b608547cc90f440b3316e262d8632cce65f1233bcb8660a623869a7cb0c7df3cb18fc7c48b080010d209095d22c06100000c8c9d89a4928f1a0001bc93e000034411197aaa3e702c0000000000000001b28000027e5bc00000037700000009d2250000129ca3549e800000003a80028cd1df0000001894354bfc46408788820003df1d85e0c780404b76931ead358e00ffbbc5310000000000ead00031e0846000482a381898a390000000aca81f4dd00000007fa6949370ef6ba313a808dd0a8a90003124470bb560d24974b26c932533bd768bb778e9038000ccb613955c000e9c4917441344ceac3196ed9d828700008c44617d74d21c6c000000671f369d0c0dbda689491af89d70559ae0004745d08dc99a00004f5c0004e4392458c5ad2580006b92
  | 35 => 0x134e50528583781bd845b96bd09c08f2200035e69ea1fa0003288918569000000046565e0001d910c41087370db5ce435f383aa00c5a000333944c2f80000001d418cd5fd1800cacb5c5c300029c4162c61c9186646573350cfc9557c81dd4cb445000000902ef59cbca000421f64cba80000002754149b1e800399545671a2d3566000092f8879710848a34606052802db34739a824b422d3112617c8301900ad276758c0002b00f203a90002008001e90da500032ebd925a527f800045a75262010712602dc009c0009ac97942c65540000000000000eba26e0dd06d56429a35e09a1ca8658206ba60a0be8251b637cfe4c3a72b7a7fd25293350900004402c60000000000df08000d340000000002a6027299b800000115ece41a98000000493282000000000045ac001be40002090000d688d69bb926753400050c2fb1a7053ee9780005538aad8f3c30000000459167e3dc0000000000000c707320000d6edd30000001556bbd28f19d8e2053956a00000000000000001e2078b00019e97c6000689a04dd2a0000002be05abd3b01b030c7c8212570a99533166fda938ea9e41385e18eb2acc0000000cedd9a9d88f2a719cf445100000013f163a000359805560c2c78894f350f30000a8c00000065259a000000049cae0c00000000000005e4ddd3e884140003d821a063db78e0d0000000500b040769f000000005e90000fd4ec0442000000011eba700000004284e383c0df000027280014868b8932a362c343f8ba409e8000c0500027840000002971a540000e061f204600083a1ee02ed2f00005a7391e0007b660404386b2e41784800000000037e85a800059f2fe39ddbbe00000027b9b6643f2801c28aa8037ad31c7400099b61a0000000d6c06200840006d78009e201ecaa44912c1c7f49255be32e1a0ec5c3050adc1ea
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x1320ca40c0d651d1320ca40a2481594420c940a0c835884214540a0c835905208540a0c835944208540d207214541d0140989801d1320c840c24721855150040c31751864150040a0c825cc6454f20c0c731c96414f20a0c835506250f20a0c8454c6250f2081c875954310f20c0f651c94310f20a0c835526290720a0e83d944290720a0c8454e628c720a0e84d94328c720a0c835506250320a0c835506250e20a0c8454c6250e20c0f651c94310e20c0d651c94310e2090d851cd4210a2090c8754d4210a2090d851d1320ca2090c87551320ca20d0473dc55410920c27761c55410920d07731c55410920d04731c55410920d2071dc1541092092681dd64310920924815d44310920d0474dc5530c920c47761c5530c920d07741c5530c920d04741c5530c920d4071dc1530c92094681dd7430c920944815d4430c920a0c835904214520a0c8458c3214520c0c541cd6210520a0c835944210520c0c7414d620c520a0c84594320c520c0c541cd62d0120c0c7414d62cc120a0c84594324c120d207414521c8120d407314521c812090c825ce5410c2090d851c94310c20989801c94310c2090c835c9541082090c835d2521082090c845c9530c82090c845ce520c820c24741855148020c44731855148020c6175186214802090c835c85410b1090c835d05210b1090e839d54210b1090c845cc520cb1090e849d5320cb1090c835ca5410a1090c835d25210a1090c835d54210a1090c845ce520ca1090c845d5320ca10a0e83d8a62d5110a0c835886215110a0e83d9264d4910a0e84d8e63d4910a0c835906414910a0c8458c6314910a0e82d506350910c0e7418f525091090c835c8541091090c835d0521091090e839d5421091090e851cd4210910c0e651cd4210910c0c651cd421091090e87d4d421091090c8714d4210910c0c649cf524c91090c845cc520c91090e849d5320c91090e851d1320c910c0e651d1320c910c0c651d1320c91090e87d51320c91090c87151320c910a0c835886295010a0c835886255010a24815886255010a0c835906494810a0c8458c6394810a0c835906454810a24815906454810a0c8458c6354810a448158c6354810a0c825506350810c0c7418d525081090c835ca541081090c835d2521081090c835d5421081090d851cd4210810c0f651cd4210810c0d651cd421081090c8794d421081090c8754d4210810925851c54210810c2965dc14210810c0c641cd524c81090c845ce520c81090c845d5320c81090d851d1320c810c0f651d1320c810c0d651d1320c81090c87951320c81090c87551320c810945851c5320c810c4965dc1320c810aa0825844110010aa0845842108010ac0835842108010a28865515244010c28765515244010e095418d5244010c487654d5244010e086454d5244010
  | 1 => 0x2c88639c35350842c88635c353508428a9801da535084288e8718d6150842c0f7518d6150842c8863dc16150842c88631c1615084288c835c0615084288e839c76050842c0d7518e605084288e87d8d6050842c8463dc56050842c87631c56050842c84631c5605084288e861cd425444288e87d8d425444288c8718d4254442a888350b6054442a88835086054442aa081508605444288c8798d421444288c8758d4214442a888350a6014442a8883509601444288c8798d42d404288c8758d42d404288d861cd429404288c8798d429404288c8758d4294042b08835095014042b09809944310832a8980190438c832a8a80dcc644c832a8980dcc644c83288e849c7654c83288c845c3654c832a8a80dd4644c832a8980dd4644c832a0f855c4644c832a8b805c4644c832a88805c4644c832a0d851c4644c832a8a801c4644c832a89801c4644c832a0d85dc0644c832a0d859c0644c832c89701c0644c832c88649c3544c832c88645c3544c8328c9801da544c832a0c86550544c83288e87191614c832c0f75191614c832c8864dc1614c832c88641c1614c83288c845c0614c83288e849c7604c832c0d75192604c83288e87d91604c832c8464dc5604c832c87641c5604c832c84641c5604c83288e861d1325443288e87d91325443288c871913254432a88844cb6054432a88844c86054432ac0814c8605443288c87991321443288c875913214432a88844ca6014432a88844c9601443288c8799132d403288c8759132d403288d861d1329403288c87991329403288c875913294032b08844c95014032a0e83d88425424190e851cd421094190e87d4d4210941c0c649cf524c941c0e651d1320c941c0c651d1320c941b088350842d4141b08844c832d4141b08835084214141b08844c83214141a48835496014841c0c641cd524c841949801d5320c84184c87595320c841c0f651d1320c841c0e541cd6210621a0e83d904254221a0e84d8c3254221a0e83d506250d21a0e84d4c6250d21c0e651c94310d21c0c651c94310d2190e851cd421092190e87d4d421092190e851d1320c92190e87d51320c921b088250c43d4121b088350842d4121b08844c832d4121b088250c4314121b08835084214121b08844c83214121a18835516015021a0c825cc6454c21a188454d6014c21c0c731c96414c21a0c835506250c21a0c8454c6250c21919801d54310c2181c875954310c21c0f651c94310c21a0d8614c4310821b098014c431082190d87150430c821a0d86150430c821b0980150430c821a0c835526290421a0e83d944290421a0c8454e628c421a0e84d94328c421c0c641cd524cb4084c87595320cb40c0f651d1320cb40c0e641cd5288740a0e83d94428874090d851cd4210a4090c8754d4210a40c0c641cd524ca40c0f651d
  | 2 => 0x10c40c4603cd31ce00000b0b60b128c110611f0cd21340423c02d154833c6f600000000af30cbd00000000002340002400000100000000000000b800000388ae1f31446c9a808c11bc4513c0000000001170004c01ea105495191021c6c600000000000000042c00000000004e828000007b0007a00a003780000000000e00641f0006d000d9260e822834184650490f1f8810000c000cd105052140d448b72a09a3947614452878ec3e0c027c00288001a46a04c00000800682b348001e60502c00460ff124543f0d724f07440b621a00290310700000036220ca0dc002eccc42800000000a80000000158001c800280b92b600454164644b31cbe2a4000000009c2110c1b000001ca1713e00000fd15c350100000000000001c0b226ceb1ee5222cdf1a0ce140c40f0f10010430800404db24c62088202b11e0c8fa3b4cb0005d0a4efa025f00073000b34700024400000001dc3d0c0000008e00044434590003f00000468e93c8000062800051800000b0000bc0035823000afa66972986039c003ecaa400381f4e30004ca18a51fcbc276000003a3144e0009d0001d000941780014203000f0b84b5000ba1e496b44f42c0713f83b0000e000d41ac780980127a822403941866094533d4992249c24800000000006e0503e012f719c6c37475134ea210000000000116000c83248700048000e4000001d0063e520090da25e5a1280002000000002589e2fc003b8004380744ce647509000ab23cd5001111708c3bc2e33c7c100002b40020a5b18c472d0580000029c000000042000000dc00000000f3000000180404038140a00018080000000000401018000e06028440206000280c070000024010382c06040281008110080800000100c04060000400070083008000201400010200818030d8040002000040401068242202010240c00000040201000080002028280000040000003000000000018000008000080204a8a80dc86350842a8980dc86350842a8a80dd06350842a8980dd0635084288e839c7655084288c835c36550842a8a80dd46350842a8980dd46350842a0f855c46350842a8b805c46350842a88805c46350842a0d851c46350842a8a801c46350842a89801c46350842a0d85dc06350842a0d859c06350842c89701c0635084
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 27
  | 6 => 1098
  | 5 => 6068
  | 4 => 3920
  | 3 => 290
  | _ => 0
def gbR (k i : Nat) : Nat :=
  match k with
  | 8 => packedAt gbK8 (i*5) 5
  | 7 => packedAt gbK7 (i*16) 16
  | 6 => packedAt gbK6 (i*27) 27
  | 5 => packedAt gbK5 (i*38) 38
  | 4 => packedAt gbK4 (i*49) 49
  | 3 => packedAt gbK3 (i*60) 60
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 8 => packedAt gbK8 (6+((h/1+packedAt gbK8 (5+(h % 1)*1) 1) % 2)*1) 1
  | 7 => packedAt gbK7 (510+((h/13+packedAt gbK7 (432+(h % 13)*6) 6) % 49)*6) 6
  | 6 => packedAt gbK6 (35670+((h/502+packedAt gbK6 (29646+(h % 502)*12) 12) % 2404)*12) 12
  | 5 => packedAt gbK5 (266018+((h/2531+packedAt gbK5 (230584+(h % 2531)*14) 14) % 12130)*14) 14
  | 4 => packedAt gbK4 (212243+((h/1551+packedAt gbK4 (192080+(h % 1551)*13) 13) % 6142)*13) 13
  | 3 => packedAt gbK3 (18363+((h/107+packedAt gbK3 (17400+(h % 107)*9) 9) % 467)*10) 10
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x3f81fff81fffffe07ff07c1ff83fffef88e3f
  | 1 => 0xfffffffffffffffff81fffffffffffff0fffff
  | 2 => 0x3ffe03ffe03f81fffe007fe0ffc1f01f0f3cc
  | 3 => 0xfc00003ffffc001ffffff8000fffe001ff03f0
  | 4 => 0xffffffc00000001ffffffffff0000001fffc00
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x514a42988c48968e0165415192a33954788615
  | 1 => 0x810850110912000580a0a82250442a80338ea
  | 2 => 0xaa6149aa243a42b6aaa084f489e91c0db0d34c
  | 3 => 0x33459634492074db34d3d0210e738831dd03b0
  | 4 => 0xc386183871c3871dc71ce739c04210c1eeec00
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 31 gbPos gbNeg, 0xecc8c888ecc8c888ecc8c888ecc8c888ecc8c888ecc8c888ecc8c888ecc8c888ecc8c888ecc8c888ecc8c888ecc8c888ecc8c888ecc8c888ecc8c888ecc8c888, gbN, gbR, (fun _ _ => 0), gbI⟩
end PEqualNP.Outside.L_meta_16401
namespace PEqualNP.Outside.L_meta_16401
open PEqualNP.Outside.L_meta_16401.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bgb_3_288 : Interval gbAtlas 3 288 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 290 := (concat (concat (concat bgb_3_0 bgb_3_32) (concat bgb_3_64 (concat bgb_3_96 bgb_3_128))) (concat (concat bgb_3_160 bgb_3_192) (concat bgb_3_224 (concat bgb_3_256 bgb_3_288))))
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
theorem bgb_4_3904 : Interval gbAtlas 4 3904 16 := block_range (n:=16) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 3920 := (concat (concat (concat (concat (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat (concat bgb_4_96 bgb_4_128) (concat bgb_4_160 bgb_4_192))) (concat (concat (concat bgb_4_224 bgb_4_256) (concat bgb_4_288 bgb_4_320)) (concat (concat bgb_4_352 bgb_4_384) (concat bgb_4_416 bgb_4_448)))) (concat (concat (concat bgb_4_480 (concat bgb_4_512 bgb_4_544)) (concat (concat bgb_4_576 bgb_4_608) (concat bgb_4_640 bgb_4_672))) (concat (concat (concat bgb_4_704 bgb_4_736) (concat bgb_4_768 bgb_4_800)) (concat (concat bgb_4_832 bgb_4_864) (concat bgb_4_896 bgb_4_928))))) (concat (concat (concat (concat bgb_4_960 (concat bgb_4_992 bgb_4_1024)) (concat (concat bgb_4_1056 bgb_4_1088) (concat bgb_4_1120 bgb_4_1152))) (concat (concat (concat bgb_4_1184 bgb_4_1216) (concat bgb_4_1248 bgb_4_1280)) (concat (concat bgb_4_1312 bgb_4_1344) (concat bgb_4_1376 bgb_4_1408)))) (concat (concat (concat (concat bgb_4_1440 bgb_4_1472) (concat bgb_4_1504 bgb_4_1536)) (concat (concat bgb_4_1568 bgb_4_1600) (concat bgb_4_1632 bgb_4_1664))) (concat (concat (concat bgb_4_1696 bgb_4_1728) (concat bgb_4_1760 bgb_4_1792)) (concat (concat bgb_4_1824 bgb_4_1856) (concat bgb_4_1888 bgb_4_1920)))))) (concat (concat (concat (concat (concat bgb_4_1952 (concat bgb_4_1984 bgb_4_2016)) (concat (concat bgb_4_2048 bgb_4_2080) (concat bgb_4_2112 bgb_4_2144))) (concat (concat (concat bgb_4_2176 bgb_4_2208) (concat bgb_4_2240 bgb_4_2272)) (concat (concat bgb_4_2304 bgb_4_2336) (concat bgb_4_2368 bgb_4_2400)))) (concat (concat (concat (concat bgb_4_2432 bgb_4_2464) (concat bgb_4_2496 bgb_4_2528)) (concat (concat bgb_4_2560 bgb_4_2592) (concat bgb_4_2624 bgb_4_2656))) (concat (concat (concat bgb_4_2688 bgb_4_2720) (concat bgb_4_2752 bgb_4_2784)) (concat (concat bgb_4_2816 bgb_4_2848) (concat bgb_4_2880 bgb_4_2912))))) (concat (concat (concat (concat bgb_4_2944 (concat bgb_4_2976 bgb_4_3008)) (concat (concat bgb_4_3040 bgb_4_3072) (concat bgb_4_3104 bgb_4_3136))) (concat (concat (concat bgb_4_3168 bgb_4_3200) (concat bgb_4_3232 bgb_4_3264)) (concat (concat bgb_4_3296 bgb_4_3328) (concat bgb_4_3360 bgb_4_3392)))) (concat (concat (concat (concat bgb_4_3424 bgb_4_3456) (concat bgb_4_3488 bgb_4_3520)) (concat (concat bgb_4_3552 bgb_4_3584) (concat bgb_4_3616 bgb_4_3648))) (concat (concat (concat bgb_4_3680 bgb_4_3712) (concat bgb_4_3744 bgb_4_3776)) (concat (concat bgb_4_3808 bgb_4_3840) (concat bgb_4_3872 bgb_4_3904)))))))
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
theorem bgb_5_6048 : Interval gbAtlas 5 6048 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 6068 := (concat (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 (concat bgb_5_192 bgb_5_224)) (concat bgb_5_256 (concat bgb_5_288 bgb_5_320)))) (concat (concat (concat bgb_5_352 (concat bgb_5_384 bgb_5_416)) (concat bgb_5_448 (concat bgb_5_480 bgb_5_512))) (concat (concat bgb_5_544 (concat bgb_5_576 bgb_5_608)) (concat bgb_5_640 (concat bgb_5_672 bgb_5_704))))) (concat (concat (concat (concat bgb_5_736 (concat bgb_5_768 bgb_5_800)) (concat bgb_5_832 (concat bgb_5_864 bgb_5_896))) (concat (concat bgb_5_928 (concat bgb_5_960 bgb_5_992)) (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088)))) (concat (concat (concat bgb_5_1120 (concat bgb_5_1152 bgb_5_1184)) (concat bgb_5_1216 (concat bgb_5_1248 bgb_5_1280))) (concat (concat bgb_5_1312 (concat bgb_5_1344 bgb_5_1376)) (concat bgb_5_1408 (concat bgb_5_1440 bgb_5_1472)))))) (concat (concat (concat (concat (concat bgb_5_1504 (concat bgb_5_1536 bgb_5_1568)) (concat bgb_5_1600 (concat bgb_5_1632 bgb_5_1664))) (concat (concat bgb_5_1696 (concat bgb_5_1728 bgb_5_1760)) (concat bgb_5_1792 (concat bgb_5_1824 bgb_5_1856)))) (concat (concat (concat bgb_5_1888 (concat bgb_5_1920 bgb_5_1952)) (concat bgb_5_1984 (concat bgb_5_2016 bgb_5_2048))) (concat (concat bgb_5_2080 (concat bgb_5_2112 bgb_5_2144)) (concat bgb_5_2176 (concat bgb_5_2208 bgb_5_2240))))) (concat (concat (concat (concat bgb_5_2272 (concat bgb_5_2304 bgb_5_2336)) (concat bgb_5_2368 (concat bgb_5_2400 bgb_5_2432))) (concat (concat bgb_5_2464 (concat bgb_5_2496 bgb_5_2528)) (concat bgb_5_2560 (concat bgb_5_2592 bgb_5_2624)))) (concat (concat (concat bgb_5_2656 (concat bgb_5_2688 bgb_5_2720)) (concat bgb_5_2752 (concat bgb_5_2784 bgb_5_2816))) (concat (concat bgb_5_2848 (concat bgb_5_2880 bgb_5_2912)) (concat bgb_5_2944 (concat bgb_5_2976 bgb_5_3008))))))) (concat (concat (concat (concat (concat (concat bgb_5_3040 bgb_5_3072) (concat bgb_5_3104 (concat bgb_5_3136 bgb_5_3168))) (concat (concat bgb_5_3200 (concat bgb_5_3232 bgb_5_3264)) (concat bgb_5_3296 (concat bgb_5_3328 bgb_5_3360)))) (concat (concat (concat bgb_5_3392 (concat bgb_5_3424 bgb_5_3456)) (concat bgb_5_3488 (concat bgb_5_3520 bgb_5_3552))) (concat (concat bgb_5_3584 (concat bgb_5_3616 bgb_5_3648)) (concat bgb_5_3680 (concat bgb_5_3712 bgb_5_3744))))) (concat (concat (concat (concat bgb_5_3776 (concat bgb_5_3808 bgb_5_3840)) (concat bgb_5_3872 (concat bgb_5_3904 bgb_5_3936))) (concat (concat bgb_5_3968 (concat bgb_5_4000 bgb_5_4032)) (concat bgb_5_4064 (concat bgb_5_4096 bgb_5_4128)))) (concat (concat (concat bgb_5_4160 (concat bgb_5_4192 bgb_5_4224)) (concat bgb_5_4256 (concat bgb_5_4288 bgb_5_4320))) (concat (concat bgb_5_4352 (concat bgb_5_4384 bgb_5_4416)) (concat bgb_5_4448 (concat bgb_5_4480 bgb_5_4512)))))) (concat (concat (concat (concat (concat bgb_5_4544 (concat bgb_5_4576 bgb_5_4608)) (concat bgb_5_4640 (concat bgb_5_4672 bgb_5_4704))) (concat (concat bgb_5_4736 (concat bgb_5_4768 bgb_5_4800)) (concat bgb_5_4832 (concat bgb_5_4864 bgb_5_4896)))) (concat (concat (concat bgb_5_4928 (concat bgb_5_4960 bgb_5_4992)) (concat bgb_5_5024 (concat bgb_5_5056 bgb_5_5088))) (concat (concat bgb_5_5120 (concat bgb_5_5152 bgb_5_5184)) (concat bgb_5_5216 (concat bgb_5_5248 bgb_5_5280))))) (concat (concat (concat (concat bgb_5_5312 (concat bgb_5_5344 bgb_5_5376)) (concat bgb_5_5408 (concat bgb_5_5440 bgb_5_5472))) (concat (concat bgb_5_5504 (concat bgb_5_5536 bgb_5_5568)) (concat bgb_5_5600 (concat bgb_5_5632 bgb_5_5664)))) (concat (concat (concat bgb_5_5696 (concat bgb_5_5728 bgb_5_5760)) (concat bgb_5_5792 (concat bgb_5_5824 bgb_5_5856))) (concat (concat bgb_5_5888 (concat bgb_5_5920 bgb_5_5952)) (concat bgb_5_5984 (concat bgb_5_6016 bgb_5_6048))))))))
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
theorem bgb_6_1088 : Interval gbAtlas 6 1088 10 := block_range (n:=10) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1098 := (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 bgb_6_224))) (concat (concat (concat bgb_6_256 bgb_6_288) (concat bgb_6_320 bgb_6_352)) (concat (concat bgb_6_384 bgb_6_416) (concat bgb_6_448 (concat bgb_6_480 bgb_6_512))))) (concat (concat (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640)) (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 (concat bgb_6_768 bgb_6_800)))) (concat (concat (concat bgb_6_832 bgb_6_864) (concat bgb_6_896 bgb_6_928)) (concat (concat bgb_6_960 bgb_6_992) (concat bgb_6_1024 (concat bgb_6_1056 bgb_6_1088))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 27 := block_range (n:=27) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 27 := bgb_7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 1 := bgb_8_0
theorem allgb : ∀ k ≤ 8, ∀ i < count gbAtlas k, checkRow gbAtlas k i = true := by
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 6, 22)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeeeaeaaaecc8c888eeeaeaaaecc8c888eeeaeaaaecc8c888eeeaeaaaecc8c888eeeaeaaaecc8c888eeeaeaaaecc8c888eeeaeaaaecc8c888eeeaeaaaecc8c888
theorem fullBound (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have low := boundgb certgb
  have lift := lift_ok (u:=true) (ms:=fixRows 32 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 5 zero,1,33)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 5 zero,1,33)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008372906 * 2 ^ 32 + 3972581512) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_16401.Model.Repr at out
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

def mono : List Gate := [⟨.and,[2,3]⟩,⟨.and,[4,6]⟩,⟨.and,[2,4]⟩,⟨.or,[5,7]⟩,⟨.and,[3,4]⟩,⟨.or,[1,9]⟩,⟨.or,[6,10]⟩,⟨.or,[8,12]⟩,⟨.and,[1,13]⟩,⟨.or,[0,14]⟩,⟨.and,[11,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372906 * 2 ^ 32 + 3972581512) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372906 * 2 ^ 32 + 3972581512) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_16401

open PEqualNP.Outside.L_meta_16401 in
theorem PEqualNP.Outside.L_meta_16401 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372906 * 2 ^ 32 + 3972581512) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372906 * 2 ^ 32 + 3972581512) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound allgb)
