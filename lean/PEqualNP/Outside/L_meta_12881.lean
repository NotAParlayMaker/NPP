import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_12881.Model
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
  (n*n % 2305843009213693951 * (n+7) + 971*n) % 2305843009213693951
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


end PEqualNP.Outside.L_meta_12881.Model

namespace PEqualNP.Outside.L_meta_12881
open PEqualNP.Outside.L_meta_12881.Model
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

end PEqualNP.Outside.L_meta_12881

namespace PEqualNP.Outside.L_meta_12881
open PEqualNP.Outside.L_meta_12881.Model
def gbK8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x841fc41083fe62107f8c420fe98841fc31083fe42107f88420fe90841fc21082fca0107fd0020ff20041fd40083f880107fcc020ff18041fd30083f860107fc8020f790041fe20083f440107f48020f690041f920083fea9885fd5310ff2a6217e54c43faa9885f55310fe2a6217c54c43fea7885fd4f10ff29e217e53c43faa7885f54f10fe29e217c53c43fe87887f90f10fea1e21fc43c43fea5885fd4b10ff296217e52c43faa5885f54b10fe296217c52c43fe85887f90b10fea1621fc42c43fe65887f8cb10fe99621fc32c43fe83887f90710fea0e21fc41c43fe63887f8c710fb18e21fd31c43ea63887f0c710ff90e21fe21c43fa43887f08710ffa0621fe40c43fa81887f10310ff98621fe30c43fa61887f0c310ff90621fe20c43fa41887f08310ffaa4217f54843fca9085f95210feaa4217d54843f8a9085f15210ffa9c217f53843fca7085f94e10fea9c217d53843f8a7085f14e10ffa1c21fe43843fa87087f10e10ffa94217f52843fca5085f94a10fea94217d52843f8a5085f14a10ffa1421fe42843fa85087f10a10ff99421fe32843fa65087f0ca10bea8c21ff41843fc83087f50610fe20c21ff31843fc63087f4c610fe18c21ff21843fc43087f48610fe10c217e50843fe81087f90210fea0421fc40843fe61087f8c210fe98421fc30843fe41087f88210fd10421fd20843f241087f08210ff88421f710843f621087fd5110bfaa221fe54442fca8887f55110beaa221fc54442f8a8887fd4d10bfa9a21fe53442fca6887f54d10bea9a21fc53442f8a6887fd0d10ff21a21fd43443f886887fd4910bfa9221fe52442fca4887f54910bea9221fc52442f8a4887fd0910ff21221fd42443f884887fcc910ff19221fd32443f864887fd0510ff20a21fd41443f882887fcc510ff18a21f631443fa62887d4c510fe18a21ff21443fc42887f48510fe10a21ff40443fc80887f50110fe20221ff30443fc60887f4c110fe18221ff20443fc40887e88110fe90221f920443f840887fc4110fd88221fe10443ec20887fd5010bfaa021fe54042fca8086f950109f2a021fd54042faa8086f550109eaa021fc54042f8a8087fd4c10bfa9821fe53042fca6087794c10af29821fd53042faa6087754c10aea9821fc53042f8a6087fd0c10ff21821fd43043f886087fd4810bfa9021fe52042fca4087b94810b729021fd52042faa4087b54810b6a9021fc52042f8a4087fd0810ff21021fd42043f884087fcc810ff19021fd32043f864085f94410ffa0821fe41043fa82087f10410ff98821fe31043fa62087f0c410ff90821fe21043fa42087f08410bf28021ff40043fc80087f50010fe20021ff30043fc60087f4c010fe18021ff20043fc40087f48010fe10021ff10043ee20087f84010fd08021fd10043ea20087e44010
  | 1 => 0xf404c3fc80987f50130fe20261ff304c3f660987f8c130ef18261ff540c2fea8187f95030bf2a061be540c27ca8187f55030beaa061bd540c27aa8187f15030be2a0617e530c3fe861877d0c30ff21861fd430c3f886187710c30ffa9061fe520c2fca4187b94830b729061fd520c2faa4187b54830b6a9061fc520c3fe84187f90830fea1061fc420c3fe64187f8c830fe99061fc320c3fea2187f94430bf28861f6510c2eca2187f54430bea8861f5510c2eaa2187f14430ffa0861fe410c3fa82187f10430ff98861fe310c3fa62187f0c430ff90861fe210c3fa42187f08430bf28061ff400c3fc80187f50030fe20061ff300c3be60187f8c030fd18061fd300c3ba60187e4c030ffaa6417f54c83fca9905f95320feaa6417d54c83f8a9905f15320ffa9e417f53c83fca7905f94f20fea9e417d53c83f8a7905f14f20ffa1e41fe43c83fa87907f10f20ffa1641ef42c83fc85907f50b20fe21641ec42c83fe65907f8cb20f719641fd32c83da65907f0cb20ffa8e41fe51c82fca3907f54720bea8e41fc51c83fe83907f90720fea0e41fc41c83fe63907f8c720fe98e41fc31c83fe43907bc8720ff10e41fd21c83da43907f08720ffa0641fe40c83fa81907f10320ff98641fe30c83fa61907f0c320ffaa4417f54883fca9105f95220df2a4413e54883faa9105f55220deaa4413d54883f8a9105f15220ffa9c417f53883fca7105f94e20fea9c417d53883f8a7105f14e20ffa1c41fe43883fa87107f10e20bea9441ff42883fc85107f50a20fe21441ff32883fc65107f4ca20fe19441ff51883fca3105f94620fea8c417d51883f8a3107fd0620ff20c41fd41883f883107fcc620ff18c41fd31883f863107fc8620ff10c41fd21883f843105f94220ffa0441fe40883fa81107f10220ff98441fe30883fa61107f0c220ff90441ef20883f641107fd5120bfaa241fe54482fca8907f55120beaa241fc54482f8a8907fd4d20bfa9a41fe53482fca6907f54d20bea9a41fc53482f8a6907fd0d20ff21a41fd43483f886907fd0920f7a1241fe42483fa84907f10920f621241ff32483fc64907b8c920fe99241ed32483f864907fd4520bfa8a41fe51483faa2907f14520be28a41ff41483fc82907f50520fe20a41ff31483fc62907f4c520fe18a41ff21483de42907f88520fe90a41ed21483f842907fd0120ff20241fd40483f880907fcc120ff18241fd30483f860907fc8120fd90241fe20483dc40907fd5020bfaa041fe54082fca8107f55020beaa041fc54082f8a8107fd4c20bfa9841fe53082fca6107f54c20bea9841fc53082f8a6107fd0c20ff21841fd43083f886105f94820ffa1041fe42083fa84107f10820ff99041fe32083fa64107f0c820ffa8841fe51082fca2107f54420bea8841fc51083fe82107f90420fea0
  | 2 => 0x3fca5205f94a40f7294816e52903faa5205f54a40f6a94816d52903f8a5207fd0a40ff21481fd42903f885207fcca40ff19481fd32903f865207fd4640ff28c817e51903faa3205f54640fe28c81ff41903fc83207f50640fe20c81ff31903fc63207f4c640fe18c81ff21903fc43207f48640fe10c817e50903fe81206fd0240fda0481ff53502fea6a077d4d40afa9a81fe53503faa6a07f14d40be29a81dc53502b8a6a07fd0d40dfa1a81fe43503fa86a06f50d40fe21a81ff52502fea4a07f94940fea9281fc52502f8a4a07fd0940ff21281be42503fa84a07f10940de21281ff32503fc64a07f4c940fe19281ff51502fea2a07f94540fea8a81fc51502f8a2a07fd0540dfa0a81fe41503fa82a06f50540fe20a81ff31503fc62a07f4c540fe18a81ff21503fc42a07f48540fe10a81ff40503f680a07f90140df202817e54103fea6207f94c40bf29881fd53102faa6207f14c40ffa1881fe431037c86207f50c40fe21881bc43103fea4207f94840bf29081fd52102faa4207f14840ffa1081fe42103fa84207f10840ff99081fe32103fa64207f0c840ffa8881fe51102fca2207f54440bea8881fc51103fe82207f90440fea0881fc41103fe62207f8c440fe98881fc31103fe42207f88440fe90881fc21102fca0207fd0040dfa0081fe40103f480207f50040dea0081f940103fea9985fd5330ff2a6617e54cc3faa9985f55330fe2a6617c54cc3fe87987f90f30fea1e61fc43cc3fea5987f94b30bf29661fd52cc2faa5987f14b30ffa1661fe42cc3fa85987f10b30ff99661fe32cc3fa65987f0cb30ffa8e61fe51cc2fca3987f54730bea8e61fc51cc3fe83987f90730fea0e61fc41cc3fe639877cc730ff18e61fd31cc3ba63987f0c730ff90e61fe21cc3fa43987f08730ffa0661fe40cc3fa81987f10330ffaa4617f548c3fca9185f95230feaa4617d548c3f8a9185f15230bea9c61ff438c3be87187f90e30fea1c61fc438c3b887187fd4a30ff294617e528c3faa5185f54a30fe29461ff428c3fc85187f50a30fe21461ff328c3fc65187f4ca30fe19461ff518c3fca3185f94630fea8c617d518c3f8a3187fd0630ff20c61fd418c3f883187fcc630ff18c61fd318c3f863187fc8630ff10c61fd218c3f843185f94230ffa0461fe408c3fa81187f10230ff98461df308c3f661187fd5130bfaa261bf544c27ea8987f95130bf2a261fd544c2faa8987f15130be2a261bc544c278a8987fd0d30ff21a61fd434c3f886987fd4930bfa9261fe524c3faa4987f14930be29261ff424c3fc84987f50930fe21261ff324c3fc64987f4c930fe19261ff514c2fea2987f94530fea8a61fc514c2f8a2987fd0530ff20a61fd414c3f882987fcc530ef98a61fe314c3fa6298774c530fe18a61ff214c3fc42987f48530fe10a61f
  | 3 => 0x8618ff90c31fea1863fc430c7fea418ff94831bf29063fd520c6faa418ff14831ffa1063fe420c7fa8418ff10831ff99063fe320c7fa6418ff0c831bf28863ff410c7fc8218ff50431fe20863ff310c7be6218ff8c431fb18863fd310c7ba6218fd4c431ffa8063fe500c6fca018ff54031bea8063fc500c7fea990dfd5321ff2a6437e54c87faa990df55321fe2a6437c54c87fea790dfd4f21ff29e437e53c87faa790df54f21fe29e437c53c87fe8790ff90f21fea1e43fc43c87fe8590ff90b21fea1643fc42c87fe6590ff8cb21fe99643fc32c87fe8390ff90721fea0e43fc41c87fe6390ff8c721fe98e43fc31c87fea190ff94321bf28643fd50c86faa190ff14321ffaa4437f54887fca910df95221feaa4437d54887f8a910df15221ffa9c437f53887fca710df94e21fea9c437d53887f8a710df14e21ffa1c43fe43887fa8710ff10e21bea9443ff42887de8510ff90a21fea1443fc42887d88510ffcca21ff19443fd32887f86510df94621ffa0c43fe41887fa8310ff10621ff98c43fe31887fa6310ff0c621ff90c43ef21887ee4310ffd4221ff284437e50887faa110df54221fe28443ff54486fea890efd51219faa243fe54486fca890ff55121beaa243fc54486f8a890ef151219e2a243ff53486fea690ff94d21bf29a43fd53486faa690ff14d21be29a43ff43487fc8690ff50d21fe21a43ff42487fc8490ff50921fe21243ff32487fc6490ff4c921fe19243ff41487fc8290ff50521fe20a43ff31487fc6290ff4c521fe18a43ff21487ee4290ff88521f710a43ff50486fea090ff94121fea8243fc50486f8a090ffd5021bfaa043fe54086fca810ef950219f2a043fd54086faa810ef550219eaa043fc54086f8a810ffd4c21bfa9843fe53086fca610f794c21af29843fd53086faa610f754c21aea9843fc53086f8a610ffd0c21ff21843fd43087f88610df94821ffa1043ef42087fc8410ff50821fe21043ec42087fe6410ff8c821fe99043fc32086fca210ffd0421ff20843fd41087f88210ffcc421ff18843fd31087f86210ffc8421f790843fe21087ec4210ff48421f690843f521087fea010ff94021bf28043fa50086f4a010ff54021bea8043f950086f2a010ff14021ffa9e81fe53d02fca7a07f54f40bea9e81fc53d03fe87a06fd0f40ff21e81fd43d037a87a07f10f40ffa9681fe52d02fca5a07f54b40bea9681fc52d03fe85a07f90b40df21681fd42d03f885a06f10b40ff99681fe32d03fa65a07f0cb40ffa8e81fe51d02fca3a07f54740bea8e81fc51d03fe83a06fd0740ff20e81fd41d037a83a07f10740ff98e81fe31d03fa63a07f0c740ff90e81fe21d03fa43a07f08740beaa481ff53903fca7205f94e40fea9c817d53903f8a7207fd0e40ff21c81be43903fa87207f10e40de21c81ff529
  | 4 => 0x7f14432ffa8065fe500cafca0197f54032bea8065fc500cbfea7a0ff94f41bf29e83fd53d06faa7a0ff14f41ffa1e83fe43d077c87a0ff50f41fe21e83bc43d07fea5a0ff94b41bf29683fd52d06faa5a0ff14b41ffa1683bf42d07fc85a0ff50b41dea1683fc42d07fe65a0ff8cb41fe99683fc32d07fea1a0ff94341bf28683fd50d06faa1a0ff14341beaa483ff53907fca720df94e41ef29c835e53907faa720df54e41eea9c835d53907f8a720ffd0e41ff21c83fd43907f88720ffd4a41ff294837e52907faa520df54a41fe29483ff42907fc8520ef90a41fea1483fc42907788520ffcca41ff19483fd32907f86520df94641ffa0c83bf41907ee8320ffd4241ff284837e50907faa120df54241fe28483ff53506fea6a0ff94d41fea9a83fc53506f8a6a0ffd0d41ff21a83be43507fa86a0ff10d41de21a83ff52506fea4a0fbd4941b7a9283fe52507faa4a0ff14941be29283ec52506d8a4a0ffd0941dfa1283fe42507fa84a0ef50941fe21283ff32507fc64a0ff4c941fe19283ff41507ee82a0ff90541df20a83ff50506fea0a0ff94141fea8283fc50506f8a0a0df95041ffa9883fe53106fca620ff54c41bea9883fc53107fe8620ff90c41fea1883fc43107fea420ff94841bf29083fd52106faa420ff14841ffa1083fe421077c8420ff50841fe21083bc42107fe6420ff8c841fe99083fc32106fca220ffd0441dfa0883fe41107ec8220ff50441dea0883f541107fea020ff94041bf28083fd50106faa020ff14041ffaa6637f54cc7fca998df95331feaa6637d54cc7f8a998df15331ffa1e63df43cc7fc8798ff50f31fe21e63dc43cc7fea598ff94b31bf29663fd52cc6faa598ff14b31ffa1663fe42cc7fa8598ff10b31ff99663df32cc7fc6598ff4cb31ee99663fc32cc7fe8398ff90731fea0e63fc41cc7fea198ff94331bf28663fd50cc6faa198ff14331ffaa4637f548c7fca918df95231df2a4633e548c7faa918df55231deaa4633d548c7f8a918df15231bea9c63ff438c7fc8718ff50e31fe21c63ff528c7fca518df94a31fea94637d528c7f8a518ffd0a31ff21463fd428c7f88518ffcca31ff19463fd328c7f86518df94631ffa0c63fe418c7fa8318ff10631ff98c63df318c7ee6318ffd4231ff284637e508c7faa118df54231fe28463ff544c6fea898ff95131bf2a263fd544c6faa898ff15131be2a263ff434c7be8698ff90d31fea1a63fc434c7b88698ffd4931bfa9263fe524c7faa498ff14931be29263ff424c7fc8498ff50931fe21263ff324c7be6498ff8c931fe99263dd324c7f86498ffd0531ff20a63fd414c7f88298ffcc531fb98a63fe314c7bc6298ffd4131bfa8263fe504c7faa098ff14131be28263ff540c6fea818ff95031bf2a063fd540c6faa818ff15031be2a0637e530c7fe
  | 5 => 0xa43ff294877e5290ffaa521df54a43fe29487ff5190ffca321df94643fea8c877d5190ff8a321ffd4243ff284877e5090ffaa121df54243fe28487ff4350fbe86a1ff90d43df21a87ff5250efea4a1ff94943fea9287fc5250ef8a4a1ffd4543bfa8a87fe5150ffaa2a1ff14543be28a87ff5050efea0a1ff94143fea8287fc5050ef8a0a1df95043bf29887ff4310f7e8621ff90c43ef21887fd4310f7a8621f750c43ffa9087fe5210efca421ff54843bea9087fc5210ffea221ff94443bf28887fd5110efaa221ff14443ffa8087fe5010efca021ff54043bea8087fc5010ffea7a17f94f42bf29e85fd53d0afaa7a17f14f42ffa1e85fe43d0bfa87a17f10f42ffa8e85fe51d0afca3a17f54742bea8e85fc51d0bfea1a17f94342bf28685fd50d0afaa1a17f14342beaa485ff5390bfca7215f94e42fea9c857d5390bf8a7217fd0e42ff21c85be4390bfa87217f10e42de21c857e5290bfe85216fd0a42f7a1485ff5190bfca3215f94642fea8c857d5190bf8a3217fd4242ff284857e5090bfaa1215f54242fe28485ff5350afea6a17f94d42fea9a85fc5350af8a6a17fd0d42ff21a85fd4350bf886a17fd0942f7a1285fe4250b7c84a17fd4542bfa8a85fe5150bfaa2a17f14542be28a85ff5050afea0a17f94142fea8285fc5050af8a0a15f95042ffa9885fe5310afca6217f54c42bea9885fc5310bfe86217f90c42df21885fd4310bf886216f10c42bf29085ff4210b7e84217f90842f721085fd4210b7a84217b50842ffa8885fe5110afca2217f54442bea8885fc5110bfea0217f94042bf28085fd5010afaa0217f14042ffaa6657f54ccbfca9995f95332feaa6657d54ccbf8a9995f15332ffa1e65fe43ccbfa87997f10f32ffa1665fe42ccbfa85997f10b32ffa8e65fe51ccafca3997f54732bea8e65fc51ccbfea1997f94332bf28665fd50ccafaa1997f14332ffaa4657f548cbfca9195f95232feaa4657d548cbf8a9195f15232bea9c65ff438cbfc87197f50e32fe21c657e528cbfe85197f90a32fea1465fc428cbfe651977cca32f799465ff518cbfca3195f94632fea8c657d518cbf8a3197fd4232ff284657e508cbfaa1195f54232fe28465ff544cafea8996fd51329faa265fe544cafca8997f55132beaa265fc544caf8a8996f151329e2a265ff434cbfc86997f50d32fe21a65ff424cbfc84997f50932fe21265ff324cbde64997f8c932ef19265ff514cafea2997f94532fea8a65fc514caf8a2997fd4132bfa8265fe504cbfaa0997f14132be28265ff540cafea8197f95032bf2a065fd540cafaa8197f15032be2a0657e530cbfe86197f90c32fea1865fc430cafca4197fd0832ff21065fd420cbf884197fcc832ef99065fe320cbdc64197f4c832ee99065ed320cbfea2197f94432bf28865fd510cafaa219
  | 6 => 0x4052ec908e804a000d9016e19e92823ec46baa000e1c0b800200000100000000000100800200000300100300000100000200100500300400100000700201000001100500200100a00700201c00200000000a00100000300000201e01300600001100000300800400100000400300500701700200a00100800100c00300600200101a00a00000000300000a00000100200000e00000100400001300400100000000600300500600800200100000000000300200200200100200500000700d00c00000000000000100100800301c00400400100000e01300000100300200d00000200000e00400d00100a00900200101800700502300000000100a00000000100000000000000d00000f00000200000000600100000000100600900800000100100000300100500300200100a00200000200100000b00f00001f00600200700000e00900200000b00001d01801600f00200000000100900000000000700600000000201000001d00000400400000900300600d00100b00301700000002000101600100300000000000000600000000100600700100100400500400600100000101700000200100000000600201000200400100300400d00900400001000900100000000003001800700000100100700700800500000100100200000500500600000e00301300000401500700000000700f00000000700800200000600000400300000601300400000700000500000300000400100000300000400300000000000200000000000600100000d00500000600200000200000200f00100500100000000c00200b00001300100000c00500400100000000701a00200200100100500500101e00100000700000300000200100100200000300600b00300300000300000000000a00200400500b00700100400200000701801b00001700000100101000100402400000300202600300600900000100003100500000201800100000100200500900000000c00b00b00000000000d00000100c00700100200200800000100d00300000000201700000000200300500e00b00000000000000500e00c01300901a00900200000200400000101f00500000400500100000000400200000000000100800c00901400200300000201201000001200000500200400200100001100000b01200000000200000400200500600200400501600700300100e00401500100200101a00000000500300000000400401000000100000b00900100701d00000101100000000400400101300000300200000500100000500002200001601500000001800100600d00300400500d009000ffa9687fe52d0efca5a1ff54b43bea9687fc52d0ffea3a1ff94743bf28e87fd51d0efaa3a1ff14743ffa8687fe50d0efca1a1ff54343bea8687fc50d0efaa921df94e43ffa1c87bf4390fbe8721ffd4
  | 7 => 0x448bc000065a0e24a8688000000cae00003a00a5e20003101b8bb0060594468260b10000b523060000000863e4000000d886f433841a0000002c62760007fe0009508a2a1e13c5b6000000000000000000000000000000ba40000005020005c8a6867e0007e6038d9a23200061aa4e0004669364889b8b36d3270c0006a6c2c7a8046bb29d2e386027fa780de221c7b071e362578de80ac00cd725b419a662636534d9e94e2ccc261d0000c54000282e18524b6640e5f8d6c5fa00861c00095cd926c8000d00a5c0005840004207f26fac1e000c0210c992106000ca83b0734000ce6156a32b5a810a4c0c80445a4cea2ac480cbcc5609620c0f6a5a87e1d6c0a0547b8db800088abde1da9fabf2828b828bc0005389c082495ad546a8dbe000582db4bce2dcd7a0005da15c42e0004d4000000000638000be0b766a4c0c1a8d8034231a41e0cc05a09007e9f8bd07c800064054c74ca38296334c62982a743009c4a5800000068c000e5ca942bc51a0000000000f4000d0e00011acdea06ac6d16dac8caa268ced705481d84ea4d268692c2e425e2b0cc20b288e3126f801e730e3eb6c50ea8239872638c7de6665ca15a8541baa845d474860c6d8000000dbac649aad8e000000564e1a5f252a13e4100feaca7640e01c6cf02b2d083e63460000003b8000a045d000000096a846ab4000cd0b50e5ecca25cb1814a000dd43ac000000000a1a000912b2a4e80001b00000f061289e2746dc0000000c07560005d226c0000000007f6762d8681e000b8a4380000005f0e44d8cb0c0001300000003e2ddcbf40b48b42c4b0442800000000000066a7a00104001780000008e6904cac5ee00000000000000037e33ce30272000888000b6a8e2000dd600010e2ce002000a983be264d747eeaec7504fcbbe0b69e89d0bd6610cc041436e830cdc7aea162de6ecabcade58a1a0d9c0280004dc5a2600b7e0000004b62ca4940009be01a0000007eac5c0002d443cc8063c5ec6541f0000b9c000ad87ba000708da66b8b00e5a000000000084000660d8453a00077e17428e8065c00042aadec000a56bd88ee000000b223b49209dc00000000075c3fe7c07b6cfc0000006989c82a2000242e3492e000c3a3daa4200056c0ced3eaa254049e0001fc000826e0ee3a00000002c848e20000a8c0003ee2d2380000000000af005643234cd5aafc492890c84a6ae4839a088ace58cb606500d898a0d42b42fec88cee000206000e32000e660002a01900000000009300009a800046c0000000002c053e00088c17c0000007be00000018ae0800038e000896b32776cd8906dc669caa40009bc230ab27dcd68dce4bec7a4fe408a2c5e097edd89e01e0070670b4e59a022b206344b0c94000c402169381ea22072eae477c738ada0001628e03c637097a5226de0d6b
  | 8 => 0xae294caee6300000c62e64544ace4042449a000000482000000e2a684e109960ba0000002388ea0000000003d8434000000000ab8b7c3720006220006c0000ce48509e40000001f47b4000bfc9f2c1c000c7ebc6000b6e1ee000396bc20005360340006ac5ae23a000000e0000000083a000ba217254aac2ca4000cb6000d2a308000e588800182becc400065694812a29c800000dfa458dc817a000844dd00240cadc0d6a60e2f8000d24d14c3890ed96dea4c600000069ea3000081c000c0e7fc914d52498e2e5ac35cb1eb868866ca7409f67e879a00000e0006d605e0000003f21845c457cd0c1be4f870ab4252c4d0d1a0002e200037a000714000c4a1a28f8be27f43de142c10902b9e2547d6e52000af6d2c000000d1e586746de00a0b30b4855e3a05c209c470bb831ca3e10884ec740c2b140000000000000000004a600035600026abfa7900004e4000bee36c6b2aacb3451400004086663225a000126078da21fe0000000eab468be6da0002d0c9ccb40003fa4cc314026000c6c00000000000090cb9a5187960001e486ebece620006f64bc0000000d00000f804e7449ac81294a4228ac54e000c8e000d22168b5c2280007bc418c980000524b267ccbe566386be8964694da8192d5e3a66d0a18224ae817eb266bc53cad42583788167886263d09e248c70e000590adcd303eaa9e838a800000008dc23c000390b3c72806400000008ec96bd2bb600011c2fabae222a6475e0000008200d247e768df640c86231e57032ac9224870289291644c0008d8d0abc4236000000000d46da046a976990ad0a36e0a2687f8132322bd42084da6448f6af2836b2ec8a06c6ae6d40001ae6c67108427d85601009f4ccc57a872a142e029418c1ca868d483f8bc84ce876e24a2a78cc482b8000000c7235ed66cec802a0ece875a62815000000018200000035400003c50c520870000000000000dde04836029ec424f2a78c1a84041c93c0ec8f40003d42f67f036400095248a00095e49c0000a6484000af4d7c0007700001ce9000000009d46e0d987ecd2e68a8c421a3a20005980000000008ae6a2000000d123527d4154000dfc526000d10bba376000e569b6b08a5027c1106cc36a67a732a5e0001b4c28000dee000daa000000000d6080811e972000ce08fe864aa8c0600006a0000000001383cea200002ea0bca4a000000e60c24b98dc41e219464cdf256e6768a0704ce29ee77ac4eb84504974000cd4abebe64363682a6606000e26164784c08874000d409fc59ca9000044a000e04c82bea0001f21c2692b38b7a8787cc0823cca08000000000212b968aa202000000a7600055600017658e4d6166000cf40001460003e80004ec1b60003921a600000074e2840000005b8b1c7668221fa98e60ad8abe413a7ac884c3c7ca69000000000
  | 9 => 0x26bbc25640a000cf883c19846200045e5880007740e8a0c000aa65aa000000000d440005d889c80c64a14c000dcc0000000004f02aed36000000a00942b0e72c758da40001146b40b00000000588a87e2dc25bc84c348000574cb071ad2800000066800000004200076c614c68000000d5c3fc7820003bc0009ea07a4067aa62c87c0728fa6f0d56e147224ded821c04f69585d6a4498c000cf200097c5ba70000027a5a6000102ac014448e8c20000000000000000000000000000009ba000d042d800000090a000ae60000004b466c358a6c43aa54b700004a46ea00042a26ecc678e62aa8e8b8000000000000a40c60000000426a3c3c29805965120000004e2000000000000374cb8b5400038879c33a2d699a7c447600000085c956a92b78b900684aa9d69260000005440000005164c8d4264243e24006ebca32e4520002f2ba61b257e00068000000002a000000000000d4c63aa020000dcd34652882d2600000097813471c65c2900009ce3d2b58c2ee02720de47c282e0000008d04e60005424743306a00005f60a25500002660002ee4567d05e61c82a4e4aa72ba834076089a00055ad02000a7a1bc1223f60001168341962929b43b214e02e44ea2e0000009a60003d60005a88d46be00047c1400da994db6000000270814000856682c5acaa0008ec0007ce09a09e7780e6c505cc0a80001284720000000004960125725585e4798430000000320818b168986aa0a4500d3c000a96cf607600000074a9881ccca6e128f2db08a634aa223a8094db2a34b6403e832d4a000b280000006e87160e44faa2845ccd2e162bad6eb0a50691815200032451e9540000009989ccb56cfec6a4c0786000afe000050350e3ccba72450ae5400039402000073a22c30a00000008c0008a4a9aad60006e60fab80aeaa70014966604ad23babf6a1cdbc00066e000a52000000000d065de0001c48f000052821e286000c8c6fe20ad649f0b7400006200000000024e674000e643c44c4dd2460ab600080400018e3261eca6638a1484e00000007188de7a201634ec7cd205b09700be00073e0000008580005c6000000d3a000e42e283c0000000dda6fcc443ca1700003324409fe00020e9a40008da0001d26080000000000000005be00000033e0000002520006c20009ec0000000000002c232cc20316c364d82f045044600093adf0bfe000000000aaa000a1075219c4f46729b22b6000568d7621428cc04a8ab92234000cc861e84aaba6bac580000009b01aa9a2000794030b72c5e65e4b8ca05dc3c82ec664d94532ac8112b4a81a772b62c121d45feb2c0aebf091a2621586b67b23f46cea483aa07c5fc07464e0008c0000c16000b028c67120001200360003b638427e47880ad1c946c66444cfac140006960002c89ae0009082443a49ca934000
  | 10 => 0x9891c30eba024c0001808e4de6066894ca26f285e2a8b4c4121365521ac39c960c34e36b8c40444210ad58a7e0c47a66e400059e8b60000004a2000df8000acc8b20000009e64c2e22b5e000000c70940d38a60336d7e922c00dfec866c4e2c204b3e69aa1208005c86a73c6b00aa9c211883eb442fc000e0c12493e648a9c000188000b680006e28d2c188c83f09c6d628cc00099e00030c1f69da00080e0007e0000032b88000984ac45b2250000a2421862e580000402c3e000c220f28fce4ecce0000008d60006187da00072a94446e508986b24a0ad4e4ba000cda56200049028a00024a5cea6e0000000000005927540006d2cb232800078a416dca000000366aa09320003ae0004ee382620000bb40000000920000009a0afaae01debcc000e1e0000000ee76a00086000047ab94000304e4c4aeb8e7922880fc2463ec85282aa8600012c00016004c96cb120000007a40000000006eed187368b09de5ea42c962c78318646bda18608a2100002782001dc000000d502daa3aaf85f47e492a1a4ab02f462400686c3dce06280000df4000000bf80001e891e576c4c99c87a68e1f89d8000bdc00015e00051c45a00092491000096e0000000005e84caa62a7cc9e7d282c74216c0003e012e56a53022ec767c651076ec6e39e35aaae01cc2a104cd6e46546e504a079ed7855c658a8870629a37c0005545a0486c301e663e2e8b3a34422abac464a46c9a298968daec52616b0630285a000c320000de8ba678b1a16a2
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc210436e5208410db54821043e52108410be98021042f960084109f992500427d64940109f98e500427d63940109f98a500427d62940109f586500427d65d0010cf953400433d54d0010d794f400435d53d0010db94b400436d52d00109fd96400427d6590010cf952400433d5490010d794e400435d5390010bb98a40042ed6290010db94a400436d5290010bd98640042f561900109fd95400433e5450010cf55140042df6350010b718d400435e5350010d754d400436e5250010db549400427f65100109f994400427d65100109f194400433e5410010cf550400435e5310010d754c400436e5210010db54840042f66110010bd584400427d65cc010cf953300433d54cc010d794f300435d53cc010db94b300436d52cc0109fd96300427d658c010cf952300433d548c010d794e300435d538c010db94a300436d528c010bd98630042f5618c0109fd9530042bf644c010af191300433e544c010cf551300435e534c010d754d300436e524c010db549300427f650c0109f994300427d650c0109f19430042be640c010af590300433e540c010cf550300435e530c010d754c30042ee620c010bb588300436e520c010db54830042f6610c010bd58430043d9300c0109f597200433e54c8010cf553200435e53c8010d754f200436e52c8010db54b200427f65880109f59620042be6488010af592200433e5488010cf552200435e5388010d754e200436e5288010db54a20042f66188010bd586200437a50880109fd95200433e5448010cf551200435e5348010d754d200436e5248010db549200437a50480109fd94200427e65080109f594200427c6508010cf950200433d5408010d794c200435d5308010db948200436d5208010bd98420042f56108010cf953100433d54c4010d794f100435d53c4010db94b100436d52c4010dd59710043b654c4010ed553100437753c4010f594f100437553c4010f554f100435553c4010f994b10043e552c4010cf952100433d5484010d794e100435d5384010db94a100436d5284010bd58610043765184010be596100437965840109e59610043ba5484010ee55210043da5384010f654e100437b5284010fa94a10043795284010fa54a10043695284010be586100437a5184010fc946100427f6544010cf951100433d5444010d794d100435d5344010db949100436d5244010bdd95100437765440109dd9510043b65444010ed55110043775344010f594d10043755344010f554d10043555344010f994910043e55244010bdd8110043765044010fc90110043f14044010bed95100437b65440109ed9510043ba5444010ee55110043da5344010f654d100437b5244010fa94910043795244010fa54910043695244010bed8510043f36144010de94510043f25144010fc90510043f14144010
  | 1 => 0x435d63148109758c520427e6214810db988520426e62148109f984520437661148109f980520437a60148109e980520427f65d08109f997420427d65d08109f197420433e54d0810cf553420435e53d0810d754f420436e52d0810db54b420427f65908109f996420427d65908109f196420433e5490810cf552420435e5390810d754e420436e5290810db54a420427f65508109f995420427d65508109f195420433e5450810cf551420435e5350810d754d420436e5250810db54942042f76150810bd185420427f65108109f994420427d65108109f194420433e5410810cf550420435e5310810d754c420436e5210810db548420427f65cc8109f997320427d65cc8109f197320433e54cc810cf553320435e53cc810d754f320436e52cc810db54b320427f658c8109f996320427d658c8109f196320433e548c810cf552320435e538c810d754e320436e528c810db54a320427f654c8109f995320427d654c8109f19532042bf644c810af191320433e544c810cf551320435e534c810d754d320436e524c810db54932042f7614c810bd18532042fb604c810be181320427f650c8109f994320427d650c8109f194320433e540c810cf550320435e530c810d754c320436e520c810db548320427e64944109f592510427e63944109f58e510427e62944109f58a510427d65d0410cf953410433d54d0410d794f410435d53d0410db94b410436d52d04109fd96410427d6590410cf952410433d5490410b798e41042dd6390410d794e410435d5390410db94a410436d5290410be98241042f960904109fd95410433e5450410cf551410435e5350410d754d41042ef6250410bb189410436e5250410db549410427f65104109f594410433e5410410cf550410435e5310410d754c410436e5210410db54841042fa6010410be580410427d65cc410cf953310433d54cc410d794f310435d53cc410db94b310436d52cc4109fd96310427d658c410af99231042bd648c410cf952310433d548c410d794e310435d538c410db94a310436d528c410dd94631042fa608c410be582310427f654c410cf951310433d544c410d794d310435d534c410db949310436d524c410dd945310427f650c4109f594310433e540c410cf550310435e530c410d754c310436e520c410db54831042fa600c410be580310427d65c8410cf953210433d54c8410d794f210435d53c8410db94b210436d52c84109fd96210427d6588410cf952210433d5488410d794e210435d5388410db94a210436d5288410be98221042f960884109fd9521042bf6448410af191210433e5448410cf551210435e5348410d754d210436e5248410db549210427f65084109f59421042be6408410af590210433e5408410cf55021042de6308410b758c210435e5308410d754
  | 2 => 0x5454c10e7951530431e5454c10d7551530439d5454c10c7551530435c5454c10d7d91530435e6454c10d7591530435c6454c10d7d89530435e6254c10d7589530435c6254c10d7985530435c6154c10d7981530435c6054c10d704153042be6414c10af590530433e5414c10cf55053042de6314c10d754c53042ee6214c10bb588530427e6414c10cf990530423e6414c109f590530433d6414c108f590530427e6314c10d798c530425e6314c109f988530436e6214c109b988530427d6214c10db588530426d6214c109f98453043766114c109d984530427e6014c10de980530427f65d0c109f997430427d65d0c109f197430433e54d0c10cf553430435e53d0c10d754f430427f6590c109f996430427d6590c109f196430433e5490c10cf552430435e5390c10d754e430427f6550c109f995430427d6550c109f195430433e5450c10cf551430435e5350c10d754d43042fb6050c10be181430427f6510c109f994430427d6510c109f194430433e5410c10cf550430435e5310c10d754c43042be64d4810af593520433e54d4810cf55352042de63d4810b758f520435e53d4810d754f520427e64d4810cf993520423e64d48109f593520433d64d48108f593520427e63d4810d798f520425e63d48109f58f520435d63d48109758f520427e61d4810dd987520427e60d4810de983520427d6594810cf952520433d5494810d794e520435d5394810dbd4a520427e64948109f592520427e63948109f58e520426d6594810dbd52520436e5494810eb952520432e5494810db55252043ad5494810cb552520436c5494810dbd4e520436e5394810f394e520434e5394810db54e52043cd5394810d354e520436c5394810dbd92520436e6494810db592520436c6494810dbd8e520436e6394810db58e520436c6394810dbd0e520436e4394810db50e520436c4394810db986520436c6194810db982520436c6094810cf951520433d5454810d794d520435d53548109fd91520427c64548109fd8d520427c6354810dbd89520427f61548109f585520427f60548109f581520436f6554810dbd51520436e5454810eb951520432e5454810db55152043ad5454810cb551520436c5454810dbd4d520436e5354810f394d520434e5354810db54d52043cd5354810d354d520436c5354810dbd91520436e6454810db591520436c6454810dbd8d520436e6354810db58d520436c6354810dbd0d520436e4354810db50d520436c4354810db985520436c6154810db981520436c6054810db04152042be6414810af590520433e5414810cf55052042de6314810b758c520435e5314810d754c52042ee6214810db548520427e6414810cf990520423e64148109f590520433d64148108f590520427e6314810d798c520425e63148109f58c520
  | 3 => 0x110f54c5304427e650c110af99030442bd640c110bb98830442ed620c110bd98430442f5610c1109f997204436f52c8110db14b20442f661c8110bd587204427e6588110af99220442bd6488110be996204437a6588110ee99220443b96488110be58a204437a5288110de14a20442fa6188110fc8c620443f131881109fd95204427d65481109f195204436f5248110db14920442f76148110bd18520442f86548110de19520442786548110fad8920443eb5248110de94920443785248110fa14920443eb4248110fa10920443ea3248110fa4c920443f36148110be18520443f06148110fc8c520443f13148110fac8520443e921481109f99420442fa6008110fa48020442fb62c4110be58b10443f231c4110fc4c710442f76384110bd58e10443f35084110fc88210443f12084110b798f54042dd63d5010bb98b54042ed62d50109f98f540435e63d50109798f540427d63d5010d758f540425d63d50109f98b540436e62d50109b98b540427d62d5010db58b540426d62d50109f987540437661d50109f983540437a60d50109f596540433f54950109f98e540427d63950109f98a540427d62950108f596540433f6395010cf98e540433d6395010cf18e540433f6295010cf98a540433d6295010cf18a540433e6195010cf186540433e6095010cf182540433f64550109fd8d540427c63550109fd89540427c62550109fd85540427d61550109fd81540427d6055010cfd95540433f6355010cf98d540433d6355010cf18d540433f6255010cf989540433d6255010cf189540433e6155010cf185540433e6055010cf181540433c1055010af990540433d5415010b798c54042dd6315010bb98854042ed62150109f990540433e64150108f990540427e6315010d798c540425e63150109f58c540435d63150109758c540427e6215010db988540426e62150109f588540436d62150109b588540427e6115010dd984540427e6015010de98054042be64d4c10af593530433e54d4c10cf55353042ee62d4c10bb58b530427e64d4c10cf993530423e64d4c109f593530433d64d4c108f593530427e62d4c10db98b530426e62d4c109f58b530436d62d4c109b58b530427e61d4c10dd987530427e60d4c10de983530427d6594c10cf952530433d5494c10d7d4e530427e6494c109f592530427e6294c109f58a530425d6594c10d7d52530435e5494c10e7952530431e5494c10d7552530439d5494c10c7552530435c5494c10d7d92530435e6494c10d7592530435c6494c10d7d8a530435e6294c10d758a530435c6294c10d7986530435c6194c10d7982530435c6094c10cf951530433d5454c109fd91530427c6454c10d7d8d530427f6254c109f189530427f6154c109f585530427f6054c109f581530435f6554c10d7d51530435e
  | 4 => 0xf98f524427d63d4910dbd4a524427e64949109f592524427e63949109f58e524427e62949109f586524437561949109f58252443796094910afd9152442bc6454910b7d8d52442dc63549109fd91524433f64549108fd91524427c6454910cf191524423c64549109fd8d524435f635491097d8d524427c6354910d718d524425c6354910dbd89524427f6154910ddd85524427f6054910ded81524427e6514910db548524427e64149109f590524427e63149109f58c524436e62149109f984524427c61149109f980524437960149109f180524427f65d09109f997424427d65d09109f197424436f52d0910db14b424427f65909109f996424427d65909109f196424433f5490910cf15242442fa6090910be582424427f65509109f995424427d65509109f195424427f65109109f994424427d65109109f194424433f5410910cf150424436f5210910db14842442f66110910bd58442442fa6010910be580424427f65cc9109f997324427d65cc9109f197324436f52cc910db14b32442f661cc910bd587324427f658c9109f996324427d658c9109f196324435f538c910d714e32442fa608c910be582324427f654c9109f995324427d654c9109f19532442bf644c910af191324427f650c9109f994324427d650c9109f194324435f530c910d714c324436f520c910db14832442f6610c910bd58432442fa600c910be580324427e65d0510cfd53414433c54d0510be98341442f960d05109f99641442de6390510b758e414427c6550510cfd51414433c5450510bbd8941442ec6250510bed8141442f860505109f994414427e65cc510d7d4f314435c53cc510be98331442f960cc5109f99631442be648c510af59231442f6658c510dd99631443b6648c510ed59231442f5638c510dd94e3144374538c510bd982314427c654c510d7d4d314435c534c510bed8131442f8604c510dd1953144274654c510f5d8d31443d7534c510dd94d3144374534c510f514d31443d7434c510f510d31443d7324c510f54c931443f3604c510bd18131443f0604c5109f99431442f6610c510f54c4314427e65c8510dbd4b214436c52c8510be98321442f960c85109f996214427c6548510afd9121442bc6448510dbd49214436c5248510bed8121442f860485109f99421442be6408510af59021442de6308510b758c21442fa60085109f997404433f54d0110cf15340442f661d0110bd587404427e6590110bb98a40442ed62901109fd95404427d65501109f195404433f5450110cf15140442df6350110b718d40442f76150110bd185404427e65101109f997304435f53cc110d714f30442f661cc110bd58730443d531cc1109f996304427f654c1109f595304427c654c110afd9130442bc644c110d7d4d304435c534c110bdd8530442f4614c
  | 5 => 0x21842fb6048610be18121842be6408610af59021842de6308610b758c21843e52108610be580218433f54d0210cf153408433e5490210cf55240842ee6290210bb58a40842f66190210bd586408433f5450210cf15140842df6350210b718d408433e5410210cf55040842f66110210bd584408435f53cc210d714f308435e538c210d754e30842f6618c210bd58630842bf644c210af191308435f534c210d714d30842be640c210af590308435e530c210d754c30842ee620c210bb58830842f6610c210bd584308436f52c8210db14b20842be6488210af592208436e5288210db54a20842f66188210bd58620842f96588210de59620843ba6488210ee592208437a5288210fa94a20843e95288210de14a20842fa6188210fc98620843f16188210dbd49208436c5248210bed95208437b6548210fad8920843eb5248210de94920843785248210fa14920843eb4248210fa10920843ea3248210fa4c920842f86148210fac8520843e92148210db948208436d5208210bd98420842f56108210fa48020842f565c4210dd597108437753c4210dd54f10842f965c4210de59710842fb62c4210be58b108427e63d51109f58f544427e62d51109f58b544433f54951109f992544427e63951109f58e544427e62951109f58a544427d6195110dd586544427d6095110de58254442df6355110b718d54442ef6255110bb189544433f64551109fd8d544435f635511097d8d544427c6355110d718d544425c63551109fd89544436f62551109bd89544427c6255110db189544426c62551109fd85544437761551109fd81544437b60551109f994544433d5415110cf990544427e63151109f58c544427e62151109f588544427e61151109f184544427e60151109f180544427e64d4d109f593534427e62d4d109f58b534435f5394d109f992534427d6494d109f98e534427e6294d109f58a534427d6194d10dd586534427d6094d10de58253442bf6454d10af19153442ef6254d10bb189534427f6454d10cfd91534423f6454d109f191534433c6454d108f191534435f6354d109fd89534436f6254d109bd89534427c6254d10db189534426c6254d109fd8553443776154d109fd81534437b6054d109f994534435d5314d109f990534427d6414d10d798c534427e6214d109f588534427e6114d10dd584534427c6114d109f980534427c6014d109fd97434427e65d0d109f597434427c65d0d10d7d4f434435c53d0d109fd96434427e6590d109f596434427c6590d10cfd52434433c5490d10bd98643442f56190d109fd95434427e6550d109f595434427c6550d109fd94434427e6510d109f594434427c6510d10cfd50434433c5410d10d7d4c434435c5310d10bd98443442f56110d10be98043442f96010d109f993524427d64d49109
  | 6 => 0x37a60d5210cfd52548427e63952109f58e548427e62952109f58a54842df6355210b718d548433f64552109fd8d548435f635521097d8d548427c6355210d718d548425c63552109fd89548427c6255210cf550548433e64152109f98c548427d63152109f988548427d6215210dd584548437a60152109f993538427d64d4e109f98b538427d62d4e10dd587538437a60d4e10d7d4e538427e6494e109f592538427e6294e109f58a53842bf6454e10af191538427f6454e10cfd91538423f6454e109f191538433c6454e108f191538435f6354e109fd89538427c6254e10af99053842bd6414e10d754c53842ee6214e10bb588538427e6414e10cf990538423e6414e109f590538433d6414e108f590538435e6314e109f988538436e6214e109b988538427d6214e10db588538426d6214e10dd584538437a6014e109fd97438427e65d0e109f597438427c65d0e10cf953438433d54d0e10d7d4f438435c53d0e109fd96438427e6590e109f596438427c6590e10cfd52438433c5490e109fd95438427e6550e109f595438427c6550e10cf951438433d5450e109fd94438427e6510e109f594438427c6510e10cfd50438433c5410e10d7d4c438435c5310e10be98043842f96010e10af99352842bd64d4a109f993528433e64d4a108f993528427d64d4a10cf593528423d64d4a109f98f528427d63d4a10dd587528437a60d4a10dbd4a528427e6494a109f592528427e6394a109f58e528437a6094a109fd91528427c6454a109fd8d528427c6354a10dbd89528436d5214a109f990528427d6414a109f98c528427d6314a10db98852843756114a10de980528427f65d0a109f997428427d65d0a109f197428436e52d0a10db54b428427f6590a109f996428427d6590a109f196428433e5490a10cf55242842fa6090a10be582428427f6550a109f995428427d6550a109f19542842f76150a10bd185428427f6510a109f994428427d6510a109f194428433e5410a10cf550428436e5210a10db54842842fa6010a10be580428427f65cca109f997328427d65cca109f197328427f658ca109f996328427d658ca109f196328436e528ca10db54a32842fa608ca10be582328427f654ca109f995328427d654ca109f19532842bf644ca10af191328436e524ca10db54932842f7614ca10bd185328427f650ca109f994328427d650ca109f19432842fa600ca10be580328433e54d0610cf55341842fa60d0610be58341842de6390610b758e418433e5450610cf55141842ef6250610bb18941842fb6050610be181418435e53cc610d754f31842fa60cc610be58331842be648c610af592318435e534c610d754d31842fb604c610be181318436e52c8610db54b21842fa60c8610be58321842bf6448610af191218436e5248610db549
  | 7 => 0x494b109f59252c427e6394b109f58e52c42bf6454b10af19152c427f6454b10cfd9152c423f6454b109f19152c433c6454b108f19152c427f6354b109f18d52c436f6254b10af99052c42bd6414b10b798c52c42dd6314b10db54852c427e6414b10cf99052c423e6414b109f59052c433d6414b108f59052c427e6314b10d798c52c425e6314b109f58c52c435d6314b109758c52c436e6214b10dd98452c43796014b109fd9742c427e65d0b109f59742c427c65d0b10cf95342c433d54d0b10dbd4b42c436c52d0b109fd9642c427e6590b109f59642c427c6590b10cfd5242c433c5490b109fd9542c427e6550b109f59542c427c6550b10cf95142c433d5450b109fd9442c427e6510b109f59442c427c6510b10cfd5042c433c5410b10dbd4842c436c5210b10bd98442c42f56110b109fd9732c427e65ccb109f59732c427c65ccb10d794f32c435d53ccb10bd98732c42f561ccb109fd9632c427e658cb109f59632c427c658cb109fd9532c427e654cb109f59532c427c654cb10afd9132c42bc644cb10d794d32c435d534cb10bed8132c42f8604cb109fd9432c427e650cb109f59432c427c650cb10bd98432c42f5610cb10cfd5341c433c54d0710cf95241c433d5490710b798e41c42dd6390710be98241c42f96090710cfd5141c433c5450710bbd8941c42ec6250710cf95041c433d5410710be98041c42f96010710d7d4f31c435c53cc710af99231c42bd648c710d794e31c435d538c710be98231c42f9608c710dd59631c43b6648c710ed59231c4376538c710f594e31c43d5538c710dd14e31c42f6608c710fc98231c43f1608c710d7d4d31c435c534c710bdd9531c4377654c710f5d8d31c43d7534c710dd94d31c4374534c710f514d31c43d7434c710f510d31c43d7324c710f54c931c42f4604c710d794c31c435d530c710f54c431c42fa600c710be58031c436f52c8710db14b21c436e5288710db54a21c42fa6088710be58221c42bf6448710af19121c436f5248710db14921c42be6408710af59021c42de6308710b758c21c436e5208710db54821c42fa6008710be58021c433e54d0310cf55340c42f661d0310bd58740c42ee6290310bb58a40c433e5450310cf55140c42df6350310b718d40c42f76150310bd18540c435e53cc310d754f30c42f661cc310bd58730c43d531cc310afd9130c42bc644c310d794d30c435d534c310bdd8530c42f4614c310f54c530c42be640c310af59030c42ee620c310bb58830c42f6610c310bd58430c43d9300c310db94b20c436d52c8310bd98720c42f561c8310af99220c42bd6488310db94920c436d5248310bdd8520c42f46148310bb98b54842ed62d52109f98f548427d63d52109f98b548436e62d52109b98b548427d62d5210db58b548426d62d5210dd5875484
  | 8 => 0x20be583210827d65884209fd9521082bf6448420af191210836e5248420af99021082bd6408420b798c21082dd6308420dd94421083755108420f948421082fa6008420be580210827e6494020cf992500823e64940209f592500833d64940208f592500827e63940209f58e500827d65d0020cfd53400833c54d00209fd96400827d6590020cf952400833d5490020bb98a40082ed62900209fd95400833f5450020cf15140082df6350020b718d400827f65100209f994400827d65100209f194400833e5410020cf55040082ee6210020bb588400827d65cc0209fd96300827d658c020d794e300835d538c020bb98a30082ed628c0209fd9530082bf644c020af191300827f650c0209f994300827d650c0209f19430082be640c020af590300835e530c020d754c30082ee620c020bb58830082f6610c020bd584300836e54c8020db153200836f53c8020db54f200836d51c8020af99220082bd6488020bb58a200836e5288020ee99220083b96488020be58a200837a5288020fa94a200837951880209fd9520082ef6548020dbd95200826f6548020db951200836c5448020dbd4d200836d5348020db54520082ef6048020db94120083ea4048020fa50120083eb3048020fa0c120082fb6548020ded95200827b6548020bed8920083eb6248020de94920083ea5248020fa90920083e94248020facc920083e83248020de54520083eb2148020fa48520082de63d5310b758f54c427e63d5310d798f54c425e63d53109f58f54c435d63d53109758f54c427e62d53109f58b54c437661d5310de58354c433f54953109f98e54c427d63953109f98a54c427d6295310bbd8954c42ec6255310cfd9154c427f63553109f18d54c427f6255310dbd8954c426f62553109f18954c436c62553109b18954c433d5415310cf99054c427e63153109f58c54c427e62153109f58854c43766115310de58054c42be64d4f10af59353c427e64d4f10cf99353c423e64d4f109f59353c433d64d4f108f59353c427e62d4f109f58b53c437661d4f10de58353c435f5394f109f99253c427d6494f109f98a53c427d6294f10dd98653c427f6454f109f19153c435f6354f109fd8953c427c6254f10d754c53c427e6414f109f59053c435e6314f109f98853c427d6214f10dd98453c43796014f109fd9743c427e65d0f109f59743c427c65d0f10d794f43c435d53d0f109fd9643c427e6590f109f59643c427c6590f10cf95243c433d5490f10bd98643c42f56190f109fd9543c427e6550f109f59543c427c6550f10bed8143c42f86050f109fd9443c427e6510f109f59443c427c6510f10cf95043c433d5410f10d794c43c435d5310f10bd98443c42f56110f109f99352c427d64d4b109f98f52c427d63d4b10dd98752c437960d4b10dbd4a52c427e6
  | 9 => 0x586540833f64550209fd8d540827c63550209fd89540827d62550209fd85540827c6155020cf55054082de6315020b758c54082f66115020bd584540827e6415020cf990540827e6315020d798c540825e63150209f58c540835d63150209758c540827e6215020db988540827e6115020dd984540827661150209f584540837561150209d584540827e6015020de980540827e64d4c209f593530827e62d4c20db98b530827e61d4c209f587530827e60d4c20de983530827d6594c20d7d4e530827e6494c209f592530827e6194c209f58653082bf6454c20af191530827f6454c20cfd91530823f6454c209f191530833c6454c208f191530835f6354c209fd89530827d6254c209fd85530827c6154c20af99053082bd6414c20d754c53082f66114c20bd584530827e6414c20cf990530823e6414c209f590530833d6414c208f590530827e6314c20d798c530827e6214c20db988530826e6214c209f98453083766114c209d984530827d6114c20dd58453082756114c209f980530837a6014c209fd97430827e65d0c209f597430827c65d0c20cf953430833d54d0c209fd96430827e6590c209f596430827c6590c20cfd52430833c5490c20d794e430835d5390c209fd95430827e6550c209f595430827c6550c20cf951430833d5450c20d794d430835d5350c209fd94430827e6510c209f594430827c6510c20cfd50430833c5410c209f992520827d64948209f98e520827d63948209f597420836e52d08209fd96420827d6590820cf952420833d5490820be98242082f960908209fd95420827f65108209f594420833e5410820cf550420836e5210820be98042082f960108209f597320827f658c8209f596320835e538c820d754e320836e528c820be98232082f9608c8209fd9532082bf644c820af191320836e524c8209fd94320827d650c820d794c320835d530c820be98032082f9600c820ddd46510827e64944209f592510827e63944209f58e510827f64544209f191510827f63544209f18d51082be6414420af59051082de6314420b758c510837551144209fd97410827e65d04209f597410833e54d0420cf553410827f65904209f996410827d6590420b798e41082dd6390420dd946410837551904209fd95410827d65504209f195410833e5450420cf55141082ef6250420bb18941083765150420dd545410827f65104209f994410827d65104209fd97310827e65cc4209f597310835e53cc420d754f310827f658c4209f996310827d658c420af99231082bd648c420dd9463108375518c4209fd95310827d654c4209f195310835e534c420d754d31082ef624c420bb1893108376514c420dd54531082fb604c420be181310827f650c4209f994310827d650c420db94b210837651c8420dd54721082fa60c84
  | 10 => 0x1482dd6314520dd544514827e6414520cf990514823e64145209f590514833d64145208f590514827e6314520d798c514825e63145209f58c514835d63145209758c514836f4214520db108514837960145209f997414827d65d05209f197414833e54d0520cf55341483af42d0520ddd47414837451d05209f996414827d65905209f196414833f5490520cf15241482de6390520b758e41482ee6290520bb58a41483ac4290520be98241482f960905209fd95414827e65505209f195414833e5450520cf55141482ef6250520bb18941483af42505209f994414827d65105209f194414833f5410520cf15041482ee6210520bb58841483ac4210520ddd4441483745110520be98041482f960105209f997314827d65cc5209f197314835e53cc520d754f31482ee62cc520bb58b31483cd32cc520ddd47314837451cc5209f996314827d658c5209f19631482be648c520af592314835f538c520d714e31482ee628c520bb58a31482fa608c520be582314827f654c5209f995314827c654c520d794d314835d534c520f34c9314827e650c5209f594314827c650c520d7d4c314835c530c520bb98831482ed620c520ddd443148374510c520be98031482f9600c5209f99721482ee65c8520db99721482ee64c8520bb19321482ef63c8520bb58f214836c51c8520fad8321482ee60c8520fa18321482ed6288520ddd4621483745188520be98221482f96088520afd9121482bc6448520ddd4521483745148520bed8121482f86048520ebd9121482ee6448520bb19121483ac6448520ab19121482ef6348520bb58d21483e76148520f9d45214836c5148520f914521483645148520fad8121482ec6048520fa181214827e6508520af99021482bd6408520b798c21482dd6308520bb98821482fa60085209f997404833f54d0120cf15340482ee62d0120bb58b40483ac42d01209f99640482ee6290120bb58a404827f65501209f595404827c6550120cfd51404833c5450120b7d8d40482dc6350120bbd8940482ec6250120eb109404827e6510120ee500404827e65cc120d7d4f304835c53cc120bb98b30482ed62cc1209f996304827f654c1209f595304827c654c120afd9130482bc644c120d7d4d304835c534c120bbd8930482ec624c1209f99430482be640c120af59030482ee620c120bb58830482f6610c120bd58430483d9300c120fad0b20483e842c8120fa8cb20483e932c8120be58720483eb21c8120fa48720482be6488120af59220482ee6488120eb99220482ae6488120eb59220482ec6488120bbd8e20482ed6388120bb58620483eb50881209f98f540827d63d50209f98b540836e62d50209b98b540827e61d50209f587540827e60d5020de983540827d6595020cfd52540827e63950209f58e540827e61950209f
  | 11 => 0x7d61d5120cfd52544827e64951209f98e544827d63951209f58a544836d62951209f986544827d61951209f58254483796095120b7d8d54482dc6355120bdd8554482f46155120cfd91544827f6355120d7d8d544825f63551209f18d544835c63551209718d544827f6255120dbd89544827f6155120ddd85544827761551209f185544837461551209d185544827f6055120ded81544827e6515120cf550544833e64151209f98c544827d63151209f988544827c62151209f984544827d61151209f993534827d64d4d209f987534827d61d4d20d7d4e534827e6494d209f592534827e6394d209f58a534836d6294d209f986534827d6194d209f58253483796094d20afd9153482bc6454d20bdd8553482f46154d209fd91534833f6454d208fd91534827c6454d20cf191534823c6454d20d7d8d534827f6254d20dbd89534827f6154d20ddd8553482776154d209f18553483746154d209d185534827f6054d20ded81534827e6514d20d754c534827e6414d209f590534835e6314d209f988534836d6214d209f188534827e6114d209f584534827f65d0d209f997434827d65d0d209f197434835f53d0d20d714f434827f6590d209f996434827d6590d209f196434833f5490d20cf15243482ee6290d20bb58a434827f6550d209f995434827d6550d209f19543482ef6250d20bb18943482fb6050d20be181434827f6510d209f994434827d6510d209f194434833f5410d20cf150434835f5310d20d714c43482ee6210d20bb58843482fa6010d20be580434827e65d0920cfd53424833c54d0920be98342482f960d0920db997424826e65d0920dbd5342483af54d0920db55342483ac54d0920bb58f42482ed61d0920bb98342483ea60d0920ba98342483e960d09209f996424833e5490920cf55242482ee62909209f195424833f5450920cf15142482fb6050920be181424827e6510920cf950424833d5410920eb50842482ee6510920db99442482ee6410920eb990424836f5410920eb950424836d5410920eb55042482ed6310920eb90c42483ac4310920bb58442482ee60109209f997324835f53cc920d714f32482fa60cc920be583324827e658c920bb996324836e658c920bb99232482ec648c920bb58e324836e538c920db14e32482ed618c920bb982324827c654c920afd9132482bc644c920d7d4d324835c534c920bed8132482f8604c920db195324826c654c920ebd9132482ee644c920bb19132483ac644c920ab19132483cf634c920f3d4d324836e534c920db14d32483cc534c920bbd8532483eb604c920bb18132483e8604c920ba181324827e650c920bb988324827e64d45209f593514827e63d45209f58f51483775194520afd9151482bc6454520b7d8d51482dc6354520af99051482bd6414520b798c5
  | 12 => 0x50e209f195438833e5450e20cf55143882fb6050e20be181438827f6510e209f994438827d6510e209f194438833e5410e20cf55043882fa6010e20be580438833e54d0a20cf55342882fa60d0a20be583428833e5490a20cf552428833e5450a20cf55142882fb6050a20be181428833e5410a20cf550428833e54cca20cf553328835e53cca20d754f32882fa60cca20be583328833e548ca20cf55232882bf644ca20af191328833e544ca20cf551328835e534ca20d754d32882fb604ca20be181328833e540ca20cf55032882be64d4620af593518833e54d4620cf553518833e5494620cf552518837751946209f992518827d64946209f98e518827d6394620de982518833e5454620cf551518827f64546209f191518827f63546209f18d51882be6414620af590518833e5414620cf55051882de6314620b758c518837551146209fd97418827e65d06209f597418833e54d0620cf553418827f65906209f996418827d6590620cf952418833d5490620b798e41882dd6390620be98241882f960906209fd95418827d65506209f195418833e5450620cf55141882ef6250620bb189418827f65106209f994418827d6510620cf950418833d5410620be98041882f960106209fd97318827e65cc6209f597318833e54cc620cf553318835e53cc620d754f318827f658c6209f996318827d658c620af99231882bd648c620cf952318833d548c620dd9463188375518c620be98231882f9608c6209fd95318827d654c6209f195318833e544c620cf551318835e534c620d754d31882ef624c620bb1893188376514c620dd545318827f650c6209f994318827d650c620cf950318833d540c620be98031882f9600c620cf953218833d54c8620cf952218833d5488620dd94621883755188620be98221882f96088620afd9121882bc6448620cf951218833d5448620dd94521883755148620bed8121882f86048620af99021882bd6408620cf950218833d5408620b798c21882dd6308620f948421882f96008620cf953408833d54d0220cf952408833d5490220bb98a40882ed6290220cf951408833d5450220b7d8d40882dc6350220cf950408833d5410220bb98840882ed6210220ee500408833e54cc220cf553308833e548c220cf552308835e538c220d754e30882ee628c220bb58a30882bf644c220af191308833e544c220cf55130882be640c220af590308833e540c220cf550308835e530c220d754c30882ee620c220bb58830882f6610c220bd58430883d9300c220cf953208833d54c8220bb597208836d65c8220db95320883ae54c8220cb95320883ad54c8220db153208836f53c8220db54f208836d51c8220be597208837965c8220ee95320883b954c8220be587208827e63d51209f58f544836d62d51209f98754482
  | 13 => 0xbb18941c83af42507209fd9441c827e65107209f59441c82ee6210720bb58841c83ac42107209fd9731c827e65cc7209f59731c835e53cc720d754f31c82ee62cc720bb58b31c83cd32cc7209fd9631c827e658c7209f59631c82be648c720af59231c82ee628c720bb58a31c827f654c7209f59531c827c654c720d794d31c835d534c720f34c931c82fb604c720be18131c827f650c7209f99431c827d650c720bb98831c82ed620c720dd94721c837551c8720be98321c82f960c8720bb99321c82ec64c8720bbd8f21c82ed63c8720db94721c83e651c8720f954721c82ee60c8720fa98321c83e960c8720afd9121c82bc6448720bbd9521c836f6548720ebd9121c82ee6448720bb19121c83ac6448720ab19121c82ef6348720bb58d21c83e76148720db94521c82ec6048720af99021c82bd6408720b798c21c82dd6308720dd94421c83755108720be98021c82f96008720cf95340c833d54d0320bb98b40c82ed62d0320eb10b40c82ee6290320bb58a40c833e5450320cf55140c82df6350320b718d40c82ef6250320bb18940c83ac4250320d794f30c835d53cc320bb98b30c82ed62cc320afd9130c82bc644c320d794d30c835d534c320bbd8930c82ec624c320af99030c82bd640c320bb98830c82ed620c320bd98430c82f5610c3209f98f548827d63d5220db58b548827e61d52209f587548837a60d5220cfd52548827e63952209f58e548827e61952209f586548833f6395220cf98e548833d6395220cf18e548833f6295220cf58a548833f6195220cf986548833d6195220cf186548833e6095220cf182548833f64552209fd8d548827c63552209fd85548827c6155220cfd95548833f6355220cf98d548833d6355220cf18d548833f6255220cf589548833f6155220cf985548833d6155220cf185548833e6055220cf181548833d5415220cf990548827e63152209f58c548836d62152209f984548827d6115220de98054882be64d4e20af593538833e54d4e20cf553538827e64d4e20cf993538823e64d4e209f593538833d64d4e208f593538836d62d4e209f987538827d61d4e20de983538833e5494e20cf552538835f5394e209f992538827d6494e209f986538827d6194e20cf951538833d5454e209fd91538827c6454e20d7d8d538827f6154e209f18553882be6414e20af590538833e5414e20cf550538835d5314e20bd98453882f56114e209f990538833e6414e208f990538827d6414e20cf590538823d6414e20d798c538836d6214e209f98453883766114e209d984538827d6114e20dd58453882756114e20de980538827f65d0e209f997438827d65d0e209f197438833e54d0e20cf553438827f6590e209f996438827d6590e209f196438833e5490e20cf552438827f6550e209f995438827d65
  | 14 => 0x45300c2df604c030d7941300c3da404c030f6501300c2fb654c030ded95300c27b654c030eed91300c3b8644c030ee951300c3b9544c030bed8d300c3db634c030de94d300c3da534c030f690d300c3d9434c030fa949300c3e9524c030f6cc9300c3d9324c030fc945300c3f1514c030f68c5300c3d8314c030b798f54c82dd63d53209f98f54c835e63d53209798f54c827d63d5320d758f54c825d63d5320db98b54c827e61d53209f58754c837960d5320cfd5254c827e63953209f58e54c827e61953209f58654c833f64553209fd8d54c827c6355320db18954c827f61553209f18554c833d5415320cf99054c827e63153209f58c54c836e62153209f98454c827d6115320de58054c82be64d4f20af59353c827e64d4f20cf99353c823e64d4f209f59353c833d64d4f208f59353c836e62d4f209f98753c827d61d4f20de58353c835f5394f209f99253c827d6494f20db98a53c827e6194f209f58653c827f6454f209f19153c835f6354f209fd8553c827c6154f20d754c53c827e6414f209f59053c835e6314f20db98853c827e6114f209f58453c83796014f209fd9743c827e65d0f209f59743c827c65d0f20d794f43c835d53d0f209fd9643c827e6590f209f59643c827c6590f20cf95243c833d5490f20bb98a43c82ed6290f209fd9543c827e6550f209f59543c827c6550f20bbd8943c82ec6250f209fd9443c827e6510f209f59443c827c6510f20cf95043c833d5410f20d794c43c835d5310f20bb98843c82ed6210f20bb59742c836d65d0b20dbd5342c836d54d0b20bb58f42c82ed61d0b20bb98342c833e5490b20cf55242c82fa6090b20be58242c833e5410b20cf55042c83ad4210b20be98042c82f96010b20db59442c83ae6410b20dbd5042c83ae5410b20db55042c83ad5410b20bb58c42c83ae4310b20eb10c42c82ed6110b20bb98042c83ea6010b20fa58042c835e538cb20d754e32c82fa608cb20be58232c836d658cb20bb99232c82ec648cb20db94e32c83ce538cb20f354e32c836c538cb20bb58632c82ee608cb20fa98232c83e9608cb20afd9132c82bc644cb20bbd9532c836f654cb20ebd9132c82ee644cb20bb19132c83ac644cb20ab19132c83cf634cb20db94d32c836c534cb20bbd8532c82ec604cb20d794c32c835d530cb20be98032c82f9600cb20ddd4651c827e64947209f59251c827e63947209f58e51c836f4294720db10a51c827f64547209f19151c827f63547209f18d51c82be6414720af59051c82de6314720b758c51c837551147209fd9741c827e65d07209f59741c833e54d0720cf55341c83af42d07209fd9641c827e65907209f59641c82de6390720b758e41c82ee6290720bb58a41c83ac42907209fd9541c827d65507209f19541c833e5450720cf55141c82ef625072
  | 15 => 0xc36d5290430dd946410c37551904309fd95410c27d65504309f195410c33e5450430cf551410c2df6350430b718d410c39c4350430bbd89410c2ec6250430db949410c36d5250430dd945410c3755150430bed81410c2f860504309fd94410c27e65104309f594410c33e5410430cf550410c36e5210430db548410c3765110430dd544410c33e54cc430cf553310c35e53cc430db94b310c36d52cc430dd947310c37551cc430be983310c2f960cc4309f596310c2be648c430af592310c33e548c430cf552310c36e528c430db54a310c375518c4309fd95310c33e544c430cf551310c35e534c430db949310c36d524c430dd945310c33e540c430cf550310c36e520c430db548310c376510c430dd544310c2fa600c430be580310c27f65c84309f997210c27d65c8430cf953210c33d54c8430db94b210c36d52c8430dd947210c37551c84309fd96210c27e65884309f596210c33e5488430cf552210c36e5288430db54a210c3765188430dd546210c27f65484309f595210c27c6548430afd91210c2bc6448430cf951210c33d5448430b7d8d210c2dc6348430db949210c36d5248430dd945210c3755148430bed81210c2f860484309fd94210c27e65084309f594210c2be6408430af590210c33e5408430cf550210c2de6308430b758c210c36e5208430db548210c3765108430dd544210c2fa6008430be580210c27e64940309f592500c35f4394030d710e500c27d65d0030cf953400c33d54d0030e7d0f400c36e52d0030db54b400c37651d0030dd547400c27f65900309f596400c33e5490030cf552400c2de6390030b758e400c39c4390030bb98a400c2ed6290030db94a400c36d5290030dd946400c37551900309fd95400c33e5450030cf551400c2df6350030b718d400c39f4350030db949400c36d5250030dd945400c37551500309fd94400c27e65100309f594400c27c6510030cf950400c33d5410030b798c400c2dd6310030e710c400c36e5210030db548400c3765110030dd544400c33e54cc030cf553300c36e52cc030db54b300c37651cc030dd547300c2de64cc030b7193300c39e54cc030e7553300c3ce52cc030f354b300c3d651cc030d7547300c3d551cc030d5547300c33e548c030cf552300c2dd638c030d794e300c36e528c030db54a300c376518c030dd546300c3ba548c030ee552300c2f9638c030de94e300c3da538c030f6d0e300c3d8438c030fa94a300c3e9528c030fc946300c3f1518c0309fd95300c2bf644c030af191300c33e544c030cf551300c36e524c030db549300c376514c030dd545300c2df654c030d7d95300c25f654c030e7d91300c2de644c030b7191300c39c644c030a7191300c39e544c030e7551300c3ce524c030f3549300c3d6514c030d7545300c3d5514c030d55
  | 16 => 0xd4354830db10d520c36f6154830db985520c36d6154830db185520c36e6054830db181520c36c3054830af990520c2bd6414830cf950520c33d5414830bb988520c36d5214830bd984520c2f561148309fd97420c27e65d08309f597420c33e54d0830cf553420c36e52d0830db54b420c27f65908309f996420c27d6590830cf952420c33d5490830b798e420c2dd6390830e710e420c36e5290830db54a420c2fa6090830be582420c27f65508309f595420c27c6550830cf951420c33d5450830b7d8d420c2dc6350830db949420c36d52508309fd94420c27e65108309f594420c33e5410830cf550420c39c4310830db948420c36d5210830cf953320c33d54cc830db94b320c36d52cc830be983320c2f960cc8309f596320c33e548c830cf552320c36d528c8309fd95320c2bf644c830af191320c33e544c830cf551320c36e524c830cf950320c33d540c830db948320c36d520c830be980320c2f9600c830af993510c2bd64d4430cf953510c33d54d4430bb98b510c2ed62d4430db94b510c36d52d4430cf952510c33d5494430db94a510c36d5294430ddd46510c27e64944309f592510c27e62944309f58a510c3775494430dd952510c3b65494430cd952510c3755494430ed552510c3355494430dd152510c3d74394430f510e510c3775294430dd94a510c3e65294430d994a510c3755294430f954a510c3655294430dd14a510c3776494430dd992510c3756494430dd192510c3746394430ddd0e510c3764394430dd50e510c3744394430ddd8a510c3766294430dd58a510c3746294430ddd0a510c3764294430dd50a510c3744294430ddcca510c3763294430dd4ca510c3743294430dd982510c3746094430cf951510c33d5454430db949510c36d52544309fd91510c27c6454430d7d0d510c35c43544309fd89510c27c6254430ddd95510c3775454430dd951510c3b65454430cd951510c3755454430ed551510c3355454430dd151510c3d74354430f510d510c3775254430dd949510c3e65254430d9949510c3755254430f9549510c3655254430dd149510c3776454430dd991510c3756454430dd191510c3766354430ddd0d510c3574354430dd90d510c3754354430dd10d510c3544354430ddd89510c3766254430dd589510c3746254430ddd09510c3764254430dd509510c3744254430ddcc9510c3763254430dd4c9510c3743254430dd981510c3746054430dd0c1510c2be6414430af590510c33e5414430cf550510c2ee6214430bb588510c36e5214430db548510c2f66114430dd544510c27f65d04309f997410c27d65d0430cf953410c33d54d0430e710f410c36e52d0430db54b410c37651d0430dd547410c27f65904309f996410c27d6590430cf952410c33d5490430b798e410c2dd6390430db94a41
  | 17 => 0x130cfd51404c33c5450130b7d8d404c2dc63501309f994404c33f5410130cf150404c33f54cc130cf153304c3bb54cc130ee153304c3db31cc130f64c7304c33f548c130cf152304c39f548c130d7952304c35c548c130e7152304c31c548c130b7586304c3db508c130bb98b540c2ed62d5030bd987540c2f561d50309f98f540c35e63d50309f98b540c36e62d50309b98b540c27d62d5030db58b540c26d62d50309f987540c37661d50309d987540c27d61d5030dd587540c27561d50309f983540c37a60d50309f596540c33f54950309f98a540c27d62950309f986540c27d61950308f596540c39c6395030cf98e540c33c6395030cfd8a540c33e6295030cf58a540c33c6295030cfd86540c33e6195030cf586540c33c6195030cf982540c33c6095030cfd91540c27f63550309f58d540c35c63550309fd89540c27c62550309fd85540c27c6155030cfd95540c39c6355030cf98d540c33c6355030c718d540c33f6255030cf989540c33d6255030cf189540c33f6155030cf985540c33d6155030cf185540c33e6055030cf181540c33c3055030af990540c33d5415030bb988540c2ed6215030bd984540c2f561150309f990540c33e64150308f990540c27e6315030d798c540c27e6215030db988540c26e62150309f588540c36d62150309b588540c27e6115030dd984540c27661150309f584540c37561150309d584540c27e6015030de980540c27e6494c309f592530c27d65d0c30cf953430c33d54d0c30b7597430c35d65d0c30d7d53430c39e54d0c30d7553430c39d54d0c30c7553430c2dd60d0c309fd96430c27d6590c30cf952430c33d5490c30b798e430c2fa6090c30be582430c27f6550c30cf951430c33d5450c309fd94430c27d6510c30cf950430c33d5410c30e750c430c2fa6010c30be580430c35d6510c3097594430c2de6410c30e7990430c35f5410c30e7950430c35d5410c30e7550430c3da6010c30b7580430c3d96010c30b6580430c2be64d4830af593520c33e54d4830cf553520c2f661d4830bd587520c33e5494830cf552520c36f52948309f992520c27d64948309f986520c27d6194830dbd52520c36e5494830eb952520c32e5494830db552520c3ad5494830cb552520c36c5494830f3d0e520c3cc4394830dbd92520c36e6494830db592520c36c6494830db18e520c36f4394830db90e520c36d4394830db10e520c36f6194830db986520c36d6194830db186520c36e6094830db182520c33e5454830cf551520c27f64548309f191520c27f61548309f185520c36f6554830dbd51520c36e5454830eb951520c32e5454830db551520c3ad5454830cb551520c36c5454830f3d0d520c3cc4354830dbd91520c36e6454830db591520c36c6454830db98d520c36f4354830db90d520c36
  | 18 => 0x9f993524c27d64d49309f987524c27d61d4930af992524c2bd6494930cfd52524c33c5494930dbd4a524c2bf6454930af191524c33f5454930cf151524c2f76154930bd185524c33f5414930cf150524c36d52149309f990524c27d64149309f984524c27d61149309f997424c27d65d09309f197424c33f54d0930cf153424c27e65909309f596424c27c6590930cfd52424c33c54909309fd95424c27e65509309f195424c33f5450930cf151424c27e65109309f594424c27c6510930cfd50424c33c5410930b798c424c2dd6310930be980424c2f960109309f997324c33f54cc930cf153324c33f548c930cf152324c36f528c930db14a324c2fa608c930be582324c2bf644c930af191324c33f544c930cf151324c36f524c930db149324c2fb604c930be181324c27e650c930cfd50324c33c540c930cfd53514c33c54d45309f993514c27d64d45309f98b514c27d62d4530af992514c2bd6494530cfd52514c33c5494530ddd46514c2bf6454530af191514c33f5454530cf151514c2ef6254530bb189514c33f5414530cf150514c37551145309f990514c27d64145309f988514c27d62145309f997414c27d65d05309f197414c33f54d0530cf153414c27e65905309f596414c27c6590530cfd52414c33c5490530b798e414c2dd63905309fd95414c27e65505309f195414c33f5450530cf151414c2ef6250530bb189414c27e65105309f594414c27c6510530cfd50414c33c5410530b798c414c2dd6310530be980414c2f960105309f997314c33f54cc530cf153314c2de65cc530d7997314c39f54cc530d7953314c35c54cc530e7153314c31c54cc530d7d4b314c35c51cc530b7983314c2be648c530af592314c33f548c530cf152314c2dd638c530ddd46314c374518c530be982314c2f9608c530cfd51314c33c544c530ddd45314c374514c530bed81314c2f8604c530e7d51314c35e544c530d7151314c39c544c530c7151314c35f524c530f5d85314c3d7514c530d7145314c3d4514c530f6d81314c2dc604c530f6181314c2d8604c5309f994314c33f540c530cf150314c2de630c530f54c4314c27e65c85309f597214c27c65c8530cfd53214c33c54c8530ddd47214c37451c85309f996214c27d65885309f196214c33f5488530cf152214c2de6388530b758e214c36f5288530db14a214c27f65485309f995214c27c6548530afd91214c2bc6448530cfd51214c33c54485309f994214c27d65085309f194214c2be6408530af590214c33f5408530cf150214c2de6308530b758c214c36f5208530db148214c3775108530dd144214c2fa6008530be580214c27e65d0130cfd53404c33c54d0130b798f404c2dd63d01309f996404c33f5490130cf152404c2ee6290130bb58a404c27f65501309f595404c27c655
  | 19 => 0x6428c33e5490a30cf552428c2de6390a30b758e428c39c4390a309fd95428c27d6550a309f195428c2df6350a30b718d428c27f6510a309f994428c27d6510a30cf950428c33d5410a30e710c428c36e5210a30db548428c2fa6010a30be580428c36e528ca30db54a328c2fa608ca30be582328c2bf644ca30af191328c36e524ca30db549328c2fb604ca30be181328c37751946309f992518c27d64946309f98a518c27d62946309fd91518c27c6454630d7d0d518c35c43546309fd89518c27c6254630af990518c2bd6414630bb988518c2ed6214630dd544518c27f65d06309f997418c27d65d0630cf953418c33d54d0630e710f418c27f65906309f996418c27d6590630b798e418c2dd63906309fd95418c27d65506309f195418c33e5450630cf551418c2df6350630b718d418c39c4350630bbd89418c2ec62506309fd94418c27e65106309f594418c2fa6010630be580418c2be648c630af592318c376518c630dd546318c2fa608c630be582318c376514c630dd545318c2fb604c630be181318c27f65c86309f997218c27d65c8630db94b218c36d52c86309fd96218c27e65886309f596218c27f65486309f595218c27c6548630afd91218c2bc6448630b7d8d218c2dc6348630db949218c36d52486309fd94218c27e65086309f594218c2be6408630af590218c2de6308630b758c218c2fa6008630be580218c33f54d0230cf153408c39f43d0230cf952408c33d5490230b798e408c2dd6390230e710e408c2ee6290230bb58a408c33f5450230cf151408c2df6350230b718d408c39f4350230cf950408c33d5410230b798c408c2dd6310230e710c408c2dd65cc230d7597308c2de64cc230b7193308c35d51cc230be597308c37965cc2309f98b544c27d62d51309f987544c27d61d5130cfd8f544c33d63d5130cfd8b544c33e62d5130cf58b544c33c62d5130cfd87544c33e61d5130cf587544c33c61d5130cfd83544c33d60d5130cfd52544c27e64951308f992544c27d6395130d758e544c27e62951309f58a544c27e61951309f586544c27d6095130de582544c33f64551309fd8d544c35f635513097d8d544c27f62551309f189544c27f61551309f185544c27f6055130ded81544c27e6515130cf550544c33e64151309f98c544c27c63151309f988544c27d62151309f984544c27d6115130af994544c33e65151308f994544c33f6315130cf58c544c33f6215130cf988544c33d6215130cf188544c33f6115130cf984544c33d6115130cf184544c33f6015130cf580544c33d30151309f997434c33f54d0d30cf153434c2fa60d0d30be583434c27e6590d30cfd52434c33c5490d309f195434c33f5450d30cf151434c2fb6050d30be181434c27e6510d30cfd50434c33c5410d30cfd53524c33c54d4930
  | 20 => 0xc27d65d0b309fd9642cc27e6590b309f59642cc33f5490b30cf15242cc2fa6090b30be58242cc27f6550b309f59542cc27c6550b309fd9442cc27e6510b309f59442cc33f5410b30cf15042cc2de6310b30b758c42cc36e52ccb30db54b32cc2fa60ccb30be58332cc2bf644cb30af19132cc36e520cb30db54832cc2fa600cb30be58032cc2be6494730af59251cc37751947309f99251cc33e64947308f99251cc27d6494730cf59251cc23d64947309f98a51cc27d62947309fd9151cc27c64547309fd8951cc27c6254730dd54451cc27f65d07309f99741cc27d65d0730cfd5341cc33c54d07309fd9641cc27e65907309f59641cc2de6390730b758e41cc27f65507309f59541cc27c6550730cfd5141cc33c5450730bbd8941cc2ec6250730bed8141cc2f860507309fd9441cc27e65107309f59441cc2de6310730b758c41cc37651cc730dd54731cc2fa60cc730be58331cc35e54cc730d715331cc35d52cc730d794731cc3d651cc730f554731cc2de60cc730f698331cc3d960cc730af99231cc2bd648c730b7d9531cc35f654c730d795131cc35c544c730d754931cc3d7614c730f5d4531cc35e514c730f514531cc2dc604c730dd94431cc375510c730f54c431cc2fa600c730be58031cc27f65c87309f99721cc27d65c87309fd9621cc27e65887309f59621cc2de6388730b758e21cc27f65487309f59521cc27c6548730afd9121cc2bc6448730bed8121cc2f860487309fd9421cc27e65087309f59421cc2be6408730af59021cc2de6308730b758c21cc2fa6008730be58021cc33e54d0330cf55340cc2de63d0330b758f40cc33f5490330cf15240cc2ee6290330bb58a40cc33e5450330cf55140cc2df6350330b718d40cc33f5410330cf15040cc2ee62d5230bb58b548c35d63d52309f98b548c36e62d52309b98b548c27d62d5230db58b548c26d62d52309f987548c27d61d5230de983548c33f54952309f98a548c27d62952309f986548c27d6195230cfd91548c35f63552309fd89548c27c62552309fd85548c27c6155230cf550548c33e6415230d758c548c27e62152309f588548c27e61152309f584548c37a6015230cf953438c33d54d0e30be983438c2f960d0e30d7597438c35f54d0e30e7953438c35d54d0e30e7553438c3da60d0e30b7583438c3d960d0e30cfd52438c33c5490e30cf951438c33d5450e30bed81438c2f86050e30cfd50438c33c5410e30e750c438c2dd6510e30d7594438c39e6410e30d7d50438c39f5410e30d7550438c39c5410e30b7580438c2be64d4a30af593528c36f5294a309f992528c27d6494a309f986528c27d6194a309fd91528c27c6454a309fd85528c27c6154a30db548528c27f65d0a309f997428c27d65d0a30db94b428c36d52d0a309fd96428c27e6590a309f59
  | 21 => 0x5210840be98042102f960108409fd97321027e65cc8409f597321035e53cc840d754f321027f658c8409f996321027d658c840af99232102bd648c840db94a321036d528c840be98232102f9608c8409fd95321027d654c8409f19532102bf644c840af191321035e534c840d754d321036e524c840db549321027f650c8409f994321027d650c840ddd46511027e63944409f58e511027e62944409f58a511027f63544409f18d511033e4354440cf10d511027f62544409f18951102de6314440b758c51102ee6214440bb58851103755114440cf953411037651d0440dd54741102fa60d0440be583411027d6590440b798e41102dd63904409fd95411033e5450440bbd8941102ec6250440dd94441103755110440be98041102f960104409fd97311027e65cc4409f597311035e53cc440d754f311039c43cc4409fd96311027e658c4409f59631102be648c440af5923110376518c440dd546311027f654c4409f595311027c654c440afd9131102bc644c440d794d311035d534c440e710d3110376514c440dd54531102fb604c440be181311027f650c4409f994311027d650c4409fd97211027e65c84409f597211036e52c8440db54b211027f65884409f996211027d6588440dd946211037551884409fd95211027d65484409f19521102bf6448440af191211036e5248440db54921103765148440dd545211027f65084409f994211027d6508440af99021102bd6408440b798c21102dd6308440be98021102f96008440cf90e501033c4394040db98a501036d6294040af98f401033d53d0040cf94b401033d51d0040af592401033e5490040bb98a40102ed6290040be592401037a5490040ee95240103ba4390040ee10e40103ea6290040fa58a401027f6550040b7d8d40102dc6350040afd95401033f65500408fd95401039f6350040af18d401039c6350040a718d401033d5350040cf949401033d5150040afd81401033e5050040bed95401037b65500409ed9540102fb6450040eed91401037a5450040ee95140103db6350040f618d40103bb4250040ee509401035e63d53309f98b54cc27d62d53309f98754cc27d61d5330de58354cc33f54953309f98a54cc27d62953309f98654cc27d6195330cfd9154cc27f62553309f18954cc27f61553309f18554cc33d5415330cf99054cc35e63153309f98854cc27d62153309f98454cc27d6115330de58054cc33f54d0f30cf15343cc33e5490f30cf55243cc2fa6090f30be58243cc33f5450f30cf15143cc33e5410f30cf55043cc2fa6010f30be58043cc36f5294b309f99252cc27d6494b309f98652cc27d6194b30afd9152cc2bc6454b309fd9152cc33f6454b308fd9152cc27c6454b30cf19152cc23c6454b309fd8552cc27c6154b30db54852cc27f65d0b309f99742c
  | 22 => 0x540d714f41502be65d0540cf99741502bd63d0540e7d4f415033c53d0540e714f415031c53d0540af98b415033f52d0540cf14741502be60d0540af59241502de6390540b758e415035f5390540d714e41503775190540dd14641502fa6090540be582415035f5350540d714d41502ef6250540bb18941503775150540dd14541502fb6050540be18141502bf6350540e7d4d415033c5350540e714d415031c5350540ebd8941502bc6250540eb18941502ac6250540cfd4941503b76150540edd45415033c5150540ed14541503bb6050540af18141503b860505409f99441502be6410540d7d4c415035c53105409f997315027d65cc5409f19731502be64cc540af593315035f53cc540d714f315039f43cc5409f996315027d658c5409f19631502be648c540af592315035f538c540d714e315027f654c5409f995315027c654c540af99131502bd644c540d7d4d315035c534c540e7d0d315027e650c5409f594315027c650c540af99031502bd640c540d7d4c315035c530c540be98031502f9600c5409f997215027d65c85409f19721502bf64c8540af193215035f53c8540d714f215037751c8540dd147215027e65885409f596215027c6588540af99221502bd6488540d7d4e215035c5388540dbd4a215036c5288540eb10a215027f65485409f995215027c6548540afd9121502bc6448540d7d4d215035c53485409f994215027d65085409f19421502be6408540af59021502de6308540b758c215035f5308540d714c215036f5208540db14821503ac4208540ddd4421503745108540be98021502f96008540d7d4f405035c53d0140f6d4f40503d853d0140eed0f40503b943d0140ee90b40503b842d0140eed0740503b941d0140d7d4e405035c5390140bb98a40502ed6290140af58e405039f5390140cf14e405039c5390140c714e40502be6290140eb98a40502ae6290140eb58a40502bd6190140eed42405035f5394c409f98a531027d6294c409f986531027d6194c409fd89531027c6254c409fd85531027c6154c40d754c53102ee6214c40bb58853102f66114c40bd584531033e54d0c40d794f431035d53d0c40be98343102f960d0c409f59643102bd6590c40cf596431023d6590c40af98e431033d5390c40af582431027f6550c40cf951431035e5310c40d754c431039d4310c40be98043102f96010c40af98c431039e6310c40e794c431033d5310c40e754c43103ba6010c40af58043103b96010c40dbd4a521027e63948409f58e521033e4394840cf10e521027e61948409f586521027f63548409f18d521027f61548409f18552102de6314840b758c521036d5214840bd98452102f56114840db94b421036d52d0840be98342102f960d08409f596421033e54908409fd95421033e5410840db948421036d
  | 23 => 0xe580219036e52d0240db54b40902bd65d0240cf59740902be63d0240cf54f409033e52d0240eb94b409032e52d0240eb54b409033d51d0240be597409037965d0240fa94b40903e952d02409f98b535027d62d4d409f987535027d61d4d40e7d93535035f64d4d40d7d8b535035e62d4d40d758b535035c62d4d40d7d87535035e61d4d40d7587535035c61d4d40d7d83535035d60d4d40d7d4e535035d5314d409f988535027d6214d409f984535027d6114d40b7994535035e6514d40e7590535035f6414d40d7d88535035e6214d40d7588535035c6214d40d7d84535035e6114d40d7584535035c6114d40d7d80535035d6014d40d7500535027e65d0d40d714f43502be65d0d40cf997435023e65d0d40e7d4f435033c53d0d40e714f435031c53d0d40af98b43502bd61d0d40af98343502bd6490d40d7d4e435035c5390d40be98243502f96090d40d7d4d435035c5350d40bed8143502f86050d40e7d8d435039f5350d40cf14d435039c5350d40c714d43502bc6250d40afd8543503bb6050d40af18143503b86050d409f99443502be6410d40d7d4c435035f53d4940d714f525027e63d49409f58f525027e61d49409f58752502de6394940b758e525035f5394940d714e525036f5294940b7d8d52502dc6354940d7d4d525035c5354940bdd8552502f46154940d7d4c525035c5314940db548525027e63149409f58c525027e61149409f584525027e65d0940d7d4f425035c53d0940d7d4e425035c5390940dbd4a425036c5290940be98242502f96090940af58e425039f5390940cf14e425039c5390940c714e42502be6290940cfd4a42503af5290940eb14a42502bd6190940af98242503ba6090940ae98242503b96090940d7d4d425035c5350940dbd49425036c5250940bed8142502f860509409f994425035f5310940d714c42503ad4210940af994425033e6510940af58c425039f5310940cf14c425039c5310940c714c42502be6210940eb988425033f5210940eb94842503ad5210940af58442502be60109409f997325027d65cc9409f19732502be64cc940af593325035f53cc940d714f325027e658c9409f596325027c658c940afd9232502bc648c940d7d4e325035c538c9409fd95325027e654c9409f19532502bf644c940af191325035f534c940d714d325027e650c9409f594325027c650c940af99032502bd640c940d7d4c325035c530c940be98032502f9600c940d7d4f515035c53d45409f98f515027d63d45409f98b515027d62d4540b798e51502dd6394540d7d4e515035c5394540ddd4651502df6354540b718d515035f5354540d714d51502ef6254540bb189515035f5314540d714c515037551145409f98c515027d63145409f988515027d6214540cf908515033c42145409f997415035f53d0
  | 24 => 0x43903b96090e40d794d439035d5350e40bed8143902f86050e40e750c43902bd6510e40cf594439039e6310e40e7d4c439033d5310e40e714c43902bd6010e40dbd4a529027e6394a409f58e529033e4394a40cf10e529027e6194a409f586529036f5394a40db94e529036d5394a40db14e52903ae4394a40eb10e529036f6494a40dbd8e529036e6394a40db58e529036c6394a40dbd0e529036e4394a40cb90e529036d4394a40db10e529032c4394a40dbd86529036e6194a40db586529036c6194a40db982529036c6094a409fd8d529027c6354a409fd85529027c6154a40dbd95529036f5354a40db94d529036d5354a40db14d52903ae4354a40eb10d529036d6454a40dbd8d529036e6354a40db58d529036c6354a40dbd0d529036e4354a40db50d529036c4354a40dbd85529036e6154a40db585529036c6154a40db981529036c6054a40db548529036e52d0a40db94a429036d5290a40be98242902f96090a40db949429036d5250a40bed8142902f86050a40db548429027f65cca409f997329027d65cca40db94b329036d52cca409fd96329027e658ca409f59632902be648ca40af592329036e528ca40db54a329027f654ca409f595329027c654ca40afd9132902bc644ca40db949329036d524ca409fd94329027e650ca409f594329036e520ca40db54832902fa600ca40be58032902ee62d4640bb58b519036e52d4640db54b519036e5294640db54a519037751946409f98e519027d63946409f98a519027d6294640db949519036d52546409fd8d519027c6354640cf90d519033c43546409fd89519027c6254640b798c51902dd6314640bb98851902ed6214640db948519036d5214640dd544519036e52d0640db54b41902de6390640b758e419036e5290640db54a41903765190640dd54641902fa6090640be58241902ef6250640bb189419036e5250640db54941903765150640dd54541902fb6050640be181419036e5210640db548419027f65cc6409f997319027d65cc640d794f319035d53cc640e710f319036e52cc640db54b319027f658c6409f996319027d658c640af99231902bd648c640db94a319036d528c640dd9463190375518c6409fd95319027d654c6409f19531902bf644c640af191319035e534c640d754d319039c434c640db949319036d524c640dd9453190375514c6409fd94319027e650c6409f594319036e520c640db54831902fa600c640be580319027f65c86409f997219027d65c8640db94b219036d52c86409fd96219027e65886409f596219036e5288640db54a219027f65486409f595219027c6548640afd9121902bc6448640db949219036d52486409fd94219027e65086409f59421902be6408640af59021902de6308640b758c219036e5208640db54821902fa6008640b
  | 25 => 0x27d6294f409f98653d027d6194f409fd8953d027c6254f409fd8553d027c6154f40d754c53d035e53d0f40d754f43d02fa60d0f40be58343d033e53d0f40e794f43d039d53d0f40af98b43d02bd61d0f40af98343d03ba60d0f40ee58343d02bf6550f40cfd9543d039f6350f40cf94d43d02bc6250f40afd8543d02bc6050f40d794c43d035d5310f40be98043d02f96010f40dbd4a52d027e6394b409f58e52d027e6194b409f58652d027f6354b409f18d52d027f6154b409f18552d036d5214b40db94b42d036d52d0b40be98342d02f960d0b40af59642d033d6590b40af58e42d033e5390b40cf54a42d02bd6190b40af98242d036e5210b40db54842d03ad4210b40be98042d02f96010b40af58c42d033e5310b40eb98842d03ae5210b40cf54842d03ad5210b40af58442d02be6010b40ee98042d03b96010b409fd9732d027e65ccb409f59732d02be64ccb40af59332d027f658cb409f99632d027d658cb40afd9232d02bc648cb40be98232d02f9608cb409fd9532d027d654cb409f19532d02bf644cb40af19132d027f650cb409f99432d027d650cb40af99032d02bd640cb40b798e51d02dd6394740ddd4651d027e6394740d798e51d025e63947409f58e51d035d63947409758e51d027e62947409f58a51d033e4294740cf10a51d027f63547409f18d51d027f62547409f18951d03755114740dd94741d037551d0740be98341d02f960d0740af58f41d033e53d0740af98b41d033d52d0740cf94741d03b651d0740ed54741d02be60d0740ee98341d03b960d0740b798e41d02dd6390740bbd8941d02ec6250740afd9541d033f6550740afd8d41d033e5350740ebd8941d02bc6250740eb18941d02ac6250740cf54941d03b76150740cf94541d02bc6050740dd94441d03755110740be98041d02f960107409fd9731d027e65cc7409f59731d02be64cc740af59331d039f43cc7409fd9631d027e658c7409f59631d02be648c740af59231d027f654c7409f59531d027c654c740af99131d02bd644c740e7d0d31d02fb604c740be18131d027f650c7409f99431d027d650c740af99031d02bd640c7409fd9721d027e65c87409f59721d02bf64c8740af19321d027f65887409f99621d027d6588740af99221d02bd6488740eb10a21d027f65487409f59521d027c6548740afd9121d02bc64487409fd9421d027e65087409f59421d02be6408740af59021d02de6308740b758c21d03ac4208740be98021d02f96008740bb98b53902ed62d4e40d7d4e539027e6294e409f58a539027e6194e409f586539027f6254e409f189539027f6154e409f185539035d5314e40bb98853902ed6214e40bd98453902f56114e40d794e439035d5390e40be98243902f96090e40e794e439033d5390e40e754e43903ba6090e40af582
  | 26 => 0x3c8421f354f210873e5488421cf552210875e5388421d754e21086ed6288421db94a21087b65488421ed55221087d65388421f554e21086f56288421dd94a21087e65288421f9d0a21087e442884219fd9521086bf6448421af191210873e5448421cf551210875e5348421d754d21086ef6548421dbd95210866f6548421ebd9121086ee6448421bb19121087ac6448421ab19121087ae5448421eb55121087ce5348421f354d21086ef6148421db94521087e64148421f950521087e63148421f94c521086f76548421ddd9521086776548421edd9121087b46448421ed95121087b55448421f594d21087d55348421bdd8921087e76248421dd94921087e65248421f990921087e54248421f98c921087e53248421af99350086bd64d4021cf953500873d54d4021b798f50086dd63d4021d794f500875d53d4021cf952500873d5494021d794e500875d5394021ded42500867e64940219f592500867e63940219f58e500877b5494021de95250087ba5494021ce95250087795494021ee55250087395494021de152500877b5394021de94e50087da5394021d694e50087795394021f654e50087595394021de14e50087eb4294021fa10a50087eb2194021fc88650087e92194021fc486500877b6494021de99250087796494021de192500877b6394021de98e50087796394021de18e500877b4394021de90e50087794394021de10e50087786294021ded0a500877a4294021de50a50087784294021decca500877a3294021de4ca50087783294021de186500877b4194021de90650087794194021de106500877b3194021de8c650087793194021de0c6500877b2194021de88650087792194021cf951500873d5454021d794d500875d53540219fd91500867c64540219fd8d500867c6354021dbd09500876c4254021dbc85500876d2154021ded95500877b5454021de95150087ba5454021ce95150087795454021ee55150087395454021de151500877b5354021de94d50087da5354021d694d50087795354021f654d50087595354021de14d50087eb4254021fa10950087eb2154021fc88550087e92154021fc485500877b6454021de99150087796454021de191500877b6354021de98d50087796354021de18d500877b4354021de90d50087794354021de10d500877a6254021ded09500876b4254021de90950087794254021de10950087684254021decc9500877a3254021de4c950087783254021de985500877b4154021de90550087794154021de105500877b3154021de8c550087793154021de0c5500877b2154021dac85500877a2154021de48550087692154021de08550086be6414021af590500873e5414021cf55050086de6314021b758c500875e5314021d754c50086fa6014021de540500875f5394f409f98a53d0
  | 27 => 0x219f988530876e6214c219f98453087766114c219f980530877a6014c219e980530867d6014c21de58053086796014c219fd97430867e65d0c219f597430867c65d0c21cf953430873d54d0c21d794f430875d53d0c219fd96430867e6590c219f596430867c6590c21cf952430873d5490c21d794e430875d5390c21bb98a43086ed6290c21bd98643086f56190c219fd95430867e6550c219f595430867c6550c21cf951430873d5450c21d794d430875d5350c21bbd8943086ec6250c219fd94430867e6510c219f594430867c6510c21cf950430873d5410c21d794c430875d5310c219f992520867d64948219f98e520867d63948219f597420873e54d0821cf553420875e53d0821d754f42086ed65d0821db597420876f54d0821eb953420876d54d0821eb553420872d54d0821f394f42087cd53d0821bb587420867f65908219f596420873e5490821cf552420875e5390821d754e42086ee6290821bd98642086f561908219fd95420873e5450821cf551420875e5350821d754d420867f65108219f594420873e5410821cf550420875e5310821d754c42087ad4210821bd98442086f56110821db594420866d6510821bb99042087ae6410821dbd5042087ae5410821db55042087ad5410821f394c42087cd5310821eb90c42087ac4310821f998442086ed6110821f958442086e561108219f597320873e54cc821cf553320875e53cc821d754f320867f658c8219f596320873e548c821cf552320875e538c821d754e32086f6618c821bd586320867f654c821afd9132086bc644c821cf951320873d544c821d794d320875d534c8219fd94320867d650c821cf950320873d540c821d794c320875d530c821bd98432086f5610c8219f992510867d64944219f98e510867d6394421dbd0a510876c42944219f597410873e54d0421cf553410875e53d0421d754f41087af42d04219fd96410867d6590421cf952410873d5490421b798e41086dd6390421d794e410875d5390421bb98a41086ed6290421eb10a410867f6550421cf951410873d5450421d794d410875d5350421bbd8941086ec6250421ebd09410867f65104219f994410867d65104219f194410873e5410421cf550410875e5310421d754c41086ee6210421bb58841087ac42104219f597310873e54cc421cf553310875e53cc421d754f310867f658c4219f59631086be648c421af592310873e548c421cf552310875e538c421d754e31086ee628c421bb58a310867f654c421cf951310873d544c421d794d310875d534c4219fd94310867e650c4219f594310867c650c421cf950310873d540c421d794c310875d530c421bb98831086ed620c421f54c4310873e54c8421cf553210875e53c8421d754f21086ee64c8421bb19321087ae54c8421eb55321087ce5
  | 28 => 0x15221487af5488521db952214876c5488521eb152214872c5488521f9d4621486ed6088521cfd53504873c54d41219f993504867d64d41219f98f504867d63d4121af99250486bd6494121cfd52504873c5494121ded4250486bf6454121af191504873f5454121cf15150486df6354121b718d504873f5414121cf150504877950141219f990504867d64141219f98c504867d6314121b798f54086dd63d5021be98354086f960d50219f98f540875e63d50219798f540867d63d5021d758f540865d63d50219f98b540876e62d50219f987540877661d50219f983540877a60d50219e983540867d60d5021de583540867960d50219f596540873f54950219f98e540867d63950219f982540867d60950218f59654087ac6295021cfd8e540873e6395021cf58e540873c6395021cf98a540873c6295021cf986540873c6195021cfd82540873e6095021cf582540873c6095021cfd91540867f63550219f18d540876c62550219fd81540867c6055021cfd9554087ac6255021cfd8d540873e6355021cf58d540873c6355021cf989540873c6255021cb189540873e6155021cf185540873c2155021cfd81540873e6055021cf581540873c6055021af990540873d5415021b798c54086dd6315021be98054086f960150219f990540873e64150218f990540867e6315021d798c540865e63150219f58c540875d63150219758c540867e6215021db988540867e6115021dd984540867e6015021de980540867a60150219f580540877960150219e58054086be64d4c21af593530873e54d4c21cf55353086fa60d4c21be583530867e64d4c21cf993530863e64d4c219f593530873d64d4c218f593530867e62d4c21db98b530867e61d4c21dd987530867e60d4c21de983530867a60d4c219f583530877960d4c219e583530867d6594c21cf952530873d5494c21d7d4e530867e6494c219f592530867e6094c219f582530865d6594c21d7d52530875e5494c21e7952530871e5494c21d7552530879d5494c21c7552530875c5494c21d7d92530875e6494c21d7592530875c6494c21d798a530875c6294c21d7986530875c6194c21d7d82530875e6094c21d7582530875c6094c21cf951530873d5454c219fd91530867c6454c21d7d8d530867f6054c219f181530875f6554c21d7d51530875e5454c21e7951530871e5454c21d7551530879d5454c21c7551530875c5454c21d7d91530875e6454c21d7591530875c6454c21d7989530875c6254c21d7985530875c6154c21d7085530875f6054c21d7981530875d6054c21d718153086be6414c21af590530873e5414c21cf55053086de6314c21d754c53086fa6014c21be580530867e6414c21cf990530863e6414c219f590530873d6414c218f590530867e6314c21d798c530865e6314c
  | 29 => 0x44873f54951219f992544863e64951219f98e544867d63951219f58a544876d62951219f586544877561951219f982544867d6095121cfd91544867f63551219f18d544867f6255121dbd89544866f62551219fd85544877761551219fd81544867c60551219f994544873d5415121cf990544867e63151219f58c544867e60151219f58054486be6515121cf994544863e6515121cfd8c544873e6315121cf58c544873c6315121cfd88544873d6215121cfd84544873d6115121cf484544873f6015121cf980544873d6015121cf180544873f54d4d21cf153534867e64d4d219f593534867e60d4d219f58353486be6494d21af592534873f5494d21cf152534875f5394d219f992534873e6494d218f992534867d6494d21cf592534863d6494d219f98e534867d6294d21db58a534867d6194d21dd586534867e6094d219f58253486bf6454d21af191534873f5454d21cf15153486fb6054d21be181534867f6454d21cfd91534863f6454d219f191534873c6454d218f191534875f6354d219fd89534876f6254d219fd8553487776154d219fd81534877b6054d219ed81534867c6054d21de18153486786054d219f994534873f5414d21cf150534875d5314d219f990534867d6414d21d798c534867e6014d219f580534867f65d0d219f997434867d65d0d219f197434873f54d0d21cf153434867f6590d219f996434867d6590d219f196434873f5490d21cf152434867f6550d219f995434867d6550d219f195434873f5450d21cf151434867f6510d219f994434867d6510d219f194434873f5410d21cf15043486ee6210d21bb58843486f66110d21bd584434867e65d0921cfd53424873c54d0921bd98742486f561d09219f996424873f5490921cf152424867c6550921cfd51424873c5450921bdd8542486f461509219f994424873f5410921cf150424867e65cc921cfd53324873c54cc921d7d4f324875c53cc921bd98732486f561cc9219f996324873f548c921cf152324867c654c921afd9132486bc644c921cfd51324873c544c921d7d4d324875c534c921bdd8532486f4614c9219f994324873f540c921cf150324867e65d0521cfd53414873c54d0521bb98b41486ed62d05219f996414873f5490521cf15241486de6390521b758e414867f65505219f595414867c6550521cfd51414873c5450521bbd8941486ec62505219f994414873f5410521cf150414867e65cc521cfd53314873c54cc521d7d4f314875c53cc521bb98b31486ed62cc5219f99631486be648c521af592314873f548c521cf152314867f654c5219f595314867c654c521cfd51314873c544c521d7d4d314875c534c521bbd8931486ec624c5219f994314873f540c521cf150314873f54c8521cf15321487b754c8521ed153214873f5488521cf
  | 30 => 0x3e64943219f59250c873d64943218f59250c867e63943219f58e50c867f64543219f19150c867f63543219f18d50c87795014321b798f54886dd63d52219f98f548875e63d52219798f548867d63d5221d758f548865d63d5221db58b548877661d52219f983548867d60d5221cfd52548867e63952219f58e548867e60952219f582548873f64552219fd8d548867c6355221dbd89548867f60552219f181548873d5415221cf990548867e63152219f58c548876d6215221dd984548867e60152219f58054886be64d4e21af593538867e64d4e21cf993538863e64d4e219f593538873d64d4e218f593538876d62d4e21dd987538867e60d4e219f583538875f5394e219f992538867d6494e219f982538867d6094e219fd91538867c6454e21d7d8d538867f6054e219f181538875d5314e219f990538867d6414e21d798c538876d6214e21dd984538867e6014e219f580538867f65d0e219f997438867d65d0e219f197438875e53d0e21d754f438867f6590e219f996438867d6590e219f196438873e5490e21cf55243886ee6290e21bb58a438867f6550e219f995438867d6550e219f19543886ef6250e21bb189438867f6510e219f994438867d6510e219f194438873e5410e21cf550438875e5310e21d754c43886f66110e21bd584438873e54d0a21cf55342886f661d0a21bd587428876d65d0a21dbd5342887ae54d0a21db55342887ad54d0a21f998742886ed61d0a21f9587428873f5490a21cf152428873e5450a21cf55142886f76150a21bd185428873f5410a21cf15042887ad4210a21bb594428876d6510a21eb990428876f5410a21ebd50428876d5410a21eb15042887ae4310a21eb10c42886ed6110a21d794f328875d53cca21bd98732886f561cca21afd9132886bc644ca21d794d328875d534ca21bdd8532886f4614ca21cfd53418873c54d0621ebd0b418873e5490621cf55241886de6390621b758e41886ee6290621bb58a41887ac4290621cfd51418873c5450621bbd8941886ec6250621ebd09418873e5410621cf55041886ee6210621bb58841887ac4210621d7d4f318875c53cc621af99231886bd648c621d794e318875d538c621bb98a31886ed628c621d7d4d318875c534c621d794c318875d530c621bb98831886ed620c621bb597218876d65c8621bb99321886ec64c8621bd597218877565c8621ded42508867e64942219f592508867e63942219f58e508867f64542219f191508867f63542219f18d508876f4254221db109508876f2154221af99050886bd6414221b798c50886dd6314221de540508867e63d51219f58f544867e60d51219f583544873f63d5121cf98f544873d63d5121cf18f544873f62d5121cf58b544873f61d5121cf587544873f60d5121cf983544873d60d5121cf1835
  | 31 => 0xc831bd584320c67e6494431cf992510c63e64944319f592510c73d64944318f592510c67d65d0431cfd53410c73c54d04319fd96410c67d6590431cf952410c73d5490431b798e410c6dd63904319fd95410c73f5450431cf151410c6ef6250431bb189410c67f65104319f994410c67d65104319f194410c73e5410431cf550410c6de6310431b758c410c75e54cc431d7153310c75d52cc431af992310c6bd648c431b758e310c75e538c431ed992310c7b5648c431bd58e310c776538c431f594e310c67f654c431b7d95310c75f654c43197d95310c75e544c431d7151310c75d524c431b7d85310c75e514c431f5905310c7d5414c431bdd95310c777654c4319dd95310c6f7634c431f5d8d310c776534c431f594d310c7d6434c431f550d310c7d6324c431f50c9310c77b50940319f992500c67d64940319f98a500c67d62940319fd91500c67c64540319fd89500c67c6254031d7cc5500c7763154031d74c5500c7753154031af990500c6bd6414031bb988500c6ed6214031de540500c67e63d53219f58f54c876e62d5321dd58754c867e60d53219f58354c873f54953219f98e54c867d63953219f98254c867d6095321cfd9154c867f63553219f18d54c867f60553219f18154c873d5415321cf99054c867e63153219f58c54c876e6215321dd58454c867e60153219f58054c867e64d4f219f59353c876e62d4f21dd58753c867e60d4f219f58353c875f5394f219f99253c867d6494f219f98253c867d6094f21afd9153c86bc6454f219fd9153c873f6454f218fd9153c867c6454f21cf19153c863c6454f21d7d8d53c867f6054f219f18153c875d5314f219f99053c867d6414f21d798c53c876e6214f21dd58453c867e6014f219f58053c867f65d0f219f99743c867d65d0f219f19743c867f6590f219f99643c867d6590f219f19643c873f5490f21cf15243c86f66190f21bd58643c867f6550f219f99543c867d6550f219f19543c867f6510f219f99443c867d6510f219f19443c873f5410f21cf15043c86ee6210f21bb58843c873f54d0b21cf15342c873e5490b21cf55242c86f66190b21bd58642c873f5450b21cf15142c873e5410b21cf55042c86f66110b21bd58442c875f53ccb21d714f32c875e538cb21d754e32c86f6618cb21bd58632c86bf644cb21af19132c875f534cb21d714d32c875e530cb21d754c32c86f6610cb21bd58432c873e54d0721cf55341c86ee62d0721bb58b41c873f5490721cf15241c86de6390721b758e41c873e5450721cf55141c86ef6250721bb18941c873f5410721cf15041c875e53cc721d754f31c86ee62cc721bb58b31c86be648c721af59231c875e534c721d754d31c86ef624c721bb18931c87d5310c721af99250c86bd6494321ded4250c867e6494321cf99250c86
  | 32 => 0x1b7997324c75e65cc931b7993324c6dc64cc931d714b324c6de61cc931b7583324c6dd638c931dbd4a324c76c528c931bd986324c6f5618c931afd91324c6bc644c931dbd49324c76c524c931bdd85324c6f4614c931e7d91324c6de644c931b7191324c79c644c931a7191324c7cf624c931f3d49324c75c524c931f3149324c7d7614c931b7185324c7d4614c931b5185324c6df604c9319f994324c6de630c9319f997414c73f54d0531cf153414c6de63d0531b758f414c79c43d05319f996414c6de6390531b758e414c67f65505319f595414c67c6550531cfd51414c73c5450531b7d8d414c6dc6350531e710d414c6ef6250531bb189414c67e6510531ed504414c7d743cc531f510f314c7d732cc531f54cb314c6f560cc531af992314c6bd648c531b7992314c79e648c531a7992314c79d648c531b7192314c6dd628c531f5d46314c6dd608c5319f993504c67d64d41319f98b504c67d62d4131ded42504c6bf6454131af191504c6ef6254131bb189504c6be6414131af590504c6ee6214131bb588504c77950141319f990504c73e64141318f990504c67d6414131cf590504c63d6414131d7d0c504c75c43141319f988504c76e62141319b988504c67d6214131db588504c66d62141319f98f540c75e63d50319798f540c67e62d50319f58b540c67e61d5031dd987540c67e60d50319f583540c67d6595031cfd52540c67e62950319f58a540c67e60950319f582540c73f64550319fd89540c67c62550319fd81540c67c6055031cf550540c6ee6215031bb588540c6fa6015031be580540c67e6415031cf990540c67e6315031d798c540c67e6215031db988540c66e62150319f588540c76d62150319b588540c67e6115031dd984540c67e6015031de980540c67a60150319f580540c77960150319e580540c67e6494c319f592530c67d65d0c31d794f430c67f6590c319f596430c73e5490c31cf552430c6f66190c31bd586430c67f6550c319fd94430c67d6510c31cf950430c73d5410c31d794c430c6f66110c31bd584430c76f52948319f992520c67d64948319f982520c67d6094831afd91520c6bc64548319fd91520c73f64548318fd91520c67c6454831cf191520c63c64548319fd81520c67c6054831af990520c6bd6414831db548520c6fa6014831be580520c67f65d08319f997420c67d65d0831cf953420c73d54d08319fd96420c67e65908319f596420c73f5490831cf152420c76e5290831db54a420c67f65508319f595420c67c6550831cf951420c73d5450831db949420c76d52508319fd94420c67e65108319f594420c73f5410831cf150420c75e53cc831db94b320c76d52cc831bd987320c6f561cc8319f596320c67f654c831afd91320c6bc644c831d794d320c76e520c831db548320c6f661
  | 33 => 0x95428c73e5450a31cf551428c6f76150a31bd185428c67f6510a319f994428c67d6510a31cf950428c73d5410a31bd984428c6f56110a31cf953328c73d54cca31cf952328c73d548ca31db94a328c76d528ca31bd986328c6f5618ca31afd91328c6bc644ca31cf951328c73d544ca31db949328c76d524ca31bdd85328c6f4614ca31cf950328c73d540ca31cf953418c73d54d0631cf952418c73d5490631b798e418c6dd6390631cf951418c73d5450631bbd89418c6ec6250631cf950418c73d5410631b798c418c6dd6310631ed504418c73e54cc631cf553318c6dd65cc631d7597318c75e54cc631e7953318c71e54cc631e7553318c75c54cc631d754b318c6f565cc631dd597318c7b654cc631ed553318c6f560cc631af993508c6bd64d4231cf953508c73d54d4231cf952508c73d5494231ded42508c67e64942319f592508c67e62942319f58a508c73e5454231cf551508c67f64542319f191508c67f62542319f189508c75f3154231af990508c6bd6414231cf950508c73d5414231bb988508c6ed6214231de540508c75d63d51319f98b544c67d62d51319f983544c67d60d5131cfd52544c67e64951319f58e544c75d63951319f98a544c67d62951319f586544c77561951319f982544c67d6095131bbd89544c6ec6255131bed81544c6f86055131cfd91544c67f6355131d7d8d544c67f6255131dbd89544c66f62551319f189544c76c62551319b189544c67f6155131ddd85544c67f6055131ded81544c67b60551319f181544c77860551319e181544c67e6515131cf550544c73e64151319f988544c67d62151319f980544c67d60151319f997434c73f54d0d31cf153434c6f661d0d31bd587434c75e65d0d3197997434c75f54d0d31e7d53434c75d54d0d31e7153434c6dd62d0d31b7987434c7d661d0d31b5987434c7d561d0d31b7583434c67e6590d31cf952434c73d5490d31b798e434c67c6550d31cfd51434c73c5450d31bdd85434c6f46150d319f994434c73e5410d31cf550434c79d4310d31b7994434c75e6510d31b7990434c79e6410d31d7d50434c79e5410d31d7550434c79d5410d31b7588434c6de6110d31b7580434c67e64d49319f593524c67e60d49319f583524c76f5294931afd91524c6bc6454931bed81524c6f86054931db548524c67e64149319f590524c67e60149319f580524c67e65d09319f597424c67c65d0931dbd4b424c76c52d09319f996424c67d65909319f196424c73f5490931cf152424c6de6390931b758e424c79c43909319fd95424c67e65509319f195424c6df6350931b718d424c6f76150931bd185424c67e65109319f594424c67c6510931cfd50424c73c5410931b798c424c6dd6310931e710c424c76f5210931db148424c6f66110931bd584424c67e65cc93
  | 34 => 0xcc6f66190f31bd58643cc73e5410f31cf55043cc79d4310f31bd98443cc6f56110f31d759443cc79e6410f31d7d5043cc79e5410f31d755043cc79d5410f31b758843cc6de6110f31f598443cc7d56110f31b758043cc6be64d4b31af59352cc76f5294b319f99252cc67d6494b319f98252cc67d6094b319fd9152cc67c6454b319fd8152cc67c6054b31db54852cc67f65d0b319f99742cc67d65d0b31db94b42cc76d52d0b319fd9642cc67e6590b319f59642cc73e5490b31cf55242cc6de6390b31b758e42cc79c4390b319fd9542cc67d6550b319f19542cc6df6350b31b718d42cc67f6510b319f99442cc67d6510b31cf95042cc73d5410b31b798c42cc6dd6310b31e710c42cc76e5210b31db54842cc76e52ccb31db54b32cc6f661ccb31bd58732cc6de64ccb31b719332cc75e52ccb31f394b32cc7cd52ccb31b798732cc7d661ccb31f558732cc6dd60ccb31afd9132cc6bc644cb31b7d9532cc75f654cb31e7d9132cc6de644cb31b719132cc79c644cb31a719132cc7cf624cb31d794932cc6dc614cb31b7d8132cc76e520cb31db54832cc6f6610cb31bd58432cc73e54d0731cf55341cc6de63d0731b758f41cc79c43d0731b798e41cc6dd6390731cf95141cc73d5450731b7d8d41cc6dc6350731e710d41cc6ef6250731bb18941cc77b50943319f99250cc67d6494331d7d0e50cc75c43943319f98a50cc67d62943319fd9150cc67c64543319fd8950cc67c6254331af99050cc6bd6414331bb98850cc6ed6214331de54050cc75d63d52319f98b548c67d62d5231dd987548c67e60d52319f583548c73f54952319f98a548c67d62952319f982548c67d6095231cfd8e548c73d6395231cfd8a548c73e6295231cf58a548c73c6295231cf986548c73c6195231cfd82548c73e6095231cf582548c73c6095231cfd91548c67f62552319f189548c67f60552319f181548c73f6555231cfd8d548c73d6355231cfd89548c73e6255231cf589548c73c6255231cf985548c73c6155231cfd81548c73e6055231cf581548c73c6055231cf550548c73e6415231d758c548c67e62152319f588548c77661152319f980548c67d6015231cf953438c73d54d0e31bd987438c6f561d0e31cf952438c73d5490e31cf951438c73d5450e31bdd85438c6f46150e31cf950438c73d5410e31af993528c6bd64d4a31cf953528c73d54d4a31cf952528c73d5494a31dbd4a528c67e6494a319f592528c67e6094a319f582528c73e5454a31cf551528c67f6454a319f191528c67f6054a319f181528c6be6414a31af590528c73e5414a31cf550528c76d5214a31be980528c6f96014a319fd97428c67e65d0a319f597428c73e54d0a31cf553428c67f6590a319f996428c67d6590a31cf952428c73d5490a319fd95428c67d6550a319f1
  | 35 => 0xe6294141bb58a505076f5294141db14a505077b5094141b7d8d50506dc6354141bbd8950506ec6254141dbd49505076c5254141dbd48505076c5214141de540505067e63141419f58c505073e4314141cf10c505067e62141419f588505075f5394c419f98a531067d6294c419f982531067d6094c419fd89531067c6254c419fd81531067c6054c41d754c53106ee6214c41bb58853106fa6014c41be580531075e53d0c41d754f43106f661d0c41bd587431067d6590c41cf952431067f6550c41cf950431075e5310c41d754c43106f66110c41bd584431076f52948419f98e521067d63948419f982521067d60948419fd8d521067c63548419fd81521067c6054841b798c52106dd6314841db54852106fa6014841be580521073e54d0841db94b421076d52d0841bd98742106f561d08419f59642106bd6590841cf596421063d6590841cf94e42106be6290841cf54a42106bd61908419fd95421073e5450841db948421076d5210841eb50842106f66110841bd584421073e5310841af98842107ae6210841eb948421073d5210841eb54842107b66110841af58442107b561108419fd97321067e65cc8419f59732106be64cc841af593321075e53cc841d754f32106f661cc841bd587321067f658c8419f996321067d658c841db94a321076d528c8419fd95321067d654c8419f19532106bf644c841af191321075e534c841d754d321076e524c841db549321067f650c8419f994321067d650c841d798e511075d6394441cf90a511073c4294441cf94f41106be62d0441cf54b41106bd6490441cf95241106de6390441b758e41106f56490441dd95241107b65490441f598e41107d56390441ed90a41107b442904419fd9541106ef6250441bb18941106bf6550441cfd95411063f6550441cf94d41107af6250441af18941107ac6250441ab189411073d5250441afd85411073e5150441bdd95411077765504419dd9541106f76450441edd9141107765450441ed95141107b74350441ed50d41107e76250441f9189411077b50940419f98e501067d63940419f98a501067d62940419fd8d501067c63540419fd89501067c6254041cf909501073c4254041cfd05501073d4154041b798c50106dd6314041bb98850106ed6214041de54050106ee62d5331bb58b54cc75e63d53319f98b54cc76e62d53319b98b54cc67d62d5331db58b54cc66d62d5331dd58754cc67e60d53319f58354cc73f54953319f98a54cc67d62953319f98254cc67d6095331cfd9154cc75c63553319fd8954cc67c62553319fd8154cc67c6055331cf55054cc73e6415331d798c54cc67e62153319f58854cc77561153319f98054cc67d6015331b759743cc75d65d0f31d7d5343cc75d54d0f31b758b43cc6de61d0f31b758343cc73e5490f31cf55243
  | 36 => 0x42419fd8d509067c63542419fd89509067c6254241cf909509073c4254241cfd0550906de6314241b758c509075e5314241d754c50906ee6214241bb588509077950142419f98b535067d62d4d419f983535067d60d4d41d7d4e53506ee6294d41bb58a53506ef6254d41bb18953506fb6054d41be181535075d5314d419f988535067d6214d419f980535067d6014d419f997435075f5390d41d714e43506f66190d41bd58643506be6390d41cfd4e435079f5390d41e714e43506bd6290d41af98643507b66190d41ad98643507b56190d41af582435075f5350d41d714d43506f76150d41bd185435067e6510d41e750c43506be6510d41cf99443506be6310d41e798c435073f5310d41e794c435079d5310d41af58843506be6110d41af580435067e63d49419f58f525067e60d49419f58352507af64d4941dbd4f525076e53d4941db54f525076c53d4941eb90f52507ac43d4941dbd93525076f63d4941db98f525076d63d4941db18f525076f43d4941db90f525076d43d4941db10f525076f61d4941db587525076f60d4941db983525076d60d4941db183525076f5294941db548525067e63149419f58c525073e4314941cf10c525067e60149419f58052506ee6514941db99452507ad6414941dbd4c525076e5314941db54c525076c5314941eb90c52507ac4314941dbd90525076f6314941db98c525076d6314941db18c525076f4314941db90c525072e4314941db50c525076c4314941cb10c525076f6114941db584525076d4114941dbd80525076e6014941db580525076c60149419f997425076c52d0941af997425073e65d09418f99742506be63d0941ebd4b425073c52d0941eb14b425072c52d0941af98742506bd60d0941af592425076f5290941db14a42506f66190941bd586425076f5250941db14942506f76150941bd18542506bc6350941ebd8942507af5250941cf14942507ac5250941cb14942507b76150941af18542507b46150941afd81425067e6510941af990425076f52109419f997325067d65cc9419f19732506bf64cc941af193325076f52cc941db14b325067e658c9419f596325067c658c941af99232506bd648c941dbd4a325076c528c9419fd95325067e654c9419f19532506bf644c941af191325076f524c941db149325067e650c9419f594325067c650c941af99032506bd640c941dbd48325076c520c941bd98432506f5610c941dbd4b415076c52d0541ed90f41507b443d0541f9d4b41507e452d0541edd0b41507b542d0541b798e41506dd6390541dbd4a415076c5290541af98e415079e6390541a798e415079d6390541af58a41507af5290541cf14a41507ac5290541cb14a41507b75190541af582415076f52d4141db14b505067e63d41419f58f505067e62d41419f58b50506e
  | 37 => 0xcf94b42d07ae52d0b41eb54b42d06be61d0b41ed98742d07b561d0b41af58342d06bf6550b41cfd9542d06bc6350b41ebd8942d073e5250b41af18542d06bf6050b41db94842d076d5210b41bd98442d06f56110b419fd9732d067e65ccb419f59732d06bf64ccb41af19332d06f661ccb41bd58732d067f658cb419f99632d067d658cb41af99232d06bd648cb419fd9532d067d654cb419f19532d06bf644cb41af19132d067f650cb419f99432d067d650cb41af99032d06bd640cb41bb98a50d06ed6294341ded4250d067e63943419f58e50d073e4394341cf10e50d067e6294341db98a50d066e62943419f58a50d076d62943419b58a50d067f63543419f18d50d067f62543419f18950d07795014341d7d4e539067e6294e419f58a539067e6094e419f582539075f6494e41d7d8a539075e6294e41d758a539075c6294e41d7986539075c6194e41d7d82539075e6094e41d7582539075c6094e419fd89539067c6254e419fd81539067c6054e41d7d95539075d6454e41d7d89539075e6254e41d7589539075c6254e41d7985539075c6154e41d7d81539075e6054e41d7581539075c6054e41d754c539075e53d0e41d794e439075d5390e41bd98643906f56190e41d794d439075d5350e41bdd8543906f46150e41d754c43906de63d4a41b758f529075e53d4a41d754f529075e5394a41d754e529076f5294a419f98e529067d6394a419f982529067d6094a41d794d529075d5354a419fd8d529067c6354a419fd81529067c6054a41b798c52906dd6314a41d794c529075d5314a41db54852906fa6014a41be580529075e53d0a41d754f429075e5390a41d754e429076e5290a41db54a42906f66190a41bd586429073e5390a41e794e429071e5390a41e754e42907ae5290a41cf54a42907ad5290a41ed98642906bd6190a41ed586429075e5350a41d754d429076e5250a41db54942906f76150a41bd185429075e5310a41d754c42907ad4210a41af594429073d6510a41cf94c429079e5310a41c794c429079d5310a41eb98842907af5210a41cf54842907ac5210a41af584429067f65cca419f997329067d65cca41af99332906bd64cca41d794f329075d53cca419fd96329067e658ca419f596329075e538ca41d754e329067f654ca419f595329067c654ca41afd9132906bc644ca41d794d329075d534ca419fd94329067e650ca419f594329075e530ca41d754c32906f6610ca41bd584329075e53d0641d754f41906bd65d0641cf597419073e53d0641e794f419071e53d0641e754f41906be62d0641cf54b41906f565d0641dd59741907d653d0641f554f41906de63d4241b758f509075e53d4241d754f509075e5394241d754e509077b50942419f98e509067d63942419f98a509067d6294241d794d509075d535
  | 38 => 0x4514ca7e64145329f590514ca7e60145329f580514cb3f54d4132cf153504ca7e64d41329f593504ca7e61d41329f587504cabe6494132af592504cb3f5494132cf152504cb7b5094132afd91504cabc6454132cfd51504cb3c5454132bdd85504caf46154132cfd50504cb3c5414132de540504ca7e64141329f590504ca7e61141329f584504ca7e63d5032d798f540ca7e62d5032db98b540ca7e61d50329f587540ca7e60d50329f583540ca7d6595032cfd52540ca7e61950329f586540ca7e60950329f582540cb3f64550329fd85540ca7c61550329fd81540ca7c6055032cf550540caf66115032bd584540cafa6015032be580540ca7e6415032cf990540ca7e6315032d798c540ca7e6215032db988540ca7e6115032dd984540ca7661150329f584540cb7561150329d584540ca7e6015032de980540ca7a60150329f580540cb7960150329e580540ca7e6494c329f592530ca7d65d0c329fd96430ca7d6590c32cf952430cb3d5490c32bb98a430caed6290c329fd95430ca7f6510c329f594430cb3e5410c32cf550430caee6210c32bb588430ca7e64948329f592520ca7d65d08329fd96420ca7d6590832cf952420cb3d5490832b798e420cadd63908329fd95420ca7f65108329f994420ca7d65108329f194420cb3e5410832cf550420cade6310832b758c420cadd638c832d794e320caed638c832db94e320cbce538c8329fd95320cabf644c832af191320cadf654c832d7d95320ca5f654c832e7d91320cb9c644c832b7d89320cb5e524c832f3909320cbcd424c832bbd95320cb6f654c8329bd95320cbaf644c832eb191320caef634c832f3d8d320cb6e534c832f394d320cbce434c832f350d320cb7751944329f992510ca7d64944329f982510ca7d60944329fd91510ca7c6454432d7cc9510cb5d32544329fd81510ca7c6054432af990510cabd6414432dd544510cafa6014432be580510cb7b50940329f992500ca7d64940329f986500ca7d61940329fd91500ca7c6454032db8c9500cb6d32540329fd85500ca7c6154032af990500cabd6414032bd984500caf56114032de540500cb5f5394f419f98a53d067d6294f419f98253d067d6094f419fd8953d067c6254f419fd8153d067c6054f41d754c53d075e53d0f41d754f43d06f661d0f41bd58743d06bd6590f41cf59643d073d5390f41af58a43d06be6190f41af58243d075e5310f41d754c43d079d4310f41bd98443d06f56110f41e798c43d079e5310f41cf54c43d079d5310f41af58843d06be6110f41ed98443d07b56110f41af58043d076f5294b419f98e52d067d6394b41cf90e52d073c4394b419f98252d067d6094b419fd8d52d067c6354b419fd8152d067c6054b41db54852d076e52d0b41db54b42d06f661d0b41bd58742d06be63d0b41
  | 39 => 0xcb795014332be983548caf960d5232d758f548cb6e62d52329f987548ca7d61d52329f983548cb7a60d52329e983548ca7d60d5232de583548ca7960d5232cfd52548ca7e61952329f586548ca7e60952329f582548cb3f64552329fd85548ca7c61552329fd81548ca7c6055232cf550548cb3e6415232d758c548cb6e62152329f984548ca7d61152329f980548ca7d6015232cf953438cb3d54d0e32bb98b438caed62d0e32cfd52438cb3c5490e32cf951438cb3d5450e32bbd89438caec6250e32cfd50438cb3c5410e32cf952428cb3d5490a32b798e428cadd6390a32cf950428cb3d5410a32b798c428cadd6310a32eb508428cadd65cca32d7597328caed65cca32db597328caed60cca32ddd46518ca7e64946329f592518ca7e60946329f582518ca7f64546329f191518cb5f32546329fd81518ca7c6054632af990518cabd6414632dd544518cafa6014632be580518cabe64d4232af593508cabe6494232af592508cb7b50942329f992508cb3e64942328f992508ca7d6494232cf592508ca3d64942329f986508ca7d61942329fd91508ca7c64542329fd85508ca7c6154232de540508ca7e61d51329f587544ca7e60d51329f583544cb3f63d5132cf58f544cb3f62d5132cf58b544cb3f61d5132cf987544cb3d61d5132cf187544cb3f60d5132cf983544cb3d60d5132cf183544cb3f54951329f992544ca3e64951329f58e544cb5d63951329f58a544cb6d62951329f986544ca7d61951329f982544ca7d6095132cfd91544ca7f6355132d7d8d544ca7f6255132dbd89544ca7f61551329f185544ca7f60551329f181544ca7e6515132cf550544cb3e64151329f984544ca7d61151329f980544ca7d6015132af994544cb3e65151328f994544cb3f6315132cf58c544cb3f6215132cf588544cb3d3215132cfd84544cb3e6115132cf584544cb3c6115132cfd80544cb3e6015132cf580544cb3c60151329f997434cb3f54d0d32cf153434caee62d0d32bb58b434ca7e6590d32cfd52434cb3c5490d329f195434cb3f5450d32cf151434caef6250d32bb189434ca7e6510d32cfd50434cb3c5410d32e750c434ca7e65d0932cfd53424cb3c54d0932b798f424cadd63d09329f996424cb3f5490932cf152424ca7f65509329f595424ca7c6550932cfd51424cb3c5450932b7d8d424cadc63509329f994424cb3f5410932cf150424cbad4210932cfd53324cb3c54cc932ebd53324cbac54cc932bb583324cb3f548c932cf152324cb9f548c932e7152324cbcf528c932b7586324cb3f54d4532cf153514ca7e64d45329f593514ca7e60d45329f583514cabe6494532af592514cb3f5494532cf152514cb775194532afd91514cabc6454532cfd51514cb3c5454532bed81514caf86054532cfd50514cb3c5414532dd54
  | 40 => 0x51145429f98c5150a7d6314542dbd085150b3e42145429f9805150a7d60145429f98f5050a7d63d4142dbd0b5050b3e42d41429f9875050a7d61d4142ded425050adf6354142b718d5050af76154142bd1855050b7950141429f98c5050a7d63141429f9845050a7d6114142d7d4e5310a7e6194c429f5865310a7e6094c429f5825310a7f6154c429f1855310a7f6054c429f1815310b5d5314c42bd9845310af56114c42be9805310af96014c42d794f4310b5d53d0c42bb98b4310aed62d0c429f5964310abd6590c42cf5964310abe6390c42cf54e4310abd6290c42af9864310abd6090c429fd954310b5e5310c42d754c4310aee6210c42bb5884310abe6310c42e798c4310b9e5310c42cf54c4310b9d5310c42c754c4310bae6210c42af5884310bad6210c42ab5884310abe6110c42af5804310b3e4394842cf10e5210abe63d0842af9874210abd60d0842af5924210b3e5490842bb5924210b6e5490842eb9524210bae4390842eb10e4210aee6190842bb5824210a7f6550842afd954210b3f65508428fd954210abc6350842afd894210b3e5250842af1854210abf6050842bbd954210b6f65508429bd954210aef6450842ebd914210b6e5450842eb9514210baf4350842eb50d4210aec6150842bbd814210b7751944429f98e5110a7d63944429f9825110a7d60944429fd8d5110a7c6354442cf90d5110b3c4354442cfd095110b3d42544429fd815110a7c6054442b798c5110add6314442dd5445110afa6014442be5805110b7b50940429f98e5010a7d6394042cf90e5010b3c43940429f9865010a7d61940429fd8d5010a7c63540429fd855010a7c6154042b798c5010add6314042bd9845010af56114042de5405010af661d5332bd58754ccb5e63d5332db58b54cca7e61d5332dd98754cca7661d53329f58754ccb7561d53329d58754cca7e60d53329f58354ccb3f54953329f98654cca7d61953329f98254cca7d6095332cfd9154cca7f61553329f18554cca7f60553329f18154ccb3d5415332cf99054ccb5e6315332db58854cca7e61153329f58454cca7e60153329f58054ccb3e5490f32cf55243ccaee6290f32bb58a43ccb3e5410f32cf55043ccb9d4310f32bb98843ccaed6210f32cf95342ccb3d54d0b32b798f42ccadd63d0b32cfd5242ccb3c5490b32cf95142ccb3d5450b32b7d8d42ccadc6350b32cfd5042ccb3c5410b32af99351ccabd64d4732af99251ccabd6494732ddd4651cca7e6494732cf99251cca3e64947329f59251ccb3d64947328f59251cca7e60947329f58251cca7f64547329f19151cca7f60547329f18151ccb755114732ded4250cca7e64943329f59250cca7e61943329f58650cca7f64543329f19150cca7f61543329f18550ccabe6414332af59050ccaf66114332bd58450c
  | 41 => 0xc439fd954310ebf6550c43cfd954310e3f6550c43afd8d4310f3e5350c43af1894310ebf6150c43af1814310edf6550c43d7d954310e5f6550c43b7d914310f9f6450c43d79514310f9e5450c43b7d854310edc6050c43dbd4a5210e7e61948439f5865210e7e60948439f5825210e7f61548439f1855210e7f60548439f1815210f6d5214843bd9845210ef56114843be9805210ef96014843ddd465110e7e62944439f58a5110e7e60944439f5825110e7f62544439f1895110e7f60544439f1815110eee6214443bb5885110f755114443be9805110ef96014443ded425010e7e62940439f58a5010e7e61940439f5865010f3f4354043cf50d5010e7f62540439f1895010e7f61540439f1855010eee6214043bb5885010ef66114043bd5845010f795014043d7d4e53d0a7e6194f429f58653d0a7e6094f429f58253d0a7f6154f429f18553d0a7f6054f429f18153d0b5d5314f42d794f43d0b5d53d0f42bb98b43d0aed62d0f42d794c43d0b5d5310f42e750c43d0aee6210f42bb58843d0ade6394742b758e51d0b7751947429f98e51d0b5e63947429798e51d0a7d6394742d758e51d0a5d63947429f98251d0a7d60947429fd8d51d0a7c63547429fd8151d0a7c6054742dd54451d0b7b50943429f98e50d0a7d63943429f98650d0a7d61943429fd8d50d0a7c63543429fd8550d0a7c6154342de54050d0afa60d4e42be5835390b5f5394e429f9865390a7d6194e429f9825390a7d6094e429fd855390a7c6154e429fd815390a7c6054e42d754c5390b5e5390e42d754e4390aee6290e42bb58a4390b9e5390e42cf54e4390b9d5390e42eb98a4390abd6290e42eb58a4390abe6190e42af5824390b5e5350e42d754d4390aef6250e42bb1894390abd6510e42cf5944390b9e6310e42cf54c4390abd6210e42af9844390abd6010e42af5974290b3d65d0a42af98f4290abe61d0a42af5834290aed65d0a42db5974290b7751946429f98e5190a7d6394642dbd0a5190a7e60946429f5825190a7f63546429f18d5190b3e4354642cf10d5190b3f42546429fd815190a7c6054642b798c5190add6314642dd5445190afa6014642be5805190ade63d4242b758f5090b7b50942429f98e5090a7d6394242cf90e5090b3c43942429f9865090a7d61942429fd8d5090a7c6354242dbd095090a7f61542429f1855090b7950142429f9875350a7d61d4d429f9835350a7d60d4d42d7d4e5350af66194d42bd5865350b5d5314d429f9845350a7d6114d429f9805350a7d6014d429f9974350b5f5390d42d714e4350aee6290d42bb58a4350b5f5350d42d714d4350aef6250d42bb1894350a7e6510d42e750c4350b3c5390942ebd4a4250abd61909429f98f5150a7d63d45429f9835150a7d60d4542b798e5150add6394542ddd465150b75
  | 42 => 0x600040030000001001400100400000014003000400c0000000000c004000000600040020028000000400000000010008004000000500080000098001007c0000020004002800200000020000019000800400100000000002002000000080060000001001c000002c000003000200000000000000000000a000800700600030000001000c002001c000000000c00140000000010000001c000000200040000004002001800100000040038000003c000001800100280010018000000000400000010008002001800000080010000005000c00a000000600080050000000000c008000800600300010008000000400000100000018000001400100040020018000000800000000020000005002400000000000000007000c00000000020000001000800200140050000000001800100000000000000001800000180090000002004c008000000000000060020000000c0000004000000400000540040010005000c0010000004001c005000f6f5294b439f98652d0e7d6194b439f98252d0e7d6094b439fd8552d0e7c6154b439fd8152d0e7c6054b43db54852d0f7751947439f98a51d0e7d62947439f98251d0e7d60947439fd8951d0e7c62547439fd8151d0e7c6054743dd54451d0eee6294343bb58a50d0f7b50943439f98a50d0f6e62943439b98a50d0e7d6294343db58a50d0e6d62943439f98650d0e7d61943439fd8950d0e7c62543439fd8550d0e7c6154343de54050d0ebd65d0e43cf5974390ebe62d0e43af5874390ebe60d0e43b75974390f5d65d0e43bd9875290ef561d4a43dbd4a5290e7e6194a439f5865290e7e6094a439f5825290e7f6154a439f1855290e7f6054a439f1815290f6d5214a43bb98b5190eed62d4643ddd465190e7e62946439f58a5190e7e60946439f5825190f5f43546439fd895190e7c62546439fd815190e7c6054643dd5445190f7b5094243d7d0e5090e7e62942439f58a5090e7e61942439f5865090f3f43542439fd895090e7c62542439fd855090e7c6154243bb9885090eed6214243bd9845090ef56114243de5405090f9f5390d43af5824350e7e61d49439f5875250e7e60d49439f5835250f6f5294943be9825250ef96094943db5485250f3e43149439f9845250e7d61149439f9805250e7d6014943d7d0f5150f3e43d45439f98b5150e7d62d45439f9835150e7d60d4543ddd465150eef6254543bb1895150efb6054543be1815150f7551145439f9885150e7d62145439f9805150e7d60145439f98b5050e7d62d41439f9875050e7d61d4143bb98a5050eed6294143ded425050f795014143d7d0c5050f3e43141439f9885050e7d62141439f9845050e7d6114143af98b4310ebd61d0c43af9834310ebd6490c43cf9524310edd6490c43d79524310f9e5490c43b75864310ede6090
  | 43 => 0x200140010000002001c008000400000040000024002004000700080000004007000000500000000000000000400200040000000001000000000000000020004000000500040000000000002000200180030000000001000f00040000048000002c0000000000000400000340010020000001000800000060004005000400100080000004000001400500040080008000001800400080050000000000c013000400000280000018005000000100000060010002000000000000030000005003000000000020014002000c005000800b000000000000010000000000000100100020024003000c00400240020010000001000d0018002000000a00080000000001000400e00140040000002000800500080020024000000000600100020004001001400400080000000002003800d0004002000c0000010000002000400040010020007000400a0004000001800000040030004002000000000000000000001008400d00280040008004002000300000000020009000c0000004007001800100140000004002001c001000000000040000008000000000a0000007000001000080000008000000400000100000028000001c00e0000003000c008000c00800300020038003002c0000004000000800d0000000001400b00040000000003000400c0004000000400000000000018000000400100040000008001000400200000000004000003c0030030002000000300000340008000000c00400000010000007000c000000000200000010004009000000a0004005000000000000000010003000000a00200000010006000c00300280050010000001800c0020000000000200000010008002001c00000040000000007001000600000020018008000c001000400100040000000000000800000040010008001001c0010000007002000200000060014000000000000000000020000000801500080030004000000000000340080010000000400100040010018000000c005002c000000000100040020004000000c004000c00000140000004001000000300000010004001000400b00100000000000000000000040070018001000c004003c0000004014001800700040000018000000000000440000004004000000b002400400000090000002000c00000000020050010000000000080060000004000000200000060018000000400000080000010000000000000480040000000000000000040010008000000800100200000004003000c0020040000000000700000030010000000c001006c01800000010008000001400c0010001000800b000000600080020008004000c000000c0000004000000800000580040010005000c000001000200240010008003000000100000000000001002c01d0034000000000500000010000000000400200180000
  | 44 => 0x80000014004000400600000000000003001c002000400400000030000007000400100000000000000000800100040060004000001400300300090014000000800400000010004001000000000080000004003000c00200000000000000000000200000000000002000c0010004002001400200100060000000001c003000400000000000000003000c0000000003000000000080020014001000c000004800a005c0000000008000c001000000e0008000000c0000000000000800000000000000000002c00100040090084003000000b000000800040150000003001800000040000010003005c00400000000000000000400100000000000000003800500080000004000001400000080030000000001000400080060000002000800500040030000000000000300000000000005001000100000030008007000c00d002c00100040010010000000400000040010008000004000000000000004002000c001000c0040000005002c00000000040000000000000000440040010002000800c001400000140000024000000c0030010004004c002000c000005c0040000005000000c00000030000000000400000040000048000004400000340000004006000c0050004000000000100000030004000000000100080000008001000c001001c0000004007000000400000020014000000000100240000004002003000600000000000000006c012000c0030014000001c001000c002000000b000c00b00140080000005000400200000010024000000c000002800000100010000006000400b0008000000800600040000020007000000000000000000005003800a000000700000000000004000000100000000010001001400100000010000004000800800000020000001000400200300050004004000c002000c0020024000000000100080000008003001c0000000002003c00800000020034000000c00400240000038006000c000000000100080040004002000000000000010024000001000100140010004004000000100280000000000000400000000050000000000400f0030000000c0000008000000000900080030014000000000e0010000000c00300080000038000000000a0010001000c006002c0040000000004800d00140010008001000000100080040004000000000b0008023000400000000000004001000000200000010004007000c001000400100000080008001003800900080000000000001c00000040000004007000000300040010004000001000400580000000003004c000000800000040000048003000400d001c0020018004002c0020000000000c003000000000000030004005001c001001000700080050010006000400900100010010001000000d0000006000c00000100020004006001000f00040070020
  | 45 => 0x1400000000000008001000400000600030000008001c007000000100080000000002004800300080000008002000400100080030000004000000000140040000002002c00100080020008000000000000040030000000000800000280010000002003c0000008000002c001000400000000070014002000000200280040024002000000000000050000004000400000140030000002000c00500100020014001001c0060008001000800200000040000005005c000000400000140000004002004c000000000100200070004008000000200040000008001000000200000020000000000800000080000004007000c0000000004001c000001c006001000200000000000001000400100140060004000001400100140060028001000000700000050010000001000e00340000018000000000e00000000000003000000300000010008003000800000000000004005000000700000040004000001000000040060034001000400e0014000000000000240030010002000c00300040010008001000800400000000000000000800100040000004001001800000040000004003000400300100000000011000c0010000005000000200000000000002000400100080000004000003c00100040020020002007000400040000004000000400b0000000001800a00040020000006000400a000000800040010000002000400100280060008000000800000040010000007000800b0004003000c00000040010030002003400d000c002000001b001c000000c001000400000080000008000000400000100070004001000000000500030010000000000000000000034002000000a000000000140000008000001c003003400000000030018001002c00000100240018003000400200200000008003001000000000060024014000001000000010000005000800c004c00000080050004001000c0090018000001c00200100000004000001000a0000000000000100080000010007000000800280000000002000c013000000100340020000000001800000000000000000006000000000000028000000000a003c003000001c0004007002000400040000000005002c00e0004002000000d00080020000000000c00700040000004001000c0120024003000400000540000004000000800500080020000001001400000040000020000000400b00040050044002002800200080010008000000800000000020004001000000c0000001000800100000000010003000c00100040010000000000000000200040024003000000000000030000002000c0030000006000c0000004022001800100100000000001000c00800140000040002000400100040040004000000c00000080020000000000c000000c01100200000000000000000100a8000
  | 46 => 0xc001000000000040020004000000c003001000000000070000004002c0020000004001c014000400300080000004000000c00000000140000001000c00100000000030002000400100000010014002000800a000800200000050000003000400200080000008000002800000500030000000000000200000010050000002c001001000800040020000003000000a000c009000400100000000000006000800100000020004008001800200000020028000000000b003400600200170004010000c0000004001002c004000000000000000004002000c00300000020008002000c002001000b000c0000010002000000c000000000140020000005001c000000c00300140080000000000800000080060004001000000400300090000013002c002001c002000400000000010004000000000500000010024001000800300040030004002000c0010000000000c00800000020048006001c00400080000000001001c00d00180010000001000c003002c00a00000000000000000000000100130000001000c0040008001000000100040040000006000000500080000000000000000900040000000000002800000140000000003000c01f00000010000000000800200000000014007000400000040140008001000c001000000a000000d000400400000070000008001000000080080000000001c0000084001000000300040000000005000000100000000014002000400000340000010000001000000080050000003000000800000020000002000c006000800000240030018009001000400000000000007000400800000030010005000c002000800200000050034001000800100000050010000000c000000c000000000000080010020000002c000001400100040000014002001c016000000d00000010000001000800500040010008003002400100080010018011000000000480000000007001000a000000500040000000003000000100040120000001007c00100180000010002001400000040060000000001800000000000000001000c001001000000040000034000001800000200020010004002800700140020004001000800000380100008003000002100000000004004000400000040010004000000c0110008005000000400000020004007000c00100100030000001001400700100020004000000c003001401e000001e0014004003400200000020004000004800300040020020000001400100200030010000004c02300040000000000000000500080010010005000000300200010004003001400000140050000001004000300040010000003000400000040010000001001c005004000300000040014000004401000000000018000000c01b000400200280000008000000c000000000b000000000000000014000000
  | 47 => 0x668207d130000000000000000000000000000ddf0620000000008ec180303f8000000000000ba867b8000000047720fd0000192a2c26840c000231900000184000000000006f7506f8a0200000a6851f0690316400011668000000059900000c662e88358830a9cb100000df00000b98000080e80f88003000c00000380010000008000c00900000010004002000000100340000004000000c009000c000000400f00000030010003000800d00140000040006000400000000010004006000000000080000020000001000000000070004000000c0000000000000000100080080000000000000000100010000001000000500040110038000000400000180090000000001000400000000004002000000d0004008001c0000000006001c0000000009001c00c00040000008001000000a004c002000c00b0004001000000000080070008002002c0000004009000c00000140020000001000c000001c0000000000001c00700000010014000000000400140010000001001800000080000004000002c000000000100000010004001000000200180000014001000000b001c000000800a00280010000000003c000000000100440020058000000000b000800d002400100000030000010000400c0000001000c000000000100000030000001005800100000000004001001000000000020000008005c000000c001000c00000000010000001000000200000000008000002000c00500020010000003800200080010000000003000e0000001003400400000050008000000800500100000008001001c0010020010000400100040030004000000000800000000004000000c003002000000140000004000002400200040090008004000000000000000000000001800500080100000000000000000140000004000002400e000000500040090000000000c00900000000000001001c0030008001000000000000010000006001c00100180000004002000000100040010008018000400100080000010017003c00700040000010002000000300000010004000001400000300010008000000400500080010018002000c0130000000000000800000020018003000000100680000000000000c0000000002000000500180000004003000400300000020024004002000000000070000002000401400180050000005002400100000020000001000000000080020000002003000000000020000000000800500100000004002000800000000000000006000000000040020004006001400000180000000009000800300040010018013001000d000800000000000000007001800100040020004003000c0020010004002800000000000004000001c00000000010008002001c00000080000004000000c000000800000140020040000003000
  | 48 => 0x97c4a58fa927e20000f279c8b00000000000000025c20000000212a0000131c000217113b889a087e99d01a1884451af80000408041c000000000000000c5e800000007decc0d04640000450400006172264491058f8f0d32ec0d0001e0000000000002f5896847564294cd6238a248e38246550791096e81e0000000037e083b8000000000000000453000000005a44c7f213c175c81681cd800018d822211e602a118d66d1cc80879729e24da8eae1e5c11502ed0a750000000000000000000000006888a680000000000000000000c0c13f82ae9a5a20002c3440f000000002801021000000008cec8ca1a0926c66c30e889dbd02a01824000175b019c42f88dc0000412082700001f7a32705bc40000e431cbc160d18e8d991914742c97ba07b13a00cecc02894444b8795d0768ce80000192000022a53b362a18d4512b740b20898df20000151800000001a0e02c6242800009cb0000000000000001a080000000000000000000000000000000000000000000002cd47a68e322f94000023d1a5f000000007a121c100004f9400000001bd2000033d110600000000ac40080287247f8c3990bd00000000e680000233a586012d000000005f604e2954844d462b88850e8b28ea51fca181a5726668f1800010d50000820806380003948371c2c0159d0c8a0000f6fa13f3af032c87a89a270dd26ea4001854900ea2d288f115b606bc50b0fcc81bc1d04802800017d1000000009b2800000000000f420862000076e51f39274180800005328a9c21e4000000022f2436a863d09c00002b622fdcaee197f141200003188ea3008e67a00d6000029c63ff8a820000000011dcc2013e83756816ce729f9336e86bb11ab1f24281a7cac2658f2000005e1c0db98da43063b8400000e5000029b8000000000001c600000ebb102a000063c0d1128ec000000000000000000000000000726140c00000001ec000000ee0cd22e447db4000138305c00000acc800000341fd400018bc272e22e4de100002f80063c0bb9e3d04d21bd047c000031ea0844ccc9eed3e8a1a7c55a8b0b00000000000044c000000006658000000000004ab180b2af4798c5788e160ca61a8c97815ff2530413800009ae2c0255d8e24800043c8000000007cd429825b000000002ea400000001b040e4c0000000187e20ce41c80000000232c00007b800002b146d24cda800013f255b0d59000038083c280000000000000000001f543fc2230c0000000000000010ec800000002914000173e3af800006bd1c142a2e17b0164000024360000df3837f0000667cac619fc000000000001ec9221200002449cf2108011a8000072731aa0de802d12ec00004ff04030183000000000000000120055a8f9094990000892cae400000f14000021100a33dee34b50bc000000000
  | 49 => 0x6258f6a03bb0000000000000000000000000000000000000000016f200003cf8000000000000000000000000003a38000177f031837e062b02db0c7800000001564257217807cd153737f6000000021c800000000c400000000000004290000000000000000000421e3360dcc00001cbe5e7868c02380000196c21d1c43000000000001ac51cb6208c58f000000000000000000036ee000032799504442045cd938c6f00007964c22817d2008086907f857b00006e58000000000000000000000041d800000001366000079dc4e198253bb67bc4a960b8d00000001199066416c866cc058a25b1304000000000002bdc2214f6a8e2e207272188ea2175433e77d51c2217a00000000000035803fa38e0000000000004604000205d0000000000003cd29ac3ce80001f0e000000004961b3d3d30000052d16e53fe03e31100800000000000000192b2f3a000083b0347000027740000b553c103478c7386ad000002a8ad8000000003d40dfb9bc404ac2048f71956f10381688808800030dc1ce0e7480000000000025c9d0800000000000144900000ab400009202a7a8bbcb8781893a8e0f20000031100000000ef30079082a40c0da300000000000110b000041344268000000000000000c2a81b5000000000001b210f48655476602351d4452a4e3082fd398800000001c26000040f4c5087363ad40000a1f00000000000047e0000342600002e98000000000a0fff8000000000011d20e17000000000000231339a0000f0b8f9d00000d50bda17232e90688cea08a321dca66ac0ad167c307037248a182b7477037b4d2994d209983518a460ec147246d505ba81973ef27794831800040ec3d300001e1024b05714a918f5400005744c7f8000422c00005bb8a6a00000408cbc92191584119cd7e1b1f00006f6c0000000000000010028ddd0000000101a85bb07120000755171436d47791154a317138c74ad05e1d89405085d86d1800033c064d0b81950e041e029cdcf1b1b37aa56b03498023037c6b246ea070032e43c21058054320963c4c7b684bc2ae872ac01f82be170469a06579a1b00003f8d14112f2118e00010ea1a2037e20000000032d111a18980002039000000000000000000000010148c9326fa6904000000043c68d440000aa430a44908000000000005dec5470000000041f0a77927300000000720800001661b9c000064719020000cd0800000008b15155800030447808bb40df92be600008ae2019000000000000fcd00008330f860c5210180348a540445000082144ed80003dcc0000fa200002108598c00000002188110c0001b6124560000a488d61383c636042a07493228684835b057419e05c9829f1b5331c066d8a6794291f3c0ae8ffb0fb20000000000022a10242000007f81d939923758000000000008f000000
  | 50 => 0x9b0006a00004cda32600b81ff0b42a167281881d517896c71aee1060d2f000040680000dd509d515a60000c7506ca00004700000000012c4014c0000000297e00010d0000000008a605e4230d2352000000015bc00002f64000024700005a6c764091f0e3e00010530000235a2b10000000000005a502b0917c135672e87929629375c644c5e4a002461e770089f0aa20dca55e496e9c2a2a8221e0fce800000003ef82188c9e24ba464000000002b80000000000000000694000000000000001c00006b01c801eac6b180000000000053d80002c206c54a318173212c705896d80002f5085b821d8000337c00000000000000044f0000000000000000000000038380000000062c000025f80001185311881e8d2e800000008ab0b6d800009ac42bcb6f8000000073e4a838000412800000000000157e32dcb9a9bda10147dfc3671b432b84127039c88b8025a54c8f1b1d190000308024c211f348c00000001b8832d634d882921a8000000007990b7a1b1c00000e88000000049944e4812a20aa0000776800031a00000679954600000000000000000006d94f0a800012624f903422063000086f400010d71d9c0000000000000000000000000000000000000000038fc000065a061c2e8e4e9832f20f900005970e5b971829660000f169f3c157400011bb231c36ea0000562800009685aa8bf4817900000ec023704dc0aa60000d9a000000000000000000000003d38fdc80001cc827f10df0b3b02aa851800005ab12a8098c0000000000000000000000000000000000f090000000000000002e141a89163000040c40000dea000000000000cba000000007fc88908a5e2e1884a0000008c2c2845a00000000266c2458000000029f21a98d33a2ee000000006650fb8126c89d061880000000000000006790aae000102f1a9f003e26491de000038ec169c00000001cd41fe000000000000000000000003c1c00000000000000000005600917000058d80000000104004cd139000021fc000000000000000012400009d8000000005ec155332940000c858db311c431e4c5d04d344d8647c00002d43ff672ec0001b370000434431423db46f20ed0000000000000000000000000007d48e40000043fe0000f33186c000006006c8178638404a2c6849b863bae000098d000001ea38d8b23906e00000000000000010944de400020d445cc80f077580b617a02ee40001e6a077a8190000141b0000000000003fe044285a8000000021466f888b7974f00004490fe58fc021620000000000000001df44e7a35c00000e68f341cff152e1d8831a800000000000d9e000033500001088000041960001025000000006e4c0000000000000000000bb60000000088a971300000001047000000003b1c8a29d560000000000008e6000000000001d200df8
  | 51 => 0x773067b0ada294400000e9000035f200001ee089e0000000000000000000000000013a90000000088f1b1d357c0000000000000000000fc90b05000061dc40e9fbe149e1c58fa30e731b8a70fc66d000026284204d1d1e803d520e2c000000000000000c688ca1012c8c94fda945d00004ff4000104f1b1200000000df1000000006f0029e000068d88a3000000002f8c00000004428000000009a400007abc4558000000056142a317f2392c000000007b800000000d8b23953718000084d800000001e7c0c822491dd800005269d4c3b3e233c0000f69013e5e3856f1cc216a200002488e9b000035ec00008d2194066301e501e2462458b8ad79a4d038e000000000001188000061f800002b600000000b54000000000000000127267580000000000000000001c213b1e0000ab580002b8c52e85740000220676340271ce10000314c7c29cf81e804f7026d80002104067102a000000000b680cc000000002ef8000000000000000000098c0000000000021532d3c8e880000db230f285a050c93c339c8381078885ee361a8d203f8800018b40a549c0967d05260bcc5c400002f1671344d50bcb3acc0000aea800000000000f9980000000000000000000000269ce89215f0000000000000002b126648d890b1800005e4d02a800033de8f111b11c0c000079ac00d8f1b137602ed1d9926c2d1a6794700931e0b902850155057939425e409950d102d4815c063393fa1d2800a4bb795e0453c8b04b53a066146812b073d000020be19c05258000322e0000000000000000afc0000000452600006da02762d62807110b919927325f18f61075310a64eec06e866922c662dd1ee00011b8063b07030000000020dc4020e72110e000000010c137b25f7c000000006c61448000000036ac00000000e573a862af9048823e000a0000aa10000128a7c14000041a0000061903f000024f001a8c339fb1117c673903f98ed241038c000000000000869800011790dfe31200aba15400007e40000059107807b3836f9d0a00006290e2b824a0000000000020082b9400011c018c9026a4eb43a6110500007f890d085411b5c886012813be3b382e0d10406560ad2073cd141bd005f655141aa8000189a3a60f6682fa3cbe000000022ca00006548a2f1a880000353800005b61fa48868cb4800014e28f140000d2c42c837fc00001940000000052b89e443926cc487a00000000000000010d4000065cc000122723a405d800000000000000000000003d6605201a70000000017c4b1d00000000607c0000000046800000000000000063a4db48ca3160e45ac7b99e8f09c07c4cfc603b819780000d17016632506e5065c80003442397008988bc000070e84750e6b00001c686b80bb201a613c014a00001bfa000028b91cb00005ba0de3914a0b420f31154
  | 52 => 0x28d6204c1921e5e00004850f7f00001f6e17ec0001c3d0000567c000000032b00000d7a8000000000004dd1730000013a09258ad82c2246a00000000000048340000000000000000000000000067a8000000020405a40ea8800031ec000047e80003ab60d5c9c5000002580000e2996fc000004e4fac08922d105e30bc91f8d38944745013800000000000000000040346f38b369d5945fa28581d4000000000000000000026c200009ca00003ae8024400018700000000000000002c0401c427594ab07bc25d49530562449a0000aa58000000000005e9074a093a8bd4e1a9a44000069f00000000000000010ca1d5d066600003808000006683080000000098200000000da8389800000000000024a1ef0c079177008063bceab98b615702c100001d80000087550519749162c360c928169643fc5b203b09c2c2bcc00002ab1ab709ec0000adc036a3f2e6774070919a000000009d88000206619bc14e91fa00008f4d1d2800043a6000019600000000000069f0beb030a000000000001fec000000021c4000000000002306000000000000a5d000048b446109840a0e070c000000043bc0a70000191c000075fc00000001a8a481034d81bd330a183c82d80003f0a64d910d80001ed066c0389a34721f40000bc29be638b02dc02dfa03341aa1f98cff8874407600c00000000000000010181d5845f63dbcdd210120ed60000967800000000000e7119cc0000000000005012aa4000000021a9000049d8000028d0000706430c80000faa00005eb91b445b4782cda0974e386c333c000000000002b58e04800000001940000000000000001017030347c057510dd944b0000000000000003e2a0000000000028fc764c7ba147300007770e5a9f40000069c4a8c0e0e0000000053c800000000000000127e192e000000000003f887245013000000000000b6d1e1f000000004e3889d2cac7cec0000b9643d40000e2c8000000000000000000221600007ab8000452800000000000181e529cb85800000006a6109d1676327408ac7de0000000000000000000083c000075e009900003c0449114782254017508c9c2f00002cf4e931f220000050450780001fd473dc000158f15a80000000000028a05914000026432364ad4fbe00000000000000020b6000047ec6fe04560fc2424c5ef1b5e04d659e871c800000001904000000039d8000081f8000000000000000000000080f400000000000000000017d50762039c8ee8000169e09fc26b963300000000c1900003db60000000000005de0000f7a800000000000000234b43c0000029d8ce227c20000ebb95a0000000005a0000037f0016000003dd44244450b55a0a4000000001300000000000000001377000049640000d330df20000bf1016b0fa629b0db222a308f05588df78000000
  | 53 => 0xaa77b84af230300000000000218d469a8824f198289444a6e7c2710a1b401829f4d7700000000814d11b21e2000051001a604b6000000000001b820b500000000056700003e10000187c078a00000002254130275d82dc1a3d447036e0fa7223723dc39f85be212222b6180d10992f62f6a3eec5149a9226781f4029180bc16123c7c1c3199322883d2d0d38be900005f340000a6700002be000000000000246c9750000000000000001f4700008aa80000000434671150f99f5c000065a000000001a6a000015e84240f500000000000020ae0000fd81b1003d23f98c7e0c3805000f3cb5802a713de7b20339a16c108c1194000235b0000313c000037d00000000000201b02a211a4a2080000000000000000003f8c89f400015a11218557000001ed25a60000000099f00000834a1fa09e074400011c300000000000078121c2000000000001cee000000009651b32000002f477500002cb41f8c000181b38ca66b400000002fd47fac000059a0000000000000000c4200005120000095e3cb8000011b0000000000000000000724c00002ae00008c54000000000000000000079005208aec1b200001f360000040800000003adc3b7000012a65fb05810000115e00001210000000029084db94f01036447000020d636700000689157b1e942ef4f090e0d0000595c25d973d190e699464b12fd15c6000006406bc000071c8000000021c400009c60000000000000001e032b54000000015023f8611180000000407e56a40df92eb00001b800000000258c00003ec80003f7e3131176149225284d24ad110db1112133c8f78b69041c183851e80000000000000000000000000023b1dd2000000000000000076a00010c82338000006c006c0000000000007be80001ad4000041d04de0db68010f2800000fce22000000a52000076dc0001a1a0d30751898ca24f1fd88b389a7100f1750000054017434564011845823081b343b083b29f1d0b401d64692a0d90cb87ff82cb9e1a47743334249858c00003a642518b6301a00000af8000007c62780efd070c26363fbc0000fe0000088c90ad00000c9a861019d000000000210a0e1c3939a84a48000000037222bd04080000047e5d9049d935622680000bdd232a000034b82948e4b0b98648804399bd07c400004181fca37707b28000122800008adc91b863e00000000000216b0dd47f00cf39ec700007a9c7bc81d834cc5654e15870328401e6106c032800000000000000022224e01073144616b88130f15a2d0194479b43e919c11edc432443d8e8a3f7a6df8e03235e15ec04a089d1ae11b8c080cbc780510000111c3af0000000000006f90000223a3844077800000001b980000000000068949d180004368000000000001bdc0000a5507c90d7667790249cc0297835e40000e5800000ba000
  | 54 => 0xe5994400000000f8780000000000000020563d7838c40000000314e62885d80f9c22f447041fca17000007e2cff18b4e00000000644192d3c2c503800015f500000018000040b17fc21781ac931724f481a4000152f0000000041b0ce6322a00002171854044605880001a7804e28c0800000003f062a540000000283a00006ca989b0000000000007c63d1c30a8000000038d63ba0ce89fa83f9800011a49510000030c00000000171634a0bd69c5b473e4e6815280001c444afca4980000c081cbc0000d01314c62f800000000000187c0001e4543740000b9c00252c908d101d4800046582448e9f9d541ec63da8911810f0d004580efe86cf00001f7050e1e18005427d4fb18a9b17400000744800002c22edc9eb00000000000000012b800001b689c11593079c1998000000000004398fa48000042c0000d8e074d000000010f4000000000000494000000000000c0680003f1473b4000000017d81964d640000000000011050000000039b8e1c0000271e79bc061937c08b43be8000064e000000010c51193308e88b8044000036a475ac6a39c4832623128bbd000000000b0c00007b000000000ced8b68156c745800005bd222e1d490460000000000000000bfa000072a47fa0f0012ce68404c709290000000109e93ce00005800cf21a03000020a41e800000000745024a17e015ca8c805519bdf04ae0000d1e231a18008000ca304443d3a4bf84a391bd24908dcc9e40d1b07883338dc81c0f18340424b92995a000000006921017000033bc000000000000000000061a03620000000000000000000e6e80001c560000fd200000000000000009ad00000000686902a200a0000efc98063bf851c8ea41e7e20cc1cd458a000025c02bac4b30083000051a0000000000000000000000000006fa000003c144ea00011371f800000000000010c71f441accb5d000000000000000216046fa630496f8000368474d4347219d20706694000000013ae31c000000001aa65a4cfde161200002cd8c8400000000549910394de00007690000000000000000cc407db00007e9c2ec90cb33721318eb91558185000000001c7f2bce0000a5a0000000000000001d4500000000e87855522000000a9e126e22021ca8279901d1e7237bc9aa80000000000046f800000005a009e9225900002624617800022bc7a905e7173a28866fd09940cbb2dfe67e4632800000005b38e59873a45e61ddc3c081e43c440000c791a29447c2fc859082d81c5424700000d58000042a4d99922e0000195062f14e1000009dc3ab000036b020911cb8c3c0bca2cb10d5946416f617285548000059c697033fa2cb148816b0a288000010a2ca00000000000084a40000000155e217c000000000000000c08108a11220000ffa124944ee8814a5206960000000000001de19
  | 55 => 0x736402514600e0c13943390c063e7a17bcf30a13e0f8022ec1bd8a9d00000000000077b2bb200001fe096a019a8c406b61e7314160000000161700000000724800000003b0c000000020460c4800000000000000000014db0000000000016ec00000298000191a3a840000a408000410c00006a5953b2ad00000000169a0000000000017e700006a9c2078b2031520000a388d820a6669a800000000000000046f000000007fcc0000d37162270688a7000000007fa40000000127c89ec0000000275600000000000256800000000000309668784c0213b43de0b2c0001df427f600006d59099247a71f0000000000000000509800000006550000000000000000b698000278e00000000000000000007c4000000000000a6c80f71e1c4ef08048ef5193a74f4061235423e28500a7b969d2eb41f111d822510a3a83a051f9d3a213a1c5400015280dde00000000000395e420c891000000000000e320000168c866000006dc11962b040000059258474940001da9000009a8000089700000000ce38a4801fc6044f4080003aca0000d3700003b2a00000001a7a0c840000efb0000000024401f2000020da18d8962800043ea0000845800026f0000000000000026795400003eb07da87ec8480000311e00005018000000000000000000000060c4656062304c21ee8b4319c442466aec01d9f760000000000000000000647879180002482016c0000000000053d4b8b800015c23cf43798000151a228c000000000001928000000034a885f81379d7d05580000000193c00000000000000000008ad00000000183a0d80000000000006748394800000000000000000018c28a44000140800000000db385aa15e00234000184841ae29bd05100001ec2752814511f22a6a1f75157000000007488c3323a737fc00000000000479c85780000000439a000000005c238da8034000000000000b48000000000000000f9f000012262bb40000000400e000035a91021baa72146771f893af42ab47529fd9457a7b400001110103000001fd000000000000000000000000000000000000000000000000000000dc873420983796433011500000000000000018422604682c4cc082500001178d1890b600007674d7285450000619484e00000000000000000000000717404d00000000575893a8d0b0000288400011533d5000006a9000035da41f8bf1972117f806947a7800025120000eb98cf50000000090f0000183e498519a000000000000e41000000002ffc955188b21480000e0f889c18ba1fb001c81f400006f84ef11d0134e4000000010bf1cfe00005bc877900008024000154e164864e40000e7b08cc3a5ca1700001df83590f8e0d6600002ca4f5e800000003ed86cc1a4e00000b58c6f800042ca82000000f9621b800000001cae08f210150
  | 56 => 0x6f10cf62888a3a00000000000023e000047b22f44b6202993e3c10301908f0b00000000ccf0e140f247ac1187000000001c480000f7c00002650f8917693c3a3b705c991230000000000007172c0e1dc0d6300001c380cb898e800000007928e0c1b9935805b004e98000000047d41d2810c2edc0000d84000006c400000000000184a13dc000000000005c48000000019d816a480a800006d24b0cae68c912c541c80b3a0000174c00000000000000000002de21251572000110a836b2f8e0000afc89bc2374846c8c71489225e1a24a5813d70a1a73d80000000249e00006da800000000280e141a8500000000f290000000000006c580000000123c4f680000000555c00017010000000000013cd12b40000e1b8fae0df00848654000041a400000002350191a5fb4fc09ba640247f2450411b02dd600000d68d1700000f1c658a39e000000007120000000060f000000000be41a78000111b07207980964922633166a00d8719291c9e00000000000081a53683d89fcd43b4180018e952b22c46214007157c0000052400003ad00008b6c00005c30ea8000000000002bda76bce6f15c1292c1dc4d5b21dc32ce3170a3815391358101c00000002dfa3dc88ad00cf2f447bf0000000041a22f99199816e290a8978000000000002e1cfb100001ad20d982ed10f9000000000001262003a25046019e87205e0e64c901e910e326b78e399c66249a0154244068f31b8558428d964600000000bf989c00b480000d23800000000000000000038463e00f1a98580e625e5d10e047202f858203a113b20000248466f9e510000775400011872dce53d917016be000002c01fe97bf00000c8c9059b0f2d4c2e7c7338522165a000046680000c027be0000149700004da0f2da1a4000005189c700000f9c00000000000000000003ff00002c4806a400016813f3000009dea337132a01ac0b3a1b71a1c03690290000323253b88249c22376e32ac1c2800000000000cf5825c38be07d4988078700004780a9388e820803de047d1b2b08a0621c005a1c31e48000025319401a000000baf9fe726266204290000025100aaccc311e100006e241288e7c000000000000bfd36140698000000013ca32f4375844113982e447748c3e0310182c000000000000000000046d0000000000003613f581ab80001203047800000000deb1e6a714400010ba260c06540000f1c45b807d85e21bb41d2259c4e081e70000000007c5041c000040510350724062600000000000000082d4000000024f8000000000001a8239d49d21ba300005a1c00022d304860000d83000000000000000000000000e100001ddd00000000ae900003a92000061702e223160000000011400004e94000000000000000000000036a225240001b2e0000505c0000000000036bcd4e80000
  | 57 => 0x167811849ac1beb00007844c9da3b22f88626057380002fe0000000003c208ba10e0c2d96720000556c000123624c80000bb0904300000000d4a20f623ae71dc000185d09527288f3200b93b8e735c000029f1382596c0ed000026b421a0bab800000006864000223400000000265007b1b0800000000efb0000329c000133b150e7ee916f000016b252d409e1b9d1c30000000007f7040a000109c8c05201a491800000000cfa73ac00000c41928000088400000842823cfb09d1008f682f826a8000078600000000000408c0bf8eb00a2a1eac21d42ff91950d3873440001a8c0c1006e49120f9318e600000000000000000002040000066e00000a1864600007a780d70a4a13a221e83c68000293466b861a80001ebc21c917d080e40a0729499917fc0a2806e0f4b10f300402c94413162600be000000000000000000000000000000000000000000000445909780000e12805c8958000278a0000dd0150642567588d8c1129205069c000000001c000000e6d0d4800000000e9d84ee00001fcc057000029627b811858e2c08b828c41a29fd540fa0f246dc80000d286bbc00000000000000000000000ad03a850098000000062740000000093e0db0e2f0de200003ac00000000000000000000000226a0580000000000003ab4bdc80000592000045a8000000036a40fd917e11680e900fc05e4000000004bc00000000255c74e0c460000516105792d70000363c0001d40000000007b100001ae607f858800002ce65d8c46b8a7047521d906cf22e10000000068e997b2b8e6c5c6418000273e47a8345975107d42738693038e069a470c95982c700000000000054b380e00000000000000005c8a591a380b5c6cd50590a7f09be5404fb39c17095c6bc840b9b9b11e245e116b12d91a985fbc83400ad00000efc0000df71d92457ca98000011588a2000000000000000071d0b2a3d18772cf6205a333020000b6a00003fb00000de68000000000005f500001f1a4cac0000bf60e0e00000000613268c4b440001ded424c0000000000000006708fa080003e7e00006ab800000006ec8440800000000000e8f02330fd43b6d0eb047d080c1d7cec3063400003dfc88f9421050c84c80cf22c943b017e0e5a20eb239a8648e43815d3558895452600003b66000067b8bd50000539400000002b200000000000000000000561901800000000000000000000000eec0000000007e850f0000000000000000000365800000000000262400009a1000000000000e5900002b7e4ffccd500000000000000000000000102852b06d238024f00016a3bf3d3868f800006880c280850cfb000016a6737c933000015240930edf0a8b3290000000000001a7420b88b500bf000018e40001b4d27848468f6b9b3e28c21144b07215211422f00000057e0b880000
  | 58 => 0xa73800025200000000000000007f380000000354a331c9300c1325f45948a80108719f2544515d18631662764023f0860083a0a909af9e2a092055e0000000000000c70e97800025f800010b68000261800000000000000000000001b502f924f8085081db00003358000164c00003b8ca1a135b26f64ab8d5a98b934640000b12934835be4ce0df4969200005b300000000428445480001c5c000000000b80acc00000000d9f8000273c86208df86a10a300000afa0c7500002fe4b370f1800000000000000028d47f0800015c90000632000011c924f20f9c000086f000058fc82d000005ec000030c123f2ea83fb80001119000000002e6800000000000e54000047380000000204000000000000134d000000009a000000000120027e2359283e5a602a7224200003ab854c96d6084c000000011d30962000000000003d2655408b6082d356272d8705a23013665250ae70cbf00004cf8231800000005fc4e8d09fe00003e8cf5a800000003b880000000350c000107815fd114a8ba44c8127724f61a9400000000000000000000003afc15a91219eba00ec82a4000000043ec0000cda0000000048606b580003074000081a0f49476a1e7083fa3cb1fae1d74ae1959434687fa01b680002440000070280000000659400006d300903b44f4f876a00000000000000000007fb8d2790510000000043180000000025479f9ad01dee00011118f273de086e48e3858922405d7825f80e600000000f839bc3289c3150de520ef130a8e0c803000046fe54e0a0d00000000341c000140000000000000000005f825fd129999a3a7c429c1141ec53c9a04c00000fc138f43fe802802df3f7000002e8800000007b64b5a897a00000000000051900000000cb880004730000000000db0000032c0000000000000010f60000000000000000000000000000000000117e0000000115d000000007c800001f3e00000001e32000050ac7ee143c0cd60000db780000000257424098e6140c4070b3400002d1825dc4978ad935b278107601cfb3d0c61c89e300002d2a0000809913d00e600000d4100322e014f0620a03134ea3ddc0000000100029380000000131a000048e814b3fc8000000000000d7e8e3c9af00001cf00000d7400002712696ca618b0a218c45d02b58043020a47640001dbb000000000001bc6000006c874b11880a2000000000403000000000001c271e6c7eacbe900000cd4038cff88000343a1294f1701dd39cc384c47f0000000000000000000455e0000a168cd4446a0000f1b80000000000000023e400000000d180d3c00000000000000000002dfcd540cd734b23a8000002730000304450e800000c40a2c078014d00002b74000157d44d6000096c16de1f5a3c885f2a28a179e14b05991bf6449c07a911e0e513ce42670a121a58
  | 59 => 0x40c960000f5c1bc5317600002cd949524523998000199b0000000000019af0f447a20df987e5363c564512200000cc05f98f119d3c1d665b7010d93ca000087940002097453227ec22c9b230dec8ce433700003c3615e00001b8e45986c9881f15800f5810505bb19b700008c9d087000000005c2504b11390fde64cd0aa987d0000000000014031ecc22111e39b8a29301654a519f0322b08af07d09fad000000006e988023312000000008f62ace38280000000000061e80000d5f0b82444ca0f01f71fd035fd0e8000026a400000000a1f3ec0000000000000e1c14c400000001fce00000000026397e07506ed11f42ee62ba84bd9e31350283785e3000000003ca0a8a8bed000000000001c3b36ae0000a879e0c00004b7830f000014c2660800000003cf6573c7f59dc53c323084044851c403c59a8b7aa3c8000080443e89deb3e28700cfba00001cac00000000ed2129800000000d0f429400001601b6b03de00000000e450f82593800000000c1a01991d00c95094e8060805800014586be8993000000000000ecb12ad11660000cba8218000000009a60d060000000016e236d000000001190000468600000001a9a367681acbd28000136250980000004000000000001fd1187a00011240000385a3a100001b133eca0001101000000003378952000000005fd08550000226c000046da281000000001d317590000747c7e820721690000000001290e380000000000000002f34dbfa3dd0db20000000084b1bae425c000028202140000f16000000000001072116e1f02215c85a137f000000000e99353000029708e6000034f27204000000000008cc400014cc00007ed8000063017ba00000000aee00008d4c0321404212a3a3400021cc4110181444d000032d8823400011aa085803a457a8d08159c509c45395ec3fd4561cbc2000004ba34ac000000002480000a528ac9429600008640b49360a00000000000000053880000b0800007260c0a92e7000084b40000aa11ab21f60000059d1fca757c0f400862e9a00002eb23ac2b72334c000229a00000a8cbf40dcb045a8b203828d40263e00009749ab032b236a80000ad713e07e947a3043600006b5c660096400000c78b8680000ac010acea7998d2b480cf91a3208416e800002c583503f2a48cc587948d19f07638af8990d16ac3ec42ad22830f3685fc00016d91aec13b08b900000dee00006481c6a023a13904680f2a0000000000021d100003cb475f0ab421563980a530000000000000001b4c0000601c3c99433043c00000001e470e7e0000c5a0a73393c1fb850900000000727c000000000007c0400005e31dfc13650110000000000002eda09922a200000002127182e5c190869d5e25ea00005800000098a77640001ee10000099400010412d1c00000000c1e398c26e
  | 60 => 0xaa523d000005964e619c67000074b479585af303c68306a81e2530bc3bc4b7f000013c4000000000001c060000ca48c370000026c40892520000216097c07303fa47d089581543380043347ae1db538dc7db0bf59bd300007b4c000220f0000000000002e333f00fc8b0d207c30a25058a2fa17300002980c6917163ea02e48cd11b8f0b5a683c3e39bde109a5ec02831d6e00000000fe08cfa32ae8c28b3480003c480dd0000239a102879688d88ad51b441e9cb779b8404fc74a800b0760043e46980329dc4388000000001d921c884f9cdbe00000d504584b1d87f41dba163800000000000219c7961d1d0f3400000001ef900001d9c1d183170c187dd50fc906500000000b78000008642ccd075236f0000000050880000a4e6f243450000000000007f8800015222e8c00000003c283b900000000000063f48e11ed801f0000042a80003f3400000001ea616260000fc41ce8180200000000000000046bc7fc9ff935c40dc4000000000000000bd7059e000044fd056800000ce27b000000003772000078d1372090c450012c1d8100000000b219dda087e0000000000005a01ac90701a04000000001e984f1000042c104580001e70532492b20e9100227a0000033c20e2000019782a919ce76c429284f435526b0c0e5800000000000000000000005f84c300000412600000000f9500006bf4a72000000001c34865000008460000000000000000000cbe80001012735455300003f6e7df800000002a280644ad6a0c618d07cbcc2b8000400c8cac00000002f287f58000053d145e20f4000001235aa3a2000016e2248643fce66181332fc7680bed1fe6051c8ed04d90ff71d58364837f00001390200c0000000393a00009b680000e0848e41051f8220c00440c57930025580000ef6000000007bad0340dca00000000521872d000089cc0000c1400004c5865b058a000000004da0ec43d123bd8547901900005e0046615553a12000000000000000298d0a7996f1d9a39747281654000000000000fa700006a447e8800000000000000046b00004338000000000000000ee51e623f6872501d39737346661ec5730000000016085df95f834483ae40001bbb00dc5219145a0672f8a1b74ad91016000031fc0000e103ec8364cc928000405667844ef1d1814be14a0000000031a804380000000012600007ed0b7e3a706d38321800014c812907d600003ac25c0800013d5313e613800000002f540000000159200000cc40000000000000002859d8c25ca15c820890f500002fd40000000186c00000001334000000006e915bd0b4a000000005c62fea000070780000000636400000001b7a0000b901519000042004ef8ff3081288bd1b18ceb439c5bdcc5889480afa5350b1c8000000000000001a0d2a4a42b00001d0200000000000184
  | 61 => 0x59e4000000000000000557222d1a681d38c45057f00000d7c22589be1b2c0000000000012c685840bf1afb1dc04c60ef4000000000000436000000001ebc000068d3a502e188ed81c11db47b748040a412bc802c90a4939346f629404b6800018d26484000228f2cfe0000000121c2598249400004a123fa61ac00000000000834000005c7000030cc0000e2529fe8dd40000000413e00007e3800000000000000138818aa0000e17000033cc6e54a6880001cc6013c00000a43b8200009d996a50000151ca5d8e6f00003f600000d74000020e4b88800002d20000eff800000004d9c00008ec00000000000000000006ce4000196245c60000cdc110e00005f64a62129f000088b018510220b8a0364c9f2252075487488cf800000000628e208cdc07222944e0284fb0fb462550ee8122189231d009a09f10fae0000f55138d388c0e30637000000000000000000023ee53e8ce98000096008d87b88aef326e73bc0001ec3000000011520ea70000527c00014e8343e519868a21f7071a165850d19430e4453b498792da25006e9458d9a4a2cb07994e389ace000000001f0800000004b48a92090e3696745c743a2b007b211a0982a29619c03614000000028460000000168439b634686c8952a00000000000089b21b4175ca3c94c500001d54af50f4140e20000e2d1147000000001b8000000003b3cca7824e000023cc83ba2a2196a13e80001aa6035e2828947181238847da487d8a2000ac16200041a7426fc094c000004c2bec41904a10000430a00007c7800000000000000000018741cec00014a0000067cc00000a828ce00003521b70269e302c00000001ed8007000000000000000105c8000000000000000ab2000022e8000000000007a3400000002ba6089c84680000388000000010ae00000000485800000002c8c48f00000000000078a03b200000bc4f51186d0000000000019c3000083287ac206d00000000297063b00005d0400000000000000000000000000000093e80001a8458acb0214ca351e0000b4ca1620000000051d03ba1f0e3b28471a00e2b986c24e780b2721806a34748181423427dbc6df20a52a4065b424b8201410600002c90000301873d000013153ab445a4000030d1b744fe49da97e40000139915b0a94224e00b075a9964450e0c08c251f9b024000003cc80002d72000083c800002947d20c3aa0c900000000b5a00001bb800000800000332800000000c29068c00000001bb31a44000000012552bd04ee823a000000000000000000029aa00001948e35334812e0000009c465c0000f211452040e5874000000000000d58000000000000590000032a0bc4000000000000000000000003f523d21258000003d0000000000003441e248604000000000005420dc680001ba20eac0000000000000
  | 62 => 0xba321090b4c000000010ec1a600f18000219337ac27a40000000105400001901c553598068c000133f1abc000000022b12c1211540001425131e5d9c3e197dd0da01b545680000184e37e81f782eb2b043930000017416967aad1978000044059780001b660000769896b00000068779c7aa838330540024a0a905631c269488a40594252a336d0e0000000000000d9505770e5800010790394471646d8e9ca11810e27e5846c000013c2097800000000612330400018e3136c250d0c58000000000006be800036c463b8bde23bd03023ed4a1a8000000011fd08108da00008b44000222a438e27080000971159e0000e8000002a140f480000000000000003a8897d40f22f140a210593d061c9494ba02000008d68146092735462d78000000000000000000000000000000000121700000000ed580000000035487c21db32205be4250173439946d800002117000072351000000053021acf6e082f3a6c1134e5395eb0f7e000000000001206000000000000000000000012450000178400016212bb48228f18238d2b080000000000042020000000000000000000ed600003bd28c840000e3323140000000030600000000000000015b68474b690eb24498000018d000035780000000000042f67e88000000040ae00010c482d7000000009ff00001d4c0000000003107003ffc000000000003ae0dd8830700006f60a25000000000000000000000000000e461a060000000092b950d00002af00000a0c17321f7800018db1bd463382f8000000000000000000000005e6840390323f287d58982000033461f30000000027500000b659ac40df628e441f1aff08e65e8c0000ed01b7600002e780001bb00000b0e000027b2000000009eb0000613ccae0997351600000000000225a4aeca0780ec1fa62d04c1819840c440000000000006821dbc94c8cba1d683ea8e8d97d72338830c06f944f059a3568f56850a02da19b46e200420c2200000ac000026b2000000003752a0a7cd00000000000037cc0000000373409100a99a263fd8000117a14df000000000000000000000006b70000162438d06ba9b010000000114a8000405e1e14ed396a9190a0000e60800035b87dacb1f049b00004e84a098000000077c4e3c0f4325081560000019f392e839c00013af225c0aa00000f6b3a0c04d8b95800000000000a4d8000000088ec9e6092b00000ef0e7e98f71ca80be4663000002d800005e100000000353c0000686000036209ef965500002c54000000000003808ae58a0e00003874000000036f62218000080b35e62b88000000000000000000000016c200004b580000d900998e82800000000000dae80000ba42418a858000000033b4000000000008ae4a0100c000001040000037700000bc00001bf900000000dfa800000003f2105500
  | 63 => 0xf263aaa6cbcf8b80000000000035f21ae0a9401e10f80000318a4a94dfe1faa2ef01508000000033b250dcad997ee097435f02d90ad20000000000000002a3c000077a23302fca0000000129100007d3d11206de0ff200000001ae00000167c00000000000788100805ed00008ddd1228fdf422a5578000217739ce000000000003df643941f280000000000061a0000000005480000000148e0000000052b00000000378237e0000000000000000f6e0000000000032b608400000b1a1fb68d0447b8000287023c0000000002b86f5cb61800000000000efba31f3c96811c00008a41bc81e9400010e01824075841e01060000000076a182c2004000000021240000000000021bc00002208e551a1c0a2a262820f951200000abc00006972e2a0b440e620da3a8875a057b9fcf1f401b009dba135000002085cd843909067c4024693750e3c0000f9c1fc50000144499382ea1b2e0e1c4628f302c4e2f6c00019c5077c8c8c5cf2104236e09e00001de004aa4d80a239a00111817d4000218600000324000135d10ca0000c0e838a358e0000000236944f47bbc0e0028106b826203e514690f4624f44459f352fb61a9c324800000000000000000008ea00004808000351c60b4e3109592f6c269439f0000000021b82dd0000213c66f043f800000003ad80000000000048c879080002bfc5d4000021cf32c014780a7800000000000000000027e60000822947733b452d80001e0d000040306cf97a6000000000000000416e5a2436b00000000520ca240c101bb6000000000003b160ad09caa1bf1e78635cb1e0df0163a000095e8000369e0000f7f80003aea2020098800000001590000000000008c1400017a123301e3800000000918000014418bf46844e48a090000000030ec00010730000463400012a100000000000000000fe0000ef7800019e8882c5cd1f8e0000000000000000000000000000001a2c000034c80001fbc61e05a21b8331f00000d6d800039104bfc000000000008074e18800012f253700000000018c0000d929bee00003cd098093cf3d626ba4000210c2e800000960966f04387800a4200002d7a6104dbe8f5d03760000b458aec0dc2465d1f1a0163ca6000000000000000000100f845222a000000000000000000000000000177627649770000000000000000e710000000000000001b4800000000789000010102450000000074c80000000191882f400000000a2c197400000003f4c13b400000000000000000019a600000000000000011ba3a90e07000046d400449e20000000029245a1000044ec7b5825693bf03c621e400022e500000c504198000310468b4ca399ba18fa3c1000014f840c23864d6d21e126b836004709149049001dc75f80002f4e665400000ac2cc283cc81a80000f5200004cd14eb3ade0
  | 64 => 0x358051b00f400001b90c7d000000005d28b8d800000000000000000038fa4fdccbb800000005f3c0000000467e79a496e0de52a0607fcc1d8000304e00008260000337600006fa80002b4a593400003b70000000111895fa44de00000001f7034540000000000020d275c48bd870a350672b0000030544d200000002240000031802f300003be600011750000000000000000126000001c8ca100003f3c0000000000028b625f00000000000000005118000000003a8000000040160000b8d11380d7082240001bc11e5e000000010c30000223c71680000082000000003983af200000001159000000000001436000009f0962144508b0000000018f31ad0000001c0aac3338000026e800000000388c2b1755320a60b85d6a367000000001ad83320fe04de800002c400000000000000023e000000000000000007cc00000003da4301c0001cd300000000f3c000000000000ec29bba3322000000001ba2e100000c7c81f03a1c52b8a7907ae3efa00011c110ed000040b09f18000000067d000016bf00000000000003615fe34c4929800025500000000166500008c1cad19d6900000000000000000000000000000000000000000000000001d685ee078c00007dc80001a5100007ab0000000042102ce00001c6f0000459400009a200000c2c000186f00000000b9d8000000000008071b0b1d0c2f1d0f88f051278664085904203e9a24c86d61f31165c887c82f19b1430e6e1caed88d400004840000035d00003454000000028148084000220300000000000000000006720000000000000e7c00002e1391e0000cf60000000001c08daa35534280000000000000004dd0ee9917628fa5fe11388d4a0a9a0000000000018c82454000234500000000000000000006bc00001660051e0000ee4148a2e6c000052c800017660000ed70db7000000003e100000f04000043b80003e4e6b8d17b000000005df478a9f4c00005e6101b9c831d008ec402f1966034e658464205752614702c5158961191c00009a3981927920000c14800043640000bc198dd00000000bfd80003dfa1e78000000000002cdc92f0000262200011d0800010b2210518c00000a4c3b142c20ef23c70000000016e300000000000000014e85d3007000002ffe1e18385936c00001f58afe08ef2e5000001db000000005458000000000003320000000000000000000000000005eb0000148b1c8e000054b00001a5e8c4c08f00003e60078400000002462000000000002ed45f4c0000b81000089940000000000030b081480002c5e2e700001ae70000008851403922db000002c308dc09fa000000005d50b68434c00020db360e3f582b185d80000000000000003fbe00000000d8100008c44cce8000012e0000ad70c58000039d081b000045364554af28000208c00010b30
  | 65 => 0x5c1c000062910f8331073683df3c3800008fc236e216a2cd000000000000000000020bf2bae00000000000261a42a05e0800027b400008bf8b4522fa24d40c9800007dc00000000fc6306e0000000000000000000b7d9ea137780a80000226219322ef0000000027d82b1848d20e13554000060c8325215a0d683dd800000005f580001f0428842840c1a170518100da09921a6f440c2d348d580002a44000090882170000151000000d100006058de90000075c00000890c63193e6c8800000003a524fbc0f6134b27ec16e400000001c3c05949289eb224340000c4198612d5e000119a986846d80148bfe84f5345e14a8000000000000000000000000001f2c00017f623902f280000b0e454c000000010ef0cce4b1ca05800000005060000000000006ce8cbd0856000071d0000165300000000a4e000000005194000000000005558000000000000b0454c0ac81f888a300001df028128d847d5800000002b3469c961900001910ef0959a2cd673e88d221503c0285e400001820000000011612683ae06234de60000000061d0426233e1e900000000000000008be5125163127d209c0794928c000065784738ede12681ba06a4862e0b268d984fa08c80a606a4d07d9aad217804b82779d4e0d680c64f1e08380bee000000000000000792051c1c3e42388acce2a23b7011c8a0012a000000000000fe8180e2c8863ec2a023683f0c0bb873807962e3e3ae8f84152123d8000000007aa0000000073e89da000000000000000000040f00001db226e22cac36c0000000029540000d5600000000000132e082c7e440000000000000011d51f18000063580000000206e03c860a800000001c4499d0396000000000001d37366c000000022d900000de000000000000000000000000000630c00000001e06649c48219d704800000cfa8e3716cc617c000056c000022d800020ab16b46084efd932d00000000838039c10cc22b8c1f000010561e3cbae800012dc0d9c91c065200000db80000ab343ae0b085af90260000455c3b6981c2a7c32180000e3e37d80001131953a000000006708b0100007818cd3800000005e58d69826d22603480000000039b024b800016ae1f607a5400002062e8400000000000000000000000000000024602179ecb3ed47a94f138e1500006c44000008b091600011c6000005360de4a1d976210884aac00000000bec4d1030e8000443c01f4f80039e201400000000000000079b01d080000000194400011c50cb0000000000002a120000000000005944d400000000000068dc0000000000000000000849000000003688000409a0000000000023f20000a2d00000000000115680000a0400000000000000000000001131000000010800000000052010a3932514fc10b400004851f9e
  | 66 => 0x17cc0001876000000000001acf00000000ecc12d00000398467f0f8e33fa2dbc469a2dd31103a48a94a39005604645024017f44ae0000000000000000000d8a09fd00006ebc80d800000000000aaca3c123b8000000000002bd2000021f0b3901420000afb800009f202d514200000e2826a000000001bbe8e1c0001640273a58e00001c0200004abcf1f972400005524d240f8218da3b18000179912e023907a296f8000000003ba80000cca46f850c090800000000b5099c90000791085100000000000000007663de81414000000000000000c5180000000000000004c2000000000e68d3800005c780000627012000000000000000000000000000433400006120000000088980000000321200000001b78321e0fb0842945c00004e1ceb396c600002dac0c5800044fe54b4ec416ad2308000030b0a2e30a08be05e1843c00000000000030e391414b4000205f235865051148230000000010e2a3000000000011b87e9000039d862f8d0a0000409c000170e00005154dc58b30000012a800f0776309a0fa0109800044725dc40000000000045d4d0380000000000089600000d9811bcbff000000000000c4d1d2703082814531000000005c00e7180001eb2000000015ab027c78a400000004786000004f00000000000034113a2000072e0512998300003c3c0001ecc2de8000000006bd00001b50e8984b500000000ffe094f00da61a89e8819b2c5a55c441a82b120ea0000159800000000000000000020f400001a5909813ac0000fb31e9a000062947cb8000000000000001da800000000036159617be02a42921899181c00000000b5711320000000000037600000bd0196a438c0f59133075841a646b893f8ed8374e0000a48233c000087f4261869a08600000475800000004710000000030980fd8000000000000000d3182520000000000000000174000086c8000000056784a90000218a47b421380003c7c00000001ee200004b9042d0000000000000000538322431dd194000038220000a2600000000065800c800000000eb0000000000000000000000046f04a182af0b3f350e0558cbe18c4000040e8dff90b3000000000000000432283e81ea94103f4600004a021483dec26800001f2000008a750cba3af4174000083d9cce00000000822000034e66db400007a6000000008680895058a6fa800016423dbc04547fc034828622cf80000ed51106243cc6797ce0000000008080002dd480a88431f43000000010be8f19000000005910000000000000000b8e32988f0800000003eae3e0c4ff806900004d44b4f96b800001b180001f02377a1ae8a26820c33aa5dacd7c00002ab421151cca0e20000000113f1808000000000d980003742000000018c02dcc00f8000000000000000000195321120000000024f1d560000000
  | 67 => 0x107be43362af4a4f0272234e80b06e69839211888e809e8ba71b4a62189200a852d66515c88780000000554400000000e668d3c000000000003abc000000000000000447075c36d80fc00001eee000000000000000000000000001cad000016dcf45800000001f7c000017545a46abc0ea800000007240cf1000036be000000005de00003be46fb22d500000000214800000000000000000040e0505047c9bbf0000000018b0000044a00000000000274e4a6814880001b140000000000001dc0f801c1000041c600003b6085b22240000000000000004c880002292000000000000000280216c08e5099d45ae7be80001b481eb47a6421b829709320000a0c95341d96000000014af000000000001573232466a5030206c073a58145f2151f25e204ac5da8d2a06de00b80000cdd000000009ab992300006b4417f9a7d00002a280000000000042806c38ab100007694000000000004b880000000028e855c0000000000055504a800000fd018cc00013ac00000000ee880000000000009c00000000000000000000000483800000000000115c0000000000059749e0987f063e0000984016f000000009d7051a234600006060000000069dccc7000000000000a6300000000000000000000bf20000000075700007d6c4f900000000000000007c81d34619008b1cc807f08bac000217418864160e06883b0000520828f8b972da2133400009f6000000000000000072e58180000000000000000000b47000000000000000000028b4711922a0000000021e9ab437441a543491b003c50000000000001a7e00008038dcf2c16483c47498c20000322c43821b011dc588d12b1a4c0f4250a000000000bf45dd0c930a83000085380000ffb37b81348000123b14020001012000000000000000000017de000078380cc00000000d2b0000000000000001f39000000003e2800000000000000000037fa1de0271867614780dd80740000098027510278602000069008fe0938353c00000002329475c3dd4000000031500000000136e00008f7ce34983600006ed800000000000113c0001a952dc27358c47152e05f057742389f360ee656a000011e845c800002df13de3de47ec80078000213e2b2ca179aca38c06a582c6a3de07e203ec664971035b014c91621212219e828444b0000000050a800008fb394c7a8cec11e210000586c0000000424055745ce810324947534000000006e618b466183da000068fc49f8c183c5e38f08ef0000000000010db000000000c6000013310c366b500000000000000000da004400006f8c0001a6b0000312c00000000000000000000000000000055d8fb93cfa00000a0000000001f9000000000ee873f0000000000000000c1a95980000344c0000702000015989870000450a00006388000224c6dccfc79956000
  | 68 => 0x1cd25ef4d420000091c000000009ea00006004361800026607ad0c5013db1bce3e951968000251e0000d1ca0ce2a1800000000000000000003a7865500006a40000000000004108a5b8000154e0000773a25f316a681400000000000233800003081dfa4fc8c659a433fde0564b9e06320000384915f163d160c0f9837192b6000000007d4120a47360000000090200004ac517f13211ece36191d68f3b23445b3c00000003e94000000000002e5c841cb3c000011ac0000b068000000000007c580002646000062383f720760000682924e282251f037e8000000006a864d0000000000009c8800009b4103800000000000000000012a33750132088618ac46d64be40bd1a6436dc8b08000200f0e883938b61154c0aa069891c0a0c805aa3c30b3f00000000578ccf18000148c000000018e845702534000000000001b110ac92b200000000000000044b00000b018000000000000001c1217d00000000000000005a2800013033bc652b4652844e17202d480002374420c6c6516c1d832b3800000001a9b00000000d4b877e09444fc00000be0384a2554b110b0c39e60000000000005e400000000413170072e409f91250000213854108a033404bbcf1322283c728114bea1b9c3d047fe800005fd327a0a1c000080d0000077c0001c990bce8dc8fcf82d33e6e48f03fb19973e3e0000d6e8905479a197c34280dc45fe5014430878816ca7fd40000d3236f200010c610e300006f80a56000007400000ca595c400005398950000002344c80e91800000000000ab8000000000000243800000003fd40000000136a409400017a400002d7418620cd0fd600000001cbc0000611829092ce001805a02791f680e785dc82bd1b5a000022280001dbf00000000149133d2d46000068f800026828fa0000000046a435c800016752f82770ce999487000000000000000000000000000fb446e221087e49f234228781c000179500007c2c4e50e3f00000000606800000f4479105a000000000000e500000000038ec22509d2297c000017a078341ba000029b80001fba00000000d9c0d5e86780f01e580c4a0000f20000000000000e820000000000003b40000000000000001cc700008f3c540949d000086cc00007b643e4000076c80000dea33a800000000000000000000000000000000000f12d787cc819b0000000053ec57e0c5947b02fc4000000047b4035c3a38b433c3c00004bb0000342a0000a440dfb31225e20b141aea0e5033f44609b97407c411cfd70000000083700000000000000000001dcd00002b80465004b00001f80a22125c02980000000063f000000000001cc53e1447387699ae6000030ac00000002c3c77501e581c635ac00000000249137e0000c0b92702a6c46ed178195d21ec3a543dc80001b3a797437
  | 69 => 0x4fa0b800004fb41728000000029ac10402e443f05db044818e500000000c3880000a981cc89cd9a7e410e00000000000000001f094e8c9c0b0a20fc000000000004740000000012be0000000000022c800000001a0800002f4c00000000000865800000000be8000110719cf004e4174ccc18000a184ce49c82370097c03149f51fdb000000009a51d63000031ec28797cc000079e40000000000020c800001272e8a4ba0f931e13035600005b8981800c00000ada80001f0c7628d3d800000006a8085b866138661c4015a9dfe2708496c5b69df2154a000083595d0023247cd03b9fa93b5a473c52c1d9731265d98efc0484000025700000000458e550084780002fb82a80ab30000000000009b2000015260000000146d0000000051323e123cc000058e000000000000d08800033ee566cc2c982000006da0b25212c13e604e80001e9400006dc449317912f040ba4432185a37246428cdfa3d2000064c8ba98f0612d27ab8000000000007f5000006aa25c67b00aec054f00004ee0000177700000001062800038ac00000001128383a00004c888ad134c5d2c9b5828500000000b76982800000000e6680000f3a2120926010b0ef81b1491f000000000000ada0000000047ac94d9d84214c000090b1ac200008e8c0120000000053f0496876300000001144800000004128000057128dc5edc848989c1ae256f91b017320f167664b6b8fd52be444ec0000000000000010caa2ed00006e140558973000081b80000e5925f63830b25916610fc7254a8d223f191e0000000000030b85de4da204f82c2a414c00022d41d06261d098031514d2099c000000015563f087b2998f413a2ee8000164f00000ae1062225a00000000000000033960000b3380003fbc8c24fed201400007e700000671000000000000000410284dcf3b077200000a98000057312460000000000000005699148015e2e7200009008da742a2000000012c800007f5c000000029c04a04000000000000000d2495de1dac00000001f5d07a25334ff28000260e79fc484934512c053f4883890d378000010a18000113e000000021562d94000022a05e9000000003879abd3fba31f899a81082fee132505380001260000026a000035746acc29d10d61b36000048a06ee38146390bab1e97368a76f09098c8017e60ecd000887d06440000fc39c6c0cae7dc51a5090730046f2074e856505ee5a082848e9324a8597c53c000000007ba0e97002f0ffe741c8ef849e00006718a2c8513205a69a4fd08cbe34963140000000033f676509048f1e3d3618e86ef0000000015486ae000034844b9800023010d067ca800000000000000000006370000000000021af000075b4d2a98eb3f763100eeb00003d6c02600001a82000000000000000000010d019c87b3066a00009b4947b00
  | 70 => 0x7b047f1000043cc0000f3883fb2f84544c000029609d4452c000169c00001bb410481c81e2e1310ebd800000005f400001337000085a45d89daa24c6702088c059812de00000000a7200002a24000064c245e79046aa08aa25386d54c2480000ba035bcf94042500000000000101f00004e580001ee905bc000053d119e0d9a73d4e14800000008c6ca110000000029d800000a200003c409b8068c00005db493588052e08000024a8b78000035b4fbc00001eb68a703589b5c2f1a12f4873873d0f2a1be807c87bd0000000000000000e6e388419f98b32ca2000011200003cea8e4c9b116a000003994000190600002fd0e98956944a009151bd000000000000000098b423c00000000000448227e07d7905c25e854742310937014a23fc979932c342c25d1136862422340000901157e44f855fc000072e27a8155087500001ace000000015863eb226a4000000019fe7738000217c00006188000118000000000e9a0db636b200000000c452c922250bef10d8016800000001ab82e321b2c363877f43541bb0afd9a3b2b1c4968000055f142a5e28315a37c112645080001918000000007041d30406400000000000000042380000ed714d000005790000305e0000b330000000068b110e8000317000007af833d40e855c800018ca1b5a1cac2299b28409649a8fe4000033802d9c5fd90fc11b200000000eff00003f381eb8b0321e03e60c63800018f8172c4ac1e093848203ca36000000000000000000042620000000049200c6116c07b05c0470a36fcf2b233d446609d007e8f92085439200000000323a0000000186921a400000000587315658d4000000034c200008a6000000007e10f5c80181a4200000000000000000011e517b318e48b8803a0aca0aa20000a479b201a0675b0a9f9e9230121a740001630140868d490289332552898461c803a38788170d44819a0d848e20120979b17f001f86629354008a7b18e0a9d5214b66eb06f3154f1fe4000000008a9343000007d202bb00007a14726800000000000ca2800039c00000cec0cad00000000000121f01c800007e62199000000000000000088000005688000031a44dcef50d5b254e677c000175c000000008ab0c0221c80000caf8c6a00002464b979e7400000000f21800004163ee800000000c0e71a0137000000004004d8d1b0200008e58000000033b86028000000000004680e190c2d038a43086f41eea312e00007e19e0f00000000000000000000bd50f48000236437d0c13014e13dc4694bfc86b700006ca4c8b08690c5e3a1400005b1000000003bd000000007fe00e100002cd81d04b9f99f000000000a1d0000000003e800000003de6640c000000020560000f76000000008d306e122a004f46a88f3d2336250463185f8000019a2000006a1662144e4bb51
  | 71 => 0x1c78000000057bc00000001e6600000000a750056000015b00000d0e0000463228d34c00000a2b119b000072706d8177e033a47685639d2c21dc77785dc13cb3204633102180002740138473613d80000000044c06c900008484000132f00000000710000000000000f2a0000000000000001ecf2ddc4c70e6593d000000000427800000000000000042831a6658c00000000cee00000000000000000011dd8f5300000000360800000000000679215c1708080847a998a416235f83da17a936e4481c000234e07b028dc0c706ab000000000002003000002f8df9209b00000000652104804520000b1b958b00000000add8000011441b064d826c0ade0b9d0e51f0d29965f0c78b18b02c583224b7b00003ffa0000000000028a64b2c52a18f10432000000005fc37f427dcff012961c4e4dbc1a7800000001bc8cbc0baa420a0000000218e16c40000000000031081048f370b6c35828ea00000b8921d26f3c9db1e90000038a4000000035d68e440000000000036f06d30349000000007bb04ff1f128b0cca69da11306000000000000000000000017bb0ff654cc74f8000000000010788057054409ec15ca1a5444043ac91290de00003058faf825b2f6434a4b5407ed3556577c72100000000831d0c112830000392861108c01fb2000020d8000376a743417600002d6e3e64000000000000000a2a1c473b465c700e812cd00002adc0000ffc00000000000000000000000d5c860a2d588e38882000000000000cf68c092de6535d05980de27600000000000044ba0000e4719240000858c0000000000058c90ad85e80000000000000002aea3f14e3c9cb008021400e18146f0000326080d213633a80000000094e2128378453e1a76068613380000000000047d80000000000023c8ab1875042de281c672822e00001d209a19088000000001a981180a681000000000000006dd8e38000000004dcc00020e529ba86e0c4900002df400004a899fa03325e04994a0a023660000000000000000000000000000000000000000010d4000105d87b2000005ec00000003e2c0918bd894f3392400000001cbe0e8600000000000000000000000000000022c4000005400000e20e4d155f184600011538b5027a6055005793ee435a6a64be5834217c200005b50a0d189c3b985b9800000000000000000033e400000000000382600008998c1c00003be000000000e687490000000000003574193177c47ae000000000001a3200006e4000031c448d4000137600000000cb719ca117a0000000160c3c8c0000000000000000000000000000002170a0300000ab874306a20000315a00000000000000000000000000246000000000000000000000000000047462a8224800010da00000001f6e030e214400000000000209c000076944f05c9c2da85990
  | 72 => 0x1c5e0b7400000000000463000023e219e2152000000001fda0000000000039083aa4eef80001ffa5a5c00000001c7a0000b7480000000000000010f13e5c00000000d232b1a8ad50f68000412a0b6442e80f308e063790f3a025000000000000b2f2da033ec41a16b220485eac0001ee7198400006a685dd045e000000b80000bd400006ff0000028a0000000178924e226645330000425c41e0000179c0000000070d8000000087ac00a000029b058800001a01000000000001dc200005d606a890e839d400009379c341c500000000000000000000ac088b73a2a32a4cf4849a000000000000bd6307e0000000102e313c6a90e31a36436c60d28d3600001d3c8888d7b9d6400000000aa680000000315c0000000000056dc0000da00000000000004d800002d6c00000000d02889c0759eb707b640780000000171e01a00000e553f4014fca4701d716fa1fc800017be000011080000000000000000000000404600011ce80000a6c8514b1a00001f280000000000000004f74faf000000006b2c8f3800029e837b03a019fe14da7ddcacb80000000349c0fc866c0000000106096162a884e6000016413cce0000f051af640a200000000000034210d4000126932600000ca8a14d230400000000000297a0b3c000172d00008e98000153103240000e6780001718000000006a03b60339062212c037ca05088b69f4b0000000069e8c92000066008eb00003b0e4b5117b82bc3fa608008ff8000175814d45b70000000000000000e070000000000022fc066000000000fe4000041f516f800023aa0000000075b3fda0000fb9a0c0306673c501c011146285a88000000004b2000095d03f33a420001037800013883e440f5800000007c6471308f40b0264b86b280000000072800005762ac03d482b70f4411aa2d60cc39cfe00008830000031b1cc480d8dad928a329c306c0001e8a3d7c00000000000000064d4f96a297415c816000000001b1a53000d0000000000000000000000001c8c29c80003b3c89e496a8000000032cc047850e0000000090014c70000000000000000000000000014ce00000000000000047ac350c13c8fbf2aca05c4f24991134560000ee48504000019f80000b850000453c000000006ca7b90af1000000006cb467e21343e34391831c0000359a23b4faa96e0251a891d1df0a1700000434b6680000000184800000001d02000000008c909a2030502200003e3609d4e8e0000116441bc000000009662b711db04e9000009a000120a834fe00000000000000000003d690f70000530400023e5127400005c500000ce800000000cb8368089c043b129e3b6800010328c623e7418f44dc89e3000008ecd81841727d64618a74800000008f5041890b91752374027380002dc80b18518000000004818a8d800000006400
  | 73 => 0x9a107a87aec70d06b9016e0a0c000000019980000000099e31e800000000c8200000000bdc00002b06079879ba1802616294cd4e0ae900000000c12173330080000000000000000000000000000000000000000038a465c0000000002d400000000ba1023800000000847002a00000001d9120422658747821d22e2000011c9e3b450c23944888000175e00000001fb32b74000000000004158000063d0000000041a8000000003ce00000000000000071400000000000012ace0d8ca6000077180000ef0135e1008b62800000000000000123a00000000182000000de0000000184347aa67c400000002e3a10cc4a509720e36000001b80000000463c4c31683153e2518b3b8668389600006e70000441a00000000691000017f90d612872f3e76d80000000000059c0000000000000a10c838a88394603280001b2415f286c4000079431120000000000000002bf8000000021760000b96000000000000870800029fc0ebc7de9cdc08c059ec000125f000087d0000000032080000000035224da336510ca3e629a0000000011540cf04ed0b078a3b00005fe8000000041f04fe11231bed0c80363040d004d280e5aec53b84194124167054d000017a858287d31bd10b9278e84f300000000000000000000f6a3b7c00011c60000000000000000264000000014b800000000e3a938627722aa118f00001a0424a90ef9d9a0af830c82aca3161b860000f6d000034440000000000008be00002ad87fa00002f9c0000000056400000000873000000011c49293000000000001cd21f6609f4c4a177035fc37640001c9b00007d445ca9c4e0ffa8f240000a9e451c754c0f294ec27c47a8107b881916c048b02ee1a02001a64bc19580000e960000000082c10a08504e81813b0a5e28d519112851ca62c98f5f9385457e64b0d3688e023c6163c5ed0be20000752cccb0000000083f404a223d37020000000000000001b5c41404d0000079383a2800042166afcab71ee5000036500001c7b00000000b94800000002e50a5c96b603e40000000120c000000000000000000000000000000000000007b214c2000000001a88000000000000001af4000076881c0a0730000000000021fc0b200b9812681783b7002e01880e77209a2be886f800016740000bbb202d17dc04bc000000014668e50fad01a4000000000000cd041f800000000e5a00147930ea8000020a002746570000000036c498493aa00005f211ae8000355c4af00000000000000000000000000000000000000000084290ac00210000196891080000000000000000001ca412085d58b172ca0000000000004420000062899b216e450f4000000028f4000070f8000230600001878000000000000001c4f428849c90b90000000000005d100001346000091a092400001c7509993f4
  | 74 => 0x9fa90310000569c0001dba29a664fc1ca9b800f08256c06b09cd000000000000000458000011e88de31f968c100000c42000000008080d78156064304de9faf000068285a6000030560000bb2800000000000a1900923ba018a8000154700008ce855507cf0000234400020cf1fe07c1873c8ef33f8e72240190fe10950844c0e4800000000000bd789fa27cc3decf6880001d62177c0000000000078148308f1d42ba000083a0dcc0000112000811bc2eea00000001f2944220000548000000008c9062d87d4000000000000000020800004b280002aee34700000000000083f890e800000005ca88c4878000007d4c0000ba544ce6cc07bd23650000000107a80002bc200000000000000000004510000000000009ce156d2942279c7e50b1944c8000100a9222422448540000000000007382d9800000000000000024b15f6000000000000000208800018f0148000000001bad0e8c5cc461300003e1279f00768f3103dc1c847a380001a768670d0b800008d84188d788000000019d518606ac46ae69143f1000015be3af43841aa100004e2c93380000000057ca64190e000083d033e0c7610864af80001dcf00000df882a02ed45ce1aa4000000000000001115800028c4000065800000b9c81382590000000087b8131000000000000000204136940000f8880001d18000000000002dba3704000000021ba0b306d08af30000047c542056d000042e08f287a00cc6000033100002daa424809b9f2531200000d690eee01f800001ff800000000000000000000000000000000000000000a8e01b600005a3c00022cf19d2000000000003888338cf1a12a230a63bbcb64823d319a000000000000000048c193800015fa8d011ac00002d827cb05d21fdc00000000000000000000000000000006000000d720ea8000000008b38ae4397a86880000000307a00000000000000044340000f7e0000355400022e81fd2608cbb00000000087e80000c0a0a1000004c99b7a04440ee4000000023720854308000000003f50ffb881600000000000117300000c0441080000000000019c00000000587c1f4a2041798000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x845e73194400422eb98ca200211b9c865100108dae43288008655539844004332a94c2200218d9516110010caaa6b08800866552584400432aa9cc3180211ddd5618c010caaa6b0c600843e76951300421e3b4a8980210f9d9544c010878ecaa2600861f6494d300430e324a69802187d91534c010c38c8a9a600862f649493004316324a4980218bd91524c010c58c8a92600843e74d94300421eba6ca180211b9cb650c0108dae5b28600843e74994300421eba4ca180211b9ca650c0108dae5328600847571594300421f3a0ca180210f5d0650c0108dce4328600846d72194300421ebacc8180210fdd5640c01087eed2a0600843d76950300421fbb2a8180210f5d9540c010c3cc9298600861d6494c300430f322a61802187591530c0108daeb310600862e549883004316aa4c4180219394e620c010c9aa7310600846f7558830043172a2c4180218b551620c010c9ca6b10600864d535883004237bb4a4180211b5da520c010c5cc9290600862d649483004237bb2a4180211b5d9520c010c5cc8a90600862d64548300431b2a4c2180218d552610c010caaa73086008666529843004332a94c2180218d951610c010c6aa8b08600865653584300432aa9ac21802199949610c010ccaa4b086008659654c030042cc3a26018021c6551300c010e92a4980600843e74d96200421eba6cb100210f5d6648801087eeab24400843f76952200421ebb4a9100210fdd9548801087aecaa4400861e6494e200430eb24a710021879915388010c3ac8a9c400862e6494a2004316b24a5100218b9915288010c5ac8a94400865553986200432aa9ac31002199549618801087ce9328400843d74994200422f39cca10021175ce650801087ce8328400843d74194200422f398ca10021175cc6508010c6aa9308400865553984200431aaa2c2100219554d6108010ccca4b08400847576d4f100438b2a2a788021c555153c4010e8aa729620087255454b10043a2a9aa5880211d5da5184010c72cb2a4200863965552100432cb2ca708021965955384010e32a8a9c200847976d4a1004334b2ca5080219a5955284010e54a8a9420087295454a10043a529aa508021d254d52840108f2ed28c200863765951100431bb2aa8880211d9db5344010aaaeb29a20086576594d100432bb2aa688021c59515344010e2aa8a9a20086676594910043a2a9ca48802199d955244010e4aa8a92200874553549100432aa9ec088021d454e4044010ea2a6a02200863b65951100431db2aa88802196d965344010cb6caa9a20087195454d100423d3b6a4880215a5d65244010cd6cb292200866b6554910043952a2a488021ca5515244010e94a6a922008749535491004334a96c288021d854b61440108f4ed28a20087515394510043b0a948288021d85494144010
  | 1 => 0x320423d380ca190211bdc964944108d8e4b24a20843f7458a510421e3a2c528821179cf65904108bae7b2c820845d7598e410430f2a4c7208218755263904108beeab1c820861e5458e410430eaa2c72082117dda53904108baed29c820845f7654e410422ebb2a7208219398e5290410c9ac7294820864e6354a4104326b1aa5208219a54a6090410c72a8b0482086695258241043172a6c4a08218b5536250410c9ca7b12820864d53d8941043172a0c4a08218b5506250410c9ca6312820864d5318941042373b4a4a08211b1da52504108dceca92820846c76549410432ca9cc0208219a54a6010410c74a8b008208659535804104334a92c0208210f9d3658c41087ae9b2c620843d75992310421fbaac9188210fdda548c41087aed2a4620843f76552310421ebb2a91882187992538c410c3ac929c620861e6454e310430eb22a7188218b992528c410c5ac9294620862e6454a3104316b22a5188219a54a608c410cb2a6b04620866952582310431caa4c0188219a54a600c410c72a8b00620865a535803104334a92c0188219a54a60884108f6eab04420866952582210421f3b4a8908210f1da544841087cecaa2420843c76551210430fb24a690821871925348410c3ec8a9a420861c6454d2104317b24a4908218b1925248410c5ec8a92420862c64549210421f3a6ca108210f5d365084108bce7b28420845d73d94210423cb82ca108210f5d6640841087eeab20420843f76950210421ebb4a8108210fdd9540841087aecaa0420845d7598c210430f2a4c6108218755263084108beeab18420861e5458c210430eaa2c61082117dda53084108baed298420861e6494c210430eb24a61082117dd953084108baeca98420861e6454c210430eb22a6108218b9925208410c5ac9290420864e639482104326b1ca4108218b9915208410c5ac8a90420864e635482104326b1aa410821995952108410b48e890842087255448421043a2a9a42108218e9526008410c72a9300420865a53980210432ca9cc0108219a54a6008410c74a8b00420863954580210432d29ac0108219654d6008410cd4a4b00420866952580210422fb9ac928021171cd649401087ee8b1ca00843c7458e5004237396cb200211b5cb65900108daeb314800862e5498a4004316aa4c5200219394e6290010c9aa7314800846f7558a40043172a2c5200218b5516290010c9ca6b14800864d5358a4004237bb4a5200211b5da52900108deeca94800846d7654a400432aa9cc3200218d5516190010caaa6b0c800861e54d8d400430eaa6c6a0021879506350010c3aa831a800845e7694d400422e3b4a6a0021179d953500108b8eca9a800864f63949400432631ca4a002193d8d5250010c98c6a92800845e73994400422eb9cca200211b9ca65100108dae532880
  | 2 => 0xc3a90214b9d35294810a5ae9a94a40854e73d4a52042a6b9ea5290210fdd16394810878e8b1ca40854e73d5252042a6b9ea929021539cc5494810a9ae62a4a40852e74d4e5204296ba6a729021c39525394810e1aa929ca40870e5454e5204386aa2a7290214b9d05394810a5ae829ca40852f7458e52042963a2c7290214b9d06194810a5ae830ca40854e7318652042a6b98c3290214b9d26094810a5ae9304a40852e74d895204296ba6c4a9021539cf6254810a9ae7b12a40843f74585520421e3a2c2a90211b9db5454810a9ce7aa2a40854d73d5152042373b0a8a9021539cc5454810a9ae62a2a40846e76d4d52042973a6a6a90214b5d35354810e1ca929aa40870d5494d52043872a2a6a9021c355153548108dcec29aa40852e7414d5204296ba0a6a9021591c56454810a5ee8b1aa40852c7458d52042b238ac6a90215a1c16354810ad6e0a1aa4085687050d52042973a0c2a90214b5d06154810a9ce630aa40854d7318552042973a4c0a90214b5d26054810a5ce8082a40852d7404152042a739820a9021535cc105481087aed2a0a40843f76550520430f2a4c629021875526314810c3ca8b18a40861d5458c520422ebb4a629021879925314810c3ac9298a40845f7654c520430f322a629021875915314810c5ca9310a40862d54988520432729cc4290219354e62148108deeca90a40862e645485204316b22a4290219398d5214810c9ac6a90a40861e6498c520430eb24c629021879916314810c3ac8b18a40862e649885204316b24c4290219398e6214810c9ac7310a40863564984520432ab1cc2290218e9926014810c72c9300a40865a63980520432cb1cc029021179ce65d08108bae732e840845e73197420422eb98cba1021179ce65908108bae732c840845e73196420422eb98cb210211e9c065908108bce732a840845d73995420422f398caa1021175cc6550810c6aa9b0a840865553d854204332a96c2a10211d5d46150810caaa630a840845e73994420422eb9cca21021179cc65108108bae6328840847671194420423d380ca210210f9d265cc81087ae932e640843e74197320421eba0cb990211d9c465cc81087ce932c640843d74996320421f3a0cb190210f5d0658c8108f4e032c640843e74995320421eba4ca990210fdd1654c810878e8b2a640843e74195320421eba0ca990210f5d7644c81087aea322640843e76951320421e3b4a8990210f9d9544c810878ecaa2640861f6494d320430e324a69902187d91534c810c38c8a9a640862f649493204316324a4990218bd91524c810c58c8a92640865553d853204332a96c2990211d5d4614c810caaa630a640865953d813204334a96c0990211e5d4604c810cd2a4302640843e74994320421eba4ca190210f9d0650c81087ae8328640847671194
  | 3 => 0xc44248110ad0ea99240885a8744c920442e8b98c2902213c1d93148110f826498a408866865c85204433432a42902216a1d12148110c9cc7316a80864d6398b540432731ac5aa0219358d62d5010caac730ea80866962983540428f39ea92a021475cf5495010a5ce5aa4a80852d72d52540428f39cc32a021475ce6195010a5ce5304a80852d72982540428f39ec8aa021475cf6455010a5ce5b22a80852d72d915404237b92c2aa0211b1c961550108bee6b02a80845c73581540429c382c6aa0214d1c56255010a3ce730aa80851d739855404297394c0aa0214b5ca605501087eecaa0a80861d5498c540430eaa2c62a0218b5526215010c5aa8b10a80861e6498c540430f322c62a0218b9926215010c9cc7310a80864d639885404317322c42a0219398d6215010c9ac6b10a808655639845404332b14c22a0219658e6015010cd2c5300a80862e5498b5304316aa4c5a98218b95162d4c10c5aa8b16a60862e6498b5304316b24c5a98218b99162d4c10c5ac8b16a60866962983530428f3a6a729821475d35394c10a9ce5a9ca60854d72d4e530421fba2c5298210f1d16294c10a9ce5aa4a60854d72d5253042a7390a929821535c85494c10a3ee8b14a60851c7458a530428f3a4c329821475d26194c10a3ce8304a60851d7418253042a7390c129821535c86094c10a3ce9b1aa60851d74d8d53042a7396c6a9821535cb6354c1087ee8b02a60843c74581530422f3b6a8a9821539cb5454c10a9ae5aa2a60845e7615153042a7390a8a9821535c85454c10ab0e0b22a60851f74589530428e3a2c4a9821551c56254c10ab0e0b12a60851e74985530428eba4c2a9821479d06054c10a3ae8302a60854e7218153042a6b90c0a9821479d01054c10a3ae8082a60843d76950530421fbb2a829821879526314c10c3aa9318a60845f7654c530430f322a629821875915314c10c5ca9310a60862d549885304326a9cc4298218b9516214c10c5aa8b10a60864d53588530430f324c629821875926314c10c5cc9310a60862d64988530432731cc4298218b9916214c10c5ac8b10a60864e63588530431b324c2298218d5926114c10cccc5308a60866562984530431cb24c0298219a58a6014c108dce532e860846d729974304237390cba18211b5c865d0c108dce532c860846d729964304237390cb218211b5c86590c108ece232c860846e729954304236b94caa18211b9c86550c108dae432a860863954d81430432ca9ec0a18211e5d46050c108dce5328860846d729944304237390ca218211b5c86510c108ece2328860847a70194430430f2a4c7a90218755263d4810c3ca8b1ea40861d5458f520430f324a7a90218759253d4810c3cc8a9ea40861d6454f520430f324c7a90218759263d4810c3cc8b1ea40861d6458f520432ab1c
  | 4 => 0x5ce9a92410846e7614920842d53a6c4904216a9d35248210bc2e3a92410847a7614920842753b0a4904215a9d74248210ad0ea99241085a8744c920842f1b8a64904216a1d12148210dc0c290a410846f765482084370b0a401042187d906355110c9ec7b12a88864c63d895444317b20c4aa22193d8c6255110c98c6312a88866462d85544432c31ec0aa2210fdd95415110a38e6aa0a88852c72550544422f39cc22a221175ce61151108dce5300a88846d72980544430e326c6a9a218bd936254d10c58c9b12a68862f641895344316320c4a9a2193d8c6254d10cc8c5b0aa68863864d815344334316c0a9a2117dd95314d10a38e8a98a68854c7254c534421fba2c429a210f1d16214d1087ce9308a68843d74984534421f3a0c029a210f5d06014d108dce4300a68846d721805344237396cba1a211b5cb65d0d108dce5b2c868846d72d96434423a3aac321a211bdc96550d108d8e4b2a868847b705954344237b92ca21a211b1c96510d108dce4328868846d72194434423a3aac221a218d1516110d10ca8a6b08868847875580434432c29ac021a2187d936354910c38c9b1aa48861f6418d524430e320c6a92218b1936254910c98c7b12a48863464d85524432a31ec2a92219618f60549108deeca90a48852c7454852442a639aa4292210fdd16314910878e8b18a48843e74184524421eba0c229221179cc61149108bae6308a48843e74980524421eba4c029221179cf65d09108bae7b2e848845e73d96424422eb9ecb212211e1d560909108bee6b2a848845c73595424423bb8acaa122117dcd65109108b8e6b28848845e73194424422eb98ca212211d1d56110910cc8a4b08848847875580424431c2a2c0212219a149601091087ce9b2e648843d74d97324423a3aac3992210f9d3658c91087ae9b2c648847875582324421f3a4ca992210f5d2654c91087ee8b2a648843c74595324423bb8aca992211edc1654c91087ee8b28648843c74594324421f3a0ca192210f5d0650c9108e8eab08648866452584324423c3aac0192219614d600c9109d2e5306828862f5418941443162a0c4a0a219614d60cc5109d2e4302628859674d8d314423b3b0a698a21559d7434c510ca8cba1a62886546510d31442e8b808698a21551d5324c510b28e899262885e1721813144316326a490a218b19052485109aae730e808845f73595404422e39acaa02211bdc965501108d8e4b2a808861f5418d404430e2a0c6a0221551d531cc11087ee8b2a608843c745953044237b92ca982211b1c9654c110c38c9a9a608861c6414d30442aa3aa6298221a5191314c110cc8a4b0e408843f74595204421e3a2ca9022117dcd65481108b8e6b2a40884d57318520442d53a6c4902211e9d85248110ad4eba12408866865d0920443343288490221785
  | 5 => 0x851e73d5042c4332292c2216210f9d365ccb1087ae9b2e658843e7499732c421eba4cb996210f9d0658cb1087ae832c658843e7499532c421eba4ca996210fdd1654cb10878e8b2a658861c6494d32c430e322a6996210f9d0650cb1087ae8328658851e73d5341c4296392a920e21879526390710c3aa931c838851e73d5141c421f3b0a8a0e218bd506250710c58a8312838843f7655041c4296392a820e21479d353cc710c3cc929c638861e6454e31c431ab2cc918e218d595648c710a3ce9a9a638845e7614d31c42cb3a6c698e21659d3534c710ba2e1a9a63884767614d31c426b3b0a698e21559d7434c710aa8ea9926388594744c931c42e9b826498e2117dd9530c710da262b00638852c7454a21c4316326a490e211b9d85248710c58c8292438846f7654821c42963a2a410e219a9496008710cd2a4b00438852c7255340c426ab9cc3a06214b1c95450310c3ca831a818861d5418d40c430e324a69862187191534c310d28c898a61885d0704c530c42cc3a26018621b4585300c310a58e8a96418852c7454920c426ab98c290621995486148310a5ce5aa4a90852e72d91548430fb20c6aa4210fdd95415210a38e6aa0a90867161980548421fba2c529c210f1d16294e10c38c9b1aa70845f7654c538428e3a2a629c21871cd6414e10c5cc9310a70862d649885384317322c429c218b5916214e10c6cc8b08a708635645845384333312c229c21995896114e108dce532e870846d72997438428e39aa9a1c21475d053d0e108dce432c870846d721964384297396a921c211b9ca6550e108dae532a870843e76951438428e39aa8a1c211b9c86510e108dae4328870843d76d504384297396a821c219614d6010e10a5ce9a94a50852e74d895284237bb2a4294210fdd16314a10878e8b18a50845e73d96428422eb9ecb21421471cd5490a10c72a9304850845f73595428422e39acaa1421179cc6510a108bae6328850851c73550428421f3a0cb994210f5d065cca1087ce9b2c650843d74d96328421f3a4cb194210f5d2658ca1087ce932a650843d74995328421fba2ca994210f1d1654ca10c58c9292650862c64549328421f3a0ca194210f5d0650ca10a38e6aa683084e972983418428e39aa8a0c218b9506250610c5aa8312830851c7454f318428e3a2a698c219654c604c6109d2e4302630862c649492184316322a490c21691d12108610dc242b00430852e72d53408428e39aa9204218b9526290210c5aa9314810852e72d51408421f3b0a8a042187d506350210c38a831a810843f76550408428e39aa820421471d1538c210c38c9a9a610845e7614d308430e320a69842117dd9530c210a38e8a98610865653584308432aa9ac2184214b9d352c8210c5cc9294410862e6454a208431cb2cc9104218e5956488210a
  | 6 => 0x308237394cba18411d9c465d0c208eae232e861046e72196430823b388cb218411d5c46590c20a5ce5aa4861051d73152430829ab88a921841471d15390c208dce532a861047a70995430821fba2caa18411d9c46550c208eae232a861043e769514308237390ca218411d9c46510c208eae2328861047a70194430821ebb6a8218414b9cb5410c2087aec2a0861051d73150430829ab88a821841179cf65908208bae7b2c841063954982420821f3a6cb190410f5d3658c820cb2a7304641062c64949320823bbb2a2288418d5915114420caac6a88a21045e73d96410822eb9ecb208419558e5190420caac6a8c821045e73195410822eb98caa08418b9506250420c5aa831282104e9701894108332314a2a0841471d153cc42087ce9b2c621043d74d96310831ab24a3188418d591518c42087ee8b2a621043c74595310821f3a0ca988410f5d0654c420a38e8a9a621046d75d89310832ca98c0988418b1925248420c6ac9288421065563944210831ab22a2108419558d5108420ce2a3300421052e72d53400828eb98a9a00414d5c454d0020c5ca9314801062d5498a4008297396a8a00414e9c3545002087cec2a2801051d73151400829ab88a8a004187d506350020c38a831a801045e73194400822eb98ca200410fdd954100208deeab10801043f74597300821e3a2cb980410f9d3658c02087ae9b2c601051c7454e3008237baac5180410f9d3650c02087ae9b28601043e74194300821eba0ca1804187592530c020a38e8a98601061d6454c3008326a9cc4180419594d610c020caaa6b08601054d7315320082b2b88a9900414b1d153c80208daed294401062e6494a200823cbb4a5100411b9d85448020a9ae62a240105657115120082373b6a6900414b1d15348020a5ce928240105697590120083942a28090041721cd4048020ad2ea18240105a9740c120083a4a986090041785c43048020b52e9b12401056b7550920082b4bae6490041d85472148020b56e890a401051e73d5254c428f39ec8aa6218bd90625531087eecaa0a98852c7255054c433930ac02a621479d35394f10a3ce9b1aa78845f7654c53c421fba2c429e210f1d16214f108dce5b2c878846d72d9643c4296392a921e218d5526190f108dee4b2a878846c7259543c4237390ca21e211b5c86510f10a58e4aa0878843f7458e52c421e3a2c7296218b1936254b108deeca90a58852c7454852c4316392c829621879926314b10c3ac9318a58861e6458c52c430eb22c6296218e9916014b10c72c8b00a58865a6358052c432cb1ac029621179ce65d0b108bae732e858852c7255342c4296ba0a5a1621179cc6590b108bae632c858851e73d5242c422f39ccaa1621175ce6550b1087ced2a2858852c7255142c422f398ca21621175cc6510b1087aedaa0858
  | 7 => 0x8992418b194644c920d18c9a9a649046e7614d3248346320a699241aa193604c920d56c830264906a86418132482753a8c0992419a9d4604c9209d2e2302649045f73593514822e39ac9a8a410fdd163d4520878e8b1ea29047776544514829a3a2a228a41551cd5114520c5ee4b20a29062c72590514831a38ac828a41879926314520c3ac9318a29061e6458c514830eb22c628a41951c56314520c5ac9a10a29056571108514831d322c028a418e5916014520cb4c6b00a29065963580514828e39aa9a0a414d1c554d0520a6ae828e829072742147414822f398cb20a41175cc6590520c3ea931c829061c5498e41483473188520a41aa109609052087ced2a2829051c73551414829a38aa8a0a413a9c36250520c5ca8312829062d5418941482573b684a0a418b19742505208bee6b28829045c73594414822f398ca20a41175cc651052087aedaa08290665621444148392210a220a41aa1096010520ce0a2b00829051c7454f31482aa38aa798a413a1c162cc520b18e8996629055573147314821f3a0cb18a410f5d0658c520c3cc9a9c629061e6414e314822f3b4a698a41471d1534c520aa8e2a9a629064c654c931482c63a26498a410fdd1650c520878e8b28629043e74194314821eba0ca18a41175db530c520958e8b10629066562144314821f3a4cb90a410f5d265c852095ce932e42904ea7099321482373aec790a412b1d163c85209d0e0b1e42904ae7498321482b53a8c190a418d1935148520c68c828a42904ae749912148275384c890a412b1d163485209d0e0b1a429056675d852148352326a290a418b1905148520d48c828a42905667614521483333b0a290a41c99d05148520e4ae828a4290727641452148333320a290a41991905148520e48c828a42906246414521483a3398a290a41d15cc5148520ec2e028a42906a864d812148355b20c090a4117dcd65501208b8e6b2a809061f5418d404830e2a0c6a0241a318c4250120b30e6a0080904ac7458b304821fba2ca982410f1d1654c120c38c9a9a609061c6414d30482cc3a26018241b4585300c120b50e899640906e161c8720482d43a243902412b9d36388120d54c9a84409045e73986540822eb9cc32a0410fdd95415020c3aa8b18a81063554584540830f322c62a0419358e6215020cacc7308a81065563984540831b322c22a0419598d6115020caac6b08a81066662584540832cb1cc02a0419c586601502087ce9306a61043d74983530821f3a4c3298410f5d26194c20c3ae6322a61043f74589530821e3a2c4a984117dd95314c20c3ac8a98a61065553584530830eb24c6298418b9926214c20c5ac9310a61063664984530831ab24c2298419998a6114c20c6cc8b08a61063564584530832b31ac229841999896114c20c72c9300a610671619805
  | 8 => 0xa544ca20878ecaa2651043e74d8d518821eba6c6a8c410f5da541462087eecaa0a31061e5498c518830eaa4c628c41879516314620c3aa8b18a31047776544518832ab1aa228c41179cf65906208bae7b2c831061e5498e418830eaa4c720c41879516390620c3aa8b1c83106395458241883172a6c4a0c418b9506250620c5aa8312831063a54580418821f3a4cb98c410f5d265cc62087ce9b2c631043d74d96318821f3a4cb18c410f5d2658c62087aeb324631043f75592318821fbb4a918c410f5da548c62087eecaa4631043d76552318821f3a0ca98c410f5d0654c620c5ca9b12631062e54189318821f3a4ca18c410f5d2650c620c72a9300631063954580318821ebaec890c410f5d4644862087ced2a2431043c76551218821ebb4a810c410fdd95408620c3ca9318431061d5498c218830f2a2c610c41875516308620e4aa8908431063a54580218831caa2c010c418b9526290220c5aa9314811062e5458a408830f2a6c6a0441875536350220c3ca831a811061d5418d40883172a4c4204418b9516210220b30e6a00811062e5498a30883172a2c5184410f9da544c220878ecaa2611043d75990308821fbaac8184410f5da540c22087eecaa0611062e549883088316aa4c4184418b951620c220c5aa8b10611064d53588308831b2a4c2184418d552610c220c6ca8b08611063554584308832b29ac2184419554d610c220b30e89806110719544c03088368b0a60184418b59654c8220c5acaaa6411052e74d4f208831cb2ca9904418e59554c82208bce730ca89045d73986544830fb20c6aa24195d8f6155120ca8c7b0aa89063764185544832bb18c2aa2419518c6155120ccec430aa89043f76550544828e39aa82a2414d1c5541512087ee8b14a69043c7458a534821f3a4c329a410f5d26194d20c38c9b1aa69063764d85534831a326c2a9a418dd906154d20c68c830aa690657631855348333b10c2a9a419c1876054d208beeca98a69051c7454c53482aa38aa629a411d9c765d0d208eae3b2e869047671d96434823ab8ecb21a411b1d56290d209d0e0b14869047771595434823a38acaa1a411b9d76250d208f4ebb02869047771594434823a38aca21a411d9c46510d208eae2328869046c7558843483162a2c421a419314d6210d208f0eab0086906585358043482b238aa9a12413a9d660d0920cd4eb30684904e971983424828e39aa9212414d1c5549092087cec2a2849043f76550424828e39aa8212414d1c55410920b52e12a0849046f7655042482b238aa8212412bdd95410920b18e6aa084905a47155042482d5b82a8212413a1c16310920a5aea218849068d6310c42482d4b8086212413a9c2648c92095ce9304649061c64d4d324830e320a6992418b197644c9208dceb32264904ae749913248275384c
  | 9 => 0x8ecaa2601861f65551300c327b2ca498061a3192524c030c9ecaa92601868c64549300c386aa2a49806195d96514c030d28c928a601861c64545300c32bb2aa298061a5191514c030e2ca8a8a601871554545300c3a3292a298061d1549514c030e2ec8a8a601865664545300c32a322a298061c5191514c030c28c8a8a601875070545300c30e324a098061a6192404c030b92e5202601875151901300c26c3b28098061d4545404c030c76e9b2a601863874d95300c31db2ec8980618ed94644c030c76cb2a2601863b65551300c34c326c698061369da434c030cd6cb292601866b65549300c394aa2a49806166dd1324c030ce6cb28a601867365545300c398aa2a298061d494d514c030ec2a4a8a6018559758c5300c2ccba462980619698d60d5320a3ce7aa4a99045e7398654c822eb9cc32a641479cf645532087eecaa0a99066a6258054c831d322c1a9e419a98960d4f20a3ce9a9ca79043e7498653c821eba4c329e41479d36354f208beeca98a79047671d9643c823ab8ecb21e418b5526290f208ece232887904757119443c831d2a2c0216411bdd95410b20a5aea218859068d6310c42c82573a4c1196411b9d8534cb20cb4a6b00659045e73d9151c822eb9ec8a8e410f9d3635472087ae9b1aa3904777654451c822f39ccba0e41175ce65d07208bce7b2c839045d73d9641c83473188520e418b9506250720c5aa831283904ae76d0941c821f3a6cb98e410f5d365cc72087ce932e639043d7499731c82c63a26598e410f9d3658c72087ae9b2c63905547154d31c82c63a26498e413a5c8604c720958e8b1063904ac7458f21c82573a4c190e418bd946448720958e8b1a43904e87058d21c8316324a290e419c5456008720c3ca831a819061d5418d40c834631884a06412b1d162cc320c38c929a619061c6454d30c822f39cc32a441175ce6195220c3ac631ca91053a7018e548828f39cc32a441475ce6195220a5ee4b0ca91053a70186548828f398c12a441475cc6095220a6ce2304a91053571182548829c382c6aa4418758c6355220a3ee6b12a91051c73589548829bb8ac4aa4414d1c56255220a3ce730aa91051d73985548829d384c2aa4414bdc9615522087eecaa0a910669629805488317322c5a9c419a58a60d4e2087ce930ca71043d74986538821ebb4a829c410fdd95414e208beeca98a71063654984538831aaa4c229c418d9516114e20c6aa8b08a710655535845388317322c429c418b5916214e20c6cc9308a710635649845388332b14c229c418d9916114e20c6ac8b08a710656635845388332b12c229c411d9c46590e208eae232c871051c73551438831caa6c0a1c411d9c46510e208eae2328871051d73950438831d2a2c021c418e95160d0a20c72a9b02851043d75d91328821eba8c8994410f9d
  | 10 => 0x71443545410c333b12a2a0861991895150430c72a9b02821867151d81410c34c218c0a08611b9ca65104308dae5328821867151583310c21fbb4a9188610f5da548c43087eecaa4621843d76552310c317324a5188618b592528c430c5cc8a94621862d6454a310c31b322a3188618d591518c430c72a9300621866952980310c31caa2c0188619a549600c430ce4a2b00621843e74997210c21eba4cb908610f9d2658843087ae932c421843f74595210c21e3a2ca908610f9d0654843087ae832a421843d75d91210c21eba8c8908610f9da5448430878ed2a2421843e76551210c21e3b2a8908618bd925248430c58c9292421862f64549210c316322a49086193d8d5248430c6ec928a421863464945210c31bb22a2908618d1915148430caec6a8a421865463545210c334a96c0908619c547604843087ce9b28421843d74d94210c21f3a4ca108610f5d2650843087aeb320421843f75590210c21fbb4a8108610f5da540843087eecaa0421843d76550210c30f2a4c610861875526308430c3ca8b18421861d5458c210c317324a4108618b5925208430c9cc7290421864d63948210c317322a4108618b5915208430c9cc6a90421864d63548210c31b324a2108618d5925108430caac7288421863664544210c31ab22a2108619598d5108430caac6a88421863a54980210c31caa4c0108619a54a6008430ce2a3300421863a54580210c31caa2c0108619a9496008430cd2a4b00421867251580210c338a8ac0108618759743d0030e2e86a8e801861d5458e400c28eba88720061665c043900308daeb314801862e5498a400c316aa4c520061a310e62900308deeab14801862e5458a400c316aa2c5200611b5da52900308deeca94801866662946400c332b14a3200619598d5190030caac6a8c801871443546400c333312a320061995895190030c3ca9b1a801861d54d8d400c30f2a0c6a006187550635003093ceda1a801861f65d0d400c327b1ca4a00619318e5250030c9ec6a92801864c63549400c32bb1ca2a00619518e5150030caec6a8a801865463545400c38ba1aa2a0061879516310030a3aea21880185997010c400c32731aa4200619358d5210030cacc6a88801865563544400c38a21aa220061c355152cc030e2ca8a8e601871554547300c3a3292a398061d154951cc030cacc8a8e601865464547300c22ebb4a7180611e5da538c030e52a8a94601873154546300c3b0a92a3180610f9da544c030878ed2a2601843e76551300c21e3b2a8980618bd92524c030c58c9292601862f64549300c316322a4980618dd92514c030c68c928a601863764545300c31a322a29806187dd3654c030c38e9b2a601861f65d91300c22ebacc898061279d2644c030c3eca322601869970191300c24e3b4a89806187d96544c03093
  | 11 => 0xc2b3396a928861595cb5494430e28e6aa4a21856672152510c2b2b90a928861c55534394430ba2e021ca21853674d4a510c29aba6a528861c99525294430e4aa9294a2187265454a510c392aa2a5288614d9d05294430a6ae8294a21855673d92510c2b3b92c928861591c96494430a6ee8b14a2185347458a510c29b3a0c5288614d5d06294430aace6314a2185727018a510c29bba265288614d1d13294430a6ce8304a21853574182510c2b3390c128861595c86094430ab2e021aa21843e74189510c21eba0c4a88611d9db5454430acce5aa2a21856572d51510c38a39ca8a8861c51cd54544308ecec2a2a21856672151510c2b2b90a8a8861555d74354430e2ca9a1aa21871554d0d510c38b2a086a8861c55504354430ba2e021aa21847676d49510c29b3a6a4a88614d5d35254430e4ca9292a21872554949510c3a3a1ca4a8861d110e5254430e4ca8a92a21872554549510c3a3a1aa4a8861d110d52544308ecec292a21853674149510c29aba0a4a8861559cf6454430aa8e6b22a21856772591510c2b2392c8a88615c1c16454430aaae1a1aa2187154310d510c2b938086a88615c5c04354430e2ce821aa2187166410d510c38ab2086a8861d49c04354430aaae021aa2187517010d510c2a8b8086a88614ddd16254430a68e8b12a21855473589510c2b8382c4a88614d9d06254430a6ae8312a21855673189510c2b9380c4a8861559ce4254430aaae7212a21871443909510c2b938484a88615c5c24254430aaee6a12a21855473509510c38a21884a88614ddd13254430a68e8992a218572700c9510c2b8b8064a88614d9d06054430a6ae8302a21856672181510c2b2b90c0a88614d9d03054430a6ae8182a218566720c1510c2b2b9060a88610f5da541443087eecaa0a21862e54988510c316aa4c4288618b9516214430c5aa8b10a21846d76948510c317324a4288618b59252144308deeca90a21862e64548510c316b22a4288618d9526114430c6aa9308a21866652984510c332a94c2288611ddd95114430c6cc8a88a21863564544510c333312a2288619958951144308dce532e821846d72997410c28eba887a0861665c043d0430e2886a8e821846e72996410c236b94cb20861879526390430c3aa931c82184d97098e410c30f2a2c720861875516390430c9cc7294821864d6394a410c32731aa5208619358d5290430caac728c821865663546410c32ab1aa3208611bdc965504308d8e4b2a821846e72195410c236b90caa0861875536350430a3aea21a82185997010d410c236baec4a08618b9536250430c5aa9b12821846d75189410c3172a0c4a08618b5506250430d1886312821846e76949410c2363b4a4a08611b9d952504308d8eca92821866762945410c332314a2a086195d8d5150430ca8c6a8a8218
  | 12 => 0xaa061479ce6255030c38c7312a81853a70989540c28e39ac4aa0618718c6255030c38c7b0aa81851e73985540c28e39ac2aa0618718d6155030a5ee4b0aa81852c72585540c29c382c2aa0618718e6055030a5ce5302a81852d72981540c30e318c0aa0610fdd95415030c5aa9310a81862d54588540c31aaa4c22a0618d5516115030c5cc9310a81862e64588540c32731ac42a0618d9926115030cccc5308a81866562984540c31b322c22a0619598d6115030cccc4b08a81866562584540c334b14c02a0619c5866015030aaae3aa6861861d65953430c31caa2c121861875954310c30c74a8b00861869943580430c30eb2cc821861555c75410c308beecaa0861861e64550430c22fbaac021861a69916010c309b6eab00861865b75580430c34d2a2c021861a65516010c30c6ca930ea41863554987520c31b2a2c3a90618d55161d4830a5ce9a94a41852d74d4a520c2b338ea529061595c7529483087ee8b0ca41843c74586520c2b338ea929061595c75494830e18e6aa4a41856671152520c2b2b88a929061c35534394830b92e021ca41854e73d92520c2b5386c9290614bdd16194830a58e8b0ca41852e74186520c296ba0c329061539cc6194830ad4e030ca41852e74982520c296ba4c1290610f9d0615483087ae830aa41846e76d51520c2b338ea8a9061595c75454830e18e6aa2a41846e76151520c2b3388a8a9061595c45454830a9aeba1aa41870d54d0d520c386aa086a9061725c04354830a98e6b22a41870d4310d520c2b538086a90615a5c04354830a5ee8b0aa41852c74585520c2a639ac2a90615a1c16154830a5ce830aa41852d74185520c2a7398c2a90615a9c06154830a5ce9302a41852d74981520c2973a060a90614b5d0305483087aed2a0a41843f76550520c3172a4c4290618b55262148308deeca90a41862e64548520c316b22a4290618d9526114830c6aa9308a41866552984520c31b2a2c2290618d5516114830ccaa4b08a41847671997420c23ab8ccba10611d9c665908308eae332c841861d5498e420c30eaa2c721061475d44390830b32e021c841864d6394a420c31caa4c121061a610e6090830c72a8b04841866a52582420c23b388caa10611d5c46550830c3aa9b1a84184d97018d420c327b1aa4a10611d9c665108308eae3328841851d7510c420c30eb288621061665c04310830cd2a4b06641843e76951320c21e3b4a8990610f9d9544c830878ecaa2641862f64949320c316324a4990618e552600c830c72a8b00641866a52580320c3172a4c5a88618b55262d4430c5ca8b16a21862d5458b510c317324a5a88618b59252d4430c5cc8a96a21862d6454b510c29b3a6a3288614d5d35194430acce5a8ca21856572d46510c237b92c9288611b1c9649443087ee8b14a21843c7458a51
  | 13 => 0x61151308d8e4b08a89851d73188544c316b10c42a2614d9c46215130a6ae2310a89853970188544c28eb9cc22a2614bdc96115130a58e4b08a89851d73184544c297390c22a2614b5c86115130a72e0308a89863854983434c31daa0c0a1a610f9d261d493087ae930ea49843e76d51524c21f3b0a8a92618dd536154930c68a9b0aa49863754185524c31a2a0c2a92611bdd95214930ac8e2a90a49843f74584524c21e3a2c2292614b9cb54509308ece2328849847571194424c296b90a821261871526310930c38a8b18849863854980424c31c2a2c0212618e152608c930c70a8b04649843e75d91324c21f3a8c8992610f9db544c93087cec2a2649843e7498b514c21eba4c5a8a610f9db545453087cec2a2a29862f54d89514c3162a6c4a8a618bd506254530c58a8312a29847776544514c2b2392a228a610fdd16214530878e8b10a29861f5498e414c30e2a4c720a618715163905309b0e0b1c829846e72995414c236b94caa0a618bd536250530c58a9b12829862f54189414c3162a0c4a0a611b9c865105308dae4328829861c5498c414c30e2a2c620a618e1526010530c3cca2a6629861c54983314c21f3acc918a610f1d5648c53087aedaa4629843d76152314c31c2a6c098a618e150604c530a3ce92a2629855671951314c38a2a6c298a61c5153514c530e2ea828a629871854d81314c30e2a0c098a61c6150604c5309b4ea302629865a75181314c34d3a0c098a61a65d0604c530d36a8302629865a54181314c32c2a0c098a61a6150604c530c30a830262986ca72181314c364b90c098a6187152630c530e2ea8988629843f74597214c21e3a2cb90a610fdd16588530878e8b2c429861c5498e214c30e2a2c710a61361c1638853087ce9b2a429843d74d95214c21f3a4ca90a610f5d2654853087cebb22429843e75191214c21f3b6a890a610f1db544853087cec2a2429843c76151214c21fba2ca10a610f1d1650853087ce8328429843d74194214c21f3acc810a610f1d5640853087eedaa0429843d76d50214c21fbb0a810a610f5d85408530c3ea9318429861c5498c214c30faa2c610a61871516308530c9ac7a90429865563d44214c31daa4c010a618e1526008530c76a8b00429863854580214c335a92c010a619a1496008530ce6a2b00429861c5498f404c30e2a2c7a02618bd526290130c58a9314809862f5458a404c3162a2c520261871536350130c3ea831a809861c5418d404c30e2a2c3182619998a61d5030ccac530ea81865663587540c333312c3aa0619958961d5030a5ce5aa4a81852d72d52540c29b38ea92a0614d5c754950308dee4b0ca81846c72586540c28f39cc32a0614bdc96195030a58e4b0ca81852e72982540c296b94c12a0614b9cb6455030a5ae5b22a81853671d91540c29ab8ec8
  | 14 => 0xa731480a064f5358a405032629ac5202818758c5390140c3aec29c80a061c5398a405038629cc520281a3d4e6290140c58a731480a068c5398a405030629cc520281c314d6290140c38a6b0c80a06aa62d42405022fbb2a6298819354d6214c40caaa6b08a62045e73185521022eb98c2a90811bdd95214840c9ac6a90a42066552584521021fbaac9190811d9c4654c8408eae232a642061c6494d3210316324a4990818b191524c8408bce6312a22045d73189511023bbb2a2288819558d5114440ccac4a88a22062e54189411031b322a3188811bdc9654c4408d8e4b2a622046e721953110236b90ca988810f5d7644c440e2886a8a622065953181311034c218c0988819c544604c4408bce632a422045d731952110316324a4908818b1915248440c68c928a422045e73d94211022eb9eca108810f5d8439404087eeca9e802061e6354f401021ebb4a9200811e5da5490040c3ecbb1a802061f6518d401030eba8c6a00818718d5350040c38c7292802061c6354540102d4b96c8a008196d976350040cb6ca31a802069b6418d401029dbaa84a00810fdd95415330cb4c6b00a99843e7615143cc21fbb2a821e611bdd95214b30c76a9304859852d7215042cc30e2a2c6216611ddd951147308dee4b2a839846c7259541cc29b38ea8a0e618bd506250730c58a8312839851c7454b31cc28f3a4a398e61479d3654c730aace32a2639851c7454931cc2aa38aa498e61745c3514c730a3ce928a63984d67614531cc36898ac018e610fdd165c8730878e8b2e439843e74d9621cc21eba6cb10e610fdd16548730878e8b2a439843e74d9421cc21eba6ca10e618bd526290330c58a9314819843e7695140cc30f2a0c6a066187550635033087aedaa0819866962983548c297396a92a4614b9cb645523087eecaa0a91865963980548c297396a921c610f9da5450e3087aedaa0871852e72d50438c22ebb6a821c61275db5410e30b1ce5aa0871859a70d50438c2cd380a821c614b9d35294a3087ce830aa51843d74185528c237bb2a4294611ddc56550a308e8e2b2a851861e6510c428c34c21cc0214618b192524ca30c58c8a92651846f72592518c236392c928c610fdd16294630878e8b14a31847776544518c237394cba0c611b5ca65d06308dee4b2a831846c72595418c3172a0c4a0c618b5506250630d1886312831843e74997218c21eba4cb90c610fdd16548630878e8b2a431862c64949218c316322a490c61591c5524863087ce9b28431843d74d94218c297396a9a04618b9526290230c5aa9314811868c4398a408c297396a8a04610f9d85450230c38a831a811849e76d0d408c21fbb2a820461271d165cc230a5ce5b1ea89852d72d8f544c317b14c5aa2614b9cb61d5130a5ae5b0ea89851d73187544c21fbb2a82a2611bdc9
  | 15 => 0x1d6314e425030ebb0a721281c314c5290940c38a6b0c84a061c53982425038c29cc1212812e9d66090940c74eb30484a069b53982425031c29cc121281a614e6090940c30a730484a0718535824250387a9a84212818758c5310940a5ae429884a061e6514c425030ebb0a621281c39c85310940e1ae429884a070c53988425038629ca4212816a5c2521094095eeca9084a070f5354842502d238aa4212816adc15210940c38a6b0884a061c53980425030f320a7992818759053cc940974e1b2464a043e75192325030fb20a71928187190538c940c38c9a9a64a061f6414d325030e320a6992811d9c4650c9408eae232864a061e6414c325030eb20a6192819614e600c940cb0a6b0064a045e7398b515022eb9cc5a8a81179db53545408bcec29aa2a064f53d89515032629ec4a8a8193d4c6254540c98a6312a2a04777654451502b2392a228a810f5da4214540c3ac629e82a061e6514f415030ebb0a7a0a81c59c453d0540e2ae229e82a061c5398b415025d384c5a0a818714e60d054095ce530682a045e7598e415022e3aac720a81175db53905408baec29c82a064f53d89415032629ec4a0a8193d4c6250540c98a631282a066462d454150332310a2a0a819614f6050540cb0a630282a043e75d8d415030fb18a6a0a81879d85350540e18a7b1282a061c531894150386298c4a0a818b9d46250540c5aea31282a068f531894150316298c4a0a81a314c6250540c18a631282a043e76d494150316316a4a0a81c514f6150540e28a7a8a82a06a462d454150316310a2a0a81c5d4c5150540d48c428a82a071853d814150354316c0a0a818714c6050540e30a630282a06ab62181415030f320a798a818759053cc540a3ceba1e62a061e64d4e315030f320a718a8187590538c54087ceb32262a04ac72591315025c382c898a81559c7534c540c3cc829a62a061d6414d315028f3ae8698a8187197434c5408dce432862a046d72194315030f320a618a8187590530c540aaae229862a065853980315022fb9acb90a81171cd65c8540974e1b2642a061f6414f215030e320a790a8117dcd65885408b8e6b2c42a061e6414e215030eb20a710a81c314c42885408bce7b2a42a045d73d95215030fb26a690a81871935348540c3ec829a42a061c6414d215022fb9aca10a81171cd65085408bce632842a045d73194215022f3acc610a81171d563085408beeda9842a045d76d4c215030f326a610a818759353085408beec29842a045d7614c215030f320a610a81875905308540c5ac9a9042a04ad7610821503862988410a81695c44208540c6ac9a8842a072442144215032da9cc010a819614e6008540cb6a6b0042a0658535802150335a92c010a819a1496008540d5084b0042a06735158021502d439283a028193d4e6290140c98
  | 16 => 0x2a739ec929481535cf6494a40a5ae9b1ca52052f7458e52902b5380c7294814b5c24394a40e1ce621ca52070e6310e5290386b1887294814b5c04394a40a5ee8b0ca52052d7418652902a7398c329481535cc6194a40ccac230ca52056a7018652902a7398c129481535cc6094a40acce2304a52056571182529022f398c2a9481175cc6154a408dceda9aa52046e7614d52902b3388a6a9481595c45354a40a5aea21aa52070f5310d52902a7b9ac8a9481531cd6454a40acee2b22a520564715915290297ba2c6a94815adc14354a40ad0e0a1aa52070d4310d5290297ba2c2a94814b5d06154a40a9ce630aa52054d731855290332b08c2a94815a9c06154a408deeca90a52066a525824290334a96c0a14818b992528ca40c5ac9294652062f649493290316324a4994818b191524ca40cd4a4b00652046d76948519032731ca428c819358e52146408deeca90a32064e635485190326b1aa428c811ddd95114640caac6a88a32064e6394a4190326b1ca520c819398d5290640c9ac6a94832065563946419032ab1aa320c819a54a6090640cd2a4b04832046d75d894190236ba8c4a0c811b9da52506408d8eca92832046e729973190236b94cb98c81c310e52cc6408dce532c632046d729963190317324a518c818b592528c640c5cc8a94632062d6454a319031ab22a318c811b9c8654c6408dae432a632062f649493190316324a498c81c310e524c640e2886a8a632046e729943190236b94ca18c819a54a600c640cd2a4b00632062f649492190316324a490c818b1915248640ac8e2a92432045e73d94219022eb9eca10c818b9925208640c5ac9290432064e639482190326b1ca410c81595c65208640c5cc8a90432062d64548219032731aa410c819358d5208640cd2a5300432066a525802190334a92c010c818798d53d0240c5acb296812062e6394b4090316b2aa5a04819a59652d0240cd2caa96812058e72d9353502a7396c9a9a81535cb64d4d40a3ae9b16a6a065761987535028eba0c3a9a8117dd95314d40a9ce5b20a6a054d72d9053502ab38ec829a81555c76414d40a3ae9b10a6a051f74588535028eba0c429a81559c46214d40aaae2310a6a055970188535028eba6c229a81475d26114d40a3ae8308a6a054e7218453502a6b90c229a81955846114d40ab2e0308a6a061f73997435030f32ea7a1a818714e62d0d40974e131686a061c53587435030e29cc1a1a812b9ca60d0d40cb0a730486a065b53181435028f3aec6a1a81479d85350d40c3cec29a86a061c53189435030e29ec2a1a81a6d8c6050d408bce730ea4a045d73987525022f3b6a6a9281179d85354940caea7b0aa4a065453d85525032ba98c2a92819514c61549408deeca90a4a056471548525032c29cc1212819614d6090940878eab1c84a06
  | 17 => 0x8043ca9534254021e52a9a12a010f4a53d0950087a4a9e84a8043ca9504254021e52a8212a010f4a5310950087a4a9884a8043785c44254021e54a990aa010f2954c8550087a529e42a8043d254f2154021e62a910aa010f515388550086b5baa42a80436a1d12154021e54a890aa010f295448550087a529a42a8043d254d2154021ae6ea90aa010f315448550087a8a9a42a80435a9cb6454021ab6e6b22a010d587359150086b4392c8a80435c1c56454021a76e8b1aa010d387458d50086b4392c6a80435c1c56354021a74e831aa010d397418d50086b5390c6a80435c9c46354021ad4e521aa010d697290d50086b938c86a80435c5c64354021ad6e4a1aa010d687250d50086b4b8e84a8043ca5084254021ae4e2212a010d717110950087953a084a8043ca9904254021e52c8212a010f2a43109500879421884a8043d89c44254021ad2e2212a010f617110950086b0b8884a80434edd13254021a70e8992a010d72710c950086b8b8864a8043cad0b4154021ab4e720aa010d597390550086b539482a80435a5ca4154021e508520aa010d6b7250550086b439282a8043cad094154021ad4e420aa010d6972105500879421082a80434e9d23154021a72e918aa010d6a728c550086b4b9462a80435a9c83154021ad2e418aa010f51310c550086b53a642a80435a1d32154021a76e890aa010d38744855008795ba242a80435a9d12154021ad0e890aa010f287448550086943a242a8043d8dc52154021ec48290aa010f614148550087b118a42a8043d84c52154021a74e810aa010d397408550086ad39842a8043565cc215402187aed2a0a010c3f76550500870f2a4c628043875526314021c3ca8b18a010e1d5458c500862ebb4a628043879925314021c3ac9298a010c5f7654c500870f322a628043875915314021c74a9300a010e3954980500872d29cc0280439654e60140218f6eca80a010e3a64540500871cb22a0280439698d5014021cb2c6a80a010c5f7654c53d0257394c1a1e811bdd95214b4087eeab1885a047671d9732d023ab8ecb996812e9c3648cb40972e930465a061e6390a51d021ebb08528e818798c42947408eeeca88a3a043f7558f41d021fbb2a5a0e81479ce51d074095ce530683a05367194d41d0317b28c4a0e818b5d46250740c5ca631283a06aa7018941d0354b80c4a0e818b1895250740a3ce728a83a062c6294541d0237396cb98e811b5cb65cc740958e4b2263a04b87059131d025cba0c098e81a6d0c604c7408bce7b2c43a045d73d9621d022f39eca10e81175cf6508740b4ae221043a06a84258021d022fbb2a629c819554d6114e4093aeda98872059a70d4c43902cab88a621c81669c05310e40c3ac621ca5205667114e52902b2b88a729481c394e4394a40a5aea21ca52070c5310e529
  | 18 => 0x250421c9aa7b128210e2e541894108716aa0c4a08439394c6250421c9aa63128210cae76d094108717b2e84a0843179ce65104218bae73288210c5e73194410862eb98ca208439354e6210421c5ca8b108210e4d535884108696ba88420843695c4421042187ce9b2c6210c3d74d96310861ebacc9188430fdd5648c42187eed2a46210c3d76952310861fbb2a9188430f5d9548c421c3cc929c6210e1d6494e310870f322a71884387591538c421c9aa6b146210c3e74994310861eba4ca188430f9d0650c42187ae83286210e2d5498831086563a2c4188438b551620c421c9ca6b106210e55654c4310878aaa26218843b1589310c421e1aa8a9e4210c6d7694a210878aaa2a7108431d5da528842187ced2a24210c3c76951210861f3b2a8908430f1d95448421c3ec929a4210e1c6494d210870fb22a690843871915348421c5ee9b2a4210e2c74d952108717b2ec8908431b5d6644842195ce93224210e2f651912108752b88c8908432b1da5448421c5ecb2a24210cac765512108717b2aa89084393d965348421d18c929a4210e4f6554d2108746322a690843c35515348421c58c928a4210ea46490521086e2b9c8290843391d94148421b4ae918a4210ea4648c5210875232262908438ddd36548421c68e9b2a4210e3765d91210871bb28c8908438dd965448421c6ecaaa24210e576594d210872bb2aa690843c55515348421d48c9b124210ce67690921086d3ba264908438795263d4021c3aa931ea010e1e5458f500870eaa2c7a80438799253d4021c3ac929ea010e1e6454f500870eb22a7a80434e9d35094021a72e9a84a010d5a73d4250086acb9ea12804317dcd64940218b8e6b24a010c3f7458e500861e3a2c728043569cf5494021ab2e7aa4a010f287255250086ad398a928043565cc5494021a74e9a9ca010d3974d4e500878d2a4a728043c65525394021e34a8a9ca010f195454e500869d3a0a7280434e5d05394021e52a9a14a010de17110a50086b5baa43280436a1d12194021ae6ea90ca010d6a72d9250086adb9ac928043561cd6494021a76e8b1ca010d387458e500869d3a0c7280434e5d06394021ad4e431ca010d727118e500869dba265280434e1d13294021a74e830ca010d397418650086ad398c328043565cc6194021ab4e720ca010d597390650086b5b9283280435a1c94194021a74e918ca010d39748c6500869dba243280434e1d1219402187ce831aa010c3d7418d50086b2b8884a80434b1d121540218f4edaa2a010d5a73d5150086acb9ea8a8043ca1ca5454021e50e4aa2a010c7a7615150086ad398a8a8043565cc54540218f4eda9aa010d3a74d4d500869cba6a6a8043c69525354021e32a929aa010f1a5454d500878caa2a6a80431e9d85354021a74e829aa010d397414d50086b4bae84a
  | 19 => 0x4b06a610d1e74d4e530868eba6a729843569c35394c21ab2e1a9ca610c3f74582530861e3a2c129843569c35494c21ab2e1aa4a610f0c7255253086ad380a929843565c05494c21a9ce5b24a610d5671d92530868f3a4c329843475d26194c21a3ee8b04a610d1c74582530868f3a0c129843475d06094c21a9ce4304a610d5671182530868f3a6c6a9843475d36354c21ab4e1b1aa610d5970d8d530861f3a0c0a98430f5d06054c218bcedaa2a610d5a70d5153086acb86a8a9843c31c95454c218bcec2a2a610d5a7015153086acb80a8a9843531c96454c21a3ce930aa610d1d74985530868f3a042a9843475d02154c21a3ee8b02a610d1c7458153086a6392c0a9843551c56054c21a3ce8302a610d1d7418153086a7390c0a9843559c46054c2187aed2a0a610c3f76550530870f2a4c629843875526314c218beeca98a610e1e6454c530870eb22a6298438e9526014c21c72a9300a610e5953980530871d2a2c0298438e5516014c21cb2a6b00a610e1e6498c530870eb24c6298438b5926214c21c6ac9308a610e3a64980530871cb24c0298439698e6014c21c74c8b00a610e3964580530872d31ac0298439a9896014c21ce4c2b00a610c7a70997430863cb84cba18431e9c065d0c218f2e032e8610c7a70996430863cb84cb218431e9c06590c218f2e032c8610c6d7598a4308716aa4c5218438b5516290c21c9ca6b148610c7575986430871aaa4c3218438d5516190c21caca6b0c8610c7a70995430863cb84caa18431e9c06550c218f2e032a8610e2d54d894308726a9ec4a18431b5d46250c219cae23128610c7a70994430863cb84ca218431b9c86510c218ece23288610c7a70194430863cb80ca218430fdd16394821878e8b1ca410d6970d534208716b2ca9a1043c355253d0821c9acaa9e8410f0d5454f420871aaa2c3210438b5954210821e1aa6a108410e5553984420871b2a2c2210439554d6110821d4a84b088410e2d6599042086b4b86a8210431bdd95410821c5cc8aa08410f0d5454c4208716b2c8621043699c64310821a5aea2188410e2d6510c4208637baac221043a999161108219ceeab088410e677558442087532a2c221043a95516110821d8ca6b088410ec553584420875321ac221043a910d6110821caaa6b0c6410c3e76951320861e3b4a8990430f9d9544c821878ecaa26410e1f6494d320870e324a69904387d91534c821c38c8a9a6410e3554984320871aaa2c2190439594d610c821c5acba168210c5e73d96410862eb9ecb20843175d66390421c3ca931c8210e1d5498e410862fbaac720843879516390421c3aa8b1c8210c5f7694e410862ebb4a72084317dd953904218baeca9c8210e2d5458a4108696ba88520843a398c4290421b4ae22148210e2e54d894108716aa6c4a08439394f6
  | 20 => 0xb76540508870fb1cc7aa243479cf62d5121a3ae7b16a890d1e73d83544868eb9ec1aa2434b5c860d512187eecaa0a890c5f73580544862e39ac02a2438758c6315121a5ae4318a890d357118c544869d380c62a2434e5c06315121a5ae5300a890d1f73580544868e39ac02a243479cc6015121a3ae6300a890d2d72180544869ab88c02a2430f9d260d4d2187ae9306a690e2e6458a534871b322c329a430f9db5454d2187cec2a2a690e3b54d81534871c2a6c0a9a438ed506054d21c70a8302a690e2c64d89534871db26c0a9a438e1936054d21c76c8302a690e3864181534872db18c0a9a439ad886054d21ce6c2302a690e6972181534862fbb2a629a43561c15314d2187ee8b00a690c3c74580534863d386cba1a431e5c365d0d218dae5b2c8690c7571d964348637b92caa1a431edc16550d218f0e0b2a8690d1e73d51434863d380ca21a431e5c06510d21a3ae62a08690e2c5498843486363aac421a438b1516210d21c68a93088690c7475584434871a2a2c221a438d15261d0921c6ea830a8490e3454987324871a2a2c3992439514d61cc92187cebb226490c3e75191324861f3b6a8992430f1db544c92187cec2a26490c3c7615132487162a4c5a0a438b15162d0521c3ea931c8290e1c5498e414870faa2c720a43871516390521c58a9b128290e2f5418941487162a0c4a0a438b15262cc521c58a8b166290c3f76d52314861ebb6a918a430fdd8548c52187aec2a46290c3e74d95314861eba6ca98a430fdd1654c521878e8b2a6290e2c54d8931487162a0c498a438b151608852187ce931ea090c3d7498f504861f3b6a8a82430f9d85454121c3ea9b1aa090e1c54d8d504870faa0c6a82438715063541218f6eca80a090d5873540504861fba2c6282430f1d16314121cb4c7306a810e5963983540872d31ac1aa0439658d60d5021cd4c4b06a810d1e73d52540868eb9ea92a0434e9c35495021a72e1aa4a810c5f73582540862e39ac12a043479ce6195021a3ae730ca810d2e72982540868fb9ac12a043471cd6095021a3ce7b22a810d1d73d91540869d386c8aa0434e5c36455021a5ce531aa810d367198d5408696392c6aa0438b98c6255021c58c6312a810d1e73985540868eb9cc2aa0438b18a6155021c58c430aa810e2c62d815408697394c0aa04347dcd6055021a38e6b02a810d2c72581540869a38ac0aa0430fdd95415021c3aa9318a810e1d5458c540871caa4c02a0438e5516015021c3cc9318a810e1e6458c5408726b1cc42a0439558e6115021c74c9300a810e5a63980540872cb1cc02a0438e9916015021cb4c6b00a810e59635805408735312c02a0439c9856015021c74a9306a610e3954983530871d2a2c1a98438e55160d4c21c74c9306a610e3964983530871d322c1a98438e59160d4c21cd4c
  | 21 => 0x66ab80c2992638bd506250531c58a83128298e8c43189414c6d23928220a63651d132cc531d2cc9a8c6298c6f72593504c636392c9a82630fdd162d4131878e8b16a098c7b76540504c69c3a2a0282635a1c95014131c3ee6b20a098e1c73590504c71c382c828263875934314131ab2e0218a098e2e64988504c716b24c4282638b9916214131c5ac8b10a098c6e72982540c636b94c12a0630fdd95415031c5aa8b10a818e3954580540c717322c42a0639398d6215031ccac5308a818e6a62980540c734b14c02a0638e9916015031cb4c6b00a818e6a62580540c734b12c02a0639c9856015031c6aa930c8618c3e74982520c61eba4c1290638b5c864548318deeca90a418e2d64548520c734a92c029063479cf5490831a5ae42a48418d3970152420c6963a2a5210631e9c065508318f2e032a8418c3e76951420c61ebb6a821063479cf5410831a5ae42a08418d3970150420c70e324a699063479cf54d0431a5ae42a68218d3970153410c70f2a4c720863875526390431a3ce7aa28218d3671d51410c61f3b0a8a08634b5c85450431a72e02a28218e2f54189410c7162a0c4a08630fdd954104318beeab188218d4d72153310c6acb80a998863471d152cc4318baed29c6218e1e6494e310c63abb4a718863179d8544c431a9ae42a26218d5970151310c68e3a2a498863479d2514c431aaaeb20a6218f1454505310c6e23928298863655d3634c431aaeeaa1a6218d55758c9310c63dbb2a0280638e5915014031cd2c4a80a018c3f7655054c8733312c22a6430f9d260d4f2187ae9306a790c5f7654c53c8733312c229e438dd526190f218f4e132a8790c797099543c863d380ca21e431e5c06510f21a3ae62a08790e2c5458843c861f3b0a8a16430fdd95410b218bcec29a6590c5f7654c32c870faa4c720e4387152639072187ced2a28390e2e5418941c8716aa0c4a0e430f5db5410721a38e8a9e6390d1c7454d31c863dbb2a0286439558e61d5221a3ce7aa4a910d1e73d91548861fbb2a82a4439958a6115221a3ce9a9ca710d1e74d8d538861f3a0c0a9c430f5d06054e218beeca98a710e6562984538863db82caa1c431e1c16550e218f4e03288710c7970194438868f39ea9214430f9da5450a2187aedaa08510d1e73d504288636bb6a8214432b5db5410a21b1ce7aa08510da671d5042886d3388a8214434b9d44310a21b4ce22188510e1c6494d328870e322a6994439554c614ca21a3ce7aa68310e1e5498e418870eaa4c720c43a398c4290621a3ce7aa28310c3e7615141887162a0c4a0c432b9db425062187eecaa08310d1e74d4f318870f324a718c4387991538c621a3ce9a9a6310c5e7614d318862fbb2a618c432b1d1620c621958e8b2e4310c5f73592508862e39ac9284430fdd16394221878e8b1ca110c7
  | 22 => 0x8838b5d46250441c5ca63128220e2c6254941106cab9ec8a08834ddd54350441ccecbb128220e67651894110753b20c4a08831b9c863540418dae431aa020d2c72505501063dbb2a0280839658d5014041cd2c4a80a020e666258754cc697396a92a6631b9ca60953318dae5304a998d2e72d9154cc61fbb2a82a6639598d6115331c6ca8b088798c5f7655043cc6973a6a5296630f9d26094b3187ae9304a598c6f7654852cc63d386cb216631e5c36590b31c3aa931c8598e1d6510c42cc6c6b908621663279d261ccb31b2ce221e8398e2e5418941cc716aa0c4a0e63a310c62507318dce5b22a198c6d72d9150cc61f3a6c4a86630f5d362543318f6eca80a198c6e72982548c636b94c12a4638b5886295231a6ce2314a918d2e72186548c696b90c32a4634e9c06195231a72e030ca918d2e72982548c696b94c12a46347dcd6095231a6ce2304a918d2f7258d548c696392c6aa4634edc16355231a70e0b1aa918d3471589548c716b10c4aa4634b9ca6055231a5ae5302a918d3671981548c68fb9ac0aa4630fdd95415231caac7308a918e3654587438c71aaa6c2a1c630f9d26094a3187ae9304a518c3d76950528c61fbb2a8294631bdd95214a31c74a9300a518e3954980528c71d2a2c0294638e5516014a31cd2a4b00a518d2c72551428c71aaa6c2a14634b5ca5410a31c6ca8b088518c3d75d91328c61eba8c8994630f9da544ca31878ecaa26518e1e5498e418c70eaa4c720c63879516390631c5ca9b128318e2d54d89418c7172a0c4a0c638b5506250631c3ca93188318e1e5458c418c6d23928220c638759654cc631c3acaaa66318e3565953318c71ab2aa998c630f9d3625423187ae9b12a118c3d76950508c61fbb2a8284638b9526214231c5aa9310a118e2e54588508c716aa2c4284631edd95014231cd2c4a80a118c6e72982544c636b94c12a2638bd906255131cd6c5b02a898e6862d81544c71db20c0aa26396d8c6055131cd6c4302a898e6862181544c61fbb2a82a2634b1c95415131a70e0aa0a898d5870553434c66b3acc3a1a63959d661d0d319aae130e8698d2c72552434c69c382a921a630f9d85450d3187eecaa08698d2c72550434c69c382a821a63655c65410d318beecaa08698d5870550434c64fbb2a821a63631c95410d31b2ee2aa08698d9870550434c66a38ac421a631bdd95214931a58e8a90a498d6870548524c66a38ac7212631edc165109318f0e0b288498c7a70194424c63cb80ca21263871516310931c3aca2188498d8d7210c424c726b18a421263a510d6110931cc8a4b088498cd671993324c64f3a4c3992638b193524c931c58c82926498c9e74991324c66b38cc899263a3193524c931d18c82926498e9464d85324c74bb20c299263a5190614c9319acea30a6498e5675185324c
  | 23 => 0x10a41e1ca62908520da67114842906d4b80a4214838794d6110a41c3cc929e6520e1d6494f329070fb24a69948387192534ca41c38c8a9a6520e5653584329070eb2ca7a0c838759553d0641c3ca73168320e2e6254b419072ab2ca7a0c839559553d06418baed298a120c5f7654c509072729cc4284839354e6214241c9ca6b10a120e4d53588509063dbb2a0284839a58950142418dce5306a6a0c6d72983535062fbb2a629a83561c15314d41878eab1486a0cb675986435071b3acc321a83655c65310d4193eeca9886a0d977154c43506cc382a621a83639cf64d4941ad6e0a9ea4a0d687054f52506d338c87a9283c354c43d4941a9ce7b26a4a0d4d73d935250696ba6c7a9283c350c43d4941cd6c1306a4a0d2d741835250637bb2a4292834b5ca4314941a6ce3218a4a0e1d6310c5250696b9086292831b5da53149418deeca98a4a0d6b7054c52506b4382a629283c314e4314941b4ce3218a4a0d2e7510c52507872988629283539cf6414941a9ae7b20a4a0d6a70d9052506b4b86c8292834b5d36314941a5ee8b18a4a0d2d7418c52506b2b88c6292835a9c06314941ad2e0318a4a0d667190c52506b2b8c86292834b5da4314941a5ce3218a4a0f267190c525069338c8629283c95c64314941a5ae1218a4a0d2d7610c52507873988629283c398c4314941e1ac6218a4a0d2e7110c5250696b8086292834b5d36014941a5ae9300a4a0d2d7418052506a7398c029283535cc6014941acae2300a4a0e69601805250717b94cba12832d9c663d0941c5ccba9684a0e2e6314b425064f39cc3a12838b14a61d0941c58a4b0684a0e64529864250733a90c2a12834b9d76250941a5cec29284a0e2e761494250716318a4a1283a9d886150941c58a5b0284a0cb671d93325061f3a8c9992838bd9052cc941c58c829664a0e2e6414a3250716b20a5192838b193524c941c5ec829264a0e2c64149325063d380ca192831e5c0650c941c5cc829064a0e2d641483250732294c21928399149610c941c9cc7a9482a0e4d63d4a4150727318a520a839358c5290541d1cc7a9482a0e1e6314a4150716b10a520a83a398c5290541c5aec29482a0e2e6314a4150787318a520a838398c5290541e1ac629482a0e9663d464150716292c120a831b9ca63d41418dae531ea0a0c6e76d495050727b1ea4a82839318f52541418dcec292a0a0e4f631495050726318a4a82831edd95014141ab0e6a80a0a0c3d7690c5050637390c0a98831b5c86054c418beeca98a620e4d53588531072ca9ac0298831bdd95214841c9ac6a90a420e6952580521061fbaac9990831e9c0654c8418f2e032a6420e1c6494d321070e322a6990838b192524c84187aec214a220c3f7654b4110717312a5a08830f5da54904418eaed2a48220e2f65d894110717b28c4a0
  | 24 => 0xb24a3996347159251cca1f3a0c0a8e650f5d060547328eeeca88a39947b7654050ccb2cb1cc1aa4659a98960d5232a74e1aa4a91953a70d91548ca1fbb2a82a4659358e6215232a74e1aa4871943e76951438ca1ebb6a821c654e9c35410e32c3ca8b18851947776544518ca9d3a6a12846587dcd6494232c38e6b24a11963870592508ca1f3a0c2a84650f5d061542328f6eca80a11953a70d8f544ca9cb86c7aa2654d9c762d5132a6ae3b16a89952d72d87544ca8eb98c3aa265475cf60d5132a5ae4306a89943f76550544ca8eb9cc22a2654bdc96115132a3ae6308a89952d72184544ca9d380c22a2654e5c06115132a5ae5300a89951f73580544ca8eb98c02a2654b5c86015132a6ce2300a89953571180544cb162a4c5a1a658bd506250d32a38eaa18869961c5498f424cb0faa0c6a12654b1d5421093287ce9306a29943d74983514ca1f3b6a8a8a650f9d85454532c76a9b02a29963854d81514cb1daa0c0a8a658e15060545328eeeca88a29957070544514ca1f3a4c3a82650f5d261d413287cedaa2a09943e76151504cb1baa6c2a82658d1536154132c6ea830aa09963454185504ca3dbb2a0282655c1c5501413287eecaa0a81963554584540cb1caa2c02a0658d9916115032cacc6b08a81966662584540cb3930cc02a0659c5866015032c74c8b00a81965a63580540cb35312c02a0659c9856015032ce2c2b00a81962d5498a430cb0eaa4c721065175da538c8328daed29c641961f65d91320cb0fb28c8990658bd97644c832c5eca322641943e74181510ca1eba0c0a88651ddd95114432c6ac8a88a21967151580510ca1f3a0c2a80650f5d061540328f6eca80a01963964540500cb38b0aa02806517dd95314f4187eeab1087a0c6f7654852d064f39cc3a16832d9c764ccb4196ae930e65a0c7a70d9632d063cb86cb196830f5d84394341c5c87314a1a0e2c4398a50d063dbb2a028683539cb6494e41a9ae5b24a720d1d74d8a539068fba2c529c83559c46294e41a9ce430ca720d4d7218653906ad380c329c83565c06194e41a3ee8b04a720d1d7418253906a7390c129c83535c86094e41aace2304a720e59601825390637390c0a9c831b5c86054e41a9ee4b22a720d4c7259153906adb82c8a9c83561c16454e41a3ee8b12a720d1f74581539068eba0c0a9c83539c86054e41a9ae4302a720d5671181539072cb00c0a9c8317dd95314e41caca6b0c8720e5553d85439062ebb4a62948317dd95314a418deeca90a520e5a53980529072ca9cc0294839694d6014a41cb2a6b00a520e6952580529078729ca5214838794d6190a41caaa7b0a8520e55531854290786a9a84214834b5ca5310a41c3acb2988520f0e7294c4290786b94a621483875955310a41e1ca73108520cad76d484290786a9ea421483699c752
  | 25 => 0x200080000010000002000200080000000002000000200000020018000000800400000040008000000800000380000000006000000a000000600080000000000000000200000000000002003800000000020000000000000a0028000000001600000020000000000000000000000028008000800200080060018000000000000100000000000003800000100080028002000000c00000060000004000800000100020028000003000400080000000006000000600000000010018000800e000000400280000000002000800000000000000000004800800000080018000000801200000000000002000000200080000000002002800000000000018002002000a00280000000000001001400080080028002000000800080011bdd95214b438eeeca88a3a1c7b7654050d0e57394c1a1c87599c75294a438deeca90a521d6672d465190e37390c0a8c871b5c860546438eeeca88a321d3a70d0d5090e3dbb2a0284879ad4960949438deeca90a4a1c7a7098b5150e3cb84c5a8a871b9ca60d45438dae5306a2a1c77765445150f34b16a1282871edd95014143a72e1218a0a1cae729834310e1ebb4a921887175da5490c438f4e030aa421c79701855210e37bb2a429087995496114843cd2a4b00a421c7a701895110e3cb80c4a88871b9c860544438dae4302a221c77765445110f32b12a2288879c5456014443a74e1a1aa021d387050d5010e37390c2a80871b5c861540438f6eca80a021e69625405010f38b0aa02808717dd95314f428eeeca88a3a147b7654050d0aad386a729c8517dd95314e4287aeb30c872149e739874290a9b38e84a8c851ddd95114642ab4e7a84a12143d7690e5090a9cb808728485179cc61542428bae630aa12147b765405090b2ba9ac329a8517dd95314d42caac7a8ca2a1477765445150a9ab8c8428a851d9c663d41428eae331ea0a145e739875050a2eb9cc3a82851edd950141428ece2302a621475711815310a2fbb2a6298859554d6114c42cb2a6b00a62151d7598c4310a8fbb2a62188587dd95310c42a3ee2a98862151c7054c4310a57baac4218858bdd56210c42958e2b1086214af705884310a1ebacc2218858754d6010c4293ce730e842143d769524210a36bb4a9210852b9db4350842a6ce321aa22152d7210d5110a9b38886a88854d9c74254442a68e2a12a22145e731815110a2eb98c0a88851ddd95114442caac6a88a221671515805110a1ebb087280854e5c043940428ece231aa0214757118d5010a2f398c2a8085175cc61540428f6eca80a021659635405010b38b0aa0280859958a61d5332cacc6b0ea99953671d5254cca9b38ec8aa6650fdd95415332c9cc6b10a99962e5458843cca9b38ea9216650f9da5450b3287aedaa0859953671d5042cca9b3a6a328e658bdc96494732c58e4
  | 26 => 0x10002000000400100020000002000000000200000018000000800600100020008012000000200380000008000001000a000000200400000000000000000a003001000200040000006001800000200000008002001000400000060008004001000000000040000006001000a00b8004001800000000000000004000800600000000008002000000200000000010002000800a001800000100020000002002800000000020000000000000000000000000000000000600400000010002000000800000000028004000000e001000000000000018002000000200200000000000001000000200000030000000800400080060010006002000000000120008000000000400080000000006000000000200020000000000000a0000000000000000000040000000003800200080020000002000000a00000000000004000000200080040000008000000a000000400080000000006000800a0000008000000000180000000000000000200100020008004000000a00000000010000000801400000020000006002000000080000000004000800000000000000000000000a000000000100040008000000800000000040008000000800400080020000000002000000000100000002000000000000000000000000000a0020008000800000000060060000001800400000000030000000000800100060048004002800000000000018000000000200100020000000001000000000000008000000800600080000000000000800600100060028000001000a0010002001000000000000018002002000200180000000010000800200100000008006001800000100020000004000000e00000020000000000000200080040000000001000600080040000000002000000180020000004001800000080000010000000000000080040000004000000000000000048000000000000000000000000002000200000000018000000800e00200000008002000001000000000000002000000200000000000000000000000000000028000003800200080000000000002801000000040010000002000600200000000002000800400080000010002000000200180060000004000000400180000000000000000a00000020000000003000000000040028000001000200080000028000001000400000000008000000000400000000008002000800a002000c0000002000000000000140000002000000200000040000006001000200080000000006000000000000000008004001800200080060070002000000200180060000002000000400080000008004001001a00080000000000001000000000000008002000000600180000010000000000000200020048000001800200200000020000000000e000800c0000000000000a0000006002800200000060018006003001
  | 27 => 0x400080000008010000800400380000000004000000600180000000000000000200000100040000000000000280160000000000000600000040028004000000000080000020000000800200280000020004001800200400000000000000000200080020000004002800600300020018002000800200000020008016005800000000020000004003000400180040010000001000000080020000000000000200080080000000001000000000080000002003800200080060000000000000e000000c00000000000004001000200000080008012000800200000000000000001800200080020000000004800a0028000002000800100000008012003800200280040010006001000200100020000000000800c000000c000000200280000000000004000200180060048006002000000080000000012000000000080000008000004000400380020000002000000000080020000006000000000000020000000000801c00000020020006000000200000040010000000000000000040010000003800200000000008002000000200100020000002000000200080000008004000000600380000008008000000200000040000000000001800000120000000002800800000000000000000000400000020010000001000000100000000000000800200000080068002001000000000040000000001000200000000050004000000a00100000008002000800000080000010000000000000000000040000000000000180080000000000000200080000018002000000600000020000000002000000200000008000001800000100000000000001800000000000010004000000200100020008004000000000080020000000000800000100020000004002800000000000000008000800000000000030000000000000000000000004000000200000000008000000000a00000000000008000800000000020050002000800c0018000000000000100020018000000000600200020020000000001000100040010000001800000000020000006001000c0000000001000000080040008002000800400000020000000000000600600000000000000000200000000010006000000200400080000000000000000180000010000000001000000000000000000000400080100020000001000800000000000002000000800000020000000000000a0008012001800400080040000004008000a0000002000000a0018004000000a00000040028010000800000100000008002000000600180040000000000000c000800200200000018000000000000180000008006001800200000060018000000000a00100000000000000800000000020000000000800000000040008006000000000180020000006000000800000060000000000000600000000030000001000200
  | 28 => 0xdba3d881a411887da0000fbe1f8c6a50da80ce000034e000000000000000000ee700000000000503000000034804f53e9400000000d7092c00009400001fec4b130783b700000000000000000000000000000000c8d0000e9d1d080002788a6a026c0001d900000000000000103d1a3c000053d0b7000105b000052c000000004480000000000000000000005f440dcadc1fa00001bb0a3f3d84000000000000000002df40c31c64000000000000000000000b7f000000000000000cf00000000c3707e013b03c8c27000049522c4e4f2a40ee60000000000055634b0fe60000000000043f3f381b22cbce7a344000011e80000000a243c4000000000000000000096400000000003f2c00019c03c7000000000002400000000302000008300000000000000086125300e03fe484a0360795107800012d0000241c00039e08eb2ca040437f475d18fce4b26ac54e369c815343032d014c1a920c400000000002e2c4523408b942cd0add32cc4111d64ab42f800bb00000000000000008400000007531a60000427cf43340c000000000035f00000000cd800001a810805b22208e1c2f3d0052064b8836acc661ab80003a0c0000000000000000000000000000165410cf941f488670000287000099421648cf2fa80001b1003900009a621800002e30f992da00002f3400000000001f640aa00006ad0000fcd0000000000023e183c0000000aad00003f3387800012b40003c78834027c000230800009d105a048c00028c0000000000015dc0000000000000000026e40000000000000000027500000000000000000000002ff000000025487840d2475c0bec00000000000000c7c000000006d800000000000000c81000046100886174194d6d0000000000000000006ee00003eb00000000000000000000035c0000000000028183452c340000000d44000047b0b4800000000002c200003a70d7d0750d630fb470b11f84790000000000017414745393148000000000000000000b5033d00000000000f11000056700000002dd40003b204c004c035f2f2000000000000000000348c00000000000d280000000000000000000000000000c3409c079e39a40002acc000076c44d0000e04000000000000000000000000096b202c00000000000000ba2000000000009f13d30a4000040008000000000400480000010002000001c0050002000800400080020000000000000000200020050016000000a00180000000000000000000100020000000000800000000060008000002000200000040010000000800600000040000002000000200200040020004000800c000800000080000000004000800400280000000008000000000000000000000000000600000000010006001001000100000000002000000000200000000008002000000080
  | 29 => 0x370df43d980000000000000000000000000000000010800002b8d0500004a427d4ac13614ff024500001674aa736b451f0000000096800005b8bc030c80002e941a52ebc00000002e136c8ae2419059b048855c363097a00000000000000000031a00003191ec8ef617d85d02f7ca91266025d012414300000000000fe7037458800000000000ffb00003cd00010c9000000000002460000000000000036a81192c086ba35fc928102873d0000c6f3c08abf27310632ed8bd002dc2da0f780003320d4500000002f0c000000068400000000000000000000003100000000000000000000009df0000cd615ecb40229d030117c6d2113c000000000020dc00000000001a4000038e00000000c63409c69f00005a700000001dfc0000000d4d00000003c88e8233a86d33c2065e05ac000000000000007992598d5210d80002f9c0000c88cdf0000676000000000000001ee40000000a7709510a32aac00000000000000a540000f4e0000dda3260150372400000000000000bec0000e792b6400000000000000000000000000000000000000000000011bc1ac3780a6835e82931e6c000255447c0000a0b38b42d80000000000033025106102078000000000000000000000000000000023104690e300002ce400000000000ea040d327cf8c16dce3b06ac00000000002c60ef800004b30d540000000cf200008100e0000040f0ad23e1c0000ffc0001c1821b0000c800e60cf0000076a00000000000f2c414400000000000000000150019f00000000d7800000000002dcc0001870a860000000000041021742a40000f6d000026020b0242012cfa907a800014ec0000000f17000000000000000000000000000000000000000af52ecc3370e44ab028500001c1cef036f506f0000414000093000000000000633000000004e8365000079427040001424b8f0000000000000000000003f0800004c85d33a2c0001ec400000000000000000000000000000000000000000007e00006b132f4a132b4057400000000000000000000015940002580a5d00000000000b140c60b5342ec51e00000000000000314400038600003128d5e0000eb9000000000ec5cf186800000000000000f310df88520000c542c4400000005870000f840000000274010a3fa80002110bb800000001f784c8000000000000000000c4b16fce0300000000000f380a2000000000000000000402c000000000000000003cc80003a48000000019a000060e195cef10000a9633f0000000000000000000c4c000000000000000003938d3e32b00cc339857a251d06820949681f240000000000425853800010b50000000263c00000001991ccc4b200000000000eff000000000009e93f4c00026c40000000000000012b000000000000001c7400020c000030c436f092082d00000
  | 30 => 0x49e2c800e6000000016000000000b8e0000916000000028b40000000000011800000003050000644000000000000000000000000000000000000bf80003d9c0000c481e0266c000000000000002641170000000000000001a7000000000005ff00000000000b920000000000000021c027300005cd000056c00003e21608000000018e0000000000000000000000e580001244000000098907c40000000000000000024e80000000f5a3944ec13f6400012502c7194095b31d06a434ec481259cb3c00000000000b31132cb123590a4400001110000000046c00000000000000000000000031603ac000000000000000000be61ea046325c80c6000077700007d400000002bbcace000035c000088a000076100000000000000000082f30fc00030b80000000cda1e2845627d800018c400020f8000000000000002330000000000000000000001ba0000000000000000000848d480000c8e00005fb1bc0a1e1e3c36e30e4b2d3aa80ad09b4da9000041c000000014a0dd9327476500003513d900001cb87ea000000000000000000000397000000000003e2063d00000002bf5062000000000000000000000000000000000000000000364065f12dcdc526dcffc199d02f051c04a1e900001f1c00024d077a000014b3aec00000000000ec04e4084c00018a800030d80000000000000000000000000000000000000000000001b4414142142c800809cb00000000000000311400000008b20000000000000000000000000dac18b8c3e00000000000f892f5c6962fac234419c00039d4c5900000000608ff5000000010f4b50074c0000000cb60000000000000015cc000000000000005a416a0cc7028000000000002658000000000000000001dc0d8111b84fc000000036f80000af8000204c04d09140001fb0000000000000009930000f830c808bf41fc44e0001010000065423a810d3a6507503d0cae054c117000000000000000000a2e226c6fb430070f29c8885000093e1554fee06549fa1dacecd00000000000000000000000008ad04cce2a0000c3d3dcc00024fc2f0050841b000000041c00000000fb70000000291400042e41f90000000369400000000000000576000062b24940000000000247000000006ab0000c29298492c247ce7e0efc0003ba0b170000000000000000000000000bf614dc000000049239cc0000000acc0000000000000013786134184000000000000006642c2c6302238000103c672000000003f0000000000034109b6000000000000a616e00000000775000000000000000000a2f0130c8a2f440000a5818b0000d1200000000000000000070e00003f200000000000000387498d36543e942a04ea2d9c7960000000000000000000003b3000000009de00002f400000001150000000019123ecc4037040003
  | 31 => 0x10830a7509000000b800009e1000000000003e00000000000000022204e80000000000068b3804ade215052d3d105d803e000003a800000000000000ca915f800000000880000e4c0000000058c9c00000000000000007650571aa4598432cf58385000042a40001ef8000000000006700000000482000000000000000000000000000000000000000000000083a00003f435600002d200000000000000000039580000000000090c0000000e12367c0000000000361c2611d0c19b34200000000d0032702d731a86fd2f58aa2426c7102d9000000000003d180003208d06093c08f00009bb38b80000000055009000000000003ad46ac033cdce020cec423f45a309e00002eec43e0000372000000024480000000d9124400000000db62498f0a1f70e3d2fec0003c840002cf48c60000000000000024ac0000000000325c7fc15e00002ac40002cfc00002d42103124fbb00007283af07e218bc8e52bb40003d447343a5cf96142cefb0000bd41a0822f00004460ebc000000016726d03e707080001ef00000000a8a0000e98357400000000000000e3f01400000000ddb3c640001a88aae0e99042000000000000001b40000000000000000000000000000000000000000000000088800000000000000000085041a000000022240001ed80003f489e700001ad00010c400000000000cd5111c0000000a08000064b22310af3cfc134360ce453c14366000000000000003be8a6f0390000000000000000001c30000000000000000003a149b200006010000e19000000036c400002d800037c08af189c69e25e000000000001edc000000000000000000000b4e010c523265cd011f340b0000005908c0ff80000000000000000009ef2854e401210f690ea4000000086800005513e750560000e2c00000000000b3708c881400000002870f9500000000000f542d34000008ca7e00000000000ab80000000000000015310a12bfc0000b0000029b40000000000000000019600812080cb83b6104d35c480022545d730680d03648000000000000000001e1c93d022c7c004d40000000000288ce0a1fb80000000000000000000010ba000000037dc00021ac0000d50760000000000000001c14f8000008a2000068516c464a000000000000000000000244c7010000000098c95d276c000044c99d00000000698000000060a0cfc00000000002b2400000000000000ff3085c00009ec000000000000000004020000000035d0000bbd00000003e980002eb00002794006181c3641dc80000000000000000000000000000ee12e0906900005a20000ee231805a50000000112088f00000000000000000000000000000000d7600000001d040000000000000004e000000000005ed00000000000a850000000423800013289920314
  | 32 => 0xcd22478000311c00024c869425b80000000000000000000000001e404c32ce0c673064a2800004c40858ead0000dfc000038d0000000000000000000003d7000000000000000fb800009d2000000000008e242700002fc400004e000042cc0000000000000000041c45b000005dc00000001c009cd22449ee0b2829a000000000005bb0000eef00000000e78000000000021c4d2e000000000007bf00000003dc05aa0b5800000000ef00000002c546181a8000007d4000100800000000001e984392ccc3ce00000000000000000000018b4000000000000002af1cd4763000000000002563530000000049a0000000000000000009ba232c56b0000ad32a08d7400004d50ecc000000000000000000000e300000000196c00042e00003ffc0002d44b3e1c9c2c50000000000109530f00003cbc0250000b953580000000000000000000000ea4000050a0000000334c00008e4000000000000000000000000000000031c09dd0aa080718e877d298cc4316800e10000c9614202ac2e1800000000000218f8218ec0004130000352c9560e0c1c8000010b33b0000060c000000000002840002ddcd14301c0003ff4c9921bc00000000000000000000000025180000000000000000014ac18400001400000e6e000000007f8000000082900005d100000000000000000000000000000000000000000036f0ef9426832b1bd898511640bc1020000000000000000000000b252ad4600000000000008743508e3e284476214f00002fe02082b44175253c00000000000000c83305cbe20000f3300000000000f131d5c86341b8c5d2e40000000075a00000002b60000000042c27980000000e290000ed70000fe800000000000000000000000000000000c8b0000d0f28f824d12f03d31b842a20000000072400000000000000000146105437d80b31ffc56d19a400000000001bcca8f00008a0000093b000000000000000000a0200000003d8000000000002d5400007fc000000046a00000000000000000078000000000f700000000d1a0000000000000000000000000000000000000009d703349d300000000000000187c0000a9c0002d50505065cfbf2e680003b14000399000021c8000034400000000000000d6e00000000b4400002a40000000c1b00000000000000121c4e2000000000000de0294df13c0cd26000055416a450c00000000000769378c4ec00008f400000000000d1d000069200008d20000d180c5c000000000000002c10b88a4b000000004f000010884d9000052502d0186000026f000089a3b084b50a180000000ffa0000cc50000b7e0000e7400010a03330000000044b0000000177c0002dd000000000000000007000000000000001c0cc640000000128c0000000000074100e32c8cf53a00000000000012fc5d60000000
  | 33 => 0x3f408d328400000a0846d246c67300009b50d34c110000fcf000105c0000dc2000008d00000000000aa300000000000552032400000000000000406000000000000000000000000078200000003ee802606b80000fdc00008f400040ec2532074ea927d0ec90f24a3905b4af134582cd19b000037441582da4d40412c75f34d8166128400023b000000000002f8c207153c000000000000005c200000000000d370000000000000039680000d6109d1410d290000000000000000001440ca88570ad102301a400000010a705900000000000083c00000000003f600000000000000000000000001580000000000000000000000000157c000000028a000082e03ccb6340f8f150bd87023c708ba17bc0000e6c5ad263108f3b3c0003e806f540440003bac00000000000000000000000000000000000d2d0000000000000000000000000a710000001009c00006e01af0000000379c00000000000000000000000010ec0000000000000000000007980000000000000013c800000000000000a84000000031f4e2f0000ae11f9c0002f043590000af83e6c0000000000150c4170000619000000013f4f9200000000000000000042b3f040003894000043800021cc145000000021249f8000081f00009220728acb0dd40000ce80003950f1805a0b653000000000082716d840534f00571be89fc2d048052d1400030b076c3b780000000000000108c238cf8531300001bf0000318800000d83152d98cfd3a5000000000000bcc00000000000000e0e00003b50000000000061e2380f6c0f9464f03480001aa858d1cdc0003eb4000000000000000000490000000000029c0bbe21fc6dc24389c42eb45f90000000000037b01100ec00000001d606890000d4f0000000000000021e000000000001ee83012b18ba91a9c0000000ca500000000df40002e0000040ac000136c03d40d80000000000000067c00001da18087563d9400000002ea01cc1cb00000001b508120000343000000024b892a0000292088c0fa23fc64018a00000870000000000000200000000000000067100007220000000361107b000000020040000028666016887b0000ae6284852a00000001b9000029a43fc000000000000000000000000000017484f9000039f0000e6707b80d30dd00000000000000083800000000001047104800038d46450000000377874400000002464e9e00000000000000000000033d0a6c000108a154c0000000d940000c75000042a19810b21d283d0000000000000000000000000000011c8f1b00000000000000000070d000000000000004244b5c16b0000000000023603c01368aa800000000000aee0000000000000031eca32151c0000000dff00000000518ae500006831dbcc0d190800919bc0003748000000000000000000000564000
  | 34 => 0x9400000007bd2dec4f1032901f4104f7e000100d431c0000000a1d3880f7c3ef00003690cc900006b80d1c000000000000002d51d2000000000003e5c0003ac4000000000000000e2000000000000003fb40000000000230c4372d800000b08974422c00000000000000000000000000006c50a140001b280001b08bfc0000b4916580a23ed04ac4314000239c000287c0000000000303c00000000003d2ccb423f0000000000019b8000199400000003e3000000000000000000000000000036580000000a25424ced033350400000000077c0002d1c0000000000000013f043c1ec00000000000f6a2ad891d000000000000000000000000085c00000e800000000000000291800000000000d800150000000000082100000000a9400019f45203c190cc2374e1a000000000004e60000000267c0003cd80000000c6b0d8800038000001e84000000000000000002514e390000000167013e00000000fd800007ccbc5233429b000015500000000000ce90a34b0e00000000000fd414907200000000000000021f4000000000000001890000000000000005c8a562a1c6f82d6000012c09402f6c00000000000000000148400021e80000000000000000001040000ed800000003db000000000000001ecd0aa0f74000000005b000000040cc091000000000000002d5c49600000000000304000026c328c000326c3c10000b4b00001f0000000000000001338b2925f80000000000195421500000000000000286000017f00000000f590000000000028f2a200000adc0000000000200c000000000000000000000632000060600005114208258220d0220000000000098b061cb1b35f8000000072c29d0f420000000000037c2070b83396c000000000022ad0bf225c711000089c000000000000000260f470000e9336bcb710000c6d1434000000000000006a803b40000e94d43000085832d400000000000000a480000000000000000009f2000000000000000000000075860b00000001ae4c2f28a8e061ac000000004f7315c0003af8000000038200000000000000000007441780000000f5d12bc0000000000421ca730868ea21cc0f753d78bc42560b5b0c34768063c00000000000000000000006d0f605952e98000337887e00000000000000000000007e879721b8000000067f000000034d0000121800000000003280000000026e000075b1e3016f0000bf3000077812a800032e800000003b42fe800000000000000000000000034a0c7700001d2302800000001bf000047f0000000104c0ee32f89c22aa8d4e06001cf12706160cf8000355c09300005fa3d5400000000003a40a51000000000000000000eb735dcc040b6c7741b00116000000000000000000000298800000000000000000000000000000000000e420000713000099
  | 35 => 0xd5002c1c4000000000009092e9c0000000000000000000005c620c837300010be2cc8eb30dc400005d864d23f800008a4000000071600000000000dd0000000000000001b78000000016a0000000391080e22d8a1a00005fe0000f260000000000000005dcd8d14c45b319e4dc63170e6c375c726000101c000055d0000000000000024300000c7ca2000008c500000000000e430000000404c00000000000000e500000000110400000004a93dc8b8a0000000000000000000000b64db942d8000000000026388020cd075200001c124280000000192036c6ed0000637056c7933138000000000038dcdca000104924c45f32e04000000000042ac2680000000271cee92e8cc05000c01f000000000000001dcc48837bc00000008920000000000000005f0000000000000000000000890000000040e800000000000000a220000000000000041480450000000000052f3d8c338000000006f0000000077e0f087153cd0f3a40e00000000427213800000000003f689be2d28b001340000000059a0224e4a00002b000007e118989a405f81fb3c48000000000000000000b7878600000000c3c0000000d333c5800000009cf000000000000001a00e4d1e045db0000688000000e0000000000000039f400000000000000000000093c0210dbb39bc00f14980001b1c00033c40000000e55000000036748de3b50a4c3710afa000040700000000000ece295c00005e104a37742f10000fe1000000037c80750000000000000000000003a54bf405e4000000000038e8000000000000000000000000000098a000000000003a01830000000042d0000cbb000000000000000000000403c00000000000000d723afc7d5222c06115880672158000068ce320cb800012a01e5000033213c000020fc000000000000005ae0000e8900000000000000000000034905e30d6c0000000caf25a50bd000000025c0d59116c1ce0000000416000032845ea0000000000085106ece0f12980003b700000000ff12ba0000000103935cc0000000899000000022f00001ce400031a024700007311c6877113d097d1e3831106805831b200000ba4f770000458000078801d89ae159800030e80002f540000000b011eb000000000000000d250c8c6533c2c00039483c80000ea70000000202400023c902100000000000b1c2e64bef0000af42830000000000001b80002834e8431040003d2867500000000d8c00000000003ea8b4f07f0000000000007980000000000000000003ec0000000000000000000000000000000000018a000000000006db2a340000000000219000009a400000000000000000000094300009d6000063802bc05100000003c94000000089400000000478b6b00000000000c2a0000000260400000002b825bc9c50a500000fbc7f4087409504
  | 36 => 0x22b800000000000000f2b2c4c0f600002e60ce40003b8c9b839fc0000000000000000000000000000000162cbc71ba8b8d1924fa80558cdd0000d2700000000000f0e376027a3478ac23bd10863eac0000000000047c000000000000000003770ab20000950088400000007670bb00000270000170c000208c84f000000007b4c5328048b000000001e3400000000000000c89000000000001eb0000c1300000002a048d70000efc4298000017400002a098000000003f28e9a000000017f5016046089e0000d9b0ac46b6107c00000005c4000000000000001a284980000c840000000000000000000000000000000055e2edcbd9000053f00000000000bf030e0000000000000000000e4c000000000000000000000000000000000000002b900000000000162800000005940000000000000039f00001fd400000008860be80000000000000000000000d900005581684896000023f000067400000000aec03124040002b34ce725b0745106000000000000f1400000000f0000000017b8d780d18000000000000000000000000000000000000000000000330c000000056a0c0c00000000000000000000000009ac0e740c8ac4211c2623b905eb000000000001200000ff607f40000000dcf000000027cc000000000000000002a000000000000000079d000000000000000000c950000bed34fc0002e6c00000003aa3f30000000008221788a80f7c00030842760760b2e2c840103a586bb0000000000071e00000000000000000000036e00000000000000000000000001a300000000f2a000000000000001d2c0002fb8fdb00007910000c0c1584000093000024e0e36000020903dc000329c000210800003c4000000000000000001528de40000c850548000000020d0000a3400000000000d4740c400017a094a16788cc0000535046800000000002f9000026b000000000000000b9d00003790000426308c000079c982000000000005320000000384c000087c00d00009a90000000074400000002c43b1c0000000000000000010a4000000000041ac979000000000006610430fb200000000000000000000009c81072e70000000108021200000000a76000002b0000917268c00003fca5e0000dd40000935000093700000002f2800000000000000000000000016f000000006cc298038b00007fd000011400000000000b0900000000c5000000000003ab000000002490ae888d000000004a80001adc000000102422e00002e440000000000000048d0000000000000000000000b4c92401bcdeb07d0caa3cb4ac81a647c41e1490607a0000359892d4024f09000000021680001b6000000000000000a0521b000015b8b2c07d85930000000000083b0a445af0b186a6000053e000000000008840000b26232800032ac1
  | 37 => 0xa3700006ce1b18c1f2824cd000000003b2c0001e2ca97302448901604750d688bd00002a01380ae30ef4000280c1dd000094b00000000000b5200000000000000000065d00000002ed07380000f7b03f80000e189bd000096223000000000f930000000397c0000000000000000000000001b5cfa308ac5720d5c030000038a00000000000000285835331108243080000202072f000107216f8b420000e11171c00000000000000000341c7c30a646a1255030c3a7c5e000000000e1d0b013e86b3000105d14880000000000000000000000000000000000000000010042a68d65253800000008f7017800004b40000e640000000000000000028f0a531458d461d00d980000000000086900003c419e10732b9c00026a02dd029058e0000eaf22842f5270c00000008a40814cca2b7c87500002fd0044000135c0003e40000368c000018c000000000001e4000000019e0e8495e01f4faf0c40000283c016000048e00a000000000001280000000000000000000000000000072d0000000000000008e80003d486e90000df935bc0000fa8cff32300001e6819d000000013700000000b6c362000001dc00000000000000000301902900005ab00001572c589fd109039205346c92b0c2e50000000000000000000000730356000045517542e3412000000007fa00000000000280025c0000000000000017100000000000b3023707473380ef7134c74d0000000315800003ac00000010b400000000000bb200001f73e180000cd4e9b00482cb2e248f51f7c1c50000000000000000000002db4389000000000000000000000000099e0000abc00000003a04000289c0002368bb13e6861100000df139c0000000b9f000000000000000000000000000000000000000000000000033ecaa500002063e34000000000000000000000000080c68e19310500000000000093300000000000000406000000009ff0000a0a39240700000000000084501701260ad4cd7000000031405e94004300000018800000001ebc853047000035440000214625000000022b0c6500004a23eb00000cd80000000e7b03d4e8c000000000000003e2c0000000000000054500000000000f3e0000efd00000000000b6125d89a51778b10317882b000100223e400000009ad0000000000000023b4e0936780004050000000000000000900634326000007f00000002e10000000000026fceab1b04a0030ac4b825686cb19640003cb84cd0000ac50cc400000008e10000000000007227640002fdc0003974dee1384e8e000000033e400000000003c900000000000000025b00000000fec97f000007100000000000be800000002970000346cbd326100000000000000000000000003e84be134e48e600000003f8c822000000000000001920000000000033f80000
  | 38 => 0x3facdb50000866290805f00000003964000000000000106fe11782e00000d5000001012a90afb2444000000000000006f9000000000000000000419000000019180000000000000031c3e2825e00000003f7800000000000e14000181000000000000000000000054d000000039ac1bd0a7887c00007b011083d5155c29500000003cf0000000000000010790000a9e0af400000005ca2c10fc301f000000000001a5c000000000000000da21941900000a433cf427d0d000001fc8aac000000000c80002af8000000000000000000000000000000000010921b9800000000000000a490000000000000000000000000b7000000000000b360000c5f00000000000060296000000001ef0000b9e156c0002c7400000000000000370000000000000000000000324c5300000d620a8c79200008e90000ad40000000000000000000000000000000000000002892a6400000005152ef00000e3c00000006b51afc766000000010c800004f43da00000000000edd000000000000002efc00005c02b32eb8a17000000001ec80a0000bc90000000000000035240001b7400000006140000eb2000029c0000ff2240c1360b7c0000f4859000007b400000000a100000828c6c333c00005cc00012ec000000015d0c7800000002750000000000000000000000a38ed2000000000000003c10000000109700000000000e760000d3a297c0003b4c10300000000000dd31ac84782e60c481cc800006e873c000000015d40002f600003980000321c0000000a351f2000000005480000000143c40e33e80003b44000248048a000000000000b1000000000002bc00006222b5880f08d89c6000000017d40000000f8f00000000d0858f0d40ae91dec0000274348000000000009d13c9c5e12ca80003ae0acf34a8a8301a0000000017a0000ca81c487d80000000000000000003c3000000000000000000000000028c261c000000000000000002c780004210d690000c26099400009c400000000000000000000014c0000435221cdfb0000de50b3c00000009082668749000000000003520000000100c00000000540000000000000041d8cf3278c0003fd06860000000268445729b90170000000249c4090000ebd0000000000083c10c402a000096d375800000004d100008172d104be000000000000000000000000042300003f01ee08df000006b3df40001c700621eb44830000a7f3f440000000000000000030b47c612140000000a070000000000022a00000000000000000042800000001eec0000000000000000008f096100000002354ad70000000000015f1c50eea00008d114d800017748f8000061d17b0266220006638f00000e88000000000000000523de400000004d2000000008800bd0000bd2000000000000000000fc7066000000000000000
  | 39 => 0x80002298000000000000000000b387dd1308b0a2cd4eb42f709af31343f8188422e0000000377c7eb2bb0d6c296cc0e0000a7820f4746000002c2f089711464000000106600005e23bb8000000009200000003218000000016c00000000000000000000041540003904000000000000000003b00000413c7f000000000000000000000000009230000ce3000000000000001d5400000000640000000000000008640000000bb916e4a95206c0000de824a00000000000000005c00000008430000000000000019580000000000000000000000002bf801800000000778000000089839200000000000000049d3c6800000000000000000000000000009a2258c4cf0ca00000000000293422c3dac7d30000395000000010bc00000000002f94bfe0000000000000000000000000290000000006c0000000000029981693ae817f00000e514cc00000000001fe40003a803f1180ca413624f071764eca2ff4eed27f80000000a9d2eac0002948000000000000009880000000000000000000000000000000000000000002abc72a0000000000000000080000194d9a205800000000000000d79000062c00004340000ba1000000000006d509482f80000570000000000000000000000000000000007a73d200000000a3b0000000000000033e00003288cc216049f90000c2434540000000a9b1704db4000000002c866a18d40000000fb63ac000031cc000000000011f4000000000027b40dc32980000001026000000000000000000f8e365c1b1025000004149ce00000003ab84c62ae8000132400041a905929f400011140000ff8000000000000003690000033000011d0000000000000000000002fe5028000000000000003a989151540d0e306000000004ef0000e860000bcc00000001854000000000000000001e8010632506b4000044c1e8c000000000000000001af400000000000000ec600000002a240000000e2600000000dfc0001b882cc0000000000000041800000000000000020e20d8000294000035ec000000057929e400018340000000000135834c00010153684000122cfc61c606eb16441f200000000000b972564000138c0002d181592e4cdcb0000d8b049c0000000fb0000000000000000000000131400000000000550ab9358412c40686080718e0d0000000000000007880000570000013c0000000000000000000000560000b7c4000b6a34f400009dc0001fe00000e5c15127c0fdf41107f117c40000000202093800000000000000000383039d00000001c1000034880000e380000000000000000000004dd0f440003c74b780000a4700000000000000414c0003db8a4f3cdc7ab00000000000000000000000000000000f3b000074e239000000003a40584b5e37845493884000000000000000001f4504e0f3102c
  | 40 => 0x8c4c3300000000320b5f338800042340000000000000000000003a3000000000000001dd800031e83250000aa6063000000000001f3861b0000bf50000200000000000000000000e081d5000009fc00017dc000194800000000002ea0000144c000000000000008aa0000ee500000000bdd05f00b400000004f80e040000000baa0000ac73c3c4f30000e6800d50810000e66000000000000000000cd900002ed0000ba00000f9833180000000000345cb8516e83ba37f8b872a8406a19f80000000000000000000000000860000236c0001d4087622d000000000001bfc0001a3400023640000970000265400000000000000d8f000000000000003d4c00000000000a0400000000000000000000042e000000000000000000000135030e000043a0000000000000014710193a94d321fcc000000020108980000000cf612e400008900001a5410000009e000000000be400023c000000000001b3400024a45120000cbc00003d61a8c0e913fc3b914d059226c04210cb080427ec4770000000000000000000000000000000000000000000000000000000030a00000000000000000037207db00003e600007e500000000000000000000000002e40000000000000000000000000c1500004010264b053300000000095700005840000f6f2de46f4197031b00000002af400000002a10ddc0000000000000000042b85073d2494d000000012649640da0c690000000339400000000001b7c0003118000299c0001c6c0000000f40000109409f04f60f901aa0b24000400c0003bcc6f20c2c00000000001b58fae0000000021cf391b68019000002931e000000000003688e3402587cf000084d0f2c333000000000001480000cb00000000430ce463fb0000000066b41f8000000008a0c900003888000395c5710000d5c348448c01e00000000000310851b0000ed5176800000005e609e4b1f2fc800000008c71198000000025f00004cc00001e935280000eb40000000cce00005bd0000b4c0000e280000977000000040d44651cd8af219ec000302c000000000023a0327000045300000000000000000107d000000037000000000bb51e0c3f90000000191c59700000001e24000260c1e3040800037b40003d3c3841f300000000000335000000000000000000188054442c474c0cbc0000000e6300003b8000018500000e30ec86e531c49eb2cac0000c84000028ce1000000000000c6117242b2000000032c4a0e3278d3500000000c280000350000000000000000000000fc00000000000000000007a53a349390000a9c00007d700fc50018a48d400000001c94000000000000000000000a8b0000000257d0770bf08d00000000370c000209800000000000000000000057c3c508f12c0d01e3f74d680000b5d00000000000ab700f
  | 41 => 0x88cf73d040001700038000049f0000000000000032400000000dcd145c1100d8425713ac000344400025f00002bcc0000000000000090f0fd4376336c1e414380000000991000015e0904473000000029902eb12000000684b59000091a00008bb000000000000000000a3612f40003dd88550000d30000090203f47f71f149ea1b0cb27000001c145000000bc41d04201b41cfce6142640000001074179400034340001a745f200003ca19041c312949991ff80003290ea336c0e6a010046b363809e198ce1536b849b0000cc13c30a6b10ccdb342201be20a0c1000000000000f562ba84441c5c0000000000305000017380003a2000031b80000b9c0003fbc00000000001890f7420190ad000000033900000000000000000031fc0001ea812e29548770000000000000000004ba09440002c3c0000000c01000000000000000c2400000000000424000131ccb741140000000f2904e486a217c00000010ca000084b000000000000800000000357c000326800008785c500000002508a75000109e1db85d400003d700000000c20d6b28cd0a225a80000000000000027e00004710000bc6000000017e000002e800000000000eac000000034b2bac0000000edf156448f404800000000002068000261909800000002e589aa000000000000000b70fd73cc000000000000000000056800028c4000000037800000000bb88a90000fc410550c240a800000000000000f2300000000000000000022d2324599391c00011d8ac024d816037307090000000000020b0000fb9276009a00000003bf8c550000000000000000003b100000003f80be913040000000000032d07800000000000000000065116d40002a4c00012d80000a6000000000000000000000000000004e51418000000000008e0a9802f8fe500000000000000000000000000003ed49dc000000026cc6be0ae4e7028a46ef00006e338902bf00000000000000366400000004d8269c00000000003de8fbd3f58000000047401e80002bdc000000092f2304000000055a0fa082a0000000000031628e04000000c3036fc00000006810000b6f00000000000bb004a000000000003b6c00000006120000dc733bcbff00008ef0000000000000000000002594fa240801c7161479f3de09ec3e908b700000001e70e87000090b3a44b1a0d040000000e272b6c80c000000040fc0003a28493000010400000001cec89d0000000000000000000000000f0d1404000224c0000000a1900000001c8463e00d000000009da0700ed6000000000006e700007c22b54fe900007ed0000c1200005460e68eb60000000308800000001b90000000000000000001b300000000b40c7e000077c00000000000db70e20ba40000000031c000091000000010a51058a5a359c00017200003c7c000000000
  | 42 => 0xe40000de80f64d5a323c4503f88d8a342c44025d436734c40c239c88c80000000000000036a00002db8d8642f08501f800000a2c0001c7c36b0e700000000cad1d4467a0000d2f000000000000001c2873e190c000169885b0000b5a00000002b8000000000000000000000000000000000000000000000011740003c047cb27a02552188b070000000000000000000003f242271fa400032fc0000230c1600000000000000000000002b0af9000000038c400031c88f600000000000c1d322000000000000fb800000001b50000c7600000000000000300c00000000000000000000084100000000000000220400026706e00000d550000e77000000000000000aa80471240196000000000000002898a7b000000000000000000000004c26a00000000000b4300001dc000000028b0b7a0000d80000000000000001c9000003e403a18f000000004ab0000aca00010ac000000000006230e4066d04bc3be00006873d1484618248d600000000a5c468000000035500001ce80000000000000000000000000000d2b08a0000129c5cb397800000000000000000296400000000000000000000000000000000000000000000000007d02a3000023b901b19a044908d40000000000409401a00000001bdc00000000000650000000000000000000aa40000000000000000000000000030fb340b40000000000000000024009052994d8220d446c394c0003d40f811b3cd0900000000000000000000000008ce324875e2044037064cd4100000000000c9100005b4000000000009c8385ca3a00000000000000316cb620894a3d000049739880001a6c69c0bc80000000000000040c035436d0588000000000000000000000425000100a0000605378800000000000ef08f300000001a4400005240000000e1b0000b723ff800000000000000000000000000009ca21b400000010c105281210c184430ad858c3b0c00000000003e7800000007f63a3ceec3c8000002fc0000000000000000000008b53dc4000000000000001cd35d400014a4d1c313c0000000000000000000000000000000000008e000000000000000000000000000000005e4000106c0000000286cbde0000e232dd90c615a45e71618fb13d5c0b93da07e638cc89f3c0053d2ce894800000000db00002aa40000000000403000000000000000ee00000fc8000000041e80000000aa00000000281103430d4d1f3d7c0000000eda0000c252ee80000000b220000ceb000000000000000000000006c000000002e0000e5838ac30242900000eec00000000000000000007452721e4da60000000000102e26f00000000000000000000003fa338447037e84ae0000677228ced90000b3b00007ca0000e0b15bc000000000029f000000009490000cc400003e11e880002b680003f146bc06
  | 43 => 0xd930000904000000039b4000000000041b4000000000006dc000000000018d0181000000000003940000000000000000000000000b2300000000000000000017d0000000000000022cc2672f680002d5895c00007a9000006c0000000075cb0c25ec0001938df80f3c3ec000000000000000d3c00011680003ca09f700000003e7000015a0000000072300000141f0463914404640000000167c3ae1988000385853a04c4a21000080d000090d000030700000003fdc00000000000000e051bc43d40000d530000c020000c5a3754f7f40182a60000cb900002ef2aec4fe000000000000000000000000000015090c837a400000000000c74000000000000004df41f0000000000025cc0000000000000000000001293464000401c0c00000bcb000051a02ac0002a7c00000000000000df3000000040740002c1857f000000000000000000000000000000000003f900002c90e7105ec54b00000001d3c0003558000000000000004511db4000356cced000000037b0211254414e25040000000000381c0000120000000000029e800000001e1000000000000000000000000023b0f1881800009d5000000028ac000000000037a8bce3a840000000000000000000004ed00008be1f58f9f035800000007b51eb80000000ce8158c4fb00000000000fdc387c00035a8000000000011802ad00000000000cee3994d9c00005020d10000000000017c052e17303fd3bc80c11a687080cec2e8344cef500000000000000000000000002ae3070e02368063613a47e4029c0000000000254cc792bd8000000091800000000b0c000000000000006930000467000000000008401de4bdd10f00000000af02a380000454ccb0a0c2ab10c00054224a923e9c0000000000000000000f00003798000000000000008390e9c4ee000000015f40001abc8fa29288330000cd100000001cacc3b3f5400024840002938f9137d50461fbc9a0000000022e40000a7c00022944382bf00000000d0a102c6d93d340003d6c0003cd4a94000072915040000000000000084c0000329000000000002370000000000058900002040000ea804dc0000000000000000000780000000000000044a34e000000009c9000065a0000b1900009
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x46250540e045318b5150540e07531885150540e085318b6050540e0853d886050540a0c82590534c540a1a80d9053c8540a0d8614c4208540d04535c44208540e08531096008540aa1811096008540e1043544604c440a8982d906350040a2681d506250730c24641c55248630c25625c46215130c18541c16390530a1b87150604c530a1987150604c530e08549c8604c530c89745c8604c530e08545c8604c530c18541c16388530c18639c26255030c0c631c96155030c18631c16155030c0c639ca6055030d09545c04354830d09435c04354830c19655c04310830d12545c04354430d11545c04354430b418010e5254430b418010d5254430d11435c04354430b04825904354430b10805904354430d12745c04354430d12645c04354430d11645c04354430b118010e4254430d10439c24254430951801cd4254430b118010c4254430b118010d51d0430a518098d5190430a0d8510c6250430c0d7510c6250430a898010c6250430b118010d5150430e04431895150430c0d7510e6290030a898010e6290030b118010d5190030e04439895190030a1686d0d5150030b118010d5110030a0c86551524c030a1486951514c030a1486551514c030e0464949514c030e0464549514c030e1180191514c030b11841c1514c030e10641c1514c030b41821c1514c030c88645ca404c030e1064546404c030d4172546404c03089a86dd1324c030898865d2314c030a188058c635522092487551210862091887551300c220c9074585300c220e1154585300c2208e1811c16310920924815d44310920a888058c4310920c89635c04310920a0c835506250520a24815506250520e20421456010520c0c651d1324c520a2484588510c520a27871905148520a25871905148520e04649cc5148520d05745cc5148520e04645cc5148520d21745c05148520e20645c05148520d41735c05148520c9074585300c120a188454c604c420a0e82d506350020a1a80d506350020a1581150635002081c87591530c020a148454d610c020b09831514048020b21811514048020d08541cd4048020b088454c3048020d097454c3048020d41535c43048020a0e83d906255310a24825526190f10a0c825526390710a0e83d506250710a28845496008710a0c825506350310c90641c1314c310c9074585300c310a24845486148310a0e82d906355210a18835526090a10a0c835506250610a188454c604c610aa0844856008610a0c835526290210a0e82d506350210a148454d610c210ca0741852148210c50655c0434c510c1475191314c110c60655c44248110cc0764c93148110b40854c93148110b80844c93148110c28651d12148110c25651d12108410924875512108410d047454d2108410c19651d1300c01091887551300c010d0874549300c010
  | 1 => 0x26e4e80070334209cca0025271b60a2e15410ca56294c632610fd22a7169a800a2002dc90cc060014cb43a000000064000e00063800f8be5c8018a002c1ac84a95708020c36aab5c2ba1806950bf68204007934a3c62cb2005012444591c0a3c2480000a429339344b6b86dca83341ed88864f348a02f0e0a8e4da10989c41d69b1936df5e17c00c014a244ac147105562c67b60000058359c8b20900166660fa28006144078f4dc140081c760a82d320021b99c67800000006d000e5924509a7d2a000015c0e60461750ab803001309757b78566c3aaf500560c14c0000412407a3b3221c07038000002098200c0e1c01c0a1c310000013060140000028140614001783810030000a110002802050000800240005c04090180006010003c0000000005809000140001020140a0405098120400024121203800000b915811c15310c428a9801c56210c42a188054d6010c42924815c8435444290e82dd16094e41d05539c75210a4190d8794c5210a41d0a535c05210a41b088054c43d4941a0d8694c4314941b05819cc431494190c835d26014941c49735806014941c61715806014941a268198c52d0941c0e7314a61d0941a2685d886150941a8583d906250441a248158862552318d1801c56210d31a18805944310931984815c84310931a858210d6110931a29801506250431b0582151414c431b1180151414c431d04541c9414c431c19635c06315121a268198c6255021c0e7318a6155021e05535096110821c25659c64310821e055454d6110821a258510d6110821a0d8598c4290421c0d7598c4290421c86635c4429042182c87551620c421a8484589310c421e0554589310c421a0c865515348421c84645ce41484218a58719231484218a686dd13248421d22545c44254021d21545c44254021d42535c44254021d41535c44254021928879512154021928875512154021d087494d2154021d087454d2154021961811c94354021d21425c44254021b08835904254021b20815904254021b228190c4254021d22745c44254021d22645c44254021d21645c44254021d22435c44254021d20435c44254021d0a7310a4154021b218110a415402192a87d094154021b21811084154021928845c83154021d41724c43154021d21811d12154021d20749052154021b41839052154021b21848c52154021d20748c52154021d20744c52154021a268194c6250740c0e7318a5150740aa1811096008740b058114c4394a4090e83dd16194a40a0e86d4c4354a40b088050c4354a40c24641c55248640a6181949600864090c825d26114d40c45725846114d40c51615c06114d40c18539c262d0d40c0c539ca60d0d40a1a85d8c6050d40d08535c2521094090e87d4d5210940d07531c55210940c18539c262d0540c0c539ca60d0540a0c835d
  | 2 => 0x978000026a511a0d130884692000dcee002c80000e01703c9ebb389bc6a7e23000b4b52a25954176a131a2b149ad800033f99d4673000007400000d800046e96c00d9001f4224e000586800500919a191f284a
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x41c6ac8ba39880612602ad92000e3cc2400ab80c80200d0202803e79630050004000458104110b908c8900a9ac021885121902057210d5110a3032040ae42188498d40640541c9414c431a02cacc6b88852084320498551624c431086a0126b22e2212a010e409cd8110a4154021a804a2e498862a80439007460e4148550086243303a46290aa010d01658535c44208540d0029b02212c010a814099715172181314c2a0124b22e021aa2186025d58010c6250430b00c8086312a2a0861809756004398a400c2c032021cc4a8c8018484660641c1514c030d0032304382a298061c00645c951901300c28212eaa2c298061104a06448058c4310920a02cb8c8b98a290a41421971917014521483800c8b9ae028a4290540644541cd40480208844c2e8a9860900415009454d710c120083080ec42a6498a40886201d8844c93148110
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 40
  | 6 => 1844
  | 5 => 9193
  | 4 => 4301
  | 3 => 231
  | 2 => 32
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
  | 5 => packedAt gbK5 (392230+((h/3064+packedAt gbK5 (349334+(h % 3064)*14) 14) % 14682)*15) 15
  | 4 => packedAt gbK4 (230811+((h/1433+packedAt gbK4 (210749+(h % 1433)*14) 14) % 9141)*14) 14
  | 3 => packedAt gbK3 (14553+((h/77+packedAt gbK3 (13860+(h % 77)*9) 9) % 278)*9) 9
  | 2 => packedAt gbK2 (2332+((h/10+packedAt gbK2 (2272+(h % 10)*6) 6) % 42)*6) 6
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfe07ffc1ffffe383e3c7f1ff1fffc0f819f3f3
  | 1 => 0x1ff87ffe0fc7fffc03f8fe3fe381fff8e63c9f
  | 2 => 0x1fff83fff007fc7ffc00ffc7fc01ff0707cf1c
  | 3 => 0xe00003fffff8007fffff0007fffe0007f80fe0
  | 4 => 0xfffffc000000007ffffffff800000007fff000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x4290084442810400a081304904a4425008d131
  | 1 => 0x84221088240a401401484212210894a0622486
  | 2 => 0x48512914819480a96400948548152a13054b18
  | 3 => 0x816552212900c94e4a52000692580c25b00ec0
  | 4 => 0x11866039ce27127393a4e920006030c6dfb000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 31 gbPos gbNeg, 0xfee8eac8fee8eac8fee8eac8fee8eac8fee8eac8fee8eac8fee8eac8fee8eac8fee8eac8fee8eac8fee8eac8fee8eac8fee8eac8fee8eac8fee8eac8fee8eac8, gbN, gbR, (fun _ _ => 0), gbI⟩
end PEqualNP.Outside.L_meta_12881
namespace PEqualNP.Outside.L_meta_12881
open PEqualNP.Outside.L_meta_12881.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 32 := block_range (n:=32) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 32 := bgb_2_0
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
theorem bgb_3_224 : Interval gbAtlas 3 224 7 := block_range (n:=7) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 231 := (concat (concat (concat bgb_3_0 bgb_3_32) (concat bgb_3_64 bgb_3_96)) (concat (concat bgb_3_128 bgb_3_160) (concat bgb_3_192 bgb_3_224)))
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
theorem bgb_4_4288 : Interval gbAtlas 4 4288 13 := block_range (n:=13) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 4301 := (concat (concat (concat (concat (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96)) (concat (concat bgb_4_128 bgb_4_160) (concat bgb_4_192 bgb_4_224))) (concat (concat (concat bgb_4_256 bgb_4_288) (concat bgb_4_320 bgb_4_352)) (concat (concat bgb_4_384 bgb_4_416) (concat bgb_4_448 bgb_4_480)))) (concat (concat (concat (concat bgb_4_512 bgb_4_544) (concat bgb_4_576 bgb_4_608)) (concat (concat bgb_4_640 bgb_4_672) (concat bgb_4_704 bgb_4_736))) (concat (concat (concat bgb_4_768 bgb_4_800) (concat bgb_4_832 bgb_4_864)) (concat (concat bgb_4_896 bgb_4_928) (concat bgb_4_960 (concat bgb_4_992 bgb_4_1024)))))) (concat (concat (concat (concat (concat bgb_4_1056 bgb_4_1088) (concat bgb_4_1120 bgb_4_1152)) (concat (concat bgb_4_1184 bgb_4_1216) (concat bgb_4_1248 bgb_4_1280))) (concat (concat (concat bgb_4_1312 bgb_4_1344) (concat bgb_4_1376 bgb_4_1408)) (concat (concat bgb_4_1440 bgb_4_1472) (concat bgb_4_1504 (concat bgb_4_1536 bgb_4_1568))))) (concat (concat (concat (concat bgb_4_1600 bgb_4_1632) (concat bgb_4_1664 bgb_4_1696)) (concat (concat bgb_4_1728 bgb_4_1760) (concat bgb_4_1792 bgb_4_1824))) (concat (concat (concat bgb_4_1856 bgb_4_1888) (concat bgb_4_1920 bgb_4_1952)) (concat (concat bgb_4_1984 bgb_4_2016) (concat bgb_4_2048 (concat bgb_4_2080 bgb_4_2112))))))) (concat (concat (concat (concat (concat (concat bgb_4_2144 bgb_4_2176) (concat bgb_4_2208 bgb_4_2240)) (concat (concat bgb_4_2272 bgb_4_2304) (concat bgb_4_2336 bgb_4_2368))) (concat (concat (concat bgb_4_2400 bgb_4_2432) (concat bgb_4_2464 bgb_4_2496)) (concat (concat bgb_4_2528 bgb_4_2560) (concat bgb_4_2592 (concat bgb_4_2624 bgb_4_2656))))) (concat (concat (concat (concat bgb_4_2688 bgb_4_2720) (concat bgb_4_2752 bgb_4_2784)) (concat (concat bgb_4_2816 bgb_4_2848) (concat bgb_4_2880 bgb_4_2912))) (concat (concat (concat bgb_4_2944 bgb_4_2976) (concat bgb_4_3008 bgb_4_3040)) (concat (concat bgb_4_3072 bgb_4_3104) (concat bgb_4_3136 (concat bgb_4_3168 bgb_4_3200)))))) (concat (concat (concat (concat (concat bgb_4_3232 bgb_4_3264) (concat bgb_4_3296 bgb_4_3328)) (concat (concat bgb_4_3360 bgb_4_3392) (concat bgb_4_3424 bgb_4_3456))) (concat (concat (concat bgb_4_3488 bgb_4_3520) (concat bgb_4_3552 bgb_4_3584)) (concat (concat bgb_4_3616 bgb_4_3648) (concat bgb_4_3680 (concat bgb_4_3712 bgb_4_3744))))) (concat (concat (concat (concat bgb_4_3776 bgb_4_3808) (concat bgb_4_3840 bgb_4_3872)) (concat (concat bgb_4_3904 bgb_4_3936) (concat bgb_4_3968 bgb_4_4000))) (concat (concat (concat bgb_4_4032 bgb_4_4064) (concat bgb_4_4096 bgb_4_4128)) (concat (concat bgb_4_4160 bgb_4_4192) (concat bgb_4_4224 (concat bgb_4_4256 bgb_4_4288))))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 5, 21)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 5 zero,inputs.getD 4 zero]
def fullWord : Sig := 0xfee8eac8eac8eac8fee8eac8eac8eac8fee8eac8eac8eac8fee8eac8eac8eac8fee8eac8eac8eac8fee8eac8eac8eac8fee8eac8eac8eac8fee8eac8eac8eac8
theorem fullBound (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have low := boundgb certgb
  have lift := lift_ok (u:=true) (ms:=fixRows 0 32) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 5 zero,21,53)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 5 zero,21,53)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276677320 * 2 ^ 32 + 3939035848) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_12881.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,2]⟩,⟨.or,[0,3]⟩,⟨.or,[1,2]⟩,⟨.and,[1,6]⟩,⟨.and,[1,9]⟩,⟨.and,[0,3]⟩,⟨.and,[4,8]⟩,⟨.and,[5,12]⟩,⟨.or,[11,13]⟩,⟨.and,[7,14]⟩,⟨.or,[10,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276677320 * 2 ^ 32 + 3939035848) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276677320 * 2 ^ 32 + 3939035848) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_12881

open PEqualNP.Outside.L_meta_12881 in
theorem PEqualNP.Outside.L_meta_12881 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276677320 * 2 ^ 32 + 3939035848) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276677320 * 2 ^ 32 + 3939035848) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound allgb)
