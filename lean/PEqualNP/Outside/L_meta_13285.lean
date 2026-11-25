import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_13285.Model
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


end PEqualNP.Outside.L_meta_13285.Model

namespace PEqualNP.Outside.L_meta_13285
open PEqualNP.Outside.L_meta_13285.Model
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

def SBf (j : Nat) : Nat := [3, 4, 4, 2, 4, 7].getD j 0

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

end PEqualNP.Outside.L_meta_13285

namespace PEqualNP.Outside.L_meta_13285
open PEqualNP.Outside.L_meta_13285.Model
def s0K2 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 2 => 1
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt s0K2 (i*4) 4
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt s0K2 (5+((h/1+packedAt s0K2 (4+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffffffffffffffffffffffffffffffffffff
  | 3 => 0xffffffffffffffffffffffffffffffffffffff
  | 4 => 0xffffffffffffffffffffffffffffffffffffff
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffff84b7
  | 2 => 0xffffffffffffffffffffffffffffffffff895b
  | 3 => 0xffffffffffffffffffffffffffffffffff926d
  | 4 => 0x238e
  | _ => 0
def s0Atlas : Atlas := ⟨2,rawDecor 30 s0Pos s0Neg, 0xc0000000c0000000c0000000c0000000c0000000c0000000c0000000c0000000c0000000c0000000c0000000c0000000c0000000c0000000c0000000c0000000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_13285
namespace PEqualNP.Outside.L_meta_13285
open PEqualNP.Outside.L_meta_13285.Model
def s1K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s1K3 (i*5) 5
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s1K3 (6+((h/1+packedAt s1K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xfff01fffe03ffffffc07ff81ffe07ffff38e3f
  | 3 => 0xfffe01fffc03fc07ff81ffe07ff81f01cf3cc
  | 4 => 0xf000001fffffc0007fffe00007fffe001f03f0
  | 5 => 0xffffffe0000000007ffffffff80000001ffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x12108144220484901058a2a288a8a2154534d5
  | 2 => 0xa4aa528a51a9292a2e055511554455aa928a2a
  | 3 => 0x88c954d294a3b20aceac19d4467511c0d8d34c
  | 4 => 0xce8d9b1d193223b377367061879e78831f03b0
  | 5 => 0xf0e1c1e1e3c3c3c7bc79e79e418610c1fec00
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xaaa0aaa0aaa0a0a0aaa0aaa0aaa0a0a0aaa0aaa0aaa0a0a0aaa0aaa0aaa0a0a0aaa0aaa0aaa0a0a0aaa0aaa0aaa0a0a0aaa0aaa0aaa0a0a0aaa0aaa0aaa0a0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_13285
namespace PEqualNP.Outside.L_meta_13285
open PEqualNP.Outside.L_meta_13285.Model
def s2K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s2K3 (i*5) 5
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s2K3 (6+((h/1+packedAt s2K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 1 => 0xfff01fffe03ffffffc07ff81ffe07ffff38e3f
  | 3 => 0xfffe01fffc03fc07ff81ffe07ff81f01cf3cc
  | 4 => 0xf000001fffffc0007fffe00007fffe001f03f0
  | 5 => 0xffffffe0000000007ffffffff80000001ffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x12108144220484901058a2a288a8a2154534d5
  | 1 => 0xa4aa528a51a9292a2e055511554455aa928a2a
  | 3 => 0x88c954d294a3b20aceac19d4467511c0d8d34c
  | 4 => 0xce8d9b1d193223b377367061879e78831f03b0
  | 5 => 0xf0e1c1e1e3c3c3c7bc79e79e418610c1fec00
  | _ => 0
def s2Atlas : Atlas := ⟨3,rawDecor 59 s2Pos s2Neg, 0xaa88aa88aa888888aa88aa88aa888888aa88aa88aa888888aa88aa88aa888888aa88aa88aa888888aa88aa88aa888888aa88aa88aa888888aa88aa88aa888888, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_13285
namespace PEqualNP.Outside.L_meta_13285
open PEqualNP.Outside.L_meta_13285.Model
def s3K1 : Nat → Nat
  | 0 => 0x7
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 1 => 1
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 1 => packedAt s3K1 (i*3) 3
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 1 => packedAt s3K1 (4+((h/1+packedAt s3K1 (3+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 1 => 0xffffffffffffffffffffffffffffffffffde73
  | 2 => 0x6f9c
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffff8205
  | 1 => 0x2552
  | 2 => 0x1958
  | _ => 0
def s3Atlas : Atlas := ⟨1,rawDecor 7 s3Pos s3Neg, 0xa8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_13285
namespace PEqualNP.Outside.L_meta_13285
open PEqualNP.Outside.L_meta_13285.Model
def s4K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s4K3 (i*5) 5
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s4K3 (6+((h/1+packedAt s4K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 1 => 0x7f01fff80fffe07fe07e0f83ff07fe07f44e73
  | 2 => 0x7ffe03fff01fff81ff800ffc1ff83ff818739c
  | 3 => 0x800003ffffe00001fffff0001fffc0001f83e0
  | 5 => 0xfffffc0000000001ffffffffe00000001ffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x108100881024000028a1104220842a28194a5
  | 1 => 0x2aa529946a548ae8f0548aa35546b415544a52
  | 2 => 0x4c954aa528d91a2b75410ce919d23950586318
  | 3 => 0x68d9b3464c91d34db9e7a8421ee710619e83e0
  | 5 => 0x70e1c3878f1e1c71de79cf73908421861f7c00
  | _ => 0
def s4Atlas : Atlas := ⟨3,rawDecor 47 s4Pos s4Neg, 0xaaa8aaa8a8a8a8a8aaa8aaa8a8a8a8a8aaa8aaa8a8a8a8a8aaa8aaa8a8a8a8a8aaa8aaa8a8a8a8a8aaa8aaa8a8a8a8a8aaa8aaa8a8a8a8a8aaa8aaa8a8a8a8a8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_13285
namespace PEqualNP.Outside.L_meta_13285
open PEqualNP.Outside.L_meta_13285.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x800f003a00119003932c56a0b00008d0804a911004e4948054001931420e0d36250070a5c81a3e54c0b22507810c00603106408003341142288149ff43df43fe43be43fd43fc43bc43dc439c43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0xf41026008fa6a11820000702914f200051041a35239a000641c8001e000e8a434630d84c221200064000000000ae4e000c80200000f0e27e171e07e18000ace60000024a000349280038001246c001680c006018800ea1f00000b60037800ee4d14000006d0000000002e0000025000002e7c3a000dc0b020b0ec5f060584c0e1b93c66591f158387f0a91028611d0bc40512a9c0001e40178e46221994ce5a12108a6220009ca46610800ba48201b0f63b1e918a80003000604b358d054580203870280000d8b00098082818000838300000a85028009898c00818110000083918200148100800003805794e439f29c871e5390f3a8621cf94c43cf298875e5410f3ca821e7d4843cf290879d5210f38a421e7d4443cf288879d5110f38a221e7d4043cf280879d5010f38a021e710f42af29c855d5390b3887215d94642baa8c855f5350ab8a6a16710d42ce218859c43cca7ca9194f55232ce21c6576518caeaa3194fd51329e2a2659c434cb3886196710f41af29c835d53907388720db94a41b6a94835f53506b8a6a0e710d41ce218839c43cc67ca918cf55231ce21c636e528c6daa518cfd51319e2a2639c434c7388618cf953219eaa6435e53c86baa790e710f219f2a4433d54886bca710d754e21ce21c439c43487388610f948421ce21e815e53902baa7206710e40afa9a815c535033886a05bd4940b6292817751502e8a2a06710c40ce21e613e548c27aa9186710e309faa2613c544c33886985bd4930b62926177514c2e8a2986710c30ce21e419c438827ea8904f15120afa9a415c534833886905dd4520ba28a413e540827aa8105794c20aea98419c43082eca2105d54420ce21e219c438427ea8884f15110afa9a215c534433886885bd4910b6292213e540427aa8085794c10aea98219c43042dca4085b54810
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x1b81800000000000091f911815000000001a00109d1680141e1aa0000d800000170311960a0019208e8000210f801f050019938980000d101c000000120881060294a1958b1e87078000059280001b00000c8f0c0a800008009c849786801302000400000000000000188000038000000b9d8000000e00020814002000c080000020100380000234101a59875210e9561d4843a59865210e956194843c35485210e8e62d4443a358b5110e8e6294443a358a5110f155114443a3d895010e8c6254043a5d855010e946154043a39885010e8d6214043a59845010e956114043c510e5190b144354642c510e518cb144354632c310e529070c4354a41c310e528c70c4354a318718d54c861c6454f2187d9443c861d6510f218718d548861c6454e2187d94438861d6510e21e110d210870c43d4940c310c525031443d4540c510c515021c6315130c310f524c30c4314930c510f514c31443145308798f544821e64d4d2087994434821c6510d20c510f514831443145208718d540821c6454c2087d94430821d6510c20c510e510831443544208798f544421e64d4d1087994434421c6510d10c310f524430c43149108718d540421c6454c1087d94430421d6510c10c310e520430c4354810
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 45
  | 4 => 129
  | 3 => 68
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (i*5) 5
  | 5 => packedAt s5K5 (i*16) 16
  | 4 => packedAt s5K4 (i*27) 27
  | 3 => packedAt s5K3 (i*38) 38
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (6+((h/1+packedAt s5K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s5K5 (810+((h/15+packedAt s5K5 (720+(h % 15)*6) 6) % 55)*7) 7
  | 4 => packedAt s5K4 (3827+((h/43+packedAt s5K4 (3483+(h % 43)*8) 8) % 170)*9) 9
  | 3 => packedAt s5K3 (2738+((h/22+packedAt s5K3 (2584+(h % 22)*7) 7) % 118)*8) 8
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfffffffffffffffc0fffffffffffffff0fffff
  | 1 => 0x7f03ffe07ffc0ffff07c1e0ff83ff03ff44e73
  | 2 => 0x7ffc0fff81fff03fff801ff07fc1ffc0f8739c
  | 3 => 0x80000ffffe00003fffffe0007ffe0000ff83e0
  | 4 => 0xfffff0000000003fffffffff80000000fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x11040241048000002942410904215140194a5
  | 1 => 0x2a48a64324915d1cb0290a8d2a35a0aa744a52
  | 2 => 0x4c292a890d23456d550213a44e91ca82b86318
  | 3 => 0x68b2cd12483a69b669cf41087738830cde83e0
  | 4 => 0x70c30e1c71c38e3b8e739dce04210c30ef7c00
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xeaa8a8a8eaa8a8a8eaa8a8a8eaa8a8a8eaa8a8a8eaa8a8a8eaa8a8a8eaa8a8a8eaa8a8a8eaa8a8a8eaa8a8a8eaa8a8a8eaa8a8a8eaa8a8a8eaa8a8a8eaa8a8a8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_13285
namespace PEqualNP.Outside.L_meta_13285
open PEqualNP.Outside.L_meta_13285.Model
def gbK8 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x58304c001a188e004e0a000076460000000048020000441e00820c4066747c00001486420050008800002e6e0052005e000000000070343c002a1c32560462008a647e003e240000803800006812006a00000000725c005400000000106c3a786000004a7a0e160600365a00262c000028008420000000000022088c00000000010081000c00300081820404100000800000ffd50037f5400ff95003fd54005f55003fc5400ffd4c03fe53005f94c03fd5300ff14c037c53007fd0c01fe43006f90c01fd43007f10c01bc4300ffd48037f5200ff94803fd52005f54803fc52007fd0801fe42007f50801fc42007fcc801fe32007f4c801fc3200ffd44037f5100ff94403fd51005f54403fc51007fd0401fe41007f50401fc41007fcc401fe31007f4c401fc31007fc8401fe21007f48401fc2100ffd4003fe50005f94003fd5000ff140037c50007fd0001fe40007f50001fc40007fcc001fe30007f4c001fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x204000ef590200057ac810002fc640800dbfaa04000df55020005fec610002fe6308001ef3184000b798c20005fac610003dd63080016eb184000bf18c20006fca61001b7c5308001df2184000ef10c20045fcc41001b7f5208001bea904000fbd0820007d88410003ef3208001f61904000bf98420007ecc210002f661080017eb084000fd58420005eac21001b7f5108001bea884000fb88420007d8421001efe6008001bf2804006df14020007de4010003fa2008001f69004000fe48020025fecb88006fe65c4009bf32e20019f99710025facb880037d65c40013eb2e2001bf19710005fec988002fe64c40017eb262000bf19310026fea9880037d54c40017fb1e2000bf98f10005fac788002fc63c4001bf29e2004df14f100077c8788003bc43c40017fb162000bf98b10005fac588002fc62c4009bfa962000df54b10026fea3880037d51c4001fb10e2000fd48710006fca1880137c50c40077fb2c2000dfd9610004fecb08006fe65840077eb2c2001bf1961001ef8cb080067c65840017fb242000bf99210005fac908002fc6484007bfaa42000df55210005fec708002fe63840017eb1c2000bf18e10006fca70800f7c5384001df21c2000ef10e10005fec508002fe62840017eb142000bf18a1001efea5080037d528400b7eb0c2003dfd4610006faa308003f74184001fa20c2000fdcc610007e86308003f72184001fa10c2002bf98210006fca10800f7c5084001fb8842000fec421002dfeca880037f65440013fb2a2001bf9951002dfaca88006fc654400bbe32a20019f19510005fec888003bf64440015fb222000bf99110005fac888002fc6444001de3222000af1911002efea8880037d54440017fb1a2000f7d8d10005bec688002fe63440017eb1a2000bf18d10007b8c688002dc6344001bf29a2005df14d100077c8688003bc43440017fb122000fbd8910005dec488002fe62440017eb122000bf18910007d8c488002ec624400bbfa922000df5491002efea2880037d5144001fb10a2000fd48510006fca0880177c5044001fd8822000fd84110015feca08006fe6504005bf32820019f99410015faca080037d65040013eb282001bf19410005fec808002fe6404001df3202000af99010005fac808003bd64040015eb202000bf19010016fea8080037d54040017fb182000bf98c10007bcc608002de63040017eb182000f758c10005bac608002fc6304001bf2982002df14c100077c8608003bc43040017fb102000bf98810007dcc408002ee62040017eb102000fb58810005dac408002fc6204005bfa902000df54810025fcc20800b7f5104001bea882000fdd0410007e88208003f73104001fa1882000fdc8410007e8420800efe6004001bf2802002df14010007ee2008003fa1004001fa8802000fe44010
  | 1 => 0x37e508c017be2846000f7cc230007f66118036ff654c001bfb2a60009fd953000dfcca98036fd654c0037e32a600ddf1953000cf8ca98002ff644c001dfb226000afd9130005fcc898002fd644c0017e3226000ef1913000578c8980377f544c001beaa26000df94d3006ef8a698003be434c001de21a6000bfd8930007dec498002ef624c0017e3126000fb18930005d8c4980377f524c001bea926000f7cc930007ba6498002ff614c001fbb0a6000bdd8530005f8c298003f4614c0017a30a600ddfd4530006faa298003df314c001ee98a6000df9413006ef8a098003fb304c001ef182600abfd9430006feca180027f650c0037f328600abf5943000df8ca1802b7c650c0033e3286000bfd9030005fcc818002fd640c0017e320600adfd5030006faa818032fe630c001bf298600adf14c30007be8618003be430c001de2186000f710c30007388618002fe620c0017eb10600adfd4830006faa418003de320c001ee1906000bf98430005fac21802b7f510c001bea886000f78c430007b8621802efe600c001bf280600adf14030007be6018003fa300c001ee9806000fe4c030045fecb90006fe65c8011bf32e40019f99720045facb900037d65c80013eb2e4001bf19720005fec990002fe64c80017eb264000bf19320046fea9900037d54c80017fb1e4000bf98f20005fac790002fc63c8001bf29e4008df14f200077c8790003bc43c8011bfa964000df54b20005fcc390002fd61c8011bfa8e4000df54720007de4390003ed21c8001bf2864008df1432003dfecb100037f65880013fb2c4001bf9962003dfacb10006fc658800fbe32c40019f19620005fec910002fe64880017eb244000bf1922003efea9100037d54880017fb1c4000bf98e20005fac710002fc6388001bf29c4007df14e200077c8710003bc43880137eb144007dfd4a20006faa510003ef4288001f62144000fbcca20007d86510002fe61880017eb0c4007dfd4620006faa310003ee2188001f610c4006bf98220006fca11001f7c5088001f79044000fec822004dfeca900037f65480013fb2a4001bf9952004dfaca90006fc6548013be32a40019f19520005fec890003bf64480015fb224000bf99120005fac890002fc6448001de3224000af1912004efea8900037d54480017fb1a4000f7d8d20005bec690002fe63480017eb1a4000bf18d20007b8c690002dc6348001bf29a4009df14d200077c8690003bc4348013bfa924000df54920005fec290003f761480017bb0a4000bf18520007e8c290002f46148013bfa8a4000df54520007de4290003ed2148001bf2824009df14120007f64090003ee204800d7fb284001bf99420036fcca100067e650800d7eb284000df59420004faca10006fc65080017fb204000bf990200077cc810002be64080017eb
  | 2 => 0x50085fecba0006fe65d0021bf32e80019f99740085facba00037d65d00013eb2e8001bf19740086fea9a0043be54d0001beaa68010ef553400067aa9a0002fe63d00017eb1e8000df94f40086f8a7a0003be43d0001de21e8000bf98b40005fac5a00437f52d0001bea968000efd0b400077a85a0002fe61d00017eb0e8010dfd4740006faa3a0003bf41d0001dea0e8000df94340086f8a1a003eff6590001bfb2c80009fd964000dfccb2003efd65900037e32c800fdf1964000cf8cb20046fd649001fbfaa48000df55240005fcc720002fd6390001bf29c800fdf14e400077c8720003bc43900017f3148000bf58a4007efea5200037d5290001df2148000ef10a40005fcc320002fd619001fbfa8c8000df546400077c8320003bc419001d7f3048000df9424007ef8a120003bf4090001fda048011bfd9540006fecaa00027f65500037f32a8011bf5954000df8caa00477c65500033e32a8011dfd514008f7ca8a00037d5450023deaa28000cf55140005fec6a0003df63500016fb1a8000bf18d40007b8c6a0002dc6350001bf29a8011df14d400077c86a0003bc43500017fb128000fbd8940005dec4a0002fc6250001f63128000bb1894008efea4a00037d5250001dfa128000ef50940005fec2a0003f761500017bb0a8000bf18540007e8c2a0002f46150023bfa8a8000df545400077e82a0003bd4150001bf2828011df14140007f680a0003be405001d7fb288001bf99440076fcca200067e651001d7eb288000df59440004faca20006fc65100217f320800edfd5040006faa820002fe63100017eb188000df94c40076f8a620003be4310001de2188000bf98840005fac42003b7f5210001bea908000ef90840007788420002fe61100017eb08800edfd4440006faa220003be4110001de208800fbf98040006fca02003b7c5010001dfa008000fe900400077a8020003f940100197fb2e6001bf99730066fccb980067e65cc0197eb2e6000df59730004facb98006fc65cc0017fb266000bf99330005fac998002fc64cc019bfaa66000df55330006fca7980337c53cc001df21e6000ef10f30005fcc598002fd62cc019bfa966000df54b30007be6598003dd32cc0017f30e6000bf58730066fea3980037d51cc001ef98e6000f74c730006fca1980337c50cc0177fb2c6001bf9963005efccb180067e658c0177eb2c6000df59630004facb18006fc658c0017fb246000bf992300077cc918002be648c0017eb246000ef592300057ac918002fc648c017bfaa46000df5523006dfac7180037e538c017be29c6000f7d0e300077c8718003bc438c001ee21c6000e710e30005fcc518002fd628c017bfa946000df54a30007bc6518003dc328c0017f30c6000bf5863005efea3180037d518c001ef18c6000f70c630055fcc11800
  | 3 => 0xf9906200f74c8310bdfcc21885b7f510c401bea886200f7cc431007ec6218803dd310c401fa9886200bf98031005fac01885b7c500c4297fb2e4201bf997210a6fccb908067e65c84297eb2e4200df59721004facb90806fc65c84017fb264200bf993210077cc990802be64c84017eb264200ef593210057ac990802fc64c8429bfaa64200df55321005fec790802fe63c8401ef31e4200b798f21005fac790803dd63c84016eb1e4200bf18f21006fca7908537c53c8401df21e4200ef10f210a6fea5908037d52c8401f7a164200fb10b21007de6590803ec32c8429bfa8e4200df54721005fcc190802fd60c8429be2864213bfd962100dfccb1084f7e65884033f32c4213bf59621006facb108027d65884037e32c4200bfd9221005fcc910803be64884015f3244200bf592210077ac910802bd64884017e3244213dfd5221006faa910802ff63884017f31c4200f798e21005bcc710802fd6388401eeb1c4200b758e21005f8c7108037e5388427be29c4200ef90e21007788710856fd6288427bfa944200df54a21095fcc31084f7f5188401bea8c4200fdd0621007e88310803f73188401fa18c4200fbc8621007ee4310802fe60884017eb044213df142210adfeca90806fe654842bbf32a42019f995210adfaca908037d65484013eb2a4201bf19521005fec890802fe64484017eb224200bf191210aefea8908037d54484017fb1a4200bf98d21005fac690802fc6348401bf29a4215df14d210077c8690803bc434842bbfa924200df54921007de8490803ec4248401f79924200fb0c9210aefea2908037d5148401fba0a4200fd10521007ee6290803f43148401fb90a4200fb88521005fec090802fc604842bbe2824212bfd942100dfcca1084b7e65084033f3284212bf59421006faca108027d65084037e3284200bfd9021005fcc810802fd64084017e3204212dfd5021006faa810802ff63084017f3184200bf58c21005f8c6108037e5308425be2984200ef90c21007788610852fe6208425bfa904200df5482109dfcc21084b7f5108401bea884200fbc8421007ec4210803ed2108401fa9084200f948421005fcc010802fd6008425be2804200dfd9250006fcc9280037d64940013eb24a000df19250006fec7280037e63940013f31ca000df58e50006f8c7280037f4394001bf21ca000cf90e50006fa87280037c43940019e21ca000dfd8a50006fcc5280037d62940013eb14a000df18a50006fe85280037e4294001bea14a000df10a50006fe65280037e3294001be994a000df0ca50006fec3280037e6194001beb0ca0009f58650006f8c3280037f4194001bf20ca000df50650006f883280037f3194001bf18ca000df4c650006f863280037f2194001bf10ca000df48650006f843280077e60940033f304a001de982
  | 4 => 0x8037e5390437be29c8200ef90e41007788720802fe6290401f73148200bb98a41005fac520803ed629040176b14821bdfd4a41006faa520803bf4290401dea14821abf986410defea3208037d5190401dfa0c8200fdd0641005fcc120802fd6090437be284821dbfd954100dfccaa08777e65504033f32a821dbf59541006facaa08027d65504037e32a821ddfd5141006faa8a0802ff63504017e31a8200df94d410eef8a6a0803be4350401de21a8200bfd8941005f8c4a08777f5250401bea928200ef909410077884a08777f5150401bea8a8200fdd05410077c82a0802ff60504017e302821ddf141410d5feca20806fe6510435bf32882019f994410d5faca208037d65104013eb288201bf194410e5fcc82086b7f5410435df2a08200df550410d77aa8208033d54104017f3188200bf58c41006fca62086b7c5310401df2188200ef10c41005fcc420802fd6210435bfa908200df548410077e8420803bd42104377f308821adfd4441006faa220803bf4110401fb2088200ef50441007ea8220802fe60104017eb00821adf140410c5fecb988037f65cc4013fb2e6201bf997310c5facb98806fc65cc431be32e62019f19731005fec998802fe64cc4017eb266200bf193310c6fea9988037d54cc401bf29e6218df14f31007be8798803be43cc401de21e6200f710f31007388798802fe62cc4017eb166218dfd4b31006faa598803de32cc401ee1966218dfd4731006faa398802fe60cc4017eb066218df143310bdfecb18806fe658c42fbf32c62019f996310bdfacb188037d658c4013eb2c6201bf19631005fec918802fe648c401df3246200af99231005fac918803bd648c4015eb246200bf192310befea9188037d548c4337eb1c6200df94e310bef8a718803be438c401de21c6200bf98a31007dcc518802ee628c4017eb146200fb58a31005dac51885f7f528c401bea946200f7cca31007ba651885afe618c42fbfa8c6200df54631007be6318803f7318c4017f3046200bf582310bef8a118866ff654c401bfb2a62009fd953100dfcca98866fd654c4037e32a6219df1953100cf8ca98802ff644c401dfb226200afd9131005fcc898802fd644c4017e3226200ef1913100578c8988677f544c401beaa26200df94d310cef8a698803df434c401df21a6200ef10d31007b886988039c434c4017fb126200bf189310cefea4988037d524c401ef1926200f70c9310cefea2988037d514c401fb98a6200f78c531005fec098802fc604c433be2826216bfd943100dfcca1885b7e650c4033f3286216bf59431006faca188027d650c4037e3286200bfd9031005fcc818802fd640c4017e3206216dfd5031006faa818862fe630c401bf2986216df14c310077c8618803bc430c4017f3106200bf588310b6fea4188037d520c401e
  | 5 => 0x4442005fcc021002fd6010845be2808420bfd9732006fecb990027f65cc8037f32e6420bf5973200df8cb990837c65cc8033e32e6400bfd9332005fcc999002fd64cc8017e3266420dfd5332006faa9990037e53cc841be29e6400f7d0f320077c8799003bc43cc801ee21e6400e710f32106fea5990037d52cc8017f30e6400bf58732106fea399002fe60cc8017eb066420df143320fdfecb19006fe658c83fbf32c64019f996320fdfacb190037d658c8013eb2c6401bf19632005fec919002fe648c801df3246400af99232005fac919003bd648c8015eb246400bf192320fefea9190037d548c8437eb1c6400df94e320fef8a719003be438c801de21c641ebf98a320fefea5190037d528c801ef9946400fbcca32005fcc319003f6618c8017b30c6400bf58632007eac319002f5618c83fbfa8c6400bf98232005fac11907f7c508c8437fb2a6400dfd9532004feca99006fe654c8437eb2a6401bf1953210ef8ca990067c654c8017fb226400efd91320057ec899002fe644c8017eb226400bf1913200778c899002bc644c843bfaa26400df55132006fca6990877c534c801efa1a6400ef90d32007788699003dc434c801ce21a6421dfd4932006faa499003ef324c801ef1926400bfd8532005f8c2990877f514c8017fb026400bf1813210ef8a09907aff650c8037f328641edf9943200cfcca1907afd650c801beb2864009f5943200df8ca19002ff640c8017f3206400bf59032005f8c81907b7f540c801beaa06420bf98c32006fca61907b7c530c801df2186400ef10c320fdfcc41907b7f520c801bea906400f7cc832007dc6419003dd320c801f69906400bf98432005fac21907b7f510c8017f3006400bf580320f6f8a0190037f64544013fb22a200df99151006fac8a88037c6454401bfb1aa200df98d51006fac6a88037c63544013e31aa200dfd0d51006fc86a88033e4354401bea1aa200df10d510067886a88037f62544013fb12a200df98951006fac4a88037c6254401bfa12a200df90951006fa84a88037c4254401bf992a200df8c951006fa64a88037c3254403bfb0aa2019fd855100eeec2a88037f6054401bf302a200df58151006f8c0a88027c60544397fb2e8201bf997410e6fccba08067e65d04397eb2e8200df59741004facba0806fc65d0439bfaa68200df55341005fcc7a0802fd63d0401bf29e821cdf14f410077c87a0803bc43d04017f3168200bf58b410e6fea5a08037d52d0401df2168200ef10b410e6fea3a08037d51d04017f3068200bf583410e6f8a1a086eff65904037f32c821bdf9964100cfccb2086efd6590401beb2c82009f5964100df8cb20876fd6490437bfaa4821bef95241006faa92086fbd54904019eaa48200bf98e41007bcc720802de63904017eb1c8200f758e41005bac720
  | 6 => 0x17f3208626dfd50431377ea82189b3f5410c4ddf2a08600df550431377aa8218033d5410c4dde2a08627bf98c43137bea6218037e5310c4dbe2988626f714c43136b8a621803bf4310c01ef2188600ef50c43007ba86218039d4310c017f3108600bf58843136fea421802fe6110c017eb088626dfd4443005fcc021802fd6010c4dbe2808626efd94431377cca2189b3e6510c4ddeb288600cf5944313778ca21803be6310c4f5f3188600e798c431377ea62189b9f5310c4ddf2988600cf94c431377aa62189bbc5310c4d9e2988626e714c4313638a621803bf6210c01df3108600ef5884300778c42189bbf5210c4d9fa908626ef948431377aa42189bbc5210c01dfb088600ef984430077ac221803bc6110c4ddfa888626cfd44431377ca22189bbd5110c4dde2888600efd80430077cc021803bd6010c01de3008626efd40431377ca02189bbd5010c4dde2808626cf14043006fec8a90027f6454801bf322a400df59152006f8c8a90037f6354801bf31aa400df58d52006f8c6a90027c6354801bfa1aa400df90d520067c86a90037d4354801be21aa400cf10d5200efec4a90067f6254803b7b12a400dfd8552004fec2a90037e6154801beb0aa400df18552006fec0a90037e6054801beb02a400df18152004f8c0a9092ff65d08037f32e8424df9974200cfccba1092fd65d0801beb2e84009f5974200df8cba10937f54d0801beaa68400bf98f42005fac7a10037e53d0849be29e8400ef90f420077887a10937f52d0801bea968400bf98742005fac3a10937f51d08017f3068400bf58342126f8a1a108eff65908037f32c8423df9964200cfccb2108efd6590801beb2c84009f5964200df8cb21096fd6490847bfaa48423ef95242006faa92108fbd54908019eaa48400bf98e42007bcc721002de63908017eb1c8400f758e42005bac7210037e5390847be29c8400ef90e4200778872108afe6290847bfa948400df54a420077e8521003ef42908017f30c8400fd98642005ecc321002fd6190801fab0c8400bd5864211efea321002fe60908017eb048423df1424212dfecaa1006fe655084bbf32a84019f9954212dfacaa10037d65508013eb2a8401bf1954212efea8a10037d54508017fb1a8400bf18d42006fca6a10977c5350801df21a8400ef10d4212efea4a10037d5250801f7a128400ef90942005fec2a1002fc615084bbfa8a8400bfd8142005f8c0a10977c50508457fb288401bf99442116fcca210067e65108457eb288400df59442004faca21006fc65108497f3208422dfd50421177ca8210037d5410845deaa08400cf55042005fcc621002fd6310801bf2988422df14c420077c8621003bc43108477f3108422dfd4842006faa421003bf4210801f72108400ef50842007da8421002fe61108017eb088422dfd
  | 7 => 0x1600400600000000000602c05404604801e01002a00e01001200201c01803e00200a00800601a02200000200400401400400e00000000a00600c02400000001001401600203a02200600000800000400000a00a09e07a00201400400000000000000000200001602200c01800800400a00202a04405c00001a00605800400001c00000801c00200203401400e00800200402608c00208201c00203000000a00000000000000c00400201402005c00a00e00e00200602c07c00e01a01e00000200600000800002e00401600a00200600a03400000800201dfd915400cfec8aa0073f6455001bfb1aa800d7d8d54006fcc6aa0037d6355001be31aa8009f18d54006b8c6aa0025c6355001bfb12a8009fd8954006fcc4aa0037d6255001be312a800dfd8554004fec2aa0037e6155001beb0aa800df18554006fec0aa0037e6055001beb02a800df18154004f8c0aa0037f6494c01bf324a600df59253004fac9298037c6494c03bf31ca6019f98e5300ebcc7298037f6294c01bf314a600df58a53004fac5298037c6294c01bfb0ca600df98653006fac3298027d6194c01be30ca600dfd8253006fcc1298027e6094c01beb04a600df18253145fecba1806fe65d0c51bf32e86019f99743145facba18037d65d0c013eb2e8601bf19743146fea9a18037d54d0c51efa9e8600df94f43146f8a7a18a3dc53d0c51ae29e8600bf98b43005fac5a18a37f52d0c017f30e8600bf58743146fea3a1802fe60d0c017eb068628df1434313dfecb218037f6590c013fb2c8601bf9964313dfacb21806fc6590c4fbe32c86019f1964314dfac92189f7f5490c4fdfaa48627cfd524313f7ca9218037d5490c4fdeaa48600cf5524313f78a92189afe6390c01bf29c8627df14e430077e8721803df4390c017f3148600bf58a4313efea521802fe6190c017eb0c8627dfd4643005fcc121802fd6090c4fbe2848627efd96430067ecb2189fbe6590c4fdeb2c8627ef1964313e78cb2189abe6390c4fdfa9c8627ef94e430067ca72189fbd5390c4fde29c8627cf14e430077ec521803be6290c01deb148600ef18a4313f7ea52189f3f5290c4fdf2948627ef54a4313f78a521803bf6190c01df30c8600ef5864300778c32189fbf5190c4f9fa8c8627ef9464313f7aa32189fbc5190c01dfb048600ef982430077ac121803bc6090c4fdfa848627ef9424313f7aa12189fbc5090c4f9e2848629bfd9543006fecaa18027f6550c037f32a8629bf5954300df8caa18a77c6550c033e32a8629dfd5143006faa8a18037e5350c53be29a8600f7d0d430077c86a1802ff6250c017e3128629dfd4943005fec2a1802fc6150c53bfa8a8600bfd8143005f8c0a18a77c5050c4d7fb288601bf99443136fcca218067e6510c4d7eb288600df59443004faca21806fc6510c5
  | 8 => 0xd3c80011411a890c481800e8d5e469c00135137d4dc000000964294b6dae4ba400090088ce554b400105d0d83e82f400000147cdbc320d91550c60b516f50cc14c5a98f8814ac16b9a84064e9d65d2840002c0004f053a40008d00001e4db0000000000000000afc0000009a07840000011889b474d5fc7b99c0b24000a6c780000000f894ad0880008cc9e9134b1c000b30000f400000000019940015944a979805c45c3c8a2d454000000000a58470000b0087d4093446cd68cfdd4ec8b8f6c618e199f01880013dd4816359ad6b00001d942d4fc0014890d0001518c709450bd3d0000d7c5acf0d4a9004000bf0fc8000001621474fe4b180a50c54d484070cb602ac50880cbb4101998c751201ad41430c1a8424799aed815074b140ecec4a712712259d93419f4dc4be01682593387009091b5770a543bd9a52885f8cec8ac681ad99752b811caada500e96051245d51d90112655583dcea0894a85a70ef45a0650e4d92489c310dacec907990856d3f0921538b4c01600000400000600805600800200000203a00403600a00c00400200000c00c00005000200a00a00000600203c02c01600401200800200400c01a01800c00600400600002200000200c02400802600a00201c04200000000000a00200602006c00000800400001c00000000800000400001000e00000200000200001401000c00a00007600800400001000614a05c00600800c00e00803c01e01000e03600801c00200800e01400200200000003600000800c01000000000200000801200a01400c00800201200a00002202401a07600002401600200600412e00201a00603a00000402c00400200c00601001e01204e00003a00400600000800800000e00400200009c02200000c00204a00400804800000008800a00200003800800400200400003a01200a02200602001c01200000a00a00c00201c00000800001200003e00400200e00200601201200000c00200600000400600400001000200000200600400800601801000e00000600000a0220c000000400600606400600001400400a07000600200a00000601c01000203000a00c01801200e00000201200205605400002200e00800e02601003e04202802000800000e02a01202600806c00000000800000002a00000200000001000000000600200e01400400000000000000e00001601200804000c00007001800200000600000400403c02e00001401606801e00008600002a01600c00400200000400a01c00002600600002800a00401a02602600000001800000000800000600002000002a02200200005600e01a00802200200001201000000000000000001001c01c00602c00200003a01c0020ba00000604000e00800000003003400002800203800400000002400000000006200201a0120000040280000000
  | 9 => 0x274d380000000000000008a409c0000008a10c96916700018c4270000f90000000000b5d601820e5d4995458680004349f8d409bc834aa400035c0709c8e5103c9ac000f9c00000199d068ee400080839559041c989a5982c7ec1b46ad74d7889f5ad0f74e4591cfe0cb072cb34f84000d4c0017643f0f795e0cb56414944c967980506c641528b9c960e0d8d88fc76c95cca000140d67da6d458fd0f09665a89a480cd0a5970a08aa01f0d89080f013012745240004d8bf9831230c2800023579064cf38d49730e811010fc0002bd5c54a0000050000e617f4a680005ec001ab8129418abd2c8830811440ad91087e45f4994601400a90d2000000000000000086819d22d5244cc99d0e83717c8b412cc61d90102c37c0e0e389500f128d431a04208f6512d560000fb4000124a200000956a00011ac000f14a6400000072164c0000000000000011c44b0cf4000000bc00000a00018c16452913f58b91a146c5353550152696e104ce907a994d0e51506842f90b85f1850704a5d5d4000000ad5a4022c7098ec344fcc714bad2dc8dcc9c6dcd5c2a161cd990e1a14dd0001a7986d59d48c0010500005e00000000017a4af57045fd7596f0de5239add72d6f99551ed7b82c8000d84e6515d2059113bd0ad69c0000003ac6bc00085400000000130c000000000000e846a400000185c0000014b9894e95384000000000000055170000b4407c00000000000128000067c884000001aa800169498c7e13983011c80015d96cca318180015e8001a6546073920973d80dab12ad9dc904494000621588c79130fb93c45540907541c83b944879d4b1a4c000ffcd011e85496283315b4adc839058bd4c7cf4945c94c3054bc8e40014c4fece890a86b52c0474dc8e21038bed864000000a341cc000000000001a24000000000b2ce7cfe8bd97d52e4540461018b3c001404ea4d14ccc22440d374b280f990c25d9f9861a983549a4c113480006d400150d23d2140ad6c800096c4f0000458c4cfbc00000038d44533d60941dac18281380180015540002a803808c000c893d8925a101107482f0220ee178554854d7a0fb141120051ca3cc49638e310654794341d400166d9150445b90c07507c00c4c8d8bcea88f4244740f5c7d891cab8ff508d3a83c57452e960c531ad439d96d6497f911ccdcc38dcca1ccc400066d78d9bd2bc92814463c2b561952d7f1258000de8d0c7a12d98c8d50b959308258ac9b00d5330001a948bc980a949fd0f59d42a5624000194ab531c4c001c1718d4bb90415f40002780f551c1bcd300017d10615b00009483588e00012b4bc96dc000ebc28c000b8482c73cc540013e80010087359358b45880696155a8000af10dc289a9c0007441a40001b80000009789300000010482519840017cc000bc40011dc0000018482d509
  | 10 => 0x9100cd1997c60d9413198440000012500000119280000000011994f9580001a5c15175d714014998328ce03b4ded9b54d0cf00783e0211a205794f1958318b6587da18c1971c390efce08b80d9d9cc8600856540bc93ccc81e9abd07d9618991101597b17ac79082827c9ccd34e792283b0da4f7c000000f11a7cf240d163d6fd46925ca491d4ce42fd578ef0450db8000e050b51048007608906a0accf345d18f006d6d454577c0b9334ae8511750118f45320facf28574000b889ed7c43ece14794f60914448c6d8a9164081acd29595c214b09689368df8c1d540ae033c00193871cc3d6a8000dc00004c4660e2d6a5a915ed7a897cc84000e986940004141f87b4000ed449d7e815c26d05432c000ad0c019ec0002040009d99e8804a4087543c83d660db53e04653a000118400000012046c140d74130610350ddd0b046848d2fcfc04e957d5c8001870200c698554295b8eac2d1700b04f2c000240c440005bc000000000b9867886cd8d1b000026556924075c000000d2c8c86f8c980017740c04f442c00170c02c8b0594f1c000880d1c5806995000005900000008709c5a00a9dae0000d694202b94e47cd650044e6d1e00003984ac0012799e44202cd18c2287f46e0879598d58a389686b07300592ed58441068d98cdf45983e56ed4a4655a61768558fd85d95313b49b9874d558883600006f093949d49132c02877443c000000f58be9ae8000971309020fa09402846a82d8d793ad4c96591c0d3c0006d00c9138768a2910c00000000085c000001450a60000000b38001000048fd5091a8138c0000011e5719234a103d13297dc000000a8c0740000000012f07dc21d6ac4b8000e580000008c0d088210954cc4851d14389580000000000018e40016e961092ca44ff18f5708a803656d11780016684d4154604f8d7943f583ce34c0cf70bbd93d0ecfc5839a08ce87ac3397248c47591fc550cfd4716b52e1304cbd8dc4a113c571728a88b705cd88c7d05b17bc4900b0ae4e10dd53e4de10299c49d47f94c0f309dd1196c000195153579c0002c4b8d2b05209e4561034dfc10cb91808000a042197109840000005b45c000154c000658764e74b48724298ed136c6741852c49348892f850534c2692f4164500da126cd619057d80009e02b06c40011f40000009c114d8cd29d21cab19c8440cc0b20899314c30770eec00189d6804047d44b4d6da1d20d211a0d8d0f50c34098fa8000e1d0d40000012183088e8290e24c95978001aad84ccd95743d56bce018107c99fc0014d80008a85e452d8900000000009d031c41865c4e10a03f86480013240009101d1698bdca1981cdf15d11598843ccd647117e429c18c0003840a80018a12d48d9310c08e696753b94e81780000000013940002ed0f00fd0246e4ac91915a06e9ab4281464
  | 11 => 0xd24cd5390375a28f993c07fc3805e8f95834478ac4d101f50840300019b8000b74000f811f8bfc0019a8ecc4f8c14c4000000000057c664001ac4ee9880e3d14998003515535c0b458423c7a55f812c0615c077c0004bcf540014e062d740000000000000bb017c5686317395a57b594400000177803d27c000b5800000014800051495400156411451816cb792986149f084501d840e283c1631ac8b55a2c0d992c0008f0f18990d441b04019652a924404cc64000cd000081cd71a8c7bd780000001030000000001160000cac00081853c001a381ecff8000eb91b84ec000c24e712556c4f680000005c4000254689260c5d7611693d58b04a46c18786c80001c54f4b0ce4000138000020ca99748bd03a800119c0013f80004440017fcf3c0001dc325a300015215140018fd5ac6fd371a68000bf47f0fa4858000edcb682dc10484c499988aa8be5a547e8634a00000eb116c2e447d0f86383142e117c3d88b45284081c0ca40243896848ec000eb400000139c60813c3fca15360a24c04bccba17ecd945383491f0ca91cdaa44d13fc3a557000118194955c77800c0212d153c001a757555bc1084fd364341aa044cef99917c12a15058e0c2c6441a05a41fc4dc2e8a50001508a0d7e18a4cb8334c800e4000001a458251956e42301803a13ec974c58ba800162c58c55d7211741603680084885c93b06687b0ed84380001354240008d5128000b115cc00078c5dd1a437800059d6d819958ca74cf91446ed44cc512a4864dd95dc36c62976c9186d99d078973524caf8850f4c0008f935800000072956c0004550999184280dc000000a7c8499a0f20d286b9114da8b7c260000431378aed9e18586f59b0c207184e5070564248670a79a355f050daf0691484d0592034d968040d80ec1388a4c17408824c1e13cce491bc9a8c912492206258e9511a3c7c42381
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc735501000577715501000c7e75d8c100047d75d8c10004be74d8c10004bd74d8c10004ee72d8c10004ed72d8c1000c7c7598c100065c5398c10004dd7698c100065e6598c100065d6598c100069e6498c100069d6498c100065f7598c100065c7598c100069f7498c100069c7498c100065f5498c100065d5498c100065f5298c100065f5198c100065c5098c100047f7558c1000c7c7558c10004bf7458c10004bc7458c100065c5358c100065e6558c100065d6558c100069e6458c100069d6458c100065f7558c100065c7558c100069f7458c100069c7458c100065f5458c100065d5458c100065f5258c10006d47158c100065f5158c100065c5058c1000c7e7518c100047d7518c10004be7418c10004bd7418c10004de7318c10004ee7218c10004ed7218c100047f7694c100047d7694c100063e6494c100063d6494c100065e6394c100065d6394c10004bf7690c10004bd7690c1013e3e6590c100063d6590c100069e6390c100069d6390c10004bf7610c10004bd7610c101363e6510c100063d6510c100069e6310c100069d6310c101571c5310c1000c7e75d88100047d75d8810004be74d8810004bd74d8810004de73d8810004dd73d881000c7e75988100047d75988100066f5298810004ed76988100066e65988100066d6598810006ae6498810006ad6498810006ce6398810006cd63988100066e75988100066d75988100066f54988100066d54988100066e53988100066c5398810006ae4398810006ac43988100066f51988100066c509881000c7e75588100066f52588100066e65588100066d6558810006ae6458810006ad6458810006ce6358810006cd63588100066e75588100066d75588100066f54588100066d54588100066e53588100066c5358810006ae4358810006ac4358810006e471588100066f51588100066c505881000c7e75188100047d7518810004be7418810004bd7418810004de7318810004dd7318810004ee7218810004f671188100047f76548100047d76548100063e64548100063d64548100065e63548100065d63548100066e62548100066d62548100057771548100247f76544100063e64544100063d64544100065e63544100065d63544100066e62544100066d6254410006b564d0410006e562d0410004f57610410007355410410006e56210410006d563cc4100079443cc410006e562cc410004f5760c410006e5620c410004f576c8410005b674c8410005d673c8410006e562c8410004f57608410006e5620841001c7f769401000c7d76940100063e64940100063d64940100065e63940100065d63940100066e62940100066d6294010005757194010006e562c401000cf97684010004f77644010005b47444010005d47344010005e47244010006e56244010004fb7644010
  | 1 => 0x8d100065c5318d10004de7618d100065f6518d100065c6518d100069f6418d100069c6418d100065f7518d100065c7518d100069f7418d100069c7418d100065f5418d100065d5418d100065f5218d100065f5118d100065c5018d100047e7694d100047c7694d100063f6494d100063c6494d100065f6394d100065c6394d10004be7690d10004bc7690d100063f6590d1013e3c6590d100069f6390d100069c6390d10004be7610d10004bc7610d100063f6510d101363c6510d100069f6310d100069c6310d1015f1c5310d1000c7c75d89100066f52d89100066f65d89100066c65d8910006af64d8910006ac64d8910006cf63d8910006cc63d89100066f75d89100066c75d89100066f54d89100066d54d89100066e53d89100066c53d8910006ae43d8910006ac43d89100066f51d89100066c50d891000c7e75989100047d7598910004be7498910004bd7498910004de7398910004dd7398910004ee72989100047f755891000c7c7558910004bf7458910004bc7458910004df7358910004dc7358910004f7715891000c7e75189100047d75189100066f5218910004ee76189100066f65189100066c6518910006af6418910006ac6418910006cf6318910006cc63189100066e75189100066d75189100066f54189100066d54189100066e53189100066c5318910006ae4318910006ac4318910006e571189100066f51189100066c50189100047e76549100047c76549100063f64549100063c64549100065f63549100065c63549100066f62549100066c625491000c7c76545100063f64545100063c64545100065f63545100065c63545100066f62545100066c6254510005787054510004f67688510006b46488510006d46388510006e46288510004f47648510006b46448510006d46348510006e462485100247e76941100063f64941100063c64941100065f63941100065c63941100066f62941100066c6294110006b46484110006d46384110006e4628411000c7f76594100047f74594100047c73594100047f725941000c7f715941000c7d71594100147c705941000c7e75d90100047d75d9010004de73d9010004dd73d9010004ee72d9010004ed72d901000c7e75990100047d75990100063f5499010004bd76990100063e65990100063d65990100063e75990100063d7599010004be73990100063c53990100063f52990100063f51990100063c509901000c7e75590100063f54590100063e65590100063d65590100063e75590100063d7559010004bc73590100063c53590100063f5259010006b471590100063f51590100063c505901000c7e75190100047d7519010004be7419010004de7319010004dd7319010004ee7219010004ed72190100047f76550100047d76550100063e64550100063d64550100055
  | 2 => 0x4be74d8b10004bd74d8b10004de73d8b10004dd73d8b1000c7e7598b100047d7598b10004be7498b10004bd7498b10004de7398b10004dd7398b1000c7e7558b1000c7e7518b100047d7518b100047f7654b100047d7654b100147f7654710006e4624871002c7d76943100047d74d96100047e73d96100047d72d96100067571d96100067a70d961000c7c75d921000c7e75992100047d75992100047f755921000c7c7559210004df7359210004dc7359210004ef7259210004ec725921000c7e75192100047d75192100047e76552100047c76552100063e64552100063d64552100055c735521000577715521000c7e75d8e100047d75d8e10004be74d8e10004bd74d8e1000c7e7598e100047d7598e100047f7558e1000c7c7558e10004bf7458e10004bc7458e10004ef7258e10004ec7258e1000c7c7518e100047e7694e100047c7694e100063f6590e1013e3c6590e100063f6510e101363c6510e100069f6310e100069c6310e101671c5310e1000c7c75d8a1000c7e7598a100047d7598a100047f7558a1000c7c7558a10004bf7458a10004bc7458a10004df7358a10004dc7358a1000c7e7518a100047d7518a10004be7418a10004bd7418a10004de7318a10004dd7318a100047e7654a100047c7654a10005777154a100057870546100073554106100079443cc610005b674c8610005d673c8610006e7620861000c7e769421000575719421000c7e76d95100047d74d95100047e73d95100047d72d951002c7d71d951000c7e70d951000c7c70d951000c7c75d91100063f54d91100063f65d91100063c65d91100063f75d91100063c75d9110004be73d91100063c53d91100063f52d91100063f51d91100063c50d911000c7e75991100047d7599110004be7499110004de7399110004dd7399110004ee7299110004ed72991100047f755911000c7c7559110004df7359110004dc7359110004ef7259110004ec7259110004f7715911000c7e75191100047d75191100063f5419110004be76191100063f65191100063c65191100063e75191100063d7519110004be73191100063c53191100063f52191100063f51191100063c50191100047e76551100047c76551100063f64551100063c64551100055c735511000c7e75d8d100047d75d8d10004be74d8d10004bd74d8d100065c53d8d100065f65d8d100065c65d8d100069f64d8d100069c64d8d100065e75d8d100065d75d8d100069e74d8d100069d74d8d100065f54d8d100065d54d8d100065f52d8d100065f51d8d100065c50d8d1000c7e7598d100047d7598d10004be7498d10004bd7498d10004de7398d10004ee7298d10004ed7298d100047f7558d1000c7c7558d10004bf7458d10004bc7458d10004ef7258d10004ec7258d10004f77158d1000c7c751
  | 3 => 0xf7458c20004bc7458c200065c5358c200065e6558c200065d6558c200069e6458c200069d6458c200065f7558c200065c7558c200069f7458c200069c7458c200065f5458c200065d5458c20006cc7258c200065f5258c200065f5158c200065c5058c2000c7e7518c200047d7518c20004be7418c20004bd7418c20004de7318c20004f67118c20004f57118c200047f7694c200047d7694c200063e6494c200063d6494c200065e6394c200065d6394c20004bf7690c20004bd7690c2013e3e6590c200063d6590c200069e6390c200069d6390c20004bf7610c20004bd7610c201363e6510c200063d6510c200069e6310c200069d6310c201771c5310c200447f76548200063e64548200063d64548200065e63548200065d6354820006ad64d0820004ed76108200072d5410820006cd63cc8200078c43cc820004ed760c82000c7e75984200047d7598420006775198420006766598420006756598420006b66498420006b56498420006d66398420006d56398420006767598420006757598420006775498420006755498420006765398420006745398420006b64398420006b4439842000677529842000675529842000674509842000c7e7558420006775158420006766558420006756558420006b66458420006b56458420006d66358420006d56358420006767558420006757558420006775458420006755458420006765358420006745358420006b64358420006b44358420006775258420006755258420006e74258420006e44258420006e73258420006e432584200067450584200047f76544200047d76544200063e64544200063d64544200065e63544200065d63544200056f7254420006766154420006756154420004ed7688420005ae7488420005ce7388420006e56188420006e5610842003c7f769402000c7d76940200063e64940200063d64940200065e63940200065d63940200056d7294020006766194020006756194020006e561c8020004ef7648020005ac7448020005cc7348020005e47148020006e56148020004fb764802000c7f76597100047f74597100047c73597100047f725971000c7e75d93100047d75d9310004de73d9310004dd73d9310004ee72d9310004ed72d931000c7e75993100047d759931000c7e755931000c7e75193100047d75193100047f76553100047d76553100063f64553100063c64553100055c735531000c7e75d8f100047d75d8f10004be74d8f10004bd74d8f10004ee72d8f10004ed72d8f1000c7c7598f100047f7558f1000c7c7558f10004bf7458f10004bc7458f1000c7e7518f100047d7518f100047f7694f100047d7694f1013e3e6590f100063d6590f101363e6510f100063d6510f100069e6310f100069d6310f1016f1c5310f1000c7e75d8b100047d75d8b10
  | 4 => 0x8d200069c7418d200065f5418d200065d5418d200065f5218d200065f5118d200065c5018d200047e7694d200047c7694d200063f6494d200063c6494d200065f6394d200065c6394d20004be7690d20004bc7690d200063f6590d2013e3c6590d200069f6390d200069c6390d20004be7610d20004bc7610d200063f6510d201363c6510d200069f6310d200069c6310d2017f1c5310d2000c7c76549200063f64549200063c64549200065f63549200065c635492000578705492000c7c75d85200067751d85200067765d85200067465d8520006b764d8520006b464d8520006d763d8520006d463d85200067775d85200067475d85200067754d85200067554d85200067653d85200067453d8520006b643d8520006b443d85200067752d85200067552d85200067450d852000c7e75185200047d7518520006775118520006776518520006746518520006b76418520006b46418520006d76318520006d46318520006767518520006757518520006775418520006755418520006765318520006745318520006b64318520006b443185200067752185200067552185200067450185200047e76545200047c76545200063f64545200063c64545200065f63545200065c6354520006776154520006746154520004ee76c8520006ac64c8520006cc63c8520006e461c8520006ac6448520006cc6348520006e461485200447e76941200063f64941200063c64941200065f63941200065c6394120006776194120006746194120006ac6488120006cc6388120006e4618812000c7f76594200047f74594200047c735942000c7f725942000c7d72594200047f71594200347c705942000c7e75d90200047d75d9020004de73d9020004dd73d9020004f671d9020004f571d902000c7e75990200047d75990200063f5499020004bd76990200063e65990200063d65990200063e75990200063d7599020004be73990200063c53990200063f52990200063f51990200063c509902000c7e75590200063f54590200063e65590200063d65590200063e75590200063d7559020004bc73590200063c5359020006ac72590200063f52590200063f51590200063c505902000c7e75190200047d7519020004be7419020004de7319020004dd7319020004f67119020004f571190200047f76550200047d76550200063e64550200063d64550200055c73550200056f725502000c7e75d8c200047d75d8c20004be74d8c20004bd74d8c20004f671d8c20004f571d8c2000c7c7598c200065c5398c20004dd7698c200065e6598c200065d6598c200069e6498c200069d6498c200065f7598c200065c7598c200069f7498c200069c7498c200065f5498c200065d5498c200065f5298c200065f5198c200065c5098c200047f7558c2000c7c7558c20004b
  | 5 => 0x47f7694f200047d7694f2013e3e6590f200063d6590f201363e6510f200063d6510f200069e6310f200069d6310f2018f1c5310f200347f7654b2000c7e75987200047d7598720004be7498720004bd7498720004de7398720004dd739872000c7e75587200047f76547200047d765472004c7d76943200047d74d96200047e73d96200066d72d96200047d71d96200067a70d962000c7c75d922000c7e75992200047d75992200047f755922000c7c7559220004df7359220004dc7359220004f77159220004f4715922000c7e75192200047d75192200047e76552200047c76552200063e64552200063d64552200055c73552200056f725522000c7e75d8e200047d75d8e20004be74d8e20004bd74d8e2000c7e7598e200047d7598e200047f7558e2000c7c7558e20004bf7458e20004bc7458e20004f77158e20004f47158e2000c7c7518e200047e7694e200047c7694e200063f6590e2013e3c6590e200063f6510e201363c6510e200069f6310e200069c6310e201871c5310e20005787054a200072d5410a200078c43cca2000c7e75986200047d75986200047f755862000c7c7558620004bf7458620004bc7458620004df7358620004dc73586200047c76546200056f7254620005ae7488620005ce738862000c7e76942200056d729422000c7e76d95200047d74d95200047e73d952004c7d72d95200047d71d952000c7c75d91200063f54d91200063f65d91200063c65d91200063f75d91200063c75d9120004be73d91200063c53d91200063f52d91200063f51d91200063c50d912000c7e75991200047d7599120004be7499120004de7399120004dd7399120004f67199120004f571991200047f755912000c7c7559120004df7359120004dc7359120004ef7259120004f77159120004f4715912000c7e75191200047d75191200063f5419120004be76191200063f65191200063c65191200063e75191200063d7519120004be73191200063c53191200063f52191200063f51191200063c50191200047e76551200047c76551200063f64551200063c64551200055c735512000c7e75d8d200047d75d8d20004be74d8d20004bd74d8d200065c53d8d200065f65d8d200065c65d8d200069f64d8d200069c64d8d200065e75d8d200065d75d8d200069e74d8d200069d74d8d200065f54d8d200065d54d8d200065f52d8d200065f51d8d200065c50d8d2000c7e7598d200047d7598d20004be7498d20004bd7498d20004de7398d20004f67198d20004f57198d200047f7558d2000c7c7558d20004bf7458d20004bc7458d20004ef7258d20004f77158d20004f47158d2000c7c7518d200065c5318d20004de7618d200065f6518d200065c6518d200069f6418d200069c6418d200065f7518d200065c7518d200069f741
  | 6 => 0xd7518530006775118530006776518530006746518530006b76418530006b46418530006e76218530006e46218530006767518530006757518530006775418530006755418530006765318530006745318530006b64318530006b44318530006775218530006755218530006d73218530006d532185300067450185300047e76545300047c76545300063f64545300063c64545300066f62545300066c6254530006776154530006746154530004de76cc5300069c64cc530006cc62cc530006d461cc5300069c644c530006cc624c530006d4614c5300647e76941300063f64941300063c64941300066f62941300066c62941300067761941300067461941300069c648c130006cc628c130006d4618c1300047d74d94300647e73d94300065e73d94300047d72d94300047d71d943005c7e70d94300067a70d943000c7c75d903000c7e75990300047d75990300047f755903000c7c755903000c7e75190300047d7519030004ee7219030004ed7219030004f67119030004f571190300047e76550300047c76550300063e64550300063d64550300055c73550300057a7094c301465c65d0c300063f6590c3013e3c6590c301a59e7390c300063f6510c301363c6510c300071e5310c301971c5310c30004dd7610c301365c6510c300069d6410c301971f5410c300071d5410c300069e7610c300069d7610c301971e7510c300071d7510c300071f6510c301369e6510c301369c6510c301971c6510c301361c6510c301971f5210c301971f5110c300079a7010c30007997010c3019e9e6010c301971c5010c3000c7e75988300047d75988300047f755883000c7c7558830004bf7458830004bc74588300069c43588300047c76548300055c73548300071c43548300066e62548300066d6254830004dd768c8300059e748c830005d6718c83000c7e75984300047d75984300047f755843000c7c7558430004bf7458430004bc74584300069c43584300047c76544300055c73544300071c4354430006766154430006756154430004dd768c4300059e748c430005ce728c43000c7e76940300547c76940300055e73940300071c439403000798438c030004df764c0300059c744c030005cc724c030005d4714c030004fb764c03000c7f76597200047f74597200047c73597200047f715972000c7e75d93200047d75d9320004de73d9320004dd73d9320004f671d9320004f571d932000c7e75993200047d759932000c7e755932000c7e75193200047d75193200047f76553200047d76553200063f64553200063c64553200055c735532000c7e75d8f200047d75d8f20004be74d8f20004bd74d8f20004f671d8f20004f571d8f2000c7c7598f200047f7558f2000c7c7558f20004bf7458f20004bc7458f2000c7e7518f200047d7518f20
  | 7 => 0xe300069f6410e300069d6410e3019f1f5410e300071d5410e300059d7610e300069d7610e3019f1e7510e300071d7510e301369e6510e3019f1e6510e301361e6510e300071d6510e301369c6510e3019f1f5210e3019f1f5110e3019f1c5010e3000c7e7598a300047d7598a3000c7e7558a300069c4358a300047f7654a300047d7654a300063e6454a300063d6454a300055c7354a300071c4354a300059e748ca30005d6718ca3000c7e75986300047d759863000c7e75586300069c43586300047f76546300047d76546300063e64546300063d64546300055c73546300071c43546300059e748c630005ce728c63000c7d76942300063e64942300063d64942300055e73942300071c43942300075a50cc2300075a53cc23000c7e76d95300047d74d953000c7e73d953000c7c73d95300047d72d95300047d71d953000c7c75d91300063f54d91300063f65d91300063c65d91300063f75d91300063c75d91300063c53d91300063f52d91300063f51d91300063c50d913000c7e75991300047d7599130004be7499130004ee7299130004ed7299130004f67199130004f571991300047f755913000c7c7559130004df7359130004ef7259130004ec7259130004f77159130004f4715913000c7e75191300047d75191300063f5419130004be76191300063f65191300063c65191300063e75191300063d751913013cbe7319130134bc73191300063c53191300063f52191300063f51191300063c50191300047e76551300047c76551300063f64551300063c64551300055c735513005c7e7694d300063f6494d300063c6494d30004be7690d300063f6590d3013e3c6590d30004be7610d300063f6510d301363c6510d301af1c5310d3000c7c75d89300066f52d89300066f65d89300066c65d8930006af64d8930006ac64d89300066f75d89300066c75d89300066f54d89300066d54d89300066e53d89300066c53d8930006ae43d8930006ac43d89300066f51d89300066c50d893000c7e75189300047d75189300066f52189300066f65189300066c6518930006af6418930006ac64189300066e75189300066d75189300066f54189300066d54189300066e53189300066c5318930006ae4318930006ac43189300066f51189300066c50189300047e76549300047c76549300063f64549300063c64549300066f62549300066c6254930004de76cc9300069c64cc930006cc62cc9300069c644c930006cc624c93000c7c75d85300067751d85300067765d85300067465d8530006b764d8530006b464d8530006e762d8530006e462d85300067775d85300067475d85300067754d85300067554d85300067653d85300067453d8530006b643d8530006b443d85300067752d85300067552d85300067450d853000c7e75185300047
  | 8 => 0x6776154540006746154540004be76d05400053d75d05400069c63d0540006ac62d0540006b461d05400053d75505400069c6350540006ac6250540006b461505400847e76941400065f63941400065c63941400066f62941400066c62941400067761941400067461941400073954d01400053f75901400069c6390140006ac6290140006b4619014000c7f765944000c7f745944000c7d74594400047c73594400047f72594400047f71594400747c70594400847f76550400863e64550400055c735504000c7c7598c400047f7558c4000c7c7558c400047f7694c400047d7694c4013e3e6590c400063d6590c401363e6510c400063d6510c400069e6310c400069d6310c401bf1c5310c4000c7e75988400047d759884000c7e75588400047f76548400047d76548400053f7454840004bd76908400063d65908400059e7390840005b671908400063d651084000c7e75984400047d759844000c7e75584400047f76544400047d76544400053f7454440004bd76904400063d65904400059e7390440005ae72904400063d651044007c7f769404000c7d76940400053d74940400063d65d0040004bf76500400063d65500400059c7350040005ac7250040005b47150040004fb765004000c7f76597300047f74597300047f72597300047f715973000c7e75d93300047d75d9330004ee72d9330004ed72d9330004f671d9330004f571d933000c7e75993300047d759933000c7e755933000c7e75193300047d75193300047f76553300047d76553300063f64553300063c64553300055c735533000c7d7694f300057a7094f3013e3e6590f300063d6590f301363e6510f300063d6510f301b71c5310f3000c7e7598b300047d7598b30004be7498b30004bd7498b30004f67198b30004f57198b3000c7e7558b300047f7654b300047d7654b3000c7e75987300047d7598730004be7498730004bd7498730004ee7298730004ed729873000c7e75587300047f76547300047d765473006c7d769433000c7f76596300047f74596300047f72596300047f715963000c7e75d92300047d75d923000c7e75992300047d75992300063f5499230004bd76992300063e65992300063d65992300063e75992300063d75992300063c53992300063f52992300063f51992300063c509923000c7e75592300063f54592300063e65592300063d65592300063e75592300063d75592300069f73592300063c53592300063f52592300063f51592300063c505923000c7e75192300047d7519230004be74192300047f76552300047d76552300063e64552300063d64552300055c735523006c7d7694e300063e6494e300063d6494e301465e65d0e3013e3e6590e300063d6590e301363e6510e300063d6510e300071e5310e3019f1c5310e301365e651
  | 9 => 0xa50d02400073954d024000c7e76d954008c7d74d95400047e73d95400047d72d95400047d71d954000c7c76551400055c735514000578705514000e3f765514008d3c765514000e3c765514000c3c76551400071f73551400053c73551400071c73551400051c73551400053f72551400053f71551400073b70551400053c705514000738705514000c7e75d8d400047d75d8d400065c53d8d400065f65d8d400065c65d8d400071d54d8d400065e75d8d400065d75d8d400065f54d8d400065d54d8d400065f52d8d400065f51d8d400065c50d8d4000c7c7518d400063d5418d400065c5318d400065f6518d400065c6518d400071d5418d400065f7518d400065c7518d400069f7418d400065f5418d400069e5418d400065d5418d400069d5418d400061d5418d400065f5218d400065f5118d400065c5018d400047e7694d400047c7694d400065f6394d400065c6394d400053f7590d400063f6590d4013e3c6590d400069c6390d400053d7510d400063f6510d401363c6510d400069f6310d401c71c5310d4000c7c75d89400066f52d89400066f65d89400066c65d89400072d54d8940006cf63d8940006cc63d89400066f75d89400066c75d89400066f54d89400066d54d89400066e53d89400066c53d8940006ae43d8940006ac43d89400066f51d89400066c50d894000c7e75189400047d75189400063d54189400066f52189400066f65189400066c65189400072d5418940006cf6318940006cc63189400066e75189400066d75189400066f5418940006ae54189400066d5418940006ad54189400062d54189400066e53189400066c5318940006ae4318940006ac43189400066f51189400066c50189400047e76549400047c76549400065f63549400065c63549400066f62549400066c6254940004be76d09400053d75d09400069c63d0940006ac62d09400053d75509400069c6350940006ac625094000c7c75d85400067751d85400067765d85400067465d85400073554d8540006d763d8540006d463d8540006e762d8540006e462d85400067775d85400067475d85400067754d85400067554d85400067653d85400067453d8540006b643d8540006b443d85400067752d85400067552d85400067450d854000c7e75185400047d75185400063d5418540006775118540006776518540006746518540007355418540006d76318540006d46318540006e76218540006e46218540006767518540006757518540006775418540006b65418540006755418540006b55418540006355418540006765318540006745318540006b64318540006b44318540006775218540006755218540006b74218540006b542185400067450185400047e76545400047c76545400065f63545400065c63545400066f62545400066c6254540
  | 10 => 0x86500053f74586500053c74586500047f74586500063f74586500043f74586500063c74586500047c73586500063e43586500063c43586500047f72586500053e74186500053d74186500055e73186500055d73186500056e72186500056d721865001d7a70186500047e76d06500047d76d06500063d64d06500047e76906500047d76906500055e73906500055d73906500056e72906500056d72906500047d76506500063d64506500047e76106500047d76106500047f76cc6500065e63cc6500071c43cc6500047e768c6500047d768c6500053e748c6500053d748c6500056e728c6500056d728c6500047f764c6500047c764c6500053f744c6500053c744c6500065e634c6500071c434c6500047e760c6500047d760c6500047e76c86500047d76c86500053e74c86500053d74c86500055e73c86500055d73c86500066d62c86500047e76886500047d76886500053e74886500053d74886500055e73886500055d73886500067561886500047d76486500066d62486500067561486500047e76086500047d760865000765210865000c7f76597400047c73597400047f72597400047f71597400747f76553400055c73553400053f76553400763f76553400071f73553400053c73553400071c73553400051c73553400053f72553400053f71553400053c705534000c7c7598f400063d5498f400047f7558f4000c7c7558f400047f7694f400047d7694f400053f7590f4013e3e6590f400063d6590f400053d7510f401363e6510f400063d6510f400069e6310f400069d6310f401d71c5310f4000c7e7598b400047d7598b400063d5498b40004de7398b40004dd7398b40004f67198b40004f57198b4000c7e7558b400047f7654b400047d7654b400053d75d0b400053d7550b4000c7e75987400047d75987400063d5498740004de7398740004dd7398740004ee7298740004ed729874000c7e75587400047f76547400047d76547400053d75d07400053d755074008c7d76943400055e73d96400063d74d96400047e73d96400065e73d96400045e73d96400065d73d96400047d72d96400047d71d96400067a70d964008e3d64552400055c735524000578705524000c7e7598e400047d7598e400065c5398e400047f7558e4000c7c7558e400065c5358e400047e7694e400063f6590e4013e3c6590e400069e6390e400063f6510e401363c6510e401cf1c5310e4000c7e7598a400047d7598a400047f7558a4000c7c7558a400047c7654a400053f7454a400063f6590a400059e7390a40005b67190a400063f6510a4000c7e75986400047d75986400047f755864000c7c75586400047c76546400053f74546400063f65906400059e7390640005ae72906400063f651064000c7e76942400053d74942400063f65d02400073
  | 11 => 0x47c73594210047c705942100c7e75d90210047d75d9021004de73d9021004dd73d9021004ee72d9021004f671d902100c7e75990210047d759902100c7e755902100c7e75190210047d75190210047f76550210047d76550210063f64550210063c64550210055c735502100c7e75d8c210047d75d8c21004be74d8c21004bd74d8c21004ee72d8c21004f671d8c2100c7c7598c210047f7558c2100c7c7558c21004bf7458c21004bc7458c2100c7e7518c210047d7518c210047f7694c210047d7694c2113e3e6590c210063d6590c211363e6510c210063d6510c210069e6310c210069d6310c211ef1c5310c210a47f765482109c7f76544211e5e57288421004ef76484211df675148421007655148421004f776484211df675248421007655248421005e77648421006e776484211df6675484210076575484211df666548421007656548421006e66448421006e464484211df675448421007655448421006e66348421006e463484210076653484211df645348421007a64348421007a44348421005e470484211df64504842100c7c75980210047f755802100c7c7558021004bf7458021004bc7458021004df7358021004dc7358021006e521580210055e73d92500055d73d92500757a70d92500063f64992500047c73592500047f72592500047f71592500063d641925007d7a70192500053e74d8e500053d74d8e500557a70d8e500047d7498e500047d7298e500047d7198e500053f7458e500053c7458e500065d6318e5005d7a7018e500047e76d0e500047d76d0e500065e63d0e500047f7690e500063d6490e500063f7690e500063c7690e501353e7390e500063e6390e5013e3e6090e5013f3a6090e500047f7650e500047c7650e500047e7610e500047d7610e500063d6410e500065e6310e500071d4310e500063e7610e500063d7610e5013d3e7310e500071e7310e500063e6310e500071e6310e500061e6310e500071d6310e501363e6010e501373a6010e500357a70d8a500053f7458a500053c7458a500047f7458a500063f7458a500043f7458a500063c7458a500047c7358a500063e4358a500063c4358a500047f7158a500053e7418a500053d7418a500055e7318a500055d7318a50005767118a50005757118a5003d7a7018a500047e76d0a500047d76d0a500063d64d0a500047e7690a500047d7690a500055e7390a500055d7390a50005767190a50005757190a500047d7650a500063d6450a500047e7610a500047d7610a500047f76cca500065e63cca500071c43cca500047e768ca500047d768ca500053e748ca500053d748ca5000576718ca5000575718ca500047f764ca500047c764ca500053f744ca500053c744ca500065e634ca500071c434ca500047e760ca500047d760ca500157a70d
  | 12 => 0xd76552210063e64552210063d64552210055c735522100577715522100c7e75d8e210047d75d8e21004be74d8e21004bd74d8e2100c7c7598e210065c5398e21004dd7698e210065e6598e210065d6598e210069e6498e210069d6498e210065f7598e210065c7598e210069f7498e210069c7498e210065f5498e210065d5498e210065f5298e210065f5198e210065c5098e210047f7558e2100c7c7558e21004bf7458e21004bc7458e210065c5358e210065e6558e210065d6558e210069e6458e210069d6458e210065f7558e210065c7558e210069f7458e210069c7458e210065f5458e210065d5458e210065f5258e21006d47158e210065f5158e210065c5058e2100c7e7518e210047d7518e21004be7418e21004bd7418e21004de7318e210047f7694e210047d7694e210063e6494e210063d6494e210065e6394e210065d6394e21004bf7690e21004bd7690e2113e3e6590e210063d6590e210069e6390e210069d6390e21004bf7610e21004bd7610e211363e6510e210063d6510e210069e6310e210069d6310e211ff1c5310e2100c7f7654a210063e6454a210063d6454a210065e6354a210065d6354a21005777154a210947f76546210063e64546210063d64546210065e63546210065d6354621006b564d0621007355410621006d563cc6210079443cc621006ae64c8621006ce63c86210076551c8621005b674c8621005d673c86210076552c862100c7c75982210047f755822100c7c75582210047f74595210047c735952109c7f72595210066f72595210a47f71595210067771595210047c705952100c7e75d91210047d75d9121004de73d9121004dd73d912100c7e75991210047d759912100c7e755912100c7e75191210047d75191210047f76551210047d76551210063f64551210063c64551210055c73551210056f725512100577715512100c7e75d8d210047d75d8d21004be74d8d21004bd74d8d2100c7c7598d210047f7558d2100c7c7558d21004bf7458d21004bc7458d21004fb7058d21004f87058d2100c7e7518d210047d7518d210047f7694d210047d7694d2113e3e6590d210063d6590d211363e6510d210063d6510d210069e6310d210069d6310d211f71c5310d21005777154921004ee76d0921005e671d09210072d5410921004ee76cc9210078c43cc921005e671cc92100c7f76545210ac7d76545210056f7254521004f676d0521005e672d0521007a442d0521007355410521007a74210521004f676cc5210079443cc521005e672cc521007c432cc521007c7320c521005b674c8521005d673c8521005ae7488521005ce738852100c7e75d81210047d75d812100c7e75181210047d7518121004be7418121004bd7418121004de7318121004dd731812100c7f76594210047f7459421
  | 13 => 0x80310047f755803100c7c7558031004bf7458031004bc7458031004ef7258031004ec725803100c7f76597210047f74597210047c73597210047c705972100c7e75d93210047d75d9321004de73d9321004dd73d932100c7e75993210047d75993210063f5499321004bd76993210063e65993210063d65993210063e75993210063d7599321004be73993210063c53993210063f52993210063f51993210063c509932100c7e75593210063f54593210063e65593210063d65593210063e75593210063d7559321004bc73593210063c5359321006ac72593210063f52593210063f51593210063c505932100c7e75193210047d7519321004be7419321004de7319321004dd73193210047f76553210047d76553210063e64553210063d64553210055c73553210056f725532100c7e75d8f210047d75d8f21004be74d8f21004bd74d8f2100c7c7598f210065c5398f21004dd7698f210065e6598f210065d6598f210069e6498f210069d6498f210065f7598f210065c7598f210069f7498f210069c7498f210065f5498f210065d5498f210065f5298f210065f5198f210065c5098f210047f7558f2100c7c7558f21004bf7458f21004bc7458f210065c5358f210065e6558f210065d6558f210069e6458f210069d6458f210065f7558f210065c7558f210069f7458f210069c7458f210065f5458f210065d5458f21006cc7258f210065f5258f210065f5158f210065c5058f2100c7e7518f210047d7518f21004be7418f21004bd7418f21004de7318f210047f7694f210047d7694f210063e6494f210063d6494f210065e6394f210065d6394f21004bf7690f21004bd7690f2113e3e6590f210063d6590f210069e6390f210069d6390f21004bf7610f21004bd7610f211363e6510f210063d6510f210069e6310f210069d6310f212071c5310f210947f7654b210063e6454b210063d6454b210065e6354b210065d6354b21006ad64d0b210072d5410b21006cd63ccb210078c43ccb2100c7f76547210063e64547210063d64547210065e63547210065d63547210056f725472100c7c75983210047f755832100c7c755832100c7f76596210047f74596210047c73596210047c705962100c7e75d92210047d75d9221004de73d9221004dd73d922100c7e75992210047d75992210063f5499221004bd76992210063e65992210063d65992210063e75992210063d7599221004be73992210063c53992210063f52992210063f51992210063c509922100c7e75592210063f54592210063e65592210063d65592210063e75592210063d7559221004bc73592210063c53592210063f5259221006b471592210063f51592210063c505922100c7e75192210047d7519221004be7419221004de7319221004dd73192210047f76552210047
  | 14 => 0x66f5458a310066d5458a310066e5358a310066c5358a31006ae4358a31006ac4358a310066f5158a310066c5058a310047f7654a310047d7654a310063e6454a310063d6454a310066e6254a310066d6254a310069e64cca31006ce62cca310069e644ca31006ce624ca310b47f76546310063e64546310063d64546310066e62546310066d62546310069e64cc631006ce62cc6310075551cc6310075653cc631006e562cc63100c7c75982310047f755823100c7c755823100c7e76d95310047d74d95310047d72d95310cc7d71d95310047e70d953100c7c75d91310063f54d91310063f65d91310063c65d91310063f75d91310063c75d91310069d73d91310063c53d91310063f52d91310063f51d91310063c50d913100c7e75991310047d7599131004be74991310047f755913100c7c755913100c7e75191310047d75191310063f5419131004be76191310063f65191310063c65191310063e75191310063d75191310063c53191310063f52191310063f51191310063c50191310047e76551310047c76551310063f64551310063c64551310055c73551310bc7e7694d310063f6494d310063c6494d31004de76d0d311465c65d0d31005d671d0d31004be7690d310063f6590d3113e3c6590d312259e7390d31004be7610d310063f6510d311363c6510d310071e5310d3121f1c5310d311365c6510d310069f6410d310069d6410d3121f1f5410d310071d5410d310059e7610d310069e7610d3121f1e7510d310071d7510d310071f6510d311369e6510d311369c6510d3121f1c6510d311361c6510d3121f1f5210d3121f1f5110d3121f1c5010d3100c7c75d89310069c43d893100c7e75189310047d75189310047e76549310047c76549310063f64549310063c64549310055c73549310071c43549310059e748c931005d6718c931004de760c93100c7c76545310063f64545310063c64545310055c73545310071c43545310079443cc5310059e748c531005ce728c53100c7e75d81310047d75d813100c7c75181310069c431813100c7f76594310047f74594310b47c73594310047f72594310047c705943100c7e75d90310047d75d9031004de73d9031004ee72d9031004ed72d903100c7e75990310047d759903100c7e755903100c7e75190310047d75190310047f76550310047d76550310063f64550310063c64550310055c73550310c47f7694c3100c7d7694c31005757194c3113e3e6590c310063d6590c311363e6510c310063d6510c312169e6310c3120f1c5310c3100c7e75988310047d7598831004be7498831004bd749883100c7e75588310047f76548310047d7654831004df764c8310bc7f7654431005e5728c431004df764c43100755514c431004f7764c43100756534c43100796434c43100c7c759
  | 15 => 0xd6310c412371c5310c41005b57110c4100c7e75988410047d75988410063d5498841004de7398841004dd739884100c7e75588410047f76548410047d76548410053d75d0841004bf76508410053d75508410dc7f76544410053d75d0441007355490441005e57290441004bf76504410053d7550441004f7765044100c7c75980410047f755804100c7c75580410063d5458041004df7358041004dc7358041004ef7258041004ec72580410047d74d97310065e73d97310047d72d97310067571d97310047e70d973100c7c75d933100c7e75993310047d75993310047f755933100c7c755933100c7e75193310047d7519331004ee7219331004ed72193310047e76553310047c76553310063e64553310063d64553310055c7355331005757194f311465c65d0f310063f6590f3113e3c6590f310063f6510f311363c6510f310071e5310f312171c5310f311365c6510f310069d6410f312171f5410f310071d5410f310069e7610f310069d7610f312171e7510f310071d7510f310071f6510f311369e6510f311369c6510f312171c6510f311361c6510f312171f5210f31007967110f31007957110f312171f5110f312171c5010f3100c7e7598b310047d7598b310047f7558b3100c7c7558b31004bf7458b31004bc7458b310069c4358b310047c7654b310055c7354b310071c4354b310066e6254b310066d6254b310059e748cb31005d6718cb3100c7c76547310055c73547310071c435473100c7e75983310047d7598331004be7498331004bd74983310069c43983310047f755833100c7c755833100c7f76596310047f74596310047f72596310047c705963100c7e75d92310047d75d9231004ee72d9231004ed72d923100c7e75992310047d75992310063f5499231004bd76992310063e65992310063d65992310063e75992310063d75992310063c53992310063f52992310063f51992310063c509923100c7e75592310063f54592310063e65592310063d65592310063e75592310063d75592310063c53592310063f52592310063f51592310063c505923100c7e75192310047d7519231004be7419231004ee7219231004ed72192310047f76552310047d76552310063e64552310063d64552310055c73552310cc7d7694e310063e6494e310063d6494e3113e3e6590e310063d6590e311363e6510e310063d6510e3122f1c5310e3100c7e7598a310047d7598a310066f5298a310066e6598a310066d6598a31006ae6498a31006ad6498a310066e7598a310066d7598a310066f5498a310066d5498a310066e5398a310066c5398a31006ae4398a31006ac4398a310066f5198a310066c5098a3100c7e7558a310066f5258a310066e6558a310066d6558a31006ae6458a31006ad6458a310066e7558a310066d7558a31
  | 16 => 0x8e410047f7558e4100c7c7558e410065c5358e410065e6558e410065d6558e410071d5458e410065f7558e410065c7558e410065f5458e410065d5458e410065f5258e410065f5158e410065c5058e410047f7694e410047d7694e410065e6394e410065d6394e410053f7590e4113e3e6590e410063d6590e410069e6390e410053d7510e411363e6510e410063d6510e410069d6310e412471c5310e4100c7e7598a410047d7598a410063d5498a410066f5298a410066e6598a410066d6598a410072d5498a41006ce6398a41006cd6398a410066e7598a410066d7598a410066f5498a41006ae5498a410066d5498a41006ad5498a410062d5498a410066e5398a410066c5398a41006ae4398a41006ac4398a410066f5198a410066c5098a4100c7e7558a410066f5258a410066e6558a410066d6558a410072d5458a41006ce6358a41006cd6358a410066e7558a410066d7558a410066f5458a410066d5458a410066e5358a410066c5358a41006ae4358a41006ac4358a410066f5158a410066c5058a410047f7654a410047d7654a410065e6354a410065d6354a410066e6254a410066d6254a410053d75d0a410069e63d0a41006ae62d0a410053d7550a410069e6350a41006ae6250a410d47f76546410065e63546410065d63546410066e62546410066d62546410053d75d06410069e63d0641006ae62d06410073551d06410073554d0641006e562d064100c7c75982410047f755824100c7c75582410063d54582410055c73595410dc7f74595410063f74595410065f73595410047c73595410065c73595410045c73595410047f72595410e47f71595410067771595410047c70595410055c735514100577715514100c7e75d8d410047d75d8d410065c53d8d4100c7e7518d410047d7518d410065c5318d410047d7694d4113e3e6590d410063d6590d410069c6390d41005b67190d411363e6510d410063d6510d4123f1c5310d4100c7e75d89410047d75d894100c7e75189410047d75189410047f76549410053f74549410063d65909410059e7390941005b67190941004be76109410063d651094100c7f76545410ec7d76545410053f74545410063d65905410059e7390541005ae729054100c7e75d81410047d75d814100c7e75181410047d751814100c7f76594410d53d74594410047c73594410047f72594410047c70594410e47f76550410055c73550410053f76550410e63f76550410071f73550410053c73550410071c73550410051c73550410053f72550410053f71550410de3e61550410053c705504100c7c7598c410063d5498c410047f7558c4100c7c7558c410047f7694c410047d7694c410053f7590c4113e3e6590c410063d6590c410053d7510c411363e6510c410063d6510c410069e6310c410069
  | 17 => 0x47d7418d510047d7218d510047e7018d510047e76d0d510047d76d0d510065c63d0d510047c7690d510063f6490d51005767190d51005757190d510063f7690d510063c7690d511353e7390d510063c6390d51007367190d51007357190d5113e3f6190d5113f376190d510047f7650d510047c7650d510047e7610d510047d7610d510063f6410d510065c6310d510071d4310d510063e7610d510063d7610d5113d3e7310d510071e7310d510071f6310d510063c6310d510071c6310d510061c6310d511363f6110d51137376110d510053e74d89510053d74d89510063e74d89510047d74d89510063d74d89510043d74d89510047e73d89510063e43d89510063c43d89510047e70d89510053e74989510053d74989510055e73989510055d73989510ad7571989510a57771589510047e76d09510047d76d09510063f64d09510047e76909510047d76909510055e73909510055d73909510057671909510057571909510047e76509510063f64509510047e76109510047d76109510047c76cc9510065c63cc9510071c43cc9510057671cc9510057571cc9510047e768c9510047d768c9510053e748c9510053d748c95100576718c95100575718c9510047f764c9510047c764c9510053f744c9510053c744c9510065c634c9510071c434c9510047e760c9510047d760c95102d7571981510053f74581510053c74581510055f73581510055c73581510056f72581510056c725815101d7771581510053e74181510053d74181510063e74181510047d74181510063d74181510043d74181510047e73181510063e43181510063c43181510047d721815100c7f76597410047c73597410047f72597410047c70597410d47f76553410055c735534100c7c7598f410047f7558f4100c7c7558f410047f7694f410047d7694f4113e3e6590f410063d6590f411363e6510f410063d6510f410069e6310f410069d6310f4124f1c5310f4100c7e7598b410047d7598b4100c7e7558b410047f7654b410047d7654b410053f7454b410063d6590b410059e7390b41005b67190b410063d6510b4100c7f76547410053f745474100c7c75983410047f755834100c7c755834100c7f76596410047c73596410047f72596410047c705964100c7f76552410055c73552410057771552410dd3f765524100e3f765524100c3f765524100e3c76552410071f73552410053c73552410071c73552410051c73552410053f72552410053f71552410073771552410073471552410053c705524100c7c7598e410063d5498e410065c5398e410065e6598e410065d6598e410071d5498e410065f7598e410065c7598e410069f7498e410065f5498e410069e5498e410065d5498e410069d5498e410061d5498e410065f5298e410065f5198e410065c509
  | 18 => 0xe7558632006775158632006766558632006756558632006b66458632006b56458632006767558632006757558632006775458632006755458632006765358632006745358632006b64358632006b44358632006775258632006755258632006e7325863200674505863200c7c75982320047f755823200c7c755823200c7e76d95320047d74d953210c7d72d95320047d71d95320047e70d953200c7c75d91320063f54d91320063f65d91320063c65d91320063f75d91320063c75d91320069d73d91320063c53d91320063f52d91320063f51d91320063c50d913200c7e75991320047d7599132004be74991320047f755913200c7c755913200c7e75191320047d75191320063f5419132004be76191320063f65191320063c65191320063e75191320063d75191320063c53191320063f52191320063f51191320063c50191320047e76551320047c76551320063f64551320063c64551320055c73551320fc7e7694d320063f6494d320063c6494d32004de76d0d321465c65d0d32005ce72d0d32004be7690d320063f6590d3213e3c6590d3226d9e7390d32004be7610d320063f6510d321363c6510d320071e5310d322671c5310d321365c6510d320069f6410d320069d6410d322671f5410d320071d5410d320059e7610d320069e7610d322671e7510d320071d7510d320071f6510d321369e6510d321369c6510d322671c6510d321361c6510d322671f5210d322671f5110d322671c5010d3200c7c76549320063f64549320063c64549320055c73549320071c43549320078c43cc9320059e748c932005d6718c93200c7c75d85320069c43d853200c7e75185320047d751853200c7e75d81320047d75d813200c7c75181320069c431813200c7f76594320047f74594320f47c73594320047f71594320047c705943200c7e75d90320047d75d9032004de73d9032004f671d9032004f571d903200c7e75990320047d759903200c7e755903200c7e75190320047d75190320047f76550320047d76550320063f64550320063c64550320055c73550321047f7694c3200c7d7694c320056d7294c3213e3e6590c320063d6590c321363e6510c320063d6510c3225e9e6310c322571c5310c320fc7f7654832005e5718c832004df764c8320074d524c832004ef764c8320074e534c8320078e434c83200c7e75984320047d7598432004be7498432004bd749843200c7e755843200c7c75980320047f755803200c7c7558032004bf7458032004bc7458032004f77158032004f471580320047e73d91510047d72d91510047e70d91510063f64991510ed7571991510055f73591510055c73591510e57771591510063d64191510053e74d8d510053d74d8d510065f6398d510cd757198d510053f7458d510053c7458d510c5777158d51
  | 19 => 0x8c420047f7558c4200c7c7558c420047f7694c420047d7694c420053f7590c4213e3e6590c420063d6590c420053d7510c421363e6510c420063d6510c420069e6310c420069d6310c4227f1c5310c42005ad7210c4211c7f76548420053d75d08420072d5490842005e57190842004bf76508420053d7550842004ef765084200c7e75984420047d75984420063d5498442004de7398442004dd739844200c7e755844200c7c75980420047f755804200c7c75580420063d5458042004df7358042004dc7358042004f77158042004f471580420047d74d97320065e73d97320066d72d97320047d71d97320047e70d973200c7c75d933200c7e75993320047d75993320047f755933200c7c755933200c7e75193320047d7519332004f67119332004f571193320047e76553320047c76553320063e64553320063d64553320055c73553320056d7294f321465c65d0f320063f6590f3213e3c6590f320063f6510f321363c6510f320071e5310f3225f1c5310f321365c6510f320069d6410f3225f1f5410f320071d5410f320069e7610f320069d7610f3225f1e7510f320071d7510f320071f6510f321369e6510f321369c6510f3225f1c6510f321361c6510f320078e7210f320078d7210f3225f1f5210f3225f1f5110f3225f1c5010f3200c7c7654b320055c7354b320071c4354b3200c7e75987320047d75987320047f755873200c7c7558732004bf7458732004bc74587320069c435873200c7e75983320047d7598332004be7498332004bd74983320069c43983320047f755833200c7c755833200c7f76596320047f74596320047f71596320047c705963200c7e75d92320047d75d9232004f671d9232004f571d923200c7e75992320047d75992320063f5499232004bd76992320063e65992320063d65992320063e75992320063d75992320063c53992320063f52992320063f51992320063c509923200c7e75592320063f54592320063e65592320063d65592320063e75592320063d75592320063c53592320063f52592320063f51592320063c505923200c7e75192320047d7519232004be7419232004f67119232004f571192320047f76552320047d76552320063e64552320063d64552320055c735523210c7d7694e320063e6494e320063d6494e3213e3e6590e320063d6590e321363e6510e320063d6510e322771c5310e320f47f7654a320063e6454a320063d6454a320069e64cca320074d52cca320074e53cca3200c7e75986320047d7598632006775198632006766598632006756598632006b66498632006b56498632006767598632006757598632006775498632006755498632006765398632006745398632006b64398632006b44398632006775298632006755298632006d7329863200674509863200c7
  | 20 => 0x56f725524211d3f765524200e3f765524200c3f765524200e3c76552420071f73552420053c73552420071c73552420051c73552420053f72552420072f72552420072c72552420053f71552420053c705524200c7c7598e420063d5498e420065c5398e420065e6598e420065d6598e420071d5498e420065f7598e420065c7598e420069f7498e420065f5498e420069e5498e420065d5498e420069d5498e420061d5498e420065f5298e420065f5198e420065c5098e420047f7558e4200c7c7558e420065c5358e420065e6558e420065d6558e420071d5458e420065f7558e420065c7558e420065f5458e420065d5458e420065f5258e420065f5158e420065c5058e420047f7694e420047d7694e420065e6394e420065d6394e420053f7590e4213e3e6590e420063d6590e420069e6390e420053d7510e421363e6510e420063d6510e420069d6310e4228f1c5310e421147f7654a420065e6354a420065d6354a420053d75d0a420069e63d0a420072d52d0a420072d54d0a4200c7e75986420047d75986420063d5498642006775198642006766598642006756598642007355498642006d66398642006d56398642006767598642006757598642006775498642006b65498642006755498642006b55498642006355498642006765398642006745398642006b64398642006b44398642006775298642006755298642006b7429864200674509864200c7e7558642006775158642006766558642006756558642007355458642006d66358642006d56358642006767558642006757558642006775458642006755458642006765358642006745358642006b64358642006b44358642006775258642006755258642006e7425864200674505864200c7c75982420047f755824200c7c75582420063d54582420055c735954211c7f74595420063f74595420065f73595420047c73595420065c73595420045c73595421247f72595420066f72595420047f71595420047c70595420055c73551420056f725514200c7e75d8d420047d75d8d420065c53d8d4200c7e7518d420047d7518d420065c5318d420047d7694d4213e3e6590d420063d6590d420069c6390d42005ae7290d421363e6510d420063d6510d422871c5310d4200c7f765494212c7d76549420053f74549420063d65909420059e7390942005b6719094200c7e75d85420047d75d854200c7e75185420047d751854200c7e75d81420047d75d814200c7e75181420047d751814200c7f76594421153d74594420047c73594420047f71594420047c70594421247f76550420055c73550420053f76550421263f76550420071f73550420053c73550420071c73550420051c73550420053f725504211e3e62550420053f71550420053c705504200c7c7598c420063d549
  | 21 => 0x671d8843005b571d88431353e75988430053d75988430063d65988430071c5398843005b67198843005b571988431353e75588430071c53588431353e75188430053d75188430063d65188430071c5318843006ad62188431353e75d84430053d75d84430071c53d8443005ae72d8443005ad72d84431353e75984430053d75984430063d65984430071c5398443005ae7298443005ad72984431353e75584430071c53584431353e75184430053d75184430063d65184430071c5318443006b561184431353e75d80430053d75d80430063d65d80430071c53d80431353c75980430071c53980430053f75580431353c75580430063d65580430071c5358043005af7258043005ac7258043005b77158043005b471580431353e75180430053d75180430071c5318043005ae7218043005ad7218043005b67118043005b571180430047e73d91520047d71d91520047e70d91520063f649915212d6d72991520055f73591520055c73591521256f72591520063d64191520053e74d8d520053d74d8d520065f6398d5210d6d7298d520053f7458d520053c7458d521056f7258d520047d7418d520047d7118d520047e7018d520047e76d0d520047d76d0d520065c63d0d520047c7690d520063f6490d520056e7290d520056d7290d520063f7690d520063c7690d521353e7390d520063c6390d520072e7290d520072d7290d5213e3f6290d5213f2f6290d520047f7650d520047c7650d520047e7610d520047d7610d520063f6410d520065c6310d520071d4310d520063e7610d520063d7610d5213d3e7310d520071e7310d520071f6310d520063c6310d520071c6310d520061c6310d521363f6210d521372f6210d520053e74d85520053d74d85520063e74d85520047d74d85520063d74d85520043d74d85520047e73d85520063e43d85520063c43d85520047e70d85520053e74985520053d74985520055e73985520055d73985520ad6d729855209d6f725855204d6d72981520053f74581520053c74581520055f73581520055c735815203d6f72581520057771581520057471581520053e74181520053d74181520063e74181520047d74181520063d74181520043d74181520047e73181520063e43181520063c43181520047d711815200c7f76597420047c73597420047f71597420047c70597421147f76553420055c735534200c7c7598f420047f7558f4200c7c7558f420047f7694f420047d7694f4213e3e6590f420063d6590f421363e6510f420063d6510f420069e6310f420069d6310f422971c5310f4200c7f7654b420053f7454b4200c7e75987420047d759874200c7e755874200c7c75983420047f755834200c7c755834200c7f76596420047c73596420047f71596420047c705964200c7f76552420055c7355242
  | 22 => 0x8a430053f7558a4313d3c7558a4313d3e7518a430053d7518a430063f6518a43005b67118a43005b57118a4313d3c75d864313d3e75986430053d75986430063f6598643006b761986430053f755864313d3c755864313d3e75186430053d75186430063f6518643005ae7218643005ad721864313d3e75d82430053d75d82430063f65d8243005ae72d8243005ad72d8243005b671d8243005b571d824313d3e75982430053d75982430053f755824313d3c75582430063f655824313d3c751824300c7e76d954314c7d74d95430047d72d95430047d71d95430047e70d954300c7c76551430055c73551431447e7694d431465c65d0d430063f6590d4313e3c6590d4300c7c75d894300c7e75189430047d751894300c7c75d854300c7e75185430047d751854300c7e75d81430047d75d814300c7c751814300c7f76594431353d74594431363f74594431363c74594431365f73594431347c73594431365c73594431345c73594431363c43594430047f72594430047f71594430047c70594431447f76550431353f74550431355c73550430053f76550431463f76550430071f73550431371c735504313e3e63550430053f72550430053f71550430053c705504313c7f7694c4300c7d7694c430053d7494c431355e7394c431353e75d0c430053d75d0c432bf1c53d0c431355c7590c432b59d7490c4329f1f5490c430071d5490c43004bf7650c430053f7550c431353c7550c430071e5350c432a71c5350c43004df7650c431355c7550c432ad9f7450c432a71f5450c430071d5450c430059f7650c430069f7650c430071f7550c431359e7550c431359c7550c432a71c7550c431351c7550c432a71e6550c430071d6550c430059f7250c432a71f5250c430059f7150c432a71f5150c430059c7050c432a71c5050c4300c7e75988430047d75988430063d5498843004f67198843004f5719884300c7e755884300c7e75984430047d75984430063d5498443004ee7298443004ed729844300c7e755844300c7c75980430047f755804300c7c75580430063d5458043004ef7258043004ec7258043004f77158043004f471580431353f76594431363f76594431371f73594431353c73594431371c73594431351c73594430053f72594430053f71594430053c70594431353c7598c4313e3e6598c430063d6598c4329f1c5398c430071f7598c431359e7598c431359c7598c4329f1c7598c431351c7598c4329f1e6598c430071d6598c430059d7298c4329f1f5298c430059d7198c4329f1f5198c430059e7098c4329f1c5098c430053f7694c431353d7694c431353e7394c431371e7394c431351e7394c4313e3e6394c430071e6394c430053d7294c430053d7194c430053e7094c431353e75d88430053d75d88430071c53d8843005b
  | 23 => 0x65c63d89541263d74d89540047e73d89540047d71d89540047e70d895412d3d74989540055e73989540055d73989540065c639895400576719895400575719895411d3f74589540055f73589540055c73589540065f63589540065c63589540065c63189540065f63d85540065c63d85540e63d74d85540047e73d85540047d72d85540047e70d85540ed3d74985540055e73985540055d73985540065c63985540056e72985540056d72985540dd3f74585540055f73585540055c73585540065f63585540065c63585540065c63185540065c63d815408d3d74981540055e73981540055d73981540065f63981540065c639815407d3f74581540055f73581540055c73581540065c63581540056f72581540056c72581540057771581540057471581540065f63181540065c63181540763d74181540047e73181540047d72181540047d71181541355e73d92531465e63992530047f72592530047f71592530047c70592530063d641925313d5e73192531365e63192530f55e73d8a530053f7458a530053c7458a530047f7458a530063f7458a530043f7458a530063c7458a530047f7158a530047c7058a531055e7318a530066d6218a530b55e73d86530053f74586530053c74586530047f74586530063f74586530043f74586530063c74586530047f72586530047c70586530c55e73186530067561186530555e73d82530053e74982530053d74982530063e74982530047d74982530063d74982530043d74982530047d72982530047d71982530655e731825300679601825300c7f76597431465f73597431465c73597430047f72597430047f71597430047c70597431347f76553430055c735534314c7d7694f431455e7394f4300c7e7598b430047d7598b4300c7e7558b4300c7e75987430047d759874300c7e755874300c7c75983430047f755834300c7c75583430063d74d96430065e73d96430047d72d96430047d71d96430047e70d964313d3f74552430055c735524300e3f765524300e3c76552430071f73552430071c73552430053f72552430053f71552430053c705524300c7e7694e430053d7494e4313d3e75d0e430053d75d0e430071e53d0e431465c65d0e430071d54d0e4300c7e7598a430047d7598a430063d5498a430047f7558a4300c7c7558a4300c7e75986430047d75986430063d54986430047f755864300c7c755864300c7e75982430047d75982430047f755824300c7c75582430063d545824313e3e76d96430053e73d96430071e73d96430051e73d96430053d72d96430053d71d96430053e70d964313d3e7694e4313d3c7694e4313d3e7394e4313f1e7394e431363e6394e430053d7294e430053d7194e430053e7094e4313d3c75d8a4313d3e7598a430053d7598a430063f6598a43006af629
  | 24 => 0x800100000080000000018000000002006800c00000100b0000002000002801000000600080000000010028010000001001001800e000002800400000000000080000010108000004000005000c012012008000c026001000000800600700100000000010028000004004005002c0080070000010028001000000c00800000900200060000088008000000004000000000300480000000010000004000001000001801200000380000000000038018006000002000000400500600000020000000004016002001801c000000003801000a000000000402000700000180020020010010004001000001c002002000000800000100000040000000018004000000003801000c001000000000600000000000000050010000002001002000400600400000000280020008008000000002001400800500000100100020010014002009000002c00000c00080040100060000010002000001800000600000280000000000008004000005000000000000400080180000010018004010002000800000200700600100000090010000000001000000000c0090000038000004000800000000000380000020000008000000000001800000200100b800400000000300080100020000008002001000800000000100000000040090060038004000000800800000200600000000000000008032000000000000a00100d00000000020000004012007000003000000100180040040020000000000000002000c00000100080480040020000004000004000000000000300000080000010000000000003006801c000003003800c01e0000030000010000000000c03e00200000140000090000000004002000800c000006003800800e001003001800000100000040020000000000002000000000000e0020000004002000001809400200e000800000a005000800c00200500100180000020000014010000001000400000400080040060000008034004008000800400000d000000001000000000000040000010008006000000001400200000280000080040008000000003003000800200300100080020010008008000003000800000001a00080040020060068014024003000800000000700300200060001471d74d8d541465f64d8d541471f64d8d5414d3d7498d5413e3f6498d541355e7398d540065f6398d5413d3f7458d541363f6418d540065d6318d541363f7418d540047d7218d540047d7118d540047e7018d541455e7618d540065e7618d541371f7418d541365f6418d541371f6418d541361f6418d541365f7418d541361f7418d541365d7418d540065f7218d540065e7218d540065d7218d540065c7218d540065f7118d540065e7118d540065d7118d540065c7118d540065f7018d540065e7018d540065d7018d540065c7018d540065f63d8954
  | 25 => 0x3000c00a012002000400000c00600140040000020028010000000002000200100b0028000000000000000400000b8000006000000800800e001000001c0060040008000002000003801c002004005800001c00b001000000000500080080020000000014004002000000000000100200000000050048004002004003000400c00b000001001c0000000008006000001801400400000400000020020000004008001002801400a00500000000080000030000004001000000000000500280100000000048000014003000800000000f00080040120000008000000001000800001e0000008008008004001000400400200080000020000000000000000003801000000200200080020000020000012000006801400200600400140040040010028000000000000c000001003002800200000100040000000068008010001003002800200000000080020020078024008008000801c00400500080080080030010008000008000000001a01200000000000020000010000000000800000000a002800c006003000000c006000000000000200000080100040020020000004002000000400a00000000040040020098000008001001800000800100100040000010000004008000000000000000100380080000010020000000006004800400c000000800400600f0000004002002000001000a000000001c000008001000c00000d000800000000100100000080040010010006001003800801200100f800800a00400280240000000008004006003000800000600400200040000000048020004007009000401a000003800001a000002800001000100000000000010000010018000003000000400100000100140110008000006000000800001e0030008000004000000800c000001000000c00000c0000000010002004800c0220010018008006003001801000000100100000020070008000002000003000c0020050048000006003000001400200200180040000000000010000000005800400a0010000000000003000000c0000030038008006001000801000200000280240000020018000010005001800c00000000080100000050000000000003002003400e00f000004400000000000000080010010000000000001800001200c002001400200600080040000000028000008005000000c0000000008010004004000000c000000000803000600200000000000000000020008000000000c00200b003003400600200100000020030050000012002008000000a005001003c00c00000100000040000010068048015003002c000003000000c02600000000080000000010000000000000000000a00200080000000090090008000004000000400000900200040020040010004000007000001401a00100080080020000000018000009000800c00
  | 26 => 0xef20cd800000006ba00008c5000075b1b105b9000028922f4953352c35a00000b422c811b00000000000000000000000004293e5c0000000000004c000000000000000c4381c0000000000000000000003ab00a40000f200000000fb60a00f32190484309d8b882a3c95b002c4d41d684f210882661884fd53fc4bd824e0e2b206c4c310589d92674e4c000000011248930a548ac07a0496000060b00000003cd88ce3cf874b215c0002ab48bb0b14e1100000003e3032f0a647a900002bc00002cb09bc7040b3873b16680000db4000000056b1f7800000008c10000d552ab800000000000000000000000000000003f44000000056c20f442815d0bb51144bd50000000393c8ec32c00822b940c73db000000000000000c290000d5e0294500000000034f05d2334401b137489611089423a400001640000168c8510fb80003df8000356846a2bd420100000000000cd700003b9404cfb9000000000000000000000324462a1e38bbe1f7400000000f1038800011b4a0b0000b7100004d60a80afd3c644d5032ce2d13cc379000000000002aa15f0a1131b0da50000a271f3c2e40ee0000000000028f0000366c0000000dc100000000000d1703dc2a626e00001a586f8000063e000000000002d00000b3f0000cdf00003080000a8300000000000b8600000000000cde00000002ec00000000000000000000003130000a93047000000009021910f5824940000000bb200000000000000000073e0000b270000c4a0128000000000009b40001ee80001cd05dc29e07af05a880b13acc610000b93023c9e11d288a8061c48237d08741b744b8034c0382d44eea2ff492b08f41b235ec0030008000000007003000001600900b002400000c000000000800300180000080190018000006007000000000600000080100060000000008002003000800400200100080000000030000010000000000000400a0010040000008002000000002a0000028000002001012000000001d00080000040190000040004006000000000a007000000c0000020000008000000000000000800200080040260060028028000007000802c008000000001c002000000801c00400200380080080000010000004002000802000000100a802c0020010018000000003000001400e001000000800a00000000000000030018004004000001800401200900080040000020000000000000000004800a0090010010000005001801000a001000804400a000000000400c001000001c0000000008004000012000000000000000000040000040000044004001000000800000100000000080000028008000013000000000a008000800000000300180040100010000004000000001000801000000080040300030068004002000000002c010007000800001000700
  | 27 => 0x91e0858000000000000008e50d48e413c8c0001190c8b2b18000000000002e400036900000000a43197901f347cdd6000038a0000f750ce40000000000056400017186d6000084415340002880f0800005a11e206660000c740bacb7314787c935e400000000000000000000000000009b500000000000c1400000003a30000000078334dc2c200000003d0400022000002724000000000016b08da2034cdc1954000000080114b8f5437b02bd1e5cc7013d4d250000bc700006dc1420daf00f884c2ce08be1fa051d1908ee70000cbf2c946351e744f62afc42527c86c223dc84512bcde009340892c20aef2aecebe3be861f1078000000000024f03353708000000000000000002714c2100000002a3000000000000000000026000000000002a687f10cb800022100000000000000021f18cc867113400017600000d3c000000038d01ac4a901e02263ff47e9231c0002694297000000000008342e34658000000009d000000000001f7c000313c2a4107000000000003204000091036e000000006f400000008d03734f2600002700000e951448539000074c394c00000000001e586f30000000000000000000000e9005a3fdc0003a5898c128000000010193e0034e0c1023318a4b6e3ddc60e102c012295445921bc0000000fe635f49690000e2c0000d800e184f710900000340b6a0000cfa0000a210d6c9d614b40d91ba8fa113e8dcb115c00020f0a8900007261f040000dc400034ecf50000000026f0fa71194b3104943fb000000025b4fcd1a10d740000e180000eca000000000000682b143e2000071425f44a800006fc16780001e90eab37b466d00000001380d6b000002e22bcfad163c00523d4c361f5800029f800021400000000000000000034d85ba00005c52d7ca640b4400000000000000404167c000000000025d8a3000000003e6ccbd0ef10181af0a0639b0794103c88300009b31e040001c28000349c00022200002778777000000026dc00026445350000eaf0678fa4142840e3814d6600000003e7cd49296400022a426b2a8cc080000fe41e24523000000000000001bf875e3f6c24e04f4cfe32e4000113c0002cccbc31458000000050c00000000a441c10b6800020c8d680000cda3638d8a40702cd000064700003f2267c00006ec00027000be0e606280118090000000037acb2a000007100003fe0c04000018c4581c2c000000049f3d3c000038400018c80001fbcdf50000b8e38880000dd499236b00000000000000000000007390000957287054f00000001f3816c0000370112000000003490000f11000000000000000000000096c5a400000000000000197492900005800904c1100007f338340000000e230be888c38640000000000140400021fc92f20a0000000000000c8c133804d0d07b80bb24a000
  | 28 => 0x7e21e45f5000061d3c946d1000000000000000000f4340200003b90000000000000008251750000207c318360c000305c0002dec9e5000000032580000410f0700000000788bdd00000001c34000000100a3d207eb16b8000377cd2e1ba45910c441721bf400022643d116d47643dd0d5c0ed0f520a305be1dacba41d0451013709be1df80000718b9d33b45923cf4904071caea29ac36a2e64cca0e1c766184ca6d00006a70000736195c5340c34c6000000000000aa5000002a00000000000000000000000008e700000002f00c5b00007b9000000022147aa3bd0000371877a00004cc3b44f5d0508c6427a0e3e0000000250c1f42f886493a68469024ce5113bc0001d600003fec9080000000000093437fcb2c000000036c800000000003bc40350000000000000029044e209b80000000000072839200008f10000aac231800038e413e27f0000000033f00006f007a4242000000022d8000000027c40740003110b4a25c85f624b0033162c03608a0e022b34fbd190c000221c0000000000287800000001dc3f8c3a30000718155cb2606900000000000325ceb0153853107fc4e80000000000000014680001a2400021e847201780000390d962f300002bc000000008b700000000b7800034fc86e0000a5310e0bfc0000000383878d39b80000d405c32b8c0001ee0000000000000000003b4c6ff0000dfa000000001e464c04c04b219644b72cbc58e21b0ebd0b64000000000037d8000000000015940001110f5a1844aff00000000000e1400005eb00005661bb4f150000eb10000da800005dd3afc61c171002d1a7007e00449e735c06c10000fa30000d32374c5ed37101b4000000000000000f1869839e0ce80000da3189455800000002ef43532f10e2601743d600005d012702190dccac70000000092482c358c00000000002c4c65f000086a1f445cf13845931db84fb0000000000027f00000000000000000000025c0344000000000000000f080000848000000000000000151f3000000000c50000000262821e0000baf00000af000100f00000001524bf40b11004108479907800001104a8a0fd4d87000052c00000003a08e0f00000000abcb752b8810111888e20000000042ce4b0000000084000000000000000b3526b000030dc00028a40003a00000000050506c400007684ea000060601dc2ef181c0000b3c0003648000000000037f0bdb00000742c70d261cb42360000ecb0000f600000ab90000000318c0000000b1d0000f8d3c600001b0ccaa383003b0b58f4c192810700002272cb400033ac0003608b9b145c2a9140cafc246c72b000081a339c0f4194c24b075c5bb3e747ca1fd800012a831900000000e5c0591fc8bec00000003fb88b0000000000005782f900000000a2817444db2704cc6000079f000000000
  | 29 => 0x45476a0000000000057a240400000000003e1400000000000000c6d2f287840fbc75613b4073314cf6f0000c1d31f02350064abd1a44b1f007c00036b400016c0e1a094400012f43d4225000028cc000000000000000000000b3b30e875238f064003541a936d42df102055200000000000eba16ac0002c6400000000003590802000047f20e4000000000036c0a81000083b300c35602b4000102400000009972e8c105000085815d41c300000721b1c00027d4dda07c800000000000000ac12cf4191000000020a8fd42050f640000d4e1c48372149400000000003eec4b41410bc817c80e016a090c14247ad0b046c93574fb12d90000000036633380003c00000285ccd8302400036e092a0000000000000027382d53d9800000001ac000005000001412e884263918b6c00007ec19340000000ecd0000000000000000008613c7c0003298177183000000004bc3a48000000000012d8014000010900000003b840fc19b0ab038c4bab000000000000610000000167000000009190000e132b28021000062e1790c9d1d9cd8b000090006bc0000000000183cad900001a132b496026ec09431588e017d089f0a58fd220dce73027c0002810be72b4400000000000aec00032a000011dc7e53c704c92d146db0000a2222b80fe30988063b805c91378fd600000000000a7429b0134053c4b500003ec15449963828000029000000000000adc4cf0e50217389033a31549f310ec00000003d00000e1f00000000000ed00000ce0000062b25bc000000000000000000000a032cd800022b4a5d025c00000000000000000062023b12cc0001e1d0230c98018118400038d8000403800021acc8d2de0a370000db1394800022ac44638c000005ec1141bec12a00002400d703cc05acfca05cc0002dc0c2300003e30c40f100f2400000004353bfc0000f7c000228c00037741db275ce7002e9005191432d31ec2c023f0000357ca8e0df4000377847b2688a462fe4000048000000002db0670b281f48000088800000008cd401c95603c0dbc1cdc000000042a019c6022b545b40000fa23d44a2b0000c102df800019200003e4cedb000020000000ea203047d00000002ddc0000d005e100005452cacf0900007f03a103431e5468100000001ac86e00000639000023a2c58000000000003f423008d065b38bc7a30000c0d385800000006d0000010a3cb8f72056cbe51a7c911238c31c0000cae1f800000db075c2438f0f351cdb418403690ad0c31081800014a42e524f40002c40000350c4ac3c303f414a88a7367c000000005800006ab03b000000000000000d4800000003564000035850f0e840001d4c38f26549490258eb8305800010549370000186000063f00000002858ff03b9400008840003f7c135000000000001cc19bc00005b49db00002
  | 30 => 0x1d20000b563400ace000000000000000000ab41fe0c7229881bc2fec1631ef058132b0000000037600000003fe00003c50c6736d874f3264229143851b2208ec637646c630d06180000000132c00036cc8d9358803420ccb213480b12000000000000002c9000000000000b3027d0000ac4000000000008bf31c4000000000000000840000b4f19f8dc70518abe2f84e6030309f021184940f60d5716f0b5c00000000634f8a38209b00000c4833202433bac000000000029c08eb00006eb277c43338a09e4000022538cc000000000026fc48c0000b1a188c00019a40000000f1e1344000000000012680001138cd43e2c5f92a180002a6000000000000000000000000000009ee377098430b05db3998bd208703231b3cbbf28e07d734e001e30a8d5331aca2f266436f344400035b4bff135c0000000ac80000000321800011f031d104c6122e800002e44fe116c8f551bbc53f1eb05960c2c8413610df800000000b8c0000000389000000100000000000000000000009500000000000055c167000000000000000000fc10a2c4b02a9c0000000fa92db400e2aa86b70d90a42000000031d469a0000b6108b8000020036132d88e132404123b680000000693000000000000000ccc64f000000000000000000000000000000000eb00000000ef400038c80000f00a1b1d24cf8247486030647932c503dc1ca0b850a04b8f2190cb100000000000b4710bce7927a45851f0cadb10146da000000000000000000b980000d6100000002d6800002480a9281c2d213b80000000213242c00033d000028fc00029bc74d00000cf163400026082920000e4d2ce400033ec662000000017e871100000000000a0c00004d000008630e88cdb2b70fbe00000c12c00e6a1628b7a00000ff0000bf5000000009e400028c80002b846cd000100100003e10000692157c0003de894d1fe4ca005907ab000000026200000ae0000000027805143fd0000000326000035bc64b1768c39128817a338495d3f6053e00001e513c450d0000b2e17f4000000035701b892306a8aa00da031400000002bcc0001a0800025a0faf000001d000089807e406a0000bde2acc39e05009750e4c10600006f905f00003a143b600002e7000000039d8fba000084f3e70cc11348f3500000000000d222eb000000000002aa40003018000000000000000002c24b55200c00033a448a3fb40a300008fd3d6ca6100000000000000000000000000090bfc00000000000000329108c00000000000000a2c3d1c55024c000006e81ed302c4ca00988241a98e29000000030c07903c4c00725cc00004000000000185000041a31b8c5f1aa00000000c8e144c000000054622d00000000000000084025900001cd416005d40000000000000000025e40002d48bd1000033220e000f26242ea3
  | 31 => 0x3a78000000000032540000a18fea00000001ab400000000002460ae60000d9c0cecea63460f903e04f683bf8d100568f833cc400000004fe13a4193000043d2ae020802f0000095895e00000002a40c791318bd61064000000000000002e000000003d28b46171c00000003d733e48480000599389c1d805b8cf308dc5d7345809e253cc2e2804045000000024700001510000000030e2e103d226680000fa02e804ec56e0d6053a2c14c6230485e502d429a03b8111315c4533164b62254800000004341e28e3500003471780a3d00000000b5087e0000827408456f33f06be4030fc007ac00011289d13df4bae0000ca93e94bee1a900002dd8ea91ef800029280000000fb30d20000180c0000000000034400000000000000e7a000014d0000000195022d022000035e02470000a8d33b09460720e9700007ed2d980001000b3727d8f30000060400001ae2d00ec3000068e00001470000000000000000000003530156000088f050c668000000d3ac88ed1afcdf02024aec009c4741db40b02eecd6c1334cb73288a3b1e9400008f84c80d44ef7356cec731a0b58000000000004c700000000000000000021a0000000073c6672aa0c0200002641dc83342fa100b391025837e4ea42e68ac20000000328c87209549930d500002138b6700880003bf000005280001044aaf06fc4682108d7a000000038e8c870000e8f00003451c74000000000000000003b780001a6c0001b880000e68965068c0000000e473398000000040624c8000008000000003c33cf077b3b7ccf703b407d000000031010093a24c730000e2a3d70723232408131d8119271832b38b8dd113f0a7f000008d3c90cc500001c922d42ec21882b60000f04000042d00000000000c1b09148a428d00000000000000000007ec000323c9ca0000000000000000002840000000219482910803832c54000000000010c8211000000006d400000000000000f1601ec0000000b74000000000006f62850000343cc15000081500000002280bcd0000d993c38c7e3a801e41bd45bf3ed017f0214f2107bc0000000e8b0000e4007f424a1f107f539587093de04751888000328443f3da4aa1100c00000000002458499408055a398c29d000028d27c40001c140002bd81c035582b31e802a3000000034641650000b1b15d8c5421c02fd10e4a1327b43383f789b933d8c58277400000009aa1dd8000000000000007751460025376c0000524000088c00033c00002d64f6e00004010c18bc6000000006ac8071f1c00018ec0000000fcf3364e7f000010c2708e7c0000d1a1b4c0000000000000000027bc000234c3db04e400039380ce00000001d404402cf81f104085830000000000032a14443de00000003ee00542e003e400000003010835000016825c472e2f2c00000000000000
  | 32 => 0x3f04054bea0e6c5323ea87e605bc2980000e72000022b3794a5f00000000000ebc38100000000c1a3624afe0d7400000000002ce80001fa819f329c000000098d00005b10000fb5148465c1c5400000009a333c476f07d8a100000be93e544a10000f870000bb72b58fec101c2313c4866307c0d9d054ce4534d0f4500000000000ef01f08d13098496e03600001d206720498de23448f4000002e13ad00000000e10000000010606e707589870eb081900000002434721141c8811d7cc3c0be05333ccc954000000015a000013c08ea35d80b80000daa000000000002c900000000000a2a00001b7000000000000000000b0113f42523484a540000f910000000219814b31700100ad45cc00000000000000000006500007b20000bdf1a3c0ae25e83e92af089b0000de8000000000000001cbc2fe0000000259800023ec5223108000000000039540000000000000000000006aa0254ff90a6cef93a28b5b39a454109d4f203d18df22d04ffa2a6400000000003000000000000000000000000a823118000198400000009220fb4e250000fc200001df27482ac0000257126098f06380001674ce4365400000007a108f02f93414fb71a547b508fca75000000000002d805e0000212871321f40000ea83ae395c000000000034309ec160800034bc60900001de2a4400024e46ac3c3474301a4a87000029f000003c000000002680000000000278c5191418eec19c09860ddc47e1ed0000324c7650738c50000000027688310000066125cb6b23d82ca16a80bd327852729a4000270cd413f5c00000008db0000d3e111c00000000000000e3800000000f2c000385cff5000000023910000f6400035cc0000000150000000000004c50000c94000025908c820c34f4d2930a057f00000001ecc8c8000031b1ff80000000000000013a0000000000000036ac0001d6409d2e9c00037980000000572000073d0000bb6000000018548d70000e5f000000005d0000029800022340000000e5c2e78e8e00000000000f630000000000000000003f11d14000065880f0000e000000000099c46e17cc32723a073325dc8c0000006c00002a221c4798000000000000001b8c0000000000000043e08e4ff33be0a9400004311cc8000081430c04349ea1d185530000000157400018f06a20000ece00000001c040001efc0002c8800024244560d883e0048c1080f9812d1a5045d2c3c3b500006c518980003eac4d3000000000000000000000000029e000049d000069e00000003b5c0001e7000018bc00023e406d0468f590000000097c0c83940c1c18280001f640001c5c96b000030726f4852293037a10dc3370608000000039504d8000000011e000081c1ffc00a00009450d18000334c82218f4000378442e0000d710000f172b30b1734ac0000000000
  | 33 => 0x20008821372000000007e3000000000004f8000026c00000000000000355011700000000000000000000000000000000000179c0000ef85ff09a84300000a260f1d011000048e3d5ce9b29a097b2a780003094e99142c6143470000000000028e4b3436883f303d85ad174cbed0000efd24fc7d826381c239746302740bb92d0800023c030a00000000000000000000031680002d4c00007a8fef00001b9000074702a807f00002d73f24d65272c039125400420fc000330800000000e91d08cd508b01813ce00000000000303cda737f8000000027a00007c5249000000002a71c880573b98dc0251c12732f0fb23474ec1000000019ec6d7396000011d800003e81ec16bc6a100000000d0800023280002224000396cba617206832684980340490736ec6a3000071b00000002fc8272293808c00002ab01104be36b897c237c00000003f701d8bf01b288cb2f24e713208000000000000008161480000000000039d495c0000000000000000000000000a631b549ae2b780000000a44057400015a40000000000000000000002463b70d3527d000000003af2be812b1c686f430149ad00bcc3d14ec9a42f9837e0980a5a00000003c6856330b4000000080800005e60000ee3227094009a4588271cd58216c4860000dcc3fd80e6224400000000000000000000000000000002a74000119800000000000000e8300000003aec52b3cb4f370544000204800000007bd00007570000000173455915c41212ad4c3f12b40002fe8676379000018d8cfd23780000440000000004b0000fe7000000018340001ed800003940000750da62b0053c4088e48341876020e86192a5473837dc5140538118057c707122c214361874e03a0b5e13648bc229409c3c0c359338859427e800033100000000000002000000000002eb40003bb800000000000000a1d000000000000000a1cff400000000000000000069900000003e2495f37eca67390c0000000000082c17d0000e030000dea152c22f000011300004df1dc46c83c28d1410f08d13144a722c2800023601a215f46e636780000000c3316e084d0c680000000000000068d130800000000000000c7d000085e23f89ba39ec0002808c7a097800000fc86d382c0003988ae00000ad8000000000001b30000e09000000000000000000000000000000000003bec0002dfc2682348d7f3d8800028b400000000a00000eed0000f1d0000e943f70190320cd2c07dc000151c0002568c5d1e7802c172800000000002800da00000000130000021740623f401971b7856d04b0000000056108a8b32291c000000000025a8baa23e0646000082000003c125b0acb0000bef1a147cb11e8b2900000001cc407018d00002010db71940000000068c22686ec39f8d0a29006a0000000000004ae0cf01fa0000000000
  | 34 => 0x801c41f00fc50000000000077327f870c049000000000000000000033066e2e0cf76107c0001eecb823b54ed20a38c2b313400000aca1200003120000000000082d1878d8f2ba0c1f00008e918c48d406740002de400000004a53ec00000000fa83f9467931040002b742d300009a806945fc18000002e940000f3c13c0cc00000f9cf49224000000000002c384890e100000834b041a7501b29d8f6b2150c9c0000d7700000e716180001530f560df02c709c4830000000006106a53c085bd36446383cfc9591214000194410300001a81bdcde92f040000e580001fe8f982c2c94813fc000215400036400000c24000000000000000001ca836300001480000ccc28600000000000338cd0806e060125fc00029582152ee8dbe2a70bf61764075000059b3eb00003b7430514e0e063728dd03ab40f92cf078f3e7844b27e0a2400000003a84000000000000009833ad40003c146b90e30f8f00004a6199017e00e8325129c0001fd00000124ccf0000aba000064e00008050000548000051f1b7cb8119a800029702483ba03ff31fc0f51cfc7192370000000000021f00002f680003220000000000002b00000068c380000000000090a12485c03f1c88a10d88cc16d85302b4c71c0000fff0000df10000c070000d7c2c440002504931293d01a0000f2900001e70000de7000000015080003da815e269c04123d0a2e295c0003870d3a31dce20020c0000000e882ef04272dbc55600000000dac0002aac0001d743a50ecc4c40b880000000ef61af4000017c5ef208c000026c4800000028353cc3e00000000000000000067a216415c11cc04e15905b3000073a2998b2300005e900000000dfc091000000000000002da400009944522920e3b0bf02ba00002940000000204000012c40002f40000342c00000001d0332c460000000002c40000000f2a27209ab00000000000a5800007d30000d440c0877c1dd00003b1400000003c504882730000000124c000298067700005f70ac80c202c80001c2000000000001a0000000002f33438cef00007e200000000a0800000000002a6c000262c0000d2cfc80598bd93f80589331c0000000bc2000045a1b84d7200000000bd84873decc2f000099b00000003e200000000000138c00000006b33038d333614e3f1554000000028a2bc45a61c3c20300007c6000000018dc000022c000354012839280002f3c04219f4000055400008e08113a1c0000e2c4502e48a9200005151ca400001009812be037436680003cb0f820fe8f2f21707a810080d70000cbe0000ed92ecc0db0000d301b946742d5c2203b209fd000046c2e40ef5000000000009cf00000000000b720000a65217cb5400005ea000000000007e100000001ff0e77000000013601620284ecc0ee86af00006d20000d1b0000000010cb0
  | 35 => 0xc30000a7a0f28f94000000000000002060c3b2df097e2ea000034c4869007000021ec9672ea45c13c2c93b19f0000373cffc1a1c000378c060107448d2e84c8908749850000cff0000000000000031142f0069cec0000000024680000bb82dc35803ea00000001c9c38800006cc3200e7d0000cb20448fae3bbc8f20000bdc00001b019c400015802b03e38b8a000036719486050000ad4000034d3b2408e2374c78000000000004c11ae010e24b41440090000139c0062814f4d00000001bc80002c784e6249c0000f54000251000038546d90000dbf26a400000000000000a0d3ba434c000000000006ce0000b1829c400026bc000021c00000005ee00000000efce1e00000002fe0ff200005e80a70f9a00000000130300000000019940000000000000044c33740000ea4f86168040a04dc4bf39b4385000100d22a8fcc00005ce274c000060c9173d7800000000000e980000000000000000000000000000d4500000000c549a6000000000000002a5c0000754d2402a00003fac0ab000046f20d80000000f420000000093cdd700000000000000120c7540158a6a05c4961000000035d44e4000036000003ce0000b8c0ab4a803340e210000aa426d0a96000078200009f90000bf100000002868eac000038e339431e4048202000000020ac00014980000000b8b00005cb0000b5d000038233c80001ad000036e40002f14116029c00000000001c7c21b3e480004050a51074c99e359c0000ba40002098ae900000001d8881e0000b443f0c00029b8000000000033d400036a4f3b16dcec23b8835e129058c39acb6300c4ab600006e40a0ce9c037092617c0b891de4a733a94a77000057e20f8acf28c46ee3424fdd1f90bd7405c0160698f3400000001c0c00027fc0003a740003c184ce22880001cf0e6515ec000000003d074400037cc06f311c5c202d800019cc000000082e3ad83b034a054a375020a00004da00000000000000292c502326c5a50000000365029035f85df0000000322800034e41d9000c8fa1a5c2ed0bec6cb00007ee037800032e000000003dd0ec4000000000017f8ab1334800000dc5f118b07dc296c00000c0000000000000000000bd40003f88f443aa8d1e39a0cc003e008a247cdbd000000000005670000bd41de044532bcaf9000000019588e6182061a073428504e01f30000a79094000000003800000af4000101e000000030c80000000467205c00000000003090051030ce3400008b3317893a000101635a80ca32e8000000071600003240d7c48418b449136e839d3f4c7db06f8000282800000008ee3c880000fe4b960f94ad01f5040d31249e2000000000005433410000000000000000000000000313899c000094b1e1488e1470aed04b8849081c08623fcac300002240000c353d9c4f42d0cc6626
  | 36 => 0x21000000008a604fc0a221e05e33ca0dd213e40cd0bd00003534adf1e680e340180000c5c0000000f39000039905840003b3c7c81ba01f8365c048340829300003fc0454fc400002181ab80003a882f701540000fe000000000000000eae3d844bb1e6cae700004ba0000ed40000d4000007a71c8000000009360000e120000724000000015c0000000000000007703d94a88115053623ccb49000019502cc587110c000165400018900002df480e32149900f10000047c0001cc00000000000126c1f5312c91200005282168a250474cb32e5468829ec8760000b4e2bdc000098c8130f34d8817549cd0000d030000755000080a00009b110b033e309c6b5000000027704792f802dd00000002a7c00028d4000169c0000b200000000f2b24d400000000dd000000012ad003000078015a8b4c1aa400000000000e04a0e37f478b21d4a7c00006b1404048100000002218f7925e00000000000063c45f000000000000000f6800000000001e300000624d42165ce9131309e636300fb000000005c068b2c80744072c204306000003bcbf7000000001f0e490000c8c1da00000650b870b98b4d000000002640000000eb71ff40003f3855e3ce80003968e59000004d3d4c3160000000016c0000930e61364c9c40000e9f06486160000bb8354843a000041b26600000000000094c0000000eb300000003a4cc201f3432c3660cab2c3490f341ca3a1dfcb650000cc90000000000000000007020000bf300003d33f6800026c800003cc95016a4c922adc9050970c01155000023bc00029480001ac0b500600ea80a8400010ac000000000000000000cc4053000000000000000ab86b6253039f37146170000a080d948c33a9c8d523588001fec000017000035a472c1e889cc33a80000eece1d00001fc0000f842b5cc5234a85373f6400022e4cc3000000c11c400000000000c88ef33c0400000003eb2d2c0003d2c9eb0fd8afb00000001c38b970000000156c0000000f7004a407a14bcb60000000006d8e6f0000000000000017e000000000000c3cfc60dec0000000c690ac478600007f71c78ac93b103911bc45de1a2889d1e98792326800026d800000000002bac61b0000064327c7e70000a7d40083b20e9c2c627ec8532cc00001a4000009eca4d31a848f000000035440000660579000000000000b7000054025d0000375400000000bf00000000000000000000010508a11758706395012f265094e0838be32480e670000a1f35183030000000000025a00000001c0000004cc15414906c03dfc00000000001b5000004c8e810000ffe0c7c4e50000000000095117ec55c2a989063c9c67539d0dc90000f1b30787d5386c0002b905a224500000000e420000000043cdd8297805211701ad10400c0066cb480ca09d83ae40001db000000002
  | 37 => 0x2f4c000000000000000003b5802300000002ec433d000000005606bb0bc418c1f68c6f0e4019a21dc00000009211be80001c94000000065a3d38f6d2a880000000000348c00006280000000b683dcc8950000000000074000000000000e5e00000002c0c00028d8000000000000000000000000000000017b049e000000025887692a2c710066445e292414c0000f7c189c0da37387b10ae44a311ac9e028547512b684550350000255435503480003a1800012201760000f5f39908b821cc0001588d810000e8d000000000000000000fcb24b80000000000000034a00001e6370c00019acc0a00000000000000258c39c38f42092fac1e30000000011cbfe0000a3e3e988ba1f4063a22c40c9103062003c8791308813133340003efc00000004172f38a1919e0ed82c1c00000006d83634000000018b252845b0000000000000000000003dc40000de0000000058400008c200007b70000cbb000000024409f73294dee083c66000003ad000000000001c500001792e7000022780000000000005c8921d8cdef00000000000000000000034b40000000000097400007740003a6000003180002a10aee013cf9620740002ac81692c1888b0000598225c2620e800000000a090c84000000000000009580000fbc294093e00000002ed067f0000000000057323104ec32d028f15dc0000000913368446300002f21240000310c4b90000b0c000085635b82bf14f41e138dc00035280001df4000000000017881fe00000003fa4000000000005480001eb8fa0000027700000df000034124cc0000000cd6245432011c08cf0000ad20a20478240c2be0aa00001ec0b9f00003a8283c9d500000000000000000000000000000000ea329140002750ca42e503b70000fe80000000211c76100000000000a230680c650000cee00002a5000000021a068620bcaf2212ca8532d4f993
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xca4745852008001988e6b0a40100020f61372597100042e41aecaa6200183e87d9154c400143d07b22a9880028ba0b64553100060fb20e6aa62000c1c641cd54c400107f08bb4a7880028720d6510f101350e42cc621e2026a1c8558c43c400107b09bb2a5880020fe1172d96100042f41cecaa4200183c87591548400143906b22a9080028b20964552100060f320e6aa42000c1d641cd548400107b093b4a70800287a0f6510e101350f42ec621c2026a1c8518c438400107b083b2a508002c520d54106100041fc22e5b2a2000a1e83dd7644400183ce629ec8880020fa1f52d91100041f43ea3b22200083e8714364440010b906ba8c8880028720d75191100051ac08a6322200083d87d48644400107b0fa88c8880020f61c50191100042f41cecaa2200085e861cd544400183ec839aa8880030719073551100060f3a0a7b1a2000c1e759d363440010bf0eaa6c6880028761352d8d100050ec26a3b1a2000a1d8414363440014ab02298c688002956047518d100060e3a8e831a200085c87550634400143b09a90c688002876135118d100050ec20a031a2000c1c539d84344001838a63b0868800287a0f6510d101350f42ec621a2026a1c8518c434400145b09a96c4880028b61075d89100052641aa9b122000e0c5310f624400145b09a8ec4880028b61050d891000516c26a43122000a2d849d4624400149906aa0c48800299604531891000706298863122000a2d84d44624400145b08280c4880020f61372594100042e41aeb3202000a1c835d6640400107b0fa94c8080020f61f51990100041ec38a13202000a35819d5640400143906baac808003071cc53590100041ec3ea4b202000c35751c5640400107b0fa8ac8080020f61c50590100042e41aecaa0200085d861cd540400183cc839aa8080030759073550100061ab26e2aa02000c1c751d263040010b90eaa4c608002876135298c100050ec26a33182000a1d841426304001838e829ac608003071d47458c100052ac0ea8b18200085c87551630400143b09a92c608002956075258c100050ec26a2b182000a1d8414163040014ab02282c6080030714f7610c100060e29aec2182000a1c83594430404d4390b318860809a872156310c1000516c26a53102000a2d849d6620400149906aa4c4080038314c439881000516c26a33102000a2d84142620400145b09a92c4080028b612755881000532c0ceab102000a6581d51620400149906aa2c40800299e0554588100070629886b102000a2d84d45620400145b08282c40800299604505881000632b16e2a902000c3576550410400162906aa082080038955162104100054ac30879882000e844358b310400194ce8b164208003319cd62c841000632b12e328020008e4875891004001948e8b122008003311cd6244010
  | 1 => 0xb043b2a218003071d8435443000c3a43ac2a886000e1443585510c04d83cec21ca0180020f61371597200042e41aecaa6400183e87d9154c800143d07b22a9900028da0764553200060fb20e6aa64000c1c641cd54c800107f08bb4a7900028720d6510f201350e42cc621e4026a1c8558c43c800107b09bb2a3900020fe1171d96200042f41cecaa4400183c87591548800143906b22a9100028d20564552200060f320e6aa44000c1d641cd548800107b093b4a71000287a0f6510e201350f42ec621c4026a1c8518c438800161906aa085100020f61076546200041fc22e3b2a4000a1e83dd7644800183ce629ec8900020fa1f52d91200041f43ea3b22400083e8714364480010b906ba8c8900028720d751912000516c10a6322400083d87d48644800107b0fa88c8900020f61c50191200042f41cecaa2400085e861cd544800183ec839aa8900030719073551200060f3a0a7b1a4000c1e759d363480010bf0eaa6c6900028761352d8d200050ec26a3b1a4000a1d84143634800149b04298c690002936087518d200060e3a8e831a400085c87550634800143b09a90c690002876135118d200050ec20a031a4000c1c539d84348001838a63b0869000287a0f6510d201350f42ec621a4026a1c8518c434800146b09a8ec2900028d61075d85200052a41aa9b0a4000e145310f614800146b09a96c2900028d61050d85200051ac26a230a4000a35849d461480014a906aa0c2900029960853185200070a2988630a4000a3584d48614800146b08280c2900020f61371594200042e41aeb3204000a1c835d6640800107b0fa94c8100020f61f51990200041ec38a13204000a2d829d5640800143906baac810003071cc535902000616ba8e4b20400083d87d49640800107b0fa8ac8100020f61c50590200042e41aecaa0400085d861cd540800183cc839aa81000307590735502000616b26e4aa04000c1c751d263080010b90eaa4c610002876135298c200050ec26a33184000a1d841426308001838e829ac610003071d47458c2000526c16a8b18400085c87551630800143b09a92c610002876135158c2000526c16a2b184000a1d84141630800149b04282c6100030714f7610c200060e29aec2184000a1c83594430804d4390b318861009a872156310c2000616bb2a82104000b0c83550420800151b0c21e64100028d61351984200051ac24eb3084000a54835526108001c28a621cc2100028d61352984200051ac20a13084000a3584d45610800146b093aac2100029960a755842000532c16a8b084000a548355161080014cf04aa2c2100038514c43584200051ac26a4b084000e25541096108001d0887992c2100028d610505842000532c10a0b084000c6772585510800194ce8b0c4210003319cd618842000632b92c32804000
  | 2 => 0x954185400051a402a830a8000a358414c615000146f0b218c2a00028d61443185400070a2988630a8000a3584d48615000146b0ba10c2a00028d61542185400051ac20a030a8000c1d7518f415000185aea31682a00030d5d461d05400048e41aeaa0a8000c1d7518d415000185aea31282a00030d5d461505400058c41aa9a02800183e86dd6405000123d07bac80a000307dd4639014000617ba8c52028000c3775186405000307b09b92ca200060f61371594401d60f320e6aa08000a1c83594431004d4390b318862009a872156310c400042e41aeca90800083d86dd1521000183acb39c84200030d59671908400042e41aeca88800083d86dd1511000183acb39c82200030b59672904400041fc32e92808000c1d651cd401000185aca39280200030d59471500400041ec26e4b2e600083d84dc565cc00307d0fb22a9980028ba0b64553300051b40ec8aa66000c1f641cd54cc001838c839aa9980020f6137654b300041ec26eca8e600083d84dc9658c00107b09b8acb180020f61f52992300041ec3ea3324600083d87142648c00143d073aac9180028b60a75592300051ac0ceab24600083d87d49648c00107b0fa8ac9180020f61c50592300060f320e6aa46000c1d641cd548c06b43b0d298871809a87a176410e301350f42ac821c6000a1f86550438c04d43d0abb0871809a87e197510e301350fc32ca21c6026c1e7510d628c00183cc839aa51800307dd84354a301360f3a886b0c6000c1e641cd518c00183eec21aa3180030799273942301360ebb087284600083f845cb654c00107f08b8eca980020fa1f52d91300041f43ea3b22600083e87143644c00107b0fa90c8980020f61f51191300041ec38a0322602685c831d9544c00183ec839aa8980030719073551301350f41eca21a6000a2d84d4b624c00145b083aec4980029320d54d89300070629887b126000a2d84d47624c00145b08286c4980028b613521893000516c24ea3126000a4c83550624c001c18a6218c4980028b613511893000516c20a03126000a3584d47614c00146b083aec2980029520d54d85300070a29887b0a6000a3584d4b614c00146b08286c2980028d61351185300051ac24ea30a6000a5483550614c001c28a6218c2980028d61352185300051ac20a030a600083f845cb650c00107f08b8eca1800217a0e765503000436c10ecaa06000875811d9540c0030790eb22a8180030799073550300060eb20e6aa06036a1e83d94430c04d4390ab208618003075d95410c301350e42cec2186026a1c855d8430c0014390cba88618003075d97510c300058d406ca2186000d19755c0430c04d838ea21ac4180020f61076548300043ac08eca906000c1c7610d520c0030d90eb12a4180038310d62548301360e3a886b08600083d841d9510c0010d
  | 3 => 0x6b0ca00085e839db419400107b09bb663280021b60b76cc6500060fbb08798ca000c1c7498d319400183eec21a63280020fe11760c6500041fc22ec90ca00083f845d821940018caec90843280df07dd873553400060fc30e6aa68000a1c8355263d000143906b2887a009a872166310f401350e42ac621e8000a1c8355262d000183aa939cc5a00030d5527198b400048e41aeaa168000a1c8355261d000183aa939cc3a00030b55272987400048e41aeaa0e8000c1d749cf659000183f0939ecb2000287a0f6590e400050f41eca21c8000a1e83d96429000183ecb39c85200030dd967190a400041ec3eca2148000a1e83d94429000143d07b2c832000307d96739064000617b2ce520c800083d87d94419000143d07b28832000287a0f65d02400042f430e6aa28000a1e86dcd5450051838edb9aa8a009b07dd873551401360e3b0e6aa28026c1f861cd545000123d0c39aa8a009b0721873551400041f436e4aa2800083e86dc55450001a30e7b82a8a016247e1d54d8d401342fc3aa9b1a8000a1d84d4b635000143b09a8ec6a00028761050d8d401341e43aa831a8000a1c83550635000143b08298c6a01624721d5418d400050ec20ea31a802685c87550635004d1390eaa0c6a00a307e1d5418d400050f43aa831a8000a1c87550635004d8390eaa0c6a009a0721d5418d400050fc12a831a8000a1f81550635000143900aa0c6a0002876135218d400050ec26a231a8000a1d84140635000183eea31c86a009a0f2197510d402c48e41aea21a8000a1e83d94435004d43d0bb1886a00028b61352d89400058641aa9b128000e0d5418f625000145b083aec4a00029320d54d89400070629887b128000a2d84d47625000145b08286c4a00028720d541894000517c12a83128000a2d84d48625000161906aa0c4a000383553631894000706aa0c63128000a2d849d4625000149906aa0c4a0002a320d541894000517c3aa83128000e0f83550625000145906aa0c4a00038320d54189400050641aa83128000a2f81550625000145900aa0c4a00028b610531894000517c2c863128000a2d8510c6250001c18a6218c4a00028b613511894000516c20a03128000c1d7518f425000185aea31684a00024720d75509400060eba8c6a128000c2d75189425000146b09a8ec2a0002c520d54d85400070aaa0c7b0a8000e255418b615000146b083aec2a00029520d54d85400070a29887b0a8000a3584d4b615000146b08286c2a00028720d54185400051bc0aa830a8000a3584d44615000162906aa0c2a00038555363185400070aaa0c630a8000e2554d886150001c4aa8310c2a00028d61275185400052a41aa830a8000a9483550615000146f0eaa0c2a000385e0d54185400051a41aa830a8000e1483550615000142906aa0c2a00028de0
  | 4 => 0x3c840143b08284c790803071d05358f210060e3a8e8b1e4200a4d82d5163c84010b90eaa2c790802876135258f210050ec26a2b1e4200a4d82d4563c840143b08282c790802936085058f210060e29eec21e4200c1c535d843c840143906b28879089a872166310f211350e42ac621e4200b0c8355042c840151b0c21e65908020f61070596210042e41aeb3244200a1c835d6648840145b0429cc9108020f61f52992210041ec3ea3324420083d87142648840146b033aac9108028720d75592210060e398a6b24420083d87d49648840186aea38ac9108020f61f51592210041ec38a0b24420085c835d954884010bb0c39aa9108030799073552210060eb20e6aa44200c3564dc5548840149b0429cc710802936087598e210060e3a8e931c420085c87552638840143b09a94c710802876135198e210050ec20a131c4200c1c7414d6388401838ea3a2c710802956075458e210042e43aa8b1c4200a1d84d4963884014ab03a92c710802876135158e210050ec20a0b1c4200a55811416388401838a7bb087108030714d7610e210050e41aca21c4226a1c8598c438844d4390ab188710802c520d54106210054ac308798c420083d841c165484010b906bb2a8908021e201765512100c1f43ec8aa24200a1e83d91544840183ec839aa8908030719073551210041fc22ed29a4200a1c83594434844d4390b318869089a872156310d210054c402c621a4200b0c83550424840164f02aa08490802c520d541052100593c12a820a420083d841c165084010b906bb2a8108060fa1f64550210050f41ec8aa04200a2e82d91540840146d03b22a81080307d9073550210060e320e6aa0420083f845da530840143906b28861089a872166310c211350e42ac62184200c677654521084018ceeca924210802a9a1376484210056341eec9084200a67865d521084018ceecbaa421080319dd9654842100533c32a89084200e2464551210840168906aa24210803a198c43484212cf82298869084200ca4744856008401988e690ac010802b820121580210050f41ec9324a00083f8759064940010db05bb487280021d6077690e500050f41eed21ca000a2d82dda439400146b03bb48728002876126310e500050fc328621ca000a1f8798c439400143b053188728002876066310e500048f41ee8b14a00085e83dd1629400143d07ba2c5280020fa0f7458a500060f41ee8b14a00081e83dd1629400183b07ba2c5280020f21e4358a500041f43886b14a00085e839db429400107b09bb665280021d60776cca500060fbb087994a000c1c7498d329400183eec21a65280020fe11760ca500048f41ee8b0ca00085e83dd1619400143d07ba2c3280020fa0f74586500060f41ee8b0ca00081e83dd1619400183b07ba2c3280020f21e43586500041f4388
  | 5 => 0x8020fe1d65109410050e41aca2128200a1c83596415040183acb39c82a08030b59672905410049ac08e6aa08249c1f761cd541040183f0c39aa82080345a0473550410068ac08e6aa08248c1e611cd541040143906aa4c62096a4720d7510c410050e41aca2188226a1c8598c431044d4390ab1886208028720d54988410060eaa4e7310820083f865d5421040123906baa8420802c520d549044100692aa2e5208820083f865d5411040123906baa82208028720d54580410060eaa0e6b008200c2d541c9601040107f08b96cb988020f61270d973100436c10ecaa6620183c8759154cc40183cc839aa9988030759073553311350e42ac821e6226a1c859d843cc44d4390abb08798802872197510f310060ebb2ea21e6200b1581d9443cc401a2aeb3888798802e160a7110f311360e3a886b16620083d841d952cc401838ec21aa5988061b21d6254b310070621ac4a966226c1c7610d51cc44d83cea21cc1988020f61372596310041ec20e0b2c620083d87d4a648c40107b0fa8cc9188020f61c50992310051ac0ceab24620083d87d49648c40107b0fa8ac9188020f61c50592310060f320e6aa46200c1d641cd548c40145b09a94c5188028b6127598a310052641aa93146200e0c5310e628c40145b09a8cc5188028b6105098a3100516c26a4b146200a2d849d5628c4014cb033aac518802996075458a310052641aa8b146200e0c5310d628c40145b09a8ac5188028b6105058a3100532c08a0b14620083f845cb654c40107b09386ca988028d60754d91310050f418ebb226200a2d821d7644c40146b023aec8988020fa1f52d91310041f43ea3b22620083e87143644c40107b0fa90c8988020f61f51191310041ec38a03226200c1f641cd544c401838c839aa89891687a1a5310d311350e42ec821a6226a1c85590434c4014390caa0869889a872167610d311350e432ea21a6226a1e86d94434c44d838ea21ec4988030719073549310060e3b086a926200c1c641cd514c44d838ec21aa29889b071d443181310041ec26e4b28620083d841c1650c40307d0fb22a81880287a0f645503100517416c8aa0620085d861cd540c40183ec839aa818803071907355031004aac08e6aa06241a1c83594430c40107b09bb2a41880315dd9514c4310062bbb4a6988620083d841c165c84010b906bacc9908028720d75993210051ac08a7326420083d87d4a64c840107b0fa8cc9908020f61c509932100516c14eab264200a1c835d564c8401838e629ac9908030b5d472593210041ec3ea4b26420083d87d4564c840107b0e282c9908021720d76553210042ec30e6aa64200c1e641cd54c840183ac839aa9908030b59372553210052ac08a731e4200a55811d663c8401838ea3a4c7908021721d5498f210050ec26a531e4200a1d84d466
  | 6 => 0x627bb2a49906400c4f7694d320c80107f0eb20c8a88028720d641915100436c10ed21aa201874865c6435440143d063b486a88028b6087690d510061bbb4e321aa227a34865c6435440143b0831886a8802872194310d510058ac0ce621aa200a1f8718c435440143b0431886a880287a006310d510048e41ae9b12a20085c835d3625440143906ba6c4a880307e0d74d89510041e41ae9b12a200c1c835d3625440103906ba6c4a88030de0574d89510061a40ae9b12a20083f8790f625440107b0e21ec4a88021720d76d09510041ec20ed992a200c1c7610f32544030e90cb8e64a88034510d71cc9510060e3a0c6992a200c1c7610d325440107b093b064a88024720d74181510042e41ae8302a200a1c835d0605440183f06ba0c0a88020f20d74181510060e41ae8302a20081c835d0605440186f02ba0c0a88030d20574181510041fc3c86302a20083d8710c605440143906b2887a089a872166310f411350e42ac621e820085c835d952d040183acb39c85a08030d5967190b410042ec30e6aa48200a1d86dcd549045183eedb9aa92089b07dd873552411360e3b0e6aa48226c1f861cd549040123b0c39aa92089b0721873552410041ec36e4aa48200d14731c5549040107b0c382a92089a0f21d5498e410050e41aa931c8200a1d8414e63904b72390eaa4c720802876107598e411342e43aa931c822689c87552639045183f0eaa4c72080287a1d5498e410050e43aa931c8226c1c87552639044d0390eaa4c72080287e095498e410050fc0aa931c8200a1c80552639040143b09a94c720802876135198e410050ec20a131c825b91c8755163904014ab03aa2c72089a1721d5458e410050ec26a4b1c8200a1d84d45639040143b08282c72080307dd66390e411341fc32ea21c8200a1c83594439044d4390ab1887208028720d5498a4100517c12a93148200a2d84d4a629040161906aa4c520803835526398a4100706aa2c73148200a2d849d6629040149906aa4c520802a320d5498a4100517c3aa93148200e0f83552629040145906aa4c5208038320d5498a410050641aa93148200a2f81552629040145900aa4c5208028b6105398a4100517c2c873148200a2d8510e6290401c18a621cc5208028b6135198a4100516c20a13148200a2d84d49629040161906aa2c520803835526358a4100516c24eab148200a6581d51629040149906aa2c52080299e055458a410070629886b148200a2d84d45629040145b08282c520803075d663d0a4100616bacc5a14820091c835d5429040183aeb31a85208030b5d66250a410060ebacc7a0c8200c2d7598b419040143906aa2c12080307dd073595410060fc20e6b2a8200a1c83596435040186acb38c86a08028720d6510d410050e41acb2128200c1d659ce425040186acb38c84a
  | 7 => 0x3781552619080146b09a8cc321002c520d54986420070aaa4c730c8400e155458e619080146b093acc3210029520d54986420054a41aa930c8400a37875526190801c2f06aa4c3210028d20d54986420070a41aa930c8400a1483552619080146f04aa4c3210028d20154986420051ac20a730c8400a378590e619080146b0a21cc3210038514c43986420051ac26a530c8400a3585d0a619080146b08284c3210028d61351586420058a41aa8b0c8400e155498d619080146b093aac3210029960b54586420052a41aa8b0c8400a67825516190801c28a621ac3210028d61352586420051ac20a0b0c8400a1c83551609080183ee839acaa100307e1073595420050e41acb21a8400c2d659ca435080143906b2886a10028720d65909420060eb2ce72128400c35659c6425080125b0439aa82114b07dd873550420060fc30e6aa08400d0e821cd5410801a1b0439aa8211470798873550420050e41aa9318845c91c835d4431080143906b28862109a872166310c421350e42ac62188400b0c835524210801a4aa8b8c84210020fe1975508420048e41aeaa108400a1c83552611080183aa939cc2210028720d54580420060eaa0e6b008400c35541c5601080107f08b8ecb990020f61270d97320043ac08ecaa6640183c8759154cc80183cc839aa9990030759073553321350e42ac821e6426a1c859d843cc84d4390abb08799002872197510f320060ebb2ea21e6400b0d82d9443cc801a1aeb3908799002e16067210f321360e3b086a966426c1c7510d61cc84d83cea21cc1990020f61371596320041ec20e0b2c640083d87d4a648c80107b0fa8cc9190020f61c509923200516c14eab24640083d87d49648c80107b0fa8ac9190020f61c50592320060f320e6aa46400c1d641cd548c80146b09a8cc3190028d61275986320052a41aa930c6400e145310e618c80146b09a94c3190028d61050986320051ac26a2b0c6400a35849d5618c8014cb053aac3190029960b54586320052a41aa8b0c6400e145310d618c80146b09a92c3190028d610505863200532c10a0b0c640083f845c7654c80107b09386ca990028b60b54d91320050f418ebb226400a2d821d7644c80146b023aec8990020fa1f52d91320041f43ea3b22640083e87143644c80107b0fa90c8990020f61f51191320041ec38a03226400c1f641cd544c801838c839aa89913a87a1a5310d321350e42ec821a6426a1c85590434c8014390caa0869909a872167610d321350e432ea21a6426a1e86d94434c801838c839aa49909b071d843549321360e3a887b0a6426c1c7510c604c80107b09b8aca190020f610705943200c1f43ec8aa06400a1e83d91540c80146d03b22a8190021761873550320060fb20e6aa06400c1c641cd540c80129b0439aa81912a8720d6510c320
  | 8 => 0xfbaa862180307ddb7550c431348e43acaa188600c1f765954310c4d2390bb92862189a472177150c431348e428e0a188600c35549c66210c0185aa9394c2218030b55072580430061aaa0e2b008653a1c835966310c4d2390ab94c62189a472157198c431348f42ce1318862691e83dda5310c4d23f0f31ca62189f075da6394c430041fc32e5298860083f865c65310c0107b0d384a621802c360853d88430068a29ce3b108600d14535c76210c4d07f0eb2cc4218024761c53988430050ec30a73108600c35659c66210c01a28a738cc4218034514d71988430048ec38a6b108600b0d8214c6210c01c18a6b10c421802c560453d84430068629ce5b088600d0c535cb6110c4d07f0eb2cc2218024761c53984430050ec30a73088600c2d659ca6110c01a18a7394c2218034314d72984430048ec38a6b088600b158114c6110c01c28a6b08c22180247a1c53980431341e43acab00860091e8714d6010c0143b0c29ac0218034314f725804300616b28e4b008600d0c531c96010c01a28a7b8ac0218030d59471580430068a298e2b008600d0c539c86010c01a18a6b90c0218034514e71180430068a29ae2300860083f87590645480143906b20c8a90021d6047690d5200c36432e521aa400a1e831da435480146b023b486a90030bdda7290d5213d16432e521aa400a1d8418c43548014390ca1886a9002c360a7310d520050fc38c621aa400a1d8118c435480143d0031886a90024720d74d85520042e41ae9b0aa400a1c835d3615480183f06ba6c2a90020f20d74d85520060e41ae9b0aa40081c835d3615480185f04ba6c2a90030b20974d85520041fc3c87b0aa40083d8710f615480123906ba0c0a90021720d74181520050e41ae8302a400c1f835d0605480107906ba0c0a90030720d74181520040e41ae8302a400c2f825d0605480185904ba0c0a90020fe1e43181520041ec3886302a400a1c8359443d084d4390b31887a109a872156310f420042ec30e6aa48400a1d86dcd549085183eedb9aa92109b07dd873552421360e3b0e6aa48426c1f861cd549080123b0c39aa92109b07218735524200686398e4aa4840083d86dc5549080107b0c382a92109a0f21d5498e420050e41aa931c8400a1d8414e63908bb2390eaa4c721002876107598e421342e43aa931c842689c87552639085183f0eaa4c72100287a1d5498e420050e43aa931c8426c1c87552639084d0390eaa4c72100287e095498e420050fc0aa931c8400a1c80552639080143b09a94c721002876135198e420050ec20a131c845d91c87551639080149b05aa2c72109a1721d5458e420050ec26a4b1c8400a1d84d45639080143b08282c72100307dd66390e421341fc32ea21c8400a1c83594439084d4390ab188721003075d663d0a420050e41aa930c8400a
  | 9 => 0x10000050040040001c0020380000501803c0180001a0000e0000080000380a0040a40300001c000008000240000080300601c010120060580100100c00000800010020000000000000480a004000048010220080c8020040380000f00601800000000000000170060180080000000001002000004000040000280780100001802000000010008000020102880e01400003000010004000010260300000300e0200080800200000800004038000030000100180600a000000140140080100000e004008090020000300000006c09800002000010010020400580501e0040100800e004150030000040000100800c0000e0240280600000c0000001a01200c0d00700801411824000064000000040040000700200007804010000008030020000080500e01409817000028000010000000e8030020040a8030020040b00101a0000100500c004008030020080100f00601c0100200001c00000028000010030060080302400c000008010000000480300a0900100d00e000000000040180101800c020000000000000780100c0000400200c000120020020b80c80217e1d6318d542ad0fc22c631aa826a1d84dc863550014ad03b90c6aa002956077218d542850ec24e431aa800a56819c863550014ab03390c6aa14687e117218d5400626b90e431aa826a1d84dc4635500149d05b88c6aa0029360b7118d5423d0ec24e231aa800a4e829c4635500149b05388c6aa12287e117118d540062ab88e231aa838a1d849c0635507343f08b80c6aa00293e097018d5400526412e031aa800a57815c063550014a902b80c6aa09a876107018d5400527410e031aa800a4d821c063550014ad02380c6aa002956047018d540042e41ae3b12a80085e839c362550a183ae831cc4aa0031518e71989540062a31ae3312a80085e87d8d62550a383ee831ac4aa0021720d72d85540042f41ce1b0aa847c1d7418e6155001898c7394c2aa0031318d72985540042f43ec6b0aa848c1f7418d615507183ae831cc0aa00217a1c63581541ce0fba0c6b02a800c4c63dc96055001898c6392c0aa0031518f71581540062a318e2b02a80085c835c860550010b906b88c0aa09a47a0f7458a5326d0f41ee8b14a600c1e83dd16294c0183b07ba2c52989a47a0f74586532250f41ee8b0ca600c1e83dd16194c0183b07ba2c32989a4720d74982532fd0e41ae9304a600c1f835d26094c0183906ba4c12995b075d273d96431360fbb0e6aa4865391f875534390c4d8390d39ecb2180287a0f6598a4313c1ec3eca3148600c37659c46290c0143d07b2cc32189e0f61f651864300617b2ce430c862783d87d976090c0185ecb396c1218030dd9671d82430050f41ecab04865e91e8794d4310c0183eed29a862189a4721d5450c430060fbb2a8a18862691c85dd94310c4d23d
  | 10 => 0x3724572bf4130eb4fd0dd4450000004bd03e2f100000000200000041e00030407e2ea1c600027100047a36a0c64a40f01ee2034064f22a90f93db00019f48120032e20c34d0170002e61063e107901414010807410438c25031a00049b00000035100000000026e2cb00000001900000002e0001fa29b0320000000e30001800002e324e3cf15033f0002cd42a2c430e50a1d300000004844d0003d817e0000005050031720000001d223536300000045f10d19c1b04ee00025a1bb0380001ad2650001611bc0624b40c050b5230005161ab15d0ef4823ae32515e0c325b0330b63eb0000e848c42218a07f05d4de0001330dc05600c0000782c73e00002110e10000004f152a3f61640433214ac15c4b04fa27d0000004c01163be0672201a40af17803c00b2c00df3b20000e93bc13c12d35a19133e46d00039a4db1cc2810290001453e55010004f336b00013e3b629a2173ac0003cd0c728932636c0fe5244ec04e36105326a4190001253e94143fc04d00007c40400002a0003b846e00000a0000000004f00001c03b024b3a445e0002d602840e0001771b349c4bf3290a653306408c0003231cd3c74a303b32a35e4e314c48e3402431c435751829233b4462d52253561e81a535948a00034314722a0b800025e14d4d746f3332e41602fa52b2fe00000053027f1f700000000000000004f4633ba4362f500011b3ce00026328a00000030d20700035247100000000000020625525921600000022c16e3a01665071171952330a24254d20363ee4a73550aa05542921d46717c29e1713a150c4cf24701c00000051d2ce26c0220492b544e38228f0000003660002e125102c17520219d0002390b200000004b32c0000000000cb2e544c37b29f48700044200031c25800038e09f3751310000c42e03ea0002cc26049600047741c10f26637000052c00050e0002dd0000001433fe0000000404a50874680e70203304c82d12db1aa40500037f3c82754654fb3492b41760f421e11e06948f00010c0000003c200038420f0350000001f04d621b2de3dd00000000000028304132b4c523d27e48d0d81e21fd00047e0260000ad4e70801630ce0542312b71692a814e1a309825702539e1490f50001d71c731031119900000000200400000030000050080080000500100000005801000048000040020380480000000c0680503003800001002000090000020080e00a000000000000020000100d0140700e80b0140981400001603c0300300603c01003000000000120300000100303400400001002008098180080000600901c004038030140300880000e0040400600001c0380200a008068030040080400000601c0101700c000158020020080080b01000c00000000020020060040000000201e000000010040200080000a000028020020
  | 11 => 0x28c5290000000000902790240ed08a00019712700000000021c0000591832911594d82da0ea40f20e11c0000000fa3e226d0004f70003aa08900037e50d0003c12640000003884f900051100024c0000000314490000000be0000001d620d2901514764181c94884431bd1292b32412c54d30e61af3a730a1d81024c10002b24742eb4865130b10000001263f00001813380154cd0000000000003011560ee00013545b3484103ed31b42110908147b0000923850002a238d3034d40fb0ba3810003b72854992083cb1e50001ff2d74380181f60bb14b0930000003d217f0d015a10105810e31342b34105a0002bb25c1e925d0b533a1a000000041f21a00045229500044f22419a0000000002f600042000000000015200007b17d09b0003e30ae00025f0000864e41730000000001203ad3900700b70000123f80002be0000000004550000da0000000004a843d00000002100000000035b00015b0004d02fd1d04500910840000002ef2ad18c0d63f100e2d84470bc15400000032000040c0000000000003223a90000000000111900bd17a00044041d4541a63a61f51b81363621a904434e40808f1ba22705c4eb4e013d0d11b710300009a4a11d926b1000000003c000000000047c2c800000000043b3980fc2ab09645c1181f94ff4ed49022300031e0000000001ae16c4701df3f909c0603542820002ec2a324f43f1a72183a24e81244df49e3d017b0001c132d18406536f4940a100019e0003274bb4e53ca3c90a822916f22800036e12a3e647f0005204300d30001484803ff3440fd00024d0000001ec2b041a39f0003d51193ef3743f70005030084172d41c82ed4aa06e01e47916252f2a54780001de3f319411039c24025335313a41551900000018747308500046a4be2f71fc33c03d45106d0d527a18d06313801650807740d05b3bb2d929839424645846100011a42d0000004fc0001854600000ec36d16536825600004a2150e200044a52e11f0ff0a016d0004b94910000000000003733fd00009e2300830001e13bd2d00c20000000004c611135005034700000000000003f4622b95173d70a43fb35c34630f38b0000ab15545337a3d62341573693c449f00008831211328e0000001da3835252ac32f1db0000004ef3600db0004f52bc0000002e92e82af00004c00020431d4350000001144d503403a4f44ae1534d100001a4ca00001b00012808d00000000006f51a4c700000013b0000000000000002373de37816a2c624803043e00000006a1a80004a00001a10e44c900007144801d1f234a41611523a10a0000001224bc4750003160003bf0001be0000000002682b14da2f400000040342f0133d100045d00040a1bf1ed1eb0000003c53e400452d00000051c00000038f00000000000000051210500000000000000000
  | 12 => 0x5323802d330713900000002b00011d27c37d00002d4970050003934a60b443a3421e61070005060000003771b15090004070004690003020003a82010c14b64a915f1863e70955022743d95264e235f3b53b300000005f4cc4f607222b4b81e03d43ec01052121027605e3d34f80f80f224242e2f846423821441b00000018e22d0000000000003f52444fe4dd2bd0001e70000000274723920472863e80ac0004c233d48542308e1e400027229921f1c50000000b02260a90000000014010000de15830900012100000045a0233762b63794e621239b07d24942c0994441ac06b2973ab08b3df3c32322f00003a300037c38a0e00b351f1b234f2800f736533114f31f0752a105243247d00f1dd2941c250f39901f0b92b82a026f44b1930c912f4cb1982ff0000001d15270001922df0002882ee2e22c20000d44393580001cf4261413183170000002dc4ad18b22200023f1f81890941670002210000375100000000000001ea30b4c40bf0000a507628400050400019b28b04239100000013f1e320a2ae30848b1ce1790003240000002a61a234b0453b93151b62f30f12190002454921ca1f112e4093dc2ca00049d0001230002774341d53f24ba2134ab3062360f332839500627b0664311b95282673453361744842734b34dc0e54273971821f31680072704023710a32fc1d44000ca1b443c13023e30031946b49a0974c300038938600006c2540a73da5000000000001460571373370000000000001961880004984590392f90d20614ea0000003cc3c61b50005220002e70000001fe34c4b55312fb00033428d14a00046c5342aa0c52c300000000031406833951e29d3af2cf29600039d38709d0d92a44e14af42851500036722e0000000823354932c94ce0000000003fa00000007a00035d1dc1704330464410732a74b202f3f440b0512094240c833251429c48900000d3a53b40002933961cb1124e93b14d94662d20002780cf4121c330c0d724a0f630518f00036426113416b10b1ef2c12690cd0cc4a20001421fb23b0002872ba4954564831322620000092f220b51b12b00000022f4b100020500012c4b74114372521f423c144
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x120d922197510c3000485644865d4430c04d01c985d97510c30005056447610d520c04d80c8710d6254830005036487610d510c04d8148710d61544300040724d84dc565c800141691d90735532013407a4f845da53c800101c93613765472000407a4f845c765880014149159073552201340724d849da538800101c93610765462000407a4f845c7654800101e93a1f52d912000407a4e87d47644800101e93a1c50d91200040724d87d48644800101c9361f511912000407e5d84d4b634800101f9761351d8d2000407e5d84143634800140d921d47418d200040725d84d48634800101c976135118d200040725d84140634800140d9214c7610d200048524d84d4761480012149361075d85200048524d84d4b61480012149361050d85200048524d84d446148001214936127518520005816485310c61480012149361352185200048524d84140614800101c9361371594200040724d87d46640800101c9361c50990200050324d751c9640800101c9361f52590200040724d87d45640800101c9361c50590200040725d84d4a630800101c976135198c200040725d84142630800101c976135258c200040725d84d45630800101c976105058c200048365883550420800180d7620d54108200048524d84d4661080012149361275984200048524d84d4a61080012149361050984200048524d84d4561080012149361275584200048524d84d4961080016049355042584200048524d84141610800101c93613725971000503a4b641cd54c404d01e93e117694f100040724d84dd952c400101e93e1172d961000503249641cd548404d01c936127694e100040724d841d9528400101e93e1172d951000407a4e87d4b644400101e93a1f51d911000407a4e87143644400101c9361f52191100040724d87d44644400101f9761352d8d1000407e5d84d47634400101f9761050d8d1000505644751d0634400101c976135218d100040725d84d44634400101c976105018d1000505644531d8434400120c9361352d89100048324d841d7624400120c9361351d89100048324d84143624400120c9361352189100048324d849d462440016059114c43189100048324d84d44624400120c9361050189100040724d84dc9650400101c9361f52990100040724d87142640400101c9361f52590100050524d751c5640400101c9361f51590100040724d87141640400101c976135298c100040725d84d46630400101c976105098c100040725d84d49630400101c976135158c100040725d84141630400120c9361352988100048324d849d6620400120c9361351988100048324d84142620400120c9361352588100048324d849d5620400120c9361351588100048324d8414162040012159620d5410410006055d8835504104001604935516210410
  | 1 => 0x10054124d545ca411040140c93550725804100483648865d443cc44d80c8710d6254b310048324d849d6628c40120c936135198a310048324d84142628c40120c936127558a310048324d84d45628c40120c936105058a31136039cd821d7644c44d8167360475d913100503a4b641cd540c4018146460473550310040724d841c165c840101c9361f51993210040724d8714264c840140c935d472593210040724d87d4964c840101c9361f51593210040724d8714164c8401415911d47498f210040725d84d4a63c840101c976135198f210040725d8414263c840101c976135258f210040725d84d4563c840101c976105058f210050564453dd843c840120d9620d5410b210040724d841c1658840101c9361f52992210040724d87142648840101c9361f52592210050524d751c5648840101c9361f51592210040724d87141648840140d921d47498e210040725d84d4a638840101c976135198e210040725d84142638840101c976135258e210040725d84d45638840101c976105058e210050364853dd843884012159620d54106210040724d841c1654844d01e93e117694d210040724d841c1650840140e92d90735502100505a47641cd540844d01e93e117694c21006811908355121084018c07320121580210048364b8798c439400121591e1e6310e50005056477610f329400140d92dd843cc65000407a4f845d9219400101e93e11760865000503a4b861cd54d000141691e1873553400050524d549c662d000140c93552729874000503a4b849cf659000141691e1273d964000505a4f659c6429000140e93d96729064013407e5d84d4b635004d01f9761351d8d400048324d84d4b625000120c9361075d89400048324d84d47625000120c9361050d89400048324d84d48625000120e9620d541894000483e6154d8c625000120c9361275189400048324d84d44625000120c9361050189400050324d7518942500012149361351d85400058124d5418b61500012149361075d85400048524d84d4b61500012149361050d85400048524d84d4461500012169620d541854000485e6154d8c61500016049355362185400058124d5418861500012149361275185400048524d84d4861500012149361542185400048524d84140615000140c935d462505400050524d75185415000140e93dd4629014000505a4f75186405000140e92d90735533000505a47641cd54cc04d80c7360a7559230136051cd819d5648c04d01c9361f52191301340724d87d44644c00120c9361075d89300048324d84d47624c00120c9361050d89300048324d849d4624c00120c9361351189300048324d84140624c0012149361075d85300048524d84d4b614c0012149361050d85300048524d849d4614c0012149361352185300048524d84140614c
  | 2 => 0x5380000000001687197875800958e4000b852808780506006a5b1a82e9cc22a208180000072000001e800001641101e000ae088ec621963a1248a97a3c8960000086a42308200013c62956000564e2163f0664c000071488423c5a8d67a0065402600000001b2001f64f80000000769ae4b9607608c1c1820604e7e85e001944300039a4800154668a86f82e38224429f22492846a3e9489c671f87f1a0510148c9f467874798003795233a04000000900000000000be6602a3b8000007e1b0bc740001d9628e0fa2680032800000005d0000000086000002006913a00000739228080000000002300e11c000a00021c7489810a129184c000000014693000160c43a8407520c002503d0789386e0d00000000729c40003e599046b0821221e6a800000d40117c348008b1f0001b0850000002c6409000010578000020e498f00000011a0a000002d0004d9ba018081c100200400020409002090480400020180002000183c0205038000401018141401018140005170040c00060080008028102a0100020040200048080000030083c0280804000000c020c01014000105000000a0081020040180c04130983c140000000042304000061d0183c080200541648539c76210c014159614e719884300541644539cb6110c0140d9614e729844300503658531c96010c014159614c7158043004856478718c435480180c8320974d85520060320c825d0605484d01c976135158e421340725d841416390801214936135198642004856588355261908012149855163986420048524d849d661908012149361352986420048524d8414261908012149361351586420048524d849d561908012149361352586420048524d84141619080141691e1073595420050324d659ca435080141493596719094200505a47861cd541084d40d96a08735504200541646821cd541080110d9720d54908420054124d545c6421080141493550715804200485644865d443cc8012149361275986320048524d84d4a618c8012149361050986320048524d849d5618c8012149361352586320048524d84141618c84d80e7360875d9132136059cd811d7644c80141691d90735503200603191821cd540c80120d92e1c6310d510060520c815d3625444d8148610d71cc9510060520c815d0605444d01c976135258e411340725d84141639040120c936135298a410048365883552629040120c985516398a410048324d849d6629040120c936135198a410048324d84142629040120c936135258a410048324d849d5629040120c936135158a410048324d84141629040140c935d66250a4100503a4b841cd6550401414935967190d410050524d659c6425040140c93596729054100503a4b861cd541044d41596a0473550410054164a811cd54104011159720d549044
  | 3 => 0x92918181a60a0f87a8e21291e9015840000790000017e2c8b63200a6300c04986068c6211846498e7b9b6168d80c9323423403800772548891600228821de1a17229912708aa4d05c0f244371142b0b0190f68b942000007fa36571c80d92a239bc149ec789021f170480628e8943314c000546d030000026e0fe0000043976689063008029016899100e8005689e7012c00088288003696e00086421400
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x6
  | 2 => 0x4e
  | 3 => 0x124e
  | 4 => 0x138e
  | 5 => 0x94e
  | 6 => 0x8e
  | 7 => 0x128e
  | 8 => 0x150e
  | 9 => 0x98e
  | 10 => 0xce
  | 11 => 0x12ce
  | 12 => 0x168e
  | 13 => 0x9ce
  | 14 => 0x10e
  | 15 => 0x130e
  | 16 => 0x180e
  | 17 => 0xa0e
  | 18 => 0x20e
  | 19 => 0x140e
  | 20 => 0x154e
  | 21 => 0xb0e
  | 22 => 0x24e
  | 23 => 0x144e
  | 24 => 0x16ce
  | 25 => 0xb4e
  | 26 => 0x28e
  | 27 => 0x148e
  | 28 => 0x184e
  | 29 => 0xb8e
  | 30 => 0x3ce
  | 31 => 0x15ce
  | 32 => 0x170e
  | 33 => 0xcce
  | 34 => 0x40e
  | 35 => 0x160e
  | 36 => 0x188e
  | 37 => 0xd0e
  | 38 => 0x58e
  | 39 => 0x178e
  | 40 => 0x18ce
  | 41 => 0xe8e
  | 42 => 0x58056
  | 43 => 0x58956
  | 44 => 0x59256
  | 45 => 0x59396
  | 46 => 0x58096
  | 47 => 0x58996
  | 48 => 0x59296
  | 49 => 0x59516
  | 50 => 0x580d6
  | 51 => 0x592d6
  | 52 => 0xc596
  | 53 => 0x589d6
  | 54 => 0x59696
  | 55 => 0x58116
  | 56 => 0x58a16
  | 57 => 0x59316
  | 58 => 0x59816
  | 59 => 0xb0216
  | 60 => 0x20b16
  | 61 => 0x58216
  | 62 => 0x58b16
  | 63 => 0x59416
  | 64 => 0x59556
  | 65 => 0x58256
  | 66 => 0x596d6
  | 67 => 0x58b56
  | 68 => 0xb4596
  | 69 => 0x59456
  | 70 => 0x58296
  | 71 => 0x58b96
  | 72 => 0x59496
  | 73 => 0x59856
  | 74 => 0x583d6
  | 75 => 0x59716
  | 76 => 0x58cd6
  | 77 => 0xcc596
  | 78 => 0x595d6
  | 79 => 0x58416
  | 80 => 0x58d16
  | 81 => 0x59616
  | 82 => 0x59896
  | 83 => 0x178596
  | 84 => 0xe8596
  | 85 => 0x59796
  | 86 => 0x58e96
  | 87 => 0x18c596
  | 88 => 0xa0596
  | 89 => 0x58b021e
  | 90 => 0x28596
  | 91 => 0x148596
  | 92 => 0x40596
  | 93 => 0x160596
  | 94 => 0x598d6
  | 95 => 0x12c596
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 72
  | 6 => 1725
  | 5 => 4132
  | 4 => 1333
  | 3 => 300
  | _ => 0
def gbR (k i : Nat) : Nat :=
  match k with
  | 8 => packedAt gbK8 (i*15) 6
  | 7 => packedAt gbK7 (i*26) 17
  | 6 => packedAt gbK6 (i*37) 28
  | 5 => packedAt gbK5 (i*48) 39
  | 4 => packedAt gbK4 (i*59) 50
  | 3 => packedAt gbK3 (i*70) 61
  | _ => 0
def gbH (k i : Nat) : Nat :=
  match k with
  | 8 => gbHint (packedAt gbK8 (i*15+6) 9)
  | 7 => gbHint (packedAt gbK7 (i*26+17) 9)
  | 6 => gbHint (packedAt gbK6 (i*37+28) 9)
  | 5 => gbHint (packedAt gbK5 (i*48+39) 9)
  | 4 => gbHint (packedAt gbK4 (i*59+50) 9)
  | 3 => gbHint (packedAt gbK3 (i*70+61) 9)
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 8 => packedAt gbK8 (16+((h/1+packedAt gbK8 (15+(h % 1)*1) 1) % 2)*1) 1
  | 7 => packedAt gbK7 (2040+((h/24+packedAt gbK7 (1872+(h % 24)*7) 7) % 125)*8) 8
  | 6 => packedAt gbK6 (70725+((h/575+packedAt gbK6 (63825+(h % 575)*12) 12) % 2071)*12) 12
  | 5 => packedAt gbK5 (216237+((h/1377+packedAt gbK5 (198336+(h % 1377)*13) 13) % 6598)*14) 14
  | 4 => packedAt gbK4 (83531+((h/444+packedAt gbK4 (78647+(h % 444)*11) 11) % 1760)*12) 12
  | 3 => packedAt gbK3 (21900+((h/100+packedAt gbK3 (21000+(h % 100)*9) 9) % 397)*10) 10
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffff801fffffffffffffffffff0fffff0fffff
  | 1 => 0x3ffffe07e03e03ffc0fff00fff49d13f44e73
  | 2 => 0xfc07ffff8003ffc07ff03fff00f8e61cf8739c
  | 3 => 0x7fffffffc00007fffc00000ff07e0ff83e0
  | 4 => 0x7ffffffffffff8000000000fff800fffc00
  | 5 => 0xfff80000000000000000000000ffffff000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x850800028a84485088104154540128650194a5
  | 1 => 0x22d3b9605422a22d548eba02aa749512744a52
  | 2 => 0x6845dab50043368467a23caa02b8c618b86318
  | 3 => 0x4086ecd9e76804087bcf080c0cde07a0de83e0
  | 4 => 0x8307771e79f3df3e0104103030eff800ef7c00
  | 5 => 0xf3e0781041821830420820c0c0ffffdf000000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 63 gbPos gbNeg, 0xeaa8aaa8eaa8a8a8eaa8aaa8eaa8a8a8eaa8aaa8eaa8a8a8eaa8aaa8eaa8a8a8eaa8aaa8eaa8a8a8eaa8aaa8eaa8a8a8eaa8aaa8eaa8a8a8eaa8aaa8eaa8a8a8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_13285
namespace PEqualNP.Outside.L_meta_13285
open PEqualNP.Outside.L_meta_13285.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 1 := bs0_2_0
theorem alls0 : ∀ k ≤ 2, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_2 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 1 := bs1_3_0
theorem alls1 : ∀ k ≤ 3, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 1 := bs2_3_0
theorem alls2 : ∀ k ≤ 3, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_1_0 : Interval s3Atlas 1 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_1 : Interval s3Atlas 1 0 1 := bs3_1_0
theorem alls3 : ∀ k ≤ 1, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_1 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 1 := bs4_3_0
theorem alls4 : ∀ k ≤ 3, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 68 := block_range (n:=68) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 68 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_96 : Interval s5Atlas 4 96 33 := block_range (n:=33) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 129 := (concat bs5_4_0 bs5_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 45 := block_range (n:=45) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 45 := bs5_5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 1 := bs5_6_0
theorem alls5 : ∀ k ≤ 6, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
  · exact alls5_6 i (by omega) hi
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
theorem bgb_3_288 : Interval gbAtlas 3 288 12 := block_range (n:=12) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 300 := (concat (concat bgb_3_0 bgb_3_96) (concat bgb_3_192 bgb_3_288))
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
theorem bgb_4_1248 : Interval gbAtlas 4 1248 85 := block_range (n:=85) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 1333 := (concat (concat (concat bgb_4_0 (concat bgb_4_96 bgb_4_192)) (concat (concat bgb_4_288 bgb_4_384) (concat bgb_4_480 bgb_4_576))) (concat (concat bgb_4_672 (concat bgb_4_768 bgb_4_864)) (concat (concat bgb_4_960 bgb_4_1056) (concat bgb_4_1152 bgb_4_1248))))
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
theorem bgb_5_4128 : Interval gbAtlas 5 4128 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 4132 := (concat (concat (concat (concat (concat bgb_5_0 bgb_5_96) (concat bgb_5_192 (concat bgb_5_288 bgb_5_384))) (concat (concat bgb_5_480 (concat bgb_5_576 bgb_5_672)) (concat bgb_5_768 (concat bgb_5_864 bgb_5_960)))) (concat (concat (concat bgb_5_1056 bgb_5_1152) (concat bgb_5_1248 (concat bgb_5_1344 bgb_5_1440))) (concat (concat bgb_5_1536 (concat bgb_5_1632 bgb_5_1728)) (concat bgb_5_1824 (concat bgb_5_1920 bgb_5_2016))))) (concat (concat (concat (concat bgb_5_2112 bgb_5_2208) (concat bgb_5_2304 (concat bgb_5_2400 bgb_5_2496))) (concat (concat bgb_5_2592 (concat bgb_5_2688 bgb_5_2784)) (concat bgb_5_2880 (concat bgb_5_2976 bgb_5_3072)))) (concat (concat (concat bgb_5_3168 bgb_5_3264) (concat bgb_5_3360 (concat bgb_5_3456 bgb_5_3552))) (concat (concat bgb_5_3648 (concat bgb_5_3744 bgb_5_3840)) (concat bgb_5_3936 (concat bgb_5_4032 bgb_5_4128))))))
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
theorem bgb_6_1632 : Interval gbAtlas 6 1632 93 := block_range (n:=93) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1725 := (concat (concat (concat (concat bgb_6_0 bgb_6_96) (concat bgb_6_192 bgb_6_288)) (concat (concat bgb_6_384 bgb_6_480) (concat bgb_6_576 (concat bgb_6_672 bgb_6_768)))) (concat (concat (concat bgb_6_864 bgb_6_960) (concat bgb_6_1056 bgb_6_1152)) (concat (concat bgb_6_1248 bgb_6_1344) (concat bgb_6_1440 (concat bgb_6_1536 bgb_6_1632)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 72 := block_range (n:=72) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 72 := bgb_7_0
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 3 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 28, 30),(inputs.getD 2 zero, 26, 30),(inputs.getD 3 zero, 22, 30),(inputs.getD 4 zero, 14, 30)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 4 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 2 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 4 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 33, 41),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 9 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 9, 25),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeaa8aaa8eaa8a8a8eaa8aaa8eaa8a8a8eaa8aaa8eaa8a8a8eaa8aaa8eaa8a8a8eaa8aaa8eaa8a8a8eaa8aaa8eaa8a8a8eaa8aaa8eaa8a8a8eaa8aaa8eaa8a8a8
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 9 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 33 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) (SBf 1) :=
    slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have s2 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 2 zero)) (SBf 2) :=
    slice_correct (ms:=fixRows 4 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
  have s3 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 3 zero)) (SBf 3) :=
    slice_correct (ms:=fixRows 56 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds3 certs3)
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (3936922280 * 2 ^ 32 + 3936921768) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_13285.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,4]⟩,⟨.and,[1,2]⟩,⟨.and,[5,6]⟩,⟨.or,[1,2]⟩,⟨.or,[0,7]⟩,⟨.and,[0,9]⟩,⟨.or,[4,8]⟩,⟨.and,[10,12]⟩,⟨.and,[3,13]⟩,⟨.or,[11,14]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,15⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 9) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3936922280 * 2 ^ 32 + 3936921768) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3936922280 * 2 ^ 32 + 3936921768) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_13285

open PEqualNP.Outside.L_meta_13285 in
theorem PEqualNP.Outside.L_meta_13285 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3936922280 * 2 ^ 32 + 3936921768) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3936922280 * 2 ^ 32 + 3936921768) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
