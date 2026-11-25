import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_15251.Model
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


end PEqualNP.Outside.L_meta_15251.Model

namespace PEqualNP.Outside.L_meta_15251
open PEqualNP.Outside.L_meta_15251.Model
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

def SBf (j : Nat) : Nat := [2, 3, 3, 6, 4, 7].getD j 0

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

end PEqualNP.Outside.L_meta_15251

namespace PEqualNP.Outside.L_meta_15251
open PEqualNP.Outside.L_meta_15251.Model
def s0K1 : Nat → Nat
  | 0 => 0x7
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 1 => 1
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 1 => packedAt s0K1 (i*3) 3
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 1 => packedAt s0K1 (4+((h/1+packedAt s0K1 (3+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffffffffffffffffffffffffffffffffffff
  | 3 => 0xffffffffffffffffffffffffffffffffffffff
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffff8b
  | 2 => 0xffffffffffffffffffffffffffffffffffff95
  | 3 => 0x26
  | _ => 0
def s0Atlas : Atlas := ⟨1,rawDecor 14 s0Pos s0Neg, 0xc000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000c000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_15251
namespace PEqualNP.Outside.L_meta_15251
open PEqualNP.Outside.L_meta_15251.Model
def s1K2 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 2 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt s1K2 (i*4) 4
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt s1K2 (5+((h/1+packedAt s1K2 (4+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffffffffffffffffffffffffffdf0ffc1fc7
  | 3 => 0x6ff0ffe0f8
  | 4 => 0xffffffffffffffffffffffffffffffffffffff
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffff81222ca55b
  | 2 => 0xffffffffffffffffffffffffffffa2e45696c5
  | 3 => 0x144e9ad4e8
  | 4 => 0x888e318b6
  | _ => 0
def s1Atlas : Atlas := ⟨2,rawDecor 29 s1Pos s1Neg, 0xaaa00000aaa00000aaa00000aaa00000aaa00000aaa00000aaa00000aaa00000aaa00000aaa00000aaa00000aaa00000aaa00000aaa00000aaa00000aaa00000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_15251
namespace PEqualNP.Outside.L_meta_15251
open PEqualNP.Outside.L_meta_15251.Model
def s2K2 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 2 => 1
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt s2K2 (i*4) 4
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt s2K2 (5+((h/1+packedAt s2K2 (4+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 1 => 0xffffffffffffffffffffffffffffdf0ffc1fc7
  | 3 => 0x6ff0ffe0f8
  | 4 => 0xffffffffffffffffffffffffffffffffffffff
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffff81222ca55b
  | 1 => 0xffffffffffffffffffffffffffffa2e45696c5
  | 3 => 0x144e9ad4e8
  | 4 => 0x888e318b6
  | _ => 0
def s2Atlas : Atlas := ⟨2,rawDecor 27 s2Pos s2Neg, 0xaa880000aa880000aa880000aa880000aa880000aa880000aa880000aa880000aa880000aa880000aa880000aa880000aa880000aa880000aa880000aa880000, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_15251
namespace PEqualNP.Outside.L_meta_15251
open PEqualNP.Outside.L_meta_15251.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x19c24600492980002da8028018020bf43bd43be42bc42be41bc41be40bc40de30dc30ee20ec20f610f410
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x2087180c200405100cb149439a28a87385050e6ca3214b94a41cc20061c830083a060087808010
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 14
  | 3 => 9
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
  | 4 => packedAt s3K4 (244+((h/4+packedAt s3K4 (224+(h % 4)*5) 5) % 19)*5) 5
  | 3 => packedAt s3K3 (255+((h/3+packedAt s3K3 (243+(h % 3)*4) 4) % 14)*5) 5
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 1 => 0xff83fff803ffffff807fff80fffff807fc7fc7
  | 2 => 0xfffc1ffffc01ffffff807fff01fffff8078ff8
  | 4 => 0xffffffffffe01fffffffffffe03fffffff0ff
  | 5 => 0xf0001ffffffffe0000007ffffffc000007ff00
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x21108259148a42588909168b162c5b2b29b75b
  | 1 => 0x427504af512c94a947522bc0ab56a8a5b45bc5
  | 2 => 0x8423a9325ba9193252474dd5819b35b0a68de8
  | 4 => 0xe84211c46231d1c464647166cd03c6c6c760b6
  | 5 => 0xf7bde0783c1e1f878787e78f1e2070707fe00
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xa8a88080a8a80000a8a88080a8a80000a8a88080a8a80000a8a88080a8a80000a8a88080a8a80000a8a88080a8a80000a8a88080a8a80000a8a88080a8a80000, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_15251
namespace PEqualNP.Outside.L_meta_15251
open PEqualNP.Outside.L_meta_15251.Model
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
  | 0 => 0x5be0ffc1ff801ffffc01ff00ffff0063f8
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffffffffffffffffffffffffffffffffffff
  | 3 => 0xffffefff07ffffffe00fffffffff00fffffc3f
  | 5 => 0x73fff801fffffff00001ffffff00007fc0
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x243e10ba25f68592c71c5fc0cbcb1a61f8
  | 1 => 0xffff804221084a92a8a54924ab4b55556aaedb
  | 2 => 0xffff808442109324d14992493595a6a6b3576d
  | 3 => 0x1108f4211c471d8e2391c6e6c0f8dc7836
  | 5 => 0xe1087bde0781e0fc3e1f8f8f8c0e07f80
  | _ => 0
def s4Atlas : Atlas := ⟨3,rawDecor 47 s4Pos s4Neg, 0xc080c080c000c000c080c080c000c000c080c080c000c000c080c080c000c000c080c080c000c000c080c080c000c000c080c080c000c000c080c080c000c000, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_15251
namespace PEqualNP.Outside.L_meta_15251
open PEqualNP.Outside.L_meta_15251.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x808023260111e004800000a9600360000050993a9385cc25560c80c143408610843a01214a9f166920e3a64a1600447801514080043010c53c558eff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fb40fe40be40fd40fc40bc40f840b840ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x10c00000000019c99b8f47db0000064000150c001817059b4000000005d2cfc00a80000000000e93c0000e00000001054744c8da0c4eccc015400009538680125bca0904510dc7988000160a40001a86005580000f9a400295cbd846c800c000000000001458c3940e440017434249c0101299800b400d9791801acf11dd9c4003c0088ac000000d001d1c00050017c000000494c000109c949042c193014c870851421d590b000000008016521cc1d3430b994000000000168d56c0000080c0004040204041000000a0400040200060606000404040800000800060a32001004000218017a5090ef2a121dbd4943b629287775150ee8a2a1ded4143bc282877a5090af2a12157d4d42ae29a85775150ae8a2a15ed4142bc282857651ccaeaa3995d94632baa8c65cd320caf4a120de54241afa9a835c53506dea4a0db14941bda82837850506dca598db54b31b7294636d528c7aa6218d794f21aea9e435e53886baa710f948421bd284813e5090274a1206e500409f28081ba50102f4a8206e95040dda1881ba431037286206e10c40dda1081ba421037284206e10840dda0881ba411037282206e10440dda9881ba5310372a6206e14c40dda9081ba5210372a4206e14840dd99081ba321037264206e0c840dda8881ba5110372a2206e14440dd98881ba311037262206e0c440dd90881ba211037242206e084409f2a6613d54cc37081986e102309faa2613c544c2dea4985b14930bba8a6174514c37080986e100309f2a6413d54c837081906e102209faa2413c54482bea6905714d20bba8a4174514837080906e100209f2a6213d54c437081886e102109faa2213c54442bea6885714d10b7a92216c524437080886e10010
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x1f00015147a28b270085f2e00c532060edc340071798000800f7ea5110506568e7201b9e4af09a30e45b00002490164d55ba1a741b30cb12082a2c01a001000c0a5cd800204243001c78a87002010206100000224280aad8943102a86250c40acd8543102b06150c40a6d8d42102986350840acd8542102b06150840a6d8d41102986350440aad8941102a86250440aad8953102a86254c40acd8553102b06154c40aa98853102a96214c40ac98453102b16114c40a6d8d52102986354840acd8552102b06154840a698c52102996314840ac98452102b16114840ac98732102b161cc840ac98632102b1618c840e24c8321029b6354440a618d51102ab6254440aa189511029a6314440a658c51102aa6214440aa58851102aa62cc440aa58b31102aa628c440aa58a3110391310c440a698f211029963c8440a698e21102996388440e8484211032b5210130ca148404c3335110130cc144404c31b5310120c614c40483335110120cc14440482386015110c6d4c40443185310110cad4840443285210110
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 45
  | 4 => 119
  | 3 => 64
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
  | 4 => packedAt s5K4 (3525+((h/39+packedAt s5K4 (3213+(h % 39)*8) 8) % 189)*8) 8
  | 3 => packedAt s5K3 (2579+((h/21+packedAt s5K3 (2432+(h % 21)*7) 7) % 77)*7) 7
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x1ffffffffffffe03f03ffffffffffe001ffff8
  | 1 => 0xe01fe03fc07fffffffc0fc07e03fffffe631ff
  | 2 => 0xffe0003fff80ffffffff0007ffc07ffff83e3f
  | 3 => 0xffffffc00000fffffffffff800007fffffc03f
  | 4 => 0xffffffffffff0003ffffffffffff8000ffffc0
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x82a2a186450a0238700b2c69634696340ad6f8
  | 1 => 0xba88ca9293146449b2c05522a9372ad566315b
  | 2 => 0xc8da95250a26a892d5550244db924d66b83a2d
  | 3 => 0x131306362c58d12369a69b70122471b8df4036
  | 4 => 0x1c1c18383060e1c38e38e3871c3801c0f5ad80
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xeaa8c000eaa8c000eaa8c000eaa8c000eaa8c000eaa8c000eaa8c000eaa8c000eaa8c000eaa8c000eaa8c000eaa8c000eaa8c000eaa8c000eaa8c000eaa8c000, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_15251
namespace PEqualNP.Outside.L_meta_15251
open PEqualNP.Outside.L_meta_15251.Model
def gbK8 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x85c0000001c1a8e0052820a800076000c486c4c0200004a226a7a000074447c00008614000054468800000070003200566200000020723840182e8a365a040000000000684228007e3c0000005800001200006e000000006000004e0064003e1066008478500e1606003a5e002a301e002c000024000000003426008c000000100040010208301000820d00001002020000017fd50057f54017f95005fd54005f55005fc54017fd4c057f5300ff94c05fd53005f54c03fc53007fd0c03fe43007f50c03fc43017fd4805fe52005f94805fd52017f148057c52007fd0801fe42007f50801fc4200ffcc801fe32007f4c803fc32017fd4405fe51005f94405fd51017f144057c51007fd0401fe41007f50401fc4100ffcc401fe31007f4c403fc31007fc8401fe21007f48401fc21017fd4005fe50005f94005fd50017f140057c50007fd0001fe40006f90001fd40007f10001bc4000ffcc001fe30007f4c003fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xa4000df9452006ef8a2900037e504801bbe2824000ef90120007788090003fb2048001f71024009bfd9420006feca100027f65080057f3284009bf59420015f8ca100277c65080053e3284000bfd9020005fcc810002fd64080017e3204009dfd5020006faa810002ff63080037f3184000bf58c2000df8c6100277f5308001bea98400cbf98820006fca4100277c5208017f7990400bfb0c820005fcc210002fd6108001bf2884009df14420007dc4210003ec21080157f3004000df9402004ef8a010003fb4008001df2004000ef10020007f08010003b84008001f79004000fe88020007da4010003f9200800d7fb2e2002bf99710036fccb8800a7e65c400d7eb2e2000df59710004facb8800afc65c40017fb262000bf993100077cc988002be64c40017eb262000ef593100057ac988002fc64c400dbfaa62000df55310005fec788006fe63c40017eb1e2001bf18f10036fea7880037d53c40017fb162000bf98b10005fac588002fc62c4001bf2962006df14b10006fca38801b7c51c4001bf2862006df14310007f68188003be40c4001de2062000fe10310007708188012ff65840057f32c2004df99610014fccb08012fd6584001beb2c20009f59610015f8cb08002ff64840017f3242000bf59210005f8c9080137f5484001beaa42000bfd8e1000dfcc708002fd63840037e31c2004dfd4e10006faa708002ff62840017f3142000bf58a10005f8c5080037e5284009be2942007bf58610006fca3080137c5184011fb98c2008fd0c610007ee4308003f421840077f3042000df94210026f8a108003be4084001de2042000fdc4210007f6210801eff6544001bfb2a20009fd9510015fcca8801efd65440057e32a2007df19510014f8ca88002ff6444001dfb222000afd9110005fcc888002fd64440017e3222000ef1911000578c88801f7f5444001beaa22000bfd8d10007bec688002df63440037f31a2000bf58d1000df8c688003dc63440036e31a2007dfd4d10006faa688002ff6244001f7b122000bbd8910005fcc488002fd62440017e3122000fb18910005d8c4880037e524400fbe2922000df9451003ef8a2880037e504400fbe2822000ef90110007788088003fb1044001fb0822003bfd9410006feca080027f65040057f3282003bf59410015f8ca0800f7c65040053e3282000bfd9010005fcc808002fd64040017e3202003dfd5010006faa808002ff63040037f3182000bf58c1000df8c60800f7f5304001bea982000bfd8810005fcc408002fd62040017e3102000df9481001ef8a40801afe6104001bf2882003df1441002fee6208017f43104001fb9082000fd08410025fcc0080037e5004007be2802000fed00100077c8008003bc4004001fc2002000ee10010007ee2008003fa1004001fa8802000fe44010
  | 1 => 0x7bf3110001df1888000ef4c44008f786220003bf2110001df1088000ef48440007784220003be60100275f3008000ee980400977ea02004bbb5010025df2808000cf940400977aa02004bbc50100259e2808012ee1404009670a020047bf3010023de1808010bfd9630006fecb180027f658c0057f32c6010bf59630015f8cb180437c658c0053e32c6000bfd9230005fcc918002fd648c0017e3246010dfd5230006faa918006fd638c003bfa9c6001df54e30005fcc518002fd628c001bf2946010df14a30007bc6518007dc328c0017f30c6000bf58630006fca3180437c518c001ef18c6001f70c63000dfcc1180037e508c021be2846000fed02300077c8118003bc408c001fc2046000ee1023000fbe6118007fb308c003fc184600fbfd9530006feca980027f654c0057f32a600fbf59530015f8ca9803f7c654c0053e32a6000bfd91300077ec898002bf644c0017f3226000bf59130005f8c898003bc644c0015e322600fdfd5130006faa898006ff634c003bfa9a6001df54d30005fec498003ef624c00177b126000bf18930007d8c498002ec624c001bf292600fdf14930005fec298003f7614c0017bb0a6000bf18530007e8c298002f4614c001bf28a600fdf1453000dfec0980037e504c01fbe2826000fed01300077c8098003bc404c001fc2026000ee1013000ff66098003de304c003ee1826001fe0c130065fecb9000afe65c8019bf32e40029f99720065facb900037d65c80013eb2e4002bf19720005fec990002fe64c8001df3264000af99320005fac990003bd64c80015eb264000bf19320066fea9900037d54c80017fb1e4001bf98f20005fac790006fc63c8019bfa9e4000df54f20006fca5900337c52c80017f30e4000bf58720006fca3900337c51c8001bf286400cdf14320007f68190003be40c8001de2064000fe1032000770819002aff65880057f32c400adf99620014fccb1002afd6588001beb2c40009f59620015f8cb10002ff64880017f3244000bf59220005f8c91002b7f5488001beaa44000bfd8e2000dfcc710002fd63880037e31c400adfd4e20006faa710036fd6288001bf294400adf14a20077de651003bec32880017f30c4000bf58620006fca31002b7c5188001f710c4000fb0862004dfcc1100037e5088015be2844000ef90220007788110003ef2088001fd904400dbfd9520006feca900027f65480057f32a400dbf59520015f8ca900377c65480053e32a4000bfd91200077ec890002bf64480017f3224000bf59120005f8c890003bc64480015e322400ddfd5120006faa890002ff6348001efb1a4000b7d8d2000dfcc690002fd63480037e31a4000f718d2000db8c6900377f5348001bea9a4000df9492006ef8a490002ff6148001fbb0a4000bdd8520005f8c290003f461480017a3
  | 2 => 0x40004fecb2000afe65900277eb2c8002bf1964009ef8cb2000a7c659002b7eb248013dfd524009f7ea92004f3f5490027df2a48000df5524009f7aa9200033d5490027de2a48001bf98e40005fac720006fc6390027bfa9c8000df54e400077e872005bbe4390001dea1c8016ef10e40005fcc520002fd6290001bf2948013df14a400077e8520003be4290001dea148000ef10a40005fcc320002fd6190001bf28c8013df146400077e8320003be4190001dea0c8000ef10640095fcc1200037e5090027be2848000efd0240007f6812004fbf65900019fb2c8013ef9964009f7acb2004fbc65900279e32c8000efd8e400b77cc720003bd639002dde31c8013efd4e4009e7ea72005bbe5390027dea9c8000cf54e400b778a720003bf6290001df3148000ef58a4000778c52004fbf5290027df2948000cf94a4009f7aa52004fbc52900279e2948016efcca400077c6520003bd329002dde1948000efd86400077cc320003bd6190001de30c8013efd464009f7ca3200033e5190027dea8c8013ef1464009e78a32005bbf3190001df18c8000ef4c6400b7786320003bf2190001df10c8000ef4864000778432004abe6090027dfa848013ef942400067ca12004fbd5090027de2848013cf142400b77e612005bbc309002b7fb2a8000dfd9540004fecaa000afe655002b7eb2a8002bf195400aef8caa000a7c655002bbfaa28000df55140005fec6a0006fe63500037e31a8015dfd4d40006faa6a0002ff62500017e3128000df949400aef8a4a0002ff61500017e30a8000df945400aef8a2a00037e505002bbe2828000fed01400077c80a004aff65100057f3288012df99440014fcca2004afd6510001beb2880009f59440015f8ca20052fe6410025bfaa08012efd50400967ea82004bbe5410001beaa08012ef550400067aa82004bbc54100037f3188000bf58c4000df8c62004b7f5310001bea988000efd0c4008f7c8620003bd4310023de2188000bf98840005fac4200037e5210025be2908000efd08400077c8420003bd4210001de2108000bf98440005fac2200037e5110025be2888000efd04400077c8220003bd4110001de2088013bf98040097f6a0200037e5010025be2808012fe14040096f0a020003bf4010001fd2008000ef50040007f2802004bbf6510025df3288012cf994400977aca200033d6510025de3288000efd8c4008f7cc620003bd6310023de3188012efd4c400967ea620047be5310025dea988000cf54c4008f78a620003bf6210001df3108000ef5884000778c42004bbf5210025df2908000cf948400977aa42004bbc52100259e2908011efcc8400077c6420003bd3210023de1908000efd84400077cc220003bd6110001de3088012efd44400977ca2200033e5110025dea888012ef1444009678a22004
  | 3 => 0xf32e42029f997210d5facb908037d65c84013eb2e4202bf19721005fec990802fe64c84017eb264200bf193210d6fea9908037d54c84017fb1e4201bf98f21007bcc790806de63c84017eb1e4200f758f21005bac790806fc63c8435bfa9e4200df54f21006fca59086b7c52c8401bf28e421adf14721007ee8390803f441c8401fb18e4200fd4c721005fcc190802fd60c8435be2864219bfd9621015fccb108677e65884053f32c4219bf59621006facb108027d65884057e32c4200bfd9221005fcc910802fd64884017e3244219dfd5221006faa910802ff63884037f31c4200f798e2100dbcc710802fd6388401eeb1c4200b758e2100df8c7108677f5388401bea9c421bbf58a21006fca5108677c5288401f7a144200fb10a21007dc6510803ed32884317f30c4200df946210cef8a310803ef2188401fb90c4200bf98221005fac1108677c50884377fb2a4200dfd9521004feca9080afe65484377eb2a4202bf195210def8ca9080a7c65484017fb224200bf99121005fac890802fc6448437bfaa24200df55121005fec690806fe63484017eb1a4201bf18d210defea6908037d5348401bf292421bdf14921006fca29086f7c5148401fb90a4200fb88521005fec090802fc6048437be2824218bfd9421006feca108027f65084057f3284218bf59421015f8ca108637c65084053e3284200bfd9021005fcc810802fd64084017e3204218dfd5021006faa810802ff63084037f3184200bf58c2100df8c6108637f5308401bea98421abf98821006fca4108637c5208401f7a104200fb10821007dc6410803ed32084337f3084200df944210c6f8a210803f74108401fa2084200fd8c421007ea6210803ef2108401fb1084200fb48421007ea4210803e521084017f3004200bf580210c6f8a0108037f6494001bf324a000df59250004fac9280037c6494001bfb1ca017df98e50006fac7280027d639402fbe31ca000dfd0e500befc87280037d439402fbe21ca000dfd8a50006fcc5280027e6294001beb14a000df18a50006fe85280037e4294001bea14a000df10a500befe65280037e3294001be994a017df0ca50006fec3280037e61940013f30ca000df58650006f8c3280037f4194001bf20ca000df50650006f8832805f7f3194001bf18ca000df4c6500bef863280037f2194001bf10ca000df48650006f8432800b7e60940053f304a002de982500befe612805f7c30940297fb2e8002bf997400a6fccba000a7e65d00297eb2e8000df59740004facba000afc65d0029bfaa68000df5534000dfcc7a0002fd63d00037e31e8014dfd4f40006faa7a0002fe62d00017eb168000df94b400a6f8a5a0002fe61d00017eb0e8000df947400a6f8a3a0053fb50d0001bf2868014df143400a7f0a1a00537850d00277fb2c8000dfd96
  | 4 => 0x8027d6394445be31ca200dfd0e51116fc87288037d4394445be21ca200dfd8a51006fcc5288027e6294401beb14a200df18a51006fe85288037e4294401bea14a200df10a51116fe65288037e3294401be994a222df0ca51016fcc32880a7e6194405bb30ca222dfcc651116f863288037f6094401bf304a2009f98251006fac1288037c6094445bf984a222df0c251105fecba080afe65d0441bf32e82029f99741105facba08037d65d04013eb2e8202bf19741106fea9a08037d54d04037f31e8200bf58f4100df8c7a08837f53d0401bea9e8200bf98b41005fac5a08037e52d0441be2968200df94741106f8a3a0802fe60d04017eb068220df143410fdfecb208037f65904013fb2c8202bf996410fdfacb2080afc659043fbe32c82029f1964110dfac92087f7f5490401beaa48201bf98e41005fac720806fc639043fbfa9c8200df54e41005fcc520802fd6290401bf294821fdf14a410f5fcc3208037e519043fbe28c8200efd0641007ee8320802fe60904017eb04821fdf1424110dfecaa08037f65504013fb2a8202bf9954110dfacaa080afc6550443be32a82029f1954110efea8a08037d54504017fb1a8200f7d8d41005bec6a0806fe63504037e31a8200f718d4100db8c6a08877f5350401bea9a8200bfd8941007dec4a0802ef62504017e3128200fb18941005d8c4a08037e5250443be2928200df9454110ef8a2a0803f74150401df20a8200bfd8141007f6c0a0802fb60504017e3028200fe18141005f0c0a08877c505043d7fb288202bf994410f6fcca2080a7e651043d7eb288200df59441004faca2080afc65104417f320821edfd5041006faa820806fe63104017eb188201bf18c410f6fea6208037d53104017f3108200bf58841006fca42087b7c521043f7f3088200df944410f6f8a220803bf4110401fb2088200ef50441007ea8220802fe60104017eb00821edf140410edfecb188037f658c4013fb2c6202bf996310edfacb1880afc658c43bbe32c62029f19631005fec918802fe648c4017eb246200bf192310eefea9188037d548c4037eb1c6201dfd4e3100efaa718803df438c403ee21c6200bf98a31005fac5188037e528c43bbe2946201f7cca31007ba6518806fe618c401bf28c621ddf1463100fbe6318807f7318c403fa18c6200bf98231005fac1188777c508c403ee184621cbfd9531006feca988027f654c4057f32a621cbf59531015f8ca988737c654c4053e32a6200bfd9131005fcc898802fd644c4017e322621cdfd5131006faa898806ff634c403bfa9a6201df54d31005fec498802fc624c401bf292621cdf14931007bc6498807dc324c4037fb0a6200df945310e6f8a298807f7314c401ef18a6201f70c53100fe86298802ff604c4017e302621cdf141310d5fecb9080afe65c8435b
  | 5 => 0x4143006fec9290037e6494801beb24a4009f59252006f8c9290037f6394853bf31ca400df58e52004fac7290a77c6394801bfa1ca429df90e52006fa87290a77c4394805bf314a4029f98a52016dcc5290a77f3294853be194a400dfd8652006fcc3290027e6194801beb0ca400df1865214efe63290a77c3194801bfb04a400df98252004fcc1290037d6094801be304a429dfcc25214ef8612909eff65d08057f32e8427df99742014fccba109efd65d0801beb2e84009f59742015f8cba109f7f54d0801beaa68401bf98f42005fac7a1006fc63d084fbfa9e8400df54f42006fca5a109f7c52d08017f30e8400bf5874213ef8a3a1002fe60d08017eb068427df14342135fecb210037f65908013fb2c8402bf99642135facb2100afc659084dbe32c84029f19642145fac92109b7f5490801beaa48401bf98e42005fac721006fc639084dbfa9c8400df54e4212dfcc5210037e529084dbe2948400efd0a42007de8521002fe61908017eb0c8426df14642005fcc121002fd609084dbe2848428bfd9542006fecaa10027f65508057f32a8428bf59542015f8caa10a37c65508053e32a8428dfd5142006faa8a1002ff6350801efb1a8400b7d8d4200dfcc6a1006fc6350801ee31a8401b718d42146fea6a10037d5350801bf2928428df14942007de84a1003be42508017fb0a8400fdd8542005eec2a1002fc6150801fa30a8400bd18542146f8a2a1002ff6050801fdb028400bed8142005f8c0a1003f860508017c3028428df1414212dfeca2100afe651084bbf32884029f9944212dfaca210037d65108013eb288402bf1944213dfcc8210977f5410801beaa08401bf98c42005fac621006fc631084bbfa988400df54c42135fcc4210037e521084bbe2908400efd0842007dc8421003bd4210801f6a108400bf98442005fac2210977c51108017f3008400bf5804212ef8a021092ff658c801bfb2c64009fd9632015fccb19092fd658c8057e32c6424df19632014f8cb19002ff648c8017f3246400bf59232005f8c9190937f548c801beaa46401bf58e3200efea7190077d538c801efa1c6401f710e3200dfcc5190037e528c849be2946401f7cca3200fde6519007ec328c8017f30c6400bf58632126f8a319007df318c8017f3046400bf58232126f8a119007dc308c8477fb2a6400dfd9532004feca9900afe654c8477eb2a6402bf1953211ef8ca9900a7c654c8017fb226400bf99132005fac899002fc644c847bfaa26400df5513200dfec6990077f534c803bea9a6401bfd8932006fca49908f7c524c803f79926400f78c93200fb86499007ec324c8017fb0a6400bf1853211ef8a299007dc314c8017fb026400bf1813211ef8a0990037f6494401bf324a200df59251004fac9288037c6494401bfb1ca222df98e51006fac728
  | 6 => 0x300c00400200300200300300401b00100100700000b00000700100700800300600400501400000500000400000000000000600100000000b00300801300200001200c01200200600800100800700800001000300700200000000100000200100000300003000500100100201700200000100102100100700100100800100a00600000001900400100000b00300100b00200d00700100000600000002e00000100600200500000700100100200002d00000600600100600000000200100300a00001800702201100200200000000400600e01200200000000801500700100000000600400000000800300500000200000100000000000200000200600600100000700100800a00200500800000300100000200000101500100700200000200100000500600400500500000f00000000500000000300000200600100400400500300100800100700200300201200100000300800100000200100401200600200000700200900000200000000300000000700000100000300100100400200000a00100500601000300000300301700200000000000400700200600200000000200200000700000000500a00000000700900100200000100000100000000600301d006004001002003000000003000001011000001011003016fec8aa00a7f64550059fb22a800dfd8d54004fec6aa0b37e6355001beb1aa82cdf18d54166fc86aa0b37c4355001bfb12a800df98954006fac4aa0037c62550013e312a82cdfcc954166f864aa0037f6155001bf30aa800df58554006f8c2aa0027c6155059bf98aa82cdf0c554006fec0aa0037b6055001bf302a800df58154006f8c0aa0027c6055001bc302a8009e18154166fe60aa0b37c3055001bfb22a6009fd9153006fcc8a98037d6454c01be322a601dfd8d5300cfec6a980b5f6354c03bf21aa601df10d53006fec4a98037e6254c01beb12a600df18953004f8c4a98077f3254c03be192a600dfd8553006fcc2a98037d6154c01be30aa6009f1855300efe62a98077c3154c01bfb02a600df98153006fac0a98037c6054c013e302a601dfcc15300ef860a98aeff65d0c057f32e862bdf99743014fccba18aefd65d0c01beb2e86009f59743015f8cba1806fe64d0c57bfaa68600df5534300dfac7a18077f53d0c03bea9e8601ef90f4300fbc87a1807bc43d0c017f3168600bf58b4315ef8a5a1807dc32d0c017f30e8600bf5874315ef8a3a1807dc31d0c017f3068600bf5834315ef8a1a18aaff6550c057f32a862adf99543014fccaa18aafd6550c01beb2a86009f59543015f8caa1806ff6450c55bfaa28600df5514300dfec6a18077f5350c03bea9a8600f7d0d4300f7c86a1807bc4350c03ee21a8600bfd8943005f8c4a18ab7c5250c017fb0a8600bf18543156f8a2a1802ff6050c017e302862adf1
  | 7 => 0x1c82e4fa07e98691a000000ae042a3982b010836e1e696400080277c2120d2b465e20000003842dab1ea3a114aee20e18a3423102d20623700004880009747c8000410b22b0e9ca00062c1264440005a8690a1e1d88600006caa748ae2bc4c04220d6a2cabe8f49946720000000005760002a60008f28d079a1806ac0b8636000000a0662000000022446270a10c9700006b87e68ac7ee11cada3180000000007d21d200070600035c0005080000009660000007306c20005ee478740540b443529542ee408ab855e0000e20268665701a401058e0aa0004da2007580000f03a8aeab406ea0c6000a5281424c80a68607a00047c1f86cc0a492a7722822e200077eae204a57aace79e1ec55a81a0000000fa366b3caa44820008cc0000009faadc74e4a200662666e1726f6656532af01d68caa8e0fc17434825e9c2a222c458808471a4e4ad6710050ac414a0aca9c4bc2f23f68f07a200000013c0005f68900002ce6f0b1400027e9ea93c8860007f822000000069e4dea863501901b800094405400000000021e7fa00020400001a68095200000072063aa0800000036ab360000001aaa8a1a2000000b2a28c000218a70000a661e42e60000009fc27600000060e22aa5e0000ee4f000053a00008a0003b8a7c1e000000015800076e0007be9b422e0cc0000007e00000009f29c0698a263dc324a8c2927a6000ae60000000006765ae5fa3b20e043e0006124d20009a296a00050298c430202ab0892092a287cc6c49209d2a940d84b633e738000aa2ae8000000a1a26284056a32c1689885ce1f697c0bc8dc0000008ea0000000003089320003200000245680006ec0004600003e40005540004f45de0000000003cc59e00025a0009a600a0009c4906000acc0009e26789301b49e400093a19a02000014c7a881e00085669400000090a3c20b60004b296c0005565485c80345f80005ac70c23641a85867a00099800000042600000051823e0000000003600004860000007b68be7247625b087265c8b816039400040ea54714ad2000b2e000000a4087e00e7f673640a0000007da0008d44be00000602000000200100000300000e00400200200201000200000500000400800200200000400000500000500000700000300800300900000000200000100100700000b00500100000e00001500600100400400000200000600200000300000100100b00101000f00100100600700600001101000200a00900900900600101f00d00300000100000000200001600000600400500700d00000200000c00100201300200900100100000400100100100000000600000e00500201501d00000900100000000000000400300300000200000d00002f00200000300000a01d00200000101b00100e002000000000002000000001000002004000000001000
  | 8 => 0x83f0aaa8289422228b20000000003bc4560000000006443ce9bc0000000321641020002706386d46480002607880000002903fe6e000008600000059c9221c4a040000125e617c01c89a000aba6020e46e6a2a75c9fe09c67e000000000b280005fc3c80d08d200015a0004b817a33861800000000000082200015672a35a86e00058456e9a47a00002642568b6a480000002c607c4680c430476c1c60000000000006a64765d80004400000000f42f40000da0a00000009de492a10760070226732af60000000003e845400013e0005ba0006ce0008b4000afc6586669ac5dc00000020a50c38e5c00000001dc322000000334000000774ac600069c26e0006fa6ee67c3d831e28895a5b82fc7dea00000afa0e81541fe4b40000003747bc85a9f027a47490c7c6726a5690e5247ea34c13409a6501c03ba0186da62842865247a5860e6b024947dc3961aca8000030e8a40682fe5b20008ec000000a2e0000000008420006ae71e00000000039aaae446664744000000a208c20ea3e63f2820442432414ac84e21420009d808c68a6d00b253e0000002862f075a5d48fc9da00032835e45a0941d088a000a4e4000001285f05740000000008640000004ce00000000055078450e00030a000000a320009820000000000000000000000000000000000000003da00000000000000000000015e8c4566914a503fa4ea9a8000a4a4d800011e00000018814e0000000000009d617000097237c56298e8f66b694838279c0009128800083aa8a818403e684250000ade0001be000000ad06a8a9078e25c52021c8ba8682c02a82e8a4400035400004e6707760008764a43a266a0641b67925721a811805210ea4c65a80626a9104161628d80000007000006fc0a20005140000000481cc7d40006306d2000000000832000000a92a588b0000a760000000001f40000000884a08160002542c800003c8c65a20007f2ab20000fe0009c80009ee1b02ec6bc04c232a980009ec0005be0000587187fe000000a5aa96ae4b4e23c00000003a0000000006468bc00000000079474a0009b20002e00006e200005e138000af84dc8040005ea0004ec000272940000340a0a00077898a35600007883e8100005985ec1ba3580000000009b840c89800012e0000007683327aa2cc84c8aaa345e83e292e3ec0006a2826b3e06c40428456c62a99c05618c08e6164064d43866dc00000090457e1480000000000000000009be000000450000210a6255c5bc4e652a000000a365800000003640000000820000000000006c800000094a4ac0005260000000009926b200032e0006087b23000007ba00000066c00086c5aa00000000000000023a5f241c00000072238a49065437a0007482fa0001500009a019e000000000000a6c00034a934a382a264c65e6680000003
  | 9 => 0x9ae0000001122f63f40008fe0008246b44700001b274638870e790000ac24fe306b169162de0008e291e000000000000b38578000b1000088800082a24200000000000000002c57c3788700008c0000000000692b24a8800000007200000095687c00000000000000000000006a5520000c278200068e95c3b000049e4fc89c83c0009020008e8afea169582a488c3d633a99a59258284aad80dc9182ba6e81d484883a1f277010a9e65640ca29c0ce4a68964ccb3a46648424a58a9900047ec402b320003625d2a829245420000000000008380003681bcb2c096000000a9e2c20000005909e000003697800000000000011a1523d229eab44aaa247e81f00a88e03a41a00ec96878628e00036c0b43c016a4f851a6883129e84d60000000f20001789dc54c5c463243a00000076600047279600037263c10455800080839250631a64a5a09c681c3b600069614095e0008e6000b0482c02201e2960000000006be0003be3de4203ac0000000003d0000000000000000a3e0000004e0b0000074c0000002945b484e0000005000006140000005104eea848822d00400005a400048caf270852218e19419615c6047e212456081254493868222c0c02302402aa0004ba0001980760000003c40000000001da610b0687473e5e4000110b307c046a63424827439e0003ea51c24e0002d444a0007f08307fc0748da60a1de2162f80000006225302e4a140004d000000000000000072e0006c00000000000000000000000000000001fa0003fc12c0000904580000668d600096e6aa00000094c000000756b083a60006a000088e818a6a00008023400012a0005f400016c6b00ba754aca7ac0001a6534734aa801473a89400071c528000a1c93e46e7028fa05a0003ee89ea4661aa642aea6e97e85e0004c88000000600005cab4ab1a000a0caa000000046c41e98459a7524380009969aa0000d40000981ee3367c40008540003ca61e00000051200000000000000063e6e42388340004e88629cc0004980002b802e41231600006e4f200000000095050a00093600097609e16e05ca9a4528f837679800000c20c000a7e5d62804c200000062421a9607ae6749d4030a680000000003ae1ea0006de8de000038000728b128e400288459697a330a7a000b0aa7800000000000000080e7b800000000076a0007ca37eabc38c5a64caa606feb42028b262469f800049a5e00000de48a18686a87800000000091c0000000000427e413a5b617643ca120002dc7124648a69d00be64e6600c854644c00000047e2062a00002d67d09809000000008ce0f6000000a721304a89ba0b03f843428a48010678069a02a418b341e252c8c85fe000044516b4c9b054a2980000006622b4000000000640a5c0006f20008364c400019c30c0000008a06f429a1007d
  | 10 => 0x4b000012200000027c750000000b0c00000039078a2524242786d845e17e1e8b205cc7b41ae77a8ee2b2b48a422141c200049c8465c261c0007ce00000034624458c45c000116a0e0000007167a47d6b1c48e5c6228af453c0000003b496272c9283d426626caa6000a3cb182ea0a600054e62e0009f68a27c200042ca309462d81c81441fc00000044e1362b69089ce19220800060c7040ae7f413278c000538000a0292600051e92c6ba000000a1800000000000000073c0000008500000000006426c63c66a47427641200003e0ab66d6aac3266f800052e87a5da0f8ad44364f60000003a00001829f40000003442ca14630299e0004968529b6ac000085c1ce80c7b044831416639c00001668c0002be000536504000000000aec4c600034e00026832a75e0006065940006000001ca00094e2ac8440005d000000004638042e33c0000002580004ae000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xd54d89100066f53d89100066d53d89100066c51d89100066c50d89100147e75989100047d7598910004be7498910004bd749891000cde7398910004dd7398910004ee72989100047f75589100147c7558910004bf7458910004bc7458910004df735891000cdc7358910004f771589100147c75189100066c5218910004ee76189100066f65189100066c6518910006af6418910006ac6418910006cf6318910006cc63189100066f75189100066c75189100066f54189100066d54189100066f53189100066d53189100066c51189100066c50189100047e76949100047c76949100063f64949100063c64949100065f639491014e5c63949100066f62949100066c62949100247e76945100063f64945100063c64945100065f63945101165c63945100066f62945100066c62945100347e76941100063f64941100063c64941100065f63941100be5c63941100066f62941100066c6294110004be76901100063f659011009e3c65901100069f63901100b69c6390110006af6290110006ac6290110004be76101100063f65101100963c65101100069f631011008e9c6310110006af6210110006ac621011018f385010110006b864c4110046d46384110006e462841100047d74d94100047d73d94100047e72d94100347e71d94100067671d94100247e70d94100067a70d94100147c75d90100147e75990100047d75990100047f75590100147c75590100147e75190100047d751901000cde7319010004dd7319010004ee7219010004ed72190100047e76550100047c76550100057870550100147c75d8c100047f7558c100147c7558c1002cf47158c100047e7654c100047c7654c1000e5e6354c100065d6354c10005747154c100147e75d88100047d75d881000cde73d8810004dd73d88100147e75988100047d75988100047f75588100147c75588100147c75188100047e76948100047c76948100057a709441002dd673c8410004f57608410006e562084100147e769401001c7c76940100057671940100a67865d00100063f659001009e3c6590010185ba70900100063f65100100963c65100100073a5010010177385010010004f976100100967865100101773b5410010007395410010006ba7610010006b976100101773a75100100073975100100073b6510010096ba6510010096b86510010177386510010096386510010006bb6310010006b963100101773b5310010007395310010006ba6210010006b862100100073a5210010177385210010007b27110010007b1711001017eba61100100073a511001017738511001016fb3311001016fb03110010007b32110010007b02110010007b040c401000cf97684010004f7764401002dd47344010005e47244010007725044010004fb7644010005b87444010007725144010
  | 1 => 0x3100963e65103100063d65103100073a501031017f3850103100967a6510310006b9641031017f3b5410310007395410310005b97610310006b9761031017f3a7510310007397510310096ba651031017f3a65103100963a6510310007396510310096b86510310006bb6310310006b9631031017f3b5310310007395310310006ba6210310006b862103100073a521031017f3852103100073a511031017f3851103100147f76596100047f74596100047f73596100047c72596100147e75d92100047d75d921000cde73d9210004dd73d9210004ee72d9210004ed72d92100147e75992100047d75992100147e75592100147e75192100047d75192100047f76552100047d76552100057870552100147e75d8e100047d75d8e100147e7558e100047f7654e100047d7654e10005747154e100147e75d8a100047d75d8a100147c7598a100047f7558a100147c7558a10004df7358a1000cdc7358a100147e7518a100047d7518a1000cde7318a10004dd7318a100047f7694a100047d7694a1003c7d7694610045d673c8610006e762086100147d769421000576719421009e3e65902100063d65902100963e65102100063d65102101973850102100147e76d95100047d74d95100047d73d95100047e72d95100147e71d95100147c71d95100147e70d95100147c70d95100147c75d91100063f54d91100063f65d91100063c65d91100063f75d91100063c75d91100063f53d91100063c52d91100063c51d91100063c50d91100147e75991100047d7599110004be749911000cde7399110004dd7399110004ee7299110004ed72991100047f75591100147c7559110004df735911000cdc7359110004ef7259110004ec7259110004fb70591100147e75191100047d75191100063f5419110004be76191100063f65191100063c65191100063e75191100063d75191100063f53191100063c52191100063c51191100b4be701911008cbc70191100063c50191100047e76551100047c76551100063f64551100063c64551101665c63551100057870551100147c75d8d100065f53d8d1000cde76d8d100065f65d8d100065c65d8d100069f64d8d100069c64d8d100065f75d8d100065c75d8d100065f54d8d100065d54d8d100065c52d8d100065c51d8d100065c50d8d100047f7558d100147c7558d10004bf7458d10004bc7458d10004ef7258d10004ec7258d10044f77158d10004de7618d100065f6518d100065c6518d100069f6418d100069c6418d100047e7654d100047c7654d100063f6454d100063c6454d100065f6354d1000e5c6354d100147e75d89100047d75d89100066c52d89100066f65d89100066c65d8910006af64d8910006ac64d8910006cf63d8910006cc63d89100066e75d89100066d75d89100066f54d89100066
  | 2 => 0x63f65101200963c65101200069f631012008e9c6310120006b76110120006b461101201bf385010120006b864c8120076cc6388120006e461881200047d74d94200047d73d94200647e72d94200066e72d94200047e71d94200547e70d94200067a70d94200147c75d90200147e75990200047d75990200047f75590200147c75590200147e75190200047d751902000cde7319020004dd7319020004f67119020004f571190200047e76550200047c76550200057870550200147c75d8c200047f7558c200147c7558c2005cec7258c200047e7654c200047c7654c2000e5e6354c200065d6354c200056c7254c200057a70948200147e75984200047d75984200047f75584200147c75584200047e769442005dce7388420006e561084200147e769402004c7c76940200056e72940200a67865d00200063f659002009e3c65900201b5ba70900200063f65100200963c65100200073a501002019f385010020004f9761002009678651002019f3b5410020007395410020006ba7610020006b9761002019f3a75100200073975100200073b6510020096ba6510020096b8651002019f386510020096386510020006bb6310020006b9631002019f3b5310020007395310020007aa7210020007a972100201aeba62100200073a521002019f3852100201a7ab32100201a7a83210020006ba61100200073a511002019f385110020007aa2110020007a82110020007a840c8020004ef764802005dcc7348020005e471480200076a5048020004fb7648020005b874480200076a52480200147f76597100047f74597100047f73597100047c72597100147e75d93100047d75d93100147e75993100047d75993100063f5499310004bd76993100063e65993100063d65993100063e75993100063d75993100063f53993100063c52993100063c51993100063c50993100147e75593100063f54593100063e65593100063d65593100063e75593100063d75593100063f53593100063c52593100063c5159310006bb70593100063c50593100147e75193100047d7519310004be74193100047f76553100047d76553100063e64553100063d64553100057870553100147e75d8f100047d75d8f10004be74d8f10004bd74d8f10004ee72d8f10004ed72d8f100147e7558f100047f7654f100047d7654f100063e6454f100063d6454f100147e75d8b100047d75d8b10004be74d8b10004bd74d8b1000cde73d8b10004dd73d8b100147c7598b100047f7558b100147c7558b100147e7518b100047d7518b10004be7418b10004bd7418b100047f7694b100047d7694b100063e6494b100063d6494b100147d76947100063e64947100063d64947100057a709471003c7d76943100063e64943100063d64943100a67a65d031009e3e65903100063d659
  | 3 => 0xe75592200147e75192200047d75192200047f76552200047d76552200057870552200147e75d8e200047d75d8e200147e7558e200047f7654e200047d7654e200056c7254e2006c7d7694a200147c75986200047f75586200147c7558620004df735862000cdc73586200047f76946200047d7694620075ce73886200147d76942200056e729422009e3e65902200063d65902200963e65102200063d65102201c73850102200147e76d95200047d74d95200047d73d95200147e72d95200147c72d95200047e71d95200147c75d91200063f54d91200063f65d91200063c65d91200063f75d91200063c75d91200063f53d91200063c52d91200063c51d91200063c50d91200147e75991200047d7599120004be749912000cde7399120004dd7399120004f67199120004f571991200047f75591200147c7559120004df735912000cdc7359120004f77159120004f47159120004fb70591200147e75191200047d75191200063f5419120004be76191200063f65191200063c65191200063e75191200063d75191200063f53191200063c52191200063c51191200063c50191200047e76551200047c76551200063f64551200063c64551201665c63551200057870551200147c75d8d200065f53d8d2000cde76d8d200065f65d8d200065c65d8d200069f64d8d200069c64d8d200065f75d8d200065c75d8d200065f54d8d200065d54d8d200065c52d8d200065c51d8d200065c50d8d200047f7558d200147c7558d20004bf7458d20004bc7458d20074ef7258d20004f77158d20004f47158d20004de7618d200065f6518d200065c6518d200069f6418d200069c6418d200047e7654d200047c7654d200063f6454d200063c6454d200065f6354d2000e5c6354d200547e76949200063f64949200063c64949200065f639492014e5c63949200147e75d85200047d75d85200067451d85200067765d85200067465d8520006b764d8520006b464d8520006d763d8520006d463d85200067675d85200067575d85200067754d85200067554d85200067753d85200067553d85200067652d85200067452d85200067450d85200147c7518520006745118520006776518520006746518520006b76418520006b46418520006d76318520006d463185200067775185200067475185200067754185200067554185200067753185200067553185200067652185200067452185200067450185200047e76945200047c76945200063f64945200063c64945200065f63945201165c63945200067761945200067461945200647e76941200063f64941200063c64941200065f63941200be5c6394120006776194120006746194120004be76901200063f659012009e3c65901200069f63901200b69c6390120006b76190120006b46190120004be7610120
  | 4 => 0x45300063c64945300066f62945300066c62945300067761945300067461945301d47e76941300063f64941300063c64941300066f62941300066c62941300067761941300067461941300bf58309413000cfa76d01300a67865d0130006e862d0130006f061d013008cbe76901300063f659013009e3c6590130006af6290130006ac6290130006b76190130006b4619013008dba70901300b4be76101300063f65101300963c6510130006af6210130006ac6210130006b76110130006b461101300073a50101301cf385010130096786510130006bb64101301cf3b5410130007395410130006e86210130006f061101300b5ba7610130006ba76101301cf3a75101300073975101300073b6510130096ba6510130096b865101301cf38651013009638651013008ebb631013008f3b531013008f395310130007ab6210130006b86210130007a86210130006a862101300073a52101301cf385210130007b36110130006b86110130007b06110130006b061101300073a51101301cf385110130006cc628c130006d4618c13000798408c1300147f76597200047f74597200047f73597200047c71597200147e75d93200047d75d93200147e75993200047d75993200063f5499320004bd76993200063e65993200063d65993200063e75993200063d75993200063f53993200063c52993200063c51993200063c50993200147e75593200063f54593200063e65593200063d65593200063e75593200063d75593200063f53593200063c52593200063c5159320006bb70593200063c50593200147e75193200047d7519320004be74193200047f76553200047d76553200063e64553200063d64553200057870553200147e75d8f200047d75d8f20004be74d8f20004bd74d8f20004f671d8f20004f571d8f200147e7558f200047f7654f200047d7654f200063e6454f200063d6454f200147d7694b200063e6494b200063d6494b200057a7094b200147c75987200047f75587200147c75587200047f76947200047d76947200063e64947200063d649472006c7d76943200063e64943200063d64943200a67a65d032009e3e65903200063d65903200963e65103200063d65103200073a50103201af3850103200967a6510320006b964103201af3b5410320007395410320005b97610320006b976103201af3a7510320007397510320096ba65103201af3a65103200963a6510320007396510320096b86510320006bb6310320006b963103201af3b53103200073953103200073a52103201af385210320006ba61103200073a51103201af3851103200147f76596200047f74596200047f73596200047c71596200147e75d92200047d75d922000cde73d9220004dd73d9220004f671d9220004f571d92200147e75992200047d75992200147
  | 5 => 0x4f77158a30004f47158a300047e7694a300147e75986300047d75986300047f75586300147c7558630004ef7258630004ec72586300047e76946300147e76942300055d73942300bf5b30942300a67865d02300063f659023009e3c65902300063f65102300963c65102300073a50102301df38501023000cf976102300967865102301df3b5410230007395410230006ba761023008eb976102301df3a75102300073975102300073b6510230096ba6510230096b865102301df38651023009638651023008f9a731023000799731023008f3b531023008f395310230006ba62102300073a52102301df3852102300079a321023008f983210230006ba61102300073a51102301df3851102300079a311023008f9831102300147e76d95300047d74d95300bc7f73d95300bc7d73d95300047e72d95300047e71d95300147c75d91300063f54d91300063f65d91300063c65d91300063f75d91300063c75d91300b63f53d91300b63d53d91300063c52d91300063c51d91300b6b970d91300063c50d91300147e75991300047d759913008cbe7499130004ee7299130004ed7299130004f67199130004f571991300047f75591300147c7559130004ef7259130004ec7259130004f77159130004f471591300147e75191300047d75191300063f54191300b4be76191300063f65191300063c65191300063e75191300063d751913008e3f531913008e3d53191300063c52191300063c51191300063c50191300047e76551300047c76551300063f64551300063c64551300057870551300147e75d89300047d75d89300066c52d89300066f65d89300066c65d8930006af64d8930006ac64d89300066e75d89300066d75d89300066f54d89300066d54d89300766f53d89300766d53d89300066c51d89300066c50d89300147c75189300066c52189300066f65189300066c6518930006af6418930006ac64189300066f75189300066c75189300066f54189300066d541893005e6f531893005e6d53189300066c51189300066c501893005ecc30189300047e76949300047c76949300063f64949300063c64949300066f62949300066c62949300147e75d85300047d75d85300067451d85300067765d85300067465d8530006b764d8530006b464d8530006e762d8530006e462d85300067675d85300067575d85300067754d85300067554d85300467753d85300467553d85300067652d85300067452d85300067450d85300147c7518530006745118530006776518530006746518530006b76418530006b46418530006e76218530006e4621853000677751853000674751853000677541853000675541853002e77531853002e75531853000676521853000674521853000674501853002ed430185300047e76945300047c76945300063f649
  | 6 => 0xe75d8c400053d75d8c40005ba70d8c400073850d8c400953e7558c40007385058c400053f7654c400053d7654c4008d3f7354c400971f7354c400053c7254c400053c7154c400073b7054c400053c7054c40007387054c40005387054c400b63e6054c400953e75d88400053d75d8840005ba70d88400073850d88400953c75988400073850988400053f75588400953c75588400059f735884008d9c7358840005b77158840005b471588400073850588400953e75188400053d751884008d9e73188400059d7318840005b67118840005b57118840005ba70188400073850188400053f76948400053d76948400053d73948400953e72948400972e72948400053e71948400053e70948400073a70948400053a709484000739709484009e3e60948400053f758c8400953c758c84022738508c8400053f754c8400953c754c840005bb704c840005b8704c84021f38504c8400953e75d84400053d75d8440005ba70d84400073850d84400953c75984400073850984400053f75584400953c75584400059f735844008d9c7358440005af7258440005ac72584400073850584400953e75184400053d751844008d9e73184400059d7318440005ae7218440005ad7218440005ba70184400073850184400053f76944400053d76944400053d73944400053e72944400953e71944400973671944400053e70944400073a70944400053a709444000739709444009e3e60944400053f758c4400953c758c44021738508c4400053f754c4400953c754c440005bb704c440005b8704c44020f38504c4400953e75c84400053d75c844008d9e73c84400059d73c8440005ba70c8440005b970c84402073850c84400953e75884400053d758844008d9e73884400059d7388440005ba7088440005b970884401ff3850884400053f75484400953c7548440005bb7048440005b870484401f73850484400053f75084400953c7508440007a521084401ef3850084400953c759804009e3e65980400063d65980401e73850980400073b7598040095ba7598040095b875980401e73875980400953875980401e73a6598040007396598040005b973980401e73b5398040007395398040005ba72980400073a52980401e7385298040005ba71980400073a51980401e73851980400053f76940400953d76940400053d73940400053e72940400053e71940400953e70940400973a70940400953a709404009e3e60940400073a60940401d57a70d96300047d74d96300065d73d96300047e72d96300047e71d96301d47e70d96300067a70d96300147c75d92300147e75992300047d75992300047f75592300147c75592300147e75192300047d75192300047e76552300047c76552300057870552300147e7598a300047d7598a300047f7558a300147c7558a30
  | 7 => 0xc64009d3c758c6400053f754c64009d3c754c64009d3e75c86400053d75c86400b59e73c86400059d73c864009d3e75886400053d75886400b59e73886400059d73886400053f754864009d3c75486400053f750864009d3c7508640007a5210864009d3e769424009d3c76942400053d73942400053e72942400053e719424009d3e709424009f3a70942400963e60942400147e76d95400ac7d74d95400047d73d95400047e72d95400047e71d95400147c76551400057870551400147c75d8d400047e7654d400047c7654d400147e75d89400047d75d89400147c75189400047e76949400047c76949400147e75d85400047d75d85400147c75185400047e76945400047c76945400a47e76941400a67865d01400063f659014009e3c65901400147f76594400953d74594400147f74594400963f74594400147d74594400963c74594400047f73594400047c72594400047c71594400967b70594400947c70594400967870594400947870594400963c40594400a47f76550400953f74550400957870550400053f76550400a63f76550400053f73550400053c72550400053c71550400073b705504009738705504009e3e60550400147e7558c400047f7654c400047d7654c400053f7454c40005787054c4000cbd76d0c400953e75d0c400053d75d0c4028f3850d0c400953e7550c400053d7550c40287385050c400147c75988400047f75588400147c7558840004df735884000cdc7358840004f77158840004f471588400047f76948400047d76948400053d74948400057a70948400953e75d08400053d75d0840005b970d084027f3850d08400053f75908400953c75908402773850908400053f75508400953c75508400059f735084008d9c7350840005b77150840005b47150840005bb705084026f3850508400953e75108400053d75108402673850108400147c75984400047f75584400147c7558440004df735844000cdc7358440004ef7258440004ec72584400047f76944400047d76944400053d74944400057a70944400953e75d04400053d75d0440005b970d044025f3850d04400053f75904400953c75904402573850904400053f75504400953c75504400059f735044008d9c7350440005af7250440005ac7250440005bb705044024f3850504400953e75104400053d751044024738501044009c7f76940400147d76940400053d74940400957a70940400953e75d00400053d75d004023f3850d00400957875900401e73b5490040007395490040004bf76500400053f75500400953c755004022f385050040004fb7650040095787550040235bb745004022f3b54500400953f76594400963f76594400053f73594400053c72594400053c71594400973b70594400953c70594400973870594400953870594400953
  | 8 => 0x55d73c86500047e76886500047d76886500bd5e73886500055d73886500047f76486500047c76486500047f76086500076521086500147f76597400047f73597400047c72597400047c71597400a67b70597400a67870597400947f76553400057870553400147e7558f400047f7654f400047d7654f40005787054f400147c7598b400047f7558b400147c7558b400047f7694b400047d7694b400057a7094b400147c75987400047f75587400147c75587400047f76947400047d76947400057a70947400ac7d76943400a57a70943400063d74d96400047d73d96400047e72d96400047e71d96400067a70d964009d3f74552400057870552400163f76552400163c76552400053f73552400053c72552400053c71552400073b70552400073870552400047f7558e400147c7558e400047c7654e400053f7454e4000e5e6354e400065d6354e4009d3e75d0e400053d75d0e4000cbf7650e4009d3e7550e400053d7550e400147e7598a400047d7598a400047f7558a400147c7558a400047e7694a400053d7494a4009d3e75d0a400053d75d0a400053f7590a4009d3c7590a400053f7550a4009d3c7550a400059f7350a400b59c7350a40005b77150a40005b47150a4009d3e7510a400053d7510a400147e75986400047d75986400047f75586400147c75586400047e76946400053d749464009d3e75d06400053d75d06400053f759064009d3c75906400053f755064009d3c75506400059f73506400b59c7350640005af7250640005ac725064009d3e75106400053d75106400147e76942400053d749424009d3e75d02400053d75d02400073a50d02400a67865d02400073954d024009e3e76d96400053d73d96400053e72d96400053e71d96400053e70d96400073a70d96400053a70d964009d3c75d8e40005ba70d8e400053f7558e4009d3c7558e400053e7654e400053c7654e400b53f7354e4009f1f7354e400b71e6354e400071d6354e400053c7254e400053c7154e400053c7054e4008e3e6054e4009d3e75d8a400053d75d8a400b59e73d8a400059d73d8a40005b671d8a40005b571d8a40005ba70d8a4009d3e7598a400053d7598a400053f7558a4009d3c7558a4009d3c7518a40005ba7018a400053e7694a400053c7694a400053d7394a4009d3e7294a4009f2e7294a400053e7194a400053e7094a400963e6094a400053f758ca4009d3c758ca400053f754ca4009d3c754ca4009d3e75d86400053d75d86400b59e73d86400059d73d8640005ae72d8640005ad72d8640005ba70d864009d3e75986400053d75986400053f755864009d3c755864009d3c7518640005ba70186400053e76946400053c76946400053d73946400053e729464009d3e719464009f3671946400053e70946400963e60946400053f758
  | 9 => 0xf75591210147c7559121004df735912100cdc7359121004ef7259121004f77159121004fb7059121004f870591210147e75191210047d75191210047e76551210047c76551210057870551210147c75d8d210047f7558d210147c7558d21004bf7458d21004bc7458d21004fb7058d21004f87058d210047e7654d210047c7654d210056c7254d21005747154d210cc7e76949210d47e76945210147e75d81210047d75d8121004be74d8121004bd74d81210147c75181210047d74d94210047d73d94210d47e72d94210066e72d94210cc7e71d94210067671d94210047e70d94210147c75d90210147e75990210047d75990210047f75590210147c7559021004df735902100cdc7359021004fb7059021004f870590210147e75190210047d75190210047e76550210047c76550210063e64550210063d64550210056c72550210057471550210057870550210147c75d8c210047f7558c210147c7558c210047e7654c210047c7654c21005767194821004ed7610821005e5711082100ced768c821005e5718c8210147e76944210c47c76944210056e7294421004f57610421005e5721042100cf5768c421005e5728c421007c5328c421007c6324c421005cd73c8421005d573884212a5e57288421004ef764842100766514842129f645148421004f7764842100766524842129f645248421005e77648421006e7764842100767754842129f64754842100767654842129f646548421005e67448421005e4744842129f675448421007655448421005e77348421005e5734842129f675348421007655348421005e4704842129f6450484210147e75980210047d75980210047f75580210147c7558021004bf7458021004bc7458021004df735802100cdc73580210957a70d92500a67a60992500047f73592500047c72592500047c71592500063d641925009d7a70192500967a60192502957a70d8e500be5c6358e500047f7458e500047c7258e500047c7158e500147c7058e500be5c3058e500047e76d0e500047d76d0e500047d7650e5004d7a70d8a500047d7498a500047d7398a500047e7198a500557a7018a500047e76d0a500047d76d0a500047f7690a500047f7650a500047c7650a500055f7350a500bd5c7350a50005777150a50005747150a500057b7050a50005787050a500047e7610a500047d7610a500047f768ca500047f764ca500047c764ca5001d7a70d86500047d74986500047d73986500047e72986500257a70186500047e76d06500047d76d06500047f76906500047f76506500047c76506500055f73506500bd5c73506500056f72506500056c72506500057b70506500057870506500047e76106500047d76106500047f768c6500047f764c6500047c764c6500047e76c86500047d76c86500bd5e73c8650
  | 10 => 0x8a310047f7558a310147c7558a310066c5258a310047e7694a310055d7394a310147e76946310055d73946310147e75982310047d75982310047f75582310147c7558231004bf7458231004bc74582310147e76d95310047d74d95311147f73d95311147d73d95310047e72d95310047e70d95310147c75d91310147e75991310047d75991310047f75591310147c7559131004df7359131004ef7259131004ec7259131004fb7059131004f870591310147e75191310047d75191310047e76551310047c76551310057870551310147e75d89310047d75d89310147c75189310047e76949310047c76949312ac7e76945310147e75d81310047d75d8131004be74d8131004bd74d81310147c75181310147f76597210047f74597210047f73597210047c70597210147e75d93210047d75d932100cde73d9321004dd73d9321004fa70d9321004f970d93210147e75993210047d75993210147e75593210147e75193210047d751932100cde7319321004dd73193210047f76553210047d76553211665e63553210057471553210057870553210147e75d8f210047d75d8f21004dd7698f210065e6598f210065d6598f210147e7558f210065f5358f2100cdf7658f210065e6558f210065d6558f210065e7558f210065d7558f210065f5458f210065d5458f210065c5258f210065c5158f210065c5058f210047f7654f210047d7654f2100e5e6354f210065d6354f210056c7254f210147d7694b2114e5e6394b210065d6394b21005767194b210dc7d76947211165e63947210065d639472100ed6638c72100cf7764c7210147c75983210047f75583210147c7558321004bf7458321004bc74583210147f76596210047f74596210047f73596210047c70596210147e75d92210047d75d922100cde73d9221004dd73d9221004fa70d9221004f970d92210147e75992210047d75992210147e75592210147e75192210047d751922100cde7319221004dd73192210047f76552210047d76552211665e63552210056c72552210057870552210147e75d8e210047d75d8e21004dd7698e210065e6598e210065d6598e210147e7558e210065f5358e2100cdf7658e210065e6558e210065d6558e210065e7558e210065d7558e210065f5458e210065d5458e210065c5258e210065c5158e210065c5058e210047f7654e210047d7654e2100e5e6354e210065d6354e21005747154e210dc7d7694a2114e5e6394a210065d6394a2100ece638ca2100cef764ca210147d76946211165e63946210065d63946210056e7294621005cd73c8621006d563c86210147c75982210047f75582210147c7558221004bf7458221004bc74582210147e76d95210047d74d95210047d73d95210047e70d95210147c75d91210147e75991210047d75991210047
  | 11 => 0x73554d06410147e75982410047d75982410067850982410047f75582410147c75582410067850582410147e76d954110c7d74d95410047d73d95410047e72d95410047e70d95410147c76551411665c63551410057471551410057870551410147c75d8d410065f53d8d4100cde76d8d410065f65d8d410065c65d8d410065f75d8d410065c75d8d410065f54d8d410065d54d8d410065c52d8d410065c51d8d410065c50d8d410065f6518d410065c6518d410047e7654d410047c7654d410065f6354d4100e5c6354d410147e75d89410047d75d89410066c52d89410066f65d89410066c65d8941006cf63d8941006cc63d89410066e75d89410066d75d89410066f54d89410066d54d89410066f53d89410066d53d89410066c51d89410066c50d89410147c75189410066c52189410066f65189410066c6518941006cf6318941006cc63189410066f75189410066c75189410066f54189410066d54189410066f53189410066d53189410066c51189410066c50189410047e76949410047c76949410065f639494114e5c63949410066f62949410066c62949411047e76945410065f63945411165c63945410066f62945410066c6294541006e462d05410147e75d81410047d75d81410067850d81410067b65d81410067865d8141006db63d8141006d863d8141006eb62d8141006e862d81410067a75d81410067975d81410067b54d81410067954d81410067b53d81410067953d81410067a52d81410067852d81410067a51d81410067851d81410147c75181410067850181410067b6518141006786518141006db6318141006d86318141006eb6218141006e862181410067b7518141006787518141006bb74181410067b54181410067954181410067b53181410067953181410067a52181410067852181410067a5118141006785118141006ba41181410147f76594410047f73594410047c72594410f47c71594410047c70594411047f76550410057870550410147e7558c410047f7654c410047d7654c41005747154c410147c75988410047f75588410147c75588410047f76948410047d76948410fc7f76944410147d76944410053d7494441004bf7650441007365150441005b87050441004f77650441007355450441005e472504410147c75980410047f75580410147c75580410056e72d96312ad7671d96310047d74d96310065d73d96310047e72d96310066e72d96310046e72d96310066d72d96312ac7e71d96310067671d96310047e70d96310147c75d92310147e75992310047d75992310047f75592310147c7559231004fb7059231004f870592310147e75192310047d7519231004ee7219231004ed72192310047e76552310047c76552310055f73552310057870552310147e7598a310047d7598a310066c529
  | 12 => 0xc75980420047f75580420147c75580422bd6e72d96320057671d96320047d74d96320065d73d96322bc7e72d96320066e72d96320047e71d96320067671d96320047671d96320067571d96320047e70d96320147c75d92320147e75992320047d75992320047f75592320147c7559232004fb7059232004f870592320147e75192320047d7519232004f67119232004f571192320047e76552320047c76552320055f73552320057870552320147e7694a320055d7394a320147e75986320047d75986320067451986320047f75586320147c75586320067451586320147e75982320047d75982320047f75582320147c7558232004bf7458232004bc74582320147e76d95320047d74d953214c7f73d953214c7d73d95320047e71d95320047e70d95320147c75d91320147e75991320047d75991320047f75591320147c7559132004df7359132004f77159132004f47159132004fb7059132004f870591320147e75191320047d75191320047e76551320047c76551320057870551322bc7e76949320147e75d85320047d75d85320147c75185320147e75d81320047d75d8132004be74d8132004bd74d81320147c75181320f57671d92510057a70d92510057970d92510047f73592510047c72592510047c70592510063d64192510fd7671192510056e72d8e510056d72d8e512b57671d8e510047f7458e510047c7258e511165c3258e510147c7158e511165c3158e510047c7058e510047e76d0e510047d76d0e510047d7650e511155e73d8a510055d73d8a510c57671d8a510047d7498a510047d7398a510066f3298a510066c3298a510047e7098a510cd767118a510047e76d0a510047d76d0a510047f7690a510047f7650a510047c7650a510055f7350a511155c7350a51005777150a51005747150a510057b7050a51005787050a510047e7610a510047d7610a510047f768ca510065d638ca510047f764ca510047c764ca510053e74d82510053d74d825101d7671d82510047d74982510047d73982510047e72982510053f74582510053c74582510357671182510147f76597410047f73597410047c72597410047c70597410f47f76553410057870553410147e7558f410047f7654f410047d7654f41005747154f410147c7598b410047f7558b410147c7558b41004df7358b4100cdc7358b410047f7694b410047d7694b4110c7d76947410147c75983410047f75583410147c75583410057a70d96410063d74d96410047d73d96410047e72d96410067671d96410047e70d96410067a70d96410047a70d96410067970d96410057471552410057870552410047f7558e410147c7558e410047c7654e410147e7598a410047d7598a410047f7558a410147c7558a410047e7694a410147e76946410053d74946410073651d0641
  | 13 => 0x82520656e72182520147f76597420047f73597420047c71597420047c705974212c7f76553420057870553420147e7558f420047f7654f420047d7654f420056c7254f421447d7694b420147c75987420047f75587420147c7558742004df735874200cdc73587420147c75983420047f75583420147c75583420057a70d96420063d74d96420047d73d96420066e72d96420047e71d96420047e70d96420067a70d96420047a70d96420067970d96420056c72552420057870552420047f7558e420147c7558e420047c7654e420147e7694a420053d7494a420072e52d0a420072d54d0a420147e75986420047d75986420047f75586420147c75586420147e75982420047d75982420067850982420047f75582420147c75582420067850582420147e76d95421447d74d95420047d73d95420047e71d95420047e70d95420147c76551421665c63551420056c72551420057870551420147c75d8d420065f53d8d4200cde76d8d420065f65d8d420065c65d8d420065f75d8d420065c75d8d420065f54d8d420065d54d8d420065c52d8d420065c51d8d420065c50d8d420065f6518d420065c6518d420047e7654d420047c7654d420065f6354d4200e5c6354d4213c7e76949420065f639494214e5c63949420147e75d85420047d75d85420067451d85420067765d85420067465d8542006d763d8542006d463d85420067675d85420067575d85420067754d85420067554d85420067753d85420067553d85420067652d85420067452d85420067450d85420147c7518542006745118542006776518542006746518542006d76318542006d46318542006777518542006747518542006775418542006755418542006775318542006755318542006765218542006745218542006e742185420067450185420147e75d81420047d75d81420067850d81420067b65d81420067865d8142006db63d8142006d863d8142006f361d8142006f061d81420067a75d81420067975d81420067b54d81420067954d81420067b53d81420067953d81420067a52d81420067852d81420067851d81420147c75181420067850181420067b6518142006786518142006db6318142006d86318142006f36118142006f061181420067b7518142006787518142006bb74181420067b54181420067954181420067b53181420067953181420067a5218142006785218142006ba42181420067851181420147f76594420047f735944212c7c72594420047c71594420047c705944213c7f76550420057870550420147e7558c420047f7654c420047d7654c420056c7254c421347f76948420147d76948420053d7494842004bf76508420072e5250842005b87050842004ef76508420072d5450842005e471508420147c75984420047f75584420147c75584420147
  | 14 => 0x67a61181540067961181540067861181540967b74181540963b74181540967974181540067b73181540067a73181540067973181540067873181540067a43181540067843181540067b72181540067a72181540067972181540067872181540067b32181540067832181540067b71181540067a71181540067971181540067871181540067b31181540067831181540147d73d91532ce3f43d91530047e72d91530047e71d91530047e70d91530063f64991531555d739915315d5f73591530056f72591530056c72591530057771591530057471591530057b705915300578705915311d5d73989530057671989530057571989531255f73589530047d74189530147d73189532be6d32189530047e71189530047e70189530e55d73985530056e72985530056d72985530ed5f73585530047d74185530147d73185530047e72185532ae7531185530047e70185530053e74d81530053d74d815307d5d73981530053f74581530053c74581530855f73581530056f72581530056c72581530057771581530057471581530047d74181530147d73181530047e72181530047e71181531d67930181530147f76597430047c72597430047c71597430047c70597432cc7f76553431671e43553430057870553430147c7598b430047f7558b430147c7558b43004f77158b43004f47158b430147c75987430047f75587430147c7558743004ef7258743004ec72587430147c75983430047f75583430147c75583432cd3f74595430056c72595430057471595430057870595432cc7f74595430063f74595431647f73595430065f73595430066f72595430047c72595430066c72595430046c72595430067771595430047c71595430067471595430047471595430067b70595430047c70595430067870595430047870595430147f76551431647d76551430055f73551431671c43551430057870551430147e75d89430047d75d89430066c52d89430147e75189430047d75189430066c52189430147e75d85430047d75d85430067451d85430147e75185430047d75185430067451185430147e75d81430047d75d81430067850d81430147e75181430047d751814300678501814312d6e72d92520057a70d92520057970d92520047f73592520047c71592520047c70592520063d64192521356e72192522c56e72d8e520057671d8e520057571d8e520047f7458e520147c7258e5214e5c3258e520047c7158e5214e5c3158e520047c7058e520047e76d0e520047d76d0e520047d7650e5214d5e73d86520055d73d86520c56e72d86520047d74986520047d73986520067731986520067431986520047e70986520d56e72186520053e74d82520053d74d825204d6e72d82520047d74982520047d73982520047e71982520053f74582520053c745
  | 15 => 0x200300e00e00900303603d04100300700c00001604c00000602f01b00500100800000200100303e02100000000b01000000300e00100401600000000400101400e00602f00002001600000000101000001100e00402900000000001001301300200f00200100006300500e01200a01100000200100001700700001100000600000002b00100c01000200200e00700800100000300500002500000400000500200100b00701800401501900200a00c00400000100002100000000c00000500701400104300100400003500701a00200600300001b00000002c00700000101400b01200900003c00500000002200000001a00e00000d00700000701502601003a00100100500000600200800a01400200600100200200000f00300100c00000100000200000300000100200900900000200500e01200400000000300100000100201100a01f00a00000a00200501400004601400b00100700c00500000200100000201000200200f01a00200001d00300200000c00100400000600600902000000000000000900800000300500000000301c00400800300400000501000600800300100a00000d00c00200501900100100000300002300000002c02900600101100200500000000e00200000300206100300002e00402900300b00200003100600000700200100800200d00000101902000000100200e00105800301100105100f00c00800501000200200001000a00200500d00000e04801800200100b0030147d74d8d541665e43d8d540047e72d8d541665c32d8d540047e71d8d541665c31d8d540047e70d8d542d53f7458d540056f7258d540056c7258d54005777158d54005747158d540057b7058d54005787058d541453d74989540057a70989540057970989541353f74589540055f73589541655c73589540057771589540057471589540057b70589540057870589540047d73189540066f32189540066c32189540047e71189540047e701895410d3d74985540057a70985540057970985540fd3f74585540055f73585541655c73585540056f72585540056c72585540057b70585540057870585540047d73185540047e72185540067731185540067431185540047e70185540a73974d81540a67b64d81540a73b64d81540067b63d81540067963d81540067a62d81540067862d81540067a61d81540067861d81540ad3d749815409e3f64981540957a709815409d3f74581540963f64181540067960181540963f74181540047d73181540047e72181540047e71181540067b30181540067830181540a57a76181540067a76181540973b74181540967b64181540973b64181540963b64181540067b63181540067a63181540067963181540067863181540067b62181540067a62181540067962181540067862181540067b6118154
  | 16 => 0x4092418406c87128a229d9224d0c52d2299474e7c083059a1dc7c02253880124c0c21b32f034138664e3fc1310aae6672d11eccf2042e2bf2185032265218177417c8754e492f47061d93f092842943f30f7022c04a38035805049bc769149153d4565751f726a4c449d524e0be44de01d3cc8ca50b0a3104404050064d6479a6ed2fa54d422a36d27216c2e0a2b0b468663bda3d8f18a3e0e78e9c20a24a4da20911123c82bb8dc8a245fd4dc94b01442f411c1eb81ae7962cb26a853844600e1df8dd01f7283a35001802806a14a41ee86917919d012888030703303206d5492862098a0002be075837a1d1340826127864745f20ad1de00000c03201000000100401404901f00600800000000100400000000000200700000d00000500b00500000400400a00002100000b00702a00000000100000401f00201500400500100000500000400300100100600d00400400400600200000401100500200200400000000802202000100000700300f01702000000100d03400000401c00300300000100e00500000000100200003401800100401800500000001400400300000c00200001c00000d00200800100000c00300600100f00d00200500600000200504c00000200500900000000000100702500800c00500000000e01300000301000000c00c00100f00700200100200201f00000200200000000600a00000a02000300500900900500101600000100200000b00000000a00000000000100200601d00500c00100200801400100300500500100802100301d01b00100800100400200d00900000d00b01d00000100f01403300100100000100000502200000500a00101102c00c00600700300204400500900300200500200300300100300100a00300002300000100100700b03900200000300700101100d00106a00600300000700400002200a00000a00c00202300400600b00000000101100100400000400200302900400000001000a00700001900700000200600c00a00100600300000700100100200100102100000f00301a00200f00d00100702000000100301c00000000800901100000900100600d00000500700303500000500200000000000000100400402a00900500402100702000200900300300100000001902000301900002100500601600102601002b00000000400100201500e00200401200d00100800300000100000800200000200400400200000001900000000200000101800000301501100400405700800000000100c04d01300000400300500600000100b00500000002200700000000a00300901e00800100000000000605e07000001001000100401300000b00800602500000f00e00000300d00900900401200300b02800400200003000300f00500100600101300d00102200000100300400c0020060000000
  | 17 => 0x8e1ffc9460001cba4347665912e4a7ac5ee475063a8b89f0145145a4e8cfc99226d977d40a8ce36e1b9d13239800018fd38453d00008589a44a850c1168a026cc1d525ac3506bc40f9f38db06d900003a131290e07c12b48387dc1288600238a1a4ca13d85de3371b8a0d934659816583d4142a120000000f7a0000d1998d1d20000b78a140004062c5000000044d0501c8400000020580012c80003e18ea4fc851e2df8c310de83e24ba7dc44e62d47f067c1003cb06c0dac7e00ea2c111b01e44280941b28da62b84a30c0445a19114a206815e6c81df80007b663709f8464dfc5e82fb0a54b540003b3153824c37511b87e52b262820810600000ef3cd0d900004ff30c00004b47d13770d683861e94bb9af400043440700007cc21139a1ec53b400045a837400080c0221dfcbdc169243a5a44ee75f14c923c8ec5cc43c246cb0817647c07941806431568f30000000155a80400085e1698b28f5423140f19b0a6a3533f99e6c2406783d815b400007f443139d3b684f4b691980001d221e83108c60592631cbc0a64a60dd0000000a4c4a10000000a4b000087c00020800000008f8696048161ce8c9372f60084f1c3230d214a000070a4cc0f8c96e9ca2be94cd4645f32e5a4d80007a30528000c8c00049da9383c643848314ad3fe15200f0be8d4c40123811b844430a0000000bd26f300018d000004e0000fbc85a39624b1b5cd265da376800110a46a06f18e00000820001a080007c40000b7800000016688005a800000000000000002ae800127e8b00001ba830c000000142800051b4c412c80009131f29ce40003483d49cfc0005732e191f53ac8830000f709848cc2dd17080009d105600000002720000ff4fe843e3e90aa09d03b90000f140000000f6852c0ae9114d2a2d0dde82c18d82c83321ff12f98f804600000027b007475411ca818966a4d2261288df83912c08c4509c5880001bd033823d3818e2896800d2b3a774b6621a0c58a0c2fc0004e61af800050e4ea02c12d048236d09a4bf63360ea81cc5aa9180002578c540000a000010ae0004ba00003e872b45488251fe0000000cd52b45cf109891cf6435244613a40c49d70ad8f78e1a58d2de270502646d4b988cc0fc04c1710e7902820e255a0e0f0e68b46e07312966aa30b1fe4fe40004c199482ac5761cf88ecd2a0f13d5a4840007fa000120c0002f600006bc9220931dea2d8ff6000092211857c00018e80002fe7b54a19e7c97044805523887104dd00007713321eb490167518877600019811267be00009b944c65b51c98b806609105384b40000000000000000a3f1e380000000002102628f3c1152fa8a3c5da00f03e96c40009e500019ac6f6a1601b25c4c982591158dfc0003190691b0cb181ad4b00b1d1802da32987e11ca27416e8b8c90c83b05ba5f0b
  | 18 => 0x6dd0000e84cca00000000000006482f80000000a2533f80009c45a8000000091a3f73dc00900003a60002158a4852f31aa6cd2be0474b107d80bc0004509f288248650be8ae908456b2ff9d80b606a921d8fe123e9d34579a480005834fb1d44a70416507063c18471205221f0f0a5c422b9508ab659303ca89d1d04b92c489ece8633400000008b20000fe8118b286f73bca3b0a5c89a19f9d28aa46852df2910e92722057209d4704453ec0fc9220175461a095114a3300017d043200032106b8a30000352865000031e256000129039913821f80009bd38f1338c6c02709e93dc8e600037600002e09d239b0e74d145ea00010c88d236e0b2a5bc38c27a1ffa034d0653e0ec02ac00000034c1d6c0ce5320ef006826885216fa530f4889e2480d742a08680000000000000000187539629e04e8e040162c80002058054545000000000000003c14e890a4fc3e280011f698001ba0a05f840d0000000000000000000000049a1eb000129e00000022ac0006fd2b6000044600004795e4cc80000000000f84a1d121a5e4c062794ec852064286300001dcaca7141f4126c00098e00009100009ee000000014c4f251aa240c0858e3e98f4c17816d2b206583cc0004300000d722e404600008d60003a100008c808117fa9094386cd16281ed4682e04fa9afc54c97530d1d84fa01e02b0000125492c192136000049329183b032422a14c00008b000026b9ddc60a1b41fa8ac40007c81108c18000000414845c4c6a431258d340000fd000000130870f4178fc4de4a284cfa13118c4ea0d622a85d29b53f8a040000056000037c0000540c3a2b513e33c28219d936e69942a8ff8de2042066854c0007860000e3c00095539d0564fde6b2370099c27c21400013b400004a22882ec7161fc25d01a01360002af22e93fc08713c1b88f082c344687b000000050f8c38dc86ce3f60ee8b6843123f1df087894134a072420403d2071c2d41a7ac04f1b7824220615608d0036212056a26c30411214b94c503aa152c5a65916e6a23f5a28c67077331199b853a6572b1204850e2e63570c88ae894a2328ca89289703f51740c4a60a43389906201c418d0cf80761db15480001927ad3a40b302166a402805a00009ac28800002c242216e20e480a5924500cf40003b50000c7c0003a8463a10ce509870f3a3342ae9812650eac63099b4d3000009e23200014dd3f84d33dca4211ac5b507d900ceb40990da800037c6505228a58000000482a6fc43811e4d39e042e200032f86d80009a000000f8f222c42d685344aa96711300003b43551bd1d8c00075900015a4e1082d0001248bc600000003d00000004b504e8aa09ba05f98013b89ab00989fc0000003eea8bc9b493203e0fb40003bc3600ac05dc15a21504c918217a0191fa017a4ee4c30880c163c92
  | 19 => 0x42d80004ae96c45223d50e06c13d317c84b86e543c9530e8a3420020e912506c6280280c69620c00010cd1e200013ea31400082e49ea12800047f20c8a44f7e1f0000000022048b2e40ca000000034e14446de9c400011251e800015a800000069e255058c0baa2c32b21b821a94715e86346bc2c6340183c498379107825cbb676a00817bc00054934820440008bb03095a911e00038e09206d000000f80007580001a2a4f91f839409d981c5469b25151068d6c5253c18810edc55a45f97dd21873138da7a4c8890404b1b98000a1020a80009d640c2cc83ac00028417624011025ce33507f886a70c33d800065a2d700017912f49542ac035912a97f327a000efa5a50000000f7461e000221043a07622500005129954a7036c7ec2a10b9990400076c32e16001e014e1c289049fa3744819c18f922eb1bf1510c100fe0860660fd216028100000dc6d40000000000000000000000000006580006c64400001f5c6ae00034d27e07f40003af0bf906602d0002024e2e00001c0000f4e0004f9a5151647230001ba48080001780000d2e9c04d826b842a3bb32497290fe00026000602f80004a6908400061723880000002d806e01e8e881034c61d045646ba0e406144ec7fd266976131e56810b88410045dc0dc142445e951000117c8e861b1e6a84400051a418282c2a27352129d2c000923032000075a00014099cc00000042019d512e0000b327c0cba00013e07752b8747227a0d0e302f530fa36029e4f400006282867042f106ec00050c5079b2c05216e4fe82e800099c18480000000000088000b567023c9800000032f117184400045d000156400000002fa6451e077833d106d0303b6000135462a6771a516d9292224388939033a3b749a1eecf789661c30fa82aa5b9418894c4d83490c4971d12c3eb3b907bc2c85132640f9c0de5c04f1905c4d044324e879102a95b39983a541011d12f1be8406000146018c96a3b129315544503390e09f989f4000092a018c0219e1550ba85c23730d50f64e3462002287a94329172b8273447c9ea26e229c10a8c81800f844e2362098165d2ba1840641734b366c7423a6a12a08c20000154e4098d4d6839c7843442859cb46804d43ab992939c0002b780011d68cf23c81451b202646501986409df46f09a901424f46e9748c040e13028a9084e24e2d7189084c2cf00010a54741f50000f480006ad41f9239244000254a2953a00004bda51138a75d42d06806daa0246904d800258f44ea8c0000707095a4e0a6817b0001f8c79c4e007e028c01c000003a6c40001b72f396a45e67580002248fc4000441000000035c0001aec46a3b043d20dc0007945060000e0000000019e40009f400005608bc86d39900f139e00000011054908e646f904d15c00048a00011f450519d039000012f0002560
  | 20 => 0x92900002e00004474de25580005d10f982a4f1a8d73478000fc013c000232ca2c369189a43c520a1e19980000809fa1058210000137317903d4804cc001974d03847214991080149e63c918c83845e004f83446865de12c0e543804601fd8f5c2102f83201cf40000000000064ae235629f9c050be7f52a8851c00a8c93068e480002b4384a0111724a40218f401da21e15018c4e2c71d3d400006b088e2d7a2e021e34e00020809a289834683cd3e23b836913d44840002570a28a4e2883bd2810ca88223579260ede87d000247137c00031c830402830b01c9ff923a78b16828b411462b2a01e880000000001b6c0ea0003fb101ce488911c607149f25461aa1aac00077431319f000076b0eb96dd02e0001b024cd1d49a40001aa0a541420000c9cdc6000102800060425600016691a65c6364a92933416a00009002ee9f22ec88a42ba00008a0000000a1449789410a600000000000000000000698000377425a61400000042a00000004020000d841aa0000000438dd60002e298ec18c0001b60d991a04390000ebc4da54b4d780010d67df16c80000009b800010252805e636b00000001491ad9f308562db0918a1858097e0d380009e02ce1e1a93c2706a70fd0ba0f96a223611cec32e63d212187093c59c3598ff08ce6213931dd4e988f913319c4f3a3870718054b4831218698f028c8711309a24c968644130924fb49a201782e43960001c20a08c2600007f94f074a1093a822990887190001f6400069b035a01c7401a550b882800000000004680005ed26821d80000001bc28f13bc13550da8f541412243991bc1385b2405a904b7a4df28a12c146c0b526193eca326ff1b39ed8c7402c39e1a2099e2451579da13de1270ef98cc65c5561a605e0b3e436326863883a33b4bb13b0dec2b9085096cf123d40e991ec4ba16b0301ca83783ae25e045868e0cf32d161493e1e1234107d00a6555101504c2a17448b10dcf800303db91500905a125f938c89c15f45983d8f2e1a10002368bca91249580008960003e30000fdc1c751b8c1121499743d86040d40da1d18bf4c122bc00011114768d507d140c4fc65900006687d23b202d00491c093540d9e54d9e06500010000006e11e204600001330000a34d8a78f21f9ca46821fb3a91cc090037641508fd1505613ea2684e5c8504719079446972270800000032517380008746f900001488f46662b728a40009934c113c41c431c3cc262c0007671b2857800051522800000da5203a0066d2c61003781484eac3cf13992ec9fc29f1688e4cdbe7c13b280003e478049384190826840001a4400000049887510024d914d218860e919000000000000041a800000000000027ec0000000d88f68000915094943cf4211f4b29f3d1da00050996540001b03870fb04602c205a291c94e000
  | 21 => 0x104676d157241d07896145e83287aa3d11358b4885e57b2fe0aeccda1310001ce0c4e00000004a8d620000000cc8a6c47838f94880009d82af8000000902000185011a3f43560f88bf01793a7a39124c2c10f114c00b89e834f88e877c0f91819b44d187703c11fdc54a90b11b08b032a09a4249a746a27252500a9c0000d316b00002220003d0164006839b30609892f01bf062a3b86a00005121e28ca2499000118800066f47e8e4000088728f8c980d237d000000050000000001c800073740424250b23144f1254800048a00000011c283d00000000000002309d70d0e0002ae0000d703c00820ad802c0060000dc109a00039380000007cd2648c5c7680e54cf07a094a86c0049ed000000000017e8f4a5080380a88b76254396000027235f00000d4cc22462041f58d880003310000c604e500000012dc7c731489488b62010e6821901e2fb0000f60d4638233ea2710e40ce47393bc0b65634f69f6c0000000001754c2400013a80b90427fc35b902944239c3f3800140e6fb38a8000ce04813ce21d090866823b83b80e25a70e81a3800028e3f2a67495e6a022e00003527553ef1f5400015c4ab8acc6d403f1d112d8bac0002cf012c056669000000815092d4440bc400000000026d8000a093a6a22c0000001e0a3c800000028683646b20002d312f86562bf2dc1e2000086a0d980013200002a397acba84f305b154c00032c47b8000af06d00aa16182c40e04e301d01624e6258904517891a4980a6cc32a461be0e3425c5f90000001128172000214478c71300000000003311a795e82360580c60d182ce6f50e508f0000000229064c00001726080800006a11ee97f80005e13229fb47f23161011be092a3df083a720c206b509607388aa2070730f280d80001648000ec848c4f00134a949e7000150c2887530040e68fe0089339271c12a5722160c3ce9c90100009340008d10000000f5e5664971c140000c348f254c29857f458883422653904712203728322a40f90000000000131c0005d732c0088062a000f8941812400000006ad3c200042e18b0aa842322b0cc08284cb3b106890baa4915ba7900008480c18b9471c5173b88860b5883a2f88000d689f9020898
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xe2852188404c001c56ca31080980038a194621013000715c28c42026000e2885188404c001c54ea31080980038a5d462101302e715a98c4202605ce2953188404c001c50a231080980028ea1a521013000714314a42026000e3065d84404c001d40c5b08809804a8e214611013000718288c22026000e3365184404c001c60ca3088098003a8d88611013000750310c22026000e3385184404c001c610a30880980038c9d4611013000718ba8c2202605be3353184404c0b7c62a630880980038c948611013000718290c22026000a3a86944404c001c50c528880980038c186511013000744310811826000e9061102304c00143b073aac9900028ea0275593200061d320e0aa64000c39641c154c8001874c9384a5900de8e61a50103200951d42ac82064000a3b8655040c80254750abb0819004a8ee1975103200951dc32ca2064012a3a85d8c40c800156503b18819004a8ea1563103200051dc32a62064012a398694840c80254710b30881900028e61a51103200043a40aeca9c4000c3b641c15448001870c8382a8900031618c70551200052c402a9b1a4000a708055361480014e100aa0c29000386143631012000718286c22024000e305018440480010f5013b2a8100021760c76550200043b40ceca98400285c8758d530800189ac6392a6100021760e76944201c51d406ca2004012a38859d840080254710abb080100028e219751002000595416ca2004012a3885d8c40080254710ab1880100d2aa20963100200051c432a62004000e196354c400800165104a9880100d2e220d7210020005d040ae42004012a3a8694840080254750b30880100028ea1a51100201a5c541c422004000a1d839d564c4001475013aac9880030e99070553100061cb20e0aa62000c3a649c251c40634730d280818804a8ea1564103100051dc32a82062012a3a855d840c40254770cba8818804a8ee1965103100951d42ec62062000aaa82d8c40c40254750ab1881880028ee1953103100951c42cc42062012a3a8518840c40014730d290818804a8e61a511031000436412eca9c2012878801d95444001876c8382a8880030e19070551100062c318e0aa22000a588055363440014d100aa6c4880029a20154189100951d406ca2022000e1850d8c4044001c50a1b1080880038a14062101100043d404ecaa0200085d831d954040010dd053b2a60800a1721d6354c100062ab18e2a98200085d839da520406547501b28800804a8e21676100100951c42aec2002000a38865d4400400166503b28800804a8e21763100100951c42ac6200202dab08158c40040014710ca9880080038658d53100100059840aa62002012a3a8598840040254710a31080080028ea1a521001016dc841ae22002000ba0825c440040254750d28880080b6e4a0f2110010
  | 1 => 0xa1b9a84200034c143715084000698280e2a10801293a85dc142100252710ab86822000346143735044000694286e4a088000d28501c941100252750bb82822004a4ee1c50d8c400049cc38a1b188000b198314363100012730e282c6200024b2097654c400049a40aeca988000939861c1531002527306382a6200024ea087054c400049d408e0a98801293b8714362100012730e286c4200024ea1c50988400049d406eab10800093a871416210001a36e6282c42017f461cc505884000699b88a0b108000d307114162100252770e280c4200024e61c50188402fe8d398a03108000d19731406210001a64e2280c4200034c5c450188400049cc34e12908000939839c2521000127503384a4200024da07758c8400049d406eb190800093a80dd532100252750bb82642004a4e214704c8400949dc38a1b0880009398714361100012750e284c2200024ea0375584400049d438a0b088000d1b7314161100bfa30e6282c2200034adc8505844000694390a0b08801293b8714061100012730e280c22017f469cc50184400068cb98a03088000d2a721406110001a52e4280c2200024e61a70944400049cc1ce1288800093a829c2511000125d05bac62200024ea03758c4400049d406ea988801293a85dc131100252710a38262200024e20175c84400068c282e79088012938859c321100252710ab8642200024e20175884400068c282e71088012938859c221100252710ab8442200024ea0375484400949d42ee09088012938851c1211000127501ba84220002e820121084402f79028242108803ca388059660100252710ab9cc0200024e21d53980400068cb9aa7300801293a859ca60100012750f294c02004a4ea1671980400049d43ca3300801293a80dda50100252770f304a02004f0e5da609404000437414ecaa46000876819d9548c0010f5013b2a9181768ea0365102300951c42cec2046000a38865d4408c0254750db288118002c660f65102300951d42cc42046000a3a86948408c0254750b30881180028ea1a51102300050ec1ea9b226000a1d831d7644c001475003aec8980030ed9070551300061c320e0aa26000a6880553624c00149b06290c4980029360c751893000526c1ea83126000a6a80d50624c0014d100aa0c4980029360c511893000538402a9b0a6000a5583144614c0014ab063a8c2980029560f541853000539406a830a6000a7080550614c0014ab06290c2980038a143621013000714280c42026000e3050d84404c001c60a030880981768ea1a501013000714314a02026000e3061940404c0254710bb2080980028e219541013000715aa0c42026000e2954188404c001c66a830880980038c55061101300951c42cec2026012a38865d4404c0254750db2880980038a19762101300951c428c42026000
  | 2 => 0x971181540052d418e2302a800a59831c460550014d505988c0aa0029a60b31181540043a40ae8312a600878805d06254c010d904ba0c2a98021e201741855300627b98e4b2a8600c6472dc56550c018aee638acaa180319dc8715954300632390e2b2a8600c6872dc16550c018e0e3b82caa18030edd0705954300635b90e0b2a8600c68721c16550c018e6e2382caa18031c1c470595430061dc20e0b2a860087a80dd163948010f100ba4c32900299a0b31986520043a40ae7304a400874815d953d0801872e9386cb210030ee1270d964200626318e4aa2840087a861c154508018b0c6382a8a10029620154d8d4200538402a9b0a8400a3584144615080146b083a8c2a100299a0b541854200532412a830a8400a708055061508250f70eaa6c0a10028e610511814200617bb4a4a108400c2f7655142108c589ae7396cb19003155ce71d963200633392e3b2c640086e829d9548c8010ed033b2a9190021ea0276552320043d404ecaa2640087a80dd163944010f100ba4c52880299a073298a5100436412e7304a20086c825d953d0401872e9386cb208030ee1270d96410062a318e2aa2820087a861c154504018b0c6382a8a08029620154d8d4100534402a9b128200a2d84148625040145b083a8c4a080299a0754189410053240aa83128200a688055062504250f70eaa6c0a08028e61052181410061bbb4a2a088200c3776551411040189ae7396cb18987155ce71d963100632b94e3b2c620086e829d9548c4010ed033b2a9188021ea0276552310043d404ecaa26200878805d954c84018acc638aa9908031698c705532100526412eab1e4200a588055163c840189ac6392a7908031598e7194b210043c402ecaa44200c4e631c954884018b4c6382a910802952057558e210052c402a8b1c4200c55631c5538840189cc7394a3108021ea0276551210043d404ecaa0420283c87591540840147100b22a8108030e99070550210061cb20e0aa0420086e829d953084010ed033b2a6108020f6107654c21004e2c1eec908420096687d9521084012c90eaa24210802d82015448421004d2422e690842009e0805cd21084014c90ca9a421084a1ea037458e500943c402e9314a012878805d2619400107b09bb043281830e5d270d96400961dbb0e0aa4800285c8758d539000125904baa87200024d2057550e400042ec1ced294800085d839da51900792770eaa6812004b0e21a70d964000497414eca9c8000936819d95390001275013b2a7200024ea007654e4009c8e43ac6a9c800091d839da5290001275013b4a5200024ea007694a400049b40eeb194800091d839da5190001275013b4a3200024ea00769464000497416eb18c800086c825d953100010e902bb2a6200024b2097550c400049a40aeaa188012938855c34210001a3
  | 3 => 0x1c6489612005c691d274d960e4dd549401f856720e06b55d098004f441619a73154a700371e4c7729c163000000006940035d3f6658e0007a001150000039151000b76a94d681640003b2c1905040000038001b42880023800000300011e1b96812d6b7102e654001e0003240055da1101082a49165c53440f4108ba001331f0051c8031a55c6a03d000215c0b13b4003300068c002b8000c4704f0000016e1403a1ec631c4004053b59c00398006c4db610173793e4b854708af6e8aa449745b0520d8c65e4bc4748723c5f0704a5c49c1b59d4a0005f5d4000a8494000a8041bd816b176444343b892464a72f90913ca1579532f555741cc6d46b33800060005c9567240b0000003d064c9274e84762ce30000000000001661cc8d000434394e6f0890018f01d6322074021470785a0413719cab07d1f6099b0015840c00518b342cef3e4d350c0033c2364c0d43c65068683c185144c40b4666f42f0009f540a46989e6884d5fca36ccf26790a1302c411294e43f4c1880a0455b5be001b024d83308445a8990004e0012b354b8125c72597a4585526876001485dd141fd4220dce634955894c4bd26261af0f99800000001540cd000d54b0060080604006020000000e008000082e2103e01004028140000a06844028161000400022038200480401000050120480c000000000c0580000050000000100400802010200080213004000100382001018230040a038000240b800000040e0060080c048040080000810018260000000000008000b000028060500e018001001e0a822090000008602828010580180603800048100e80404000000060a014008020082c078020000405000010040001e0100c0600c000180000201800000040c8160380299a073218954005334166230aa800a688258f60550014e102b1ec0aa11a8ee11601815400436412e6302a800874815cc605500147309980c0aa0021e61e63181543451cc24c6302a867a3b8458c60550014d704b18c0aa0029a209631815400539c0ac6302a800a708158c60550cd47309310c0aa0021ee1d621815432d1dc22c4302a800a5b8358860550014b106b10c0aa0029ce0562181540053840ac4302a864a398498460550010f70eb08c0aa18e8ee1161181540052dc1ac2302a800a588358460550014d704b08c0aa0029a20961181540051d424e6302a868a39849cc60550cf47708b98c0aa0029ae09731815400534412e6302a800a73815cc60550014e102b98c0aa0021e61e43181543351cc24e4302a865a3b845c860550014b706b90c0aa0029620d721815400539c0ae4302a800a70815c860550014b506390c0aa0029660c72181540053940e64302a800a7181cc860550c947309388c0aa18e8ee1171181540052dc1ae2302a800a58835c460550014d704b88c0aa0029a20
  | 4 => 0xb4204824140059458074006c91300000000cb1640000000094000040046c0038400471235800000000350004d4005d4c116c8a054d915c00050191800c3d8e55cc13328dc668004909d5bd2c469ae4a862001023f0000012d3ddb6000462d809190cd2fc125100a61d7841cff5ec8453c61348d11f47701991231175652121475090e82b4ac3f518369b9648c367dc5629c33a53139d49058006502b120f5625cf038fb481340c8a53f85e0a48b088f15f8a6009ab2d43c6ed362c82717486000df1b000734d000000000202e411358006a5b73201b57c973e09b388bb3b0d85a55b3e80024000000f33acea280000000000000600944357c569bf1a9cb515386e10c671d13
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x2498328185800028b1b0480b9a387c00c0878e92103828f0e04c151a40c9100000000000b84501219925b00012309061051185420048c241841d461508012289061052189410048a241841d46250401038906107654c210940e24184dd821940011289261c5058c400044c2458714163100011309160e70948400044a249839c2511000111993a1e52980400044664e87946601002581a7060c75d91300058264f54188404c00161193d5061101300058264c52188404c0016099321462101300058264e75188404c0016099314462101300058464c51184404c0016119321461101300058464e75184404c001611931486110130096061c1839d564c8001219932197510020094862616354c4008001a096320953100200048664e8694440080258187060e75593100048664c865d440040252189858d53100100068458c8154c400400121993a1a5210010
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x4
  | 2 => 0x6
  | 3 => 0x4e
  | 4 => 0x124e
  | 5 => 0x4c
  | 6 => 0x138e
  | 7 => 0x94e
  | 8 => 0x124c
  | 9 => 0x8e
  | 10 => 0x128e
  | 11 => 0x8c
  | 12 => 0x150e
  | 13 => 0x98e
  | 14 => 0x128c
  | 15 => 0x9ce
  | 16 => 0x12ce
  | 17 => 0x10c
  | 18 => 0x10e
  | 19 => 0x130e
  | 20 => 0x180e
  | 21 => 0xa0e
  | 22 => 0x130c
  | 23 => 0x134c
  | 24 => 0x20e
  | 25 => 0x140e
  | 26 => 0x154e
  | 27 => 0xb0e
  | 28 => 0xb4e
  | 29 => 0x144e
  | 30 => 0x28e
  | 31 => 0x148e
  | 32 => 0x184e
  | 33 => 0xb8e
  | 34 => 0x14cc
  | 35 => 0xcce
  | 36 => 0x15ce
  | 37 => 0x40e
  | 38 => 0x160e
  | 39 => 0x188e
  | 40 => 0xd0e
  | 41 => 0x164c
  | 42 => 0xe8e
  | 43 => 0x18ce
  | 44 => 0x104c
  | 45 => 0x10054
  | 46 => 0x10056
  | 47 => 0x11396
  | 48 => 0x4116
  | 49 => 0x10956
  | 50 => 0x11256
  | 51 => 0x10096
  | 52 => 0x10094
  | 53 => 0x11516
  | 54 => 0x8116
  | 55 => 0x10996
  | 56 => 0x11296
  | 57 => 0x109d6
  | 58 => 0x14c
  | 59 => 0x112d6
  | 60 => 0x130116
  | 61 => 0x20116
  | 62 => 0xb0116
  | 63 => 0x140116
  | 64 => 0x154116
  | 65 => 0xb4116
  | 66 => 0x144116
  | 67 => 0xcc116
  | 68 => 0x15c116
  | 69 => 0xa0116
  | 70 => 0x11316
  | 71 => 0x180116
  | 72 => 0x28116
  | 73 => 0xb8116
  | 74 => 0x148116
  | 75 => 0x184116
  | 76 => 0x40116
  | 77 => 0xd0116
  | 78 => 0x160116
  | 79 => 0x188116
  | 80 => 0xe8116
  | 81 => 0x18c116
  | 82 => 0xce
  | 83 => 0xb0216
  | 84 => 0x20b16
  | 85 => 0x2cc
  | 86 => 0x24e
  | 87 => 0x44c
  | 88 => 0x3ce
  | 89 => 0x1a8c
  | 90 => 0x178e
  | 91 => 0x4114
  | 92 => 0x8114
  | 93 => 0x10154
  | 94 => 0xb02011e
  | 95 => 0x14114
  | 96 => 0x10a16
  | 97 => 0x24b56
  | 98 => 0x3ccd6
  | 99 => 0x11496
  | 100 => 0x10b96
  | 101 => 0x11616
  | 102 => 0x10d16
  | 103 => 0x11796
  | 104 => 0x10e96
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 72
  | 6 => 1448
  | 5 => 2640
  | 4 => 469
  | 3 => 33
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
  | 6 => packedAt gbK6 (59360+((h/482+packedAt gbK6 (53576+(h % 482)*12) 12) % 2102)*12) 12
  | 5 => packedAt gbK5 (137280+((h/880+packedAt gbK5 (126720+(h % 880)*12) 12) % 3169)*13) 13
  | 4 => packedAt gbK4 (29231+((h/156+packedAt gbK4 (27671+(h % 156)*10) 10) % 563)*10) 10
  | 3 => packedAt gbK3 (2376+((h/11+packedAt gbK3 (2310+(h % 11)*6) 6) % 40)*7) 7
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x7fff007ffffffffffffffc0007fff8f1ffff8
  | 1 => 0xfffffff807f801fc00ffffffff988fffe631ff
  | 2 => 0xfffffffff80001ffff003fffffe0f1fff83e3f
  | 3 => 0xf803fffffffffe0000003fffffff01f0ffc03f
  | 4 => 0x3ffffffffffffffffc00003fffe00ffffc0
  | 5 => 0xfffc0000000000000000000003ffffff000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x32c70025a5b1a2d8d6372c0d02b37870ad6f8
  | 1 => 0x5d55b65806a8495424bb955b55988abb66315b
  | 2 => 0xae9adaaea800919aee0929ad9ae0d15db83a2d
  | 3 => 0x33036d373735dc0048123e36e37d01e0df4036
  | 4 => 0x4038fc5c5c6e1e370dc000703d6ec00f5ad80
  | 5 => 0xc7e00e060607010380e0303803fffffe000000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 63 gbPos gbNeg, 0xeaa8c080eaa8c000eaa8c080eaa8c000eaa8c080eaa8c000eaa8c080eaa8c000eaa8c080eaa8c000eaa8c080eaa8c000eaa8c080eaa8c000eaa8c080eaa8c000, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_15251
namespace PEqualNP.Outside.L_meta_15251
open PEqualNP.Outside.L_meta_15251.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_1_0 : Interval s0Atlas 1 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_1 : Interval s0Atlas 1 0 1 := bs0_1_0
theorem alls0 : ∀ k ≤ 1, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_1 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_2_0 : Interval s1Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_2 : Interval s1Atlas 2 0 1 := bs1_2_0
theorem alls1 : ∀ k ≤ 2, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_2 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_2_0 : Interval s2Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 1 := bs2_2_0
theorem alls2 : ∀ k ≤ 2, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_2 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 9 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 14 := bs3_4_0
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
theorem bs5_3_0 : Interval s5Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_32 : Interval s5Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 64 := (concat bs5_3_0 bs5_3_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_32 : Interval s5Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_64 : Interval s5Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_96 : Interval s5Atlas 4 96 23 := block_range (n:=23) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 119 := (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 bs5_4_96))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 13 := block_range (n:=13) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 45 := (concat bs5_5_0 bs5_5_32)
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
theorem bgb_3_0 : Interval gbAtlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_32 : Interval gbAtlas 3 32 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 33 := (concat bgb_3_0 bgb_3_32)
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
theorem bgb_4_448 : Interval gbAtlas 4 448 21 := block_range (n:=21) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 469 := (concat (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat (concat bgb_4_96 bgb_4_128) (concat bgb_4_160 bgb_4_192))) (concat (concat (concat bgb_4_224 bgb_4_256) (concat bgb_4_288 bgb_4_320)) (concat (concat bgb_4_352 bgb_4_384) (concat bgb_4_416 bgb_4_448))))
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
theorem bgb_5_2624 : Interval gbAtlas 5 2624 16 := block_range (n:=16) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2640 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 bgb_5_192) (concat bgb_5_224 (concat bgb_5_256 bgb_5_288)))) (concat (concat (concat bgb_5_320 bgb_5_352) (concat bgb_5_384 (concat bgb_5_416 bgb_5_448))) (concat (concat bgb_5_480 bgb_5_512) (concat bgb_5_544 (concat bgb_5_576 bgb_5_608))))) (concat (concat (concat (concat bgb_5_640 bgb_5_672) (concat bgb_5_704 (concat bgb_5_736 bgb_5_768))) (concat (concat bgb_5_800 bgb_5_832) (concat bgb_5_864 (concat bgb_5_896 bgb_5_928)))) (concat (concat (concat bgb_5_960 bgb_5_992) (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088))) (concat (concat bgb_5_1120 (concat bgb_5_1152 bgb_5_1184)) (concat bgb_5_1216 (concat bgb_5_1248 bgb_5_1280)))))) (concat (concat (concat (concat (concat bgb_5_1312 bgb_5_1344) (concat bgb_5_1376 (concat bgb_5_1408 bgb_5_1440))) (concat (concat bgb_5_1472 bgb_5_1504) (concat bgb_5_1536 (concat bgb_5_1568 bgb_5_1600)))) (concat (concat (concat bgb_5_1632 bgb_5_1664) (concat bgb_5_1696 (concat bgb_5_1728 bgb_5_1760))) (concat (concat bgb_5_1792 (concat bgb_5_1824 bgb_5_1856)) (concat bgb_5_1888 (concat bgb_5_1920 bgb_5_1952))))) (concat (concat (concat (concat bgb_5_1984 bgb_5_2016) (concat bgb_5_2048 (concat bgb_5_2080 bgb_5_2112))) (concat (concat bgb_5_2144 bgb_5_2176) (concat bgb_5_2208 (concat bgb_5_2240 bgb_5_2272)))) (concat (concat (concat bgb_5_2304 bgb_5_2336) (concat bgb_5_2368 (concat bgb_5_2400 bgb_5_2432))) (concat (concat bgb_5_2464 (concat bgb_5_2496 bgb_5_2528)) (concat bgb_5_2560 (concat bgb_5_2592 bgb_5_2624)))))))
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
theorem bgb_6_1440 : Interval gbAtlas 6 1440 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1448 := (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 (concat bgb_6_192 bgb_6_224)) (concat bgb_6_256 (concat bgb_6_288 bgb_6_320)))) (concat (concat (concat bgb_6_352 (concat bgb_6_384 bgb_6_416)) (concat bgb_6_448 (concat bgb_6_480 bgb_6_512))) (concat (concat bgb_6_544 (concat bgb_6_576 bgb_6_608)) (concat bgb_6_640 (concat bgb_6_672 bgb_6_704))))) (concat (concat (concat (concat bgb_6_736 bgb_6_768) (concat bgb_6_800 (concat bgb_6_832 bgb_6_864))) (concat (concat bgb_6_896 (concat bgb_6_928 bgb_6_960)) (concat bgb_6_992 (concat bgb_6_1024 bgb_6_1056)))) (concat (concat (concat bgb_6_1088 (concat bgb_6_1120 bgb_6_1152)) (concat bgb_6_1184 (concat bgb_6_1216 bgb_6_1248))) (concat (concat bgb_6_1280 (concat bgb_6_1312 bgb_6_1344)) (concat bgb_6_1376 (concat bgb_6_1408 bgb_6_1440))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_32 : Interval gbAtlas 7 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_64 : Interval gbAtlas 7 64 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 72 := (concat bgb_7_0 (concat bgb_7_32 bgb_7_64))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 2 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 3 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 20, 21),(inputs.getD 2 zero, 17, 21),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 5, 21)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 3 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 18, 19),(inputs.getD 1 zero, 17, 19),(inputs.getD 3 zero, 17, 25),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 18, 19),(inputs.getD 1 zero, 17, 19),(inputs.getD 2 zero, 17, 21),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 7, 39)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 4 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 38, 39),(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 5 zero, 7, 39)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 18, 19),(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 9 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 18, 19),(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 7, 39)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeaa8c080eaa8c000eaa8c080eaa8c000eaa8c080eaa8c000eaa8c080eaa8c000eaa8c080eaa8c000eaa8c080eaa8c000eaa8c080eaa8c000eaa8c080eaa8c000
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 9 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 49 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) (SBf 1) :=
    slice_correct (ms:=fixRows 34 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have s2 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 2 zero)) (SBf 2) :=
    slice_correct (ms:=fixRows 36 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (3936927872 * 2 ^ 32 + 3936927744) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_15251.Model.Repr at out
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

def mono : List Gate := [⟨.and,[0,4]⟩,⟨.and,[2,3]⟩,⟨.and,[0,2]⟩,⟨.or,[3,8]⟩,⟨.and,[6,9]⟩,⟨.or,[1,10]⟩,⟨.and,[5,8]⟩,⟨.or,[6,12]⟩,⟨.or,[7,13]⟩,⟨.and,[11,14]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,15⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 9) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3936927872 * 2 ^ 32 + 3936927744) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3936927872 * 2 ^ 32 + 3936927744) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_15251

open PEqualNP.Outside.L_meta_15251 in
theorem PEqualNP.Outside.L_meta_15251 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3936927872 * 2 ^ 32 + 3936927744) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3936927872 * 2 ^ 32 + 3936927744) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
