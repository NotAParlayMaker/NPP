import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_17053.Model
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


end PEqualNP.Outside.L_meta_17053.Model

namespace PEqualNP.Outside.L_meta_17053
open PEqualNP.Outside.L_meta_17053.Model
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

def SBf (j : Nat) : Nat := [5, 8, 7, 7, 6, 6].getD j 0

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

end PEqualNP.Outside.L_meta_17053

namespace PEqualNP.Outside.L_meta_17053
open PEqualNP.Outside.L_meta_17053.Model
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
  | 1 => 0x1ffc1fffff83f83fe0ff83fc3ffff03ec733f3
  | 2 => 0xe0ffe07c1ffc1fc3ff07fc1fc3c0ffc179cd9c
  | 3 => 0xffffff801ffffffc0007fffffc00ffff81fe1f
  | 4 => 0xffffffe0001ffffff8001fffff0001fe0fe0
  | 5 => 0xff00000000001fffffffffe000000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x4244451104250808a849a124065290944310b1
  | 2 => 0xca48c321292129416942a50c4286a584594594
  | 3 => 0x491080a5242129410844a52a8084a2980aa0a
  | 4 => 0x94a2124a034a54e65290421b312c0309ac0f40
  | 5 => 0x18c39c739c739f3b9ce7738222308c31f7f000
  | _ => 0
def s0Atlas : Atlas := ⟨4,rawDecor 62 s0Pos s0Neg, 0xfcfcfc00fcccfc00fcfcfc00fcccfc00fcfcfc00fcccfc00fcfcfc00fcccfc00fcfcfc00fcccfc00fcfcfc00fcccfc00fcfcfc00fcccfc00fcfcfc00fcccfc00, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_17053
namespace PEqualNP.Outside.L_meta_17053
open PEqualNP.Outside.L_meta_17053.Model
def s1K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K6 : Nat → Nat
  | 0 => 0x23004d08d0a54d1f143c5841c304064a401803c00009007401200003802200a00000000048000190004000000002700000002e980182c01002007111b0e00080881e040030200001ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s1K5 : Nat → Nat
  | 0 => 0x4817e53902faa7206f90e40de21c817e52903dca5205b94a40bea9481ed52902daa5206fd0a40dea14817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a81df53502bea6a05f14d40ee29a815c535037e86a06f50d40bfa92817c525037c84a06f10940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40bea9881be431037886205f94840bea9081bf421037a84205f94440bea8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330bf296617d52cc2fca3985f54730ef98e61dd31cc2fea9185f95230beaa4617c548c2faa71877d0e30ee21c617e528c2faa51877cca30ee994617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130bfa92617c524c2fea2985f14530ef98a61dd314c3f66098778c130bfaa0617e540c37ca8184f95030beaa061bd540c27aa8185f15030bf29861df430c3b886185f94830f7290616e520c2faa4187b54830b6a9061df320c3ba64185f94430fb2886176510c2faa2187d54430baa8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c83bca7905794f20bea9e41dd53c82baa7905f14f20f7a1641ec42c83dc65907b4cb20bf28e417d51c83de43907b48720bfaa4417e548837ca9104f95220beaa441bd548827aa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3107b88620f610c417e50883de41107ec8220bfaa2417e54482faa8905f15120bfa9a417e53482faa6905f14d20f7a1241ec42483dc64907b4c920bfa8a417c51483de42907b48520fd90241ee20482fea8105f95020beaa0417c54082fea6105f94c20bea98417c53082fca4105f94420bea8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb18e21f531c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3085f94210fd10421f920843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fb18a21f531443f440887e48110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c52042fca2085f94010fb88021fa10043ea20087e44010
  | 1 => 0xd5190afca1215f54242bfa9a857c5350b7e86a16f50d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42ef298855e5310afaa6217754c42aea9885be4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332ef21e65dd43ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7195f94a32f721465ed428cbbe65197bcca32bf28c657d518cafca1195f54232bfaa265bf544ca7ea8995f95132beaa2657c544cb78a8994f15132ef21a65dd434cbdc84997b50932f799265de324cafea2995f14532bfa82657c504cafea8195f95032df2a0653e540cafaa8196f550329eaa0657c540cafca6195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077c87a0ef10f41bf296837d52d077e85a0ef50b41bf286837d50d06faa920df94e41ef29c835e53906faa720f754e41aea9c83bf439077a8720df94a41bea9483be42907788520df94641dfa0c83f741906fca120df54241bfa9a837c535077c86a0ef10d41bfa9283ef52506dea4a0df14941f6292836c525077e84a0ef50941fba0a83be41506fea0a0df14141bf2a0837e53106faa620efd0c41dea18837e52106faa420ef90841de210837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc77ca998cf95331beaa663bd54cc67aa998df15331efa1e63dc43cc6fca598fb94b31b7296637d52cc7daa598db54b31ef99663dd32cc6fca198df54331bfaa4637e548c77ca918cf95231beaa463bd548c67aa918df15231bea9c637e528c6faa518df94631ef98c63f7318c6fca118df54231bfaa2637e544c6faa898df15131efa1a63dc434c6fea498df14931ef99263dd324c7ee6298f78c531bfa82637c504c6fea818df95031beaa0637c540c6fca618df94831bea90637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510fbd0a21f621443ee32887da6510df94621f790c43f721886fca110df54221bfaa243bf544867ea890df95121beaa2437c5448778a890cf15121bfa9a437e53486faa690df14d21fb90a43ee21486fea090df14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53087bca610d794c21bea9843dd53086baa610df14c21bf29043ef42087d88410fb8c821f6990437e51087de4210fd88421f690843f521086fca010fe94021bd280437d50087f2a010de54021bf29e817d53d037e87a06f50f40bf296817d52d037c85a06f10b40bf28e817d51d037e83a06f50740beaa
  | 2 => 0x60005a08280000000035985474608ae0312c227116a8c2dca24e418b152a20088be0004f40812b31054d1e06e27899c0485a47e000469961ac4e518a25362000000c44581c8f5861344694000004cc444d39ef4ee5003226202c1489f8e433248543000010280cfa53000a28478001726b00687444e000000690000008d0002904a8ba8003241e8fe80000000036800000001480000001a0170000005883b1ed00072c00000000000a300006a00071000036000d40000000010c9ae4c00000027548e000970c10e09314180022800127a7018c00000000274471389b34405b4000b12b681c0000000000102800000000001b643627841a294029fc078ea21c420002940005dc000d32007092b17c1fa730b28001f40000f8000000011121603c5f88b8141e000000013000348b500023e704000c200001cc09f23b0000bd9470827ecdf0000008a92518747a00000218000a0000103000000000001aa630328dd21a000001292f0524c680000070c002630000e40002c0cc3d00c0c50a6000c18004da0011c2920344c0000002860012c1283f05f47f800356a4d0a8000007b11780046c2400000c126360ea800000a2c8813e1c26fc0003b18e008460000000000e00007c0000009f0009b81080047c2a00000008c7c14b00000002c071411248280004e1f608cc4a2351e9ecbc88000000000000000130fd000000330092373460a80020314c1652b8000000000019000047478a123c61f8001931543d42e26f000000458c90000000000a0100a028020041000003010110040505c0600000008020080a000000000100400008000180200c010240101006004020100500c0200401038050100103c010000d00001000000180100c0200c030000c0080c02c0307c09004040040306c0600c0700c09034000000402007000000000100400020090040100c00008010040000400004000000000c0601802018020000101403000000080e004040000100c0c054060000003c070040102000008010080402401000000040100c150000200c030000000000008000000001806018060080102400034010000d00c0000801014010000e0080000404000000000300001024000180100400000000000100005034000140a0000600c0100800008010000500804bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421fb94843b7290877d5210fdaa421db54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7216f90e42de21c857e5290b7e85217bd0a42bf28c857
  | 3 => 0xb78001109d82019b3f821c0021f000000001801582393580032a974000250863ad411f922a85c7021d1ae05c00000000000002140003792f000000000f1000000000ba1f611291922a09068218849d0400001122283d000c9b07344c4dced24d00053c000000c69f0858194b6560001d634811d2819c2b22750d2080008d4ff80043c0000500006c0c1390ec08a1588f03715c9a0bd00036a8342a24941c7747c02b190a04450000008c80000012a7247e0002b497117233322000790003ce001351f71682f4719d300000093a7a0003f86506a174a38000004f019d329700000991a0000001e1010000c40005b80000078490000000000000003ea0004da59000618000000000007722104e9d0879e5236408000000002f000000000000178e70000012f97252a00000135000628a922b29c1ec0000024892ca68000001086f9db4fa5b0de832000a1c0000000000051a4e296140db9ba426698b21ce40c734520000ae00014184244000599b03c0364000cd20c000860a516c5d8e915d2d29a50e1fe1224e0990e80be580001e938e13438a0f480000bf96602a210962511861440000048825c9302919ca146d80639e77c509182d632c1e1b22a8089420a700090c2da523280002a8003cc7645da110882649d92515e7cc000f30001dc000960080007c8002e209000048232000000002a26803e8200000e00e9a94906b4d51981b80008504a1ee3b53f1732a01bc00000000000000c00001f0000000006f0001c50000002c10422663c0003d104000d78003a20cc681b93dc014af0e92620000023010a6753c8811a2710ee1bb224000ea1f40003bcdc12d000004a28000f20000000052ea44aa9b44aa4cc5a95625e0fcef0ad4181745f9ea4c2000a12424b4810001c60000000000022c0004c28d4827909a0a2170000c7273288000249a13342ad1d83a05a528a60e50fe58c001f12ae1d4b38001344040020b160000001ca1cc1780025432e2c800000000000000da000000000000007000000000048c000000d88e427a64128000301d72be12d0819e20e9b06a0cf000000000f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x2310c355518c430d5544310c35551cc03097d95300c29c644c030d5545300c27b654c0309798f54c825d63d5320cb18954c825e63153209758c54c823e64d4f208f59353c831e5494f20c755253c834e6294f20c795153c831d5454f208f99053c823d6414f20cb55342c82cd6310b20cb55232c82ac644cb20cb55132c834e534cb20ab19121c823e64d4e208f593538823e6414e208f59053882766114e209d584538832e5488620cb95021882e96008620cb953208825f63551209718d544827761551209d185544823f6454d208f19153482776154d209d185534823e6414d208f590534826e65d0920b358c424826c654c920ab19132482e8604c9208f990514823d64145209798c514825d63145209b99721482ac6448520ab992204826e62d50209798c540825d63150209d984540827561150208fd91530823c6454c208f990530823d6414c209b98853082766114c209d584530823e64948208f592520825e63948209758e520823f64544208f191510826d6588420ba580210823e64940208f592500826f65480209ed95200825e63d53109758f54c426f62553109b18954c423e64d4f108f59353c423e6494f108f59253c426e6294f109b58a53c423f6454b108f19152c423e6414b108f59052c425e6314b109758c52c426e62d52109b58b548425f63552109718d548423f6454e108f191538423e6414e108f590538426e6214e109b588538423e64d4a108f593528423e6494a108f592528425e6394a109758e528423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f994544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d1097994534431f5414d10c715053443556114d10cbd53524432c54d4910d3d4f524434c53d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524426e6514910cbd50524432c5414910d3d4c524434c5314910da5805244354538c5109d195314436852881109e195204425e63d50109758f540426e62d50109b58b540423d65950108f990540425e63150109758c540426e62150109b588540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c108f990530423d6414c109798c530426e6214c109b58853042766114c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520423e64148108f590520425e63148109758c520426e62148109e980520435553c40109e596100436952840109dd95100435553440109ed9510043695244010
  | 1 => 0xc66f62551319b189544c67b60551319e181544c65e65d0d31b3588434c63e64149318f590524c69c644c931b5185324c69e648c5318f990504c63d64141319b988504c66d62141319798f540c66e62150319b588540c67a60150319e580540c63e6494c318f592530c63f64548318f191520c63e64944318f592510c65f654c4319dd95310c63f64540318f191500c65e63153219758c54c863f6454f218f19153c863e6414f218f59053c863e64943218f59250c865e63d52219758f548863e64d4e218f593538863e6494e218f59253886cd6310a21ab191328863f64542218f191508865f63542219718d508863e64951219bd89544863e65151218f992534863d6494d219b58a534863f6454d218f191534867b6054d219e181534872c54885219798f540865d63d50219e983540867960d50218f596540872c62550218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c21d398a530871e5454c21c7551530863e6414c218f590530865e6314c219e98053086796014c21cb553420866d6510821b358c420866d658c821cb55232086ac644c821cb551320874e534c8219bd9521086ac64484219dd95210873a5494021ce552500875a5394021d654e500873a5454021ce551500875a5354021d654d500876b4254021da109500876a3254021da4c9500876b2154021da485500869d6310b409798e51d025d6394740ab18941d02ad6210e409798e529025d6394a40d398e529034d6394a40cb90e529032c4394a40cb94b429032e5250a40a798e419032e5290640cb948419032e52d02409b988535026d6214d40d3988535034d6214d408f997435031c53d0d40c714d435031c53909408f994425029d6310940c714c425023e65d0540c714f415031c5350540ab189415031c5390140ab98a405023d6590c40ab588431023f65508409bd89511026c62544408f596411029e63904408fd95401029c63500409ed95401026e62153309b58854cc23f6454b308f19152cc23e64947308f59251cc26e62d52309b58b548c2cd6210e308f992528c23d6494a30a7191328c23f64546308f191518c26f62546309b189518c29e648c6308f992544c25f63551308f994544c25e65cc530c7153314c31c544c530c7152304c26e62d50309b58b540c27661d50309d587540c23d6595030c718d540c23e64150309b988540c26d62150309d984540c2756115030c7553430c25d6510c30b3588430c32e5494830cb552520c32e5454830cb551520c31d54cc830a7191320c31d544c830d3949320c3365494430cd552510c3665294430d954a510c3365454430cd551510c3665254430d9549510c3574354430d510d510c3573254430d54c9510c25d658c430a799
  | 2 => 0x82c60e8380c21be2a41e0e71d015ca296d044190bd99408a3b43f83730e75c1a9913505c0e89420325588e1010b022c531d50580bc2100037a0000002b3d20001d9ea0000210589f042000000004301d0b59dc25e3c8ef918000384ce11b00024ca3079000048bc0001f863c000880642700018142c64ce900003e7d0a70003d8000000ac3c07d8000000004341e8cf000818cd9f34021dce60721081b8c70003ee370e5a123146b800909304000d300004042c000004321e0ff1001e6000001a9000000001ef292000230000000010d1300008083600020a4fced1ba16c000250390a47640a00020c1d8000001bc6343d000000000000000000002a800000044280f417a5cc00104362000e3000000000000001fe5b89c94a32e0007300018800001020000000303c1400c030280100c01008000640900400000050340001402000030000000c1100401030030080400c000300000c2400000004030040900800008080040600402000010200302000068030280201801000000080a000000001100c15000010000702c040000800402000000040500005000020000100007070000340000c010040000002000030040000800008010000305800000030000000c020340c0000101c030380d000020b0060040100c1900001000030301002000010000100001c020000309c03010020000000401028000142300c0000c010026f62547439b18951d0e6e62943439b58a50d0e3f6550c4397d954310f2f4354843d390d5210f2d4354843d350d5210e5e63947429758e51d0a5f63543429718d50d0aad6210e428f9974350a3d6590c42c754e4310b1d5310c42ab5884310b1d53d0842d354e4210a3f6550842c754d4210a6f6550842d354d4210a7661d53329d58754cca3e64947328f59251cca3f64543328f19150cca7a60d52329e583548ca3f64546328f191518ca3e64942328f592508ca3e64951328f994544cb1d6315132cb588544cb1c5490d3297195434cb2c5490932e390e424ca6c6550932e350d424ca3d65950328f990540ca5e63150329b988540cb1d54cc832cb552320ca5f654c832c7551320ca6f654c832cb551320caad6210f419b98a50d066d62943419b98a539066d6294e41d398a539074d6294e41c794f439071e5350e41c794e429069d6310a41c794c429071e53d06418f99443506ad6210d419798c525065d6314941d398c525074d6314941cb90c525072c43149418f997425072c52d0941cb149425069e6390541cb14a415063f6550c418f596421069d63108418fd9541106ac62504419dd95411065f63540419718d501066e62d53319b58b54cc71c63553319b98854cc66d6215331c755343cc6cd6210f31cb95252cc72d5494b31cb95152cc72d5454b31c755332cc69c644cb31c755132cc74e524cb31c7953318
  | 3 => 0x1eb19200096158194430002084185bcc58002a23dc001af0007a0000b100081cd50f9000688129e12ce85cc281334e1f0a01641b45b0538000cc4b84e87b04e188b403339e1f42e8000000000000000000000000000000001e60be000000003fa000000000000002c8000000000000000026400000000000879a3358000ff80000014c0000000000000000000000fa8851722780019226c000b489b166000000000000000010e1c63b0278002560007e8971868008880023c000000000d0000748cb02e6300d000000000000000540010a000000000000001ca2a85200001200099800000000001b207e000f8800000194309c93e00000000009601d098e0000000ba80023e178201724146e02689a2c4304e017c0365f8000001ea45000000000000208000000002600036016c001f224a3b82b0003da48000000000000ba000242000000000002586a0d92ae704000000000000000c0006240000024e504481652b4120000000000d8f1881000000a38f000000000000000138000000de000640000000009a04939a80c3480000038800000000000001150000004a9241ac00000000290000d09e700000000000000000bf8be030000b31c20e2000000a20080004799e0007e4df8890388105b88e02a34cd680608674096a0d22e0081c0ae19c600289380000000008724c00046000306360a7a0f00070c00102180680ad860246208398001fc11c668002066544a0001063740000001c4a45f9132b2000000003c4078e994b27a000050b00007ed048a3000548000003326ec00000000000ae86b00071ca98441ec5a8aa8313880d0880a00ce0c04c0b4298668f7108000218001f8170000000050004c40015e000000000001f6000001dd2be294001e500004000000000540000000003e0001a53785802d1440b8000068260002b40001d0000001f0000000000012800000000029016058789c52784ecdc96118c000000cc05041c00000000000851160003bc0000040a000720001ae000eb19f368000e41762b86f855863000000078003a831c000031d400000000264000002153b66d44917a356760000000000b4bb9902442f08e800420000000001d636c000750000902a0000002bc000c51227388d000422284b88ba3c80008c80032c00000184046674690001a0448469b61a23e8000001141f89b8b53481a8c414d286200369fa41c728db93e1647f09a8d52fa5e4aa0a830c0b8d98bb2547789d19
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x1024008000000054e0001405800ca1d444d0002c01010000000083c660000c4800004d7000820021041018358d6215132a1ae529a8720d0d731494250707318a520a83435c86355331838ecaa26598d0d7318954086163b2a899043525cc4254021a50e8992a010d28744855008686b9ca4a14818398e5290640a1ae429a86a060c53189415030629cc520281435c86355030838ecaa264185457210d510c28a3a264a886185991518c430c28c8a8a601850d7318954c82163b2a8996418a9516008620
  | _ => 0
def s1K2 : Nat → Nat
  | 0 => 0x10000806080d8798c529054180d8798e529064080d8714c625054080d8714e6290140
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 664
  | 4 => 539
  | 3 => 25
  | 2 => 4
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s1K7 (i*5) 5
  | 6 => packedAt s1K6 (i*16) 16
  | 5 => packedAt s1K5 (i*27) 27
  | 4 => packedAt s1K4 (i*38) 38
  | 3 => packedAt s1K3 (i*49) 49
  | 2 => packedAt s1K2 (i*60) 60
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s1K7 (6+((h/1+packedAt s1K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s1K6 (731+((h/13+packedAt s1K6 (640+(h % 13)*7) 7) % 69)*7) 7
  | 5 => packedAt s1K5 (20138+((h/221+packedAt s1K5 (17928+(h % 221)*10) 10) % 963)*11) 11
  | 4 => packedAt s1K4 (22272+((h/179+packedAt s1K4 (20482+(h % 179)*10) 10) % 860)*11) 11
  | 3 => packedAt s1K3 (1273+((h/8+packedAt s1K3 (1225+(h % 8)*6) 6) % 48)*6) 6
  | 2 => packedAt s1K2 (244+((h/1+packedAt s1K2 (240+(h % 1)*4) 4) % 11)*3) 3
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x81fff83ffffe1e0ff87f87fe1fffe07d19f3f3
  | 2 => 0xfe1fffc1f87ffff07f87f87fe1c0fffee63c9f
  | 3 => 0xffe0fffe007fe3ff8007ff8ffe00ff8307cf1c
  | 4 => 0xffffff8003fffff8000fffff0003f80fe0
  | 5 => 0xffff0000000003fffffffff000000003fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xa402088850102002900980920252212808d131
  | 2 => 0x884110480a400502882082420844a50622486
  | 3 => 0x144aa290354906a58444d50b540a950b054b18
  | 4 => 0x5954c425240d4b394d50440d992c0613b00ec0
  | 5 => 0x61988739c67193ce7667664110301863dfb000
  | _ => 0
def s1Atlas : Atlas := ⟨7,rawDecor 61 s1Pos s1Neg, 0xfafafaa0faaaf0a0fafafaa0faaaf0a0fafafaa0faaaf0a0fafafaa0faaaf0a0fafafaa0faaaf0a0fafafaa0faaaf0a0fafafaa0faaaf0a0fafafaa0faaaf0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_17053
namespace PEqualNP.Outside.L_meta_17053
open PEqualNP.Outside.L_meta_17053.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x8947a70c6cd2f007c0082ab9823009000d0000c032c5cc8b12a800000749800a45307200000e04800005a298ac500062b00a50a238789000050000000008000000000004000060800011000c109ff43bf43fe43fd43bd43fc43ff42fe42be42fd42fc42bc42ff32fe32ee32fd32ed32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0xd3a6440240ba1b341d0be000001426000b000146200060d6021d93428710e8343e9e2a000987e3f8fc0000000000000000e03400000005a0042a453000111140089440a800001e1f400431989c480046a3c003e22000007c0001c006500280640000000f07a00290dc8c31a386a2f3680000000000062774da092c150000000722902cc00824000200012800bc004b8b06e561e804ae870c9e452000018400172588c8e5c4f9d8aa000012514000300068004d1bc4c814980142702014082460728ca2693514cd84a1804924364200000000003cea730000144002d824509c06044005a278ac00952c909280027000000033961167b1ca0c42040007800000e0000066100005c864c8007400000082800181800101020306020001000282010100810d000080808184010189800000820100008000000080800182008b8081800281804f94b439ea8e873e50d0e7aa921db94a43b6a94879f5350e78a4a1cfd45439e282873e5410edca421db548439ea9c853e5290a7aa3214f94242af298855d5310b3ca6214f54c42cea98851d5310a7ca4216b948429ea88853e5010a7ca9994f55332cea1e653f548ca78a9196b90a32d621465af548cb58a9195b54e32d7a1c65ad438ca7ea8994f15132cea1a65ae424cb5884996bd5132d62a265cf534cb5e86997390d32d6a1a65cd434cb1a86994f950329eaa0656e520ca7aa7a0cf94b41d719683ad32d067ca1a0cf55241b7a92836c525067ea6a0ebd49419e29283ac5250658a4a0eb8c941d699283b75150678a0a0cf950419f2a6633d54cc6dca598db54b31e6996633e548c67aa918cf951319eaa263cd324c67ca818cf55031b7290636d520c6f4a018de540319faa6433c54c867ca910cf55221d6214433f5448678a890cf950219eaa0435e53086baa610eb10821bd280437950086dca5205b54a409ea9c813e529035ca5204b94a40d6a9481ae329035a65204f546409f284813d531027ca4206b8c840d6990813d511027ca0206e940409f2a6613d54cc2dca5985b54b309faa4613c548c39a65184fd51309e2a2613e540c27aa8185b94830b6a9061cd320c2eca2185d544309f2a6413d54c82bca7905754f20d6216413e548827aa9104fd51209e2a241ac424827ea8104f150209f2a6213d54c427ea9084f152109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x36000003a00000174200c800001100007400000019800a0060e28008805600000000001c0eb800000000000000000000032500000000009caf267802d6a0000020a400a00580200600000003c0004e8c01264c04001a01237000001554c4c000000f9b586930908eda280201c0016040000002000820000100000008000081008b18951d0e2e6294343c39895310b0d53948428e983548ca8d63d5232aa983548ca8d631523287195434ca8d6490d32a3995434ca8c6550d32a3d85434ca8c6050d32c354d32d062e62943419358c525061d6314941a358c525070e63149418b58c525070d63149418358c525062c658c9418b195325070d544cb318b189548c62c62551318e181544c70d544c9318758c54c868d6310a218b594420868d6310821c354c420872842540219358e529021d6394a40a358e529030e6394a408b58e529030d6394a408358e529022f658ca408bd95329030d534c8408b189511022e62d5230c3d51328c22e62d5130c3551320c3453254430a358c42c830d5310b20a358c424822e62d50208758c540823561150208b18954c422e62d5210
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0xc92902038008000031080284b84c4a9885229c26550d3281ae7314a1a0d0870551324c606bb2a621043425cc425402181ae6312a22040d7398b5408206b98c4aa621035ce62d5210
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 50
  | 4 => 165
  | 3 => 60
  | 2 => 10
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s2K6 (i*5) 5
  | 5 => packedAt s2K5 (i*16) 16
  | 4 => packedAt s2K4 (i*27) 27
  | 3 => packedAt s2K3 (i*38) 38
  | 2 => packedAt s2K2 (i*49) 49
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s2K6 (6+((h/1+packedAt s2K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s2K5 (912+((h/16+packedAt s2K5 (800+(h % 16)*7) 7) % 73)*7) 7
  | 4 => packedAt s2K4 (4895+((h/55+packedAt s2K4 (4455+(h % 55)*8) 8) % 239)*9) 9
  | 3 => packedAt s2K3 (2420+((h/20+packedAt s2K3 (2280+(h % 20)*7) 7) % 126)*7) 7
  | 2 => packedAt s2K2 (502+((h/3+packedAt s2K2 (490+(h % 3)*4) 4) % 15)*5) 5
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xf07ffc1ff87fc3c3fc3fc3fe1fc3fc1e99f673
  | 1 => 0xff87ffe1ff87fffc1fc3fc3fe1fc1fff66399f
  | 3 => 0xfff87ffe0007fc7fe003ffc7fe001fe187ce1c
  | 4 => 0x7ffffff8007ffffc0007ffffe001f80fe0
  | 5 => 0xffff80000000007ffffffff800000001fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x1501044450810400a404c04a0241444c08d231
  | 1 => 0x20200880800a00080841041020900910222086
  | 3 => 0x431351483554a0d562226a875408d2c5854e18
  | 4 => 0xa5462112440a96652a82205992a8081d00d40
  | 5 => 0x8c66439dc667327b9f33b32110330319ffb000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeeeee88eeeecc88eeeeee88eeeecc88eeeeee88eeeecc88eeeeee88eeeecc88eeeeee88eeeecc88eeeeee88eeeecc88eeeeee88eeeecc88eeeeee88eeeecc88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_17053
namespace PEqualNP.Outside.L_meta_17053
open PEqualNP.Outside.L_meta_17053.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x8d2310068000001908004012a7000058058341a660117993c88e983e0168c145d52e52707130e54400000000012000050040880000141400480800000000006d00056007802c0000009003008b001cd090218004ff43fe43be43fd43fc43bc43ff42fe42be42fd42fc42bc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21ef21fe21fd21ed21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0xd00000002040062000000000358ac008900000aa0021000765e0000000000007c00000000000000c8000000000014400068007e2846000000000000000000000008b2c800ba00000011000001a80000000791a0016000445b001700038032084c93001e82a9d0019c2400001f40036000a462000000128a025800008700000000a00000043300000000000000400000000480000000fc000017c000000000d821191493c5800000004600000f80000000fe6e4b89400000000000004a8000000020000000000000000002680000001007210229c4003c330000000000000000000000000000004e72421bcc24a0013548000000022004824400000026cc0000e82400181e8bc3850060012400001d4e60000000463a4f8006a0000001460040228000000000000000000a6003b1513083001242c002d000000e000011e00221200000001c09800321e400013400006860000000001b9b42e6500000c656219a4ee30000009e0000258000816800000009a640000272700000470b800000d800e85700000000000000a2004282c0000028008e7800000050000802000000400020100000000000802030000000040000000010000000000000000010000000010080c0400000000000000000001000040202005b94a43b6a94873e5390e7ca521eb94a439729487ad5290e7aa321cf542439f298879e5310e7ca421cf544439ea80873e5390a7ca5214f546429ea8485765110aeaa2214f94c429f29085ae5210b6ca2214f54442daa8885355110a7aa0214f953329eaa6653e548ca7aa9196b10a32bb28c6575518ca7ea8994f15132d6212653f540ca78a8194f94f419f296833d50d067aa920db94a41b6a94833c5350678a4a0edd45419fa82833e54106dca420db548419faa6633c54cc67ca918cf55231b7294636d528c67ea898cf151319f2a0633d540c6dca418db54831bd2806379500c67ea990cf15321d721643ac42c875ea990eb15321d721e43ac43c875e8390eb507219f2a4433d54886daa510ed506219faa2433c544875c8490eb10921daa0a43af5448758a890eb90d21d621a43e7514875e8290f990521d6a0a43e5414874a8290f9cc521f218a433e540867aa810db948219f29e813e52d027aa3a06bc8740d690e813d54902dea4a05b149409e29a81af5250278a4a06b1494096292813f515035e42a06b48540dda82813e541027ea9984f153309f2a4613d548c27ea8984f15130b7a92616c524c2eea2985d145309f2a0613d540c2dca4185b54830bb2886175510c27ea9904f153209f2a4413d548835885104fd51209e2a2413e540827aa8105794c20aea9841ac42082eca2105d544209f2a6213d54c42dca5885b54b10f290e213e548427aa9084f951109eaa221e5214427ca8084f55010af298215d53042dca4085b54810
  | 1 => 0x68003e3d81c280000000820f000a9420000
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x8b848300bc000000150000009800018000020121d20016b56869d0a10a40330000012000003638851002208d800000000000058000000002a000004c8c0000a58000180002c4a38b9f00014001e81cb26ec18873ce0c194e5158d7616000000004681041008012440000600003995865290e356194a43a95865290f266194a438b5865290f256194a43895865290e2c6254043c99495110b266254442a9584428cb244254632a9584424ca2e62d50328d584540ca3960150328b98a53d062c62543418b98b54cc62e62d51318798f54c868e63d5321a958754c86a561153218b99643c863465505218b99643486a56110d21a959241486a66550521a919541486a46350521a9d8141486a764cc521a959031486e1600c5218b98a53d032551487409958452502356114940a9584525032661149408b5845250325611494089584525022c65c85408b195215022e62d53308b189548c2356115320a9584428822d6510820c354c42082a56110820c9109510832554487108b189548421c63551108b18954443255448510
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x6000400148008d07024310212b88c4a8087415ce625444290ce732a8290c2675d933148612b8cc529e81095c662d533084ae2312a9186055358442082123b2a890a21411cd5448510
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 50
  | 4 => 165
  | 3 => 60
  | 2 => 10
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s3K6 (i*5) 5
  | 5 => packedAt s3K5 (i*16) 16
  | 4 => packedAt s3K4 (i*27) 27
  | 3 => packedAt s3K3 (i*38) 38
  | 2 => packedAt s3K2 (i*49) 49
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s3K6 (6+((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s3K5 (912+((h/16+packedAt s3K5 (800+(h % 16)*7) 7) % 80)*7) 7
  | 4 => packedAt s3K4 (4950+((h/55+packedAt s3K4 (4455+(h % 55)*9) 9) % 381)*9) 9
  | 3 => packedAt s3K3 (2420+((h/20+packedAt s3K3 (2280+(h % 20)*7) 7) % 105)*7) 7
  | 2 => packedAt s3K2 (505+((h/3+packedAt s3K2 (490+(h % 3)*5) 5) % 17)*5) 5
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xfffffc3ff87fffc1e1c3fffe1f83fffe07f27f
  | 1 => 0xf07ffc1ff8f87fe01fc787fe3fc3c1f193d93
  | 2 => 0xff87ffe000ff87ffe007f87fc003fe1e1ce1c
  | 4 => 0xf0007ffffff0007fffff8007ffffc001fe0fe0
  | 5 => 0xffff80000000007ffffffff800000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x1000408408200004040908804810508025025
  | 1 => 0x4251488494144c4a10a42c5321282855092492
  | 2 => 0xa4335114352944d6b2204d474818b2c5618e18
  | 4 => 0x20a42221200111252509000492528080b40b40
  | 5 => 0xc8c643b9c64e6679d9f2766100632319dff000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xfefea8a8eeeea8a8fefea8a8eeeea8a8fefea8a8eeeea8a8fefea8a8eeeea8a8fefea8a8eeeea8a8fefea8a8eeeea8a8fefea8a8eeeea8a8fefea8a8eeeea8a8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_17053
namespace PEqualNP.Outside.L_meta_17053
open PEqualNP.Outside.L_meta_17053.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x28c2a590e64080960000800abe43bc43bf42bd42bf41bd41ef21f621ed21f521e521be40bc40
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x2a490000004c30c0042ca71c070ce94243b2a9443a7414874a8290e9d0921d2a1243a6544874aa890e990d21d221a431e539034a43206948440
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x2c000200a118d54486a06055121a898243487065348640
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 13
  | 3 => 13
  | 2 => 4
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (i*5) 5
  | 4 => packedAt s4K4 (i*16) 16
  | 3 => packedAt s4K3 (i*27) 27
  | 2 => packedAt s4K2 (i*38) 38
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (6+((h/1+packedAt s4K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s4K4 (228+((h/4+packedAt s4K4 (208+(h % 4)*5) 5) % 17)*5) 5
  | 3 => packedAt s4K3 (371+((h/4+packedAt s4K3 (351+(h % 4)*5) 5) % 18)*5) 5
  | 2 => packedAt s4K2 (156+((h/1+packedAt s4K2 (152+(h % 1)*4) 4) % 11)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xffffe0f87c3fff0f0f0ffff870707ffe0ff49f
  | 1 => 0xf07fff007ffe1ff00ff1e1ff807ff83f3138f3
  | 2 => 0xff83ffff803fe1fff001fe1fff807fc1c1cf1c
  | 3 => 0x3ffffffc001fffffe001fffff8001fe0fe0
  | 5 => 0xfffc0000000001ffffffffe000000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x12102220904c00030302423012120b18065485
  | 1 => 0x250a44152a1131308490b14c812550a5112832
  | 2 => 0x412a88540aa113549081350d25016485418918
  | 3 => 0xa51128040044489292400124a4a0108aa06c0
  | 5 => 0x8c621ce6733999eecec9d9840c0c4631fdf000
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xfea8fea8fca8fca8fea8fea8fca8fca8fea8fea8fca8fca8fea8fea8fca8fca8fea8fea8fca8fca8fea8fea8fca8fca8fea8fea8fca8fca8fea8fea8fca8fca8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_17053
namespace PEqualNP.Outside.L_meta_17053
open PEqualNP.Outside.L_meta_17053.Model
def s5K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x16800ef21ed21df30dd30
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 4
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s5K5 (i*5) 5
  | 4 => packedAt s5K4 (i*16) 16
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s5K5 (6+((h/1+packedAt s5K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s5K4 (67+((h/1+packedAt s5K4 (64+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x787e7fc7f0f1c7fc718f8fc3f1c1c3ff19349f
  | 1 => 0x7f9f87f8ff01ff1f81f1f1fc3e01ff8726c8f3
  | 2 => 0x801ff800fffe07e3fe01fe003ffe03f8c70f1c
  | 3 => 0xffe00000fffff803fffe00003ffffc00f80fe0
  | 4 => 0xffffffff00000003ffffffffc0000000fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0xa02210812020a0010820240a04850a4081485
  | 1 => 0x11041081202480208010908812048912024832
  | 2 => 0x548129244609405a201a41914940a52470918
  | 3 => 0x220165248a81024a55a40022a9293024b806c0
  | 4 => 0x445146000cc924936949493300302040f5a000
  | _ => 0
def s5Atlas : Atlas := ⟨5,rawDecor 31 s5Pos s5Neg, 0xfeeefca8feeefca8feeefca8feeefca8feeefca8feeefca8feeefca8feeefca8feeefca8feeefca8feeefca8feeefca8feeefca8feeefca8feeefca8feeefca8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_17053
namespace PEqualNP.Outside.L_meta_17053
open PEqualNP.Outside.L_meta_17053.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x715187c1a812893000080a3f381929736b95120a851800441f3460dc50852587997811cac74900010e340003a9c01100f40316cb4035007998076c80180001c0b5601780004c01a0b000800124000812a00f820448f030424082007fd5001fe54007f55001fc54007fd4c07fe53007f54c07fc53007fd0c07fe43007f50c07fc43007fd4805fe52007f54805fc52007fd0805fe42007f50805fc4201ffcc805fe32007f4c805fc3200ffd44037f5100ff94403fd5100df54403fc5100ffd0403fe4100ff50403fc4100ffcc403fe3100ff4c403fc3100ffc8403ef2100ff88403fd2100fb48403fc21007fd4001fe50007f54001fc50007fd0001fe40007f50001fc4001ffcc001fe30007f4c007fc30017fc8001fe20007f48005fc2000ffc4003fe1000ff44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x826003ff0c13001fb8609800ff8304c019ff902600cff0813005ffe209802ffe104c017fd082600bff4413005ff2209802ffc104c011ffb2c4000bfd9620007fccb1001efe6588001feb2c4000bf59620047f8cb1001efc6588011ffb244000bfd9220007fcc91001afe6488001feb244000bf59220047f8c91001afc6488001ffaa44000ff95220007faa910003fc5488011ffb1c4000bfd8e20057fcc71000efe6388001feb1c4000bf58e20047f8c71000efc6388001ffa9c400aff94e20007faa71002bfc5388001ffa1c400aff90e20007fa871002bfc43880057eb144002ffd4a20017fca51000bfd5288005fe2944002ffd0a20017fc851000bfd4288005fe2144002ffcca20017fc651000bfd3288005fe1944008ffd862004dfec310027fe61880037f30c4009ff5862004dfac310023fc61880037e30c4009ffd462004efea310027fe5188013fea8c4009df5462004ff8a310027ff4188013ff20c4009ff5062004ff88310027ff3188013ff18c4009ff4c62004ff8631000bff2188005f790c4002ff88620017fa4310027ed2188005fe10c4002bf98220007fea110023fe5088001fea844008ff14220007fe8110023fe4088001fea044008ff10220057fe6110023fe3088001fd1844000ff4c220007f26110023fc3088005ff9044002fbc8220017f64110023fc2088005fc1044009ffc4220047fc2110027fd1088011fe0844000ffd9520005feca900037f65480013fb2a4000ff9952003dfcca90003fd65480017eb2a4000ff1952003df8ca900037c65480013e32a4000ffd9120005fec890003fe644800d7f3224000ff59120005fac890003fc644800d7e3224000ffd5120007fca890003fd5448001fe2a24000ffd8d20005fec690017fe63480077f31a4000ff58d20005fac690017fc63480077e31a4000ffd4d2002ffca690003fd534800bfe29a4000ffd0d2002ffc8690003fd434800bfe21a4002bfd8920017fea49000bfe5248005fea924002ff14920017fe849000bfe4248005f72124002ff50920007da849000bfc4248005ff9924002ff8c920017fa649000bfc3248009ffb0a4004bfd8520027fcc290006fe6148009feb0a4004bf58520027f8c290006fc6148009ffa8a4004dfd4520027fca290013fd5148009bea8a4004ff14520027fe8290013fe4148009fea0a4004ff10520027fe6290013fe3148009fe98a4004ff0c520017fe429000bef2148005ff10a4002ff48520027da429000bfc21480057fb024000ffd4120007fca090003fd5048001fe2824000ffd0120007fc8090003fd4048001fe2024005ffcc120007fc6090003fa3048001fe9824000fe4c12002ff8609000bff2048005fd9024002ff88120007dc409000bfc2048005f61024002fe08120027fe2090013fe1048009fe8824004ff04120
  | 1 => 0xffd211001ff6908800fff08440095fcc020003ff5010011ff2808000ff54040047f8a02001bff401000ddfa008008ff90040037f4802001bfd4010001dea008006fe5004008ffe6020023fc3010021ff9008008ff0804007ffe2020023fe101001ffe8808008ff04040047fecb18002ff658c001ff32c6007bf99630006fccb180027e658c001feb2c6000bf59630006facb180027d658c011fe32c6007bf19630047fec918002ff648c001ff3246006bf99230007fac918002fd648c011fe3246006bf19230007fea918003fe548c001feaa46000ff1523001dfac71800fff538c007ff29c6003ff54e3001ff8a71800fff438c007ff21c6003ff50e3001ff88718023ff628c01dff3146002bf98a30007fac518002fd628c011fe3146002bf18a30007fea51803bfe528c001fea94600eff14a30007fe851803bfe428c001fea14600eff10a3001ffe651800ffe328c007fe9946003ff0ca30047fec318036ff618c01bff30c6001bf9863006ffac318036fd618c011fe30c6001bf1863006ffea3180377f518c01bff28c600dff5463006efaa318037fc518c01bffa0c600dff9063006ffa8318037fc418c007ff98c6003ff8c63001ffa631800ffc318c01bff90c600dfbc863006ffc4318037fd218c01bf690c600dff0863001dfcc118003ff508c011ff2846000ff54230047f8a118003ff408c011ff2046000ff50230047f8811800fff308c007ef9846003fecc230047f8611800ff8308c01dff9046008ff0823006ffe2118023fe108c01bfd084600dff4423006ff22118023fc108c001ffb2a6000bfd9530007fcca9801efe654c001feb2a6000bf59530007f8ca9801efc654c001ffb226000bfd9130007fcc89801afe644c001feb226000bf59130007f8c89801afc644c001ffaa26000ff95130007faa898003fc544c0077fb1a6003ffd4d30007bea69800ffe534c007fea9a6003ff14d3001fb8a69800fff434c007ff21a6003f790d3001ffa8698003dd434c007fe21a6000ffd8930005fec498033fe624c0057f3126000ff58930067f8c49800afc624c001ffa92600cff94930007faa498033fc524c001ffa12600cff90930007fa8498033fc424c007ff9926003f7cc93001ffc649800ffd324c001ee9926003ff0c93005ffec29802eff614c017ff30a6001bf9853005ffac29802efd614c017fe30a6001bf1853005ffea29802f7f514c017ff28a600bff5453005efaa29802ffc514c017ffa0a600bff9053005ffa829802ffc414c007ff98a6003f7cc53001ffc629800ffd314c017ee98a6003ff0c53005ffe429802fef214c017ff10a600bff4853005fda429802ffc214c0077fb026000ffd4130007fca098003fd504c001fe2826000ffd0130007fc8098003fd404c001fe2026003ffcc13001ff6609800ffe304c001ef1
  | 2 => 0x40097fc832004bfd419000dfe20c8012ffcc640097fc632004bfd3190025fe18c8012ffc8640097de432004bfe2190025fe90c8012fb48640097f8432001afe6090001ffa848008ff94240007faa120023fc509000dffa048000efd0240037f6812005fff3090011fe1848016ffc8240047f8412004bff1090011ff0848012fe84240097fa212004bf91090011fe0848000ffd9540005fecaa00037f65500013fb2a8000ff9954003dfccaa0003fd65500017eb2a8000ff1954003df8caa00037c65500013e32a8000ffd5140037fca8a0003fd545000dfe2a28000ffd8d40005fec6a0057fe63500077f31a8000ff58d400aff8c6a000efc6350001ffa9a8015ff94d40007faa6a0057fc535000dffa1a8015ff90d40007fa86a001bfc4350001ffb128000bfd89400a7fcc4a000afe6250001feb128014ff18940015f8c4a0003ff5250029ff2928000ff549400a7f8a4a001bff4250001dfa128014ff90940007fa84a0003bd425000dfe2128015ffcc9400a7fc64a0003fd3250029fe1928013ffd854009dfec2a004ffe61500037f30a8013ff5854009dfac2a004ffc61500037e30a8013ffd454009efea2a004ffe5150027fea8a8013df5454009ff8a2a001bff4150027dfa0a8013ff9054009ffa82a004fbd415000dfe20a8013ffcc54009ffc62a004ffd3150027fe18a8013ffc854009fde42a004ffe2150027fe90a8013fb4854009ff842a0003ff5050001ff2828000ff54140007f8a0a001bff405000dfda028000ff901400077c80a0057ff305002bfe1828014ffc81400a7f840a004fff1050027ff0828013fe8414009ffa20a004ff91050027fe0828008ffd9440035feca2001bfe651000f7f3288006df99440004fcca2001bfd65100017eb288006df59440004faca20023fc651000d7e3288006bf99040037fea82001bfe541000dfeaa08006ff15040047fec62001bfe63100077f3188006f798c4001dbcc62001bfd63100017eb188006f758c40005bac620023fc63100077e3188000ffd4c4008ffca620003fd5310023fe2988006ffd0c400377e862001bfe431000dfea188000ef50c40037f88620023ff621000dff3108002bf98840037dcc42000aee621000dfeb108000bf58840037dac420002ed6210011fe3108002bf18840007fea420043fe5210001fea908010ff14840037fe842001bfe421000dfea108006ff1084008ffe6420043fe3210001fe9908010ff0c840047fec22001aff611000dff3088001bf98440037ecc220006f6611000dfeb08800fbf58440037eac220002f56110011fe3088001bf1844007ffea22003f7f511001fff288800fff5444007efaa22003ffc511000dffa088006ff90440037fa822001bfc411001fff988800fff8c44007ffa622003ffc311001fff908800ffbc844007ffc422003
  | 3 => 0xf218a000ff50c500eff88628023ff621400fff310a002bf9885003ffac428002fd6214011fe310a002bf1885003ffea42801ffe5214039bf290a007ff5485003ff8a42801f7c5214001ffa10a01cff90850007fa8428073fc421403bff990a01cff8c850007fa6428073fc3214011ffb08a007bfd845003ffcc228006fe611400ffeb08a01bbf58450047f8c228006fc611400fffa88a007dfd445003ffca22801ffd5114037bea88a007ff144500dffe822806ffe4114037fea08a01bff104500dffe622806ffe3114037fe988a01bff0c4500dffe422806fef2114037ff108a01bff484500dfda422806ffc211403d7f300a007ffd405003efea028023fe501400ffd280a007ff54050006faa02801ff9501403bff980a008ff0c0500e7fe4028023fc2014037ff880a008ff840500dffa2028023fc101400dffb2e8006bfd9740037fccba001efe65d000dfeb2e8000bf59740037f8cba001afc65d000dffaa68006ff95340037faa9a001bfc54d000dffb1e8006ff98f4001dfcc7a001bfd63d00017eb1e8006ff18f4001df8c7a0003ff53d0035ff29e8000ff54f400d7f8a7a001bff43d000dff21e8006ff50f40037f887a001bff62d000dff3168002bf98b40037fac5a0002fd62d000dfe3168002bf18b40007fea5a0067fe52d0001fea968019ff14b40037fe85a001bbf42d000dff2168006ff50b400077a85a001bfc42d0035ff9968019ff8cb40007fa65a0067fc32d000dffb0e8006bfd8740037fcc3a0006fe61d000dfeb0e8018bf58740037f8c3a0006fc61d0031ffa8e8018dfd47400c7fca3a0063fd51d0031bea8e8018ff14740037fe83a001bbf41d000dff20e8006ff507400c77a83a001bfc41d0031ff98e8018ff8c7400c7fa63a0063fc31d0031ff90e8018fbc87400c7fc43a0063fd21d0031f690e8018ff08740007fea1a0003fe50d0001fea868000ff143400d7fe61a006bfc30d0033ff9068019ff083400c7fe21a0063fe10d0031fe8868018ff04340047fecb20002ff6590001ff32c8007bf99640007facb20002fd6590011fe32c8007bf1964009dfac920003ff549000dff2a48000ff55240037f8a920023ff639002fff31c8003bf98e40007fac720002fd6390011fe31c8003bf18e40007fea72005ffe5390001fea9c8017ff14e40037fe8720003bf439002fff21c8000ff50e400077a872001bfc4390011ffb148016ff98a40015fcc520003fd62900017eb148008ff18a40015f8c520003ff529002dff2948000ff54a400b7f8a52001bff429002dff2148000ff50a40037f8852005fff329002dff1948000ff4ca400b7f86520023ff61900257fb0c8012ff9864000dfcc32004bfd61900257eb0c8008ff1864000df8c32004bff5190025bfa8c8012ff94640097faa32004b7d5190025fe28c8006ffd06
  | 4 => 0x93fc21d404dff986a026ff0c35012ffe41a8097fc20d4049ff886a024ff84350127fa21a8093fc10d403f7eb2ca008ffd9250007fcc92801afe6494001feb24a000bf59250047f8c92801fff5494001ff2a4a000df95250007faa92801ffc5494001be2a4a008ffd8e5011ffcc72800efe6394001ef31ca003b798e50007fac728002fd6394001eeb1ca000b758e50047f8c72800efc639400fffa9ca000dfd4e5011ffca728003fd5394001bea9ca007ff14e50007fe872808ffe4394001fea1ca023ff10e50047fec52808bfe62940057f314a000ff58a50005fac528023fc62940057e314a007ffd4a50117fca52808b7e5294001fea94a007ff14a50116f8a528003ff4294045ff214a000ff50a50117f8852808fff3294045ff194a000ff4ca50117f86528023ff619403d7fb0ca01eff9865000dfcc32807bfd619403d7eb0ca008ff1865000df8c32801fff519403dbfa8ca01eff946500f7faa32807b7d519400ffe28ca01effd06500f7fc832807bfd419403dfe20ca01effcc6500f7fc632807bfd319403dfe18ca01effc86500f7de432807bfe219403dfe90ca01efb486500f7f8432801efe609400fffa84a000dfd425003ff6a12808fff3094011fe184a022ffc8250047f8412807bff1094011ff084a01eff44250047f82128003ff64540017fb22a000ff99150007fac8a8003fc645400d7e322a007ffd5150006fea8a8003fe5454001feaa2a000df5515003ff8a8a8003ff63540017fb1aa021ff98d5001dfcc6a8003fd6354043fe31aa003bf18d5003ffea6a8087fe5354043bf29aa000ff54d5003ff8a6a80877c5354001ffa1aa021ff90d50007fa86a8087fc4354001ffb12a000bfd8950107fcc4a800afe6254001feb12a020ff18950015f8c4a801fff5254001bfa92a020ff94950007faa4a80037d525400ffe292a000ffd0950107fc84a8003fd4254041fe212a021ffcc950107fc64a8003fd3254041fe192a01fffd85500fdfec2a807ffe61540037f30aa01fff585500fdfac2a807ffc61540037e30aa007ffd45500fefea2a807ffe515403ffea8aa01fdf5455003ff8a2a807fff415403fff20aa01fff505500fff882a807fff315403fff18aa01fff4c5500fff862a807fff215403ff790aa01fff885500fffa42a807fed215403ffe10aa007ffd415003ff6a0a8003fe5054001bf282a021ffcc15010ff860a8083ff2054041fe102a01fffc41500fffc20a807ffd105403ffe082a007bf99450047fec82801ffe641400d7f320a007ff59050005fac828023fc641400fffaa0a007ff95050006fca82801ffd541400ffe2a0a007df15050047fec62801ffe63140077f318a007ff58c50005fac628023fc63140077e318a007ffd4c5003efea62801ffe531400ffea98a000df54c5003ff8a628003ff431403bf
  | 5 => 0x942037de84a100bfe4250805df2128402ff109420177884a100bec4250805ff9928402ff8c942017f864a10a3ff61508517fb0a8428ff9854200dfcc2a10a3fd61508517eb0a8428ff1854200df8c2a10a3ff5150851bfa8a8428ff94542147faa2a10a37d5150851fe28a8406ffd0542147fc82a10a3fd415080dfe20a8428ffcc542147fc62a10a3fd3150851fe18a8402ffc8542017de42a100bfe2150805fe90a8428fb48542017f842a1003ff60508017fb028400ff98142007fac0a1003fc60508017e3028429ffcc14214ff860a100bff2050805f79028402ff08142147fe20a10a3fe1050851fe8828428ff04142007feca99002ff654c801bfb2a64009fd9532007fcca9901efe654c801feb2a6400bf59532007f8ca9901efc654c801be32a64009f19532007fec899002ff644c801ff3226406bf99132007fac899002fd644c801fe3226406bf19132007fea899003fe544c801feaa26400ff15132015fec69900fff534c807ff29a6403ff54d3201ff8a69900fff434c807ff21a6403ff50d3201ff8869900aff624c805ffa926402ff94932017faa49900bfc524c805ffa126402ff90932017fa849900bfc424c805ff9926403fbcc932017fc649900bde324c805fe1926402f70c932017d8649909fff614c84f7fb0a6427ff9853200dfcc29909ffd614c84f7eb0a6427ff1853200df8c29909fff514c84fbfa8a6427ff9453213ffaa29909f7d514c84ffe28a6427ffd053213ffc829909ffd414c84ffe20a6403ffcc53201ffc629900ffd314c807fe18a6402ffc8532017de429900bfe214c805fe90a6427fb48532017f84299003ff604c8017fb026400ff98132007fac099003fc604c8017e3026403ffcc13201fbe609900ffc304c805ff9026402ff0813213ffe209909ffe104c84ffe8826427ff0413203ffec9a801ffe64d400d7f326a007ff59350005fac9a801ffc64d400fffaa6a007dfd535003ffca9a801ffd54d4001beaa6a007ff1535003ffec7a801ffe63d40077f31ea007ff58f50005fac7a801ffc63d40077e31ea007ffd4f5003ffca7a809b7e53d400ffea9ea007ff14f5003ef8a7a8003ff43d404dff21ea000ff50f50137f887a801fff62d400fff316a002bf98b5003ffac5a8002fd62d400ffe316a002bf18b5003ffea5a801f7f52d400fff296a007ff54b50006faa5a801ffc52d4001ffa16a025ff90b50007fa85a8097fc42d404dff996a025ff8cb50007fa65a8097fc32d400fffb0ea007bfd875003ffcc3a8006fe61d400ffeb0ea024bf5875003ff8c3a8006fc61d400fffa8ea007dfd475003ffca3a801ffd51d4049bea8ea007ff14750127fe83a8093fe41d4049fea0ea024ff10750127fe63a8093fe31d4049fe98ea024ff0c750127fe43a8093ef21d4049ff10ea024ff48750127da43a8
  | 6 => 0xfff986a42fff0c352017fe41a900bfc20d485dff886a42eff84352177fa21a90bbfc10d48057fb2aa400ffd9152005fec8a9003fe6454801feb22a400ff19152035f8c8a901fff5454801ff2a2a400df95152007faa8a901ffc5454801be2a2a400ffd8d52005fec6a90b7fe63548077f31aa400ff58d5216ff8c6a900efc635480fffa9aa400dfd4d5216ffca6a9003fd5354801bea9aa407ff14d52007fe86a90b7fe4354801fea1aa42dff10d52015fec4a900bff525480ff7a92a402ff94952016fca4a900bfc5254805be292a402fb14952017fc84a900bfc4254805ff992a402ff8c952017f864a90b3ff61548597fb0aa42cff9855200dfcc2a90b3fd61548597eb0aa42cff1855200df8c2a901fff5154859bfa8aa42cff94552167faa2a90b37d515480ffe28aa42cffd0552167fc82a90b3fd4154859fe20aa42cffcc552167fc62a90b3fd3154859fe18aa402ffc8552017de42a900bfe2154805fe90aa42cfb48552017f842a9003ff60548017fb02a400ff98152007fac0a9003fc60548017e302a42dffcc15216ff860a900bff2054805fe102a42cffc4152167fc20a90b3fd1054859fe082a406ffd9742035fecba101bfe65d080f7f32e8406df99742004fccba101bfd65d08017eb2e8406df59742004facba101bfc65d080d7e32e8402bf99342037fea9a101bfe54d080dfeaa68406ff15342037fec7a101bfe63d08077f31e8406f798f4201dbcc7a101bfd63d08017eb1e8406f758f42005bac7a101bfc63d08077e31e8400ffd4f4215ffca7a1003fd53d0857fe29e8406ffd0f420377e87a101bfe43d080dfea1e8400ef50f42037f887a100afd62d0805ffa968402ff94b42017faa5a100bfc52d0805ff2168402ef90b42017dc85a100bfc42d0805de2168402ffccb42017fc65a100bfc32d080dffb0e8406bfd8742037fcc3a1006fe61d080dfeb0e842abf58742037f8c3a1006fc61d0855ffa8e842adfd4742157fca3a10abfd51d0855bea8e842aff14742037fe83a101bfe41d080dfea0e8406ff10742157fe63a10abfe31d0855fe98e842aff0c742017fe43a100bef21d0805ff10e8402ff48742157da43a100bfc21d080dffb068406ff98342005fcc1a101bfd60d08017eb068406ff1834215ffe61a10affc30d0805ff9068402ff08342157fe21a10abfe10d0855fe886842aff04342007fecaa1002ff6550801ff32a8407bf99542007facaa1002fd6550801fe32a8407bf19542015fec8a1003ff545080dff2a28400ff55142037f8a8a1003ff63508017fb1a8429ff98d4201dfcc6a1003fd6350853fe31a8403bf18d42007fea6a10a7fe5350801fea9a8429ff14d42037fe86a1003bf4350853ff21a8400ff50d420077a86a101bfc43508057fb128402ffd4942017fca4a100bfd5250805fe2928402ffd
  | 7 => 0xa18cffc52d0c0dff2168606ff10b4301ffe65a180ffe32d0c07fe1968606ffd8743035fec3a181bfe61d0c037f30e8606ff58743195fac3a181bfc61d0c037e30e8632ffd4743196fea3a18cbfe51d0c65fea8e8632df54743197f8a3a181bff41d0c0ddfa0e8606ff90743037fa83a18cbbd41d0c0dfe20e8603ffcc74301ffc63a180ffd31d0c07fe18e8632ffc8743197de43a18cbfe21d0c65fe90e8632fb48743197f843a181bff60d0c0dff3068600bf98343037fac1a1802fd60d0c0dfe3068603ffcc34301ff861a18cfff20d0c67fe1068632ffc4343197fc21a18cbfd10d0c65fe0868600ffd9543005fecaa18037f6550c013fb2a8600ff9954303dfccaa1803fd6550c017eb2a8600ff1954303df8caa18037c6550c013e32a8603bfd9143007fea8a181bfe5450c01df2a28600ff551430077aa8a181bfc5450c077fb1a8603ffd4d4301ffca6a180fde5350c07fea9a8600f754d4301ff8a6a180fff4350c0defa1a8603ff90d4301f7c86a180ffc4350c07de21a8603f710d43007fec4a1802ff6250c63ff3128602bf98943007fac4a18c7fc6250c057e3128631ff9494318ff8a4a18c7fe4250c0dfe2128603ffcc94301ffc64a18c7de3250c07fe1928603f70c943187fec2a18c2ff6150c61ff30a8601bf98543187fac2a18c2fd6150c61fe30a8601bf18543187fea2a18c37f5150c61ff28a8630ff54543186faa2a18c3fc5150c0dffa0a8630efd0543187fc82a18c3fd4150c61dea0a8606ff1054301ffe62a180fdf3150c07ff18a8603ff4c543187ba62a180ffc3150c61ff90a8630fbc8543187fc42a18c3fd2150c61f690a8630ff08543007fec0a1802ff6050c01ff3028600ff58143007f8c0a1802fc6050c07ff9828603f7cc14301ff860a18c7ff2050c63fe1028630ffc4143187fc20a18c3fd1050c61fe0828602bf9975203ffec9a901ffe64d480d7f326a407ff59352005fac9a901ffc64d480fffaa6a407ff95352006fca9a901ffd54d480ffe2a6a407df1535203ffec7a901ffe63d48077f31ea407ff58f52005fac7a901ffc63d48077e31ea407ffd4f5203efea7a901ffe53d480ffea9ea400df54f5203ff8a7a9003ff43d485fff21ea400ff50f5217ff887a900afd62d4805ff296a402df94b52017dca5a900bfc52d4805be296a402ff90b52017f885a900bff32d4805ff196a402ff0cb5203ffec3a901eff61d480fff30ea401bf9875203ffac3a90bafd61d480ffe30ea401bf1875203ffea3a901f7f51d480fff28ea407ff54752176faa3a901ffc51d485dffa0ea42eff90752177fa83a90bbfc41d485dff98ea42eff8c752177fa63a90bbfc31d4805ff90ea402fbc8752017fc43a900bfd21d485df690ea402ff0875203ffec1a901ffe60d48017f306a407ff58352005fac1a901ffc60d485
  | 8 => 0xf544541c6faa22a01ffc511500dffa08a806ff90454037fa822a01bfc4115071ff988a838ff8c4541c7fa622a0e3fc3115071ff908a838fbc84541c7fc422a0e3fd2115071f6908a838ff08454037fec02a01bfe60150017f300a806ff58054005fac02a01bfc6015075ff980a83aff0c0541cffe402a0e7fc2015071ff880a838ff840541c7fa202a0e3fc10150077f32ea607ffd935303ffcc9a981afe64d4c0ffeb26a600bf5935303ff8c9a981fff54d4c0fbfaa6a607ff9535303ffaa9a98037d54d4c0ffe2a6a603bf58f5301ffca7a980f7e53d4c07ef29ea603ff14f5301ef8a7a980ffe43d4c07fe21ea607ffd8b5303ffcc5a980afe62d4c0ffeb16a600bf58b5303ff8c5a980afc62d4c0fff296a607ff14b531bffc85a98dffc42d4c07ff996a603ff8cb5301ff865a981fff61d4c0f7fb0ea607ff9875300dfcc3a981ffd61d4c6d7eb0ea607ff1875300df8c3a981fff51d4c0fbfa8ea607ff9475303ffaa3a98db7d51d4c0ffe28ea636ffd07531b7fc83a98dbfd41d4c6dfe20ea603ffcc75301ffc63a980ffd31d4c07fe18ea636ffc87531b7de43a98dbfe21d4c6dfe90ea636fb487531b7f843a981fff60d4c0fff306a600bf9835303ffac1a9802fd60d4c0ffe306a603ffcc35301fbe61a980ffc30d4c6fff906a637ff083531b7fe21a98dbfe10d4c6dfe886a636ff0435301dfecaa9803ff6454c017fb22a600ff99153007fac8a9803fc6454c0d7e322a607ffd5153006fea8a9803fe5454c01feaa2a600df5515303ff8a8a980eff6354c07ffa9aa607f7d4d5301ffca6a980f7e5354c07fe29aa603df14d5301fb8a6a980ffe4354c07ef21aa603ff10d53007fec4a9802ff6254c6bff312a602bf98953007fac4a98d7fc6254c057e312a635ff9495303ff8a4a98d7fe4254c6bfe212a603ffcc95301ffc64a980ffc3254c69ffb0aa634bfd85531a7fcc2a9806fe6154c69feb0aa634bf585531a7f8c2a9806fc6154c0fffa8aa634dfd45531a7fca2a98d3fd5154c69bea8aa607ff145531a7fe82a98d3fe4154c69fea0aa634ff1055301ffe62a980ffe3154c07fe98aa603ff0c5531a7fe42a98d3ef2154c69ff10aa634ff485531a7da42a98d3fc2154c01ffb02a600bfd8153007fcc0a9803fd6054c01fe302a600bf1815301ffe60a980ffc3054c6bff902a635ff081531a7fe20a98d3fe1054c69fe882a634ff04153037fecba181aff65d0c0dff32e8607bf99743037facba1802fd65d0c0dfe32e8606bf1974301dfcc9a181bff54d0c0dff2a68606ef95343037faa9a1803bd54d0c0dfe2a68603bf58f4301ffea7a180ffe53d0c07fea9e8603ff14f4301ffc87a180fbe43d0c07ef21e8603ff10f4301f7887a181bff62d0c0dff3168602bf98b43037fac5a1802fd62d0c0dfe3168602bf18b4319ffca5
  | 9 => 0x83fe98ea841ff0c75420ffe43aa107ef21d5083ff10ea841ff4875420fda43aa107fc21d500fffb06a807ff98354005fcc1aa01ffd60d50017eb06a807ff1835421ffe61aa10ffc30d5085ff906a842ff0835420ffe21aa107fe10d5083fe886a841ff043541ddfacb2a01afe649500dffaa4a806dfd525403f7ea92a0033f549500dffb1ca806ff98e5401dfcc72a01bfd63950017eb1ca806ff18e5401df8c72a103fe5395081bf29ca807ff14e54206f8a72a01bfe439500dfe21ca806ffd8a54037fcc52a00afe629500dfeb14a800bf58a54037f8c52a00afc629507fff294a807ff14a54037fc852a01bfc4295081ff994a83fff8ca541fff8652a01bff619500d7fb0ca806ff9865400dfcc32a01bfd619507d7eb0ca806ff1865400df8c32a01fff519507dbfa8ca83eff946541f7faa32a0fb7d519500ffe28ca806ffd0654037fc832a01bfd419500dfe20ca83effcc6541f7fc632a0fbfd319507dfe18ca83effc86541f7de432a0fbfe219507dfe90ca83efb486541f7f8432a01bff609500dff304a800bf98254037fac12a002fd609500dfe304a840ffcc254207f8612a0ffff209507ffe104a83effc42541f7fc212a0fbfd109507dfe084a807ffd515403f7ea8aa01bfe545500dbf2a2a800ffd8d54005fec6aa0f7fe63550077f31aa800ff58d541eff8c6aa00efc635507bff29aa807ff14d541effc86aa01bfc4355001ffb12a800bfd89541e7fcc4aa00afe6255001feb12a83cff18954015f8c4aa0f3fe5255079bf292a807ff149541e6f8a4aa0f3fe425500dfe212a83dffcc9541e7fc64aa0f3fc3255077ffb0aa83bbfd85541dffcc2aa006fe6155077feb0aa83bbf585541dff8c2aa006fc615500fffa8aa83bdfd45541dffca2aa0effd5155077bea8aa807ff14554037fe82aa0effe4155077fea0aa806ff105541dffe62aa0effe3155077fe98aa83bff0c5541dffe42aa0efef2155077ff10aa83bff485541dfda42aa0effc2155001ffb02a800bfd8154007fcc0aa003fd6055001fe302a800bf181541effe60aa0f7fc3055079ff902a83cff081541dffe20aa0effe1055077fe882a83bff0415403dfcca2a01afe641500dffaa0a806dfd5054037fca82a01bbe541500dfeaa0a806df5505403f7aa82a01bff631500dff318a803bf98c54037bcc62a00ede631500dfeb18a800bf58c54037bac62a002dd631500dfe318a803bf18c5403ffca62a0eb7e531500ffe298a807df14c54037fc862a01bfc431500dffb10a806ff98854015fcc42a01bfd62150017eb10a806ff18854015f8c42a01ffe521500ffe290a806ff90854037f8842a0ebff3215073ff190a839ff0c854037fec22a01aff611500dff308a801bf98454037fac22a0e2fd611500dfe308a801bf1845403ffea22a01f7f511500fff288a807f
  | 10 => 0x1a00000200200c00601202400a02000800400000001a00600400e03a00400a00403600402402c00201002000000000003400000000000e03803800e04c00000000400000a00000601800a00200400401400800000800402000600000c00000e01600200c01e00004a00a00400000802e00602200002800200000000400002200e06800000200000a01400600000000400203000600200000001200800400000000000400a01a01a01600800001801200000607a00000000400000001800000603600000600a0000020260b800000000001601800400a01200a02201000403206e01a00001400200400205e0140000000060060a400001c00402400400800800a00000000000a00200600000000000000400000a00201c03a00400e00000200400002200000400000600000001200402a00400200000e00000000000401800803a00200801000002800c00a00401c00400401400202e00000200400203000200200000000200801200a01001200001800404401600800600002801600201200000001600200000400400002400000400601200801403400e00a01200c00200400000400e00400001c00601000000200000001600001c00000000000000400600000000000200400000401403601000600e00000600400601400800600800c00000e0040a402e00800401800600601e0120040060d401403a05800400800400000c00000602800001600000c02202e02200001000400200600402000600000202600200000000001802600200000205a02800204200400001200400000600001e00002e00000200000002402e00400600000000200000202000400000000a00200200c00202402600000800400200600200800e00200c00000400000400c00000a04000e02c05601a00c00000800602a00000200000001c00200000200000c00000000600e00a00a00404c00800000e00201800000600c00000000c02e00c00600002001600209000002200000004e00000201800402600802000200203a00000600400006800401200002200e02400600402e00400400e00400200a00601000400000604802800600000400600800000800000606a00800a00001001a01000800400c00200000607ffd8f5403ffcc7aa00efe63d500ffeb1ea800bf58f5403ff8c7aa00efc63d500fff29ea807ff14f5421ffc87aa01bfc43d500fffb16a807ff98b54015fcc5aa01ffd62d50017eb16a807ff18b54015f8c5aa01ffe52d5085bf296a807ff14b5403ef8a5aa10bfe42d500dfe216a843ffccb54217fc65aa10bfc32d500fffb0ea807bfd875403ffcc3aa006fe61d500ffeb0ea841bf5875403ff8c3aa006fc61d500fffa8ea807dfd475403ffca3aa01ffd51d5083bea8ea807ff14754037fe83aa107fe41d5083fea0ea806ff1075420ffe63aa107fe31d5
  | 11 => 0x442124d04944e064f128848c4ee2e72440934d2a5323a79c0c85458d00200c4b7045e11b1b2064626a3ad9a78b8800000021bc00023008806dc4761de20e8f8cfde00019e12b48ce47d31f07ad12a1032bb9f60ed250335618e80001ef1108cd0000000368962423a8520000fa43363870fb8498e424c80000000f187e22b1a0e102c56c07180485961b007e8fc42421d00e49f9cd2c61a000113453450d1e681ad17000027a9f248f41f924f07c80004d400000006504e0060044c0001e13f19e6872415316b9dbc6ec3f900000008dc68d00000011202b63888000b9c62800017e8c907890a601245245d4013027000043d2bc8d940007ff06a800000063331c07e86901d100021f116a000000201067e0dc06697c03544db27080000000000028dc400066b1e09ec0ec02fb2e305800002e34130aa01068c935d13000001870000f5516c7070000e8495c0000b703b09ba4d71b700000001ba01a8d88c2e2801de000c0003690001ee85f849b0000ed499800000015540008c54570000000000000000000000044480000000004128c9cc9200012180000003c2000159806c1e43861ba91361432db198005e0ab18513c0f440bf18722610d4092000129816c7dd2fc0d14d5400028b1b2c11c78f04b83385f08ac1ca8bb4b0c5132219848a5e2f30001b9d19e00034914b400000000021510ba17000000007fe40200000009620004271940b000002821440eb421315987942f87de4419ca801074313c80010ce00000010600282093bf80006ba00000000007c86011f900f44783fc38a19880000000e010d90ec88c3a6a248d6282b2c5067507652a3420000b3c5b12421af4f0878b08f0b44b740e91c4085053614e3e001e90f072810515611a414622e1cd07920f70e1816842c7021a09ec81e638121b84188a61dd2cc889c0007c33be11ec7a8447223146837a78108788d4ccc7953de926101658c0281c6000200000000400e01400001001600004c00401004e01400000200000e00001400000600001201c02001000000002000600c00e00000800200a00000800600606401400e0000080040060020040060080040000000060000a800a00400800001801e01600000000800201000000203a00402601200200001000200800000800400400000400400001000000000400200a00801801400200200200e00800200600e00400a00000000000002e00800c00e00602400604800000200000200000000a00207200400400000200803600a00600800400600205a00800602c00800000000201601801000a00a03a00000002600001400c00200000000a00000601202c01400600600000000a00000604200200600001403a00c02a00000200001200200400200a00000000000000000c01800200003c01e01401a00000601000c010000004000
  | 12 => 0xc70000cec14937f13a030246410890c88be0000279ac8ea83b8363987c8485382411a151a005c04f20e8cc661c40e0230daa20e2df0bacc0669913f9c28cc200023699b505c17f45f15888460b911c8000540534286006042442928aa05cc3281334d84605760000002334dde0a2306a1a469a8ca34316d40002643339d1c7f0401181800059c5761308e28dcc4204579bf000000000005480008960000988aa673f06e81d4bfe1ad11b8d285ba8cb02121b80000562bf80000003da21e0d8cbce11f01189a00006533cc1b0c902777016009c5de5fe2a692386720610000d1c0001b93e11ce80001f10340000e8867b08c85e867c6a61bf8688af05bc45c8e089d21150ae83acaa418d11221984e47b906203d910c74b255867c0001e32dd886458a2c131187082cc5a81fb0584c9a0000001cac0f20bc2a6000071c11a18b000000083f27e8000ce07464182280ebe72e09a158055a3a911f8db485a2ca0368f4c5740003218fb0be82d800022200003d92f70e1436600f30d83941be000164195860e3cc43f85b44ba7683fc1370f0e35100020d40007121611c18cbc00009a9ab80006b72ef800116e4b02988a710d87ea2f416b89b22bd1270bd86f685324894a4da82571a4943c45a19925c8c7cfb641c4630e5000e0950f40000bde00037c00000003c52e800010640001580fecc165912f50f988ca41638e035034a0000000000cb08c705a8bd04dc5201dc95b80002750001eacfd60000000c78000000243824c00027c00000006be7dc12480005024ac00000000008700d8800113800000000007d000019d80009b41e9000000000059d0001af08a411219ba0740001e00001400cea00000016dcb7a51f0000a3447c0000e91964fb24450771ef037822a0000fbcaae32f04087311525371709ea0dca2423f3043498a00045300003b6053405000000006f30301a49426372220b68fac5c12a50210000000000000000057e000000112e00000000b43a6000292228c000000238000000000014f818c39a4422fca34c000657000000000067c0000001132000000000000000000000000001a83321a90d401a126b03601624b309b0cc8c2031a00000002ce0003fd989000042700d09aca46827054081ce4a1323d71e38ed85a53911c5426e67a2350ba8eae53d28096a89a21f01859dd4e6a506000022c326000322131c1a0310097220027e698389819425a5263769c7c9ce5832671fb90be42e0aa1a88a8262215a04cd15a3523fc8000a5c0001620000a7c000000000098c6b00000000fc225501c09d00004f414b1414b603cf29b04bc44c75d0529064e1679c1498c18f4266e2a00df0cb67192520000e524282e505c873c2ac4529088a4a51c0269e0c5103c606310205043501480e9c71e60817f952ca7242f0cb07d83d4088424171c2
  | 13 => 0x2d5903c6000001999b28c6c0d1114a08c00068c27b8680a16000248207c0003114238de0fd800030c0f8910e27e2b2817801c0000000000000632275849c8720000000fdc91859634501d000000000000011a80000c90d9c00019500000008d20002da118054e78d40d02cc6388bf00010e01fe00000000000001cb435a34400000000000000000000000000f965283ba1fb468c65d00000000000c70538c24bb679f0001e140007013410c5c4887e40000d8427c60a0699df50304151e383a8f705083bc18b0f4e39c3f982b80001b805a00000006ee0150000b4444c2f9096064831d0000000d5607e00021640000960000a140004e317b8ebc7c2000000000063200000000000000b044f81309840000000000ca20001e2059076e0aa2cc20186ac3a63efa2a01903362430000d84758014194800030d1298ea80000003ff1e8c21684100000000000000ed00010e4000000099431423300000000007d53b2800000000000000008b04751178e2433400000001d895e0000180b78b4e851375800002c24b35085880007e00eb1f48b1e79410f180800008732084e076422c2b78a8c0046ff38d840022c1e642b1b411862252af9a38e2e21f1731994f526db0001c900005882f08000dac0000eb800000015010596848e451731a15aca781391679a690207a50b5981099e5d724a9a8c5781012ba00000005ad08b80011221420f3883c85867d000100cc7600015900000900003d99f4cea637900003885fa69c0000ca851800032113fcc4a0003440d9000058110620b40c01ae2f480fc52a2c63829cbcfe082922a80807b07b419088e04d263d0002320d2e00030008408cc0003c886189928c02e011f00006e200000000000b700017980003730650fb8b9252709222883886f107c033cf6e65f1bd05dcfca1f51431f10624000386a2f045c3530ad20340000003bf00000007f101a000000003a20980006ea60c00000000000000000000cd400024e80000000003148cc01203e51b400000005460000750f2e64c2548000000246164925c0002f0000103000008d0fd800005c4d030b0ce81ae2ec39d85d0f5a76b0d39c007080a603d80744f621c2bda25061078626f9ce0e3c0003a50b881143380ea8b7c8162e943a800065862e0d796a41044bb1d8042000000044d01483b084241207f00005b200000005087d409e127c6885223e70f490b819c0aba1810ca00026517b400004400000000002af00015710120001041928000000000000073a0000000000f100000000000000000000000000028f00011e4d6a23225181e062813d06d12a88fe0570199514db8710155191442a0bb1b7978800007c3e796b06b40e404a0c9836420d05f106c4946ec22d970cb5e0593598bd479052124b15d42d20000000eec99a67121980001e85dd0
  | 14 => 0x287168037c047000000000000034f9ef8cee5a400000003060000c48e580003dc0000000d9c00000000000000000ee01047f414d42805940fe84f0000000c7e2fe0001880dbe80c2fa800093875c2b481b0000000000088c000185000043900a23d426800000000000013780008683070c544824ed3eb8000fe800b42f0000cb800045896542f2240000000000034e0000000dbc00042d8b549aa00035f0000a922a13b50144d124b500000000003770000000ef601c1ae1824ab20ed42605050f214742c1eec3760001c8a10c000000000000042e00027d2278882000000000000000000000011080001b91d30c220002ce05a00006300d60000a0e4c4000000000000000000000008770ab134806472d3fd06008b4544000092000000000000008ba3350001de40004350000000d22276259115cd72000317893c15e0003a40c60da48080000eb400017e23984b0f3259704da2ecac222b0b790d08a230f1af1d001586c50660818a741fd04304107ea71a3fb8b950c42fa3391ad8a863d740a823caa805b00000000002730000bb800081200000010788030000a7800075e0000000a660001c80eaca9000020f8000000000000000020a0000000314d682b74078000a2885a36c94743fc51816910249f655e00010fc4de0802e90e2c8fc27a20000006402e001282f40000e82539cdc5161ff10d80888084e631a95c80006fb0db1794c0a88f00012507ce0002959650078000230800000019e0001cc82fa0101c987cc03e3b436b880000015f3d30000ae05bf1ad991800000000b80010940670000000f827711361fd4fd06870ae05d42561140ac91b0dea1e246203c41ea2050370b648b283e07c99a45523de3ed206454a0ad35d83f829436638b07040ee1ca1d88ae438a3d100005b079663c33a1f282a25f34039f151548cc0002084bb879e084800000046f3821e2800000000015080007e91e018540008111d1a2c8e1200d05486606181290c88044aac61e2be8000000000000000089e6e101492000aa089000097c00000027280005d037432a1038de00004228df491a0000521fc80004b826c224cedc3054179bc800002127b00000008011b589301bc34316a0f805484ea0a59304af43bd2091ed497834c0c6058cb202783a49c98b3e00012d0000d9a8ba00000000007a411d20d06b00000000980000000315000000022004f800081a07304c8000d70037431800082207243d95a000000032d17804b8000000056c0002dc3740e800000000000000ec67b6000112800000000000000002c726580004a000a3039760f400c21c01c3c67a2c00000a5c0006804309a3cff851e32021b400000000020c4f201710000ca41824100000000fec0002c11b8110a21810e8000814000192800000049339b07b80000002f6172ccd81450001188
  | 15 => 0x400043e39f0f384b236c32700009e25a61a020f50280a01df82e800009a0c597c4a24731123987400028a0000000c4c44821818847e6881000173511c20325d184d1825d302312dc5ac0001ff000071801b1438f58a0400012a0f400008741d708049506f945e934c1867620000e186d404307089f413a2b5000009025485739009981f64b42c92100dd24141a5a1c438e2041f50d50eda34f22586100c40003e380007860b82c29248000000410000000000000000000005b31cc88091420981f80554de800036d0c04e720002fe05ecdf400000003c80002bf0af0e5c02a6550df8000d5a58b17c80000005933b31efcd260000001d408ec7fd36e8000dee1a300c8a440004f21ed8e0c00057315700003b284922b192c00008524500002145eb2cd97dc73e4be2a79e482184712c720cc0004e40a792d80001480000b90000182354836400042600007b03280002c387389f82f20d4a0b000088d38e91dc4680012e28df8c567af00000000006bf12f0000000000000000101c05d1f58aac84a0003408030000828000000000054e000046c0000002a88ed8ab400000000000000000f69768d921cf051800000088a00011382803592eb0c10bbc0002dc80000005e302000ecd885f628da2d000028e4111e00000564000000019277608e207800021a00f000000089d0001d48ee667f00000000004073ac957494a7702a800e42f04f329f8348348499000000000013a1512000c1e0003b2189c0002454399ea80005c22478000a3246b000000086200000000002b074235380000e200043d0000000000334015000000034185cc0004050351d387508c209d99e0f0474100004c000087d004a1100000004410e94000000453800059a0004320018c280fc00007200000004580ef86aa8ab1680e60f9007d03213e08d01314671a2c7444fe00000010fc26724492804444ee15f00000000001cd10ec00012800000003f005834e94280005fd3168000ef40001f69e7428800023a1abc0000fa1971100da63420e30cacf8c755425918c87444936785a816428913898c412253b39e15f06364bf178920cea248b1d99c9ce7a56d0000c88e460003b91cccd806cc2848198ad46f339622cc0007080c7961000042b15c04801960e600014c10548552cd0b4c90a3dd0da1444ab600044583587be3ac2b38b30d288361fe906834c31337b11e06c04e23e81f30d4a0000001eb00940701e51cc10724bd1588fd05b64ec0001b04ece000000000103639b3b080000006e402f813853a35729a8a509de8371d202841b629801f1150a5828322800000005e412b0c084b600020b84880005fb0c4098cf261f41b8128865a0003e68114dfa6d81369078ae25c808893e40962282e8991cb982523e88cc40263ba40117643be2a601588c41e01762618000baa197
  | 16 => 0xa641c05473cd83bcd207450d59b1871a6a83378b0cb9e70e0c81ec436a0e73719d5820e79633f1018ce68a42d198e400000042319e
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xf6350d2001edc6350d20036ec7650920034ec76509200076f65509200076c6550920015ef7450920017af7450920007af6450920036ee6450920036ec6450920007ac6450920007af4350920007ad435092025def715092025ded7150920256ef6150920256ed61509202576f51509202576d5150920007eb7050920045ec7050920007e87050920016ef6050920017eb6050920014fe76d4120014fc76d41200067f65d412003e7c65d4120015ee72d4120005ed72d41200e4fe76941201167f659412003e7c659412002dde7394120005dd739412003cff7654120014fe7654120104fd7654120014fc76541200067f655412003e7c6554120005ef7254120015ec7254120114fe76141200067f651412003e7c6514120014fe76d0120014fc76d01200067f65d01200067c65d0120006bf64d0120036bc64d0120015ee72d0120005ed72d0120007ad42d0120084fe76901200067f65901200067c6590120045ec7290120034ff7650120014fe76501200a4fd7650120014fc76501200057f75501200057c75501200067f65501200067c6550120006bf6450120036bc6450120005ef7250120015ec7250120007ad42501200b4fe76101200057e75101200057d75101200067f65101200067c651012002dde7310120005dd7310120015ee7210120005ed7210120025f67110120005f5711012024cfe768c1200057e758c1200057d758c1200067f658c1200067c658c12024dfa768c120246fa768c1200077a758c12000779758c1200077b658c12000778658c120065f9738c12001efa638c12001ef8638c120015fa728c120015f8728c120046fb628c120077ea428c120007e9428c12023efb618c12023ef9618c12023f7b518c12023f79518c120077eb218c12023fe9218c12001cff764c120014fe764c120064fd764c120014fc764c1200067f654c1200067c654c120006df634c12001edc634c120005ef724c120015ec724c12002fd8304c120015f8764c12001ef8764c120014f8764c1200077b654c12000778654c120075fb734c120007db734c120007db634c12001efa634c12001ef8634c12002fd8634c120007db534c12002fd8534c12002fda434c120007d9434c120007eb724c120015fa724c120015f8724c120067e8724c120066fb624c120067ea424c120007e9424c120067db324c120067d9324c120236fb614c120236f9614c1202377b514c12023779514c12002fdb314c120237d9314c120067eb214c120237e9214c120015ee7688120046ee768812000cee76881200076f65881200076c6588120045ef7488120005ed7488120045ef718812022ded7188120226ef6188120226ed61881202276f51881202276d5188120045ee7088120047ea7088120046ef6088120017eb6088120047ea3088120007e93088120
  | 1 => 0x91200067f51d91200067d51d9120006be41d9120006bc41d91200b6ef21d9120006ed21d9120044fe70d9120044fc70d91200057e75991200057d75991200067f65991200067c6599120006bf649912002dde7399120005dd73991200a5f970991200057f75591200057c75591200067f65591200067c65591200cdfb7059120004ff75591200067f75591200047f755912003cfc75591200067c755912003c7c7559120006bf7459120004ff735912001cfe735912001cfc73591200a4ff7259120006ef7259120004ff715912000cfe7159120004fd715912000cfc71591200067f51591200067d51591200a6ef2159120006ed21591200ccff7059120006fb70591200b4fe76191200067f65191200067c6519120036be6419120006bd641912003cff76d5120004fe76d5120004fd76d512003cfc76d51200067f65d512003e7c65d5120034ff7695120004fe7695120004fd7695120034fc76951200067f659512003e7c65951200073f5495120015ee7295120005ed7295120004ff7655120004fe7655120004fd7655120004fc76551200067f655512003e7c6555120034ff7615120004fe7615120004fd7615120034fc76151200067f651512003e7c651512002dde7315120005dd7315120015ee7215120005ed7215120005fa7015120005f9701512001cfe76d8d200067f65d8d200067c65d8d2002ede63d8d2003cfe75d8d20004fd75d8d20034fe74d8d20004fd74d8d2002ede43d8d20044ff72d8d20014fe72d8d20074fd72d8d20014fc72d8d20076df32d8d20076dd32d8d20004ff71d8d2000cfe71d8d20004fd71d8d2000cfc71d8d200067f51d8d200067d51d8d20006de31d8d2002edc31d8d20076ef21d8d20006ed21d8d20044fe70d8d20014fd70d8d20044fc70d8d2002edf30d8d200057f7558d200057c7558d200067f6558d200067c6558d2002edc6358d20265fb7058d20004ff7558d200067f7558d200047f7558d2003cfc7558d200067c7558d2003c7c7558d20004ff7458d20034fc7458d20074ff7358d20006df7358d20064ff7258d20006ef7258d20004ff7158d2000cfe7158d20004fd7158d2000cfc7158d200067f5158d200067d5158d20066ef2158d20006ed2158d20264ff7058d20006fb7058d2003cff76d4d20004fe76d4d20004fd76d4d2003cfc76d4d200067f65d4d2003e7c65d4d20004ff7654d20004fe7654d20004fd7654d20004fc7654d200067f6554d2003e7c6554d20034ff76d0d20004fe76d0d20004fd76d0d20034fc76d0d200067f65d0d200067c65d0d20006bf64d0d20036bc64d0d20015ee72d0d20005ed72d0d20004ff7650d20004fe7650d20004fd7650d20004fc7650d200057f7550d200057c7550d200067f6550d200067c6550d20006bf6450d20036bc6450d20006d
  | 2 => 0x1176f21d95200076d21d95201177b20d95201176c20d95201177820d95200067f74d95200067e74d95200067d74d95200067c74d95200067f73d95200067e73d95200067d73d95200067c73d95200067e43d95200067c43d95201167f72d95201167e72d95201167d72d95201167c72d95201167f42d95201167e42d95201167d42d95201167c42d95201167f32d95201167e32d95201167d32d95201167c32d95200067f71d95200047f71d95200067e71d95200067d71d95200047d71d95200067c71d95200067f41d95200067e41d95200067d41d95200067c41d95200067f31d95200067e31d95200067d31d95200067c31d95201167f21d95201166f21d95201167e21d95201167d21d95200066d21d95201167c21d95201167f70d95201167d70d95200067f30d95200067c30d95201167f20d95201167e20d95201167c20d95200067f10d95200067e10d95200067d10d95200067c10d95200067f6599520105f9709952012dfb70595200067f7559520004ff7459520034fc7459520004ff735952001cfe735952001cfc7359520104ff7259520006ef7259520004ff715952000cfe7159520004fd715952000cfc71595200067f51595200067d5159520106ef2159520006ed215952012cff7059520006fb7059520114fe761952003e7e65195200067d65195201157e76195200067e76195201147e76195200067e63195200067c63195200e76e42195200057f71195200057d71195200067f61195200067e61195200067d61195200067c61195200e76f21195200076d21195200e77b20195200e76c20195200e778201952003e7f741952003e7e741952003e7d741952003e7c741952003e7f731952003e7e731952003e7d731952003e7c73195200067e43195200067c431952003e7f721952003e7e721952003e7d721952003e7c72195200e67f42195200e67e42195200e67d42195200e67c42195200e67f32195200e67e32195200e67d32195200e67c321952003e7f711952003c7f711952003e7e711952003e7d71195200047d711952003e7c71195200067f41195200067e41195200067d41195200067c41195200067f31195200067e31195200067d31195200067c31195200e67f21195200e66f21195200e67e21195200e67d21195200066d21195200e67c211952003e7f701952003e7d70195200067f30195200067c30195200e67f20195200e67e20195200e67d20195200e67c20195200067f10195200067e10195200067d10195200067c1019520034fe76d91200067f65d91200067c65d912003cfe75d9120004fd75d912001cfe73d9120004fd73d912001cfc73d9120044ff72d9120014fe72d91200b4fd72d9120014fc72d91200b6bf42d91200b6bd42d9120004ff71d912000cfe71d9120004fd71d912000cfc71d
  | 3 => 0xd74d8e20064fd73d8e20046ed72d8e20044ff71d8e2000cfe71d8e20004fd71d8e20044fc71d8e200067f51d8e200067d51d8e20076ef21d8e20006ed21d8e20044fe70d8e20046fa70d8e20046df30d8e2001cff7658e20046dc6358e20004ff7558e2003cfc7558e20004ff7458e20034fc7458e20046df7358e20056dc5358e20056de4358e20066df3258e20066dd3258e20004ff7158e2000cfe7158e20004fd7158e2000cfc7158e200067f5158e200067d5158e20056df3158e20006dd3158e20066ef2158e20006ed2158e2001cff7058e20044fe7058e2001cfd7058e20044fc7058e20046de3058e20046dc3058e2003cff76d4e20044fe76d4e20004fd76d4e20044fc76d4e200067f65d4e2003e7c65d4e2001ede63d4e20006dd63d4e20004ff7654e20044fe7654e20004fd7654e20044fc7654e200067f6554e2003e7c6554e20005ef7254e20015ec7254e20034ff76d0e20044fe76d0e20004fd76d0e20044fc76d0e20006bf64d0e20036bc64d0e20004ff7650e20044fe7650e20004fd7650e20044fc7650e200057f7550e200057c7550e20006bf6450e20036bc6450e2001ede6350e20006dd6350e20005ef7250e20015ec7250e20104fd76d42200467f65d42200467c65d422012cff76542200467f65542200467c65542200a4fd76d0220046bf64d0220046bc64d02200ccff76502200057f75502200057c7550220046bf6450220046bc6450220045f9768c220046f9768c220014f9768c2200477a758c22004779758c22001efa638c220047da638c220047d9638c220046f8638c220015fa728c220047ea728c220047e9728c220045f8728c220046fb618c22027ef9618c22027f7b518c22027f79518c220077eb218c22027fe9218c220264ff764c220046df634c220046dc634c220047d8304c220265fb764c220276fb764c220047db734c220047db634c22001efa634c22001ef8634c220047d8634c220007db534c220057d8534c220057da434c220007d9434c220015fa724c220015f8724c220067db324c220067d9324c22026efb614c22026ef9614c22026f7b514c22026f79514c220057db314c22026fd9314c220067eb214c22026fe9214c22003cfe76d9520034fe74d9520004fd74d952001cfe73d9520004fd73d952001cfc73d95200067e53d95200067c53d9520044ff72d9520014fe72d9520114fd72d9520014fc72d95201167f52d95201167d52d9520004ff71d952000cfe71d9520004fd71d952000cfc71d95200067f51d95200067e51d95200067d51d95200067c51d9520116ef21d9520006ed21d9520044fe70d9520044fc70d952003c7e76d95200067e63d95200067c63d95201176e42d95200057f71d95200057d71d95200067f61d95200067e61d95200067d61d95200067c61d9520
  | 4 => 0x130036be6410130006bd641013001dde7310130005dd73101300079d4310130065ee7210130005ed721013005df67110130005f57110130047d83010130295de758c1300475e758c1300055e758c1300475d758c130045dc758c130045df748c130005dd748c130005dd728c130045df718c13028ddd718c1302875f518c1302875d518c130287cf218c130287cd218c130045de708c130047da708c130046df608c13001fdb608c130047da108c130287d9108c130034fe74d9620004fd74d962001cfe73d9620046de73d962001cde73d9620004fd73d9620046dd73d9620004dd73d9620044fc73d9620046ed72d96201167e52d96201167c52d9620044ff71d962000cfe71d9620004fd71d9620044fc71d96200067f51d96200067d51d9620116ef21d9620006ed21d9620044fe70d9620046fa70d9620104fd76996200467f65996200467c659962003cff76596200467c65596200467f7559620004ff7459620034fc7459620004ff735962001cfe735962001cfc73596200067e53596200067c53596201067f52596201067d5259620004ff715962000cfe7159620004fd715962000cfc71596200067f51596200067d5159620106ef2159620006ed215962003cff7059620044fe705962003cfd7059620044fc70596200467e50596200467c505962003cfe75d9220004fd75d922001cfe73d9220004fd73d9220044fc73d9220046ed72d9220044ff71d922000cfe71d9220004fd71d9220044fc71d92200067f51d92200067d51d92200b6ef21d9220006ed21d9220044fe70d9220046fa70d9220046ef20d92200a4fd7699220046bf6499220046bc6499220034ff76592200057f75592200057c7559220046bc6459220004ff75592200067f75592200047f755922003cfc75592200067c755922003c7c7559220046bf7459220004ff735922001cfe735922001cfc73592200a6bf42592200a6bd4259220004ff715922000cfe7159220004fd715922000cfc71592200067f51592200067d5159220006bf4159220006bd41592200a6ef2159220006ed2159220034ff7059220044fe7059220034fd7059220044fc7059220046be4059220046bc40592200a6ef205922003cff76d5220044fe76d5220004fd76d5220044fc76d522003e7e65d52200067d65d5220034ff7695220044fe7695220004fd7695220044fc76952200067f659522003e7c65952200073f5495220004ff7655220044fe7655220004fd7655220044fc765522003e7e65552200067d6555220034ff7615220044fe7615220004fd7615220044fc76152200067f651522003e7c6515220055de7315220005dd7315220045fa7015220005f9701522003cfe75d8e200467e75d8e2003c7e75d8e20004fd75d8e200467d75d8e200047d75d8e20034fe74d8e20004f
  | 5 => 0x36de6450d30036dc6450d300079c6450d300079e5450d300079d5450d30005df7250d3018ede6250d3018edc6250d302b5df7150d302b5dd7150d302aedf6150d302aedd6150d302af5f5150d302af5d5150d302af9f4150d302af9d4150d302afcf2150d302afcd2150d30007db7050d30045dc7050d30007d87050d30005d87050d3001edf6050d3001fdb6050d302afda1050d302afd91050d30014fe76d8930066ee62d893003cfe75d8930004fd75d8930034fe74d8930004fd74d8930014fc73d8930066ec52d8930066ec42d8930066ee32d8930056ed32d8930004ff71d893000cfe71d8930004fd71d893000cfc71d89300067f51d89300067d51d8930066ef21d8930006ed21d8930044fe70d893001cfd70d8930066ef20d89300057f75589300057c7558930066ec6258930245fb7058930004fe76d4930004fd76d493003cfc76d493003e7e65d49300067d65d493001ddc73d49302975f53d4930006ef62d4930016ec62d4930004ff7654930004fe7654930004fc765493003e7e65549300067d6554930005df735493001ddc73549300075f5354930004fe76d0930004fd76d0930034fc76d09300057e75d09300057d75d0930036be64d0930006bd64d093001dde73d0930005dd73d09300079d43d0930006ef62d0930016ec62d0930004ff7650930004fe7650930004fc7650930036be6450930006bd645093001dde73509300079d4350930065dc764c930016dc764c930014dc764c9300075f754c930295de754c930295dc754c9300075c754c9300055c754c930005df744c930005dd744c93001ddf724c93001fcf724c930007cf624c930016de624c930016dc624c930067cc624c9302a5df714c9302a5dd714c93029f5f514c93029f5d514c930067cf214c93029fcd214c930007db704c930045dc704c930007d8704c93001edf604c93001fdb604c93029fda104c93029fd9104c93001cfe76d413001cfc76d41300067f65d413003e7c65d413001dde73d4130005dd73d41301375c53d41300ecfe769413003e7e65941300067d659413001dde7394130005dd73941300075f5394130047d8309413003cff765413001cfe765413010cfd765413001cfc76541300067f655413003e7c6554130005df735413001ddc735413010f5c535413010fd8305413011cfe761413003e7e65141300067d6514130045dc73141302975f531413001cfe76d013001cfc76d0130006bf64d0130036bc64d013001dde73d0130005dd73d01300d7d830d013008cfe7690130036be6490130006bd6490130045dc73901300079d4390130034ff765013001cfe76501300acfd765013001cfc76501300057f75501300057c7550130006bf6450130036bc6450130005df735013001ddc73501300bcfe76101300057e75101300057d751
  | 6 => 0xc535953010edc535953010ede4359530004ff7259530006ef7259530004ef7259530014fe7259530014fc7259530006ec7259530014ec7259530004ff715953000cfe7159530004fd715953000cfc71595300067f51595300067d5159530006ef2159530006ed2159530134ff7059530006fb705953011cfe761953003e7e65195300067d6519530034fe76d913003cfe75d9130004fd75d9130044ff73d913001cfe73d91300bcfd73d913001cfc73d91300bebf43d91300bebd43d9130014fe72d9130004fd72d9130014fc72d9130004ff71d913000cfe71d9130004fd71d913000cfc71d91300067f51d91300067d51d91300bedf31d9130006dd31d9130006ef21d9130006ed21d9130006fa10d9130006f910d9130006bf64991300adf970991300057f75591300057c7559130005ef7259130065ec7259130005f7715913005df471591300d5fb7059130004ff75591300067f75591300047f755913003cfc75591300067c755913003c7c7559130006bf74591300acff7359130006df7359130004ff7259130006ef7259130004ef7259130014fe7259130014fc7259130006ec7259130014ec7259130004ff7159130006f77159130004f7715913000cfe7159130004fd715913000cfc7159130006f4715913000cf471591300067f51591300067d5159130006bf4159130006bd41591300aedf3159130006dd3159130006ef2159130006ed21591300d4ff7059130006fb7059130006fa1059130006f910591300bcfe76191300057e75191300057d7519130036be6419130006bd641913003cff76d5130004fe76d5130004fd76d513003cfc76d513003e7e65d51300067d65d513001ddc73d5130034ff7695130004fe7695130004fd7695130034fc76951300067f659513003e7c65951300073f549513001dde7395130005dd73951302075c5395130004ff7655130004fe7655130004fd7655130004fc765513003e7e65551300067d6555130005df735513001ddc7355130005fb7055130005f87055130034ff7615130004fe7615130004fd7615130034fc76151300067f651513003e7c651513001dde7315130005dd73151301d75c5315130296de76d4d30004de76d4d3001dde75d4d3001f5e75d4d30296df65d4d300075f65d4d30296dd65d4d302975c65d4d30005dd74d4d302975f54d4d300075d54d4d30005dd72d4d30295df71d4d302c5dd71d4d302975f51d4d302bf5d51d4d302bfcf21d4d302bfcd21d4d30045de70d4d30297da70d4d30005da70d4d30297d970d4d3001edf60d4d3001fdb60d4d302bfda10d4d302bfd910d4d30036dc7650d30034dc7650d300075f7550d30295de7550d30295dc7550d300075c7550d300055c7550d30006df6550d30006dd6550d3001ddf7450d3001f9f7450d300079f6450d30
  | 7 => 0x92300acfd76992300067e65992300067d6599230046bf6499230046bc6499230034ff76592300067e65592300067d6559230046bc6459230004ff755923003cfc7559230046bf74592300aebf43592300aebd4359230004ff7259230014fe7259230014fc7259230004ff715923000cfe7159230004fd715923000cfc71592300067f51592300067d5159230006bf4159230006bd4159230006ef2159230006ed2159230044fe7059230044fc7059230046be4059230046bc40592300aedf3059230006fa1059230006f9105923003cff76d5230044fe76d5230004fd76d5230044fc76d523003e7e65d52300067d65d5230034ff7695230044fe7695230004fd7695230044fc769523003e7e65952300067d65952300073f5495230004ff7655230044fe7655230004fd7655230044fc765523003e7e65552300067d6555230005fb7055230045f87055230034ff7615230044fe7615230004fd7615230044fc761523003e7e65152300067d651523001dde7315230005dd7315230014ff7658a300067e6558a300067d6558a30046ec6258a30004ff7558a3003cfc7558a30004ff7458a30034fc7458a30076ee4258a30076ee3258a3002eed3258a30004ff7158a3000cfe7158a30004fd7158a3000cfc7158a300067f5158a300067d5158a30076ef2158a30006ed2158a30014ff7058a30044fe7058a30044fc7058a3002edf3058a30046ee2058a30046ec2058a3003cff76d4a30044fe76d4a30004fd76d4a3003e7e65d4a300067d65d4a30004ff7654a30004fd7654a30044fc7654a3003e7e6554a300067d6554a30034ff76d0a30044fe76d0a30004fd76d0a300057e75d0a300057d75d0a300067e65d0a300067d65d0a30036be64d0a30006bd64d0a3001dde73d0a30005dd73d0a30004ff7650a30004fd7650a30044fc7650a300067e6550a300067d6550a30036be6450a30006bd6450a30016ee6250a30006ed6250a3010cfd76d423003e7e65d42300067d65d4230134ff765423003e7e655423010e7d65542300acfd76d02300067e65d02300067d65d02300d4ff76502300057f75502300057c75502300067e65502300067d655023003cfe76d9530034fe74d9530004fd74d9530044ff73d953001cfe73d953011cfd73d9530006dd73d953001cfc73d953011e7f53d953011e7d53d953011edc53d953011ede43d9530014fe72d9530004fd72d9530014fc72d95300067e52d95300067c52d9530004ff71d953000cfe71d9530004fd71d953000cfc71d95300067f51d95300067d51d9530006ef21d9530006ed21d95300067f65995301375c539953010df9709953010f5c5359530005ef7259530065ec7259530135fb70595300067f7559530004ff7459530034fc745953010cff7359530006df735953010e7e535953010e7
  | 8 => 0x3e7e729963003e7d729963003e7c72996300067e42996300067c42996301367f32996301367e32996301367d32996301367c329963003e7f719963003c7f719963003e7e719963003e7d71996300047d719963003e7c71996300067f41996300067e41996300067d41996300067c41996301367f31996301367e31996301367d31996301367c31996300067f21996300066f21996300067e21996300067d21996300066d21996300067c21996300467e70996300467c70996300467e40996300467c40996301367f30996301365f30996301367d30996300467c30996300067f20996300467e20996300467c20996300067f10996300467e10996300067d10996300467c109963003cff76596300467c65596300467f7559630004ff7459630034fc745963010e7f535963010e7d5359630004ff7259630014fe7259630014fc72596300067e52596300067c5259630004ff715963000cfe7159630004fd715963000cfc71596300067f51596300067e51596300067d51596300067c5159630006ef2159630006ed2159630044fe7059630044fc70596300467e50596300467c50596300457f76596300067f765963003c7f76596300467f64596300467c64596300467f62596300067e62596300467c62596300057f71596300057d71596300467f61596300067e61596300067d61596300467c61596300076f21596300076d21596300475f305963010f7b30596300477830596300477a10596300077910596300067f74596300067e74596300067d74596300067c745963010e7f735963010e7e735963010e7d735963010e7c735963010e7f435963010e7e435963010e7d435963010e7c43596300067f72596300067e72596300067d72596300067c72596300067e42596300067c425963010e7f325963010e7e325963010e7d325963010e7c32596300067f71596300047f71596300067e71596300067d71596300047d71596300067c71596300067f41596300067e41596300067d41596300067c415963010e7f315963010e7e315963010e7d315963010e7c31596300067f21596300066f21596300067e21596300067d21596300066d21596300067c21596300467e70596300467c70596300467e40596300467c405963010e7f30596300467e305963010e7d30596300467c30596300067f20596300467e20596300467c20596300067f10596300467e10596300067d10596300467c105963003cfe75d92300467e75d923003c7e75d9230004fd75d92300467d75d92300047d75d9230046dd73d9230014fe72d9230004fd72d9230044fc72d9230044ff71d923000cfe71d9230004fd71d9230044fc71d92300067f51d92300067d51d9230006ef21d9230006ed21d9230044fe70d9230046fa70d9230046df30d9230046fa10d9230006f910d
  | 9 => 0xc754c8400067e654c8400067d654c84001ede634c840006dd634c840016ee624c840006ed624c84013ef6614c840006f77558440006f67558440006767558440006f57558440006757558440006f47558440036f77458440036f67458440036f57458440036f47458440036f75458440036f65458440036f55458440036f45458440006f77358440006f67358440006f57358440006f47358440006f75358440006f65358440006f55358440006f45358440036f74358440036b74358440036f64358440036f54358440006b54358440036f44358440006f77258440006f67258440006e67258440006f57258440006e57258440006f47258440006f75258440006f65258440006f55258440006f45258440036f74258440036f64258440036f54258440036f44258440006f73258440006f63258440006f53258440006f4325844007ef77058440046f6705844007ef57058440046f47058440046f65058440046f45058440036f74058440036b74058440046f64058440036f24058440036f54058440036f14058440046f44058440006f73058440046f63058440046f43058440006f72058440046f62058440046f42058440004fd76d404003e7e65d40400067d65d4040136de63d4040006dd63d404012eee62d4040006ed62d4040126f661d4040006f561d4040004ff765404003e7e65540400067d655404010ede6354040006dd6354040106ee6254040006ed62540400fef66154040006f56154040045bf7650040006bf7650040004bf76500400073f75500400073c75500400473e65500400473d6550040005bf73500400479e63500400479d6350040047ae6250040006bd6250040047ad6250040006ad6250040046bf6150040047b661500402cebd6150040047b56150040006b561500402cf3f51500402cf3d51500402cfaf21500402cfad2150040045bf7050040037bb7050040046be6050040047ba6050040047ba10500402cfb91050040034fe74d9630004fd74d9630046dd73d9630014fe72d9630004fd72d9630044fc72d9630044ff71d963000cfe71d9630004fd71d9630044fc71d96300067f51d96300067d51d9630006ef21d9630006ed21d9630044fe70d9630046fa70d963010cfd76996300467f65996300467c659963010c7d76996300467f64996300467c64996300467f62996300067e62996300467c62996300057f71996300057d71996300467f61996300067e61996300067d61996300467c61996300076f21996300076d21996300475f30996301377b30996300477830996300477a109963000779109963003e7f749963003e7e749963003e7d749963003e7c749963003e7f739963003e7e739963003e7d739963003e7c73996301367f43996301367e43996301367d43996301367c439963003e7f7299630
  | 10 => 0x8c4003cff76d4c40044fe76d4c40004fd76d4c4003e7e65d4c400067d65d4c4001ede63d4c40006dd63d4c401beee62d4c401b6f661d4c40004ff7654c40004fd7654c40044fc7654c4003e7e6554c400067d6554c4001ede6354c40006dd6354c401aeee6254c401a6f66154c40035bf7650c400d6bf7650c400073f7550c400073c7550c40036bf6550c400373e6550c40006bd6550c400373d6550c400063d6550c40035bf7350c400379f7350c4001ebe6350c400379e6350c4001e9e6350c400379d6350c4001ebc6350c4008f9e5350c400079d5350c40037ae6250c40037ad6250c402df9e3250c4008f9c3250c40036bf6150c40037b66150c402d6bd6150c40037b56150c402d73f5150c402d73d5150c4008f9f3150c402d79d3150c402d7af2150c402d7ad2150c40005bf7050c400bebe6050c40037ba6050c4008f9f3050c40004ff755884003cfc7558840014fd7458840004ff735884001cfe735884001cfc7358840036bf4358840006bd4358840044ff7258840046ef7258840086ee5258840086ec5258840036ef4258840036ec4258840006ef3258840086ee3258840086ec3258840004ff715884000cfe7158840004fd715884000cfc71588400067f51588400067d5158840086ef2158840006ee2158840006ed2158840086ec2158840036bf4058840046ee2058840046ec2058840006ef7558840006ee7558840006ed7558840006ec7558840036ef7458840036ee7458840036ec7458840036ef5458840036ee5458840036ed5458840036ec5458840006ef7358840006ee7358840006ed7358840006ec7358840006ef5358840006ee5358840006ed5358840006ec5358840036ef4358840036af4358840036ee4358840036ed4358840006ad4358840036ec4358840006ef7158840004ef7158840006ee7158840006ed7158840004ed7158840006ec7158840006ef51588400066f5158840006ee5158840006ed51588400066d5158840006ec5158840036ef4158840036ee4158840036ed4158840036ec4158840006ef3158840006ee3158840006ed3158840006ec3158840086ef7058840046ee7058840046ec7058840046ee5058840046ec5058840036ef4058840036af4058840046ee4058840036ed4058840046ec4058840006ef3058840046ee3058840046ec3058840006ef1058840046ee1058840006ed1058840046ec105884003cff76d4840044fe76d4840004fd76d484003e7e65d48400067d65d484017ede63d4840006dd63d4840016ee62d4840006ed62d4840176f661d4840004ff7654840004fd7654840044fc765484003e7e65548400067d655484016ede6354840006dd6354840016ee6254840006ed6254840166f66154840004ff764c840004fd764c840044fc764c8400057f754c8400057
  | 11 => 0x4ff735944001cfe735944001cfc73594400067e53594400067c5359440036bf4359440004ff7259440014fe7259440014fc72594400067e52594400067c5259440004ff715944000cfe7159440004fd715944000cfc71594400067f51594400067e51594400067d51594400067c5159440006ef2159440006ed2159440044fe7059440044fc70594400467e50594400467c50594400367f74594400367e74594400367d74594400367c74594400067f73594400067e73594400067d73594400067c73594400367f43594400363f43594400367e43594400367d43594400367c43594400067f72594400067e72594400067d72594400067c72594400367f42594400367e42594400367d42594400367c42594400067f32594400067e32594400067c32594400067f71594400047f71594400067e71594400067d71594400047d71594400067c71594400367f41594400367e41594400367d41594400367c41594400067f31594400067e31594400067d31594400067c31594400067f21594400066f21594400067e21594400067d21594400066d21594400067c21594400467e70594400467c70594400367f40594400467e40594400367d40594400467c40594400067f30594400467e30594400467c30594400067f20594400467e20594400467c20594400067f10594400467e10594400067d10594400467c1059440004ff7558c4003cfc7558c4001cfd7458c40044ff7358c40046df7358c4008ede5358c4008edc5358c40036df4358c40036dc4358c40004ff7258c40014fe7258c40014fc7258c4008edf3258c40006de3258c4008edc3258c40004ff7158c4000cfe7158c40004fd7158c4000cfc7158c400067f5158c400067d5158c4008edf3158c40006de3158c40006dd3158c4008edc3158c40006ef2158c40006ed2158c40046de3058c40046dc3058c40006df7558c40006de7558c40006dd7558c40006dc7558c40036df7458c40036de7458c40036dc7458c40036df5458c40036de5458c40036dd5458c40036dc5458c40006df7258c40006de7258c40006dd7258c40006dc7258c40006de5258c40006dc5258c40036df4258c40036de4258c40036dd4258c40036dc4258c40006df7158c40006de7158c40006dd7158c40006dc7158c40006df5158c400065f5158c40006de5158c40006dd5158c400065d5158c40006dc5158c40036df4158c40036de4158c40036dd4158c40036dc4158c40006df2158c40006cf2158c40006de2158c40006dd2158c40006cd2158c40006dc2158c4008edf7058c40046de7058c40046dc7058c40046de5058c40046dc5058c40036df4058c40046de4058c40036dd4058c40046dc4058c40006df2058c40046de2058c40046dc2058c40006df1058c40046de1058c40006dd1058c40046dc105
  | 12 => 0xe76d09400373e75d09400373d75d09400073f65d09400073c65d09400379e73d09400379d73d0940006bf63d09400a5bd72d0940016be62d0940016bc62d0940035bf71d094030dbd71d09403073f51d09403073d51d09400a7af21d0940307ad21d0940045be70d0940036bf60d0940037bb60d0940307ba10d0940307b910d0940014fc76509400067f65509400067c6550940006ef6250940016ec6250940037ac4250940005fb7050940005f870509400a5bc7650940016bc7650940014bc76509400073f65509400073c6550940006bf6350940035bf7250940037af7250940007af6250940016be6250940016bc62509400a7ac62509402fdbf71509402fdbd71509402f73f51509402f73d51509400a7af21509402f7ad2150940007bb7050940045bc7050940007b87050940036bf6050940037bb60509400a7af20509402f7ba10509402f7b91050940004ff764c940004fe764c940004fc764c9400057f754c9400057c754c9400067f654c9400067c654c940034fe76d4140034fc76d41400067f65d414003e7c65d4140035be74d4140005bd74d4140004fe76941400067f659414003e7c65941400adde7394140005dd73941400077b509414003cff7654140004fd7654140034fc76541400067f655414003e7c6554140005bf7454140035bc7454140004fe76141400067f651414003e7c65141400067f65901400067c6590140035fa7090140036fb60901400073f65901400073c6590140006bf6390140005bd7290140045bf71901402edbd71901402e73f51901402e73d51901402e7af21901402e7ad2190140045be7090140046bf6090140037bb6090140047ba10901402e7b910901400367f74994400367e74994400367d74994400367c749944003e7f739944003e7e739944003e7d739944003e7c73994400367f43994400367e43994400367d43994400367c439944003e7f729944003e7e729944003e7d729944003e7c72994400367f42994400367e42994400367d42994400367c42994400067f32994400067e32994400067c329944003e7f719944003c7f719944003e7e719944003e7d71994400047d719944003e7c71994400367f41994400367e41994400367d41994400367c41994400067f31994400067e31994400067d31994400067c31994400067f21994400066f21994400067e21994400067d21994400066d21994400067c21994400467e70994400467c70994400367f40994400467e40994400367d40994400467c40994400067f30994400467e30994400467c30994400067f20994400467e20994400467c20994400067f10994400467e10994400067d10994400467c1099440044ff75594400467f7559440034ff7459440034fe7459440034fd7459440034fc74594400367e54594400367c5459440
  | 13 => 0x95400067f61195400067e61195400067d61195400067c61195400073f41195400073d41195400076f21195400076d21195403177b40195403177840195400077a101954000779101954003e7f741954003e7e741954003e7d741954003e7c741954003e7f731954003e7e731954003e7d731954003e7c73195403167f43195400067e43195403167c431954003e7f721954003e7e721954003e7d721954003e7c72195403167f42195400067e42195403167c42195400067f32195400067e32195400067c321954003e7f711954003c7f711954003e7e711954003e7d71195400047d711954003e7c71195403167f41195400067e41195400067d41195403167c41195400067f31195400067e31195400067d31195400067c31195400067f21195400066f21195400067e21195400067d21195400066d21195400067c211954003e7f701954003e7d70195403167f40195400067d40195403167c40195400067f30195400067c30195400067f20195400067c20195400067f10195400067e10195400067d10195400067c1019540004fe76d5140044fc76d51400067f65d514003e7c65d51400373e54d5140005fa70d5140005f970d514003cfc76551400067f655514003e7c6555140005fb7055140005f8705514001cfe76d8d400067f65d8d400067c65d8d400aede63d8d4003cfe75d8d40004fd75d8d4001cfc74d8d400aede43d8d40014fe72d8d40004fd72d8d40014fc72d8d40004ff71d8d4000cfe71d8d40004fd71d8d4000cfc71d8d400067f51d8d400067d51d8d40006bf41d8d40006bd41d8d40006ef21d8d40006ed21d8d40034fd70d8d400aedf30d8d40006fa10d8d40006f910d8d400057f7558d400057c7558d400067f6558d400067c6558d400aedc6358d40005ef7258d400a5ec7258d40005f77158d4009df47158d40004fe76d4d40004fd76d4d4003cfc76d4d400067f65d4d4003e7c65d4d40004ff7654d40004fe7654d40004fc7654d400067f6554d4003e7c6554d4001cfc7650d400057f7550d400057c7550d400067f6550d400067c6550d40006df6350d4001edc6350d40005fb7050d40005f87050d40014fe76d89400067f65d89400067c65d89400a6ee62d894003cfe75d8940004fd75d8940014fc74d894001cfe73d8940004fd73d894001cfc73d89400a6ee42d8940006ef32d89400a6ec32d8940004ff71d894000cfe71d8940004fd71d894000cfc71d89400067f51d89400067d51d89400a6ef21d8940006ed21d8940034fd70d89400a6ef20d89400057f75589400057c75589400067f65589400067c65589400a6ec6258940004fe76d4940004fd76d494003cfc76d49400067f65d494003e7c65d4940004ff7654940004fe7654940004fc76549400067f655494003e7c6554940005be76d0940036b
  | 14 => 0x6ed2158a40044fc7058a40046ee2058a40046ec2058a4003cff76d4a40044fe76d4a40004fd76d4a4003e7e65d4a400067d65d4a40004ff7654a40004fd7654a40044fc7654a4003e7e6554a400067d6554a40014ff7650a40016ee6250a40006ed6250a40005fb7050a40045f87050a40004ff764ca40004fd764ca40044fc764ca400057f754ca400057c754ca4001ede634ca40006dd634ca400467f65d42400467c65d42400477a50d42400467f65542400467c6554240045bd76d0240036bd76d0240005bd73d0240006bd62d0240046bf61d0240326bd61d02403273f51d02403273d51d0240327af21d0240327ad21d0240047ba60d0240047ba50d0240007b950d024003cfe76d9540034fe74d9540034fc74d954001cfe73d9540004fd73d954001cfc73d95400067e53d95400067c53d9540014fe72d9540004fd72d9540014fc72d95400067e52d95400067c52d9540004ff71d954000cfe71d9540004fd71d954000cfc71d95400067f51d95400067e51d95400067d51d95400067c51d9540006ef21d9540006ed21d954003c7e76d95400067e63d95400067c63d95400067e62d95400067c62d95400057f71d95400057d71d95400067f61d95400067e61d95400067d61d95400067c61d95400073f41d95400073d41d95400076f21d95400076d21d954031f7b40d954031f7840d95400077a10d95400077910d95400067f74d954031e7e74d95400067d74d954031e7c74d95400067f73d95400067e73d95400067d73d95400067c73d954031e7f43d95400067e43d954031e7c43d95400067f72d95400067e72d95400067d72d95400067c72d954031e7f42d95400067e42d954031e7c42d95400067f32d95400067e32d95400067c32d95400067f71d95400047f71d95400067e71d95400067d71d95400047d71d95400067c71d954031e7f41d95400067e41d95400067d41d954031e7c41d95400067f31d95400067e31d95400067d31d95400067c31d95400067f21d95400066f21d95400067e21d95400067d21d95400066d21d95400067c21d954031e7f70d95400067d70d954031e7f40d954031e7c40d95400067f30d95400067c30d95400067f20d95400067c20d95400067f10d95400067e10d95400067d10d95400067c10d95400067f65995400067f7559540004ff7459540006bf7459540004ff735954001cfe735954001cfc7359540004ff7259540014fe7259540014fc7259540004ff715954000cfe7159540004fd715954000cfc71595400067f51595400067d5159540006ef2159540006ed2159540004ff7059540006fb7059540004fe761954003e7e65195400067d65195400057e76195400067e76195400047e76195400067e63195400067c63195400067e62195400067c62195400057f71195400057d711
  | 15 => 0xe73d964001cde73d9640004fd73d9640046dd73d9640004dd73d9640044fc73d9640014fe72d9640004fd72d9640044fc72d96400067e52d96400067c52d9640044ff71d964000cfe71d9640004fd71d9640044fc71d96400067f51d96400067d51d9640006ef21d9640006ed21d9640046fa70d9640004fd76996400467f65996400467c659964003cff76596400467c65596400467f7559640004ff735964001cfe735964001cfc73596400067e53596400067c5359640004ff7259640014fe7259640014fc7259640004ff715964000cfe7159640004fd715964000cfc71596400067f51596400067d5159640006ef2159640006ed2159640044fc70596400467e50596400467c505964003e7e65d52400067d65d52400373e54d5240045fa70d5240005f970d524003cff765524003e7e65552400067d6555240005fb7055240045f87055240037bb405524001cff7658e40046dc6358e40004ff7558e4003cfc7558e400bedc5358e400bede4358e40004ff7258e40014fe7258e40014fc7258e400bedf3258e40004ff7158e4000cfe7158e40004fd7158e4000cfc7158e400067f5158e400067d5158e400bedf3158e40006dd3158e40006ef2158e40006ed2158e40044fc7058e40046de3058e40046dc3058e40006fa1058e40006f91058e4003cff76d4e40044fe76d4e40004fd76d4e400067f65d4e4003e7c65d4e4001ede63d4e40006dd63d4e40004ff7654e40004fd7654e40044fc7654e400067f6554e4003e7c6554e40005bd76d0e40036bd76d0e40006bf65d0e40006bd65d0e4001ebe63d0e4001ebc63d0e4033ebf61d0e4033ebd61d0e4033f3f51d0e4033f3d51d0e4033faf21d0e4033fad21d0e40005bd70d0e40037ba60d0e4033fba10d0e4033fb910d0e4001cff7650e400057f7550e400057c7550e4001ede6350e40006dd6350e40005fb7050e40045f87050e400bdbf7650e4001ebf7650e4001cbf7650e400073f7550e400073c7550e40006bf6550e40006bd6550e40035bf7350e400379f7350e4001ebe6350e400bf9e6350e400079d6350e4001ebc6350e400bf9e5350e400079d5350e403379e3250e400bf9c3250e4032ebf6150e4032ebd6150e4032f3f5150e4032f3d5150e400bf9f3150e4032f9d3150e4032faf2150e4032fad2150e40005bf7050e40007bb7050e40007b87050e40036be6050e400bf9f3050e4032fba1050e4032fb91050e40014ff7658a400057f7558a400057c7558a40046ec6258a40004ff7558a400067f7558a400047f7558a4003cfc7558a400067c7558a4003c7c7558a40004ff7358a4001cfe7358a4001cfc7358a40006bf4358a40006bd4358a400b6ee4258a40004ff7158a4000cfe7158a40004fd7158a4000cfc7158a400067f5158a400067d5158a400b6ef2158a40
  | 16 => 0x8500edde73d0850005dd73d0850004ff7650850004fd7650850044fc76508500057f755085003d7c7550850036be6450850006bd6450850016ee6250850006ed6250850004ff764c850004fd764c850044fc764c8500057f754c85003d7c754c85001ede634c850006dd634c850016ee624c850006ed624c8500457f76540500067f76540500047f76540503157c74540500067d64540500057f735405010e7e63540500467c63540500e57e72540500e57c72540500067d625405036d7f715405036d7d71540500467f61540503667d61540503676f21540503676d21540500457f705405003f7b70540500467e60540500477a60540500367f7559740034fc74597400367e54597400367c5459740004ff735974001cfe735974001cfc7359740004ff7259740014fe7259740014fc72597400067e52597400067c5259740004ff715974000cfe7159740004fd715974000cfc71597400067f51597400067d5159740006ef2159740006ed2159740004ff7558f400067f7558f400047f7558f4003cfc7558f400067c7558f4003c7c7558f40036df7358f400d6de5358f40036df4358f40036dc4358f40004ff7258f40014fe7258f40014fc7258f40036bf4258f40006de3258f400d6dc3258f40004ff7158f4000cfe7158f40004fd7158f4000cfc7158f400067f5158f400067d5158f40036bf4158f40006bd4158f400d6df3158f40006dd3158f40006ef2158f40006ed2158f40036bc4058f400d6df3058f4003cff76d4f40034fe76d4f40004fd76d4f4003e7e65d4f400067d65d4f40004ff7654f40004fd7654f40034fc7654f4003e7e6554f400067d6554f4001ede6354f40006dd6354f40004ff7558b4003cfc7558b40004ff7358b4001cfe7358b4001cfc7358b40036ef7258b40036ef4258b40036ec4258b40004ff7158b4000cfe7158b40004fd7158b4000cfc7158b400067f5158b400067d5158b400ceef2158b40006ed2158b400ceef2058b4003cff76d4b40034fe76d4b40004fd76d4b4035e7f65d4b4003e7c65d4b40004ff7654b40004fd7654b40034fc7654b403567f6554b4003e7c6554b40035bf7650b40086bf7650b40006bd6350b40037af7250b40037af6250b40016be6250b40016bc6250b40037ac6250b4034dbf7150b4034dbd7150b403473f5150b403473d5150b400cfaf2150b40347ad2150b40045bc7050b400cfaf2050b40004ff764cb40004fd764cb40034fc764cb400057f754cb400057c754cb4003e7e65d43400067d65d4340035be74d4340005bd74d434031e7f659434003e7c65943400d5de7394340005dd739434003cff765434003e7e65543400067d6554340005bf7454340035bc74543403167f651434003e7c6514340046bd74d964031e7e54d964031e7c54d964001cfe73d9640046d
  | 17 => 0x10dde7394150005dd739415003dfa709415003efb60941500057d749415031e7c649415010d7e73941500475e739415010d5e73941500475d73941500457c73941500067f63941500057d72941501167e62941501167c62941500457f719415039d7d71941503967f61941503967d61941503976f21941503976d21941500457e70941500467f609415003f7b6094150046bf745905003ebf545905003e7c545905003ebc5459050004ff735905001cfe735905001cfc735905003e7f5359050004ff7259050014fe7259050014fc72590500067e525905003e7c5259050004ff715905000cfe7159050004fd715905000cfc715905003e7f51590500067d5159050006bf4159050006bd4159050006ef2159050006ed215905003e7f5059050046be4059050046bc405905003d7d76950503167d76950500047d769505003d7e749505003f3e749505003e7f64950503167d64950500057d73950502067e639505003e7c63950500e57e72950500e57c72950503157f719505038d7d719505003e7f61950503867d61950503876f21950503876d21950500057d709505031e7e609505003f7a609505001cfd7558c50004ff7458c50034fc7458c50044ff7358c50046df7358c5003edf5358c5003edc5358c500eede4358c50004ff7258c50014fe7258c50014fc7258c500eedf3258c50004ff7158c5000cfe7158c50004fd7158c5000cfc7158c5003e7f5158c500067d5158c500eedf3158c50006dd3158c50006ef2158c50006ed2158c50046de3058c50046dc3058c5003d7f7654c501367f7654c501347f7654c503157c7454c500067d6454c5003d7f7354c5003f5f7354c5001e7e6354c5001e7c6354c500ef5e4354c500e57e7254c500e57c7254c5037d7f7154c5037d7d7154c5003e7f6154c503767d6154c503776f2154c503776d2154c500057f7054c5011e7e6054c5003f7a6054c50034ff76d0c50044fe76d0c50004fd76d0c503157f75d0c5003d7c75d0c50036be64d0c50006bd64d0c503173e54d0c50004ff7650c50004fd7650c50044fc7650c500057f7550c5003d7c7550c50036be6450c50006bd6450c500073e5450c5001ede6350c50006dd6350c500075d5350c50014fd7558850004ff7458850034fc74588500067e545885003e7c5458850004ff735885001cfe735885001cfc735885003e7f53588500067d5358850044ff7258850046ef725885003eef52588500e67e525885003e7c525885003eec52588500e6ee42588500e6ee3258850004ff715885000cfe7158850004fd715885000cfc715885003e7f51588500067d51588500e6ef2158850006ed215885003e7f5058850046ee2058850046ec2058850034ff76d0850044fe76d0850004fd76d085003d7e75d08500057d75d0850036be64d0850006bd64d
  | 18 => 0xc7655150006bf6455150036bc6455150005fb7055150005f870551500347c765515003d7f745515003f3f74551500073f64551500367e64551500367c64551500073c645515010d7e735515010d7c73551500057f72551501e67e62551501e67c62551503cd7f71551503cd7d71551503c67f61551503c67d61551503c76f21551503c76d21551500077b70551500457c705515000778705515003e7f605515003f7b605515001cfe76d8d5003d7e75d8d5010ede63d8d5010f5e53d8d5001cfc75d8d50034fe74d8d50004fd74d8d500067f54d8d500067d54d8d5010e7e53d8d5010ede53d8d5010e7c53d8d50014fe72d8d50004fd72d8d50014fc72d8d50004ff71d8d5000cfe71d8d50004fd71d8d5000cfc71d8d500067f51d8d500067d51d8d50006ef21d8d50006ed21d8d5003cfd70d8d5010edf30d8d5010edc6358d5010f5c5358d50005ef7258d50105ec7258d5001cfc7654d5010d7f7554d50006df6354d5001edc6354d5003f5c5354d50005fb7054d50005f87054d50004fe76d0d50004fd76d0d50034fc76d0d5003d7e75d0d500057d75d0d50006bf64d0d50036bc64d0d500073d54d0d50004ff7650d50004fe7650d50004fc7650d500057f7550d5003d7c7550d50006bf6450d50036bc6450d500073d5450d5001ede6350d5010f5e5350d50014fe76d8950106ee62d8950014fc75d8950034fe74d8950004fd74d895001cfe73d8950004fd73d895001cfc73d8950106ee52d8950006ef32d8950106ec32d8950004ff71d895000cfe71d8950004fd71d895000cfc71d89500067f51d89500067d51d8950106ef21d8950006ed21d895003cfd70d8950106ef20d8950106ec62589500057e76d495003e7e76d49501147e76d49500057d74d495035e7c64d495010d7e73d495003d7c73d49500067f63d49501057d72d49500167e62d49500167c62d495003d7f71d49503bd7d71d49503b67f61d49503b67d61d49501076f21d49503b76d21d49500457e70d495003e7f60d495003f7b60d4950014fc7654950006ef6254950016ec6254950005fb7054950005f870549501057c76549500167c76549500147c76549500057f74549503567c645495010d7e735495010d7c73549500067f635495003d7f725495003f6f72549500076f62549500167e62549500167c62549501076c62549503ad7f71549503ad7d71549503a67f61549503a67d61549501076f21549503a76d21549500077b70549500457c705495000778705495003e7f605495003f7b6054950004fe76d0950004fd76d0950034fc76d095003d7e75d09500057d75d095010dde73d0950005dd73d0950004ff7650950004fe7650950004fc765095003d7e75509500057d7550950004ff764c950004fe764c950004fc764c9500057f754c95003d7c754c950
  | 19 => 0x4e5003f5f7354e5001e7e6354e5011f5e6354e5001e5e6354e500075d6354e5001e7c6354e5011f5e4354e501157e7254e501157c7254e503fd7f7154e503fd7d7154e503f67f6154e503f67d6154e503f76f2154e503f76d2154e500057f7054e500077b7054e50007787054e5003e7e6054e50034ff76d0e50044fe76d0e50004fd76d0e5031d7f75d0e5003d7c75d0e50036bc64d0e5031f3e54d0e5001ede63d0e50006dd63d0e50004ff7650e50004fd7650e50044fc7650e500057f7550e5003d7c7550e500073e5450e5001ede6350e50006dd6350e500075d5350e50014ff7658a5003d7c7558a50006de6358a50006dd6358a50046ec6258a501176e5258a50004ff7458a50034fc7458a500067e5458a500067c5458a50004ff7358a5001cfe7358a5001cfc7358a500067f5358a500067d5358a501167e5258a50116ee5258a501167c5258a50116ee4258a50004ff7158a5000cfe7158a50004fd7158a5000cfc7158a500067f5158a500067d5158a50116ef2158a50006ed2158a50044fc7058a50046ee2058a50046ec2058a50014ff7654a501157f7554a5016ede6354a50006dd6354a50016ee6254a50006ed6254a50005fb7054a50045f87054a50034ff76d0a50044fe76d0a50004fd76d0a5003d7e75d0a500057d75d0a50036be64d0a50006bd64d0a5011dde73d0a50005dd73d0a5015ede63d0a50006dd63d0a50004ff7650a50004fd7650a50044fc7650a500057f7550a5003d7c7550a50036be6450a50006bd6450a5014ede6350a50006dd6350a50016ee6250a50006ed6250a50004ff764ca50004fd764ca50044fc764ca500057f754ca5003d7c754ca5001ede634ca50006dd634ca500457d76d425003e7d76d425031d7e74d42500067d64d42500057d73d42501367e63d42500475e63d42501365e63d42500475d63d42500467c63d42501157e72d425003d7c72d42500067d62d425003d7f71d42503ed7d71d42500467f61d42503e67d61d42503e76f21d42503e76d21d42500477a60d425001cfe73d9150004fd73d915001cfc73d9150014fe72d9150004fd72d9150014fc72d9150004ff71d915000cfe71d9150004fd71d915000cfc71d91500067f51d91500067d51d9150006be41d9150006bc41d9150006ef21d9150006ed21d9150006bf6499150036be6419150006bd641915010dde7319150005dd73191500057e76d515003e7e76d51500047e76d51500367e64d51500367c64d515010d7e73d515003d7c73d51500057d72d51502167e62d51502167c62d515003d7f71d51503dd7d71d51503d67f61d51503d67d61d51503d76f21d51503d76d21d51500457e70d515003e7f60d515003f7b60d51503cd7d7595150006bf6495150036bc649515003f3f5495150005fa7095150005f97095150034f
  | 20 => 0x4257d711525041e7f611525041e7d611525041f6f211525041f6d21152500057d701525003f7a601525011f5d7598e5011f9e7498e5011f9d7498e50046df6498e50006de6498e50006dd6498e50046dc6498e500075e5498e500075c5498e50046df6298e50006de6298e50046dc6298e500075e5298e500075c5298e50046df6198e50006de6198e50006dd6198e50046dc6198e500075f5198e500075d5198e50007cf2198e50007cd2198e50046de6098e50417db5098e50047d85098e5001cff7658e50046dc6358e50004ff7458e50034fc7458e5011ede5358e5011ede4358e5011edc4358e50004ff7258e50014fe7258e50014fc7258e5011edf3258e50006de3258e5011edc3258e50004ff7158e5000cfe7158e50004fd7158e5000cfc7158e500067f5158e500067d5158e5011edf3158e50006de3158e50006dd3158e5011edc3158e50006ef2158e50006ed2158e50044fc7058e50046de3058e50046dc3058e50045df7658e5011edf7658e5001cdf7658e500075d7558e50046df6458e50006de6458e50006dd6458e50046dc6458e500075e5458e500075c5458e50046df6258e50006de6258e50046dc6258e500075e5258e500075c5258e50046df6158e50006de6158e50006dd6158e50046dc6158e500075f5158e500075d5158e50007cf2158e50007cd2158e50297db5058e50047d85058e50006dd7558e5011edc7558e50006df7458e50006de7458e50006dd7458e50006dc7458e50296df5458e50006de5458e50006dd5458e50296dc5458e50006df7258e50006de7258e50006dd7258e50006dc7258e50296df5258e50006de5258e50296dc5258e50006de4258e50006dc4258e50006df7158e50006de7158e50006dd7158e50006dc7158e50296df5158e500065f5158e50006de5158e50006dd5158e500065d5158e50296dc5158e50006df4158e50006de4158e50006dd4158e50006dc4158e50006df2158e50006cf2158e50006de2158e50006dd2158e50006cd2158e50006dc2158e5011edf7058e50046de7058e50046dc7058e50296df5058e50046de5058e50046dc5058e50046de4058e50046dc4058e50006df2058e50046de2058e50046dc2058e50006df1058e50046de1058e50006dd1058e50046dc1058e500057d76d4e5003e7d76d4e5010c7d76d4e5031d7e74d4e500067d64d4e5001e7e63d4e5011f5e63d4e5001e5e63d4e500075d63d4e5001e7c63d4e501157e72d4e5003d7c72d4e5003d7f71d4e5040d7d71d4e504067f61d4e504067d61d4e504076f21d4e504076d21d4e500057d70d4e5003f7a60d4e5011f5f30d4e5001cff7654e5001ede6354e50006dd6354e50005fb7054e50045f87054e5011d7f7654e5001e7f7654e5001c7f7654e5031d7c7454e500067d6454e5003d7f735
  | 21 => 0xf215535044f6d21553500457c7055350004ff7458f50034fc7458f5003e7f5458f500067d5458f5003edf7358f5003edf5358f501367e5358f5003e7c5358f5003edc5358f50136de4358f50004ff7258f50014fe7258f50014fc7258f5003e7f5258f50004ff7158f5000cfe7158f50004fd7158f5000cfc7158f5003e7f5158f500067d5158f50006ef2158f50006ed2158f5003e7c5058f50136df3058f50034ff76d0f5003cfe76d0f50004fd76d0f5003d7e75d0f500057d75d0f50036be64d0f50006bd64d0f500073d54d0f50004ff7650f50004fd7650f5003cfc7650f500057f7550f5003d7c7550f50036be6450f50006bd6450f500073d5450f5001ede6350f50006dd6350f501375e5350f50004ff7458b50034fc7458b50004ff7358b5001cfe7358b5001cfc7358b5003eef7258b5003eef5258b5003eec5258b50004ff7158b5000cfe7158b50004fd7158b5000cfc7158b5003e7f5158b500067d5158b5012eef2158b50006ed2158b5012eef2058b5003d7f7654b500e67f7654b500e47f7654b500057f7454b503567e6454b501357e7354b501357c7354b500067d6354b5003f6f7254b500167e6254b500167c6254b504457f7154b504457d7154b5003e7f6154b5043e7d6154b5012f6f2154b5043f6d2154b500457c7054b50034ff76d0b5003cfe76d0b50004fd76d0b5003d7e75d0b500057d75d0b50135de73d0b50005dd73d0b50004ff7650b50004fd7650b5003cfc7650b5003d7e7550b500057d7550b50004ff764cb50004fd764cb5003cfc764cb500057f754cb5003d7c754cb50046bf6499250046bc6499250046bc6459250004ff735925001cfe735925001cfc7359250004ff7259250014fe7259250014fc72592500067e52592500067c5259250004ff715925000cfe7159250004fd715925000cfc71592500067f51592500067d5159250006bf4159250006bd4159250006ef2159250006ed2159250044fc7059250046be4059250046bc4059250036be6495250006bd649525003f3f5495250206de6395250045fa7095250005f9709525003d7e749525031f3e649525031e7d64952500073d64952500063d64952500057d73952502067e63952502065e63952502067c63952501157e72952501157c729525031d7f71952504357d719525042e7f619525042e7d619525042f6f219525042f6d219525031f7a70952500057d709525031f79709525000579709525003e7e6095250034ff7655250036be6455250006bd64552501eede6355250005fb7055250045f8705525003f7b50552500057d761525003e7d761525003f3e741525031e7d641525003f5e73152500057d731525003f5d73152500055d73152501d67e63152501d65e63152501d67c63152501157e721525003d7c721525003d7f7115250
  | 22 => 0x9132466bd43d913201cff72d913201cfd72d913245ebf42d913245ebd42d913245ede32d913245edc32d9132004ff71d913200cfe71d9132004fd71d913200cfc71d91320067f51d91320067d51d913245eef21d9132006ed21d9132044fe70d9132004fd70d9132466df30d913218cfd76991320057e75991320057d75991320067f65991320067c6599132006bf649913218ddd739913214ded7299132034ff76591320057f75591320057c75591320067f65591320067c655913219ddf735913215def7259132004ff75591320067f75591320047f755913203cfc75591320067c755913203c7c7559132006bf745913219cff7359132006df735913218cff7259132006ef725913218ede325913218edc3259132004ff715913200cfe7159132004fd715913200cfc71591320067f51591320067d515913218eef2159132006ed2159132004ff7059132044fc705913214edf305913245cfe76191320067f65191320067c6519132036be6419132006bd641913203cff76d5132004fe76d5132004fd76d513203cfc76d51320067f65d513203e7c65d5132034ff7695132004fe7695132004fd7695132034fc76951320067f659513203e7c65951320073f5495132004ff7655132004fe7655132004fd7655132004fc76551320067f655513203e7c6555132034ff7615132004fe7615132004fd7615132034fc76151320067f651513203e7c651513201dde7315132005dd73151320067f65d81320067c65d813203cfe75d8132004fd75d8132034fe74d8132004fd74d8132014fd73d813201cfd72d8132004ff71d813200cfe71d8132004fd71d813200cfc71d81320067f51d81320067d51d8132266ef21d8132006ed21d8132246fa30d8132266fa20d81320057e75981320057d75981320067f65981320067c6598132006fb60981320057f75581320057c75581320067f65581320067c65581320067f65181320067c6518132006f9601813203cfe7518132004fd7518132034fe7418132004fd7418132014fd7318132046dd731813201cfd7218132044ff711813200cfe7118132004fd7118132044fc71181320067f51181320067d511813224eef2118132006ed2118132046df3018132046fa3018132276f93018132046fa201813224ef9201813203ebf745935003ebf545935003ebc5459350004ff735935001cfe735935001cfc7359350004ff7259350014fe7259350014fc7259350004ff715935000cfe7159350004fd715935000cfc715935003e7f51593500067d5159350006ef2159350006ed215935003d7f76553500067f765535003f3f74553500367e64553500367c64553501357e73553501357c73553500057f72553501e67e625535003e7c62553504557f71553504557d715535003e7f615535044e7d615535044f6
  | 23 => 0x67f74d95320067e74d95320067d74d95320067c74d953247e7f73d95324867e73d953247e7d73d953247e7c73d95324867f43d95324867e43d95324867d43d95324867c43d953247e7f72d953247e7e72d953247e7d72d953247e7c72d953247e7f42d953247e7e42d953247e7d42d953247e7c42d953247e7f32d953247e7e32d953247e7c32d95320067f71d95320047f71d95320067e71d95320067d71d95320047d71d95320067c71d95320067f41d95320067e41d95320067d41d95320067c41d95324867f31d95324867e31d95324867d31d95324867c31d953247e7f21d953247e6f21d953247e7e21d953247e7d21d95320066d21d953247e7c21d95320067f70d95320067e70d95320067d70d95320067c70d95324867f30d95324867e30d95324867d30d95324867c30d953247e7f20d953247e7e20d953247e7d20d953247e7c20d95320067f10d95320067e10d95320067d10d95320067c10d95321acfd76995320067f65995321addd739953216ded729953203cff76595321bddf735953217def72595320067f7559532004ff7459532034fc74595321bcff7359532006df73595321acff7259532006ef7259532004ff715953200cfe7159532004fd715953200cfc71595320067f51595320067d51595321aeef2159532006ed2159532004ff7059532044fc705953247cfe761953203e7e65195320067d651953247d7e76195320067e761953247c7e76195324776f321953246f5e321953246f5c321953246f6c32195320057f71195320057d71195320067f61195320067e61195320067d61195320067c611953246f6f21195320076d21195324775f301953203e7f741953203e7e741953203e7d741953203e7c741953203e7f731953203e7e731953203e7d731953203e7c73195324767f43195324767e43195324767d43195324767c431953203e7f721953203e7e721953203e7d721953203e7c721953246e7f421953246e7e421953246e7d421953246e7c421953246e7f321953246e7e321953246e7d321953246e7c321953203e7f711953203c7f711953203e7e711953203e7d71195320047d711953203e7c71195320067f41195320067e41195320067d41195320067c41195324767f31195324767e31195324767d31195324767c311953246e7f211953246e6f211953246e7e211953246e7d21195320066d211953246e7c211953203e7f701953203e7e701953203e7d701953203e7c70195324767f30195324765f30195324767e30195324767d30195324767c301953246e7f201953246e7e201953246e7d201953246e7c20195320067f10195320067e10195320067d10195320067c1019532034fe76d91320067f65d91320067c65d913203cfe75d9132004fd75d9132014ff73d9132014fd73d9132466bf43d
  | 24 => 0xe70d8d42004fd70d8d420057f7558d420057c7558d4214edc6358d42004fe76d4d42004fd76d4d4203cfc76d4d4203e7e65d4d420067d65d4d42004ff7654d42004fe7654d42004fc7654d4203e7e6554d420067d6554d42005ef7254d42015ec7254d4249dbe76d0d42036be76d0d42006bf65d0d42006bd65d0d4218dbd73d0d4201ebe63d0d4201ebc63d0d42015be72d0d42015bc72d0d42036bf62d0d42037af62d0d42496bf61d0d42496bd61d0d424973f51d0d424973d51d0d4219faf21d0d42497ad21d0d42005bd70d0d4219faf20d0d42014fc7650d420057f7550d420057c7550d42006df6350d4201edc6350d42005ef7250d42015ec7250d42015bc7650d4201ebc7650d42014bc7650d420073f7550d420073c7550d42006bf6550d42006bd6550d42035bf7350d420379f7350d420079f6350d4201ebe6350d4201ebc6350d4214f9c6350d4214f9e5350d420079d5350d42007af7250d42015be7250d42015bc7250d4218fac7250d42036bf6250d42037af6250d4218f9e3250d4218f9c3250d4248ebf6150d4248ebd6150d4248f3f5150d4248f3d5150d4214f9f3150d4248f9d3150d4218faf2150d4248fad2150d42005bf7050d4214f9f3050d4218faf2050d4203cfe75d8142004fd75d814201cfe73d8142004fd73d814201cfc73d8142034fd72d8142004ff71d814200cfe71d8142004fd71d814200cfc71d81420067f51d81420067d51d81420ceef21d8142006ed21d81420cefa20d8142006fb60981420057f75581420057c75581420057e75181420057d751814214dde7318142005dd7318142145f67118142005f57118142006f9601814203cfe75181420467e751814203c7e7518142004fd75181420467d75181420047d7518142046bd741814201cfe7318142046de731814201cde7318142004fd7318142046dd7318142004dd7318142044fc7318142006bf4318142006bd4318142034fd7218142044ff711814200cfe7118142046f6711814200cf67118142004fd7118142046f57118142004f57118142044fc71181420067f51181420067d5118142086ef2118142006ed2118142046ef2018142046fa2018142086f9201814203cfe76d9532034fe74d9532004fd74d9532014ff73d9532014fd73d95324867f53d95324867d53d953201cff72d953201cfd72d953247e7f52d953247e7d52d9532004ff71d953200cfe71d9532004fd71d953200cfc71d95320067f51d95320067e51d95320067d51d95320067c51d953247eef21d9532006ed21d9532044fe70d9532004fd70d953203c7e76d95324876f32d953247f5e32d953247f5c32d953247f6c32d95320057f71d95320057d71d95320067f61d95320067e61d95320067d61d95320067c61d953247f6f21d95320076d21d95324875f30d9532
  | 25 => 0x4f420067d65d4f4201ede63d4f42006dd63d4f42004ff7654f42004fd7654f42034fc7654f4203e7e6554f420067d6554f4201ede6354f42006dd6354f42035bf7650f424aebf7650f420073f7550f420073c7550f42036bf6550f420373e6550f42006bd6550f420373d6550f420063d6550f420379f7350f4201ebe6350f420379e6350f4201e9e6350f420379d6350f4201ebc6350f4215f9e5350f420079d5350f42015be7250f42015bc7250f4218f9e3250f4218f9c3250f42036bf6150f424a6bd6150f424a73f5150f424a73d5150f4215f9f3150f424a79d3150f4218faf2150f424a7ad2150f42005bf7050f4215f9f3050f4203cfe7598342004fd7598342014fe7498342046be7498342014be7498342044fc749834201cfe7398342004fd7398342044fc7398342036bf4398342006bd4398342044ff719834200cfe7198342004fd7198342044fc71983420067f51983420067d51983420b6ef2198342006ed2198342046fa7098342046bf4098342036fb4098342046f84098342046fa20983420b6f92098342046fa1098342006f91098342004ff755834203cfc7558342014fc7458342004ff735834201cfe735834201cfc7358342036ee4258342036ed4258342004ff715834200cfe7158342004fd715834200cfc71583420067f51583420067d51583420a6ef2158342006ed2158342036fb7058342036fb4058342036f840583420a6fa2058342006fa1058342006f9105834203cfe76d954201cfe73d9542004fd73d954201cfc73d95420067e53d95420067c53d9542034ff72d9542034fd72d95421fe7f52d95421fe7d52d9542004ff71d954200cfe71d9542004fd71d954200cfc71d95420067f51d95420067d51d95421feef21d9542006ed21d9542044fe70d9542004fd70d95420067f65995421e5bd7499542215bf74595420067f7559542214ff7459542006bf74595423567e54595423567c5459542004ff735954201cfe735954201cfc73595421e4ff7259542006ef72595421e67e52595421e67c5259542004ff715954200cfe7159542004fd715954200cfc71595420067f51595420067d51595421e6ef2159542006ed2159542004ff7059542044fc70595421fcfe761954203e7e65195420067d6519542014fe76d5142014fc76d51420067f65d514203e7c65d51420373e54d5142015ee72d5142005ed72d514203cff7655142014fe76551421e4fd7655142014fc76551420067f655514203e7c6555142005ef7255142015ec7255142037ac425514201cfe76d8d4214ede63d8d4203cfe75d8d42004fd75d8d42014fd74d8d4214ede43d8d42034fd72d8d4219edf32d8d42004ff71d8d4200cfe71d8d42004fd71d8d4200cfc71d8d420067f51d8d420067d51d8d4219eef21d8d42006ed21d8d42044f
  | 26 => 0x1cfc73597420067e53597420067c5359742036bf43597421e67f52597421e67d5259742004ff715974200cfe7159742004fd715974200cfc71597420067f51597420067e51597420067d51597420067c51597421e6ef2159742006ed2159742004ff7059742044fc70597420367f74597420367e74597420367d74597420367c74597420067f73597420067e73597420067d73597420067c73597420367f43597420363f43597420367e43597420367d43597420367c43597421e67f72597421e67e72597421e67d72597421e67c72597420367f42597420367e42597420367d42597420367c42597421e67f32597421e67e32597421e67d32597421e67c32597420067f71597420047f71597420067e71597420067d71597420047d71597420067c71597420367f41597420367e41597420367d41597420367c41597420067f31597420067e31597420067d31597420067c31597421e67f21597421e66f21597421e67e21597421e67d21597420066d21597421e67c21597420067f70597420067e70597420067d70597420067c70597420367f40597420367e40597420367d40597420367c40597420067f30597420067c30597421e67f20597421e67e20597421e67d20597421e67c20597420067f10597420067e10597420067d10597420067c1059742004ff7558f4203cfc7558f42014fe7458f42014fc7458f42036df7358f4215ede5358f4215edc5358f42036df4358f42036dc4358f4218edf3258f42004ff7158f4200cfe7158f42004fd7158f4200cfc7158f420067f5158f420067d5158f4215edf3158f42006de3158f42006dd3158f4215edc3158f4218eef2158f42006ed2158f42004ff7058f42044fc7058f4215edf3058f4215edc3058f42006df7558f42006de7558f42006dd7558f42006dc7558f42036df7458f42036de7458f42036dd7458f42036dc7458f42036df5458f42036de5458f42036dd5458f42036dc5458f4218edf7258f4218ede7258f4218edd7258f4218edc7258f4218edf5258f4218ede5258f4218edd5258f4218edc5258f42036df4258f42036de4258f42036dd4258f42036dc4258f42006df7158f42006de7158f42006dd7158f42006dc7158f42006df5158f420065f5158f42006de5158f42006dd5158f420065d5158f42006dc5158f42036df4158f42036de4158f42036dd4158f42036dc4158f4218edf2158f4218ecf2158f4218ede2158f4218edd2158f42006cd2158f4218edc2158f42006df7058f42006de7058f42006dd7058f42006dc7058f42036df4058f42036de4058f42036dd4058f42036dc4058f4218edf2058f4218ede2058f4218edd2058f4218edc2058f42006df1058f42006de1058f42006dd1058f42006dc1058f4203cff76d4f42034fe76d4f42004fd76d4f4203e7e65d
  | 27 => 0xe63d4d5201e7c63d4d520157e72d4d520157c72d4d5203e7f62d4d5203f6f62d4d5203d7f71d4d524cd7d71d4d524c67f61d4d524c67d61d4d521bf6f21d4d524c76d21d4d520057d70d4d5216f5f30d4d52014fc7654d52006df6354d5201edc6354d52005ef7254d52015ec7254d520157c7654d5201e7c7654d520147c7654d523557c7454d520067f6454d5203d7f7354d5203f5f7354d520075f6354d5201e7e6354d5201e7c6354d5216f5c6354d5216f5e4354d520076f7254d520157e7254d520157c7254d521af6c7254d5203e7f6254d5203f6f6254d524bd7f7154d524bd7d7154d524b67f6154d524b67d6154d521af6f2154d524b76d2154d520057f7054d52004fe76d0d52004fd76d0d52034fc76d0d523557f75d0d5203d7c75d0d52036be64d0d523573e54d0d52004ff7650d52004fe7650d52004fc7650d520057f7550d5203d7c7550d520073e5450d52006df6350d5201edc6350d520075d5350d52034fe74d8152004fd74d815201cfe73d8152004fd73d815201cfc73d815203cfd72d8152004ff71d815200cfe71d8152004fd71d815200cfc71d81520067f51d81520067d51d815212eef21d8152006ed21d815212efa20d815216dde7398152005dd7398152006fb6098152006f960181520467d7518152034fe7418152004fd74181520067e54181520067c541815201cfe7318152004fd7318152044fc73181520067f53181520067d531815203cfd72181520e67e52181520e67c5218152044ff711815200cfe7118152004fd7118152044fc71181520067f51181520067d51181520e6ef2118152006ed2118152046fa20181520e6f920181520367f74997420367e74997420367d74997420367c749974203e7f739974203e7e739974203e7d739974203e7c73997420367f43997420367e43997420367d43997420367c439974203e7f729974203e7e729974203e7d729974203e7c72997420367f42997420367e42997420367d42997420367c42997422167f32997422167e32997422167d32997422167c329974203e7f719974203c7f719974203e7e719974203e7d71997420047d719974203e7c71997420367f41997420367e41997420367d41997420367c41997420067f31997420067e31997420067d31997420067c31997422167f21997422166f21997422167e21997422167d21997420066d21997422167c219974203e7f709974203e7e709974203e7d709974203e7c70997420367f40997420367e40997420367d40997420367c40997420067f30997420067c30997422167f20997422167e20997422167d20997422167c20997420067f10997420067e10997420067d10997420067c10997420367f7559742014fe7459742014fc74597420367e54597420367c5459742004ff735974201cfe7359742
  | 28 => 0xf5203d7c7550f52036be6450f52006bd6450f520073e5450f5201ede6350f52006dd6350f520075d5350f52014fe75983520467e75983520147e7598352044fc7598352034fe7498352004fd74983520067e549835203e7c549835201cfe7398352046de739835201cde7398352004fd7398352046dd7398352004dd7398352044fc739835203e7f53983520067d53983521167e529835203e7c5298352044ff719835200cfe7198352004fd7198352044fc719835203e7f51983520067d5198352116ef2198352006ed2198352046fa70983520467f509835203efb5098352046f85098352046fa2098352116f92098352014fc7558352004ff7458352034fc7458352004ff735835201cfe735835201cfc7358352004ff715835200cfe7158352004fd715835200cfc715835203e7f51583520067d5158352106ef2158352006ed215835203efb705835203efb505835203ef85058352106fa2058352034fe76d91522167d75d915201cfe73d9152004fd73d915201cfc73d915203cfd72d91522167e52d91522167c52d9152216bf42d9152004ff71d915200cfe71d9152004fd71d915200cfc71d91520067f51d91520067d51d9152216ef21d9152006ed21d9152044fe70d9152004fd70d9152006bf649915216dde7399152005dd7399152036be6419152006bd6419152014fe7695152006bf6495152036bc649515203f3f5495152015ee7295152005ed72951520157e76951521fe7e76951520147e769515203d7e74951523567f64951520073f64951520063f64951523573c64951520057d73951522067e63951522067c63951520157e72951521ff6e72951523576d72951520157c729515203e7f629515203f6f62951523557f71951524ed7d71951524e67f61951524e67d61951521ff6f21951524e76d21951520057d7095152014fc76551521e67f6555152006bf6455152036bc6455152005ef7255152015ec72551522157e761515203e7e76151522147e76151521fd7e741515203f3e74151523567f641515203f5e73151520057d731515203f5d73151520055d73151521d67e63151521d67c63151520157e72151520157c721515203e7f621515203f6f621515203d7f71151524dd7d71151524d67f61151524d67d61151521cf6f21151524d76d21151520057d701515201cfe76d8d5216ede63d8d52014fd75d8d52034fe74d8d52004fd74d8d5216ede53d8d5216ede43d8d5203cfd72d8d521bedf32d8d52004ff71d8d5200cfe71d8d52004fd71d8d5200cfc71d8d520067f51d8d520067d51d8d52006de31d8d5216edc31d8d521beef21d8d52006ed21d8d52044fe70d8d52004fd70d8d5216edf30d8d5216edc6358d5246d7e76d4d5203e7e76d4d5246c7e76d4d523557e74d4d520067f64d4d521ad7d73d4d5201e7
  | 29 => 0x34dd73d894318eee42d894318ede32d894318eee32d894318edc32d8943004ff71d894300cfe71d8943004fd71d894300cfc71d89430067f51d89430067d51d894318eef21d8943006ed21d8943044fe70d8943004fd70d894315edf30d894318eec20d89430057f75589430057c75589430067f65589430067c655894318eec62589430067f65d81430067c65d814303cfe75d8143004fd75d81430d6bd74d8143034fd73d8143014fe72d8143004fd72d8143014fc72d8143004ff71d814300cfe71d8143004fd71d814300cfc71d81430067f51d81430067d51d8143006bf41d8143006bd41d81430d6df31d8143006dd31d8143006ef21d8143006ed21d81430d6fa30d81430057e75981430057d75981430067f65981430067c6598143006fb60981430057f75581430057c75581430067f65581430067c6558143005ef725814318dec7258143005f77158143185f471581430067f65181430067c6518143006f9601814303cfe7518143004fd7518143034fd7318143014fe7218143004fd7218143044fc7218143044ff711814300cfe7118143004fd7118143044fc71181430067f51181430067d5118143006ef2118143006ed2118143046df3018143046fa301814308ef93018143014fc755935203e7c75593520147c755935203ebf745935203ebf545935203e7c545935203ebc5459352004ff735935201cfe735935201cfc735935203e7f53593521e67e525935203e7c52593521e6bf4259352004ff715935200cfe7159352004fd715935200cfc715935203e7f51593520067d51593521e6ef2159352006ed2159352004ff7059352044fc705935203e7f505935203d7d769535235e7d76953521e47d769535203f3e749535203e7f649535235e7d64953520057d73953522067e639535203e7c63953520157e72953520157c729535235d7f719535250d7d719535203e7f61953525067d61953521ff6f21953525076d21953520057d7095352014fe7558f52014fc7558f52004ff7458f52034fc7458f5203edf7358f5203edf5358f5203edc5358f5217ede4358f521aedf3258f52004ff7158f5200cfe7158f52004fd7158f5200cfc7158f5203e7f5158f520067d5158f521aeef2158f52006ed2158f52004ff7058f52044fc7058f5203d7f7654f524767f7654f5247c7f7654f5235d7c7454f520067d6454f5203f5f7354f5201e7e6354f5201e7c6354f5217f5e4354f520157e7254f520157c7254f524fd7f7154f524fd7d7154f5203e7f6154f524f67d6154f521af6f2154f524f76d2154f520057f7054f52034ff76d0f5203cfe76d0f52004fd76d0f5235d7f75d0f5203d7c75d0f52036be64d0f52006bd64d0f5235f3e54d0f52015ee72d0f52005ed72d0f52004ff7650f52004fd7650f5203cfc7650f520057f755
  | 30 => 0xc431954303e7f721954303e7e721954303e7d721954303e7c72195435567f42195430067e42195435567c42195431d67f32195431d67e32195431d67d32195431d67c321954303e7f711954303c7f711954303e7e711954303e7d71195430047d711954303e7c71195435567f41195430067e41195430067d41195435567c41195431d67f31195431d67e31195431d67d31195431d67c31195430067f21195430066f21195430067e21195430067d21195430066d21195430067c211954303e7f701954303e7e701954303e7d701954303e7c70195435567f40195435567c40195431d67f30195431d65f30195431d67e30195431d67d30195431d67c30195430067f20195430067c20195430067f10195430067e10195430067d10195430067c101954301cfe76d514301cfc76d51430067f65d514303e7c65d51430373e54d514301dde73d5143005dd73d51431d5be7695143036be76951431edbd75951432073f659514303ebe659514303ebc65951430073c659514303e3c65951430379f739514301dbe739514301dbc73951430379c7395143036bf63951430379f63951432073e53951432079e53951432071e53951432073c5395143005bd729514354f9e32951432079c3295143035bf7195143545bd719514353f3f519514353f3d51951432079f319514353f9d319514353faf219514353fad2195143005be70951432079f309514303cff765514301cfe76551431ecfd765514301cfc76551430067f655514303e7c65551430373c5455143005df735514301ddc73551430379c435514301dbc765514303ebc765514301cbc7655143035bf75551430373f75551430073f655514303ebe655514303ebc65551430073c65551430079f735514301dbe735514301dbc73551431ef9c7355143036bf63551430379f63551431ef3f53551431ef9e53551431ef3d5355143005bf72551435373e52551435373c52551435379e32551431ef9c325514352dbf715514352dbd71551435273f51551435273d51551431ef9f31551435279d3155143527af2155143527ad2155143005bc70551431ef9f3055143035dc7654d4303edc7654d43034dc7654d4301ddf7554d4301f5f7554d430075f6554d4303ede6554d4303edc6554d430075c6554d430079f7454d43035de7454d43035dc7454d430079c7454d4301edf6454d4301f9f6454d430075f5454d430079e5454d430075d5454d430079d5454d430071d5454d4318dde7254d4318ddc7254d4351ddf7154d4351ddd7154d435175f5154d435175d5154d435179f4154d435179d4154d43517cf2154d43517cd2154d43005df7054d43014fe76d89430067f65d89430067c65d894301dde73d894318eee62d894318fce32d894303cfe75d8943004fd75d894301cfd74d8943034fd73d8943
  | 31 => 0x834303cfe76d9543034ff73d9543034fd73d95432067f53d95432067d53d9543014fe72d9543004fd72d9543014fc72d95430067e52d95430067c52d9543004ff71d954300cfe71d9543004fd71d954300cfc71d95430067f51d95430067e51d95430067d51d95430067c51d9543006ef21d9543006ed21d9543044fe70d9543004fd70d954303c7e76d95432073f74d954355f5f73d95432075c73d954355f5f43d95432073e43d95432073c43d95432075c43d95430067e62d95430067c62d95430075e32d95432075c32d95430057f71d95430057d71d95430067f61d95430067e61d95430067d61d95430067c61d95430073f41d95430073d41d95432075f31d95430075d31d95430076f21d95430076d21d95432075f30d95432067f74d954355e7e74d95432067d74d95432067c74d95432067f73d95432067e73d95432067d73d95432067c73d95432067f43d95432067e43d95432067c43d95430067f72d95430067e72d95430067d72d95430067c72d954355e7f42d95430067e42d954355e7c42d95432067f32d95432067e32d95432067d32d95432067c32d95430067f71d95430047f71d95430067e71d95430067d71d95430047d71d95430067c71d954355e7f41d95430067e41d95430067d41d954355e7c41d95432067f31d95432067e31d95432067d31d95432067c31d95430067f21d95430066f21d95430067e21d95430067d21d95430066d21d95430067c21d95430067f70d95430067e70d95430067d70d95430067c70d954355e7f40d954355e7c40d95432067f30d95432067e30d95432067d30d95432067c30d95430067f20d95430067c20d95430067f10d95430067e10d95430067d10d95430067c10d95430067f65995431edbd749954321dbf74595430067f755954321cff7459543006bf74595431ecff7359543006df7359543004ff7259543014fe7259543014fc7259543004ff715954300cfe7159543004fd715954300cfc71595430067f51595430067d5159543006ef2159543006ed2159543004ff7059543044fc7059543204fe761954303e7e65195430067d65195432057e76195430067e76195432047e76195431d73d74195431d75e73195430075d73195435575f43195431d73e43195431d73c43195431d75c43195430067e62195430067c62195430075e32195431d75c32195430057f71195430057d71195430067f61195430067e61195430067d61195430067c61195430073f41195430073d41195431d75f31195430075d31195430076f21195430076d21195431d75f301954303e7f741954303e7e741954303e7d741954303e3d741954303e7c741954303e7f731954303e7e731954303e5e731954303e7d731954303e5d731954303e7c73195431d67f43195431d67e43195431d67d43195431d67
  | 32 => 0xcfc71d89530067f51d89530067d51d89531aeef21d8953006ed21d8953044fe70d8953004fd70d89531aeec20d89531aeec62589531367d75d8153034fe74d8153004fd74d81530067f54d81530067d54d815303cfd73d8153416df53d81531367e53d81531367c53d8153136dc53d8153136de43d8153014fe72d8153004fd72d8153014fc72d8153004ff71d815300cfe71d8153004fd71d815300cfc71d81530067f51d81530067d51d8153006ef21d8153006ed21d8153136fa30d8153006fb6098153005ef72581531adec7258153006f96018153034fe7418153004fd741815303cfd7318153014fe7218153004fd7218153044fc7218153044ff711815300cfe7118153004fd7118153044fc71181530067f51181530067d5118153006ef2118153006ed2118153046fa30181530eef930181530367f755974301cfe745974301cfc74597430367e54597430367c54597431ee7f53597431ee7d5359743036de4359743036dd4359743004ff7259743014fe7259743014fc72597430067e52597430067c5259743004ff715974300cfe7159743004fd715974300cfc71597430067f51597430067d5159743006ef2159743006ed2159743004ff7059743044fc7059743035bf7655343006bf76553430373f75553430373f655534303ebe6555343036bc65553430373c655534301dbe735534301dbc73553431ef3f53553431ef3d5355343005bf72553435773e52553435773c525534356dbf715534356dbd71553435673f51553435673d5155343567af2155343567ad2155343005bc7055343004ff7558b4303cfc7558b4301cfe7458b4301cfc7458b43036ef7258b4319eec5258b43036ef4258b43036ec4258b4319eee3258b43004ff7158b4300cfe7158b43004fd7158b4300cfc7158b430067f5158b430067d5158b4319eef2158b43006ed2158b43004ff7058b43044fc7058b4319eef2058b4303cfe7598343004fd759834301cfe7498343044fc7498343014fe7298343004fd7298343044fc7298343044ff719834300cfe7198343004fd7198343044fc71983430067f51983430067d5198343006ef2198343006ed2198343046fa7098343036fb4098343046f84098343046fa30983430bef93098343046fa1098343006f91098343004ff75583430067f75583430047f755834303cfc75583430067c755834303c7c755834301cfc7458343036bc745834301cbc7458343036de4358343036dd4358343004ff7258343014fe7258343014fc7258343036bf4258343004ff715834300cfe7158343004fd715834300cfc71583430067f51583430067d5158343036bf4158343006bd4158343006ef2158343006ed2158343036fb7058343036fb4058343036bc4058343036f840583430aefa3058343006fa1058343006f9105
  | 33 => 0xd715535303e7f615535359e7d615535359f6f215535359f6d21553530057c70553531ef5f305535301cfe7558b5301cfc7558b53004ff7458b53034fc7458b5303eef7258b5303eef5258b5303eec5258b531beee3258b53004ff7158b5300cfe7158b53004fd7158b5300cfc7158b5303e7f5158b530067d5158b531beef2158b53006ed2158b53004ff7058b53044fc7058b5316edf3058b5301cfe7598353044fc7598353034fe7498353004fd7498353014fe7298353004fd7298353044fc7298353044ff719835300cfe7198353004fd7198353044fc719835303e7f51983530067d5198353006ef2198353006ed2198353046fa709835303efb5098353046f85098353046df3098353046fa309835311ef9309835301cfc755835303e7c755835301c7c7558353004ff7458353034fc745835303e7f54583530067d545835310e7e535835303e7c5358353004ff7258353014fe7258353014fc725835303e7f5258353004ff715835300cfe7158353004fd715835300cfc715835303e7f51583530067d5158353006ef2158353006ed215835303efb705835303efb505835303e7c505835303ef8505835310efa3058353034fe76d915303cfd73d915321ebf43d9153014fe72d9153004fd72d9153014fc72d9153004ff71d915300cfe71d9153004fd71d915300cfc71d91530067f51d91530067d51d9153006ef21d9153006ed21d9153044fe70d9153004fd70d91532067f6599153006bf64991531adee7299153005ed72991531d67f6519153036be6419153006bd64191531d57e76d515303e7e76d51531d47e76d51530367e64d51530367c64d515303f5f73d515301d7e73d515301d7c73d515303f5c73d515303e7f63d515303f5f63d515321f5e43d51530057d72d51532167e62d51532167c62d515303d7f71d51535957d71d515358e7f61d515358e7d61d515358f6f21d515358f6d21d51530057e70d515301cfe76951531ed7d75951532067f6595153006bf6495153036bc649515303f3f549515301dde7395153005dd739515301cfc7655153006bf6455153036bc645515303f3c5455153005df735515301ddc735515303f5c535515301d7c76551530367c765515301c7c765515303d7f745515303f3f74551530073f64551530367e64551530367c64551530073c64551530075f735515301d7e735515301d7c73551531ef5c735515303e7f635515303f5f63551531ef5e43551530057f72551531e67e62551531e67c62551535857f71551535857d715515357e7f615515357e7d615515357f6f215515357f6d21551530057c7055153014fe76d89531aeee62d895301cfd75d8953034fe74d8953004fd74d895303cfd73d89531aeee52d89531aeee42d89531aeee32d8953004ff71d895300cfe71d8953004fd71d8953
  | 34 => 0x8c541d65f7558c5403ede7558c5403edc7558c54036df7458c54036de7458c54036dc7458c54036df5458c540365f5458c54036de5458c540369e5458c54036dd5458c540365d5458c5403e9d5458c54036dc5458c54006df7258c54006de7258c54006dd7258c54006dc7258c5403edf5258c5403e5f5258c5403ede5258c5403edd5258c5403edc5258c54036df4258c54036de4258c54036dd4258c54036dc4258c54006df7158c54006de7158c54006dd7158c54006dc7158c5403edf5158c5403e5f5158c5403ede5158c5403edd5158c540065d5158c5403edc5158c54036df4158c54036de4158c54036dd4158c54036dc4158c54006df2158c54006cf2158c54006de2158c54006dd2158c54006cd2158c54006dc2158c54006df7058c54006de7058c54006dd7058c54006dc7058c5403edf5058c5403ede5058c5403edd5058c5403edc5058c5403e5c5058c54036df4058c54036de4058c54036dd4058c54036dc4058c54006df2058c54006dc2058c54006df1058c54006de1058c54006dd1058c54006dc1058c54004ff735885401cfe735885401cfc7358854034ff7258854036ef725885403eef525885403eec5258854036ef4258854036ec4258854004ff715885400cfe7158854004fd715885400cfc715885403e7f51588540067d51588541ceef2158854006ed2158854004ff7058854044fc70588541ceef205885401cfe7398054004fd7398054044fc7398054014fe7298054004fd7298054044fc7298054044ff719805400cfe7198054004fd7198054044fc719805403e7f51980540067d5198054006ef2198054006ed2198054044fe7098054046fa709805403efb5098054046f85098054036fb4098054046f84098054046fa1098054006f910980540367f54580540367d5458054004ff735805401cfe735805401cfc73580540067e535805403e7c5358054004ff7258054014fe7258054014fc725805403e7f5258054004ff715805400cfe7158054004fd715805400cfc715805403e7f51580540067d5158054006ef2158054006ed2158054036fb705805403efb505805403e7c505805403ef85058054036fb4058054036f84058054006fa1058054006f9105805401cfc755935303ebf745935303ebf545935303ebc545935303ede535935303edd53593531eebf4359353004ff7259353014fe7259353014fc7259353004ff715935300cfe7159353004fd715935300cfc715935303e7f51593530067d5159353006ef2159353006ed2159353004ff7059353044fc70593531eedf305935303d7f76553530067f76553532047f765535303f3f745535303f3f64553530367e64553530367c645535303f3c645535301d7e735535301d7c73553530057f72553531e67e625535303e7c62553535a57f71553535a57
  | 35 => 0x6ed2158a54004ff7058a54044fc7058a541feef2058a54034fe749825401cfe7398254004fd7398254044fc7398254036bf4398254014fe7298254004fd7298254044fc7298254044ff719825400cfe7198254004fd7198254044fc71982540067f51982540067d5198254006ef2198254006ed2198254046fa7098254036fb4098254046f84098254046fa1098254006f91098254034fc74582540367f54582540367d5458254004ff735825401cfe735825401cfc73582540067e53582540067c5358254004ff7258254014fe7258254014fc7258254004ff715825400cfe7158254004fd715825400cfc71582540067f51582540067d5158254006ef2158254006ed2158254036fb7058254036fb4058254036f84058254006fa1058254006f9105825401cfe76d8d541eede63d8d54034fd75d8d5403cfd74d8d541eede53d8d541eede43d8d54014fe72d8d54004fd72d8d54014fc72d8d54004ff71d8d5400cfe71d8d54004fd71d8d5400cfc71d8d540067f51d8d540067d51d8d54006ef21d8d54006ed21d8d54044fe70d8d54004fd70d8d541eedf30d8d541eedc6358d54014fe76d895403d7e75d89541e6ee62d89541e76e52d8954034fd75d89540347d75d895403cfd74d895435e7e54d895435e7c54d895401cfe73d8954004fd73d895401cfc73d89541e67e52d89541e6ee52d89541e67c52d89541e6ee42d8954004ff71d895400cfe71d8954004fd71d895400cfc71d89540067f51d89540067d51d89541e6ef21d8954006ed21d8954044fe70d8954004fd70d89541e6ec625895401cfe73d8154004fd73d815401cfc73d8154014fe72d8154004fd72d8154014fc72d8154004ff71d815400cfe71d8154004fd71d815400cfc71d81540067f51d81540067d51d8154006ef21d8154006ed21d81541edde7398154005dd7398154006fb6098154006f960181543167e54181543167c541815401cfe7318154004fd7318154044fc7318154014fe7218154004fd7218154044fc72181540067e52181540067c5218154044ff711815400cfe7118154004fd7118154044fc71181540067f51181540067d5118154006ef2118154006ed21181540367f5458c54036be5458c540367d5458c5403ebd5458c54034ff7358c54036df7358c5403edf5358c541d67e5358c5403e7c5358c5403edc5358c5403e5c5358c54036df4358c54036dc4358c54004ff7258c54014fe7258c54014fc7258c5403e7f5258c541d6df3258c54006de3258c541d6dc3258c54004ff7158c5400cfe7158c54004fd7158c5400cfc7158c5403e7f5158c540067d5158c541d6df3158c54006de3158c54006dd3158c541d6dc3158c54006ef2158c54006ed2158c54004ff7058c54044fc7058c5403e7c5058c541d6df3058c541d6dc3058c5403edf755
  | 36 => 0xc5458b54004ff7358b5401cfe7358b5401cfc7358b5403e7f5358b5403eef7258b5403eef5258b542167e5258b5403e7c5258b5403eec5258b54216ee4258b54004ff7158b5400cfe7158b54004fd7158b5400cfc7158b5403e7f5158b540067d5158b54216ef2158b54006ed2158b54004ff7058b54044fc7058b5403e7f5058b54034fe75983540347e759835431e7e549835403e7c549835401cfe7398354046de739835401cde7398354004fd7398354046dd7398354004dd7398354044fc739835403e7f5398354014fe7298354004fd7298354044fc72983540067e529835403e7c5298354044ff719835400cfe7198354004fd7198354044fc719835403e7f51983540067d5198354006ef2198354006ed2198354046fa70983540467f509835403efb5098354046f85098354034fc7558354004ff735835401cfe735835401cfc7358354004ff7258354014fe7258354014fc7258354004ff715835400cfe7158354004fd715835400cfc715835403e7f51583540067d5158354006ef2158354006ed215835403efb705835403efb505835403ef850583540373d76d52540353d76d525403e3d76d525403f3f73d525403f3e73d525403f3d73d525403f3c73d52540373f63d52540373e63d52540373d63d52540373c63d525403f3f72d525403f3e72d525403f3d72d525403f3c72d52540373f62d52540373e62d52540373d62d52540373c62d52545bf3f32d52545b73e32d52545b73c32d525403f3f71d525403f3e71d525403f3d71d525403f3c71d52540373f61d52540373e61d52540373d61d52540373c61d52545af3f31d52545af3e31d52545af3d31d52545af3c31d52545af3f21d52545af2f21d52545af3e21d52545af3d21d52545af2d21d52545af3c21d525403f3f70d525403f3e70d525403f3d70d525403f3c70d52540373f60d52540373e60d52540373d60d52540373c60d52545bf3f30d52545bf3c30d52545b73f20d52545b73c20d52545af3f10d52545af3e10d52545af3d10d52545af3c10d5254034fc7458e540367f5458e540367d5458e54036df7358e542067e5358e54206de5358e542065e5358e542067c5358e54036df4358e54036dc4358e54004ff7258e54014fe7258e54014fc7258e54006de3258e54206dc3258e54004ff7158e5400cfe7158e54004fd7158e5400cfc7158e540067f5158e540067d5158e54206df3158e54006dd3158e54006ef2158e54006ed2158e54004ff7058e54044fc7058e54206df3058e54034fc7458a54004ff7358a5401cfe7358a5401cfc7358a54036bf4358a54036ef7258a541feee5258a54036ef4258a54036ec4258a54006ef3258a541feec3258a54004ff7158a5400cfe7158a54004fd7158a5400cfc7158a540067f5158a540067d5158a541feef2158a54
  | 37 => 0xc0000050001000800000040030000000001000000140140008000000c001002400500000110000003001c000000800c00040010008000001400c0014000001000800040000004003000c004000800200080020004000000000400000030004002000000000000000004006000400300000020000003000c00f00a0001000000000040060018004000400a000c009000400000000000004003000000000000000014005002c005001000e0004003000401200140000010000000001e000c000001000000140040000008003c00d00000050000000004800f0008000000000400000050014007000c00100300000010000000c0010008000004c00000140000018006000c00000080010000003000000100000040018002000c025000000100300000004001000000500040090024008000400100300050000020000800000180060000000000400c000c001000400a000800500040010000008015800200040010000011000000600640060008004000c00600000010020000000800300040060004000000400700040060004002000c00500000110000000000400600000070078003000801c0040001000400200000020014001000800000000000000001004c00200000050034000000000000080000014000001400100080090000000002801400000000000001001400000000000000000001c00d000400000000060000021000000900240000000002000c000000401100040000008000003400700000050030005000800100000110020000001c0080008004002401f000c00200080000030001001001d00080010074009000000d000004000040010000000000000300140060008003000001000080000000001001801f000000000000000028000002401300180000018001000c01500200080004003001000a000000400180090004004000c010000400c00100020004001000000c0008007001000000440000000005005c002000c00200000010000000000000100480000004000002c003001000a00080000038004000000500080010038000000000300180010028001000800800040090000001000c00100000030004009000000100040040000001001400200280030000000000800100080130000005000000100000340008000000401e000c004000400e000c005000000000140000008001000800000040040008000000000000100000000000000000100180030000002034fc7558f5403ebe5458f5403ebd5458f5403edf7358f5403edf5358f5403edc5358f5421ede4358f54004ff7258f54014fe7258f54014fc7258f54004ff7158f5400cfe7158f54004fd7158f5400cfc7158f5403e7f5158f540067d5158f54006ef2158f54006ed2158f54004ff7058f54044fc7058f54034fc7558b540347c7558b543567e5458b5403e7
  | 38 => 0x10040011000c0000024000000400700000030000000001c000000000000040000000023000400a0048000000000200200040000009000400000000050008002000000000440000034000000400200000040008001000000f00000000000036000001c0020004000000100040020014000000400c0004000001c0010000000001c002002800a0028001000401400000010000000003c00200000010008000000000800680000000005005000100100000014001000800500040000024006004000300000010004003001800200580000014006004000700400020038005000c000000000500100070004000005400000140000000006000000f0000001005400200280010014006001400000100040010000000400400000010010002001000a0004005001c000000000100000020004000000400000000000008000000000b0008003001400500000070008004002400300100010000002000800900000050004003000c0000054000002c000003800100080010044002000001000140000008014000c0190014000000000000100010004001000800f001800400a00000000006000000b000800700140000000000000c0050008005001002d001c00100140000000001000000b00040190000007005000100180030030004000800d00080010000000000001400100060000009000400000240000000000000c0000018007000800200340010000000000c00200500000000001000c00301700000004000007c0010008003000800800000000010001000400000000050008000004000900000000000002004400b0004000001800000100000008002000400100300060020006000c0030024002000000000040000010000001c000005c0010004000001c0060060000000c004002400b00040000000003007c000005c00100000030058003000001000000010020000000400300240000048003000000400000050008001000c00200180080014032000001200000010048004002c00000080130000003000c00200040000028000001c001000400000140020004001000000500040020004003000c000000000b0014007002c0060018003000000c001c0000014020005400a0010002001000b001c000000800100000060008006001000000440010030001001c0030000015003400100000000004003000c003002400000100010000005000000300140040080000000000900080000004006000000100000030044007000000000140070000005007000000040030000000000000000000040000000000000200380000008000000c000001c0160018001001000b0000000000800c000401900080030004003000c00900040000000004002c0000000003001400900480000000007000000b00100060054005000c000001000000180000014003000
  | 39 => 0x40000003003800100000000000003000402c0030004000000000000060000000000c003000000c000800200100030004002001000200080030000003000001000200100008008001400100080030008002000000700140010000000000c0090008004000c0020008000000000200000000008004000c00d00180000000001000800500080050030014000c0010038001001c000000000e002c01600040030000002002800100080030000000000c000004c01b0008008000000000000000000002001800200540050014004001c005000000400000070004009000000000340000008000004800000080000008000000401600080110008000001c0020000000000c0000000002001c00a00280010054004000000200240040000000000000a00000000008002004800e000c005000001800100040004000000000000080000000004000000200080000000004004400200340000040002000800000100050000005001000a0000004000000000200040024001000c0000000003000001200080020000006000c0050010001002c0050030005001800100000000000000000401d003c0050028013002c0000000000000c001003400300080070030031000000000100030004004005c05a00880020000002000c001001c00200000070014003000400000080010000002000001c006800100080010000000000c0020018005000400200000040000000002000300040020020000000400b000400000180000000000000000b0000004001c0000028000000000400440010004000000400700040010014000000800100080020004000012800c001800c002400000040020000000000c006001c002001400000640030018004000c004000000300100000010005000c000003c000000c0050010000006c005003c001000400000000030000000005400800040000008003003400e007800100180040008003000000a0008000000400200040020000010001800100140000018003001c004000c00000040020000000002800000000010000000000800700280000000000004400d00140250004001001c0010060002000000a0064000000400000000010014003000c0000000003006400300740050084001000c0010000002002003e003c00d00040000008009000001000080050008000005400000240010014001001400300100010000014000000500080060010001000800000200000000015002400000000030000000000000100000070018002000c0020004000001400b003000100300090000003005800200040010000006000400800040000028012004000000080030000004000000200140040004000000c015001000d002400100240030008000000c005000000000c00020004003000c0110004002000000200000000000008000400
  | 40 => 0xfe6190d6c6c4800011686363a180004cf108e623005862d94f06f78bd611784304c396ee02811ae000174c83700004bd13f0000284e8438c3e4ef8aa200007300001eaa000191e4ed20a00001c54bc3029200000000002478c489710000196a9d424385e2130c462b062149a482a0500002f000008450000754948458b1baa120014800000007e5000000027ac00000000002aa20001c0aa46abf200008a80338a389e499e600011160000000000273a00010bc4101fa27820c86000000038a0bce9630000508079400000003ad2caa2d20a5ca7594fe00000000002a820000b5477480004cb949200004642838b2277080009fa0d4abaf0c9037084b20000000a3d09f60014007000000100a40030028001000c00a000400000000000014006000800000400030000000006000000000030014000000800100040010014003000400100140010010009002800a0004006003400000080050004004003400a000c005000c003000c00e0010000001400000400010004000000800400000000004005003800000040000014002000000000000010018003000000000180040000000001000000540000010001000000300100000008005000000b00300000018001000400000180030000000000c005000400200000030010000000800200000010014000000000a000401500040010020000000c0000024003000000000000040038020000400100540140024000005400c0024003000c0030000012001c0000000001000800200200020004001000c00000000030004012000400100080030000000006800000000140044016004c0030050016000000b0018001004c0000000000000c001004800100080020000001000400300a800000100000020004000400000100010000009000800000400000030007000400c0024001000c00600100070060004000400200ac014002401200040000020008003001300080050014006000800000000020000000000000400040000008007000c00000000050018001002400000080020000000000400000200000014000002c0010000000005c003000800000200030000006000000000180020014004002000c0038007003c00a0000000000000300080010000009000c0040028011000000b00000150000006000000100000030008000000c0090000003000c00800000040004001009800200000070000013000c0000020000001000100200000030001000000c0000001000000000200000044005000000000080000000000000001400180000010000000c000001000700000000030016000801c00000190004006002400200140050000005000c000000000100000000000001001000100080010010000000000100a00180020000002400000200000034006005400a000c002001c00c0000001004400a00
  | 41 => 0x1e060002c7044503fa0000382000000092d80000001b1c000000015a000000000000001b1e81e286eabc0b58103ad2655a80007e1afac16e9eb6058a9280002d7a00000009ee8000a1900003f7ab3615b0000267800057f8c6c00000000000000000000070eab8a96a16b000030240000c2600000007b41be4000137e000057e000000026b0fb4000000000000000001bb8317896a475967c00000000002f2000003467be90222dda8382af1ff887d802a433970c54d03da86080004d5000093f000054480009ca000000000002cb15ac1f8aaf47cf80003c6979a734042200028aa42980007ea80000000cb8bf980005ca80000000ef83da8bf6a91000024802faac718a6c2093cc19d88c83b981ce8668f02103112200000000d700009f920de000000063e1c16000000000000008188000000109e4ca2d88000000022586a20001bd6444800000029da4ac80007c99d6600000007a291e0a860000000000000004a0000000050d18bc9971b3a7e6800094b083400000008f20d9aa1499340002d5e0001afc4ed86ce3e3068249e99fa7da00d29e18e1095d13ca1eaa6d4abf8394911812e2d42ba6bb225186aa1336c500bd8a960c34572aefe1c2105e3058c80808af2c1be9bdca8809d66a3000000000000bcae80487000000030b887004b04ff1bee167015abc5a76000002dc00000006a680000000000bb1000083e991a397981c66d90aead41b868f7956ea990cc230b82f0703b0365c700e8558204e16790f0ad2803ac25242e5bca1920b30e82c0c0022b9a8b7abd7000000016d800015f66ce29b263806f247ea55620f9ea890fa47441085c882f20520000a466ee893218d000000000000000a54c572368182a39e16b950e000201c926a6ce90726dab9200000000000c2403e68310000115218466c842aa49943c34b0f760000314000000007e80000000ba255c000000001887cf165090f08e81bd8a0c0f72fee71a916404b26c637d0e0458015541d8adf674f275456c92e40000180b608000747a69cb261b1400009b451d8000000000000000000002c5cb462e2e00007660002c8c4b80000736945a60c11566ec1b0446900000ac800013414561091660b14800098d1d9470319c4730a79a2c5a85c3d92460a4d30e69d4ac12156291e8afa9a01180a3039ca8eca0980006261e6a4c59c44ab708e46f8990e9a82be29962d1e20c000000014b0000316e000151c2860e742d80fd800000000000000000000018b00000001b8000000004ea800032bad0ca3503f000003b09890ec600004c4698827cc5885648a42aac0000fbe5ee8576228800039680000001cba6e483f2000020605c9af60002cbc00015d600002ec00000000000000adeb13e00027dc01816c06b8ab0094d888a6b31d8a0001262b510810333800039a28e8772ab
  | 42 => 0xeb0841ab2e84e8ce4000128436d0000000000059b00009f3acde0001c623520332000271035d80000000000b74800012babea0000000a2c9a9c1ed9a1a84f85b08fb80001c7aace00012360438658b9a2f14000314899f877a00000000000596000260a07580000000000b9e80001a6a6981e68f4e7a393740000dc68fa2874bee0e5c2c1000000011808b8a1360000becb8000005c6854c33a80002138000a0f9e78060ab1a0f191e40001c6c19300006d7b1048f08e30000204800021660353038000013c8d52c3c2540002495a85600021b89e22f9c761090400028243e18c500000000b1a80000000000000000022f0000000000060f80000dd000000019d847419a80001e44c46855072f9dd400001e66a9858044e21e236d9dba5a7289c0001fae8dc990c6340000000185200000003dbac503eb00000000000a28800000000000001a5a0000000000000000000000ff942800000000000000014178a6af06f4b3e8000523868623800007672652279000000000007e29ce299a97ce3f300003df800020607705db1e165f6880cbc0a2ae5d18c880310320592204a6722eb439093f893c98328b9055a1d200008e613461e087d2000276e00c19c25d9967821a01e40730b8c57babbc00000001a980001fc8e44c4e224c00000000000000000034a0001706000298a00000004aa8000490000000000007412100c4c8000273b0163fa0000319a3308670000bd50eda934a6f80000000000192a2b500007af12d22010d4c2a980009fba15a0002b7e0000000aab8f542261d580001de2000109a000000e000000076d1508000000003d00005f5312c66f0000ad50000000000000027b26de88ae0000000916063800013bc3d02662adc8000a42000000000002579196000123200000001770a42842800057d20287da80002da288e9d3244e13a8000000000009427762e62b401f2adc40001fe85e7050a0001bce3de839677c1f048e0aab4280019e63b2ca0c15ad0a0a5adbe3f8934ea8e2a969d128f200000004e284ac0518000610a57c67a9c08a7e80006698000bed2dc603a8dc05bf1f2a0000000a4f00000000000a3a927600000003890edc838000006e3088b39a2d00de04ee1f903c8395b06677d00000000000000076038d069c000108000000003d30d569ab025650b0d2062a1a4c73200003d5b0c8bef97a6ab292100a3236e26f2ce817c8000c21a072000000000000005178fca8ffae6e7d919200d0129400000006948000b6c14a000022ee0000000a518000000030800019048c0228400008dc85d2fc08f8af660efaac229d8776657aa74b84000086c000000008cc0002a76a020764b3491bc5480de800000007f00000000000003e29ac2581d1400000002baa520c2904942a80d2206b800098626002ef144c0000000000096c0
  | 43 => 0x907abfc0000baa4c621300001ebe49428040f300003e6980e0ad9fd862e20be7d317785f7000000000000000000000000069580000002f085d88000000025e608a46c00027481f1955600000f6a8c836625b9c640000d8409ca14e3d2000000000000001bfc0aa26ca0000000000000077918e466c2cdcbbf0000000000072d80000002c5442a000058300009f60f46b0180000001ca6263074c85330143078bee3d28ed0c269b08862abb2ad30df8404800051b000013a159851386b64920f685789ffe3cb044a7ef28849d69d9e11d80009c4921ea45054629b18d6a41800094788be8a3859a0000dfe7c69d8ea22ada81242490000088467916420001d7aa92000077709fa78303bc7db8c2a65da392ae704a24c08000b08ad2c25d2694000072eab612ae7dfb03e14496367a505040000ee200031028bf931e7a58000351a64a33d18066e400006e22d644162cca8dead8a0000000000000051f2e5c00000008dd877c77e0eba000012233e80000002a5a0000826000000029e0000000000080c18b0000079800000003dd0000500b03c6020000000000051c8b92a1f8000b820f143f9212800012f60000000a1e164e0000c8eb58a38a79817bc8f6867ab838d140000b4a00000000000000b07800054f80002e199703630fa486f99d000029a294cac6800020c8000072657e2818600abc40001a384df1462226a282bc92b3a632000050e871063c21caa6a80001b2000000028660000000000227600005c632e89a0000000049112d000000001bf0000000000014c00004218000000000000000002ee80000002646b0100009e5167aab680008992f463560738b06000067a000000014d21473096a9f80000000000b97800001500008ae02d83e227e05ca1a200000000c3a0ae04d5a1f84a6000072180000000000c42a8a800000000002e0c00000004ae0000489aa241da812a000000000030c0000000056f0ef6ad893fa00024ce0060000ac4a218000000000011ca0002a9c27e10b200000ee38b8aaa000013a00000000000000bf6a4b80800cd6c3faf825031290b699de8884987c0001cc08e180005e79b9e0f624185fd80000000000000119a74b800000000009b480007ee8000c00800000015e000000001e329dcb5d8000000000000000005c495c621e8072537000000024000001c0600000000000000000065cad608766f817cc7c380000000000b3209224672d3600000000001cf04f4800000008329e90000512a35e3999ceeb928000000032e9f880000001d181c50000000061a00000800000000000177632b018e1682dbc98f809e34ba61079d1f14000000088880008a30b9a1d39ede1801fb272a14c678cb02a0000000525b170789127c3ec1f2093a000000023c00000e8c9ec1a6e22b0ea28f399ac0002168064a5ea8870
  | 44 => 0x8f30b9c9946196a55e3928ea0af99532047908831212343d4214800000002cc0a04660240e2ba0000a722918bb08e58a0c8000000000045a11ba0000000000000000029588d11c7a4f1a48a000000003b06a4000000000013703f580004b322de0892ac600016e0a302c567432aee0002e648881da811a27580001dbc00000005cf03d6223800022e13dac1a201e00007ea0ac00000000c5a0000000c580000c5e800055700000000ec00000da80000dd45048aac0002e3436980000000000000000025307fe0000326000021c5af8536b3087a09f22c147d10a281ef80000001b0c282b17c30d88580002370c2c0e0ea66aa6a0002d165590000000173015c299e0000000ad700001ea30be00000000002d1000000000000000000000029b895aaaa000049b8000000003656423360000cb402ea31c00022c0440800000020d00000a6a272000035e1968bb180000000000000130600024723a4ae42427211211fa2f479b1aea33b8a8a0000000000188453e9a16388269a4e722dcc0800003a127aa60eaacc00008a60000440bec2a620001a009a98864b2a2dfaa7a02286901d1c0001e0a41321fe82c162200022242f20000266070057302fc4d680005e1ac9013c06f80378c0690899f80000000b5c92ea4949dfc000000068c1dc400009929f98ed6b4c8264a2b1e3c0000392000039e4801060000234a00000008ec93003088000b9e249c7c0a03838f0a1c0001b58b7511c6b65891600000b4000000065e09fc000000000010f65f009669322ecca5b9574000000000020060000000000000009a29eec06a14a65e800000023a05aa103237700009121bd469a8000b2396ec83b042641ca80c6c88000050272023a8b6c88213b200000005e89e30037000019ca43086f28f63830000b538dda000082433f1bb29150e0037824d08548ba63baade0bfc1daa8590eb6622a394251ac323c91736205989c10f97fa0000882000286a80682e651c21cc23405a64e0aaa407d800000023500000c82000000000000007e801ba00000000001f4000008089980a3c000297e00000003b510b64cf8f520000e6c00000005c0ac6469280008d39af837dae1698f235247fa2d88470dbc0000000a4f800000006d458696ca86780008cfadee0000ac800000000002e2c5840000c4a24ba95e80006a898385a48000000000090c9cfa365800047e0fc806c0f3c953311600000005ac82de184af124be80089ae80004fd1f08206952850b8b960002c9c3f0800090319f6000000000017209bb9ce42b89c1eb3321ce7ce1b1604922ea2358af44e8073c00000003f1ab8429402300001a180000000000000083a81e27d500000d31a4281928e02d131066d9800000018181d683448b105a29e3800000004de31a000000009189f511009c111829b90fe632d83ba
  | 45 => 0x2000000000024ca58480006d700001350000000000000000001139df60000000b03800000008fe0002c3e00029e00001fc6000000086c8000000000078800008aa008e4cc000051000006520000bb50d7233330800000000000000083c000092580005418000480a8f80231136c30a1a600003c0606800000305165ed90020000a741af88a40002b32c5b184088e93ec1e8a3e0a7c140a0001b986d5ae8444c185a00003ae2ae815c2dbab70503a22c0e60000031a9cea9b80000000000000000087601867732668c1716ea3d608ca155252876c20d2a6b800079500006a4985ca2316183380b0e4c51784000289a0eb0000bf4987a06d80002c8307233700002438000bc10db8b4200560000000000205cbfa02f63940ea6bb6b074b761844939a75e0000d4e0002d78b96138c00017809b80000451111e4530dba00025682b1000060a2f1a30927a60002e88000261e0002eecc498000000000000003d000000000001d1650c0f9e03800002fc800054a9da62a58000aa80000997800085612160000000789a2e63a5a238477000000000001f6af7a000244217c018400013926f60000b3e2c605ff271e65f18fc57996668d1a56e6eb24e27d89bcc8ba2fb6783877e0bb824a00018fe9c681285b32cd6498023e8028168aed8000ab0000045d0000a9b3070a9e0b10c100baca142ebab7a28da0000092b8c00008c41b7c909817800000004438416000105a7a1a5a245429f62da8fc000000000fa80001b190b800000000670000000000060b80000002f840fd2a0600000000000000afb000090eae56000000009884384f5203e72f0be49222098abd9e5e84e05d019b00004f080000002bd2000141c0002f3c9c019327b387de95f9c2488f88f405d1e2ca00999cae0800023619380ea2c4810e9e4a9f119dc000101473a978e80b800036789e85548000ba7a0200001926a580b3c484ac7862b00000228a100002c76bb497d097a1410c078d068270000a3327622f8ae468bd8000a1a19360000000b6b92d49da8572a532f5246f80006cf83c2c2f00006e580001b6a61266d19a231bac0c70a8000ba9048874a82943b78000b60000088f1afa0baa7f655f1846bb9041e4c496a63988108b9b1d9251faf9035a9ae016b0d5c677a8bc2148ee02c6205080c860c450acd00fa00009858d746d924da20bb17e000017ca9400000340000000176a78080001e20000000000000000004818000000047a84f1824b690000830a9504f8000017e9b480b3afaa8f59f82aaf8bc42d327c075e2ee6bb79b10bb88380961123c09e24363e510aa57a0d2a09185208c23118802307c71a053e000277431e2cc679725da84204f6a979a9eabf22800188db000007e86a92dc21c0a81a0002572baa8000b9498da52b8000081000048809d89e0115e4c2a22e181
  | 46 => 0xb82287a65a625a8be5cf8a1a7c60b700000000a3482700001a24000160a48a2484be5aa703472d489e88f1c3b12b104f11dda3c894ea000000028ea27226889721c1000000007e00000000000197e1951fdaacb06e82dc8dd825e9cd4453ad6ac60157852305cc483000016f9eb2b4a96a000009400002778b1c80000000000930000013c800000000000001c028fb00000000e800002e1eb7f800010180004fb9d6eb0980000091fe47f211665f62406000000030a0a521369fac000126878d000087e800066f80001301fec9938000c2b2d98678add00002e0661400008d8237c46d0772be529b856d98105002cb69390f1826e0b2e107159a18a10200b809ae24e1a74a95b0fc00000002a200000000000a5780007b08a8c00000006569d883408cbc871af8000000000000c847cd1e8c57926fcaf41098727b15018a8000761aa9200000b2b2514465962c0a7129fce93e24f41e108f20002cec01a84ce0fb093a00021467d080009080000000000000000007781b4400000000000000000000021c26c20000b280000000b1880000100f048ea84a60051264000000000000004e7aea8bf29f5840a80001c2aee073806de2e7a25e09d12a24850048000000071f02609f580008af000052906180001756942102eaf90000431136c793000030c173256480006680000074a3a465097b00000000a0b800000017d200022cc000000000000000000fa6c3d006c52a00000c5a732000193e000020800001a800000009f1aff889f000057c00003080000afc00009ad00000002dc8a5a03fc000000017a99ce00002b4000000000002180002e60413b08c0000f783fa85e400023d2b0d000070700000000000b880000000000000000000002b8684ab000000000000e2e623ee149878017444b880fa473276c011314c000229e7bf066e77980000002462a6014f68dfb110a201892489014a288117e2b782f8b13830641f98aa14e1e18030a0a65b524f0244adb46c180005d70000368800000031300d3800019280000000000b7c800000028b8180800001f800051e95820003010c212e8c00000000000000bcea4ee0130c4e7ba908a7e3192886381be9d3b1760000c425300164b5b9e80c36948a52e2a7c00000000001e4200000000002eea4be12a002da4ecaa6042e00014ee89c2444000047c000274047015a000000008a1800065504020002fe000000005ed0000000000000000002858000514000074b000009b141e4bf800000001940000d44aa326e600026960001fd200000000000000b130000bac1b7e5460000b3003020002ad4000153a0002230bc38000000154428c8bfc000000000004bc16e00005a100000eda4a20e100005468000b8f1c503271352c3600005f7870c00b8102a5080006cc146e0000000000000077410961f017e
  | 47 => 0x99468ba34c0002650be9911800000005d480000000cc6000000005b1c90576ad8c27c0000aa9800000000000000d7a0001cb023097ec629000015980000000b5c0000a22282097e06280000001a946b2812600030ea7e024c60001e363aa8000000000000000007d995465d40000a741fd40000000140a57640000000cb29888b08db219c1f360002004bc729763bb0000000173400019ca81ba6929cb171e881800099d00000002c5a2c28098b2080004b68000b2c800000000000000000170000000000005199f7a000000000000000000e902e90000b6822aa7868000c51217c22eaa4c5ba13649529e3a92b1f8e15d15b82f5000000019c000013385cb000000022e00a3a984806186200000005390000ad39bc40000000000083c000000000000004e199f069d91f400000000001a262b0035a000296c9b78a4400000001820000000000000000009b200003862b463b919d6000000000011240000a702ff8000a1c05a8000194aaa0255c000302e2490b3400000005578f44a4d8b025330000be88ae4835000082b17c25068e080000000000000040f800007524a6b808ab2119a0341122a2c00026d6b1b8c56a0b14600000000615000098c924200024dc0000000000000056a8b0049f93b0502000058a15d2a798000c099c9ab8e800098a9dac372800000006264f8af883ae04ba92380006639ffaa3c2a4633f957a31f0000000084a13d2c841442bfa733196060100003fea456b0e9b8e3e815b000022d20000000a64068ec1a8d8e00000007b1800000000008ed00000002160000000075680002c9000054e000000000000000ea8000000044f800000000b07a6025c734889ea1693620000000b4000000000dd20000000c1b800000014488eea3c62980b40470a3d8b162a543b602100a9a5407be17ca636125c8e1194e3d6aefa1752334ba093a641511527a701421f5800000000008ca800052aaf8a1fb00000002d3cbd00000b57072400009844de9812a41010aaf804caaf083480002f22830186c1d50f4263a2606a059288613ad563312898296054400010e6c5580000000000616000000007b400011989888c3800020ba224800000000005e50000000000069900002ce9a3e4c9800000014b2000154a0a900000002f441a28000975885ead4800072b9aae9582e1a1398b3835a000054504d696c282800000000000000000174a00000000000b3e92a96342bf11de6130000945835ea432552a9700000000254329887e2aa1d50bda80007178220525208669a2b2265600005fa00005b90a123b2a7c2000000000000001a8000085b000026d8000000000000000000002fd84a380000000000787a5a00002d700718000c5d1e489e407804641698000000064f000053f0000c341d6a0000a2ec23a7faa35882200
  | 48 => 0xf30000402969469f9df255fa4f60002cce0000bb200000004032de60001bcabd7881e118800067819ec00029b09850000c568622655848e3662cba59a250e00001340002a4e123000085411a2000220cb58051e22816d200000000002d060000680bff233a7501c3833e0000a779d4652430aa2112fa8ad21b34449ac466b20df26c285280ee0e7c1a61ef632a032a599300841a9f7cc5a96061172bd47509bb4b9995967fd86f0bfd94ac00fa4043951d3e6b985e6666ac168b1a26808c87fc000101a000137885795301f0aa7a34994d463d959e7ff0000000138e0002edc89525880b41468673064461a221004593047d8291223785eeb3f934000019c6acf10e8894a2da89880006389e2800005520000c46000151e84080003d980008c6274a00005ca0000e6e0000996aae84c80000c0c1ab800074a2f568278000af61cfe08994165ad8a644768a020830bc2b872e326660000000162eaeba5d8bca800000000005708000000000000030a80000000000000000023a8299a1aa6b0a8fc49a800000000000001f48000082c0e898369a200008241e66bdd241046386e4bda1c4cacfb0c475d830e5e624fabdca9f224f21722e021deb38982605c1a803dc12c00c32256704975e9202d301cc9d3a4869c3e382849a0001be6b9689303f400009c92ea016510083ca00004b1000008ba9941e980000000c76270ab66709aa3092c2f86b10122a3cc8000000000000000000000000000122200000006500000000000000000004ad0c1a00018d20e68ebcc0ea2a00a4245ab080052250a1b6991312043898ce00017c80001ca038c9e6e8248d860001d82b409a7856123ae00022d60000000000181600028d041e0000028b03410694c45fe00007c48004c3c8000b5d07364b29b463b480cc820207466900005df84006ca8f0ca8408d24aa00000000000000000000000004560000a888c940001ecc00021a833680006bb0000b73823a77fa42a08b00006838fae60f258e57700000000000be3a2b237915008d883549838000070000046180000002e4c0000000247800000f134c2ec18dea10874497384d804c81e000000000002f3800000009ba8000000086221aacea00029920002afa18c12ec0002b68b7aa56c0001790000000069400000000000a1b00008c92d1a532952638d8dbe394ace4a1811ee823800083f2f64563a92481e845669981fc0a7113c0e80c7eb5300000002fc8bab1ba600000002dd0902bae000009d95fca3901c20000a360000dd000023f400016e20000000000071a00027f4000101804e226a000205e60d00000001f4e0000000a849c1400000000a20000000000000022ec60800007221d3669e865089e000088a28ce129200cab100004ca80003b3adb697900001b100009e1000037a80005e4a1da68ca28a36500
  | 49 => 0x532b8fb10eaec211843b000003294be838a5420002d5885500005b380001f400007c40c1c1400f3600000e294ea7b80d608b48be00006610850a1e9d0e6472b747f982ba2241ba898b29a48cb25f096f0000000000000027080cf0800083a604b2b9aac56209dab4f885c2318f0826980008d0af7eaf300000000000c3e8240452800079c03aa27d0c9e9fb0b4600015d800000006b60000a2d800000000000000bb80001516c4712de2a5132c42d0000662a8347489ca40002512000053c3bf8722bf39f16b50aa9a1ee9aee1e70e2262401bc4a707b206b25704192b0c81a10fca9000847842982143062087d06945ee1d4eb7b1b5a83187ee8800e8e48ead941b72070c3c17c69598a9a744890a185955a23f09e21d02a3a297887457520a41d6000056010c621c97aca7faa3c4bbacf0bafad6c9fe0000000000000006ac000000027700000000000b02000044d0cec52217e434e13767b02996aea9d3400029108bea7a081610b05b78dae000000097d9c3699f15a200031146870000000154eb8d80009cfb0e4ac3a656000000000022f20000000a998000bbd26660000000000000000000001e29a543e1000001baa88bef20b400004d281d8000000136a00018b26db8e7e17a21e801919503b2117600012a40e9ae5466e9c9693f915a8de00000002e9c00010cca98000000015a850991b21ac8000a8f80009379d9ab489c7845f00000002d508cf00006828000c3587f6183af78773a1ea713977202a2fc60001094c17923e00000006af8cb08b3864817fa97c00000000002b9a5ec83180000298ae5a56202e168e00000000e3000059524b4000000034100003fc000000021ec0000c4c8558000000000000000009cd0000b0c21a462d00006d3858a000118c00000007900000000000000000003f1235a00028620c78000133000000026f400003383290d0a74200000ba0000000000000000009e700000000000432a0b224a03287a80000b502060a0c000046214a241e8ab863ea464467b0a03bca1d01ad288830f26b097114543bc21d6000000039c00000db31546458e6400000000001bae24402a26ad819aab49cfc5ce00005cb981460b0000afd0000000246a9ebad6889288aa90d0000b940b420001880000000000000000000000000002801993e6393aa2a8960000000042000000000cea476483800000000000001f9e00000001f701525a2000000000900001ef476928b03dc9e9eb07000000003e20000fee0001f063ca80006461c9c00000001aa2cd8000029a111a32288da0a86a1000000000008f70000b89953c000000000000004fd811079f2ba24ac056a00026d8a0a8000b6b2558aa518a000015044a280000000000318963e05616245a014d836b0000a150000a24a49e02f0fb2bcd8e9a626aa8e39e8000adb8000b
  | 50 => 0x26027ba135ebd4281022724bc39da8de7c78266ba28000000000000000000001ec883d2c4ac1800000000b8452698cc8d580000000000a259b846ac00004bf00000000000000000000011b600000006a2910c000000043225f800030e07b9800000000000000b320001572000000000000000001d10698000000025d0000000000004ec000000000021dc000000000022940000000225000084980002311bfa98dab089ae0000b77959c67c800033526fa085000000013c03001a280001e5a0000000959070e21baf700000000000216a0f4a5fe3d800002bb9f0a00000000000000000000018713222018000a4c22420170000000062e4d9971600004980000000665afe22640000493800077e9b760002eae7f800000002af20000e9c3c80000c2e9146c47a29a2b400000001cf65c0000000023d4b4a15c8000001a7760cb2000202a14d00000001cf8000231a05588422fc259e2a789702f7af2e00000000001e588d60b0c0530000b471148000001c00003b487c000000017d600025ba8d70000afe1bc2b77000092c80000001e1c7a680000d8aff4a6a277c84b0000ac90000000068c7261dc67c904125d52b5e000227e000000004313fe000025a15200009aa9b7240180007a9abba17e2390000021ebbe00000002b20a8709fe9a3ae0400014f80a818ba51920567c891a03ff25441d7858231805b67b88cf61a590487ca1f9201da188b640d5284b9004882a4ae1c8095861d00000000f3e0002e74800262683312bea5c80000002ed80001c7e7990000000164c000315861e198661b80869a28000000000000000009ef2a0ca2185bcaac85425a787f037b891400009545dbb1420c4a5b871c80000000be0000000000001ea0000af68c7800030e8000000116e57780000000000000225c2b19b42000000069f1f4a8ca1418ac98000255810486b91042fa00005e58000254a7a800022a606a80000000000000000058c90ba9720c9200000004370fecbb02314b2d15408910000000241296294444421372a5282d27fca45e08d966a4d416a2aaf1a3ac072d34a6da594a5a88da01e0fe0ae916908792c742b99e525172e2205b904a143a9028d200001589c6063b88e21ceaa0487112d67409bd229594527231f7824d86d0a69a03c13f16d633a0000c598000a78969a84121702df8000bd8abce000000081f162abc79b2c29a0000bff880e17606ec29896c44a990d6000084812f964400000000000e6a8631c922620d3ea8080000000000000000000000000000000000186a75928a400000000001132798a95200000000002214000024c1c598ca000057a3d78000ab88d920001c841b286624eb2716c29b07e328a6f6b4485da0ec807c0000846549168673787c84ada97a34c8fd49699b02a89848473394a67ee30926888
  | 51 => 0xbfe82aa97b99947a91e92abe00006f02dda000256a000270e0001e38c148000000278200000003a623f04c4000012a18940002176b3ba882bba2f4e23d96b4a0281981981efe1f32580000150a96c8dce75322b480b079279d892cc128000bada59a640000094730502e52a1a0000e1c5bd00000002eca6d8965a4481602a52103685b90743a526aeacd2642bf080008c99d2600000003400000ba98000000303200024026ad26863e72d9c6598b0694d06e600000002690000000000000000007cb875000000000ae000084697f2000000000000004e5151016300003c401b4b852f8c20a9a10000230a000213400010e02bc0000000164a0000196000236a00009e000023804650000836800001ea7da00027cc5562c96000000000001f800015a4000084c00017fe3eaa7f015780000000000281975a000000007780002009be8000000075d2772a1c8c74409ac42c5180a4be792e85df29c4a1d887c1aa8afe8039c80296880a26e800000020aea5d046e00020020000d3c86b0f926fe0c70760165c47b00007cc9d0a3c2a1c8c4d98e60000718000000050aa0d8a17af10b27a0f800010fe101258600000000002b568398000000000045c3044765852c2e2293a00028fa069000000000000002ade000000044700003ab2b2800015224b20000344a1782778cc891c09b00001daeb56acfc000168ac60800090b000003c20100002a722fe0000bf9176433007ae0001bf27e11ae4819984a044865e3258abe0001bec2f980006de00000000176000011a74caa3400000000000000617a62e97d24d4000250a0e2ad520000508000000000000005618222a9a30120320f38000000087984b667f13a864525d2585000085e94dab1b31721b819d447f000000013d8520a428000174e9de840a000158c00b01c8b201368740208a3389bd04189ac0bf4227a4af1a0c89380004a7950c595847000000002be8cf04eba0e8a29ac029a91218964000000000000000000000264c000116ab228000000005a0001b6a41b00001a400002b600000002f4c65700000002dcc1418304883ac7aafa23beab800000001c8a2471f460df8de248b80000000000000000000000007e5800082e07f8aac1a983c587f494f214024a9b8a77a91ea19a23ea5838a7e1649ef035880002eb80000002452360000000000000002b30000269038e80001e38000bbc000068b000000020b67e90000000000000025ca0fb9b708480000b1f30ce94f864e0000000ad10d1ac2880000001b2e26a3022b21aa8600022a400023329f4800000000000002e9414ba7989fc8000000000000024c40e700000000000000000099d80000001dbe000156cc4f0dfab5f8d180ab07c4c3720f2a4b90160000d1e00030189b026e86bfa9408d9a26c0002e9a0001db688116f60001a34
  | 52 => 0x2230000bf5800000017046198000622178c0000a2a000188e95380005379cf428f8026000004e0000000000000045801f00000000a7e24d800010f4000204c00000005e8000000000006818f962218000c1e80009c080000000452965800000003ca9282c2e7f08000b068e3800000003590000a489f528288000a559272a0ea1f20002df40002240a3fa4167552ed612d0a14ae30aec55a17f427ca51ac32a49489b9a86a7d2c286121e7e1ae1ec48b294865978c2c146989e5408d3613801e86a5b168a4809449c9a40aa790a2410d19309e32e986e71ab89bca73c09080007089c200001eb80002b6c6cd94b40000000000000024680006dd00002a0000000029cc0001da200017a80000578b1f95ce0542a842d580006c98000000314ab8a000000030f6000036a0000bda000141419d0000aee294e6a4017e3260000000279ea511bf435f9d68b41047400c8c404e40000af20000000000000000008ee2f280000000389abee00030d47f121940b8800000000001ef072a0000000424986000025e208a86644e10dd6c1b0000bc2876c8bf2c440000000a128632000041010a12ac6301c52a082fd40001f506b12f5a94316b845c8b268a72e924232ece000000019080008589360bd29d606bc8c044111f5e71600102fa92e69a3000017b0c641a20bd23c02ba08c0a63070c29bc48121a20001ac60bd08f88b517c48c81a700002ab8c33225a2ed07684712f76000032484925ecb3d0f8eb269576ae602e4a570000000254613f99066490d502ad88ce25914e6875112a4bc9d9894c06c2c1080000002b5a2f4196c000295a7959a3642823cc00030b42d90b08b9c00009b72198910000020ea91ca5916aa000000064286bc5878000ac51ae8be680009490d425880b8e0002fdeb598a4c92906927cb280084c867e41c0e482b0800040f000018780000001922000101c5eb86b000000000000b5e0000000000000064200002fd27de00016040002014000166e414298c0000000921ad84833abbe4a593a2ae48000b220ef41711ba070c903a0e19a58571125e000018c55986d2582175863d19ae00000006fa81da05517be88d1aba000181e554133a02b1724a4c82c2bbb80003e4000600000000000000a6185de0a291b0983000096fa08cb43800046a9a127cc09861132a902b300000000000000000071709801060000000290e3be9fde4172de474e19f4c1e05560a0809a6f211b88ac30b637c0ecc940987000024be000000000009b200000000b18f12570000000028dc00010520aba3bc30297685d014ec7e70e1a0b221223040caa527051474199aa5b6894e6e509c4b66863a9702682c131e88000098a000180c36201ec302016007cac2a9da0000b0923160000000303a5cc2f32dcaa1f0cde000000000000007a080004f58000000
  | 53 => 0x92312839063e7109b6800020ee8150000bbc800000000005c2112cb6e992c4f3858e3a780000000000b84ab760001c7453a0000000236416d0000851000055880006e30b7c0000000a4e2ce000026cc00008ec0271d5e0000000832a1907d580007ad00000000ff6bd0854a2e80000a7f00000001c94000014e4428000ab5800000000009a10e124610000000013058e00002c687ac35001ee6811c70c2c8fbc58e80003df01443fe0756c4e9ace000000078480000001ce6000000000025380000000000000059ca962949a6b69771e4e755a9c6ae40000a7600003a2027e0af079e000279600016c600027d0000196e4d2915c7e22b1697527fec5e1aaa00000000f50000967000000014ba7f711e27b709d4c448000000024e00000000b687780002b1ea118d3a00000001ee0000b0d9d7e387ab0200030640000fdc0001ade0000000000280e11b06c000028d829203de6d280000000000a8580000000000bdf1dee00030f8000000000012580e90da43db154c5b08c3221510a23c1ae9043628220f91cb2c590000305149e00019d200000000001cec0000000000000000000007b28d160000000987241a825800036280008c38000bcc0000a59800000002c4c378000000047200014384a680005bc00000000000c388000a948000000000000001a6000000087f05b2aa2ad86a308000000263ac0380006a38000b518000a8d8000000135818511c8bc0030a0fd800000025822de21168f41760811173a637312ea672292175a39a32f87ce71b83c4ab428ca1e1849ca322ea28eb22b6120a730342061022c8c7a51616fe7e41fa80cfa2264b3b04e99cabb40d827b649e16e6b9d8d60005a49870d16769662b2a01d2c5e7f3060442929b4ba192d820509349d1a6c4a319db200d125aa7b16bcb2b2d9e02b800a8ab17182a900001d19eac9a78352752a05a0af873eb9f14f43e6020a9fa80000000000a2d000072392826ff8fa8b6e2e4e79184fa9b88000000143e0001a825ae9af400030ec0000000000000000005f473a0ad68c125b64a1800055208e645e8e066ef1eb020e00e600010fa7360000000000052f00129c603227dd18761b897ee8e8a6a89c8a088191aa0e6d41cd6c22a66ec262fc4bdb1056252000000001900000a403ce8000be81cdc4db83765ea80000000000312a75635699020000000a90800012a8000763000000000008e703500000000000000000000009bf82340001e3e0000492000000000016620002dc000000005f993b88cb80000002e242a480001582ae891b89ea00000000000000a4a80000000000000000000000000000000000000023500003ab87906ac80000e380000002bc0000000000006660000d0c6d008b63799a14170acda27295b413087d859f86789ed053a22c19440000000c1182d63d7000
  | 54 => 0x3a4919c82c0b1e22804919243c800046a0000660aa0a99e05d200011f09781fd0364276625f0b620001682407852438f85aa56b80687ef9b18000000000019da000226000780000000000000041468a800000000006158ff48a88000ae530762939c6600029cabcd1e7275206520d5a66c29289ec00000000001d1a98e315e00000007b600002a1952e6efa8c49ca80004c6a3fa07609d02a116fa9309ed604010da87817e0a110ada5e080002220fcec4a883600000006d31dc01ec2e8e8108000367123882500001c4acf600023ca343a3fc36811e61902d3a88080008e213880002aea41f135c5340eee15f09cc1d2a50494b93de0922046865a5de13e0000a161fb67fa95ec88a987e00015d02b49f98057a554538215c0002b60000065600003ce9c700000000d6e1e58774baca084334000062f9ee079a309e09ba5c6b550a342d380006809fb44350b1e6c6a2c800000000001616000210c5650d7c0002e180712cc400000005dd031c8f98a7c2a72dd666231240001fa64340000000000000000005c50590c02b0c6ab918866a8021a0000372772131c8dd17480df0070b68ab644822cbe068289071214c20e4116cb648000bcc8f8a00000000001ebaac1284c2d69ea2a7080e48918b2a7f5a0d64390742b7f0000ace0000b2e0d3437f0c580002468bee97428940e4c0000a820002550000026a38585e27168000b5f0000000000000009ee1f9800049c2cb076e000000000006308000000000010d8c123c79b546029d2000020821db800024206d608480000000000aa7800000016f80000000c2b885a99e92c29520584be9099a53886d8b001caa102042c0000ab000019720000dc80001c560002db200000005c2abf6a821e84131800000000000002ed098a0000000305a03f023c02a80007dc9ad2b52800001280000001ff4adf194c5c380000000c8a0960f820000000000000000013a40000900b6a8fb60000ebe7fb947800000003d894b6ab9acd4b0b01ca2e280da0a7a61a508ab4283d8ec2bbd9fb0000000000000009a89ff023c0000a8780008ed9f1c00000000000a7a7f88000b8a817a3e0000082a9910a6eaa006c92bca0221d90beba8ee77b2d20a8503f801080960001726000218000000000000b120598cd21620a98030000000019fe0000540355154200000004faa6bc0000000ae228e6b19800048b29987db15ea1bf848696b8000000000000000000001a46332800000020268058dec1b30fa270b836e000209a9ac8d5e0b0133411e230ca6380005fa8000995000054d800000017f0b9fb00600010de0d096308479ba20a0152c8fc80006fc0000000000000000003440000000000000019909b427be000004600009d200000201ae88fa0000000be6000000000002e72592000000025e0c5c9691ef200000004c
  | 55 => 0x280976b4b85f6c5390ac9920000000000000007521780ee8029af4800000001108af2935875c000000059c0000af5800000026f0000000000009be81f80007c309c06c002d45de844421580005b7292c9cd812040430ee00000002589bc6b788000948943260aa03a2181a4e9400d284739c1a5011ad4000000070b22960da0370474a3f80000000b828a9053590c0628800000000000000000ac2ad38bf70000b45140640b1b3200010d2533800045884b825a1cb89450daa03ca4a861c9474b2916d05a599746b40f0e3900eb207fa5ac4d2120a9050c024468114bc19a1e5ab93c82c50a7200000000002b8e7bb96469d90e146648000000289e76800003268ffe000271475880000000000757062400000006f680000002feaade2b18360ad8e000000078b80007c000000000000000000000018ea00000005b2110649523381a7a2664ccab9e00010be569800000000002efb09c04d8cd8809206a0003048979800000005fca45858675113f228b1f70885837a2d9aca274900002b3816a58f126641b80000000812a070dc48fd80007940000000270a93a8c52732967400000000002f6e2898000036000009100005900000000000000025aa45000008e9ac1034c0828731277ec0a1274000067c9ff198c69217220000000094b1520001c102f7098e3f49eda06ca8a02719b3c0000000000000040900000002900000162646b0000644aab63a2a78a57eb0044930000b8e18008e59af004f9f5aac1923026700005108000c15000075c993a85f886cb900c727a40b9024fa9ea18f2df851aab8000001f463cad243cd289441a28e21570af87b502fe6fd924a3fc999e0002806a5c04dc0208b3641d83100001c0400016ac00007fa39e1046a2eaf60000100e9569d6c4bc00001ba83300001d3000029c000014c856fa670ba58000153800071d84e20f80b52c40148056e80000001c289d700000000000000192e000000087b80000000f26a9292c6125800062b890c4ee80008e3887849b28120002680aaa800097ca44a09ea5062f1a3c4000248c0001f5c5a300008db2f18b24a45c1692e4450daba894a8fda7288000bd618d4b7c25fc4699e7a0002ac80001c1800005980000000000112e38b000000000009cba38c00000007100000311206c00000000000000000106669700003151eecc4211286db00000000000000000000000000000000000000067bafb29dc1c3ca8a21100c0221a9d09fca085a1860741c0089d0c6a2ed90300460000000068465880000001ada56293d000000006d80286c432036000300c73c8000000000000013e4017b1348ec229838a80007dd89060000aae257045845529d269796526ca0000a6f80005092f920000000990000057c8d2498213e86e92ca608e2a2eadaa5fa6911280398244c2c71ee417391
  | 56 => 0x43ab058a2b89269af88ee1e9072c40a0cf2000071c00024cc00002840000000000000007723409092c386a21a3c0808bfac34afec9ce00007ce87348c1800042402ca04705226d4852aa1010f83ee99b8000000021980000001dd691f07d49bb24e000011d440e000069b2142114000042089aa2b710848bc10ee000000000000008a211e8000129269c881c20813dc35c0a8e5e927ca00000004d121a06592cf20001bb66c380000358e0200024920000000abb00001279e2a6e080000002836af7000012285180cd1398000000000013200002706870800072b0000000066a4762248a5e00fe24b831a6e6a45073198c6aeb043c8100ab4000139a620800086e93424c213960e204320001e04af7a1d2af691102f29ed28ae856e3060ea4bcfa47aa751b2027980948f92848000088037303360000000000084025280be000128ca55000000000003399d705dc2408000221e0000d6600000004b70000587000000001a2000000039186ee430800000014f20002ff291980004e003642300ba895e11f22b2800004199520001e1400007281390000af1870699900000002f2698825b483f9cb411a8982000281e6310f2ea42a1b43231eae40d1a08a0f25103bf000045e1d7c77796a40000dde9c300000001adc91f91f688c92ba711a5c20001ad63
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc9c645ce64480010fd0fb2ac8900021fa1c65591200043ec0eeab224000c6f21dd564480010ff0ab8ac89001e1f21571591200045fc22e2b2240008df835c564480071b906b8ac8900021fa1f515912003c3e43ea2b22400087e8754564480010f90ea8ac8900063b21d215912000637baa42b2240b8c6c7548564480019cee290ac890007391c5215912000732a8a42b2240008bf87590644800d0f90abb6a8900028f613659512011637396cb2a240088ec865ca54480018decab94a8900021fe1576551200343f43ecaaa2400787c855d854480018bce7b28a89000317d95731512003e2e32ae62a240088ec865c8544800f8f0cb380a89000a3e219701512000673b8a43b1a4000e65514876348001d8c6290ec6900021fa1f6558d200043f438cab1a400787e87dd563480010fb03baac6900031bc877558d20006363aee4b1a40018ec82dc563480010ff0ab8ac69001e1f2157158d200045fc22e2b1a40068bc845c563480011bf06b8ac6900021fa1f5158d2003c3e43ea2b1a400087e8754563480010f90ea8ac6900063b21d2158d2000637baa42b1a40b8c6c7548563480019cee290ac690003995452158d2001c3e42aeda9a400087f855d953480011df04bb2a69000e1fa1f6554d200043fc2aeda1a400787c855db434800717908bb686900731b9c865d0d2004476432e5a1a4000c6c655cb434800f0fd0bbb286900021f6177650d2003c3f42ceca1a400087d859d943480010ff0abb2869001e1f2157650d2000477c12eca1a40008f7815d943480031e902bb286900021fa1b7550d200043f430eaa1a400087e87d9543480010f90fb2a86900021fa1c6550d2003c3e438caa1a40038be87d91434800d1bd0fb1a86900038bd946450920036563b686a124006cac7650d424800179306382849000317d9573941202962e32ae72824022c6c72d9550480018decbb92a090022ab21942d01200e43f436eaa02402287e861d540480c50fd0fb2a809008a1f21f655012031c3f438caa02400787c8719540480113590ea128090022ab2194250120045d440284a02400087f87d9440480010fb0fb288090003179cf651012011637396ca2024000c7671d94404800f0ff0e32880900021f61c65101200062f398ca202401cc6e7219440480018ece2328809000317d9573101200062e32ae62024000c6f655c840480018d8cab9080900031dd9571101200063a32ae2202400087f87d9630480010fb0fb2c609001e1fe1c658c1200043ec38cb1824000e5830d9530480398d8e432a60900223ba1b724c1200063632ee49824022c7876d953048001cb0c7b2a60900731e1d8654c120005ad42ee69824000ada86d4d30480015b10ca1a609000f361d9434c120005ac42a869824000f894350930480458dcedb2c409001f1b9d86588120
  | 1 => 0x30018eca9008a9be0521d952011733c0a43b2a4000c6f714876548001ccee290eca9000319dc521d952000636b8a43b2a4000e64714876548001cce8290eca900039910521d95200073318a43b2a4000e653148765480450fd0f986ca900021f61f30d95200051f42661b2a4000a3d84cc365480450fd0f886ca900021f61f10d95201153741621b2a4000a6d82c436548001cca43886ca900039948510d95200043f43821b2a400087d87043654800147d08086ca900028f61010d95200052f41821b2a4000a5d8304365480454dd04086ca900029b60810d952000c3e42ee2b2a400087f855c5654800117f08b8aca9001a2f21171595200046fc1ae2b2a40038dc835c565480010fd0fa8aca900061f21d51595200063bb8aa2b2a40018ec8748565480019cee290aca900039954521595200043fc3aca32a4000a3e8498c654800147b09318ca900021fa1b71195200043fc3ec232a4000c7571d8465480010fb0f308ca900021fe1d61195200051fc22c232a4000a3c8458465480014bf06b08ca900029720d61195200043ec38c232a4000c757118465480458dcec908ca90003595c5211952000733b0a4232a4000a7a8090c65480014f301218ca9001e1fa1c43195200043ec388632a400787f815c4654800f8ef02b88ca900031bc8571195200063b10ae232a4000c75215c4654800f0fd0f208ca900021f61e41195200e5374148232a4000a6d8290465480018eae3208ca900031d5c5411952003c3f4388232a400087d8710465480014bd06208ca900029760c41195200e5374108232a4000a6d8210465480014f500208ca900029e600411952003c3f43c6232a400087d878c465480394dd05188ca900029b60a31195200063ab8c6232a4000c75714c4654800f0fd0e188ca900021f61c31195200051f4206232a4000a3d840c465480394dd04188ca900029b60831195200053d4006232a4000a79800c465480394df02908ca9007399e0521195205c637b8a4232a40b8e667148465480018dae2908ca902e3995c5211952000632b8a4232a4000e67414846548001cc882908ca90003998c521195200073298a4232a400787e87cc065480010fb0f980ca900028fa1330195200051ec266032a400787e87c4065480010fb0f880ca900729ba0b101952000536c162032a4000e6521c4065480018eae3080ca9000399485101952003c3f4382032a400087d87040654800147d08080ca900028f61010195200052f4182032a4000a5d8304065480394dd04080ca900029b60810195200063ab882032a4000a9d83107644800155b0420ec890002ae60041d912000e7338a43b224000ce5714876448001ccaa290ec890003a910521d91200062f39ecb3224000c5e7319664480018becab9cc8900031719573991200064fb22e73224006
  | 2 => 0xe53596200051ec20a6b2c40008bf845c5658800d17908b8acb100221f21d51596200063bb8aa2b2c4001ce67148565880019cae290acb1000399545215962000c77c3a43b244001ce67148764880019cae290ec9100039954521d92200043ec0eeab244000c6f21dd564880010ff0ab8ac91001e1f21571592200043f43ea2b24400787c87d4564880010fd0ea8ac9100021f21d51592200445e43a82b244000c6f7548564881718d8ea90ac91000339dc5215922000e7238a42b244000e65514856488001d4e8290ac9100028f61365952202052f41ecb2a4400087f855d954880110f90eb2aa91001e1f21576152200043ec3eca2a4403aa5e83d9454880018becab98a91001f1719573152200043fc0aebb1c4000c6f215d7638800f0ff0fa8ec7100021f61f51d8e200043fc3aa3b1c400087d8754763880031df0e90ec7102e31b9d521d8e2000636baa43b1c4001ce67148763880019cae290ec7100039954521d8e200446e43a62b1c4001ce67148563880019cae290ac710003995452158e200076298a42b1c400387c855db53880010fb0fb2ea71000e97a0f65d4e200446fc3ac7a9c400387e87d9553880074bd07b2aa7100021fe1576d0e2003c3e42aeda1c40038bc845db43880010ff0abb2871001e1f2157650e200047bc0aeca1c40018f4815d943880758bcc63aa871000e2fa1f6450e200446e43ac6a1c4000c5c7558d43880115b50da9a6110022b6219434c220005ac42a869844000bcb8250d308800147d0829eca900028f61053d952000536c14a3b2a400187f8754765480018eae2a8eca900029b60851d952000673b8a43b2a4000e66514876548001ccaa290eca900028fa1263d95200051ec24c7b2a4000c7571d87654800147f08b0eca900028f21161d95200052fc1ac3b2a4000a5c8358765480018eae230eca900731b9d921d9520006b3b8a43b2a4000e67614876548001cc8c290eca9000297a0e74d95200052ec1ce9b2a4000c3d741d365480014db043a6ca900028fa1273d95200051ec24e7b2a4000a7a801cf65480454f30039eca900021fa1c43d95200043ec3887b2a4000c6f21dc765480018ec43b8eca900031d48771d95200043ec3ce3b2a4022a6e829c765480014db0538eca900031de0571d95200063790ae3b2a4022a6e821c765480014db0438eca900021fa1e41d95200043ec3c83b2a4022a6e8290765480014db0520eca900021fa1c41d95200043ec3883b2a4000a5e8310765480014bb0620eca9008a9ba0841d952000536c1083b2a4000a7a8010765480014f30020eca900021fa1e31d95200043ec3c63b2a4022a6e828c765480014db0518eca900021fa1c31d95200043ec3863b2a4000a3e840c7654800147b0818eca9008a9ba0831d952000536c1063b2a4000a7a800c765480014f
  | 3 => 0x1a9a6000d59519c3534c001b9643386a6980037248670d4d301d4af43eeaa1a60abc5c76dd5434c1558b8ec3aa869814b17a187550d302962ec30eaa1a603ad1d841d5434c0a52bf023aa8698002576047550d30006a7908eaa1a6000d4d211d5434c0758bec03aa86980eb56d807550d30006ad080eaa1a6000d59101d5434c0a58b8ebb2a869801a3721d6550d3018d66412caa1a6000b1d85191434c0a5a38eb2a2869800387d965450d3001cce43aa8a1a6000e1d65551434c00173100aa286980c73318b7250d30006ac3aee0a1a6000d5b751c1434c001ab0ea382869805e76a187050d300466d430e0a1a60009d9821c1434c0113b7023828698002766047050d30006ada88e0a1a6000d59511c1434c001b96423828698003724847050d300043fc2ae9b12600787c855d3624c0011ef02ba6c4980063d20574d893000c77c3a43b126001ce671487624c0019cae290ec4980039954521d893000636310eab12600287e859db524c0111bb073b6a4980021fe1d65d493001536412cba92600287c87595524c0054d904b2aa49802276a037354930484af43ea6a9260028be849db424c0071b9073b6849810b1b18a75d093001556412c9a126031ccc625cf424c0113b100b9e8498003279d943d09300068ebaa87a126031e8c6250f424c0018dcebb16849801e1fa1476509300043ec28eca1260028bc87591424c001938eca1a849823a57a1f754c93047e2e3b6ea992608dc5c761d5324c179a98c43aa649814a57e04754c930004aec08ea99260bcd4f211d5324c001a9a423aa649823b17d80754c930476adb00ea99260bcd5a201d5324c179ab2403aa649800356840754c930006ac880ea99260088dc865d1324c0a52b90aba2649802276201744c930006a63aec49926000d5875dc1324c001ab6ea38264980225721573d413001c3fc3acb2826021c5e73596504c0454d904b2ca09802276201739413010caec3ea7282601dc5e76d4e504c0010ff0eb28a0980729b2096514130294ae42ae7a0260038bf87592404c02393ceca1c8098023560c175101300045fc3ac820260089d8805cc404c02f93ceca188098003475d5431013003657322e42026000cad645c8404c001b1a86b908098023720c172101300365b322e22026000cb5645c4404c001b2a86b888098023740c17110130294afc0ceb182600095d819d6304c001a9e433ac609800353486758c1300462fb04eb1826026d5b609d6304c011ab4413ac609802356842758c130006ac884eb1826008dca205ca304c00199e42b9ecb102ef179cf51d96200062eb9ea3b2c400187f8754765881758bce6a8ecb10003175cd51d96200063ab8aa3b2c40018ef87487658817399ce690ecb10003335cd21d962000e7338a43b2c4000ce5714876588001ccaa290ecb100221fa1
  | 4 => 0x8c0010f90eb2a81180029760e52d95300053ac08a5b2a60088dd83dc7654c0030ff0ea8eca9800297e0d51d95300063ab8aa3b2a6001ce671487654c0019cae290eca980039954521d95300147743ee4b2a60008ed81dc9654c0018deea392ca98002b960472595300045fc22e2b2a60068bc845c5654c0011df04b8aca9800a3b209715953000637b96a2b2a60bfc6c72d45654c0030f90ea8aca980031bdc951595305f636392a2b2a6000c7771545654c0011dd0f90aca9800a3b21f21595300047743a42b2a60008ec87485654c0039cce290aca98003395c5215953000732a8a42b2a600087f87594654c0014d904b28ca980021fe1572d913003c3e42ae5b226001ce671487644c0019cae290ec8980039954521d91300076298a43b226000ee121443644c0010fb03baac89800a3ba1f725913000637baee4b226000c6c75dc9644c0011db03b92c8980031bdd47259130006363a8e4b2260018f687dc5644c0018eeebb8ac8980031d1d7715913000673b96e2b226000ce472dc5644c0018ef0bb8ac8980031d217715913000673c16e2b226000ce482dc5644c0010ff0ab8ac89801e1f215715913000477c12e2b2260028ec825c5644c0011ed0e38ac8980031ddd471591300063a3a8e2b226000ce7721c5644c0019c8e438ac8980021fa1f515913003c3e43ea2b226000c6f72d45644c17f8d8e5a8ac8980031ddc7515913000e3a38ea2b22600087e87545644c0010f90ea8ac8980031bdc951591305f636392a2b226000c7771545644c0038e8e2a8ac8980072d1c7415913000c5e43a82b226001cb471505644c0031b90e98ac8980023ba1f21591300147643e42b226000c6f75c85644c17b8d8eb90ac89800339dc7215913000e7238e42b2260008ee87485644c0011d90e90ac8980031bdd521591305c6363aa42b226000ce771485644c0039c8e290ac89800399545215913000753a0a42b226000ec531485644c0039e0e3082c8980063e21d105913000758a0a20b226000ee121441644c00117f0eb20c89801a1fa1676d51300446ec1cedaa26042a6c82597544c00147b09b2ca8980223721973951300062fb2ae72a260089d8805ce544c0010ff0abb2a8980023be09765513001476412ecaa260008f7815d9544c0031e902bb2a89801a1f21d65551301e536412caaa260088de86dcd544c0071f50db82a89800e3720e761513003c3e42aec2a26052c5c535d8544c0011df04bb0a89800a3b20976151300043ec3eca2a260088dc865cc544c0018becab98a89801f1719573151302962fa8ceda9a6000c5d519db534c00199e433b6a6980033348676d4d3010caec3ecba9a604095f87553534c0016b100aa6a69807676a1a70d4d300466d434e1a9a60009d9829c3534c0113b703386a6980027660670d4d30296ada8ce
  | 5 => 0x80221f21d51596300063bb8aa2b2c600087e87145658c0014dd0428acb180029b608515963000e7338a42b2c6000ce571485658c001ccca290acb180039954521596300453d404c4b2c600087f865c5658c0010fd0f30acb180029ba0a615963000536c14c2b2c6000c7771985658c0114f50130acb1801e1fa1d61596300063bb8ac2b2c60bdc6f76c85658c1718deec90acb18003595c521596300073330a42b2c6000e6561485658c001ec242882cb180030fdd274596300453c402e8b2c6000a5d831d1658c0018dee5392cb180229ea0272596300053cc04e4b2c6000a76811c9658c0014eb02392cb180021fa1e42596300043ec3c84b2c6000a7681909658c0014eb03212cb180229ea0042596300053cc0084b2c600087d879c5658c0014dd0538acb180029b60a71596300453d404e2b2c6000a79809c5658c0018ef02b8acb180021fa1c715963000537410e2b2c6000a6d821c5658c0010fd0f20acb180021f61e41596300053741482b2c6000a6d82905658c0010fd0e20acb180021f61c415963010d2f41882b2c6000a5d83105658c0014dd0420acb180029b60841596300453d40082b2c6000a7980105658c0018dee390acb180031b5c721596300043f43c42b2c600087d87885658c1854db0510acb180031d5c621596300063ab8a42b2c6000e6781485658c0018dee290acb18003999c5215963000636b8a42b2c6000e6571485658c0018cae290acb1800399d0521596300073220a42b2c60c1e6631485658c183cca6290acb180021fa1c21596300043ec3842b2c60c0a6e82085658c0010fd0f882cb180021f61f10596300053741620b2c6000a6d82c41658c001cca43882cb180039948510596300043fc0aebb24600787f87d47648c0010fb0fa8ec9180021fe1d51d92300043ec3aa3b2460bdc6e75c87648c0018daeb90ec9182e31b9d521d923000636baa43b246001ce671487648c0019cae290ec9180039954521d92300077090a21b24600787e85dc9648c0010fb0bb92c9180222f21d415923000673b8a42b246001ce471485648c001ccaa290ac918003a9d05215923000758a0a20b246000ee121441648c0110ff0eb2ca9180028fe1165952300447c402ecaa4600887c87595548c0018f2cbb82a918087179cd65152300346fc32e62a46007c5e655cc548c0018bacab98a91801e1fa177458a300043ec2ee8b1460088ec87485628c0019cee290ac518003995452158a300443ec2aeda94600887c85dd9528c0110f90eb2aa5180021f61a75d0a300043fc32eba14600787f87997428c0010fb0f32e851809b179ce65d0a300043fc3acba14600087d87597428c0438bce6b2e85180031799573d0a300062eb2ae7a146000c9d645cf428c0111790eb2285180021fa1e655023003c3e43ccaa04600087e875954
  | 6 => 0x3f52422e4b0880c7ce6745c9611018f9c8e8b92c22000339dcd725844000672b9ae4b0880c7ea7435c96110001d4a86b92c22000339dc1725844000672b82e4b0880c7ea7405c9611018fdc480b92c22031fb850172584400053b428e4b088000a75851c9611018d5cd04392c2200023da1c52584400047ac38a4b088006ab684cc9611000156b09992c220003a550e32584400053bc2a64b088000a74854c961100011ed0e192c2200023d61c32584400053b42864b088000a75850c9611000d56d08192c220002ad61032584400074aa1864b088008af2800c961100015e300192c2200029da1730584400053ac2e60b088006ab684cc1611000156b09982c220003a550f30584400443ec2aeda80800887c85dd9501000187f0bbb280200030f21776500400061fa8eeca008000c3d51dd9401000195e43bb280200032b48776500400061fbb6eaa008000c3f761d54010001c5eeab1280200038b1d5625004000657b9ac4a008000aaf81589401000155b02b1280200038bd45625004000716a8ac4a008006eab705894010011d5420b128020003aa44162500400071b42ac2a008000e35855854010001c6eeab0a80200038d1d561500400065bb9ac2a008000ea6825854010001d4b04b0a8020023aca01615004062f58c02c2a008008cb770585401000dd66e0b0a80200061fe1d51d96300063ab8aa3b2c6001ce671487658c0019cae290ecb180039954521d96300453d404c532c6000a6e82986658c0014db0530ccb180031d5c661996300453d404c332c6000c7571586658c001acae290ccb1800399985219963000732b0a4332c6000d7171442658c001ec242884cb1801e1fa1e42996300043ec3c8532c6000a768190a658c0014eb03214cb1801f1de0571996300062f982e332c600787e87906658c0010fb0f20ccb180029ba0a419963000536c148332c600787e87106658c0010fb0e20ccb1809a97a0c41996300052ec188332c6000a6e82106658c0014db0420ccb180229ea0041996300053cc008332c60bdc6f71c86658c0018dae390ccb1831393cc3219963003c3f43c4332c600087d87886658c0018eae310ccb1800297e0d21996301352e41a4332c6000c7571486658c001c9f0690ccb1830f9320d219963000733c0a4332c60b8c6f71486658c171ccce290ccb180031b5c521996305c732b8a4332c6000c6571486658c001cce8290ccb1800399105219963061f3318a4332c60c3e6531486658c187c9e6090ccb1801e1fa1c21996300043ec384332c600787e87c42658c0010fb0f884cb180029ba0b109963000536c162132c6000c7571c42658c001cca43884cb180031d5c510996300073290a2132c6000c6f72949658c0014ed02292cb180029d60452596300443f43ca2b2c6000a6e82945658c0014db0528acb1
  | 7 => 0xe571945621000155f08a8ac42001aab211515884000672b8aa2b108000e2f845456210197c5908a8ac42032f8bd0d515884000716a1aa2b108000e678154562100018dee2a8ac420003999c5515884000636b8aa2b108000e657154562100018cae2a8ac42032f8bd01515884000477438a2b1080008ed8714562101954dd0a28ac42001aaba13315884000556c2662b108000e8d43cc562100011dd0f18ac4200023b61e31588400053742c62b108000a6d858c562100019cae318ac420003a350d315884000672b8a62b1080008ee870c562100011db0e18ac4200029ba14315884000536c2862b108006aae840c5621000155b0818ac420022baa00315884000574c0062b108000a6e85cc162100014db0b982c42001aaba13305884000556c2660b108000e8d43cc162100211dd0f882c4200023b61f10588400053742e20b108000a6d85c4162100110f90eb2aa4200223720f764c84004476416ec990800087f855d9321000f0f90abb264200021f61b754c8404862f31eea990808fc6e62dd532100018ecc3baa64200021f618754c8404762f318ea990808dc6e621d532100018ecc23aa64200021fa1e654c84003c3e43cca990800087e8759532100010f90eb2a64200223721d634c8400062fbaac69908000c5c7558d32100111d90eb1264200031bdd5624c840006363aac49908000ae682dd561100015cb05baac22032e9d61e75584406571ba1ceab0880cae37409d56110195ce4813aac22032b9c50275584406655bc22eab088006ab4845d561100018ef0ebaac2200038de11755844065f1a422eab0880cbe37435d56110197c6e80baac22032f9c901755844065f38a02eab0880caa76851d561100015cd043aac220002b960875584400053b42ee6b088000a7585dcd61100015cd05b9ac220002b960b73584400355b424e6b0880c9ab5849cd61100014ed0a39ac2200029d61473584400355b420e6b08800fab5841cd61100015cd0439ac220002b9608735844004579400e6b08800faf1801cd611000d56d0929ac220002ad612535844004579404a6b088000af18094d611000d56d0829ac220002ad61053584400071bc2a86b088000e348550d6110001c6ceaa1ac2200038d5d543584400355bc1a86b088006e978350d6110001d2ce6a1ac220003a55cd43584400074b29a86b088000e955350d611000156f00a1ac2200029da1772584400053ac2ee4b088000c7575dc9611018f5cb0f392c220003999d6725844000732bace4b0880c6ea7439c96110001d4a87392c22031ba9d02725844063771204e4b0880c6ee1409c961100018eaeab92c220322ade1172584400355a422e4b088000ce7875c961100019ceeab92c220003999d5725844000672baae4b088000e65755c961100018caeab92c220003a9e1172584406
  | 8 => 0x2292c620002b56045258c400052f42ce2b188000a5d859c5631000159d0538ac620002b360a7158c400052f428e2b188000a5d851c5631000d53d0838ac620046a76107158c4000567410e2b188000acd821c563100115b50038ac620046b66007158c4065d2ec2ca2b188000ace82945631000159b0528ac62000395e055158c406552f428a2b188000ace82145631000159b0428ac62000393d472158c4000726a8e42b188000a5e8588563100014bb0b10ac62031eb360a2158c400072aa8c42b188000e55514856310001d8f0290ac620003b19c52158c4000762b8a42b188000e4f514856310001d8ca290ac620003935452158c4000762a8a42b188000e4551485631018fd8e8290ac62031fb11052158c400052f42842b188000a5d85085631018d59d0410ac62000297a171058c400052ec2e20b188000ace82c41631000159b05882c620003b14871058c400076290a20b18800887c875955310081c3cc7baa86200eb8798c7550c4001d4f41acaa188000e1e53595431000147d0eb2a86200028f21d6550c400070f41acaa188000e1d83595431000d87ee6b2a862001b87dcd6550c400070f192caa188000e1c32595431000147f02b2a86200028f6056550c400070f98acaa188000e1d315954310001c5e42b2a86200038b4856550c400070f982caa188000a9f8654d4310001c3acaa9a862016fa38c943588402df4619286b108006aae84cc9621000d17908b8ac42000339c85715884000e3b38aa2b108000c757154562100111dd0f10ac4200029ba16215884000536c2c42b108000e655188562100111d90e90ac42001aab211215884000673b8a42b108000e655148562100015cd023aac420002b9604755884003557424e6b108000aad849cd62100014df0ab9ac4200029b215735884000537428e6b108000a6d851cd621000d55d0839ac420042ab610735884000573408e6b108000ae5811cd62100115d50039ac420042ba600735884003557424a6b108000aad8494d62100115d50129ac420002ba602535884003557420a6b108000aad8414d6210001c5f0aa1ac4200038b215435884003747c1a86b108000e8f7350d6210001d18e6a1ac420003a394d435884000746a9a86b108000aaf8050d621018d95e87b8ac4200032b50f715884063657a06e2b1080c78ed879c562100014dd0b38ac4200029b616715884000557c22e2b108006aac845c5621000195f08b8ac42031f2b211715884063e57a1ae2b108000cad435c562100019cf02b8ac42031f39d05715884063e7220ae2b1080c7caf405c5621018d1dd0e38ac4200029ba14715884000536c28e2b1080cae2f43d456210001c5a87a8ac4200031bdc7515884000636b8ea2b1080cae2f40d4562100011dd0f28ac4200023b61e515884065d36c2ca2b108000c
  | 9 => 0x219944000636b8a4332880b8e657148665100018cae290cca2031f99d05219944063f3220a433288000e66314866510001cca6290cca2001e1fa1c21994400043ec384332880c6a6e82086651000f0fd0f984ca200021f61f30994400351f426613288000a3d84cc2651000f0fd0f884ca200021f61f109944000537416213288000a6d82c426510001cca43884ca200039948510994400351f424a6b288006a3e8414d65100014ed02292ca200029d60452594400345e422e2b288000c7571d4565100110fd0f28aca200029ba0a515944000536c14a2b28800887c8754565100018eee2a8aca2032a1fa1c515944000537410a2b288000a6d8214565100039cce290aca20003395c521594400073328a42b288000e6551485651000d47d0939aca200028f61273594400453d404e6b288000a79809cd651000d47d0839aca200028f61073594400053b408e4b288000a75811c9651000d47d09992ca200028f61332594400043f43864b28800087d870c9651000d47d08192ca200028f61032594400053b40864b288000a75810c965100114f500192ca200029e60032594406561fa1ee2b2880cb87d879c565100014dd0538aca200029b60a71594400051fc22e2b288006a3c845c5651000187f08b8aca2032f0f211715944065e1fa1ae2b288000c77815c565101950fd0e38aca200029ba08715944000536c10e2b288006a3e84cc5651000147b0998aca200021fa1e31594400043ec3c62b288000a6e828c565100014db0518aca200021fa1c31594400043ec3862b288006a3e840c5651000147b0818aca200029ba08315944000536c1062b288008a7a800c565100014f30018aca2031b8bd0f215944000637b8e42b288000c6d71c8565100010fd0f10aca200021f61e215944063d36c1442b288000c757188565100018eae290aca2031f8bd0d215944000733c0a42b288000c6f714856510001ccce290aca200031b5c5215944000732b8a42b288000c6571485651018fcce8290aca2031f9910521594400073318a42b288000e653148565100010fd0e10aca200021f61c21594406353741042b28800087e87cc165100010fb0f982ca2001a8fa1330594400051ec2660b28800087e87c4165100010fb0f882ca200029ba0b105944000536c1620b288000e6521c416510001cca42882ca2002237a1e3158c400052f42c62b188000a5d858c5631000159d0518ac620002b360a3158c400446e43a62b188001ce67148563100019cae290ac620003995452158c400076318a42b188000ec531485631000d53d083aac620046a76107558c400052fc2ae4b188000a5c855c963100014bd0a392c620002976147258c400354f420e4b188011a9d841c963100015ad02392c620002b56047258c400456d400e4b188011ad9801c963100015ad
  | 10 => 0x32a800087d8788465501714db05108caa00031d5c621195400063ab8a4232a8000e678148465501718dee2908caa02e3999c5211954000636b8a4232a80b8e657148465500018cae2908caa033799d05211954066f3220a4232a8000e66314846550001cca62908caa001e1fa1c21195400043ec384232a80bda6e82084655000f0fd0f980caa00021f61f30195403151f4266032a8000a3d84cc0655000f0fd0e100caa00021f61c20195403151f4204032a8000a5e8308065500014bb06100caa00029da0420195400053ac084032a800787e87c4065500010fb0f880caa00029ba0b101954000536c162032a8000e6521c40655000147f08880caa018a8f21110195400073290a2032a800787e8704065500010fb0e080caa018a8fa1010195400051ec202032a8000a5e8304065500014bb06080caa00029ba08101954000536c102032a8063c3e549db545000d47909b2ea8a001f1e19670d51400063db28e0aa28000ce77148763500039c8e290ec6a00039954521d8d4000753a0a43b1a8000eb1414436350001dc242886c6a00021fa1f6558d4000636396cab1a8000c7471d9563500010fd0e32ac6a00031b1c86558d400063a388cab1a8000c6f65dc963500018d8cbb92c6a00031dd977158d400063a32ee2b1a800387c855db53500070fd0fb2aa6a000e97a0f6554d400043f436eaa1a800087e861d543500750fd0fb2a86a01021f21f6550d402043f438caa1a800787c8719543500031df0e90ec4a0003395c521d894000732a8a43b12800087e87d9562500010fd0e32ac4a000a1f21576d494001c6f41ceca9280008dd839d952500050fd0fb2aa4a018f8b10b6550940004f8c08e0a128000c3c76d954250001c58c5b2a84a00030f1d86550940005d8c08e0a12800787e85dd932500010fb0bbb264a001e1fa16764c9400043ec2cec992800087e86dd532500010fd0c3aa64a00021fa1f654c9400043e43eca992800087e87195325000f0f90e32a64a0003179cf65941400062fb2ae72828052c5c655ce50500c74f50da84a0a018f0f1d365541400061fb2ee8a828063c3e76d9640500c7c76c1b2c80a001f0f9d8659014003c3f43865328800087d870ca651000d47d08194ca200028f61032994400053b408653288000a75810ca65100114f500194ca200029e600329944003c3fc0ae33288007c77815c6651000f0fd0f18cca200021f61e319944000537414633288000a6d828c6651000f0fd0e18cca200021f61c31994400351f420633288000a3d840c665100014dd0418cca200029b60831994400453d400633288000a79800c6651017b8dee390cca200031b5c7219944003c3f43c43328800087d87886651018f4db0510cca200031d5c621994400063ab8a433288000e678148665101718dee290cca202e3999c5
  | 11 => 0x500014bd0638ecaa00029760c71d954000537410e3b2a8000a6d821c765500014f50038ecaa018e9e60071d95400043f43c83b2a800087d8790765500014dd0520ecaa00029b60a41d954031f1a20a83b2a800087e878c765500010fb0f18ecaa00029ba0a31d954000536c1463b2a800087e870c765500010fb0e18ecaa018e8fa1031d95400051ec2063b2a8000a6e820c765500014db0418ecaa00029ea0031d95400053cc0063b2a8000c6f71c8765500018dae390ecaa00021fa1e21d95400043ec3c43b2a8000c777188765500018eee290ecaa000399e0521d954000637b8a43b2a8000e677148765500018cee290ecaa00031b5c521d95400073238a43b2a80cee6741487655019dcc88290ecaa0003998c521d95400073298a43b2a800087e8708765500010fb0e10ecaa018e1fa1f30d95400043ec3e61b2a8063a3e84cc3655000147b09986caa00021fa1c20d95400043ec3841b2a8063a3e8408365500014bd06106caa00029760c20d95400053b40841b2a8000a758108365500c70fd0f886caa00021f61f10d95400053741621b2a8000a6d82c436550001cca43886caa00039948510d95400043f43821b2a800087d8704365500c747d08086caa00028f61010d95400052f41821b2a8000a5d8304365500014dd04086caa00029b60810d95400043fc2ae2b2a80008bf845c565500010fd0fa8acaa00061f21d51595400063bb8aa2b2a8000ce77148565500039c8e290acaa00039954521595400043fc3aca32a800087d819d865500014ed03310caa00029d60662195400043f436e232a800087f87d8465500018eae3b08caa00021f61e611954000537414c232a8000a6d8298465500010ff0eb08caa00021f61c61195400052f418c232a8000a5d8318465500014dd04308caa00029b60861195400063ab88c232a8000a3e86d0465500018dced908caa00031b9d92119540006b2b8a4232a8000e67614846550001cc8c2908caa0003c9d0521195403153c4322032a8000f31414406550001ec242880caa00029ea0243195400053cc048632a800087d8790865500014ed03210caa00029d606421954003c3f4386432a800087d870c865500c547d08190caa00028f61032195400053b4086432a8000a75810c865500014f500190caa00029e600321954003c3fc0ae232a8007c77815c4655000f0fd0f208caa00021f61e4119540005374148232a8000a6d82904655000f0fd0f188caa00021f61e3119540005374146232a8000a6d828c4655000f0fd0e188caa00021f61c31195403151f4206232a8000a3d840c465500014dd04188caa00029b60831195400053d4006232a8000a79800c465500c547d09908caa00028f6132119540007174264232a8000e2d84c84655017b8dee3908caa00031b5c7211954003c3f43c42
  | 12 => 0x21fe15764cb4003c3e42aec996806287f8759750d01218bce7296cb2023b179cc52d96400053ac08a5b2c80bbc5e73d4765900018bae7a8ecb200061fe1d51d96405d62f39aa3b2c8000c5d7354765900018eae2a8ecb2033f339cf21d964000666b9e43b2c80b9cce73487659000199ae690ecb20007399c521d964000672b8a43b2c8000e6551487659000147b0929acb200028f61053596400443e43aa2b2c8000a3f8454565900018eee2a8acb20007399c5215964000672b8a42b2c8000e655148565900c70ff0eb2ea9200223721d3158e4000e7338a42b1c8000ce5714856390001ccaa290ac720003b14c52158e400077090a20b1c800387c855db53900010fb0fb2ea72000e97a0f65d4e4000477c12eca9c80028ec825d953900070fd0fb2aa72000e97a0f6554e4001d4f41ecba1c80038bf865c343900758bcc63aa8720003171d56350e400466c382c6a1c8040c3f76dd5439007587eec3aa872000e2fa1f6550e400070f29acaa1c8000e1f6554d4390001a76ebb82872001e1fa1f7558a400043ec0eeab148000c6f21dd5629000187eeba1ac5200030fdd54358a4001e4e39a86b14800087f855c5629000f0f90ab8ac52000237e0d7158a4001c6e41ae2b14800087e87d45629000f0f90fa8ac5200021fa1d5158a400043e43aa2b1480088ec8748562900018deea90ac5202e31b1d52158a4000673b8a42b148000e655148562900010ff0eb2ea5200021fe157654a400443e43acaa94800087f855d9329000f0f90abb2652023b1798c754ca400446e43ac69948000c5c7558d329000147b0829ecaa00028f61252d95400053b408a5b2a8000a758114b655000147b0928ecaa00029ba0a51d954000536c14a3b2a800187f8754765500018eae2a8ecaa00029ba0851d954000536c10a3b2a8000ce77148765500039c8e290ecaa00039994521d954000732a8a43b2a8000a768198b65500014eb03316caa00031d5c761d954000537414c3b2a8000a6d8298765500014bd0630ecaa00029760c61d954000537410c3b2a8000a6d8218765500018eae230ecaa00038d18541d9540006b3b8a43b2a8000e67614876550001cc8c290ecaa0003c9d0521d954031d3c43221b2a8000f31414436550001ec242886caa000297a0f74d95400052ec1ee9b2a8063a3e849cf655000147b0939ecaa000317dce73d95400052f41ee5b2a8000a5d83dcb65500014ed03396caa00029d60672d954031d1f420e5b2a8000a3d841cb65500010fb0f216caa00029da0642d95400053ac0c85b2a800087e870cb65500010fb0e196caa018e8fa1032d95400051ec2065b2a8000a76810cb65500014eb02196caa00029ea0032d95400053cc0065b2a8000a6e829c765500014db0538ecaa00031de0571d954031d1f420e3b2a8000a3d841c765
  | 13 => 0x62ec1cedaa2a00087f819db54540010fb033b6a8a80031bc8676d51500063690cedaa2a04287c865cb545400163b06322a8a80021fa1b725515010c3ec3ea9b1aa0aa87f8755363540430fb0fa8ec6a808697a0f51d8d5000e7338a43b1aa000ce5714876354001ccaa290ec6a820b5614f7054d5001c5e422eda1aa00787c851d943540018bca63b286a82af0f1937550d5001c5f43ec8a1aa000c3f75d91435400f2790eaa286a801a8f2195450d500143e42ae9b12a000c777154762540031df0e90ec4a8007399c521d895000672b8a43b12a000e655148762540d70f90cba6a4a80861f61f63d49500043f436e8a92a08d87e87d8d525400d0f90b3b684a80221f219755095003c3e428ec992a00787c865d250540c7878c8ba4a0a801e1f61f639415010e2f39ec7282a00787c865ca50540458d8c4b94a0a818a1fa1e52590503151f424a4b20a00787c855c564140c50f90ea8ac8280222f21d415905000673b8a42b20a001ce4714856414001ccaa290ac828003a9d0521590503161fa1aed2a0a00087f815da54140010fb02bb4a8280031bc8576950500063690aed2a0a04087f865ce54140818bcc6b9ca8280223721d3158c5000e7338a42b18a000ce5714856314001ccaa290ac628003b14c52158c503143e43ac8a98a04087f855d943140111790eb2286280028f61a5450c502070f31ca8a18a007c5c7558d431400f2b90ea9a862809a97e195350c500070eb22a6a18a00287d85dd162140390fd0f2a2c4280729ba0a54588500e43e43aa6b10a00787c855c562140011bf06b8ac42800e3720d71588500e43e43aa2b10a0088ec8748562140019cee290ac4280039954521588500343ec2aeda10a007c3e75593421400d93cc8b9e84280032759173d08500043ec36eaa10a0088bc87591421411f0ff0abb264280223721d634c85003e2e3aac6990a0088ec8758932140010ff03bb2a0280021f60776540500063790eeca80a000c6d21dd950140c50f90eb22a02818b0f1d1645405010c3ec36e6a80a021c5e63dcd50140390f90eb12a0280731b1c9625405035c3f438a4b2e8000a758114965d00030f90ea8acba00031ddc5515974000673b8a42b2e8001ce47148565d0001ccaa290acba001e1fa1f7558f400043ec0eeab1e800087f855c563d000f0f90ab8ac7a00021fa1f5158f4003c3e43ea2b1e800087e8754563d00010f90ea8ac7a00072d1c54158f4000c6e43a62b1e8000c6f75c8563d017b8d8eb90ac7a00031bdd52158f405c6363aa42b1e8000ce77148563d00039c8e290ac7a0003995452158f4063f53a0a42b1e8000ec53148563d01550ff0eb2ea7a02ae1fe157654f4001c3e43acaa9e80018ec8748562d00019cee290ac5a0007391c52158b4000732a8a42b16800287c855db52d00050fb0bbb2a5a0
  | 14 => 0xe841c9639400153b08392c728002b5a047258e500056ac08e4b1ca008ada801c963940475b300392c72814b93d4a5258e500456d404a4b1ca000ad98094963940a54bd0b212c728002976164258e500056b40c84b1ca000ad58190963940115b500212c728002b66004258e502952f42ce2b1ca000a5d859c5639400159d0538ac728002b360a7158e5011d2f428e2b1ca000a5d851c5639400153d0838ac728002a76107158e5000567410e2b1ca000acd821c563940115b50038ac72808eb66007158e5000567414a2b1ca000acd8294563940115b50128ac728002b66025158e502972bc0aa2b1ca052a5e8590563940014bb0b20ac728002b3a0a4158e5000566c1482b1ca0008de8710563940011bb0e20ac72814a97a144158e500052ec2882b1ca000ace82105639400159b0420ac728022b6a004158e500056cc0082b1ca000e4f51c856394001c9aa390ac72814a97a162158e500052ec2c42b1ca000e55518856394001caaa290ac728003b1e052158e500076338a42b1ca000ec5714856394001c9ea290ac728003b19452158e5000726a8a42b1ca000ec5514856394001c8aa290ac728003b1d052158e500076220a42b1ca052a5e8508563940014bb0a10ac72814a97a171058e500052ec2e20b1ca000ace82c41639400159b05882c728003b14871058e500076290a20b1ca021c5e635db53940c70ff0eb26a72818f0f9d164d4e5001d2fc32c7a9ca000c5d7658f53940070ff0cb86a7280871798d70d4e500066cb1ee0a9ca03a87c8759153940074bd06b22a72800e97e196354e5011e2fbb2c6a9ca026c5e63dc15394105ab6e7b82a72800e2f21176d0e5031e1f2a2eda1ca040c5e63dd5439400187eed2a287281038798e5450e502962e3aac6a1ca00795c8754d43940074bf0ca9a872800317dd95350e500062fbacc6b14a08ec5c7598d6294001c9ca4b1ac5280021fa1e5458a5011537414a8b14a02287e8715162940014bb062a2c52808a9ba085458a501143f43ea6b14a08e87c8754d62940450fd0fa8ac5280031d5c55158a500447643a42b14a000ce7714856294001ccaa290ac52800e37a0d76d0a500062f31aeba14a000c3d7559342940011bf0cb9e852800237e1d63d0a500046ec3ac7a14a052c5e7558f42940018baeab1e85280031798f7550a500445e43ac8a14a000c3f7559142940111b907bb265282431798f754ca500446e43ac6994a052c5c7558d32940c70ff0eb26a12818f0f9d164d42501343fc32e7a84a026c5e635cf50940450ff0eb16a12808b1b9c962d42500051ec2c83b22a000a3d85107645400153b0620ec8a8002ae60041d915000e7338a43b22a000ce5714876454001ccaa290ec8a8003a910521d91500045fc3ac8322a063c5f655cc64540432bd073b6a8a800317a0e76d515000
  | 15 => 0xaba0c0992ff175cf51181325f62eb9aa23026401c7671544604c8018eae2a88c09900b335cd211813200e7338a423026400ce571484604c801ccaa2908c09900339dc5215935000e7238a42b26a000e655148564d400f87ee9bb2a9a80f21f61b72553501e637316e4aa6a02687c8755163d40110f90ab8ac7a809a1f21d5158f5000e7338a42b1ea000ce57148563d4001ccaa290ac7a818a1fe1975d0f500443e42aeca1ea0038bc8759143d400f2790eaa287a8003875516350f5000c7643a42b16a000ce77148562d4001ccaa290ac5a81aa1f61b7454b503561f326e8a96a02687c8758d52d40110fd0bbb285a80221f215764cb5001c6f41ee4b24a0008dd83dc964940010fd0f292c92818e8fa12525925031c3f438a4b24a063a3e8414964940014eb02292c92818e1fa1f515925031d1f426a2b24a0088bc87505649400147f0aa0ac92800339dc5215925000e7238a42b24a000e65514856494001d4e8290ac92818e8fe1d64952500061fc3ac92a4a063c3f71592549400187ae2b24a9280038bc8564952500071690ac92a4a00087f865ce54940818bcc6b9ca9280031798d7095250004bdc32e12a4a062c7b865c254940018f6c2b84a9280031e5857095250006b590ae12a4a000d69215c254940750ff0cb98a9280eb1798d73152501d62fc32e62a4a03a85f865cc54940758b90cb98a92818f17d91731525031e2eb22e62a4a000c5f615cc54940018bac2b98a92800353c857315250006a690ae62a4a007d5a605cc54940018bcc6b80a92800297e1a5498e500070f324a931ca000e1d6495263940016b3012a4c7280025761c5498e500052ec30a931ca000a5f8694a6394001c9cc5294c728002976185298e50005aac08a531ca000ace82986639400159b0530cc7280029761b5198e500052fc32a331ca000a5d865466394001caac2a8cc728343935972198e5060f26b2a4331ca000ec6614866394001d8ac290cc728003d15452198e500052ec2c62b1ca000ace828c5639400159b0518ac7280223721d3158e5000e7338a42b1ca000ce5714856394001ccaa290ac728003b18c52158e500076298a42b1ca000b4c825d563940818beed2a2c728003875925458e50005acc04a8b1ca00095d8715163940014bb0c2a2c7280eb17dd85458e504862fbb4a4b1ca000a5d8614963940016ab02292c728002b3a0a6158e5000566c14c2b1ca0bbc5f76d4563941758beeca8ac728003959855158e500072ab0aa2b1ca0cfccf76c85639417399eec90ac728003b19852158e5000762b0a42b1ca000f4551485639400159f04baac728002b32097558e500052fc2ae8b1ca023a5e851d163940014bb0a3a2c72814b87d525458e500056dc02a8b1ca008ad88055163940014bf0ab92c72808e97a147258e500052ec28e4b1ca000a9
  | 16 => 0x1d953200636b8a43b2a6400e6471487654c801cce8290eca990039910521d95326cf3318a43b2a64d9e6531487654c91f4bb06386ca990021fa1f10d95320043ec3e21b2a648fa6e82c43654c8014db05886ca990039948710d95320073290a21b2a640087e87043654c8010fb0e086ca990028fa1010d95320051ec2021b2a6490a5e83043654c8014bb06086ca9923e9ba0810d953200536c1021b2a640087f855c5654c8011bf06b8aca990021fa1f515953200c3e43aa2b2a6400c7771545654c8031d90e90aca9900339dc5215953200732a8a42b2a640087f87594654c8010fd0db88ca990021fe1f61195320063ab8ec232a640087d87984654c9b14db05308ca990021fe1d61195326bd2fc1ac232a640087d87184654c8018eae2308ca9923a9b219211953247e373b24232a6400d6571484654c801ccec2908ca9901e1fe05711953203e3bc0ae232a6400c77315c4654c8018e862b88ca990031bc8571195320063b10ae232a6400c75215c4654c8018be60b88ca9901e1fa1e41195320043ec3c8232a648da6e82904654c8014db05208ca9901e1fa1c41195320043ec388232a648ea5e83104654c8014bb06208ca992369ba08411953200536c108232a6400a7a80104654c8014f300208ca9900393e0d21195326b72641a4232a648da6f81484654c91bccf02908ca992e31bdc521195325c73338a4232a6400c6d71484654c971ccae2908ca99003195c5211953200733a0a4232a6400e6441484654c9adccc62908ca9935b994c521195326b7279824232a640787e87c40654c8010fb0f880ca992369ba0b101953200536c162032a6400c7571c40654c801cca43880ca9923a97a0e10195320052ec1c2032a6400c7571440654c801cca42880ca9901e1fa1c10195320043ec382032a6400a3e84040654c80147b08080ca9923a97a0c10195320052ec182032a648da6e82040654c8014db04080ca99007399c521d913200672b8a43b226400e6551487644c9ab8bae7b2cc899353175cc659913269e36b90cb32264d2c9d73d92644c8010fd0fb2ac8990021fa1c65591320043ec0eeab226400c6f21dd5644c8010ff0ab8ac89901e1f21571591320047dc02e2b2264088f8805c5644c8010fd0fa8ac89901e1f21f51591320043f43aa2b22640087c87545644c8031d90e90ac8990031bdd521591325c6363aa42b226400ce771485644c8039c8e290ac8990039954521591320045fc3ac8322640687c855db544c80147b09b2ca8990021fe1576551320343f43ecaaa2640787c855d8544c9218bce7b28a89900a3721973151320062fb2ae62a26407c5c655cc544c8019cee290ec0990039954521d81325e62eb98cb302640087e87d95604c8010fd0e32ac0993471bdc865581320047dc3ac0302640087f855d0604c80f0f90
  | 17 => 0x6840787e85dcd60d08010fb0bb9ac1a1003395c5215834200732a8a42b0684018f88744160d0801dc242882c1a10028f61253d95420062eb9ca7b2a8400a3d8414f655080517b09b8ecaa10061fe1d51d95420051fc22a3b2a8400c757154765508019cee290ecaa1007391c521d954200732a8a43b2a84b6c3f75dd165508011bf06b8acaa100e3720d71595420047dc02e2b2a84088f8805c565508030f90ea8acaa10031ddc5515954200c7643a42b2a8400ce77148565508039c8e290acaa10039954521595420043fc3aca32a846a87d87d9754508019cee290ec6a1007391c521d8d4200732a8a43b1a840087f855c3635080f0f90ab86c6a100e1fa1676d4d420043fc3acba9a840387c87595535080d1dd0db92a6a11030f1db7550d4200696396eaa1a843ac3c761d54350801c3ca7b2a86a100e2f21d6550d420070eb2aa6a1a8431b8c8254d43508010ff0ab9ec0a101e1f21573d814200673b8a43b028401ce4714876050801ccaa290ec0a10023ee1d60181420043fc0aea3028400c6f215d4605080199e42b98c0a10233688173181420066c902e630284008bd87d0c605080187aeba18c0a1002ae60343181420061ebaa863028403c9e7350c60508019ce42b88c0a10031da1571181420063ac2ae23028400cb7435c4605080196a86b88c0a100339a09711814200672c12e23028408cb7405c460508119e480b88c0a10232d501711814204673902e23028408ce5205c4605080f0ff0fa88c0a10021f61f51181425fe1eba6a230284bbc5e73d4460508018bae7a88c0a10071d9c751181420063ab8ea2302840087f8754460508010fb0ea88c0a12fb0f5d151181425d62f39aa23028400c5d7354460508038ece2a88c0a10031d5c551181425c6373aa423028400c6d75484605080595ae8908c0a12e7339cd211814200666b9a423028401ce67148460508019cae2908c0a100399545211814200536c14a3b2a640187f87547654c8018eae2a8eca990029b60851d953200673b8a43b2a6400e6651487654c801ccaa290eca990031d5c761d95326d536c14c3b2a6400c7571187654c9214d90c90eca992371b9d921d9532006b3b8a43b2a6400e6761487654c801cc8c290eca993569760e74d95320061eba0e9b2a6400c6f21dc7654c8018ec43b8eca990031d48771d95320043ec3ce3b2a648fa6e829c7654c9b54db0538eca990031de0571d95320063790ae3b2a648fa6e821c7654c9214db0438eca990021fa1e41d95320043ec3c83b2a648fa6e82907654c8014db0520eca990021fa1c41d95320043ec3883b2a6490a5e83107654c8014bb0620eca9923e9ba0841d953200536c1083b2a6400a7a80107654c8014f30020eca9923e9be0521d953247f33c0a43b2a6400c6f71487654c801ccee290eca9900319dc52
  | 18 => 0x98fc5e8690acba10f29be0521597421e733c0a42b2e8400c6f7148565d0801ccce290acba10031b5c5215974200732b8a42b2e8400c657148565d098fcce8290acba131f9910521597420073318a42b2e8400e653148565d080d47d09382cba100297a0e70597420052ec1ce0b2e840087e87cc165d08010fb0f982cba101a8fa1330597420051ec2660b2e8406a3e840c165d080147b08182cba10021fa1f10597420043ec3e20b2e843ca6e82c4165d08014db05882cba10039948710597420073290a20b2e840087e8704165d08010fb0e082cba101a8fa1010597420051ec2020b2e8400a5e8304165d08014bb06082cba10f29ba08105974200536c1020b2e84068de878c563d08014bd0b18ac7a1002976163158f4200566c1462b1e84018dc874c563d08019cae290ac7a1003995452158f420076318a42b1e8400ec53148563d080f0fd0bb82c7a10021f6177058f420354f420eab1e842ba9d841d563d08014bd0b38ac7a1002976167158f4218d67414e2b1e8400acd829c563d08014bd0a38ac7a1002976147158f420354f420e2b1e842ba9d841c563d086359d0438ac7a1002b36087158f420056d400e2b1e8400ad9801c563d09b9c9e43a8ac7a132e976165158f4218d67414a2b1e8400acd8294563d0801caf02a8ac7a136f93c855158f426df2b10aa2b1e84dbe552154563d09954bd0a28ac7a10c6b3a085158f4200566c10a2b1e8431acf8148563d0863d8f0290ac7a1003b19c52158f4200762b8a42b1e8400e4f5148563d0801d8ca290ac7a1003935452158f4200762a8a42b1e8400e455148563d098fd8e8290ac7a131fb11052158f420052f42ee0b1e8400a5d85dc163d080d53d09b82c7a10aea76137058f420052f42ce0b1e8400a5d859c163d080d53d09382c7a1002b3e097058f420066cb80e0b1e8400a5e85c4163d08014bb0b882c7a10c6b3a0b1058f4200566c1620b1e8400ec521c4163d0801d8a42882c7a100237a1c1058f420046ec3820b1e8400a5e8504163d08014bb0a082c7a101aa7a101058f420054ec2020b1e8431ace8204163d080159b04082c7a101a37e1d63d4f4201c3e43acaa9e84068dc8758d53d0881c3cc7baa87a10eb8798c7550f4201d4f41acaa1e8400e1e5359543d080147d0eb2a87a10028f21d6550f420070f41acaa1e8400e1d8359543d080d87ee6b2a87a101b87dcd6550f425370f192caa1e84a6e1c3259543d080147f02b2a87a10028f6056550f420070f98acaa1e8400e1d3159543d094dc5e42b2a87a10038b4856550f420070f982caa1e8400a9f8654d43d0801c3acaa9a87a10022fe1d43983425fe1f3a6a330684bec3e7454660d080595ce890cc1a1007399c5219834200672b8a433068400e655148660d0801dc242884c1a100e37a0f75583420046ec1eeab
  | 19 => 0xeb17e1973151521d62e432e62a2a46ac5f645cc54548d58bac8b98a8a901f17d89731515203ea7b12e62a2a400c5f615cc54548018bac2b98a8a900353c857315152006a690ae62a2a400ce7714876354801ccaa290ec6a9003b18c521d8d523543ec3ec9a9aa46ac3e74d9353548750fd0fb22a6a90721fa1b7054d520143ec2ceda1aa4038be849db43548d587ca93b686a900a1fa1b7550d522062e31eeaa1aa400c3c769514354881c38c72a286a901e5721d5350d5201d2e432a6a1aa48f87f855cf60548019cee290ec0a90039954521d81520047dc3ac0302a4dda7b8558060548010fb0f2a0c0a90029760c54181520043ec3ea6302a42687f8754c60548010fb0fa88c0a90031d5c751181525f43ec3aa2302a402c6d7548460548039cce2908c0a9003395c5211815200732a8a42302a40787f815c665d080f8ef02b8ccba132f1d905719974265e3aa0ae332e8400c6f215c665d08018ec42b8ccba10031d485719974203c3f43c6332e840087d878c665d08854dd0518ccba10029b60a319974203c3f4386332e840087d870c665d080d47d0818ccba10028f6103199742215374106332e8400a6d820c665d08014f50018ccba10029e600319974221537c0a4332e8442e678148665d09718dee290ccba12e3999c5219974200636b8a4332e84b8e657148665d08018cae290ccba131f99d05219974263f3220a4332e8400e663148665d0801cca6290ccba101e1fa1f30997420043ec3e6132e8406a3e84cc265d080147b09984cba101e1fa1f10997420043ec3e2132e8442a6e82c4265d08014db05884cba10039948710997420073290a2132e840787e8704265d08010fb0e084cba101a8fa1010997420051ec202132e8400a5e8304265d08014bb06084cba110a9ba08109974200536c102132e8406a3e8494d65d080d47d0829acba100a2f21171597420343f43ca2b2e8400a6d8294565d08030f90ea8acba10031ddc551597426543f438a2b2e8400a6d8214565d08019cae290acba100399945215974200732a8a42b2e8406a3e849cd65d080147b0939acba10029ea0273597420053cc04e6b2e8406a3e841cd65d080147b0839acba132b0fd0f71597420063790ee2b2e84cb87d879c565d08794dd0538acba10029b60a71597420051fc22e2b2e8406a3c845c565d080187f08b8acba132f0f211715974265e1fa1ae2b2e8400c77815c565d08018de42b8acba10031d88571597420063a90ae2b2e84ca87e871c565d08794dd0438acba10029b60871597420351f42662b2e8400a3d84cc565d08010fd0f18acba10021f61e31597421e53741462b2e8400a6d828c565d08010fd0e18acba10021f61c31597420351f42062b2e8400a3d840c565d08794dd0418acba10029b60831597420053d40062b2e8400a79800c565d
  | 20 => 0x4e3b4a8a9a863db1d859515350c81a3eeb2a2a6a180e5721d5454d430362e3b2a8a9a8606d1c745515350c075390caa2a6a181b271d95454d4303f0e32aa8a9a8603b1c875515350c0da390eaa2a6a180ec7a195454d4301d8e432a8a9a8607e1c865515350c0fc3eecaa2a6a181b479d95454d430368e3b2a8a9a8607e1c765515350c0163f04aa2a6a1a9b479c95454d435368e392a8a9a86e2b1f815515350dc563b02aa2a6a1b8747dc55454d4370e8eb8aa8a9a86e0f0f215515350dc1e1a42aa2a6a1802c72015454d43034cf426e0a9a8600d1d54dc15350d578bae7b2ec4a1803938cb65d89435562eb98cbb1286018ef874876250c6399ae690ec4a1803395c521d894300732a8a43b12860087e87d956250c010fd0e32ac4a180e2f61371d81435de1eba6a3b0286bac3d745476050c0117b0fa0ec0a18072d1c541d814301e4eba263b0286cfcad74c876050d7395ae890ec0a180339dc521d814300e7238a43b028600e65514876050c01d4e8290ec0a1803b14c521d81430043f43ecab028600c6c72d956050c018e8e3b2ac0a18021fa1c655814300636390cab028600c74711956050c018decbb92c0a18031b19772581430063bb2ee2b028600c7465dc56050c011f70eb00c0a18021fe15721814303c3e42ae43028601c76715446050c018eae2a88c0a1807399c5211814300672b8a423028600e65514846050c0f0f90bb8ac9a900a1f215715935235c3e43aa2b26a400c777154564d48058d8ea90ac9a900339dc5215935200e7238a42b26a400e655148564d48810ff0cb9ca9a91031798d73953520063bb8aa2b1ea401ce67148563d48019cae290ac7a9003995452158f5235c3e43ac8a9ea40287c855db43d480d95cc8b9687a900a1f2157650f5201c5e43ac8a1ea4dfa3d8695143d4881c3cc72a287a923a97e195350f520070eb22a6a1ea400c3d7495260d48818bce72a4c1a90029e60254983522962fa8ae7306a400ccf215ce60d48119b440b9cc1a90033648173983520043fc3aa7306a403c5e7354e60d480f0fd0ab8cc1a90021fe1d51983525d62f39aa3306a400c5d7354660d48018eae2a8cc1a900b1b9d521983525ce6739a43306a400ccd7348660d48039cce290cc1a9003395c5219835200732a8a43306a40787e85dcd60d48018eee2a8ac1a9007399c5215835200672b8a42b06a400e655148560d48050fb0bb8ec8a91aa1f61f51d91523551f426a3b22a400c7571d47645497d0fb0ea8ec8a900b1b5d521d915200e7338a43b22a400ce5714876454801ccaa290ec8a937b0f5d764991520045fc3ac8322a46aa3d87d92545480187b0fb24a8a92db8bc8764951520071690ec92a2a48d87c865ce54548818b8c6b9ca8a90721f21970951523561fbaec8aa2a43a87c865cc54548758b8c6b98a8a90
  | 21 => 0x87c436550c014dd05886caa18029b60b10d95430073290e21b2a8600e65214436550c010fd0e086caa18021f61c10d954355d1f42021b2a8600a3d840436550c814bd06086caa18029760c10d95430053741021b2a8600a6d820436550d6f87eebba2caa18021fe1571595430043f43ea2b2a860187c875456550c018eee2a8acaa180339dc5215954300e7238a42b2a8600e65514856550c010ff0eb28caa181e8f212761954303d2e41cec32a863ad1d745cc6550c014ed03310caa18029d60662195430043f436e232a860087f87d846550c018eae3b08caa18021f61e611954300537414c232a8600a6d829846550c010ff0eb08caa18021f61c611954300537410c232a8600a6d821846550c018eae2308caa18029ea0061195430053cc00c232a863aa3c865046550c01c68c2a08caa1aaa97219311954373e373b64232a86e6c6e764846550c01acae2908caa180399d8521195430073230a4232a8600f27414846550c01e8a62908caa181e1fa1e42195430043ec3c8432a8600a76819086550c014eb03210caa181e1fe05711954303e3bc0ae232a8600c5f305c46550c0f0fd0f208caa18021f61e4119543005374148232a8600a6d829046550d5547d09908caa18028f6132119543007174264232a8600e2d84c846550d7bc5ce9908caa1af78b5d321195435ef2739e4232a86bde4d73c846550d7b8dee3908caa18031b5c7211954372f279864232a860787e878846550c010fb0f108caa1ae29b60a21195430063ab8c4232a8600a5f834846550c754b906908caa18031d5c521195435c7173a24232a86b8e2d744846550c01c9f06908caa1b8f9320d21195435c72739a4232a86b8e4d734846550c01ccf02908caa1ae31bdc521195435c73338a4232a8600c6d714846550d71ccae2908caa1803195c5211954372733a0a4232a86e4e64414846550dc7ccc62908caa1b8f994c5211954371f279824232a860787e870846550c010fb0e108caa1af69ba08211954303c3f4384032a860087d870806550d5547d08100caa18028f61020195431d52f4184032a8600a5d830806550c014ed02100caa18029d604201954303c3f43e2032a860087d87c406550c014dd05880caa18029b60b10195430063ab8e2032a8600e6521c406550c754bd07080caa18029760e10195430051fc222032a86aaa3c844406550c018eae2880caa180399485101954303c3f4382032a860087d870406550d5547d08080caa18028f61010195431d52f4182032a8600a5d830406550c014dd04080caa18029b608101954354ec6192e52a28640c5c73d955450c81878edb2aa8a181f0f1d865551430349ec2ee4aa2860399e83dc95450c0733d06382a8a1aaf171db6554d4303e2e3b0caa9a863ad1f751d15350c752bd0faa2a6a181b171db5454d43036
  | 22 => 0x908c0a980399545211815335c3f438a4b2e8600a758114965d0c030f90ea8acba18031ddc5515974300673b8a42b2e8601ce47148565d0c01ccaa290acba181b0fdd7765534300c7643a42b168600ce77148562d0c039c8e290ac5a1803995452158b430043fc2ae5306860787c855ca60d0c039cce290cc1a1803395c5219834300732a8a433068600ee12144260d0cc7878e9baac1a180317a0f75583430062ec1eeab068663c5e43dd560d0cc78ba87baac1a18021f60775583433161e3a0eab06860087f855c560d0c0f0f90ab8ac1a180e2f21171583430043f43ea2b06860787c87d4560d0d77878e9a8ac1a18021fa1d51583430043e43aa2b0686bac3c7454560d0c011790ea0ac1a18031bdd721583435ee363ae42b0686cfcac74c8560d0c018deea90ac1a1ae31b1d521583435ce563a242b068600ce77148560d0c039c8e290ac1a180399545215834363f53a0a42b0686018f88744160d0c01d6282882c1a1803b848510583430051ec24a5b2a8600c6d7294b6550c014ed02296caa18029d60452d95430051ec24a3b2a8600a6e829476550c014db0528ecaa18061fe1d51d95430063ab8aa3b2a8600a6e821476550c014db0428ecaa180339dc521d954300e7238a43b2a8600e66514876550c01ccaa290ecaa18029da0662d95430053ac0cc5b2a8600c7571d876550c014dd0530ecaa18029b60a61d954300537410c3b2a8600a6d821876550c018eae230ecaa18029ea0061d95430053cc00c3b2a8640a3c865076550c01c68c2a0ecaa1aae9721931d95430072a30a63b2a8600d67714876550c01ccec290ecaa18039918521d954300793a0a43b2a8600f45314876550d574bb07b96caa18029da0672d95430053ac0ce5b2a86aba3e841cb6550c8147b08396caa18031b5c872d95432043f43c85b2a860087d8790b6550c014ed03216caa18029d60642d95430043ec3ce3b2a8600a6e829c76550c014db0538ecaa18031de0571d954355d1f420e3b2a8640a3d841c76550c814bd0638ecaa1aae9760c71d954300537410e3b2a8600a6d821c76550c014f50038ecaa18029e60071d95432043f43c83b2a860087d879076550c014dd0520ecaa18029b60a41d954300637b8e43b2a8600c6d71c876550c010fd0f10ecaa18021f61e21d95430063bb8c43b2a8600c77714876550c01ccf0290ecaa18031bdc521d954300733b8a43b2a8600c67714876550c018dae290ecaa1803991c521d954374733a0a43b2a86e8e64414876550dcdccc6290ecaa1b9b994c521d95430043f43843b2a860087d870876550c8147b09b86caa1aae9760c70d95430043f43841b2a860087d870836550d5747d08106caa18028f61020d95432052f41841b2a8600a5d830836550c014ed02106caa18029d60420d95430043f43e21b2a860087d
  | 23 => 0x58c545ef46aa642b18a8bde4f51c856315001c9aa390ac62a2f7931432158c5403d2f42c42b18a800a5d85885631518f59b0510ac62a003955462158c5403d2f42a42b18a8b8e4f524856315001caaa290ac62a2e393a152158c5400726c2a42b18a8e3e4f75485631518fc9ea890ac62a31fa39512158c5463f26aa242b18a8b8e8d544856315001d8f0290ac62a003b19c52158c5400762b8a42b18a8b8e4f514856315171d8ca290ac62a003935452158c545c762a8a42b18a800e4551485631518fd8e8290ac62a31fb11052158c545c72628242b18a807a5e8508563150014bb0a10ac62a31ab3a082158c5403d2f42ee0b18a83aa5d85dc163151058b8ebb82c62a01aa7a137058c541d54ec26e0b18a807a5e859c1631500f4b90ab82c62a002b3e097058c5400566412e0b18a807a5c851c1631500f4bd0b902c62a002976172058c540046f43840b18a8008dd87081631500f4bd0a102c62a002976142058c540354f42040b18a800a9d8408163150015ad02102c62a002b56042058c5403d2f42e20b18a800a5d85c41631500159d05882c62a002b360b1058c540076290e20b18a807a5c8584163150014bf0a882c62a01e972151058c540054fc2220b18a806a9c844416315001d8a42882c62a00237a1c1058c540046ec3820b18a807a5e8504163150014bb0a082c62a01aa7a101058c540054ec2020b18a800ace82041631500159b04082c62a0063b21d215885400673b8a42b10a800e655148562150039cce290cc02a003395c5219805400732a8a43300a800ee12144260150039cce290ac02a003395c5215805400732a8a42b00a8018f8874416015001dc242882c02a01e1fa17725935300673b8a42b26a601ce47148564d4c01ccaa290ac9a981f0fdd376553531e43ec36e4aa6a6018ec8748562d4c0159f0690ac5a980339dc52158b5300732a8a42b16a60787c855ca60d4c018eae2a8cc1a9807399c5219835300672b8a43306a600e655148660d4c0f0f90bb8ac1a980e1f21571583530045fc22e2b06a6068bc845c560d4c010f90ea8ac1a9b3f1b1d721583535ce363aa42b06a601ce67148560d4c019cae290ac1a98039954521583534843fc2ae5b22a601ce6714876454c019cae290ec8a98039954521d91530045fc3ac8322a6aba3f855906454c850f90cb96a8a980e57a0e70d51532062fb2ae72a2a68e87e86dc95454c4d0fd0c382a8a98031ddc551d895300c77c3a43b12a601ce6714876254c019cae290ec4a98039954521d89530361f3a6a9b02a66287f875536054c070fb0bb8ec0a98021f61f51d81535d43ec3aa3b02a6cfc6d75c876054d738daea90ec0a9807399c521d815300672b8a43b02a600e65514876054dd38f2ebb04c0a98023ee1d60181534843fc2ae4302a601ce6714846054c019cae2
  | 24 => 0x6a8038dc835c562d50850f90ea8ac5aa0063b21d2158b54216363aa42b16a800ce77148562d5001ccaa290ac5aa14b17d4573983544862f39ca5306a8bac5e7354660d50018bae6a8cc1aa0031d5c5519835467e6739e43306a800ccd73c8660d517399ce690cc1aa003335cd219835400e7338a43306a800ce57148660d5001ccaa290cc1aa007399c5215835400672b8a42b06a800e655148560d50014bb0b192c72a1021fa1f5158e542052f41ea2b1ca840a5e8354563950031b90e98ac72a00297e153158e5473f2729e42b1ca8e6e4e5348563950019cee290ac72a007391c52158e5400732a8a42b1ca800ec53148563950018eae2a8ac52a0063b21d2158a5400673b8a42b14a801ce4714856295001ccaa290ac52a007399c5219825400672b8a43304a800e65514866095001dc242884c12a0021fa1e53582540051ec20a6b04a800a7a8014d60950014f501a8ac12a00339dc5215825400e7238a42b04a800e655148560950031f10e882c12a0029ee1510582540077090a20b04a800ce77148763550039c8e290ec6aa0039954521d8d541e43ec3ea3b12a800c777154762550031df0e90ec4aa0f31b5d521d895400672b8a43b12a800e655148762550019cee290ec0aa007391c521d815400732a8a43b02a808cd8605ce60550019b2e7b04c0aa0023ee1d60181540043ec3ca4302a800a758114860550018eae3a88c0aa007399c5211815400672b8a42302a800e6551484605500f4bd0b192c62a01e1f2157158c541d43e43aa2b18a83aa5c83545631500d1bd0f18ac62a01e97a163158c540056741462b18a800acd828c563150031b90e98ac62a01e972153158c545ef2629e42b18a8b8e4c5348563150039cce290ac62a003395c52158c5400732a8a42b18a800ec6314856315001d8a6290ac62a20b1714f7058c5403d2e42ee4b18a807a5e859c963150014bb0b392c62a01e972157258c5403d2f428e4b18a83aa5d851c9631500d53d08392c62a0eaa76107258c540056b408e4b18a800ad5811c963150015b500392c62a002b66007258c5403d2e42ee2b18a807a5e859c563150014bb0b38ac62a002b3a0a7158c5400566c14e2b18a800a5f855c5631500f4b90ab8ac62a01e97a147158c541d52ec28e2b18a806a9e841c5631507553b0838ac62a002b3a087158c5400566c10e2b18a800ada801c563150015b30038ac62a0ea97a1d5158c541d52e43aa2b18a8cba5f8454563151974bb08a8ac62a00297e095158c5403d2fc0aa2b18a807e578154563150014b900a8ac62a01e97a172158c540052ec2e42b18a806a9e84c85631500153b0990ac62a2f793d4b2158c545ef2742e42b18a800e4d85c8563151cbc9eeb90ac62a31ba3a132158c5400746c2642b18a8c6e4f54c85631518dd1ca990ac62a31b9355321
  | 25 => 0x780000060040048008004002002800400200300080080040030000000008002000000000400b005800000c00f001803800c0060008008002001002005c002007000000000600100100000040000000008000001000000c0000020000004000000000000800e0010010000000006000000800200a0028000000002001001800800a0000034000004001000000000000000080020040000004012004003807c01400000200300020030000018006008000000800000000180000000090000000000000003800800e000000000800e000002000000200500100080060000058000000004000001000200000000040000030010008004001002800000600e000000000a00000a800000000100e80080040000000014000001000800800e000000800000400000100000020020020000000005000800000800200680180040020028000006000000000000e000000000c006006000000000000a0008014000000006001000000c00280040000000008014002005011000c000000000802c00e0000000000012004004800400c0010068000012003000801800e0030020008000001001800400200d002001000200100600000020000000000000000007800c00c00000200080040000000014004000000000400c000000002400201200000000040010008000006000002800000a0000020008008004001802000200400000080000000008018002000001001c006000000001c0100030020014000001000000400000300080000020060008008000001000000000000e00000140000080000000000009000000c00200500200040040010008038000000000000000000d0000004004000000000000600e0000008000001005801000400000900000000050030028000004001800000c004000004c000006001000000000000000080000000000014002001003001001c00800200100000000010004004002001800000400600180240040000000000000000004800c00000f000002000c009000000800000d0010004002001003802800a00a0000000008003004800c002009003800400c0000018014000000000800400200e0010014004003002000c002000006000001000000280000060000018014000006002000000c007000000c004003000800001a015002001000200500f0000000004000801c00000200000080060020010000000006005000c00001100100000080000000000008006002000000c00a000800400800200200000040060008000000018007800001400300200040020020000000002004000801400e000000000000400900000100040050040000000000000000400000500180040020010030004004000000000c00e002006000000c01000e7338a42b1ea800ce57148563d5001ccaa290ac7aa01a1f2157158b540046fc1ae2b1
  | 26 => 0xc00002422703598000b52b491d780019dc00000033d049a0850000000fbebd60f00540000000000222000059400000000000003f08f0c6f46d728a30b969a2f500036408de7f50001f1c0008fd3c60000000787620800000054663f00000000003bba5b000000045fada18a262c3f2a858966ccb33c8000a401833ae80000000003d80006000002000800400d00000140040010038014002003004800c000000002003000000b0000000030002006800000000001300040080000008048000002000000c006003002800000400000080000080010040008002000000800000600000400100020010038000008007000008c004003000000800e019000800c002001002002801c0030038004000001004800400800e00000040060020030008008006001000402400300180780040070008010004000001000c00800000900600060000000000008000001000c006000005000001600100b000000000200280140080050048030008000002801c0020010040010002008000006c00002a002002c002016000800800200000280200000020018000008000000000000200100000000020000010000002000000800000000100000100040000008000004000002001000200c004002400a0070068008008005000000000400400080780020030008008016002000000001600d00100080020000010008000004000002000800a001000400200100080000100010008050012010000801c0100020010010002001000800000800000100080080000028058008002002800400200000000040040060000000006001000002801600200380000040010008010006001000800000800e000001c00a00000780000060010030018002006000000000200300400080020000018014012003000800c000000000800401e00200080380000000000014002003000800c0020050000004002002000002c0060000000038000006006000c008001002002400000000180000020000008000004000002800000200200100000240030018000004001000800400c005000000001a00100080080000000000004000003001005000c000000001400000100000000000080000008000010000000801200d004001000000300200000040020000004000000000000800200100280080000000010008030005001001400000400a0004000000004800001400e0000000000002000000c00800200080080040010010000004000003001001c002009000c00400300500000000020010000002000001000c0000040000004000001000002800201300380000020000000000002001003000802c004002001000a0000010008002003000000c0000000000000000001000800000000100000200000000030000000005001001c004004002800000600a0050004002000001801400200
  | 27 => 0x144bf0000000000b0d000000000053957a0840af2a5e06a80000006bf4970000000a4c622981cb9600000000000000005e899e93000000000000000000000000000000016d00000009043d50000c6e0005d0aa358c40000a591b58420240edb0f80000f200025e0810000000000000000035f22ad09097000019c43bc328000000069400000000000769c62e0800141000000022540000005e306440004ab45480007a400032900016ce41616285f9a2490f3319a1830061a3ba8800170d7c2ac2b88fee00009281300007142dd80011240003e612652b61973a08fdc7b00002430868ab400019b8000ac090d000124c11a8ea54815a40000006760000000bbf00009a944c8535641e0d4da00058b9b00000000000000000013a00000008ec00043e1f198f80002b38001a400f523e80000009a10598000000000076000000000003c00002d44cd1143184a4801300000000001b100021d8eca00031f0001662d8200000016fead54000c489d03413eb2cb859a00016c8a141c2000047800000000000000009129a90000000f22ad142c800036e00000022e44aa0002cd8f940000000000000000000000163c000000000263531c78d00025397aa97e502070cea035033300015ca00013f2191aec3cf15f8000000000000217087a5c80002b0c964599000091572600042d8a685f600031f8a040ee82e00005b4000cfc680233c6ac8440af1f3ca2236a2b6321c62ec930002699832a7905d9d1d60e6ce34b9025a8e2621d532393bccbd599b4fc1a467b62ab60c960aca20d81040002b01508f98692000000000118ad2800000000006f1000018c9de00037f000117800000000003d4000406a9680422bc2eb08e54d800049b8000c8482a00012956ee000509872cdce2d13d080011849594c800017360fa31700011085c70ae0dddac400066c1fc40c4943227925869817800000000003e017c0e1d5785e3000359c0008c939480000006af000102c00073b000295c000a2b2ec0d640ea00032ba6908c00000a6a8900000000000000d8443900000017283000001318000000000000000023a2c5000186000033e89600000000a5000158e58136a00013664240002c89592991541a4c189c3b73f20000d486692721b6479c0000000b90348000000000000032d000311c00000039a00000000000000000000000000194d1580000b315b41949a718a86940000002fa8001a3e2975c822959869770002090970b9763aa8a9334bae3d9335557ca9d0002b4800000000022c00002244482afd75e3b40002155aae41357995847e051660400000006060bd00000000000000000b6600063282e93b4a982480001a760cd121a1e52e4bdd6ac835145216f0ea80014b68f32e500000d60005dc0000d3e0005b700000000000000d1800000061880000000003d
  | 28 => 0x2a2658608a3f00003b80000001d58fe543289d12e8cb000000041baf88000000000286c00079a000193d1e0a0b0002cd00000000a180018ae34f3b200e4f3ed164f290e15c8be13220d717965dd3fea3d4b40cbe000137086470059c8ff4e7000000035b01f8cf300000014605a75c10000000a860000c04000c3616c3180f14000000000000000f5e6000000036f00000cc7020000000000000d5c0000001756d155ee252d52e9c42c996ddaf297600399b0316cb90000000000b2d24e89f4c142af2150b04060000000000022c0891d20000000828000261c0009e3250274d154434120800189a0005588f250340000000000000a2c46b80016060000001de07a01825b7b519b0e2e15489fb8f688e3000006000004b41b0000000000000000117c2ca5daa9c11fc61661489fc00000000000018f296556d00000000001a2800000062b11800000a22e60d68cb800062900024f80004011da80010200006939798e0e000653800054e00059082f000033d491ac485a00002ba800000014627380013c4b1900000012e800058718f16c200011635d400000006f8000c180000002aa47c2762000007018e00000022880007f300000000000000001dcc3e23ec12c9ae01200a20002cac000c5f0000001a820000000000000d2d00010b825c0000001a4000000000031d8f9000023e06ec00000053280013c24c92549e20000000000000000021d5e80a499102574e42920e1e000000000033429c2b92d29a04d651b8a67c000000682a8080000000000000150c86000179000087f0bd89c80008fb0000290b620001548000a34caf1e108eda30cd215b80015f02175f580001d0a820fc800000074539f0af800068c0031eb58a07fc128b010e98c546649c153060000002d14c3a0004f7223030c7d100000000004eb00000000007960000000000a2500015990cec1b67129512320004d12a599fe09f695a770e2600000000017da2d56b9271c0004a42070000ca29ec14e80000000002d4000028800000035ac00064d5ab80000003e300035d06c001d00000000000004f80000dca0001cc1b204e60000000000cd00003422e346cca6000013cd9c2ae32a400000000c000000000000000000fe8000000000000186e6dc00003986520003da9374262aeb096258572a3c80000f7093e000000000000000058a800119abc22a11541790c6a408800000027c0000000000000000000000000054d1e95280a9c672125580ed5f000000000072f17480000008265a08000000cef00000016b40000000001a0600000000fc00000000027380005a55a8b13c51a7ea49604391aa000213a444298453353270d5d27d56aea4680006330000654916a2722f89d44841d016dac04be20001b425fc0f43a14378d34596c9d379000116426832fb0cd00a01646e9ba9b
  | 29 => 0xb124680de9a7845a076000000189023148c00000005330000fd0000a2048e86c00000001bc00000000002281e9019c48f530b1997e464e31aa1dd7e8a1153e0000c9848a000180579e233233000044e373111ae611de159412a1740000000000000000cb7000000000000000029d8fbcb704451f600009383e2a3a40000006082a8584c000588b14c2fe01b6058000f6e00033234f00008bb1ca800199400000000000000003359b540006b00002ad0000c0c000044ce220000210e59944000000045488c98a000053868eb2700000000000002228001a6c43363935cc498cab6a20000696000000000190a0b54078000000b142e993f425651f1ea1a4c0000000000aa00009950001a0c00000010a2ca8d2c000000356cbae000000000000030733f00000000004488000cea6651aa0001a62bb609380011506954b48ff86327210fb2b188d200025780010f6000000000007400066a2260bd600000000000008a6000000000043e5e18000000000000000000067f0e00698fc665567caf014860003f7a72c67600000017f020c1e3000049830aabd192ab4cbfa000640800140c0004b79e38a78b2c56590bce9e0000000b5c00095c2e82d600007243d18000000672033055c4b4c5202b97bc38a03d00012dc73600000022d0430c6805f17e40889ad0000b240000004760e2c09292249c80017a6afa00018896d233e6678000b1ca8f00000000000944a2a0d547a07c0000d4400000069500000000010000000d1262d4bd2a8000000000000013585c96540000a1e6b141e951da480002e630d161451950e9c403749e0481ae7da9ab6d69491e447e00000032645fe4df5fd108d35c7fe42300001e00003668548000a1e4b21cfd5ba6b6030a13c47a2c32ce07c943400001b00012da0a12d7000000000000000000000000f080011cca31000000024600034280000aa000600201d6fc0000002d0c00007b0000001278000691950400021100000000006a060f97d102e8cb40f99a8000000073a8340000002fb8000000000282000000046552880000000003ae000198a2540cd80000004d20000000000000000000000037500000000c80e439d13fc000b81680b3300000353af917918ea0000021896ba88713201a04d85e80ac1861600cf667280011b800055aadad3a430912987fc0000000e480008e6947000183400042d1f9b3a00000003661e1477422908831d0922d220000000000b130001c0818ad0d1768001528bd41c280000001ef21305080000c16bb8001466cc204c1e74d24afd0000e9da1c26d0000aed6b6ba40ada61000000000009200006eb4608524a6c5a400028d45167350001530000cc000030900000000398001532c7b0002b0833c0004588000000000411ab105de28200018c597602259016358eea4161a8e5ccc4a442
  | 30 => 0x19240000000001220000000000093800000000012661d206100013e40000000d910ca000000000000000000000000003800000000b9a6fd0000000000000544000063a1b40002ac801852b00000000002ae000338000000000021a4ddcbad50a82816a400001a31cd9a6bf900000000000000001088636535000292813c0a313d000000050516633f80008500ee2e1911a0005c40ed83a60000002a38cbc20335c8ac8d420000002c3062800054504354b200006c05a5002b9c6880000e4e55600002b40009a3043000000056b52c000000000000031f54646e80002bc97d40000000d113da2215de91c16a889328e953ce1c0005d91ee560c1ec44db2349bcb9a5b20b017d86f059324806fcc8b0c480e1af01945541f7594a0004f798e4006c202d5b2c9aaa7c0000000138480404e83d0e388735061d806c63cd00000008800006c580017fc00000000000007400001ea18dc0006848000000000634ac945320001048bc0d0e9fc3ac2bd40322ba00002296903860000d9c0004a700000011707f02162bc06dc0005521fb101023715680000b00000001158620d0f24c05f514e61f0000fa18645294f504b57ce04e005000064eab86c8ae301323241870df000048000000008ae000262b59045e57050a130457095326793505663331ac27a0f5e0832f805a1ac28513de04ccef400039b0000000cf76b18000000000000000000000000005580000001b800000001a737d000000084b00000013ec0005fb2b30cb62df169240004a9dd000000040e000000182c2e492b00014257c65770000428d64ac50002c7cd8868b6a99bd55fe0000000000000000000000125a000000000158000000000009ecb553ec86e13cc0000001045a08000242000139460400033102f8c716758bc994000052fad40000a124700d4ce3200004124d179c00058d2db01960000002aa9558ad73e48000000000000000000000065e12b580c00023c14083200002f52e5918837b04b0c08000000516b20108e0000001358000aef00012858c86a81b097d95b2000000000042a5b0000225192008b075800000000064c0d21250000356814800039100016e4000000042307027a00020d0000b3e7a754f0000000a730000f7800000045b14d00007120000000e12860000000069c000210a6145d44e50000000000000000075c00019d0002e88000000241000123e0004fc800000076d0000ce80000000000000ff2000000000000000040a9dac00064355580000008d00e1000123c3ca49200011a2c6f00011455b600007d800000000003c800000000000030a8d4a99e16eabf87667533b314fc7a60003b9024c00050600000018120000002e8c4be39c55d800188800000026480000000000000a5c00000014e16f216b30e0000dd20000c200004260002e90000
  | 31 => 0x981cbc11951dd11e4737002b2fd26c37d01688b8a7c7ca5f22d64798ab90000000b58c6b0c400000001da0000001078000000185400063012300000000000000000000000000363426a00058e00013c85213368000ea2754403000199cbef0002470d3800069a08c822e24900028e400000061c800137a000000000000020b00000000000000001f08bbc5bf15a1360436b3d4ff954c82a000450046c0000000001ca979aa2f268b2843320000000000000263000025400000000000000000004ec8000000000000000000000031e800000055541f8630a882871372ea000024e3ed00000000000001de4d148ce3deb2e11f8cb00002318000907158b050000014416800000000000033201547b12a5a68149e00006201f8a76000663800074a75900011fcf5c8e20a3a39400000053c1b91492b78132a439acc8d660ab46494c7220392f696965e167d8344000d43000266d1a877c00032c40000005c00000000000162209c00018a00026204ecaec4c623600000000000000c7000031b2494c507990000f65112bbb00000000000003f423a000000000000016a60005c90000000399000000019e4643380000000000125000192ec3d000000000000022d3520f1202308d0000000af15d8257596aaed20210d8000bb10d51f389d2296084800097a55d000000140e0002992f78a3600000006800000000002f299b20000980bb133000055280016eaa7f00000000002f3000273d4e4a171f7938c160447000256110a02660695b96ac2ee00029a4000576451800000000043817cc6d61f50b28001406000056000000000014880014cc8780b09eacd7898959db484bbeb04482aea4a2098117b9e1122a000000047d22c00054580000009680001428e4aad616f2e3c4701b629ba07446c0005b8955c61a000000361184601a000000000000001480000000af06b85b8b8a0000000000000d7b00028e8000000000000154c000000277c90abfd0001a20d287d057b2c740004830001388cb28312699aaccee0003cd800000043f00024f58020f74d50000f2059a0ba288c57200d5948bc52c00004350000e50954415afecabc000280ad3c0000000000000fd276f6a280000582e342185c00008523a69124e1843b1031a68d867ac37600013e835d0002f6c5d00000001684a3c9d43dd0000d460000aa800032c66f4b300000005a600000001b494835b91ec00041811022f497c4ee52a84640005c4000054d7721ae0b6000128c0ff21a80011fe0dc2730000e0828953aa82874c00018980000d8000409000000000000000000000000ea000190400007782e4b0c1ee0cfb624e5a1c66b817641c4000000000183c0000003374000b370000001aaccba0350000de88a12fc098073e0000000000000ad400000000000000000000000000420b0f19b8000
  | 32 => 0x9b8810b5e0000001d5400000000027d5b0cadf25709796129ab1b4b5793722773c99da82c00003bb00011eca800e404fd62097b000000000000000000012ac59e1091d2d7f0bc541600007c41eb0001e98c460005a382498fecac67894956e4ced2c2ad88df24446898000000820457ad8d21200028c13841da93a00000017e62c20000000000000000000000020a31015f174e85f01414340000000ef800000000048590dcee268d26701fc4a41f35be86700620003f30878000000636ab84a4494a05919600003a30002d313164da00003a8000afb0001a086220000000000500b024ed8000af44ed4330000000d25419182000000000029d14960000001d3900400b0000a8c00000025d9b8d856a4e0000000000769000005400000000000000000006051ccc0000000000b940000000000000000000000000000056f0000eb19be3400000000000a3800004900000000000000b043305a3121d0b08ae3cc11d40000003840a0c4f60e944f2adcc92d6e6252ce00009514d4215947c00000000007ce87462300000001010002c2c000ac13550ce19c600038b2ab47ae0001dd800148e0000b125100005d4226215c77c00051d9bbc000957414a9dc0009290640000cac000510b254e169131e8919c66c526000000000064b44e2d702063820839f0cbb8ba6200328c0000000000000860c7000000000005c00000b9ce786d200002308ee0002e7a328000000000000000000000000000000003b08001b1c000000000000000000016440000002b414b1ad43220d90000000d3215e800073437f3b8320db1035e00030bce862955bb2fd436a6ff2561a398580a526ba0cd2ea000026900ca745923123478bfe0000000ab0cec6da000000176600038faac00002dc00002381ba274535a0259124551ffa5f50845c3000000000028e43680000000000000000000000000000060c06f4228000ce69b7000112109a25b0000000dda3a842d07911f448830704740005740000cf00000460000f2c28a00034c23640009b500112307dc000000000000041400023c5a9e1a200013c0724b3c0001c34e029a500000009f4d3d298ae452b400009f00000005d500015440000000000cac000c2762e1a44b083c557380000000000001aed7540000000001740108089000000071e0000c3d5d4a6800000000000004e49355650a9b0000000f0400059d1400c360000002c3c7d218f35a12a000047e27e136400006d58c0dd838238c000204db1e0005da27340001323b3a2e80009bc00000005d6c111d88000000818152a504c3209a12780000009d0000000198cbdf000000187e00050c0000aca00000007dc0008cc1b9000000009100000000006056b49eec91ad7f24d8000b1000048631785ecd260003345a7265a27bb0b4a261d6297a6e06e83655b0335
  | 33 => 0xff00000000a78bf461400000000006e200800011dc000230a1ad0946ac0000000000000000000133a6a9142000166a883115903000078f010183d56632f037000054457e000222c0004c72d5275c000000353b3e80005b60000001a5c000000189ca8ace900000009ea000000246c7f89b648300000005541c6a50901862546f2064000000000029800000000014f4684c964b1322885254e0092fa42280000000000000000000327cc5400020e8000000a9231d836d38231e00027cc0000001c8000064063441a10401c639308280004c2a635c387e800000029535300006f7456800084a00001f000113400000000011d64aa4e008592d61b93a300000001400e8b5bc00000039e8999a608da5228000000b5e17ea139a927526c9a9ecc6488f0001c600000000000000000000008813c0002e000000000000001dc96600000002e71c18a8600000003d800000009b00002c8563000317400029360b2029b1872c24f33c13766bd138b3d41e62c804e00000001f000011c8000000000000054c0000aa0000000adc34e835927e6c14ea8000ad400000011e800000000000000002ab00026bc47c0006b6a2d4cc23890e60901aa261e52006fd374000000274400000000000007440005f880000000001f925348b202f0328660b3a05005ba238af000064200009880710b1b3a889c5db03a0168fdabe669a9c68000971660b41c540d2c17e1efc41800022d9df88b0732000000146e4524842870a06053684279ca1ca9f5b5005c3567fa1ad80000000003cf120400000000000000001f40000000be400018d0f58984be800000000000000d60000000419087802464c7e02ff2990a509c54f891c50ea0001e21c280005b50000000000000000161c0001761338001224000000000000000000000002220e00000001934aa75212e94752cad0001c8c44cb8e6532e24968bc45e38d888e857d36480010fc8df567abb800000068ba1780003df5519f8950ed7a1460c8c00038f06ca66559c2f964d8e3971600044c82204040005eba53d7ee9492218000000000544811c6d854010726c04880de5cf00003c40693a11c5400087125b313000000000000000000002032a4cb468f705e99009245e233a0488fb82d60001bcd8cec0f49395eca461fb000000023cd856b000001f00003c0800006e5301908000782a6e02c80000002345a0202c00000000008f00000001f5800000015a2370c298840004522405afcc8c5df0649092000000059c0006f64b7000000000060e800112e1d903e8b18000000542103541e00000000017144c8000000000000000000000000004fd000125e97c2c1907173a58c00000000005c200000007c85be20f978000000000013a80000000000001968612022800145c4db000000039a00027a32780001fd20bacfc31ccd
  | 34 => 0xae57c8e115bc7864ff1fd95f89d60e3b60020002a5110001aa462632534287140004f493812980000003048e2e4f103025cc4acaae081145c0000000003508000bb70000c2d07c9be00000011e8000231000000000000000007da65d26632cd1f2c58000259c000c6c6b42f252d412f040061cf163830860000000595000218c8403f64fb999c0000000000000000000000304c0000000000d7c12e7d3308800000062f0000ef4fe80000000b3cffe3c602189bcafea5004db52c000b5f235b39c7f06d60a7acbcc8a0000001cc00002c70001918240cdb12e00013680000002b401fad8128e00012a000000000019389021dc13293640e520780000000000000000f240000000000f9a2ce3510b899bc000000180880eae62cbaad926476800f0001a38bac0e50c0cf008d24110001a9ca4d5f286bcc2e29f3db000000000002f9b189440001153250a920000000000000515320863427830853f000000000018e03e4f2e7db2250000000442000000046a000000000000036d0002a5417e56442a15cc00000056c34dc9f20000001b4d1da0005de1b2c0000000000000ef6c910000e795ee0001d9057c2086cf43eb3e067e4fb3e0800118039400012e4b00000013a18400000000002d000000000020e80000b614c265c2ba77f0241d8c0001793300000000bf000026c483c0000001420000b7a41c0000e9000000006057dc0000000000000a535409ef8dbe28f0df15487f6205625ab800000001430000000000000000000000041cae1400000000000014b868f3ca00006aa00000000016e800066d34bd098c050001c0cdcc52d3ce30e932600028600000000001de00002e67b313597b143e6211c4079c4323f5535064da74000502b500000000000000162c0fe058a824000a010f4254924c9eb37c00000000000000000000000000000014e4ec064a00c438c186111f2c0005ee62c8000bca45c2518eb560a6c740da204dc0c173d1087c0000000000000a9a03c4342f4827000000000000000000001e54000c5b0001cb8d744f26201fad0d8000144156441e13b1e3934044a0000000a900002d40ec29187b4000225854545000009cb47510446c6b8a4c4000334261b23cdbc91700012683509795b280000000000000000da282f293868cdb05b40002078980512308195113e6501068504dc2c035379688abe1a91992ded3f0d7d55d00018040002ad80009fc76c38d8ec19480f1205000000000000007e00000000000cc40000d32f380000000004e60000000000000000000011c09a29f566093b0000d4930ccae5461b6d2bc000470821c4447561f5125c18ca522dc29883cc6780000000df600041d8000000b3e53d239c2ee2b60000be800098221884a4b5a5fb5dd24a87804946ac1fc808031800017a4000d332b880000000005b300
  | 35 => 0x1a947e73af2838000d5a2ed0000000d5009512d499674a231801000000000027ec198ae8000000185030c00000000000000000000b2000025d0340e3a00000000007aa63a1ad2dcc000000666a5540b883058412f00002f40e70000d328211482038000c5a00000000ac2690548efc00090a00000003427d40001014000000557b2a4056b243fd80000000ae000245000000051a197000055c00000000000000001c800000c30000b4c0008b300000002160000e780012be000000019c0005d100021c80000002b12a88c000811f8b0e00005ba0002c6d96c00e0ba80b80007442de234ce9227951e28d84f069b67e87f83786d047c1ea4cf8b8419aa76166c72b02533c8df82aa00f81507b63dd621affc3dad0c464000000054a4b1af64eb428a00010a08741b322e8000000000000000000000069f346c00000012800013fa8b70000001a286c50fe1a0400034335a97187400004372e648042015ec12c4f406130001f4891c0001259cc46ae72600017b49f02086552a158343790000020000000533b35c0bc000000000159a6096aa000000039d0000001a700000001a0000000063d22003ca0006c91ce51b60005f000000000000002c8c00000020900000000005c18000eae00052b01c000088618280000005b200000018f0316685942c63e81659923908561dd0941d6cd5c0000001db80000006248001a340000002100cdc7c444b0a50000000000344400000000000016f80ab0b88000000d0608c20500002fe3018000000a100f4a070a0e1484dfb39800099419c991cdba46a490800163c29b0001b2800077d0000000b2c0000000ad4000c562de800000098f43d1104388a7149aad0889a00000000000000000001f5c000000000016c000000000000000000000000000640000002d38878000000297584abfc00000000bac6361d8000b1600000000000008c30002d10c90000123a6700003
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x1c85435c531588400068361543cc16210001234985d54358440005a46425350d61101d9465979d5725844063d29251755c96110001c27945d5725844075f09251755c961101d7c24845d5725844075f09d0d755c961101d7c27405d5725844075f18901755c961101d7c61405d57258440007095d7845c9611000146595dcd7258440007095d5435c96110001c857350d725844000519657705c961100018958750c325844000685615430c96110001a914360032584400068561543cc16110001c255148776500400050b25d515894010001a258154562500400050d25d855854010001a25856096150040006a86018258540100034679754521d96300061960971986658c171865825c6219963000711e0d71486658c001c44835c5219963000711cc171486658c0014659710521996300059164c41486658c0016619010521996300061960971c42658c00186587487109963000519e5971485658c001465979c521596300059864271485658c0014659710521596300059164c41485658c0016619010521596300061961d21c41658c0014679754521d92300051965d51487648c0034679754521d953000591e4d51487654c0018677560472595300143926171485654c18f4a4945c5215953000619a1d51485654c00126591209651953000619e1782dc5644c0014669754521591300051925d51485644c0018668754521591300061921d51485644c0018a487d05215913000d3125d31485644c0018c4874c5215913000e2c21d41441644c0014e097485105913000e3821d21441644c001c455148676d4d3000654605519c3534c0019c18148670d4d3000750545219c3534c001945814847550d3000654605101d5434c001d41214407550d305358324965551434c001951815447050d3000670605211c1434c001d41514847050d3000519644621d5624c00141d951d9435093000513259211d5324c00194581484754c93000654605101d5324c001d4121440754c93000651605219d6304c00195181442758c13000750485109d6304c0034679754521d9620757119cd514876588001c457354521d962063d292517148565880014669754521592200051925d51485648807505e98d95731522000519e5d5148763880014659754521d8e2000519a5c4148765480016459310521d952000598640414876548001466978c521d952011619a1d21c43654800146797d8521195205c51964a215c46548001865825c6411952000619609718c465480014659710521195200059164c4148465480016619010521195200051965e3148465480018658748710195200060d611710406548001855835c41019520006196097104065480016859310521d9120005a86404148764480014669754521591200051925d514856448001466975452158d20
  | 1 => 0x20059864041487654c8018668748710d953200519e5f61484654c801465920c571195320051c640315c4654c9714659288571195320051524d215c4654c801c47835c521195320071120d71484654c801c47305c521195320051965c41484654c8016459310521195320059864041484654c801865825c710195320061961d21c40654c8014669754521591320051925d51485644c97dc4573545211813267709dc5215925494001c616148570952501d417a63615cc54941cb84f86c85731525071e13e19215cc5494001c4561485731525000487251865466394001647965452198e5000591659514866394001645958c52158e5000613dd8825d56394001345912097558e5041615dd9811496394001645929855158e5075711dd95148563940012c5912097558e50005916567148563940016c1909452158e500053165c414856394001645951052158e50005b0640414856394001a45854871058e501d4172637654d43940016259510521d9150005a164c4148764540016a19010521d915000619605219db545419b46497545215905000619e05215da541400186581487765405000d1925d5148565d0001466975452158f400051925d5148563d00034c4974c52158f40006159cd8114b65900034679754521d9640757119cd514876590001c457354521d964001d07a5f6554d4390001466975452158a400059164c6148765500c7a308650510d95406769821921443655000181d84dce73d954067589a50714876550001645931c521d954067598640714876550001466978c521d954067619a1d21c4365500034649754521595400061960971184655000146797d8521195400051965c61484655000164593185211954000589a5b41484655019ba608648510195405c61960971884655019b62694e0521195400051965e31484655000186587487101954066e89211214406550171865825c621994400051965e31486651000186587487109944063d292517148565101d9465979c5215944063d89251714856510001c27945c5215944075f092517148565101d7c27435c521594400051965e31485651000186587487105944000591656314856310001645959c52158c4076591656514856310001a45854871058c400058664283595431000121d980c96550c4000585644325954310001619900c96550c400040f25d815954310001a25814856550c40007814c521595431000121d98cc16550c40005836547350d6210001685911cd43588402dda26407350d62100016899094d435884063e2921171545621000122c9850d515884075d1965e715456210001c27945c5515884076709251715456210001c27845c55158840767092117154562101d9c27435c551588400070950d7154562101d9c27405c5515884000619615718c56210
  | 2 => 0xd862900004e800521ca700005c9f0000006a0000000000000000007d000000ba000000007e000fc001ce0019000000000840b254000005a04285800000000005400000000000f80012000000009419a00000000e4008000000100003004040001000c000000a0000500802000030000000c0000c02008000080000401018000000001c0101000014020000700000008000000100005004090000100000000080000000400028000040000002000000000000800004000080100004004010080000004000010040000801000010380100c0000c0a00c000100000c00757119cd5148660d5001c4573545219835400d3125d314856395001647954c52158e5400e3821d214416095001a638548510582545c6916095188563151c744c976152158c540059165781485631518f68694e052158c5400591656714856315001647955c52158c54004b1644825c16315001a45854871058c5400691e1521441631518fa84844851058c5463d292517148560d4ddf4659754521d815300d1925d5148565d0c0141d94a0f755834300519a5d5148560d0c01464975452158343757091d15148560d0c038e08748510583430058c640615076550c016619018521d954374591259314876550dd1626941c521d95437459164c714876550c01661901c521d954300619a1d21c436550c0346497545215954300619609711846550c018717160061195430058c640615046550c0146797d8521195430051965c614846550c0166190185211954372591259314846550c0142d97a1321195435c619609718846550dc962694e05211954300711e0d714846550c01c44835c5211954300711cc1714846550c01865825c710195430061961d21c406550dc9a2484485101954347447a5f825515350c4d11e972015454d4331447e6154dc15350dd5c257454521d81435cf215d1314876050ddd46497545215935200519e5d5148660d49d5c46735452198352007115cd5148660d497d4659754521d91521d417261615cc5454801c476148573151525f51965d5148460549714659288571997420051965e3148665d0801865874871099742015292517148565d09d9465979c521597421e5892517148565d0801c27945c5215974275f092517148565d09d7c27435c521597420051965e3148565d0801865874871059742005916563148563d0801645959c52158f4276d916565148563d0801a45854871058f42005866428359543d080103c976056550f42006896052159543d0801e05314856550f42004876633059543d097dc2674545219834200d1925d5148565508014b190d0d711814200619615825c460508014679754521181420051965d51484605097dc25745452118142757119cd514846050801c4573545211814200519a5c41487654c8016459310521d953
  | 3 => 0x248000000000000000000000022c00000002561413c000008a1100d8007ba302400a3305e000ca9e000628b080000000ee0000035800458fe518000000000000908003c1b2000000000000134820860000000000000000007c380000021c0000000112930003e8000000019000648000000000000209fc00000398920024a0022a0000000000000000023e0000000000000008d0000006000000001864f8c60014e0018400000681060000000132000be000b40000054914130f20d1a62e00000000a29fa1998e2a8148306c431c68412000000710003116e602744e12457000000527600033800000005d0002b800000f80000000000000000020600000000004112c001ec000a0508400000000000000000000000000000009697a1181a5c10a08000000162725200000000000000000000001f20000000000000001ba728900009800000009780000006899f80027c0004e8e88a090002900000000011948c94c468a2998d80008869000001b63d9da0012a0019600000110000000000000000003a0004d800000006b27e6724647000000003a85c9b1e85124e46028588681d1cc811660014087808660dc9a000000f4001b0a20001d8560000000000001ae278009c00000000808000000025870438de0e1b8000000000000000000000000000000001be000000000000000000940001e0000078a6a00000000008e000000000000000000340000023c00000828000000e000000000000264000008b8000000000000000000000000000000005f02a30800000a8000020003a0027a368001e08c2f25c0000070a6e63000679784a1e65b000488005500000000000000015e0001c0015a000000000000000a0000001301601200150408004b9b40017e6a9d0000008d8005580034800478000c90088800749ba2d9fe5900096000001de1a8306201800080529825a8000ba8679000300000000000212268009d9dc000000000003214000c8350000f05a0000083958388723b07a5826000010001a2a10b2001e09884a0889891126861bc001f675282000ac758000008e86800002207a800420a600000720005
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x4004403000001121c508020e3413c300000b00600000a0002400200038023c30258165e84c846550c01620d0106b8a4232a8600a0929d814856550f420048a34049a42b88ca99002c41a020d71484654c80100ed3928c32a331ca000981291965452198e5000501b49bb104baac72800304776644825d5639400141253b0290acaa188000a09aa3945c5515884000504950a1ae2a8ac420002427a95d7845c9611000121254aeaa1ae4b088000c0925d8154562500400050494ec2b04b0a8020002c41a020d71486658c0018224b302908ea9926000b1029921440754c930
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x8004405b7291965452198e50005005b4dd9912097558e50
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x2
  | 2 => 0x3
  | 3 => 0x4
  | 4 => 0x98a
  | 5 => 0x98c
  | 6 => 0x5
  | 7 => 0x6
  | 8 => 0x1
  | 9 => 0x128a
  | 10 => 0x128c
  | 11 => 0x9ca
  | 12 => 0x9cb
  | 13 => 0x12ca
  | 14 => 0x12cb
  | 15 => 0x10a
  | 16 => 0x10b
  | 17 => 0x10c
  | 18 => 0x130a
  | 19 => 0xa0a
  | 20 => 0xa0b
  | 21 => 0xa0c
  | 22 => 0x130b
  | 23 => 0x130c
  | 24 => 0x180a
  | 25 => 0x180b
  | 26 => 0x180c
  | 27 => 0x14a
  | 28 => 0x14b
  | 29 => 0x14c
  | 30 => 0x134a
  | 31 => 0xa4a
  | 32 => 0xa4b
  | 33 => 0xa4c
  | 34 => 0x134b
  | 35 => 0x134c
  | 36 => 0x198a
  | 37 => 0x198b
  | 38 => 0x198c
  | 39 => 0xcca
  | 40 => 0xd0a
  | 41 => 0xd0c
  | 42 => 0x188a
  | 43 => 0x188c
  | 44 => 0xd4a
  | 45 => 0xd4c
  | 46 => 0x1a0a
  | 47 => 0x1a0c
  | 48 => 0xe8a
  | 49 => 0xe8b
  | 50 => 0x18ca
  | 51 => 0x18cb
  | 52 => 0xeca
  | 53 => 0xecb
  | 54 => 0x1a4a
  | 55 => 0x1a4b
  | 56 => 0x74a
  | 57 => 0x74b
  | 58 => 0x74c
  | 59 => 0x104a
  | 60 => 0x104b
  | 61 => 0x104c
  | 62 => 0x194a
  | 63 => 0x194b
  | 64 => 0x194c
  | 65 => 0x1a8a
  | 66 => 0x1a8b
  | 67 => 0x1a8c
  | 68 => 0x128992
  | 69 => 0x99292
  | 70 => 0x9c992
  | 71 => 0x12c992
  | 72 => 0x150c
  | 73 => 0xcb
  | 74 => 0xd0992
  | 75 => 0x98d12
  | 76 => 0x168b
  | 77 => 0x9d292
  | 78 => 0x8c
  | 79 => 0x12d292
  | 80 => 0x12c9d2
  | 81 => 0x9d2d2
  | 82 => 0x9ce
  | 83 => 0xcc9d2
  | 84 => 0x9ccd2
  | 85 => 0xe89d2
  | 86 => 0x9ce92
  | 87 => 0x1a49d2
  | 88 => 0x9da52
  | 89 => 0xa0112
  | 90 => 0xe8112
  | 91 => 0xe8113
  | 92 => 0x130a12
  | 93 => 0xa1312
  | 94 => 0xd0a12
  | 95 => 0xa0d12
  | 96 => 0x188a12
  | 97 => 0xa1892
  | 98 => 0x14d
  | 99 => 0x134d
  | 100 => 0x181312
  | 101 => 0xe9312
  | 102 => 0xe9313
  | 103 => 0x18d312
  | 104 => 0xd1812
  | 105 => 0x180d12
  | 106 => 0xd4d
  | 107 => 0x1a0d
  | 108 => 0xa4152
  | 109 => 0x14a52
  | 110 => 0xec152
  | 111 => 0x14ed2
  | 112 => 0x194152
  | 113 => 0x15952
  | 114 => 0x134a52
  | 115 => 0xa5352
  | 116 => 0xd4a52
  | 117 => 0xa4d52
  | 118 => 0x1a0a52
  | 119 => 0xa5a12
  | 120 => 0x104a52
  | 121 => 0xa5052
  | 122 => 0x1a8a52
  | 123 => 0xa5a92
  | 124 => 0x199352
  | 125 => 0x135992
  | 126 => 0xed352
  | 127 => 0x134ed2
  | 128 => 0x1a5352
  | 129 => 0x135a52
  | 130 => 0x168e
  | 131 => 0x75352
  | 132 => 0x134752
  | 133 => 0x195352
  | 134 => 0x135952
  | 135 => 0xd5992
  | 136 => 0x198d52
  | 137 => 0x105992
  | 138 => 0x199052
  | 139 => 0x178b
  | 140 => 0x160c
  | 141 => 0x5cb
  | 142 => 0x44c
  | 143 => 0x17cb
  | 144 => 0x164c
  | 145 => 0xe8d12
  | 146 => 0x18cd12
  | 147 => 0x58b
  | 148 => 0xe9892
  | 149 => 0x40c
  | 150 => 0xecd52
  | 151 => 0xd4ed2
  | 152 => 0x1a4d52
  | 153 => 0xd5a52
  | 154 => 0x74d52
  | 155 => 0xd4752
  | 156 => 0x194d52
  | 157 => 0xd5952
  | 158 => 0xeda12
  | 159 => 0x1a0ed2
  | 160 => 0x195a12
  | 161 => 0x1a1952
  | 162 => 0xece92
  | 163 => 0xe8ed2
  | 164 => 0x104e92
  | 165 => 0xe9052
  | 166 => 0x104e93
  | 167 => 0x194e92
  | 168 => 0xe9952
  | 169 => 0x194e93
  | 170 => 0x5cd
  | 171 => 0x17cd
  | 172 => 0x1058d2
  | 173 => 0x18d052
  | 174 => 0x1058d3
  | 175 => 0x104ed2
  | 176 => 0xed052
  | 177 => 0x1a8ed2
  | 178 => 0xeda92
  | 179 => 0x105a52
  | 180 => 0x1a5052
  | 181 => 0x1a9952
  | 182 => 0x1a9953
  | 183 => 0x1a9954
  | 184 => 0xb0e
  | 185 => 0xb0c
  | 186 => 0xbcc
  | 187 => 0x19cc
  | 188 => 0x5c9d3
  | 189 => 0x154e
  | 190 => 0xbcb
  | 191 => 0x19cb
  | 192 => 0xa5554
  | 193 => 0xb0a54
  | 194 => 0xa4b14
  | 195 => 0xb1994
  | 196 => 0x155994
  | 197 => 0x10a12
  | 198 => 0x154d
  | 199 => 0xb0d
  | 200 => 0x11612
  | 201 => 0x10e92
  | 202 => 0x19cd
  | 203 => 0xbcd
  | 204 => 0x11a92
  | 205 => 0xb0155
  | 206 => 0xb1355
  | 207 => 0x154c
  | 208 => 0x154a54
  | 209 => 0x45294
  | 210 => 0x178e93
  | 211 => 0x44d14
  | 212 => 0x5ce93
  | 213 => 0x17ce93
  | 214 => 0xb0454
  | 215 => 0x5d453
  | 216 => 0x44b14
  | 217 => 0xb1654
  | 218 => 0x164b14
  | 219 => 0xbce93
  | 220 => 0x19ce93
  | 221 => 0x15353
  | 222 => 0x1a9053
  | 223 => 0xe9053
  | 224 => 0x104ece9a
  | 225 => 0x104e8eda
  | 226 => 0xece905a
  | 227 => 0xb0754
  | 228 => 0xb05d5
  | 229 => 0x154754
  | 230 => 0xb1954
  | 231 => 0x155954
  | 232 => 0xb17d5
  | 233 => 0x198a54
  | 234 => 0xbcb14
  | 235 => 0xbcb15
  | 236 => 0xb0bd5
  | 237 => 0xe8bd3
  | 238 => 0xb1a15
  | 239 => 0xb0bd4
  | 240 => 0x5cb15
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 64
  | 7 => 2261
  | 6 => 6338
  | 5 => 3476
  | 4 => 326
  | 3 => 19
  | 2 => 2
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
  | 8 => packedAt gbK8 (1811+((h/21+packedAt gbK8 (1664+(h % 21)*7) 7) % 84)*7) 7
  | 7 => packedAt gbK7 (92693+((h/753+packedAt gbK7 (83657+(h % 753)*12) 12) % 2985)*13) 13
  | 6 => packedAt gbK6 (333792+((h/2112+packedAt gbK6 (304224+(h % 2112)*14) 14) % 9202)*14) 14
  | 5 => packedAt gbK5 (220138+((h/1158+packedAt gbK5 (205084+(h % 1158)*13) 13) % 5551)*13) 13
  | 4 => packedAt gbK4 (23900+((h/108+packedAt gbK4 (22820+(h % 108)*10) 10) % 693)*10) 10
  | 3 => packedAt gbK3 (1575+((h/6+packedAt gbK3 (1539+(h % 6)*6) 6) % 34)*6) 6
  | 2 => packedAt gbK2 (186+((h/1+packedAt gbK2 (184+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffff1c30fc3f03fc380e07fff2060ff19349f
  | 1 => 0xf0f0fe03f0fc7fc0fc00fff81f51931326c8f3
  | 2 => 0xff0ffc00ff8000ffff007fe09e1c1cc70f1c
  | 3 => 0xff000fffff000000ffffff8000e01fe0f80fe0
  | 4 => 0xfffffffffff0000000000ffe000fff000
  | 5 => 0xfffff000000000000000000000ffffff000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x1211041010090128084220a8c002065081485
  | 1 => 0x9058a200106424806402495052109112024832
  | 2 => 0x809a868400e90184692a016542161418470918
  | 3 => 0x2a00096baa00020a9254960084e00aa0b806c0
  | 4 => 0x8000db2cc924b2c0018040100eb4000f5a000
  | 5 => 0xccecc02088200c302060184618fdffdf000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfefefea8feeefca8fefefea8feeefca8fefefea8feeefca8fefefea8feeefca8fefefea8feeefca8fefefea8feeefca8fefefea8feeefca8fefefea8feeefca8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_17053
namespace PEqualNP.Outside.L_meta_17053
open PEqualNP.Outside.L_meta_17053.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_3_0 : Interval s1Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 25 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_32 : Interval s1Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_64 : Interval s1Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_96 : Interval s1Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_128 : Interval s1Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_160 : Interval s1Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_192 : Interval s1Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_224 : Interval s1Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_256 : Interval s1Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_288 : Interval s1Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_320 : Interval s1Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_352 : Interval s1Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_384 : Interval s1Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_416 : Interval s1Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_448 : Interval s1Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_480 : Interval s1Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_512 : Interval s1Atlas 4 512 27 := block_range (n:=27) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 539 := (concat (concat (concat (concat bs1_4_0 bs1_4_32) (concat bs1_4_64 bs1_4_96)) (concat (concat bs1_4_128 bs1_4_160) (concat bs1_4_192 bs1_4_224))) (concat (concat (concat bs1_4_256 bs1_4_288) (concat bs1_4_320 bs1_4_352)) (concat (concat bs1_4_384 bs1_4_416) (concat bs1_4_448 (concat bs1_4_480 bs1_4_512)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_32 : Interval s1Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_64 : Interval s1Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_96 : Interval s1Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_128 : Interval s1Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_160 : Interval s1Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_192 : Interval s1Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_224 : Interval s1Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_256 : Interval s1Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_288 : Interval s1Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_320 : Interval s1Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_352 : Interval s1Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_384 : Interval s1Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_416 : Interval s1Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_448 : Interval s1Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_480 : Interval s1Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_512 : Interval s1Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_544 : Interval s1Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_576 : Interval s1Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_608 : Interval s1Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_640 : Interval s1Atlas 5 640 24 := block_range (n:=24) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 664 := (concat (concat (concat (concat bs1_5_0 bs1_5_32) (concat bs1_5_64 (concat bs1_5_96 bs1_5_128))) (concat (concat bs1_5_160 bs1_5_192) (concat bs1_5_224 (concat bs1_5_256 bs1_5_288)))) (concat (concat (concat bs1_5_320 bs1_5_352) (concat bs1_5_384 (concat bs1_5_416 bs1_5_448))) (concat (concat bs1_5_480 (concat bs1_5_512 bs1_5_544)) (concat bs1_5_576 (concat bs1_5_608 bs1_5_640)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_6_0 : Interval s1Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_6_32 : Interval s1Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls1_6 : Interval s1Atlas 6 0 40 := (concat bs1_6_0 bs1_6_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_7_0 : Interval s1Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_7 : Interval s1Atlas 7 0 1 := bs1_7_0
theorem alls1 : ∀ k ≤ 7, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_2 i (by omega) hi
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
  · exact alls1_6 i (by omega) hi
  · exact alls1_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_2_0 : Interval s2Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 10 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_32 : Interval s2Atlas 3 32 28 := block_range (n:=28) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 60 := (concat bs2_3_0 bs2_3_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_32 : Interval s2Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_64 : Interval s2Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_96 : Interval s2Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_128 : Interval s2Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_160 : Interval s2Atlas 4 160 5 := block_range (n:=5) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 165 := (concat (concat bs2_4_0 (concat bs2_4_32 bs2_4_64)) (concat bs2_4_96 (concat bs2_4_128 bs2_4_160)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 50 := (concat bs2_5_0 bs2_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_0 : Interval s2Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_6 : Interval s2Atlas 6 0 1 := bs2_6_0
theorem alls2 : ∀ k ≤ 6, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_2 i (by omega) hi
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
  · exact alls2_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_0 : Interval s3Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 10 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_32 : Interval s3Atlas 3 32 28 := block_range (n:=28) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 60 := (concat bs3_3_0 bs3_3_32)
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
theorem bs3_4_160 : Interval s3Atlas 4 160 5 := block_range (n:=5) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 165 := (concat (concat bs3_4_0 (concat bs3_4_32 bs3_4_64)) (concat bs3_4_96 (concat bs3_4_128 bs3_4_160)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 50 := (concat bs3_5_0 bs3_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 1 := bs3_6_0
theorem alls3 : ∀ k ≤ 6, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_2 i (by omega) hi
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
  · exact alls3_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_0 : Interval s4Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 4 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 13 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 13 := bs4_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 1 := bs4_5_0
theorem alls4 : ∀ k ≤ 5, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_2 i (by omega) hi
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 4 := bs5_4_0
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 2 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 19 := block_range (n:=19) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 19 := bgb_3_0
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
theorem bgb_4_320 : Interval gbAtlas 4 320 6 := block_range (n:=6) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 326 := (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 (concat bgb_4_96 bgb_4_128))) (concat (concat bgb_4_160 (concat bgb_4_192 bgb_4_224)) (concat bgb_4_256 (concat bgb_4_288 bgb_4_320))))
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
theorem bgb_5_3456 : Interval gbAtlas 5 3456 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 3476 := (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 bgb_5_384)))) (concat (concat (concat bgb_5_416 (concat bgb_5_448 bgb_5_480)) (concat (concat bgb_5_512 bgb_5_544) (concat bgb_5_576 bgb_5_608))) (concat (concat bgb_5_640 (concat bgb_5_672 bgb_5_704)) (concat (concat bgb_5_736 bgb_5_768) (concat bgb_5_800 bgb_5_832))))) (concat (concat (concat (concat bgb_5_864 (concat bgb_5_896 bgb_5_928)) (concat bgb_5_960 (concat bgb_5_992 bgb_5_1024))) (concat (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120)) (concat (concat bgb_5_1152 bgb_5_1184) (concat bgb_5_1216 bgb_5_1248)))) (concat (concat (concat bgb_5_1280 (concat bgb_5_1312 bgb_5_1344)) (concat (concat bgb_5_1376 bgb_5_1408) (concat bgb_5_1440 bgb_5_1472))) (concat (concat bgb_5_1504 (concat bgb_5_1536 bgb_5_1568)) (concat (concat bgb_5_1600 bgb_5_1632) (concat bgb_5_1664 bgb_5_1696)))))) (concat (concat (concat (concat (concat bgb_5_1728 (concat bgb_5_1760 bgb_5_1792)) (concat bgb_5_1824 (concat bgb_5_1856 bgb_5_1888))) (concat (concat bgb_5_1920 (concat bgb_5_1952 bgb_5_1984)) (concat (concat bgb_5_2016 bgb_5_2048) (concat bgb_5_2080 bgb_5_2112)))) (concat (concat (concat bgb_5_2144 (concat bgb_5_2176 bgb_5_2208)) (concat (concat bgb_5_2240 bgb_5_2272) (concat bgb_5_2304 bgb_5_2336))) (concat (concat bgb_5_2368 (concat bgb_5_2400 bgb_5_2432)) (concat (concat bgb_5_2464 bgb_5_2496) (concat bgb_5_2528 bgb_5_2560))))) (concat (concat (concat (concat bgb_5_2592 (concat bgb_5_2624 bgb_5_2656)) (concat (concat bgb_5_2688 bgb_5_2720) (concat bgb_5_2752 bgb_5_2784))) (concat (concat bgb_5_2816 (concat bgb_5_2848 bgb_5_2880)) (concat (concat bgb_5_2912 bgb_5_2944) (concat bgb_5_2976 bgb_5_3008)))) (concat (concat (concat bgb_5_3040 (concat bgb_5_3072 bgb_5_3104)) (concat (concat bgb_5_3136 bgb_5_3168) (concat bgb_5_3200 bgb_5_3232))) (concat (concat bgb_5_3264 (concat bgb_5_3296 bgb_5_3328)) (concat (concat bgb_5_3360 bgb_5_3392) (concat bgb_5_3424 bgb_5_3456)))))))
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
theorem bgb_6_6336 : Interval gbAtlas 6 6336 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 6338 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat bgb_6_96 (concat bgb_6_128 bgb_6_160))) (concat (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)) (concat bgb_6_288 (concat bgb_6_320 bgb_6_352)))) (concat (concat (concat bgb_6_384 (concat bgb_6_416 bgb_6_448)) (concat bgb_6_480 (concat bgb_6_512 bgb_6_544))) (concat (concat bgb_6_576 (concat bgb_6_608 bgb_6_640)) (concat bgb_6_672 (concat bgb_6_704 bgb_6_736))))) (concat (concat (concat (concat bgb_6_768 (concat bgb_6_800 bgb_6_832)) (concat bgb_6_864 (concat bgb_6_896 bgb_6_928))) (concat (concat bgb_6_960 (concat bgb_6_992 bgb_6_1024)) (concat bgb_6_1056 (concat bgb_6_1088 bgb_6_1120)))) (concat (concat (concat bgb_6_1152 (concat bgb_6_1184 bgb_6_1216)) (concat bgb_6_1248 (concat bgb_6_1280 bgb_6_1312))) (concat (concat bgb_6_1344 (concat bgb_6_1376 bgb_6_1408)) (concat (concat bgb_6_1440 bgb_6_1472) (concat bgb_6_1504 bgb_6_1536)))))) (concat (concat (concat (concat (concat bgb_6_1568 (concat bgb_6_1600 bgb_6_1632)) (concat bgb_6_1664 (concat bgb_6_1696 bgb_6_1728))) (concat (concat bgb_6_1760 (concat bgb_6_1792 bgb_6_1824)) (concat bgb_6_1856 (concat bgb_6_1888 bgb_6_1920)))) (concat (concat (concat bgb_6_1952 (concat bgb_6_1984 bgb_6_2016)) (concat bgb_6_2048 (concat bgb_6_2080 bgb_6_2112))) (concat (concat bgb_6_2144 (concat bgb_6_2176 bgb_6_2208)) (concat (concat bgb_6_2240 bgb_6_2272) (concat bgb_6_2304 bgb_6_2336))))) (concat (concat (concat (concat bgb_6_2368 (concat bgb_6_2400 bgb_6_2432)) (concat bgb_6_2464 (concat bgb_6_2496 bgb_6_2528))) (concat (concat bgb_6_2560 (concat bgb_6_2592 bgb_6_2624)) (concat bgb_6_2656 (concat bgb_6_2688 bgb_6_2720)))) (concat (concat (concat bgb_6_2752 (concat bgb_6_2784 bgb_6_2816)) (concat bgb_6_2848 (concat bgb_6_2880 bgb_6_2912))) (concat (concat bgb_6_2944 (concat bgb_6_2976 bgb_6_3008)) (concat (concat bgb_6_3040 bgb_6_3072) (concat bgb_6_3104 bgb_6_3136))))))) (concat (concat (concat (concat (concat (concat bgb_6_3168 (concat bgb_6_3200 bgb_6_3232)) (concat bgb_6_3264 (concat bgb_6_3296 bgb_6_3328))) (concat (concat bgb_6_3360 (concat bgb_6_3392 bgb_6_3424)) (concat bgb_6_3456 (concat bgb_6_3488 bgb_6_3520)))) (concat (concat (concat bgb_6_3552 (concat bgb_6_3584 bgb_6_3616)) (concat bgb_6_3648 (concat bgb_6_3680 bgb_6_3712))) (concat (concat bgb_6_3744 (concat bgb_6_3776 bgb_6_3808)) (concat (concat bgb_6_3840 bgb_6_3872) (concat bgb_6_3904 bgb_6_3936))))) (concat (concat (concat (concat bgb_6_3968 (concat bgb_6_4000 bgb_6_4032)) (concat bgb_6_4064 (concat bgb_6_4096 bgb_6_4128))) (concat (concat bgb_6_4160 (concat bgb_6_4192 bgb_6_4224)) (concat bgb_6_4256 (concat bgb_6_4288 bgb_6_4320)))) (concat (concat (concat bgb_6_4352 (concat bgb_6_4384 bgb_6_4416)) (concat bgb_6_4448 (concat bgb_6_4480 bgb_6_4512))) (concat (concat bgb_6_4544 (concat bgb_6_4576 bgb_6_4608)) (concat (concat bgb_6_4640 bgb_6_4672) (concat bgb_6_4704 bgb_6_4736)))))) (concat (concat (concat (concat (concat bgb_6_4768 (concat bgb_6_4800 bgb_6_4832)) (concat bgb_6_4864 (concat bgb_6_4896 bgb_6_4928))) (concat (concat bgb_6_4960 (concat bgb_6_4992 bgb_6_5024)) (concat bgb_6_5056 (concat bgb_6_5088 bgb_6_5120)))) (concat (concat (concat bgb_6_5152 (concat bgb_6_5184 bgb_6_5216)) (concat bgb_6_5248 (concat bgb_6_5280 bgb_6_5312))) (concat (concat bgb_6_5344 (concat bgb_6_5376 bgb_6_5408)) (concat (concat bgb_6_5440 bgb_6_5472) (concat bgb_6_5504 bgb_6_5536))))) (concat (concat (concat (concat bgb_6_5568 (concat bgb_6_5600 bgb_6_5632)) (concat bgb_6_5664 (concat bgb_6_5696 bgb_6_5728))) (concat (concat bgb_6_5760 (concat bgb_6_5792 bgb_6_5824)) (concat bgb_6_5856 (concat bgb_6_5888 bgb_6_5920)))) (concat (concat (concat bgb_6_5952 (concat bgb_6_5984 bgb_6_6016)) (concat bgb_6_6048 (concat bgb_6_6080 bgb_6_6112))) (concat (concat bgb_6_6144 (concat bgb_6_6176 bgb_6_6208)) (concat (concat bgb_6_6240 bgb_6_6272) (concat bgb_6_6304 bgb_6_6336))))))))
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
theorem bgb_7_2240 : Interval gbAtlas 7 2240 21 := block_range (n:=21) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2261 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 bgb_7_224))) (concat (concat (concat bgb_7_256 bgb_7_288) (concat bgb_7_320 bgb_7_352)) (concat (concat bgb_7_384 bgb_7_416) (concat bgb_7_448 (concat bgb_7_480 bgb_7_512))))) (concat (concat (concat (concat bgb_7_544 bgb_7_576) (concat bgb_7_608 bgb_7_640)) (concat (concat bgb_7_672 bgb_7_704) (concat bgb_7_736 (concat bgb_7_768 bgb_7_800)))) (concat (concat (concat bgb_7_832 bgb_7_864) (concat bgb_7_896 bgb_7_928)) (concat (concat bgb_7_960 bgb_7_992) (concat bgb_7_1024 (concat bgb_7_1056 bgb_7_1088)))))) (concat (concat (concat (concat (concat bgb_7_1120 bgb_7_1152) (concat bgb_7_1184 bgb_7_1216)) (concat (concat bgb_7_1248 bgb_7_1280) (concat bgb_7_1312 (concat bgb_7_1344 bgb_7_1376)))) (concat (concat (concat bgb_7_1408 bgb_7_1440) (concat bgb_7_1472 bgb_7_1504)) (concat (concat bgb_7_1536 bgb_7_1568) (concat bgb_7_1600 (concat bgb_7_1632 bgb_7_1664))))) (concat (concat (concat (concat bgb_7_1696 bgb_7_1728) (concat bgb_7_1760 bgb_7_1792)) (concat (concat bgb_7_1824 bgb_7_1856) (concat bgb_7_1888 (concat bgb_7_1920 bgb_7_1952)))) (concat (concat (concat bgb_7_1984 bgb_7_2016) (concat bgb_7_2048 bgb_7_2080)) (concat (concat bgb_7_2112 bgb_7_2144) (concat bgb_7_2176 (concat bgb_7_2208 bgb_7_2240)))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 32 := block_range (n:=32) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 64 := (concat bgb_8_0 bgb_8_32)
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 5 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 8, 10),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 20, 52)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 8 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 20, 52)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 6 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfefefea8feeefca8fefefea8feeefca8fefefea8feeefca8fefefea8feeefca8fefefea8feeefca8fefefea8feeefca8fefefea8feeefca8fefefea8feeefca8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4278124200 * 2 ^ 32 + 4277075112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_17053.Model.Repr at out
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

def mono : List Gate := [⟨.or,[3,4]⟩,⟨.and,[5,6]⟩,⟨.or,[4,7]⟩,⟨.or,[1,2]⟩,⟨.or,[8,9]⟩,⟨.or,[3,7]⟩,⟨.and,[1,4]⟩,⟨.and,[9,11]⟩,⟨.or,[0,12]⟩,⟨.or,[13,14]⟩,⟨.and,[10,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124200 * 2 ^ 32 + 4277075112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124200 * 2 ^ 32 + 4277075112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_17053

open PEqualNP.Outside.L_meta_17053 in
theorem PEqualNP.Outside.L_meta_17053 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124200 * 2 ^ 32 + 4277075112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124200 * 2 ^ 32 + 4277075112) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
