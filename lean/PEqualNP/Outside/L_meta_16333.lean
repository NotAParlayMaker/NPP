import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_16333.Model
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


end PEqualNP.Outside.L_meta_16333.Model

namespace PEqualNP.Outside.L_meta_16333
open PEqualNP.Outside.L_meta_16333.Model
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

def SBf (j : Nat) : Nat := [3, 3, 8, 6, 8, 8].getD j 0

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

end PEqualNP.Outside.L_meta_16333

namespace PEqualNP.Outside.L_meta_16333
open PEqualNP.Outside.L_meta_16333.Model
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
  | 2 => 0xffffffffffffffffffffffffdfc7fff87ffe3f
  | 3 => 0x6bf878ff8783cc
  | 4 => 0x73ff80fff803f0
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffff8041102888a8d5
  | 2 => 0x20b2245455522a
  | 3 => 0x1517459d461b4c
  | 4 => 0xe2476e66463b0
  | _ => 0
def s0Atlas : Atlas := ⟨2,rawDecor 30 s0Pos s0Neg, 0xccc0c0c0ccc0c0c0ccc0c0c0ccc0c0c0ccc0c0c0ccc0c0c0ccc0c0c0ccc0c0c0ccc0c0c0ccc0c0c0ccc0c0c0ccc0c0c0ccc0c0c0ccc0c0c0ccc0c0c0ccc0c0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_16333
namespace PEqualNP.Outside.L_meta_16333
open PEqualNP.Outside.L_meta_16333.Model
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
  | 2 => 0xffffffffffffffffffffffffdfc7fff87ffe3f
  | 3 => 0x6bf878ff8783cc
  | 5 => 0x73ff80fff803f0
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffff8041102888a8d5
  | 2 => 0x20b2245455522a
  | 3 => 0x1517459d461b4c
  | 5 => 0xe2476e66463b0
  | _ => 0
def s1Atlas : Atlas := ⟨2,rawDecor 45 s1Pos s1Neg, 0xaaa0aaa0a0a0a0a0aaa0aaa0a0a0a0a0aaa0aaa0a0a0a0a0aaa0aaa0a0a0a0a0aaa0aaa0a0a0a0a0aaa0aaa0a0a0a0a0aaa0aaa0a0a0a0a0aaa0aaa0a0a0a0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_16333
namespace PEqualNP.Outside.L_meta_16333
open PEqualNP.Outside.L_meta_16333.Model
def s2K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K6 : Nat → Nat
  | 0 => 0xa800a580001c040290000000009d1133e31080003d2170000f001aa8e82201d406466000000105914a00900366530a560ca00108049a3800114d001001040000141ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31de31fd31fc31dc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x881be501027ca0206e94040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330ef21e61dd43cc2fca5985f54b30ef99661dd32cc2fca3985f54730ef18e61dc31cc37c81986f10330bfaa4617e548c2faa9185f15230bea9c617e528c2faa518778ca30ee194617e518c2faa318778c630ee18c617e508c37c81186f10230ef98461fb308c2fea8986fd51309faa2617e544c2faa8985f15130de2a2613c544c3bc86987750d30bfa9261ef524c2dea4985f14930f6292616c524c3be6498774c930bfa8a61f7514c2eea2985f14530fa28a6174514c3bc6298770c530df20261bc404c3f66098778c130bfaa0617e540c2faa8185f15030bf298617e520c2faa418778c830ee190617e510c2faa218778c430ee188617e500c37c80186f10030ef98061fa300c3ba60187e4c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c82faa7905f14f20bf28e417d51c83bc6390770c720df20641bc40c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c53882faa5107bcca20f6194417e51882faa310778c620ee18c41ee21883d843105f94220df20441bc40883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20bfa8a41f751482eea2905f14520fa28a417451483bc6290770c520df20241bc40483f640907b88120bfaa0417e54082faa8105f15020bfa98417e53083bca6105794c20bea9841dd53082baa6105f14c20bf29041ef32083d864105f94420bea8841de31083b862107b88420f6108417e500837c80106f10020f790041fa20083da40107e48020bfaa6217e54c437ca9884f95310beaa621bd54c427aa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10ef18e21dc31c43f681886f90310de20621f840c437081887ec8310fc106217f54842fca9085f55210be2a4217f53842fca7087794e10af29c217d53843baa7085754e10be29c217f52842fca5085f54a10be294217d51843ee6308778c610ee18c21f431843a863087dc8610fa10c217e508437c81086f10210fb88421fb10842fea8886fd51109faa2217e54442faa8885f15110de2a2213c54442fea68877d4d10afa9a217e53442faa6885f14d10ee29a215c53442fea4887bd4910b7a92217e52442faa4885f14910f6292216c52443bc6288770c510df20221bc40443f620887d84110bfaa0217e54042faa8085f15010bfa98217e53042faa6085f14c10bfa90217e52042faa4085f14810bf28821f731043bc6208770c410fa18821d431043ee42087d08410bf28021fb400437c80086f10010fc20021b840043f640087e08010fb88021fa10043ea20087e44010
  | 1 => 0xe528c6faa518f7cca31ef19463dd328c7b86518df94631ef98c63f7318c6fca118df54231efaa463de548c7baa918f715231efa9463de528c7baa518f714a31efa1463de428c7ba8518f710a31af28c63df418c7bc8318f750631ee20c63df508c7bca118f754231ee284637f544c6fca898df55131be2a2637f524c6f8a498fdcc531ef18a637f504c6f8a098dfd5031bf2a063be540c67ca818df55031deaa0633d540c6f8a818df94c31efa1863de430c7ba8618f710c31bf290637d520c7be6418f78c831ee99063dc320c6fca218f7cc431fb18863dd310c7ea6218df94031bea8063df540c7bca818e795031eeaa0639d540c7b8a818f7d4831ef29063dd520c7b8a418f7d0831ef21063dd420c7b88418f794431af28863d6510c7be8218f790431eea0863dc410c7bea018f794031eea8063dc500c6fea990df95321beaa6437c54c86fea790df94f21ef29e435e53c86faa790f754f21aea9e437c53c87bc6390f70c721bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510fbd0a21f6214437e51887bc6310f70c621f790c43f721886fca110df54221bfaa243bf544867ea890df95121beaa2437c5448778a890cf15121bfa9a43df53486bea690df94d21bea9a437c53487b8a690d714d21ef18a43dc31487ee4290fb88521bfa8243fb50486f6a090df14121fc282437850486fea810df95021df2a0433e54086faa810ef550219eaa0437c54086fea610df94c21bea98437c53086fca410fbd0821f6210437e51087bc6210f70c421f790843f621087da4210fd48421bf280437d50086fca7a05f54f40bf296817d52d02fca3a05f54740ef18e81dc31d02faa9205f94e40bea9c81bf439037c87206f50e40de21c817e52902faa5206fd0a40df21481bd429037885205f94640bea8c81bf419037c83206f50640de20c81de31903b863205f94240dfa0481fb409037ea7206f94e40dea9c81bc539037ea5206f94a40dea9481bc529037e65206f8ca40de99481bc329037ea3206f94640dea8c81bc519037e63206f8c640cf18c81bd31903786320670c640df90c81be219037a43206f086409f284817f53502f8a6a05fd4940be292817f51502f8a2a0778c540ee18a81fb405037c80a05f95040bf29881de53102bca6205f54c40eea98815d531037e86206f90c40dea1881bc43102fca4205f54840dfa1081be421037a84206f10840bf288817d511037e82206f90440dea0881bc41103bc6220770c440bf28081bf40103f480206f50040fca0081bf531037ca6206794c40dea98819d5310378a6206fd4840df29081bd5210378a4206fcc840df19081bd321037864206fd4440df28881bd5110378a2206fcc440df188819e311037a62206f0c440ce18881bf211037c42206f48440de10
  | 2 => 0x4004018040000301c801006000010040020040000900a0240300000600c0000300200c0300c00406002801004004008000060cc03826028000018060080000000000c01000000000004018050000100082000004c0001800000c0000000e0040002b07e0000100500800c0102501c0600100e002000010020040300003700401c060060260000000200200c0280400600801000014000000000100040180400a01c0100100800002001002000000000000280100000e0100c0000000200000200401002000000028010010000440080100000008804000038000030140000000000601001802016014098060080040080100200c0100400200000000000014000010000d4008040020000080100000001004004024040080000042300d002008048060020040480a03400008003bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf288877d5110efca021df54043bf29e85de53d0abca7a15f54f42eea9e855d53d0afca3a15f54742bf286857d50d0afaa9215f94e42bea9c85bf4390b7a87215f94a42dfa1485ef4290afca3215f54642bf284857d5090afea6a15f14d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42bea9885bf4310b7a86215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccb7ca9994f95332beaa665bd54cca7aa9995f15332bf28e657d51ccafca1995f54332bfaa4657e548cafaa9195f15232bea9c65de438cbba87195f94a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132beaa2657c544cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cafaa8195f15032bf29865de430cbba86195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e83de53d06bca7a0df54f41eea9e835d53d077e87a0ef50f41bf296837d52d077e85a0ef50b41bf286837d50d06faa920df94e41bea9c837e52906faa520ef90a41de214837e519077e8320fdd0641bf284837d50906fea6a0f7d4d41afa9a837c53507b8a6a0d714d41dfa1a83bd43506fea4a0fbd4941b7a92837c52507d8a4a0db14941dfa1283bd42507ee82a0ef90541bfa8283fb50506f6a0a0df14141fc282837850506fca820df94c41bea98837e52106faa420ef90841de210837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331bf296637d52cc6fca198df54331bfaa4637e548c6faa918df15231bea9c63df438c7bc8718f750e31ee21c637
  | 3 => 0x96c1d4b6c0f8b753a909332b73c899d58000000234d22f05204c5758a700001d6cab40009c08a80058e000e600046a0000025200014942a5309c000dd8005ccbe16a80061a000969c3000350000000c200000000000be8320000006fc0019b0002994b87d664001570000001e03729c39a624bd8f30000013f16f0000fc4800032ca9c0029233a348000005120011b22a38c6055f299084000b000155e3dc0000015011d811981f600000000080c3c188540d45d5682d262e044000001980000006d0003b8ff2a92aec1c000001c27d8c32e91345f07a000000379952592747f5500005c2accfd82f07a0157ea7800069813800000001430000c465c6f8d9246538e385f2c436935a750648951f00010cc7400140000000528004580010d1020009b800000208000002e01721c59890c59e000001a96665a8e496900095ccf9e10000000032d1ceb787f0ca05091cbf2382e6c244a8bf29a8b4b6a0f0a67601c239000569510fa0000000026014447d3698c4e8c44b223c196000488004125c89b0006321c12a15516200067800594bfd7e000000000000000000000013700000000114608000269f2582001200f239ca9406a58000728020000004c0002dd0001a4641c10aa001841d562cb2c000003b253c5000000000106000000ae1089484620012a95d30e9d825a1d0002054a2cd1ec20019802012648dc0db10a6086c31b4b660109097510001890000300000024500000189800000000000001c00003fb151c675c002410008b8d6949000c28eb16b3cca0c6e9212368a04e07a0e87413126a1925303795e0000285f17f2827e8631a30004e4000000eaaa8000d736a43d90a9a10e1300027a0d00001a9090002a57b0000004a00017d00040c002430007804d8e4126aac000194742d800000000000002d3000001520003a200186000000ae4d02a613c5e0e90001680000029f5c4628fc0000003e4000003f8000001bd000ab02b82a0000014125a1d24000184a652775000ac000000001901fa444000000000000024c36e544000003b46cc000ad00017551810000124600253fe020788005e21c931800000c900031c00089d342222f2000f513b0000000013d0000008b873000114002374964582b0bd0b2000001714f2000caadf308a34ef12523a0000012464a05c0003c0000000029349a3d54f0004e22ec002e54661b10a96605c76ce11ab2166c8c70001645183d826210b08d1272000001101ac2e806c0025d35c4651d9381280000022922027c3b2c908c2499001d47e0000000000040441a3d000000e000031664c1609856abdcafa7b26600044a3000000a0000002001600013800000000090080000040400e008008010040040080080000400003001002014008090040980100d01c01403800000000010080000140100200c00c0
  | 4 => 0xb39778d13a80dc000d60000005d2d118aa540000000041d6c00000000018000542000a3800000ca00032f15ec14001e8254000dc800000c8c55b003e60010d8b5606a30828000005288995c00060d8824465c10d2482d2447d50e1d31c400000248268000db000000b18ee0001da00069800322000fb800046b8c0f1ef4ac89097218000a040013f0007946aa0852c0017215457800000000000b0c0000061c000efae763e0000020a170670cf17a286808001bc0002c11598d000b140009d4640008d0000005840007e000460900000429b02f00060c058fca16368ac57a92f154a618d0885d0cc0780005b46c40014400002c330000000001000021c3393081a5808194700010849d930002a40010f8005da00102b1e0ee78c0004800079c00000000a01348c7166000000000002b8001c42c6514b7156576000000002e06f93e1c83d88bcb40c3446000099a700c2284c80027c000002910000000000002a000000003da0018c2c43600009e000468bec318000cebf8f1000048000a82014b80888f00000056c0007c3285dd278a426a668002b2024bc8459990b8b710f29b508bd1082f338abb075a140000000028b0009fd09b22000978000d0000000000002ec0380020b09e0012528f0a20013e800000000730c13540e82d2ee00093850a6f3e2000f580000000000000252239230000000008e00039600074000000000001e943262000000088ad8001f00000eca58790000000010d1de9cc478000000000016500073d3bacc34203c148344423f0000c4224000002f93740001c8005740000031400028c0010a000000610411b8899859f424c3b10b86512cc9d321534cab502daea1043942825f34a80cc2aa81f0941439583502f015ad6118cb09630140eb2195a5106c59d0728a0184180a06b41a5640e1321feab4f72040b0508c79af57a1801f2d719aafc95
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0xd510825f658c42097596310825f650c42097594310831e5390020c754e400831e5310020c754c400826f6548020b318d20082e46148020ea101200827b6548020bc185200825e63953109758e54c431e6395310c758e54c433b60553108f99353c423d64d4f109b98b53c426d62d4f108f99053c423d6414f108f99352c423d64d4b109798f52c425d63d4b109798e52c425d6394b108f99052c423d6414b10c795231c431d548c710c795031c431d540c710ce55040c42b96510310ce59440c439a6310310e658c40c439a3110310e60c440c42ba64c83109798f548425d63d52109b98b548426d62d52109798c548425d63152108f992538423d6494e10c7992538431d6494e10d5d85538423e64d4a108f593528425e63d4a109758f528423e6494a108f592528425e6314a109758c5284355530c610b55943184355650c610e59903184395640c610b598f218431e5390210c754e40843943190210c794c408431d5310210e50c4408423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551109ed81544423e65151108f980544423c6015110c7d53534431c54d4d108f992534423d6494d109798e534426e6294d109b58a534423f6454d108f191534426f6254d109b18953442776154d1097994534431f5414d10c7150534425e6114d1097184534432f54d4910cb153524434f53d4910d314f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109dd85524427b60549109b994524432f5414910cb150524434f5314910d314c524425e658c510c7d52314431c548c510d3d4a314434c528c51097994314431f540c510c7150314434f520c510d3148314423e6590110c7d4e404431c5390110cbd4a404432c52901108f994404431f5310110c714c404432f5210110cb148404433854c4110da14b10443545384110d914a104425e63150109758c540426e62150109b588540423e6414c108f590530426e6214c109b588530423f64548108f191520425f63548109718d520423e64148108f590520425e63148109758c520423e64944108f59251042d6618c4109d5943104356650c410d55943104396640c410e559031043d2600c410f458031042d663c84109d594210425e63940109758e50043543194010f40c740043943190010ae982400439431100109e59440043d03110010ce99440043396510010e698c40043996310010ec98440043b16110010ce94440043b33110010e68c440043983110010ec0c440043903110010ecc8440043b02110010ae99320043d031c80109e59420043d03108010f808420043b040c40109e59610043d031840109dd9510042d46344010b9189100427b6544010ae19110042e86244010
  | 1 => 0x2b860484408f994211023d6508440c794e501031d5394040c78c6501031c3194040ce982501039a5394040e654e50102ba6194040e68c650103983194040c798e54cc31e5450f30a759332cc31e548c730c755231cc29d640c730c795031cc31d540c730d594431cc355510c7308fd91528c23c6454a308f992518c23d6494630d5946318c23e64951309b98a544c26d62951309d986544c27561951309bd89544c26c62551309dd85544c27461551308f994544c31d6315130c7152434c25c6550d30b6181434c32f54d4930cb153524c32f5414930cb150524c34e4314930d350c524c25e65cc930a7593324c34c52cc930d3149324c33754d4530cd153514c36752d4530d914b514c3375414530cd150514c3675214530d9148514c3576314530d590c514c3554314530d5cc8514c3553214530c7d52314c31c548c530d3d4a314c34c528c530d5146314c29d640c530c7d50314c31c540c530d3d48314c34c520c530d5d44314c23e6590130cbd4a404c32c5290130cdd46404c33451901308f994404c32f5210130cb148404c3375110130cd144404c34c528c130d5146304c26e62d50309b58b540c25e63150308f992530c23d6494c3097596320c356510c43097d95300c2cc624c030b5185300c398404c0309ed95300c25e63953209758e54c831e6395320c758e54c823e64d4f208f59353c827661d4f209d58753c823e6414f208f59053c825f63547209718d51c831e548c720c755231c831e540c720c755031c8356510c720d554431c825e63152209758c548823e6414e208f590538823e64946208f592518825f63546209718d518823e64951209798e544825d63951209d9865448275619512097d8d544825c63551209dd85544827461551208f994544831f54d4d20c7153534825e61d4d208f992534823d6494d209798e53482766194d209d586534823f6454d208f191534826f6254d209dd8553482746154d2097994534831f5414d20c7150534825e6114d209798f514825d63d4520cdd53514833454d4520d5d4f514835453d4520d598f514835563d4520cdd5051483345414520d5d4c51483545314520d5d8c5148354631452097996314825c658c520c7d52314831c548c520d5d463148354518c52097994314825c650c520c7d50314831c540c520d5d443148354510c5208f996404831f5390120c714e40483375190120cd146404823e6510120c7d4c404831c5310120cdd4440483345110120dc147204834c5388120d9146204825e63d50209758f540825e63150209758c540827661150209d584540823e6494c208f592530825d6594c20c7992530831d6494c2097986530834c6254c2097185530825e6314c208f992520823d6494820d354f320826d650c820ba580320823f64544208f191510825f63544209718
  | 2 => 0x6454d219ed8153486786054d2197994534871f5414d21c7150534865e658c521c7d52314871c548c52197994314871f540c521c7150314872c54885218f993504863d64d4121ced53504873854d4121d6d4f504875853d4121ce993504873964d4121d68c7504875831d4121ced5050487385414121d6d4c50487585314121ced9050487386414121d68c450487583114121dcc84504876a21141219798e540865d63950218f596540871e6395021c758e540863e6095021cb189540863c60550218f990540863e64d4c218f593530863e6414c218f590530867a6014c219e580530865e63948219758e520872d54d08219b59442086e56110821c7952310871d548c421c7950310871d540c4219bd9521086ac6448421f10c521086e860484219dd9521086f060484218fd91500863c645402197d8d500865c635402197d8d51d025c6354740d594431d0355510c74097d8d529025c6354a40a798f429029d63d0a40cb949429025f63546409718d519029e63d0640a758f419029f6350640a718d41902af6250640ab18941902ba60d4e40ab98853902ad6214e40ae98053902ba60d4a40cbd4a529029f6354a40a718d529029e6314a40a758c52902ba6014a408f997329023d65cca40a798f519029d63d4640ab98b51902ad62d4640ae983519029f6354640a718d51902ba60146408f994319023d650c640c7994319031d650c640e5984319029e63c8640a758f219023f65486408f195219029f6348640a718d21902bb6048640ae181219023e65086408f594219025e63d45409758f5150357510c540d5144315025e6194c4097185531031d5390c40c794d431029e63d0840a758f421031d5390840c754c421032d521084097d8d511025c63544409bd89511026c6254440a798f411029d63d0440c754f41102b960d0440a7d8d411029c6350440c754d41102af6250440ab18941102bb605044097d96311025d658c44097d94311025d650c4408fd95401027b6550040ae983531029d6594c40a7986531031f6554c40a7185531029e6314c40ae980531029e63d4840a758f52102ba60d4840c754e521029e6314840a758c521031d5314840cb54852102b66114840ad58452102ba60148408f997321023d65cc840aed8132102b8604c840ae98032102b9600c840a798f511029d63d4440c754f51102ba60d4440a7d8d511029c6354440c754d51102af6254440ab189511029e6314440a758c51102ae6214440ab58851102ba6014440ae98331102b960cc440a7d96311029d658c440a798631102bb604c440ae181311023e650c4408f594311029f650c440c7994311029d650c440c7594311021d650c440a79843110396610c440a798f211029d63c8440ae98321102b960c84408fd95211023c6548440a7d8d211029c6348440aed81211
  | 3 => 0x1329d185544ca7b60551329e181544ca3e64145328f590514ca3e64d41328f593504ca7a60d50329e583540ca3e6494c328f592530ca5d6590c32b358a430ca9d64cc83297d95320ca6f654c8328fd91500ca3c64540329dd85500ca746154032c794d43d069d63d0b4197d8d529065c6354a419798e509065d6394241c714f43506b46150d41d3d4f525074c53d4941d3d4c525074c5314941cbd0c525072d43149418f997425069d63d0941cb14b425072c5250941cb14a415075b53d4141d614f505076b52d4141da14b505075b5314141d614c505076b5214141da148505073b6414141ced0c50507394314141ced0850507394214141ce904505063d65908418fd9541106ac6250441ae181411067765504419b98b54cc66d62d53319e98354cc67960d53318fd9150cc63c64543319b988548c66d62152318fd91528c63c6454a31a7993328c69d64cca31d3949328c63f64542318f191508c6d661d5231b3988548c6cd6215231b5984548c6d661d4a31d3d4a528c69f6454a31a7191528c69e6414a31a7590528c6d66114a3197997428c65d65d0a31b3d89418c6cc6250631b6d81418c6d86050631a7993508c69d64d4231b398b508c6cd62d4231a7d91508c69c64542319758e544c65f63551319bd89544c66c62551319ed81544c67860551318f993504c63d64d41318f596540c71e63950318f982540c71c63550318f181540c63e6415031c7553430c65d6590c31c7951430c65d6510c31a7993320c69d64cc831c7552320c71d540c831d3548320c65f654c4319dd95310c63f64540318f191500c66f62540319b189500c6d661d5031a7596540c69e6095031c7d95540c69c6055031a7990540c6d66115031a7993520c69d64d4831b5987520c71d5494831a7990520c69d6414831c7550520c74d5214831b5984520c6da6014831b6580520c65e65d083197597420c6d76150831b5185420c6d66110831b5584420c71e5494431c7552510c7566194431e5952510c7955494431b5982510c65d65d043197d95410c6cf6250431b3189410c6db6050431b6181410c7954110431a7993500c69d64d4031c7553500c69f6454031a7191500c71d5454031b3d89500c6cc6254031a7990500c69d6414031b3988500c6cd62140319798f54c865d63d53219e98354c867960d53219798c54c865d63153218f99253c863d6494f21c799253c871d6494f218fd9150c863c64543219798c548865d63152218f990538863d6414e219798e508865d63942218fd91508863c64542218f983544863e64951219798e544865d63951219e9825448679609512197d8d544865c63551219bd89544867b60551219e181544863e65151218f980544871f54d4d21c7153534863e6494d218f592534865e6394d219e98253486796094d218fd91534863c
  | 4 => 0xd759ac6740005d80059e841ae800180cc0c2924430a10000005780018082a256001bb800000000000000000007c0dc00000000000000250000010008ec0028e62a9dc0015800000000131000000a52d9000d51370004f06c02e193000d98d680000095c000ec04e000001600001617f8000000007384e0009558a0002d6001bd8000000009ca5f4b6c8cc11f81dc368000000005cc00000000dd800000000001872a50001500014353c0000011627e9c93d000542dbc000000000004ca17502d90000000ca9900000020a000002990000003480001a6e05e22a0101e8000002889219000000000000044000464e30000001b4002df000554f60cb0009509c0000002959200000027c0033e0004947f000000000001d0340000dc800488a016a93659a4840034f0006f8f48420003e8000000004a0520001180000016f22e8c0001082586a17a8005f001cb3978000000002874e0000000000000ac002ce0004c0ae16234a0000009b000000002fd000001260f9106a30001884b425c5511f212ba00027e3ba000d1b2166a000001e46e01bc758450fe001a88005f8000b63065060489918926e178501f067801416a3a000001072de10c0451b8001ae309851576628f8838b425426947a526ea0000000280100001c000010000180000100402c008030000100000000a0080100700600002800004004020060020000080100002c0000100800400004012004040000000000000b00000c00000006000010000000300380100600400004004000020040000000080e00600000800000010000010060000000000c01c0280201c0200000300a00c000010060180000400600c010020060040180000a0000100000001402000002024008010180080000000004c06000006000010000040000100100800c0280d0000080100000001000800000000000000060000180c004008008020000000000e00000000809004000008000060000100000600001000018020000000000040200100a00000800006000000000060040080000c00000004000008030000020200080400403c010020020000000602200c0380000200c020010020000000100e000010000160180180000e000010000040000101801401400801002000000020020040000b00a0000200200000c0100100200400000004004010050080400200000600000005002000008000020000180000000c028008fd954310e5f6550c439798653d0a5c6154f4297d8d51d0a5c6354742a758f4290a5f63546429718d5190a5e63d45429758f5150a5e63141429758c5050aad62d0c42a758f4210a3f65508429bd954210a5f63544429718d5110a7b60544429e1815110a3e60953328f18154cca3f64543328f19150cca7661152329d584548ca9d64cca328fd91508ca3c64542329758e544ca776155
  | 5 => 0x1cd3bc8bc000001e600000000426000cf83c2dc000003471e09d1572a86c6ad8000001c6000350000cc000001ea2ee2a4400ae28a0000000046a0012c2c421cb18000000000006f8000001d0001230000001a9010922580015b30c7580000000000000291000001a280068c00000000182595a500010e0015220061e8943700058e001048001c4000001f14320003a97e416000f100000013c11aca000000821800006d9aa80062edacd50cd6d4000000004d69347680000006c000af000499b1316000994000000003fc000000006a400000190000000002386053896d000000001d23b65a40000411e1f0000000003a5568002c60018d80060419000118676000000004520000000000000000018000001ae0f5000000003493eeaecb09c324e0005b80002600000292000755238b00c6b09021846b0000f300034252c002c52e80000012e09443c390005b4000162280003d117340000000f01d700075145ad700051c1087d6ce0006a0000686c95607e17e1ccdd29b01eb20000000002994fabf31a9ec3b000070000d1000000000000001503eda117f2be000001f23f863cb30e6000000001140005e91c800000224638ad48ac304130d52c0000000000080cfd2e032c7e4d88b2572888f086b65c794d7a9a0006f1a6ac92b2000d394c158c1c740000000011237c000000c93781a2b9c1325343e5c85c9fd0008300000067a000e60f6000000ce00026600000000000c200a02f000b4c000004ecaf8000000000004f1710004a4002661aca34c500c0001695a80063c001360886902e9882330000000033f0000016886c0006690b0ef57a0016c000000000ba80000000000000000000000000000000000001200040800000000000b3000000000006500000000000071d712070000000021b000000810000aa0000000000000000000000361582492a4074240005400003c95622a0019693b000001302e95860ddb4800192cd80000064e74ce08000000c03c0850000017b1f652e000000000008845eb1f0008740019e07e331ad24a3d6000000003849a575039000cc80000048400000246000000262430000006f1990007600725036a5c0000004100000023105c0a57c90d07c000003570000000000039c000801bb000745b707740c99dafb686a6341a70000000000000029eac5559c8000000000000000a0000000ac0000000020c00191251000000f436100010400000040001a8000186444032dc116ae9b69223480011e0fd0c06fc010f24f81193e8000000009a00016c00000000000a88000000000401d000554000122ed4c4394ed00046400000000220474be25600065d4480038a00000000668590752f11082f82d9fe34cd102f98e0aec700000000000148000000651b8800000c753500035c0009f17d23c7248909000046
  | 6 => 0x1770000000000000000010000000000000ee000000a600015a0008d8001680008511fadb306285092a729c8800f91a2bc9d4efa0d000000a8000456bcd658703c65d80013556e0c4da000064c14000000008e000000000000000000000000020f00010c000001220000000038833c000005e00000022c0000007222d000000ceb040000005580000000160000434001961494bc001378000005e4000ca240001012e31e20000007b6ca2d58d2e60e200000000000971ba000000001b637250ca20faae519c6cd49800000d580000064c000002a342a1a00000002a6415a00027a000000000008700018c0000000003618ca0800000414ae00000000013400000000000002f4000000588000b2a14a018700000000000000abc4a800000000699f46309e4ec8001f802913afb5a4d491a3415c242c003382f6260282a63da7fd008001b2000000001c0d80000005c8000000002a2c0c000004800000000000092c0018b00000000000000189590a2214000001545a8b319c81a000001acb2500066c2e80012411c0029447a058000256f4349778220006546aa730000000015d0009a120b37000d6c53867000430a69035520000027f624938e58a34b2000d5800000660003330764b40000352a384de8f744c00000017626315308003e612c0008e000ca8a9b0000002c621ca03c0004e9485f43741e85125e00111b2f28c7ec000000005a93180069693c0e205000000002c1000000000005fc0014e94127479c001cf6f20000cb2b3dec6400000380000000b800000000000000000002f70000000000042244d0f1ee000001888004da0019488a000a28002d61b600159a5d00000000000000c2c0037d00000000000138000003096bc0000008d066000290000006dd7634c5a0001b9861538bc829b432844f0c8893000000000005ba
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x18020d0000219a099a800091a10a12941695079d10179c001c9e0c1e8d921d91049f800e85198f0b16170a80041b860000069b00000b80139f018880001593208000030c8f8390881920058298948901070e01890804303120400000241cd0e00000706c0008a8e2b18a0a143870590514ca9238a8629283251c563d0941c1ac629684a0d307150c505068cb9e8428283865516014831c92a4b00a418cd070584420c6c23928220863641c14110431a30e0aa2a018e0d54189500c670382c221043075da540c421d08c818a4210ec031181210868a38aa6a08818354c6250440c2aa6b08a42062552584521025838ac019081451c55354440c1aa6312a22041d76994311020ebacc790881521c14314930930e0b26649860d6414b324c2a83828628a61455d33214530930e0b20629841d76150314c306b20a418a61a2188404c030d20c2202601841d7695031c827038ac019041075da5310020d10c620240106a061101200820ebb4a818e21265d8311031083aed2988108495760c4408430ab2ac818821641c1640c410b20e8b0062086916458031042e0392c018821255d831100109a2ec18880086196558c40042c838ac620021641cd6110010d22c6b0880085a07258440042c938c6220021265d83110010962ec1888008593760c440043493b06220021645d83110010d22ec1888008491760c440042c939e4220021a499031c8010
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x18140014440180041c0b7240c0b4048015a048158c52d0941910815cf4214141a08805506254031a048154c6250440a048154c6254440a088059052cc930910805d33214530a0880590520c530c11651c1640c410c81641c9600c410c11651c56310010c81631c96110010891879d83110010891869cf21100108918799031c8010
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 44
  | 5 => 820
  | 4 => 894
  | 3 => 68
  | 2 => 15
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s2K7 (i*5) 5
  | 6 => packedAt s2K6 (i*16) 16
  | 5 => packedAt s2K5 (i*27) 27
  | 4 => packedAt s2K4 (i*38) 38
  | 3 => packedAt s2K3 (i*49) 49
  | 2 => packedAt s2K2 (i*60) 60
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s2K7 (6+((h/1+packedAt s2K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s2K6 (788+((h/14+packedAt s2K6 (704+(h % 14)*6) 6) % 63)*7) 7
  | 5 => packedAt s2K5 (25143+((h/273+packedAt s2K5 (22140+(h % 273)*11) 11) % 1191)*11) 11
  | 4 => packedAt s2K4 (37250+((h/298+packedAt s2K4 (33972+(h % 298)*11) 11) % 1569)*11) 11
  | 3 => packedAt s2K3 (3486+((h/22+packedAt s2K3 (3332+(h % 22)*7) 7) % 82)*8) 8
  | 2 => packedAt s2K2 (925+((h/5+packedAt s2K2 (900+(h % 5)*5) 5) % 22)*5) 5
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffffffff01ffffc0fffffffff80ffe3ffe3f
  | 1 => 0x1fffc07fffffffffff03ffc07fffffffc71fff
  | 3 => 0xe03fff80fffe03fffffc0fff81fff03ff9e3c7
  | 4 => 0xffc00000fffffc07fffff00001ffffc1fe03f8
  | 5 => 0xffffffff00000007fffffffffe000001fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x224a450a211c4891402cb2d2a25886521a6e1b
  | 1 => 0x8909314522491228b01554854ab18a4c514ed
  | 3 => 0x5a230a2694483a44d55409ab1135a23969a346
  | 4 => 0x933a2c58e8912077669a603261c6cf11be03b0
  | 5 => 0x1c3c3060f0e1c387b8e38e3c78070c21f7d800
  | _ => 0
def s2Atlas : Atlas := ⟨7,rawDecor 59 s2Pos s2Neg, 0xee88aa88cc888800ee88aa88cc888800ee88aa88cc888800ee88aa88cc888800ee88aa88cc888800ee88aa88cc888800ee88aa88cc888800ee88aa88cc888800, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_16333
namespace PEqualNP.Outside.L_meta_16333
open PEqualNP.Outside.L_meta_16333.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x710e14d3c00cb00000029018124220000030018820bf43de43bd43dd439d43bf42bd42df32dd32be41bc41de31dc31be40bc40de30dc30
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x27001600240653060010022810000000c7552438fa92871c5150e38a0a1c754f428eaa6651d544ca3aa620c7d52318eaa0631d531023ea9184755030
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0xa018085185544ca18605513286983548c61661d5230
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 17
  | 3 => 13
  | 2 => 4
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (i*5) 5
  | 4 => packedAt s3K4 (i*16) 16
  | 3 => packedAt s3K3 (i*27) 27
  | 2 => packedAt s3K2 (i*38) 38
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s3K5 (6+((h/1+packedAt s3K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s3K4 (297+((h/5+packedAt s3K4 (272+(h % 5)*5) 5) % 25)*6) 6
  | 3 => packedAt s3K3 (371+((h/4+packedAt s3K3 (351+(h % 4)*5) 5) % 22)*5) 5
  | 2 => packedAt s3K2 (155+((h/1+packedAt s3K2 (152+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x1ffff81ffff83fc1fffc1fff83ffe07e79f3f3
  | 1 => 0xe07fffe07fffc1fe0fffe0fffc1fff819e7cfc
  | 2 => 0xff83ffff83fffffff03fff07ffe0ffffe78f1f
  | 4 => 0x3fffffc0001ffffc00007ffff0001f80fe0
  | 5 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x430888c51090504052cc09498129212c28b171
  | 1 => 0xc91111432122028a05552092a4124b049254b4
  | 2 => 0x42222080a442114a02252044a409451450a0a
  | 4 => 0x965bc4924876b5e7398318c7739c0619f80fc0
  | 5 => 0x1863871c738739f9ce3b9ce063181861ffe000
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xe8e8e8e8e8e8e0e0e8e8e8e8e8e8e0e0e8e8e8e8e8e8e0e0e8e8e8e8e8e8e0e0e8e8e8e8e8e8e0e0e8e8e8e8e8e8e0e0e8e8e8e8e8e8e0e0e8e8e8e8e8e8e0e0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_16333
namespace PEqualNP.Outside.L_meta_16333
open PEqualNP.Outside.L_meta_16333.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x452000000017060130a5870f060ebc2a510a8f932a640000000000006000000b800924a538240840042838000360118d16ac08000740000000000446802d00000000000b0c000082800000001e000010300000071a180050600000ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32df32fe32fd32dd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30de30fd30fc30dc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x61dd320c3b864185f94430bea8861df310c3bc6218774c430ee188617e500c37c80186f10030ef98061fa300c3ba60187e4c030efaa061de540c3baa8187715030efa9061de520c3baa4185754830ee29061df420c33e84187790830eea10619d420c3b8841877d4430ef28861dd510c3b8a21877d0430ef20861dd410c3b8821877c8430ef10861dd210c3b842187794030af28061da500c3be80187790030cf20061dd400c3b880186710030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c83bca7905794f20bea9e41dd53c82baa7905f14f20dfa1641bd42c83be6590774cb20bf28e417d51c837c81906f10320ef18641dc30c82fea9106fd52209faa4417e54882faa9105f15220de2a4413c54882fea71077d4e20afa9c417e53882faa7105f14e20ee29c415c53882faa5106fd0a20dea1441df32883ba65105f94620bea8c41ee21883d843105f94220df20441bc40883bc6110770c220f790441fb20882fea8906fd51209faa2417e54482faa8905f15120de2a2413c54482fea69077d4d20afa9a417e53482faa6905f14d20ee29a415c534837e84906f50920ef99241dd32482fea2907dd4520bba8a417c51483e8a2905d14520df20241bc40483bc6090770c120fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53082fca4106fd0820dea1041df32083ba64105f94420fb288417651082faa2107d54420baa8841ee21083d842105f94020df20041bc40083bc6010770c020f790041fa20083da40107e48020bfaa6217e54c437ca9884f95310beaa621bd54c427aa9885f15310bfa9e217e53c43bca7885794f10bea9e21dd53c42baa7885f14f10bfa96217e52c42faa5885f14b10dfa1621bd42c43be6588774cb10fb10e21f521c437c81886f10310ef18621dc30c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c528437e85086f50a10ef99421dd32842faa3087dc8610fa10c217e508437c81086f10210ef18421dc30843f441087e48210fb88421fb10842fea8886fd51109faa2217e54442faa8885f15110de2a2213c54442fea68877d4d10afa9a217e53442faa6885f14d10ee29a215c53442fea4887bd4910b7a92217e52442faa4885f14910f6292216c524437e84886f50910ef99221dd32443ec42887d48510df20221bc40443bc6088770c110fd10221f920443f620887d84110bfaa0217e54042faa8085f15010bfa98217e53042faa6085f14c10bfa90217e52042faa4085f14810dfa1021bd42043be6408774c810bf28821f721043e842085f94010df20021bc40043bc6008770c010fb88021fa10043ea20087e44010
  | 1 => 0x721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21dfa1243bd42487be6490f74c921fb90a43ee21486fea090df14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53087bca610d794c21bea9843dd53086baa610df14c21bf29043bf420877a8410f7cc821ee990437e51087de4210fd88421f690843f521086fca010fe94021bd280437d50087f2a010de54021bf29e81de53d02bca7a05f54f40eea9e815d53d02fca5a05f54b40dfa1681bd42d03be65a0774cb40bf28e817d51d02faa9205f94e40bea9c81bf439037c87206f50e40de21c817e52902faa5206fd0a40df21481bd4290378852077cca40ee994817e51902faa3206fd0640df20c81bd419037883205f94240dfa0481fb409037ea7206f94e40dea9c81bc539037ea5206f94a40dea94813d5290378a5206fcca40cf99481be329037a6520674ca40de19481bf519037ca3206f54640de28c81bf319037c63206f4c640de18c81bf219037c43206f48640de10c813e50902fea6a077d4d40afa9a817c53503b8a6a05714d40bfa92817c525037e84a06f50940ef99281dd32502fea2a05f14540fda0281be40502fca8205f94c40bea9881bf431037c86206f50c40de218817e52102faa4206fd0840df21081bd4210378842077cc840ee990817e51102faa2206fd0440df20881bd411037882205f94040dfa0081fa401037a80207e50040dfa9881be531037aa6206f14c40dfa9081be521037aa4204f54840de29081bf321033e64206f8c840de990819d321037864206fd4440df28881bd5110378a2206fcc440df18881bd311037862206fc8440df10881bd211037842206f940409f28081ba50102fea9985f95330df2a6613e54cc2faa9986f553309eaa6617c54cc2fca5985f54b30dfa1661bd42cc3be6598774cb30bf28e617d51cc37c81986f10330bfaa4617e548c2faa9185f15230bea9c61df438c3bc87187750e30ee21c617e528c2faa5186fd0a30dea1461df328c3bc6518774ca30ee194617e518c2faa31877cc630ef18c61dd318c3b863185f94230df20461bc408c3be61187ecc230efaa461de548c3baa9187715230efa9461de528c3baa5185754a30ee29461df428c33e85187790a30eea14619d428c3b8851877d4630ef28c61dd518c3b8a31877d0630ef20c61dd418c3b8831877c8630ef10c61dd218c3b843185794230efa0461de408c33c81187750230ee204619c408c2fea8986fd51309faa2617e544c2faa8985f15130de2a2613c544c2fea4985f14930dfa1261bd424c3be6498774c930bfa8a617c514c37c80986f10130fd98261de304c2fea8185f95030beaa0617c540c2fca61877d0c30ef21861dd430c3b886185f94830bea9061bf420c37a841877cc830ef19
  | 2 => 0xafaa6217754c42aea98857e5210b7e84217b90842dea1085ed4210afca2215f54442bf280857d5010afea9995f95332beaa6657c54ccbbe87997790f32eea1e65dc43ccb7e85996f50b32bf28e657d51ccafca1995f54332efaa665de54ccbbaa9997715332efa16659f42ccbbc85997750b32cea1665dc42ccbbea3997794732eea8e65dc51ccbbea1997794332af28665dd50ccbb8a1995fd5232bf2a465be548ca7ca9195f55232deaa4653d548caf8a9195f54e32aea9c657e528cb7e85196f50a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132beaa2657c544cbbe86997790d32eea1a65dc434cb7e84996f50932f799265de324cafea2995f14532bfa82657c504cbbea8997795132eeaa265dc544cbbea49973d4932efa12659f424cbbc84997750932cea1265dc424cbbea2997794532eea8a65dc514cbbea0997794132eea8265dc504cab8a0995fd5032bf2a065be540ca7ca8195f55032deaa0653d540caf8a8195f94c32af298657e520cb7e84196f50832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef50f41bf296837d52d077e85a0ef50b41ef99683dd32d06fca1a0df54341beaa4837e53906faa720ef90e41de21c837e52906faa520efd0a41dea1483df32907ba6520df94641dfa0c83f741906fca120df54241bfa9a83df53506bea6a0df14d41ee29a835c535077e86a0ef50d41bfa92837c525077e84a0ef50941ef99283dd32507ee82a0ef90541bfa82837c50506fca820df94c41ef298835e53106faa620f754c41aea9883be43107788620df94841bea9083bf421077a8420f7cc841ee990837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331ef21e63dd43cc6fca598df54b31dfa1663bd42cc7be6598f74cb31bf286637d50cc6fea918df95231beaa4637c548c6faa718f7d0e31ee21c637e528c6faa518efd0a31dea1463df328c7ba6518df94631ef98c63f7318c6fca118df54231bfaa263bf544c67ea898df95131beaa2637c544c778a898cf15131ef21a63dd434c6fea498df14931dfa1263bd424c7be6498f74c931fb98a63de314c6fea098df14131bfaa0637e540c77ca818cf95031beaa063bd540c67aa818df15031bf29863df430c7b88618df94831bea9063bf420c77a8418f7cc831ee990637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c877ca990cf95321beaa643bd54c867aa990df15321bfa9e437e53c87bca790d794f21bea9e43dd53c86baa790df14f21dfa1643bd42c87be6590f74cb21bf286437d50c86fea910df95221beaa4437c54886fea710df94e21bea9c437c53886faa510efd0a21dea1443df32887ba6510df94621f790c43f
  | 3 => 0x10ba21e2c26b5f90580ee444bb98c000ec8001c7000fdc00010422d1d330005c68a800000000d31f9b3c5c2d853197b276a4d1c3073b8d052dacb6c0d7cb32c4766a619f9bb5d4811111fb742cb5dbb171a0000100007caf1d2480067c3d00000000026c0035110a22827a2b0460000032a198ea198b27000c594482f2165bd8e8ca28c591250000e80017a000416464e090e55aea800000166b95d0000164701a238e21e000000006140fc00000190000000006b6000001733fe000468004c8398000000000020080a80d01201801009004014040000120000000e016004000000020040080000e0000300601a0100200700a018050050060100081200400c03003000020010000040000180300e00800000000034048030000100900900601c020000000100200600200002805000000008020000100080100000000006000010008010000040000500e0040180000203c0101500a000000000020040200000604c000070280000000100801803800012004000020000000300800a0100880300602400004044020020000000100000100201000002040000008010000240000000a0100680000800800000006014058000000040300b004010020030060080080000c000048020100000000200c0000000000005c0000900009c07800004000000020000100100302600404000002000008000000000080a00800c030130000040c00b004000048010000400080100000002802002010000030000040080400202c000050100000080100000c02002004018000010000080000000000c1400100008c0700001a04806000008000008050000200000900001000800002004010010020080000003400c06018000000020050000040401200003005800008018008000020000c8140060040b80800c0180080601200c00df94b43bea96877e51d0efaa3a1df94343bea86877d5490efca721efd0e43efa1c877e5290efaa521df94643bea8c877e5090efaa121f7d0d43df21a877f5250ef8a4a1dfd4543be28a877f5050ef8a0a1df95043bf29887bf4310fbc8621ef50c43eea18879d4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f90f42dea1e85bc43d0afca3a15f54742bf286857d50d0b7ea7a16f94f42dea9e85bc53d0b7ea3a16f94742dea8e85bc51d0b7ea1a16f943429f28685bd50d0b78a1a15f552429eaa4857e5390bbca7215794e42bea9c85dd5390abaa7215f94a42dfa1485ef4290afca3215f54642bf284857d5090afea6a15f14d42dfa1a85be4350b7a86a16f10d42f7a1285be4250afea2a15f14542bfa82857c5050b7ea6a16f94d42dea9a85bc5350b7ea4a16bd4942dfa8a85be5150b7aa2a16f14542dfa8285be5050b7aa0a16f141429e282857e5410a7ca8215f94c42ef298855e531
  | 4 => 0x4511cf3f1000adc62bdd000001a3000348d20000e7000934c80b6000648da0001d26687e9a80ec000000000000005a8000004f0bf800000000078002307097d000000001841af5b4a4454000656c90002ca0fead1ec3d126494c329be50a2b054bbf0000c855800738e88ad81b51686c000700d4000000a000000049a4e402ab8be86f246f90000bd25e0015c1002ae420fd3cc3229ad80bd37a8ee8000003dc00000257520000000e4752359478000000009e972000839182aa4eab189f16c1f0da00000024c8c54b9020eaf68001891a4fd979987196bb187bb4000000c0073000000000007807d967800664065b62e400000030000000e94000005eaf28000af0008700035d63e480a100000078c002de5bafc1ef0151c4069c6b8047ea107ba9f0005e4002a964a0007284d79edb400036642354003ec1a69583eb0c4900980c1480000012080058e00047ad60bc000b125a2a2000003eb5fa4cc95bc959816d170545da000440ce45a0001712c0001f0c9b6f0c2000000000006dcc31ce6b85350a8dc0680000000060c0012ab1b0e42e8001ea0002ec00216180299978000000013605c2ca2556926a17ed2c000000006c84b9340ac248001fd64ca7000000000001b3aa5000bb90e8900fc1315926261a835cb27705673cef1854ba67ccb1226a89c92a2217b8849f3b8c76237c898794b2cec4319c1a8000000c6000085301d0000000e90a4000000ac00050400053bc446e000002a4346d40a2af7672000e48002be6c5b18003f0001902796f8001bd0000000200000031a001b98000000000009c1c0139890006ca000b73b0116a748a00078c84c0000034e0018d000000a0c00000000000001971885480011611200166b5518e000002733860007500057e850000004d0a500028c1e64b4000004fe35c003c14be1e0aa00a1467dd5eaa757410c00000000000001e7540000b680049e5001f03300074c001d70cc00000274000000ea8c356000000107000000d9959000000359d1000001ac9ed0008cc0000000000080b6a0ae555f737f40e0b000000000b6c2d2461b027c129821d630943adf08e5c503000094b5c0000048ec4dcd2e927e0f51f0000186a5813e02424d5daafc4ca5e0003a358650594a197de4dc0114365094134a1702e0e8973494527e4003726ea001980535a019dc23bb0000004600004e87d74000758aedeb91e514679790b0342fd1b4bb65a266c0000056a9bcbd000006000002fe666eb9258870004e800127000d2949176000000000623de7340000000000122000000ce8002033e600000278000001d3800796001d3000144000000d97ac1654d80047800000000000001960cf69e000001b53d22593e39d468f6c02afb000e44efb1c02847c00000404000c7aef7302c400022572574a50fa66c568c51f56124
  | 5 => 0x694000002d29e8001a24463f0dd0005422f08b9884003d888170410260000fb79a3048d1ae51a000db00000072da7318590791ca3221fc120cca862960011a95e2f8930001474f6768002f8000000bf395726414fa371000f41e7352558279fa800236385bf3450000000000006efb436000502e18d500d3d61a40e9395a6c787faf169a8edc3800000d08e20006e86501aa704a2df56c1832608999e80008c2f8002a83f81250780052a728000000005814700060ac8cde8810008bdb21d8000000000006d60edcd800000fa42e81c56c000000004dcb00000007106e40000000004de1a99000f98001e82a6b55e431157c000000000002d0140b81ba000000001dc000d80007203d53f00000c000789283ac1e8168915fe0005b81e34c7c000000000000c20e851071400163248001c4800000001c2ab1000000a78003020018a8000f60014f240000000002f02ea00000016000000001e62b8001df00b356fa80036e458558f10001b47f8002e76b4191bd8ec5f2890000043780000f82900089c0012508401db3000000000000395ec4244a1063c00009c00058a7b0002eb000824258a1024869803c50020000039f078001368527c6ddc340000008a1ccabc000000f8800048b09880db472ef5339291bc97000112330ce0d00001c60000000054c000373bc000001c789a5a83b5400f0238cd04cb0e6f067400000784345218000a0750000003ba6fdea8306162b9abbd9292238000c900000000044704000000003c2000001c6358a580005f0000017300008000000000172000000000000000038a000000e62c12a04353ea3a000000003404ec978003351080008ab046068149b24265c001e90007d0000a62a272400066a1815ade4553a470600004800000cddab0000a21b400045592000000005c000000370000c65191c86bc4a88522500076ddc0824147c815195000b39a980023a00138b762ce0014d16b0000001c1b80008418a2364402942a8000000004e9035660396e000000984000004b0eb4003623b20000014e000001dcaa30e2045292d95c4eacc71310007947c80048a000000006b03bdfc08072e5a91e90c75ef7c20a0c3163c831b432d0e0557b8b7c20c441aab7c
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x352c425e63d4b109758f52c423e6494b108f59252c425e6394b109758e52c423e6414b108f59052c425e6314b109758c52c423f65d0b108f59742c431e53d0b10c754f42c423f6550b108f59542c431e5350b10c754d42c42b86050b1097d9732c425d65ccb10c795332c431d54ccb1097d9532c425d654cb10c795132c431d544cb10b618132c431e5390310c754e40c431e5310310c754c40c431e548c310c755230c431e540c310c755030c425e63d52109758f548425e63952109758e548423e64d4e108f593538423e6494e108f592538423e6494a108f592528425e6394a109758e528423e6414a108f590528425e6314a109758c52842f16008610e610030843e02188210bc185208423d62d51108f992544425e63951109758e544426e62951109b58a544425f63551109718d544426f62551109b189544423e65151108f588544423e60151108f180544431f54d4d10c7153534425d62d4d108f992534423d6494d109798e534426e6294d109b58a534423f6454d108f191534426f6254d109b189534425e6514d10c7d50534431c5414d1097588534425e6014d1097180534432f54d4910cb153524434f53d4910d314f524432f64d4910cb193524434f63d4910d318f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109dd85524423e64149108f590524425e63149109758c524426e6514910cbd50524432c5414910d3d4c524434c5314910cb990524432d6414910d398c524434d6314910d9584524436960149108f997424423c65d0910c7d4f424431c53d0910cbd4b424432c52d09108f995424423c6550910c7d4d424431c5350910cbd49424432c525091097997324425c65cc910c7d53324431c54cc910d3d4b324434c52cc91097995324425c654c910c7d51324431c544c910d3d49324434c524c9109d996214436452885109d195214436452485108f996404431f5390110c714e404432f5290110cb14a404423e6510110c7d4c404431c5310110cbd48404432c521011097996304431f548c110c7152304434f528c110d314a304425e650c110c7d50304431c540c110d3d48304434c520c110e610030443685288110f888620442786548110d914a104425f63550109718d540425e63150109758c540426e62150109b588540423f6454c108f191530423e6414c108f590530426e6214c109b588530423e64948108f592520425e63948109758e520423e64148108f590520425e63148109758c520427661148109e980520432e5250810cb54942042b86050810d3949320434d524c810b6181320423e64944108f592510425e63944109758e510427565c84109d59421042f160084109e59610042776544010b918910043b04044010f40c1100427b6544010
  | 1 => 0x831f544ca20c715132882d8604ca208f992518823d64946209798e518825d63946208fd91518823c645462097d8d518825c6354620ba580218831f5390220c714e40882ad6290220c7d4c408831c5310220ab588408831f548c220c715230882cd628c220c7d50308831c540c220b3588308823e64951209798e544825d63951209d9865448275619512097d8d544825c63551209dd85544827461551208f994544831f54d4d20c7153534823e6494d208f592534825e6394d209d98653482756194d208fd91534823c6454d209dd8553482746154d2097994534831f5414d20c7150534823e65d0920c7d4f424831c53d0920ae983424823c6550920c7d4d424831c5350920ae181424825e65cc920c7d53324831c54cc920b6983324825c654c920c7d51324831c544c920e350932482d8604c920cdd53514833454d4520d5d4f514835453d4520cdd0b514833542d4520d5ccb514835532d4520cdd5051483345414520d5d4c51483545314520cdd0851483354214520d5cc851483553214520dc580514823e6590120c7d4e404831c5390120cdd46404833451901208f994404831f5310120c714c40483375110120cd144404825e658c120c7d52304831c548c120d5d463048354518c12097994304831f540c120c71503048357510c120d5144304836451881209798f540825d63d50209d987540827561d50208f596540823f62550208f589540823e64150209798c540825d63150209d984540827561150208f993530823d64d4c209d987530827561d4c2097596530831e5494c20c7552530831e5454c20c7551530825f6254c2097589530823e6414c208f590530825e6314c209d98453082756114c208f992520823d64948209798e520825d63948208f597420831e53d0820c754f420823f6550820c794d420831d535082097597320831e54cc820c7553320825f654c820c7951320831d544c820cd95251083355494420d594e51083555394420cdd0a51083354294420d5cca51083553294420cd95151083355454420d594d51083555354420cdd0951083354254420d5cc951083553254420d9546210823f65900208f596400831e5390020c754e40082ad6290020cd946400833551900208fd94400823d6510020c794c400831d5310020ab58840083365110020cd544400825f658c02097596300831e548c020c755230082cd628c020d59463008355518c02097d94300825d650c020c7950300831d540c020b35883008356510c020d55443008398400c020dc546200826f6548020b9185200827b6548020dc545200825e63d53109758f54c423d62953108fd8954c425e63153109758c54c423e64d4f108f59353c431e5494f10c755253c425d6294f10c795153c431d5454f1097d8953c423e6414f108f59053c423e64d4b108f59
  | 2 => 0x655063097994418c25d651063097997218c25d65c8630a7993218c29d64c863097994218c25d6508630a7990218c29d6408630b6980218c2d96008630a758a408c31d5290230a7588408c31d5210230e6980408c23d62d51308f992544c25d639513097d8d544c23e65151308f588544c23e64149308f590524c23e65d09308f197424c23e65509308f195424c25e65cc930c7d53324c31c54cc930c7d51324c31c544c930d3d49324c23e65901308f994404c31f548c130c7152304c26e62150309b588540c27661150309d584540c23e6494c308f592530c25d6590c30c7151430c25d6510c30c7550430c23e64948308f592520c32e5250830cb549420c2b86050830d354b320c25d658c830a7992320c29d648c830a7990320c29d640c8308fd91510c23c6454430a7d91310c29c644c430a7990310c29d640c430d5544310c29e64cc030a7593300c25f654c030a7d91300c29c644c0309ed95300c2da60d5030c7550540c2ce6215030b3588540c2d66115030b5584540c2da6015030b6983520c29e6494830a7592520c29e6414830a7590520c2d66114830b5584520c2da6014830c754b420c29e60d083097996420c25d6590830a7592420c34d5290830d3549420c2db6050830b6181420c38f6250830e3949420c31d5250830e3549420c30d5250830e6d81420c29c6050830e6181420c298605083097994420c25d6510830a7990420c2da60d4430a7d91510c29c6454430a7990510c29d6414430b3988510c2cd6214430d5544510c2da6014430b6982410c2d9609043097d95410c25c655043097994410c25d651043097997210c25d65c8430a7993210c29d64c8430d354b210c34d5248430b6d81210c2d8604843097994210c25d6508430a7990210c29d6408430b6980210c2d96008430c7d0a500c31d4294030d6982500c39b4294030e650a500c25d65d0030a758a400c31d5290030a7982400c31e5090030e6942400c25f6550030a7588400c31d5210030a7980400c39a6010030c7940400c39a50100309798f54c825d63d53209798c54c825d63153208f99353c823d64d4f20c795253c831d5494f20c795153c831d5454f208f99053c823d6414f20c794f42c831d53d0b20c794d42c831d5350b20c795332c831d54ccb20c795132c831d544cb20e350932c831e5390320c754e40c831e5310320c754c40c831e548c320c755230c831e540c320c755030c8398400c320cb58b548833a60d52209798e548825d639522097d8d548825c6355220cb588548833a6015220c7d53538831c54d4e20d358b538835a60d4e208f992538823d6494e208fd91538823c6454e20c7d50538831c5414e20d3588538835a6014e20c7d4f428831c53d0a20ae983428831f5350a20c714d42882b86050a20c7d53328831c54cca20b6983328
  | 3 => 0xe40c7d4e53902ba6014e40ae983529029e6394a40a758e529029e6314a40a758c52902b66114a40ad58452902ba6014a40c754b329029e60cca408f996329023d658ca40e3d89329031d524ca40a7181329023e650ca408f594329029e63d4640a758f51902ba60d4640a798e519029d6394640cdd4651902ba60146408fd95319023c654c6408f994319023d650c6408f997219023d65c8640a798f219029d63c86408f994219023d6508640a798c219029d6308640ae98021902b960086409758b535025d6214d409798c525025d63149408f997425031f53d0940c714f425031f5350940c714d425032f525094097997325025c65cc94097995325025c654c940c7d4e405031c5390140c754c431025e63948409758e521032d52d08408f596421029e6390840a758e421029e6310840a758c421034e524c840d354932102d8604c84097d8d511025c6354440a7d8d411029c6350440a798c411029d6310440cd544411029e63d0040a758f401023f6550040a7d8d401029c63500409ed9540102ba60d4c40c754c53102ae6214c40ab58853102b66114c40ad58453102ba6014c40ae983521029e6394840a758e521029e6314840a758c52102b66114840ad58452102ba6014840c754b321029e60cc8408f996321023d658c840a758e321032d528c840cb54932102bb604c840ae181321038f624c840e3949321031d524c840e3549321030d524c840e6d81321029c604c840e61813210298604c8408f994321023d650c840a798c32102ba60d4440a7d8d511029c6354440a798c511029d6314440ab98851102ad6214440cd54451102ba6014440ae98231102b9608c4408fd95311023c654c4408f994311023d650c4408f997211023d65c8440a798f211029d63c8440cb54b211032d5248440aed8121102b860484408f994211023d6508440a798c211029d6308440ae98021102b96008440c7cca501031d3294040ce982501039b3294040e64ca501023d62953308fd8954cc23e6494b308f59252cc23f65d0b308f59742cc23f6550b308f59542cc2b86050b30c795332cc31d54ccb30d354b32cc31e544cb30c755132cc27661d52309d587548c31e5450e30c7d50438c23e6494a308f592528c29e648ca30a7592328c34d524ca30a7990328c29d640ca308f992518c23d6494630a7d91318c29c644c630d5945318c29e640c630a7590318c29e64cc230a7593308c2d661d5230b5587548c2da60d5230c7d52548c2da6015230b6983528c29e6494a30a7592528c29e6414a30a7590528c2d66114a30b5584528c2da6014a30c754b428c29e60d0a3097996428c25d6590a30e3d89428c31d5250a30a7181428c25e6510a3097594428c29e64d4630a7593518c2da60d4630a7992518c29d6494630d5d46518c2da601463097d95418c25c
  | 4 => 0xf990524c63d64149318f997424c63c65d09318f995424c63c6550931c7d53324c71c54cc931c7d51324c71c544c931d3d49324c6d4614c931c7152314c63e64d41318f593504c63d65950318f58a540c63e6095031c718d540c63f62550318f181540c63e64150319798c540c65d65d0c31c7553430c65d6510c31c7550430c63e64948318f592520c63f65d08318f597420c63f65508318f595420c71e54cc831c7553320c74d52cc831b5587320c71e544c831c7551320c71d54cc43197d95310c69c644c431c7551310c677654c4318fd91500c63c64540319798f54c865d63d53218f98254c863c60553219798c54c865d63153218f99353c863d64d4f21c795253c871d5494f219798253c871e5454f21c755153c865c6054f218f99053c863d6414f21c794f42c871d53d0b21c794d42c871d5350b21c795332c871d54ccb21c795132c871d544cb218fd9150c863c645432197d8d50c865c635432197d8d548865c63552219798c548865d63152218fd91538863c6454e218f990538863d6414e21e3509328863f64542218f191508865f63542219718d508865f63551219718d544867b60551219e181544865e63151219758c544863f6454d218f191534867b6054d219e181534863e6414d218f590534863e64d41218f593504865e63d41219758f504865e63d50219758f540867a60d50219e583540863d65950218f982540863c60550218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c2197982530871e5454c21c7551530865c6054c218f990530863d6414c219798c530867a6014c219e580530863e64948218f592520865e63948219758e520863d65d0821c794f420871d53d08218fd95420871e5350821c754d420865d65cc821c7953320871d54cc82197d95320871e544c821c7551320878d424c8219bd9521086776548421e950921087c53248421ce95250087395494021d694e50087595394021ced9250087386494021d6d8e50087586394021ced0a50087394294021d6cca500875932940218fd91500863c645402197d8d500865c6354021ce95150087395454021d694d50087595354021ced9150087386454021d6d8d50087586354021ced0950087394254021d6cc950087593254021dc885500877121540219758a53d025f6254f409798e52d025d6394b40c794f42d031d53d0b40cb54b42d031e5350b40c754d42d025f65ccb409759732d025f654cb409759532d02d8604cb40c794d439025e6394a409758e529029e6390a40a758e429032d5250a40a798c429029d6310a409798e519025d6394640a7d8d419029c6350640cd945419029e6310640a758c419029e63d0240a758f40902b661d4e40ad58753902ba60d4
  | 5 => 0x5350a9f6354542a718d5150abb6054542ae1815150a9e6314542a758c5150b355114542a798f5050a9d63d4142a7d8d5050a9c6354142add855050ab46154142979825310a5c6054c42c794f4210b1d53d08428fd954210b1e5350842c754d4210a6f6550842cb9514210a5f63540429718d5010a7661153329d58454ccb1c5450f32c755043cca3f64547328f19151cca3f64543328f19150ccacd62d5332c755054ccacd6215332b598454ccad56115332a798342ccb8f6250b32a718142cca9f6454732a719151cca9e6414732a759051ccb555114732a799350cca9d64d4332b598750ccad561d4332c7d0a50ccb1d4294332a7d9150cca9c64543328f982548ca3c6055232c7953328cb1d54cca328fd91508ca3c64542329dd85544ca7461551329ed81544ca78605513297997434ca5c6550d32c7151434cb1d5410d32a7992324ca9d648c9328f990514ca3d64145328f993504ca3d64d4132b358a544cacf6255132b5d85544cad46155132b6d81544cad86055132c7550544cb8f52d0932a7983424ca5e6590932a7592424cb8f6250932e3d49424ca9c605093297994424ca9e6410932a7d91514ca9c6454532b6d81514cad86054532a7990514ca9d6414532d5544514ca9e64d4132a7593504ca9f6454132a7191504cad76154132b5185504cb1f4214132c7508504ca5e63d50328f596540ca3e60950328f181540ca3e64150329798c540ca3e64948328f592520ca3d65d0832c794f420ca3f6550832c794d420cb1e54cc832c7553320ca5f654c832c7951320cb1d544c8329bd95320cb4e534c8328fd91500ca3c64540329798e52d065d6394b41cb54b42d074e524cb41d354932d065f63543419718d50d065e6394a419758e529072d5250a4197d8d509065c63542419758b535065e60d4d4197588535065e6014d418f997435071c53d0d41c714d435065e63149419758c525071f53d0941c714f425071f5350941c714d425072f5250941ad185425065e65cc94197197325065e654c94197195325071c53905419798f505065d63d41419758a531065e6094c4197d89531065c6054c418f596431071d5390c41c754c431065e63948419758e521071e53d0841c754f421072d52d0841ad587421071e5350841c754d421065f65cc84197597321065f654c84197595321071d53d04418fd95411069c6350441c754d4110677655044197d8d501065c63540419b98854cc66d6215331c715143cc63e6494b318f59252cc72e5250b31cb54942cc74d52ccb318fd9150cc63c64543319e983548c67960d5231c7d50438c63e6494a318f592528c74d524ca318fd91508c63c64542318f58b544c63e60d51318f992544c65f63551318f994544c71d63151318f588544c63e601513197996434c71c5490d3197195434c71c5450d318
  | 6 => 0xc60000000000002868001b000005c29d1df1cd0f0000114a9680000016700000000017614900b80000004611a9018190000329ae25c0000000000d900027f0000000000000000000128000000001081720000000428000000398001cc8b219d96e8ad8000000da800000000803c00000000001800400000400c01400c00801803800001000001401402001000002400400002000000001c00000400400400400000001000401802000400000000401400400800000000000c02000403400000001c00000c00400000400800402800800801802c00802002400c00400400000400801400001000000000001401000400000c00800000400000800000401400000400001002000800400001800000000000000000400800c00000001000000003400800000000401800000001000000400003c00400000000000800401c00401800800800400400800000000000002800000000000c00002001c00000c00000800800000001000000001000400002000c01000000800800c00000400400000801000000800000400000400400000000000001c00c00000400800000400000001000000801c00001c02400c00400000800000400000400000801801800401400c01000000800402400400000401400002c00800000c00c00400800000800400800800802c00403400c00000000000000000000000000803800800000000001000800400400800000000000800400001400401000000000000400000000000400400000800c00000c02800000000000400400001400000000400800400000000c00000400c00000000400000c00800400000400000000000800000000000002401000000000400001000001800000401400800000402402800800000000400001001001001402c00800002800000400400001c01400000001400000802c02400802800000000000801c00000001800001000402800400400800000001c00c00000c00400400800000400401000800001c00801000400000001000800c00001400c00000000400800000400000000c01400800000000c03c00400000c00400c04000c02001c00001400000401e9d6490c438fd954310e5f6550c43a7d954310f1f6550c43a7d894310e9c6150c43a71814310f1d4354843c750d5110f1d4394043c754c43d0a5f63547429718d51d0a5f63543429718d50d0aad62d4f42c754c53d0aad6214f42ad98453d0ab56114f42a7d8d51d0a9c6354742a798c51d0a9d6314742cd54451d0a9e63d4342a758f50d0ab661d4342ad58750d0a9f6354342a718d50d0a5e6094e42971815390b1e53d0a42c754f4290a5f63542429718d5090b1c5350d42a798e4250a9d63909429798c5150a5d63145429798f5050a5d63d4142ab58a5350aaf6254d42add855350ab46154d42aed815350ab86054d42c754c
  | 7 => 0x2188001e00000000001c80001a50000000000000010000518000000000001f780000000000000000012400009a8000001909d524f84b1930000000a609a18f16a80000004827a80000009e2929331c51598000000002a017f8c894e8002982550000910000c526a0ed0b9a1c8000ae00286b07828f0298bf009816922840048a381a393c93d966a8c03d8000f58000000000001fc21f8000002310002488f68e280015500000024b917800263a8a13c0000970000000000000001320a32698620000808000000000b78000002641a5a3c98d1af1170b58000001060000000000000000000000001e08c10001ff00000027800000000002700000013880000000000008800000000000020229a18780000000021824b0000002140db00015c00013424a0200000000000000000000001520000000000000000001628002581e3a4d86d1548000001480001ce80013e8000000001eba9180000000000019e00006600002400027f9a60000000118000229048000c085c8001da23700028928c8ab1711b980021789780022e16907185fa7400026f0000000000c78000000000000000528001f30000000000000002268000308001e225a0001a82898000e10440ef00025e24d000000000000000107a3a9ba8000a425ea3b8002900000cb80000000000009c0001c880000002600000000000000014c8000aba168000002601ab0000000f41c280000012d06791f0c382094780017500000020f0001dc8000af8000001bd1530001260d980000000009000006a8000000000000000000f88000000000dc14a0348e202312880024c80000011296d00021107c06f11d80000000000e8b68000220002010001898000000000731250000000000001b404a00001487481b0002150000af0fb233a1f00000000000029d8000001ed18b80019780008e95b99f18580000002f1b10001518c20000ce9f20000b70180f813f0ac8f225c80008d25b80022b00009c83c9781159fe8ef8000ae89f0311ad14d25600000025d20d9808000000521a40001f08000000001b60000868c697e8001058001be80000010c8000a8a5f8600498000001c200000014b8000000001868000000000001b5800000000000000000047a759bb85f00020e8000001a194aa100001c780180a00000000015400012387b8d413087f00000000009f89600000009480004900017918119b8860000f90e92198e180000000000000000008c9e923505e1f19428000dfa6882d80000000017580000016808f000000000031a432840000000000000840000a21ab80019680001728700c80000021b00000000000000015f0002730000001fb0000001630000000000000000e51fd0561e980010f8000a48001d100006480029f99380000000017787980026900029400000500000
  | 8 => 0x2750000001748000000000000000000000000c900000000000000000021700000019900003f27d80029600028380002800000000000000000003300006390a00021a9bca2c84d0000001f28000000000c19c40000ad0000000000002288000000000000000de99a0988002721c91a71d99dd8cca4917c9f600005d80026580000017a26d02c00b1d722400000021616480000019200000013a9220001350002579820000000d20000000000b08411a480004e0959fa8150811168c314893d2848e80001ac9662811d399c8000e300020480000013916198888c07fa5380f23f800000245000084835a2f80000000000000008380012914b2930000e980000002d00000000000000000001f2909db11b2191c70000000000000001b68000002860a500000000000000014185911000000028800001e0558000000791d200000028b80000027e00018c194000000a5912b00217318726700000000029115f80e00000000027680000000000000000024210000000000029500000000010b0001130000468818000000001c68000878cda50a0c02926e8000b60001b480015e8968001071aa0000360d783200006703f8000001ac0faa1a20d0ea8f48000b00fe8000000bb1110f980000025300000000013813b1960000000000001231008000000000002378001cb00000013020a800000000000000000151000054000000000000000000027a9480015d00019880002a29a8000001b702e80000000026200000000007600000027b1b28d50f11c4a470000cb16ca8780002f8420738000a81582708e01f399180001d8002092858000000000000001818000000001e180027c8000000f38000002390000001e60000000001b30898249d796b239a458ff8000ba91e0001e51998000000000001ce00000000013e0048000df00000019f80008700405ba1d2549f426313681600000000000000027a00028d0be0d080005500013720a07010100008a8000000001188000f30000000002528001658450692461ee00000000000003d00000024e11416f0b88000001e58000000e400000f800000000000007a8000000000000000a8000000000720000a68a280000003c1ec00000003e8408000001ef8000000002080850000c59d680006808a1dc0000000000000ce00000000000000028a81b95a8929561411650fc8002130001ff8ee1210771a78f500015390280000006100000014502c80000000000000000000026080028e8000000001c380018d8b10001108000002220000000001788000002920000000f180000019b1090000000002438000000000000000001e70000000000769b080012c0000188000bc0000001f5a4780000018900000000000000018303680000000000d0000000aa0a79358000001fca6b07c8000d60a1a4284c00020c9b8
  | 9 => 0x600012980000000000000000029900018e80000016400000000000028d80000029b8002998000000001970000000000000001c18000002541bf8eca729fe26e021a9c07ea9e8bd27c1a207b00000000000013b80000580000000000011c80000005a80004da739b20d10b180010b83700000024107a0001d408880000005a0001638e680017700013180022500000000000000000000023f0000bc80000011ea469c100025b0c70eb80023d00004f14411522a00016f8001c09f480000000000000017b8000000002808000511041ad8438b517b1bf0000000000dd25d9e800000000000000012e26c0000001df80000023888580018400000000000023691b8000001508d80cd030120a7b80000013a22c0000001a91499db80016c1e7800037a9c90300019d22380026b80000000022800000000000020297381100028e18ca7919e83380025f0000000000000000000001c300000000012a06e80008b828933a278640000ee8000000c40000000000d69b18000aa92b90da5680017d80000000010e8570998000000000032071ba00014700000000000000021d8100000000000000000000000000000001910000000000688ba23c00006d8001ae8000418000588000000000000000001328f600000022ea2f0001a880000022a9fd9b79139da9678568001cd80024f0000001468b282e00024800015b0e70fe1eb00d90f1d31590941069f009b92aa3408017aa5583409080714fa668650252441098e881ea500e48b801c9e31161d601a1578000000000001d900011180000018f80000027480010208d9e680912f0c99929408000fa0000000ac22300018e00018502b0d288b13f8002118001cb80000000000000006181599a979a259d18000002770000000000000ed80023b0000000dd80000029b000205065a0381f80000000022b80000000000025709822d80c00004ca888920000d89de8000000000000a38db800277a938cc1b8a069c614c0000000002320000002098001a29880001c00000000001180000000000000000000001b506680000000022d0e380007280003b0ca00000000021380000024480000027886ba59800000000000222a088d712e96a11f9849248631f50752520000821951f70000001900001271d48060000000000950002000e785b0001d2800000207a200000000000e59d08080000000000b3a058000001379a680000000005300029f0000001050a5a5a80000008fa6d80000000000000020e00023580000000000018b1349281e88000000f280000005080000009e8000000001fb96e17021c1801cf00021200016d8000000002400d000003500012d9e48ff25112ca3180000007a8da0b315298390d00004a86f8002300cf1d880000000013100008e14026f9600000000c00758000990000001c98789a98
  | 10 => 0x2061708000d380024191984f8000000000c29e123480880000000000004b80000000000000002100000000000002aa0b8d48000000001e40fc00000000000000000000007e00026aa0f8000778000000f78cfa3601200018a8000000000000000001398598000000001fa02692fa4c1718001dd00010c000062a0080000024e9218000e60000001589f99ea00018600003aa2187400009d28b0001bd83b8579b915017f23a0830000000000b480000026494d800014000000270000010850210800000258a6ca15a519bb1768002851a080000017c02b8001570239f1182a4a8000001ea80000016080003a0000001c580000011c07d8000001438000259f885386997e0389e29a303801a84ea7195d9b39120000000000000000f0a7e8000001d80448001af9ed8001431d580000016b80024989380000010e2650c800000006e0002828470fb80000000000000000000000017d00001389da1b8a100029714e1ca9d018a11a2308fd8000001420001be14480023da148000001f69a000000021e071000000233060a3e1ef0000000ec0000000000de00021ea261610c489324080026800027985490a800155a761cf8000001bc22100000000006c0000000001740000000d30828002978b41ec8002618000000000000069200000000000000ea0002610002129980bf80000000000000000000029585e8eb0a916880000000003913606a1268001622248198dc81c1cc05800000015e0001aa8000000000000000e080027d0001258178000001f90b90038001a10a72030d58f7156a208a99279458000a011d00000000004310387d2818000000000000001ca0000be8000a080015a00014f0708002041959088ca80006c8000fd00000005d26284580000015c80029899c09b16981d089000194a32a29a9e000201a710bb8000000001f8282000091a3ea83172a8fa6783e0130000001de0000000000001ee8bda2900000000020b0d194622711926
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0xc0400020000b896c4c8540020521832721e2c68bc00dc0000300a80144a8c069ad274d8343a1a844e2e00b4000036beacce426a48c66e60cad0da7ac07000aac25e5c780038120010d66658006400000000000098decc762200009e240e00a2006c8ea8a000407c8892089490009c00ae6200d4a4ba3e0000444c7e56462ab2003c5a500000a60082000000280000000026001c868a16b0b6000003010000010902000001000101000504001102010104000e07020500100300010100020f01a1ee4a1aa421d187050e5010f0aa9ac229e858558d5114742a28e2a98a6a15187054c5350a8a39aa228a854c1c15114542a2ae22a287996155458454ccb0ab22a228e65451c55410d32a30e0aa0869951471550544ca8c382a82a265451d15114532aa0e0a88a29951870508504cb0a298c2a12838554d61d0841a1ae529a8420c58705953210686b90a8a1e63469c35410e31c28a830a6498c3870595420c70aaa2c399063435ca544c831838ecaa26218f09424c95008790a1242a8043d04c92154021a1ae529a85a061463945419028b38ea729c81459cf5194640c92a43026420615635444110306a9ac4298818554d6114c40930e0b1ca420629521813210384a96c09908183548604c840e12a4302642068a52181321030ca90c099081a2548604c840c12a4302642049a70d8d511030ab1aa22888189589511444085ae432a62204987058f2110306b1aa590881435ca544cb30a2ce3aa0871861464945318c28b38ea92a461459d35194630a1ae42a2861851571151430c314a90c0a106185591510c430c1aa8b10a81861554584540c24c382c929061925486050830e12a5b02841860d52181420c384a90c0a1061a29486050830c32a4302841868952181420c304a90c0a1061269c36454430c2ac8a88a21864562544510c226b90caa0861261c164c8430c1ac8a96421860d62548400c30c298c0a144186150604ca20c1ea6b10811060f54588308830c298c0a1241431d5424c920c18caa12649058870509324830c2a0c099241a2508604c920a60e0a10a290705424c851482a83826428a418354d6210020c4ac4a88801060d545883008322b12a218041465d4400c020c32ca2006010589721003008344b108018041c4544400c020a1ae529a858861a5318142c4286b94a89962186950604cb10e10a420060885627588620443503108088021b01883044010
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x240329c0810020010c010a088058d52c8440a088059152c8430b00805093214520d01421c13214520c09655c8400c020c0975588400c020d0172544400c020e0162544400c020a098294c6050b10a0982950604cb10
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 48
  | 5 => 1017
  | 4 => 1345
  | 3 => 112
  | 2 => 10
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s4K7 (i*5) 5
  | 6 => packedAt s4K6 (i*16) 16
  | 5 => packedAt s4K5 (i*27) 27
  | 4 => packedAt s4K4 (i*38) 38
  | 3 => packedAt s4K3 (i*49) 49
  | 2 => packedAt s4K2 (i*60) 60
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s4K7 (6+((h/1+packedAt s4K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s4K6 (880+((h/16+packedAt s4K6 (768+(h % 16)*7) 7) % 90)*7) 7
  | 5 => packedAt s4K5 (31188+((h/339+packedAt s4K5 (27459+(h % 339)*11) 11) % 1477)*11) 11
  | 4 => packedAt s4K4 (56486+((h/448+packedAt s4K4 (51110+(h % 448)*12) 12) % 2598)*12) 12
  | 3 => packedAt s4K3 (5784+((h/37+packedAt s4K3 (5488+(h % 37)*8) 8) % 162)*8) 8
  | 2 => packedAt s4K2 (612+((h/3+packedAt s4K2 (600+(h % 3)*4) 4) % 15)*5) 5
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xffff81ffff83f07ffff83ffc1ffc0fcf9f3f3
  | 1 => 0xf03fffe07fffc3f83f07fc3ffe1fff03467cfc
  | 2 => 0xffc1ffff83ffffffc007ffc3ffe1ffff878f1f
  | 3 => 0x1fffffc0003fffff80003fffe0003f80fe0
  | 5 => 0xfffe0000000003fffffffffc00000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x218408c5109040014b098044c022425818b171
  | 1 => 0x64889143212205281542a429521496094254b4
  | 2 => 0x821122080a44225280844a82254128a2850a0a
  | 3 => 0xcb2dc4924876ab9ce6d06223b9980c33e80fc0
  | 5 => 0xc31871c738733e738e77330311030c3f7e000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xeae8eae8e8e0e8e0eae8eae8e8e0e8e0eae8eae8e8e0e8e0eae8eae8e8e0e8e0eae8eae8e8e0e8e0eae8eae8e8e0e8e0eae8eae8e8e0e8e0eae8eae8e8e0e8e0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_16333
namespace PEqualNP.Outside.L_meta_16333
open PEqualNP.Outside.L_meta_16333.Model
def s5K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K6 : Nat → Nat
  | 0 => 0x400615093874a0000a1286000502f58009000008f8c1e7919b2c3869744985992a1d200522000a00008ae5a9d085064d590340405c03433430010040c9080ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32df32fe32fd32dd32fc32ff41fe41be41fd41fc41bc41ff31fe31de31fd31fc31dc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x4617c548c2faa71877d0e30ee21c617e528c2faa5186fd0a30dea1461df328c3ba65185f94630bea8c61be418c3788318778c630ee18c617e508c3be61187ecc230bfaa261bf544c27ea8985f95130beaa2617c544c378a8984f15130ef21a61dd434c2fea4985f14930dfa1261bd424c3be6498774c930bfa8a617c514c37c82986f10530ef18a61dc314c3f66098778c130bfaa0617e540c37ca8184f95030beaa061bd540c27aa8185f15030bf29861df430c3b886185f94830bea9061bf420c37a841877cc830ee990617e510c2faa2186f90430de20861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c83bca7905794f20bea9e41dd53c82baa7905f14f20dfa1641bd42c83be6590774cb20bf28e417d51c837c83906f10720ef18e41dc31c82fea9105f95220beaa4417c54882fea7105f94e20bea9c417c53882faa5106fd0a20dea1441df32883ba65105f94620bea8c41be41883788310778c620ee18c41ee21883d843105f94220f790441fb20882fea8905f95120beaa2417c54482fea6905f94d20bea9a417c534837e84906f50920ef99241dd32482fea2905f14520df20a41bc41483bc6290770c520fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53082fca4106fd0820dea1041df32083ba64105f94420fb288417651082faa2107d54420baa8841be41083788210778c420ee18841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10dfa1621bd42c43be6588774cb10df20e21bc41c43bc6388770c710fb10e21f521c43f641887e08310bfaa4217e548437ca9084f95210beaa421bd548427aa9085f15210bfa9c217e53843bca7085794e10bea9c21dd53842baa7085f14e10bfa94217e52842faa5085f14a10dfa1421bd42843be6508774ca10bea8c21be41843788308778c610ee18c217e50843f441087e48210fb88421fb10842fea8886fd51109faa2217e54442faa8885f15110de2a2213c54442fea68877d4d10afa9a217e53442faa6885f14d10ee29a215c53442fea4887bd4910b7a92217e52442faa4885f14910f6292216c524437e84886f50910ef99221dd324437c82886f10510ef18a21dc31443ec42887d48510fd10221f920443f620887d84110bfaa0217e54042faa8085f15010bfa98217e53042faa6085f14c10bfa90217e52042faa4085f14810dfa1021bd42043be6408774c810bf28821be41043788208778c410ee188217e50043f640087e08010fb88021fa10043ea20087e44010
  | 1 => 0xc508c6fea898efd51319faa2637e544c6faa898df15131de2a2633c544c6fea498df14931dfa1263bd424c7be6498f74c931df20a63bc414c7ee6298f78c531bfa82637c504c6fea818df95031beaa0637c540c6fca618f7d0c31ef21863dd430c7b88618df94831bea9063bf420c77a8418f7cc831ef19063dd320c7b86418df94431df20863bc410c7be6218fd8c431ee98863f5310c6fca018df54031efaa063de540c7baa818f715031efa9063de520c7baa418d754831ee29063df420c73e8418f790831eea10639d420c7b88418f794431af28863d6510c7be8218f790431cf20863dd410c7b88218e710431efa8063de500c7baa018f714031bfaa6437e54c877ca990cf95321beaa643bd54c867aa990df15321bfa9e437e53c87bca790d794f21bea9e43dd53c86baa790df14f21dfa1643bd42c87be6590f74cb21df20e43bc41c87bc6390f70c721bf286437d50c86fea910efd52219faa4437e54886faa910df15221de2a4433c54886fea710f7d4e21afa9c437e53886faa710df14e21ee29c435c53886faa510efd0a21dea1443df32887ba6510df94621df20c43bc41887bc6310f70c621f790c43f721886fca110df54221bfaa243bf544867ea890df95121beaa2437c5448778a890cf15121bfa9a43df53486bea690df94d21bea9a437c53487b8a690d714d21dfa1243bd42487be6490f74c921df20a43bc41487bc6290f70c521fb90a43ee21486fea090fed4121bda82437c50487f0a090de14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53087bca610d794c21bea9843dd53086baa610df14c21bf29043bf420877a8410f7cc821ee990437e510877c8210ef10421ef18843dc31087de4210fd88421f690843f521086fca010fe94021bd280437d50087f2a010de54021bf29e817d53d037e87a06f50f40bf296817d52d037e85a06f50b40ef99681dd32d02fca3a05f54740df20e81bc41d03bc63a0770c740beaa4817e53902faa7206f90e40de21c817e52902faa5206fd0a40dea1481df32903ba65205f94640bea8c81be41903788320778c640ee18c817e509037e81207ed0240bfa9a81df53502bea6a05f14d40ee29a815c535037e86a06f50d40bfa92817c525037e84a06f50940ef99281dd32502fea2a05f14540df20a81bc41503bc62a0770c540fda0281be40502fca8205f94c40ef298815e53102faa6207754c40aea9881be431037886205f94840bea9081bf421037a842077cc840ee990817e51102faa2206f90440de20881de31103b862205f94040dfa0081fa401037a80207e50040bfaa6617e54cc2faa9985f15330ef21e61dd43cc2fca5985f54b30dfa1661bd42cc3be6598774cb30bf28e617d51cc37c83986f10730ef18e61dc31cc2fea9185f95230beaa
  | 2 => 0xafaa6217754c42aea98857e5210b7e84217b90842dea1085ed4210afca2215f54442bf280857d5010afea9995f95332beaa6657c54ccbbe87997790f32eea1e65dc43ccb7e85996f50b32bf28e657d51ccafca1995f54332efaa665de54ccbbaa9997715332efa16659f42ccbbc85997750b32cea1665dc42ccbbea3997794732af28e65dd51ccbb8a39977d4332ef28665dd50ccbb8a1995fd5232bf2a465be548ca7ca9195f55232deaa4653d548caf8a9195f54e32aea9c657e528cb7e85196f50a32ef99465ef328cafca3195f54632bf284657d508cafea8995f95132beaa2657c544cbbe86997790d32eea1a65dc434cb7e84996f50932f799265de324cafea2995f14532bfa82657c504cbbea8997795132eeaa265dc544cbbea49973d4932efa12659f424cbbc84997750932cea1265dc424cbbea2997794532eea8a65dc514cab8a29977d4132ef28265dd504cbb8a0995fd5032bf2a065be540ca7ca8195f55032deaa0653d540caf8a8195f94c32af298657e520cb7e84196f50832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e83de53d06bca7a0df54f41eea9e835d53d06fca5a0df54b41dfa1683bd42d07be65a0f74cb41bf286837d50d06faa920df94e41bea9c83bf439077c8720ef50e41de21c837e52906faa520efd0a41df21483bd42907788520f7cca41ee994837e519077e8320fdd0641bf284837d509077ea720ef94e41dea9c83bc539077ea520ef94a41dea94833d5290778a520efcca41cf99483be329077a6520e74ca41de194833e519077ea120ef94241dea8483bc50906fea6a0f7d4d41afa9a837c53507b8a6a0d714d41bfa92837c525077e84a0ef50941ef99283dd32507ee82a0ef90541bfa82837c50506fca820df94c41bea9883bf431077c8620ef50c41de218837e52106faa420efd0841df21083bd42107788420f7cc841ee990837e511077e8220fd90441dea0883f541106fca020df54041dfa9883be531077aa620ef14c41dfa9083be521077aa420cf54841de29083bf321073e6420ef8c841de990839d32107786420ef944419f28883b6511077ea020ef94041dea8083bc50106fea998df95331df2a6633e54cc6faa998ef553319eaa6637c54cc6fca598df54b31dfa1663bd42cc7be6598f74cb31df20e63bc41cc6fca198df54331bfaa4637e548c6faa918df15231bea9c63df438c7bc8718f750e31ee21c637e528c6faa518efd0a31dea1463df328c7bc6518f74ca31ee194637e518c77c8318ef10631ef98c63f7318c6fca118df54231efaa463de548c7baa918f715231efa9463de528c7baa518d754a31ee29463df428c73e8518f790a31eea14639d428c7b88518d794631efa0c63de418c73c8318f750631ee20c639c418c7bea118f794231eea8463d
  | 3 => 0xb4001861320e8002f0000e54bb00000074c00310000924cabc42c2001eb8006540015b80052e000000e7000000f68df0e00011b39c680f70dc2ec1342f4312044fe26d748000b6d5c000000000000014e172c25bdaa00000000000000090093800000d1964b03088971fa8511f489c122b80000000039b00041d833d30300100ea0a722001928007e086c63b0500000000000558b185a2660000000014f000000000002d4000002af4d4f380000000000000000000255bc00030e2b00034b1da000000006de000000008000000040000600c008018010020040100000000001800000000018050000000100000000000000002000038020000000280000400000800000008000000060000000100000000807002000010000000040380000200001807004000000010040100080300001400000002008000000000040080000a00400001000000008050060000000000a00c000000000040100400000400002000004000080040000080100000801001004004028000000000000100003c01800000000000000000040100000200800000002008000010000000400300c000018000000000100200c008020000000000000100000000804000008000020040000000000c00000800000000000000180000000b0040000000000e0080080100a008000010080040000c01200001000000000020000040040280000201000008000014030010020000080301002400000004000000040020080080000200800000004000008000040040000000403800003002000010020020000100400000400001008004020010000000000000400005001008000028000000080000100000403802000028000000000100280400400c0400400200001001002004000010040000200200400c000000320000000100001400002004004005f94b43bea96877e51d0efaa3a1df94343bea86877d5490efca721efd0e43efa1c877e5290efaa521df94643bea8c877e5090efaa121f7d0d43df21a877f5250ef8a4a1dfd4543be28a877f5050ef8a0a1df95043bf29887bf4310fbc8621ef50c43eea18879d4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f90f42dea1e85bc43d0afca3a15f54742bf286857d50d0b7ea7a16f94f42dea9e85bc53d0b7ea3a16f947429f28e85bd51d0b78a3a16fd4342df28685bd50d0b78a1a15f552429eaa4857e5390bbca7215794e42bea9c85dd5390abaa7215f94a42dfa1485ef4290afca3215f54642bf284857d5090afea6a15f14d42dfa1a85be4350b7a86a16f10d42f7a1285be4250afea2a15f14542bfa82857c5050b7ea6a16f94d42dea9a85bc5350b7ea4a16bd4942dfa8a85be5150b7aa2a16f145429e28a85bf5050b7ca0a16f54142de282857e5410a7ca8215f94c42ef298855e531
  | 4 => 0xe000570000000f80000000000000000000b445b23839a51ca1916302aa84e09827800046a54000000d3012628000d50001f20010b0007f088d9e8000002900023c0000000038c546940610753b6c10002a20000000000000000000000000b300000057675c061b06f82411aab240e000000000000000000000000013b30318000000004d26d8e41563fa6ed7f1ae00000000253000589a997250032c9880000000000380000001e90000000000000f00000000000000000b6aa93ca1d83480021400000000000001180001e0bd0e58000007393400070c0000000000000068800000001b2a06508001209083266a4000003ecdf98b8006860000001f0007a0000000560000000000000000000000000000000000015400000000800000000c30003dd324d680000011e524001ab768000002d753800117800000c0800000000a6533a886b062d678000000000000000000129000000000001d0000000000bf0164d0000002f600000000000770072771f0000003d625e00074a2a78e7a8000000000001e800000000002b946e728aa0005e40000000017c0000000000000020079644a6c002830008950d1bd0009b87006326e00000000000000003013ce801993c60006a021a3204ab5800052000eb4000005860f0000007940000016000073d5a000000b3475bf25cc000000002b2570360000005b9b12ad732000d788e7128e5d3a030006e8003500000012527113a01547b45000000008e216ec851a0e56ba0000000000000090251000418002d83320000006f3aa0000000000008000000284000068000000008a20e4908fc54800000c9c00000000e48000004380002c00000044ce4936444000000004d600010b2f6103340000068e000001d95040000007e2c82940008c000329fb3ec00000000049000670000003cc0000000041e109f9979264000000004f6a15f2bbe720154dbace0007e98c000000c2de7b87000045013b0000000000001d8e2c00323238001a213f2545d5d2941160000001c00000006e800000ed4003373de0000000000000037000566000000000005bc000000002212b8005b20000000000087db91a500005516a31778bf4002240708304b38f640369160c5000000000000000000000050e00000000000000000000000000008679a0cc4f8003082c800130000914a21d224a00000000000e84810006e0440003bd5623180014a0000003c2050000000024f0003f877800614ea400000000000000001a0da8cf000000000050af06019400094000804000002d6bcc00128758000fa8007dc3dd9a388340d800011538ece4000001542d5ec9187cc9f4eb3070bedddb48006fe1b4e6000000000fc0000001fdf880000011c000000000014a2ca000000f18002ee9b5322a1000ee9ce8000006299c3793b00005680030af
  | 5 => 0x66a0000000000000000000000000000000006fc001b10000013b0cc05400146800000438000001b6001cd00027c0000300000005db38007400015b2e800052000265578bad86bb35f40000008214e000000162520000000000000000000000001b73b8336000000000009bc002d31dc958002790e6000001a2142001499d1000001ca0cf422c394c11100000000000000000fa13a0005cdf496710e065af1be208fdded00072600196a180000000000038420d268001d051531a8e000c6c1f84c358001a8800000001700000005f4fb800000000afbae424e0c00233514e5939000000a9dcc0000000004f0000006240000000e8208682e000000002ff42e001629fe58213dd30004f4001b980034234c0011d388478c01b30009d0002ab5f0dac00000122000000001260011006a000000001194b4bb80014c0f82f000376000001c28000a67809e87200000000000000000000000000007f800000bd80028954800000000000001e093900008c000000006c972000000000003117aa000003977c0a18080000000000015d000001408a2000000000005a00000002d00004c000005decf879800000000000000000008b800000000000d40a0b215e8005180000019a09c05000363000a40000000001700027e0005fce080000042d2d8806da001a91df42afd0f58001ec58d5f800000000971940000000000000035c81800000001ef80000000000000000b8c0004b000d2400000000384003cc698000788e40006380000033a3c8000000000000031e588ca40000006e0000000000000000000000000849b4694884fe00000000000000192000003d15da000001400768e9f38000646456f0000620002f0001820015301c000000002e13d85f000068000000000000000000000000000054183000000003480000008d00024213400026248b6d9e17e0000011f0f57d00bcd1bb9000b2c620000000009a8001ac000ed1f2190d0800000000001f5000000001a780000000105800000f4000000674001958000005d0148dc31a18531000202f08002c2108f24b800055c000530006b825c0000043a908003550000000034142000000000000001d58000000012626100011400292320000002fb1b2001488005b4000002b00000200000000022400000000000002a562a0003e8004e6b9c000000000000035938a000000003c8000000003e00000005a0008f5941fb4528b80029d64830c00153000e09132dc2bc0007e0001e8000003743c2fadf1b845c43f4000d50005c45c12c754001a731a29a001988000000a00001a69a001b32c700015c000000007b800000162000000005161dc002c071a001aa00000000000000000f780000000000000046000000000003721d0a584a23e000453b700069cf8b7d000d7c00259000000f48362f41500000031
  | 6 => 0xcb8000000000012c0ce00000106bc5000000001b52a400000356000c5899a963feec97c8000000000015a2ae3a8000000008240000035a000003af5ca000c12197b60000000000000189ab50000000033643c1ac968410005b1690000002e891bcb3f2b7c82a44000e04003b6000001cf12614006cc42ea57c1ec003bb61e56cac1c36c897d9da283baf20b3000000000000007de5196aa6c146000388000b2000de21475000001bc0000000003c3632348000000000000011b0cc2cc0036c0002ec001961f6000801de000000558002d20001a9517c2c01d12f5000000f9800180f900010c486e398eb3f64c9c02b24b044000d200052a000338000000001c800000000000005e2a69d1af732ed859980048e8edd23d4000594000000000000012b6eaf882ea780000d087800000000ea085000001df800000e280000000019000000102918000000009d400000000bf14f938090b515d31f4bc938000007621e915add2f0000000006d0000003716b69740000965800000000624de8000000000000f000224e7dec00011600000168000000aa9c6426000492602760000002c4aa0000000033ec70000600003793e0d8000540000e3000000731220000014f00000078800198
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x121c42f16108310f888420c425e63d52109758f548423d62952108fd89548425e63152109758c548423e64d4e108f593538431e5494e10c7552538425d6294e10c7951538431d5454e1097d89538423e6414e108f590538423e64d4a108f593528425e63d4a109758f528423e6494a108f592528425e6394a109758e528423e6414a108f590528425e6314a109758c528423f65d0a108f597428431e53d0a10c754f428423f6550a108f595428431e5350a10c754d42842b46150a1097d97328425d65cca10c7953328431d54cca1097d95328425d654ca10c7951328431d544ca10b5185328431e5390610c754e418431e5310610c754c418431e548c610c7552318431e540c610c7550318423d62d51108f992544425e63951109758e544426e62951109b58a544425f63551109718d544426f62551109b189544423e65151108f588544423e61151108f184544431f54d4d10c7153534425d62d4d108f992534423d6494d109798e534426e6294d109b58a534423f6454d108f191534426f6254d109b189534425e6514d10c7d50534431c5414d1097588534425e6114d1097184534432f54d4910cb153524434f53d4910d314f524432f64d4910cb193524434f63d4910d318f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109ed81524423e64149108f590524425e63149109758c524426e6514910cbd50524432c5414910d3d4c524434c5314910cb990524432d6414910d398c524434d6314910d9584524436960149108f997424423c65d0910c7d4f424431c53d0910cbd4b424432c52d09108f995424423c6550910c7d4d424431c5350910cbd49424432c525091097997324425c65cc910c7d53324431c54cc910d3d4b324434c52cc91097995324425c654c910c7d51324431c544c910d3d49324434c524c9108f996414431f5390510c714e414432f5290510cb14a414423e6510510c7d4c414431c5310510cbd48414432c521051097996314431f548c510c7152314434f528c510d314a314425e650c510c7d50314431c540c510d3d48314434c520c510e5104314436452885109d195214427a6588110da14a20443e221881109e19520443685248110da14b104425f63550109718d540425e63150109758c540426e62150109b588540423f6454c108f191530423e6414c108f590530426e6214c109b588530423e64948108f592520425e63948109758e520423e64148108f590520425e63148109758c520427661148109e980520432e5250810cb54942042b46150810d3949320434d524c810b5185320423e64940108f592500425e63940109758e500427965c80109e59420042f161080109e596100427765440109ed9510042e86244010ec10510043d03144010
  | 1 => 0xc356510c430b6580310c31d54cc03097d95300c29c644c030c7551300c27b654c0309798f54c825d63d53208f98654c823c61553209798c54c825d63153208f99353c823d64d4f20c795253c831d5494f209798653c831e5454f20c755153c825c6154f208f99053c823d6414f20c794f42c831d53d0b20c794d42c831d5350b20c795332c831d54ccb20c795132c831d544cb208fd9151c823c645472097d8d51c825c63547208fd9641c823d6590720c794e41c831d53907208fd9441c823d6510720c794c41c831d5310720ab58841c825f658c7209759631c831e548c720c755231c825f650c7209759431c831e540c720c755031c82cd620c72097d8d548825c63552209798c548825d63152208fd91538823c6454e208f990538823d6414e20e3509328823f64546208f191518825f63546209718d51882e9600862097d8d544825c63551209dd85544827461551209798c544825d63151208fd91534823c6454d209dd8553482746154d208f990534823d6414d208f993514823d64d45209798f514825d63d4520ab58841483375110520cd14441482cd620c520d5d443148354510c5209798f540825d63d50209d987540827561d50208f596540823e61950208fd89540823d62550208f185540823e64150209798c540825d63150209d984540827561150208f993530823d64d4c209d987530827561d4c2097596530831e5494c20c7552530825e6194c20c7951530831d5454c2097d89530825d6254c2097185530823e6414c208f590530825e6314c209d98453082756114c208f992520823d64948209798e520825d63948208f597420831e53d0820c754f420823f6550820c794d420831d535082097597320831e54cc820c7553320825f654c820c7951320831d544c820e350932083365494420cd55251083565394420d554e51083376494420cd19251083576394420d518e51083374294420cd50a51083573294420d54ca510823f64544208f191510825f63544209718d51083365454420cd55151083565354420d554d51083376454420cd19151083576354420d518d51083374254420cd50951083573254420d54c9510837060544208fd96410823d6590420c794e410831d5390420cd946410833551904208fd94410823d6510420c794c410831d5310420cd9444108335511042097d96310825d658c420c7952310831d548c420d59463108355518c42097d94310825d650c420c7950310831d540c420d59443108355510c420d9546210837151880209bd95200827b6548020ea50920083c93248020dc545200825e63d53109758f54c425e63953109758e54c423e64d4f108f59353c423e6494f108f59253c423e6494b108f59252c425e6394b109758e52c423e6414b108f59052c425e6314b109758c52c4394410c710bc18
  | 2 => 0x658c421c7952310871d548c421b358a310865f650c42197594310871e540c421c755031086cd620c421e5104310866f6548421ba18121086776548421ce95250087395494021d694e50087595394021ced0a50087394294021d6cca50087593294021ce90650087384194021d68c650087583194021ce95150087395454021d694d50087595354021ced0950087394254021d6cc950087593254021ce90550087384154021d68c550087583154021dc885500877121540219798e52d025d6394b40cb54b42d034e524cb40d354932d025f63547409718d51d033651107409798e529025d6394a40cb549429025f63546409718d51903365190640d59443190355510c6409758b535025e61d4d4097588535025e6114d408f997435031c53d0d40c714d435025e63149409758c525031f53d0940c714f425031f5350940c714d425032f5250940ae181425025e65cc94097197325025e654c94097195325025e63d45409758f515031f5390540c714e41503345190540ae982415031f5310540c714c415025e658c54097196315025e650c54097194315031c53901409758a531025e6194c4097d89531025c6154c408f596431031d5390c40c754c431025e63948409758e521031e53d0840c754f421032d52d0840ae583421031e5350840c754d421025f65cc84097597321025f654c84097595321025f63544409718d511031e5390440c754e411031e5310440c754c41103365110440ae580411025f658c44097596311025f650c44097594311031d53d00408fd95401029c6350040c754d401027b65500409b98854cc26d6215330c715143cc23e6494b308f59252cc32e5250b30cb54942cc34d52ccb308fd9151cc23c6454730d594431cc27661d52309d587548c31f5410e308f992528c23d6494a30d3549328c23f64546308f191518c3365110630cd544418c356518c6308f58b544c23e61d51308f992544c25f63551308f994544c31d63151308f588544c23e611513097996434c31c5490d3097195434c31c5450d308f990524c23d64149308f997424c23c65d09308f995424c23c6550930c7d53324c31c54cc930c7d51324c31c544c930d3d49324c2d8604c9308f993514c23d64d45308f996414c23c65905308f994414c23c6510530c7d52314c31c548c530d5146314c2da608c530c7d50314c31c540c530c7152304c23d65950308f58a540c23e6195030c718d540c23f62550308f185540c23e64150309798c540c25d65d0c30c7553430c25d6510c30c7550430c23e64948308f592520c23f65d08308f597420c23f65508308f595420c31e54cc830c7553320c34d52cc830b6583320c31e544c830c7551320c23f64544308f191510c23f65904308f596410c23f65104308f594410c31e548c430c7552310c31e540c430c7550310
  | 3 => 0x31a7590500c6ce6214031b3588500c75950140319798f54c865d63d53219798c54c865d63153218f99353c863d64d4f21c795253c871d5494f21c795153c871d5454f218f99053c863d6414f21c794f42c871d53d0b21c794d42c871d5350b21c795332c871d54ccb21c795132c871d544cb21e350932c871e5390721c754e41c871e5310721c754c41c871e548c721c755231c871e540c721c755031c8794410c721cb58b548873661d52219798e548865d639522197d8d548865c6355221cb58854887366115221c7d53538871c54d4e21d358b538875661d4e218f992538863d6494e218fd91538863c6454e21c7d50538871c5414e21d358853887566114e21c7d4f428871c53d0a21ad987428871f5350a21c714d42886b46150a21c7d53328871c54cca21b5987328871f544ca21c715132886d4614ca21c7d4e418871c5390621ab58a418871f5310621c714c41886ad6210621c7d52318871c548c621b358a318871f540c621c715031886cd620c6218f992508863d64942219798e508865d63942218fd91508863c645422197d8d508865c63542218f992544865e63951219758e544867a60951219e582544865f63551219718d544867b60551219e181544863e6515121c7d53534871c54d4d218f992534863d6494d219798e534867a6094d219e582534863f6454d218f191534867b6054d219e181534865e6514d21c7d50534871c5414d218f997424871f53d0921c714f42486b661d09218f195424871f5350921c714d42486b4615092197997324871f54cc921c715332486d661cc92197195324871f544c921c7151324878d424c921b5185324863e6590521c7d4e414871c53905218f994414871f5310521c714c414865e658c521c7d52314871c548c52197994314871f540c521c7150314873b54d4121ce153504875b53d4121d614f504873b42d4121ce50b504875b32d4121d64cb504873a41d4121ce107504875a31d4121d60c7504873b5414121ce150504875b5314121d614c504873b4214121ce508504875b3214121d64c8504873a4114121ce104504875a3114121d60c4504876a21141219798f540865d63d50219e983540867960d50218f596540863e64150219798c540865d63150219e980540867960150218f993530863d64d4c219e983530867960d4c2197596530871e5494c21c7552530871e5454c21c7551530863e6414c218f590530865e6314c219e98053086796014c218f992520863d64948219798e520865d63948218f597420871e53d0821c754f420863f6550821c794d420871d535082197597320871e54cc821c7553320865f654c821c7951320871d544c8218fd96410863d6590421c794e410871d5390421ab58a410863f65104218f594410871e5310421c754c41086ad621042197d96310865d
  | 4 => 0x754c53106ae6214c41ab58853106b66114c41ae98053106b96014c41ad987521069e6394841a758e521069e6314841a758c52106b66114841ae98052106b96014841c754b321069e61cc8418f996321063d658c841a758e321072d528c841cb54932106b7614c841ad185321078f624c841e3949321071d524c841e3549321070d524c841e5d85321069c614c841e51853210694614c8418f994321063d650c841a798c321071f3294441c74ca51107366194441e5cca51107953294441a7d8d501069c6354041a798c501069d6314041ab98850106ad6214041ce540501063d62953318fd8954cc63e6494b318f59252cc63f65d0b318f59742cc63f6550b318f59542cc6b46150b31c795332cc71d54ccb31d354b32cc71e544cb31c755132cc67a60d52319e583548c71e5450e31c7d50438c63e6494a318f592528c69e648ca31a7592328c74d524ca31a7990328c69d640ca31a7993318c69d64cc6318f992508c63d6494231b5987548c6da60d5231b6583548c71f5495231b5984548c6d661d4a31a7992528c69d6494a31a7990528c69d6414a31b5984528c6da6014a31b6580528c71d52d0a31a7987428c65e6590a3197596428c78f6250a31c7549428c69c6150a3197994428c65d6510a31a758a418c71d5290631a7588418c71d5210631e5984418c69e64d4231a7593508c69e6494231a7592508c75b50942318f58b544c63e64951319758e544c65f63551318f994544c63d62151318f990524c63d64149318f997424c63c65d09318f995424c63c655093197997324c71f54cc931c7153324c71f544c931c7151324c74f524c9318f996414c63e6510531c7d52314c71c548c5319b988540c66d62150319e980540c67960150318f992530c63d6494c3197596430c71c5450c3197594430c71d5410c318f992520c63d6494831cb949420c72d5250831ad185420c74d52cc83197596320c69e648c831a7592320c69e640c831a7590320c69e64cc431a7593310c65f654c431a7d91310c69c644c4319dd95310c63f64540318f191500c6d661d5031c7550540c6ce6215031b3588540c6d66115031b6980540c6d96015031b5987520c69e6494831a7592520c69e6414831a7590520c6d66114831b6980520c6d96014831c754b420c69e61d083197996420c65d6590831a7592420c74d5290831d3549420c6d76150831b5185420c78f6250831e3949420c71d5250831e3549420c70d5250831e5d85420c69c6150831e5185420c694615083197994420c65d6510831a7990420c71f4294431c750a510c7566194431e5d0a510c795429443197597410c69d6290431c754a410c69e6190431c7946410c796519043197d95410c69d6210431c7548410c69e6110431e5984410c71e5110431e5944410c69f6454031a7191500c69e6414
  | 5 => 0x5350a9e63d4542a758f5150a9f6354542a718d5150abb6054542ae1815150a9f6354142a718d5050ab76154142ad1855050a9e6314142a758c5050b395014142979865310a5c6154c42c794f4210b1d53d08428fd954210b1e5350842c754d4210a6f6550842cb9514210a5f63544429718d5110a7a60153329e58054ccb1c5450f32c755043cca3f64547328f19151cca3f64543328f19150ccacd62d5332c755054ccacd6215332b698054ccad96015332a798742ccb8f6250b32a718542cca9e64d4732a759351ccada60d4732b658351ccb1f4294732c750a51cca9f6454732a719151cca9f6454332a719150cca9e6414332a759050ccb5950143328f986548ca3c6155232c7953328cb1d54cca328fd91518ca3c64546329dd85544ca7461551329ed81544ca78605513297997434ca5c6550d32c7151434cb1d5410d32a7992324ca9d648c9328f993514ca3d64d45328f990504ca3d6414132b358a544cacf6255132b5d85544cad46155132b6d81544cad86055132c7550544cb8f52d0932a7987424ca5e6590932a7592424cb8f6250932e3d49424ca9c615093297994424ca9e6410932a7993514ca9d64d4532a7d91514ca9c6454532b6d81514cad86054532c7d08514cb1d4214532a7d91504ca9c6454132b5d85504cad46154132a7990504ca9d6414132d6540504ca5e63d50328f596540ca3e61950328f185540ca3e64150329798c540ca3e64948328f592520ca3d65d0832c794f420ca3f6550832c794d420cb1e54cc832c7553320ca5f654c832c7951320cb1d544c8329bd95320cb4e534c8328fd91510ca3c64544329758a53d065f6254f419798e52d065d6394b41c794f42d071d53d0b41cb54b42d071e5350b41c754d42d065f65ccb419759732d065f654cb419759532d06d4614cb41c794d439065e6394a419758e529069e6390a41a758e429072d5250a41a798c429069d6310a41a798f419069d63d06419798e509065d6394241ad98753906ba60d4e41ae583539071f5394e41ad98453906b661d4a41a798e529069d6394a41a798c529069d6314a41ad98452906ba6014a41ae580529071d52cca41a7987329063e658ca418f596329078f624ca41c7549329069c614ca418f994329063d650ca41a798f509069d63d4241a798e509069d6394241ced42509065d62d4d4197588535065e63149419758c525063e65d0941c7d4f425071c53d0941c7d4d425071c5350941cbd49425065e65cc94197197325065e654c94197195325071f5390541c714e415071d5310c419798e521065d6394841cb54b421063d6590841a798e421069d6390841a798c421069d6310841d3949321074d524c841b5185321069e63d0441a758f411063f6550441a7d8d411069c63504419dd95411065f63540419718d50106b661d4c41c
  | 6 => 0xa39321ba17d00000280025fa0400000980000000027580010803d8000dc80000000000013100000022928d800000000205800079a701d60001ae00000028017c80000012f91b0d71d709c1e88000aaa01a5a2140000101cd8001a59baa5e000000000000000000000000003c00800400000c00000400000003c00000400800001400000000400002001400000000000000400000c00000000400000000400001004c00000000000000800400001401400c00002c00000000800401400000400000000400001c00400c00400800000000800000000000000c01000400000000c00800000000000000801400000800000001800c00000001000800000800000400401400800800000800000800000000c02800800000c00c00400000800401002400401c00000000400000000401c00c00400402800400c00000800000800000000c00402000000400000400800000000c00400000000c00c00802401000400000000000000000000000000000000000001c00000000400400801000000c00001c00400401400c00401000000400000800800000c00000000000401800400400c01400000800000000000400400001000400801000c00800000401800000001003c01000400001800000000401800000800800000000000000400800400400c01000400c00400001001001c00000400000400400000802c00800000000000c00800400000400000400000000001400000800800800000400800800000000000800801400400400802800401400800000c00400000001001000400800400000003801001400000c00000000000c01000000400000400000001000000401c00400800400400000000c00000400000803400000001000800400000001400800800c00c00000400c00000000000000000000000400400003401000002801800800000000000400800800000000800400000002800000400400000000000c00000800c00000001000000000c01000000000801401000800003400400000000400000401000000c01001000000000002800000000003800400000400000000c00400800401001000c03401c0100029d6490c438fd954310e5f6550c43a7d954310f1f6550c43a7d894310e9c6150c43a71814310f1d4354843c750e5110f1d4354043c754c43d0a5f63547429718d51d0a5f63543429718d50d0aad62d4f42c754c53d0aad6214f42ae98053d0ab96014f42a798f51d0a9d63d4742ae98351d0ab960d4742a7d8d51d0a9c6354742a7d8d50d0a9c6354342a798c50d0a9d6314342ce54050d0a5e6194e42971855390b1e53d0a42c754f4290a5f63546429718d5190b1c5350d42a798e4250a9d63909429798f5150a5d63d45429798c5050a5d6314142ab58a5350aaf6254d42add855350ab46154d42aed815350ab86054d42c754c
  | 7 => 0x897139066a49150a4e01b96b0a90d399280024180000b00015119e8000000000e900000008609f0001f20001440001f40000000000000001fc8000000000000000000000000000000001ea8158000b680005e16092d011a6f0000000a600003600000000000023f00000009080f0b4a070cda5412a9989e290781321e0002458f50000000000000000000f900016419ba8980029100005500016019c15807a80019c8000a100000000029900000003b0002650000000000ee11aa8b00000000000000000000000000000023900000027600000011b8000000000000000000001150002050020b980000000000022b8000358002190bb90b8510000000001e003f18c00000010100015f80000026a12726b2262429451f70000a507b1c900015487da8e0dc1d91778e694880000016a89b8001030000000001cb96883200000006d0c99740fc8000688000001429c511207f0001801a920915b8c21228e982724680000000001e8530000000000000001878001b08000000b929800026400000014ea4c269a0380001980019f85f0000eb0000001d309029a80011280000000f9bb0000001938000001c70000000768000c8a33a030000000420f69830002591d429402f8241eea0600014e0ffa0886417180000027c8fda3209ca218001d2097a689bf88b80018c9ea0000000000f480026a9dd80924a8000000cb0000000001ac8000a5a7880002c87294f00013280000000009488d9148001b78001db2828000000000a310f8002869c00000ca8be80000000000000017600000010e80004f8bf16a000016800000222800000000146a0480008d0000000c900010511000000022c91d26480000000006f0450000000000000000a48001dc80027e80000000000017b0931950ba84a9880000fa8000af00000000000000000000a800000000289000218007801a9985897380015c83c0001c2840a8a9411282179840000001f12528000c81c808c8fb9e60000eb8000002358002509790278a994c16f2000000000001b300028f0000000b2a8a00010725993f12081c0d2a1d8000000000001fe80000000006980000000d8002239458000000000eaa420c09c1a8380000000018580001d9f809215b243a350000000001a280000000000000000000000020994a95780000005200027b82480007700028780000000000000000023f80000019826100018980000000000000000008e9fd0e787380d1e10000001e70c3a6ea2d07d2248001c7a850000e400000000012f2130000001b5a2aa009568000478001490221fb0000002978509fa05c8dea7a21180016b80000000000000020f0000000000001418000000d214600000000000000000026918680000019f1a1a4da7416209d9350000000000001c41aa05b18529e08f00000000000013614800000
  | 8 => 0x3700015a00013c8001cf14b8cb9f791688900023e22d8ef9872161538001a7011144a750001d680000020e9292771158d40000a68001330001238000bb0f9a360001500000201308000000000000000938e88000000000000000000000b413f9b500000000000011a26d00021e8000001dd0000000000001bd21b0000001561e68dd9f911403000021a1b687780000000000005aa841da00023402083300007c0000040b590f0000000000000001909ca0000378000000001c080000023a0a40610bd14d90d0000000d98000000d785f8002488002110000001ab80025d0000840000001048bf87ba3100000000880000000002880000011da6c8c10002951b980e0000000e325ea4500002a9be1990ad8000218801bb8412319650f280018f1ff0000000002888000001060000000128e380017d80017e8b08002288000f591606e8000000001a500011e94380000006380028fa3e81d04b9258fc1bc818908800000068000000181a2e80000000021d0001520002961f980013b8000000001180000f89f5a0224785c17a1f68000cc0578671e59aa9848ea0a18810990001a100000c0958070000000000000340250e0a9d0000000000002148000000002909b80000001138000001c592400b9421b10609d48000000000002410002609eba8baa004c8db0000000000000002810000b71f48000eda3c8c7191a1680019d8000001720161e48001a8a2a0000000001750000001f290997003380000024f92e1188000002511cc8df800280a1b8000000000000721288000e18000d88000000001a69d51f380024800029c8001ad000070800000005a921ce0f39ff8899c620d92b9940000d600017c27f97f0000f71301b90000d800000000025880019a81e00000001206c80000000000025200000027b04186780000020f9e5169a7280006c0190ec1788f410c0000000ac9ed00003d0000000761db80000000000000000024480000008399a20c2730148000000000000000ab00011c80000000025580000000000008707593e14a0001d80fb0000000ef00006301f0e200008c164a2300000000000010a81081b17589d00000025b00020690c94d00006496391999118d82c0000001df000000000000000000293a748580000001efa5c2221900a71e316c00003a8001479be93a11300000026703528d0ae2158460ce07000000000000002e8000000000000002568000820000000000000c400027192e96302103e974a1084d89e8968b007e0500000001542739399b40380051e080007502d19e1670001cfa3080000000000007804b00000000000029e88a98b0fd29f8000280000da18e85d8000000b30001fe0928ce80004d00014006b0170ac00021f14323819590428e8d90b183882e10680000000023da430000080000e727909e00025da07
  | 9 => 0x21700000000000000000000004a00c8000ab8000000000f300000000080006b92780000000000008a2470000000000000001a30000000f00000000049368000001218001d78c31968000001f521500000008f8000000001c200000000000000000000000000000015995580018880000013b00000000004c0000ae80011080022093c29d95a8489920000000329380000000ed00000000000000000000000018280000003f8ff17f93722c14c9091211e39c3039a72000000000042a7780000027c16c80013e80000007f8000000002968001d989600000000026796d8ca0000000000000001ce8000e28298000000000000000e80001af0b39b70001960000000001fb8000f180000000000026180000027d9810000000000000000002860000000001b18002798a79eb01380013a82680000023d00000000016f8000000000000000000001f08000000000000001008468001768438629ec0daa7d06900100026b80006a8f799783b8980cf8002188740000818000f09de80020b00000000000000000017e03c8d52579dc0c49c890e10295e8000000000000000238a81972408b200010d8001799ef00000008783a1359c4a331d580015d9f1a1f80000000000000000005e800000000000025a8c80000000000010200000006f80021298a00000017305614f8449528000000af89f8000658c1800000000271000298a499588000000000001268000000528470001171680000000000400000000b81378001ed80000000000000009193d0000001d0a6580007a0001612280002101470000001a82240000000e60000000000000000000d49f610a0540000be00017100000000000020d1fd80315c000000000268199a3000000000000025a9b201a2298001b023aa871530cf23c213a0b9ad8000001e780000000000026c0000e50000d59d00000000000002200000000001860000000000000001190000000001838000000390001d1a4c80000000000000000029a059000239a9f0aa0000000000000000000000000000001fc0000000000e480000000010180026217800020e0c600000022717a8de04f0000f60000001d1043000140903a6f9ab2210000000000000000001cd00015e0000000b780000007919d00004412625c8001f000025b800045a5f22f91c0368bc00000000000000000000007e9200fea6280021c00005a0000002278000bc80000021c8c780006d8c29d3a3287883e0bd97b8000000000000001678001341a48b6266a258000000001119f300000023b8000000000d19591f880000000028206200027a8060000a000000000027680000027e1a20000000000000000000d0294922133a519178178c0162a1a8000002548fa1df98f8e10000000950001000000d11b481c85b8000001de05181aa8588e1a39808000000000
  | 10 => 0x498000000000000000000000000000001e90b10002080000000000000001b88ee80000018d0002368000000000000889ca8ba19b1551348000000e016e80000000024b0000001c12250000f810580008080000000000000029b0ec8c5000238a550002400000002572780000002198000000000001690001230000002880002460000559d88000000000002970002349e21c99948002929b618900002b8000151fa9519af8d68000000000038000e58000001a984800000000000007300029c15723700000011f00000000002280002900000000000003080005722f0000002918001a00df23b1618000618000000000000c580000000000020c9110600000db8000711bd8000000001ae8000001728000a225605982600001f9b2a1200000024e8001319e18000000000001c680000000026000000000008304e07c8000000000000b880000000000002a16680009a9a08000000000000dd1da80000000000026306e00015d00000004e84903490b12c8001cc0001388000000fe00000000017080002300000000000000e80000028c0181660000882501ec80000000000000000025306500000016e0748d3000124a0a08292500029580002d9c38000000000000cd25800000027080013d80000000000001408582f12c0001b398e0000001a78000000000001a612d8318a282b0d0a2b18b9e8053a7f098a4f0f2066056a6da8487196598a9e98000000000000000000000001e416d253a4b80005d29b8850000002662900a880000011e0002440000000c680023780000000000018200020aa2680000000000000000000008692980014b0000000000000001d28000002818000001cb0000a089a00000a00005480012b0b500000000015f00026e09980000009b0310f11ee1bc11fa4a1a4084a0292a263a4d1ac2930002010000000000000000000001930000002830cc88b0910001bf006a2e0000ad00006a09400017714980000000000000000000
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x7c5c00480086c4522a341600c0003e12147a820e44ce00248e20ae660ad42c005e60dc2842ac9eb418003200b000de5400c898baaada40d2c2020076628c84b6900038006e003ac6723c647078560058001a1ca60000a006b274bed84ca800884a004ea4001e260400ca3036b800006c08466a688094509a00000000cc000092bc8a7e9c0096d02ed6220c5a0010a200000002060001070004030606000802101e01050000100001000312081002000206040307032707a1ee4a1aa421d147150e5110f0ca9ac029e858658d5014342a28e2a98a6a15187054c5350a8c39aa0282854c1c55014142a32e02a287996195458054ccb0cb22a028665451c55410d32a30e0aa0869951471550544ca8c382a82a265451c54214532a30e8a80a09955071540504ca86b94a6a1683469c35394e41a34e7a84a120e45521853210706a9ac4298838654d6014c41928e2b1ca420e25521853210782a96c29908383548614c841e0aa430a6420e8652185321070aa90c299083a1548614c841c0aa430a6420e19635405010714b12a028083435ca544cb31a34e1aa08718d1a70d52548c68d3a6a128463435c85450c31a32e02a28618e2552185420c706aa2c42a063865516015031928e2b24a418e4552185420c782a96c2a1063835486150831e0aa430a8418e8652185420c70aa90c2a1063a15486150831c0aa430a8418e0d62548410c70cb22a028063925895014031c28a630a8510e14541853288707a9ac420c4383d51620c621c28a630a8490d0c75509324870632a8499243611c5424c921c28a830a6490e8542185324869838a8428243c25093214121aa0e2990a090e0d535884108706aa2c418843455d4410c421c2aca2086210d85721043108742b1082188434a5c84154021a92e418aa010f10410c5500870c298c0a12818614e6090540a2ce3a9882a044d72194315030ca9ac1a1081435ca53508408a8e2b2a6420619535804110286b90a8a1e61459c75410e30c30a8302649842d72194414c30c2a4c118a61459c7540c530868e2b2a841861954583320c286b94a89906186551600c430838ecaa260185147154c41c8306a9ac420e41451c5540c720c1aa8b106390705424c95108390a12a290041d04c95148020a1ae529a8508616531854284286b94a89942185950614ca10e08a420862886626588620443503108288021b01883144010
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x41000024e5004433000804b00815093214121d01421c53214121c05655c8410c421c0575588410c421b01821043154021d01721043154021a048154d6210720a0481551620c720a058294c6150a10a0582950614ca10
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 48
  | 5 => 1017
  | 4 => 1345
  | 3 => 112
  | 2 => 10
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s5K7 (i*5) 5
  | 6 => packedAt s5K6 (i*16) 16
  | 5 => packedAt s5K5 (i*27) 27
  | 4 => packedAt s5K4 (i*38) 38
  | 3 => packedAt s5K3 (i*49) 49
  | 2 => packedAt s5K2 (i*60) 60
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s5K7 (6+((h/1+packedAt s5K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s5K6 (864+((h/16+packedAt s5K6 (768+(h % 16)*6) 6) % 58)*7) 7
  | 5 => packedAt s5K5 (31188+((h/339+packedAt s5K5 (27459+(h % 339)*11) 11) % 1964)*11) 11
  | 4 => packedAt s5K4 (56486+((h/448+packedAt s5K4 (51110+(h % 448)*12) 12) % 2598)*12) 12
  | 3 => packedAt s5K3 (5784+((h/37+packedAt s5K3 (5488+(h % 37)*8) 8) % 148)*8) 8
  | 2 => packedAt s5K2 (612+((h/3+packedAt s5K2 (600+(h % 3)*4) 4) % 16)*5) 5
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xffff81ffff87f07ff0787ffc3ffc0fdc1f3f3
  | 1 => 0xf03fffe07fff83f83ffff83ffc1fff027e7cfc
  | 2 => 0xffc1ffff83ffffffc007ffc3ffe1ffff878f1f
  | 3 => 0x1fffffc0003fffff80003fffe0003f80fe0
  | 4 => 0xfffe0000000003fffffffffc00000003fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x218488c51090a1014b418264c1324258c0b171
  | 1 => 0x6488114321200428150a8809440496081a54b4
  | 2 => 0x821122080a444252808454822a4128a3050a0a
  | 3 => 0xcb2dc49248756b9ce6d04623b3980c33e80fc0
  | 4 => 0xc31871c738673e738e76730231030c3f7e000
  | _ => 0
def s5Atlas : Atlas := ⟨7,rawDecor 31 s5Pos s5Neg, 0xece8e8e0ece8e8e0ece8e8e0ece8e8e0ece8e8e0ece8e8e0ece8e8e0ece8e8e0ece8e8e0ece8e8e0ece8e8e0ece8e8e0ece8e8e0ece8e8e0ece8e8e0ece8e8e0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_16333
namespace PEqualNP.Outside.L_meta_16333
open PEqualNP.Outside.L_meta_16333.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xd0949cd41c9014b908bc0078fc34c41040b0008ce4a05c2850c914604cc00c0000dc042084f400b4acf82ce07c300080980038003c5800a4000000d8006c70e8cd0d1008a8008800742400f1046844ed0064184854f0012006c60f0000380040830e12006010020289017fd5005fe54017f55005fc5401ffd4c07fe5301ff54c07fc53017fd0c05fe43017f50c05fc4300ffd48037f5200ff94803fd5200df54803fc5200ffd0803bf4200ff90803fd4200ef50803fc4200ffcc803df3200ff8c803fd3200f74c803fc3201ffd4407fe5101ff54407fc51017fd0405fe41006f90405fd41017f10405bc41007fcc401fe31007f4c401fc3100ffc8403fe2100ff48403fc2101ffd4007fe50005f94007fd5001ff140077c50017fd0005fe40017f50005fc40007fcc001fe30007f4c001fc3000ffc8003fe2000ff48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2a200cff1951001df8ca880337c65440073e32a200bffd911005dfec888003bf64440015fb22200bff99110015fcc88802ffd64440177eb22200bff19110015f8c88802fbc64440055e322200bffd511005ffca88802ffd5444017fe2a22000ffd8d10005fec688003df63440016fb1a2000ff98d1004dfcc688003fd63440017eb1a2000ff18d1004df8c688003dc63440016e31a200cffd4d10067fca688033fd5344019fe29a200bffd0d1005ffc868802ffd4344017fe21a200affd8910055fec488003ef624400177b12200aff9891000dfcc48802bfd62440157eb12200aff1891000df8c48802bec624400376312200affd4910056fea48802bfe5244015fea92200adf54910057f8a48802bff4244015dfa12200aff90910057fa848802bbd4244015fe212200affcc910057be648802bfe3244015fe992200af74c910057f86488033ff5144019ff28a200cff54510067f8a28802fff4144017ff20a2000ef9051005ffa828802ffc4144017de20a2000ffcc510007fc6288003fd3144001fe18a200affc8510057fc428802bf62144015fe90a200afd48510057f84288033ff5044019ff2822000df94110067faa088033fc5044019be282200bffd011005ffc808802ffd4044017fe2022000ffcc110007fc6088003fd3044001fe182200affc8110057fc408802bfa2044015fe902200afe48110057f84088003ff1044001fd8822000ff84110007ec208801bff650400d7fb282006ff9941001dfcca0801bfd650400d7eb282006ff1941001df8ca08017ff640400b7fb202005ff99010015fcc808017fd640400b7eb202005ff19010015f8c808017ff540400bff2a02005ff5501002ff8a808003ff63040017fb182000ff98c1004dfcc608003fd63040017eb182000ff18c1004df8c60801bff530400dff2982006ff54c10037f8a608017ff430400bff2182005ff50c1002ff88608013ff62040097fb102004ff9881000dfcc408013fd62040097eb102004ff1881000df8c408013ff5204009bfa902004ff94810027faa4080137d5204009fe2902004ffd08100277e8408013fe4204009fea102004ef50810027f88408013ff3204009ef9902004ff8c810027fa6408013dd3204009fe1902008bf98410037fea20801bfe510400dfea882006ff1441002ffe8208017fe4104001df2082005ff5041002ff88208017bc4104001ff9882000ff8c410007fa6208003fc3104009ff9082004ff88410027fa4208013fc210400f7f3002006ffd4010037fca0080037e500400dfea802006ff14010036f8a008017ff400400bff2002005ff5001002ff88008003ff3004001ff1802000ff4c010007f86008013ff2004009ff1002004ff48010027f84008003ff1004001fb8802000ff84010007f42008003fd1004001fa8802000fe44010
  | 1 => 0x7fc200c021ffb2e2010bfd9710087fccb8800efe65c4021bf32e20039f99710087facb88042fd65c4001beb2e20009f59710087f8cb8800efc65c401fffb26200fbfd931007ffcc98800afe64c401ffeb26200fbf5931007ff8c98800afc64c401fffaa6200fff9531007ffaa98803ffc54c4001ffb1e2000bfd8f10007fcc788026fe63c4001feb1e2000bf58f10007f8c788026fc63c4021ffa9e2010ff94f10087faa788043fc53c401fffa1e200fff90f1007ffa878803ffc43c4011ffb162008bfd8b10047fcc588006fe62c4011feb162008bf58b10047f8c588006fc62c4011ffa962008dfd4b10047fca588023fd52c4011bea962008ff14b10047fe8588023bf42c4011ff2162008ff50b100477a8588023fc42c4011ff9962008f7ccb10047fc6588023fd32c4011ee9962008ff0cb10087fea388043fe51c4021fea8e2010ff1471007ffe838803ffe41c4001df20e200fff5071007ff8838803fbc41c4001ff98e2000ff8c710007fa6388003fc31c4011ff90e2008ff88710047ec4388023fd21c4011fa90e2008ff08710087fea188043fe50c4001bf2862010ff54310087f8a1880437c50c401fffa06200fff9031007ffa818803ffc40c4001ff9862000ff8c310007fa6188003fc30c4011ff9062008ff88310047fa4188023fc20c401dffb2c200ebfd9610077fccb0800efe658401dfeb2c200ebf59610077f8cb0800efc658401bffb24200dbfd921006ffcc90800afe648401bdf3242002af9921006ffac908036fd6484001deb242000af5921006ff8c90800afc648401bffaa4200dff9521006ffaa908037fc5484001ffb1c2000bfd8e10007fcc708026fe6384001feb1c2000bf58e10007f8c708026fc638401dffa9c200eff94e10077faa70803bfc538401bffa1c200dff90e1006ffa8708037fc438400fffb142007bfd8a1003ffcc508006fe628400ffeb142007bf58a1003ff8c508006fc628400fffa942007dfd4a1003ffca50801ffd528400fbea942007ff14a1003ffe850801fbf428400fff2142007ff50a1003f7a850801ffc428400fff9942007f7cca1003ffc650801ffd328400fee9942007ff0ca10055fac30803bff518401dff28c200eff54610077f8a308037ff418401bff20c2000ef9061006ffa8308037fc418401bde20c2000ffcc610007fc6308003fd3184001fe18c2007ffc861003ffc430801ffd218400ffe10c2004bf98210077fea10803bfe5084001bf284200eff54210077f8a10803b7c508401bffa04200dff9021006ffa8108037fc4084001ff9842000ff8c210007fa6108003fc308400fff9042007ff8821003ff4410801ffd208400ffc9042007ff08210007fe2108003f71084001fd884200cffd9510065feca880037f65440013fb2a200cff9951001dfcca88033fd65440197eb
  | 2 => 0x300c7fa8118063fc408c013ff9846000f7cc23004ff66118053ff208c029ff1046014ff482300a7f8411805fff654c02f7fb2a6000dfd9530004feca9805ffe654c0077f32a6017ff595300bdfaca9805ffc654c0077e32a6017df1953001cf8ca9805bff644c02d7fb226000efd91300057ec89805bfe644c0057f3226016ff591300b5fac89805bfc644c0057e3226016ef1913001578c89805bff544c02dff2a26016ff551300b7f8a89805fff534c013ff29a6017ff54d3004ff8a69805bff434c013ff21a6016ff50d3004ff88698057ff624c02b7fb126015ff9893000dfcc498057fd624c02b7eb126015ff1893000df8c498057ff524c02bbfa926015ff949300affaa4980577d524c02bfe2926015ffd09300af7e8498057fe424c02bfea126015ef509300aff88498027ff324c02bef9926015ff8c9300affa6498057dd324c013fe1926000ffd8530005fec298003fe614c001feb0a6000ff18530005f8c29805fff514c02fff28a6017ff545300bff8a29805bff414c02dff20a6000ef905300b7fa829805bfc414c02dde20a6009ffcc530007fc6298003fd314c013fe18a6015ffc85300affc4298057fd214c02bfe10a6017ffd41300bffca0980037e504c02ffea826017ff141300bef8a09805bff404c02dff2026016ff501300b7f88098027ff304c013fd9826000ff8c130007bc6098057ff204c02bff1026015ff481300aff84098027ff650c0137fb286009ff9943001dfcca18027fd650c0277eb286009ff1943004df8ca18027ff640c0137fb206009ff99030015fcc818027be640c0055f3206009ff59030095fac818027bd640c0015eb206009ff1903004df8c81804bff540c025ff2a06012ff55030097f8a818026fe630c013ffa986009ff94c3004ffaa618027fc530c013ffa186012f7d0c3004ffc8618027fd430c013fe2186009f710c3004ffec418026ff620c013ff3106001bf9883004ffac418046fd620c013fe3106001bf1883008ffea4180477f520c023ff2906011ff5483008efaa418047fc520c023ffa106011efd083008ffc8418047fd420c023dea106011ff1083004ffe6418027df320c013ff1906009ff4c83008fba6418027fc320c013ffb086009ff98430005fcc218027fd610c0017eb086009ff1843009ffea21804ffe510c027fea886013ff14430097fe821804bfe410c001df2086012ff50430097f8821804bbc410c013ff9886009ff8c430007bc6218027fd310c013fe1886009f70c43008ffe4218047fe210c023fe9086011ff084300a5fcc01804fff500c027ff2806000df9403009ffaa01804ffc500c027be2806012ffd0030097fc801804bfd400c025fe2006009ffcc03004fbe6018027fe300c013fd1806009ff4c030007ba6018027f9300c023ff9006011ff8803008ffa401804
  | 3 => 0xf994a01ddf8ca500eefa65280775d329403bbe194a000dfd8650006fcc3280037d6194001be30ca01edfd06500f6fc83280033e419403dbea0ca01edf106500f67883280037f3194001bf18ca000df4c650006f863280777f219403bbf10ca01ddf486500eef8432800f7e60940073f304a003de982500f6fe812807b7e409403dbea04a01edf102500eefe41280777e209403bbe904a01ddf0825004ffecb98026ff65cc013ff32e6003bf9973004efccb9800e7e65cc013feb2e601cbf5973004efacb980027d65cc013fe32e6009bf1973004ffec998026ff64cc013ff3266002bf9933004ffac99806efd64cc013fe3266009bf193300dffea99806ffe54cc037feaa6601bff1533004ffea798027fe53cc013fea9e6009ff14f3004ffe8798027fe43cc013fea1e6009ff10f3004ffec598026ff62cc013ff3166001bf98b3004ffac59806afd62cc013fe3166001bf18b300d7fea59806b7f52cc035ff296601aff54b300d6faa59806bfc52cc035ffa16601aefd0b300d7fc859806bfd42cc035dea16601aff10b3004ffe6598027df32cc013ff1966009ff4cb300d7ba6598027fc32cc013ffb0e6009ff98730005fcc398027fd61cc0017eb0e6009ff187300e7fea398073fe51cc039fea8e601cff147300dffe839806ffe41cc001df20e601bff507300dff8839806fbc41cc013ff98e6009ff8c73004ffa6398027fc31cc035ff90e601aff887300d7fa439806bfc21cc039ffa86601cff94330006fca198073fd50cc039fe286601cdf143300dffe819806ffe40cc037fea06601bff103300d7fe419806bfe20cc035fe906601aff083300cffecb18066ff658c033ff32c6003bf996300cffacb18066fd658c033fe32c6003bf196300c7fec918062ff648c031ff3246002bf992300c7fac918062fd648c031fe3246002bf192300c7fea918063fe548c031feaa46018ff152300adfac718067ff538c013ff29c6019ff54e3004ff8a718063ff438c031efa1c6009ff90e300c7fa8718027fc438c031ee21c6014ffd8a300a5fec518053fe628c0037f3146014ff58a300a5fac518053fc628c0037e3146014ffd4a300a6fea518053fe528c029fea946014df54a300a7f8a518053ff428c029dfa146014ff90a300a7fa8518053bd428c029fe2146009ffcca300a7be6518053fe328c029fe9946014f74ca3004ff86518003ff618c001ff30c6000bf98630007fac318002fd618c001fe30c6019ffd46300cffca318067fd518c033fe28c6018ffd06300c7fc8318003be418c031fea0c6018ff106300c7788318027ff318c001ff18c6000f78c630007fa6318027fc318c001ee18c6014ffc86300a7fc4318053fd218c029fe10c6009bf982300cffea118067fe508c001bf2846019ff542300cff8a1180677c508c031ffa046018ff902
  | 4 => 0x80efe654c44bfeb2a6225bf5953112ff8ca9880efc654c44bbe32a62039f19531127fec898892ff644c401dfb226200afd9131127fcc89880afe644c449feb226224bf59131127f8c89880afc644c449de3226202af19131127fea898893fe544c449feaa26224ff1513112ffea698827fe534c44bfea9a6209ff14d31127fe8698827fe434c449fea1a6209ff10d3111ffec49888eff624c447ff3126201bf9893111ffac49888efd624c447fe3126201bf1893111ffea49888f7f524c447ff2926223ff5493111efaa49888ffc524c447ffa126223efd093111ffc849888ffd424c447dea126223ff1093104ffe649888fdf324c447ff1926223ff4c93111fba6498827fc324c44bffa8a6225ff9453112ffaa298897fc514c449ffa0a6224ff905310077c8298893fd414c449fe20a6224ef1053104ffe6298827f7314c401ff18a6200f78c53111ffe429888ffe214c447fe90a6223ff08531007fec098802ff604c401ff3026200ff58131007f8c098802fc604c44bffa826225ff9413112ffaa098897fc504c44bbe2826224ffd0131127fc8098893fd404c449fe2026223ffc813111ffc409888ffd204c447fe1026209ffd943104dfeca18827fe650c4077f3286209df9943101cfcca18827fd650c4437eb286209df59431004faca18827fc650c4137e3286209ffd903104dfec818827fe640c4057f3206209ff59031105fac818827fc640c4137e3206220ffd5031107fca818883fd540c441fe2a06209bf98c3104ffea618887df530c413ff2986209ff54c3104ff8a618827dc530c413ffa186209ff90c3104ffa8618827fc430c413ffb106209bfd883104ffcc418806fe620c413feb10621fbf5883104ff8c418806fc620c43fffa90621fdfd48310fffca41887ffd520c43fbea90621fff148310fffe841887fbf420c43fff210621fff508310ff7a841887ffc420c413ff9906209f7cc83104ffc6418827fd320c43fee9906209ff0c831115fcc218887ff510c443ff2886221ff5443110ff8a218883ff410c441ff2086200ef90431107fa8218883fc410c441de2086209ffcc43104fbe6218827fe310c413fb1886209ff4c431007ba6218827f5310c43fff908621fff884310fffa421887ffc210c413ffb006209ff98031005fcc018827fd600c4017eb006209ff1803110ffea018887fe500c443fea806221ff1403110ef8a018883ff400c441ff2006220ff50031107f8801887fff200c43fff100621fff480310fff8401887b7f649403dbf324a01edf592500f6f8c9280037f6394001bf31ca000df58e50006f8c72807b7f439403dbf21ca01edf50e500f6f887280777f629403b3fb14a01ddf98a500eefac5280767d629403bbe314a01ddfd0a500ee7e85280777e429403bbea14a01dcf50a500eef885280777f329403ba
  | 5 => 0x4a4115f78a5208afbf3290457cf994822bef8ca4115f7a65208af9d3290457de1948202ef986410157cc32080bb66190459dfa8c822cef946411677aa3208b3bc5190457df90c822bef8864115f7a43208afbc2190401dfb048200ef982410077ac120803bc6090459dfa84822cef942411677aa1208b3bc50904599e284822befc824115f7c41208afbd2090457de1048209ffd973104dfecb98827fe65cc4077f32e6209ff59731155facb98827fc65cc4137e32e6209ffd933104dfec998827fe64cc4057f3266209ef993310157cc998827fd64cc4537eb266209ef593310057ac998827fc64cc4137e3266229ffd533114ffca9988a7fd54cc453fe2a66209ffd4f3104ffca798827fd53cc413fe29e6209ffd0f3104ffc8798827fd43cc413fe21e6209ffd8b3104dfec598827fe62cc4037f3166209ff58b31145fac598827fc62cc4037e3166228ffd4b31146fea5988a3fe52cc451fea966228df54b31147f8a5988a3ff42cc451dfa166228ff90b31147fa85988a3bd42cc451fe2166209ffccb3104fbe6598827fe32cc413fe9966228f74cb3104ff865988abff51cc455ff28e622aff54731157f8a3988a7ff41cc453ff20e6200ef9073114ffa83988a7fc41cc453de20e6228ffc8731147fc43988a3fd21cc451fe10e6209ffd833104ffcc198802fe60cc413feb066200bf5833104ff8c1988abff50cc455ff286622aff54331157f8a1988ab7c50cc453ffa066229ff9033114ffa81988a7fc40cc451ff9066228ff88331147fa41988a3fc20cc44fffb2c6227bfd963113ffccb1880efe658c44ffeb2c6227bf5963113ff8cb1880efc658c44dffb246226bfd9231137fcc91880afe648c44dfeb246226bf59231137f8c91880afc648c44dffaa46226ff95231137faa91889bfc548c4477eb1c6227ffd4e3113fbea718827fe538c44ffea9c6209ff14e3113fb8a71889bff438c413ff21c6226ff50e3104ff8871888bff628c4457fb146222ff98a3100dfcc51888bfd628c4457eb146222ff18a3100df8c51888bff528c445bfa946222ff94a31117faa51888b7d528c445fe2946222ffd0a311177e851888bfe428c445fea146222ef50a31117f88518827ff328c445ef9946222ff8ca31117fa651888bdd328c413fe1946209bf9863113ffea31889ffe518c44ffea8c6227ff14631137fe831889bfe418c401df20c6226ff50631137f8831889bbc418c413ff98c6200f7cc63104fee631888bff218c445ff10c6222ff48631117f84318803ff608c401ff3046200bf98231007fac118802fd608c401fe3046227ffd423113ffca11889ffd508c44ffe2846227df14231137fe811889bfe408c44dfea046226ff10231117fe411888bfe208c445fe9046222ff0823112ffeca98896ff654c401bfb2a62009fd953112ffcca98
  | 6 => 0x8d3bd071014e0c000a2c2a94e4d0911ce70001370f640000000014d93147c14e0000744b983a53a1364920b9c000d0c42500447881000132c000000000f5c000f61308a24280c540000004680000005c866c0001406f8618000e24000134d28c5825c1848a4000608670ec8b9000000000000115cb94ea000000009c1302981d11a0f10ef412c90830cd2d4311140008791a49b4000fa8000510000000eb00008540003e90a8f24344fc4c64ee83a90886a90dc0004e8e9007c0e4e7800000022000068800071c00000130c00000058939c54c53537c678c5c6e80f94284753d0084a886340c80bc26d104390bc041ce6c79c260700560bc508c070c4c4154685c0ad11ec6140000000646e0c607d45403c02f433c40d2a10a53800b1148819154a1d068fb45b89143c52a41f0004150030160100980000000c1d00201c00000004000084000070560300a8150440040101204e000010020000140000101e0080480400006c0182902e0180000005a0680080200c000000060060200f01b0040080d80301004c000020120dc0002a008004000080000000f00700400400800000008000150000000000b07c0101680f0740781c00200a0440100500204c01000004000048000020140280005a0080600701c06c0480007c008010060000380005f0000800a801046020028020000000000800200001801028034000090da000010000440140480000e00006004000000000010180200500000e0080001902000000002000024000030040200b036000000000010160000380300400c038010000480200c00204c0203f02a048048040680000000d00c0080600200c03c008020040040880a02a01c0780004200c01802004004048090260340000f0bc00c0a8030000380003a01c05c000030220080281600c00c0882a07c0140181400c0000c00300000408810056004000040460a0008000080500c80001603c058150580000480101c0000000800e00c07800004008020020000040680e032008028090080000101403201416000000004090010020080180500202400802014004060000640000900100c01400005000028000090040000280003c02c0300307e0000100002c0000800f02803c0380000c0380200c07802008803006000000030060b801831000010250020100280c8000280040000300006401037014030010040080140981f00e028000040120000e00d16001c01801000090020010020040b00400001c0002104e0200700300c0200e81103800002000042000000b3bf6590459df32c822cef5964116778cb20803bf6390401df31c8200ef58e4100778c7208b3bf5390459df29c822cef54e4116778a7208afbf62904575fb14822bef98a4115f7ac5208aebd6290457de314822befd4a4115e7ea5208afbe5290457dea94822bcf5
  | 7 => 0x11e1258000000000000c400e08281200000000005e40003252e0000d610d80000013cd4783d5410000ed0000d780001c47d85fc77c36c000204138000758000968eb8a0039800148800045c93800057435800018031800094545c94075443c2902c83084a87647bd4587ec0a46d81dd3b4bb50507b023d0a08a8d74980234748a691401e0488ea52acbb10b0528649090aa00011808f124cb8ce44bf022d34541d394dbca505952940013fc7393852b8001250cfcb441e92a90c40012bc08c8700012dcf501a052400049cb4888463c00000002484c374000000db800113895512036420000013c0009490ccb70ce8000268fd8d18328b754540010f06a10002400007a4124101278890c24000e405013e4a387e87c9108a04e84254ec4b6c8c909cf18825304d1cf0933d39002d275270ce1311049504ce4a8cc98fcc9acac020d285040db05146740991dccac32ca9d2ec9611f0b00b1d3347ccbc8c3c0ed010394931034bb9208c1d224b302bc8986d14f51300dcf70aa8fe92391c41e51fc4f9438fa4c70108e74af46b81f8bcc1fcf746ad4f07a8c7c4e0d8511824cf68e68d914ed1b4c1000000142cdccf45190ae90746f439c3704387e4a30bbd0f4f14110a7c218544148e08e2886cc05408d98dd906005c5dd15936934067cebc020a2815c45904d3e8804b2d214eb512c6e44d54bc74cb3cea8ba54d1020a980000000005983f89a5111354ba05f8f300e94b87ad4acc184c8e040883307b8b0c88d480e50b40090170894035324ed4b682a4d8d2694241a8ffc8683f01f5234c88860fe4e38000cdcca80010f8000080ff87507200000000000392e94650592d0eec62d038040f7800000000000400000000015130134c0000000010bd2fd3ed1012d493c6800003d0000b10de4ec0e18058d20c8c7c49fc0003a03681951508145703780c12182ecaec8e8a481611a89283bc000000000798e88e1d1f49994ccc6916cd2454846d510a200942e40a93f4b28bdc2e8e00e994e84a0820e7c95d23055d26d1c0ca4de869c4ac248000e4d0b4a9060c068f7ce64ff4e60f39144dc50fd3f0ecc4c54d4228800d5c4d8f9864d3b8664f8c00103028d1b800038c2c02a0af0c143ad2f885c2646cc03c23027086550cafd4000000014a443005405016451920542000021d13d1f8c780000000000000a05d4c6d4dc001124000d894c90e80014509f80000000009e8a350e01144940000006c4a64000bec8c517c174000cc0208f9cdd42fc6b441910cb08dc889c0000010e40013dccc548525d098e5ca94f84b594b47a0ccc3b02245bc8582cccd0d6c92c550ae1210f80c850553d8d30ae53d4970000cc80003840014a8000794f285584b10289b00009c8000d345214fd34829c00103cb6427c04c6382e078c0090ad13507c1684983b8de06513
  | 8 => 0x194210ddc000bac000ad40008b43890080f40014940d468c5ec0004340004208748dc0008a106d0780009cd330000000d48000000698f0400000000076c0005d95085c43f4d44ef0a18ee0f1d498b7d36cd4cff117897943d3190d0e48f5947d3608b0a606f0e209f4a3c90c50d16056859018c9340d8904be83c9260bd00b43e0d407fc81c1980010848fc0004f0e803dcadc0000000012f522042c8b8310b5d3a4990e9cb18e949e48c0fac57c580f906900280f0d693c4ee4d50000924c946c8cd4001018000f3cb785d1378ad87e0000eac00059ccb92808d8e347780001b400000034947031c000950ceca100749d0ac817c000258334df0cbd4451e40009f07d00000000008e4e10cb0000000000000910000e580c42b40000b86fd514c44df8dfd2c035d3c0000cb4000000d386b0000fa0000d3c52c3d94f81b07052c4000f8848c4f4efc34151817800000083c19c118f480001b8ab0048e305789d40011cc2746eca44000000000c2c6c0bd87340006948bc9a000000140c0000002148d11688d42f8000000b3411c0d0d00b380144907dcf2d48c0fc7f891c6dc000da0000b604c07702ac001418d04380001265320000768000000000a80cd9474000000000d58000708428000660b244bc4b80000000007600000000005040007100000000000014a06a471865866928800000065d19ce14000408abd0640005cd1d800000114d44c000b151981d8c5122c9dcc384705f41ecca073135810521c1bc4100005ac7b434d080484c904484548408cc8ad0250c06bc7746104fd374df49d8c000006d43fc00018810cdac5a0000e2c7880005b4288354144a4c6245e84e5228b802d8dec3ec00d5012450c8d1127d32880d4c4a413b12cccf0f409c4bd4a7874116488095918c2f0728fc8630a14b4c3154347f4ed8b5124100c4041c832073cc212c8b2058c71523c530e8cd54fd49bc5a8ab4c9c33825016d49d248a0864072c14caac8449c11281a51d0c302b8ef82c4fed1c87804cc0ac480360edcd14c2898c000aa4460838304a5c4b4918a540100000014048f80006206000cd2d94400012f1448be5460238974539174da465531c0180010954c0d9c00094c000db4000900fb80001cc0010d4a7400098875c00006cfc0000d94a0caf88ec464bfd3882dd3a8b850ed01d200000000dd0d6528cc753c8000cf44411d49ec0008e0000ab8c34acc0000006042b13e06847251e8158c4935146c0001d505c3b447ce548485e0000000000e3c00040000070cd70000554a8461c000c0887c7f08305082451ac1c00008f4da90440004a529ca71298294888b88be001d1705f028485099cf0c4dc0449b8f94a588094b0ac4d7cfb0984f4c964350790fdca6d2905a518400045118819044403082c9a8f6d254bf8cf8bf51bd4913390b851c00
  | 9 => 0x97cb044d03cc0609942d4fd0f341acf552b120c96d35c8345b0fe06449e0c80f005653acf2053cba92b456c2d03011b00782783e4628dc0fbcb54584c0cd8000000078437c44d3981552e53f84ec12800141502d
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xc76940101e67f64940100f67e64940101e67d64940100f67c64940100067f63940101fe7e63940100067d63940101fe7c63940101f57f72940101f57d72940101ee7f62940100ee7e62940101ee7d62940100ee7c62940101ef3f42940101ef3d42940101ef5f32940101ef5d32940100077671940100077571940100867e61940100073e41940101e73c41940100357e70940100377a70940100767e6094010004fd76cc0100357e75cc0100057d75cc010004ff768c01004cfd768c01004ede638c010006dd638c010005f6718c010005f5718c010004ff764c0100057f754c0100357c754c010005bf744c01002dbc744c01004cff760c010004fe760c010004fd760c01004cfc760c01002dbe740c010005bd740c01004ede630c010006dd630c010005f6710c010005f5710c0100357e75c40100057d75c4010007b641c40101dfb441c4010046f576c40101cf7675c40100077575c40101d6f762c40101d6f562c40101d77752c40101d77552c40101d7b742c40101d7b542c40101d7d732c40101d7d532c40100077650c40101cf7450c401002dbe7484010005bd74840101b5f571840101aef661840100077a50840101c7785084010025f9768401003ef9768401000cf976840101a7ba7484010007b974840101befb62840101bef962840101bf7b52840101bf7952840101bfbb42840101bfb942840101bfdb32840101bfd932840101b5f971840101aefa6184010007f26184010007ba41840101a7b84184010004ff76440100057f75440100357c7544010005bf744401002dbc7444010005df7344010005dc7344010005ef7244010025ec7244010007b64144010177b441440100077a504401017f785044010005f77644010006f77644010004f7764401000777754401017f747544010007b77444010177b47444010007d77344010007d47344010007e7724401016fe4724401016ef7624401016ef5624401016f77524401016f75524401016fb7424401016fb5424401016fd7324401016fd5324401019df77044010196f6604401000776504401017ff2504401000772504401017ff1504401017f745044010177f34044010177f04044010007f33044010007f0304401016ff2204401016ff12044010005fb7644010006fb7644010004fb76440100077b754401017f787544010007bb7444010177b87444010007db7344010007d87344010007eb724401016fe8724401016efb624401016ef9624401016f7b524401016f79524401016fbb424401016fb9424401016fdb324401016fd9324401018dfb7144010007f37144010186fa6144010007f2614401017ff2514401017ff15144010177f34144010007ba4144010177b84144010177f04144010177b04144010007f33144010007f0314401016ff2214401016ff12144010
  | 1 => 0x4110007ba41c4110247b841c411023ff221c411023ff121c41100067f65841100767c658411005dbe7484110005bd7484110006bf648411006ebc6484110006df6384110006dc6384110006ef628411003eec6284110007b64184110237b44184110055f6768411000777658411022f746584110237b67484110007b57484110007b76484110237b46484110007d76384110007d46384110195f77284110195f57284110007e76284110227e46284110227775284110227755284110227b74284110227b54284110227d73284110227d53284110007f3608411000776508411022f745084110227f22084110227f12084110004ff75d8c1001cfe75d8c10004fd75d8c1001cfc75d8c10004ff74d8c10014fe74d8c10004fd74d8c10014fc74d8c10004ff72d8c1000cfe72d8c10004fd72d8c1000cfc72d8c100067f52d8c100067d52d8c10006bf42d8c10006bd42d8c10006df32d8c10006dd32d8c10004fe71d8c10006f671d8c10006bc41d8c10004fe70d8c10006fa70d8c100067c50d8c10004fd7698c10006df6398c1004cff7658c100057f7558c100357c7558c10005bf7458c1002dbc7458c10004ff7558c100067f7558c100047f7558c1001cfe7558c10004fd7558c1001cfc7558c100067c7558c1001c7c7558c10004ff7458c10006bf7458c10004bf7458c10014fe7458c10004fd7458c10014fc7458c10006bc7458c10014bc7458c10006df7358c10006de5358c10006dd5358c10006de4358c10006dd4358c10004ff7258c1000cfe7258c10004fd7258c1000cfc7258c100067f5258c100067d5258c10006bf4258c10006bd4258c10006df3258c10006dd3258c1004cff7158c1004cfd7158c10006bc4158c1004cff7058c1004cfd7058c100067c5058c100357e7518c100057d7518c1002dbe7418c10005bd7418c1004ede6318c10006dd6318c10025ee7218c10005ed7218c1007ebf7690410016be7690410016bd769041002ebc7690410206bf6590410166be6590410206bd6590410166bc6590410006bf639041021ebe6390410006bd639041021ebc6390410215bf7290410215bd729041020ebf629041015ebe629041020ebd629041015ebc629041020f3f529041020f3d529041020f9f329041020f9d329041002dbe719041002fb6719041007ebe6190410007ba7090410007b9709041006ebe60904102073c5090410004fd76cc41002dbe74cc410005bd74cc410004ff768c41004cfd768c41004ede638c410006dd638c410005fa708c410005f9708c410004ff764c4100057f754c4100357c754c410005bf744c41002dbc744c41004cff760c410004fd760c4100357e750c4100057d750c41004ede630c410006dd630c410005fa700c410005f9700c4100767f769401001e7e769401001e7d76940100367
  | 2 => 0x26fba209051026fb92090510004fe76cc5100067f65cc5101567c65cc51005dbe74cc510005bd74cc510006bf64cc51014ebc64cc510006df63cc51004edc63cc510006ef62cc510146ec62cc510005fa70cc510005f970cc510004fe768c5100067f658c51013e7c658c510006bf648c510136bc648c510006df638c51004edc638c510006ef628c510116ec628c51004cfc764c5100057f754c5100657c754c5100067f654c51012e7c654c510005bf744c51005dbc744c510006bf644c510126bc644c510006df634c51004edc634c510006ef624c51011eec624c510005fb704c510005f8704c510004fe760c5100657e750c5100057d750c5100067f650c51010e7c650c510006bf640c510106bc640c510006df630c51004edc630c510006ef620c5100feec620c5100057e76941100867e76941100847e769411025e7f64941100073f64941100063f64941100f67e649411025e7d64941100f67c649411025f3c64941100f63c64941100067f63941100075f63941100065f63941101fe7e63941100067d63941101fe7c63941100075c63941100065c63941102657f72941102657d72941102567f62941100076f62941100066f62941100ee7e62941102567d62941100ee7c62941102576c62941100ee6c62941102573f42941102573d42941102575f32941102575d32941100073e419411025f3c41941102577621941102577521941100657e70941100677a70941102577a2094110257792094110004fe76cc1100657e75cc1100057d75cc1100067f65cc1100e67c65cc110006bf64cc1100debc64cc110006df63cc11004edc63cc110006ef62cc1100d6ec62cc110005f671cc110005f571cc110004fe768c1100067f658c1100ce7c658c110006bf648c1100c6bc648c110006df638c11004edc638c110006ef628c1100a6ec628c11004cff764c110004fd764c11004cfc764c1100057f754c1100657c754c1100067f654c1100be7c654c110005bf744c11005dbc744c110006bf644c1100b6bc644c110006df634c11004edc634c110006ef624c1100aeec624c110005f7714c110005f4714c110004fe760c1100067f650c11009e7c650c11005dbe740c110005bd740c110006bf640c110096bc640c110006df630c11004edc630c110006ef620c11008eec620c1100657e75c41100057d75c41100067f65c41100867c65c4110006bf64c411007ebc64c4110006df63c4110006dc63c4110006ef62c4110046ec62c41100077a50c411024f7850c411024f7a75c41100077975c41100077b65c411024f7865c4110007bb64c4110247b864c4110007db63c4110007d863c4110185fb72c4110185f972c4110007eb62c411023fe862c411023f7b52c411023f7952c411023fbb42c411023fb942c411023fdb32c411023fd932c
  | 3 => 0xf4218d100069f4218d10006de4218d10006dd4218d100069d4218d10006dc4218d1004edf7118d1004edd7118d10006df5118d10006de5118d10006dd5118d10006dc5118d10006df4118d10006de4118d10006dd4118d10006dc4118d100069c4118d10006df2118d10006de2118d10006dd2118d10006dc2118d1004edf7018d1004edd7018d10006df5018d10006de5018d10006dd5018d10006dc5018d100065c5018d10006df4018d10006de4018d10006dd4018d10006dc4018d10006df2018d10006de2018d10006dd2018d10006dc2018d10006dd1018d10055ee76d8910056ee76d891000cee76d89100076f75d89100076c75d8910006ef65d89100076f65d89100066f65d8910006ee65d8910006ed65d8910006ec65d89100076c65d89100066c65d8910007af74d8910007ac74d8910006ef64d8910007af64d8910006af64d8910006ee64d8910006ed64d8910006ec64d8910007ac64d8910006ac64d8910007cf73d8910007cc73d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d8910007e771d8910057e471d8910007ac41d8910007eb70d8910057e870d89100076c50d8910006ef75d89100066f75d8910006ee75d8910006ed75d8910006ec75d89100066c75d8910006ef74d8910006af74d8910006ee74d8910006ed74d8910006ec74d8910006ac74d8910006ef54d8910006ee54d8910006ed54d8910006ec54d8910006ef73d8910006cf73d8910006ee73d8910006ed73d8910006ec73d8910006cc73d8910006ef53d8910006ee53d8910006ed53d8910006ec53d8910006ef43d8910006ee43d8910006ed43d8910006ec43d8910006ef71d8910056ee71d8910056ed71d8910056ec71d8910006ef51d8910006ee51d8910006ed51d8910006ec51d8910006ef41d8910006ee41d8910006ed41d8910006ec41d8910006ac41d8910006ef70d8910056ee70d8910056ed70d8910056ec70d8910006ef50d8910006ee50d8910006ed50d8910006ec50d89100066c50d8910006ef40d8910006ee40d8910006ed40d8910006ec40d8910056ed10d8910005be769051006ebe769051006cbe7690510276bf65905100073f65905100063f6590510166be6590510276bd6590510166bc65905102773c65905101663c6590510006bf63905100079f63905100069f639051021ebe6390510006bd639051021ebc63905100079c63905100069c639051027dbf729051027dbd729051026ebf6290510007af6290510006af629051015ebe629051026ebd629051015ebc629051026fac629051015eac629051026f3f529051026f3d529051026f9f329051026f9d329051005dbe719051005fb6719051026fb6219051026fb521905102773c5090510
  | 4 => 0x8d100065f52d8d10006de52d8d10006dd52d8d100065d52d8d10006dc52d8d10006df42d8d100069f42d8d10006de42d8d10006dd42d8d100069d42d8d10006dc42d8d10006df71d8d10006dd71d8d10006df51d8d10006de51d8d10006dd51d8d10006dc51d8d10006df41d8d10006de41d8d10006dd41d8d10006dc41d8d100069c41d8d10006df21d8d10006de21d8d10006dd21d8d10006dc21d8d10006df70d8d10006dd70d8d10006df50d8d10006de50d8d10006dd50d8d10006dc50d8d100065c50d8d10006df40d8d10006de40d8d10006dd40d8d10006dc40d8d10006df20d8d10006de20d8d10006dd20d8d10006dc20d8d100657e7598d100057d7598d100067f6598d100067c6598d1005dbe7498d10005bd7498d10006bf6498d10006bc6498d10006df6398d10055ee7298d10005ed7298d10006ec6298d100057f7558d100657c7558d100067f6558d100067c6558d10005bf7458d1005dbc7458d10006bf6458d10006bc6458d10005ef7258d10055ec7258d10006ec6258d10004ff7558d100067f7558d100047f7558d1001cfe7558d10004fd7558d1001cfc7558d100067c7558d1001c7c7558d10004ff7458d10006bf7458d10004bf7458d10014fe7458d10004fd7458d10014fc7458d10006bc7458d10014bc7458d10006df7358d10004ff7258d10006ef7258d10004ef7258d1000cfe7258d10004fd7258d1000cfc7258d10006ec7258d1000cec7258d100067f5258d100067d5258d10006bf4258d10006bd4258d10006df3258d10006dd3258d10004ff7158d10006f77158d10006bc4158d10004ff7058d10006fb7058d100067c5058d10004fe7618d100067f6518d100067c6518d10006bf6418d10006bc6418d1004ede6318d10006dd6318d10006ec6218d10005de7618d10006de7618d10004de7618d10006df6518d100075f6518d100065f6518d10006de6518d10006dd6518d10006dc6518d100075c6518d100065c6518d10006df6418d100079f6418d100069f6418d10006de6418d10006dd6418d10006dc6418d100079c6418d100069c6418d10005df7218d10005dd7218d10006df6218d10006de6218d10006dd6218d10006dc6218d10007cc6218d10006cc6218d100075f5218d100075d5218d100079f4218d100079d4218d100079c4118d10007d62118d10007d52118d100075c5018d10007da2018d10007d92018d1004edf7518d1004ede7518d1004edd7518d1004edc7518d1004edf7418d1004ede7418d1004edd7418d1004edc7418d10006df5418d10006de5418d10006dd5418d10006dc5418d1004edf7218d1004cdf7218d1004ede7218d1004edd7218d10004dd7218d1004edc7218d10006df5218d100065f5218d10006de5218d10006dd5218d100065d5218d10006dc5218d10006d
  | 5 => 0x63c65d9110005bf72d9110005bd72d9110006bf62d9110006be62d9110006bd62d9110006bc62d9110007ac62d9110006ac62d91100073f52d91100073d52d91100079f32d91100079d32d911005dbc71d9110007b621d9110007b521d91100073c50d9110007ba20d9110007b920d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d9110006be53d9110006bd53d9110006bc53d9110006bf72d9110004bf72d9110006be72d9110006bd72d9110004bd72d9110006bc72d9110006bf52d91100063f52d9110006be52d9110006bd52d91100063d52d9110006bc52d9110006bf32d91100069f32d9110006be32d9110006bd32d91100069d32d9110006bc32d9110006bf71d911005ebe71d9110014be71d911005ebd71d911005ebc71d9110014bc71d9110006bf51d9110006be51d9110006bd51d9110006bc51d9110006bf21d9110006be21d9110006bd21d9110006bc21d9110006bf70d911005ebe70d911005ebd70d911005ebc70d9110006bf50d9110006be50d9110006bd50d9110006bc50d91100063c50d9110006bf20d9110006be20d9110006bd20d9110006bc20d911005ebd10d911004cfe76d8d100067f65d8d100067c65d8d10006bf64d8d10006bc64d8d10006ec62d8d10004ff75d8d1001cfe75d8d10004fd75d8d1001cfc75d8d10004ff74d8d10014fe74d8d10004fd74d8d10014fc74d8d10006df53d8d10006de53d8d10006dd53d8d10006dc53d8d10006df43d8d10006de43d8d10006dd43d8d10006dc43d8d10004ff72d8d1000cfe72d8d10004fd72d8d1000cfc72d8d100067f52d8d100067d52d8d10006bf42d8d10006bd42d8d10006df32d8d10006de32d8d10006dd32d8d10006dc32d8d1004cfe71d8d1004cfc71d8d10006bc41d8d1004cfe70d8d1004cfc70d8d100067c50d8d1004cde76d8d10006df65d8d100075f65d8d100065f65d8d10006de65d8d10006dd65d8d10006dc65d8d100075c65d8d100065c65d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dd64d8d10006dc64d8d100079c64d8d100069c64d8d10005df72d8d10005dd72d8d10006df62d8d10006de62d8d10006dd62d8d10006dc62d8d10007cc62d8d10006cc62d8d100075f52d8d100075d52d8d100079f42d8d100079d42d8d100079c41d8d10007d621d8d10007d521d8d100075c50d8d10007da20d8d10007d920d8d10006df75d8d10006de75d8d10006dd75d8d10006dc75d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006df54d8d10006de54d8d10006dd54d8d10006dc54d8d10006df72d8d10004df72d8d10006de72d8d10006dd72d8d10004dd72d8d10006dc72d8d10006df52d
  | 6 => 0xf329421029f5d32942100077671942100077571942100073e41942102a73c41942100757e70942100777a70942100367e609421029f7a209421029f7920942100757e75cc2100057d75cc2100debe64cc210006bd64cc21004cfd768c2100c6be648c210006bd648c21004ede638c210006dd638c210005f6718c210005f5718c2100057f754c2100757c754c210005bf744c21006dbc744c2100b6be644c210006bd644c21006dbe740c210005bd740c210096be640c210006bd640c21004ede630c210006dd630c210005f6710c210005f5710c2100757e75c42100057d75c421007ebe64c4210006bd64c4210007b641c4210287b441c42100077a50c42102977850c4210005f576c4210006f576c42102977675c42100077575c4210287b664c4210007b564c421028ef762c421028ef562c421028f7752c421028f7552c421028fb742c421028fb542c421028fd732c421028fd532c42100077650c42102977450c4210005f976c4210006f976c42102977a75c42100077975c4210287ba64c4210007b964c42101adfb72c42101adf972c421028f7b52c421028f7952c421028fbb42c421028fb942c421028fdb32c421028fd932c4210007ba41c4210287b841c42100657e76d95100667e76d951001c7e76d95100067f64d95100067e64d95100067d64d95100067c64d95100073c64d95100063c64d95100057f72d95100057d72d95100067f62d95100067e62d95100067d62d95100067c62d95100076c62d95100066c62d95100073f42d95100073d42d95100075f32d95100075d32d95100073c41d95100077621d95100077521d95100657c70d95100077a20d95100077920d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067e43d95100067d43d95100067c43d95100067f72d95100047f72d95100067e72d95100067d72d95100047d72d95100067c72d95100067f42d95100063f42d95100067e42d95100067d42d95100063d42d95100067c42d95100067f32d95100065f32d95100067e32d95100067d32d95100065d32d95100067c32d95100067f71d95100667e71d95100667d71d95100667c71d95100067f41d95100067e41d95100067d41d95100067c41d95100063c41d95100067f21d95100067e21d95100067d21d95100067c21d95100067f70d95100667e70d951001c7e70d95100667d70d95100667c70d951001c7c70d95100067f40d95100067e40d95100067d40d95100067c40d95100067f20d95100067e20d95100067d20d95100067c20d95100667d10d951005dbe76d911005ebe76d9110014be76d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d9110
  | 7 => 0x9210006bf2159210006be2159210006bd2159210006bc215921006ebf7059210006be705921006ebd705921006ebc7059210006bf5059210006be5059210006bd5059210006bc50592100063c5059210006bf2059210006be2059210006bd2059210006bc205921006ebe10592100757e75d8e100057d75d8e1006dbe74d8e10005bd74d8e10006be64d8e10006bd64d8e10004ff75d8e1001cfe75d8e100067e75d8e1001c7e75d8e10004fd75d8e100067d75d8e100047d75d8e1001cfc75d8e10004ff74d8e10014fe74d8e10006be74d8e10014be74d8e10004fd74d8e10006bd74d8e10004bd74d8e10014fc74d8e10004ff72d8e1000cfe72d8e10004fd72d8e1000cfc72d8e100067f52d8e100067d52d8e10006bf42d8e10006bd42d8e10006df32d8e10006dd32d8e10006f571d8e10006bc41d8e10006fa70d8e100067c50d8e10004fd7698e100757e7598e100057d7598e10006be6498e10006bd6498e10006df6398e1004cff7658e10006be6458e10006bd6458e10004ff7558e1001cfe7558e10004fd7558e1001cfc7558e10004ff7458e10014fe7458e10004fd7458e10014fc7458e10006df7358e10006df5358e10006dc5358e10004ff7258e1000cfe7258e10004fd7258e1000cfc7258e100067f5258e100067d5258e10006bf4258e10006bd4258e10006df3258e10006dd3258e10006bc4158e100067c5058e1006dbe7418e10005bd7418e10006be6418e10006bd6418e1004ede6318e10006dd6318e10005bd769061005ebd769061005cbd76906102bebf6590610166be65906102bebd6590610166bc6590610006bf639061021ebe6390610006bd639061021ebc63906102c5bf72906102c5bd72906102b6bf629061015ebe62906102b6bd629061015ebc62906102b73f52906102b73d52906102b79f32906102b79d329061006dbe719061006fb6719061002ebe60906102bf3c50906102b7ba20906102b7b9209061006dbe74cc610005bd74cc61014ebe64cc610006bd64cc61004ede63cc610006dd63cc610005fa70cc610005f970cc610136be648c610006bd648c610006df638c61004edc638c61004cff764c6100057f754c6100757c754c610005bf744c61006dbc744c610126be644c610006bd644c61004ede634c610006dd634c610005fb704c610005f8704c6100757e750c6100057d750c610106be640c610006bd640c610006df630c61004edc630c61001e7e769421001e7d76942102a67f64942100f67e64942102a73e64942100f63e64942102a67d64942100073d64942100063d64942100f67c64942100067f63942101fe7e63942100067d63942101fe7c63942102ad7f72942102ad7d729421029e7f62942100ee7e629421029e7d62942100ee7c629421029f3f429421029f3d429421029f5
  | 8 => 0x6dd6318f10016be7690710016bd76907102e6bf6590710166be65907102e73e65907101663e65907102e6bd65907100073d65907100063d6590710166bc6590710006bf639071021ebe6390710006bd639071021ebc63907102f5bf72907102f5bd72907102eebf629071015ebe62907102eebd629071015ebc62907102ef3f52907102ef3d52907102ef9f32907102ef9d329071007dbe719071007fb671907102efb621907102efb52190710007ba7090710007b970907102e73c50907101567e65cc7100067d65cc71007dbe74cc710005bd74cc71004cfd768c71013e7e658c7100067d658c71004ede638c710006dd638c710005fa708c710005f9708c7100057f754c7100857c754c71012e7e654c7100067d654c710005bf744c71007dbc744c7100857e750c7100057d750c71010e7e650c7100067d650c71004ede630c710006dd630c710005fa700c710005f9700c7100057d76943100667d76943100647d76943102d67f64943100f67e64943102d67d64943100f67c64943100067f63943101fe7e63943100067d63943101fe7c63943102dd7f72943102dd7d72943102ce7f62943100ee7e62943102ce7d62943100ee7c62943102cf3f42943102cf3d42943102cf5f32943102cf5d32943100073e41943102d73c41943102cf7621943102cf7521943100857e70943100877a70943100857e75cc3100057d75cc3100e67e65cc3100067d65cc31004ede63cc310006dd63cc310005f671cc310005f571cc3100ce7e658c3100067d658c310006df638c31004edc638c31004cff764c3100057f754c3100857c754c3100be7e654c3100067d654c310005bf744c31007dbc744c31004ede634c310006dd634c310005f7714c310005f4714c31009e7e650c3100067d650c31007dbe740c310005bd740c310006df630c31004edc630c31006dbf765921006ebf7659210014bf7659210006bf6559210006be6559210006bd6559210006bc6559210005bf7259210005bd7259210006bf6259210006be6259210006bd6259210006bc62592100073f52592100073d52592100079f32592100079d32592100073c5059210007ba2059210007b92059210006bf7559210006be7559210006bd7559210006bc7559210006bf7359210006be7359210006bd7359210006bc7359210006bf5359210006be5359210006bd5359210006bc5359210006bf7259210004bf7259210006be7259210006bd7259210004bd7259210006bc7259210006bf52592100063f5259210006be5259210006bd52592100063d5259210006bc5259210006bf32592100069f3259210006be3259210006bd32592100069d3259210006bc325921006ebf715921006ebe7159210006bd715921006ebc7159210006bf5159210006be5159210006bd5159210006bc515
  | 9 => 0xc744c03030f9c744c0300959c744c03004f9e644c03004f9d644c03031ddf724c03031ddd724c03004edf624c030316dd624c0303175f524c0303175d524c0303179f424c0303179d424c030005dc714c0300079e414c03030f9c414c03004ddf704c03004fdb704c030306de604c03004fda604c0300075e504c0302ff5c504c0300857f76597100867f765971001c7f76597100067f64597100067e64597100067d64597100067c64597100057f72597100057d72597100067f62597100067e62597100067d62597100067c62597100073f42597100073d42597100075f32597100075d32597100073c41597100077621597100077521597100067f74597100067e74597100067d74597100067c74597100067f73597100067e73597100067d73597100067c73597100067f43597100067e43597100067d43597100067c43597100067f72597100047f72597100067e72597100067d72597100047d72597100067c72597100067f42597100063f42597100067e42597100067d42597100063d42597100067c42597100067f32597100065f32597100067e32597100067d32597100065d32597100067c32597100867f71597100067e71597100867d71597100867c71597100067f41597100067e41597100067d41597100067c41597100063c41597100067f21597100067e21597100067d21597100067c21597100867f70597100867e70597100067d70597100867c70597100067f40597100067e40597100067d40597100067c40597100067f20597100067e20597100067d20597100067c20597100867f10597100857e75d8f100057d75d8f100067e65d8f100067d65d8f1007dbe74d8f10005bd74d8f10004ff75d8f1001cfe75d8f100067e75d8f1001c7e75d8f10004fd75d8f100067d75d8f100047d75d8f1001cfc75d8f10004ff74d8f10014fe74d8f10006be74d8f10014be74d8f10004fd74d8f10006bd74d8f10004bd74d8f10014fc74d8f10004ff72d8f1000cfe72d8f10004fd72d8f1000cfc72d8f100067f52d8f100067d52d8f10006bf42d8f10006bd42d8f10006df32d8f10006dd32d8f10006f671d8f10006bc41d8f10006f970d8f100067c50d8f10004fd7698f100067e6598f100067d6598f1007dbe7498f10005bd7498f10006df6398f1004cff7658f100067e6558f100067d6558f10004ff7558f1001cfe7558f10004fd7558f1001cfc7558f10004ff7458f10014fe7458f10004fd7458f10014fc7458f10006df7358f10006df4358f10006dc4358f10004ff7258f1000cfe7258f10004fd7258f1000cfc7258f100067f5258f100067d5258f10006bf4258f10006bd4258f10006df3258f10006dd3258f10006bc4158f100067c5058f100857e7518f100057d7518f100067e6518f100067d6518f1004ede6318f10
  | 10 => 0x8430004fd759843001cfc7598430004ff7498430006bf7498430014fe7498430004fd7498430014fc7498430006bc7498430014bc7498430004ff729843000cfe7298430004fd729843000cfc72984300067f52984300067d5298430006bf4298430006bd429843004edf3298430006dd329843004ef67198430006f65198430006f55198430006bc419843004ef7319843004ef43198430006f62198430006f521984300067c5098430004ff75584300067f75584300047f755843001cfe7558430004fd755843001cfc75584300067c755843001c7c7558430004ff7458430006bf7458430004bf7458430014fe7458430004fd7458430014fc7458430006bc7458430014bc7458430004ff725843000cfe7258430004fd725843000cfc72584300067f52584300067d5258430006bf4258430006bd425843004edf3258430006dd325843004ef77158430006f65158430006f55158430006bc415843004ef7315843004edc315843004ef43158430006f62158430006f521584300067c505843021dbf7690430006bf7690430004bf769043021ebe769043021dbd7690430006bd7690430004bd769043021ebc769043021ebf6590430166be659043036ebd659043021ebc659043021f9e73904300079d739043021ebe6390430385bf7290430385bd729043021ebf629043015ebe629043037ebd629043015ebc629043037f3f529043037f3d529043021f9f329043037f9d3290430375be7190430097b67190430006be6190430006bd619043021f9c31904300c6be609043036f3c509043021f9f309043021fba309043021fb9309043004ddd768c430006dd768c43013ede658c43004edc658c430095de748c430095dc748c43004f9e648c43004f9d648c430365df728c430365dd728c43004edf628c43035edd628c43035f5f528c43035f5d528c43035f9f428c43035f9d428c43004dde718c43004fd6718c430006dd618c4300079e418c4303579c418c430005dd708c43034ede608c43004fda608c4303475c508c4300ce7f769403001e7e769403001e7d76940301fe7c76940301fe7f64940300f67e64940301ff3e64940300f63e649403032e7d64940301ff3d64940300063d64940301fe7c64940301ff5e73940300075d73940301fe7e639403032f5f43940301ff5c439403033d7f729403033d7d72940301fe7f62940300ee7e62940303367d62940300ee7c62940303373f42940303373d42940301ff5f32940303375d32940300067e61940300067d61940300073e419403032f3c41940300075e31940301ff5c31940303257e709403009f7a70940300ce7e60940301ff5f30940301ff7a30940301ff79309403004ddf764c030006df764c030004df764c0300075f754c0302ff5c754c0300079f744c030095de744c030095d
  | 11 => 0x6bc7690530004bc76905303bebf65905300073f65905300063f6590530166be65905303bebd6590530166bc65905303bf3c65905301663c65905303cdbf72905303cdbd72905303c6bf629053015ebe62905303c6bd629053015ebc62905303c73f52905303c73d52905303c79f32905303c79d32905300b5be71905300b7b67190530006bf6190530006bc61905303bf3c509053021fbb30905300067f658c53013e7c658c530006bf648c530136bc648c530006f7618c530006f4618c530005fa708c530005f9708c5300057f754c5300bd7c754c5300067f654c53012e7c654c530005bf744c5300b5bc744c530006bf644c530126bc644c530006f7614c530006f4614c530005fb704c530005f8704c5300057e76941300e67e76941300e47e76941303a67f64941300073f64941300063f64941300f67e64941303a67d64941300f67c64941303a73c64941300f63c64941303b57f72941303b57d72941303ae7f62941300ee7e62941303ae7d62941300ee7c62941303af3f42941303af3d42941303af5f32941303af5d32941300067f61941300067c61941300073e41941303a73c41941300bd7e70941300bf7a70941301ff7b30941300067f658c1300ce7c658c130006bf648c1300c6bc648c13004dfa708c13004efb608c1300075f658c13038f5c658c1300079f648c1300c6de648c1300c6dc648c1303979c648c1300c69c648c130305df728c130305dd728c13039edf628c13039edd628c13039f5f528c13039f5d528c13039f9f428c13039f9d428c130006dc618c1300079e418c1303979c418c13004dde708c13004edf608c13004fdb608c1300075e508c13038f5c508c130006bf7559030006be7559030006bd7559030006bc755903004ebf73590300969f735903004ebe735903004ebd735903004ebc735903004e9c735903004ebf535903004ebe535903004ebd535903004ebc5359030006bf7259030004bf7259030006be7259030006bd7259030004bd7259030006bc7259030006bf52590300063f5259030006be5259030006bd52590300063d5259030006bc525903004ebf325903004e9f325903004ebe325903004ebd32590300069d325903004ebc3259030006bf7159030006be7159030006bd7159030006bc7159030004bc7159030006bf5159030006be5159030006bd5159030006bc515903004ebf315903004ebe315903004ebd315903004ebc3159030006bf2159030006be2159030006bd2159030006bc2159030096bf7059030006be7059030096bd7059030096bc7059030006bf5059030006be5059030006bd5059030006bc50590300063c505903004ebf305903004ebe305903004ebd305903004ebc3059030006bf2059030006be2059030006bd2059030006bc2059030004ff759843001cfe759
  | 12 => 0xf65d91300073f65d91300063f65d9130006be65d9130006bd65d9130006bc65d91300073c65d91300063c65d9130005bf72d9130005bd72d9130006bf62d9130006be62d9130006bd62d9130006bc62d91300073f52d91300073d52d91300079f32d91300079d32d9130005be71d91300073c50d91303d7bb30d91303d7b830d9130006bf75d9130006be75d9130006bd75d9130006bc75d9130006bf73d91303d6be73d91300b6bd73d91303d6bc73d9130006bf53d91303d6be53d9130006bd53d91303d6bc53d9130006bf72d9130004bf72d9130006be72d9130006bd72d9130004bd72d9130006bc72d9130006bf52d91300063f52d9130006be52d9130006bd52d91300063d52d9130006bc52d91303d6bf32d91300069f32d9130006be32d9130006bd32d91300069d32d91303d6bc32d9130006bf71d9130006be71d9130004be71d9130006bd71d9130006bc71d9130006bf51d9130006be51d9130006bd51d9130006bc51d91303d6bf31d91303d6bc31d9130006bf21d9130006be21d9130006bd21d9130006bc21d91303d6bf70d91300b6be70d91300b6bd70d91300b6bc70d9130006bf50d9130006be50d9130006bd50d9130006bc50d91300063c50d91303d6bf30d91300b6bd30d91303d6bc30d9130006bf20d9130006be20d9130006bd20d9130006bc20d91300067f65d85300067c65d85300b5be74d8530005bd74d8530006bf64d8530006bc64d8530004ff75d853001cfe75d8530004fd75d853001cfc75d8530004ff74d8530014fe74d8530006be74d8530014be74d8530004fd74d8530006bd74d8530004bd74d8530014fc74d8530004ff72d853000cfe72d8530004fd72d853000cfc72d85300067f52d85300067d52d8530006bf42d8530006bd42d8530006df32d8530006dd32d8530006bc41d8530006f721d8530006f421d85300067c50d85300bd7e75985300057d75985300067f65985300067c65985300b5be7498530005bd7498530006bf6498530006bc6498530006f761985300057f75585300bd7c75585300067f65585300067c6558530005bf74585300b5bc7458530006bf6458530006bc6458530005ef72585300adec72585300067f65185300067c65185300b5bc7418530006bf6418530006bc6418530006f56118530004ff751853001cfe7518530004fd751853001cfc7518530004ff7418530006bf7418530014fe7418530004fd7418530014fc7418530006bc7418530014bc7418530004ff721853000cfe7218530004fd721853000cfc72185300067f52185300067d5218530006bf4218530006bd4218530006df3218530006dd3218530006bc4118530006f72118530006f421185300067c5018530006bf7690530005be7690530006be7690530004be7690530006bd7690530005bc7690530
  | 13 => 0xc6300057f754c6300cd7c754c630005bf744c6300c5bc744c630006f6614c630006f5614c630005fb704c630005f8704c630005dd760c63004edd760c63004f5e750c63004f5d750c63010ede650c63010edc650c6300c5de740c63004ddc740c63004ddf720c63042ddd720c630426df620c630426dd620c6304275f520c6304275d520c6304279f420c6304279d420c63004fd6710c630006dd610c6300079e410c63041f9c410c630005dd700c63004fda600c6304175c500c63001e7e769423001e7d76942303fe7f64942300f67e64942303fe7d64942300f67c64942300075e73942300075d73942303ff5f43942303ff5c439423040d7f729423040d7d72942304067f62942300ee7e62942304067d62942300ee7c62942304073f42942304073d42942304075f32942304075d32942300067e61942300067d61942300073e41942303ff3c41942300075e31942300075c31942300cd7e70942300cf7a70942301fe7e60942301ff7b3094230005dd76cc23004edd76cc23004f5e75cc23004f5d75cc2300c5de74cc23004ddc74cc23004ddf72cc2303f5dd72cc2303eedf62cc2303eedd62cc2303ef5f52cc2303ef5d52cc2303ef9f42cc2303ef9d42cc230005de71cc2300079e41cc2303e79c41cc23004fda60cc2300075e50cc2303dfda50cc2300075a50cc2303dfd950cc2303df5c50cc2300bd7e76d95300be7e76d953001c7e76d95300067f64d95300067e64d95300067d64d95300067c64d95300073c64d95300063c64d95300057f72d95300057d72d95300067f62d95300067e62d95300067d62d95300067c62d95300073f42d95300073d42d95300075f32d95300075d32d95300073c41d95300bd7c70d95301ff7b30d95301ff7830d95300067f74d95300067e74d95300067d74d95300067c74d95300067f73d95301fe7e73d95300be7d73d95301fe7c73d95300067f43d95301fe7e43d95300067d43d95301fe7c43d95300067f72d95300047f72d95300067e72d95300067d72d95300047d72d95300067c72d95300067f42d95300063f42d95300067e42d95300067d42d95300063d42d95300067c42d95301fe7f32d95300065f32d95300067e32d95300067d32d95300065d32d95301fe7c32d95300067f71d95300067e71d95300067d71d95300067c71d95300067f41d95300067e41d95300067d41d95300067c41d95300063c41d95301fe7f31d95301fe7c31d95300067f21d95300067e21d95300067d21d95300067c21d95301fe7f70d95300be7e70d95300be7d70d95300be7c70d95300067f40d95300067e40d95300067d40d95300067c40d95301fe7f30d95300be7d30d95301fe7c30d95300067f20d95300067e20d95300067d20d95300067c20d95300b5be76d91300b6be76d9130014be76d9130006b
  | 14 => 0x6bc415873004ef7315873004ef431587300067c5058730006bf769073021ebe7690730006bd769073021ebc769073021ebf6590730166be659073021f3e65907301663e659073047ebd659073021f3d65907300063d659073021ebc659073048dbf729073048dbd729073021ebf629073015ebe6290730486bd629073015ebc62907304873f52907304873d529073021f9f32907304879d3290730375be71907300dfb67190730006be6190730006bd619073047f3c50907301fd7d76943300be7d76943300bc7d76943301fe7f64943300f67e64943304667d64943301fe7c64943304757f72943304757d72943301fe7f62943300ee7e629433046e7d62943300ee7c629433046f3f429433046f3d42943301ff5f329433046f5d32943300067e61943300067d61943300073e41943304673c41943303257e70943300e77a70943300cd7e75d86300057d75d86300c5be74d8630005bd74d86300cd7e75986300057d7598630006f76198630004ff759863001cfe75986300067e759863001c7e7598630004fd75986300067d75986300047d759863001cfc7598630004ff7498630014fe7498630004fd7498630014fc7498630004ff729863000cfe7298630004fd729863000cfc72986300067f52986300067d5298630006bf4298630006bd4298630006df3298630006dd3298630006bc4198630006f62198630006f521986300067c5098630005bf74586300c5bc7458630004ff755863001cfe7558630004fd755863001cfc7558630004ff7458630006bf7458630004bf7458630014fe7458630004fd7458630014fc7458630006bc7458630014bc7458630004ff725863000cfe7258630004fd725863000cfc72586300067f52586300067d5258630006bf4258630006bd4258630006df3258630006dd3258630006bc4158630006f62158630006f521586300067c5058630006f56118630006bf7690630006be7690630006bd7690630006bc769063044ebf6590630166be659063044ebd6590630166bc65906300079e73906300079d73906300b6bd639063045dbf729063045dbd7290630456bf629063015ebe6290630456bd629063015ebc62906304573f52906304573d52906304579f32906304579d32906300c5be71906300c7b67190630006be6190630006bd619063021ebe609063044f3c509063021fbb3090630006f6618c630006f5618c630005fa708c630005f9708c63013ede658c63013edc658c6300c5de748c6300c5dc748c630445df728c630445dd728c63034edf628c63034edd628c63034f5f528c63034f5d528c63034f9f428c63034f9d428c63004dde718c630007d6618c630006dd618c630007d5618c6300079e418c63043f9c418c630007da708c630005dd708c630007d9708c63004ede608c6304375c508
  | 15 => 0xf744c6500053f744c6500f57e744c6504cd7d744c6500f57c744c6504b73c744c6500f53c744c6504c57f724c6500ed7e724c6504c57d724c6500ed7c724c6504be7f624c6504be7d624c6504bf3f424c6504bf3d424c6504bf5f324c6504bf5d324c6500073e414c6504b73c414c6501ff77314c6500075e314c6500057f704c6500057c704c65012e7e604c65012f7a604c6501fd7f760c6500057e760c6501fe7e760c6500047e760c6500057d760c6501fe7d760c6500047d760c6501fd7c760c6501fd7f740c6500f57e740c6504ad7d740c6501fd7c740c6501fd7e730c6501ff5e630c6500075d630c6501fd7f720c6500ed7e720c6504a57d720c6500ed7c720c65049e7f620c65049e7d620c65049f3f420c65049f3d420c6501ff5f320c65049f5d320c65013d7e710c6500073e410c6504973c410c6501ff5f310c6501ff76310c6500075d310c6501ff75310c6500057e700c6500057d700c6503267e600c65010f7a600c6500067f74597300067e74597300067d74597300067c745973004e7f735973004e7e735973004e7d735973004e7c735973004e7f435973004e7e435973004e7d435973004e7c43597300067f72597300047f72597300067e72597300067d72597300047d72597300067c72597300067f42597300063f42597300067e42597300067d42597300063d42597300067c425973004e7f325973004e5f325973004e7e325973004e7d32597300065d325973004e7c32597300067f71597300067e71597300067d71597300067c71597300067f41597300067e41597300067d41597300067c41597300063c415973004e7f315973004e7e315973004e7d315973004e7c31597300067f21597300067e21597300067d21597300067c21597300e67f70597300e67e70597300067d70597300e67c70597300067f40597300067e40597300067d40597300067c405973004e7f305973004e7e305973004e7d305973004e7c30597300067f20597300067e20597300067d20597300067c2059730004ff759873001cfe7598730004fd759873001cfc7598730004ff7498730014fe7498730004fd7498730014fc7498730004ff729873000cfe7298730004fd729873000cfc72987300067f52987300067d5298730006bf4298730006bd429873004edf3298730006dd329873004ef67198730006bc419873004ef7319873004ef431987300067c509873004edc3098730004ff755873001cfe7558730004fd755873001cfc7558730004ff7458730006bf7458730004bf7458730014fe7458730004fd7458730014fc7458730006bc7458730014bc7458730004ff725873000cfe7258730004fd725873000cfc72587300067f52587300067d5258730006bf4258730006bd425873004edf3258730006dd325873004ef77158730
  | 16 => 0x86500067d64586500057f73586501fd7c73586500067f63586500067d63586500057f72586500ed7e72586500057d72586500ed7c72586500067f62586500067d62586500073f42586500073d42586500075f32586500075d32586500077761586500067e61586500073c41586500077621586500077521586500667e60586500677a60586500057f74186500f57e74186500057d74186500f57c74186501fd7e73186500057d73186500067e63186500067c63186500057f72186500ed7e72186500057d72186500ed7c72186500067f62186500067d62186500073f42186500073d42186500075f32186500075d32186500857e71186500067f61186500077661186500067d61186500077561186500073c41186500757e70186500077a70186500757a70186500367e60186500377a60186500073f76906500073e76906500073d76906500073c76906500073f73906500073e73906500073d73906500073c73906500073f63906500073e63906500073d63906500073c63906505273f72906505253f72906505173e72906505273d72906505253d72906505173c72906505173f62906505163f62906505173e62906505173d62906505163d62906505173c62906505173f32906505171f32906505173e32906505173d32906505171d32906505173c32906500f73e71906500f53e71906500f73671906500073f61906500073e61906500073d61906500073c61906505173f21906505173e21906505173d21906505173c21906500073f70906500073e70906500073d70906500073c70906501673e609065051e3e60906501673a60906505173f20906505173e20906505173d20906505173c20906501fd7f76cc6500057e76cc6500057d76cc6501fd7c76cc6501fd7f74cc6500f57e74cc6501ff3e74cc6500f53e74cc65050d7d74cc6501ff3d74cc6500053d74cc6501fd7c74cc6501fd7f72cc6500ed7e72cc6505057d72cc6500ed7c72cc6504fe7f62cc6504fe7d62cc6504ff3f42cc6504ff3d42cc6501ff5f32cc6504ff5d32cc6500073e41cc6504f73c41cc6500057e70cc6500057d70cc6503267e60cc6501577a60cc6500057f768c6500057e768c6500057d768c6500057c768c6504ed7f748c6500f57e748c6504ed7d748c6500f57c748c65012d7d738c6500075e638c6500075d638c6504e57f728c6500ed7e728c6504e57d728c6500ed7c728c6504de7f628c6504de7d628c6504df3f428c6504df3d428c6504df5f328c6504df5d328c6501fd7e718c6500073e418c6504d73c418c6500075f318c6501ff77318c6500057e708c6500057d708c65013e7e608c65013f7a608c6500057f764c6500067f764c6500047f764c6500057e764c6500057d764c6500057c764c6500067c764c6500047c764c6504cd7f744c6500073
  | 17 => 0x67f62d8e500067d62d8e500073f42d8e500073d42d8e500075f32d8e500075d32d8e500057e71d8e500057d71d8e500073c41d8e5009d7e70d8e500077a70d8e5009d7a70d8e500ce7e60d8e500cf7a60d8e500bd7d7698e501fd7f7498e500f57e7498e500057d7498e501fd7c7498e500067f6498e500067d6498e501fe7f6398e500075f6398e500065f6398e501ff5e4398e500075d4398e501fd7f7298e500ed7e7298e500057d7298e500ed7c7298e500067f6298e500067d6298e500073f4298e500073d4298e501ff5f3298e500075d3298e500057e7198e500057d7198e500073c4198e503267e6098e500e77a6098e500057f7458e500073f7458e500053f7458e500f57e7458e500057d7458e500f57c7458e500073c7458e500f53c7458e500075f6358e501fe7e6358e500075e4358e500075d4358e500057f7258e500ed7e7258e500057d7258e500ed7c7258e500067f6258e500067d6258e500073f4258e500073d4258e500075f3258e500075d3258e500057f7158e500057c7158e500073c4158e500be7e6058e500bf7a6058e501fd7f7418e500f57e7418e501ff3e7418e500f53e7418e500057d7418e501ff3d7418e500053d7418e501fd7c7418e500067f6418e500067d6418e501fd7e7318e501fe7f6318e501ff5e6318e501fe7d6318e500075d6318e500065d6318e501fd7f7218e500ed7e7218e500057d7218e500ed7c7218e500067f6218e500067d6218e500073f4218e500073d4218e501ff5f3218e500075d3218e500057e7118e500057d7118e500073c4118e500cd7e7018e501ff7a7018e500cd7a7018e503267e6018e5009f7a6018e500057f74d86500f57e74d86500073e74d86500f53e74d86500057d74d86500073d74d86500053d74d86500f57c74d86500067f64d86500067d64d86501fd7e73d86500075e73d86500055e73d86500057d73d86500075d73d86500055d73d86500067f63d86500067d63d86500057f72d86500ed7e72d86500057d72d86500ed7c72d86500067f62d86500067d62d86500073f42d86500073d42d86500075f32d86500075d32d86500073c41d86500357e70d86500077a70d86500357a70d86500767e60d86500777a60d86500657d76986500057f74986500f57e74986500057d74986500f57c74986501fd7e73986500057d73986500067e63986500067c63986500057f72986500ed7e72986500057d72986500ed7c72986500067f62986500067d62986500073f42986500073d42986500075f32986500075d32986500067f61986500077761986500073c41986500077621986500077521986500867e60986500877a60986500057f74586500073f74586500053f74586500f57e74586500057d74586500f57c74586500073c74586500f53c74586500067f645
  | 18 => 0xc71594310067f41594310067e41594310067d41594310067c41594310063c415943104e7f315943104e7e315943104e7d315943104e7c31594310067f21594310067e21594310067d21594310067c21594310067f70594310067e70594310067d70594310067c70594310047c70594310067f40594310067e40594310067d40594310067c405943104e7f305943104e7e305943104e7d305943104e7c30594310067f20594310067e20594310067d20594310067c2059431136bf7690431016be7690431016bd769043121ebc769043121ebf6590431166be659043121f3e65904311663e6590431556bd659043121f3d65904310063d659043121ebc659043121f9e73904310079d739043121ebe63904315579f539043121f9c5390431565bf7290431565bd729043121ebf629043115ebe629043155ebd629043115ebc629043155f3f529043155f3d529043121f9f329043155f9d3290431375be7190431107b67190431136be619043121f9f319043121fb6319043121fb531904315573c509043104ddf764c431006df764c431004df764c4310075f754c43110dde754c43110ddc754c43152f5c754c43110d5c754c43104f5e654c43104f5d654c4310079f744c4315379c744c43154ddf724c43154ddd724c43104edf624c431546dd624c4315475f524c4315475d524c4315479f424c4315479d424c43104ddf714c43104fd7714c43153ede614c43104fd6614c43152fd6514c43152fd5514c4310079e414c4315379c414c431005dc704c43152f5c504c431004ff75980310067f759803101cfe7598031004fd759803101cfc75980310067c759803101c7c7598031004ff7498031014fe7498031004fd7498031014fc7498031004ff729803100cfe7298031004fd729803100cfc72980310067f52980310067d5298031006bf4298031006bd429803104edf3298031006dd3298031006be4198031006bc419803104efa70980310067c5098031006fa4098031006f9409803104efb309803104ef83098031006fa2098031006f92098031004ff75580310067f75580310047f755803101cfe7558031004fd755803101cfc75580310067c755803101c7c7558031004ff7458031006bf7458031004bf7458031014fe7458031004fd7458031014fc7458031006bc7458031014bc7458031004ff725803100cfe7258031004fd725803100cfc72580310067f52580310067d5258031006bf4258031006bd425803104edf3258031006dd3258031006be4158031006bc415803104efb70580310067c5058031006fa4058031006f9405803104efb305803104edc305803104ef83058031006fa2058031006f920580310057f74d8e500f57e74d8e500057d74d8e500f57c74d8e500057f72d8e500ed7e72d8e500057d72d8e500ed7c72d8e50
  | 19 => 0x53114cbe7690531586bf65905310073f65905310063f6590531166be6590531586bd6590531166bc65905315873c65905311663c6590531595bf7290531595bd729053158ebf629053115ebe629053158ebd629053115ebc629053158f3f529053158f3d529053158f9f329053158f9d3290531125be7190531127b6719053121fb731905315873c50905310067f658c53113e7c658c531006bf648c531136bc648c53104df6718c53104ef7618c5310075f658c53113ede658c53113edc658c53156f5c658c53113e5c658c5310079f648c5315779c648c53153ddf728c53153ddd728c53157edf628c53157edd628c53157f5f528c53157f5d528c53157f9f428c53157f9d428c53104dde718c53104edf618c53104fd7618c5310079e418c5315779c418c53156f5c508c53112d7e75d81310057d75d81310067f65d81310067c65d8131006bf64d8131006bc64d8131004ff75d813101cfe75d81310067e75d813101c7e75d8131004fd75d81310067d75d81310047d75d813101cfc75d8131004ff74d8131014fe74d8131004fd74d8131014fc74d8131004ff72d813100cfe72d8131004fd72d813100cfc72d81310067f52d81310067d52d8131006bf42d8131006bd42d8131006df32d8131006dd32d8131006be41d8131006bc41d81310067c50d8131006fb20d8131006f820d813112d7e75981310057d75981310067f65981310067c6598131125be7498131005bd7498131006bf6498131006bc6498131006fb60981310057f755813112d7c75581310067f65581310067c6558131005bf7458131125bc7458131006bf6458131006bc6458131005ef725813111dec725813112d7c75181310067f65181310067c6518131006bf6418131006bc6418131006f96018131004ff75181310067f751813101cfe7518131004fd751813101cfc75181310067c751813101c7c7518131004ff7418131014fe7418131004fd7418131014fc7418131004ff721813100cfe7218131004fd721813100cfc72181310067f52181310067d5218131006bf4218131006bd4218131006df3218131006dd3218131006be4118131006bc4118131006de31181310067c5018131006fb2018131006f820181310067f74594310067e74594310067d74594310067c745943104e7f735943110e5f735943104e7e735943104e7d735943104e7c735943104e5c735943104e7f435943104e7e435943104e7d435943104e7c43594310067f72594310047f72594310067e72594310067d72594310047d72594310067c72594310067f42594310063f42594310067e42594310067d42594310063d42594310067c425943104e7f325943104e5f325943104e7e325943104e7d32594310065d325943104e7c325943110e7f71594310067e715943110e7d715943110e7
  | 20 => 0x12d7e76d953112e7e76d953101c7e76d95310067f64d95310067e64d95310067d64d95310067c64d95310073c64d95310063c64d95310057f72d95310057d72d95310067f62d95310067e62d95310067d62d95310067c62d95310073f42d95310073d42d95310075f32d95310075d32d95310073c41d953159f7731d953159f7431d95310057e70d95310067f74d95310067e74d95310067d74d95310067c74d95310067f73d953159e7e73d953112e7d73d953159e7c73d95310067f43d953159e7e43d95310067d43d953159e7c43d95310067f72d95310047f72d95310067e72d95310067d72d95310047d72d95310067c72d95310067f42d95310063f42d95310067e42d95310067d42d95310063d42d95310067c42d953159e7f32d95310065f32d95310067e32d95310067d32d95310065d32d953159e7c32d953159e7f71d953112e7e71d953112e7d71d953112e7c71d95310067f41d95310067e41d95310067d41d95310067c41d95310063c41d953159e7f31d953112e7d31d953159e7c31d95310067f21d95310067e21d95310067d21d95310067c21d95310067f70d95310067e70d95310047e70d95310067d70d95310067c70d95310067f40d95310067e40d95310067d40d95310067c40d953159e7f30d953159e7c30d95310067f20d95310067e20d95310067d20d95310067c20d9531125be76d9131126be76d9131014be76d9131006bf65d91310073f65d91310063f65d9131006be65d9131006bd65d9131006bc65d91310073c65d91310063c65d9131005bf72d9131005bd72d9131006bf62d9131006be62d9131006bd62d9131006bc62d91310073f52d91310073d52d91310079f32d91310079d32d9131125bc71d913121fb731d913121fb431d91310073c50d9131006bf75d9131006be75d9131006bd75d9131006bc75d9131006bf73d913121ebe73d9131126bd73d913121ebc73d9131006bf53d913121ebe53d9131006bd53d913121ebc53d9131006bf72d9131004bf72d9131006be72d9131006bd72d9131004bd72d9131006bc72d9131006bf52d91310063f52d9131006be52d9131006bd52d91310063d52d9131006bc52d913121ebf32d91310069f32d9131006be32d9131006bd32d91310069d32d913121ebc32d913121ebf71d9131126be71d9131126bd71d9131126bc71d9131006bf51d9131006be51d9131006bd51d9131006bc51d913121ebf31d9131126bd31d913121ebc31d9131006bf21d9131006be21d9131006bd21d9131006bc21d9131006bf70d9131006be70d9131006bd70d9131006bc70d9131006bf50d9131006be50d9131006bd50d9131006bc50d91310063c50d913121ebf30d913121ebc30d9131006bf20d9131006be20d9131006bd20d9131006bc20d9131005be769053114ebe769
  | 21 => 0xc62907315e73f52907315e73d529073121f9f32907315e79d3290731375be719073114fb671907315df3c5090731004ff759833101cfe7598331004fd759833101cfc7598331004ff7498331014fe7498331004fd7498331014fc7498331004ff729833100cfe7298331004fd729833100cfc72983310067f52983310067d5298331006bf4298331006bd429833104edf3298331006dd3298331006be4198331006bc419833104edc319833104efa70983310067c509833104efb309833104ef83098331004ff75583310067f75583310047f755833101cfe7558331004fd755833101cfc75583310067c755833101c7c7558331004ff7458331014fe7458331004fd7458331014fc7458331004ff725833100cfe7258331004fd725833100cfc72583310067f52583310067d5258331006bf4258331006bd425833104edf3258331006dd3258331006be4158331006bc415833104efb70583310067c505833104efb305833104ef83058331016be7690631016bd76906315c6bf6590631166be65906315c6bd6590631166bc65906310079e73906310079d73906315c79f53906315c79c53906315d5bf72906315d5bd72906315cebf629063115ebe62906315cebd629063115ebc62906315cf3f52906315cf3d52906315cf9f32906315cf9d3290631135be7190631137b6719063121ebe619063121fb731906315c73c5090631005dd76cc63104edd76cc63113dde75cc63104ddc75cc63104f9e74cc63104f9d74cc63104ddf72cc6315bddd72cc6315b6df62cc6315b6dd62cc6315b75f52cc6315b75d52cc6315b79f42cc6315b79d42cc63104fd661cc6315a7d651cc6315a7d551cc6310079e41cc6315af9c41cc631005de70cc6315a75c50cc63113d7e75d82310057d75d8231135be74d8231005bd74d8231135be7498231005bd7498231006fb6098231004ff759823101cfe7598231004fd759823101cfc7598231004ff7498231014fe7498231006be7498231014be7498231004fd7498231006bd7498231004bd7498231014fc7498231004ff729823100cfe7298231004fd729823100cfc72982310067f52982310067d5298231006bf4298231006bd4298231006df3298231006dd3298231006be4198231006bc41982310067c5098231006fa2098231006f920982310057f755823113d7c7558231004ff75582310067f75582310047f755823101cfe7558231004fd755823101cfc75582310067c755823101c7c7558231004ff7458231014fe7458231004fd7458231014fc7458231004ff725823100cfe7258231004fd725823100cfc72582310067f52582310067d5258231006bf4258231006bd4258231006df3258231006dd3258231006be4158231006bc41582310067c5058231006fa2058231006f92058231006f96018231
  | 22 => 0x82410073d52d82410079f32d82410079d32d824102dbe71d8241007b671d824102db671d824107ebe61d824107fb661d82410073c50d824105dbd7698241005bf7598241165be7598241005bd7598241165bc759824121dbe7398241005bd7398241006be6398241006bc6398241005bf729824115dbe7298241005bd729824115dbc7298241006bf6298241006bd62982410073f52982410073d52982410079f32982410079d329824106ebe619824106fb66198241006bf6098241007bb60982410073c5098241007ba2098241007b92098241005bf75582410073f75582410053f7558241165be7558241005bd7558241165bc75582410073c75582411653c7558241006bf6558241006bd6558241005bf735824121dbc7358241006bf6358241006bd6358241005bf725824115dbe7258241005bd725824115dbc7258241006bf6258241006bd62582410073f52582410073d52582410079f32582410079d325824105ebe615824105fb66158241007bb6058241006be60582410073c5058241007ba2058241007b92058241005bf7518241165be7518241005bd7518241165bc751824121dbe7318241005bd7318241006be6318241006bc6318241005bf721824115dbe7218241005bd721824115dbc7218241006bf6218241006bd62182410073f52182410073d52182410079f32182410079d321824107dbe7118241007b6711824107db6711824102ebe611824102fb6611824106dbe7018241006bf6018241007ba6018241006bd6018241007b960182410073c5018241006bf7559331006be7559331006bd7559331006bc755933104ebf735933104ebe735933104ebd735933104ebc735933104ebf535933104ebe535933104ebd535933104ebc5359331006bf7259331004bf7259331006be7259331006bd7259331004bd7259331006bc7259331006bf52593310063f5259331006be5259331006bd52593310063d5259331006bc525933104ebf325933104e9f325933104ebe325933104ebd32593310069d325933104ebc325933114ebf715933114ebe7159331006bd715933114ebc7159331006bf5159331006be5159331006bd5159331006bc515933104ebf315933104ebe315933104ebd315933104ebc3159331006bf2159331006be2159331006bd2159331006bc2159331006bf7059331006be7059331006bd7059331006bc7059331006bf5059331006be5059331006bd5059331006bc50593310063c505933104ebf305933104ebe305933104ebd305933104ebc3059331006bf2059331006be2059331006bd2059331006bc205933121dbd7690731126bd7690731124bd769073121ebf6590731166be65907315debd659073121ebc65907315edbf72907315edbd729073121ebf629073115ebe62907315e6bd629073115eb
  | 23 => 0x100000000020000028000002007000802c00000400200040340170008004026007002803400c003007800000e002005804c006000000002400000700000080000020000000000000000800000000c001801c00000000b8004008005000000001200600800040040040008014002002001002c00800700400100040030000004004000002800002a0050008008000020001801c00400100000580020040000000006001005800001800000000100040070000008022010001803c00a002002800001200000000a4002001001800800a00c0070004000006000000c006003005bf75d8e41165be75d8e41005bd75d8e41165bc75d8e41005bf72d8e4115dbe72d8e41005bd72d8e4115dbc72d8e41006bf62d8e41006bd62d8e410073f52d8e410073d52d8e410079f32d8e410079d32d8e41105be71d8e41007b671d8e41105b671d8e41136be61d8e41137b661d8e41005be70d8e41005bd70d8e410073c50d8e41125bd7698e4121dbf7598e41165be7598e41005bd7598e4121dbc7598e41006bf6598e41006bd6598e4121ebf6398e410079f6398e410069f6398e4121f9e5398e410079d5398e4121dbf7298e4115dbe7298e41005bd7298e4115dbc7298e41006bf6298e41006bd6298e410073f5298e410073d5298e4121f9f3298e410079d3298e41376be6198e4114fb66198e41005be7098e41005bd7098e410073c5098e41005bf7558e410073f7558e410053f7558e41165be7558e41005bd7558e41165bc7558e410073c7558e411653c7558e410079f6358e4121ebe6358e410079e5358e410079d5358e41005bf7258e4115dbe7258e41005bd7258e4115dbc7258e41006bf6258e41006bd6258e410073f5258e410073d5258e410079f3258e410079d3258e41126be6158e41127b66158e41005bf7058e41005bc7058e410073c5058e4121dbf7518e41165be7518e4121f3e7518e411653e7518e41005bd7518e4121f3d7518e410053d7518e4121dbc7518e41006bf6518e41006bd6518e4121dbe7318e4121ebf6318e4121f9e6318e4121ebd6318e410079d6318e4121dbf7218e4115dbe7218e41005bd7218e4115dbc7218e41006bf6218e41006bd6218e410073f5218e410073d5218e4121f9f3218e410079d3218e41135be7118e4121fb67118e41135b67118e41376be6118e41107b66118e41005be7018e41005bd7018e410073c5018e41005bf75d8241165be75d82410073e75d82411653e75d8241005bd75d82410073d75d82410053d75d8241165bc75d8241006bf65d8241006bd65d824121dbe73d82410079e73d82410059e73d8241005bd73d82410079d73d82410059d73d8241006bf63d8241006bd63d8241005bf72d824115dbe72d8241005bd72d824115dbc72d8241006bf62d8241006bd62d82410073f52d
  | 24 => 0x5400c01e00000040060050028004012003000001000e0000000004008001007002800000c0098000002003002001c00a009003802400c0000090000002001002001000204a001001400a000001001c00200000400040040010000004018001001002800a0030030028006000000002000001200080000060040000000004006001001c0000000088000002000000800000600900100000360050018000000003002000000c001003802c01a001000800400200600000040000020008004002000000802400200500000000160000008004006003000800000c0000060000000006000801400a006001000000000000c00080080000010000000007008002001a00500d000000400000280000020030008024000017001000c00200200200600000040028004004000001000000e001006001000c001000000c0360070008000002002003001001a0030020004044000000002c004003001800000000000280000000010008008000004000800000401900180100000000020038000005001001802e0000048010016006002000000a0000060000006000001000002e00000100280020000010004028001005000c0020000020000018001004800000e00000000080020160008010004001000002800200000200080020180010000010001001800000c011006002c0040080000004004000003800c004002010800000a011002802c00c0000010000000000000801400800200180100000000000000000004000000400c000000002000c003006000001800400000080080080000000002009000800c000005000801400800500000080120090028014018005003000000800300200180000080118000000001002800402800601000040060010060024014006001002801e00000080000000060088000000002001802000000000a0020002012006800c000006001800c0080000000004002000001801c000000000000000000100080280220050000000016000007801000000000080040000040008010000009006812000200b000002c01a00500200000080010000014012000000000000200d004800000200000000000000010028008000004000800802000700080180300000000020004004004001000200500000040000060098000000001000800000000a001000400400e0018010008005001005000a01700280140180060000024000015000000c01400000000000020000000010000002004000400000e000801401e0010000024008001001000000c0060048000000000003001400200a002000403000100180000000010008000004005001802c004000000800400000300000000000090008000000002002800c000001001000000800700180300020030010020008002001804c0080020000030000003003800000600000000200080
  | 25 => 0x4a4d8a00023adf8c54026097805626db48a2c10000db805001b14329ee5c421b59947927dc84fca0a21b6df3de1bb67214ce800142000017421d400018827fa1cd7600000000000005006004c00800400500100080000000008022000000802400800b000800000600000380080040000080014000006000802c01200600200100020010018078004005002802800400000280140080040018008014009000002800400a003800001c00500f000001c00100c800001e00000080040000000000008002000000001c002002000800800200100000100020050010000004000004000c0000000050008010001000002001000200080080020010000000000002005000000a0020000004004009002000000000000400000020020010004022000000000400a004002000000000b0030008016000000801c0000000008038000009000004000200400000600000100008024002004000800c000001001003004a00000280000120030038000016007000002c002016000800000200000400000000040008020004001000800001000200000000000000010004022006000800402c00b000000400000000a8024000000000801c0000000008030006008003000400600c0048000010005000000400000000080bc014000001002001a0000058000000000000800400c006000801c01a001000800c014000006000003800a000000c00000200200380080030040000022002001001000a0000000004000011000000801a00500000000020010048094010002000000400c0020008000020000000800403600200100000040110008000000002001000000600b001003401400100000040040000000000004019002800000a004000000c01800200000000020010018014024001002002c004019000800c00400000d80040000000010000018003000001000200000000100080030030000000000002001c012004001800400c0030000000000000000000c000000000000c010006000000400000700000000020010008000002005008000c0000010010000000002004000c000001004000000000100080000120030008000014000004003c01c0030008008006002005800801401b000000000200200000000000020000010000005002000000e000000000000e000001801803800e000805c00e00c00780780000000000030002001001000000400100000140040030020000022016000000800c0030008000014003000800000600b003001400a007007800c0180000008000002003001804800000e000000000e007003800004200000180000000010020008000000000000000e01d0018000000004000800c01e002003000800400000080000060020038014008005000000000001d000000000000000380000000010010000004003004800400a0000028
  | 26 => 0x3a3151cc849813ab80000002a0000000078473900000000007cb0000000c727bc32b80000000000002295ce400058eaeb58fc0003a08dd41ba0007212ab83c23787148000000af600000016ccbeb000070034088100014350208b63aa9f0400029f0001b38000c690be800000000000000011f49b731e3c3c000f3e2ed800146aa081d80000d1a14049e8000000fc74d38c188743ec078ae2cb30e5b38a01d1b1000000002a098eb6337e87d16d421d000163400000073e00001febd033c800000000000029e81300007638bb070e1bf0612e1000000000007b44c6c514d735202f03260001a0800000000000004380000d7b3cc0009132660000000b8e23a9764b260006ff0ae01ca55c7a09364a180003bab681a2e46f3bb85b400003f53f0074fc4bf94c9bee96be0006238d99a4c0007ae800181c00000000000008e5152b74df1a0000000ca4d5e7f86460e040008347a5000000000000013ec8d2db70002ab40000006748000000331226106949a0000000001a4476517c2b7cbcc000031af315460004cc0a11acc0000003089e760000000000f545af4a8a8c42b8f5353781c976203945482e437a87c000000095000079a24642ac0000000001ee400053c243c55ac5000000013a00001e00c0c000ae558ca108000f2100038907a40653101f792d2fcb1482d883ee000348a28573c0006bb800086cdcf3330000886000000260dde839058d8000b8e000165b8b800000000000005dcefb2bc087c6d646e633183458a3ea752bac89c85614739e68da05152963a350721ef00505f17fa0000002a05de4d900002d3800000000000000004e946aaf28ba600000019f5248a764cd80000007ac02a000000000000000010c60000001259594d1821f3844912b317480a61a1686434a3b8535828672709d563c88544f00000003f4000000000068b6cd299d7ae7276820000d5adb12e1b3ac00000000000000000000002028000ab41398001c28de53fe3254fc00007ea253021e5f05b60001bbc8444629ad926449c1a98dc80005870b0a7a91f600261b8000f040000001cbcfd400000039cc0009fa1bb0bc951cbc5214b54deb8f0b15d3a51df867400012e5ef667a069aba41e04f0000390cd96ac700031e0f9e93700488b800000000029d4000363618800000014800027c0e14d42728a3c4b3413167d854c066000000177c97690353916e46409502ba06dc00066a0140d35b84000612180c000da90d718606ae000000089d6560757cfb885c7a9554b12891a5a8cc5fab36db5ac4a73b8904adc129451a26076ea91757aa800000000000a000000003f88000000a3f7243339d1664d00015080009925ae29c1cf454500000007c0d8b032000037400000038c18c80006920000896ef54ef00004d027f2f49984000e9617b8d040000000c88001
  | 27 => 0x25ae765ee0f891bc12c45a9c8c000000723a04c00071523338c8c1e27b0002af4d7c00000000013820e3497306858c0001c02081cbedbc62b875c000f5813d34092ca0000001d2000000000035f481a37e0000000000d5e521800000055200017fce5a06b25317c843482c4532ebc1a208f0003b09e72a054fe21ac3ce00020997d12f6ce326e2e9972248402d000000070f0000000000672570018800000000000000000006cc2ee0000a5109380000000000000000000984702969c1f21840000fb80000000000000000df44411f6d05a000000000066ea2600034f40006ac74ebefcf76f91000052855c76216682ecc144d1558b6c095839631f12343c40070000990a26d682b600000002d1547b164d461c16010f0545c000000187c000a7100018b06600000002618fd60002568000c2200032b1350916c4d0000e74ea4c7645008dc7a2bfb77ebad00000e21c4936dc120000c780013142be00000006900005d9000075600054cb3980540001540001a0ef290000000cca00000032b04fa00000000000000121c40000ff217f0000001d9a0002838c1122aed56d536254ca00044180007ce0000d32ffcdccb676890000000e7152b00009840000001ca8000cdd0001dd8000d2f00000018fe0003063c8c7300001150000000f225f38a702169c556f0000000d9c7490509a9865e0201a706549410ef18bc1929496e73f04fb8a9d317301800076d0002dec6243fc0003a28bc600000000000009e32fca15488abf3221000000059c60280014f6000705958005e21e477800000020800013140008ea0000000000ba0000000120a00031b8000000000000189800000036babf8fe69af58928ec00001444b8000000419515a548e0889b3fab989928bc70002770000bba2f0b9d5a3a69f47c000094000000033000006eb7830484000dea00039b800000000000000002fd00000000000000000000850455000252c00046d36aa88000000000000018b4d9200000000000002f3ab400008ae0002175be2bb9067a01d7ee0000003804000ae230806e0000b490ff2bb000000000001a80003eb520af54a02cef0d12a519740000002791dce2297b78a0d4bcf7621088bc000000150acb4ea600074e3688000f3800010602aef6a1252184d320003e40000f4000000037480000000000000098ca233b8a89c4a00000038582360000002f81f1c3e47ab2b9d2e0000350914dab2aee48b8dfc0000003a7a148750a095609b30d8c0e15643a3cfceb1c257be94fdcc4b03c89e40004b675ba49de40acc15baf046e66b97532889cac84d00025e937e00071580018bad29781a248000b55000035c0000006be35ed7d0ef636236bc00000077700003a07930000001aba8ed0b50000000c2b48200001086e10002b8d73432c1928000b1c0000002831376000
  | 28 => 0x63680000003ef552000044600070393e000005c137b14c40cb447b19e6cbdc000614af590525c4107b48400085b635ba1c0000000001240bee4b25be85e9f2e0ca00000000000006543e40876aed1ef2fbc06a9365b980b0ae093f1d990b000079000c3171d863c30001678f48d46079800133e010481000000065866284a14fef0949508d01d292f00005c54c0197000304816afb712d800123a0002c131a00000000c300018540002b4a86810e0000000001aa4ea12523139f7833223618c46700ae000000000076300006780000000001a1c346c974ac800197200001f00000000000002a6c000000000257c0000f759b1f48228e1a00000000001033a50000b62000000142c7c60000000eb8000a11000048c0009950002e8882e05f000039982c00005c0738bb861e6bab2cc70498d31d0001b764b400023080000002642b856340774f28be8000df022327b000058154f80000006fa44cbf5400000000039600000007b68000aa22f07780c2800000000012942d838e16d2005b9a606052abac00000042a0000b6a0d406e1bc5adeab00001644c4e1fd63198684f85893780000036856000000143c0000000b38abe9780000ca0000c0c0001aa0000a93513ad1cde641b205063422cd70453b81028cad70000000000bd100000003280003962a9800000052c89c5450dc62d100005e25090158a1cbd8ecf00330619c457b0928000de80000418034000000000000192ca073240000000b0c0001ce8f6400072580001da000000000168a09f00000000000000001859542b4b00000000000262d48955deeadb6b50b40376ced0fb0a8d34600043dbd342fc235370000000076f0001c0026a10d7841b7c0000000000db0c3ac3271b069d4467ec6b72d5d6b40005249619a9c000176aa610243144273c053de322000000131600023007b9aec5fb7d119182f6000000000019a0c42772d0000000050e3020000bfc35a8000000ec40000000a6866f18fa088b9af7367f8b893f6742083b5b4000105000000000009d0000000d3600012700000007fa00000000000371db00000000004b693851e858459094f5f42000000217800078858019319caa500001cc40000001eb071800071e00000006e83d500000000000000000000000196232146c77000050d95acfc830c09b8001d26b1f68f2d0dc30ddf16e05813da8905df9dd06040002e41c48000a1500000000004a7418800041c000000000051800047438d4000db600000018e8181000000092e3000000001a2a000000000000000022c81e1674c4f0000000f627966cab290d540004f41eb9702bda2b923c0000f6c5d0b3c117249400000000009e1116aeac00000000000000b6000238835400000077fba6c0002850000001750d87455830d2347063888001c3e47700017ac000859000000
  | 29 => 0x70cb889d00025b9c80000459b0b4f3ca906500000000b8060500000000000001525bdc0000001138894b3d7c0000000010e0000bd800000000000000007973da00017e40e422912f0fa092824eb35c0004ea036aa101eaa7d0fa819c9e259f60e0000d860002841460dbc0000000001a4e0006abaf38b6697c3811ae1a78a44000000058e0001e7a435b7af4e46b31583cc35b4349650000b973dd3f4cbb44cd49a2688aa626d0139eaccc6b15744945885e00047e800014e00000000000000000a6ad655ea2703e51d5955202e561baf044a5bb64d21d0fd20000002774bc425840e1c14a60e63000394c0005267163ead190b6400000000000004ef9b8c0000001e38001e22f2710c1af40003c80000f2dd82000000000083e7f015e3785244df95a89d701f418352f8b3cb2ec2c5ca025db1c0c63e011ecd1c68366c9b487b81395b6a3fd5b226232f84cc72a66267896b495660942e057ded0ca65c90000ae27e3000000000000019b098400045c000000000062b41f80000004b00109d85be400063919f00000000000000196000000000000021700007c800000000000000003ce608800069ce0856e80000000006d58e100001d300020dc0e600000027e4c086c96f614a0000efa000358cb967ad60d82200000db5902319eae6e57d91ed9cb80007df39a0000011213000158a00000017000003831e325506ac00033016c00002112381bf91fc3d00003b1800000062a2cb0a5e0002310001caa6f5779a0095a671677119900001f16aa0c9c56831b755be9c9320000000b6d04a3c550026c5efabd479421055788236a4b7a5352de809f1e1d45ea9c21121e95eedf610a8b65fa029537497911aec8145c32f5e3a4be45125c81dcc6e27d3244b1ef864f90d50000a4f6720f9984000000015693cc0006663b5808e0003c18000016b7f04300015560000003c1c000bc000000011a20000000000af20000000468000000000000000000000034d800000000010ccd3c00005e80000f4f470000a480000007b12b599be1490a29c7cc860000000d083e0d0f0003d50a6a00000032e0f3e8880dcb630bb0b8363b80003aa1597a628b400000000036b8cf01bc000287c2ce0000000000000b5e145be900003867898000c76a290000001c4e669736be24000f2f00000000000005a40000000546500b881dc8b092138f845c800040b800000000052735f80000001a780000008ba4bfa8280060e02b1ade5dba95d01e15900003330000000f444320cd8030a90424695800006c2e33b3a2dd52a7335868ba4000000000348dbb03d700000011e6f36000000022e000000117de0000000029b87b60001dc800102200000009b000004a00012a84843942d29948c10e4f0000000492dca0002a5c0000000000fd4efc0000000774c54bcf541800147000
  | 30 => 0xa939fbe60da2dc45843c94b540000003800000da628c8000000b397871ef8000109359108d20e8b43ff80007f40006a6bb70000a867e707219f00490000000000147796000048607c04da7d400053a6990001294000489000107a31058736e535400046f89b80000002603c6c364bbb2630920f8e0003e32f259049105b29ff44d45320002229bb8b3741aa085d402af00022500005c20002691c2e7863be8000000f515672cd5df20001df0001b9600020200000000000003d84f600004e6adc800000000023dc00000075f2ff8738b3f0002f88000cd22279a3cdf8a462c2abcd7d200072d26a0aba20313488f9800a795fc2ea800031514e9ee1a700005d72d30368a74295902c2560003c7844918699a457a5bcd7894268e36940000004d6b71ddde00565b000109868661e85459889c63880000b9e7360000b8562619d7ec1d78b4c03d6b02aa1ca496c1e4be813a6000000076caaeeac00018c800005000003a8000fa37acbacc0004ce290b05400064f566bc5c51c4792ac0e78dbafc34e714748a29c23e98aa86b233a4341e453880b20001d99bded825779705e4c6134600000a6e7e8000390400000000000000000003dc80006f400032a80000000006c680019d8267000086503c00019cb8bc000eb87c13d49b7e8796591489d3e4e861b1b4c2aa17479207a4b68dfc0a0ae240aee7d357000107600007db6640001221f8000039432163012840344c31fe8001b260000579a5dc46c0700033c89ee33f0000cb5b98ccf406800000036222f2bf11ea39971a00006486400000000000f952451d619fc8f627eb450aac7c900000008fc000000383db929752af3b2c6dee02000000000000000000003fec0161d000000000039d8001ad60000000000000fcc00000006c00004a280a48b60002aaa0c9868b8c649bb8c000eaa273a119d3c2f4146b769f52b5270e8fcced658a494be308209a019f07615b42933d484d08d49a61ec0acc7ee51427e330400018a02ca2a1d044f317f8001cca00015b3480d483fb09d86a50960004622099a1c000641ae3c00000000000000000002971f5439600012b80000000001aa80000002eb442242186078436c0001e92de03530fa101e70976287b02ee5f500037ac000000000000131cdd11f28dc45ba000000137800038503337dc000e9500031e41de0002bfa4f187800051eb691378e8c5b580016700002239279cb2b873361e28f9a00000032953eede35818000dce4373862f90254c8d00005ac49a45423197f1a62b2a1be00004666fb000312035a000485865546e1b176a2234aded4500008400006850fd0000000a62045a14c000f2a3380001e62cd30dab610000b690001b34000a8b386800167c60e73c00011187515e695940000000000001ee0e491b4000164ae7060a2644ff634000026
  | 31 => 0x460a2a57c3c341244f40f29c7000064464f000003200000005a00000004e8b591c7619371fa968a881720803720534edb43f80019dc86014427f40004761260001e60ad2673aadd276000706b418456bec742a76d6ec0002b68000c020606bd25ac8a081505680018b075000032ec0002ca7880848a7c00012880000000000002a79898dfb0b212e109274e1c9800000077c4bb12380009d92729f45b50a96000000000000000000000000000000001a7e00000000000003bb00000019ac29900000000006d434512141260004e405300007c302a9950000f3c0b4b65da507d8435234c96e18764800019460000001095dfc00031134280001c90000001f500000000000c0a246452000077e4914e58ac109e15d000000101607e62496f165064e022b4cd7caac65ae9019e14d811cb982c38e5202e7358493e6751c58000a728b100009aca4a2cc0001b885c07a750bb0e0000ae85070000c5ae0a5a519cd8ea000393256ca62f8748e03adc32bfa312bd7d85e953202a929b660a32be000134a319432aba91165b81039efcd4a1f33bc0001f662000003cc8b462d770180016f02b212e350c12054e17783d8c480324139168b7c00000002b17a639b15a9e24e709cc000004c0000c000018cd62283e68632714b60421302bc502c00074b87800000004c032c55184077569744000961000143cba0102471bae89de29b1a5aacc61a9da0d228e85860000a830240003f200032f0828afd00000013aa7d66378aec47e9203aa2a28feee910000000000fd1000191c6ce000000000000043d61fad5183c05378f000000000006c000000084800006f82203cc0128cbcf66000400103ceb4a5525d23b9f803a7000000138004f38bafc0000b171bdab2c8705760003839b1eae4000165800050400000000005364cc80d09aaf60000000141e48c48303f40000ba670acc012c15b6b63e982140000003ac15928d400039d125a3a50002024d400000cc000154e0000000000470695069043094696318e800023c07b09e8000000c354d98db48fa0be6a380000000000000001386a2107e00012f252d00000010e40003a018d4000a18000000000097100015984260000000001bfa0855e2186c000ab24ab8000000182034bd9c00000000017a83c80000001e75d0871900033554720047bcbcb800084a01132d5ecc00000014cc000c444550000d2481f0000000a0c0bf7de84b8522a614682f8d0b4dd47ed07512ce5a00003e140006f600010540004c90000fe000000000000000000000000000000b60000000000087d3992ddc1a087e42f8aa45bec196478250000e7f6140481baec2613c1cf00001260001f5039a5240000001bc40001da1a4011200000000006980000608c4c000fb04df1e84000a920000000000000000192800070b0002b445bce
  | 32 => 0x58b0000b743921532f649522446632578c0efc45b0beec9ba0003bd800000000035d27cd5744ae00008c4a22000210000000050a00018a5bc80003ed000000069800000000000000000000496985526253400000056a80016ea24521a08140000200000a29c0c00062f0000000c701048001e7e000612bad4000343000219c30000016b35cc00032b0000001aac20d7d680e00000700180001c540711debc4974a58004d003c778000000291c0009ab5182f480486500002c056f457d00010c53a83772093cac000c847ba38cc00000047023f000022c60fab710aee151ef800000013c00000008f8ad416400000004d000012d57b66da0000465c78ab90002a0800072e055be68a9600053625f5f0687712f80015348f206d3f207fe42b64ebd9588054351e36c9e305120000d6161470162a8000b8a59200017a0000ddd37ba9080000005a08000000000037a258000305000305da0a34900001a1e8c90e11eaecd3c016e6581631eeed396078000a045cc11319240bad851ad03786ca728449a1c0e6a1520002cb8f846ea000000000000000039780000004dc18559ecbac2cca32800088e69aa748fb28be0000000000871734bbb513800000031e854811c7a12ab000000029d934807600037c86300005ab654a0d943a000000232dbea9771538001a326195ba0e7dabeb3c000135dbf4b325b884104a4a6d33d9045b80e1b5a30000000000753af0800000000000000000001d2091c000000000000000086c0000000d8a0443c71d1554a0002658000000b8227580003f00000000254090fb657d0001c6e0006b2815800000000000001fc5de000000086a000000347c5a68b21d613b07e2b237648000000bc6437aa252b4d9d3f28b504cacde00000014908780000000bac30f00013597da00005304d80000000000000f2a80c191800000086e0001f98000f140003980d60d0300004bc812a1619e211cbfc31e1b700002e00003a63d6800000074030e47ba48200031cc00076900039900007303f7ac612b80000000b0977af810003e48320c6a3d780000000000003c100004bf55d80000a200000035fcd760002800fe4000c210001c7550ab9004c80b435400029c00004087643a3baec00074b59395e90a03077a00000d34ece23a0588b2acc20af0670616b8a00024840004985ad89c8dd01651732510000e57467be6df3800000004609626176b896b0000465664b00cf0aae66a527248fe00000000000000005efb10800000000002843d60c70fe263c2ecc802ebb8b403e9f1360ab00edc7490003194eb6b8d67a2ef96480b04e3a8d06c80002c83da59c000016aab3db06448000206ce300007a800000000002e52631d6c0000002224bf40004b508503667a536426e89b030936e16200a4000000000160e000040b6b0e1c90a40a0
  | 33 => 0xb76400065b2b1273de188e6000247c0000000003ed0398bb56d199c59900000000000602000000000000000000014fcc707c418b304c00000075e8001628311544049000000039e80000000000002f212cc614000000038a79c42c000132c0004d0b7b4000c615cd8000000d4f76b94694aec41000075993e106000000000000000000000000000003035d10cd84043cf51601927e900005f60000cd000000000049296c9df075d2ee8ba99a00003e63c7c000db45b8168413800000002dc00000000036440000000d280005922970000eb567695822c00000000000001fb4000e385190001258000000000046c6800002a346fa67f781058cde4c8a000153184ed7968d0000000cfc00000000000000c280017dc07f7360000bec00000000000005272cdbe4dd44b9f5781b91f62000000147d93220a62f93c8db2faa20f0001c260002221d0d15a3ba48c1439a12c8675c9388000000000000000000056c27d0000017000000128639a00000004a6e4d00000000006d66973ba4264b4d76f37e1dbeebf55c3b990801ea2ea0290754f8455798d82ea401046002027472b50581050483fe5cc8cb848066d474b8480009562418fa58e252a3acbf3c000d5c7e2b1b0e6e83800033e44188ec1a830f9e2af4f78e3d217680ce28e0d44df09b97e11000000c9245639ecb8c77f5b73d10f0000019a3998e0e0005db800000000000000000000003af88ec1520000000000000031708145c00000017a8c6800000000011c80000001af053800000072a0000fbe000000322c88000067426d000037931e800176c23c4f13df85ca4614b03d2c00099e1103501dd6dc1484a960000b860001bb0e4414f5ee86259963d97cc8001a360000000000f4c9970003a38000f7c0002af80006bf78b093c00004e3899368f9c0000002518000000421800000000000022f4e68b2641780000000000002a89ab00001d12e144ba916089800000008d0000f2839e78c000236c000be126fadf9e7448852a281000018e2818001a20ac239f10c0d8ee310ec80013d263f000000119c65d074117550ed62597aaa991c5ef60e8000474af212c8000000000000000000000020180000007b70000000000000000000057e00073f124d0a20005d49104000bd80000474e48d6913300015f20004400c704722547bd3d78000c5258300000000000003f5c0008bc0002ad40006b70000001d900004638da45f800000020b8000000000000141a0005e1a1149fc97e337194585c8870000001b42d807cb0d8400049a5fa00000001e30002060000294000000140cf8f0003f2876420176d19f9074833605a1d8f460000000f518f8a3619d8e3c00038d6638000000eae512a61da108863b41e64cd0e990001205056d3779a9e60b165297968ea416c08a00000003a4a6312800011f2
  | 34 => 0x6b6800018097cc9741010001b86ecc00003e1ab60000003a05f5e000000077c0960001ae050d9ee44966d0ae40002c03611b3c00271a7ba8bcddd0b0503b00000005590000001c7c0007728001da27bd0003b65f140000000e292367a800032f81041d131189d099e0002e480014f84801e9a99000076c67512cc000000657207507889f7681219360d165910238cced41470ad3d4d2fb87e69f85eb6000000000199a0001a28001424000000000000000078d0c2041694749c23493fc77100000000000000000000ef438c00034000000007ec97549da0000000000d3a3440aa25380000001190c5c000f3351f0000e4a8e467ab6e80009e70002e902104a2633aef085c7704a795cd23c0000003889af06887cf18c0000d51358800000010167d29ac33e6ff0000000000b984eb80009ea7dd000000000000065680010c40bc2d413e5de21b646eb9740004925201c8000000000034940002c14a40ebc00080345d923c000a2c34637fd65281a6ba05609ec54f0cc98714e646702699d911eb0f1622199364d5553326250600002e90000740c045ce0000a945f80510d75c4c0005a11fc8c8a0004648001dd40006ea9849cd67945ca89f97d4a0266e3651428ca1706000000000000010a80002964c40d280005e55883984b6cb6f655b4a9c74000273352d17e9f65a81a88be24e065f8071dc0b5636520a15e8f946f9ab118c4d9b20b062c0000001d080580008dc657b44476a78b000291537ad50519bdc5d8064b21e02440b05102de996807427609c09dc0001c249d3d55bcecaa0308279ec80d66d3a4cc0005ed0000000ddc15a000249822200000000000000003eb8d4845000040716fc000000062800066a6005a9afd8f025f3599b8a126a1c30d08364000fd60002ad8ec080614f000100a0001b80178762afb7ceba9136c1ac0070f11c388e271cbb28cb27f461d8055d34c891b510e51b42563539d1190a93e643959d8661f97828b49f5c02300000001e40430000889a58a5d415356890e0000000000000e6a4f5ac092e647a0001c6c0000b46e28f699a200022b3511c8a2210003eb14a6cc3000000000000069f000150000019e8000ab657500032d00002e74e50858d02a5c2011da893616f0d80fd8448179354b878000000000000000025e000194caeefc969d1d3403c000000000000000000019040009ff7283bb000041d78cae8c81054d0001ed4818a6a758b08cb5c62826236593282826982364afc91126980016686ed6eb32604b4db5000160c08c35f7338001b0c7c55859c21a260000002df12c8bcb22698d1c8cdd04a00e8c1e800017c8e991344732ce9e3542655039498856b00b16cfa3605026967c42e7521800044a8af5efef450001a11c88bde23c0f3574e9011f6800016641c0001aac00000036015a8000abf0fd
  | 35 => 0x3b602e60000003db8e06e6f0d4039c3d01dc16c0000aa81664c10000000000000000000000000000014d011f064292c00000073c9a2429600000000000006ef000275800000000024c00000004fc392822ae985019de5182e836b38e45a0251e62290b4388c5b64d95a09940df7c5a4e5a68b9664417f41d81447691fd8154ea865ba5a0000931000000000000021fabfd9a8de64803a8c9c6c1000026d40001da000000124600079bbb4d19a0007a19ff8000c43037201010053c0001acc81c000000000035613023400000002fe3498a2468ce8667e80018f600023580008aea7700015053b03183b935c994e5b75f8800097a9906230ab0556e4c18736798fa66b35a2e4da1a07d2d20d1d256fb53b9833112281924a8001ed628f00034eca4
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x8be8750963040011790ea12c6080030fdd54258c106561e3aa84b182000c5f75cc963041938b8eb992c60800327dd33258c106464e3a664b1820018dc874c963040018beea992c60831f171d53258c100064fba264b1820c6c9c744c9630400199ee4992c6080022fa1c4158c100061fba882b1820c5c3c7510563040010fd0e282c6080030fdd05058c1051e1e3a0a0b182009c5e635d4630401393cc6ba0c60800237e1d6318c100062ebaac63182000c9d7458c630401399cc6b90c6080033358d7218c1014c5fc3ac72082000a3f8558e41040594790ab1c82080bb6c9c570904100043fc2aed988200387c855db31040070fd0bbb462080021f617768c4100145f426ed18820008bd84dda310404f4b90ab1c62080022fe11760c4100145e422ec1882009c5e635d431040434b90ab186208003175d5630c4100e43fc3ac72802000a3f8458e500403d47908b1ca0080022fe1176cc0100145e422ed980200387e85dda30040010fb0bbb4600800a2fa13768c0100045ec26ed1802018a9c8458e30040010ff0abb0600800e1f215760c01004e4f31ae81802012a9c8458c300400193ae8b1860080063d61a710c0100863abb2eb88020c49758794310040078f2ed28420080372e5d9748401061cdcc3c830802002cb976906100400196883bb220080031e14376440100065bbb4828802000c7b769411004001e64832822008307cc10650440100063a3aeec8802000cb474dd910040019c8e5bb220080031dd4b76440100063aa96ec8802000cb742dd9100400196a85bb2200800335ccb76440100066a996ec8802000c7450dd910040018eeedbaa20080bedc20375440100065bbb6e88802000cd776dcd10040019aeec39a2008003711c8734401000673bb6e488020c29768794110040018eeed2822008002dca1e5044010616b943ca08802000d73769411004001ce6ed2822008003ccdd2504401060f983a4a08802000f53739411004001ea0e72822008302dce0a5044010605b8c14a08802000f6372941100417fec0e528220082ff9cd8a50440105ff38b14a088020bff3342941100417fe628528220082ffd4cca50440105ffa8994a08802000b7185cc1100405d7650818220080036c10776440100063c3aeec8802000cb874dd910040019d0e5bb22008003ac10776440100063da96ec8802000c7952dd9100400197685bb220080032e50b76440100066d996ec8802000cd932dd9100400197083bb220080031eddb75440100079820eea8802000cbb76dd110040019b6edb9a2008003e410773440100066dbb0e68802000dc8721cd1004001f208239a20080033addb7244010007d020ee4880202ebb284dc510040016e30b30a20082fa6ea1e41440100065dbb482880202ebb281905100405d7650998a2008002dc6143144010
  | 1 => 0xf0fb2e60880021f61f65cc1100061f3aec99822000c3d75d9330440018bcebb1e6088003175d763cc110006373aec59822000c6d75d8b30440139a8c738e60880021fe15764c11001c3e42aec98220008bf845d9304400517908bb260880023be09764c11000c76412ec982200087e86dd53044001878c9baa60880ff1718f754c11000636316ea982206487e87d95304407f0f90fb2a60880030f1d3654c1100045f436e89822000c3f65dd13044001878cbba260881eb2718f744c11000656316e898220cf8be87d9130440f51790fb2260880030fdd7644c1100061e3aec89822000c5f75d8d30440018b8ebb1a608800327dd3634c1100064e3a6c69822000c6f75d8930440018d8ebb1260880032bdd3624c110006563a6c49822000ce462dc530440019aec638a608800339188714c1100145e424ec1822000c3e74d9430440251790cba060880030fd95740c1100061e32ae81822009c9c635d03044001958c4ba060880022fe1f640c11005c5ec3ec81822000c9e74d8c304400193ae9b1860880032b9d3620c11000656ba6c4182201087c865d71044001878c8bae20880031b18975c41100643ec3ecb8822000c3e75d93104400187aebb262088003179d763c41100062ebaec78822000c5e7518f10440018baea31e20880031b9d762c411000636baec58822000ec86218f10440a15750d20e20880030f9d3658411006c5e432e90822000c3f655d21044001878caba420880032b189748411005c5ec3ec90822000c9e74d8e104400193ae9b1c2088003279d063841100064eba0c70822000cae74d8a104400195ae9b1420880331d9db658411005e5b3b6c90822000cd676d8e10440139acec31c2088003b11886384110056733b6c508220cea768694210440038dce4a96c6080031b5c952d8c1000e5739285b182000cad7250b63040031bf0e996c608007339c932d8c1000666b9265b18200387e859c763040010fb0b38ec60800a2fa1270d8c100045ec24e1b18200387e87dd563040010fb05baac6080021fa037558c100045fc22eab1820028bc845d563040010fd0e3aac60800a2fa1f7458c100061fbaee8b182000c3c75dd1630400117b05ba2c6080022fa077458c100043fc2ae8b18200387c855d1630400117d0e3a2c6080030fdd47458c100061e3a8e8b182003c5c7594d63040071b90ea9ac60800b271d24358c100146e43a86b182002c9c7450d63040031b907b92c6080021fe157258c1001c3e42ae4b1820008bf845c9630400517908b92c6080023d2057258c100047c402e4b18200087e87d4963040070f90fa92c6080030fdd35258c1066e1e3a6a4b18200087e8754963040010f90ea92c6080030fdd15258c106661e3a2a4b1820008be87d0963040051790fa12c6080030fdd74258c1065e1e3ae84b182000
  | 2 => 0xf62905100074631ec520a2000caf87d8a414409f9590fb1482880038be1762905100071642ec520a2000e8f83d8a4144001d1907b14828834f2b9c762905100075338ec520a2000e2c50d8a4144005179093b662880030f9d365cc5100045e432e998a2000c3f655d33144001878caba662880272718d74cc51000656312e998a20008bf87d93314400117b0fb266288003279d363cc5100064eba6c798a2000cae74d8b314400195ae9b1662880273618e70cc5100043f436ea98a2000c3c64dd531441678b8c7baa62880031b18b754c5106943f43eca98a20b387c87d953144001878e9b2a62880022fa1b744c5100061fb2ee898a2000c3c65dd13144087938c7ba262880032b18b744c5103745f43ec898a20438bc87d91314400187eebb2262880030f1d7644c5100062fbaec698a2000c5c75d8d314400193ee9b1a6288003271d3634c51000637baec498a2000c6c75d89314400195ee9b1262880032b1d3624c51000674316e098a2000cdb631c131440019d0c4382628800e1f216760c51010c3e432ea18a2000c3c645d431440138b8c6ba862880031b189750c5100043fc3eca18a200c87d87d94314400187cebb2062880030f5d7640c5100062f3aec618a2000c5d75d8c31440018dcebb1062880031b5d7620c5100061e324ed2822000c6c629da504403d47d0db24a0880030f9db649411000716316c92822000a3f82d92504400147b05b24a0880030fdcb64941100061eb96c92822000e1f32d925044001c3a65b24a08807a8fa0764941100f51e40ec928220d1c3e70d925044001c74e1b24a0880fe97a1b63941100062f3b6c72822000e1f64d8e5044001c38c9b1ca0880039318b63941100052fc16c72822000a5d82d8e50440018bee5b1ca088003175cb63941100070fa16c72822000e1d42d8e5044001c3883b1ca088003179c363941100072d386c7282200087f8758e504400147f08b1ca08807a8f211639411000537c12c7282201da6c8258e50440014bd0c31ca088003179d863941100070fb20c72822000e1c6418e5044001c98c431ca0880fe97e0863941100052ec10c72822000c5f7218e50440018bae431ca08800387d0863941100070ea10c72822000e1c4118e50440c98bce031ca088003969c063941100ed37436c52822000c6e76d8a5044001c5ec9b14a0880038b193629411000727b1ec52822000e4c63d8a50440018df0fb14a0881331b21f629411000717c26c52822000e2c84d8a5044001c9f07b14a0880039320f62941100071620ec528220d0c6e70d8a5044001cd4e1b14a0881528fa1a41941102e61f3b4832822000e1f639065044001c38c720ca0880038bd8a41941105171631483282200387c859db30440010f90cbae60880030f19175cc11004e2e31aeb9822000c6c625d730440010f
  | 3 => 0xbb122000a6e871d762440018dd0e3aec4881329ba0075d891000717baee9b122000e2c75dd362441a755d03ba6c4880029ba1674d891000536c2ce9b122000aae849d3624400159d073a6c488002b360e74d891000537c2ae9b122000a6c855d3624400159f06ba6c488002b320d74d891000557438e9b122000cae871d36244001c5eea3a6c4880038b1d474d891027d57408e9b122000e2f549536244001c9eebb9ec488003931d773d891000747ba6e7b122000e8c74dcf62440014dd0b39ec4880029b61673d891000557424e7b122000aad849cf624400159d0739ec4880029be1573d89100053642ae7b122000aaf845cf624400155908b9ec488002b3a1c73d891000667438e7b122000e4f751cf6244001c98ea39ec488003a3dd073d8910007463a0e7b122000aae84d4f624400155b09a9ec48800393d4e53d89100053742e87b122000a6d85d0f6244001d1a8621ec488002aba1371d891000556c26e3b12202daea80dc7624400155d09a8ec488002ab61351d891000557c22a3b122000aac84547624400159f06a8ec488002b320d51d89100053742883b122000a6d85107624400155d0e20ec48834eab21c41d89100071742883b122000e2d851076244001c5eea20ec4880038b1d441d891000747b9883b122000e8c73107624409f55d0220ec4880029ba1770d891000536c2ee1b12202dae681dc3624400155d08286c488002ab61050d891000537438a1b1220d0a6c871436244001c5d08286c4880038b61050d891000717ba0a1b122000e2c741436244001c9ee6286c488003931cc50d891000716208a1b12204ca6e8014362440014dd0ba06c4880029b61740d891000537c2a81b122000a6c85503624400159f06a06c488002b320d40d89100061e32ced20a2000cac629da414405947d0db2c82880030f9db659051000716316cb20a2000a3f82d96414400147b05b2c82880030fdcb65905100061eb96cb20a2000e1f32d964144001c3a65b2c82883530f9c765905100071b38ecb20a20a3a3e80d96414408753d0db1c8288003279db63905100070fb2ec720a2000e1c65d8e4144001d18c5b1c8288002a7e0b63905100054ec16c720a2000c9f72d8e414400193ae5b1c828800387d4b63905100070ea96c720a2000c9e71d8e4144001d2ce3b1c82880038714363905100045fc3ac720a2000a3f8558e41440594790ab1c8288002abe09639051015d56412c720a2000a9e8618e414400193cec31c828800387d9463905100070e328c720a2000e8c6218e414408753f0431c8288002a760863905100064fb90c720a2000c9d7218e4144001c3ea431c82880038754863905103764f388c720a2000e967118e4144001c38a031c82880aeaba1b6290510006573b6c520a2000e2f65d8a4144001c58cbb148288003a3d8
  | 4 => 0x3440014bf0aa00c688002972154018d1004c6f43e4031a20008dd87c8063440014bd0b900c688002976172018d100054f4264031a2000a9d84c8063440014b90b100c68800297e152018d100052e42a4031a2000ad78148063440015a902900c68802637a1c2018d100046ec384031a2000a5e8508063440014bb0a100c688002a7a102018d100054ec204031a2000ad68108063440015ab02100c68800297e151018d100052e42a2031a2000a9f84440634400153908880c6880029ba1b75d8910006373b6ebb122000a6e861d762440018dcec3aec4880031b9db65d891000476c3ccbb122000a6e85997624400155d0932ec488002ab61265d89100056741ccbb122000acd8399762440011df0eb2ec488002abe1165d891000556422cbb122000acf83597624400159906b2ec4880029ba1865d8910006373b0cbb122000aae86dd3624400195cedba6c4880038bd9774d89100071632ee9b122000aae861d3624400195cec3a6c4880038bd9474d891000716328e9b122000cae76d936244001c5ecbb26c4880038b19764d891000717baec9b122000e2c75d9362440011db0f326c4880029ba1664d891000536c2cc9b122000aae84993624400159d07326c488002b360e64d891000477c3ac9b122000a6f8559362440014d90ab26c488002b3e0d64d89100056641ac9b122000aae86193624400195cec326c4880038bd9464d891000716328c9b122000e2f751936244001c58ea326c488002b3a1b73d8910006673b6e7b122000e4f65dcf6244001c98cbb9ec488003a3d9373d891000746326e7b122000ace861cf624400199cec39ec48800393d9473d891000726328e7b122000e8f641cf6244001d18c839ec488003339db63d891000727b2ec7b122000e4c65d8f6244001d1ec9b1ec488003a319363d891000727baec7b122000e4c75d8f6244001d1ee9b1ec488003a31d363d891000476c3cc7b122000a6e8598f62440014db0b31ec488002aba1263d891000556c24c7b122000ace8398f62440011df0eb1ec4880029be1563d89100053642ac7b122000aaf8458f624400155908b1ec488002b3a1863d8910006673b0c7b122000e4f6518f6244001c98ca31ec488003a3d9063d891000746320c7b122000e4f7518f6244001c98ea31ec488003a3dd063d8910007463a0c7b12200aae686dc7624400155d0c20ec48835b2b9d841d891000717b2883b122000e2c651076244001d1ec620ec488003a318c41d891005575436e1b122000a6e8614362441ab8dcec286c4880038bd9050d891000716320a1b122000e4f631436244001c98c6286c4883429ba0375d89100053742cebb122000aae849d7624400155b093aec488002b3a0e75d891000566c1cebb122000aaf845d7624400155908baec488002b3e0d75d89100056641ae
  | 5 => 0x80033361c6218d1000727428c431a2000e4d851886344001d1d08310c688003a36106218d1000762c08c431a2000ec98018863440014bd0da90c6880029721b5218d100062f3b6a431a2000e1f64d486344001c38c9a90c68800393d8b5218d1000726316a431a2000a5e8654863440014b90ca90c688003179d95218d100070fb22a431a2000e1c645486344001c9ec4a90c688003931895218d100054f4368431a2000a9c86d08634400193ceda10c68800387d974218d100070e32e8431a2000e8f62d086344001d18c5a10c688002a7a194218d100054e4328431a2000c9e765086344001c3ecaa10c688003871954218d1000747b128431a2000e8c62508634400153d0c208c68800387d944118d100070e3288231a2000e8c6210463440015ad0d108c688003b118a2118d10007623124231a2000a5e861406344001c3ec8280c688003871905018d1000726310a031a2000ada868806344001d90c5100c688003f08862018d10007643124031a2000e1f5495063440131bf04b90c68802733e097218d106ce2fb96a431a2000c5d72d4863440014bd01a90c68802637a1e5218d100046ec3ca431a20daa5d85948634400153d09290c688002a76125218d1000727c12a431a20dac5f7254863440018bae4a90c688002972015218d1004c6f438a431a20008dd8714863441b34bd0a290c688002a7a105218d100054ec20a431a20d7c9f72d08634400193ae5a10c68800387d4b4218d100070ea968431a2000a9e81d0863440131bd0f210c6880023761e4218d100052f42c8431a2000a5d8590863441b153b09210c688003a3e094218d106c64fb928431a2000c9d725086344001c3ea4a10c688003875494218d100054e40a8431a20098de8710863440011bb0e210c68800297a144218d100052ec288431a20d7a9e84108634400153d09a88c688002a76135118d1013c6fc3aa231a20098dc87544634400153f08a88c688002a72115118d100052f4288231a2000a5d851046344001c3d0a208c688003876144118d100054ec108231a206ec9f72104634400193ae4208c68800387d484118d100070ea908231a20098de87c8463440011bb0f908c68800297a172118d100052ec2e4231a2000a9e84c84634400153b09908c688002a72122118d100054fc224231a2000a9c8448463440015b700908c688002b62012118d1004c6f4384231a20008dd8708463440014bd0a108c688002976142118d100054f4204231a2000a9d8408463440015b500108c688002b66002118d100054f420a031a2000a9d841406344001c3d08280c688003876105018d100052ec10a031a2064c5f7214063440018bae4280c68800387d085018d100070ea10a031a2000e1c4114063440014bd0ba00c688002976174018d100c46fc3a8031a20098dc875006
  | 6 => 0x656426e4b1a2000ccf83dc963440010ff0ab92c68800e1f2157258d100045fc22e4b1a20028bc845c963440011bf06b92c6880023de057258d100047dc02e4b1a2000c6f751c963440018d8ea392c6880032bdd07258d10006563a0e4b1a2000ccf731c963440010fd0fa92c68800e1f21f5258d100061fba6a4b1a20cdc3c74d4963440018dee5a92c6880071b1cb5258d100043f43aa4b1a200087c87549634400187ee8a92c6883330f1d15258d1000637b92a4b1a2001c6c72549634400117d0fa12c68800a2f21f4258d100061fbae84b1a20cbc3c75d09634400195ee5a12c6880072b1cb4258d100045f43a84b1a20008bc87509634400187eeaa12c68832b0f1d54258d1000657b9284b1a2001cac7250963440011bd0f992c68800317dd73258d1064e2e3ae64b1a2000c9f74cc96344191938e9992c68800333dcb3258d1000e6639664b1a20018dc874c963440018beea992c68831f171d53258d100064fba264b1a20c6c9c744c9634400199ee4992c688007331c93258d100145f426e2b1a20008bd84dc563440019c8e5b8ac6880022fa1c4158d100061fba882b1a20c5c3c75105634400195ee420ac68835b2b1c84158d1001c3f42ee0b1a200087d85dc163440019d0e5b82c6880021fa1c5058d100061fba0a0b1a20a3c3c7414163440018dee4282c6883571b1c85058d100046fc3ac631a2000a5f8558c63440014b90ab18c688002a7e116318d100054e422c631a2000acf8258c634400159904b18c6880023760a7618d100062f3b6ca31a2000a5d82d9463440011bb0f328c688002a7a126518d100054ec24ca31a2000ace82994634400159b05328c68800237e1d6518d100054fc22ca31a2000a9c84594634400159f04b28c688002b32096518d100062f3b0ca31a2000a5d82194634400193cedb20c68800387d976418d100070e32ec831a2000a9d82d9063440011bb0f320c68800297a166418d100052ec2cc831a2000ace82990634400159b05320c68800237e1d6418d100052fc2ac831a2000a5c85590634400159f04b20c688002b32096418d100064f3b0c831a2000e1f651906344001c38ca320c688002a76086418d100046f436e431a2000c5f65dc863440018b8cbb90c68800327d937218d100064e326e431a2000c5f655c863440018b8cab90c68800327d917218d100064e322e431a20008df87d88634400199ae5b10c6880023761e6218d100052f42cc431a2000a5d85988634400153d09310c688002a76126218d100046fc3ac431a2000a5f8558863440014b90ab10c688002a7e116218d100054e422c431a20008dd8718863440014bd0a310c688002976146218d100054f420c431a2000a9d84188634400199ae4310c68800393d946218d1000726328c431a2000e8f641886344001d18c8310c68
  | 7 => 0x5d85c87634400153d0990ec688002a761321d8d100054e42443b1a2000a9f8448763440015390890ec68800237a1c21d8d100046ec3843b1a2000a5e8508763440014bb0a10ec688002a7a1021d8d100054ec2043b1a2000ada8008763440015b30010ec68800297a1770d8d100052ec2ee1b1a2000a9e84dc3634400153b09b86c68800297e1570d8d100052e42ae1b1a2000a9e84143634400153b08286c68800387a1050d8d100070ec20a1b1a2000a5d8214363440018bee4286c688003175c850d8d100070fa10a1b1a2000e1d421436344001c3882286c68800297a1740d8d100052ec2e81b1a20128df8750363440311b90ea06c68800297e1540d8d100052e42a81b1a20008de87c8363440011bb0f906c68800297a1720d8d100052ec2e41b1a2000a9e84c83634400153b09906c6880029721620d8d100052fc2a41b1a2000a5c8548363440011bd0e106c6880023761c20d8d100052f42841b1a2000a5d85083634400153d08106c688002a761020d8d100056b40841b1a2000ad58108363440138b8c6bacc6880030f9d36598d1000637396cb31a2000c3e7419663440018dce432cc6880030fd957498d100061e32ae931a2009c9c635d2634400187cebb24c6880030f5d76498d1000657396c931a2000c3e75192634400187aea324c6880032b9c86498d100062f3aec731a2000c5d75d8e634400193ce9b1cc688003275d36398d1000667396c731a2000c6f655ca63440018d8cab94c6880032bd917298d1000656322e531a2000ccf635ca6344013998c6b94c6880031b9d46298d1000636ba8c531a2000cae7418a634400195ae8314c68800e1fa1b7558d100043f43ecab1a2000c3c74d9563440018d8e5b2ac6880021fa1c6558d100061e3a0cab1a2000c6c72195634400517d0dba2c6880030fd977458d100061e32ee8b1a20008be87d91634400187eebb22c6880030f1d76458d1000656396c8b1a20008be87191634400187eea322c6880030f1d46458d1000656390c8b1a20018ee86dc963440018decbb92c6880031b1977258d1000657b26e4b1a2000cac64dc963440018deea312c6880031b1d46258d1000657ba0c4b1a2000cac7418963440010fb05baac68800e1fa037558d100045fc22eab1a20028bc845d563440011bf06baac6880023be097558d1000c76412eab1a2000c3f75dd16344001878ebba2c6880022f60b7458d100145f40ee8b1a200087f855d163440070f90aba2c68800237e0d7458d1000477c12e8b1a20018ec825d1634400187eea3a2c6880030f1d47458d100062fbaee6b1a2000c5c75dcd634400193ee9b9ac688003271d37358d1000637baee4b1a2000c6c75dc9634400195ee9b92c6880032b1d37258d1000667b9ee4b1a2000c6f85dc963440018d90bb92c6880032be137258d100
  | 8 => 0xe5b16c68800297a1662d8d100052ec2cc5b1a2000a9e8498b634400153b09316c68800297e1562d8d100052e42ac5b1a2000a9f8458b634400153908b16c68800297a1462d8d100052ec28c5b1a2000a9e8418b634400153b08316c688003335c862d8d1000727b28c5b1a2000e4c6518b6344001d1ec8316c688003a319062d8d1000666c38c5b1a2000e4e8518b6344001c9b0a316c688003a3a1062d8d1000746c20c5b1a2000ec58118b6344001d9300316c68800297a1b52d8d100052e436a5b1a2000e1f64d4b6344001c38c9a96c68800393d8b52d8d1000726316a5b1a2000a5e8654b63440014b90ca96c68800387d9152d8d100070e322a5b1a2000e4f6254b6344001c98c4a96c688002a7a1b42d8d100054e43685b1a2000e1f65d0b6344001c38cba16c688003a3d8b42d8d100074631685b1a2000a9e8650b63440015390ca16c68800387d9542d8d100070e32a85b1a2000e8f6250b6344001d18c4a16c688002a7a1841d8d100070fb2883b1a2000e1c651076344001d18c420ec688003b118a21d8d100052f430a1b1a2000e1f641436344001c38c8286c6880039318850d8d100076431441b1a2000fc2218836344001d90c4906c688003175d475d8d100054f420ebb1a2000a9d841d7634400193ee93a6c68800297a1474d8d100052ec28e9b1a2000e1f5495363440014bd0b396c6880029761672d8d100054f424e5b1a2000a9d849cb634400199f04b96c68800297a1472d8d100052ec28e5b1a2000a9e841cb634400153b08396c688002b5a0472d8d100056ac08e5b1a2000ada801cb63440015b300396c68800317dcb52d8d100062eb96a5b1a2000a5e80d4b63440011bd0f296c6880023761e52d8d100054f424a5b1a2000a9d8494b6344001c9f04a96c68800317dc952d8d100062eb92a5b1a2000a5c8054b63440011bd0e296c6880023761c52d8d100054f420a5b1a2000a9d8414b634400193ee5a16c688003275cb42d8d100070fa9685b1a2000e1d52d0b634400153d03a16c68800237a1e42d8d100046ec3c85b1a2000a5e8590b63440014bb0b216c688003a3e0942d8d100064fb9285b1a2000c9d7250b6344001c3ea4a16c6880038754942d8d100054e40a85b1a20008de8710b63440011bb0e216c68800297a1442d8d100052ec2885b1a2000a5e85dc763440014bb0bb8ec688002a7a1371d8d100054ec26e3b1a2000a9f845c7634400153908b8ec688002a7a1351d8d100054ec26a3b1a20218df87547634404f1b90ea8ec688002a7e1151d8d100054e422a3b1a2000a5e8510763440014bb0a20ec68800387a1441d8d100070ec2883b1a2000a9d82107634400193ee420ec688003275c841d8d100070fa9083b1a2000e1d5210763440011bd0f90ec6880023761f21d8d100052f42e43b1a2000a
  | 9 => 0x52d91100045ec38a5b2220dfa3e8514b644400153d06296c888002a760c52d91100064fb9665b222000c9d72ccb6444001c3ea5996c8880038754b32d91106b64f38e65b22202bc9c71ccb644400117d0f196c8880022f61e32d91100051f42c65b222000a3d858cb64441bd53b07196c888003a3e0932d91100064fb9265b222000c9d724cb6444001c3ea4996c8880038754932d91106b64f38a65b22202bc9c714cb644400117d0e196c8880022f61c32d91100051f42865b222000a3d850cb64441bb53d06196c8880baaea0371d91100045f43ea3b2220008bd87d47644418b17f0ea8ec8880b22f21d51d91100054fc1aa3b222000a9c83547644400117d0f90ec8880022f61f21d91100051f42e43b222000a3d85c87644400153d0790ec888002a760f21d91100145fc3c43b22202b8bc8788764441ad17f0e90ec8880ae2f21d21d91100045f43843b22200b8bd87087644400147d0a10ec8880028f61421d91100054f41843b222000a9d8308764440015750010ec888002ae60021d91100051f42ee1b222000a3d85dc3644400153d07b86c888002a760f70d91101755b40ee1b2220008be87143644401717b0e286c8880030fa1c50d91106e61ec38a1b222000a3d82143644400187ee4286c8880030f5c850d91100070f990a1b222000e1d32143644414787ce2286c88836e8fa0050d91100045f43e41b2220008bd87c83644400147d0b906c8880028f61720d91100054f41e41b222000a9d83c8364440014790b106c8880028fe1520d91100051e42a41b2220008be87083644401717b0e106c8880028fa1420d91100051ec2841b222000a9e83083644400153b06106c888002ada0420d91100055ac0841b222000c5d75d4f634400153d09a9ec688002a761353d8d1001e2e3aca7b1a20038df8754f63440014bd0ba1ec6880029761743d8d100146fc3a87b1a2002c9e7450f634400193ee821ec68800333dcb32d8d100052f42c65b1a2000a5d858cb634400153d09196c688002a761232d8d1000c6fc3a65b1a2000ccd724cb63440014bd0a196c6880029761432d8d100054f42065b1a2000a9d840cb63440014bb05b2ec688002a7a1265d8d100054ec24cbb1a2000ace82997634400159b0532ec688002a7e1165d8d100054e422cbb1a2000acf82597634400159904b2ec6880029760865d8d100070fb2ec9b1a2000e1c65d93634400153b05b26c68800297a1664d8d100052ec2cc9b1a2000ace82993634400159b05326c68800297e1564d8d100052e42ac9b1a2000acf82593634400159904b26c68800387d9464d8d100070e328c9b1a2000a9d8219363440018becbb96c6880031719772d8d100064fb26e5b1a2000c9c64dcb63440018becab96c6880031719572d8d100064fb22e5b1a2000c9c645cb634400199a
  | 10 => 0xb2a2000a5c8350365440010fd0f906ca880021f61f20d95100051f42641b2a2000a3d84c8365440014bd07906ca880029760f20d951001c3fc3c41b2a201d87c8788365441ab0ff0e906ca880761f21d20d95100043f43841b2a200c87d87083654400147d08106ca880028f61020d95100052f41841b2a2000a5d8308365440014ed02106ca880029d60420d95100061f3b6cbb222000a3d82d9764441c7878e3b2ec8880022f61e65d91100051f42ccbb222000a9e83997644400153b0732ec888002aba0a65d911000556c14cbb2220008bf87597644400153f06b2ec888002a720d65d911000557c12cbb222000aac82597644400147d0c32ec8880030f9d865d91100051ec10cbb2220c5c3e71197644400117d0db96c8880030fd9772d91100061e32ee5b222000c3f655cb6444001878cab96c88800a2fe1f62d911000656b96c5b2220008bd8798b644400147d0b316c8880028f61662d91100054f41cc5b222000a9d8398b644400117f0eb16c8880028fe1562d91100051e42ac5b222000a9f8358b644400153906b16c88802e2f61c62d91100051f428c5b222000a3d8518b644400153d06316c888002a760c62d911000656b90c5b222000e2f6518b6444001c58ca316c8880032b61c62d911000717428c5b222000e2d8518b6444001d1d06316c888003a360c62d911000752c08c5b222000ea98018b644400147d0da96c8880028f21b52d911066e1f3b6a5b222000e2f62d4b6444001c58c5a96c8880028fa1952d91100051e432a5b2220ccc3e7654b6444001c5ec4a96c8880038b18952d91100054f43665b2220c8c9e76ccb6444001c3ecb996c8880038719732d911000747b1665b222000e8c62ccb64440015390c996c88831b279d932d91100070fb2a65b222000e1c654cb6444001d1ec4996c888003a318932d91100075231443b222000a3e86143644414787cec286c8880038b18850d91100075431441b222000fa2218836444001d50c4906c8880030f5d475d91100064fb9ce7b222000a3f855cf64440014790ab9ec8880022fa1f53d91100045ec3ea7b222000e1f5394f64441ad17d03b96c8880022f61e72d91100051f42ce5b222000a3d859cb644400153d07396c888002a760e72d911000657c12e5b2220028bc815cb644400117d0e396c8880028fa1472d91100051ec28e5b222000a9e831cb644400153b06396c88838aada0472d91100055ac08e5b2220e1aba801cb644400157300396c8880030fdcb52d91100061eb96a5b2220d6c3e71d4b6444057878e3a96c8880028fa0352d91100045f43ca5b2220008bd8794b64441c147b0b296c888002a7a0e52d91100054ec1ca5b222000e2f8254b644400187ee4a96c8880030f5c952d91106b61f38aa5b22202bc3c7154b644400147900a96c8880022fa1c
  | 11 => 0x44001c58c8316ca880031b61c62d951000717420c5b2a2000e2d8418b6544001c9d06316ca880039360c62d951000732c08c5b2a2000e698018b654400147d0da16ca880028f21b42d951065e1f3b685b2a2000e2f62d0b6544001c58c5a16ca880028f21942d95106561f3b285b2a2000e2f6250b6544001c58c4a16ca8800297a1b32d951064e2f3b665b2a2000e1c64ccb6544001c9ec5996ca880039318b32d95100052e43265b2a20c7c5e764cb6544001c38c8996ca8800393d8932d95100072631265b2a2000a3e861076544001c58c420eca880039918a21d95100073231243b2a2000e68628836544001ec443106ca880039a18920d95100061eba0e9b2a2000a3f845cf654400147908b9eca88003175cc73d95100043f43e87b2a200087d87d0f6544001c3a8621eca883561fa0372d95100043ec3ce5b2a2000a3e849cb654400147b09396ca8800297a0e72d95100052ec1ce5b2a2000c6f825cb65440070f900b96ca880021fa1c72d95100051f420e5b2a2000a3d841cb65440014bd06396ca880029760c72d95107553b408e5b2a2000a75811cb65441d34f500396ca880029e60072d95100061fb9685b2a2000c3d72d0b654400147d03a16ca883570f9c342d95100ee1e38685b2a200087e8790b65440010fb0f216ca883a28f61242d95100052f41c85b2a2000a5d8390b6544001c5f04a16ca880030fdc942d95100061eb9285b2a2000a3c8150b65441ab87ce0a16ca880770f1c142d95100043f43885b2a200087d8710b65441cf47d08216ca8800297a0c42d95100052ec1885b2a2000c5f72ccb65440018bae5996ca8800387d0b32d95100070ea1665b2a20d5c5e70ccb654403b8b8e1996ca880021fa1e32d95100043ec3c65b2a2000a3e848cb654400147b09196ca8839a9760e32d951000727c1265b2a2000c5f724cb65440018bae4996ca8800387d0932d95100070ea1265b2a20d5c5e704cb654403b8b8e0996ca880021fa1c32d95100043ec3865b2a2000a3e840cb654400147b08196ca8839697a0c32d95100051f426e3b2a2000a3d84dc765440014bd07b8eca880029760f71d951017d3d406e3b2a200087e8710765440190fb0e20eca880030fa1c41d95107261ec3883b2a2000a3d82107654400187ee420eca880030f5c841d95100070f99083b2a2000e1d3210765440010fd0f90eca880021f61f21d95100051f42643b2a2000a3d84c8765440014bd0790eca880029760f21d95100051e42443b2a2000a3f8448765440014790890eca880021fa1c21d95100643ec3843b2a2000a3e84087654400147b0810eca8800297a0c21d95100052ec1843b2a2000a7a8008765440014f30010eca880be9da0770d95100043f43e81b2a200087d87d0365441470ff0ea06ca8807a1f21d40d95100052fc1a81
  | 12 => 0x30f5d574d8e100045fc12e9b1c200387e85dcb63840010fb0bb96c70800a2fa1372d8e100045ec26e5b1c200387f87d4b63840010fb0fa96c7083370f9d352d8e100061eba6a5b1c200087f8754b63840010fb0ea96c7083330f9d152d8e100061eba2a5b1c20028bf87d0b638400117b0fa16c70832f0f9d742d8e100061ebae85b1c20008bf8750b638400117b0ea16c70832b0f9d542d8e100061ebaa85b1c20c9c5e75ccb63840018baeb996c708323279d332d8e100064eba665b1c20018df874cb638418f8bcea996c708003175d532d8e106364f3a265b1c2000c9d744cb638400199ae4996c7080022f61c41d8e1062e1f3a883b1c2000c3d7510763840019e2e3386c70828f0f9d050d8e100061eba0a1b1c2000c3e75992638400187aeb324c7080030f9d56498e100061ebaac931c2000a5e85d8e63840014bd0bb9ac70800237a1f5358e100062fbaea6b1c20018dc874c9638400199ee4992c70800a2fe197418e100045ec3cc831c20008bf8759063840011bf0eb18c7080022f61f63906101651f42ec720c2000a3d85d8e418400117f0cba663080022fe1d64cc61013d2f42ec718c2000c3e64dd5318400117b0dba2630810e2fa1d644c6103745e43ac898c2000c3f755913184001878eab226308003171d5634c6100061f322ea18c2000c3e75590318400187aeab2063080023761f630c61010d2f42ec618c201ea3f86592508400147f04b24a1080028f60964942100061fb92c92842000c3d725925084001c3e64b24a108003874c9649421075e1f382c92842000e3a7059250840070fb0fb1ca10807a8fa1363942100051ec26c7284204ba3d86906508400187cc8bae61080030f9d564cc2100061ebaac99842000c3e64dd5308402d17b0dba261080362f21d644c2100061fbaac89842000c3c75591308400117f0cba061080022fe1d640c2100061f322eb8842000c3e75593108400187aeab262108003cc90650c42100065b322ed8842000c76755db10840018eaecbae21080032d5d964c421022cbac3ca18842000cba645db10840018f4eabb621080031e5d975c42100065cbb2c98842048ab98690710840010fb0f326ca8800297a0e64d95100052ec1cc9b2a2000a6e8299365440014db05326ca880021fe1d64d95100052fc1ac9b2a2000a5c8359365440014df04b26ca880029b20964d95100051ec10c9b2a200087e86dcb6544001878c9b96ca880030f19172d951001c3fc3ec5b2a2000c6d72d8b65440010fb0f316ca880028fa1262d95100051ec24c5b2a2000a5e8398b65440014bb07316ca880021fe1d62d95100051fc22c5b2a2000a3c8458b65440014bf06b16ca880029720d62d95100643ec38c5b2a2000a3e8418b654400147b08316ca8800297a0c62d95100052ec18c5b2a2000c6d7218b65
  | 13 => 0x64fbb664b2420c6c9f764c9648414787eec282c9080030fdd675592100054f41ceab242000a9d839d5648400147d0bb9ac9080028f61773592100051f42ce6b242000a3d859cd648400193ae639ac9080022fa1f53592100045ec3ea6b242000e1f5394d648400117b0f392c9080028fa1672592100051ec2ce4b242000a9e839c9648400153b07392c908002aea02725921079d5cc04e4b242000ab7815c964841e556902b92c9080032be0972592100065bc0ae4b242000cb4815c9648400117d0e392c9080028fa1472592100051ec28e4b242000a9e831c9648400153b06392c9080030fdcb52592100061eb96a4b242000a3e80d49648400117d0f292c9080022f61e525921078d1ec2ca4b242000a9e83949648400153b07292c9080038be0952592100061fb92a4b242000c3d72549648400147900a92c9080022fa1c52592100045ec38a4b2420f0a3e85149648400153d06292c908002a760c52592100064fb9664b242000c9d72cc96484001c3ea5992c9080038754b32592100045f43c64b2420008bd878c9648400147d0b192c9080028f616325921077d4ec1c64b242000e8f824c9648400193ee4992c908003275c932592100070fa9264b242000e1d524c9648400117d0e192c9080022f61c32592100051f42864b242000a3d850c964841dd53d06192c9080028fe1571592100051e42ae2b242000a9f835c5648400153906b8ac908002abe09715921000556412e2b2420edabb805c5648400117d0fa8ac9080022f61f51592100071ba8ca2b24202c8bf87545648418b1790ea8ac908002a7e0d51592100054e41aa2b2420008be87c85648400117b0f90ac9080028fa1721592100051ec2e42b242000a9e83c85648400153b0790ac9080032bdca215921015c5fc3a42b2420d68bc87485648401b17d0e10ac9080022f61c21592100051f42842b242000a3d85085648400153d0610ac908002a760c215921000657b9042b242000aba8008564840015730010ac9083b6ada0670592100045f438a0b2420008bd87141648400187d0e282c9080030f61c50592100051ec10a0b242000c3f72141648400187ae4282c90800387cc850592100070e990a0b2420eca3e80141648401b17d0f902c9080022f61f20592100051f42e40b242000a3d85c81648400153d07902c908002a760f20592100051e42c40b242000a3f8548164840014790a902c9080022fa1c20592100045ec3840b242000a3e85081648400147b0a102c908002a7a0c20592100054ec1840b242000ab681081648400156b02102c9080030f9d664d8e100061ebacc9b1c2000c3e75593638400187aeab26c70800a2fa1375d8e100045ec26ebb1c200087f825d763840070fd0bba6c7080021f61774d8e100061f3ace9b1c2000c3d759d3638400187ceaba6c708
  | 14 => 0xf8748165c41ab0f90e902cb880421fa1c20597100043ec3840b2e2000a3e8408165c400147b08102cb8800297a0c20597100052ec1840b2e2000c6f7208165c40014ed02102cb880029d60420597100073490040b2e2000c3e7499763c400187ce8b2ec7880030f99574d8f100061eb2ae9b1e20028be84dd763c400117b09baec7880021fe0975d8f1001c3f42ee9b1e200087d85dd363c400187ceb3a6c7880030f5d674d8f100061f3aae9b1e2000c3d755d363c400117f04ba6c78800e1fa1772d8f100043ec2ee5b1e20028be84dcb63c400117b09b96c78800e1fe1f52d8f100043ec3ea5b1e20cdc3e74d4b63c400187ae9a96c7880021fe1d52d8f100043ec3aa5b1e20ccc3e7454b63c400187ae8a96c78800a2fe1f42d8f100045ec3e85b1e20cbc3e75d0b63c400187aeba16c7880022fe1d42d8f100045ec3a85b1e20cac3e7550b63c400187aeaa16c788327179d732d8f100062ebae65b1e20c8c9e74ccb63c400193ae9996c78800637e1d32d8f1063e2f3aa65b1e2000c5d754cb63c418d93ce8996c788003275d132d8f1000666b9265b1e20c5c3e7510763c400187aea20ec7880033c9c570d8f100043ec38a1b1e20a3c3e7414363c400187ae8286c7880030f9d26598f100061f3a2cb31e2000c3e655d263c400187acaba4c788002a7a136398f100054f426e6b1e20008de87d0d63c400193ae821ac7880063721d3258f1000667b9264b1e200387f865d463c40010fb0f328c7880021fe1d6518f100046fc3ac631e202ca3f8659641c400147f04b2c83880028f60965907100061fb92cb20e2000c3d7259641c4001c3e64b2c8388003874c965907107ae1f38acb20e2000e367159641c400517b0fb1c83880b28fa1763907100051ec2ec720e2000c3e7459731c400187ccaba663880030f59574cc71012c3ec36ea98e201087c8759531c4001878e8b2a63880030f997744c7100061eb2ee898e200087f865d431c40010ff0eb2863880021f61f63943100f51f426c72862000a3d84d8e50c409d87aed20ca1880021fe1975cc3100043fc3acb9862018a9e84d8e30c40010fb0dbaa61880fe1fa1d654c3103243e43aca9862000c3c7459530c400187ccbba261880030f597744c3100064e3a2c69862000c3e7459430c400187ccaba061880030f595740c3100046ec3ec61862012a9e84d8c30c400117d0fb2ac908002a7a0f65592100054ec1ecab2420008be87195648400117f0cb92c9083d26d20572592100045f43ec4b24200d8be87989648400147d0b312c9080028f61662592100054f41cc4b242000a9d83989648400195ee5312c90800a2fa1d625921000657b92c4b2420008be87189648400147d0a312c9080028f61462592100054f418c4b242000a9d83189648419b87eeda92c9083330fdd9525921064
  | 15 => 0x7b22cb880029760f64597100043f438c8b2e200087f865c965c41fb2f100b92cb880021fa1f62597100843f43cc4b2e2000a3e8498965c400147b09312cb8800297a0e62597100052ec1cc4b2e2000c6f7298965c40070fd0eb12cb880031bdc962597100043f438c4b2e2000a3e8418965c400147b08312cb8800297a0c62597100052ec18c4b2e20cbc3f76d0965c419587eeca12cb8832717ddb325971063e2fbb264b2e20c5c3f7610565c4001cccc510acb880030fdd274597100052f41ce8b2e2000a5d839d165c400187ae83a2cb880028fa1373597100051ec26e6b2e2000a3e849cd65c400147b0939acb8800317dce73597100062eb98e6b2e200087e87d0d65c40010fb0fa1acb880038750c43597100043ec3ce4b2e2000a3e849c965c400147b09392cb8800297a0e72597100052ec1ce4b2e2000a76819c965c41f94eb03392cb880029ee0172597107dd3c402e4b2e2000c6f825c965c40018f700b92cb880031e20172597100043f438e4b2e2000a3e841c965c400147b08392cb8800297a0c72597100052ec18e4b2e2000c3f72d0965c400187ae5a12cb880028fa0742597100043f43c84b2e200087d8790965c41f547b09212cb8800297a0e42597100052ec1c84b2e2000e2f8250965c400187ee4a12cb880030f5c942597100051e40a84b2e200087e8710965c40010fb0e212cb883e68fa1042597100052f41884b2e2000a5d8310965c40018bee5992cb88003175cb32597100070fa1664b2e2000e1d42cc965c40010fd0f192cb880021f61e32597100051f42464b2e2000a3d848c965c41f14bb07192cb8800393e0932597100062fb9264b2e2000c5d724c965c4001c3e84992cb880038750932597100043f43864b2e200087d870c965c400147d08192cb880028f61032597107bd2f41864b2e2052a7a809c565c40010fd0e20acb880021f61c41597100061f43882b2e2000c3d8710565c400147b0420acb880030fdc841597100061eb9082b2e2000e1f3210565c4001c3a6420acb883da8fa0441597100843f43e42b2e200087d87c8565c400147d0990acb880028f61321597100052f41e42b2e2000a5d83c8565c40014790910acb880028fe1121597100051e42242b2e200087e8708565c40010fb0e10acb880028fa1021597100051ec2042b2e2000a5e8308565c40014bb0610acb880029ea0021597100053cc0042b2e2000a3f845c165c400147908b82cb8800297e0d70597100052e41ae0b2e2000a6f825c165c40014d904b82cb8814a9de0570597100043f43e80b2e200087d87d0165c403d0ff0ea02cb8828e1f21d40597100052fc1a80b2e2000a5c8350165c40010fd0f902cb880021f61f20597100051f42640b2e2000a3d84c8165c40014bd07902cb880029760f205971000637b9440b2e201d87
  | 16 => 0x19843000c7ac3c4330860a3c3c74142610c0070fd0fbaac2182cf171cf75584300043ec16eab0860b3c5f32dd5610c00117f08baac21800a2f211755843013c6fc1aeab0860098dc835d5610c1a58b8e63aac21800a2fa1f74584300061fbaee8b086000c3c75dd1610c087938e7ba2c2180022f60b745843021e4f996e8b08600087f855d1610c0070f90aba2c2180263720d74584300061fba8e8b086000c3c751d1610c0dd938e63a2c2180021fe15725843001c3e42ae4b0860008bf845c9610c00517908b92c2180263720d72584300043f43ea4b08600387c87d49610c00187ee9a92c2183370f1d352584300043f43aa4b08600087c87549610c00187ee8a92c2183330f1d152584300045f43e84b0860028bc87d09610c00187eeba12c21832f0f1d742584300045f43a84b0860008bc87509610c00187eeaa12c21832b0f1d542584300062fbaa64b0860c7c5c754c9610c00193ee8992c21831b271d1325843000667b9264b086003c7475945610c0131e90ea8ac21810e2fa1c41584300061fba882b0860c5c3c75105610c0ddd286220ac2180063d21d21584300043f438a0b086000c3f74141610c147878e8282c21810ea7a0f769043021e4f39eed2086000ab681dda410c08793d07bb482180022fe0b76904300045ec16ed2086000c3f52dda410c00187aa5bb4821810f27ccb76904300064e996ed208606e8be81dda410c00196d03bb482180030f14376904300051fc2aed208602ca3c855da410c00187f0abb482180030f21576904300045fc12ed20860008bd825da410c00187ea4bb482180030f549769043021e4f992ed2086000c9d325da410c00517902bb4821810f270c576904300061e282ed2086000c9f765ce410c00517f0f30c821810e2f21e61904303745fc3ac32086000a3f85586410c0594790ab0c821809e97215768c43013d2e42ac31886000a9d86906310c1fdc3f06b24a0180ff8720d64940301ff0f39ac92806000a3f82592500c00147b04b24a0180030fdc964940300061eb92c9280603fe1f32592500c001c3a64b24a0180028f20564940303261f382c92806000e3a70592500c07f8b8ecb9ca018196c721173940300070eb22e7280601ea3c84986500c0210ff0eb0ca0180028fe1161940300f51e422c32806000a3f86906500c00147b0d20ca018003171d7764c0300064e3a6ec9806000c9f84dd9300c00193909bb2601800237e0b764c0300046ec16ec9806000c5f52dd9300c0018baa5bb2601800327d0b764c0300064ea16ec9806000c9c41dd9300c0018b8a1bb2601800317ddb754c0300068e3a6ea98060cf99e87dd1300c00193eedba2601804a67210714c030004cf43c829806000c9f76905300c0c92bd0f282601800317dda504c03032e8e3a4a0980600087e87d9165c40014bd0
  | 17 => 0x2060d88bd879c9640c00147d0b392c8180028f616725903004d4f41ce4b206106a9d839c9640c20b53f06b92c818026a720d72590300064fb9ae4b2060d8c9c735c9640c00193f06b92c8183632720d725903000657c12e4b2060d8c9f325c9640c00117902b92c81835e2fa1c72590300051f428e4b206000a3d851c9640c01353d06392c81804aa760c72590308270fb9ea4b2060d9e1c73d49640c00187ee5a92c8180030f5cb52590306cf0f996a4b206000a3e80d49640c00117d0f292c8180022f61e52590306d51ec2ca4b206009a9e83949640c00153b07292c81840f87dcd52590306d70e39aa4b206000e2f82549640c00187ee4a92c8180030f5c952590306d70f992a4b206000a3c80549640c00117d0e292c8180022f61c52590306cd1f428a4b206009a9e83149640c00153b06292c81804aa7a1d32590300954e43a64b206009a9f824c9640c013d1f04992c81800327dc932590300064eb9264b206000e1f524c9640c001c3aa4992c818026a7a0e71590308154ec1ce2b206043c9c739c5640c00147f0ab8ac8180028f215715903080d4fc1ae2b206009a9c835c5640c00147d0a38ac8180028f61471590303764e398e2b206000c3e851c5640c00187b0a38ac8180022f60871590300061fa90e2b206000c3d521c5640c0dd93e6438ac818003274c871590300045f43ea2b2060008bd87d45640c00117f0ea8ac8180022f21d51590300054fc1aa2b206009a9c83545640c00117d0f90ac8180022f61f21590300051f42e42b206000a3d85c85640c01353d0790ac818002a760f21590300045e43c42b2060008bf87485640c0011790e90ac8180022fa1c21590300045ec3842b206000a3e85085640c00147b0a10ac818026a7a0c21590300054ec1842b206000aba80085640c0015730010ac818402a760e70590303d64e39ce0b206009a9e83941640c00153b07282c8180022fa1c50590300045ec38a0b206000c3e87141640c00187b0e282c8183ff87dcc50590303270e398a0b206000a3d82141640c00187ee4282c8180030f5c850590303270f990a0b206000e1d32141640c001878e2282c8180fe8fa0050590300945f43e40b2060008bd87c81640c00147d0b902c8180028f617205903004d4f41e40b206000a9d83c81640c0014790b102c8180028fe1520590300051e42a40b2060008be87081640c00117b0e102c8180028fa1420590300051ec2840b206009a9e83081640c00153b06102c818002ada0420590300055ac0840b2060008bf845d6610c00517908bacc21802637a0f74984303755b40ee93086043ab6811d2610c00117f08b94c21800a2f211729843066e1e3a6a530860ccc3c7454a610c00117d0fa14c21800a2f21f42984300045e43a8530860c6c9c744ca610c0131eb0f28cc218026b520d5
  | 18 => 0xc00187aebb24c2980030f9d464985300061eba8c930a600387e86dd5614c0010fd0fb2ac2980030f1d3655853000636396cab0a600087e87195614c001878e832ac2980031b1c865585300145f436e8b0a6000c3f65dd1614c001878cbba2c2980022fa1f64585300061fbaec8b0a6000c3c75d91614c001958e5b22c2980022fa1c64585300061fba8c8b0a6000c3c75191614c001958e4322c2980031bd9772585300063632ee4b0a6000caf64dc9614c001958c9b92c2980030f1d365185300061e3a0ca30a60008f787584614c0015c904b08c2980022fe1175185300145e422ea30a60098dc835d4614c00156d03ba0c298002ab60874185300055b408e830a60008bf845c8614c00517908b90c2983370f1d352185306661e3a2a430a60008be87d08614c0051790fa10c298002ada0742185300045e43a8430a6001cae72508614c00195ae4a10c298002ad20542185306464e3a66430a60c6c9c744c8614c0015ab07908c298002bc600211853051e1e3a0a030a602ca3e85dda414c00147b0bbb48298002a760f76905300055b40eed20a6000c3c659da414c00117f053b482980022f60a76905300061fa94ed20a6000c3d529da414c00193e653b48298003274ca76905300061e284ed20a6000a3f855da414c0594790abb482980022fa1876905300061e328ed20a6000ab6811da414c00117f043b482980022f60876905300061fa90ed20a6000c3d521da414c00193e643b48298003274c876905300065b408ed20a6000c3c501da414c05947d0db2c82980030f9db65905300061e3b6cb20a6000a3f82d96414c00147b05b2c82980030fdcb65905300061eb96cb20a6000e1f32d96414c001c3a65b2c82984370f9c765905300071b38ecb20a600087e86dd5314c001878c9baa62980021fa1f654c5300061e3a6ca98a60008be86dd1314c00187ecbba262980030f197744c5300045f43ec898a6000c3f75d91314c001878ebb2262980030f19276941300f51f436c92826000c3e76d92504c00147f05b24a0980028f60b64941300061fb96c92826000c3d72d92504c001c3e65b24a098003874cb64941300051f40ec9282610cc3e70d92504c001c74e1b24a09807a8fa1361941300051ec26c3282601ea3c84186504c00147d0d20ca0980028f21a419413047e1f3b483282603fc5e76d96304c001c38c9b2c60980ff96d83658c1300c54f436c9182607ac9e76d92304c0315390830c6098002a7a1a418c13085d2f434a1182607fe1c64942304c07fcb6c1284609842b271cf75590300061fbaceab206009a9e839d5640c21353b073aac818422a7e0d755903004d4e41aeab206107c9c735d5640c01353907b92c81800327dcf72590306be4e39ee4b206000c9f83dc9640c1af93907b92c81835f27ccb72590300045f40ee4b
  | 19 => 0x28f61672d91303d54f41ce5b226000a9d839cb644c00195f04b96c8980022f20572d91300045f438e5b226000a3e851cb644c00147b0a396c8981eaa7a0c72d91300054ec18e5b226000c3f72d4b644c00187ae5a96c8980028fa0352d91300045f43ca5b2260008bd8794b644c22547b0b296c8981eaa7a0e52d91300054ec1ca5b226000e2f8254b644c00187ee4a96c8980030f5c952d91300051e402a5b2260008be8714b644c00117b0e296c8984468fa1452d91303d54f418a5b226000a9d8314b644c00193ee5996c898003275cb32d91300070fa9665b226000e1d52ccb644c00117d0f196c8980022f61e32d91300051f42c65b226000a3d858cb644c22153b07196c8981eaa7e0932d91303d747c1265b226000c9f724cb644c00193ae4996c89800387d4932d91300070ea9265b226000a3e859c7644c00147b0b38ec8980030fa1671d91300061ec2ce3b2260008bd829c7644c00187ea538ec8980030f54a71d91300064f994e3b226000c9d329c7644c00117d0fa8ec8980022f61f51d91300045fc3aa3b2260008bc87547644c00153f06a8ec8981eaa720d51d91300045f43e43b2260008bd87c87644c00147d0b90ec8980028f61721d91303d54f41e43b226000a9d83c87644c00117f0f10ec8980022fe1d21d91300045e43a43b2260008be87087644c00117b0e10ec8980028fa1421d91300051ec2843b22607aa9e83087644c00153b0610ec898002aea0021d91300055cc0043b226000e3b50943644c00117d0e286c89805a2f61c50d91300061f438a1b22610fc3d87143644c00147b04286c8980030fdc850d91300061eb90a1b226000e1f32143644c001c3a64286c8980030f9c450d91308751f400a1b22607a8be87c83644c00117b0f906c8980028fa1720d91300051ec2e41b22607aa9e83c83644c00153b07906c8980028f21620d91300051fc2a41b226000a3c85483644c00117d0e106c89805a2f61c20d91300051f42841b226000a3d85083644c0f553d06106c898002a760c20d91300055b40841b226000ab581083644c001d5240106c8980030f9d365d85300061f3a0cbb0a6000c3f655d3614c001878caba6c29805a2f61f64d85300055b40ec9b0a6000ab681193614c00517d09baec2980022f61375d85300045fc12e9b0a60028be84dcb614c00117b09b96c2983370f9d352d85300061eba6a5b0a60ccc3e7454b614c00187ae8a96c29800a2fe1f42d85300045ec3e85b0a6000ab681d0b614c00117f0ea16c2980022f61d42d85300055a40a85b0a60c8c9e74ccb614c00193ae9996c29831b279d132d85300064eba265b0a6000ad583087614c0015e30010ec29828f0f9d050d85300061eba0a1b0a6000c3e74d96614c00187ce832cc2980030fd9574985300061e32ae930a6000c3e75d92614
  | 20 => 0x3f43c85b2a600087d8790b654c22d47b09216ca980fe97a0e42d95300052ec1c85b2a6000e2f8250b654c00187ee4a16ca980030f5c942d95300051e40a85b2a600087e8710b654c0010fb0e216ca984568fa1042d95301fd2f41885b2a6000a5d8310b654c0018bee5996ca98003175cb32d95300070fa1665b2a6000e1d42ccb654c0010fd0f196ca980021f61e32d95300051f42465b2a6000a3d848cb654c2294bb07196ca980fe97e0932d95301ff27c1265b2a6000c5f724cb654c0018bae4996ca9800387d0932d95300070ea1265b2a6000a3e84dc7654c00147b09b8eca980fe97a0f71d95300052ec1ee3b2a6000a3f845c7654c00147908b8eca980021fa1c41d95300043ec3883b2a6000c3e87107654c00187b0e20eca980028f60841d95300061fb9083b2a6000c3d72107654c001c3e6420eca98003874c841d953089d1f40883b2a600087e87c87654c0010fb0f90eca980028fa1321d95300051ec2643b2a603fa5e83c87654c0014bb0790eca980028f21221d95300051fc2243b2a6000a3c84487654c0010fd0e10eca980021f61c21d95300051f42043b2a6000a3d84087654c07f4bd0610eca980029760c21d95300053d40043b2a6000a7980087654c07f0fd0fa06ca980021f61f40d953051c3fc3a81b2a603f87c87503654c0014bf06a06ca980fe9720d40d95301fc3f43e41b2a600087d87c83654c00147d09906ca980028f61320d95301fd2f41e41b2a6000a5d83c83654c1ab0ff0e906ca980761f21d20d95300043f43841b2a601787d87083654c00147d08106ca980028f61020d95301fd2f41841b2a6000a5d83083654c0014ed02106ca980029d60420d95300073490041b2a6000c3e76d97644c00147b05b2ec8980022f61e65d91300051f42ccbb2260008bf87597644c00147d0c32ec8980030f9d865d91300051ec10cbb2260008be86dcb644c00187ecbb96c8980030f19772d91300061fb2ae5b226000c3c655cb644c00517f0fb16c8980032b5cb62d91300045ec3cc5b226000a3e8598b644c00147b0b316c8980022fe1d62d91300051fc2ac5b226000a3c8558b644c00156f02b16c898002ad20562d91300b45ec38c5b226000a3e8518b644c00147b0a316c8980032b5c862d91300051f436a5b226000a3c86d4b644c19b87ceda96c8980028fa1952d91300051e432a5b2260ccc3e7654b644c19f93ced996c89800387d9732d91300070e32e65b2260c6c9e764cb644c001c3eca996c8980038719532d913000747b1265b226000e8c624cb644c00187ecb38ec8980030f19671d91300051f430a1b2260a3c3e76143644c00187aea3aec8981eb279cf73d913030d5d406e7b2260008be87d4f644c00117b0fa9ec8981eb8794f53d91300045f40ee5b2260008bd879cb644c00147d0b396c8980
  | 21 => 0x7159641cc001c6ce2b2c83981ba2fe1d61907300051fc22c3286601ea3c8458650cc0ef87aed20ca19800317e0d75986300062e41aeb30c600087f825d6618c0c90f900bacc31800e1fa1774986300043ec2ee930c600387e85dca618c0010fb0bb94c31800e1fe1f52986300043ec3ea530c600087f8754a618c0010fb0ea94c31832f0f9d742986300061ebae8530c60cac3e7550a618c00187aeaa14c318327179d732986300062ebae6530c60c7c5e754ca618c0018baea994c3183170f9d441986300061eba88330c60018f587886618c0070ff0e284c3180021f61c50986300045fc22eab0c60028bc845d5618c00117b05ba2c3180022fe1172586300145e422e4b0c6000c3f74d49618c19b878e9a92c3180030fdd152586306661e3a2a4b0c6000c6f72549618c0038d8e4a92c3180022fa1f42586300145e43e84b0c60008be87509618c0011790ea12c31800327dd332586306464e3a664b0c6000ccf72cc9618c00193ee8992c31831b271d1325863000c7a43a42b0c6000c3f74141618c147878e8282c3180023de1d61186301651f42eed20c6000a3d85dda418c00156d03bb483180b28fa1676906300051ec2ced20c6000ab6811da418c001938ed39c83180b28fa1661906300051ec2cc320c601899c845d8318c03133908b8063180ff171da73942303fd8e422e7284603f87e87986508c0190fb0f30ca1180028fe1161942300f51e422c32846000b59808c6508c0012bb0e18ca1180626721176cc23038caec3ca1984603fb5987943308c0e3ab30f2866118003565da50cc2301ff2cbb4a19846118f1b42943308c231e32852866118003c690650cc2308bf8c20ca1984600087d87993654c0010ff0eb26ca980028f60864d95300051f408c9b2a600087e86dcb654c001878c9b96ca980030f19172d953001c3fc3ec5b2a6000c6d72d8b654c0010fb0f316ca980028fa1262d95300051ec24c5b2a600087f8758b654c00147f08b16ca980028f21162d95300053bc0ac5b2a6000a748158b654c02f0fb0e316ca980028fa1062d95300051ec20c5b2a6000c6d7218b654c00147d0da16ca980028f21b42d953065e1f3b685b2a6000a3c8650b654c19587ceca16ca98193179db32d95300070e32665b2a60c7c5e764cb654c001c38c8996ca9800393d8932d95300072631265b2a6000a3e86107654c18b87cec20eca980030f5d074d95301fd2f418e9b2a6000a5d831d3654c0bf4f501b9eca980021fa1f43d95300043ec3e87b2a603fe1c4350f654c0010fb0f396ca980028fa1272d95300051ec24e5b2a603fa5e839cb654c0014bb07396ca980031be0972d95300043f438e5b2a6000a3e841cb654c00147b08396ca980fe97a0c72d95300052ec18e5b2a6000c3f72d0b654c00187ae5a16ca980028fa0742d9530004
  | 22 => 0xb1863280030f9da410c6500061ebb48218ca00095f874c431940014bf0c98863281921fe19700c6500049fc22e018ca01e93c845c0319400187ee93a2cb9802697a0e74597308dd2ec1ce8b2e6000c3d741d165cc1b38be65b92cb9836a1f61e72597300051f424e4b2e6000a3d849c965cc0134bd07392cb9846a9760e725973000637c12e4b2e60dac5f325c965cc1b30fd0e392cb980028fa1072597300051ec20e4b2e6009a5e831c965cc0394bb06392cb980030fdcb42597300061eb9684b2e60d7e1f32d0965cc00147d03a12cb980021fa1e42597300043ec3c84b2e60d8a3d8490965cc0134bd07212cb980029760e425973000717c1284b2e6000c3f7250965cc00187ae4a12cb9836387cc942597300051e40a84b2e600087e8710965cc0010fb0e212cb9835e8fa10425973004d2f41884b2e6000a5d8310965cc0134bf04992cb9802793e0932597300062fb9264b2e6000c5d724c965cc001c3e84992cb980038750932597300051f426e2b2e6000a3d84dc565cc00147f08b8acb980028f21171597308cd2fc1ae2b2e6009a5c835c565cc0010fd0e20acb980021f61c41597300061f43882b2e6000c3d8710565cc00147b0420acb980030fdc841597300061eb9082b2e606ee1f3210565cc001c3a6420acb9810e8fa0441597300043f43e42b2e600087d87c8565cc00147d0990acb980028f613215973004d2f41e42b2e6000a5d83c8565cc0014790910acb980028fe1121597300051e42242b2e600087e8708565cc0010fb0e10acb980028fa1021597300051ec2042b2e6009a5e8308565cc0014bb0610acb980029ea0021597300053cc0042b2e6000a3f845c165cc00147908b82cb981ee97e0d70597300043f43e80b2e600087d87d0165cc03d0ff0ea02cb9828e1f21d40597300052fc1a80b2e6009a5c8350165cc0010fd0f902cb980021f61f20597300051f42640b2e6000a3d84c8165cc0134bd07902cb980029760f20597300ec3fc3a40b2e60d587c8748165cc0390fd0e102cb980021f61c20597300051f42040b2e6000a3d8408165cc0134bd06102cb980029760c20597300053b40840b2e6000a758108165cc00156902a14c398003335c932987300045fc22eab0e60028bc845d561cc0131b906baac39800a2fa1f74587300045ec16e8b0e6043c9f32dd161cc00117f08b92c39800a2f21172587300061fba6a4b0e60cdc3c74d4961cc00187ee8a92c3983330f1d152587300045f43e84b0e60028bc87d0961cc00117d0ea12c3980022f21d42587300055a40a84b0e6000c9f744c961cc18d938e8992c39810e2fa1c41587300061fba0a0b0e60a3c3c7414161cc00156d03bb483980028fe0965907300051ec12cb20e6000c3f7259641cc00187ae4b2c839810f87cc965907300070e992cb20e606ec3e
  | 23 => 0x186500ee973928430ca000d2d725086194243a74e0a10c328483569c332186500eea73926430ca000d4d724c8619423fab4e0990c32800297a0f61186500043fc3ac230ca00097787584619423dae4e0b08c3284774e9c04118650676b938ce030ca000b1e83dda419400163b07bb48328002cda0776906500061fbb4ed20ca000b1e839da419400163b073b48328002cea0276906500061ebb0ed20ca000b36811da4194001675003b48328256cda0773906500068fb9ce720ca000a3f865ce41940014790cb9c83280028fa1873906500051ec30e720ca09db36811ce41940db67501b1c832800387d8e63906500049fc3ac720ca00093c8758e419400127d0e31c83280024f61c63906500070eb18c720ca089b3a8018e419400127b0fb0c8328002c7a0f61906500058ec1ec320ca040b3a80d86419400127f0eb0c83280038d58461906502bd9d400c320ca000a3d86dc2419400163d07b848328002c760f70906501e59b40ee120ca000a3f865c241940b566d0238483280034e5c07090650004bd404ed98ca00093f825d3319400127b04ba663280030fd8974cc6500061eb12e998ca03fd1f325d33194001a3a64ba663281930f98174cc6500069d302e998ca09993d8790731940c90ff0cb86632807a4fa13768c6500049ec26ed18ca01e93e849da319400127b093b463280025ea02768c650004bd400ed18ca000c5c7698e31940018bcecb1c632807a4fa12708c6500049ec24e118ca000c3c74dd931940010ff05bb263280021f60b764c6500061fa16ec98ca000c3d42dd931940018be65bb26328003174cb764c6500061e20eec98ca01e93e849d9319400127b093b263280025760e764c650004bd404ec98ca00093f845d9319403d27908bb263280025ea00764c6500043f438ec98ca000c3c741d931940010ff043b263280021f608764c6500061fa10ec98ca000c3d421d931940018be643b26328003174c8764c6500061e208ec98ca000c7a801d9319403d27d0fba263280030fddb744c6500061e3b6e898ca00093f82dd1319400127b05ba263280030fd8b744c6500061eb16e898ca000d1f32dd13194001a3a65ba263284730f983744c6500069d306e898ca0a193e87905319400187eed20a63280030f1da414c6500062fbb46298ca03f95e839d8319407f8bcc73b063280025ea02760c6501fe2f41cec18ca00087f829d831940010fb053b063280030fd0a760c6500061ea14ec18ca03fc5f329d831940018ba653b063280030f106760c6500063d404ec18ca00093f845d8319403d27908bb063280030fe11760c6500061e422ec18ca00087f825d831940010fb04bb063280030fd09760c6500061ea12ec18ca03fc5f325d831940018ba64bb063280030f105760c65001c3e402ec18ca03fc5c305d831940018bcec
  | 24 => 0xca12fd3a7050863940014bb0c990c72849b479d13218e500068eba26431ca12ed5a704c8639400127f08b88c72807a4f2117118e500f49fc388231ca00093d871046394001c3ac6208c7284b74e9c04118e501fcaf41ee9b0ca00095d83dd361940012f501ba6c3280024f61e74d86500f49fc3ae9b0ca00093f825d3619400187cc0ba6c3280034e98174d86500f43ec3ec9b0ca01ec3e74d9361940014ed03b26c32807b0f9d164d86500068f3a4e7b0ca000d1d749cf61940018bec939ec3280031759273d8650004aec14e7b0ca064c5e609cf6194001ab4c139ec328003479d173d86500068eba2e7b0ca00095f825cf61940018bcc0b9ec3280035698173d86501fe2f39ec7b0ca000a3f8458f619407f8bce6b1ec32807a4fa1372d86500049ec26e5b0ca03f95e83dcb61940012bb07b96c3280025ea0372d86500ec3ec3ec5b0ca000c3e74d8b619400187ae9b16c328003179cf62d86500062eb9ec5b0ca000c6d72d8b619400187ce8b16c3280030f5d162d86500062f39ac5b0ca000c5d7358b619403d27f0fa16c3280024f61f42d86500068f39e85b0ca000d1d73d0b6194259a74e1a16c3280024fe1d42d86500049ec3a85b0ca000d1e7350b6194001a3ae6a16c3284af4e9c142d86501fcafc3e65b0ca00095d87ccb619424fa3ce9996c328003475d332d8650956ad38665b0ca00095f874cb61940012bb0e996c32849b479d132d86500068eba265b0ca129d5a704cb6194001a3ce620ec328003475cc41d86509469d38083b0ca000d3a749c36194001a72e9386c328003569ce70d8650006acb9ce1b0ca03f95e83dd261940012bb07ba4c328003175ce63986500053ac0cc730ca0fba7a80d8a619403b0ff0eb14c3280771b9c9629865000636b92c530ca000a5e83d8661940736e501b0cc3280038dd8441986500ecbac3c4330ca01e93e87dd1619400127b05ba2c3280030f98374586500069d306e8b0ca00093e871d1619403d878e9b22c32807a1f21d64586500f61e3a2c8b0ca00087e87d8d619407f0f90eb1ac3280028fe1163586501fe2e39ac6b0ca00093f845c9619403d27908b92c3280030fdd362586500061e3a6c4b0ca01d87c87589619400187ee8b12c3280030f1d1625865000637b92c4b0ca00093e87d09619403d2790fa12c3280024fa1d42586500049e43a84b0ca000d1f74cc9619424fa38e9992c32800347dd132586509368e3a264b0ca000d4f724c9619403ba98e4992c3280bedca0361586500ecba43a42b0ca00097a80dd0619400127f08b98c32807a4f21173186500043ec3cc630ca000c5d7318c61940014eb02318c3280025ea0372186500ec3ec32e430ca01d87d87d88619403b8dce5b10c3280031b5cb621865092d3d406c430ca124c7a70d8861942478f4e0b10c32848b4e9c342
  | 25 => 0x459878eb20ac0188022fa1c41580310061fba882b0062c5c3c75105600c47f0fd0e282c0188030fdd0505803151e1e3a0a0b006264e5830141600c405970e9202c0188263e21d405803100c7c43a40b00620097681dd363940012eb03ba6c7280025ea0374d8e50004bd406e5b1ca01d87d87d8b639407f4bd07b16c7280031b5cb62d8e509be9d38685b1ca136d3a7050b639426bab4e1996c72807657e1d32d8e500052fc3265b1ca000d4d724cb6394269ab4e0996c7280024fe1171d8e500f49e422e3b1ca000d36711076394001a6ae220ec7284cf4e9c041d8e500f61e3a6c931ca000e1e43d92639403d0ff0eb24c72807b0f9d16498e500052fc1ac931ca132b5a80d8e639407f4bb0fb1cc7280031761f6398e500052ec26c731ca000a5d82d8e639407f8bee5b1cc72800297a076398e503252f406c731ca000e5a80d8e63940014bd0ca1cc7280ff471d14398e500070eb228731ca000c5f635ca639407fa9e64b94c7280761fe1d6298e500052fc1ac531ca01dc6e7258a63940018dae4b14c72800387d8f4298e500070fb1a8531ca01dd2e7250a6394001a5ae4a14c72800297a193298e500049fc22e331ca01e93c845c66394001c3ec620cc72807a4fa1f7458e500061f31ee8b1ca000c3c63dd1639400127b05ba2c7280024fa077458e500061f306e8b1ca000d3a60dd1639400127d0e3a2c72817ed6a036358e500f68e3a486b1ca01e95c8750d63940014b90ca1ac72807b471d14358e500049fc22e4b1ca01e93c845c9639400187ee9b12c7280030f1d36258e500ec3e43ac4b1ca000c3f745896394001878e8b12c7280fe9720d6258e5000637b92c4b1ca00093e87d09639403d2790fa12c7280024fa1d4258e500049e43a84b1ca000d1f74cc9639424fa38e9992c7280765721d3258e500052e43264b1ca000d1f744c9639424da38e8992c72800353dc93258e500f49f426e2b1ca00093d84dc5639400127d0e20ac72807a4f21c4158e501fe8f31ae831ca00093f825d0639407fa3e64ba0c7280024f2057418e503261f302e831ca000d3a605d0639403d0fb0fb20c72807b0f9d36418e500052ec1ec831ca01ec3e7459063940012bf0eb18c728003475d16318e5098ead382c631ca03fa5f8758c63940018bf0eb18c72800217e1d6318e500070fc22c631ca000e1c8458c639407fc3ce8b18c7280ff875d16318e500052fc12c631ca03fc5f7258c63942638bce0b18c7280ff969c16318e500062eb1ae431ca03fd4f325c8639403b0fb0fb10c7280030f9d36218e500061eba6c431ca000a5d83d88639403b8dce5b10c7280031b5cb6218e500061f3a2c431ca000c3d74588639403d27f0fa10c7280024f61f4218e500070eb1e8431ca130d3a70d08639400127f0ea10c7280024f61d4218e500070eb1a8431
  | 26 => 0x69760e70594311fe2e39ce0b286200a3f845c1650c40147908b82ca18a0a97e0d705943104d2e41ae0b286200a3e841c1650c40147b08382ca18993171cc70594310061f420e0b286200c3d841c1650c4010fb04382ca188030fd0870594310061ea10e0b286264c5f321c1650c4018ba64382ca188030f10470594310043f43e80b28620087d87d01650c4010ff0ea02ca188021f21d40594310052fc1a80b286209a5c83501650c4010fd0f902ca188021f61f20594310051f42640b286200a3d84c81650c4134bd07902ca188029760f20594310043e43c40b28620087f87481650c4010f90e902ca188021fa1c20594310043ec3840b286200a3e84081650c40147b08102ca1882697a0c20594310052ec1840b286200a7681081650c4014eb02102ca18ce387e0d659043121f0e41acb2086243e1e73596410c40147f04b2c82188028f60965904310061fb92cb2086200c3d72596410c487c3e64b2c8218803874c965904313761f38acb2086200e3671596410c40147900b2c8218aaac721573904310070eb2ae72086200c5c75dd9310c401938e9bb2621880317e17764c4310062e42eec98862008df82dd9310c4011bb05bb2621880317d4b764c4310062ea96ec9886200c9f42dd9310c40193a85bb2621880335947764c4310066aa8eec9886200c9c41dd9310c4018b8a1bb26218b4a57a1f754c4310062fbb6ea9886200c9f76dd1310c401a38ebba262189ba67a1e414c4310064fbb48298862aad1c75905310c4432b90a38262189929ea0375980311fd3d400eb300620087f855d2600c4070f90aba4c0188021fe15729803101c3e42ae5300620087e87d4a600c4070f90fa94c0188021f21d529803165e1e3ae8530062cac3c7550a600c58f8b8ea994c0188b30f1d6419803162e1e3a88330062098f987902600c4135b106a04c0188063e61e209803101c3f43eeab00623fc5c73dd5600c4010fb05baac0188ff17ccb75580310045fc22eab0062028bc845d5600c4c98b8e63aac01880a2fa1f74580310061fbaee8b006200c3c75dd1600c4f5938e7ba2c0188022f60b74580313d64f996e8b00620087f855d1600c4070f90aba2c01886237e0d74580310061fba8e8b006200c3c751d1600c59f938e63a2c0188021fe15725803101c3e42ae4b0062008bf845c9600c40517908b92c0188021fa1f525803101c3e43ea4b006200c3f74d49600c59b878e9a92c0188021fa1d52580310043e43aa4b006200c3f74549600c599878e8a92c0188022fa1f42580310145e43e84b006200c3f75d09600c597878eba12c0188022fa1d42580310045e43a84b006200c3f75509600c595878eaa12c01880317dd5325803163e2e3aa64b006200c9f744c9600c58d938e8992c01880333dc9325803106c5f43c82b006200c3f75905600c
  | 27 => 0xf43ec8b026200c3f75d91604c401878ebb22c0988032b1cb64581310045f438c8b026200c3f75191604c401878ea322c0988032b1c8645813100637b2ee4b026200c6c65dc9604c40195ec9b92c0988032b19372581310061e3aec83026200c3c75190604c4011f70eb00c098802ba20960181310053d406ea3026200a6d821d4604c4014f5003a8c0988021fe15741813101c3e42ae830262098dc835d0604c4010ff0ab90c09880e1f21572181310043f43ea4302620387c87d48604c4014f501a90c0988021f21d521813100e37392a43026200c6d72548604c4014f100a90c098b2f0f1d742181316561e3aa8430262c9c5c75cc8604c58f8b8ea990c0988b30f1d6411813162e1e3a8823026227c5c758c4604c4015b307900c098802bc6042018131a162e39ee8b286200c3f749d1650c4134bd073a2ca18d069760e7459431a052fc1ae8b286209a5c835d1650c60f8b8e6ba2ca188030f5d0745943104d2e41ee4b286200c5f73dc9650c5b38b8e7b92ca1880317e0f72594316ce2e41ee4b2862d9c5f32dc9650c4010fd01b92ca18b6a1f61e72594310051f424e4b286200a3d849c9650c4134bd07392ca18cfe9760e72594319f52fc1ae4b286209a5c835c9650c4018bee6b92ca18b6b171cd72594310062fc1ae4b2862dac5c835c9650c4018df04b92ca18b6b17cc972594310043e402e4b2862d987e871c9650c40147d08392ca188028f610725943104d2f418e4b286221a5d831c9650c67bc3ee7a12ca18b5f871cf42594310061fb9684b286200c3d72d09650c5afc3e65a12ca188028fa0742594310043f43c84b28620087d87909650c5b147b09212ca1882697a0e42594310052ec1c84b28633ce1f73509650c5b1c38e6a12ca188038be0942594310061fb9284b286200c3d72509650c5b1c3e64a12ca188028f20542594310043f43884b28620087d87109650c5af47d08212ca1882697a0c42594310052ec1884b286221a5e874c9650c4434b90e992ca1882697e09325943104f27c1264b286200c5f724c9650c4018bae4992ca1880387d0932594310070ea1264b28633ba5d839c5650c5678b8e738aca1882697a0e41594310052ec1c82b28620087e87105650c4010fb0e20aca188030fa1c41594310061ec3882b28633ae1f73105650c4ddc38e620aca188028f60841594310061fb9082b286200c3d72105650c4ddc3e6420aca18803874c8415943121d1f40882b28622187e87c85650c4010fb0f90aca188028fa1321594310051ec2642b286209a5e83c85650c4014bb0790aca188028f21221594310051fc2242b286200a3c84485650c4010fd0e10aca188021f61c21594310051f42042b286200a3d84085650c4134bd0610aca188029760c21594310053d40042b286200a7980085650c4134bd07382ca18ce
  | 28 => 0x2ccb644c401c3ea5996c8988038754b32d91310045f43c65b2262008bd878cb644c40147d0b196c8988028f61632d9131a2d4ec1c65b226243a9f824cb644c487d1f04996c89880327dc932d91310064eb9265b226200e1f524cb644c401c3aa4996c89890e2fa1f51d91310045ec3ea3b226200e3751947644c58b17f0ea8ec89890e2f21d51d91310054fc1aa3b226243a9c83547644c48717d0f90ec8988022f61f21d91310051f42e43b226200a3d85c87644c48753d0790ec898802a760f21d91316b45fc3a43b22622b8bc87487644c40117d0e10ec8988922f61c21d91310051f42843b226200a3d85087644c48753d0610ec898802a760c21d91310055d40043b226200ab980087644c40147d0bb86c8988028f61770d913121d4f41ee1b226200a9d83dc3644c40147f0ab86c8988028f21570d91310045f438a1b2262008bd87143644c40187d0e286c8988030f61c50d91310051ec10a1b226200c3f72143644c40187ae4286c89880387cc850d91310070e990a1b226296a3e80143644c40117d0f906c8988022f61f20d91310051f42e41b226200a3d85c83644c48753d07906c898802a760f20d91310051e42c41b226200a3f85483644c4014790a906c8988022fa1c20d91310045ec3841b226200a3e85083644c40147b0a106c89890ea7a0c20d91310054ec1841b226200ab681083644c40156b02106c8988030f19676905311651f436cb20a6200c3e76d96414c40147f05b2c82988028f60b65905310061fb96cb20a6200c3d72d96414c401c3e65b2c8298803874cb6590531a261f38ecb20a6200e3671d96414c40147d01b2c829889e97a1b658c53159f2bb0ecb18a6200e1c65d92314c68753d0d20c6298ae387196418c53112c3ec3ecbb026200a7a80d97604c4014f50032ec0988030f9d764d81310061ebaec9b026200c3e75193604c40187aea326c0988021fe0975d813101c3f42ee9b02620087d85dd3604c4070fd0bb96c0988021f61772d813101c3fc3ea5b02620087d87d4b604c4014f501a96c0988021fe1d52d81310043ec3aa5b026200a788054b604c59787ceba16c0988030f5d742d81316561f3aa85b026200c3d7550b604c5938bceb996c098803175d732d813163e2f3aa65b026200c5d754cb604c45987ceb20ec0988030f5d641d813162e1f3a883b026200c3d75107604c4015b306106c098802bc60420d81310061f3a6cb3026200c3e74196604c40187ecaba4c0988030f19574981310061f3aec93026200c3d75d92604c40187cea324c0988030f5d4649813101c3f436eab0262b387c86dd5604c4010fd0fb2ac0988030f1d3655813100636396cab02620087e87195604c401878e832ac0988031b1c865581310145f436e8b0262438bc86dd1604c40187ecbba2c0988030f19774581310045
  | 29 => 0xeca98d270f61c41d95310051ec1083b2a6200c3f72107654c40187ae420eca9880387cc841d95310070e99083b2a62b387e87c87654c4010fb0f90eca988028fa1321d95310051ec2643b2a62b3a5e83c87654c4014bb0790eca988028f21221d95310051fc2243b2a6200a3c84487654c4010fd0e10eca988961f61c21d95310051f42043b2a6200a3d84087654c5674bd0610eca988029760c21d95310053d40043b2a6200a7980087654c40147d09386ca988028f61270d95310061f424e1b2a6200c3d849c3654c4010fb05386ca988030fd0a70d95310061ea14e1b2a6200c5f329c3654c4018ba65386ca988030f10670d95310043f43e81b2a620087d87d03654c4010ff0ea06ca988021f21d40d95310052fc1a81b2a62b3a5c83503654c4010fd0f906ca988021f61f20d95310051f42641b2a6200a3d84c83654c5674bd07906ca988029760f20d95310043fc3c41b2a620087f87483654c4010f90e906ca988021fa1c20d95310043ec3841b2a6200a3e84083654c40147b08106ca98ace97a0c20d95310052ec1841b2a6200a7681083654c4014eb02106ca988030f9db65d91310051ec16cbb226348c3c71d97644c40147d01b2ec8988022f61e65d91310051f42ccbb2262008bf87597644c40147d0c32ec8988030f9d865d91310051ec10cbb2262c5c3e71197644c40147d0032ec8988022fa1b72d91310061fb2ee5b226200c3c65dcb644c40187ecab96c8988030f19572d91310145fc3ec5b226200cad72d8b644c40117b0f316c8988028fa1662d91310051ec2cc5b2262008bf8758b644c40147f0ab16c8988028f21562d91310055dc02c5b226200ab88058b644c44917b0e316c8988028fa1462d91310051ec28c5b226200cad7218b644c40147d0da96c8988028f21b52d913166e1f3b6a5b226200a3e8654b644c4014790ca96c898b330f9d952d91313764f3b665b226200e1f65ccb644c401c38cb996c898b1b279d932d91310070fb2a65b226200e1c654cb644c401d1ec4996c8988028fa1850d913151e1f3b0a1b226200c3d751d7644c48753d063aec898802a760c75d91315355b40ee7b2262008be87d4f644c40117b0fa9ec89890f8794f53d91310045ec3ce5b226200a3e859cb644c40147b0b396c89890ea7a0e72d91310054ec1ce5b226200caf825cb644c40117d0e396c8988028fa1472d91310051ec28e5b226243a9e831cb644c40153b06396c8988030fdcb52d91310061eb96a5b226200a3e80d4b644c40117d0f296c8988022f61e52d9131a3d1ec2ca5b226243a9e8394b644c40153b07296c8988038be0952d91310061fb92a5b226200c3d7254b644c40147900a96c8988022fa1c52d91310045ec38a5b226346a3e8514b644c48753d06296c898802a760c52d91310064fb9665b226200c9d7
  | 30 => 0xc631574cec3c8398c62028be84dd6608c40117b09bacc11880327e0d74982310064e41ae930462008bf825d2608c40517d09b94c1188022f613729823166e1f3a6a53046200c3d74d4a608c59987ce8a94c1188030f5d152982310145fc3e8530462008bd87d0a608c40117f0ea14c1188022f61d42982316464f3a6653046200c9d74cca608c58d93ce8994c118803275d1329823105c5ec3c8330462008bd87106608c54787ce8284c1188030f5d0509823100c7cc3c41304620087d82dd5608c4010ff0aba2c11880e1f21574582310043fc2ae4b04620387c855c9608c4010fd0fa92c11880e1f21f52582310043f43aa4b04620087c87549608c40187eeba12c118b2f0f1d742582310061fbaa84b0462cac3c75509608c40195ee4a12c1188072b1c942582310062fbae64b0462c9c5c75cc9608c40199ee5992c11880317dd5325823163e2e3aa64b046200c3f75905608c459878eb20ac1188030fdd4415823162e1e3a882b0462018f887481608c4039d0e4902c1188023ee1d60182310043ec3cc9b2a620087f87593654c40147b04326ca988021fa1b72d95310061e326e5b2a6200c3c645cb654c4070ff0fb16ca988031b5cb62d95310043ec3cc5b2a6200a3e8498b654c40147b09316ca988021fe1d62d95310051fc22c5b2a6200a3c8458b654c4014f700b16ca988029e20162d953112c3ec38c5b2a6200a3e8418b654c40147b08316ca988031b5c862d95310051f43685b2a6200a3c86d0b654c59787ceda16ca988028f21942d95316561f3b285b2a62d2c5e76ccb654c401c38c9996ca98b1f179d932d95310070e32265b2a6200e4f624cb654c401c98c4996ca988028fa1841d95310061e324e1b2a6200c3d741d3654c54b4ed03b9eca988021fa1f43d95310043ec3e87b2a62b3e1c4350f654c4010fd01b96ca988021f61e72d95310051f424e5b2a6200a3d849cb654c5674bd07396ca988029760e72d953100637c12e5b2a620087c805cb654c4010fd0e396ca988028fa1072d95310051ec20e5b2a62b3a5e831cb654c4014bb06396ca988031b5c872d95310061fb9685b2a6200c3d72d0b654c40147d03a16ca988021fa1e42d95310043ec3c85b2a634ca3d8490b654c5674bd07216ca988029760e42d953100717c1285b2a6200c3f7250b654c40187ae4a16ca988028f20542d95310043f43885b2a620087d8710b654c69747d08216ca98ace97a0c42d95310052ec1885b2a6200c5f72ccb654c4018bae5996ca9880387d0b32d95310070ea1665b2a620087e878cb654c4010fb0f196ca988028fa1232d95310051ec2465b2a634aa5d838cb654c5674bf04996ca98acf93e0932d95310062fb9265b2a6200c5d724cb654c401c3e84996ca988038750932d95310043f43883b2a622587d87107654c40187d0e2
  | 31 => 0x8354d367154860906a7b2ce3990c1208af639c93218241006c6b92643048352d96714c8609040153d07b00c120bb76c9c660182410045fc3ac030482009bb8758060906a3b64e2b00c1208bbac9856018241a869b388a03048200c3f759d564cc41353d073aac998d3ea760e75593316be4f996e4b2662d88bd879c964cc40147d0b392c9988028f616725933104d4f41ce4b26634ea9d839c964cc40195f04b92c998b6327cc972593316bc5f438e4b266200a3e851c964cc40147b0a392c998826a7a0c725933114d4ec18e4b266200c3f72d4964cc40187ae5a92c998b6787ccb52593310051f406a4b2662008be8794964cc40117b0f292c998b6a8f616525933104d4f41ca4b266200a9d8394964cc401c5f04a92c9988030fdc952593310061eb92a4b2662dae1f3254964cc40147900a92c9988022fa1c52593310045ec38a4b2662d9a3e8514964cc41353d06292c998802a760c525933104d4fc1264b266209e8f824c964cc40193ee4992c998803275c932593310070fa9264b266200e1d524c964cc40147f0ab8ac9988028f21571593315ad4fc1ae2b2662008be87d4564cc40117b0fa8ac9988b22fe1d515933162c5e43aa2b266200a9f8354564cc41353906a8ac9988022fa1f21593310045ec3e42b266200a3e85c8564cc40147b0b90ac998826a7a0f21593310054ec1e42b26622b8bf8748564cc5ad1790e90ac9988a62fa1c21593310045ec3842b266200a3e8508564cc40147b0a10ac998826a7a0c21593310054ec1842b266200aba8008564cc4015730010ac9988028fa1770593310051ec2ee0b266200a3f855c164cc4014790ab82c998d36a7e0d705933104d4e41ae0b2662008be8714164cc40117b0e282c9988030fa1c50593310061ec38a0b266200a3d8214164cc40187ee4282c9988030f5c850593313270f990a0b266200e1d3214164cc47f47d00282c9988022fa1f20593310045ec3e40b266200a3e85c8164cc40147b0b902c998826a7a0f20593310054ec1e40b266200a3c8588164cc40147f0a902c9988028f21520593310045f43840b2662008bd8708164cc40147d0a102c9988028f614205933104d4f41840b266200a9d8308164cc40156d02102c998802ad60420593310053c402a53066200ccd724ca60cc4070fd0fbaac1988021f60b75583311fe2f996eab06620087f855d160cc4070f90aba2c1988021fe15725833101c3e42ae4b06620087e87d4960cc4070f90fa92c1988021fa1d52583310043e43aa4b066200a788054960cc40187eeba12c198b2f0f1d742583310061fbaa84b0662cac3c7550960cc4018beea992c198b1f171d532583310061fbac82b06622cc3c7590560cc40187eea20ac198b170f1d441583311fc3f438a0b066243c9c769ce418c5716390ab9c831889e5721576c
  | 32 => 0x127b0fa90c720d8f4d9c75218e410049fc3aa431c820093d8754863906c5a6ce2a90c720d67479d53218e410068ebaa6431c8361d96714c8639040127f0ab80c7208b24f2157018e411649fc38a031c820093d8714063906c1a6ce2280c72090e67a0f75d8241004cec1eebb0482009b681dd7609040127b0f3aec1208b24fe1d75d82410049fc12ebb048200c3e615d76090401a6cc2baec1208b22f61f65d82410055d406cbb04822cc3e755976090401a3ceb39ec120803475d673d82410064fb2ce7b048200c9d659cf609040133b0539ec1209bb2798673d8241006cb30ce7b048200d1e755cf6090401a3aeab9ec12080267e0973d82410064f30ae7b048200d96615cf609048793ce7b1ec1208028fe1563d824121e4f39ac7b04822c93e85dcb609040127b0bb96c12090e67a0f72d8241004cec1ee5b0482009b681dcb609045717b0fb16c1208030f9d762d82410061ebaec5b048200c9e73d8b609040193ae7b16c1208032b5cb62d82410061f3aac5b048200c3d7558b609040193ce6b16c120803275cd62d82411649fc3ea5b04820093d87d4b6090401a3ce7a96c120803475cf52d8241afe9b38ea5b04820093f8754b609040127b0ea96c120803479cd52d82410068eb9aa5b04835ed367154b609048733f0f996c1208026761f32d8241ad68f3ae65b048200d1d75ccb60906bbb2ce3996c12080267e1d32d8241004cec3a65b048359d1e754cb6090401a3aea996c120d73659c532d82410069b3ace3b048200d35759c76090401b2ce738ec120803655ce71d82410068f398a1b048200d1d7314360906b7a6ce2286c12090e67a0f7598241004cec1eeb3048200c9d7398e60904015730131cc120bcaada07629824115c5fc3ac53048200cad7258a609040153d07b04c1208d2eca0760982410071db00a1304822b9b987882609045927d0fbaac1208024f60b75582410061f30eeab048200d3661dd5609040127d0e3aac1208b30f1d765582411645e43acab04822cc3c75595609040117d0fb1ac12090e2f21d63582410051fc2ac6b04820093f855c960904592790ab92c1208030fdd762582410061e3aec4b04822b8bc87589609040187eeab12c1208030f1d5625824100657b92c4b04820093e87d4960904592790fa92c1208024fa1d52582410049e43aa4b048200d1f75cc960906b5a38eb992c12080347dd53258241ace8e3aa64b048200d8f724c96090457b18e4992c1208baeca07605824115cdc43a40b04822bda872481609040136d03ba8c1208024fe1573182411649e42ae630482008bd8798c609040136d03b90c1208ae2f619721824115c5ec3ec4304822bcae72d88609040195ae5b10c120d62ada076218241abe5b38ec43048356cb67158860906aba6ce3a90c1208af4b9c9521824100696b92a4304
  | 33 => 0x4000004000000001202b00a000401201500c80340aa001001800000c008001000c00000000500080100160020004002000000002800800c005804801c003014802c0020020030010004006000802800001e00d802800a00700d800402001d00c80280c0006000000c006000000800001600d000000008400900000e403400a001800400800f009806800400100c000c020000000000c0180010000084000004009801001e0050020010002028000804000000d005800400000000000040160000010008034010001000400000e008800801c0010018000002003000800000a003001800802201200d0048004004000001405a02c0018004000005000002800a00500080000000230008004002000000801c018002000001000400700000180136d03baec7208026ea0375d8e41004dcc06ebb1c82009b681dcb639045717b0fb16c72090ea7a0f62d8e4100656b96c5b1c836ad3671d4b63906d3a6ce2a96c720da3659c732d8e4115ccfc3a65b1c8200a9f864cb6390401b1ae4996c720d9f659c532d8e410049fc2ae1b1c822c93c855c363906cda6ce2286c7208034e9c050d8e410069cb80a1b1c8200e1e53d96639045917f0eb2cc7208b30f9d56598e410054fc1acb31c8365b9681d8e639048753b0fb1cc7208032761f6398e410054ec2ec731c8200a9d82d8e639048793ee5b1cc7209baa7a076398e410074b40ec731c8200a9e80d8e639040153d0ca9cc720803875955398e410064fb1ae531c8243d8f325ca639045717f0eb14c720802a7e0d6298e4100656b92c531c8200e1f63d4a6390401c3ec6a94c7208af4b9c95298e4100696b92a531c8200a9e864ca639040127f0ab84c7208b24f2157098e410070fb18a131c822c93e87dd5639040187cc7baac7208030f18f7558e410049ec16eab1c8200c3e61dd56390401a6cc3baac7208024fa037558e410049f438eab1c82a6b9681d8d6390459a38eb29ac7208b26721d5358e410049fc2ae4b1c822c93c855c9639040187eebb12c7208030f1d76258e4115c5e43ac4b1c8200c3f755896390401878eab12c7208032bdc96258e410049f43ea4b1c822c93c87d49639040127d0ea92c7208024f21d5258e410068fbae64b1c835ad1c75cc963904573390e992c72080347dd53258e41ace8e3aa64b1c8200d8f724c9639045927d0bb82c7208024f6177058e410049f438a0b1c822c93c871416390487a3cc6ba8c7208024fe097518e4121e8f992ea31c826ec3e615d46390401a6cc2ba8c7208024f2017518e411645ec3eca31c822cc3e75594639040133f0eb18c720803475d56318e41b26cb38ac631c8243d8f325c8639045717b0fb10c7208030f9d76218e410061ebaec431c822bcae72d88639040195ae5b10c7208030f9d56218e410061ebaac431c822c93f87d4863904
  | 34 => 0x5000000400400600a0000000002000805801201000000500100060048010002011000008c00000400a8044084009003801005c0070010014000002000008c016009005807800400400200080040180050000000000001002400602700200000060000000000014000000800000c0000080050000007004003c00a00500c004c00a000002005000a0000008014008003009001c0080000048014002006000000002a003000000800c004001000000e011001804c01204800681480000250188004008000001000400a0090028024004000017002400400a000800400a0030000014002007002005400e0000028000002003012803800c00300100000140040000024000000008000000e0000050000008000000810003c006001004c00c008003801c002000009000400a002000000c000001000000402a000013000400200000000a800800400000200040230130114000002002808800a00000080000000000058008018001001801400404d0028014000005000000400a00200000540040120000000016001001002800401500080180040040258080030027000805800000000100040360000000000004009002005404c0030080008012003000000003c00a00b000800200100d000006200200a801400c006003800c01000700180780260090000010000006012001000000100a80040020110050004000006000807800600100580240060000060008002028001000c03c002009002800000f01c8000000004001000001e001001001c000004000800c00200f000800000c0060070000010001003000001e00100000340060000008028038009002000800a000002015c000003003802000401000e8004006004003000400a008006000c0060000030000022001000800c0440210000020004001006801c00200501e805000a00f006000000400500800200000280030000008000000001401402c000004400a000008001c012001005801400c0070000024000000002000000c00a018004803e00100e00080000010000008002001008003000400300c001000600f0070000000013001804c0000210030074004000010807001a00a001808401e00f000000002c0050228008000001001800002a000003005800000200100940020030040000002000005006c00604b0048020000006007800400a00000500180040000028000000001000003c01e000001000801a0110128000000001008800800203a000800400400d003808c00e000004000c016001014001c04200300f801c00000a0050000000000001001402e00300000040180040198008002000001800c0160010008094018009003000002c01a000001c00c011016803c00000e0028000020001000800800a00300000040020020010018014019007800400400103d0064000000000002
  | 35 => 0x140120140058008000008009000800a002015001006e00e0080018000001006001400000d00400080000010018008008002000000400a00100c801802800e0010000000004001813801400600880040080020048014002002007007c00a0020000000000014003801c01001d004800000800500880180400080048040032000004807800200000100a0032003020802800e007002800c020028001802401a0000010000000000000801401800400080140240000020044028004004800805e0150048018006010006000800001700001a8018003024004001a00400080040020020128008000001001000000c00000000080120180088060004010000000400c008018802c004000005004c000003011801c04000200b0028004000000001800a00d008000400402900b000000601e00000ac0360000000004018000003003400200400080200000220100018000008005003000000000200000380030000000006003015800801c000000804c02c007002800802400b0000060004001000000c0000070008030002014007800000c0010060000006007010801c02a023000800000203c0458054002005000000c024010000000400c008001805c0020010000068000000003001800c00b003800000c01a006001403800c006800000400001b80000160100060004002002005001002a008003800c00600e00f801c00e001008801400a0190078040006016001800000800301c009400000000700180260180018058002000000005800e00700f0000000016000007c01809a002004000200000000ac000007002801402600603500280d003101b000800600b00f801800400a0070004008024001000c09a000002000800801100e800800c0010048000000000000005002000400b000c0040040048004006002006008800800400280cc00001d000000c03400a0008004002005007000000000d005000400000200e800800a0000000090000014006000c0020000000024012000003800000802c000001400200501d001000402700000700080000020070004001006800403401600f805400000700000100020140038008018001007804c01400000800000100020000000002004002000802000300b815000400100000400000040168030000002000000400000000000dc002000009800c00200a012004000c000001800c00800a002002000000000a8004002065001000800001e008801c004000000800000400f00c803c004006000007801603900200080000020028000054000000000c006000007003000000800d80040000200008020000000013005004e00900280100020000060000004003000000c0000020018018018021000802003a00500000000000000018004024008003007400600500f80040060000020000006017006000400002
  | 36 => 0x98a2c15797c82548cb6000019617500000000afa5661e6e48f116e62920767011c768f81c066fe86547cf8ba88e1a01e713800a7a21d540001d4a829000092117440001a3c4b39078869024e00003b062c161020d03a0829800088410804ef00002db1a76323900c0000000236000065304e000023e269280003c7991a59c2248497961e7ba825e82b0fd000003d63a384346b5000005d00007be0edc90d14980000f781bf06c632f22364a3218c4b98c18328a44c88e964a69b17bc86b898e3f305fc0b41bb48070438000000015680002c9a2c600011a42bb19e41b7937c6f0058a3d78000585800050583e60001c3c3f18314000032a5438000000227a00000006b91d6400000000001a5a0000c7069c135e627142e0000a12000127c000068a69a18c25c4209060a187e00020f63448c6221117165271e1e137000e66f00461490ef668c9d1441f05a00ef80643258bf676e90e60000bc482591645bd14364d800ce2e70e0860a8b487cc9ec269313322f08d1e3d895b42908000101800007d8a72645158283585807a6049e52504724d49b8a2af90060899db034d18120ce878603a22968bf822e6e6920c8bd800046883fa1771bc460c0f8c07717c48c69d3854d9e522308a5e2d792b62818936166208480080d241f9aaa91600005dd863609f9bc22e30e5446406e44989944023077e3128436340090807321fa8538000814064c018202403181a66430c720531f988dc0d921d71a2e7cb0f8a7e90b3c905058448e0194619092c84d177062687e447112b4048000037ba3e47a5119a8ae13f8000055426e170c14e1b3e29d19586448224657a43c30991de00008fa77d16e43d5866c29890d00bf946a3bc1c0c4ba00000001be00000110894a3287448000000039c4bf0c2046b932c6e0929608300000001aa867300007fe800059b000066c073c0000f400000000000065a00000000000000000000075a82342e99d1c1ec800070d917e000137417580003708ea6852078c64408928308d7e46b00a47a3146c5e2071244f05fe540800000000002b291fc34283f684d80000000000000000002400000000e2a00004a856d99904a914ba4e005d21bf96ce7651da60001f282b88f326da800000019225ba041e6e71c662ae0000000002000000c0160000000024011014000400400100d8088000000000800000000600080480280390020074016003000000001400500880000000050010038002002009800000000000000140000000018014054004006802406002f001001800200f001000801800200600100000000028038004005008800c00000a000801802a000009800002a00f00100000040050090004074018000003401a0170000000000000007800800a068005802c0040000040004026003000000400600500b001c00400c00480
  | 37 => 0x1c2648cc45a3139202583900ac8dc6238a48216f8c9a11b946e3ae0000274929233f103453596d6679840c74d8f5800000002f0000000010de7f3000033700003a498086f31102535012c2698a4a55c0828000081000002a639b8c4c7b180000001330000000035a181e8f71bca0001ed861099805daa154004961864f8b1649d2490000019e00000000001fa80541e186c480000000000606810875b90f05fea05e3ab1e4200012903e68000815846603b933c433070a8ca914a06604f41f0835600c8616624000034c89f686213ae4dd85567091b8836a096830880000c78946813000009480000000000882000000000000000e847c30000000035854b00000001a968c21d0e7f19a24041000065f8000334a2da88c15960000a580000c0419215e42ee9e4613a00008d61d4036ea26605201121d185600001de400013487290000748074e1210cb881c15fa00a015881804904a206964941ee4000218006a99ea198838c0829768000078a662922056e07f077a918c00010fa36b0000000220c5ba8d608ac122c4c318d628f90bc452106224680008798cba3031556380246e86780fe459a0fa6ec1c4209e8ace4e717266b017c6000169e2c60000000040e49206b2000195a0f924666a098261669a8c91c108460b0d6a64c1aca2d180dc1a9000000002c431610a65880000292000000019ca812800000000000c38b5402500000000000658a0444e88d521ce0b56907198c79f22f2286975206c818c3ab84da83b86c03518ec40799a2c62a83d08d7a09807e8000000000000000007e1a0e886883e27000d3e0000f7c0000d768541a860001db268e0ab6000204827f040835d20004b71d2e11e233410b904485a90484780b204b4083e5f4800067580c45a018b2000197c82e21ba83189de11d9e641c917461978a9c632211621204ca3b78e4a4fb23f46e580007c595900f315ec2ce93982e4028807a0f4442e84cc87c0c0a35b168a8e580000000000634000020208da00015fc0001714000012a0000fe00002166000000246492000001a9e57d165272c935829a00001819b4e000000040e229040f8c28000000008ca3aa1a616c8628934a6c90518470029a00020de0000ac88be9a7c58c89907db85de5d395e2343104056a8f9e445871e75a030245c1a9209e056a763133859303066a70614061117837387843f299523cc0a8238600000000000134000074f0000737887c4c2138e51822ba90d987a5dc9e40773800059ca14a6fc0d860000cf871e9c5860085ae8e78ae438f08b03389c0841791da19f0e261ca1924849199814a940e31aa2728788f7e000105c5600dd23a3051400000006a8a1e420000004ed91ba115034c00012ec611000055093a600000002ec06560ae00cc0001d222ac13d045ea18a000000078880ae6de10ac54
  | 38 => 0x839e307d0a1785e49bf82f60ea229b13424968cac2498de8506038640c8bf4076889073822f07fb11842c2114e3b5a3483e387b41ef921c53d97ce6e500f66141c8a30907c612c83e83cd9d5e52f953a41a01b64b50b4c17d236689417a033fa0ec87e0dfa5441e2e684800042c08741ab149e282054200000084a88b103c507621300d384c482ce7b7960033993f62fc036848ea38c590808480992842d801542ca1bec27900062188000000000000011b4401013c219894a0000000405851e00000007dd800090419566b41eb06c817f06b30ce432400000000b0233a80003ac8f1661896886148dde3ba244856688c87a79c325bd844616f000050d15a631f1c26181085a8d00ece2069fe80159aac1910e0200004c2221840a8978000907a102000000000000008221abc0000f80792a3ba28ba38872009e8000000000000004b5a3d22d005ec064244e435000086716ae00014501db09441f823108e9019a8d38d08419109c04680001a7032282a1ff400d97e66550e1040f1052757082600000003ed88140ed1a0c23c19ac30d9f6073d8f2e7f8a4524851ce215b00007c0918a2729e5e3c195306b70c668b11aa47c980004f69c644e4080662621ce000000000019420000d6283f82c0653855291b13567460000355a43a0649a102829dd01e798c43ae94a226800008d88938162031600689cc2a68ee441b20400000000000000057e00006031e4400000008b70000000102089b800058101de4810ad6287132a43800004068b880000a7632198a63f5931c11000004d907b01501fa038486aa69600008249c943d900005ff9e0c5688a1e2651e76788035a1fe1406909a20623d920e00000006b6000036f8dc405e217e7689ab475f8cd6728800043e04ea6dd1b08000000000021b200014668b306d200011c631492f00001c7e3cb0b4e85707ce0911e3c00001e064e1324000128229c1708000225c30400000001f3a00005f27bd000061286f85fd161c5a18c38516220a0900506245923244513c61dc80720e78ed47ef9e7819193c290299d286a9ba600b92361990e904f319b66c51bd42ea974c096172a9020fc42fe0000000000062201d80000cc84d0144214d0ecc000223c5968efe0000cc200020dc00007d239d109a05a86ba5c08eec322161285e93a437d817e4ff8000000093a89da37e88982922f8000012c222255fa30000000005771e8461011445178fec18080003190f3a15c00008a2884e3251ad600016280001e662379b8668584c82501ed48f01eda57823c81589a5e02e80003140c347d30b580001a846908f4800022b4669980a1b1011861a089e80d800000000006c798f44b80000000000045d000000018203aa19d0703935a90a06c864a18a8698940c3591ffc2f3837a564997a00315084ed1bbc475a1624038d
  | 39 => 0x31a3dc9138000244604e09ea0a500005e0a15e0d116e20000b741c39e9226e800000017cc67899ec000201a2a51ae217183646ada37c7f696da00000002301d88000097e0001bdc000208a30500005291260000000000000002f3129e28e8594200953276797065e3815c5f602fc0000ca602d17d4683a110317805e00000000001c6c58193ca6880d4400016541091dcc4c2892a42098b60001a0641c80000eb00000498fc01eda1cc0001ec046f80008d58ff4106111e000033890b0e7e0a092a8333800000005b40a80000000000000010a845080007931e3a659063236680003ff0000652a0f43d197b22f283ee91f02ea5db8dda66e1f8c8f9852251a158836906e66bc8f6092382d26ba18e82bda1c862f1ade68795c82bf00000819e026c997ba000202a0002120818800021e000000014ce2c7800000000005b995ac718000059900f86a220ca33284f826a8c4604b80fa0140c5a2bc946455f00000001a3400017ec3da9cd612f84ac018800000000003878f4242e02361bd145a75880ea45013c8294189278700008562464515936c409144e76619e06811638680952e8171000000016e0e916c2165981043581f87510000000000056c86cc652000054311188c982c87aa80001c00e9c869818a09889740000312576800038107163ed1cd2000001012ba0805ae9e480001bce4471f7c3650e2235f000067791ec00006b07441a2690580007e51f4e092133e8ac9b8c171152a12d8c420000546222932636116bc6f4992671189b01d8147066389606c002746659a306948bb83209f3454d005a80308d66519dda2f4867220aa0e43170e28786818253b140a8c2956869a93ba0001270189075a3dd0dea3c283a800019c60c0150a00a80743598f00500866e2998ed20a9021463b179c15f89d663180000300f1800017da896800000015d474002a8000069400023ec0000df4702800081f000026f207e6db13442981e041e0984c8f19af6712889a4c89ce60a6162e3e60296590076e0c11e162dd8628043248050214fa23192f88b00c7e48a891c27122ac85f151658d800004e854e49b8b621d99afa39408aa2c024023948ee6422110e0ee1ea64ea93d289c156a38c13e08de002c7218c440d2018607512665f80250297042016c80006418e06234a1d266f87bc62f8de048b90020a30d406c39f9260d80005919fe67b382de0000a6400005ac000000083980000001dc850780006cc14ea487800040490360001cc26d480008471d307cf1bac72b23b427800002fc90c47e68070546a44487280007009c142230a5243b9e088f0895091e01028f6041a14399848a223b878fa1425ce9ed00be080443da2a68b98dd46481ef6634898a07a8670353800082ea02c14e887a13e8000225a2a400016ec0ea85167558e9663917de8
  | 40 => 0x1dd263fa28c870913e440143e385800000005c20001eb600015508cd928e000055c712000033c16c61789a0a505234c3f6872a4e58aa463a947655c80000f7800037300ca20e00002bf83d24d4159c903808200015c26ff850410016fc23a8e9887020b01048b8255890465618d5c486a0a235610c61b611f066aa12c3b41e565398d720a3a27e3f7881251f839277805e00bb020e8c48f923600a8a50b0b2a6150d4a88f96f2410a45a8960eea7c2083a428a36a3c306f06d0879674191fa664a3a885312526328000012a30e436011e2ff0c6e2de0e581f01d5a50f175c01ea19a86d018e10502e25cf163e66ba06859ba1be62e8000716846c7db00001a087a27078704000052c87f99088a493ea06893fc4f000160c820cc77e12d84b4924e01090b27411c782b80fd464b8cb04c788be7ec881e49599364499a7851522a84f719ce22890da4961e804de13e264e915820c821827b984e21d8e5644da0d8398081800998cc109805c21b1c825e5814261d079c7de8e8285184803468eaa30387403c1041688b8bfe26b0e3a2b711a03b196081fb0c066c2a2561f2849819d99a033b97421498d507af23328cba1e0007033613580000b18c3a2a99b841f780007819cc06b1237667d020200000008f28efc000000076e00000ba0da2808a1fc0a182900000da67ab9b720741b4433b1fc0000242200020f28c819021f9860a0001ff22fa0e4839919da6239f50117a316732a13e7a8800010714a800006da000043c7e3896204f9de867ca1ee23b9d841949e7439e01ec9178f522918ebe23d1f386dfa01002b212627e96d00e9828012091f81cc80246ce1f122d98b2461c8f666f6a212484800084e0c4e00004861aa0bd62579b9e5cc861033e9388000026c3cf196c41984de00000006e8958e38e000054a00003d2854c4ac93b0173a03a0bd91ea5d615a05c711d208f0f9c00008a000000005db11c874b178a1cb87ea0fa8c7487797d070f80000e2000005924926df1aae000066052813187f58f7656c072258c1f540000fa25ce1ae092322be000191c8ef0022114172812d00007eb84640d5104e75e000000004b81e50000000113a00000000000000000000019d00008d2987c5a080004aa924484315ee04511e40fb202823e00000ac1ee0000132862500007a188ca444a39870b11f2890000036787140000a3800000000000dfe3910e94918a1ea1a20000000000000000002c5000074a800000004ec0000ea03fe8ad82e68fa05868e8800000001ae1e2400000007799df041c154800014ca000030c7841db4000119859a16d475e9fb054e03708e10000000000088d166a59e800061d8caa4469d8a8751db607883a2000244274a00002d9201681623e86bf9ac200015521bb000084197e48281fc21170f547ff821219080003360
  | 41 => 0xa0da2b1224402399a4874000000000000ca00000be992c6888000793800003f0fa80000000000000089d06d0595938c8ce07f62e0000010a0b1c2ed20aa35784ce14f972054817f886b1d6000012ca61b9d5029f94f80001bc62e601b00001c6255ba0be38309c06bf0e408bb999e007906e11200006cd90744ac148a04396c477284947e99e362f69f402ad1ef2898158a802008623a10e88e422020b9068c0229f640001e323671ec832b80006bb80004411bf459796483fb91dc32c83328e98398699136a7c39eb213c00003c6912230a8cde4a70aac0548faa7ef02be00007aa2551d2444a1d3a6d61ae643f8000000028a2f7995071489f25bc10282c10bbe8e8929a2e81754000203c6171d26825234454880003eb891e3369b9028411e81c706501f503dc7c013a818b9dac0001182765a10a22c9a507a68d1405d9094123069280ca2867b308ce14085663de94ac00024322131cb65cd910a90b8c9e6770daa51100000000a0c00012fe4679f664ef931a350980401b11065d4000018e80000e086e260917c20e01da8131a0820000a0e2ba157633509b65ed822a0b080e48fea16e00009582a19cbc318144c6ba8bbc1b08a927bc02e08f40fce13f824239da2240000fe242482cc17e9f58000192a25312c414ba4768ce8456479965c5ae077600000000000cd0775013201502721a88ba4379924059f156621c91b80000000000000000000007a5902e2df8c2e203887024c99ba000000041406123b88df016423a057380001691bb80000d2e00001e4210043a00012bc34a102c89b22b6000131600000007a3800000009a4000194027412c8638149602005c02b5130e76f948c0001c1a000000011f800055b1efc8dd1ace00014a64f98c48000026655807a03d41f465dd14b62539f0a3bd000023400000dd04d415408802a582382559120000099642b80005700fc25e8975a03882b60001d082bc06ce1de1a083771aec526800000003463f616b07b7240480f80005df910c259800073f91d05758a78000027c5b714125c788f226a0b1a520872c34586fa73e23da38b0f201898e8676f00005b321308b4858c24c016c7f4031c19a83da75980000720f94557223200000d8215800074c818000000008ba178c00003602210e24864023078b0a1866089dc5d79a8a7320fe45b81f7e10a9daa5cb80002671ee624b80be848800000000001222046000000022b942651ca47a4c4000068500d03c22214000170057288ec24f049660ea174000057657416ee0001b4a457157800006802bd1d8e00023fe73400000cb00002261cfc43d118e40709861f5a46007b8b303fe0ac244c86d45de038e6d9856850e8cf23e9a1bc60703943fa0920229061e4ec98145300d824e6947a0001994095911056f8be68380710803a12a139800053a0b96
  | 42 => 0x200003ce000216c00017fc00000000000000000000053623548b509c211a80003c097a48bf0000000196600000006e0000031500000000f225af947c70885b80000f4e39c00000000d6e055891434d81a86ae814a53d0dd88411c9c8878f6c1b80000000059c0001e282f218d400018b890a920270e9dc2000163c7c6983c00022a22891cf082d82f00bba3228450d2a3989d90847a0422968a98001173070420d49221f366bc12be329057812909001e49ab01e389e648c14fe31b01605bfa40c3a019725ed09424a99f9c5ab09f4212849c136068e6ff15ea11c02163b2983224291343da1b2e24189ae30f14882a10f5a09189886911b5e6d320780980b4a57d97ae76693fa89e16d26fa85aa09a969c20b9f1e0a1213240e9fdc3af22bc67519008fc213c0929e828401c5e0c99f8a3fa91ce89524000fc0dae75f01a02439cf478a8b0a30b1cd8399863c27e15d81730df277702088011b4836f000083e079a52105e67e015e8300123e01980f200000006e814621bc860c00004e4322944a02788fe4bc9fce7aa089c0000c9277c817232f86387370d2c3be16985be815e0b299fe8d68ec01c619f867018005df0ffe488a3f20710eb61ffa2ae68702a26d7000089382ae08e9a6e861a3cc68d8b3e598a054000236e3380bea6800b683a6a22c8c5004c50401f029b9c2055d0bfa0d8916243a9d5874d202e6c883b61daa35201f03845ea9e7e75b115663982283cf9f445320bb60001d460eca1b88c0848a30791d8574848e47303ba2b491a860b9d0c5aa8000000000003080004b793621fa1b3268687a84a6139e1d3188a3ce1fc80001f96000136e55500006be00007390fb874f941a5a88fbc2f517e26ae0dfc4de97a67d5963448980447369d1660f83c20cc07da77d83f211d155e62b154e46580006918d3a4c19cea5630f6e00001d207f800043b245c0d2807e41808cc22b0000364206467e8ef22ba9dec22f169a21908dc6b491500b68fac13f04100df8c1c3ee901000019346fb8ce8266211a56900000001f2006e816200013e87f919fc000017c77ea19491523ea5a5120863880008c79400589a3ee43900000001c287de0752000172441e896e1a78e0e1a806dc4bd0db638d882403b18f290803ca7b29ccc65d1dee24613f067c21dc2b318ee53790be24081068ba85ba1dd04a292198462591bbe9101bd08d0974a0c200001971c445530e1a73a000006f038a620800000005e800000006f6103059d8a6a7ee042c00000005092074005000000009c86f98a906c30b0e7538b840000f88000199c2440378497196e0001932110a19890601f23b69f1038d1c9028aa3be80d160c36391f646f00004f794f08988ade3ef8d30876a1c40a70f248311cce01380006e6247e4e2800000007a6000000042a80000f60000627960a25e
  | 43 => 0xa8d9634991306d5887e10f97603970d54051228460e02640001c5065c1f6281b1a660691622754822078001b42b4114c6dc00007298a046a600007e88b9276186e8000000000000007d218fc7fe000065e17867c880000aa92684dc22e4412800069d126a0af230c458054a172134c3ca89f03e581c2257168e25c1d9c0b987b889f0000760800054600de295874431a162a4f9006a0000efa14f10540d70000713000013d9ca007d08820001fd2706143275319f64d9a01861b1f5c1a6846244b9a946f90630915800057c000000018fa0001f685fb8e2e2631a8e85c8b4248a12643ca172236c8ec846187562eb1d728e6a1525fc9f901880000549000052a8e8a0000fb06ec80a630c20b40148a8882c912c89908b836223b690910c82399cb825f0574081007867a18868388a3610887f42a88b868b406b48d7080a79a9fac29f11fe08005728bd03f88b8241a3dc1a2a52f006e1cd81c04579f9e4cd9d7029512fa1480db854791727058686860831045a8b70415836604c1bc8235186a2cd979a7158a1414291524b692f6538233e48589242c498f87f623242cb0da00100582465228e23f01168a004f229123f8188862c17290ca7ca991e2c3226a3b81e8a0d386785340d7a1c6888e01601fc238135400000008b0a35082f00002e2800000010b43ad17e88c1064001d84c43411de28a708b60350aba86c181800020c81f3092886a224c5cf85e405a14221afa4688e7013679600000d08bd03e90000000216871a036e2dca0ea156170a00000007bb800053112065b0000050a80001268e5a5e51b2a28d0b346d6800016a1096000058600014c62b18b8e0db07fc7a91dc42cb82d854101881b2803e31d98564ab10140249884000000019f80008c6000000014e20b580007e1000000000004c11e6c5678000000000000000000d0012442d8000187000049e1c7c7e0926c2689fb42738000038149063722ce72d00bc70d20521df19163b61b7616388a81861eec65a89040000000000000000000883c491f47a7142058386663c9916c8a6909805e906a71a9e7a5b2800008b1e5c0950ba26b18a408d80fc855e83d4000000000013a000000002ab814600000000000ca07ad0000000150000000006199da452484aa2dba0147ee859e6c1964428881ca00c11c257c8a8e72e856e39a1b2837e167839b124a8559eac489000069f9fde3ac0768533000012f1e2660d033c00000004ba89fe24305da21194da4cea0fc3919cee603800035c00003b098b4000000084202b4433928a87b196800011b036d1cc467202688e51dae00007ae88704042d69474000000000023f68f5a00a00000da5e6045a02700f0000025a4061b3c798037625688ba55914402f1800000000000000000000000000007701e20c4037211e290182dc1f218ae69c897
  | 44 => 0xa28ff1a1810c109e118209e7758d061a406682f900000002072000021c61e23d41ce9b3439c8c8056b9e1248421d68b2883c0000000826814e4ee154600003f40002364661a22039a800000005368b5928000015060001dfc6280e3e72c1bb6000141c0bc80aa11f01be2391ac826f823e0000000704a38a409a15a00005f01ad80008a091a63d70c7a4ae12340f206ee00009d471015c441604d22be166080c00001de881c72b88225940592467231c52d00002eb94f21c98e0a6d0000089280007719ba82d71d020429f748868b7c8eb1f886b6a2686760c7800000003e0800082713860001f5a15ea3de0000fb2026819c11e9a4090e00001f8933400001c600823ae6971478340800064109800001f4a5e780a80c914044df9ee270ba29e5ac800000000000001168000000052e22f86a010c0112908a4e10a7a2898f104c0835e6cea2a057799763212020000000086496020000000244800000013c47ae00001c1800002d800052180000000dc07839dd833d934e721178446d8be25a58ff02fb1d8072f9ed626d238272794b0000000070700009228000642800000001000000000000222a46c9ab221a0134834199a5be1b507f5039a6d897620a78ae600023c471c80004728e7a1699af487d8ff67d7a4725ee102a5cb161466215448e485b65ad9e689048a4c1d0800049300006fa1bba0321a5678e07d04eb158419e800069e87d835e14dc41d8f4c6a69a600001300000151202c899a63c000000000000dc80f45aa00007a40000000000051188b485c000071b8cb428a083644a8dec72a8000000000000017c0366085c6a81b604c8017017a8e4e3fc80002109d920ae8a8c6e48000571850800e204e144a1f47bf863e1928d0e0568a200b50db02c881d62aa995c1d412ae02e10f28198e9e67080a020811ee7cb897825da1445309f6a6fc979000014d206e1bd664f0a9e4b000005a8000088000002c18000000170e0d4a10e7af96b41cd187040880008da1e5000000004c521c6520000000006bc6a4000042180006d91d7400001665a49cf27d480000e582761aba06e6cb00005568d8a2aa00000000dd071700000000a022fb8c568448cf45ef84328a51fb620c1b5403986584420e1c41310e273e95586c603fe5d5885800013d825200000000de2547000000009ec43080007cc08940888a16000000000019ee000000014a07a40000000612208c2cc8468599800059d075849d81ac5238000000145239095fe1a9a2ec0ab1624437093420300007ea80006338000000000000e8d8c6f8915487a128612810a04f516a47469c9802c05d82de9e547c501403e417ea6301ff653911243758d5a306918039f1d0a39308a654f17d67700f3466c89c6147151404887642d413822a00888352075e07387fa8909f725c607901c221f218
  | 45 => 0x16a6616934600014fc72a05ee00000002da800000000006de982216c19c46e905d0850044c09318064b90b5224f97b00001ff052c856429380008591aa600000004cb80002789a4e08405328db178002880988ec9f185f71e7018382f4346246a68f8cc645f04e24a521a00001b1a8c1a2460000e5e801908e2af10fc75d8ab21d28ca800023b000009847c1a2044e5096a000218e2800270620154a000085068e80003f98ccc6231abe8349c9a4aea3724168000000100a0001b166ea901e0000e206c11c8e42304585a419b471d127285d800082192cc086990e0971c3800003ae7f8033e78d00003729ed20000f0e70a868466a0de44dc90d20001cec21b9fca456a2285eb12c27479f1c6fd836a000000059f9ec40000d205de94ae77f8702000000016892a017d9c968610aa053b80000ef0d224f398d82b00b44146921881a840200f10a4637886a1e021964da0c16218082c88623ce1d5000000009d800018585cd032e80e24303bb8fdc7828816000000000000004bb84ee8b6000000017ca84a18f627680008048000000000000017a800022380001b6e84e80480ff057c2310c98424127e7969684000050c462000083021187be84924b1831800d06f68b896d81cf9e1451207dc2f71860180044484b8544035800004717486eba3465c11fc48cb23306d193ee4021a4854f84a6000237a56507ee28c870c2e7a29868a12423f48d2473500006da0f1c006207a56e861a63686341f113f482ba0ce6c08e143009f0450e035082395cc55012546e396de4918c323a9000086d9a546f79fee7ba0068605963a8b220f01938f8600000001eb0e322e50c087230f842ce0500000000000003c4267800071500000df21d871c085408795e61d215bc4b887f26c421602b6a474144127a56a1d488b7853028c1da01cc17f67fa8608000143021480000000aee3271dde7318798475085e70c1b1c45198965c691aa5d98a3c8cf205a65803c625b120a32317121b5962c5170c3e344030a0cd1f7079c97401ee9eba34f117650a09b26179e6204a13f212ea2162488bb272213d64d70c12914238e06ba44a3301d4217e026e5d904521ba898272499180f022aa1c8044e0f8165859385487a8238090f9f2435319
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x40142d921d76258e4100526a43659cf609040181e73e1563d82410050b64a7558b609040148d929cd62d82410054364a7354b609040161a93d805098241007035c9524c964cc401a0d824c8505933100703dc9424cb654c401a0d824c841d953100613609329c3654c40103d9810670d953100703dc9524cb644c40182d825c850d91310068360932143644c40142d921d764181310050b64875190604c40706c985c952181310040fe61741d1650c40144d92e0f7259431007035c9424c9650c44305c9760e41594310068360932105650c40181c73610705943100613609321c1650c55521c98595739043100495a468650e639400144d92d8d7298e5000703d8d7250a639400161691d8c4198e500050b64874d89639400105f9760f6418e5000607e538758c639400181c94e1d6318e500041764b8758c639400181f87e116318e5000607e1c8458c639400105f9858d7218e5000513e49635c8639400105f9760f6218e5000507e5d63d08639400141f9758d4218e5000417e5d864c8639400141f9758c4118e500060761d63104639400145691d9273d8650006079cf8458f619400142d929d162d86500051364a7358b619400150d929cd42d865000585a4f61106619400103f985d8769065000487e616318e419400105e989d9638c65000613e09325d8319400103e98105760c6500040fe61741d165cc001c0d725093259730006836093210565cc001c0f7250932d95300060b60972107654c001a0d824c841d953000703dc9524cb644c00188d824ca71d91300068360932143644c00103d989c450d91300050b64874d94614c00142d921d065185300142b26172508614c00148d92e0f7259030007035c9524c9640c00181c73614715903000623609321c5640c02509c9760e50590300068360932141640c00103d981c4505903000623e09325da410c00103e98141769043032c87261645ce500c00103f985d0745971000417e61731cd65c4001c0d7250932597100060b60b7210565c4001a0d824c841597100040f6627499663c4001c0d7254932592100060b60b721416484001a0d824c850592100040f662759926384001c0f7250932d951000683609321076544001c0f7254932d911000683609321436444001c0f7254942d8d100062360b72107634400184d82dc850d8d10004876604114363440016c2968862018d10006b0a1a218806344001c0d725494218d100062360972104634400184d825c85018d1000487660411406344001c0f75dd373d891000623a1f73107624400184e87dcc50d89100048b66041143624404305c985d5630c410094272617458c3004001c33769065044010006581ca879411004001c3376dd2504401000714ddb739411004001d40721ce504401000718ddb729411004001d80721047344010
  | 1 => 0xc9b03853724191b95b8950c000022002a200e0d35abba06800007b0002600088837801d142f1a000d80003c0000000000002d0200000000000f000000238000002790802080253489318000002ab20000000028000001b42c8092059d9280000a00028627003922a193331f1000001491800028b51c801680002980003680000000292597af800039b38b8fb0870036380026a300000013aead80000000163b2e19bab1111c2b1e9e1a80003b800aa10032800b189f89980eac0017048424830100408100400000c04001004140c00000018000c0c1c00040474001038080c380004000000040004040129a90a195398e410052364b635ca6390401c0f635c95298e4100586a43631426390
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x5
  | 3 => 0x6
  | 4 => 0x4b
  | 5 => 0x4d
  | 6 => 0x4e
  | 7 => 0x124b
  | 8 => 0x138b
  | 9 => 0x4
  | 10 => 0x94b
  | 11 => 0x94d
  | 12 => 0x94e
  | 13 => 0x124d
  | 14 => 0x124e
  | 15 => 0x138d
  | 16 => 0x138e
  | 17 => 0xcb
  | 18 => 0xcd
  | 19 => 0xce
  | 20 => 0x12cb
  | 21 => 0x9cb
  | 22 => 0x9cd
  | 23 => 0x9ce
  | 24 => 0x12cd
  | 25 => 0x12ce
  | 26 => 0x168b
  | 27 => 0x168d
  | 28 => 0x168e
  | 29 => 0x134b
  | 30 => 0x134d
  | 31 => 0x24b
  | 32 => 0x24d
  | 33 => 0x24e
  | 34 => 0x144b
  | 35 => 0xb4b
  | 36 => 0xb4d
  | 37 => 0xb4e
  | 38 => 0x144d
  | 39 => 0x144e
  | 40 => 0x16cb
  | 41 => 0x16cd
  | 42 => 0x16ce
  | 43 => 0x148b
  | 44 => 0x148e
  | 45 => 0x94053
  | 46 => 0x94055
  | 47 => 0x94056
  | 48 => 0x95393
  | 49 => 0x5253
  | 50 => 0x95253
  | 51 => 0x5393
  | 52 => 0x124055
  | 53 => 0x125393
  | 54 => 0x4953
  | 55 => 0x124053
  | 56 => 0x124056
  | 57 => 0x138056
  | 58 => 0x138053
  | 59 => 0x138055
  | 60 => 0x134055
  | 61 => 0x134053
  | 62 => 0x5353
  | 63 => 0x134c
  | 64 => 0x148056
  | 65 => 0x148053
  | 66 => 0x5493
  | 67 => 0x148c
  | 68 => 0x124953
  | 69 => 0x124956
  | 70 => 0x124955
  | 71 => 0x138953
  | 72 => 0x138955
  | 73 => 0x138956
  | 74 => 0x134953
  | 75 => 0x134955
  | 76 => 0x95353
  | 77 => 0x148953
  | 78 => 0x148956
  | 79 => 0x95493
  | 80 => 0x139255
  | 81 => 0x139253
  | 82 => 0x139256
  | 83 => 0x135253
  | 84 => 0x135255
  | 85 => 0x125353
  | 86 => 0x149253
  | 87 => 0x149256
  | 88 => 0x125493
  | 89 => 0x135393
  | 90 => 0x135395
  | 91 => 0x139353
  | 92 => 0x149396
  | 93 => 0x149393
  | 94 => 0x139493
  | 95 => 0x9c0d6
  | 96 => 0x9d2d3
  | 97 => 0x9c0d5
  | 98 => 0x9c0d3
  | 99 => 0xc9d3
  | 100 => 0x14c
  | 101 => 0x1340d5
  | 102 => 0x1340d3
  | 103 => 0xd353
  | 104 => 0x1440d6
  | 105 => 0x1452d3
  | 106 => 0x1440d5
  | 107 => 0x1440d3
  | 108 => 0xd453
  | 109 => 0x1480d6
  | 110 => 0x28c
  | 111 => 0x1480d3
  | 112 => 0xd493
  | 113 => 0x12c9d6
  | 114 => 0x12c9d5
  | 115 => 0x12c9d3
  | 116 => 0x1349d5
  | 117 => 0x1349d3
  | 118 => 0x9d353
  | 119 => 0x1489d6
  | 120 => 0x1489d3
  | 121 => 0x9d493
  | 122 => 0x130c
  | 123 => 0x1692d6
  | 124 => 0x1692d5
  | 125 => 0x1692d3
  | 126 => 0x12d693
  | 127 => 0x1352d5
  | 128 => 0x1352d3
  | 129 => 0x12d353
  | 130 => 0x252d6
  | 131 => 0x252d5
  | 132 => 0x252d3
  | 133 => 0x12c253
  | 134 => 0x1452d6
  | 135 => 0x1452d5
  | 136 => 0x12d453
  | 137 => 0x1492d6
  | 138 => 0x1492d3
  | 139 => 0x12d493
  | 140 => 0x135695
  | 141 => 0x135693
  | 142 => 0x169353
  | 143 => 0x149696
  | 144 => 0x149693
  | 145 => 0x169493
  | 146 => 0x25355
  | 147 => 0x25353
  | 148 => 0x134253
  | 149 => 0x134255
  | 150 => 0xb5355
  | 151 => 0xb5353
  | 152 => 0x134b53
  | 153 => 0x134b55
  | 154 => 0x145355
  | 155 => 0x145353
  | 156 => 0x135453
  | 157 => 0x135455
  | 158 => 0x16d355
  | 159 => 0x16d353
  | 160 => 0x1356d3
  | 161 => 0x1356d5
  | 162 => 0x149353
  | 163 => 0x14d
  | 164 => 0x135493
  | 165 => 0xb4256
  | 166 => 0xb4255
  | 167 => 0xb5453
  | 168 => 0xb4253
  | 169 => 0x24b53
  | 170 => 0x148256
  | 171 => 0x148253
  | 172 => 0x25493
  | 173 => 0x144b56
  | 174 => 0x144b55
  | 175 => 0x144b53
  | 176 => 0x148b56
  | 177 => 0x148b53
  | 178 => 0xb5493
  | 179 => 0x14cc
  | 180 => 0x16d456
  | 181 => 0x16d455
  | 182 => 0x16d453
  | 183 => 0x1456d3
  | 184 => 0x149456
  | 185 => 0x149453
  | 186 => 0x145493
  | 187 => 0x1496d6
  | 188 => 0x1496d3
  | 189 => 0x16d493
  | 190 => 0x5255
  | 191 => 0x1349405b
  | 192 => 0x940535b
  | 193 => 0x1349405d
  | 194 => 0x5396
  | 195 => 0x4955
  | 196 => 0x4956
  | 197 => 0x28e
  | 198 => 0xccd
  | 199 => 0xcce
  | 200 => 0x170d
  | 201 => 0x170e
  | 202 => 0xd0e
  | 203 => 0x188e
  | 204 => 0xd4d
  | 205 => 0x1a0d
  | 206 => 0x125396
  | 207 => 0x10c
  | 208 => 0x94153
  | 209 => 0x94155
  | 210 => 0x2cc
  | 211 => 0x94293
  | 212 => 0x94296
  | 213 => 0x14b
  | 214 => 0x28b
  | 215 => 0x188c
  | 216 => 0xd0c
  | 217 => 0x1a0c
  | 218 => 0xd4c
  | 219 => 0x95355
  | 220 => 0x14955
  | 221 => 0x95715
  | 222 => 0x94cd5
  | 223 => 0x95a15
  | 224 => 0x94d55
  | 225 => 0x95295
  | 226 => 0x95415
  | 227 => 0x95496
  | 228 => 0x28956
  | 229 => 0x95716
  | 230 => 0x94cd6
  | 231 => 0x95896
  | 232 => 0x94d16
  | 233 => 0x95296
  | 234 => 0x95416
  | 235 => 0x124155
  | 236 => 0x125355
  | 237 => 0x125395
  | 238 => 0x125715
  | 239 => 0x124cd5
  | 240 => 0x125a15
  | 241 => 0x124d55
  | 242 => 0x124215
  | 243 => 0x124995
  | 244 => 0x124293
  | 245 => 0x138296
  | 246 => 0x139496
  | 247 => 0x139716
  | 248 => 0x138cd6
  | 249 => 0x139896
  | 250 => 0x138d16
  | 251 => 0x138096
  | 252 => 0x138b16
  | 253 => 0x138153
  | 254 => 0xd355
  | 255 => 0x140d5
  | 256 => 0xc9d5
  | 257 => 0xd455
  | 258 => 0xcb55
  | 259 => 0xd40d5
  | 260 => 0x1a00d5
  | 261 => 0xd5d5
  | 262 => 0xccd5
  | 263 => 0x104c
  | 264 => 0xda55
  | 265 => 0xced5
  | 266 => 0x194c
  | 267 => 0x12d696
  | 268 => 0x9c155
  | 269 => 0x9c296
  | 270 => 0x9d355
  | 271 => 0x149d5
  | 272 => 0x9ccd5
  | 273 => 0x9da15
  | 274 => 0x9cd55
  | 275 => 0x9d496
  | 276 => 0x9ccd6
  | 277 => 0x9d896
  | 278 => 0x9cd16
  | 279 => 0x135692dd
  | 280 => 0x135692db
  | 281 => 0x169456
  | 282 => 0x168cd6
  | 283 => 0x168e96
  | 284 => 0xb4155
  | 285 => 0x29256
  | 286 => 0x95256
  | 287 => 0xcd256
  | 288 => 0x171256
  | 289 => 0xd1256
  | 290 => 0x189256
  | 291 => 0x99256
  | 292 => 0x129256
  | 293 => 0x4096
  | 294 => 0xcd355
  | 295 => 0x171355
  | 296 => 0x28056
  | 297 => 0xcc056
  | 298 => 0x170056
  | 299 => 0xd0056
  | 300 => 0x188056
  | 301 => 0x292d6
  | 302 => 0xcd2d6
  | 303 => 0xd12d6
  | 304 => 0x1892d6
  | 305 => 0x9d2d6
  | 306 => 0x1680d6
  | 307 => 0x280d6
  | 308 => 0xcc0d6
  | 309 => 0x1700d6
  | 310 => 0xd00d6
  | 311 => 0x1880d6
  | 312 => 0x25496
  | 313 => 0x249d6
  | 314 => 0x28256
  | 315 => 0x24b56
  | 316 => 0xd0256
  | 317 => 0x188256
  | 318 => 0x255d6
  | 319 => 0x24cd6
  | 320 => 0x258d6
  | 321 => 0x24e96
  | 322 => 0x1a8c
  | 323 => 0x1456d5
  | 324 => 0xb4296
  | 325 => 0xb4cd5
  | 326 => 0xb5a15
  | 327 => 0xb4d55
  | 328 => 0xb5496
  | 329 => 0x28b56
  | 330 => 0xb4cd6
  | 331 => 0xb5896
  | 332 => 0xb4d16
  | 333 => 0x16d2d5
  | 334 => 0x16ccd5
  | 335 => 0x16ced5
  | 336 => 0x15395
  | 337 => 0x95395
  | 338 => 0xcd395
  | 339 => 0x171395
  | 340 => 0xd5395
  | 341 => 0x1a1395
  | 342 => 0xb1395
  | 343 => 0x141395
  | 344 => 0x4215
  | 345 => 0xcd496
  | 346 => 0x171496
  | 347 => 0x14055
  | 348 => 0xcc055
  | 349 => 0x170055
  | 350 => 0xd4055
  | 351 => 0x1a0055
  | 352 => 0x15455
  | 353 => 0xcd455
  | 354 => 0xd5455
  | 355 => 0x1a1455
  | 356 => 0xb5455
  | 357 => 0x16c255
  | 358 => 0x14255
  | 359 => 0xcc255
  | 360 => 0x170255
  | 361 => 0xd4255
  | 362 => 0x1a0255
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 70
  | 7 => 1351
  | 6 => 4059
  | 5 => 4682
  | 4 => 121
  | _ => 0
def gbR (k i : Nat) : Nat :=
  match k with
  | 9 => packedAt gbK9 (i*15) 6
  | 8 => packedAt gbK8 (i*26) 17
  | 7 => packedAt gbK7 (i*37) 28
  | 6 => packedAt gbK6 (i*48) 39
  | 5 => packedAt gbK5 (i*59) 50
  | 4 => packedAt gbK4 (i*70) 61
  | _ => 0
def gbH (k i : Nat) : Nat :=
  match k with
  | 9 => gbHint (packedAt gbK9 (i*15+6) 9)
  | 8 => gbHint (packedAt gbK8 (i*26+17) 9)
  | 7 => gbHint (packedAt gbK7 (i*37+28) 9)
  | 6 => gbHint (packedAt gbK6 (i*48+39) 9)
  | 5 => gbHint (packedAt gbK5 (i*59+50) 9)
  | 4 => gbHint (packedAt gbK4 (i*70+61) 9)
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 9 => packedAt gbK9 (16+((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 2)*1) 1
  | 8 => packedAt gbK8 (1981+((h/23+packedAt gbK8 (1820+(h % 23)*7) 7) % 85)*8) 8
  | 7 => packedAt gbK7 (54937+((h/450+packedAt gbK7 (49987+(h % 450)*11) 11) % 1622)*12) 12
  | 6 => packedAt gbK6 (212421+((h/1353+packedAt gbK6 (194832+(h % 1353)*13) 13) % 5893)*13) 13
  | 5 => packedAt gbK5 (296518+((h/1560+packedAt gbK5 (276238+(h % 1560)*13) 13) % 5619)*14) 14
  | 4 => packedAt gbK4 (8790+((h/40+packedAt gbK4 (8470+(h % 40)*8) 8) % 193)*8) 8
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xff81ffe01e07fffc0fffc03fd1cf3e7dc1f3f3
  | 1 => 0x7ffe07fffff80ffff03fffc02e33d19e7e7cfc
  | 2 => 0x81fff8001ffff03fffc1fffff03ce1e3878f1f
  | 3 => 0x1ffffffe000003ffffe00003fc0fe03f80fe0
  | 4 => 0x1ffffffffffffc0000000003fff0003fff000
  | 5 => 0xfe00000000000000000000003ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0xa28029610602964c0252409580c5062cc0b171
  | 1 => 0x540a02ac2a88089510249580861250941a54b4
  | 2 => 0x155500211552022ac812a2a3028a143050a0a
  | 3 => 0x11e79cd74041823bcf3803033b40fa03e80fc0
  | 4 => 0x61f9e71b9de7cf0086100c0c3dff0003f7e000
  | 5 => 0x7841001c01860c03082030303fbffdf8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeee8eae8ece8e8e0eee8eae8ece8e8e0eee8eae8ece8e8e0eee8eae8ece8e8e0eee8eae8ece8e8e0eee8eae8ece8e8e0eee8eae8ece8e8e0eee8eae8ece8e8e0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_16333
namespace PEqualNP.Outside.L_meta_16333
open PEqualNP.Outside.L_meta_16333.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs2_2_0 : Interval s2Atlas 2 0 15 := block_range (n:=15) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 15 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_32 : Interval s2Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_64 : Interval s2Atlas 3 64 4 := block_range (n:=4) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 68 := (concat bs2_3_0 (concat bs2_3_32 bs2_3_64))
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
theorem bs2_4_160 : Interval s2Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_192 : Interval s2Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_224 : Interval s2Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_256 : Interval s2Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_288 : Interval s2Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_320 : Interval s2Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_352 : Interval s2Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_384 : Interval s2Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_416 : Interval s2Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_448 : Interval s2Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_480 : Interval s2Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_512 : Interval s2Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_544 : Interval s2Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_576 : Interval s2Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_608 : Interval s2Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_640 : Interval s2Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_672 : Interval s2Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_704 : Interval s2Atlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_736 : Interval s2Atlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_768 : Interval s2Atlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_800 : Interval s2Atlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_832 : Interval s2Atlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_864 : Interval s2Atlas 4 864 30 := block_range (n:=30) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 894 := (concat (concat (concat (concat bs2_4_0 (concat bs2_4_32 bs2_4_64)) (concat (concat bs2_4_96 bs2_4_128) (concat bs2_4_160 bs2_4_192))) (concat (concat bs2_4_224 (concat bs2_4_256 bs2_4_288)) (concat (concat bs2_4_320 bs2_4_352) (concat bs2_4_384 bs2_4_416)))) (concat (concat (concat bs2_4_448 (concat bs2_4_480 bs2_4_512)) (concat (concat bs2_4_544 bs2_4_576) (concat bs2_4_608 bs2_4_640))) (concat (concat bs2_4_672 (concat bs2_4_704 bs2_4_736)) (concat (concat bs2_4_768 bs2_4_800) (concat bs2_4_832 bs2_4_864)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_64 : Interval s2Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_96 : Interval s2Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_128 : Interval s2Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_160 : Interval s2Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_192 : Interval s2Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_224 : Interval s2Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_256 : Interval s2Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_288 : Interval s2Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_320 : Interval s2Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_352 : Interval s2Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_384 : Interval s2Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_416 : Interval s2Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_448 : Interval s2Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_480 : Interval s2Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_512 : Interval s2Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_544 : Interval s2Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_576 : Interval s2Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_608 : Interval s2Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_640 : Interval s2Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_672 : Interval s2Atlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_704 : Interval s2Atlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_736 : Interval s2Atlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_768 : Interval s2Atlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_800 : Interval s2Atlas 5 800 20 := block_range (n:=20) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 820 := (concat (concat (concat (concat bs2_5_0 (concat bs2_5_32 bs2_5_64)) (concat bs2_5_96 (concat bs2_5_128 bs2_5_160))) (concat (concat bs2_5_192 (concat bs2_5_224 bs2_5_256)) (concat (concat bs2_5_288 bs2_5_320) (concat bs2_5_352 bs2_5_384)))) (concat (concat (concat bs2_5_416 (concat bs2_5_448 bs2_5_480)) (concat bs2_5_512 (concat bs2_5_544 bs2_5_576))) (concat (concat bs2_5_608 (concat bs2_5_640 bs2_5_672)) (concat (concat bs2_5_704 bs2_5_736) (concat bs2_5_768 bs2_5_800)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_0 : Interval s2Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_32 : Interval s2Atlas 6 32 12 := block_range (n:=12) (by decide +kernel)
theorem alls2_6 : Interval s2Atlas 6 0 44 := (concat bs2_6_0 bs2_6_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_7_0 : Interval s2Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_7 : Interval s2Atlas 7 0 1 := bs2_7_0
theorem alls2 : ∀ k ≤ 7, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_2 i (by omega) hi
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
  · exact alls2_6 i (by omega) hi
  · exact alls2_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_0 : Interval s3Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 4 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 13 := block_range (n:=13) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 13 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 17 := block_range (n:=17) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 17 := bs3_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 1 := bs3_5_0
theorem alls3 : ∀ k ≤ 5, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_2 i (by omega) hi
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_0 : Interval s4Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 10 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_32 : Interval s4Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_64 : Interval s4Atlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_96 : Interval s4Atlas 3 96 16 := block_range (n:=16) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 112 := (concat (concat bs4_3_0 bs4_3_32) (concat bs4_3_64 bs4_3_96))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_32 : Interval s4Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_64 : Interval s4Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_96 : Interval s4Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_128 : Interval s4Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_160 : Interval s4Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_192 : Interval s4Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_224 : Interval s4Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_256 : Interval s4Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_288 : Interval s4Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_320 : Interval s4Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_352 : Interval s4Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_384 : Interval s4Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_416 : Interval s4Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_448 : Interval s4Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_480 : Interval s4Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_512 : Interval s4Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_544 : Interval s4Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_576 : Interval s4Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_608 : Interval s4Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_640 : Interval s4Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_672 : Interval s4Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_704 : Interval s4Atlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_736 : Interval s4Atlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_768 : Interval s4Atlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_800 : Interval s4Atlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_832 : Interval s4Atlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_864 : Interval s4Atlas 4 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_896 : Interval s4Atlas 4 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_928 : Interval s4Atlas 4 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_960 : Interval s4Atlas 4 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_992 : Interval s4Atlas 4 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1024 : Interval s4Atlas 4 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1056 : Interval s4Atlas 4 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1088 : Interval s4Atlas 4 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1120 : Interval s4Atlas 4 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1152 : Interval s4Atlas 4 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1184 : Interval s4Atlas 4 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1216 : Interval s4Atlas 4 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1248 : Interval s4Atlas 4 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1280 : Interval s4Atlas 4 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1312 : Interval s4Atlas 4 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_1344 : Interval s4Atlas 4 1344 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 1345 := (concat (concat (concat (concat (concat bs4_4_0 bs4_4_32) (concat bs4_4_64 (concat bs4_4_96 bs4_4_128))) (concat (concat bs4_4_160 bs4_4_192) (concat bs4_4_224 (concat bs4_4_256 bs4_4_288)))) (concat (concat (concat bs4_4_320 bs4_4_352) (concat bs4_4_384 (concat bs4_4_416 bs4_4_448))) (concat (concat bs4_4_480 (concat bs4_4_512 bs4_4_544)) (concat bs4_4_576 (concat bs4_4_608 bs4_4_640))))) (concat (concat (concat (concat bs4_4_672 bs4_4_704) (concat bs4_4_736 (concat bs4_4_768 bs4_4_800))) (concat (concat bs4_4_832 (concat bs4_4_864 bs4_4_896)) (concat bs4_4_928 (concat bs4_4_960 bs4_4_992)))) (concat (concat (concat bs4_4_1024 bs4_4_1056) (concat bs4_4_1088 (concat bs4_4_1120 bs4_4_1152))) (concat (concat bs4_4_1184 (concat bs4_4_1216 bs4_4_1248)) (concat bs4_4_1280 (concat bs4_4_1312 bs4_4_1344))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_64 : Interval s4Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_96 : Interval s4Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_128 : Interval s4Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_160 : Interval s4Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_192 : Interval s4Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_224 : Interval s4Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_256 : Interval s4Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_288 : Interval s4Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_320 : Interval s4Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_352 : Interval s4Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_384 : Interval s4Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_416 : Interval s4Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_448 : Interval s4Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_480 : Interval s4Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_512 : Interval s4Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_544 : Interval s4Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_576 : Interval s4Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_608 : Interval s4Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_640 : Interval s4Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_672 : Interval s4Atlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_704 : Interval s4Atlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_736 : Interval s4Atlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_768 : Interval s4Atlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_800 : Interval s4Atlas 5 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_832 : Interval s4Atlas 5 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_864 : Interval s4Atlas 5 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_896 : Interval s4Atlas 5 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_928 : Interval s4Atlas 5 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_960 : Interval s4Atlas 5 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_992 : Interval s4Atlas 5 992 25 := block_range (n:=25) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 1017 := (concat (concat (concat (concat (concat bs4_5_0 bs4_5_32) (concat bs4_5_64 bs4_5_96)) (concat (concat bs4_5_128 bs4_5_160) (concat bs4_5_192 bs4_5_224))) (concat (concat (concat bs4_5_256 bs4_5_288) (concat bs4_5_320 bs4_5_352)) (concat (concat bs4_5_384 bs4_5_416) (concat bs4_5_448 bs4_5_480)))) (concat (concat (concat (concat bs4_5_512 bs4_5_544) (concat bs4_5_576 bs4_5_608)) (concat (concat bs4_5_640 bs4_5_672) (concat bs4_5_704 bs4_5_736))) (concat (concat (concat bs4_5_768 bs4_5_800) (concat bs4_5_832 bs4_5_864)) (concat (concat bs4_5_896 bs4_5_928) (concat bs4_5_960 bs4_5_992)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_32 : Interval s4Atlas 6 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 48 := (concat bs4_6_0 bs4_6_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_7_0 : Interval s4Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_7 : Interval s4Atlas 7 0 1 := bs4_7_0
theorem alls4 : ∀ k ≤ 7, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_2 i (by omega) hi
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
  · exact alls4_6 i (by omega) hi
  · exact alls4_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_0 : Interval s5Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 10 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_32 : Interval s5Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_64 : Interval s5Atlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_96 : Interval s5Atlas 3 96 16 := block_range (n:=16) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 112 := (concat (concat bs5_3_0 bs5_3_32) (concat bs5_3_64 bs5_3_96))
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
theorem bs5_4_96 : Interval s5Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_128 : Interval s5Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_160 : Interval s5Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_192 : Interval s5Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_224 : Interval s5Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_256 : Interval s5Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_288 : Interval s5Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_320 : Interval s5Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_352 : Interval s5Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_384 : Interval s5Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_416 : Interval s5Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_448 : Interval s5Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_480 : Interval s5Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_512 : Interval s5Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_544 : Interval s5Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_576 : Interval s5Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_608 : Interval s5Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_640 : Interval s5Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_672 : Interval s5Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_704 : Interval s5Atlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_736 : Interval s5Atlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_768 : Interval s5Atlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_800 : Interval s5Atlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_832 : Interval s5Atlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_864 : Interval s5Atlas 4 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_896 : Interval s5Atlas 4 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_928 : Interval s5Atlas 4 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_960 : Interval s5Atlas 4 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_992 : Interval s5Atlas 4 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1024 : Interval s5Atlas 4 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1056 : Interval s5Atlas 4 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1088 : Interval s5Atlas 4 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1120 : Interval s5Atlas 4 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1152 : Interval s5Atlas 4 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1184 : Interval s5Atlas 4 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1216 : Interval s5Atlas 4 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1248 : Interval s5Atlas 4 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1280 : Interval s5Atlas 4 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1312 : Interval s5Atlas 4 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_1344 : Interval s5Atlas 4 1344 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 1345 := (concat (concat (concat (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 (concat bs5_4_96 bs5_4_128))) (concat (concat bs5_4_160 bs5_4_192) (concat bs5_4_224 (concat bs5_4_256 bs5_4_288)))) (concat (concat (concat bs5_4_320 bs5_4_352) (concat bs5_4_384 (concat bs5_4_416 bs5_4_448))) (concat (concat bs5_4_480 (concat bs5_4_512 bs5_4_544)) (concat bs5_4_576 (concat bs5_4_608 bs5_4_640))))) (concat (concat (concat (concat bs5_4_672 bs5_4_704) (concat bs5_4_736 (concat bs5_4_768 bs5_4_800))) (concat (concat bs5_4_832 (concat bs5_4_864 bs5_4_896)) (concat bs5_4_928 (concat bs5_4_960 bs5_4_992)))) (concat (concat (concat bs5_4_1024 bs5_4_1056) (concat bs5_4_1088 (concat bs5_4_1120 bs5_4_1152))) (concat (concat bs5_4_1184 (concat bs5_4_1216 bs5_4_1248)) (concat bs5_4_1280 (concat bs5_4_1312 bs5_4_1344))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_64 : Interval s5Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_96 : Interval s5Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_128 : Interval s5Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_160 : Interval s5Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_192 : Interval s5Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_224 : Interval s5Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_256 : Interval s5Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_288 : Interval s5Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_320 : Interval s5Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_352 : Interval s5Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_384 : Interval s5Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_416 : Interval s5Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_448 : Interval s5Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_480 : Interval s5Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_512 : Interval s5Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_544 : Interval s5Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_576 : Interval s5Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_608 : Interval s5Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_640 : Interval s5Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_672 : Interval s5Atlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_704 : Interval s5Atlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_736 : Interval s5Atlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_768 : Interval s5Atlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_800 : Interval s5Atlas 5 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_832 : Interval s5Atlas 5 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_864 : Interval s5Atlas 5 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_896 : Interval s5Atlas 5 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_928 : Interval s5Atlas 5 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_960 : Interval s5Atlas 5 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_992 : Interval s5Atlas 5 992 25 := block_range (n:=25) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 1017 := (concat (concat (concat (concat (concat bs5_5_0 bs5_5_32) (concat bs5_5_64 bs5_5_96)) (concat (concat bs5_5_128 bs5_5_160) (concat bs5_5_192 bs5_5_224))) (concat (concat (concat bs5_5_256 bs5_5_288) (concat bs5_5_320 bs5_5_352)) (concat (concat bs5_5_384 bs5_5_416) (concat bs5_5_448 bs5_5_480)))) (concat (concat (concat (concat bs5_5_512 bs5_5_544) (concat bs5_5_576 bs5_5_608)) (concat (concat bs5_5_640 bs5_5_672) (concat bs5_5_704 bs5_5_736))) (concat (concat (concat bs5_5_768 bs5_5_800) (concat bs5_5_832 bs5_5_864)) (concat (concat bs5_5_896 bs5_5_928) (concat bs5_5_960 bs5_5_992)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_32 : Interval s5Atlas 6 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 48 := (concat bs5_6_0 bs5_6_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_7_0 : Interval s5Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_7 : Interval s5Atlas 7 0 1 := bs5_7_0
theorem alls5 : ∀ k ≤ 7, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_2 i (by omega) hi
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
  · exact alls5_6 i (by omega) hi
  · exact alls5_7 i (by omega) hi
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
theorem bgb_4_96 : Interval gbAtlas 4 96 25 := block_range (n:=25) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 121 := (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96))
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
theorem bgb_5_4672 : Interval gbAtlas 5 4672 10 := block_range (n:=10) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 4682 := (concat (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)))) (concat (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 bgb_5_384)) (concat (concat bgb_5_416 bgb_5_448) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544))))) (concat (concat (concat (concat bgb_5_576 bgb_5_608) (concat bgb_5_640 bgb_5_672)) (concat (concat bgb_5_704 bgb_5_736) (concat bgb_5_768 (concat bgb_5_800 bgb_5_832)))) (concat (concat (concat bgb_5_864 bgb_5_896) (concat bgb_5_928 bgb_5_960)) (concat (concat bgb_5_992 bgb_5_1024) (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120)))))) (concat (concat (concat (concat (concat bgb_5_1152 bgb_5_1184) (concat bgb_5_1216 bgb_5_1248)) (concat (concat bgb_5_1280 bgb_5_1312) (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408)))) (concat (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 bgb_5_1536)) (concat (concat bgb_5_1568 bgb_5_1600) (concat bgb_5_1632 (concat bgb_5_1664 bgb_5_1696))))) (concat (concat (concat (concat bgb_5_1728 bgb_5_1760) (concat bgb_5_1792 bgb_5_1824)) (concat (concat bgb_5_1856 bgb_5_1888) (concat bgb_5_1920 (concat bgb_5_1952 bgb_5_1984)))) (concat (concat (concat bgb_5_2016 bgb_5_2048) (concat bgb_5_2080 (concat bgb_5_2112 bgb_5_2144))) (concat (concat bgb_5_2176 bgb_5_2208) (concat bgb_5_2240 (concat bgb_5_2272 bgb_5_2304))))))) (concat (concat (concat (concat (concat (concat bgb_5_2336 bgb_5_2368) (concat bgb_5_2400 bgb_5_2432)) (concat (concat bgb_5_2464 bgb_5_2496) (concat bgb_5_2528 (concat bgb_5_2560 bgb_5_2592)))) (concat (concat (concat bgb_5_2624 bgb_5_2656) (concat bgb_5_2688 bgb_5_2720)) (concat (concat bgb_5_2752 bgb_5_2784) (concat bgb_5_2816 (concat bgb_5_2848 bgb_5_2880))))) (concat (concat (concat (concat bgb_5_2912 bgb_5_2944) (concat bgb_5_2976 bgb_5_3008)) (concat (concat bgb_5_3040 bgb_5_3072) (concat bgb_5_3104 (concat bgb_5_3136 bgb_5_3168)))) (concat (concat (concat bgb_5_3200 bgb_5_3232) (concat bgb_5_3264 (concat bgb_5_3296 bgb_5_3328))) (concat (concat bgb_5_3360 bgb_5_3392) (concat bgb_5_3424 (concat bgb_5_3456 bgb_5_3488)))))) (concat (concat (concat (concat (concat bgb_5_3520 bgb_5_3552) (concat bgb_5_3584 bgb_5_3616)) (concat (concat bgb_5_3648 bgb_5_3680) (concat bgb_5_3712 (concat bgb_5_3744 bgb_5_3776)))) (concat (concat (concat bgb_5_3808 bgb_5_3840) (concat bgb_5_3872 bgb_5_3904)) (concat (concat bgb_5_3936 bgb_5_3968) (concat bgb_5_4000 (concat bgb_5_4032 bgb_5_4064))))) (concat (concat (concat (concat bgb_5_4096 bgb_5_4128) (concat bgb_5_4160 bgb_5_4192)) (concat (concat bgb_5_4224 bgb_5_4256) (concat bgb_5_4288 (concat bgb_5_4320 bgb_5_4352)))) (concat (concat (concat bgb_5_4384 bgb_5_4416) (concat bgb_5_4448 (concat bgb_5_4480 bgb_5_4512))) (concat (concat bgb_5_4544 bgb_5_4576) (concat bgb_5_4608 (concat bgb_5_4640 bgb_5_4672))))))))
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
theorem bgb_6_4032 : Interval gbAtlas 6 4032 27 := block_range (n:=27) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 4059 := (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat (concat bgb_6_224 bgb_6_256) (concat bgb_6_288 bgb_6_320)) (concat (concat bgb_6_352 bgb_6_384) (concat bgb_6_416 bgb_6_448)))) (concat (concat (concat (concat bgb_6_480 bgb_6_512) (concat bgb_6_544 bgb_6_576)) (concat (concat bgb_6_608 bgb_6_640) (concat bgb_6_672 bgb_6_704))) (concat (concat (concat bgb_6_736 bgb_6_768) (concat bgb_6_800 bgb_6_832)) (concat (concat bgb_6_864 bgb_6_896) (concat bgb_6_928 bgb_6_960))))) (concat (concat (concat (concat (concat bgb_6_992 bgb_6_1024) (concat bgb_6_1056 bgb_6_1088)) (concat (concat bgb_6_1120 bgb_6_1152) (concat bgb_6_1184 bgb_6_1216))) (concat (concat (concat bgb_6_1248 bgb_6_1280) (concat bgb_6_1312 bgb_6_1344)) (concat (concat bgb_6_1376 bgb_6_1408) (concat bgb_6_1440 bgb_6_1472)))) (concat (concat (concat (concat bgb_6_1504 bgb_6_1536) (concat bgb_6_1568 bgb_6_1600)) (concat (concat bgb_6_1632 bgb_6_1664) (concat bgb_6_1696 bgb_6_1728))) (concat (concat (concat bgb_6_1760 bgb_6_1792) (concat bgb_6_1824 bgb_6_1856)) (concat (concat bgb_6_1888 bgb_6_1920) (concat bgb_6_1952 bgb_6_1984)))))) (concat (concat (concat (concat (concat (concat bgb_6_2016 bgb_6_2048) (concat bgb_6_2080 bgb_6_2112)) (concat (concat bgb_6_2144 bgb_6_2176) (concat bgb_6_2208 bgb_6_2240))) (concat (concat (concat bgb_6_2272 bgb_6_2304) (concat bgb_6_2336 bgb_6_2368)) (concat (concat bgb_6_2400 bgb_6_2432) (concat bgb_6_2464 bgb_6_2496)))) (concat (concat (concat (concat bgb_6_2528 bgb_6_2560) (concat bgb_6_2592 bgb_6_2624)) (concat (concat bgb_6_2656 bgb_6_2688) (concat bgb_6_2720 bgb_6_2752))) (concat (concat (concat bgb_6_2784 bgb_6_2816) (concat bgb_6_2848 bgb_6_2880)) (concat (concat bgb_6_2912 bgb_6_2944) (concat bgb_6_2976 bgb_6_3008))))) (concat (concat (concat (concat (concat bgb_6_3040 bgb_6_3072) (concat bgb_6_3104 bgb_6_3136)) (concat (concat bgb_6_3168 bgb_6_3200) (concat bgb_6_3232 bgb_6_3264))) (concat (concat (concat bgb_6_3296 bgb_6_3328) (concat bgb_6_3360 bgb_6_3392)) (concat (concat bgb_6_3424 bgb_6_3456) (concat bgb_6_3488 bgb_6_3520)))) (concat (concat (concat (concat bgb_6_3552 bgb_6_3584) (concat bgb_6_3616 bgb_6_3648)) (concat (concat bgb_6_3680 bgb_6_3712) (concat bgb_6_3744 bgb_6_3776))) (concat (concat (concat bgb_6_3808 bgb_6_3840) (concat bgb_6_3872 bgb_6_3904)) (concat (concat bgb_6_3936 bgb_6_3968) (concat bgb_6_4000 bgb_6_4032)))))))
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
theorem bgb_7_1344 : Interval gbAtlas 7 1344 7 := block_range (n:=7) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1351 := (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 (concat bgb_7_96 bgb_7_128))) (concat (concat bgb_7_160 bgb_7_192) (concat bgb_7_224 (concat bgb_7_256 bgb_7_288)))) (concat (concat (concat bgb_7_320 bgb_7_352) (concat bgb_7_384 (concat bgb_7_416 bgb_7_448))) (concat (concat bgb_7_480 (concat bgb_7_512 bgb_7_544)) (concat bgb_7_576 (concat bgb_7_608 bgb_7_640))))) (concat (concat (concat (concat bgb_7_672 bgb_7_704) (concat bgb_7_736 (concat bgb_7_768 bgb_7_800))) (concat (concat bgb_7_832 (concat bgb_7_864 bgb_7_896)) (concat bgb_7_928 (concat bgb_7_960 bgb_7_992)))) (concat (concat (concat bgb_7_1024 bgb_7_1056) (concat bgb_7_1088 (concat bgb_7_1120 bgb_7_1152))) (concat (concat bgb_7_1184 (concat bgb_7_1216 bgb_7_1248)) (concat bgb_7_1280 (concat bgb_7_1312 bgb_7_1344))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_64 : Interval gbAtlas 8 64 6 := block_range (n:=6) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 70 := (concat bgb_8_0 (concat bgb_8_32 bgb_8_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_9_0 : Interval gbAtlas 9 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_9 : Interval gbAtlas 9 0 1 := bgb_9_0
theorem allgb : ∀ k ≤ 9, ∀ i < count gbAtlas k, checkRow gbAtlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 3 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 10, 26)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 3 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 33, 41),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 8 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 10, 11),(inputs.getD 1 zero, 9, 11),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 8 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeee8eae8ece8e8e0eee8eae8ece8e8e0eee8eae8ece8e8e0eee8eae8ece8e8e0eee8eae8ece8e8e0eee8eae8ece8e8e0eee8eae8ece8e8e0eee8eae8ece8e8e0
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 33 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) (SBf 1) :=
    slice_correct (ms:=fixRows 18 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008241896 * 2 ^ 32 + 3974686944) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_16333.Model.Repr at out
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

def mono : List Gate := [⟨.or,[2,5]⟩,⟨.and,[0,6]⟩,⟨.and,[0,3]⟩,⟨.or,[2,8]⟩,⟨.or,[0,3]⟩,⟨.or,[4,9]⟩,⟨.and,[1,11]⟩,⟨.and,[1,10]⟩,⟨.or,[9,13]⟩,⟨.or,[7,12]⟩,⟨.and,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241896 * 2 ^ 32 + 3974686944) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241896 * 2 ^ 32 + 3974686944) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_16333

open PEqualNP.Outside.L_meta_16333 in
theorem PEqualNP.Outside.L_meta_16333 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241896 * 2 ^ 32 + 3974686944) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241896 * 2 ^ 32 + 3974686944) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
