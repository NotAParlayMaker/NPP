import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_15233.Model
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


end PEqualNP.Outside.L_meta_15233.Model

namespace PEqualNP.Outside.L_meta_15233
open PEqualNP.Outside.L_meta_15233.Model
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

def SBf (j : Nat) : Nat := [3, 3, 3, 5, 6, 4].getD j 0

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

def mirrorSteps : List Move := [swapRows 33]

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

end PEqualNP.Outside.L_meta_15233

namespace PEqualNP.Outside.L_meta_15233
open PEqualNP.Outside.L_meta_15233.Model
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
end PEqualNP.Outside.L_meta_15233
namespace PEqualNP.Outside.L_meta_15233
open PEqualNP.Outside.L_meta_15233.Model
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
  | 5 => 0xffffffffffffffffffffffffffffffffffffff
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffff81222ca55b
  | 2 => 0xffffffffffffffffffffffffffffa2e45696c5
  | 3 => 0x144e9ad4e8
  | 5 => 0x888e318b6
  | _ => 0
def s1Atlas : Atlas := ⟨2,rawDecor 45 s1Pos s1Neg, 0xaaa0aaa000000000aaa0aaa000000000aaa0aaa000000000aaa0aaa000000000aaa0aaa000000000aaa0aaa000000000aaa0aaa000000000aaa0aaa000000000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_15233
namespace PEqualNP.Outside.L_meta_15233
open PEqualNP.Outside.L_meta_15233.Model
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
  | 5 => 0xffffffffffffffffffffffffffffffffffffff
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffff81222ca55b
  | 1 => 0xffffffffffffffffffffffffffffa2e45696c5
  | 3 => 0x144e9ad4e8
  | 5 => 0x888e318b6
  | _ => 0
def s2Atlas : Atlas := ⟨2,rawDecor 43 s2Pos s2Neg, 0xaa88aa8800000000aa88aa8800000000aa88aa8800000000aa88aa8800000000aa88aa8800000000aa88aa8800000000aa88aa8800000000aa88aa8800000000, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_15233
namespace PEqualNP.Outside.L_meta_15233
open PEqualNP.Outside.L_meta_15233.Model
def s3K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x102281808002f185c30dc41b083b087410
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x140320c020d030043808010
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 3
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s3K4 (i*4) 4
  | 3 => packedAt s3K3 (i*15) 15
  | 2 => packedAt s3K2 (i*26) 26
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s3K4 (5+((h/1+packedAt s3K4 (4+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt s3K3 (98+((h/2+packedAt s3K3 (90+(h % 2)*4) 4) % 11)*4) 4
  | 2 => packedAt s3K2 (81+((h/1+packedAt s3K2 (78+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 1 => 0xffffffffffffffffffffffffffbf0fffc3fe3f
  | 2 => 0xffffffffffffffffffffffffffdff0fffc3fc7
  | 5 => 0xefff0fffc3f8
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffff012222c444db
  | 1 => 0xffffffffffffffffffffffffff42e44562aa2d
  | 2 => 0x244e89aa3346
  | 5 => 0x1888ee3323b0
  | _ => 0
def s3Atlas : Atlas := ⟨4,rawDecor 39 s3Pos s3Neg, 0xa8a8a8a880808080a8a8a8a880808080a8a8a8a880808080a8a8a8a880808080a8a8a8a880808080a8a8a8a880808080a8a8a8a880808080a8a8a8a880808080, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_15233
namespace PEqualNP.Outside.L_meta_15233
open PEqualNP.Outside.L_meta_15233.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x414670808a12406600000356081a3df43dc43df32dd32df31dd31be40bc40de30dc30ee20ec20f610f410
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x2000288118429aa421d554443aaa8e654d52cc75080106c10010
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 14
  | 3 => 6
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
  | 4 => packedAt s4K4 (244+((h/4+packedAt s4K4 (224+(h % 4)*5) 5) % 19)*5) 5
  | 3 => packedAt s4K3 (170+((h/2+packedAt s4K3 (162+(h % 2)*4) 4) % 9)*4) 4
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 1 => 0xfe01fe01ff00fffffff80fe03f81fffff311ff
  | 2 => 0xfffe0001ffff00fffffff0003ffe07fffc1e3f
  | 3 => 0xfffffffe000000fe01ffffffc00007f01fe038
  | 5 => 0xffffffffffffff0001fffffffffff8001fffc0
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x9612120c190a0a022418b163458a28b32566db
  | 1 => 0x2bb0a554aaa6946548ec0aa92aa1b55d53116d
  | 2 => 0x4ca5b1a93494a6a991755812336c866e9c1a36
  | 3 => 0x71393931b8d8d8d11dbe6cdba04927871fa038
  | 5 => 0x81c1c1c1c0e0e0e1e1c78f1c3c71c4081add80
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xaaa8aaa880808080aaa8aaa880808080aaa8aaa880808080aaa8aaa880808080aaa8aaa880808080aaa8aaa880808080aaa8aaa880808080aaa8aaa880808080, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_15233
namespace PEqualNP.Outside.L_meta_15233
open PEqualNP.Outside.L_meta_15233.Model
def s5K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s5K3 (i*5) 5
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s5K3 (6+((h/1+packedAt s5K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xffffdfe0ffffff803fffffffff00ffffffe1ff
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffffffffffffffffffffffffffffffffffff
  | 3 => 0x6bff07c1ffffc00ffc01ffff00ff007e38
  | 4 => 0x73fff801fffffff00001ffffff00007fc0
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0xffffa03e108825f60992c7245bc0cbcb6ce0db
  | 1 => 0xffff804221104a9252a54948ad4b5555b52f6d
  | 2 => 0x8442209324a34992913695a6a6da57b6
  | 3 => 0x1508f43b1c473b8e231dc7e6c0f81c7a38
  | 4 => 0xe1087bde0783c0fc3e1f8f8f8c0e07dc0
  | _ => 0
def s5Atlas : Atlas := ⟨3,rawDecor 31 s5Pos s5Neg, 0xc0808080c0808080c0808080c0808080c0808080c0808080c0808080c0808080c0808080c0808080c0808080c0808080c0808080c0808080c0808080c0808080, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_15233
namespace PEqualNP.Outside.L_meta_15233
open PEqualNP.Outside.L_meta_15233.Model
def gbK8 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x4802080249578000b47000066e6c2658d8000a509800011806098bc05414214001c00622011dc6200b5e182cb820092000407b9090054021b574d02dc7c01010ac68386007801406fd8c49cca0c56f41d820218203060000102000050200008020c187001c01ff5400ff95001fd5400ff15001ff53007f94c01fd53007f14c03ff43007f90c01be43007f50c03fc43006f10c01ff51007f94401fd51007f14403ff41007f90401be41007f50403fc41006f10401ff31007f8c401fd31007f0c401fe21007f48401fc21007fd4001fe50005f94001fd50007f140017c5000ffd0001bf40007f90001fd40006f50003fc40007fcc001fe30007f4c001fc30007fc4001fe10007f44001fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x9a6003ef90d3001f788698002ff614c001fbb0a6000bdd8530005f8c298003f4614c0017a30a6000ef90530007788298003df314c001ee98a6000df94130006f8a098003bf404c001dea026003fecc130007bc609800eff650c0017f3286000bf5943001df8ca1800eff640c0037f3206003ef9903000d7cc818002fd640c007deb206000af5903001df8c81800efe630c00befa186003ef90c3001f78861800fdc430c007ce2186000bf98430005fac218003be410c001de2086000f78c43001fb86218002fe600c001bf2806000df140300077e8018003bd400c007ef9806003fe8c030007ba601800ff9300c0017fb2e2000bf99710006fccb880027e65c40017eb2e2000df59710004facb88002fc65c40017fb262000efd93100057ec988006fe64c40017eb262001bf1931000778c988006bc64c40017fb1e2003bf98f10005fac78800efc63c4001df21e2000ef10f10005fcc588002fd62c40017e3162000ef90b10007788588003be41c4001de20e2000fed4310006fca1880037c50c4001fc2862000de143100077e8188003bd40c40017fb2c2000bf99610005facb08002fc65840017fb242001bf992100077cc908006be64840017eb242000ef592100057ac908006fc64840017fb1c2003bf98e10005fac70800efc6384001df21c2000ef10e10005fec508002fe62840017eb142000ef90a10007788508002fd6184009fba0c2000ef90610007788308013f44184001da20c2000fdcc610007e86308003f72184001fa10c2000bf98210006fca1080037c5084001dfa042000ef50210007ee2108003fb10840017fb2a2000dfd9510004feca88002fe65440017eb2a2000bf19510006f8ca880027c65440017fb222000efd91100057ec888006fe64440017eb222001bf1911000778c888006bc64440017fb1a2000f7d8d10005bec68800efe63440017eb1a2003bf18d10007b8c688002dc6344001df21a2000ef10d10005fec488003ef624400177b122000bf98910005fac488002fc6244001f63122000bb189100077c8488003bc4244001df20a2000ef10510006fca0880037c5044001dfa022000ef50110007f62088003f610440017fb282000bf99410005faca08002fc65040017fb202001bf990100077cc808006be64040017eb202000ef590100057ac808006fc64040017fb182003bf98c10007bcc608002de63040017eb182000f758c10005bac60800efc6304001df2182000ef10c10005fec408002fe62040017eb102000bf188100077c8408003bc42040017f3082002fdd04100077c8208003bc4104005fa2082000ed10410007ee6208003f43104001fb9082000fd08410005fcc008003fb5004001bf2802000df14010007f0a008003785004001dfa002000ef50010007ee2008003fa1004001fa8802000fe44010
  | 1 => 0x7bf65d0003df32e8001cf9974000f7acba00073d65d0003de32e8001efd8f4000f7cc7a000ebe63d0003deb1e8001ef18f400077ea7a0003be53d0001dea9e8000ef14f4000f7ec3a0007be61d00015f30e8001ef5874000f78c3a0003bf51d0001df28e8000ef5474000778a3a0003bf31d0001df18e8000ef4c7400077863a0003be21d0001de90e8000ef087400077ea1a0003be50d00019f2868000ef5434000778a1a00033c50d00017fb2c8000bf99640005facb20002fc65900037eb248000af5924001dfcc720002fd6390001df21c8001ef10e40005fcc320002fd6190001df20c8001ef1064000dfcc1200037e5090001be2848001efd024000ff68120007f840900017fb2a8000dfd9540004fecaa0002fe65500017eb2a8000bf19540006f8caa00027c65500037fb228000efd514000f7ca8a0003bd5450003de2a28000bfd8d40007bec6a0002df63500077e31a8000f718d40005b8c6a0007bf4350001df21a8000ef50d4000f7886a0002ff6150001fbb0a8000bdd8540005f8c2a0003f461500017a30a8001efd05400077c82a0003bd4150003de20a8001bfd8140006fca0a00037c5050003fda028000ef9014000f7880a0007f84050001dfb2a8000cfd95400077ccaa0003bd6550001de32a8000cf195400077ec6a00039f6350001df31a8000ef58d4000778c6a000ebc6350001ce31a8000a718d400077ea6a0003be5350001dea9a8000ef14d400077ec2a0003b76150001df30a8000ef5854000778c2a0002bc6150001da30a8000ad185400077ea2a0003be5150001dea8a8000ef145400077e62a0003be3150001de98a8000ef0c5400077c42a0003bd2150001de10a8001efd814000d7ec0a0007bb6050001dfa828000ef941400067ca0a0003bd5050001de2828000cf1414001dfecb98002fe65cc007bf32e60009f99730005facb9800f7d65cc0013eb2e6003bf1973001dfec99800fbf64cc0075fb266001bf99330005fac99800efc64cc007de3266003af19330007bea79800fdc53cc007df21e6003ef10f30005fcc398002fd61cc001df20e6000ef1073001fbe6398003dd31cc001bf2866000df143300077e8198003bd40cc0017fb2c6000bf99630005facb18002fc658c0017fb246001bf992300077cc918006be648c0017eb246000ef592300057ac918006fc648c0017eb1c6006f7d0e3001f7c871800fbc438c00dee21c6000e710e30005fcc318002fd618c001df20c6000ef10630007bc6318003dc318c0077f3046000df94230006f8a118003bf408c001dea046000f7cc23001ff66118002ff654c001bfb2a60009fd9530005fcca98002fd654c0017e32a6000df19530004f8ca98002ff644c001dfb226000afd913000dfcc898002fd644c0037e3226000ef1913000d78c898003df534c001ee2
  | 2 => 0x21005fec890803bf64484015fb224201bf99121005fac890806fc6448401de3224201af19121005fec69080efe63484017eb1a4203bf18d210077c8690803bc4348401df20a4200ef10521007dc4290802ff60484017e3024200bfd9421005fcca108037e65084013f3284200bf59421006faca108027d65084017e3284200bfd90210077ec810802bf64084037f3204200bf5902100df8c810803bc64084035e3204200bfd8c2101dfcc610802fd63084077e3184200ef90c21007788610802fe6108401fba884200fd144210077c8210803bc4108401fb1884200fd4c421007ec4210803f52108401f29084200bf98021005fac010806fe64d40017eb26a001bf1935001dfcc7a8002fd63d4001df21ea000ef10f50005fcc3a8002fd61d4001df20ea000ef10750005facb28006fe6494001df324a001af99250005fac928003bd64940015eb24a001bf19250006fea9280237e5494001beaa4a008df1525001dfcc728003de63940016f31ca000bf58e50007bac728002dd6394001bfa9ca000df94e50006faa7280037c5394001df21ca000ef10e50005fcc328002fd6194001bfa8ca000df94650006faa3280037c5194001df20ca000ef10650005fcc1280037f5094001fda84a000dfd9250046fcc9280033e6494001beb24a000cf59250046f8c9280037f6394001bf31ca000d798e50006fac7280035d6394001be31ca008dfd0e50006fc87280033e4394001bea1ca008df10e500067887280037f6194001bf30ca000df58650006f8c3280237f4194001bf20ca000cf90650006fa83280237c41940019e20ca000dfcc650006fc63280037d3194001be18ca000df88650006fa43280037c21940013f304a008dfd0250046f88128002ff64540037f322a001bf19150005fec6a800efc6354001df21aa000ef10d50005fec2a8002fc6154001df20aa000ef10550007f6a0a80037e50540017f328a001bf990500077cc828006be64140017eb20a000ef590500057ac828006fc6414001bfaa0a007df95050006faa82801f7c54140077f318a000bf58c50006fea6280037e5314001bea98a000df14c500077c8628003bc43140017f308a000bf58450006fea2280037e5114001bea88a000df144500077c8228003bc41140017f300a000dfd4050007f4a0280037d5014001fca80a000dfd905003efcc8280033e6414001beb20a000cf5905003ef8c8280037f6314001bf318a000df58c50006f8c62801f7f4314001bf218a000cf90c50006fa862801f7c43140019e218a000dfd8450006fcc2280037d6114001be308a007dfd0450006fc82280033e4114001bea08a007df104500067882280037f3114001bf188a000df4c450006f862280037e2114001be908a000df08450006fcc0280027e6014001bd300a007dfd005003ef8802800
  | 3 => 0xf30c8200efd46410077ca320803bd5190401de28c8200efd82410077cc120803bd60904015eb048200ef18241005fecaa0802fe65504017eb2a8200bf1954100dfec8a0802ff63504077e31a8200ef90d4100f7886a0802ff62504017e3128200ef9094100f7884a0806ff6150403fba0a8200ef9054100f7882a0807f441504017fb028200bf1814100f7e80a0807bf6510403df3288201ef5944100f78ca20807bf6310403df3188203af98c4100f7ac620807bc6310401dfa988200ef94c410077aa620803bc5310403dfb108201ef988410057cc420807bd6210403de3108200efd48410077ca420803bd5210401de2908201ef984410057cc220807b66110401dfa888200ef944410077aa220803bc5110403dfb008201ef9804100f7ac020802bd6010403de3008203bfd9731005fccb98802fd65cc4077e32e6203bfd933100dfcc99880fbe64cc4035f3266200bf5933101f7ac998802bd64cc4077e326620af7d0f3101f7c879880fbc43cc407ee21e6203e710f31005fcc59880fee62cc401773166200bf58b3101fdac598802ed62cc401df2166200ef10b310077c8398803bc41cc4017f3066200bf58331005fecb18802fe658c4017eb2c6200bf19631005fec918806fe648c401df3246201af99231005fac918803bd648c4015eb246201bf19231005fac718803df538c401ee29c6203ef90e3101f788718802fe628c4017eb146200ef90a31007788518803df328c4077f30c6200ef90631007788318803df318c407fb98c6200bf98231005fac118802ff654c4017f32a6200bf59531005f8ca98802ff644c401dfb226200afd913100dfcc898802fd644c4037e3226200ef1913100d78c898827df434c407df21a6203ef10d3104fb886988039c434c4017fb126200bf189310077c8498803bc424c401ef1926200ef9053100778829880ff7314c401ef18a6200bfd8131005f8c09880eff650c4017f3286200bf5943101df8ca1880eff640c407dfb206203afd903100dfcc818802fd640c4077e3206203ef1903101d78c81880efe630c401efa986203f714c3101f7c861880fbc430c4017f3106200bf588310077c8418803bc420c407ef9906200f74c831005fcc218803be410c401de2086203f7cc43101fec6218803dd310c407fa9886200bf98031005fac018802ff65884017f32c4200bf59621005f8cb10802ff64884037f3244200ef9922100d7cc910802fd6488401deb244200af5922100df8c910802ff63884077f31c4200f798e21005bcc710802fd6388401eeb1c4200b758e2101df8c710803be4388401de21c4200bf58a21007dea510803ec5288401df2144200ef10a21007dc6510803ed32884017f30c4200ef90621007788310803f721884017f3044200bf58221005feca90802fe65484017eb2a4200bf195
  | 4 => 0x82fdf4314c07ee218a600bf98453005fac229802fe6014c017eb00a603bfd9643005fccb21802fd6590c077e32c8601bf592430077ea921807be5490c01deaa48601ef1524301dfcc72180fbf4390c03efa1c8603f710e43005fcc321802fd6190c03dfa0c8601ef10643005fcc121802fd6090c03dfa048601ef1024301f7ecb2180fbe6590c07deb2c8603ef1964301d7cc72180fbf5390c07df29c8603ef54e4301f78a72180fbf6190c07df30c8600af9864301f7ac32180fbc6190c07dfb048603ef9824301f7ac121802bd6090c07de3048600bfd9543005fccaa1802fd6550c017e32a8603bfd914300dfec6a1807df4350c07df21a8603ef10d4300fb886a1802ff6150c017e30a8601ef10543005fec0a1802fc6050c03dfa028603efd944301f7cca2180fbd6510c07de3288603ef98c4301d7cc62180f9e6310c07dfa988600e7d4c4301f7ca62180fbd5310c07de2988603e714c4301f7ec22180fbe6110c015f3088603ef5844301f78c22180fbf6010c07df3008603ef580430057ac02180fbc6010c037f326a200ef9935100d7cc9a8802fd64d4401deb26a200af5935100df8c9a880efe63d44017eb1ea200ef90f510077887a8802fe62d44017eb16a200dfd4b51005fcc1a8802fd60d44017eb2ca201bf99251005fac928806fc64944077f31ca200bf58e510077c8728803bc43944017f314a200bf58a51005fcc3288037f5194401fba8ca200bf98251005fac128802ff6454401dfb22a200afd915100dfcc8a8806fc6454401de322a201af19151005fec6a8803df63544016fb1aa203bf18d51007b8c6a8802dc6354401df21aa200ef10d51005fec4a8803ef625440177b12a200bf18951007d8c4a8802ec6254401bfa92a200df54951007eea2a88037e51544017fb02a200fed8151005f6c0a8802fc6054401fc302a200be18151005fcca28806fe64144017eb20a201bf1905101dfcc628802fd6314401df218a200ef10c51005fcc428802fd62144017f308a200dfd4451007eca2288037d5114401faa88a200bf98051005fac028802ff65904017f32c8200bf59641005f8cb20806fd6490401dfaa48201ef952410077aa920807bc54904077f31c8200f798e41005bcc720802fd6390401eeb1c8200b758e4100f7e8720803be4390401dea1c8201ef10e41005fcc520802fd6290403dfa148200ef90a4100f788520806fe6190403dfa0c8201fdd064100fe88320802fe60904017eb048201efd024100f788120803bf6590401df32c8200ef5964100778cb20803bf6390401df31c8203af98e410073cc7208029e6390401deb1c8200e758e4100778c720803bf5390401df29c8200ef54e4100778a720803bf6290401df3148200af98a410077ac520803bc6290401dfa948200ef94a410077aa520803bc52904035
  | 5 => 0x20000b8070000060680100300600c000020140180100902e01000804004000030010120240003400403c010040200080200d0080000000f026014058000000280300900000408800000058108090000181300d016000000000100100b0000000240b0000060000480a0020401582900000c0b801002000008160000580580800a01c0080100a0100380100602408828002004060000680080080200001c050180100000180f00001c0502b0060100680c000000000000000500000600001c0080000e0280100000000c0000001a0081481e002010010080120100900100000c038000041440100c01e000038020360080d01600e0000100000200000002018000000000320b807002056038008080020000400501202c000020080700980a0080000400001c00c0100100800c0180000001c0082100205c0100e0040581d000030000020000300000100400a0400380100405c0100f02a0000281400a0200080100c008000080000000000102001c0f00400000c048050180000d0010040000e009000000020050120401002700004c1c00201e12800001002010000040240102380c00a0040300700002c0001800608c000040160bc0500b02e01c0000b002000080000060200480d01a00c0000500404c0200c00e0b4000020000080000c02c01403801000088010280000000281700801c0280307a09c020130020c40001400c0300280a01001000001002010050040000040000000404c010060000040580801c0000280000c000008050100200600005a0040580000a0000580101800c0601202e00410005014000030020040082681301a0140400800a0100081906a0180600000600004806126000040410281200000e0060000780400004c080000000040002b00001c0c00003600401806fe65d50037eb26a801df9535400f7ca9aa0073e54d5003be2a6a803bf98f54005fac7aa007bc43d50017f30ea800bf5875400f7883aa002fe60d50017eb06a801efd035400dfecaaa006ff6455001dfaa2a801df9515400ef8a8aa007bc54550017fb1aa800f7d8d54005bec6aa00efc6355001ee31aa800b718d5400f7886aa002ff61550017e30aa801ef10554005fec0aa002fc6055003dfa02a801bf993530077cc9a9806be64d4c017eb26a600ef593530057ac9a9806fc64d4c19efa1ea60cf710f53005fcc3a9802fd61d4c017f306a600bf58353005facb29806fe6494c017eb24a603bf1925301dfcc72980f7f5394c01efa9ca600bf98653005fac329802fe6094c017eb04a600bfd91530077ec8a9802bf6454c037f322a601bf1915300778c8a9806bc6454c01efa9aa603df94d53005fec2a9802fc6154c017fb02a600bf18153005fcca29806fe6414c017eb20a603bf1905301dfcc62980f7f5314c07ef298a603df54c53007baa629
  | 6 => 0x612d203a32c1600421670000890c500000021b38a0001a48002cfca10001be06242e1fa1e9aa9adc0da90e02638090b0ea13134b8b200992940f16c1140004090768000001f30bd04abf73ae41836413e31d9453f422b0000002302169d92584794060c438300530714e403bda41f22101d80004b0af0001af48680833c20e00000029a0001d70b03ed1550d780011a00023d80000014a2ed83e26d41323228045f9b22161651fc12e161ba832b0933b124047b20411d18416384800dc8120c0003283f4b8b052266a9c1a22952a823a9851bc3c500034c2a20709c61e79001a5c2ba2909c0a647a2a3aa72db8819931991ea80a4981d400019c0e81c00f23561178f31f74620828001e69db0db2f88000000913b98004883340002ed3951523712c60631a7894c5600000001517d304bdc28d23bc3a4552d70003c73d741901e00009e40013b8003e01583480252a60000721d629b1aab3307526531ca311250004203d1a642e229142dacb80043b3b60bc00017137f80000015a1a402d0000001e90000090e20ef24526830403f35c47699d4711ab0b13fb17700017a3fc00048506800034ab7441b33f2ac140b24a331c13e21a700000049200010d145a9701d0ec38724d0651950e03311813e7c3201792200030300013a800186464302000239c7d00046a0003d91d0a1800033706f88700004d3ca2e798a21049949d00f23c860c411fe00001a27232723888a21216413c01eb3a18d0003790e31181730998f400c41100013841c0810003f63d62b225c4392c50001d5000303a701ecafc0192260003de0000003e602a0004450ff45047c0000001ed0000048002281b30d2938b7e3762501800d4946882331ae44230302af48a0000d3a6e3fd2f9acac7e4863151031ca1ab8b80002d008c309c2223b44216220813f1ed80015319040b10237a31836712801bb5b4941659f92d433d28c31386c000375213377394000000000491040bd100000000000005f3a409b2d08000168000000000003cd0002bd1872b50000000001de06e1b400000007a00000680000028b1398002001060132e685c00013f80008b03585412b0fac612d6489382079b112d896a1cec7311c05d3b02d30b6049bc20033442ae30c1cc800326a872bac0519e4a21571891c23460000003b40003dd38922736f13ca661243781cf02d89502c24907742739d969aeac160fb139036a961d003d115bfe2bb34111492c113b1b2e5b6e1cf8c6259c18c8b46e4283902e346739a1b7105362378a58bb71b92d3c8021c1cb2341c726b3a709d19141a0601bb142be922e343a4713d96802b0f906b000307a4f00023739603500000045e8a700000005a34200046c0360fa0782ea00500c0340101c00202c030000180000080000e0040281a02a0cc008000040200000100c000000
  | 7 => 0x21700022d0ee0000cc0000291132e727646942f3a607900000017c0001ca9648000003348000001c787000029eadd31f0c230808c916bac25707e3608d93c90258001a800009fbc00f02b013746d06f000000000434034c5700029f03a8003360283d00004603c4437000059bea10f00000028a32031000025e37b220b2d1d33e12411632fd41e0002c805a8000994151418a9000000000382b402cc3c80163320c111001726944010c19b17b0d015b0b697208b9e700009403434d8000b5abc1a50002df49b02e9e41dd18e0b70311ea188af74760382740eb2da31314900017f2240404848000dc12a189800162c96095c4a2e52460003a7a2194728780000034b07b1983552c217500031d31c3e81ae42907f28200021cc2b1c8c531e24100079091ff33e45a1cb9a9219b52493477a6aa6b9ec2a58430bf330b861f24508000002c880000044b0f98000004950a18f88000800003190001200002f8000000000085bab37f28e22022500000000000000000000032f00000000000000016100000011100025f322000369031946166b1201f49a3002699c6865a0713232335e1a2be32d130a8b48002033429cd8b3293301377b1700047027811f18212d00030d0b38002b83ec2361e6207c5d00027f0a0317a3900044f800083289b14288a3c0000000000d71192d180016880000041d0a43303583380003842c400000027a302b53498800000206a5d00000028635d1ce1f80920f642d3aa34e21abe73bf2020000fb87d17421da8f0f787c1378002a90d8b9eac98448d409009080039308f42c85b3a300024405332e2e02a4a4800000020900ca5b148086c750ed2688003e40002bf0628003ae861b4a1a325143cb9c0f6c1200743127d4664081a18d51439e81cc00023f2b419f13a2ef0d5c998962de9c59692ff26140425437d18b9c315d405a6d8442c040a0e903c0001b629e2bec3ec4d3f230f21f1b83c1218b880e413017e18b24e19f8000572900003a980000031480022a0001c3a6cb592380ca30b4240cd13314c36d0c3327b0949785832a2ba1263570003f53a11a61421bd30502001b1eb1aa1c903324a21100586d2f227c42a0da407b500004350213bd2c139138d0001b13e543f80000025a0088000590000c804600b0a29150000000d336800044639d09a88f9c4a228000552593702bb9a09510000672f04263d821f96b00004f2b3000088acf29942ec363731a9b981a6a533852fb075b921792f11e8a3a2150639f53611eb96aa1e2a40f53662b60970642a53450dd271014140217c5b1444680a52051448b7bd51ee0d838c3810c740330880e2561a3a924512ee3b91a00e639700a866c3d3a549f3292a118aae92a303b4014653ba09a36aa1596f11626c1c426248f19640200036b25ba7b44f23d2830000aa00028502f0
  | 8 => 0x1e300000038e3cc1df1ad000000205b490002f4204b9f0470003d2000074bbc4144470493819f13b80000710042e108547f0ae2b13722b714b34cace10a1082600121920000004211f648e00034d2da8000002d511e3c60b520b2ceae80d18001c9a1eb6a0063ff00041aa6eade404a8908993b30e35a17635414331a1f414d14786915c40c0023f015e267b4f1341210e73cb26a2140f118822f2a6bf113543d9a8b630323ee03793e8b946f3f329d02229410412f4333c9b434841c80004543df0b401c8d13c318f21d21908e30a306167b510000562750842aa0000000100002c7045c490a9a0f0f83351970000000000003cf00000032416e00049027924b2f503739e37c2c300144c2eb0002eca0d02e3699b54823f39071e53ab9da2a7a4320a47436c2841b04382fa0761e00002fe24c3be26748d1412b92f60fc13d04547800000046cba000031e00019eb3b341c6b28804c46ba3ea523ce49c04e1128a24831361d822c3a94523b88f74300b8aec21b9c2beb0003768de1010ab1ac0df2732c906a4441703d43f90d9af2acb29809f3393f81f01d12ca0ac20626304a1fb48c43e3bb2551a13648ba0741231831120862f915f42c00049e2cd4430000a33d0c173160271c50d69562a2a3fc250000d221a27708d3600002810d60111e11ba3991170c014f0000a8344adb2ab37999a16d1cd35f08800000000039b0510001bf0bb0003b232500004145f0518cb43c00001c0e515022205e00040d0000002abc632ad0c92d90232a009800044e06603b8000000fd0879660001ef2d800001802400049700023e0000001544720001dc3af4774068ce0cf40e19415940718c3ad485c2ab654872f312745917805044838f08a91b0ad2013a2214bdb2be3213262b28003470be0e145800d3ef419a350393e680045c0003d327e26f0002422231d23fa0730a109680000000045e25a8000000001fd2e62aabb33b53800fe43f4a000000000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x46484110006d46384110006e4628411000cbe74d9410004bd74d941001cde73d9410004dd73d941000cbe7419410004bd741941001cde7319410004dd7319410004ee7219410004ed721941001cde73d9010004dd73d9010004bd7699010014f4715901000cbf765901001cbc7359010004bc7259010016b77159010006b4715901000cbf705901000cbd705901000cbe74d8c10004bd74d8c10004dd7698c100069e6498c100069d6498c1001e9f7498c1001e9c7498c10004bf7458c1000cbc7458c1001cdf7658c100069e6458c100069d6458c100069f7458c100069c7458c10006d47158c1001cbf7690c10004bd7690c1001e9e6390c100069d6390c10005b67190c1001cbf7610c10004bd7610c1001e9e6310c100069d6310c1000cbe74d8810004bd74d881001cde73d8810004dd73d8810004bf745881000cbc74588100047e75188100047d751881000cbe7418810004bd741881001cde7318810004dd7318810004bf7690810004bd76908100059e73908100069e63908100069d6390810005b6719081000cbf7610810004bd76108100069e63108100069d63108100047e75984100047d7598410004bf769041000cbd76904100059e73904100069e63904100069d6390410015b67190410005b9709041000cbf7610410004bd76104100069e63104100069d6310410005b97010410016b67610410016b57610410004b57610410075b67310410007966310410007956310410005b67210410017b27010410005b57010410017b17010410015b674cc410006d563cc4100779443cc410005e672cc410004f5760c410075b4740c410015b674c8410005d673c8410006d563c8410004f57608410015b47408410006d56308410006e5620841000cbe7498010004bd7498010026b44198010007b041d40100463e64940100063d64940100065e63940100065d63940100073441940100057a709401003e3e64140100063d64140100065e63140100065d6314010007344114010004f97614010007b041140100067a76140100067976140100073a74140100073974140100073a64140100073964140100075a63140100075963140100073a43140100073843140100067a62140100067862140100073a42140100073842140100077271140100077171140100067a611401006f7341140100073a411401000738411401006f704114010007304114010007733114010007703114010007732114010007702114010004bd76d00100069e63d00100069d63d00100073850d0010004bf76500100059c73500100069e63500100069d6350010005ac7250010005b47150010007385050010015b474c40100077050c401001cf97684010007b04184010004f77644010015b47444010005d47344010005e47244010004fb7644010005787544010
  | 1 => 0x210025b474c42100047e759951000cbe7499510004bd749951001cde7399510004dd7399510004ee7299510004ed7299510004bf745951000cbc7459510004df735951001cdc7359510004ef7259510004ec7259510004fb70595100047e76195100447e701951003c7c701951000cbe76d91100063f65d91100063c65d911001cbe73d9110004be72d911000cbe71d911000cbc71d91100047f75591100047c7559110004df735911001cdc7359110004ef7259110004ec7259110024f77159110004be76191100063f65191100063c651911000cbe74d8d10004bd74d8d1001cde76d8d100065f65d8d100065c65d8d100069f64d8d100069c64d8d100069e74d8d100069d74d8d100047f7558d100047c7558d10004bf7458d1000cbc7458d10004ef7258d10004ec7258d10004f77158d10004de7618d100065f6518d100065c6518d100069f6418d100069c6418d1001e9f7418d1001e9c7418d10004be7690d1001cbc7690d100063f6590d100063c6590d100069f6390d1001e9c6390d10004be7610d1001cbc7610d100063f6510d100063c6510d100069f6310d1001e9c6310d1000cbe74d8910004bd74d89100066f65d89100066c65d8910006af64d8910006ac64d8910006cf63d8910006cc63d8910006ae74d8910006ad74d8910006ae43d8910006ac43d89100047e75989100047d759891000cbe7498910004bd749891001cde7398910004dd73989100047f75589100047c7558910004bf745891000cbc7458910004df735891001cdc7358910004ee76189100066f65189100066c6518910006af6418910006ac6418910006cf6318910006cc6318910006af7418910006ac7418910006ae4318910006ac4318910004be7690910004bc76909100063f65909100063c65909100059e73909100069f63909100069c6390910006af6290910006ac6290910004be761091000cbc76109100063f65109100063c65109100069f63109100069c6310910006af6210910006ac6210910004be76905100063f65905100063c65905100059e73905100069f63905100069c6390510006af6290510006ac6290510004be76105100063f65105100063c65105100069f63105100069c6310510006af6210510006ac62105100047e76941100063f64941100463c64941100065f63941100065c63941100066f62941100066c62941100047e76141100063f641411003e3c64141100065f63141100065c63141100066f62141100066c6214110004be76d01100063f65d01100063c65d01100069f63d01100069c63d0110006af62d0110006ac62d0110005b671d011000cbc76501100063f65501100063c65501100059c73501100069f63501100069c6350110005ac7250110006af6250110006ac6250110005b471501100067865c4110026b
  | 2 => 0xcbc7459710004df735971001cdc73597100063f74597100063c74597100065f73597100065c73597100067b70597100047e75d93100047d75d931001cde73d9310004dd73d9310004ee72d9310004ed72d93100063e65d93100063d65d93100059e73d9310005ae72d93100063e75d93100063d75d931001cbe73d93100069e73d931001c9e73d93100069d73d9310004be72d9310006ae72d9310004ae72d9310006ad72d9310006b671d9310006b970d93100063e65193100063d65193100047e75d8f100047d75d8f1000cbe74d8f10004bd74d8f10004ee72d8f10004ed72d8f10004bf7458f1000cbc7458f10004be7690f1001cbc7690f100063e6590f100063d6590f10004be7610f1001cbc7610f100063e6510f100063d6510f1001e9e6310f100069d6310f1000cbe7498b10004bd7498b1001cde7398b10004dd7398b10004bf7458b1000cbc7458b100047e7518b100047d7518b10004be7690b10004bc7690b100063e6590b100063d6590b100059e7390b10004be7610b1000cbc7610b100063e6510b100063d6510b10006ae6210b10006ad6210b100063e65907100063d65907100059e7390710005b970907100063e65107100063d6510710005b970107100063f64943100463c64943100063f641431003e3c64143100067965143100057976143100067976143100073a74143100073974143100073b64143100073864143100073a43143100073843143100067a62143100067862143100073a42143100073842143100073a41143100073841143100063e65d03100063d65d0310005b671d03100073850d03100063e65503100063d65503100059c7350310005ac7250310005b4715031000738505031000cbe74d9610004bd74d961001cde73d9610004dd73d9610004ee72d9610004ed72d961000cbe7419610004bd7419610004df735921001cdc73592100059c73592100069f735921001cbc73592100069c735921001c9c7359210004bc7259210006b77159210026b4715921000cbe74d8e10004bd74d8e10004bf7458e1000cbc7458e1001cbf7690e10004bd7690e10005b67190e1001cbf7610e10004bd7610e100069f6310e1001e9c6310e1000cbe74d8a10004bd74d8a100047e7598a100047d7598a10004bf7458a1000cbc7458a10004df7358a1001cdc7358a10004bf7690a10004bd7690a100059e7390a10005b67190a1000cbf7610a10004bd7610a100059e7390610005b57610610026b5761061007db67310610005b67210610005b57010610025b674cc61007f9443cc610005e672cc61007db4740c610025b674c8610005d673c8610025b47408610006e762086100463e64942100063d649421000734419421003e3e64142100063d64142100073441142100059c7350210005ac7250210005b4715
  | 3 => 0xf7258630004ec7258630004bf7690630004bd769063001d9e739063000cbf7610630004bd76106300359e748c63001d9c740c6300463e64942300063d64942300071c439423003e3e64142300063d64142300071c431423001d9c7350230005b4715023000738505023001d9c74cc2300065d73d953008e3e43d953008e3c43d95300047e759953000cbe7499530004bd7499530004f67199530004f57199530004bf745953000cbc7459530004f77159530004f471595300047e76195300863e43195300863c431953000cbe76d91300063f65d91300063c65d913001cbe73d913001cbc73d9130004be71d91300047f75591300047c7559130034df7359130004f77159130004f47159130004be76191300063f65191300063c6519130004de76d4d300065f65d4d300669c64d4d300065f6514d3005e9c6414d3000cbe74d8530004bd74d85300067765d85300067465d8530006b764d8530006b464d8530006e762d8530006b674d8530006b574d853007eb643d853007eb443d8530006776518530006746518530006b76418530006b46418530006e76218530006e46218530006b77418530006b47418530006d75318530006d45318530076b64318530076b44318530004be7690530004bc76905300063f65905300063c659053001d9e7390530006af6290530006ac6290530006b76190530006b46190530004be761053000cbc76105300063f65105300063c651053001d9e7310530006af6210530006ac6210530006b76110530006b46110530004de76cc5300569c64cc530005cd72cc530006cc62cc530006d461cc53004e9c644c530006cc624c530006d4614c5300047e76941300063f64941300463c64941300067761941300067461941300047e76141300063f641413003e3c641413000677611413000674611413001cbe76d013001cbc76d01300063f65d01300063c65d013001d9e73d0130006b761d0130006b461d013001cbc76501300063f65501300063c655013001d9c7350130005b47150130006b76150130006b461501300073850501300369c648c130006d4618c13001e9c439943001cdc735903002e9f735903001cbe735903001cbc735903001e9c735903001c9c7359030004bc7159030004bf745843000cbc745843001e9c4358430004bf7690430004bd769043001d9e739043000cbf7610430004bd761043001d9c7310430004dd768c43002d9e748c43000cbe7498030004bd749803001e9c43980300463e64940300063d649403008f1c439403003e3e64140300063d64140300871c4314030004bd76d003001d9c73d0030004bf765003001d9c7350030005b47150030004df764c03002d9c744c030005d4714c03000799404c03000cbe7499710004bd74997100063e74997100063d7499710004bf7459710
  | 4 => 0x8540006b67218540006b57218540006b47218540016b77018540006b57018540004be76d4540004bd76d45400069c63d4540006ac62d4540006b461d45400069c6394540006ac6294540006b46194540004bf7654540004bc76545400059f73545400059c73545400069c6354540005af7254540005ac7254540006ac6254540006b46154540005bb7054540005b870545400069c6314540006ac6214540006b46114540004be76cc540004bd76cc54001e9c63cc540005ae72cc540005ad72cc540006ac62cc540006b461cc540004be768c540004bd768c54001e9c638c540006ac628c540006b4618c540004bf764c540004bc764c54001e9c634c540006ac624c540006b4614c54001cbc760c54001e9c630c540006ac620c540006b4610c540004be7688540004bd76885400059e73885400059d73885400069c6388540006ac6288540006b46188540004bf7648540004bc76485400069c6348540006b46148540004bc76085400053e75085400053d75085400069c6308540006b46108540007a521085400069c63d4140006b461d4140004be76941400059e73941400059d73941400069c6394140006b461941400073b50941400053e76941400063e76941400043e76941400071e73941400071d73941400071f639414008e3c63941400071c63941400061c63941400073761941400063c61941400073461941400063461941400053e70941400463f60941400473b60941400069c6354140006b46154140004be76141400069c6314140006b461141400053e76141400063e76141400043e76141400071f63141400863c63141400071c63141400061c63141400073761141400063c61141400073461141400063461141400053e70141400073a701414003e3f601414003f3b601414000cbe7499730004bd74997300063e74997300063d749973001e3e439973001e3c4399730004bf745973000cbc745973001cdc73597300063f74597300063c745973001e5c735973001e3e435973001e3c43597300065d65d4f3001e9c64d4f3000cbe7498730004bd7498730004bf745873000cbc745873001cbe76907300063e65907300063d659073001d9e739073001cbe76107300063e65107300063d651073001d9e7310730006b66110730006b5611073001e9c644c73008e3f649433008e3c64943300863f64143300863c64143300063e65d03300063d65d033001d9e73d03300063e65503300063d655033001d9c7350330005b4715033000cbe74d9630004bd74d963000cbe7419630004bd74196300369f43592300069f73592300369c7359230004bc71592300059d7610e3001e9d7610e300069e6510e300069c6510e300059e7110e300059d7010e3001e9e6010e3001f9a6010e30004bf745863000cbc74586300069c4358630004e
  | 5 => 0x69c6390540006af6290540006ac6290540006b461905400069c6350540006ac6250540006b4615054003c7e76941400065f63941400065c63941400067761941400067461941400447e76141400065f63141400065c63141400067761141400067461141400069c6390140006b461901400463f60d95400473b60d95400053e75995400063f65995400059e73995400059d7399540005b67199540005b57199540005b970995400059f73595400059c7359540005b77159540005b47159540005bb70595400053e76195400063e761954003e3f601954003f3b60195400071f65d8d400071c65d8d400369f60d8d400379b60d8d400053e7598d400053d7598d400063f6598d400063c6598d400059e7398d40005b67198d40005b57198d40005b97098d400053f7558d400053c7558d40005b77158d40005b47158d40005bb7058d400063f6518d400063c6518d4001e9e6318d400069d6318d400059e7618d400069e7618d400069f6518d400071f6518d400061f6518d400069e6518d400069d6518d400069c6518d400071c6518d400061c6518d4002e9f6018d4002f9b6018d4001e9f7518d4001e9e7518d4001e9d7518d4001e9c7518d4001e9f7118d4001e9e7118d4001e9d7118d4001e9c7118d4001e9f7018d4001e9d7018d40004be76d4d40004bd76d4d4001e9c63d4d4001e9c6394d40005ba7094d40005b97094d40004bf7654d40004bc7654d4001e9c6354d4001e9c6314d400069c63d85400073765d85400073465d85400079763d8540006b663d8540006b463d85400079463d85400069463d8540007a762d8540026b760d8540027b360d85400053e75985400053d75985400063f65985400063c65985400059e73985400059d73985400069f63985400069c6398540005ae7298540005ad7298540006af6298540005b67198540005b970985400053f75585400053c75585400059f73585400059c73585400069c6358540005af7258540005ac7258540005bb70585400063f65185400063c65185400069f63185400069c6318540006af6218540006b5611854001cbe7318540004be7218540005b67618540006b67618540006b76518540007376518540006376518540006b66518540006b56518540006b46518540007346518540006346518540006b76318540007976318540006976318540006b66318540006b56318540006b46318540007946318540006946318540006b76218540007a76218540006a76218540006b66218540006b56218540006b46218540007a46218540006a46218540016b76018540017b36018540006b77518540006b67518540006b57518540006b47518540006b77318540006b67318540006b57318540006b47318540006b75318540006b65318540006b55318540006b45318540006b7721
  | 6 => 0xe74980500053d74980500463e64980500063d64980500055e73980500055d73980500463e74980500063d74980500065e73980500065d739805008e3e439805008e3c43980500063e41980500463c41980500067a70980500073a74980500073974980500073a64980500073964980500075a73980500075973980500073a43980500073843980500057a71980500073a419805000738419805000cbe76d4f40004bd76d4f40004bf7654f4000cbc7654f4001e9c6314f4001cbe73987400069e739874001c9e73987400069d7398740004be729874000eb6719874000cbe76d4740004bd76d4740004bf765474000cbc76547400059f73547400059c7354740005af7254740005ac7254740005bb7054740005b8705474000cbe76cc740004bd76cc74001e9c63cc740005ae72cc740005ad72cc740006b661cc74000cbe768c740004bd768c74001e9e638c740004bf764c74000cbc764c74001cbf760c74001e9e630c740006b6610c74000cbe7688740004bd76887400059e73887400059d7388740006ae6288740004bf764874000cbc7648740004bf76087400053e75087400053d7508740006b66108740007a521087400059e73943400059d73943400453d76943400063d76943400071e73943400071d739434008e3e63943400063e619434003d3d76143400063d76143400863e63143400063e61143400073a701434001cde73d9640004dd73d964000ebb705924001e9e6390e400069d6390e400059e7390640006b661906400473b40942400463e74d95400063d74d95400463c43d95400463c41d954003c7e759954001cde7399540004dd7399540004f67199540004f57199540004df735954001cdc7359540004f77159540004f471595400447e761954003e3e74195400063d741954003e3c431954003e3c4119540004be76d51400063f65d5140004bc76551400059f73551400059c73551400065f65d8d400065c65d8d400369e74d8d400369c41d8d400065f6518d400065c6518d4001e9f7418d4001e9e7418d4001e9c7418d400069f5418d4002e9e5418d400069d5418d4002e9c5418d4002e9f4118d4002e9c4118d4002e9c4018d400063f6590d400063c6590d4001e9c6390d4001cbc7650d4001e9c6350d400067765d85400067465d8540006d763d8540006d463d8540006e762d8540026b674d8540006b643d8540026b443d8540026b442d8540006776518540006746518540006d76318540006d46318540006e76218540006e46218540006b77418540016b67418540006b75418540016b65418540006b55418540016b45418540016b74318540006b64318540006b54318540016b44318540016b74218540016b44218540016b440185400063f65905400063c65905400059e73905400059d73905400069f6390540
  | 7 => 0x865000cbe74d8d50004bd74d8d500069f6310d5001e9c6310d5000cbe74d8550004bd74d85500059e7390550006b76110550006b46110550004df735905001cdc735905000cbf76590500059c735905003e3f75590500069f735905001cbc73590500069c735905001c9c7359050004bc715905000c7d76d505000e3e64d505000e3e64550500055f73550500055c7355050004bf7458c5000cbc7458c5001c7d76d4c5003d3e74d4c500053d74d4c500053f7454c5003d3c7454c5001cbf7690c50004bd7690c5001cbf7610c50004bd7610c5001e9c6310c500071f5310c500871c5310c50005b97010c50004bf745845000cbc7458450004df735845001cdc7358450004ef7258450004ec725845003d3e74d44500053d74d44500057970d44500053f745445003d3c74544500055f73544500055c73544500056f72544500056c72544500057b7054450004bf7690450004bd76904500059e739045000cbf7610450004bd761045000cbe74980500047f7654050004fb765405003e3e64d90500057a70d90500053d76990500853e73990500053e71990500055f73590500055c735905003d3f765905003e3f76590500071f73590500853c73590500071c73590500051c73590500053c715905003d3e74d8c500053d74d8c500057a70d8c500053f7458c5003d3c7458c5003d3e7418c500053d7418c50005767118c50005757118c500057a7018c500853f7690c500053d7690c500853e7390c500053e7190c500053d7090c500853f7610c500053d7610c500853e7310c500871e7310c500071f6310c500871c6310c500053e7110c500873a7010c500053d7010c50087397010c50005397010c5003d3e74d84500053d74d84500057a70d84500053f745845003d3c74584500055f73584500055c73584500056f72584500056c725845003d3e74184500053d74184500055e73184500055d73184500056e72184500056d72184500057a70184500055e73904500055d73904500053f76904500053d76904500853e73904500071e73904500051e73904500071d73904500053e729045003d3e71904500053d70904500057b705045000578705045003d3f76104500053d76104500853e73104500053e72104500053e711045003f3671104500053d701045003d3e74cc4500053d74cc4500871c43cc4500056e72cc4500056d72cc4500057a70cc4500057970cc45003d3e748c4500053d748c4500053f744c45003d3c744c4500071c434c4500057b704c45000578704c4500853f740c4500853c740c45003d3e74884500053d74884500055e73884500055d73884500057a70884500057970884500053f744845003d3c74484500057b70484500057870484500047e76084500047d76084500053f740845003d3c740845000765210845003d3
  | 8 => 0x7a64348421007a44348421005e4704842100cbe7498021004bd74980210047f75580210047c7558021004bf745802100cbc7458021004df735802101cdc7358021004bf7458f5000cbc7458f5001e9e6310f500069d6310f50005b97010f50004bf745875000cbc74587500059e7390750006b66110750006b561107500463e54592500463c755925001cbc7359250004bc715925000e3e64d525000c7f76552500055f73552500055c73552500069e6498e500069d6498e5001e9f7498e5001e9c7498e50004bf7458e5000cbc7458e500069e6458e500069d6458e500069f7458e500069c7458e500453e74d4e500053d74d4e5001e5e63d4e5001c7f7654e500053f7454e500453c7454e500065d6314e5001cbf7690e50004bd7690e5001e9e6390e500069d6390e5001cbf7610e50004bd7610e5001e9e6310e500069d6310e500071f5310e5008f1c5310e50004bf745865000cbc74586500453e74d46500053d74d46500053f74546500453c74546500055f73546500055c73546500056f72546500056c7254650004bf7690650004bd76906500059e73906500069e63906500069d639065000cbf7610650004bd76106500069e63106500069d63106500055e73d92500055d73d92500057a70d925008d3e73992500053e71992500463c64592500463f765925008d3c73592500053c71592500453e74d8e500053d74d8e500057a70d8e5008f1f7498e5008f1c7498e500071e6498e500071d6498e500053f7458e500453c7458e500065f7658e500071f7458e500071c7458e500071e6458e500071d6458e500453e7418e500053d7418e500057a7018e5008d3f7690e500053d7690e5008f1e6390e500071d6390e500053e7190e500053d7090e5008d3f7610e500053d7610e5008f1e7310e5008f1e6310e500071d6310e500053e7110e500053d7010e500453e74d86500053d74d86500055e73d86500055d73d86500056e72d86500056d72d86500057a70d86500053f74586500453c74586500453e74186500053d74186500055e73186500055d73186500057a70186500055e73906500055d73906500053f76906500053d769065008d3e73906500071e73906500051e73906500071d73906500071e63906500071d63906500053e72906500053d70906500453f76106500053d761065008d3e73106500071e63106500071d63106500053e72106500473671106500053d70106500453e74cc6500053d74cc65008f1c43cc6500056e72cc6500056d72cc6500453e748c6500053d748c6500053f744c6500453c744c6500071c434c65008d3f740c65008d3c740c6500453e74886500053d74886500055e73886500055d73886500053f74486500453c74486500047e76086500047d76086500053f74086500453c740865000765210
  | 9 => 0xc7458e2101cbf7690e21004bd7690e2101e9e6390e210069d6390e21005ae7290e2101cbf7610e21004bd7610e2101e9e6310e210069d6310e21005ae7210e210059e7390a210069e6390a210069d6390a210069e6310a210069d6310a2101ece638ca2101cef764ca210078c434ca2100cbd76906210059e73906210069e63906210069d6390621005ae72906210069e63106210069d6310621005ae7210621006d563c862100cbe7498221004bd74982210047f75582210047c755822100cbe7499521004bd7499521004bf745952100cbc7459521004df735952101cdc7359521004f77159521004fb7059521004f8705952101cde73d9121004dd73d912100cbe76d91210059e73d912101cbe73d91210069e73d912101c9e73d91210069d73d9121004bd70d9121004be761912100cbe74d8d21004bd74d8d210047f7558d210047c7558d21004bf7458d2100cbc7458d21004fb7058d21004f87058d21004be7690d2101cbc7690d21004be7610d2101cbc7610d2101e9e6310d210069d6310d21004be76905210059e7390521004be76105210047e75d81210047d75d812100cbe7418121004bd741812101cde7318121004dd731812100cbe7499421004bd74994210047d76994210063e74994210063d74994210047e7099421004bf745942100cbc7459421004df735942101cdc7359421004fb7059421004f870594210057870594210063f74594210063c74594210065f73594210065c73594210067471594210067b70594210047c70594210067870594210047870594210047e75194210047e75d90210047d75d902101cde73d9021004dd73d90210063e65d90210063d65d90210059e73d90210063e75d90210063d75d902101cbe73d90210069e73d902101c9e73d90210069d73d9021004be71d9021006b671d9021004bd70d90210063e65190210063d65190210047e75d8c210047d75d8c2100cbe74d8c21004bd74d8c21004bf7458c2100cbc7458c21004be7690c2101cbc7690c210063e6590c210063d6590c21005b67190c21004be7610c2101cbc7610c210063e6510c210063d6510c2101e9e6310c210069d6310c21005b67110c2100cbe7498421004bd749842101cde7398421004dd73984210067565d44210076752d4421004f57614421005e572144210063e65904210063d65904210059e7390421005ae7290421004be761042100cbc76104210063e65104210063d6510421005ae721042101cf5768c421005e5728c42100794434c421007c6324c421005d57388421005e57288421004f77648421007a64248421007a44248421005e77648421006e77648421005e67548421005e47548421007666548421007656548421007a77448421007a47448421007a76448421007a46448421005e77348421005e57348421
  | 10 => 0x8b3101eac4398b3101ee63198b3101ee53198b31004bf7458b3100cbc7458b3101e9c4358b3101ecc3258b31006af7458b31006ac7458b31006cf4358b3101eae4358b3101eac4358b3101ecc4358b3101e8c4358b3101ecc3158b3101ecf3058b31004bf7690b31004bd7690b3101d9e7390b31006ae6290b31006ad6290b3100cbf7610b31004bd7610b3101d9c7310b31006ae6210b31006ad6210b3101d9e7390731006ae6290731006ad629073101d9c7310731006ae6210731006ad621073100cbe7498331004bd749833101e9c43983310047f75583310047c755833100cbe74d9631004bd74d963100cbe7419631004bd7419631004ee7219631004ed7219631004bc7259231004bf70592310669e64d4e3105e9e6414e31004bf7458a3100cbc7458a31004bf7690a31004bd7690a3101d9e7390a3100cbf7610a31004bd7610a3101d9e7310a310969e64cca31005d571cca3101cbd769063101d9e739063101cbd761063101d9e73106310569e64cc631005cd72cc63100cbe7498231004bd74982310047f75582310047c755823100cbe7499531004bd7499531004bf745953100cbc7459531004df7359531004ef7259531004ec7259531004fb7059531004f8705953104cdd73d913104e9f43d913100cbe76d913104e9e73d91310069d73d9131004be72d9131004bd70d9131004be761913101d9c73191310059e7610d3101e9e7610d310069e6510d310069c6510d310059e7210d310059e7110d3101e9f6110d3101f976110d310059d7010d3100cbe74d8931004bd74d89310069c43d8931004be7690931004bc769093101d9e7390931004be761093100cbc761093104d9e748c931004be769053101d9e7390531004be761053104d9e748c5310047e75d81310047d75d813100cbe7418131004bd74181310069c431813100cbe7499431004bd7499431004bf745943100cbc745943101cdc735943101e9c64d4c3100cbe7498831004bd7498831004bf745883100cbc745883101cbe769083101d9e739083101cbe761083101d9e7310831004df764c83101e9c644c83100cbe7498431004bd749843101d9e739043101cbe761043101cbc761043101d9e7310431004df764c43101e9c644c43100cbe7498031004bd74980310047f75580310047c7558031004bf745803100cbc7458031004ef7258031004ec725803100cbe74d9621004bd74d962101cde73d9621004dd73d9621004fa70d9621004f970d962100cbe7419621004bd741962101cde7319621004dd731962101cde73d9221004dd73d922101cbc7359221004bf705922100cbe74d8e21004bd74d8e210069e6498e210069d6498e2101e9f7498e2101e9c7498e2101ecd7298e21004bf7458e2100cbc7458e210069e6458e210069d6458e210069f7458e210069
  | 11 => 0x69f6398e410069f6598e410069e6598e410069d6598e410069c6598e410569e6198e41057966198e4101e9f7598e4101e9e7598e4101e9d7598e4101e9c7598e4101e9f7298e4101e9e7298e4101e9d7298e4101e9c7298e4101e9e7198e4101e9c7198e4101e9f7098e4101e9e7098e4101e9d7098e4101e9c7098e410069f7658e4104e9e6158e4104f966158e4101e9e6318e41005b67118e41004be76d4e41004bd76d4e4101e9e63d4e4101e9e6394e41004bf7654e41004bc7654e4101e9e6354e4101e9e6314e410059e73d8a410059d73d8a410069e63d8a410069e6398a410069d6398a4101cbe7398a41004bd7098a410069e6358a410053e7518a410053d7518a410059e7318a410059d7318a410069e6318a410069d6318a41005b67118a41004be76d4a41004bd76d4a410069e63d4a410069e6394a41006ae6294a41004bf7654a41004bc7654a410059f7354a410059c7354a410069e6354a41006ae6254a41005b77154a41005b47154a41005bb7054a41005b87054a410069e6314a410069e63d46410069e63946410073751946410059f73546410059c73546410069e6354641005af7254641005ac7254641005bb7054641005b870546410069e63146410053e75d82410053d75d82410059e73d82410059d73d82410069e63d82410069d63d8241005ae72d8241005ad72d82410069e6398241026b661982410053f75582410053c75582410069e63582410069d63582410063f75582410063c755824101cbc7358241004bc72582410059e73182410059d73182410069e6318241004bd7499541004bf7459541004df735954101cdc7359541004ef7259541004ec7259541004fb7059541004f870595410069f6390d4101e9c6390d410059e7390941006af6290941006ac62909410059e73905410047e75d81410047d75d814100cbe76d4c41004bd76d4c41004bf7654c4100cbc7654c4101e9c6314c41005b67114c41005b57114c4101cbe73988410069e739884101c9e73988410069d739884100eae7298841004bd709884100cbe76d4841004bd76d4841004bf765484100cbc76548410059f73548410059c7354841005b77154841005b47154841005bb7054841005b87054841005b67114841005b571148410069e73984410069d739844100eb67198441004bd76d4441004bf76544410059f73544410059c7354441005af7254441005ac7254441005bb7054441005b870544410063f75580410063c75580410069f735804101cbc73580410069c735804101c9c7358041006af7258041004bc7258041006ac7258041004ac725804100ebb705804101e9c439973101cdc73593310569f735933101cbc735933101e9c735933101c9c7359331004bc7259331004bf7059331006af7498b31006ac7498b3101eae439
  | 12 => 0xf75580430063c75580430069f535804301e9c5358043006b77158043004bc7158043006b47158043004b4715804301e9f315804301ebb705804301ebb305804301e9c305804301eb8305804301e983058043004df735935101cdc73593510059c73593510069f735935101cbc73593510069c735935101c9c7359351004bc7259351004bf7059351004bf7458f5100cbc7458f5101cbf7690f51004bd7690f5101cbf7610f51004bd7610f5101e9c6310f51004bf7458b5100cbc7458b51004df7358b5101cdc7358b5100cbe7498351004bd749835101cde7398351004dd7398351004bf7458e5100cbc7458e51005b67190e5101e9e6310e510069d6310e51004bf7458a5100cbc7458a5100cbe7498251004bd749825100cbe76d915101cbe73d9151004be72d9151004bd70d915100cbe74d8d51004bd74d8d510069f64d8d510069c64d8d510069e74d8d510069d74d8d510069f6418d510069c6418d5101e9f7418d5101e9c7418d51004be7690d5101cbc7690d510069f6390d5101e9c6390d51005b67190d51004be7610d5101cbc7610d510069f6310d5101e9c6310d5100cbe74d8951004bd74d8951006af64d8951006ac64d8951006cf63d8951006cc63d8951006ae74d8951006ad74d8951006ae43d8951006ac43d8951006af6418951006ac6418951006cf6318951006cc6318951006af7418951006ac7418951006ae4318951006ac43189510066c62d4951006e462d4551006bb64d8151006b864d8151006db63d8151006d863d8151006eb62d8151006e862d8151006bb74d8151006b874d8151006ba43d8151006b843d815100cbe7418151004bd7418151006bb6418151006b86418151006db6318151006d86318151006eb6218151006e862181510067b7518151006ba7418151006b97418151006ba4318151006b843181510067b52181510067952181510067a511815100cbe7499451004bf7458c5100cbc7458c5101e9e6310c510069d6310c51004bf745885100cbc74588510047f7654451005787054451004f77654451005e4725445100cbe7498051004bd749805101cde73d9641004dd73d964101cde7319641004dd7319641004ee7219641004ed72196410063d65d5241005b571d52410059f73552410059c735524101e9f7498e4101e9e7498e4101e9c7498e410069f5498e410569e5498e410069d5498e410569c5498e410569f4298e410569c4298e410569f4198e410569f4098e410569c4098e4104e9c7458e4104e9c4258e4104e9f4058e4101e9e6390e4101cbf7650e4101e9e6350e410069e6390a410069d6390a410047f75582410047c75582410059e73d96410059d73d9641005b671d96410063d65196410059e73196410059d7319641005ae7219641005ad7219641005b67119641005b671d8e41
  | 13 => 0x600000400200000800700004f01400101000100100900200900600a00d00200400600000200100300100000000100100400000300100600100400000500400201000700601900100000500000100b00100300100000200000100100500f00000500c00201300b00000600100700a01000000000300000800000401302500000200000400100900000300800300a00200001600200500400000b01c00000600800000600600100400100400500502100a00800000100101000b00000300100600000602200900300800300200000400100000400000200100700202000600000500e01600300100900000100000000200600000500700500000000a00000300100101a00400800101b00300000100100200100800001700103700501501700000100100000000000200b00000200300100100000600200001200400000400802400b00000700400800100000000b00000400400300602100200100800602400100a00900000200000001200000100902500100000100900100000000000100101700000100000000100000201800600400300000000400100400800600d01900100000000000400000300b00600000100000000501500601601400001801000000000300c00200100400f00000202b00000c01000000800c00200a00700000000000300000300001200100900001e00e3f65d51540669e74d8d540669c41d8d540669f40d8d5401e9f7418d5401e9c7418d540069f5418d5405e9c5418d5405e9c4118d5405e9f4018d540669f43593530069f73593530669c7359353004bc7159353004bf7059353004bf745875300cbc7458753004ef7258753004ec725875300cbe7498353004bd7498353004bf745865300cbc745865300cbe7498253004bd749825300cbe76d9153004be71d9153004bd70d91530669c64d4d5300cbe74d8553004bd74d855300cbe7418153004bd741815300cbe749945301e9c439945301cdc7359053004df7654c5305d9c7454c53004bf745845300cbc745845301e9c435845301ed4315845300cbe7498053004bd749805301e9c439805301e9c43996430063d65d524301d9e73d52430059d73d524301d9c735524301e9c435864301e9c43982430047f75582430047c755824301cbe7398643004be729864301eb6719864301eb7319864301eb43198643004bd70986430063f75582430063c755824301cbc7358243004bc715824301ebb705824301ebb305824301eb83058243004bd7499543004bf7459543064df73595430047e75d81430047d75d814301d9d76d4c430069d76d4c4301d9e75d4c4301f1e75d4c430059d71d4c430059e70d4c430069f539844301e9c5398443004be729844301e9f329844301eb6719844301e9f319844301eb7319844301eb43198443004bd709844301e9c30984430063
  | 14 => 0x238800064f800064882a3d30420d443495f63e30e60b962839a560f4769799221882c6dc2b43e3ca2cca4000169083cd3284d129dcec4362f820080003208a59d18650fac8d4000185600079c00000000000000000fac000000000000000000047d55b468652c1419ce8f2657240f8000000000083904c76e40b05913d438171a28185fc6a451e0bc0dac7a480c41a8000ade8df3da80000000000caa3d0c1b7751ffe1b4000731146893101e5a300019542dd48d2228000f6200000600000800100100400402200200200500200000000600500200000a00000200b00300400100200100700c01200000200000300b00600200200000100400d00200101f00200000400000100000200301d00100000400500300000400100100600000500900600a00001200000300900400000200a00c00400100200000100400900600100000100500600c00000000100200600400100a00001a00100500a00000600000a00200f00000001200500000400600000000901800000000100200500500100000700100000000301503200200001100900000000000b01500000300d00500000801200000000100b00e00200000800000301e00200200300301700f00100000900100800500000500800301000900101000600d00202500000c00200100000400001800c00000400200200002200101100600300300300100400300100400000000300300a00400401100100400100000000000b00100000200100b00000000201500000100500600200800000100100d00000101d00200100000402500502100100200000000300100200701000800100f00000300200500a00000900600201100a00000200c02800200000000d00400200000000300100000200300200800000600100000400a00500000100000100000300000a00601e00800100600200600200000600000600700201500601100900300600c01200003100800301300500600600200000101600b00000301300100000f00000d00500001d00100200500100200000600400400000900400000700100700000300000f01400900000600e00400000200900200200401b00500000100600200001900600200e00300100200700900300800300c00000b00100000900000100800300000000100100000200900200100100000000f00200100900200e00601000100001900200100400100600100f00f00000000300001600100200100100900b00400400100c00000000a00001000000c00d00600c00000000900100000202200000001200c00101d00300700600e00200400e00000000200000900100000100200200000400000401d00000200200200b00000100d00e00301200700000000200000100001000400600400000900301200101200800900b01100e00600b00500200500000000500a00
  | 15 => 0xa049a8ba364000081c5533d212e831484c2a10d644cc1de1cbd38816a16447455447414f63c6841513435500001e474845a2838000c608031b6a35c00028117fe250000000000073ce9800047311408ce1dc4151e0c79701342a958ca7c6290df99748f2664000000071432f8ac053c0002d342896b0f5c00028b913c7df36c3da1fd4f188f2000000084429a1a59c7ce7e14e00006442c640f000209c83c5af3ff0000fc07f14059b8cd1077e1d0187517801a1c98bba00062db81994097800000000010d67e239294ed0ee6813bce29080688b148c51830a8062d883d059b6d72ea84c875273d0c181087746970b5164052021e3891ca89e511b1da83cc00000013b04b416e4c120e1a2817412c1960a6400000017d94bca4c0000001248d9a2b5217936400000034a800000000033c000000000000013b8c0e3438d3cbd489a39480000004340000001fc8000000171176495c64900000000000000ed8000ffa00022040000007602ab0caa000000196908c00000011e0bde00000036a10dc05e00000020cc0000bd000213cc840000000d00f9d00017b11e0a280ca21d985c34a5e80000000e883163a2a1e43352fd44102bc0882d940e86e841a0cb1a3993d04347241d00900003841c7e2cc79e6040a28e9c4200e03b1888abfc0d446e1a488292f43d69484024000248896c08b4000001bec7054bd37e01843120002c5021891024336c92a8cd00002c010f400060a3d61af0c9c70602a5a671a05274161e88fd46b13c78eac84c02833c85bf0ce0001c84000b220002c499b4dd800019d0000bce6cb42980000000001f681340006634471c9c2504980000d6c0003fe0cf910800056716b1e38000496000189ccca6c900021200000000000000b167020001a3036c00000008b85b64fa8000c9c000000000207800000000002304e500026d1e6000056193d80006b000023f8f320000002c610c84a452d29120a0c805ca2388c100000003cd15e854625986680000007c2264978cfee00000000005ce4a81070000d5a2070001ae80000001c1874c82c58e35c9cc0d420001a2000000030300015a86de5ec0001c90000000000112c00080112d221cd668d629b000000000001b6064a6861c411800073200026e186057d8c135590fc0004498000000e283671ec9f1b0342aa17f00ba0002d439b80006702409c080000007cf4650fc4e147592588c4a2a61340ab00f0a781184249a0c33a6062f500181280df00000009990002a316a4000888045887c8105440a4800099c00000000000008ab0000dd80005583bd0de804e7f40ae19a48362933f200007475fa0000000f2c0002bb1420634000265064c00035324b87d110207005194644025611a2855af9a77693ea3cc2c437c1c38900d70000087800000077f1bc80001ce6163100ca400000
  | 16 => 0x4670c3618469f800087a7316c0000030400026e05f228c0000001bf227cef224b0000344a7e77840c00000000002639e20b750000000e7ebee0000000f9400059344c873901000f30082bee6800015d80011fc39e8001f3e5506730208efc4262543681700f2425f134d1d90483c017282843684c780006a0fb80000ebc62005400045c8a108e645c0000f1c89c87e335931894828c0071988c6a6bd0a3881a00063715f00004427dd2e2808aff64d647d80001de57c31622f52010001f410108c739f1a6c4fc00003d0000fcc98000014886767cb8501b9c1ac0003b900000000002ae000055515e25d934800058800006c0c48a5c04c0190000ae70003a18f7c00000000014e400063202d5bd873c75f2cb5b7c0000000000b1440c8b1104cb7106e0ad3012300cde76932600000006e122a000000086900002c400000000000000000430001ec000018240a80000007f30000040b8285f07191f00431b82e39b4c00056b04b9e782da3652d703988c48b816612080004d7000177800075c0f79e520006751088d7c00044900000000008ed000097000018617c9c14a000000f592ea000000000000000000000003e45443640410c7ee700d02bf0e144a1053290174c39433600000000002b317584888fc72e0c606dc052235a0380ae0026000bd0480f287bd00001386d10000001d3874c27fa2e9c103ac00031510f07ec6b714f00000000000001d0401a0000001730d0c7463f2a29a35c000341134293d78937206b316946007c15c504068d164800000027194e9ad03616fe3700540fc61700a41a88ef956c387206c5f5494035218106c0001d880009ce1f62a38582d414a928c09ce4f81433e40fec4a668f32d197c29673526a4888dba0a92de1ac916a17622b50d0000621000066c0000001e422240006d538385c80004e12758ac68d475b109102b1ea8a03df0c900007561c01b564b001c3bb9bfcbe62a60001a62a1a30e256805a38441700a2070fda3422c40b2d1300004380744be02b70000000f000000001c34a1673218ac00000041f84e0bb40008fa28e040000017e0001d3452e0000000000cd40002c909743a707d1abc000c4d7c3bbeca2486619809b18f86c678700000001d44d00001b1ca461032788f6800000012b0000a040000000fea000000176031054e13334217b80002af38607b03c212e32309b01ea0003459f9c0ee55b0ec000000000000000000000003910dec36211f20f899e23c708280826049e63d2d0199e17201b47480010240000b383da5c21972140f1000032629b8e920000000498ba02d882e41815980005740001d5c0303482309bf45727d0055909e3f02280001fd800071043a14440000002d69a960000aa0d208287ce2671f4a1a8bac00036c04f200000000023300003009ea00ac83d7f920c82
  | 17 => 0x38a8c300003408001330af227022250a862e6a31ff41d8f03891420800049c000000160400000037dc9aa6e9560937800000040a00000008b20002df8000b060000000000000000000000024820031d1ab80005da000050800000018aa3f09ba61c934000024202d46c010e0007e58b001c41b67423d00530956199bb783787278971ab9be400011200000000002a142b9fad13c115000000000072118fa2c0c9026a0041eec60e00019883ec8243662aa1b1881380d80015f4f8600000007245401312e78000365000202935094602c1a708f4c827d22e89f10b4c77436b40000003ce10b88f2a3e00000019d021c372b5015daf1685d00018980008420cbc54864d0003e440005dc3d139e00005824db308116a28833700004300007cb24ed8488ae27507f00006600002ee0ffc0000001029868ce43d0a8d99d8234701048144c6e38bb15448105a555731c8c94e585fb25782280ca32306d00001c415147092950140fc3dc8e3003e23919e93fcee085804080000000000e600004ca402308c00060000006b83ac2f73e01ee1c240008c2232800062887f2791dec4ee00044e1650018377b7ec550b3a4b61bc40008d80001cb000000080d3660e690c65852e1018c6e16ee3e046f515a247306a30e5fe025b269854fd246b3ad13b08aa66711013cc6d5713270168897c44a0b712e0fc10a40d683b4b041e900006cc68262b000000045d116053061cd9e38e323844484e77bc228f74d098050c580006100003d4800055617702380000002fc1b4e1c47de8d50ec8d3c0005d4000000114e2d81c1077cf047c2b1f800001f4743188000fdc000243000042c2d100000000007b62bbc000000000130de400007553b910f87924350d01ca4c5a6c51879490d6c6a511b8bcc9408e84148854f2e8ef16e839eac05bd060178904c6b00f7010077a67137d22408741f027c1d2490e720295042cbfa3d80000a60b7310a0488c8494c0b84308000c280000001b7e6934b43ea80789320002f2108252a0000039a7cdea3bc000068c5192ef89ec2005a000026a828000024417b856ce228f111480000006050b0800000000034ea1d477028630c93e91084e522308d8d3430199fa3f47e95ed4400f849ff76c1668274f8216b44b0f9a5582612260d5b0964c315142b0a8a0002848b180007a72c30e3c00000000003640000000000000f808c83ac1ccc84033c8000750b6832036b173482858fbb880cd1522ef2d85b98fb687b0001468aca27eb791670b8c3fdacd8ebcf0a13800017106c04212e40150f948cd31c0adab483ae0000e7099a54c2bd8fe80000b042e000000000000000000000000000000ccc3500d511780c40a50de000000006c000000076700000003940003100000000e566432320000dde02500009048a400046ca2f8fb20
  | 18 => 0x84600020f00000000000a42a7000000007e46d74581a311a67661b512282f118c14120d4de6504000195163cc6c22d244a010ab88c300f50571b639b0c0233c23236e8000e0ebcf00000004980000004048000eca00029d00000000003b7000116411d0780b3a34400009e0c2cf022588418c74d7c15f0000000db1000033a0c8ecc26b0001fa110a0962b10a360000002af00000000000001970000000465a05800000000013f40000003af0d5800000009d000c5ae7a12830c251eb06e20d23c00602e01fa00009366db387a05cef11693b50870880196307a3d8fa20001ea800106860c0faa0b4e2c60e000000118e865000000000a000000000111a4b70e222744e462e0000000c06000000072045f5c3000145824e1fa46e8c1800000014400006781fd06392e40000000eb904e3424fb1fc978027a5a51c0c1fc00077a8000000c3f1229f700009440003f604a40e46a434387dccb200030d400081b8a23e4936e02305a0cf0000000570a42000108600028e8c3496410100000000008c44514c0a0003ec000165c0008382ba80000003ac00023b0bb666c00000008706bb46f06acb2c3a800016e000061280000000000003a8850017615a3d78fa84f43f20d80c611f04302dac00006a1a8c3302fc0a02f21249cf85900000f5000078c8590790b8c0001252a784ace368a527a0000b4e000000142200065830ec3c4914278201c0e4a602ea3110000b668021812188d360002d5000064454e3ec143cc2600030880111368213ff95b89fc0001c4cfc20041fe0f1063ca201ed4099f14a620000001fbc094092378827c6e6238208124a66824838004a8c4869e0000cbc8820000001b0c0f046941d91168ee22b000204000000026f8000b4242d00017fc53817d10180c47fa3e184d14940000c9000000000028f1e1067080c249973000018a4f930d870677c2090640000c1602c80000006363f00000000eec1c5ab480009cc8b40001d1c87248e02480002af3a5000000050e7df1c90000f3a2311e2800078265319580001a48540e1996d1f212f2b4c2b86fe59812dc374a664663d197847225482419c9800067a450a4000000002d900d05be75000007944bc0000919668d6a4008000e340001bb43922181c88142db55a00007f800000012045780fe0ac4e460000000000dca2571becf30b9c6ca00018f202c00011f86c67161e32171b391c6000000063476b56420edc6474b59f00012fa4690000000000e3c4e800000e108e0114188d9ac770002941b48a2a2da00010a40005d82718b1c00000011319f88883d1aa18d8826015e0c21a980003cb03a15000007ba2ef8aa43a48a484280000008a61aa0ec891623004480000000000000be86fa0662299b08f6426880015406eb87d00000005780000001d9c00000022391e883a00011a0
  | 19 => 0x59e00000001ecab40ff2daa2d90006e74360b907f80003759c2c46a80cc490f5800049319a5774a644ea034800000083e13108aa364000000000020c5009acc000f5600034280000762a505a1a4400015d310dda02383f745708086db0000630c1504a0003dfa2fc0006da800000062216534b124011c00006a87405aa80713897c81100571a613f090000025603a4000000432000004c1754071b711d461e3b0972466400037bd1c064171800016e86d90001150a6b0f0428a82211081f3f595699f038e00042d89ccdf00c33b100000002e90000000c475f810616107c405500000004c60000001a00f3e64a00017e40006de28514d489083925a94483c0000286000000043bb0bde5453e6e213000320007a50000d849340000000ae870c000236974019c5950e58d740004cf0b4000006e08d248d91447c00042d01191543b63ed0ed10943f50001270ea44e43119a391c85e60e0817c2cc6da0000000d386770001204bea00003001446ea3aa00000000008e700021491d66252db1ab00000002d5869c000000262800071200005b13780155f114294149da24680017bc00000000009b4f141813de0000ec83de40880e8dda51da024dd056c7aa15c23b9044441a5dc5ccd52266a748b28f986af2189344cfe5e9034c6ce5570871cb9144cae2f103202cca1c05c2bee3247b61be069958a02a4f006b06bc9b03b282d94f433403f04c9b107764c4000079c3521cd0f9a23c5007e614a05ece2e059112894afa80e82195cbc9900f618f0cee7f70dc1780ac8d50748374234ce9e0000f9000072a00000021a0c6847b2a14000000000000000000000000003851ee63c0001c7481213b000000000033b47000008ea49532597f00465acaf289fc0ac0a74451f5c7db7391b90c6467210d11dd528a963c300004e44644243370f8c93c0001ae18bc69433520880000000001e813bc0002923e703e80000203a00330e385119f201a043a0cf3d41bccf3609e1b885640bc1f10378d623cc00012e400002e27e1941f1c4285872159ca05848761d68174aaa23a4179a4c0006a71b512ed14757f37b85f0c3e23b3ef0000b1a3941b7c02cba48ac09a8b0c83043629499f482d0003a580007090f71f311f4aa41e41eb8ddc0000001bc069890a0003550dc00000000000da43726560000af4760820836a254e6c6168001978fc2000121215800049d1c807152025a845b61bc00079280010b0f2229b120d6f869a09b2342230699000265895471062813207544943013dc1d4c2086443e9816045b00010c00000002461af0000b3c7863481cb454800a22d818a00000031da314eba28a27b88649270000000dea3b45bb0259ff0a9a0000001df42f200025395cca560000000dda0001142dec088ce04a10000c6a0000a200019800000002f5a100adf
  | 20 => 0x3d0000119a20cf081020d612cca9222f013523c2e222332880b80f86611d158926b41a3800103084a00003a8b386141c608987ec0008e5022918c0000000000000bae27900ac0000f4000439a3684e8000000096422e1373be000109c7b70000f351267b30000000aee000000130800040d0000d9e9a6048800123000000000000d829a0fd00023fc000000010800000000043e01cc07c1ab8001ba4000417b198e88e39385847a0fced67fa22f88901d862280017d05db22c0595832d1211000002540000002580000da200016f00000008a819f16e44a23a180006648ac0001e501b30566c100005bcb322c000000006d007e127c00107104800012fc00060934c1bd05d986e2ae995044e1c02ac806473a5b014b0528f8318e3a50000d2867b1385db400046f2370940efd2d1a4f95044c52bf08485d0ea86699fc0000d7e8d22b81ddeabe60818e0ac03fe108000000000032e00000006f7000004882003a31300000007c17f02db8e850f48b7000055c6667a61a49dcc1dc000378014800013e375000051c8d126921783ba04f000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xa2e82d9250c400107b0fb20a18804287a0f641431000517416c82862000b18835d050c40012730fb20a188002c6a0f641431000595416c828620009398719050c40014750c218a188002c6a0e421431000715310842862000b1a8390450c400107b0f32e81880020fe1d65d031000699388a1a06200883e8799540c400f0790eb2a81880030799473503100060eb28e6a062000c2e651c940c400185aca39281880030d99471503100061ab28e2a062000d187314140c4001a50e428281880034c1c4505031001c4e41ae832c2000c9473dc5648400713906ba6c50800e27a0f7690a1001c4e41aec214200f994835d8418401f32d07390830803e6520d7010610004d2412e020c2011a1c83592508402143906b20a10800e2720d74d89100054641ae9b122000a8e83dd0624400713d063b4848800227a1a73909100060fb2ce72122000c1c659ce424400113b0fb1c848800e27e1c63909100064739ec52122000c8e7318a424400183ecb39c82880030719673905100044ec3ec720a200389f8718e414400191ce7b148288003239cc62905100064a31ce3a022000ca4629c7404400113d0c39a808800307d9473501100060e328e6a02200589e87d8d40440071390e31a80880022ba18725011000617b28e4a022000c2c651c9404400191ec639280880032318c72501100a45743ec4a022000c8c73d894044001918e631280880030dd9471501100061a328e2a022000c97631c54044001928c638a808800329d88715011000652310e2a0220038b5869c6430401d16902bb0860803b25cc57610c1001c4f41ee8b10200389e83dda420400113b0d39c840800e27e1e63908100044fc3ac721020028b4815d8420400713d07bb482080022ba0b76904100044ec34e7208200389f8798e410401513f0eb1c820803a65a0e72104100245bc32e0208200e994835c0410400134904b8082080033158e72cc4100046bc3ac7908200389c835d2600400146b0c20ca008002cc60041940100051ac308228020009b187104500400163106ba0a008002cc20574140100070cb22c62802000b328190c50040014730c218a0080021e61c62140100058d41c842802000b3281908500401b66108b88a008002d420d7114010005b0412e22802000b1a83904500401b66503208a008036cce1c411401000598c38822802013b32831045004001e24c6208a008003c458c41140100059941082280200db3284cc45004027e2087988a008002d8a0b311401009d9842062280200db3284c8450040016a507908a008036cc21021140100145a40aeda00200389c8798d40040011390eb1a80080032398c725001000646b18e4a002000c96631c5400400192ac638a8008003461cc50500100070cb18a0a002000d28721414004001a60e228280080374c1d050c4010
  | 1 => 0xce430e62a0003295c861cc54000456412ed18a80008ae82dd9315000713906bb442a000227219738854001c4fc38c710a800089d8718e215000191ce631442a0003235cc62885400064b398c310a8000c9573186215000713d07bb242a00020fa1a75085400041e432ea10a8000938805d4215000183cea31842a0003075d463085400061b3a8c210a8000c357518421500015490c90842a0003291d921085400074231a4210a800389f8718e505000113b0e31ca0a0003259cc61941400064ab98c32828000c1f839da5050001839073b4a0a0003079da73941400060f3b2e72828000c1e76d8e505000183cec31ca0a004687e1c63941400050ec38c72828000c3676d865050001c28c7b0ca0a00030d9d861941400070bb18c32828000e14631865050001c4ec430ca0a00038918861941400070b398c32828000e1573186505001107d0d384a0a0003079db63141400060f3b0c62828010e198018c505000186cedb08a0a00038518f61141400061b3b0c22828000e17631845050001c28c6308a0a000389d88611414000712310c22828017e3360184505002fc6700308a0a001e0fa1a70141400058cc1ce02828000e18639c05050001c60c3380a0a000e2720d749973001d0e41ae932e6003c1e7399641cc00783ce6b2c83980020f61e65d03300041fc3acba06600883e8799540cc007838e732a819801e0f21d655033001e0e39acaa066000c36651c540cc00186aca38a819800f269817610e30004ca40ae021c6000c8c43dc9618c00163300218a118043461cc505023000698388a0a04600389e831da414c02383ce7b2c8298043079cc65905300b64739ec520a6015c8e7318a414c01f92ce7b0c829803b259cc61905300ae47398c420a600ec9673184414c001918c8b966298003315c861cc5300764b398c3a026011c1c73d95404c021838e632a809803e2da1871501300061bb28e2a026000c34651c5404c00516d0fb0a809803f251cf615013000652396c2a02600ec9473185404c001948e430a80980430e1d8505013000698388a0a026000e3061141404c02343906b24a0180428720d641403001c4e41aeda00600399887501300c00713906ba4cb880028720d74997100060f32ce7b262000c1d659cf64c400185ccb396c9880030b59672d93100060f3ace7b262000c1d759cf64c400185ceb396c9880030b5d672d93100064739ce5b262000c8d739cb64c400191ce6b96c9880030d9d671d93100061abace3b262000c96739c764c400192ae738ec988003299ca71d931000652b94e3b26200083d8799464c400107f0eb28c9880022ba0a7610f1001c4f41ee8b16200389e831da42c400183ccb39c8588003075967390b1001c4f41cec2162000c1e659ce41c400183acb39c83880020f61f649431008d0f41ec92862000
  | 2 => 0xd7198d400050fc2ac631a8000a1c8558c635000152f02b18c6a0002a52056318d400050f42cca31a8000a9681994635000152b03328c6a0002a5e056518d400054a40aca31a8000a1e86194635000116902bb6a6a000f2618e7094d400045b40eeca9a8000aa68298f6150001c2eca31ec2a00038519463d85400074231ec5b0a8000c1f659ce6150001838cb39cc2a0003079d463985400060eba8c730a8000c2f659ca6150001858cb394c2a000323d8e72985400064631ce530a8000c8c635ca615000191ce7b14c2a000227a1c63585400060fba8c6b0a8000c1c7518d6150001918c7b92c2a00032318c72585400051bc2ac230a8000a3485584615000152f06b08c2a0002a520d611854000553c12c230a8000aa482584615000713d07390c2a00028da1665185400054b41cca30a8000a9583994615000154d05328c2a0002a960a65185400054bc1aca30a8000a9483594615000154f04b28c2a0002a9209651854000559c02ca30a8000a3686194615001bc66c0328c2a000385d9763185400070a32ec630a8000a368598c615000146b0b318c2a0002a5a0e631854000553414c630a8000aa58298c615000116f0eb18c2a00028de1563185400051a42ac630a8000aa78258c615000154904b18c2a0002a5a1863185400064b3b0c630a8000e176518c6150001c28ca318c2a000389d9762185400071232ec430a8000e8763d886150001d08c7b10c2a00028da1662185400051ac2cc430a8000a9683988615000152b07310c2a0002a9a0a62185400045bc3ac430a8000a378558861500014690ab10c2a0002a5e0d62185400054a41ac430a8000ca6761886150001c4eca310c2a000389194621854000743b18c430a8000e8463188615000152f06ba8c2a0002a520d751854000553c12ea30a8000aa4825d4615000156700ba8c2a0002a9a0a731854000552c14e630a8000ab28094c615000156301298c2a0002a5a0f72185400054ac1ee430a8000a96839c8615000152b07390c2a00028da1472185400051ac28e430a8000ca5721c8615000146f0ab80c2a00028d21570185400054bc1ae030a8000a94835c0615000154f04b80c2a0002a9209701854001c4e41aeda8a80008ac825db515000713d07bb2a2a00022ba0b76545400044f436e6a8a800089e8718d51500071390e31aa2a00022ba1b72545400064631ee4a8a8000c8c631c9515000115d0e312a2a00022b21c625454000647b98c4a8a8000c8c73189515000192ee630aa2a0003251cc615454000653b90c2a8a8000ca4721855150001930c7b82a2a00032a18b70545400065830ee0a8a8000c98631c15150001950c4382a2a00032c184705454000456412ed98a8003c8c639cb31500011590cb9662a000f2318d72cc54000457c38c598a80008ad8718b315000194
  | 3 => 0x490842009c583dd921084016c100b2a4210802e1a0f7448421004d343ec89084200b8683d91210840134d0e3224210803895946448421004b242ae690842009e0805cd210840134d0f21a421080269a1c4348421006c2b988690842009c5831c1210840713906ba4c01080f2698d7010f50004d840ae021ea00389e83dd161d4023838a6bb0872800e27a0f745865008c8e41ae9a8ca00389e83dda419400115d05bb483280022761a739065001c4fc3cc720ca00089f8758e419402323d0738cc9280470798d7690e500841fc32e121ca011c1e635d8439402107f0cb8087280024d2057010e5008e8c182e021ca01191e83dd1619402323d07bb483280024ba0b76906500048ec34e720ca01191f8798e419400123f0eb1c832804647a0e721065003c1fc32e020ca01191c835c0419400125904b8083280474310d72cc65008c8f41ee890ca00083d86dd0219402323d07ba0432800e2720d74d85500860e29aec218a003c98635c04314001a36a6b8086280434614d7010c50004d840ae0218a01091c835d3511400713d07bb4822800e2720d76104500848f41ce3320a010d1a801cd6414021a330039ac8280434510d7118c500868c21ce0318a01183f865c2431402123906bb086280430718d7610c500058d406c6218a01183f865c0431400126902b808628043460c17010c500049dc32e0218a011c3b865c04314001a36c6b8086280434618d7010c5000699c0ae0218a000938815c04314001a6102b8086280024c2057010c500868d98ae0218a01091c835d3611402123d07bb4822804346a0273904500868cc04e7208a01091c835d8411402123d0739082280220fe1970104500848e41ae0208a00092c825c0411402123906ba662280434310d72cc4500868c21ce1988a000b198010d3114001a3086382622804247a0f74484500041ec36e8108a01091e83dd021140018caec9084228002d8201210845008d0e41ac9300a011a1e83906601400163106b24c028003465d173980500049cc3887300a000b1a83906601400713906bb6a3a000f2318d72cc74000653394c398e8000c8e7398a21d000713d07bb243a000e27a0f76087400041ec34ea10e800083f865d421d000127100ba843a0002a9e1921087400060ebb4e72868000c1d765ce50d002343d0730ca1a00428720d76143400850f41cc22868000a1c835d0655000113d0db9aa8a0002a5a0f74185400054ac1ee830a8000a9783550615000152906aa0c2a000307d9673905400060e32ce720a800089c865ce415000113b0fb1c82a0003239cf629054000647398c520a8000c8d7318a415000192ce630c82a0003255cc61905400060fb2ce732a8000c37659c66550007838c73acc6a000f0718d7598d400061bb2ce331a8000c34659c66350007928c738cc6a000f2518
  | 4 => 0x310c0152b03a9cc221847071cf755804308f0c186eab008610c1c731d56010c21c30603aac021802a6a03535804307e4a39ee2b00860fe9030dc56010c1d92e6238ac0218030ddd471580430061a3a8e2b00860ec94731c56010c0194ee438ac021803291c8715804307748180e2b00860ec96831c56010c0192b0638ac02180325d4c71580430764a298e2b00860ec97321c56010c1d9286038ac02180e27a0f7458a5101c4e41ae9304a203c94639c6435440713906ba6c4a8802a320d74d89510054741ee8312a200aa68190c625440153507ba6c0a8802aaa0b74d815101c4e41ae8302a2008ac825d0605440153106ba0c0a8802aa20974181510055940c86302a20389e83dd1621440713906ba4c0288022b20974980510044ec36e6aa4820089f8758e429040151d0432cc720802a36086598e4101c4e41ae13148200c1e7598c629040183aeb318c52080227e1d6318a4101c4f41ceda94820389e831d9529040113b0db9aa52080227a1e6354a4101c4e43cc6a948200c9663dc5529040192cc638aa520803299887154a410064d31ee0a948200c9a631c15290401954c4382a52080227a1e63546410064731ee4a8c8200c8e631c95190401934c7b82a3208032698c70546410060f3acc7b048200c1d7598f609040191cc7396c1208032358e72d82410064731ae5b048200c1f7598d6090401838eb31ac12080e27a0c72582410044ec3cc63048203c94635c4531040713906bb6a42080e2720d76d44410060fba8e6b008200c1c751cd6010401918e7b92c0208030bdd47258041006163a8e4b008200c8f731c96010401918e6392c02080ea3a0f7498b3101d4741ee8b166203a8c831d162cc40791ce6b14859880f231cd6210b3101e4739cc520e6203c8e7358a41cc407918e6b1083988022b20974983310064b322e39946200c8e645cb318c40131904b808698802652057010d310054741087b126200a998010c604c40713906ba4ca1880f2398e7290e2101e4731ce421c420089f8758e428840791eec21a65108022761a739062101c4fc3cc720c420a89f8758e418840713906ba4c11080e2720d749952101c4f41cec21a4200a1c8558c434840153100b18869080e27a0e761052101c4e41ae93284200a1c835d26508401876e8382ca108030e1d070594210062db98e0b284200c58731c165084018e0e2382ca108030ea1070594210061cc20e0b284200a3880597640840183ccb39ec8108030759673d90210060f3ace7b204200c1d759cf640840186aeb38ec8108020f61e65190210041fc3aca3204200a3880594640840147100b2c86108030d5967190c210051c402ca2184200a3880596410840183ccb39c821080307596739042100616b2ce5208420389e839d8410840147100b288210802e1a08434c421005c341c8
  | 5 => 0x50215ccf80052a00070dfb150000000000000011f000000000000da2bc000000740001400000042a00000000350239452ac50e00138800000558000000009b000000112000000e02883a850800000000000001e10003314c080000000002fc155078cb2a70010b0f19624bc990004ac00000000562000000000006180029e00059e0000018da9029000000708000000000000000000000000000000474000000000000100033500000000000a180000000000128800000000210d000045d44000000000f90811ce0a600000000000d28000006b40004848e64c000c936300d0713001e8e6b11f33b00000000000000127c0055200000000000624001f94b60001a4001365663da690009d8000000b800000000000000000000004dd56800000000e9974000000000f10004610faab0009b4b14e20002de00000000672000b42420000009f00000120d71800a25010000009bc0000048282c001b2b70018001f13b400000000000860001e39282140015a2f43e86886348473c3c8a949c001570882ec78ac080000000000000000000358000000000014a0000000000b00057aef8c656e1a0002990ec0002f142000000490000006a8770003320000029402a4fc35185000000f00000c4000754004b28d80009e0004ac000002b8000001db432000a8c000000000f400000000001cc000000000000000000000003200000000000000000d80000000008f0000000000000041800000000270f3a0c236000574000be00083a770000008800054600000000000000000002080000004930e950001e50008f00000000000a0000000044c0001f8260000017c3e01ca001110000001308c4a4000000000000000000000200e00800000000000008000080000080100000400003000000008020020000080400c000018000000280000e0020000481f0000200080100800800000000000000010040340000200200c0080100000000804000000028020000100100100601000000004024010000000040100000202000801000000000090040140000000a00c01800002000000000020000200000201c0000100000c0180100e00000002000000010000020000080000001400001002018018060060000000200800000800000008000010080000000000400000001008000000010000000201000200400001000020000010000000000300200c000010080000080300200001000004000008060080080000000000801801000000000010000000300000801c0000700200001000000000020010060040080000002400006002000000000000040000100800003801002030008050000000000000001000003004000000010000000080000c004000000080000100200c0180180600200801000010008000022d205749805300456412e130c860098f825c75
  | 6 => 0x1d6000c20000000000011e0d80000000000809ce940014ea44b45d500000000000000000480000000005b000000200620cc0282b4000003fa0000025300000076c0049e0000000010d8680014ed5e9c13e8000fa7fc5980000048000000358000188818000014f8002663bea400006c58c0000000054922800000000f693a000000001e0c42420a80000000000000019d000000004a00001e00000081c0000033a0005d00000000000124000000000af44400149000000814cc0004fc000862010000fc00000000000000280a8001064ec2540000000044a0000b8002e9001428000fe000001410000000000000000154c00000000de800000434000000002880013b0004a00000000070c001ec000000000c256a2c63c0000000000021700019433a7c4560011dab00c201c0000000000072665000000399382fe04894a4891a5803800034c576232400fc40aa85824640012300000000000000000000bbc932a6a70f78fd40c3f9550002728d5089f446e0584519580000000000000000000000003ca75d5b000000e88004650d46f00000000013c0018e9600000000000000000000000000002dc64a5b5a910c6c000000542000b4a2c800000002200000000000000000000000000000001fc0008200019dacd970000000000000000022c398ca800012000000002c700000000000000000001c80000018b0002f0000cd000000002a802035504a8d03e0b41d87a33328ce91032e1060001d74620000000017a554370000007a00000024c000f50db15f000c900031e00000000000000b8a2bc743c8e0000000000000004c42947e0001d2000000004e800000180000800a0c000000001228c0000011696b0425bc7b00e000000000005440000000000000055a4d1c2000001e187000000000000000e41c7328000a722e4080000026645b000260000000015280000092c00000000000000004a3000238000ea000bad8d34754a38960800000ac96732300000000000000000f006e00000000000000000003ee000000003d2000000000003010a1df8001a4000000000000013126a68c0022a00000000000000630000004240004891c0008293c0003bc00063e6e0020da0001a0da5ba891542c3000000000006ac00000000000b4c048002801180000016c969cd0527293500000000000041000000000000006e8000000000010e8000006c400000000000000000000000026b00086f2a8000008e1598000000000000013a3360000036e3e00019104a000000005003740000000040e000000008a40000046898c0000016e0009e11a26c72c279e400000000179336990628000000370990f0007d40015b8000001a1be00000117c000000015c0003643f200000000000001222ae0c13d00000000116000000000b7d6b8000000000032f000
  | 7 => 0x13000000087000000000001390001580000027f2af000002971cb382e7234d4e2e40000000000000147000594170a63a00007d9b3000000f19f8504000152102cc1804202b0f838a12d5f8c86e48a9a00860001ca5f000000000582d85e06e00035e000de000000424000512b0000cf0000100002e80000000000000000000000002a2a4ccb83e0449686a0200007884a8bb0008cc0017680000000170134758b218e014798298003ef37c000000007a605c000000000f26108a928000001b26d87740000050a0004438c000001250b200000000000000088001ca00000000000258000b38000000001c06630c000000006d4000000007d8a30000004f45f800000000000000003a0870001da57c8028300000000000000000b980000025c5aa9b000000002735307b94e8000007244c9588001dc2680032760c652483341c8d3575406000ad5b43ba06d4d0aa44821c2b000000ad000000000000001e13d6000000f70000007194f800000000002d400000000000000000005010000012e000642d14ae0005c800000000000000000000012600019000000000000000b42b600067145996000000000000006892495c9f2690000fb8000000000028a00000000000000002b8d2c2e08a16ccce7f8a480051c52d2f04a0000741796d0005e28f80000089c000ef1820013c9c4058584000004d00015640019e000000000000014804e07a5010680000000000000000000828000009746b0ce47a714ab5bb1e86fc79aa62f65920013400032e000000000000006f35c7507f8002860000014d320366cc48b44c49d0d8000960015250a000001590000008a0000d2000000002a000000000000000000000000008bc410003b2a105214f24642c41a441606200027b1ae00000000000000000000000000000000000000000000000b9c000004652cddc0000000003201a00000000486000000000000000015580016800000258000000000000005f0004467e8ae90127c0007aa1e2fa95cc51024608e4000051642601d0004ea5dcd38d301800071c002d5704b9400057aaed08000001c60000047ea3c000001010
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x1a5c0129e0e747613e2154e047134f2e0cd8a0c4c01800000091a000800054000000000000a544000010054872b002b875a616a8c8c2243112281066c46620275a406e8011020102080878938280810000002001427c10301d471580430cf200c0721c56010c012889260043181310050624d841c1650840143091610705942100506241659cf6408401430905967190c2100506241659ce410840142890596729042100609a1d651912108401620905946448421005412557310d2108401580905cc434842100644d4c815c04314031910532057010c500c6440c0815c04314031913312057010c500c64420c815c04314001923822057010c5000648208815c04314031912932057010c500064464c815c04314001913632057010c500c64418c815c04314031913322057010c50004c22498010d311400131091600434c450006185d880484211400111997a0e4198050005062417518c2150001430905d4610854000486660639c05050001a11831867014140004c42458010c508c001c207218450501300048aa4a8610c50c402f13397600419401000486658835d050040272309161843140100c684cc58610c500400121996a0e42140100048665a8390450040273109361c411401009cc4a4e8210450040014189758c50500100070258c721414004001c11631c45050010
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x5
  | 2 => 0x4d
  | 3 => 0x4
  | 4 => 0x124d
  | 5 => 0xcd
  | 6 => 0x12cd
  | 7 => 0x14d
  | 8 => 0x134d
  | 9 => 0xb4d
  | 10 => 0x16cd
  | 11 => 0x5cd
  | 12 => 0x1a4d
  | 13 => 0x14055
  | 14 => 0x4c
  | 15 => 0x124c
  | 16 => 0x14c
  | 17 => 0x134c
  | 18 => 0x170d
  | 19 => 0x14054
  | 20 => 0x8d
  | 21 => 0x8c
  | 22 => 0x128c
  | 23 => 0x4155
  | 24 => 0x4154
  | 25 => 0x8054
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 51
  | 6 => 1187
  | 5 => 2307
  | 4 => 697
  | 3 => 47
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
  | 7 => packedAt gbK7 (1487+((h/23+packedAt gbK7 (1326+(h % 23)*7) 7) % 93)*7) 7
  | 6 => packedAt gbK6 (49463+((h/504+packedAt gbK6 (43919+(h % 504)*11) 11) % 1815)*12) 12
  | 5 => packedAt gbK5 (121380+((h/887+packedAt gbK5 (110736+(h % 887)*12) 12) % 3513)*13) 13
  | 4 => packedAt gbK4 (44159+((h/276+packedAt gbK4 (41123+(h % 276)*11) 11) % 1762)*11) 11
  | 3 => packedAt gbK3 (3423+((h/19+packedAt gbK3 (3290+(h % 19)*7) 7) % 77)*7) 7
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffffffffffffffff000fffffff0fffffffe1ff
  | 1 => 0x803fe007f803fffffffffffffff311e623ffff
  | 2 => 0xffc00007fffc01fffffffffffffc1e383c7fff
  | 3 => 0xfffffff8000001fffff007fc00ffe03fc07e38
  | 4 => 0x1fffffff80000ffffc0007fc0
  | 5 => 0xfffffffffffffe000000000000ffffffff8000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x86c368e85a351a5b0c065b2cd90566cacde0db
  | 1 => 0xa035a226a882dcad74baad576a73116622af6d
  | 2 => 0x6b50044735b84136b95d369bb4bc1a383457b6
  | 3 => 0xf3b9d6f2011089c7de6607e038dfa03f407a38
  | 4 => 0x42211884062311f8ef8fc301c0efffc0007dc0
  | 5 => 0x7c3e1f07c7c3e000f008040200faddb5bb0000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 63 gbPos gbNeg, 0xeaa8aaa8c0808080eaa8aaa8c0808080eaa8aaa8c0808080eaa8aaa8c0808080eaa8aaa8c0808080eaa8aaa8c0808080eaa8aaa8c0808080eaa8aaa8c0808080, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_15233
namespace PEqualNP.Outside.L_meta_15233
open PEqualNP.Outside.L_meta_15233.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs3_2_0 : Interval s3Atlas 2 0 3 := block_range (n:=3) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 3 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 6 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 1 := bs3_4_0
theorem alls3 : ∀ k ≤ 4, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_2 i (by omega) hi
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 6 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 14 := bs4_4_0
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
theorem bs5_3_0 : Interval s5Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 1 := bs5_3_0
theorem alls5 : ∀ k ≤ 3, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_3 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_32 : Interval gbAtlas 3 32 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 47 := (concat bgb_3_0 bgb_3_32)
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
theorem bgb_4_672 : Interval gbAtlas 4 672 25 := block_range (n:=25) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 697 := (concat (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 (concat bgb_4_96 bgb_4_128))) (concat (concat bgb_4_160 (concat bgb_4_192 bgb_4_224)) (concat bgb_4_256 (concat bgb_4_288 bgb_4_320)))) (concat (concat (concat bgb_4_352 bgb_4_384) (concat bgb_4_416 (concat bgb_4_448 bgb_4_480))) (concat (concat bgb_4_512 (concat bgb_4_544 bgb_4_576)) (concat bgb_4_608 (concat bgb_4_640 bgb_4_672)))))
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
theorem bgb_5_2304 : Interval gbAtlas 5 2304 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2307 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)))) (concat (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 bgb_5_384)) (concat (concat bgb_5_416 bgb_5_448) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544))))) (concat (concat (concat (concat bgb_5_576 bgb_5_608) (concat bgb_5_640 bgb_5_672)) (concat (concat bgb_5_704 bgb_5_736) (concat bgb_5_768 (concat bgb_5_800 bgb_5_832)))) (concat (concat (concat bgb_5_864 bgb_5_896) (concat bgb_5_928 bgb_5_960)) (concat (concat bgb_5_992 bgb_5_1024) (concat bgb_5_1056 (concat bgb_5_1088 bgb_5_1120)))))) (concat (concat (concat (concat (concat bgb_5_1152 bgb_5_1184) (concat bgb_5_1216 bgb_5_1248)) (concat (concat bgb_5_1280 bgb_5_1312) (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408)))) (concat (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 bgb_5_1536)) (concat (concat bgb_5_1568 bgb_5_1600) (concat bgb_5_1632 (concat bgb_5_1664 bgb_5_1696))))) (concat (concat (concat (concat bgb_5_1728 bgb_5_1760) (concat bgb_5_1792 bgb_5_1824)) (concat (concat bgb_5_1856 bgb_5_1888) (concat bgb_5_1920 (concat bgb_5_1952 bgb_5_1984)))) (concat (concat (concat bgb_5_2016 bgb_5_2048) (concat bgb_5_2080 (concat bgb_5_2112 bgb_5_2144))) (concat (concat bgb_5_2176 bgb_5_2208) (concat bgb_5_2240 (concat bgb_5_2272 bgb_5_2304)))))))
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
theorem bgb_6_1184 : Interval gbAtlas 6 1184 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1187 := (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 (concat bgb_6_224 bgb_6_256)))) (concat (concat (concat bgb_6_288 bgb_6_320) (concat bgb_6_352 (concat bgb_6_384 bgb_6_416))) (concat (concat bgb_6_448 bgb_6_480) (concat bgb_6_512 (concat bgb_6_544 bgb_6_576))))) (concat (concat (concat (concat bgb_6_608 bgb_6_640) (concat bgb_6_672 bgb_6_704)) (concat (concat bgb_6_736 bgb_6_768) (concat bgb_6_800 (concat bgb_6_832 bgb_6_864)))) (concat (concat (concat bgb_6_896 bgb_6_928) (concat bgb_6_960 (concat bgb_6_992 bgb_6_1024))) (concat (concat bgb_6_1056 bgb_6_1088) (concat bgb_6_1120 (concat bgb_6_1152 bgb_6_1184))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_32 : Interval gbAtlas 7 32 19 := block_range (n:=19) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 51 := (concat bgb_7_0 bgb_7_32)
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
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 3 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 36, 37),(inputs.getD 2 zero, 33, 37),(inputs.getD 3 zero, 33, 41),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 3 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 34, 35),(inputs.getD 1 zero, 33, 35),(inputs.getD 3 zero, 33, 41),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 5 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 33, 41),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 4 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 22, 30),(inputs.getD 4 zero, 14, 30)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 9 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 22, 30),(inputs.getD 4 zero, 14, 30),(inputs.getD 5 zero, 3, 35)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeaa8aaa8c0808080eaa8aaa8c0808080eaa8aaa8c0808080eaa8aaa8c0808080eaa8aaa8c0808080eaa8aaa8c0808080eaa8aaa8c0808080eaa8aaa8c0808080
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 9 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 33 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) (SBf 1) :=
    slice_correct (ms:=fixRows 18 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have s2 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 2 zero)) (SBf 2) :=
    slice_correct (ms:=fixRows 20 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
  have s3 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 3 zero)) (SBf 3) :=
    slice_correct (ms:=fixRows 24 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds3 certs3)
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (3936922280 * 2 ^ 32 + 3229646976) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_15233.Model.Repr at out
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

def mono : List Gate := [⟨.or,[2,3]⟩,⟨.or,[1,6]⟩,⟨.and,[3,4]⟩,⟨.and,[2,8]⟩,⟨.and,[0,2]⟩,⟨.or,[9,10]⟩,⟨.and,[1,11]⟩,⟨.and,[0,7]⟩,⟨.and,[5,13]⟩,⟨.or,[12,14]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,15⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 9) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3936922280 * 2 ^ 32 + 3229646976) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3936922280 * 2 ^ 32 + 3229646976) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_15233

open PEqualNP.Outside.L_meta_15233 in
theorem PEqualNP.Outside.L_meta_15233 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3936922280 * 2 ^ 32 + 3229646976) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3936922280 * 2 ^ 32 + 3229646976) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
