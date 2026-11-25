import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_15133.Model
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


end PEqualNP.Outside.L_meta_15133.Model

namespace PEqualNP.Outside.L_meta_15133
open PEqualNP.Outside.L_meta_15133.Model
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

def SBf (j : Nat) : Nat := [3, 3, 2, 3, 4, 6].getD j 0

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

end PEqualNP.Outside.L_meta_15133

namespace PEqualNP.Outside.L_meta_15133
open PEqualNP.Outside.L_meta_15133.Model
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
end PEqualNP.Outside.L_meta_15133
namespace PEqualNP.Outside.L_meta_15133
open PEqualNP.Outside.L_meta_15133.Model
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
  | 2 => 0xffffffffffffffffffffffffffffffffffffff
  | 3 => 0xffffffffffffffffffffffffffffffffffffff
  | 5 => 0xffffffffffffffffffffffffffffffffffffff
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffff84b7
  | 2 => 0xffffffffffffffffffffffffffffffffff895b
  | 3 => 0xffffffffffffffffffffffffffffffffff926d
  | 5 => 0x238e
  | _ => 0
def s1Atlas : Atlas := ⟨2,rawDecor 45 s1Pos s1Neg, 0xa000a00000000000a000a00000000000a000a00000000000a000a00000000000a000a00000000000a000a00000000000a000a00000000000a000a00000000000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_15133
namespace PEqualNP.Outside.L_meta_15133
open PEqualNP.Outside.L_meta_15133.Model
def s2K1 : Nat → Nat
  | 0 => 0x7
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 1 => 1
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 1 => packedAt s2K1 (i*3) 3
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 1 => packedAt s2K1 (4+((h/1+packedAt s2K1 (3+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 4 => 0xffffffffffffffffffffffffffffffffffffff
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffff8b
  | 1 => 0xffffffffffffffffffffffffffffffffffff95
  | 4 => 0x26
  | _ => 0
def s2Atlas : Atlas := ⟨1,rawDecor 19 s2Pos s2Neg, 0x88880000888800008888000088880000888800008888000088880000888800008888000088880000888800008888000088880000888800008888000088880000, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_15133
namespace PEqualNP.Outside.L_meta_15133
open PEqualNP.Outside.L_meta_15133.Model
def s3K2 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 2 => 1
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 2 => packedAt s3K2 (i*4) 4
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 2 => packedAt s3K2 (5+((h/1+packedAt s3K2 (4+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffffffffffffffffffffffffffdf0ffc1fc7
  | 4 => 0x6ff0ffe0f8
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffff81222d295b
  | 1 => 0xffffffffffffffffffffffffffff82445652ad
  | 2 => 0x24e89b1cc6
  | 4 => 0x188ee398f0
  | _ => 0
def s3Atlas : Atlas := ⟨2,rawDecor 23 s3Pos s3Neg, 0x88888080888880808888808088888080888880808888808088888080888880808888808088888080888880808888808088888080888880808888808088888080, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_15133
namespace PEqualNP.Outside.L_meta_15133
open PEqualNP.Outside.L_meta_15133.Model
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
  | 1 => 0xffffdfe0ffffff803fffffffff00ffffffe1ff
  | 2 => 0xffffffffffffffffffffffffffffffffffffff
  | 3 => 0x6bff07c1ffffc00ffc01ffff00ff007e38
  | 5 => 0x73fff801fffffff00001ffffff00007fc0
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0xffff8022108825924992c5245b4b4b4b6caedb
  | 1 => 0xffffa05e21104af612a54b48adc0d5d5b5616d
  | 2 => 0x8442209324a34992913695a6a6da57b6
  | 3 => 0x1508f43b1c473b8e231dc7e6c0f81c7a38
  | 5 => 0xe1087bde0783c0fc3e1f8f8f8c0e07dc0
  | _ => 0
def s4Atlas : Atlas := ⟨3,rawDecor 47 s4Pos s4Neg, 0xa080a08080808080a080a08080808080a080a08080808080a080a08080808080a080a08080808080a080a08080808080a080a08080808080a080a08080808080, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_15133
namespace PEqualNP.Outside.L_meta_15133
open PEqualNP.Outside.L_meta_15133.Model
def s5K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x40041c6a2a48b03006134001405df43dc43de32dc32be41bc41de31dc31ee21ec21df30dd30fb10f810
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x1c40080a620d000005394b438f2a465a44108638a8985314930aa28a61b041043a062087808410
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 14
  | 3 => 9
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
  | 4 => packedAt s5K4 (244+((h/4+packedAt s5K4 (224+(h % 4)*5) 5) % 18)*5) 5
  | 3 => packedAt s5K3 (255+((h/3+packedAt s5K3 (243+(h % 3)*4) 4) % 12)*5) 5
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfffffff807ffffffffffff80fffffffffc3fff
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xf07ffffff803ff00ffffffff01fc03ffffc63f
  | 3 => 0x7c1ffffffc0000ff807ffffe0003f807f838
  | 4 => 0xff801fffffffffff00007ffffffffc0007ffc0
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x2208825ec124998a28c915c0972d565acc1adb
  | 1 => 0x441104a84a492a1451122a8b2a5698ad51ed6d
  | 2 => 0x8ea20932976234a69a644f558198c337a6c636
  | 3 => 0xef43b1c4e473b8d8e44773e6cd0313c1c77838
  | 4 => 0x87bde070783c0e0f8787c78f1e3e20607b780
  | _ => 0
def s5Atlas : Atlas := ⟨5,rawDecor 31 s5Pos s5Neg, 0xc8888080c8888080c8888080c8888080c8888080c8888080c8888080c8888080c8888080c8888080c8888080c8888080c8888080c8888080c8888080c8888080, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_15133
namespace PEqualNP.Outside.L_meta_15133
open PEqualNP.Outside.L_meta_15133.Model
def gbK8 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x605030001a188e5200000a004a7a00005a004c0200486e1e00860c4470788000144600000056008a2e00007400000058660000000076343e002a1c325e040000008c826c402400008438000000720012004200000064005c0000105468003a7c6a004e007e0e16060036623c262c000028008820000000000022080002040000018001001000100001820400100000400000ffd5001fe54007f55003fc5400ffd4c01fe53005f94c01fd5300ff14c017c53007fd0c01fe43007f50c01fc4300ffd4801fe52005f94801fd5200ff148017c52007fd0801fe42007f50801fc42007fcc801fe3200778c801fd32007f0c801dc3200ffd44017f51007f94401fd51005f54403fc51007fd0401fe41006f90401fd41007f10401bc41007fcc401fe31007f4c401fc31007fc8401fe21007f48401fc2100ffd4001fe50005f94001fd5000ff140017c50007fd0001fe40007f50001fc40007fcc001fe30007f4c001fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x204000bfd8c20005fcc610002fd63080017e3184000df94c20006f8a610002fe6208001bf2904000df14820007de8410003ec4208001f79904000f78c820007b86410003ec3208001e61904000bf98420005fac2100037f5108001bea884000ef90420007788210003ee2108001f61084000bf98020006fca0100037c5008001fda004000fe10020007de4010003fa2008001f69004000fe48020005fecb88006fe65c4001bf32e20019f99710005facb880037d65c40013eb2e2001bf19710005fec988002fe64c40017eb262000bf19310005fec788002fe63c40017eb1e2000bf18f10006fca7880037c53c40017fb162000bf98b10005fac588002fc62c4001bf2962000df14b10007bc6588003dc32c4001bfa8e2000df547100077c8388003bc41c4007fda862000df94310006f8a18800ff850c4001bc2862000fecc310007f06188003fb20c4001fc1062000bfd9610006fecb080027f65840037f32c2000bf5961000df8cb080037c65840033e32c2000bfd9210005fcc908003be64840015f3242000bf592100077ac908002bd64840017e3242000bfd8e10005fcc708002fd63840017e31c2000df94e10006f8a708002ff62840017f3142000bf58a10005f8c5080037e5284001be2942000f78ca10007b86508002fd6184001bfa8c2000df54610007ee8308003be4184001de20c2000fd10610007688308003f73184001fa18c2000fdc8610007e84308002fe6084001bf2842000df14210007ee2108003fb10840017fb2a2000dfd9510004feca88006fe65440017eb2a2001bf19510006f8ca880067c65440017fb222000efd91100057ec888002fe64440017eb222000bf1911000778c888002bc64440017fb1a2000f7d8d10005bec688002fe63440017eb1a2000bf18d10007b8c688002dc6344001bf29a2000df14d10005fec488003ef624400177b122000bf98910005fac488002fc6244001f63122000bb18910006fca4880037c5244001ef1922000f70c910006fea2880037d5144001df20a2000ef10510006fca0880037c5044001fd8822000fd84110005feca08006fe6504001bf32820019f99410005faca080037d65040013eb282001bf19410005fec808002fe64040017eb202000bf19010005fec608002fe6304001ef3182000b798c10005fac608003dd63040016eb182000bf18c10006fca6080037c53040017fb102000bf98810005fac408002fc6204001bf2902000df14810007bc6408003dc32040017f3082000dfd4410006faa208003f74104001df2082000ef10410007e88208003b44104001fb9882000fd0c410007ee4208003f421040017f3002002fed4010006fca0080037c5004005fc2802000de14010007f66008003f83004001fd9002000fe08010007ee2008003fa1004001fa8802000fe44010
  | 1 => 0x2ff654c001bfb2a60009fd953000dfcca98002fd654c0037e32a6000df1953000cf8ca98002ff644c001dfb226000afd9130005fcc898002fd644c0017e3226000ef1913000578c898013df534c001bf29a6000df14d30027b8a6980035c534c0017fb126000fbd8930005dec498002fc624c001f63126000bb18930006fca4980037c524c001ef1926000f70c930005fec298003f7614c0017bb0a6000bf18530007e8c298002f4614c001bfa8a6000df545300077c8298003bc414c001ef98a6000f74c530006fca0980037c504c001fd9826000f78c130005feca180037f650c0013fb286001bf99430005faca18006fc650c001be32860019f19430005fec818002fe640c0017eb206000bf19030005fcc6180037e530c001be2986000f7d0c30007b88618002fe620c0017eb106000df94830006f8a418003de320c001ee1906000bf98430005fac2180037f510c001bea886000ef90430007788218003de310c001ee1886000bf98030006fca0180037c500c001ef9806000fe8c030007ba6018003f9300c0017fb2e4001bf99720006fccb900067e65c80017eb2e4000df59720004facb90006fc65c80017fb264000bf99320005fac990002fc64c80017fb1e4000bf98f20005fac790002fc63c8001bf29e4000df14f20006fca5900037c52c8001ef1964000f70cb20005fcc390002fd61c8001bfa8e4000df547200077c8390003bc41c8001bf2864000df14320007f68190003f840c80017fb2c4001bf99620006fccb100067e65880017eb2c4000df59620004facb10006fc65880017fb244000bf99220005fac910002fc64880017fb1c4000bf98e20007bcc710002de63880017eb1c4000f758e20005bac710002fc6388001bf29c4000df14e20005fac5100037e5288001be2944000fbd0a20007d88510003ef3288001ef1944000f70ca20007d86510003cc32880017f30c4000bf58620006fea3100037d5188001df20c4000ef10620007dc4310003ec21880017f3044000df94220006f8a110003ef2088001fd9044000bfd9520006feca900027f65480037f32a4000bf5952000df8ca900037c65480033e32a4000bfd91200077ec890002bf64480017f3224000bf59120005f8c890003bc64480015e3224000bfd8d20007bec690002df63480017f31a4000bf58d20005f8c690003dc63480016e31a4000df94d20006f8a6900037e5248001be2924000f78c920007b86490002ff6148001fbb0a4000bdd8520005f8c290003f461480017a30a4000dfd4520006faa290003be4148001de20a4000df94120006f8a090003fb2048001f71024000bfd9420006feca100027f65080037f3284000bf5942000df8ca100037c65080033e3284000bfd9020005fcc810003be64080015f3204000bf590200077ac810002bd64080017e3
  | 2 => 0x5000efac2280027d6114003be308a000dfd0450006fc82280033e4114001bea08a000df104500067882280037f3114001bf188a000df4c450006f862280037f2114001bf108a000df48450006f842280077e60140013f300a001de98050005fecba0006fe65d0001bf32e80019f99740005facba00037d65d00013eb2e8001bf19740005fcc7a0002fd63d0001bf29e8000df14f40005fcc5a0002fd62d0001bf2968000df14b400077e85a0003bd42d0001ef1968000f70cb40005fcc3a0002fd61d0001bfa8e8000df547400077c83a0003bc41d0001bf2868000df14340005fecb20006fe65900017eb2c8001bf19640005fac920002fe63900017eb1c8000df94e40006f8a720003be4390001de21c8000bf98a40005fac5200037e5290001be2948000ef90a40007788520003de3290001ee1948000bf98640005fac3200037f5190001bea8c8000ef90640007788320002fe6090001bf2848000df142400077e8120003fb40900017fb2a8000dfd9540004fecaa0006fe65500017eb2a8001bf19540006f8caa00067c65500017fb1a8000f7d8d40005bec6a0002fc6350001ee31a8000b718d40006fca6a00037c53500017fb128000fbd8940005dec4a0002fc6250001f63128000bb18940006fca4a00037c5250001dfa128000ef50940007bc64a0003dc32500017fb0a8000fdd8540005eec2a0002fc6150001fa30a8000bd18540006fea2a00037d5150001df20a8000ef10540006fca0a00037c5050001fda028000ef90140005feca20006fe65100017eb288001bf19440005fcc820002fe63100017eb188000df94c40006f8a620003be4310001de2188000bf98840005fac4200037e5210001be2908000ef90840007788420003de3210001ee1908000bf98440005fac2200037f5110001bea888000ef90440007788220002fe6010001bf2808000df140400077e8020003fa4010001dea008000fe50040005fecb98006fe65cc001bf32e60019f99730005facb980037d65cc0013eb2e6001bf19730005fec998002fe64cc0017eb266000bf1933002fbea7980037e53cc001be29e6005f714f30006b8a798002fe62cc0017eb166000df94b30006f8a598003de32cc001ee1966000bf98730005fac3980037f51cc001bea8e6000ef90730007788398003df31cc001ee98e6000df94330006f8a198002ff658c0037f32c6000df9963000cfccb18002fd658c001beb2c60009f5963000df8cb18002ff648c0017f3246000bf59230005f8c918002fd638c001bf29c6000df14e30007be8718003dc438c0017f3146000bf58a30006fca5180037c528c001ef1946000f70ca30005fcc318002fd618c001bfa8c6000df546300077c8318003bc418c001ef18c6000f70c630005fcc1180037e508c001be2846000f7cc230007f6611800
  | 3 => 0xe32a4200df1952100cf8ca90802ff6448401dfb224200afd9121005fcc890802fd64484017e3224200ef1912100578c890802ff6348401efb1a4200b7d8d21005fcc690802fd63484017e31a4200f718d21005b8c6908037e5348401be29a4200df94921006f8a490803de3248401ee1924200dfd4521006faa290803be4148401de20a4200fdc8521007dc4290802ff6048401fdb024200bed8121005f8c090803f860484017c3024200bfd942100dfcca108037e65084033f3284200bf59421006faca108027d65084037e3284200bfd9021005fcc810802fd64084017e3204200bfd8c21005fcc610802fd63084017e3184200df94c21006f8a610802fe620840df7a904200df94821006f8a41081bec5208401b62904200fbcc821007bc6410803dc3208401f61904200f30c821005fcc2108037f5108401bea884200fdd04210077c8210803bc4108401fa2084200ed10421007de4210803f62108401f69084200fd48421005fcc010802fd60084037eb2ca000bf99250005fac9280077f5494001bf2a4a000df5525000ef8a928002fe6394001ef31ca000b798e50005fac728003dd63940016eb1ca001dfd4e50006fca7280037d5394003be29ca000bf98a50005fac5280077f5294001bf294a000df54a5000ef8a528003de3294001ee194a000bf98650005fac3280077f5194001bf28ca000df5465000ef8a328003be4194001de20ca001bf9825000efea128007fb5094003fc284a000dfd9250006fcc9280037d6494001be324a000dfd8e50006fcc7280027e6394001af31ca0009798e50006fac7280035d6394001be31ca000dfd0e50006fc87280037d4394001be21ca000dfd8a50006fcc5280027e6294001beb14a000df18a50006fe85280037e4294001bea14a000df10a50006fe65280037e3294001af194a000df4ca50006f865280035c3294001bfb0ca000df98650006fac3280027d6194001be30ca000dfd0650006fc83280033e4194001bea0ca000df106500067883280037f3194001bf18ca000df4c650006f863280037f2194001bf10ca000df48650006f843280067e60940037fb2aa000bfd9150005f8c8a8002ff63540017e31aa000df94d5000ef8a6a8002ff62540017e312a000df9495000ef8a4a8003de3254001ee192a000bfd8550005f8c2a80077f5154001bea8aa000ef905500077882a8006ff6054003fda82a000df9415000ef8a0a8007f85054003bfb20a001df9905000efac8280077c6414003bfb18a001df98c50004fcc6280077d6314003be318a000dfd0c50006fc86280037d4314001be218a001dfd885000efcc4280027e6214003beb10a001df18850006fe84280037e4214001bea10a000df10850006fe64280037e3214001af190a000df4c850006f864280035c3214003bfb08a001df984
  | 4 => 0x806fe65cc4017eb2e6201bf19731006f8cb988067c65cc4017fb266200bf993310077cc998802be64cc4017eb266200ef593310057ac998802fc64cc401bf29e6200df14f31007be8798803dc43cc4017f3166200bf58b31006fca5988037c52cc401ef1966200f70cb31006fea3988037d51cc401df20e6200ef10731005fcc198802fd60cc4017fb2c6201bf99631006fccb188067e658c4017eb2c6200df59631004facb18806fc658c4017fb246200bf99231005fac918802fc648c4017eb1c6209f7d4e31006fca7188037c538c413ee29c6200d714e31005fcc518802fd628c401bf2946200df14a31007bc6518803dc328c4017f30c6200dfd4631006faa318803be418c401de20c6200f7cc631007ee6318802fe608c4017eb046200bfd9531006feca988027f654c4037f32a6200bf5953100df8ca988037c654c4033e32a6200bfd91310077ec898802bf644c4017f3226200bf59131005f8c898803bc644c4015e3226200df94d31006f8a698803df434c401ee21a6200bfd8931007dec498802ef624c4017e3126200fb18931005d8c4988037e524c401be2926200f78c931007b864988037f514c401bea8a6200ef90531007788298803f7314c401ef18a6200bfd8131007f6c098802fb604c4017e3026200fe18131005f0c098802ff650c4037f3286200df9943100cfcca18802fd650c401beb2862009f5943100df8ca18802ff640c4017f3206200bf59031005f8c818802fe630c411efa986200df94c31006f8a618823dc530c401ae2986200bf98831005fac4188037e520c401be2906200f78c831007b86418802fe610c401bfa886200df544310077c8218803bc410c401ef9886200fd8c431007ba6218803f5310c4017f3006200bf58031005fecb908037f65c84013fb2e4201bf99721005facb90806fc65c8401be32e42019f19721005fec990802fe64c8401df3264200af99321005fac990803bd64c84015eb264200bf19321005fec790802fe63c84017eb1e4200bf18f21006fca7908037c53c8401bf2964200df14b21007bc6590803dc32c8401bfa8e4200df54721007ee8390803be41c8401de20e4200fd10721007688390802fe60c84017eb064200bfd962100dfccb108037e65884033f32c4200bf59621006facb108027d65884037e32c4200bfd9221005fcc910802fd64884017e3244200bfd8e21005fcc710803de63884016f31c4200bf58e21007bac710802dd63884017e31c4200df94e21006f8a710802fd628840ff7a944200df94a21006f8a51081fec5288401b62944200fbcca21007bc6510803dc3288401f61944200f30ca21005fcc3108037f5188401bea8c4200ef90621007788310803ef2188401fb90c4200bf98221005fac110802ff6548401bfb2a42009fd952100dfcca90802fd65484037
  | 5 => 0x8151006f8c0a88027c6054401bc302a2009e18151005fecba0806fe65d04017eb2e8201bf19741005fcc7a0802fd63d0401bf29e8200df14f41005fcc5a0802fd62d0401bf2968200df14b41007bc65a0803dc32d0401bfa8e8200df54741005fcc1a0802fd60d04017fb2c8201bf99641006fccb208067e65904017eb2c8200df59641004facb20806fc65904017eb24820befd52410077ca920803bd5490417de2a48200bf98e41007bcc720802de63904017eb1c8200f758e41005bac7208037e5390401be29c8200efd0e410077c8720803bd4390401de21c8200bf98a41005fac5208037e5290401be2948200efd0a410077c8520803bd4290401de2148200f78ca41007b86520802fe6190401bfa8c8200df546410077e8320803f741904017f3048200bf582410077ecb2082fbe65904019f32c8200ef596410067acb2082fbc6590401dfb1c8200ef98e410073cc720803bd6390401ceb1c8200ef18e4105f7ea720803be53904019f29c8200ef54e4105f78a7208033c5390401dfb148200ef98a410077ac520803bc6290417dfa948200ef94a410067ca520803bd5290417de2948200cf14a410077e6520803be3290401cf1948200ef4ca410077865208039c32904015f30c820befd46410067ea320803be5190401dea8c8200cf5464105f78a320803bf6090401df3048200ef5824100778c12082fbf5090417de2848200bfd954100dfccaa0802fd65504037e32a8200bfd8d41005f8c6a08037e5350401be29a8200bfd8941005f8c4a08037e5250401be2928200f78c941007b864a08037f5150401bea8a8200fdd05410077c82a0802ff60504017e3028200bfd944100dfcca208037e65104033f3288200bf59441006faca208027d65104037e3288200bf990410577ea820803be5410401deaa0820aef15041005fcc620802fd6310401bf2988200df14c410077e8620803be4310401dea188200ef10c41005fcc420802fd6210401bf2908200df148410077e8420803be4210401dea108200ef10841007bc6420803dc32104017f3088200dfd4441006faa220803bf4110401fb2088200ef50441007ea8220802fe60104017eb008200efd94410577cca208033e6510401deb288200cf5944105778ca20803bf6310401df3188200ef58c4100778c62082bbf5310401df2988200cf94c410077aa62082bbc53104019e2988200efd88410077cc420803bd6210401de310820aefd48410077ca4208033e5210401dea90820aef1484100678a420803bf3210401df1908200e78c8410077a6420803bc3210401ce1908200ef984410057cc220803b66110415dfa888200cfd44410077ca220803bd51104019ea88820aef144410077ec020803be6010401deb008200ef180410577ea02082bbc50104017fb2e6200dfd9731004fecb98
  | 6 => 0x13fb286401bf99432005faca19006fc650c801be32864019f19432005fec819002fe640c8017eb206400bf19032005fcc619033df530c801bf2986400f794c32006bca619003dd530c801be298640cf714c32006b8a619003df430c801ef2186400f750c32007b88619002fe620c801bf2906400df14832007dc8419003ed420c801ef9906400fb8c832007ba6419003ed320c8017f3086400bf58432005fcc019002fd600c801efb286400d7d9432067bcca19003dd650c819ee3286400d719432007bec819003de640c801eeb206400f719032067bea819003de540c801eeaa0640cf715032007bcc419002de620c801e7310640cf7d4832007bca4190035e520c801eea90640cf714832006b8a419003df420c801ef2106400f390832007ba8419003cd420c801ee2106400f7d8432007bcc219003dd610c801ee308640cf7d4432067b8a219003df600c801ef3006400f758032007b8c019033df500c819ee2806401dfd935100efcc9a88073e64d4403beb26a201cf5935100ef8c9a88077f63d4403bf31ea2009f98f5100efac7a88077c63d4401bfa1ea200df90f51006fa87a88037c43d4403bfb16a201df98b51004fcc5a88077d62d4403be316a200dfd0b51006fc85a88037d42d4401be216a200dfccb51006fc65a88035e32d4401be996a200df0cb51006b865a88077f60d4403bf306a2009f9835100efac1a88077c60d44037eb2ca2009f59651005fcc928802fd64944017f31ca200bf58e51006fca7288077c53944017f314a200bf58a51006fca5288077c5294401ef194a200f70ca5100dfcc3288077f5194403fba8ca201fd14651005fcc128802fd6094403be284a201bfd9551005fec8a8803bf64544015fb22a200bf1915100778c8a8802bc6454403bfaa2a200df95151006faa8a88077c54544017fb1aa200f7d8d51005bec6a8802fc6354401ee31aa200b718d5100efea6a88037e5354401bea9aa201df14d51005fec4a8803ef625440177b12a200bf18951007d8c4a8802ec6254403bfa92a200df94951006faa4a88077c5254401ef192a200f70c95100dfec2a8807f75154401bf28aa201df1455100fe8a2a8802ff6054401fdb02a200bed8151005f8c0a8803f860544017c302a201dfd415100ef8a0a88037f64544019fb22a200df99151006fac8a88037c64544019e322a200dfd8d51006bec6a88037e6354401beb1aa200df18d51004f8c6a88035c63544012e31aa200dfd0d51006fc86a88037d4354401be21aa200dfd8951006dec4a88037e6254401beb12a200df18951004f8c4a88036c625440136312a200dfd0951006fc84a88037d4254401be212a200dfcc951006fc64a88035e3254401be992a200df0c951006b864a88077f61544033fb0aa201ddd8551006fec0a88037b6054401bf302a200df5
  | 7 => 0x290077d6014803be300a400bfd974200dfccba10037e65d08033f32e8400bf59742006facba10027d65d08037e32e8400bf98f42007bcc7a1002de63d08017eb1e8400f758f42005bac7a10037e53d0801be29e8400ef90f420077887a10037e52d0801be2968400bf98742005fac3a1002fe60d08017eb068400bfd964200dfccb21002fd65908037e32c8400bf59242005fcc721002fd6390801bf29c8400df14e42005fcc5210037e5290801be2948400efd0a42007de8521002fe61908017eb0c8400bf98242005fac121002ff6550801bfb2a84009fd954200dfccaa1002fd65508037e32a8400df1954200cf8caa1002ff6350801efb1a8400b7d8d42005f8c6a1003dc63508016e31a8400df94d42006f8a6a1003be4350801de21a8400df94942006f8a4a1003ef4250801df2128400bfd8542007eec2a1002f761508017e30a8400fd18542005e8c2a1002ff6050801fdb028400bed8142005f8c0a1003f860508017c3028400bfd944200dfcca21002fd65108037e3288400bf99042005fcc621002fd6310801bf2988400df14c42005fcc4210037e5210801be2908400efd0842007dc8421003bd4210801f6a108400bf98442005fac221002fe60108017eb008400bfd973200dfccb990037e65cc8033f32e6400bf59732006facb990027d65cc8037e32e6400bfd9332005fcc999002fd64cc8017e3266400df94f32006f8a7990037e52cc801be2966400fb90b32007da8599002fe61cc8017eb0e6400bf98332005fac199002ff658c8037f32c6400df9963200cfccb19002fd658c801beb2c64009f5963200df8cb19002ff648c8017f3246400ef992320057cc919002fd648c801deb246400af59232005f8c919002fd638c81befa9c6400df94e32007bca7190035e538c801eea9c6400df14e3206fb8a7190035c538c801efa1c6400f790e32007ba8719003dc438c8017f3146400df94a32006f8a519003df328c801f79946400bf98632005fac319002fe608c8017eb046400f7d963206fbccb190035e658c801eeb2c6400d75963206fb8cb19003df648c801ef3246400e799232007bac9190039d648c801ee324640df7d5232007bca919003dd548c81bee2a46400b798a3206fbea519003de528c801af2946400f754a3206fb8a5190035c528c801efa146400f790a32007ba8519003dc428c801efb0c6400f798632007bac319003dc618c81befa8c640df714632007bec119003de608c801eeb046400f71823206fbea119037dc508c8017fb2a6400dfd9532004feca99006fe654c8017eb2a6401bf19532006f8ca990067c654c8017fb226400bf99132005fac899002fc644c801bf29a6400df14d32006fca4990037c524c801f79926400f78c932005fec299002fc614c8017fb026400bf18132005feca190037f650c80
  | 8 => 0xfd8653006fcc3298037d6194c013eb0ca600df18653006fec1298037e6094c013f304a600df58253006f8c129806ff6554c017fb22a600bf1915300dfec6a9807df5354c01bf29aa601df14d5300fb8a6a9802ff6254c017e312a601df14953005fec2a9802fc6154c03bfa8aa600bfd8153005f8c0a98077c5054c03bfb20a601df9905300efac8298077c6414c03bf318a6009f98c5300ebcc6298077f6214c03bf310a6009f9885300efac4298077c6214c03bfb08a601df9845300efac2298027d6114c03be308a601dfd805300efcc0298027e6014c03beb00a601df18053005fecba1806fe65d0c01bf32e86019f99743005facba18037d65d0c013eb2e8601bf1974307fbea7a18037e53d0c01be29e860ff714f43006b8a7a1802fe62d0c01f73168600bb98b43005fac5a1803ed62d0c0176b168600bf98743005fac3a1802fe60d0c017eb068600bfd964300dfccb21802fd6590c037e32c8600bf59243005fcc7218037e5390c01be29c8600efd0e43007be8721802fe6290c017eb148600bf98643005fac321802fe6090c017eb048600bfd9543006fecaa18027f6550c037f32a8600bf5954300df8caa18037c6550c033e32a8600df94d43006f8a6a1803df4350c01df21a8600bfd8943005f8c4a1802ff6150c017e30a8600bfd8143005f8c0a1802ff6510c037f3288600bf5944300df8ca21802fe6410c017f318860ef7d4c43006fca6218037c5310c1dee2988600d714c430077e8621803de4310c01dea188600f750c43005fcc421802fd6210c017f3088600bf58443005fcc021802fd6010c037eb2ca400bf99252005fac9290077f5494801bf2a4a400df5525200ef8a929002fe63948017eb1ca401dfd4e52006fca7290037d5394803be29ca401bf98a5200efea529007ef5294803f6294a400bf98652005fac3290077f5194803be28ca400bf98252005fac1290077f5094803be284a400dfd9252006fcc9290037d6494801be324a400dfd8e52006fcc7290027e6394801beb1ca400df18e52006fe87290037e4394801bea1ca400df10e5200cfcc5290037f6194801bf30ca400df58652004fac3290037c6194801bfb04a400df98252004fcc1290037d6094801be304a401bfd9552005fec8a9002fc64548017fb1aa400f7d8d52005bec6a9002fc6354801ee31aa400b718d52006fca6a90077c53548037fb12a401fbd4952006fca4a90077c5254803f6292a400bfd8552005f8c2a90077f51548017fb02a400bf1815200ef8a0a90077f6414803bf320a401df5905200ef8c8290077f6314803bf318a4009f98c5200efac6290077c6314801bfa18a400df90c52006fa86290037c4314803bf310a4009f9885200edcc4290077f6114803bf308a401df58452004fac2290077c6114803bfb00a401df98052004fcc0
  | 9 => 0x1200c01201000201206e00604e0160340000000c202001a00800400400000002200803800400600800001c02a00800600600000200000000000400000000600a00200000600200602e01000000801003000000401600a00002200200203200e00800201600400000000002a03e00c00000601600e02600200a00001a04001e00200800600e00e00a00800200600800001800200000200600000000001000000002401401a00000001801400000001000600000603400000001a00200401400201400000800400001c00000004200000800a00e00000a01a00600802800000e01e04a00a00800200403200000e00600000000000800800200c00400000000a00a00600a01200801800c00402200000000400001a00200e00803600e01200800000600000001002200001000c00c00400000001a00000a00000001000a00a00000600800600a00403000600000600000a00403c00000400c00400002a00000203000000000600a00000801200600401603000e00000200600400000c00400200c00600208e05800001a00400201800201200002e00200600600003200000000001e00000c01e00000400001000400200001200000001600600201000001200201201400c01000402800006800e00000000001001e00001400200000e00000000401600402e00c00600201a00000601600600400201200400602800400203801000400002601000a00201a00000a00800200c00200200400200000c02200000c00c00000401200600a00200800000005a01400c03201e00e00000000200201200001800600001400000200200000600400400000200a00a01004600000200c00c00e00600003800400400800000001204a00a00600200400000203000200a00000400003800000200600000001201400200607600000000001000a00000200c00c05c00200200201200001400a01200400c05201bf5965400dfcc92a0077f5495003dfaa4a801ef15254005fcc72a002fd6395003be29ca800bf98a54005fac52a0077c52950017f30ca800bf5865400efea32a002fe60950017eb04a801df1425400dfecaaa006ff6455003dfaa2a800df9515400ef8a8aa007bc54550017fb1aa800f7d8d54005bec6aa002fc6355001ee31aa800b718d5400ef8a6aa002ff62550017e312a801df14954005fec2aa002fc6155003bfa8aa800bfd8154005f8c0aa0077c50550037eb2ca600bf99253005fac9298077f5494c01bf2a4a600df5525300ef8a929806fe6394c03bfa9ca601f7d4e5300fb8a729802fe6294c017eb14a601dfd4a5300ef8a529802fe6194c017eb0ca601dfd465300ef8a329802fe6094c017eb04a601dfd425300ef8a1298037f6494c01bf324a600df59253006f8c9298067e6394c01bfb14a600df98a53004fcc5298037d6294c01be314a600d
  | 10 => 0x9a000000064010400014ccbdc2841ba13144540000000000a1432a0000000a5c000000000000000011700000000003338adc1de068000000000000000000005d21080bc80000001a400000ac5b676b2a80e180fc60a26b800000000024a94b43aa000000000000049a095008865073923f1d70bd80001e31d584a841d1829ef8a3e0002540dac08c0000000000000000057054000000000008a419e4c82458934cb44b032e84289d073609496640e44cd3079300a4a0f2176091c6ba2bc0000000af06dc0169dcc332000000000049c18f2e900000000001881ee40003e00988000f1673401e17500006b600003a800000009d8000d8a0000188000a6c1ce0001e840000002d6942c0000001f780000aa51a1490a404d47d113193b000033d0288000dd02ed00000000001732ed8000b66000185878c78a0000000000832609238000066663100018040000a536f00007ee0002fd19ac8a408b0870d089420003998778000000204000030600000000003ac33c21e8e101ac2611d5908800000035e023800000000000000000000001eac28a60e248965814006134c074008874f08e8efc81a3932320df8bde38e0000ed5006000198800088a4b222182dc0000df3b201a4f040f015c0000e52000066800000073c0001dd4e642b5000000008a69b0001e742b448511688644cc0001d200e400000000005d40004cc0000000b9a30200000006e400020a9edc49e52012d8de8bec4473dd156486c09b2ae168c27800031800007d619a0c904b42b20000000000f9a15d1439ed000046d00000000005df0000000eb451304c0f287d44972ec92f4c4400031d0000c9e08430e804c00042f00000007ac4292991a5cede5c41d688b05ea0000001884d6e5fc39f9af40006e32f8800006064900010d431209f3171b20a9e0003011988ad237c00000000000003e514b000600600a00000400000000000a00200801400000a00002000000401200400600600600200202400600001000a00201800600001400803201c00000000a00000200000000c00200000203800600e00e00600e04001c00602a00000000601c00000200800a01400601400a01000200e00200400200200201200200000000001000200000000000a00001001400000401c00800c05200a00001c00000000200401800200800402400600200800c02600200002e00202000000200a00201001a01003600000000200200200601000800000e00201400201200000000000401000c01e00c07c00001001c00800c00000400000600802a01200600000200801c01e00800000000000000e01200000800000200402600000000400a00001800600007a00200a00602000a03a00400000400000400200601000c00e01400000400a00001401601200400001200000600203400401801a0320060
  | 11 => 0x1324ff400020517586f2462000000000000005780000ce5ce25f96d8ca477f0000000a042491cb1e88cc227e28690b0b5c5b000294dcc9406b3fb12284563b1076194ccf829109a8478f186724001ea440c3db3f083d8f1e80800000cc6a274902c80000003ac00012a80ee2c10e903ec7f802123a8000d7400409011dcdf26631531a2c9820000da1b847b06d71e3951c0000341c48fe45c23c110b92f000000014d0000ee46753728000000664000000000000037598581c64f10000000e4c1741899638b300922578c44fdc1a019a8000a1e1c538a01780001c000008e81680002a91af8ac600033601ec0000000000000de823d33a1198a8a0001451e446ca0002a588d000040f13d02040be0000000e3c61075317b000038e00000005dc000472348905800032d0000000d0a000000010ceb659c000000000065600d8000d182772670bc853206d2e2835c9ca74e0aa12b886e5bb2860c7c8703c0000123801a7cf0978c944ea0230000000c5800036180f8eae00039681bcb3436113b1e6cb0e2ab0001b643d83aa2008000000421143000000073b10599e4b0c05a3231d100007d7000000000026c0001978b5621007d0000b9056200006940004310001454c9a2ce024001896e7c716c8794cd241b00000a000000015711f000032129795b4e5457f0001584d7270727f000007465c2ab82300006ac20180000000002bd1e90a060000001ab87fe00000015743160003c68ad860c0000bd80000000000001fec29e46f1340ac83f81090000db423e53e000003c00078738619387404f401300000008050d0918caf21df0000a340004f60511d8000025a38c9cb039211a1711178b2279412f00000006111a59860fd43362f5867c000474000000000003d3f60750e161570d70000e446c40e79f04ec22d20ad965cdc068f0e8959c73a75512892646f626b3ac15ac2587fc0ca09c89403850fe807cd284840fb0a4c54244822b05f4c501db241007000000012507900007d037b0000b8441a1d28000a3a1230d193640007b00001368428133132151822015e2871ec4fe82f30af823480c7a7338879c2d0613067104c4966361ec8e8c0007b50000384faa0000b192884981cd33c000064c09330912208a60003ba000000218e25c0e0c00047d3e58000d0670327d0064cf60cc00000007d00000000a14b440002431e140001fb00000008f611303d18d0bca2c407f0f940000000c6832cc0000000000002745ca07b8cb0f3c2b30000f4c00003b2d20000be0243000000066858a0ac1b242303ed0001fd410a00012800001e626923280001cc1ed03a17a46ee2bd2248d8c65600015d0d383261050001d042320e93b80780dde5850c415689ac00010684ac69243b05f1f486001af16a9ba479a3690000ea4da631200016480007c50e5158000
  | 12 => 0x5638a2ee0ef440200000002fccfc2961001a8444e49e37383e000000012f8000000165328000035034605314a8a885cc2bd8250b82000001186c68002f02e91285440601c1034c8200000000000e1c0000000fb09764b3000000088c0000ee1c607381f83c99138c4e000170012c12e14600000008b649426a16bccfe14d18d1f74f6c5270000000bbc7150000000010000065148415839434399b82c459d1f11f507323a21ae1b006880c00cc178c63258c0c380001d00e03c1800000018c1de00000003c209c16b0e7c4fb0971db0c886a90000000000000000000000030900000000004a928e06f84f60000001b500001024079df01ca7aa1298ed0bc000011895540004ac0910050b4e00029106e000049800015d400036f000197ca4c5731ea01fc10e71f0238da0dda0000000c10e602583d183fc58e02e00016f88b813d1d71d0800052b1ee17d44701252da91a00000321b9800100218a0000fd816c5f21f90ab452820e1e58db8a700a40691f245685110ff19c05924783ff80000004c61a8127c48400024015082367100248b14f5c3ee19d9030b4a2ea1ef981cde238810c00005ba5f90001e0487e48927788680002f9000000045e6ce1b8967c7343e70251bb80402fe3f5800061a0000000f900003531a508ec1ea796406083c70e39127985c82da60421d18f05f06bb2d49b6ce086470f780000007d600000001a250737e9d289bc00014d86d89da00027004840000001c8109000000000000002a249c0001c7400048339d117c5800000ee800067c0402ca00000000002b880001a00001af07088b000000000000000ed1d38dd85ee7713330554d004ea345000034c2831381b68c6a0d823f96a06c428e04788a02c265131b9f7c7b45b91a19be83720f91ee94c43d27e032c80309cc45526790787aa551217154cbb078905c8058eb233902d950c54e7de3ed977448000034490a80004db0001dd8ad81811669a6400000000000000c60003159a40a1000030a8000268000235817057e4391be8d54c4600020c07880003b63b118bcf7a2113300b70b744f73a1973c0c82a539292487f00000d98610eca3163e207601bc00000000000000aa38895f805411c1401e380e00760000000efa00019f8e2c0000820000f20eba402398985080854a37d9c4c00040900008c800034d29a0d605983923cc886cc3c30112a9cac0003cc0001a70c6421c2a40a60c3217f0001f640001760001c04e8a19c1e912d8ab62672ea8000dfc70d14084d897c180408085485655f2ac0b8c3ea01835416c834471e1a4130c5de00000000442a46e200000009ba7050000000b0017e22a12c49b017c06e8aa8a8269506a042cabc0001af9f0cc8080b1771f9832265b000169891a00005888d8d9800030809f4d9a00036a80009c800016b00008e22fd00
  | 13 => 0x9b8a9a5a000489e43ae00011f0b7c52a5232e89d40e421ea0839f70f8c6061aa107c53812734e9348cf45d31119c6cc7645122b9a68e7a2a831f0b28b0221e0280160e5e7b31d80580e806773f206e83e42d103a9410b0808817e109c3c20f4343000057c0e70d585a87e24eb2c181b81c43f40000a804b85742558b782d87f929e0000c6679527c065c2923b900015dc47e000000000000002526800000fa00035100007880000618bc0c0a1d93f384c86ea00039b8000ebe3e33580b400580002830bac0007673a3800079c08a3d915bc00000037c0000164364000129490203523c8c3cdfe25606e05b8c9816922585c0b787fd274913c48868e27ca03853e0b5000067400074c29400007f62e6000000058c0000cd836ce4612431c1a7822431d13003b8c8267d00000007d231c20382f0da403700006a4de07a51039440d2c4cb25c8000c843e6404820c91809d17a0640bce70f0210000d9401d08b895c6f034c3920cc0d624003cd1e1855e1f000007d00000003498454afa42516a07cc9be27426988903a642828f1cd49c600000b93b836036700005980006392a489209881eb2e800000002e400000000003951bf800084000000009f00000001918000bfc1282b200000002652cd9920fe05fb0001e0000000030d1d4800053a0b3831489836c18d8bfc0006c21949c082940001d915f05847f14011a982d60780000d641f86680d60ba000000a00f031cc4a5701e48000d5600027e800000033a0000000000000154801c2002c824980000ca0800148d14166000000028400032223603acc1870800000001705193c8098800000022c8ef895a3320bd1370b8c6291ff0a74a021a735900000001da3228da835425914106d40007793e7000000000008091a50085930000c6062a2e7252000033c18600000003966bf000000000058235680540007ef14b90f00ac55638511cc10c720397031069e49b28b1fa4d046203cf931ce245662dc159447868100000000000003de0fcc5620000e20fc0b7e6df02b9efcc544d12d884980000002479b745f67e83539e5c09867303101b03620000270258a2424617d1eb48ce02424e8974b6e6a004a9b904f04e133b1b40e0056e000121cf5814e25390c8caa4260000d985480000278c50eda50900006f400062d3fb87c40000002c480000006a524b00004fe1371db800000016f3bf124000000000000000000003f980000000002eb93fc0000000ab03f47a27d80001b185863a6086000000040500001e437621f00000000003de251904800000005484e4c9613f0001f000004600058000aa8000219941400056800000005e26af4050ce0b420c629f88286ae5170de132881c39f0a11fe03820000e1824468e0a33d78c1c00047600011a80004412fc0ea01b42e53440cdc07047a01b15c81
  | 14 => 0xb605b46240000000f406c109f17d065e7282370000000000000000000039e00016780000001e815d86480000000848c7a000000000071a657000043442c4303b5000085a1bf0001174e386c72611a7c3fe35600016d01746a3013987ca9c30a0831898ed01853b310f84823520388f5cfc65e60788e304122bb11988d4ea87fe000000000000000001f000032700008e4b2a00027914d45168073a682ec8462cb0000000fa64b42e1972c0000033c51ce0a287e238d17a801c63f1dd8898d70000000139c0006033dd80fc000784342000035a6e62058a3c0000001369460e907ed10192e838c1530f402407027e533793c0dd874b1020e84f306b40448f3c0340d504e14908685f71ad8d800005291678c787706d60f317fcf4c1302268e6c21e41c1379aa8f706652711bd42985c702994c00004172c69b604445bd0000000c3800008891001921f91f09044d486b32f202c04420000001b3c000000000015000054030591080002130568a240003af3e12034ca87f218197b44105e80001bc8ad458b27a972400006615197ccb545c03c9045828e64306c9decdf8414106073048a00000019b42823b30a417f46e03973938658dee500000118446e1ee1129de0edc53b1fd03084600a800000005100100fd0ee84e60003c403042883c33af1c2436e0990d91788cb006a3750948ec63801cc080800054c25a8c380006b5000185c0e61950090000f900000000ae42803f5222040c5a6706000163ce2e6080001f30eee7163351de844059007207202965da16b8a7862e14308a1da4d968060ae06081905391ad000056000034900002f06d1346829cbc200004f1d44de67da0000000a360000001ea00824a622d00009f820519700005580001fe80000a45881a08a309aa450306800017a53d00005c443a0003ce00002c81f73a309c409a30c0
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xf7258c10004dc7258c10006cc7258c10004cc7258c10006d47158c10006d87058c1000c7e7518c100047d7518c10004de7318c100047f7694c100047d7694c100065e6394c100065d6394c100057a7094c1000c7f7614c100047d7614c100065e6314c100065d6314c1000c7e75d88100047d75d8810004de73d8810004dd73d88100047f755881000c7c7558810004bf7458810004bc7458810004df7358810004dc735881000c7e75188100047d7518810004be7418810004bd7418810004de7318810004dd73188100047f76948100047d76948100065e63948100065d63948100057a709481000c7f76148100047d76148100065e63148100065d6314810004df768c810004dd768c81006e5e658c8100065d658c810004df760c810004dd760c8100665e650c8100065d650c810006cf620c810006cc620c81000c7e75984100047d75984100047d76d44100065e63d44100065d63d44100047f76544100055c73544100065e63544100065d63544100056c725441005e3e65904100063d65904100069e63904100069d6390410005b671904100563e65104100063d65104100069e63104100069d6310410007375110410007355110410004f57610410006b67610410006b57610410007367510410007357510410007366510410007356510410007966310410007956310410007365310410007345310410006b66210410006b46210410007365210410007345210410007963210410007943210410007b27010410007b17010410087b35010410087b05010410005b674cc410006d563cc410004f5760c41000754530c410005b674c8410004f57608410007645208410007c43208410004be7498010004bd7498010006b441980100047f769401000c7d76940100055e73940100065e63940100065d63940100057571940100073441940100157a709401000c7f76140100047d76140100065e63140100065d63140100057571140100073441140100167a76140100057976140100167976140100047976140100057a73140100075a63140100075963140100057a72140100075a321401000758321401001772711401000579711401001771711401001e7a61140100077341140100073a41140100073841140100077041140100073041140100077331140100077031140100077321140100077021140100157a75cc010006d963cc0100075853cc010007b041cc010007d331cc010004f9760c01001578750c010007b0410c010007d0310c0100157a75c8010007b041c8010004f97608010015787508010007c83208010007b04108010007e021080100077050c401000cf97684010015787584010007b04184010004f77644010005b47444010005d47344010005e47244010004fb7644010015787544010005d87344010005e87244010
  | 1 => 0x89100047d75d8910004de73d8910004dd73d89100066f65d89100066c65d8910006af64d8910006ac64d8910006cf63d8910006cc63d89100066e75d89100066d75d8910006ce73d8910006cd73d89100066e53d89100066c53d891000c7e75989100047d7598910004be7498910004bd7498910004de7398910004dd7398910004ee72989100047f755891000c7c7558910004bf7458910004bc7458910004df7358910004dc7358910004f77158910004fb7058910004ee76189100066f65189100066c6518910006af6418910006ac6418910006cf6318910006cc63189100066f75189100066c7518910006cf7318910006cc73189100066e53189100066c53189100047e76949100047c76949100063f64949100063c64949100065f63949100065c63949100066f62949100066c62949100047e761491000c7c76149100063f64149100063c64149100065f63149100065c63149100066f62149100066c6214910004de768c910004dc768c9100065f658c91006e5c658c9100069f648c9100069c648c910006cf628c910006cc628c910004de760c910004dc760c9100065f650c9100665c650c9100069f640c9100069c640c910006cf620c910006cc620c9100047e76d45100063f64d45100063c64d45100065f63d45100065c63d45100066f62d45100066c62d45100057a70d451000c7c76545100063f64545100063c64545100055c73545100065f63545100065c63545100056c72545100066f62545100066c6254510005787054510004be76905100063f659051005e3c65905100069f63905100069c6390510006af6290510006ac6290510004be76105100063f65105100563c65105100069f63105100069c6310510006af6210510006ac62105100047e76941100063f64941100063c64941100055e73941100065f63941100065c63941100066f62941100066c62941100047e76141100063f64141100063c64141100065f63141100065c63141100066f62141100066c621411001e7865c4110006d863c4110006e862c4110006b46484110006d46384110006e46284110004de73d9410004dd73d94100047d7699410014f8705941000c7f76594100047c73594100047c725941000c7f715941000c7d71594100167b705941000678705941000c7e75d90100047d75d9010004de73d9010004dd73d901000c7e75190100047d7519010004de7319010004dd7319010004ee7219010004ed721901000c7e75d8c100047d75d8c10004dd7698c100065e6598c100065d6598c100065f7598c100065c7598c10004de7298c100047f7558c1000c7c7558c10004bf7458c10004bc7458c10004ef7258c10004ec7258c100065e6558c100065d6558c10005cc7258c100065f7558c100065c7558c100069f7458c100069c7458c10006c
  | 2 => 0x4be7418e10004bd7418e100047e7694e100047c7694e100063e6494e100063d6494e100047e7614e1000c7c7614e100063e6414e100063d6414e100065e6314e100065d6314e1000c7e75d8a100047d75d8a10004be74d8a10004bd74d8a10004de73d8a10004dd73d8a1000c7e7598a100047d7598a100047f7558a1000c7c7558a10004df7358a10004dc7358a10004be7418a10004bd7418a100047e7694a100047c7694a100063e6494a100063d6494a100047e7614a1000c7c7614a100063e6414a100063d6414a100066e6214a100066d6214a100065f658ca1006e5c658ca100069e648ca100069d648ca100065f650ca100665c650ca100069e640ca100069d640ca10006ce620ca10006cd620ca100063e64d46100063d64d46100057a70d46100063e64546100063d64546100055c73546100056c72546100057870546100063f659061005e3c65906100063f65106100563c6510610007375110610007355110610006b56410610005b57610610006b57610610007367510610007357510610007376510610007346510610007365310610007345310610006b66210610006b46210610007365210610007345210610007963210610007943210610005b674cc61000754530c610005b674c8610006b664c8610006b66408610007645208610007c432086100063e64942100063d64942100055e73942100057571942100073441942100063e64142100063d641421000575711421000734411421001e7865c421000c7e76d95100047e73d95100047e72d951000c7e70d951000c7c70d9510004bf7459510004bc7459510004df7359510004dc7359510004ef7259510004ec725951001cfb70595100047e76195100063f65d91100063c65d911000c7e75991100047d7599110004be7499110004de7399110004dd7399110004ee7299110004ed72991100047f755911000c7c7559110004df7359110004dc7359110004ef7259110004ec7259110004f77159110004be76191100063f65191100063c651911005cbe7119110054bc711911000c7e75d8d100047d75d8d100065f65d8d100065c65d8d100069f64d8d100069c64d8d100065e75d8d100065d75d8d10004de72d8d1000c7e7598d100047d7598d10004be7498d10004bd7498d10004de7398d10004ee7298d10004ed7298d100047f7558d1000c7c7558d10004bf7458d10004bc7458d10004ef7258d10004ec7258d10004f77158d10004fb7058d10004de7618d100065f6518d100065c6518d100069f6418d100069c6418d100065f7518d100065c7518d10004de7218d100047e7694d100047c7694d100063f6494d100063c6494d100065f6394d100065c6394d100047e7614d1000c7c7614d100063f6414d100063c6414d100065f6314d100065c6314d1000c7e75d
  | 3 => 0xd76104200063f65104200563c65104200078c321042003e6c6588420005ce73884200366c6508420007a4410842000c7e75980200047d7598020004de7398020004dd7398020006cc32980200063e64940200063d64940200055e73940200056e72940200074c32940200047e761402000c7c76140200063e64140200063d64140200056e72140200074c3214020006b964d0020007ab42d0020007c832d0020004f97610020007a84210020007c83210020007c83288020004ef7648020005ac7448020005cc7348020005e471480200076a5048020004fb7648020005b874480200076a5248020007ca3248020005f07148020004df7359710004dc73597100055c73597100065f73597100047c73597100065c73597100045c73597100047c72597100067b705971001e78705971000c7e75d93100047d75d9310004de73d9310004dd73d9310004ee72d9310004ed72d931000c7e75193100047d751931000c7e75d8f100047d75d8f10004be74d8f10004bd74d8f10004ee72d8f10004ed72d8f100047f7558f1000c7c7558f1000c7e7518f100047d7518f100047f7694f100047d7694f100057a7094f1000c7f7614f100047d7614f100065f6314f100065c6314f1000c7e75d8b100047d75d8b10004be74d8b10004bd74d8b10004de73d8b10004dd73d8b10004be7498b10004bd7498b100047f7558b1000c7c7558b10004df7358b10004dc7358b1000c7e7518b100047d7518b100047f7694b100047d7694b100057a7094b1000c7f7614b100047d7614b1006e5e658cb100065d658cb100665e650cb100065d650cb10006ce620cb10006cd620cb100055c73547100056c725471000578705471005e3e65907100063d65907100563e65107100063d65107100055e739431000579761431001e7976143100057a73143100057a72143100075a32143100075832143100057971143100073a411431000738411431001d7a75cc3100075853cc31001d78750c31001d7a75c831001d787508310007c83208310004be74d9610004bd74d9610004de73d9610004dd73d9610004ee72d9610004ed72d96100055e73d96100056e72d96100063e74d96100063d74d96100047e73d96100065e73d96100045e73d96100065d73d96100047e72d96100066e72d96100046e72d96100066d72d96100067571d96100067a70d961000c7e75992100047d75992100063f65992100063c65992100063e75992100063d75992100047f755921000c7c7559210004df7359210004dc73592100063f65592100063c65592100063f75592100063c75592100069f73592100069c7359210006b7715921000c7e75d8e100047d75d8e10004be74d8e10004bd74d8e10004ee72d8e10004ed72d8e1000c7e7598e100047d7598e100047f7558e1000c7c7558e10
  | 4 => 0x4520005787054520004be7690520004bc76905200063f659052005e3c65905200069f63905200069c6390520006b76190520006b46190520004be7610520004bc76105200063f65105200563c65105200069f63105200069c6310520006b76110520006b461105200047e76941200063f64941200063c64941200055e73941200065f63941200065c63941200067761941200067461941200047e76141200063f64141200063c64141200065f63141200065c6314120006776114120006746114120006b864c8120006f061c8120006ac6488120006cc6388120006e46188120004be74d9420004bd74d9420004de73d9420004dd73d94200055e73d94200063e74d94200063d74d94200047e73d94200065e73d94200045e73d94200065d73d94200047e72d94200066e72d94200047d71d94200047e70d94200067a70d942000c7e75990200047d7599020004bd76990200063f65990200063c65990200063e75990200063d7599020004be71990200047f755902000c7c7559020004df7359020004dc7359020004f77159020004f471590200063f65590200063c6559020005b471590200063f75590200063c75590200069f73590200069c7359020006ac7259020006b77159020004bc7159020006b47159020004b47159020006b87059020004be741902000c7e75d8c200047d75d8c20004be74d8c20004bd74d8c2000c7e7598c200047d7598c200047f7558c2000c7c7558c20004be7418c20004bd7418c200047e7694c200047c7694c200063e6494c200063d6494c200047e7614c2000c7c7614c200063e6414c200063d6414c200065e6314c200065d6314c2000c7e75988200047d75988200063e64948200063d64948200057a70948200063e64148200063d64148200057a7014820006ad64d0820005ce73d0820004ed7610820006ad64cc8200065f658c82006e5c658c8200069e648c8200069d648c820005ce728c8200065f650c8200665c650c8200069e640c8200069d640c8200074e520c8200074c520c820004ed760c820006ad640c8200074e530c8200074c530c820005e9700c820006ce760c820006cd760c8200074f750c8200074c750c8200074f650c8200074c650c820006cf640c8200078e640c820006cd640c8200078d640c8200068d640c820007ca700c820007c9700c82000c7e75984200047d7598420006cc32984200047f755842000c7c7558420004bf7458420004bc7458420004df7358420004dc73584200047e76d44200063e64d44200063d64d44200056e72d44200074c32d44200057a70d44200047c76544200063e64544200063d64544200055c73544200056c72544200074c3254420005787054420004bf7690420004bd76904200063f659042005e3c65904200078c3290420004bf7610420004b
  | 5 => 0x69d63106200078c3210620006b66110620006b5611062003e6e6588620005ce7388620006ce63886200366e6508620006ce6308620007a4410862000c7d76942200055e73942200065e63942200065d63942200056e72942200074c32942200065e63142200065d63142200056e72142200074c321422000c7e76d95200047e73d952000c7e72d952000c7c72d95200047d71d9520004bf7459520004bc7459520004df7359520004dc7359520004f77159520004f471595200047e76195200063f65d91200063c65d9120004be71d912000c7e75991200047d7599120004be7499120004de7399120004dd7399120004f67199120004f571991200047f755912000c7c7559120004df7359120004dc7359120004ef7259120004f77159120004f47159120004fb7059120004be76191200063f65191200063c6519120004be711912000c7e75d8d200047d75d8d200065f65d8d200065c65d8d200069f64d8d200069c64d8d200065e75d8d200065d75d8d2000c7e7598d200047d7598d20004be7498d20004bd7498d20004de7398d20004f67198d20004f57198d200047f7558d2000c7c7558d20004bf7458d20004bc7458d20004ef7258d20004f77158d20004f47158d20004de7618d200065f6518d200065c6518d200069f6418d200069c6418d200065f7518d200065c7518d2006cde7218d20064dc7218d200047e7694d200047c7694d200063f6494d200063c6494d200065f6394d200065c6394d200047e7614d2000c7c7614d200063f6414d200063c6414d200065f6314d200065c6314d200047e76949200063f64949200063c64949200065f63949200065c63949200047e76149200063f64149200063c64149200065f63149200065c6314920004de768c9200065f658c92006e5c658c9200069f648c9200069c648c920004de760c9200065f650c9200665c650c9200069f640c9200069c640c920004be74d8520004bd74d85200067765d85200067465d8520006b764d8520006b464d8520006d763d8520006d463d85200067775d85200067475d8520006b674d8520006b574d85200067653d85200067453d85200067652d85200067452d8520006d632d8520006d432d852000c7e75185200047d7518520006776518520006746518520006b76418520006b46418520006d76318520006d46318520006767518520006757518520006b77418520006b47418520006765318520006745318520006765218520006745218520006d63218520006d432185200047e76d452000c7c76d45200063f64d45200063c64d45200065f63d45200065c63d45200067761d45200067461d45200047e76545200047c76545200063f64545200063c64545200055c73545200065f63545200065c63545200056c725452000677615452000674615
  | 6 => 0xf659043005e3c65904300063f65104300563c6510430004dd768c43004e5c658c4300465c650c43000c7e75980300047d75980300055e73940300047e761403000c7c76140300055e731403002e5c65cc030004df764c0300265c654c0300059c744c030005cc724c030005d4714c030004fb764c030005f0714c030004df7359720004dc73597200055c73597200065f73597200047c73597200065c73597200045c73597200047f715972000c7e75d93200047d75d9320004de73d9320004dd73d9320004f671d9320004f571d932000c7e75193200047d751932000c7e75d8f200047d75d8f20004be74d8f20004bd74d8f20004f671d8f20004f571d8f200047f7558f2000c7c7558f2000c7e7518f200047d7518f200047f7694f200047d7694f2000c7f7614f200047d7614f200065f6314f200065c6314f2000c7d7694b200057a7094b200057a7014b2006e5e658cb200065d658cb200665e650cb200065d650cb2000c7e75987200047d7598720004de7398720004dd7398720004bf7458720004bc745872000c7f76d47200047d76d47200057a70d47200047f76547200047d76547200055c73547200056c725472000578705472005e3e65907200063d65907200563e65107200063d6510720006b66110720006b561107200055e7394320004de73d9620004dd73d96200047c73596200047f715962000c7e75d92200047d75d9220004de73d9220004dd73d9220004f671d9220004f571d922000c7e75192200047d7519220004de7319220004dd731922000c7e75d8e200047d75d8e200065e6598e200065d6598e200065f7598e200065c7598e200047f7558e2000c7c7558e20004bf7458e20004bc7458e200065e6558e200065d6558e200065f7558e200065c7558e200069f7458e200069c7458e20006cf7258e2000c7e7518e200047d7518e200047f7694e200047d7694e200065e6394e200065d6394e2000c7f7614e200047d7614e200065e6314e200065d6314e200065e6394a200065d6394a200065e6314a200065d6314a20005ce73d0a2006e5e658ca200065d658ca200665e650ca200065d650ca200074e520ca200074c520ca20006cd630ca200074e530ca200074c530ca20005cd760ca20006cd760ca200074f750ca200074c750ca200074e650ca200074d650ca20006cf640ca20006cd640ca2000c7e75986200047d7598620006cc3298620004bf7458620004bc745862000c7f76d46200047d76d46200065e63d46200065d63d46200056e72d46200074c32d46200047f76546200047d76546200055c73546200065e63546200065d63546200056c72546200074c325462000578705462005e3e65906200063d65906200069e63906200069d63906200078c32906200563e65106200063d65106200069e6310620
  | 7 => 0xc9300065f658c93006e5c658c9300069f648c9300069c648c930006cc628c9300255c750c9300065f650c9300665c650c9300069f640c9300069c640c930006cf620c930004be74d8530004bd74d85300067765d85300067465d8530006b764d8530006b464d85300075453d8530006e762d8530006e462d85300067775d85300067475d8530006b674d8530006b574d85300067653d85300067453d85300067652d85300067452d8530006d632d8530006d432d853000c7e75185300047d75185300065c5318530006776518530006746518530006b76418530006b46418530007545318530006e76218530006e46218530006767518530006757518530006b77418530006b47418530006d75318530006765318530006745318530006d45318530006545318530006765218530006745218530006d63218530006d432185300047e76d453000c7c76d45300063f64d45300063c64d45300066f62d45300066c62d45300067761d45300067461d45300047e76545300047c76545300063f64545300063c64545300055c73545300056c72545300066f62545300066c6254530006776154530006746154530005787054530004be7690530004bc76905300063f659053005e3c65905300071c5390530006af6290530006ac6290530006b76190530006b46190530004be7610530004bc76105300063f65105300563c65105300071c5310530006af6210530006ac6210530006b76110530006b46110530004de76cc5300255c75cc5300069c64cc530006cc62cc530006d461cc5300255c754c5300069c644c530005cc724c530006cc624c530006d4614c530005d8704c5300047e76941300063f64941300063c64941300055e73941300066f62941300066c62941300067761941300067461941300047e76141300063f64141300063c64141300066f62141300066c62141300067761141300067461141300075853cc130006f061cc1300255e758c1300069c648c130006cc628c130006d4618c13002cde73d94300047e73d94300065e73d94300045e73d94300047e72d94300047d71d94300047e70d94300067a70d943000c7e75990300047d75990300047f755903000c7c755903000c7e7598c300047d7598c300057a7094c3002e5e6314c300057a7014c3007e5c65d0c30005ce72d0c30004dd7610c300765c6510c3000c7e75988300047d75988300047f755883000c7c75588300047e76948300047e76148300065f658c83006e5c658c8300059e748c8300065f650c8300665c650c830006ce620c83000c7e75984300047d75984300047f755843000c7c7558430004bf7458430004bc7458430004ef7258430004ec72584300047e76d44300055e73d44300057a70d44300047c76544300055c73544300056c72544300057870544300063
  | 8 => 0x2d5c750cb300665e650cb300065d650cb30006ce620cb30006cd620cb3000c7e75987300047d75987300065c5398730004bf7458730004bc745873000c7f76d47300047d76d47300057a70d47300047f76547300047d76547300055c73547300056c725473000578705473005e3e65907300063d65907300071c53907300563e65107300063d65107300071c5310730006b66110730006b5611073002d5c75cc73002d5c754c730005cc724c730005d8704c7300055e73943300047c72596300047f715963000c7e75d92300047d75d923000c7e75192300047d7519230004ee7219230004ed721923007e5e65d0e30005ce72d0e300765e6510e300047f7558a3000c7c7558a300047f7694a300047d7694a3000c7f7614a300047d7614a3006e5e658ca300065d658ca300059e748ca30006ce628ca300665e650ca300065d650ca3000c7e75986300047d7598630004bf7458630004bc745863000c7f76d46300047d76d46300055e73d46300047f76546300047d76546300055c73546300056c725463000578705463005e3e65906300063d65906300563e65106300063d651063004e5e658c6300465e650c63000c7d76942300055e73942300055e731423002e5e65cc230024dd73d95300265f53d953000c7e76d953000c7e73d95300265e73d95300065d73d953000c7c73d95300047e72d95300047d71d9530004bf7459530004bc7459530004ef7259530004ec7259530004f77159530004f471595300047e76195300063f65d91300063c65d9130004be71d913000c7e75991300047d7599130004be7499130004ee7299130004ed7299130004f67199130004f571991300047f755913000c7c7559130004df7359130004ef7259130004ec7259130004f77159130004f47159130004be76191300063f65191300063c65191300069f53191300069c5319130004be71191300047e7694d300063f6494d300063c6494d300255e7394d300047e7614d300063f6414d300063c6414d300055e7614d300265e7614d300071f6414d300065e6414d300065c6414d300071c6414d300061c6414d300055e7214d300055d7114d300055e7014d3000c7e75d89300047d75d89300066f65d89300066c65d8930006af64d8930006ac64d89300074c53d89300066e75d89300066d75d89300066e53d89300066c53d89300065c53189300066f65189300066c6518930006af6418930006ac64189300074c53189300066f75189300066c7518930006cf7318930006cf53189300066e53189300066c5318930006cc53189300064c53189300047e76949300047c76949300063f64949300063c64949300055e73949300066f62949300066c62949300047e761493000c7c76149300063f64149300063c64149300066f62149300066c62149300255e758
  | 9 => 0xc768c9400065f658c94006e5c658c940006cf628c940006cc628c940004de760c940004dc760c9400065f650c9400665c650c940006cf620c940006cc620c9400078d420c9400067765d85400067465d8540006d763d8540006d463d8540006e762d8540006e462d85400067775d85400067475d85400067653d85400067453d85400067652d85400067452d8540006d632d8540006d432d854000c7e75185400047d7518540006776518540006746518540006d76318540006d46318540006e76218540006e46218540006767518540006757518540006b77418540006765318540006745318540006765218540006745218540006b74218540006b54218540006d63218540006d432185400047e76d454000c7c76d45400065f63d45400065c63d45400066f62d45400066c62d45400067761d45400067461d45400047e76545400047c76545400055c73545400065f63545400065c63545400056c72545400066f62545400066c62545400067761545400067461545400057870545400063f659054005e3c65905400069f63905400069c6390540006af6290540006ac6290540006b461905400063f65105400563c65105400069f63105400069c6310540006af6210540006ac6210540006b761105400047e76941400055e73941400065f63941400065c63941400066f62941400066c62941400067761941400067461941400047e76141400065f63141400065c63141400066f62141400066c6214140006776114140006746114140006e862d01400069c6390140006ac6290140006b46190140004de73d9440004dd73d9440004ee72d9440004ed72d944000c7e75990400047d75990400047f7558c4000c7c7558c400065e6314c400065d6314c400071c5310c400047f755884000c7c7558840004df7358840004dc7358840004f77158840004f471588400066e62148400066d6214840004bd7690840006ce620c840006cd620c8400078e420c84000c7e75984400047d75984400055c73544400056c72544400057870544400059e7390440006b661104400055e7394040004bf76500400059c7350040005ac7250040005b47150040004fb7650040005e8725004002e5f73597300065c73597300047c72597300047f715973000c7e75d93300047d75d9330004ee72d9330004ed72d9330004f671d9330004f571d933000c7e75193300047d751933000c7d7694f300057a7094f300057a7014f3002e5e7614f3002e5d7614f300065e6414f300065c6414f300055e7214f300055d7114f300055e7014f3002f5a7014f3002f597014f30004be7498b30004bd7498b300065c5398b300047f7558b3000c7c7558b300047f7694b300047d7694b300055e7394b3000c7f7614b300047d7614b3002d5e758cb3006e5e658cb300065d658cb30
  | 10 => 0x84500047d76884500055e73884500055d73884500074c32884500047f764845000c7c76484500053f74484500053c74484500055f73484500055c73484500057b704845000578704845000c7e76084500047d76084500074c32084500073441084500065e73980500065d73980500065e32980500065c32980500063e41980500063c419805000e7a7098050004df7359740004dc73597400055c73597400065f73597400047c73597400065c73597400045c73597400047c72597400047f71597400047f7558f4000c7c7558f400047f7694f400047d7694f4000c7f7614f400047d7614f400047f7558b4000c7c7558b40004df7358b40004dc7358b400047f7694b400047d7694b4000c7f7614b400047d7614b40005b47150b40005b87050b4006e5e658cb400065d658cb400665e650cb400065d650cb40006ce620cb40006cd620cb400078d420cb4000c7e75987400047d7598740004de7398740004dd739874000c7f76d47400047d76d47400047f76547400047d76547400055c73547400056c725474000578705474005e3e65907400063d65907400563e65107400063d6510740006b66110740006b561107400055e7394340004de73d9640004dd73d96400047f7558e4000c7c7558e40004ef7258e40004ec7258e400065e6314e400065d6314e400071c5310e400047f7558a4000c7c7558a40004df7358a40004dc7358a400078e420ca4000c7e75986400047d75986400055c73546400056c72546400057870546400059e7390640006b661906400055e739424000c7e76d95400047e73d95400047e72d95400047d71d9540004df7359540004dc7359540004ef7259540004ec7259540004f77159540004f471595400047e761954000c7e75d8d400047d75d8d400065f65d8d400065c65d8d400065e75d8d400065d75d8d40004de72d8d400065f6518d400065c6518d400065f7518d400065c7518d40004de7218d400047e7694d400047c7694d400065f6394d400065c6394d400047e7614d4000c7c7614d400065f6314d400065c6314d4000c7e75d89400047d75d8940004de73d8940004dd73d89400066f65d89400066c65d8940006cf63d8940006cc63d89400066e75d89400066d75d8940006ce73d8940006cd73d89400066e53d89400066c53d89400066f65189400066c6518940006cf6318940006cc63189400066f75189400066c7518940006cf7318940006cc73189400066e53189400066c53189400047e76949400047c76949400065f63949400065c63949400066f62949400066c62949400047e761494000c7c76149400065f63149400065c63149400066f62149400066c6214940004be76d09400069c63d0940006ac62d09400069c6350940006ac6250940005b47150940005b87050940004de768c940004d
  | 11 => 0x56c724c6500057b704c65000578704c6500047e760c6500047d760c6500065e630c6500047f76c86500053e74c86500053d74c86500065e63c86500073441c86500047e76886500047d76886500055e73886500055d73886500065e63886500066e62886500074c32886500047f76486500047c76486500053f74486500053c74486500055f73486500055c73486500065e63486500057b70486500057870486500047e76086500047d76086500065e63086500066e62086500074c32086500073441086500065f6394d500065c6394d50004de73d8950004dd73d89500066f62949500066c6294950006cf620c950006cc620c950004be74d8550004bd74d85500055c73545500056c7254550006776154550005787054550006b76110550006b461105500055e739415000e5e7398c500047e7298c500047d7198c5000c7e76d0c500047d76d0c500056e72d0c500056d72d0c500047f7650c5000c7c7650c500047e739885000e6e72988500047d719885000c7e76d08500047d76d08500055e73d08500055d73d08500047f765085000c7c76508500055f73508500055c73508500057771508500057471508500057b705085000578705085000c7e76cc8500047d76cc85000c7e768c8500047d768c8500053e748c8500053d748c8500065e638c85006e5e768c8500065d768c8500071e748c8500071d748c8500655e728c8500065e628c85006f5a608c8500047f764c85000c7c764c8500047f760c8500065e630c8500065f760c8500665c760c85006d5e720c8500074e720c8500065e620c8500074e420c8500074d420c8500675a600c8500063f74584500063c74584500065f73584500047c73584500065c73584500045c73584500066f72584500047c72584500066c72584500046c72584500065e32584500065c325845000e7771584500067870584500057a70d04500057970d045000c7e76904500047d76904500055e73904500055d739045005e3e76904500063d76904500071e73904500071d73904500063e63904500063e62904500071e32904500071c32904500553e71904500063d619045005f3a60904500057b705045000578705045000c7e76104500047d76104500563e76104500063d76104500063e63104500063e62104500071e32104500071c321045005d3e71104500073671104500063d61104500573a60104500047f76cc4500053e74cc4500053d74cc4500065e63cc4500057a70cc4500057970cc45000c7e768c4500047d768c4500047f764c45000c7c764c4500053f744c4500053c744c4500065e634c4500056f724c4500056c724c4500057b704c45000578704c45000c7e760c4500047d760c4500047f76c84500053e74c84500053d74c84500073441c84500057a70c84500057970c845000c7e768
  | 12 => 0xe6098e5002f5a6098e500065f7498e500065e7498e500065d7498e500065c7498e500065f7298e500065e7298e500045e7298e500065d7298e500065c7298e500065f7198e500065e7198e500065d7198e500065c7198e500065e7098e5002e5c7098e500065f7658e500055c7258e500265e6058e500275a6058e500057a7018e500047e76d0e500047d76d0e500065e63d0e500056e72d0e500056d72d0e500065e6390e500047f7650e500047c7650e500065e6350e500065e6310e500055e73d8a500055d73d8a500065e63d8a500057a70d8a500065e6398a500065d6398a500065f7398a500047e7398a500065c7398a500047d7198a500055f7358a500055c7358a500065e6358a500053e7418a500053d7418a500055e7318a500055d7318a500065e6318a500065d6318a500057a7018a500047e76d0a500047d76d0a500055e73d0a500055d73d0a500065e63d0a500065e6390a500066e6290a500047f7650a500047c7650a500055f7350a500055c7350a500065e6350a500066e6250a50005777150a50005747150a500057b7050a50005787050a500065e6310a500047e76cca500047d76cca500065e63cca500047e768ca500047d768ca500053e748ca500053d748ca500065e638ca500055f768ca500065e768ca500055d768ca500065d768ca500045d768ca500071e748ca500071d748ca500065e628ca500047f764ca500047c764ca500065e634ca500047f760ca500065e630ca500055f760ca500065f760ca500045f760ca500055d760ca500065c760ca500074e720ca500065e620ca500074e420ca500074d420ca500053e74d86500053d74d86500055e73d86500055d73d86500065e63d86500065d63d86500056e72d86500056d72d86500057a70d86500065e639865001e7a60986500053f74586500053c74586500065e63586500065d63586500063f74586500063c74586500047c73586500047c72586500065e32586500065c32586500055e73186500055d73186500065e63186500057a70186500065e63d06500047e76906500047d76906500055e73906500055d73906500065e63906500063e76906500063d76906500071e73906500071d73906500063e63906500071e63906500061e63906500071d63906500063e62906500071e32906500071c32906500063d61906500065e63506500047e76106500047d76106500065e63106500063e76106500063d76106500063e63106500071e63106500061e63106500071d63106500063e62106500071e32106500071c32106500073671106500063d61106500047f76cc6500053e74cc6500053d74cc6500065e63cc6500047e768c6500047d768c6500065e638c6500047f764c6500047c764c6500053f744c6500053c744c6500065e634c6500056f724c650
  | 13 => 0x48210356e729482100575719482100c7f76148210047d76148210057571148210366e76148210366d76148210046d76148210056e73148210376671148210056d71148210376571148210056e70148210356e75cc82106e5e658c8210065d658c821005ce728c8210074c528c8210665e650c8210065d650c8210074e520c8210074c520c821004ed760c8210356c750c8210074e530c8210074c530c821006ce760c821006cd760c8210074f750c8210074c750c8210074e650c8210074d650c821006cf640c821006cd640c821007c6710c821007c5710c82100c7e75984210047d7598421004de7398421004dd739842103e6c5298421006cc32984210047d76d44210074c32d44210047f76544210055c73544210056c72544210074c32544210057870544210076452d0421007c432d042105e3e65904210063d65904210072c52904210078c3290421005b671904210563e65104210063d65104210072c52104210078c3210421007375110421007355110421004f57610421007645210421007c43210421006b67610421006b57610421007367510421007357510421007366510421007356510421007365310421007345310421007a67210421007a57210421006b6621042108fa7521042100736521042100734521042108fa45210421007245210421007a73210421007963210421007943210421007a432104210078432104210356c75c8421007a441c8421007645288421007c43288421004ef76484210356c7548421005cc7348421005e87048421004f77648421005b47448421005f07048421006cc3298021006b441980210047f755802100c7c7558021004bf7458021004bc7458021004df7358021004dc73580210055f73552500055c73552500065f7598e5002e5e7598e5002e5f5498e500065e5498e500065d5498e5002e5c5498e50004de7298e5002e5f5298e5002e5c5298e5002e5f5198e5002e5c5198e5002e5f5098e500265c7558e50004dc7258e500265c5258e500265f5158e500065e6394e500065e6354e50004df7358a50004dc7358a500065e6394a500065d6394a500066e6294a500055f7354a500055c7354a500065e6354a50004df768ca50004dd768ca50004df760ca50004dd760ca50004bf7458650004bc74586500065e63946500053f74546500053c74546500055f73546500055c73546500065e63546500065d63546500056f72546500056c72546500067561546500069e63906500069d63906500069e63106500069d63106500055e73d92500055d73d92500057a70d92500055e73192500055d73192500056e72192500056d72192500057a70192500057a70d8e500065f6398e500047e7298e500047d7198e500065f6498e500065e6498e500065d6498e500065c6498e500055e7298e5002e5
  | 14 => 0x4fb7059121004f87059121004be76191210063f65191210063c651912100c7e75d8d210047d75d8d210065f65d8d210065c65d8d210069f64d8d210069c64d8d210065e75d8d210065d75d8d2100c7e7598d210047d7598d21004be7498d21004bd7498d21004de7398d21004fa7098d21004f97098d210047f7558d2100c7c7558d21004bf7458d21004bc7458d21004ef7258d21004fb7058d21004f87058d21004de7618d210065f6518d210065c6518d210069f6418d210069c6418d210065f7518d210065c7518d210047e7694d210047c7694d210063f6494d210063c6494d210065f6394d210065c6394d210047e7614d2100c7c7614d210063f6414d210063c6414d210065f6314d210065c6314d210047e76949210063f64949210063c64949210065f63949210065c63949210047e76149210063f64149210063c64149210065f63149210065c6314921004de768c9210065f658c92106e5c658c9210069f648c9210069c648c921004de760c9210065f650c9210665c650c9210069f640c9210069c640c9210047e76d45210063f64d45210063c64d45210065f63d45210065c63d45210056e72d452100c7c76545210063f64545210063c64545210055c73545210065f63545210065c63545210056c7254521005787054521004be76905210063f659052105e3c65905210069f63905210069c6390521004be76105210063f65105210563c65105210069f63105210069c6310521006b464c852103e6c6588521006cc638852100c7e75d81210047d75d81210067b65d81210067865d8121006bb64d8121006b864d8121006db63d8121006d863d81210067a75d81210067975d81210067a53d81210067853d81210067a52d81210067852d8121006da32d8121006d832d81210067b51d81210067951d8121006ba41d8121006b841d81210067b6518121006786518121006bb6418121006b86418121006db6318121006d863181210067b75181210067875181210067a53181210067853181210067a5218121006785218121006da3218121006d832181210067b5118121006795118121006ba4118121006b84118121006f32118121006ea21181210047d7699421004df7359421004dc7359421034ec725942100c7f76594210055c73594210065f73594210047c73594210065c73594210045c73594210366f72594210066c72594210047c705942100c7e75d90210047d75d9021004de73d9021004dd73d902100c7e75190210047d751902100c7e75d8c210047d75d8c21004be74d8c21004bd74d8c210047f7558c2100c7c7558c2100c7e7518c210047d7518c210047f7694c210047d7694c210056e7294c2100c7f7614c210047d7614c210065f6314c210065c6314c21004be7498821004bd74988210047f769482100c7d769
  | 15 => 0xd6414b21005757114b210065f658cb2106e5c658cb210069e648cb210069d648cb210065f650cb210665c650cb210069e640cb210069d640cb210063e64d47210063d64d47210056e72d47210063e64547210063d64547210055c73547210056c72547210057870547210063f659072105e3c65907210063f65107210563c6510721007375110721007355110721006b56410721005b57610721006b5761072100736751072100735751072100737651072100734651072100736531072100734531072100736521072100734521072100796321072100794321072100c7e75983210047d7598321004de7398321004dd7398321006b441983210047f755832100c7c7558321004de73d9621004dd73d96210047c73596210066f725962103e6c72596210047c705962100c7e75d92210047d75d9221004de73d9221004dd73d9221004fa70d9221004f970d922100c7e75192210047d7519221004de7319221004dd731922100c7e75d8e210047d75d8e210065e6598e210065d6598e210065f7598e210065c7598e210047f7558e2100c7c7558e21004bf7458e21004bc7458e210065e6558e210065d6558e210065f7558e210065c7558e210069f7458e210069c7458e21006cf7258e2100c7e7518e210047d7518e210047f7694e210047d7694e210065e6394e210065d6394e210056e7294e2100c7f7614e210047d7614e210065e6314e210065d6314e210065e6394a210065d6394a210065e6314a210065d6314a210056d7614a2103e6d7614a210056e7314a210074e6314a210074d6314a210056d7114a210056e7014a2103d6e75cca2106e5e658ca210065d658ca210074c528ca210665e650ca210065d650ca210074e520ca210074c520ca2103d6c750ca21006cd630ca210074e530ca210074c530ca21005cd760ca21006cd760ca210074f750ca210074c750ca210074e650ca210074d650ca21006cf640ca21006cd640ca210065e63d46210065d63d46210074c32d46210055c73546210065e63546210065d63546210056c72546210074c325462100578705462105e3e65906210063d65906210069e63906210069d63906210072c52906210078c32906210563e65106210063d65106210069e63106210069d63106210072c52106210078c321062103d6c75c8621004be7498221004bd7498221006cc32982210047f755822100c7c755822100c7e76d95210047e73d95210047e70d9521004bf7459521004bc7459521004df7359521004dc735952103cef7259521004fb7059521004f870595210047e76195210063f65d91210063c65d912100c7e75991210047d7599121004be7499121004de7399121004dd7399121004fa7099121004f970991210047f755912100c7c7559121004df7359121004dc7359121004f77159121
  | 16 => 0x8131006d832d81310067b51d81310067951d8131006ba41d8131006b841d81310067b6518131006786518131006bb6418131006b86418131006eb6218131006e862181310067b75181310067875181310067a5318131006785318131006db4318131006d843181310067a5218131006785218131006da3218131006d832181310067b5118131006795118131006ba4118131006b84118131006f33118131006da31181310047d7699431044dc735943100c7f76594310465f73594310065c73594310047c72594310047c705943100c7e75d90310047d75d9031004de73d903100c7e75190310047d7519031004be7498c31004bd7498c310047f7694c3100c7d7694c310455e7394c31005757194c3100c7f7614c310047d7614c31005757114c310465e7614c310465d7614c310045d7614c310065e6414c310065c6414c310055e7214c31047567114c310055d7114c31047557114c31005557114c310055e7014c31004be7498831004bd74988310065c53988310047f755883100c7c75588310047f76948310047d76948310055e739483100c7f76148310047d76148310455e758c83106e5e658c8310065d658c8310455c750c8310665e650c8310065d650c831006ce620c83100c7e75984310047d759843104e5c53984310047d76d44310047f76544310055c73544310056c725443100578705443105e3e65904310063d65904310071c53904310563e65104310063d65104310071c53104310455c75cc43100754538c431004df764c4310455c754c431005cc724c43100755514c431005d8704c431004f7764c43100756534c431005f0704c4310047f755803100c7c7558031004bf7458031004bc74580310065c5358031004ef7258031004ec7258031004be74d9721004bd74d9721004de73d9721004dd73d9721004fa70d9721004f970d97210055e73d97210057a70d97210063e74d97210063d74d97210047e73d97210065e73d97210045e73d97210065d73d97210066e72d97210067571d97210047e70d97210067a70d97210047a70d97210067970d972100c7e75993210047d75993210063f65993210063c65993210063e75993210063d75993210047f755932100c7c7559321004df7359321004dc73593210063f65593210063c65593210063f75593210063c75593210069f73593210069c7359321006b7715932100c7e75d8f210047d75d8f21004be74d8f21004bd74d8f21004fa70d8f21004f970d8f2100c7e7598f210047d7598f210047f7558f2100c7c7558f21004be7418f21004bd7418f210047e7694f210047c7694f210063e6494f210063d6494f210047e7614f2100c7c7614f210063e6414f210063d6414f210065e6314f210065d6314f210063e6494b210063d6494b21005757194b210063e6414b210063
  | 17 => 0x47c705963100c7e75d92310047d75d923100c7e75192310047d7519231004ee7219231004ed72192310055d7614e3104e5d7614e310065e6414e310065c6414e310055e7214e310055d7114e310055e7014e310065c5398a310047f7558a3100c7c7558a310047f7694a310047d7694a310055e7394a3100c7f7614a310047d7614a3104d5e758ca3106e5e658ca310065d658ca31006ce628ca3104d5c750ca310665e650ca310065d650ca310055c73546310056c725463100578705463105e3e65906310063d65906310071c53906310563e65106310063d65106310071c531063100735511063104d5c75cc6310047f755823100c7c75582310065c535823100c7e76d95310047e72d95310047e70d9531004bf7459531004bc745953104cdf7359531004ef7259531004ec7259531004fb7059531004f870595310047e76195310063f65d91310063c65d91310069d73d913100c7e75991310047d7599131004be7499131004ee7299131004ed7299131004fa7099131004f970991310047f755913100c7c7559131004ef7259131004ec7259131004fb7059131004f87059131004be76191310063f65191310063c65191310047e7694d310063f6494d310063c6494d310047e7614d310063f6414d310063c6414d31004de76d0d3107e5c65d0d310069f64d0d31005ce72d0d310765c6510d310069f6410d3100c7e75d89310047d75d89310066f65d89310066c65d8931006af64d8931006ac64d89310066e75d89310066d75d89310066e53d89310066c53d89310066f65189310066c6518931006af6418931006ac64189310066f75189310066c7518931006cf73189310066e53189310066c5318931006cf4318931006cc43189310047e76949310047c76949310063f64949310063c64949310066f62949310066c62949310047e761493100c7c76149310063f64149310063c64149310066f62149310066c62149310065f658c93106e5c658c9310059e748c9310069f648c9310069c648c931006cc628c9310065f650c9310665c650c9310069f640c9310069c640c931006cf620c9310047e76d45310063f64d45310063c64d45310055e73d45310066f62d45310066c62d453100c7c76545310063f64545310063c64545310055c73545310056c72545310066f62545310066c6254531005787054531004be76905310063f659053105e3c6590531006af6290531006ac6290531004be76105310063f65105310563c6510531006af6210531006ac621053100735511053104e5c658c531006cc628c53100c7e75d81310047d75d81310067b65d81310067865d8131006bb64d8131006b864d8131006eb62d8131006e862d81310067a75d81310067975d81310067a53d81310067853d81310067a52d81310067852d8131006da32d
  | 18 => 0xc520c8410553e75984410053d759844105e3e65984410063d65984410059e73984410059d739844105e3e75984410063d75984410069e73984410069d73984410063e539844105e3c53984410063e529844105e3c52984410069e32984410069c3298441006b67198441007367598441007357598441007366598441007356598441007967398441007957398441007365398441007345398441005b67298441007365298441007345298441007963298441007943298441005b670984410053d76d44410563d76d44410043d76d44410053e73d44410053e72d44410071e32d44410071c32d444105e3e61d44410073661d44410053e70d44410053d759444105cbf76544410059f73544410059c7354441005af7254441005ac7254441005bb7054441005b870544410053f76544410063f76544410043f76544410071f73544410053c73544410071c73544410051c73544410072f72544410053c72544410072c72544410052c72544410071e32544410071c32544410553f71544410573771544410063e61544410073661544410073b70544410053c70544410073870544410053870544410553e75d80410053d75d80410053f75580410553c75580410059f73580410059c7358041005af7258041005ac72580410553e75180410053d75180410059e73180410059d7318041005ae7218041005ad7218041004be74d9731004bd74d9731004ee72d9731004ed72d9731004fa70d9731004f970d97310056e72d97310057a70d97310063e74d97310063d74d97310065e73d97310047e72d97310066e72d97310046e72d97310066d72d97310067571d97310047e70d97310067a70d97310047a70d97310067970d973100c7e75993310047d75993310063f65993310063c65993310063e75993310063d75993310047f755933100c7c75593310063f65593310063c65593310063f75593310063c75593310069c73593310063e6494f310063d6494f31005757194f310063e6414f310063d6414f31005757114f3107e5c65d0f310069d64d0f31005ce72d0f310765c6510f3100c7e7598b310047d7598b310047f7558b3100c7c7558b310047e7694b310063e6494b310063d6494b310047e7614b310063e6414b310063d6414b310066e6214b310066d6214b310065f658cb3106e5c658cb310059e748cb310069e648cb310069d648cb310065f650cb310665c650cb310069e640cb310069d640cb31006ce620cb31006cd620cb310063e64d47310063d64d47310055e73d47310063e64547310063d64547310055c73547310056c72547310057870547310063f659073105e3c65907310063f65107310563c651073100c7e75983310047d75983310047f755833100c7c755833104e5f53596310065f735963104e5c73596310047c7259631
  | 19 => 0x8c410047f7694c410047d7694c4100c7f7614c410047d7614c41005757114c410553e75d0c410053d75d0c410071c53d0c41005ae72d0c41005ad72d0c410053f7550c410553c7550c410071c5310c410047f755884100c7c7558841004df7358841004dc7358841004fb7058841004f870588410047f76948410047d769484100c7f76148410047d76148410553e75d08410053d75d08410059e73d08410059d73d0841005b571d08410053f75508410553c75508410059f73508410059c7350841005b77150841005bb7050841005b87050841006ad621084106e5e658c8410065d658c8410665e650c8410065d650c841006ce620c841006cd620c8410078e420c8410078d420c84100c7e75984410047d75984410047d76d44410047f76544410055c73544410056c7254441005787054441004bf7650441004f776504410047f755804100c7c7558041004df7358041004dc7358041004ef7258041004ec7258041005b671d94410053d76994410053e73994410053e72994410053e70994410059f73594410059c73594410553f76594410563f76594410071f73594410053c73594410071c73594410051c73594410053c72594410053c70594410553e75d8c410053d75d8c41005ae72d8c41005ad72d8c41005b671d8c410053f7558c410553c7558c410553e7518c410053d7518c41005b67118c410053f7694c410053d7694c410553e7394c410053e7294c410053d7194c410053e7094c410553f7614c410053d7614c410053e7314c410571e7314c410071f6314c410071c6314c410053e7214c41057367114c410053d7114c41057357114c41005357114c410053e7014c410553e75d88410053d75d88410059e73d88410059d73d8841005b671d88410053f75588410553c75588410059f73588410059c7358841005bb7058841005b870588410553e75188410053d7518841006ad6218841005b671188410053f76948410053d76948410053e73948410553e72948410053d71948410053e70948410059f73548410059c7354841005b77154841005b471548410553f76148410053d76148410053e73148410053e72148410572e72148410053d71148410053e70148410553e75cc8410053d75cc841005b671cc841005b571cc841004be768c841004bd768c8410553e758c8410053d758c8410071e538c8410071c538c8410069e768c8410069d768c8410071e758c8410071d758c8410071e658c8410071d658c8410059e728c8410071e528c8410071c528c8410053f754c8410553c754c841005b7714c841005b4714c8410053f750c8410553c750c8410071e530c8410071c530c8410071f750c8410071c750c8410071e650c8410071d650c8410059e720c8410078e720c8410078e620c8410078d620c8410071e520c8410071
  | 20 => 0x5f1e7314e410071e6314e410071d6314e410053e7214e410053d7114e410053e7014e4105d3e75d8a410053d75d8a410059e73d8a410059d73d8a410069e63d8a41005b671d8a41005ba70d8a41005b970d8a41006af6298a410053f7558a4105d3c7558a410059f7358a410059c7358a410069e6358a4105d3e7518a410053d7518a410059e7318a410059d7318a41005b67118a410053f7694a410053d7694a410053e7394a410071e6394a410071d6394a410053d7194a410053e7094a410059f7354a410059c7354a4105d3f7614a410053d7614a410053e7314a410071e6314a410071d6314a4105f2e7214a410053d7114a410053e7014a4105d3e75cca410053d75cca41004be768ca41004bd768ca4105d3e758ca410053d758ca410071e538ca410071c538ca410059f768ca410069e768ca410059d768ca410069d768ca410049d768ca410071e758ca410071d758ca410071e658ca410071d658ca410071e528ca410071c528ca410053f754ca4105d3c754ca410053f750ca4105d3c750ca410071e530ca410071c530ca410059f760ca410059d760ca410071f750ca410071c750ca410071e650ca410071d650ca410078e720ca410078f620ca410078c620ca410071e520ca410071c520ca410053d76d464105e3d76d46410053e73d46410071e63d46410071d63d46410053e72d46410071e32d46410071c32d46410053e70d4641054bf76546410059f73546410059c7354641005af7254641005ac7254641005bb7054641005b870546410053f76546410063f76546410071f73546410053c73546410071c73546410051c73546410071e63546410071d63546410072f72546410053c72546410072c72546410052c72546410071e32546410071c325464105f3771546410073b70546410053c705464100738705464100538705464105d3e75d82410053d75d82410059e73d82410059d73d8241005ae72d8241005ad72d82410069e63982410053f755824105d3c755824105d3e75182410053d75182410059e73182410059d73182410069e631824105cbf7459541004df7359541004dc7359541004ef7259541004ec7259541004fb7059541004f8705954100c7e75d8d410047d75d8d410065f6314d410065c6314d4100c7e75d89410047d75d8941004de73d8941004dd73d89410066f62149410066c6214941006cf620c941006cc620c9410055c73545410056c725454100578705454100c7e75d81410047d75d81410047d7699441054bc7459441004df7359441004dc735944100c7f76594410055c73594410563f74594410063c74594410065f73594410047c73594410065c73594410045c73594410047c72594410047c705944100cbd769504100e3e65550410059f73550410059c73550410047f7558c4100c7c755
  | 21 => 0x972181510067872181510067b42181510067a42181510067942181510067842181510067b32181510067a32181510065a32181510067932181510067832181510065832181510167b7118151004de73d9741004dd73d9741004ee72d9741004ed72d9741004fa70d9741004f970d97410047f7558f4100c7c7558f410065e6314f410065d6314f41005757114f410047f7558b4100c7c7558b41004df7358b41004dc7358b410066e6214b410066d6214b41006ce620cb41006cd620cb410055c73547410056c72547410057870547410047f755834100c7c7558341004de73d9641004dd73d96410063f745964105e3c74596410047c73596410047c72596410047c705964100e3e659524100cbf76552410059f73552410059c73552410065e6598e410065d6598e410065f7598e410065c7598e41004de7298e410047f7558e4100c7c7558e41004ef7258e41004ec7258e410065e6558e410065d6558e41005cc7258e410065f7558e410065c7558e41006cf7258e41004dc7258e41006cc7258e41004cc7258e410047f7694e410047d7694e410065e6394e410065d6394e4100c7f7614e410047d7614e410065e6314e410065d6314e4105d3e75d0e410053d75d0e410069e63d0e410071c53d0e41005ae72d0e41005ad72d0e410053f7550e4105d3c7550e410069d6310e410071c5310e410047f7558a4100c7c7558a41004df7358a41004dc7358a410047f7694a410047d7694a410065e6394a410065d6394a4100c7f7614a410047d7614a410065e6314a410065d6314a4105d3e75d0a410053d75d0a410059e73d0a410059d73d0a410069e63d0a410053f7550a4105d3c7550a410059f7350a410059c7350a410069e6350a41006ae6250a41005bb7050a41005b87050a41004df768ca41004dd768ca4106e5e658ca410065d658ca41004df760ca41004dd760ca410665e650ca410065d650ca410078e420ca410078d420ca410065e63d46410065d63d46410055c73546410065e63546410065d63546410056c72546410057870546410047f755824100c7c75582410059e73d96410059d73d9641005b671d96410053e73996410053e72996410053e709964105e3f76596410053c73596410053c72596410053c705964105d3e75d8e410053d75d8e41005b671d8e410071f7598e410071c7598e410071e6598e410071d6598e410059e7298e410053f7558e4105d3c7558e41005af7258e41005ac7258e410069f7658e410071f7558e410071c7558e410071e6558e410071d6558e410078f7258e410059c7258e410078c7258e410058c7258e4105d3e7518e410053d7518e41005b67118e410053f7694e410053d7694e410071e6394e410071d6394e410053e7294e410053d7194e410053e7094e4105d3f7614e410053d7614e41
  | 22 => 0x89510366f71189510066d71189510066f70189510066e70189510066d70189510066c70189510047e76d09510047d76d09510055e73d09510055d73d09510065c63d09510066c62d09510065c63909510066c62909510047f76509510047c76509510055f73509510055c73509510065c63509510066c62509510057771509510057471509510057b70509510057870509510065c63109510066c62109510047e76cc9510047d76cc9510065c63cc9510066c62cc9510047e768c9510047d768c9510053e748c9510053d748c9510065c638c9510066c628c9510055e768c9510065e768c9510045e768c9510065d768c9510055c768c9510071e748c9510071d748c9510071f648c9510071c648c9510055e728c9510074f628c9510065c628c9510074c628c9510064c628c95106e5f618c95106f57618c9510047f764c9510047c764c9510065c634c9510066c624c9510047c760c9510065c630c9510066c620c9510065f760c9510055e760c9510055c760c9510065c760c9510045c760c9510071f640c9510071c640c9510055e720c9510074e720c9510074f620c9510065c620c9510074c620c9510064c620c9510074e420c9510074d420c9510665f610c95106757610c9510065c63d81510066c62d81510073b64d81510073864d81510075b63d81510067a63d81510067863d81510075863d81510065863d81510076b62d81510067a62d81510067862d81510076862d81510066862d81510075a32d81510075832d815101e7b61d815101f7361d81510053e74981510053d74981510063f64981510063c64981510055e73981510055d73981510065f63981510065c63981510056e72981510056d72981510066f62981510066c62981510057a70981510053f74581510053c74581510055f73581510055c73581510065c63581510056f72581510056c72581510066c62581510063f64181510063c64181510065f63181510065c63181510066f62181510066c62181510067960181510047e73181510047e72181510065e32181510065c32181510057a76181510067a76181510067b64181510073b64181510063b64181510067a64181510067964181510067864181510073864181510063864181510067b63181510075b63181510065b63181510067a63181510067963181510067863181510075863181510065863181510067b62181510076b62181510066b62181510067a62181510067962181510067862181510076862181510066862181510075a32181510075832181510167b61181510177361181510067b74181510067a74181510067974181510067874181510067b73181510067a73181510067973181510067873181510067b43181510067a43181510067943181510067843181510067b72181510067a72181510067
  | 23 => 0x6d832181510067a511815101678511815105e3f61d915105f3761d91510053e74991510063f64991510055e73991510055d73991510056e72991510056d72991510057571991510057a70991510057970991510055f73591510055c73591510056f72591510056c72591510057771591510057b70591510057870591510053e76191510063e76191510563f61191510573761191510071f64d8d510071c64d8d510055e72d8d5104e5f61d8d5104f5761d8d510053e7498d510053d7498d510063f6498d510063c6498d510055e7398d510056e7298d510056d7298d51005757198d510057a7098d51005797098d510053f7458d510053c7458d510056f7258d510056c7258d51005777158d510057b7058d51005787058d510063f6418d510063c6418d510065d6318d510047e7218d510047e7018d510055e7618d510065e7618d510065f6418d510071f6418d510061f6418d510065e6418d510065d6418d510065c6418d510071c6418d510061c6418d510055e7218d510465f6118d51047576118d510065f7418d510065e7418d510065d7418d510065c7418d510065f7218d510065e7218d510045e7218d510065d7218d510065c7218d510465f7118d510065d7118d510065f7018d510065e7018d510065d7018d510065c7018d510047e76d0d510047d76d0d510065c63d0d510056e72d0d510056d72d0d510065c6390d51005767190d51005757190d510047f7650d510047c7650d510065c6350d510065c6310d510055e73d89510055d73d89510065c63d89510072f64d89510072c64d89510074e73d89510074d73d89510074f63d89510066e63d89510066c63d89510074c63d89510064c63d895103e6f61d895103f6761d89510053e74989510053d74989510063f64989510063c64989510055e73989510055d73989510065f63989510065c63989510056e72989510057571989510057a70989510057970989510053f74589510053c74589510055f73589510055c73589510065c63589510057771589510057b70589510057870589510063f64189510063c64189510065f63189510065c63189510066d62189510065f73189510047e73189510065c73189510047e70189510056e76189510066e76189510066f64189510072f64189510062f64189510066e64189510066d64189510066c64189510072c64189510062c64189510074f73189510074c73189510066f63189510074f63189510064f63189510066e63189510066d63189510066c63189510074c63189510064c63189510366f61189510376761189510066f74189510066e74189510066d74189510066c74189510066f73189510064f73189510066e73189510066d73189510066c73189510064c73189510066f43189510066e43189510066d43189510066c431
  | 24 => 0x47150b510057b7050b51005787050b5100c7e76ccb510047d76ccb510066e62ccb5100c7e768cb510047d768cb510053e748cb510053d748cb510065e638cb5106e5e768cb510065d768cb510071e748cb510071d748cb5106f1e648cb5106f1d648cb510065e628cb510047f764cb5100c7c764cb510047f760cb510065e630cb510066e620cb510065f760cb510665c760cb510671e640cb510671d640cb510074e720cb510065e620cb510674e620cb510064e620cb510674d620cb510074e420cb510074d420cb510047e73983510065e73983510045e73983510065d73983510047e72983510065e32983510065c329835100e7a709835100e7771596510065e6394e510065d6394e51004df7358a51004dc7358a510066e6294a5105e3e75d915105e3c53d915105e3c52d915105e3c50d91510563e75191510563c53191510563c52191510563c50191510063f64951510055f73551510055c73551510069f64d8d510069c64d8d5104e5e75d8d51004de72d8d5104e5c52d8d5104e5c50d8d510069f6418d510069c6418d510065f7518d510465e7518d510465f5418d510065e5418d510065d5418d510465c5418d51004de7218d510465f5218d510465c5218d510465c5118d510465f5018d510465c5018d510063f6494d510063c6494d510065c6394d510065c6354d51004de73d8951004dd73d8951006af64d8951006ac64d8951006cf63d8951006cc63d895103e6e75d8951006ce73d8951006cd73d89510066e53d895103e6c53d895103e6c50d8951006af6418951006ac6418951006cf6318951006cc63189510066f75189510366e75189510366f54189510066e54189510066d54189510366c5418951006cf7318951006cc73189510366f53189510066e53189510066d53189510366c53189510366c51189510366f50189510366c50189510063f64949510063c64949510065f63949510065c63949510066c62949510055f73549510055c73549510065c63549510066c6254951004de768c951004dc768c9510069f648c9510069c648c951006cf628c951006cc628c951004de760c951004dc760c9510069f640c9510069c640c951006cf620c951006cc620c9510065c63945510066c6294551006bb64d8151006b864d8151006db63d8151006d863d8151006eb62d8151006e862d815101e7a75d81510067a53d815101e7853d81510067a52d815101e7852d8151006da32d8151006d832d8151006bb6418151006b86418151006db6318151006d86318151006eb6218151006e862181510067b75181510167a75181510167b54181510067a54181510067954181510167854181510167b53181510067a53181510067953181510167853181510167b52181510067a5218151006795218151016785218151006da3218151
  | 25 => 0xc8320655c754c832004ef764c83200c7e75984320047d75984320065c53984320047f755843200c7c7558432004bf7458432004bc7458432004fb7058432004f8705843200c7e75980320047d75980320047f755803200c7c7558032004bf7458032004bc74580320065c5358032004f77158032004f47158032005ce72d94320055e72d94320074e72d94320054e72d94320055d71d94320055e70d94320665e76194320055e72194320674e72194320054e72194320055d71194320055e7019432005ce72d90320655e75990320055d75990320065c65990320055f75590320655c75590320065c6519032005ce7219032005ce7295032005cd7295032004df7655032004dc76550320655e75988320055d75988320065f659883206e5c65988320059e74988320059d749883206e5e75988320065d75988320069e74988320069d7498832006ce72988320074e75988320074d75988320074f65988320074c65988320078e7498832005cd74988320078d74988320058d7498832005ce7198832005ce70988320655e72948320065e62948320074e62948320055d71948320055e709483206cdf76548320055e76148320655c76148320055e72148320674e721483206e5e62148320074e62148320055d71148320055e7014832004dd76d08320655e75d08320055d75d08320074e52908320074c5290832005cf7690832005cd76908320074f65908320074c6590832005cd74908320078e64908320078d6490832005ce7190832005ce7090832004df76508320055f75508320655c75508320074e52508320074c5250832005d77150832005d47150832005db7050832005d87050832005cf7650832006cf76508320074f75508320074c75508320074f65508320074c65508320078f74508320078f64508320078c6450832007c77150832005cc7150832007c47150832005c47150832007cb7050832005cc7050832007c87050832005c87050832005ce72108320078d42108320059e74d84320059d74d84320655e75984320055d75984320065c65984320055f75584320655c75584320059f74584320059c7458432005db7058432005d870584320655e75184320055d75184320065c65184320655e75d80320055d75d80320065c65d80320655e75980320055d75980320055f75580320655c75580320065c65580320059f74580320059c7458032005d77158032005d471580320059e74180320059d741803200e5e7398f510047e7298f510047e7098f5100c7e76d0f510047d76d0f510056e72d0f510056d72d0f510047f7650f5100c7c7650f510047e7398b5100e6e7298b510047e7098b5100c7e76d0b510047d76d0b510055e73d0b510055d73d0b510047f7650b5100c7c7650b510055f7350b510055c7350b51005777150b510057
  | 26 => 0x6d5e75d92320055d75d9232005ce72d92320065e65992320069e65992320071e65992320061e65992320071d65992320069c65992320059e71992320069f76592320071e65592320071d65592320059c715923206d5e75192320055d75192320065e6519232005ce7219232004df7655232004dc76552320055d7694a320071e6494a320071d6494a320055d7194a320055e7094a32064df7654a320055d7614a320071e6414a320071d6414a3206f4e7214a320055d7114a320055e7014a3206d5e75d0a320055d75d0a320055f7550a3206d5c7550a32005d77150a32005d47150a32005db7050a32005d87050a3206d5e75d86320055d75d86320059e74d86320059d74d86320069e64d8632005da70d8632005d970d863206d5e75986320055d75986320065e65986320059f74586320059c74586320069e645863206d5e75186320055d75186320065e65186320059e74186320059d741863206d5e75d82320055d75d82320065e65d82320059e74d82320059d74d8232005d671d8232005d571d82320069e64982320055f755823206d5c75582320065e655823206d5e75182320055d75182320059e74182320059d74182320069e641823200c7e76d95320047d71d95320047e70d953206cdf73595320047e761953200c7e75991320047d7599132004dd7399132004ed72991320047f755913200c7c7559132004df7359132004f77159132004f47159132004fb7059132004f870591320047e7694d320047e7614d320047e76949320047e76149320065f658c93206e5c658c932004be74d8532004bd74d853200c7e75185320047d751853200c7e75d81320047d75d81320047e73d94320065e73d94320047e72d94320066e72d94320047d71d94320047e70d9432064dc735943200c7e75990320047d75990320047f755903200c7c755903200c7e7598c320047d7598c320655e7394c320056e7294c3200cdd7694c3200e5e7694c3200e5d7694c320074e7294c320074d7294c320055d7194c320055e7094c320055e7314c320056e7214c320665e7614c320665d7614c320065e6414c320065c6414c320674e7214c320674d7214c320055d7114c320055e7014c320655e75d0c320055d75d0c3207e5c65d0c32005cd72d0c32004dd7690c320055f7550c320655c7550c32004dd7610c320765c6510c32005cd7210c3200c7e75988320047d7598832004be7498832004bd74988320065e539883206e5c53988320055e73948320047e761483200c7c76148320055e7314832004ed76908320074e53908320074c5390832005cf73508320074e53508320074c53508320078e43508320078c4350832005e47150832005e870508320655e75cc8320055d75cc832005ad748c8320074e538c8320074c538c832004df764c8320055f754
  | 27 => 0x463d85420067775d85420067475d85420067653d85420067453d85420067652d85420067452d854200c7e75185420047d7518542006776518542006746518542006d76318542006d46318542006767518542006757518542006b77418542006765318542006745318542006b64318542006b44318542006765218542006745218542006b6421854200c7e75d81420047d75d81420067b65d81420067865d8142006db63d8142006d863d8142006f361d8142006f061d81420067a75d81420067975d81420067a53d81420067853d81420067a52d81420067852d81420067b6518142006786518142006db6318142006d86318142006f36118142006f061181420067b75181420067875181420067a5318142006785318142006ba4318142006b843181420067a5218142006785218142006eb4218142006ba4218142004df7359442004dc735944200c7e75990420047d75990420047f7558c4200c7c7558c42004bf76508420072c5250842005b47150842005b87050842004ef7650842005e8705084200c7e75984420047d7598442004de7398442004dd73984420047f755804200c7c7558042004df7358042004dc7358042004f77158042004f471580420047f71597320047c705973200c7e75d93320047d75d9332004f671d9332004f571d9332004fa70d9332004f970d933200c7e75193320047d751933200c7d7694f320056e7294f320056e7214f32005e47150b32005e87050b3200c7e75987320047d7598732004bf7458732004bc74587320047f755833200c7c7558332004be74d9632004bd74d96320065f735963206e5c73596320047f71596320047c705963200c7e75d92320047d75d92320063e65992320063d65992320069d73992320069f53992320069c5399232004be71992320063e65592320063d65592320069f7359232004bc715923200c7e75192320047d75192320063e6494e320063d6494e3200e5e6594e320055d7694e320065d7694e320071e6494e320071d6494e320055d7194e320055e7094e3200cdf7654e320063e6414e320063d6414e320055d7614e3206e5d7614e320065e6414e320071e6414e320061e6414e320071d6414e320065c6414e320055d7114e320055e7014e3206d5e75d0e320055d75d0e3207e5e65d0e320069e6490e320055f7550e3206d5c7550e320765e6510e320069d6410e3200c7d7694a320063e6494a320063d6494a320055e7394a320063e6414a320063d6414a320055e7314a3206d5e75cca320055d75cca32006ad64cca3200c7e75986320047d75986320065c5398632004bf7458632004bc74586320047f755823200c7c75582320065c53582320059e74d96320059d74d9632005ce72d96320055d71996320055e709963206e5f76596320055f71596320055c7059632
  | 28 => 0x52520055c73552520065e6394e52004bf7458652004bc74586520055e73d92520055d73d92520056e72d92520063d64192520056e72192520053e74d8e520053d74d8e520056e72d8e520047d7198e520047e7098e520056e7218e520047e76d0e520047d76d0e520065e63d0e520056e72d0e520056d72d0e520047f7650e520047c7650e520065e6310e520053e74d86520053d74d86520055e73d86520055d73d86520057a70d86520057970d865203e6e62986520053f74586520053c74586520063f74586520063c74586520047c73586520047c70586520047e73982520047d71982520053e74182520053d74182520055e73182520055d731825206e5e75d8d5206e5c52d8d5206e5f51d8d5206e5c50d8d520065f7518d520665c5218d520665f5118d520665c5018d520065f6394d520065c6394d520065f63949520065c6394952004be74d8552004bd74d855200e5e7398c520047d7198c520047e7098c5200c7e76d0c520047d76d0c520056e72d0c520056d72d0c520047f7650c5200c7c7650c5200e6e72988520063f74584520063c74584520065f73584520047c73584520065c73584520045c735845200e7771584520067b70584520047c70584520067870584520047870584520047e73980520065e73980520045e73980520065d73980520047d719805200e7a7098052004de73d9742004dd73d97420047c73597420047f71597420047c70597420065e6598f420065d6598f420065f7598f420065c7598f420047f7558f4200c7c7558f420065e6558f420065d6558f420065f7558f420065c7558f420047f7694f420047d7694f420065e6394f420065d6394f4200c7f7614f420047d7614f420065e6314f420065d6314f420069d6390f420071c5310f420065e6394b420065d6394b420065e6314b420065d6314b4200c7e75987420047d75987420047f755834200c7c7558342004de73d9642004dd73d96420047f7558e4200c7c7558e420065e6314e420065d6314e420072e52d0a42005ce73d0a4200c7e75986420047d75986420047f755824200c7c755824200c7e76d95420047e73d95420047d71d95420047e70d9542004df7359542004dc7359542004f77159542004f47159542004fb7059542004f870595420047e761954200c7e75d8d420047d75d8d420065f65d8d420065c65d8d420065e75d8d420065d75d8d42006cd72d8d420065f6518d420065c6518d420065f7518d420065c7518d420047e7694d420047c7694d420065f6394d420065c6394d420047e7614d4200c7c7614d420065f6314d420065c6314d420069f6310d420071c5310d420047e76949420065f63949420065c63949420047e76149420065f63149420065c6314942005ce73d09420067765d85420067465d8542006d763d8542006d
  | 29 => 0x200000000000160008020022023002003c00000000c800c000044000002404e0040030010010004000003402400e004df7358a54004dc7358a5407e5e75d8d54004de72d8d5407e5c52d8d5407e5f51d8d5407e5c50d8d540065f7518d540065e5418d540765c5418d54004de7218d540765c5218d540765f5118d540765c5018d54004de73d8954004dd73d89540063d64952530055d7395253004bf7458653004bc74586530055e73d925307e5e63992530063d64192530055e731925306e5e6398a5306e5c7398a530047d7198a530047e7098a530053e74d86530053d74d86530056e72d86530056d72d86530057a70d86530057970d865304e5e63986530053f74586530053c74586530063f74586530063c74586530047c72586530047c70586530047e72982530047d71982530265e6358253004be74d8553004bd74d855300e5e7398c530065c739885300e6e72988530047d71988530047e70988530063f74584530063c74584530066f72584530047c72584530066c72584530046c725845300e7771584530067b70584530047c70584530067870584530047870584530047e72980530047d719805300e7a7098053004ee72d9743004ed72d974307e5f53597430065f735974307e5c73597430047c72597430047f71597430047c70597430055d7614f4307e5d7614f430055e7214f430055d7114f430055e7014f430065c5398b430066e6598b430066d6598b430074c5398b430066f7598b430066c7598b43006cf7398b43006cf5398b430066e5398b430066c5398b43006cc5398b430064c5398b430047f7558b4300c7c7558b430066e6558b430066d6558b430074c5358b430066f7558b430066c7558b430066e5358b430066c5358b4300c7e75987430047d75987430065c53987430047f755834300c7c75583430065c53583430071e53d0e43005ad72d0e43005ce72d0e430047f7558a4300c7c7558a4300c7e75986430047d75986430047f755824300c7c755824300c7e76d95430047e72d95430047d71d95430047e70d954307cdf73595430047e76195430047e7694d430047e7614d4307e5c65d0d43005ce72d0d4300c7e75d89430047d75d894300c7e75185430047d751854300c7e75d81430047d75d8143074dc735944300c7e75990430047d75990430755e7394c430765e7614c430765d7614c430771e7414c430771d7414c4307e5e6414c430055e7214c430055d7114c430055e7014c430071c53d0c43005ad72d0c43004bf7650c43004df7650c430755c7550c430065c53988430047f755884300c7c755884300c7e75984430047d75984430065c53984430047f755804300c7c75580430065c5358043004ef7258043004ec7258043004f77158043004f471580430063d64952520056d72952520055f735
  | 30 => 0x10018007004001801e0210028020000025000000400800000000000020500040034004008001819c00c0010008008004000001800002a000005005c000004000800800000a005004800000200f800000201301b00240060050048008006001000803c004005010800c012002007001402c0070040018020010000005c014020000001c00000000b00100040010068004004000005000001200002e800c050001000001c01000700d801401a003003800002400002d8010010064000800000c00000a800400c0000008008002000014805c016041000800000000001180040040010020014056005006800401a004009800400e0030000024000003005804001802f0050008002007002002400200f005001c00600000c002c00e003001000002800b002000804e00f000000401200b003002c00c027006007c008000000000400200100900100b200d000000c00800000f00200260010020000000008000002800a0010000000008000001800800800900000080060020020074012002000000801c034003800801400100c800000200e0030004002006000000004801c00000080100040038008008042001817000002201280b4000039008000002e00a003000003600c0188098020001002800405e03b003001001e00200000640160100068004040016004000c01a0000060008010029002001c0440010060020022005001003004e00200400240120000010034004000005804c04e000000006000200000180100060080010004000006002000000800200e80380000050010010002002002802401200a001800c01a08b001000000000203b007c022000008001c00007c0120020044001000801001a00102b8008004004000002c002000004800000200f00000000c801700100dc00c00000b000403003700500900020000000058038001001000801400000e800c00200600c80000000050000004000014003800000c00e005000c000005002000000801e011002000e00f00c800400a0030008008066000002003c002015001000c00204c017001c00200400000140040170038030010003003000c012025006800c00805800400b002a00b0138000008002004005803e01300e8010000002000001c0000020010074002000000000c00a009000000800e0000000004000005000002800400e0048004012002005002803a0000128020064000000001c000006002000401200b000800401200b002801000c0000008060002010005800800400101b804000000901700000000020170000002000001000000e0000020008008000009007c01c00a000001804a001001000801800300280280080240048034022001004001000e0080000000002001000801402c00000a003c0060050018024000006002801000401001a800407a01500100240
  | 31 => 0x3b0018008000000002000401800400200080000080010004004005001000c01400001f800c064003009800801a012000001800a00c000000800202300100140040030090080006004000803c01800000980fc000000000800400000900200a400000600180000a0002003001000201f0000028012002017000000801b000002800000101d800c00400c000802001a003004000000c014001801000200100280000040050000004018009002001c000017001800000401a006021400a000016800400000a00000a4000000000800c00200800d00300120000030008000007000002000201e01f000000000000400000020010008000026000001802800c000005000800c00100b0044004004000801800403d0008008026011004001000e014005000000200700200040080050000038008003000000000000400b001401a005018000000000c01400cc002000009803c0020360000004018002000000c00200a0068020002034009000000e00000100180020130000048004009001809002201000a800c00401c0078000000004000001c00000400000300000010000048008002001000c0160000000008000001000015c00800a00600000300040000028000003007804400204e00680080660020000034000006000801000e0050020004008000010802c002008003805c03c00600100240a200000b802800000a00280040180000058104004005003800003c00b014801c00e0000000018002000006807400a009002801c010003009800000a001001802000e00f0000018004003000005c00200000000300080110098014006004000002c018013000000001800700d800c00800201d00040180070028010040013000000c0140090000010000007003001800801e000000003400300b0000034001000000402200b0028010006000004800400400900001a8010002001801400400400f00080020010058054000002003800000000a000001800201700000300040000008000000001008802804400401080080400000018030000017000800000001600780040020100078000004000001001c00e003000000c000000000000c00600300280000060000018000004000008800400000200281f40040020028030000016002000000a000006018c00400300880ac00e013000000c00a000001001400000000600080120000018004018002004000403e02a01581200060000028018000001006007000802200d8030018000005800000400c002805c00000d015001c0080000000004000001010003000e006000801c0020000040010002009000003002000405d80bc00200d0000004002000000806c00000a006800c00000c001002400200a0040000000002000003c0ec00400a003c00e0020038004000026001000000400e00000000640030
  | 32 => 0x43a8f96000245e1199fb63639e364779ffa000272600009ee55e80442f38bca8991e9290f0000000238c4d400009f206647f895f44fa0a684cd9a647ea00002b0a6d653b049e2dc82581ef9c4448a8b8e5d480000001f3a902162e01f0000000000000004f24f5214e91e983259e068a0ac080e8069c1804e1fd86dea4248398000376926875e9efa281066e0330f040000b665ed933c000000086b8d2c42f0000357180890b0000921800000000006b000001a700000000000270a3126bf82ba2821a9600000008f286a890a0ca2312179a931133e62903d20ff85e470f80c21179fa645d27ca12888183330c0e580a50a5e413886f9272453714987161d884580bdc0200950827a1cc0e51682194172625a8b4206b07ca52689c820e95b6589868e30881b049b13fc727187605a028e5df9df652f0e1201500b46bb057a0d706f01e59c788ec241a8a38a0e4f80f9c27304b85d4138a58f8cee26f1a40001000400000800080000200080050020008003008800800003b001000c00400200400840100110080000002001004806000c049001000000c0080290030062006000800400402a00e0050002041000001c016000000005800000b0000000002000005001801401f0270000000002002001400200000f0000008003000009402001f004800000000a0008024000009005800005e0000058130016007005803004600900000000080050010074000020000801000a003004000000a00200080b4004000002000000000003f003801200a009803000000a003001401000e001003800000101180000020000038008002000019805000200c00500100000180018004000008000800000800b001000400400d014802c00c001002806402a002001802802e02b0020010006000001801400c00a004801800002b00e002400c00c002001c00200000100f0022008001800400800d003002c0140160000038008004001003c004000000800800400400b801005a01801880000000000018108060000000000001a0040020008004004005004400000100000b0030000001802000000400000000000010020018000000001000000800000b8004020012001801000400100000300040010008000010000000001001a0210080000000002006801400000000000000300010000060000008000002400e003000000000a002018000c0ba001001000400201b00081b800000501b00200000000090004002001000001401a03100400080be000001800400a000005801800001f001000c0440000010000002004000800000000700000040000060040000000001003800400c00600180040060080008008000006001800c00000200480c8002001003001c05c00100080400020020020038000015002001c00c00f001801000c00400780240020020030004
  | 33 => 0x1d89fa4c523c26d21412521a0161f624d444a09628c518783f81c541cc00dc860098e112a2965221ccc201a6e26139ff29a496880a60b0a39c87642a1017c98d0de6323254c05221f880b894405088821f080de2c800003e28b3647ea6245de197e380861476d041832a017681925903659af242695469b718ea59a219c3019a9a2a2a59662e9d844e3249e1aa8cec6eaa15c6b70e967f311c64a11f724dd15a600026b400021b462705d02fc0e300d99500864a31695f13ae4d58970000071601a000094c0c3a05100007b7915213b11f43511c08642964479f1bce3db0b0004707c446a89d248598fc4821a2e10f86307c69bc87198e9c2379d6811113f4013a484421a76c8f125742a808943fe0d0e5fc877826207fa5a808767b901d2727800029c8f2441788362048a020b2808c95ca0de21b84ce94b0a507900fa88e700005c327e8000167a0002326038004633022b898c24cc8710000000135a0e9058871f079c4fc1eaa1641c9a8ab00009c40b7412f00000001b6a93600006948ebc44911ee19b1b6e4db276447892ee0f5000016985e0000115c350089c1f9054c06a800054d274e00008664d9052205a869a74292c800000d6000000097e91640601836390016600017bc032036a3e397b0932a4de89816fc14f20c454f043214589645630000216989498814fe925a250566133a72d8510773062e1919b062db00009539d2a000000000000006fb000000008449a20ec602700008c715123c300f40701b929ae13ac07c18de006000019c21d8000106e238279a6ba96aa12b00000001a0e47911a04e18aa82a593dc7ba80001a788b24a50ed011c0fe400000001a21e7a196a2f23f790120000954999a32e00003c4000000060b0000000164276b8f7800014a095499b09d294308cc90367d3875259f03360b0108a38b8b9c5f006ac74f0000000126e000000000013fa55f18e4699800091f000022c27d000000006fba20825d89f20001b68532a59a855912e63d9f8e7fc261625315201c6800001c9f56949a0085fa0d2a970800062b0000825800079e0000000117c71880000ab8e0049c87fc147800031999f810c0000000000015f946a765220471b00000000000000000089709a400000005bb0d1650b175c00b0a904fa91620000200000000042706b27920270419199c4698282948a6109e0160e5b10f7a0681b6032d8c940e4853a06990807c79308919003474e877400019fa0000e168fd21fe1b418520a3140c4d300220a99fce1f7a35a6eea62813e018e56825ba256155c53a89b810a0fe25ba05d66e58df06c719ba9b38a1a22e095e3c518869ae80ba0f899e25e21dca62495de9b11b0e175215e9a52546244a3b2098000001980007b88e3c000041400000000c31186000105c5278766815080a410894000005ea2bf00
  | 34 => 0x42481d0c429c58000000011032c12fe0c412be5b0800067f1b94264a5bc0001244348102e0f38b187f68de01ce241c0001a4a51327301fda0f229112b6694010a87c0aae26a972e6e30b3a7bc0d689759c16858878a2508db209886ae26196169e70c862a693ca2759b728e5953a8e987f886989f086a000000022f00000b587bb8fa00000116003800095081362f780000e5800027721ba55a935c40096049d80c8e0b90a7a8cc0b5a23b0c722f98ef22a4828400005f66f325240019b400e78ab20861a269f59d4c48191ea709932e4b588966fa80001421bfc47800206b400000b6166200004d400010e484e23fe0000000314000000013347b423b4126a06a35c9970271a1d458882ce84224d23e31c0e00012b010d97e644d80000000ec82ea1bb07f1010826c8db845205b672896cc2eb871028300000dc22b0000000077200120001ab48b5263292480007a3098281e83426d4157800014226cf965e63c1b9e02a8000000255409f0790624153e000019a00027da6549f5a7671858809985034e9d223af8b887001b107148e787108eda4db91ca7be09f48689a542af8a6c8189a3073914900c522487960d0892d9cba10e05025bb825a5668c4435624d03f99b56496141067c02643cc85f24070cf6729191c8eb878e83516a22e0147a5cf8a2063893e688616646120eee17e83343d11c485438ca47d020b64e9a5de1650d1e20d09ce5071c364be92e226622802d0211e993089a7338df41bf893279b928057718062be9c683931e0a6af83b0092001e40a82c61df15f22eca14c3b504005fc09e40a402725e183e671d88106d38e9a5c8169285281b434c8a144d8a2aa81711ce4e606523721cdc56393306071cc43da998a364239e8fd8cce78e0dd84b81a066b69c0c63e0c7e0ad8f3a635876098984b095921647d30128110861020c88400f420aa40014629bca2b42de0e707fe13e4000001a475800060821b852b0000467800002280008f6216016805b000020404dc00002e900007b180005dc99a000014409a1232409e00005c5910a000113e79327e60001efe00022d67f814be26501ae01b000092c80000001aa081f800030900d20002124000000019980006591d084d484761239cfe0001a5e6d713044da951a38e800010096a4000027a68d9f963398d100001a1e9b695a2457800099f02143eb876a4c90b906cb860e1a6233c5a7828019a965a00000003a4154c0000c2018b0ce23f6963a42e8000103177c935800090309c03aa0eb87319d1c6f1107c4d0160a9919b1a00020567858038122237c0000f6e43c9bb8094a2780000ddc6ce00001f39bbc342a65a0191cf40aa000081ca1a01e51e444ec800000020020000000000198c000179e0b51afc1a11c7e000000066890fc0001770000000010a80000000b480001c063
  | 35 => 0x80913ba1c81d020849d6a7c1275e1b71b6600005fc08813908b908e239aa58a34f22ca8de1d1e03b024c87900003f594340001dda523a11600003da444a1b62a0939600008bc42895b44d19b3459a96ce51985bc948000025680005f624f05259348353106011a91761e9211a190278a6a798cc30b0dee1039d6680f91ec41003625baa4da52b90cc1760dfa45085ee112164c0cc821c39784ae9b781a88660506628a79611f09188ae9dc262f0f46507a6786e28d1a16491543fea2fe13886f63dc005683e829a59d01d80fb923219e9a7a0db1218861117e4b19ae252c04523c427622d59d7c2fb92107e208d27a5094e1d1a32253c06900e984da29491205a10b2865025ec6c485846649be80bba4301f21d4e000248c2e602f27ae98ec61b0b84915065c65407b210b2244779906c61e9108167a68c9721a906a61a8498b1d062458aa23d20d127c29a6a4010b8c86c81f661f193c85ba1fc1db88dc1b32442595a64020a1df80740a8e7a29ae6406a19e239067e13406e88079464102881c2af0ace715a7b64378472000256815e078047a270834017184259d8a00014d247f02f8000170457618343ce023e76c026873608921cb1ba40001cac2d500000cb221691a8000000000095e82040000000547a44846225d800000009ee800070d11ae000000071780000000eb06319f1c8411e7e8efa508929a35000025847209708000000052500000900000000225a00024882ad9e0025f0e86000032276c8724971834e000029c5f0800027818549b820387ec050c22d8000445a2068318000000000000011b6000000063a14d071d04c6840a0ca00005041f1800066100007e8208c912969662792a000017ec955800000009b40000fec21c9e725d500000002142000121a47e000093a176000010b016d1a7e41980007cb1ed46d8981248b04e435909a28f700000fd9d987dc0000651800010180002d900007ef8fb289f000000012203e90c0a000024442a186a3cf263a010800000016245d2800062825a00001034146156258e0d3e00012302d815266721956000113055790104fc8dbc10d1c6a0001f6464f9ef49a807e69ea8e2c01d1b324d117928ce888e3a4812e1bb00002d4a26a8faa4b8348a43e8f5000000000002cc92fc4090a246f4994c78b839a3bd8f9a1551c14000270c0290d46297000021700007c30eb42ca8000661800000d988c4b70000900800073c8db0799090e98d872a8aba17c2f127840e88a625d195e85620d983fc9aca411800053da5e06f2917a1b7a09849aa07686387f295982509281b9c7a8070c616918e48489d03521bae66a867c6d285969b099c260f190648919481eb0f2c07b9c2a8ba14602d4083851e02169081756070a0e878609ba9f1a05091800840fc9d1098315ae90299e09261a323aa8aee9e21
  | 36 => 0x8000848800024e012c9c18c92000196c276174051c197c957000003415e00001c7a00008be9000bec9e88c907c61b3a7958a7656c27b883712da3fda19600015ea4b2827e000000042e124867589d42f40c1472a99b23909e8224200b278f8492170102c501a30875790065e591be35895f6299a39865d860042c9e88000041e1b80f940000ae073a232a81384de8fe8aac1fb07144b096f46d3048a93d0d9e0001d8649c1dd645c999a9f909ac5c6815097020b83280dd251d200e332a34c065800049922a62e80a3c83d22402bc955897916b6317098c443038046f1016000000000000009e9075000021ce5a600004981fe68d521ec0d286ba8c082e061108a20f0972c1ad97386c294082188b4619d9f6289d961417d13260369ba274107b822126d03d302960001aaa89286802308dca779054e80d195806793a27b80d5a1c21dfe0000222000000056512a411b800023b800000026ee00017a4058248e18912ec2728a063ff20200b08bc2987118c000035607500003fd16ac55c80008d088c08a406e275d1b764b9a3de3f502fc315085811b0dba46682a413d0ed832c9cc07bf180a5758dea00000001ed000083595c000000005008000904908e6c894a8337116a05e9fba7e1139480e9d320e205dc00001ba7e286c8014209490880001160d6a20503283ad800000000000000000000000000002e693b9df08bd120a07989524ad083c21d1c945d321e600002a03a300005120a7845590a620880000480dce51b9f4828586a00001a3a3b00e6c29f123c00016703c38000000000029a800046c1ab601e8cfc8fa16d810883ea0001a6c0000000843189a3dd19443b31d3e000153654a9c467c41a0872b8934172800014514f47210e9e28a0000214000082380003e40694040800034a022400009e80001cb897e15488e3938e3da00007ac903868d12380000000020a320607800009286784b9114c000238800000000000cc400014c4000019200022de7140000468886a000000000000008d29bd80001b3c1d70a3296380b61b48eca63992820318d8c07e08ba431236e37b14289268308433a65e76885e6319100e23f80005ae8c2e17781147e4264a1e484c02cf1182492948c9ba14a6000004a8bb9fde5b91c708758ba218882460000b9a00025b094307023c2000000008ca5961d426fc8000765806e68e18be7a187e0000129c0001a2a000000000010820002672000223a8620fce75900000001a16249927a62e14b21ee916832f061e7d600006e424e663e87d621320d213f07069c896300ba0556209098a5538990541985e24f9be082200403f423cc399981643d911c3c5982a5b5888860e128c4a20a4896e27d25d691140671e08000064449f00000001afa9b919903551b0c474000085e1dc6693a4560001c1e35407d40001fb2
  | 37 => 0x8049a24624e8b0e07d011a41491b428990d016609247ada5da1950bc65a6973684b82d22b18dd600015ba1ef15ec00000007db8f809dc989802b990221b11c251a052a69e23805848a108cd002816b9c9600015f07741ebc94aa2cc7761ab82481f6a4cb25b200000004f0233e9ca20bc02e25ea8a300000001e1215880009240d386f18000000000000000000000f5e2a2224e286026c00011cc00000006b080007a38000374273205c222a7cf91d89c0269c7ca19226a3a1be58305a257293b83d8962889895c45768d3064d0450192a0ba5c41ba69b48e5c5609d923d40b2c649815a59020b407fa2246ca08861d2a3660ea93f60ce831250c912a3269eca82a0af4209a29a43b1a8a9b980c468a0d946118e361f894c861c0ad40e612027138a4e499a59e1ad1d8e24b180440a0cc66599ffc59b8fea32e9bbe2d89ef26df8fd8993a5e88e0a3865819a187dea4ea630111a7d0856a076a1062f81a5c35588da22b15100d60f548ce051a8ef14840f205865eb265c1271f7890615fc1fd16b48d224048a6245a75b03488be8bd69500ae48af0bb80c923e290780009d69e046e10c4e0ef02f41b09748743263c2ed139c0168d0636a9fd02c5a66c7ee16bc25ea48a21080005010e266a50b1e78180962ee82300d301d68e400fc79a1ca02c4a3f092d1f9c2b11ba821f0bbe22a8a3015b9916755970e3ee19d29fa8cf2465943a7fb80005ed219418e8000000150431690903ed99ea28da0b05d0a1b005e197a4300f8484a95d0296071e536916c995940a8438f5c9a2a2da3fc1ed891d05261831a2c34922023f284107e6800035f1a9c30c93bc31a85584f7a5ee06d8af66299ac428e9e1e61925163c9a41628019301d505804c1a066234115812aa60835484600bb13da00001cc6f595fa79399622d71c284499b9a3119d388470ee6673922600000000788000000213e00000000000000649000000019960000e3e000183e9f70dbe41a800075c000000005e837f800009d13fe8b380f046115565dd163679c12f65d79c2e13c0df60001de04bc00007d8243a87680005cd23648029c4a1b9000008993c240309fe3d60f8855a0a3e00020a288c80002daa7446e606bc5378756000192a3099032000154230489962ad000051503160000000594a2c48d88d1c0000c747468a5a1d10564471000005c9d124da13c4487a2942a98f763cc07489ed00000000000548803e0002410000222880ca61888d04400001f746f79c8612d04c28c6a3a893f1fca6480ed61ca15d4000066807c9d585ec80009dd80007df8000587141800024405e9a19a757152e64100007d19e280e098d852496769e09ae490d9fa20e1a46692006728e6a5f45d101520f61242383a0cc695956631a0ada91e022800025e69a78c4a94e05be334858e952a0ae8e8042601a
  | 38 => 0x2642000000096b80009630aec362276862380000000000608876293193f853e228800000000bc00009449cb05a30d660d480004ca0604000252e38400e400006fa02f161a0f823ba55da07c974905a078000000025b46aa00001ea8bbc3c190dc000134e0000c5e00018c800014ce0db920e00011fe00020c80aaa53a00009b000008489ca97f410908020001da400017d200014e86808000318a37e14900980f194767e609da29b86163131d4a1af80005d89c5a5af9aac7a0194a292901854b19fe0aca6487e914e016e87722b7931268890147cc00008dd000000021707c980001d008c42ac03dc75b88cc3be96dc55fa2748b9a1529da923600013b050b9e3064e9338000267a00000000000f2e8e900000f900001c704907b20474610929e60c01c891100000000000435a6389b01ef6398853023e0ea07a98fc03d2a4ac500247e55424be1e7934263b93b61d688206d49edc56290c800020fc08e1f9e00025be83f8cfe0b417983ff802e76d80000001c9244e83d60d1800025c908468025d09d1841c167222046e90d8751131839e893c4f88000424927e00000000001d8c00008542529714000056093e891e7ef000081495745b209103b122828f825c40000aaa8d59b0800000004dc80000000000000131a96a9e1a9579122000211043e1d405a380001bf26a82409a0a393800028b800000026c674b19d835c00008eb1a1063f8000820a5f6057800004c04dc8f4a26c98089a64de262e4a2a7389d484a041894388a9211830c272c86b0bf47ad25b629f93c60000c9e000237289c92c00000000326192e000000071305f00a1904441f9e023b7110e00000003c680006dd027606f10487a68552000032039d0d2e97f81e80af80ac5da202207f0e7c85408649bd955a1d30e545ea00003350fb014807d069a17c83bd082a7b9800000012d05fb967e0ad01dc3e786c0000277024d80000000000000000000007e80001bb2062a7942fca4e456a225414289e69608000000000000027a60000000000000054284200001ed65f1119887d81b878e941a24122307e09f44321203c6b5000001f81e49a5a172000043c301278c72d161e35e0e381b120ea38101740000a4c73e80003bb24705f317ba9d513320002606830000088885b89df96f8998873e000082e21e255a05380000dea49c8e880000001b8836182105c19150336a4a844027e01e10ede9ec0d92975000097c119c06400000000f1e07e80003c61a44435100a023879876a0f202c200005e120922e585c6000237628482f69ea20c23c00468000232c79726fc68f16003d9a4a22521cbe5b4a1c2862a0ac8eda2e244c922853620f636b04ba06f99a408b14826b30ef06710c0c2b8811e920a7c289591040d79daa7c580003e188682b420708868b3e5eb98b60c38e88973a14
  | 39 => 0x328619e2242f92ae000241429d0014159a1140f3200411ea71e0d11cd07f70a946061b2a8d39a7600005703a5242a11e190e99c00000000f0a5a40be86b5920472285740000a984c800007450000000000057f82c84c0186200027140001e96000000032e190089780000ec94588bd9f0292500006380c182598afe000000093026646ab990c4d29a6088f15406be0b2e3d0a76630215bc5611912000000023e92e88c391d200022e046914c25229ece81117de7f500003a08bb09cd809a9ef97ca8369880000220c64d9f2e6de10ee217865616a198254216b000026520001800000000003291ac111800051fa1c66c5000033a8b0474380008899b3600011944ea08303359ed26731dce000021e24526be1e18dae1c391025a5131c2ed81568be1e84729a5040000cc231f24c8322279e6fd117054080ea4c883046c021aa8b000b04958faa0000000000116e00c1dd22cc07b018e2140004028a937018c9de8000000000026a0c9c5999dde8d70cc800007b64b60e982b314a445390e238a22700dc853264602cc1260e0c0c0135800590c25da9e4a7979b1e000121c4b4a3449cf1d202fd980284c99809df0f12203000061a173a0df272004d078c7891c3844405b27ed01c489b987400912982a7a1ea5d980003ba26746570bfc40780008d1800096515300ce24b00fa260459c994209ba32800000f870e875e5c78234754800a3ed00620000000000000000000007e19dec09a8000368800049000000001e7465525181b5899e26f85828dea16c57091e670c000256a814c39100883e08a3484c00002400e1e8c027ee000154a000000042b80005be96fe0fe80000cf1fd61d6143e000048c6bb848071c802a7551780370251029594aa1818cd8295186e1cc80005aca07897ca6a6197936649510da01d9d768f204a80491a743f2000067d9f3834313b435804e62a30f980001eda206964a176a0d01170b6e36d86180000846235240e67180008c4182650d98da41c08f28ea94a27180fa213d87da4af261a95806964278dfc8b0866256000004c58000746000078c800096608a46f98df8000000000000009bd00006bd1df2794a5926c095f83959cf04c78bfe58627980301a702a19fe884da6a4829868201793c81a189686b813a4057003a18f9cea01e0000150949c9ab1ffe00000008aa1fc642200005a980003871cee000143c2fe800000004b604f9376494246e1cb9dc021e995e84982ea0400d18048a0808048e461880496565a33659812ac2c080005d61aa687c8cf41c60a60533222c196055c7da13aa3dc959299d978c567a05a9de250084482888878fc690b80009170000000202a14392f445195860eb1fd246299de97710e02e181ea18f1eac1b6124c0001eae10e80008700000000266e82f8cae93e10b60ee0000945000000
  | 40 => 0x3000067b8be40000eac90e201800000000001dfc000005251112d47ba16ca1821222132a1dc6728000000000073f0000000261269600005e513803a2925a4801c5c60e99e87cd03ca12500000001ade1c9a3589561fc2257035079d858c0620e68362a25272f17c65f8168008086f23671e660000fc47c8890a2519b5a0618000426194e8a28704817973c00026c834d031800000f20001ce25038ee437502de4568d5e99aa51e545116689a1c1a59b11188f41f3642a8000369145291c8c9669097b80001b1822a22ec4a1851c000096c00000008b400000fb111e8f980000000f644bc86e66479f0873280009a680009bc00007aa05ce5ea98aa42d10c637797000000000771000087d000085aa68e791a21c2b2274c57391b22c895c60000dcc751821a00015ac85a22c68b617280b124aa000000099a0e5278d0c5644189783df892200026cc2279dbe94d122e0001c9084005e229900004be23d688d96500001b5e656a2dc8dc16d48519ecc0e71f7627a8e765109e90958a28699f98b40560e1432b1c2c22027ac84800009a001544b119ac396a7d45fa80000000ee030681ca70c80906cc18d22dd800000008b4000275c1b684c862c9e5a73d974e515a1283d5a6145c8a22e349831a4c2996e5ae1b589aa823a5f4070000ca1ee05f8cf8198123a62288c888e00002b980000000b4c470014600002fe000000047d80000000af000000000001564855147271900868240000035239400000006b20b346e39c406701f2a9be800094181c609995520eb85484768b5e700a2583161cd43668eb254580a80d00094826925e22b8b4425800003819e98297985c000000031e8000669803c30a83066af1c1005004ea93882365f716f6635000017082a23790bcc7d41fc80000eae000171200000000fd2586547001c0000c78663800000020067fd800086415e20021a7c157a56c83800000162292491800013819ae15195d23c88aea48519ec0280ca62f215b87898b9e807245061f8612795000057b80003340f400000000000070a000073a96722a22c180003c0816476e06ea8e2a2ea679965444f014a40e9c127e51a466db0fc299823e4000097480c01ce0001ce650583de0dd0fba058a24c75815285de9c3c1dd8a803d692a27bb20d80001e6c73b019800000008b2257e3cf8efe26025fc9b51a6208f15382ba26ea6d906343889e0e0e81a240f010767b08852511896e0c288d6009a7584aaa04c15f260a88f83029098ea24c3178e51b05389691e429291a1c38d26b212100009f1251c1e220ee2df19a8512800000000003df000029001a400000002b28db473214c089085d2350a13c55b1c0401305cc4291c8e6f695be5d918c410104be6c11bd48829a8833917fc000000000000000b88000000032600000000000000000209c7d486
  | 41 => 0x169000015680fe352a2120fc27186d084165c099dc30426ec84b118069b899a068800454ca6d88da979c83387ee72ca6821f70d82423022e44d171c59700f683b24ae7380e206180000899800012086a284e8000558074e000176e000000060500000000ef800010fa6ac16d0000079a04f15a45e8172472a000094f000021280001da073601c27bc0938000000215a0ab18ca1909cd633803303d39292202182e0d9000032a8000000273a62c1f4a646924e5f927a03f490725fd9276450062a4159bc28e11aa22e48a1e7a89da67d517f84f3103e226123e00000005cc14e214d8d6e34100001fc00004d7805c3b380006fc0000382939230f80003009f1441526b6360256e6b18e1a778907a7a7102000018ce4ef9b2c82ca1d05aa10f444b21d27cc86c665c8ea60000c6053591a82a725446ffa02865d0e6058800008da00e24df1c988ee1e0c4c3800026d94509d018f265e21a48c1037855c1d2e85d9be27c3a6fe0460e4849d0bd23a39bf852d80006810b948bf0de80b5831c00000006ba00000000000000037e0b71d2600000d82eb1192205800011580009d59ec014b9e9e00015c80001a4c310270a00008c62e98000829269839609de1f319b4451270e9a40af881098f42c50cf075e010462089ec4de80000e3081e000192818717d47e0180c0001bfa0001a1203a17be593877e61987c0369800090d000059207a600000002ce19f26c580000be99da5099fea685000000000000000956000147c0000000000038a218000000000a60001e1c92f18840398000000145e14f96e20a4852c129929077d02b80001782000029e24a8e184aa0ce819214ee2e2890c49e07ae000200061003fc1b39dea1bba4ba13e9bd0531a61e3e98ea42e08000000247630d07220001f5c000092830014b48d0173253f000028e16de0001d9e76e80000001d5027e144e000000074d17e2933883e7c821e06090b1a95da2a00001fec498929a43489a018a1f6c3bf036015423f88f387128120ed26450b7a497206e93087349cd20849e48368000000080b00006a180006a4800076003b418080000002742000163435d0c1e8a7820a291860a5b825480002432604230a1a49ec411f88f405b0e3211680003e49b8014d1cc20001354000000000000000001c228ac800010480009eb96f29dba5367771252000000000000008ad95cc0001d360000c2800000007e3184c40200003d807fe2228000584000000000ee79a856c223054a2ae810e19300001e821589f3258848d08ce66d9bb694c8000408945c0ee9d8289f8000370873c9d21c0a7d980002b01b2613a12b878f0000000201400021c800021de8b4a174371236c6e805fe5dd8a700000000000244c93b12ce00000000000000798262a4df8984162845400000002b608a017118dc00000000
  | 42 => 0x7e486ca00026ae8c61bac6128f3400000000001938000265404e8c6c0001cd26bc131093800000820000000170a00016085350c1600013ee6df08ea000038e07b02bc66500000970fbc0000a22452800008a962a0001ace23604d61de84a400000000001de80000d849c480923c7097e37ca2be5ab9f5e5b00a2a4b300007df08fc04a90e864b082c95aa06c75200003eb1a80000000000000001e89e2a00004cc3b8800079888a6000139e7588f363148e4a00005ec6ae94e64098b682dc0d7600025cc000251a58c8cfa2c71eb88d491d4200000015a23ec18997fa4a3a1e8666000000000009a1a1341db150c60396c67c185aa0000da80000bda8ff052842b1fae85e92ba914a28447c03a89e1820e9ec9b5414488f64a5a7d836813602c913d041427907c48e508f1a71c91b0c70736825400010ca41380004ba810c01216f03ca80005b6a18c00013d82d39d72000145a17e1c6e8c79c8865a0a2c93f9d2487e88049fb17fe5f68eea0ed99bc05ba0f852e8e247940fee9f7a0103b0a7e200005768118fe800023600cf8000060868c737a5a61fa8c809d4168a47c800024708701938d7a8d797a20001cf821f800000018d068f89f618d844c0000cbe1ea253e913a7041f4955450a8c3c1b5264400000006c80000000189600023060cb9a8277b9a1a97893d68511e200979a8c13f8000000142098f80a286080008fb93028c3041a00027ce0000adc000257032d046227f1a5a2f000001dc1d2834d9094943a29c56c831e9a89fc09af2068000163c000000000000000908e2a505000085fa78e35b0408121903c0000dc69cf8c82551244664c9a0c6c9113860a10a03d499e401810fe241a2102c990745db0eba94081b22f626b0213999e0a50c3631b88e862b9b826d11b866440742838a04a6a916e6994085639926222b592b2816105819d08f010b998811905ac785000074580002468e7e7ac0fdc04c84d83070e6e96a099c7201872166800091a23da00014e47a918a85200a424e111901a920369b2a392113a20e353889009590e64e685c870726586f01fe470818c26d199b80001f3c1e095180e4196a000260e0778c8a66f98564a980000001bdc67506a600020f00000000972800093d99d000027022df93ce000227a00000000000d7e0448000000000065800004e81646000000075f83842c40000000104c2f8832a53e9ad24e08aa4000000090180003f300001868d02775104a15c892e83900be7669faa918981a3451ad85f5a72e579277441e1fac7af837676806b89c6a166061206074c0500081a5ac4caa4f278b10f067d25786ed04c486f019482809c458b23f2378959c2b4952477e8bf82d2969c5641f246421c8c5a18a0a55b8e8412c86f8622258052e1d5a2eaa6f800026002fa90302f51dac00022142c300008f00
  | 43 => 0xab83efa20091612de4f4a528709208a13b8000579a0866bd80007c011b8000000000009ae239a5a2477035a0fe020c5ca86f415003540339ff47641bf624c000000017ce1ac0f28872a55048300fa30e03be5e2810669c800000014f26ac9dbc00002da74000004fb000045e21e208c8a1c3378e082789a486dc200c15104d28428e8068811c8000009e41a27c07840000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xa568614c3184001c4cc82904308003a199032086100060f324e72842000c1d649ce5084001a2ce620ca1080025520d7114210004b2412e22842000c58639c351440018d0c5386a28800217a1873545100060fb20e6a8a2000c1c641cd51440110bd0fb1aa2880221721c635451000437430e4a8a2000c2f641c95144001858c8392a28800313d8c725451000626318e4a8a200686e87d895144001898e7b12a28801a1b21c625451000626398c4a8a2000c3b641c15144001870c8382a28800316d8c70545100062c318e0a8a2000c6b621c151440018d0c4382a28800307d9273941100060e324e7282200085d87d8e50440010bf0e31ca088003139cf629411000627398c528220008cc825cf64040014b501bacc608003139947258c1000626b28e4b182000c1c751d1630400189eea392c608003131d47258c1000647ba0e4b182000c8c741c9630400189f0a392c608003132147258c100062a3a8e2b182000cc4721c56304001930e8382c608003321c87058c1000668388e0b182000a4c8258e53040010f30d384a60800a1e2017614c100050e422c62982000a4c8258c530400149904b1ca4080021e61a70948100143c402ec2902000a4c8258c520400149904b2864080023361c620c81000546c20c4190200085c835d6610400149904b1ea2080021721e63544100042e43ac6a882000a4c8258d510400189cc6392a2080031358c72544100044fc3ac72082000a8c8258e410400151904b188208002c520d51104100070ab1aa22082000b2482544410400162906ba88208002cc20175104100070ab2ac62082000b848258c41040016650129882080028d61853104100045ac38c42082000b32809484104001d08c41908208042cc2157010410005c841ae02082000ba0825c041040014ab0c2986208003155d8530c4100042f41eed280200086e82dda50040050f501bb4a0080021761a739401002c2fc3cc7280200585f8758e500400149904b1ca008003459cc419401000526412c62802000954835c450040012c904b88a008003165da63140100062cbb2c62802000b488258c50040018b2ed190a008003165d8321401001c3dc32e22802000958835c450040012d104b88a0080030e5da41140100a59940c822802000d31719045004001872ec208a0080025c61c411401008699438822802000d31871045004001a62ec208a0080034c9cc411401000789318822802000f11631045004001a64e4208a008003c48c8411401000788190822802000b3284cc45004001aa4e7988a008002cca132114010007a0190422802000a598614f3004021a64ea20e6008003c414c41cc010086983a8821802013d50750c43004021a64ea20e4008002b26183208010086983a8821002000f80321042004025ac0ea10840080434c1d44184010
  | 1 => 0x90eb20641000383e15640c8200070642ac81904000e0f755903208001c18eab206410003a1e05640c8200054640ac81904000e8481590320800150902b206410003a2201640c820006a43aae01904000b88845c0320800178102b8064100021720d75984200042f41ceda88400083d87993510800107f0eb26a2100028d20564d4420006273b065a884000e0d640cb5108001a9065386a2100020fa1e64544200041e43ac8a884000a3481591510800183cc839aa21000307590735442000617320e4a884000c2d641c951080012990e192a210003131d8325442000706b2064a884000c3a641c15108001872c8382a210003520c870544200041ec3ecb2084000a1e83d96410800191eec19482100020f61f65104200050f41eca2084000c8d760c84108023c48ca20842100028d20564940200060f324e72804000c1d649ce500800185ac9394a01000253e1c329402000706b2065280400085e839d8500800146902b20a01000383590321402000744b2065a004000cc9760c84008001a50e92824010003581c65048020006943a4a490040009ca878c92008001b10e91924010003589487148020006e1190e2900400085e821cd65c40018b0e7b82cb880021720d75193100050f426c629e2000a4e82d8c53c40010b906ba8c58800217a0f7694b100042e41aec296200085f8759632c40010b90eb286588002a3612620cb100050e41acb20e2000a1c8359441c40012b106bb0a1880025620d7114310004b4412e22862000c1e749cf658400183ae939ecb0800217a0a73d9610006173a4e5b2c2000c2d749cb658400189ce7396cb08003135ce72d961000627c1ce5b2c2000c4c839cb658400189ce6b96cb080030e9d270d96100061cba4e1b2c2000c5a739c365840018b2e7386cb080031a9ca70d961000634b94e1b2c200085c835d6648400143d07b2cc9080028ba0b65992100050e41aeb32420008ce82dcd648400107d0fb2ac90800287a0f655921000517416cab24200083e87195648400151d05b9ac9080021ba087694e1000437414ec29c200085c835d662840010bd063b4a50800217a0e7614a100042ec3ecb1942000a4e82d96328400113f0eb24650800217a1f650ca1000527416ca194200083d87993518400107f0eb26a30802e0fa1e64546100541e43ac8a8c2000c1e641cd518400183ac839aa3080030b990725461000616b20e4a8c2000c3a641c15184001872c8382a3080020f61f65906100050f41ecb20c2000a2e82d96418400107b0fb28830800287a0f651061000517416ca20c2000b1483544418400164904a888308002c520d75106100049ac3eca20c2000b1683d94418400164d05b288308002cca0365106100049ac38ca20c2000b3280194418400146d0c2988308003899885210610007433106420c2000
  | 2 => 0x4628c1300062b3a8c3182600085c835d6640c001898cb39686180021761f658c8300060e32ce91906000a4e82d94320c00143d07b2c821800287a0f651043002c2f41cec2806000c1c651d1300c001898ca392601800315194714c0300042e41aea3264000a1e84d8c53c80014ad03b18a79000217e1d658cb200042e41aeda8e400085c835d951c800143906b2c83900028720d65107200060e3a8e8b1c4000a1c8458c538800151f08b1865100029361a530ca2000526c30a61944000a8f845d8328800149b0dba8651000293618750ca200056340ec8194400085c835d6618800189cc7396a310003135d832d46200042e41aeca8c400085d861cd51880010b90f31aa3100021721d635462000627318e4a8c4000c4d631c951880012990e192a31000313dd832546200062d318e0a8c4000c59631c15188001a9064382a31000227e1d639062000742194c220c4011e26651042188001d0cc620843100021761a739422002c2fc3cc7284400585f8758e508800129f0e194a11000295a0f75d85200042e41aea30a4000a54835d461480010bd073b2a29001a1b20876545200042f430e6a8a4000c1f641cd5148001838c839aa29000217a1f63545200042e438c6a8a4000c2f641c95148001858c8392a29000313d8c725452000626318e4a8a4000c5473d8551480018c8e5b0aa290003151cc615452000632390c2a8a4000c3b641c15148001870c8382a29000316d8c70545200062c318e0a8a4000c73611c151480018e0c2382a29000307d9273941200060e324e7282400085d87d8e50480010bf0e31ca090003159cf61941200062b398c32824000c1e749cf650800183ae939eca100030b5d272d94200042e41aeb3204000a1e83d96640800143906bacc8100020fa1f65590200050f41ecab20400083e87195640800186eca38ac8100030d194715902000547416e6b204000c37751c56408001868ea38ac81000325dcc71590200064a398e2b204000ca4721c5640800186d0a38ac8100030d61471590200064c398e0b204000ca8721c16408001960e2382c8100028d2056494c200051a40ac8298400085c835d6620800146902b24a4100028d205641482000646b24e7a104000aa48159332080010bb0fb2c641000227e1d648c8200054a40ac9190400085e87d94320800152902b20641000383592520c82000706b20a41904000aa4815903208001c1ac92986410003135d8530c82000706b20a619040009a8845c03208001a90a6b80641000278205700c82000546c24ec1904000a4e86dd4320800169501ba8641000293a18750c82000626bb0ea1904000b4a801d4320800169501b286410002d2a00650c82000546c34c81904000ac4815903208001c1ecab20641000383195640c820005c240ac81904000c8f87590320800191
  | 3 => 0x430a800085e839d951500010dd053b2a2a000217a1873545400042f43ec6a8a800085c8718d51500010dd0c392a2a000313d8c725454000626318e4a8a800086e87d895150001898e7b12a2a00021b21c625454000626398c4a8a8000c5473d8551500018c8e5b0aa2a0003151cc615454000632390c2a8a8000c5b631c151500018b0c6382a2a00031ad88705454000634310e0a8a8000c73611c151500018e0c2382a2a00021761f63941400042fc38c72828000c4e73d8a505000189ce6314a0a0003159cf61941400062b398c32828000a6481588521000158902b106420002a361a420c8400042e41aeb308800086c825d661100010bf0cb88a798002532097114f30004ac402e229e60008b4815d262cc00183ce829cc59801617e1d658cb3000546c24c4196600086c825d951cc00162b0229883980038514e61107300062732ce5a1c6000c1e659d2328c00149904b2865180121761a73d463000436412eca8c600485d869cc508c00143d09320a69800293a0a6414d300052b40cc829a6000c1e76190534c00143d02320a698003071927214d300060e322e229a600094c825c4534c0012b100b88a698003071927014d3000706320a7b126000a4e8214c624c00149d0c298c49800383d90531893000706320a63126000a4e85dcc624c00149d0e298c49800293604531893000527400a63126000c1c649ce524c00189ce6314a498003079d4648c930006273a8c51926000c1c75190324c001c28c829ec2980039114c62d853000533416ebb0a600086c825d4614c0014ab02298c29800295a1853185300070bb20a630a6000e146414c614c001c88a7b10c2980039114c621853000532412ea30a6000a558714c614c001c2ee8298c298003851d053185300052b410a630a6000a568014c614c0014ad07290c29800295a1632185300052a4286430a600086e829d9514c0110b9063b2a29800307d9073545300060e320e6a8a600086e861c9514c00185ec8392a2980030b19072545300043743ec4a8a6000c4c73d89514c0010d90e312a298003131cc62545300062a39ec2a8a6000c6472d85514c0018a8e630aa298003191c861545300061db20e0a8a6000c38641c1514c0018d6c4382a2980031a188705453000639b08e0a8a6000c70611c1514c00183cec29c82980038314c62905300070a298c320a6000c1c7614c414c00162b0229882980038314c62105300070a298c220a6000c1c75193314c001898ea3166298003151d461cc5300060e3a8c898a6000c8c641c9314c001898ea3126298003151d4614c53000662390c298a6000c98641c1314c001990c4382629800307d9273941300060e324e72826000c4e73d8a504c00189ce6314a098003159cf61941300062b398c32826000e5053187304c00183cea3246098003139d
  | 4 => 0x19400189ac7396c3280031398d72d86500062d31ce1b0ca000c59639c3619400183ee931ac328003071d263586500062639064b0ca00085d8798c61940010bd073b483280021ba0a76906500042fc32e720ca00094c825ce41940010bf0f31c83280021761e63906500050f41ced20ca000a2e829da419400143f0cb9c8328002c320973906500050fc3cc720ca000a1d8798e419400143d0531c83280024761e32906500050ec346520ca000a1f860ca41940010bd073b0832800287a0e76106500051ac0cc620ca000a1e8298c4194001c2d0331883280038560663106500050ec346420ca000a1f860c84194001c2cc73888328003079d263cc6500060eba4c798ca000c1f7498d3194001838e931a63280031398f724c65000627318e498ca000c5a63dc131940018b4c6382632800295606630c6500060f3a4c790ca000c1d7498f2194001c2cc620e432800217a0e76886500042fc32e710ca00085f8798e21940010bb0f31c432800293e1832886500042f418ec90ca00085d86dcd21940010bd0f31a43280021721e63486500060fba4c690ca000c1c7498d21940018b4c7b8243280031698c70486500042f41cec10ca000a4f860c82194001c2cc62084328003899884108650007821908210ca000c5473d8551540018c8e5b0aa2a8003079da748c85000527416ec190a000b0d849c8321400168902a106428002d2201420c8500060fba0e6b08a000c1c741cd61140010bd0439ac228003131cf725845000617ba0e4b08a000c2c741c9611400189ee6392c228003131cc725845000627c18e4b08a000c4c831c961140010bd0f192c228003131ca32584500042e43864b08a000c4c720c96114001876e8382c2280030e1d070584500062db98e0b08a000c58731c161140018d6e4382c2280031a1c87058450004a6412e7208a000b0c825ce411400123b0f194822802a0fe1d61904500050e41ac3208a000a2c8258641140010b906bb082280028720d761045005c1fc3ac2208a000a1c83584411400145904b0882280021ba0b76cc45004c2f43cc6988a000c4e631c931140018b4c6382622800217a0f76c84500069820ce1908a00085c835d82114001e086420842280021761e32980500042f410e6b2e800085e83dda52d00010b906bb0a5a000217e1d658cb400042e43aca1968000b848150832d000171100a1065a00023320973987400042e41aeda8e800085c835d951d00010d904bb2a3a00028720d65907400050e41aca20e8000a4c8258c53900010b906bacc3200032518c715094000652310e2a128000c98631c14250001918eca1064a0002e1205420c940005c4402841928000a5683dd761500014cd05baec2a00021720d751854000436412ea30a8000a54835d461500014c904ba8c2a0002ac201421854000742a106
  | 5 => 0x803131cc72594210042e41aea320420086d869ca530840d0d904bb0a61080287a136314c210042ec38c6298420085e83dda52084012e100b88a41080313e0d76148210062641aec290420786f865c4520840129906b88a4108025a2017114821004a741ce0290420085f87596320840149b0c29464108021721d650c82106526c34a41904200a4d86148320840151b093b064108029361b750c821005a2c0eea1904200a4d861d4320840168b023a864108023361f640c821006a23ace21904200b84845c4320840178100b8864108021720d76d442100626bb065a88420094c870c9510840189eec192a210803520c870544210050e41acb2084200a2d8614a410840143906b2882108028b618521042100782196a22084200b14835444108401e0864a888210802cc201511042100662bb0642084200b14835d4410840164904ba88210802c520d651042100593414a62084200a358614c41084236490ab908210802e120d7210421005d0402e42084211b2682948410842364f0e2908210802c961c521042100592c30a42084200b2683148410840164d002908210846c9a173210421005c3414642084200f04528c84108401e0ca41908210803c1148321042108d92428642084200f06530c84108401e08a61908210803a19d8321042100742bb0642084200f07850c84108401e090a1908210803c19d4321042100782ba8642084200f06650c84108401e0aca1908210847491d441c84210074219083300420085d86dcd5494001898a4392c7280021761b7354a500042f43cc6a94a00085d86dcd519400183ee931aa328003071d263546500042e43ac6a8ca000c4e63dc9519400189cc6392a3280031358c725465000436412e331ca000a4e82192639400149b04324c72800295a077498e500052ac0ee931ca000a4e829d2639400149b053a4c72800287a127298e500050ec24e531ca000c1e849ca639400183b09394c72800287a137198e500050ec26e331ca000a1f845c6639400143908b8cc72800293e097198e5000526412e331ca000a58805c6639400189cc739687280031398d72d0e5000527416e7314a000a4e821ce62940010b906b8cc528003079d26318a500060eba4c6314a00085f8758c62940010bd073b6852800217e1973d0a500042fc3cc7a14a00085d8798f42940010bd063b285280021761b7350a500042f43cc6a14a00085c8798d42940018acc7b8a85280031598c7150a5000633310e2a14a000c5a63dc142940018b4c638285280031a9887050a500060f3a4c7194a000c1d7498e329400183aed3a46528003075d9748ca5000527416ec194a000c4e82dd8329400161b09390652800313dda420ca5000627bb284194a000b4481508329400169100a106528003079d263d86500060eba4c7b0ca000c4e639cb6
  | 6 => 0x534412a23026200e3151104604c4012e100b88a6188021761c6414c3104c2fc32e2298620094c825c4530c4012b100b88a61880255e197114c3104e2bc32e22986200d17845c4530c401a2908b88a618803159917114c310062a322e22986200d47825c4530c401a8904b88a61880354e017114c31004aa402e22986200d50805c4530c4012a100b88a6188021761a7014c310060f3a0a7310620885f87596320c40149904b2c6418802a3612620c8310050ec30a72086200b158114e410c40143b0c2988218802c56045310431044aa43aa29886200b5080545310c401aa2a2382621880255a1e534c431006a9298e09886200c1c7414d600c401898a6392c018803079d273d97210060eba4e7b2e4200c2e749cb65c840185ae9396cb90803139ce72d972100626b9ce5b2e4200c3a749c365c8401872e9386cb90803169ce70d97210062cb9ce1b2e4200c6a729c365c84018b4e6b86cb908031a9c970d97210042e41aeb3264200a1e83d9664c840147501b2cc9908028720d75993210041f43ecab264200a1e83d9564c840147501b2ac9908020fa1c655932100547416e6b26420087a801da53c84010f5013b0a7908025c2017114b210052d406cb196420089f8759232c84014b501b2865908020f61e64d47210041fc3ac9a8e420b83e8799151c84150790eb22a3908030799073547210060eb20e6a8e4200c2e641c951c840185ac8392a3908030e99070547210061cb20e0a8e420083d87d9641c840143d07b2c83908028ea0365907210041ec3eca20e4200a1e83d9441c840147501b288390802c520d511072100598402a220e4200b14835d441c840126b0fb288390802c5a0f651072100593416ca20e4200b3280d9441c840126b0e3288390802c9a0865107210051b430a620e420085e83dd560c8401838ea3a2c7108031398e7294e210050e422c629c420094c835c452884012d100b88a51080253a0e7014a2100547c22c61944200a4d8694c328840149b0c2986510802a3e11760ca2100526c36ea1944200a4d861d4328840159501b2065108021721d635462100627318e4a8c4200c4d631c951884012990e192a3108031698c70546210062cb18e0a8c4200d48321c1518840113f0eb1c8310803235d032982210042f41eeab044200c4c639cb51484010bd0c39aa29080307d9073545210060e320e6a8a420885e87d8d51484110b90e31aa2908030bd90725452100616320e4a8a4200c4f631c95148401898c6392a2908021ea1870545210061db20e0a8a4200c38641c151484018b6c6382a2908031618c70545210042e41aebb024200a58835d760484050f70ea8ec0908029620d51d812100534412a3b024200a5a83dd460484014d505a88c0908029620d511812100534412a2302420085e821cd650840189ee6392ca1
  | 7 => 0x9d878ca611040162906b2cc220803455d57398441005c2412e730882009358714e611040123906bb6a22080307e0d76d44410060e41aeda888200c1d768cb511040183aec196a220803439c832d44410048f41ce1a88820b83f865d6511040183eedb9aa22080307dd873544410048f410e6a888200d15811cd511040185eedb92a220803431cf725444100617bb0e4a888200d0f731c95110401a18e6392a22085749dc4725444100687c18e4a888200d0c831c9511042ba4f02392a22080247a1e32544410060fbb464a888200d0c728c951104012390e192a22080307dd832544410068639064a88820a83e87985511040162b0730aa220803451ce615444100692394c2a888200c3b76dc15110401a30e7b82a2208034a1cb70544410061dbb0e0a888200d1b731c15110401a30e6382a2208034adc8705444100694390e0a888214d33711c15110401a3464382a220803460c870544410a699c08e0a888200d32611c1511040123906baec020803079d273d97310060eba4e7b2e6200c2e749cb65cc40185ae9396cb98803139ce72d97310062641ce5b2e6200c4e735cb65cc401874e9386cb988030e5d270d97310062d39ce1b2e6200c6a729c365cc4018d2e5386cb98803169cd70d973100635392e1b2e6200a2e82d9664cc40147501b2cc9988028720d75993310041f43ecab266200a2e82d9564cc40147501b2ac9988020fa1c65593310061b322e229e6200970805c453cc401898cb39687988032359272d0f310043d404ec296620085d87d9632cc40149d05b2c659880296a03658cb310060e32ce9196620089f8759232cc40149d05b28659880296a03650cb310041ec3cc9a8e620083f8759351cc41707d0f322a39882a0f21d64547310060f320e6a8e6200c1d641cd51cc40185cc8392a3988030b59072547310061d320e0a8e6200c39641c151cc40107b0fb2c83988028ba0b65907310051d406cb20e620083d87d9441cc40145d05b2883988028ea03651073100527410c829c620094c825c4538c4012b100b88a71880293a085398a3100526412ca1946200b158114c418c40162906a888318802c9209511063100598402a220c6200a8c825cf644c401898cb396869880323d9272d0d3100547426e63126200c1c659d2324c40191ce83146498803139cc62d45310060fb20e6a8a6200c1c641cd514c4010dd0c392a2988030bd90725453100616320e4a8a620686e87d89514c401898e7b12a298803131cc62545310043d430e0a8a6200c3b641c1514c401870c8382a2988031ad88705453100634310e0a8a620aa3486544414c40164904a88829880389189511053100598402a220a620287b87547604c4014b106a8ec0988029a20951d813100565416863026200a9a848c8604c4014b507a88c0988029620d51181310
  | 8 => 0xcb88a7208024b2097114e410049c402e229c8200c96639c76290401934c7386c520802a9a076298a4100555406c53148200c1d7698e529040161904b1ca520803075da6314a4100586412c6294820a83f865c4529040123906b88a5208024e2017114a410048f41ce02948200c1d7694e329040183aec29c652080307a15768ca410060ec2aed1948200c1d769d6329040183aecbac6520803075da658ca410060ebb2cb1948200c1d7694a329040183aec2946520802c3a0b750ca4100587410ea1948200b0e82994329040161904b286520802a3a1a720ca4100647bb6c41948200b8681d88329040171501b106520802e1a04620ca410060ebb4c7a8c8200c1d7658f519040161904b1ea3208028761a32d46410068739065a8c820091e839c3519040183eedb9aa32080307dd873546410048f410e6a8c820091c8798d519040183eed31aa3208024721d63546410060fbb2c6a8c8200b0c8258d519040185eedb92a320803431cf725464100617bb0e4a8c8200d0f731c95190401a18e6392a32080343e0c725464100686418e4a8c8200d0e631c95190401a1ac6392a32080247a1e32546410050ec3464a8c8200d0c728c951904012390e192a320803431c832546410061dbb6e0a8c8200d1873dc15190401a50e5b82a3208030edd870546410068db98e0a8c8200d18731c15190401a56e4382a3208034a1c870546410068d318e0a8c8200d19631c15190401a3464382a320803460c870546410048f41eeab04820098c825cc60904010b906baec0a0803071d073594410042f410e6b288200964825c453104012e100b88a620802c560453d0c410068629ce5a188200b158114c43104010bd07bb4a4208021720d761484100554402c4210820085f8759632104010b90eb286420802b2201620c841005c440284190820085c835db511040123d07384ca2080247a0873594410068b408e6b288200d15811cd651040161d05b18a620802c5a076314c410048ec38c62988200b168118c531041707f0cb88a6208024b2097114c410049c402e22988200937865c4531041786f0cb88a62080345d8d7114c410068a31ae22988200d27825c4531040126904b88a620803492097114c4100492412e22988200d33805c4531040126900b88a6208034c2017114c4100498402e2298820091c835d4621040155100b10c42080247a0f76948410049ac0ce7290820091c835d8521041707f0cb88a4208024720d71148410049c402e2290820091e839c0521040183cec29c6420802c5604538c8410060f3b4eb1908200b15819d6321040123f0eb2c6420802c5604530c84100587416ea1908200b0e821d4321040162b023a864208024721d650c84100546c34e41908200b8880588321040143906b2cc22080263209739844100546412e730882008
  | 9 => 0x63181510051cc24c6302a200a5a8398c60544014d505318c0a88029a60a63181510043dc3ac6302a200a3b8458c605440147108b18c0a88029ae09631815100534412c6302a200a738158c60544014b50c318c0a8803169d863181510070db20c6302a200e186418c6054427ca6c2318c0a880296a0863181510052d41ec4302a200a5983d886054401c56c9b10c0a88038a193621815100725b1ec4302a200e4863d886054401c9507b10c0a88039260f62181510051d424c4302a200a398498860544014b507310c0a88029660e621815100535414c4302a20087b87588605440147708b10c0a88028e21162181510052dc1ac4302a200a588358860544014e702b10c0a88029aa186218151006353b0c4302a200e2b641886054401c50c8310c0a880392d8c621815100724318c4302a212e63611886054401c9706310c0a88039220c62181510052d43464302a200a58868c86054401c36c9190c0a880386192321815100725b1464302a200e48628c860544014b50c190c0a88029621832181510070db2064302a200e18640c86054401c96c4190c0a88039218832181510052dc1ae8302a200a58835d060544014d704ba0c0a88029a209741815100539c0ae8302a200a3b845cc605440147108b98c0a88029ae09731815100534412e6302a200a73815cc60544014d505a18c0a88029a60b43181510053940c86302a200a718190c60544014b507b90c0a88029660f72181510051dc22e4302a200a38845c860544014b706b90c0a88029620d721815100539c0ae4302a200a3a841c8605440147308390c0a880296a0f42181510052cc1e84302a20087b8750860544010f10ea10c0a880296e0d42181510052c41a84302a200a738150860544014e102a10c0a88028ea1232181510051cc2464302a200e1a848c86054401c3309190c0a880392a08321815100725b9064302a200e48720c86054401c9484190c0a88039250832181510062b31ae229e8200964825c453d04012e100b88a7a080217a0f755834100627328e4b1c8200c4d651c9639040189eea392c720803131d47258e4100627c28e4b1c8200c4c851c9639040149904b1ca720802932096314e410068629ce5a1c8200c8e635cb439040143b0c2988720802932096394a4100526412c62948200c9a631c14290401954c4382852080293209650ca4100647bb2841948200b8880508329040149904b1ea3208021721d635464100526412c6a8c8200c4e631c9519040189ac6392a3208031698c70546410062cb18e0a8c820085e83dd5609040123d07384cb2080323ddb7258e4100687ba8e4b1c8200d0c751c96390401a1f0a392c720803432147258e4100687328e4b1c8200d0d651c9639040183aed31ca720802c32096394e410060ebb4c629c8200b0c8258c539041507f
  | 10 => 0x312a200a68805c4625440149d07380c4a88029360e70189510062639ce0312a200a2f845c0625440145908b80c4a880293e0d70189510052641ae0312a200a67815c0625440145d08380c4a88028b610701895100626398e0312a20085c835db42544010f100bb684a88021721973d09510042fc38c7a12a20085d8718f425440189ce631684a8803135cc62d09510042f41eeca12a20087a80dd942544010bd0db9a84a880217a1c63509510042e438c6a12a200c4f731894254401898e631284a88031518f715095100632316e2a12a200c54631c542544018c8c438a84a88021ea1b70509510062c31ee0a12a200c6862dc142544018b0c638284a88031a18870509510043c402ed992a200878805da325440126902ba464a8803079d0638c9510060eba0c7192a200c2e7418a325440185ae831464a880307e12768c9510060e424ed192a200c4c829da32544014b100bb464a8803079da748c9510060f3b2e9192a200b14815d2325440183cedb2464a8803079d8648c951006273b6c5192a200c4e7618a3254401c1ec831464a880383190628c951007073a0c5192a200e0d7418a32544010f501bb264a880296a03760c95100527410ec192a200c4e821d83254401838edb2064a8803071d8640c9510042f434e4192a200a4e869c83254401898ed39064a8802c3612720c951006263b6c4192a200c4e761883254401c1ec831064a880383190620c95100527400c4192a200c4c7690832544014990ca1064a8803131d9420c951005a240a84192a200b488050832544014d50531ec0a880386d9063d81510070c320c7b02a200a5a8218f6054401c90c7b16c0a880296a0e62d815100715b20c5b02a200e286418b6054401c96c6316c0a88039218c62d815100725c18c5b02a200e488318b60544014b50d196c0a88039218a32d81510052c43065b02a200e48620cb605440183ec939cc0a88030719273981510060f3a0c7302a200c1d7418e605440185ec9394c0a88030b192729815100627b1ce5302a200c4c639ca6054401898c6b94c0a8803139cf6298151006173a0c5302a200c2d7418a605440189ce6314c0a8803135cc62981510042f438c6b02a200c1f7418d6054401838e831ac0a88031318f725815100626318e4b02a20086e87189605440185ee8312c0a88030b1d0625815100627b98c4b02a200c4c73189605440147708b00c0a88028e21160181510052dc1ac0302a200a588358060544014d704b00c0a88029a20960181510051d424c8302a200a5a8399060544014b307320c0a88029aa0a641815100534c14c8302a200a5b8359060544014b106b20c0a88029ae09641815100534412c8302a200a738159060544014750c320c0a88438cd8464181510070db26c6302a200e1864d8c60544014b505b18c0a88028ea12
  | 11 => 0x544014b307ba8c0a880296e0d54181510052c41aa8302a200a5b8354860544014b106a90c0a880307d92739915100617b24e5322a200c3b649c2645440185ec9394c6a88030b1927298d510061db24e131aa200c38649c2635440143f08b18c6a8802872116318d5100527c12c631aa200a4c8258c63544014b700b18c6a8802962016318d510050f424c831aa200a4e82990635440149b05320c6a880296a026418d510052cc04c831aa200a4f82590635440149904b20c6a880296e016418d510052c402c831aa200a1e86190635440183ec9390c6a8803071927218d510452ac0ee831aa200a4e829d0635440149b053a0c6a880287a127218d510050ec24e431aa200c1e849c8635440183b09390c6a880287e117118d510050e422e231aa200a4f825c4635440149904b88c6a880296e017118d510052c402e231aa200a1f845c0635440143908b80c6a880293e097018d5100526412e031aa200a57815c063544010d904bb686a88021e20176d0d510062631ce5a1aa20086c865cb4354401898c6b9686a88031518e7190d5100437416eca1aa20087a80dd943544014d50131ec4a880383d9063d895100706320c7b12a200c1f649ce6254401838c939cc4a8803079d063989510060eba0c7312a200c3b649c26254401870c9384c4a880316d8e70989510062c31ce1312a200c58635c262544010bd0e31ac4a880307dd063589510060e3a0c6b12a200c5863dc162544018b0c6382c4a88028be11621895100516422c4312a200a4f83588625440149906b10c4a88029ae01621895100534402c4312a200a4e82dcc625440149d04398c4a880217a0e70189510052741cec312a200a4d839d8625440145d09320c4a880293a0e641895100526c1cc8312a200a6a8099062544014d301320c4a880293e0d64189510052641ac8312a200a678159062544014d700b20c4a88029a201641895100517430c8312a211e27611906254401c1ec9b98c4a880383193731895100707b20e6312a200e0c641cc6254401c1ec9b18c4a880383193631895100517424c6312a200a2d8498c625440149d07318c4a88029aa02631895100534c04c6312a20086f8758c625440145f08b18c4a88028b211631895100535c02c6312a200a688058c625440149d0c318c4a8803139d8631895100707b20c6312a200e0c6418c625440149d073a0c4a88029360e741895100527c1ae8312a200a4c835d062544014cf02ba0c4a88029ae01741895100534402e8312a200a2e84dcc625440145b09b98c4a880383a13731895100706c26e6312a200c4e871cc625440189ee8398c4a8803135d073189510043743e86312a20086d87d0c62544014cd03218c4a880299606431895100517c22e2312a200a2c845c4625440149f06b88c4a88029320d711895100535c02e2
  | 12 => 0x316dcc70584520062c398e0b08a400a4c825ce60148010b906bacc3a100217a0f75583420042e41aeb30c840085e83dd5609080143d0c29886a100295a0f75d854200539406ebb0a840085c835d461508010f100ba8c2a10029520d751854200538402ea30a8400a9683dd06150801c28a6218c2a10021720d75d81420052c41aebb028400a5a83dd46050801c30a6218c0a1002b2a0f421814200692290e2a108400d28521c142108014390ab9cc919003075da6494e320050f40cc829c6400c1e645c4538c8012b100b88a719003079927014e320060f324e72946400a558114e618c80129904b8ccb190025620171996320050ec0ccb3246400a1e80996648c80183ccb38cc9190031399672192320060ebb4c9294640085f865c4528c8012b100b88a5190021761a7014a320060f3acc9b0c6400c9a649c3618c8014ab0332cc3190030799674186320060f32ce9b046400c56659c7608c80183ceb320c119002562017114c320060e29ce93106400c4d7614e420c80129d0f29a841900253a1c5350832006a3298e2a106400d44531c5420c801b0c8638a84190036110c7150832006a5298e0a106400d48531c1420c801b148638284190036210c705083200686ba4a71906400d0d7414e320c801838e829ac0190031514c7158032004a7404e5b28640094e809c8650c8012b100b88ca1900253a0b75590320060e32ce93106400c1e759d2620c801a1ceaba4c419003435d5749883200687b2ae93106400d0c655d2620c80131902ba4c4190325361e629483200586c24c5290640094d87988520c80161b09310a41900256201711483200626bb0cb2106400d46521c5420c801a88a438a8419003529487050832006a4290e0a10640094e87d95420c80129d0e32a841900263a1f6450832004c7438c8a106400e0c65191420c801a8eea38a8419003511d47150832006c3ba0e2a106400d46851c5420c801a8b0a38a841900351d947150832006a2328e2a106400d87841c5420c801b0ec838a8419003611907150832006e038ee0a106400ccb761c1420c801a96ea3828419003521d47050832006c5ba0e0a106400dc3711c1420c801b80e2382841900352e147050832006a4428e0a106400d4b651c1420c801a90ca382841900362d907050832006c4320e0a106400b8481508420c80171100a1084190029560465184320060e328e8b006400c54651c5600c80183ced3a465a880293a0b760cb5100526c34e4196a200b0d849c832d440149d0131065a880293e19420cb51005a240a84196a200b488050832d44010bd0539cc1a88029320973983510042ec3c65306a20085f870ca60d44010bd0db9aa8a880293e0d54189510052641aa8312a20085e86dcd52544010bd0e31aa4a880313dcc625495100626398c4a92a200a5a83dd460
  | 13 => 0x400400800c00405008800003004001801400800000000400002000800000000400c0100040600000200400c801001400c01000c00000006801801001c01000002000c00401c00000000000400800000805c04801400000401c0140280000fc00000c01802400400c00000800400001001c08000800000805800001000c0140040080000240b801400000000000000000400001001401400003c00c00c00001000004400001000001401400000401000800003400003c00c02000000002802c00004800001800000800000400c00800400001800400800c0040000d000003403805400400403000003403000000000800000800000400802001c00800000004401c00401000402800001007400804c00400c01400400c03805400803c00000400000400400002802000400000402400002000c06c00400003800000000c00400000400c00400800400400000000000000c00400403c00800400c0340100400c800400403c0140000340080280000000080000100040000000280040000d400400000001400000000001000400400000003002c00000001402c00c02c01001000400001000000800401802802004800000003400002000000000000000000002401400000000402000401400c03c00401000400400400001c00801802c00000405400000003401801401400003400800800000801401000000401000800403c04c01400c02c03800000400000002800c00000000000802c00400c00800003000400800801000001c03800000000400000c0080ac00000001c00000c00401400801801800000400403400001c00003800002400c0080d407000003001c0000080000600000000000100040000300040240240040040140340480240000480040580000180bc00400000808c03c00001c01402c00400400000c00800c00000800816400000400000000001800001000801400801400000001000400408000400401000800800001405401000802800402c01898a5396c6aa0021e2017198a5300436412e3304a60da4e821ce6214c0185ee8392c2298030b1d0725845300627c18e4b08a600c4c831c96114c018d0e5b82c2298030edd070584530061c3a0e0b08a600c6b721c16114c018d0e4382c22980316a0c70584530062cc18e0b08a60094c825c453d0c012b100b88a7a180293a085398b4300526c30a73168600a4e85dce62d0c0149d0e29cc5a1802936045398b4300527400a7316860086c825d661d0c014ab0229cc3a180296a0053583430062632ce5a1a860094c825c45310c012b100b88a6218034314d72d0c4300626298e4b008600c54531c56010c010f100b8cc7290031398e72d0e520042f418e0b0ca40085c835c6609480183ee839ac229003071d073584520062c39ee0b08a400c3b741c16114801870e8382c229
  | 14 => 0xb68a29970001830df9bcb72a6623200006807d30aa358ea80580003fa9f01b92215f00008920580027d3650dd37390f80e0089aab8eb433002d082730dada8bd2001c48ae86123326800027d9160a68001968000001fd0002ce0002040002b98000000001a61d514ca42304000000000000000129a690000000002b2b3104f8532f6a522b82ac0000000382deb7707c1e29cb80000013a8000000000000001e7aa406c8cf1cc80000000000026b8f288ea2fab6b7a26a80031d80000000d8000000000921b0988b90adf39580024eadb1eb230a819ee1e3b3c9899ab28498703e82780005b0540fc00029cb210000c205da4193124a90433b35b0469e01799b5ad11279ee82629a39999f91e0000aa94a22600014d8001c2ab58001940618000001bdaa381807000011b82a93e838b8380000000038b0331210002ff8000e41e891aa6a05b8db1c880033094b0003468bcb1e0edb76a7480000000030103380002d00036780000016f2810a00002cf8002ca8000a70002870211a48db9a82a73828000038c017e82c9b02d59e4a2b8003778001778002508ea1fb81303bae69ad36196ca4b1649da0000000002940000000000000002f100000032b00000000000000006911088e17d3488000002088c421a0002dd8000001712740b80000000ab95bac39f1a8907b0ca0002389800de0159382408000fb32480022a9db84480000000036912300015600018a8002b780000009009a8e399e8001f88000000000000000d58ce11a00000000029e80000000015d0000000733598002e21d880000038580000000000000003428d0ddadb80036f8002952328000000000000000a580025d06208023f8000002cb8d80002e59531338000de9b81ba20e0000958003388f800018684c0003438000f527011ca1c8000820000000001fe80002e96822f32b8790000001c20000000001ea0002b88001993978b98001bf0000650000000000000002540001a380023c8003878f989f800000259a8a14380000023689c8010003300002932b41f10000000b38940002429b521a8002ad33d2f223c1928000000000000000000289002220000000f600018c8000fa8002bc27e1a1000000246216ade2648002ed93636eb608000002e1800000382000000001c03001400800000800001401000000800003c01000000000400000800800c05401800005402c00000000000000001c0280080140300080040000080040c000800000000400400001000c00c00c00001001003800000400001804c0000000040040000000c002000400804003c00400003000c01000006800006000402c01000c00002003402800403006000803c02401800007c0a804400403400000000400800400000800403400001000401800401401c00401400400800000c00000002400400000401
  | 15 => 0x29b84da5c8420000002c5b74b083689f8252b4f8858000312af165a010001d126380000000012900022703d0880002c31f785f8000000001e21d59c089b2b5048a7c33634ab34004b968d9234a18ac8a5aa1180036282417010911f07b80000014a8d12ce8000002c82580499e12bcaa83569490562d98ef9df1e30ae06086fb5b80080029c06585f0908372f2aef9b489c00000037d000156a3ba4880000000600020a9be00000024f0000001b1000000182b2008d00000c0000002a8b1b9f700000003f0002850cc398109ae99bd000047000000047a00b6d0002049948001c7ab380013a2e38001a90000a8b53a882628c6b8833800029680025395c073b1b00f0000000002beaab0000d021b15380038f2ae8000f58c7800000000121a789bc0930002e498400021d00000016d0000002838f100000000000018d800000223000000000388b86ac988c27fb058d61e8078326a3d99da6b221138b338c30c98f087128f8e2345b9ab6b2a9352b1c18a241148ab187e85502b33c2d32f63422d038634b0e9887976b44a738f220d9501e6a548f7b02a8091201132094e8ce80001b0002f3ac197592f95f8fe2e918f81215799f1b90000000aa0483819601db0e18ff02982802f1f006722480a219a44043b01b4c346341a7b19aa5880500010cb3192a2cf2da21db91ae32eaa501081af0e301897da9713991500280bb8727228a9558bc25f9f900000000012eb9a13db2e8000000000000002d69fc0001de2ca189116800146a3d1c001508ab142069c42a980000006400026593400000000000031838c3440770172e813f18e2090001718002128000000fb80017b98520f34db64000000000335952b7aa7b913011a71b2c99a3330000753658baaeeac11350002c7b5721f80000002189515e86a3098000098001b63068001e0b963942b48000001178000000000000be9cd00033704d0002cca1e8d5099026a252b72e88000a801a0002772dc8002b92920e880000000002029e34d168a3f1b8ab09f42a53970000000000000000830000000328000000003230418433951efa10b2411b0001a501081e8be34a2ba1738022ba9f6b5ab830d69881bb22037c9eab5d9922780003992c00002eb9288b20000000000b29a2a15b6e24b85e17b09a1248749ac098a91292a4001e09795818080000024f8f700900000000000010a80000031ca7f2af80005000035c0ac2f890e80024c9d637402d8000000000000000b100014200000000000024d8b1b25000222800000000004000100800145101800228800355b39abd9508f88001e5a17b36b0b80017f8002ab8b60000000000d38000c90000000002143581a9af0ac2800000000000016a9d89489988f13080018600000038c80009100000818c1073472d81d4afea0d00030080e8001f31612360
  | 16 => 0x7580030a23394c35c80000023e80031103c28580023780025610500000000000000000004f000193aa28720000868000c5b1923710b00001d80009380000003a0000000ad02080022c2a78740001359fa0d20c3b153483128001408d9b050002180000fd0000000000000ee0000000000001100000919010d32c417223800000000000032a2492862d92282d40001a70000002c08adb280002988002a08000000001b316283200020312b24330d0400001bba9380029b00000024e0f31fc8002fc181945913b21b58a7eb5312cab319326885287aa1930303cb5198b81022d9d680f961b40b620000000000000002f30002060000003390000003680000000e90002b60000000ab1789f4b090000bb00007f87f1b1a468000000000c1a5b0968000238002a100000000020b12e000225b0200026100019100006b00016b99180028f0ee84ea4c00004b23e0001620000003920001d3b750002fb00015e0413719a20eb00005d31207790a28204a01425c2828000af8b78000000ef2ed1adae0a4980007db51000288a900662e62dfaf984907ca67b0ea75a1e290b0c02c38e23b26c31d37fb2206e98229ab5436ca9993681937993934e394a768f4876007906a0186e0849cc36727cb5f0a9b698568eba751ac9228e10e509296696e1c1800269a3035e13fb4bb7b0000002fba102310a20001fb06d2452fa15d8e700035537c0230df16300000019c8000000c700027996900000000026e8000002ea0000f68001978da0001b39d431f8002cd00000020234f26400000032980000009e0000001c30000001048000001678588000da800000037b1f2ff23526d2f720e8a18972e7289a620668c120f8799cf9c938a2fe11c000000088b3500000005200037ea59314b7080031731180000024715aa23a5db9883d8002d71c71740002c4a2084086306b80000000022e1d00148360002c900000000000014b91f95500000000000014f0001838f3b4535d00010890e2e11ceb1080014011e81c0000000001f080001caec1f21ca0000001c580023901f2619dc1318fc9d700006280020980000017e0000001f9a1f00000038b8000f40bdaef0a39f61ae1eda242831dc80015208b1c9b8900031799537db378000000461329d83660b09201e91c80fd8ed2f402e32932f2d60cf8698b70309061fd8000000e6b47a4a1d0800245b060001aa18d0000002a300014780033f800000267025acc2eb3199c13808002c60e61e43160002dc1370c518b26f0000000e09440001481dd0f91188001d9817b508000368bf00000007699814737f378322800000000000392b600000000cb00003528d81f8002730000000000000000002f938d00019d000000000000334b188000000440dc8000002948c4a2ca8b30b1e1b8a9ff33a3790d7167327323a9836115900
  | 17 => 0xd18a08c28e81aba5b8c88ac9642c52fd0002acb2d389b6da47aaa32619b97c082870a569588001a794f90280003000000037600016f80033a80000005e8000002bd1d2357a0c883a2b1d780025e87e00013338480000034e80004e0000000ba13ba0536a23a0b935e80022a2990002559848000001a32b200028c946295a120af2fd8002bb8578d880000018e8000002ae2f5b038450002d18002a180000019e33b96d86f2438a60a520800000000035236c38f9d9000050963aaa8000000000000002960001548000000000000000a494e000195a5f2e500013b11d0000000128cd81d0fe9fa87280009baa4965039325a3a9428001d2b801be80327611739000026000005a00000000010baa00000459f28000000228000a40000d096a3938c08000000001c380000000000026e2f482b80035480023180000035a00000000015b2d3a2d03e000151b6b84aa03b7b8e580709f29190393780000031eab0207907a8e0789b78069261af88f97c9dd9a180005494318780012388425791832c1ef04b8000000000002a62ec911a290002e40b58000000001f392bb561e50000000000f00961ebb2a9df8870001a684c800287ae2b789b70b89d3063b712cdb3d9782a5880905ad7b048f1add349a511b42e79cb1a00580000139ec3843758000000290000cb8002d2277a0712d80013ca978001140221bfb2d81980028032f80000009d0559208d4157226881b1a0001c600003480013492c0000a30002170000003730810000852c20018000000002a692f2f03720d1ad29cf11900021480028e80033f09830e1b6a6538d8c80cc915a0b8001ce12d313248363a4d19010d111000126941b1aa710002e02bf9302d530888617700014d33e1498a9000000000031a2e80005c21300002a0001c500019897280031390c19080036f00007180000000013c12500000000027933e9663630002028001ed1540000000000002be2fa9c687a1ff960a5e33280003b28412aa572f8159a278bfa6f8000000250b4a1116b38127a10d8d49a4307a0a3410b006d8ff88a0a795a141253199b502bb2f79b9a552518b508b80cb4037e11980017495c85900003992800017900000006019b3701510d781a9cd868800051b8522180014486c35f86a98100000000005731680030f80d2bf06788985380028ba1b8000000002138000000000000000358002a23278b41b2aee00013225a0000000001858fa36aa9d1da8000000000000002f1a3417f1deb100000000000000000000003649b20161020e4b9316a80000000000000000000019c2cb0003493668000002708000598e00001258000000001eca1c0002869ca80009ead480000018f2609ba96c00000000000011d9e72160000001e980000021500013d22997a0001a880010303a8648002669fe05a8d29709f5
  | 18 => 0x2d888cb321148ec29f800000328a630000000000000e78001a596e8510dc3071760b31271ae90f0a108d80000aa7280034ca44a6dac70002f512432e0c602480019630c93e17a8ec8000bb9a0a6c80030f2b105c842a8c09d9752fcb429f5a7a9129e62ad9730cd169a0c00b3910e2b158003590caac682fa399
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x401115981ce61544410064160c7298551104015119398470544410060c990805c453cc401304926045310631004c42418114c418c401a206220151105310058824951104604c401904842097114c3100644e10805c4530c401910842017114c3100650e08805c4530c401940822017114c3100614990805c4530c401850642017114c31004c42418114e410c401304926045310431004c42418114c410c40123290a185310721004d0241811d43208401b0032201511042108c892498614c41084013049361c5210421004c1a4e801484108401605962143210421004c1261750c8410840130498594321042100485245849ca6394001414916127298e500050365282dd8329400184776205420ca5000612dd880508329400104c9261e6390650004832498798e419400101d97a0a6390650004892498198c4194001604926066310650005842418198c41940012159898e711065000581e5832104219400188476205420c940005a0241420c8615000128491612620cb3000485e598114c41cc001304926045310730004c42418114c41cc00180c642097114d3000606190805c4534c001248906045318930004912498114c614c0012449261c5318530004942418714c614c001815871d05318530006051d98114c414c001304926045310530004c42418114c414c0016059114c621053000505a4f651c5640800148692dcc71590200050524d851c564080014249261471590200050c241851c5640800160491592520c8200058124564148320800160491592530c820005812456414c32080019088414d700c8200065014c815c03208001a0765205640c8200068119481590320800160a90dd5640c8200062121c815903208001a0785205640c82000681214815903208001a0695205640c82000681654815903208001a0775205640c820006811d481590320800188887201640c820006a020480590320800190875211700c820006501d4815c0320800140f9759032d442000581245640cb510800141491590735442000509245641c9510800140c9759032544200060321d640c951080016049159032544200050c245641c15108001c09640c8705442000505245649ce500800142491592729402000603e1d640ca500800160491590329402000581245640c8500800122692a18531061000413261631c951040012149858d511041000581249635444104001a0563209511041000485658835d44104001a056520963104100848c2418614c410400148597188321041009c942418614c310400104c9261a73940100050565a7310650040018497620963140100a44ce61719045004001510935c64114010005482497190450040011509361c41140100054424d871045004001c117658c4114010005c02496310450040016119614c41cc010
  | 1 => 0x278004e002450a020019c7e820029ca80057a5c64141d800007a00174009930a48444316aac207851874da1e5f2881cbc1b890b4012126038c5531f46041140c44a3a4983070644e1187860440ac340648178c63d5886ccac025ab44cb76123c8ab82aa291268418802e7e608f8064d6218900531725986001988c2495283181036520bc92b409824b629548342a72372a89e9408aecb2392fac97e9f0f9d13a0063800fe51002c00000000015c002b8291cba4d80166bd00218f86913860945c4d0d56c73108006858000011a05002b0f2005003d180000000000000004042408003860640c44100000291c50808800041424002804081c3400a8280c00003400043c0000d0ac541404001950a0000c08dc001c6498049c48347850100008840140e94e0c725845300506251831c16114c014489260c7058453004922418114e62d0c0125090604539874300606990805c4538c8012509060453986320048324981996648c8012189060665992320049124981996618c80125090606659863200550241851c5420c801c0465190715083200702194641c1420c80125090604651843200505245849c8635440160491613731895100503652871cc6254401448905d0731895100603610731c06254401414915d0638c951005092457418a325440180f8420a768c951006059d8815d23254401604915d0628c95100503652821d8325440180c76612720c951004c1245849c8325440184476205420c951006121d880508325440123091612321815100584245848c8605440160994a08321815100582650720c8605440144897508321815100590245420c86054401852632017114f4100622dd880508329040104c9858c725464100512249631c1519040188776a07620ca4100622dda80d88329040180d7620963d46410040765a821cd519040180f7620963546410050365b831c9519040110c9858c725464100603618728c951904015089258c70546410050665a321c151904013049260453d0c41004c42418114f43104015059114e72d0c41004c12498114c4310401310906045310c4100541249811cd651040151090604735944100541a4b635c453104011169818d7114c4100641e4c825c45310401904932097114c4100641d8c825c45310401904632097114c410064820b805c45310401923822017114c4100648208805c45310401912932017114c410064464c805c45310401913632017114c410064418c805c45310401130906067394841006059d98114e321040131090604538c841006059d9819d6321040130492606758c841004c4241819d6321040131090604530c841004c4241811d4321040190575209739844100503a4b835db511040101f985da32d444100541249811cd5110401510906047354441004c1249839855110
  | 2 => 0xa800320e0810b000de0003920e24700100546b5080000a5331d4f600059d80084351b088770222c58b5262e4325243800ac0
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0xc8a3a0010000b08926080300180a9600069c01e480022000030118a2e01400000000100220018023b122c24e4192a20098028594a083218151004a0140c88a73968620802900a264c805c45310401481516c6402e22988200c049d890604538c84100600cec493033ac642080301276241819d6321040108254b06394c2a88820094028993984705444100480942ca505bb06528002204a2662639c441940014025130e3a0a630a6000c011d8926045310530006020ec483022988298002600a064453188414c00140253b2a40ac81904000a8028195205640c82000540541ba902b20641000300487245640c9510800160050ac8190e0a884000c01e1c91590329402000440952b1904a888208002204a2658835d441040012025132d398832802000d005d89258c4114010
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x6
  | 2 => 0x4e
  | 3 => 0x138e
  | 4 => 0x9ce
  | 5 => 0x168e
  | 6 => 0x20e
  | 7 => 0x140e
  | 8 => 0x24e
  | 9 => 0x144e
  | 10 => 0x28e
  | 11 => 0x148e
  | 12 => 0x3ce
  | 13 => 0x15ce
  | 14 => 0x58e
  | 15 => 0x18ce
  | 16 => 0x28056
  | 17 => 0x28216
  | 18 => 0x20056
  | 19 => 0x24056
  | 20 => 0x4296
  | 21 => 0x20296
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 72
  | 6 => 2065
  | 5 => 5112
  | 4 => 1846
  | 3 => 201
  | 2 => 26
  | _ => 0
def gbR (k i : Nat) : Nat :=
  match k with
  | 8 => packedAt gbK8 (i*15) 6
  | 7 => packedAt gbK7 (i*26) 17
  | 6 => packedAt gbK6 (i*37) 28
  | 5 => packedAt gbK5 (i*48) 39
  | 4 => packedAt gbK4 (i*59) 50
  | 3 => packedAt gbK3 (i*70) 61
  | 2 => packedAt gbK2 (i*81) 72
  | _ => 0
def gbH (k i : Nat) : Nat :=
  match k with
  | 8 => gbHint (packedAt gbK8 (i*15+6) 9)
  | 7 => gbHint (packedAt gbK7 (i*26+17) 9)
  | 6 => gbHint (packedAt gbK6 (i*37+28) 9)
  | 5 => gbHint (packedAt gbK5 (i*48+39) 9)
  | 4 => gbHint (packedAt gbK4 (i*59+50) 9)
  | 3 => gbHint (packedAt gbK3 (i*70+61) 9)
  | 2 => gbHint (packedAt gbK2 (i*81+72) 9)
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 8 => packedAt gbK8 (16+((h/1+packedAt gbK8 (15+(h % 1)*1) 1) % 2)*1) 1
  | 7 => packedAt gbK7 (2040+((h/24+packedAt gbK7 (1872+(h % 24)*7) 7) % 125)*8) 8
  | 6 => packedAt gbK6 (84661+((h/688+packedAt gbK6 (76405+(h % 688)*12) 12) % 2726)*13) 13
  | 5 => packedAt gbK5 (267528+((h/1704+packedAt gbK5 (245376+(h % 1704)*13) 13) % 6135)*14) 14
  | 4 => packedAt gbK4 (116294+((h/615+packedAt gbK4 (108914+(h % 615)*12) 12) % 2680)*12) 12
  | 3 => packedAt gbK3 (14606+((h/67+packedAt gbK3 (14070+(h % 67)*8) 8) % 242)*9) 9
  | 2 => packedAt gbK2 (2154+((h/8+packedAt gbK2 (2106+(h % 8)*6) 6) % 41)*6) 6
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfffffffffffe003ffffffffffff0fffffc3fff
  | 1 => 0xffff8007ffffffffffffffffffff0ffc3fffff
  | 2 => 0xffffffffffffc00ff800fffffff18fffc63f
  | 3 => 0xfffff801fffffff00000ff800ffe0fc7f838
  | 4 => 0xff00000001ffffffffffff00000ffff007ffc0
  | 5 => 0xfffffffffe00000000000000000ffffff80000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0xab2db4da9656101cb65b5565b59076b5dc1adb
  | 1 => 0x35568c05aaaae2e958ada6cadaa70b5c29ed6d
  | 2 => 0x809b596f4d3d75440f3030b36f4bb18af6c636
  | 3 => 0x20e3ee7181cfb9be6200c4fc038dde0f477838
  | 4 => 0xc600704601f1de378fc6f8200c0efde007b780
  | 5 => 0xf8fc7f87f001e0380c0700c0700fefffb80000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 63 gbPos gbNeg, 0xe888a080c8888080e888a080c8888080e888a080c8888080e888a080c8888080e888a080c8888080e888a080c8888080e888a080c8888080e888a080c8888080, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_15133
namespace PEqualNP.Outside.L_meta_15133
open PEqualNP.Outside.L_meta_15133.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs2_1_0 : Interval s2Atlas 1 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_1 : Interval s2Atlas 1 0 1 := bs2_1_0
theorem alls2 : ∀ k ≤ 1, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_1 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_0 : Interval s3Atlas 2 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 1 := bs3_2_0
theorem alls3 : ∀ k ≤ 2, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_2 i (by omega) hi
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
theorem bs5_3_0 : Interval s5Atlas 3 0 9 := block_range (n:=9) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 9 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 14 := block_range (n:=14) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 14 := bs5_4_0
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
theorem bgb_2_0 : Interval gbAtlas 2 0 26 := block_range (n:=26) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 26 := bgb_2_0
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
theorem bgb_3_192 : Interval gbAtlas 3 192 9 := block_range (n:=9) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 201 := (concat (concat bgb_3_0 (concat bgb_3_32 bgb_3_64)) (concat (concat bgb_3_96 bgb_3_128) (concat bgb_3_160 bgb_3_192)))
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
theorem bgb_4_1824 : Interval gbAtlas 4 1824 22 := block_range (n:=22) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 1846 := (concat (concat (concat (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat (concat bgb_4_96 bgb_4_128) (concat bgb_4_160 bgb_4_192))) (concat (concat bgb_4_224 (concat bgb_4_256 bgb_4_288)) (concat (concat bgb_4_320 bgb_4_352) (concat bgb_4_384 bgb_4_416)))) (concat (concat (concat bgb_4_448 (concat bgb_4_480 bgb_4_512)) (concat (concat bgb_4_544 bgb_4_576) (concat bgb_4_608 bgb_4_640))) (concat (concat (concat bgb_4_672 bgb_4_704) (concat bgb_4_736 bgb_4_768)) (concat (concat bgb_4_800 bgb_4_832) (concat bgb_4_864 bgb_4_896))))) (concat (concat (concat (concat bgb_4_928 (concat bgb_4_960 bgb_4_992)) (concat (concat bgb_4_1024 bgb_4_1056) (concat bgb_4_1088 bgb_4_1120))) (concat (concat bgb_4_1152 (concat bgb_4_1184 bgb_4_1216)) (concat (concat bgb_4_1248 bgb_4_1280) (concat bgb_4_1312 bgb_4_1344)))) (concat (concat (concat bgb_4_1376 (concat bgb_4_1408 bgb_4_1440)) (concat (concat bgb_4_1472 bgb_4_1504) (concat bgb_4_1536 bgb_4_1568))) (concat (concat (concat bgb_4_1600 bgb_4_1632) (concat bgb_4_1664 bgb_4_1696)) (concat (concat bgb_4_1728 bgb_4_1760) (concat bgb_4_1792 bgb_4_1824))))))
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
theorem bgb_5_5088 : Interval gbAtlas 5 5088 24 := block_range (n:=24) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 5112 := (concat (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 bgb_5_192) (concat bgb_5_224 (concat bgb_5_256 bgb_5_288)))) (concat (concat (concat bgb_5_320 bgb_5_352) (concat bgb_5_384 (concat bgb_5_416 bgb_5_448))) (concat (concat bgb_5_480 bgb_5_512) (concat bgb_5_544 (concat bgb_5_576 bgb_5_608))))) (concat (concat (concat (concat bgb_5_640 bgb_5_672) (concat bgb_5_704 (concat bgb_5_736 bgb_5_768))) (concat (concat bgb_5_800 bgb_5_832) (concat bgb_5_864 (concat bgb_5_896 bgb_5_928)))) (concat (concat (concat bgb_5_960 bgb_5_992) (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088))) (concat (concat bgb_5_1120 bgb_5_1152) (concat bgb_5_1184 (concat bgb_5_1216 bgb_5_1248)))))) (concat (concat (concat (concat (concat bgb_5_1280 bgb_5_1312) (concat bgb_5_1344 (concat bgb_5_1376 bgb_5_1408))) (concat (concat bgb_5_1440 bgb_5_1472) (concat bgb_5_1504 (concat bgb_5_1536 bgb_5_1568)))) (concat (concat (concat bgb_5_1600 bgb_5_1632) (concat bgb_5_1664 (concat bgb_5_1696 bgb_5_1728))) (concat (concat bgb_5_1760 bgb_5_1792) (concat bgb_5_1824 (concat bgb_5_1856 bgb_5_1888))))) (concat (concat (concat (concat bgb_5_1920 bgb_5_1952) (concat bgb_5_1984 (concat bgb_5_2016 bgb_5_2048))) (concat (concat bgb_5_2080 bgb_5_2112) (concat bgb_5_2144 (concat bgb_5_2176 bgb_5_2208)))) (concat (concat (concat bgb_5_2240 bgb_5_2272) (concat bgb_5_2304 (concat bgb_5_2336 bgb_5_2368))) (concat (concat bgb_5_2400 bgb_5_2432) (concat bgb_5_2464 (concat bgb_5_2496 bgb_5_2528))))))) (concat (concat (concat (concat (concat (concat bgb_5_2560 bgb_5_2592) (concat bgb_5_2624 (concat bgb_5_2656 bgb_5_2688))) (concat (concat bgb_5_2720 bgb_5_2752) (concat bgb_5_2784 (concat bgb_5_2816 bgb_5_2848)))) (concat (concat (concat bgb_5_2880 bgb_5_2912) (concat bgb_5_2944 (concat bgb_5_2976 bgb_5_3008))) (concat (concat bgb_5_3040 bgb_5_3072) (concat bgb_5_3104 (concat bgb_5_3136 bgb_5_3168))))) (concat (concat (concat (concat bgb_5_3200 bgb_5_3232) (concat bgb_5_3264 (concat bgb_5_3296 bgb_5_3328))) (concat (concat bgb_5_3360 bgb_5_3392) (concat bgb_5_3424 (concat bgb_5_3456 bgb_5_3488)))) (concat (concat (concat bgb_5_3520 bgb_5_3552) (concat bgb_5_3584 (concat bgb_5_3616 bgb_5_3648))) (concat (concat bgb_5_3680 bgb_5_3712) (concat bgb_5_3744 (concat bgb_5_3776 bgb_5_3808)))))) (concat (concat (concat (concat (concat bgb_5_3840 bgb_5_3872) (concat bgb_5_3904 (concat bgb_5_3936 bgb_5_3968))) (concat (concat bgb_5_4000 bgb_5_4032) (concat bgb_5_4064 (concat bgb_5_4096 bgb_5_4128)))) (concat (concat (concat bgb_5_4160 bgb_5_4192) (concat bgb_5_4224 (concat bgb_5_4256 bgb_5_4288))) (concat (concat bgb_5_4320 bgb_5_4352) (concat bgb_5_4384 (concat bgb_5_4416 bgb_5_4448))))) (concat (concat (concat (concat bgb_5_4480 bgb_5_4512) (concat bgb_5_4544 (concat bgb_5_4576 bgb_5_4608))) (concat (concat bgb_5_4640 bgb_5_4672) (concat bgb_5_4704 (concat bgb_5_4736 bgb_5_4768)))) (concat (concat (concat bgb_5_4800 bgb_5_4832) (concat bgb_5_4864 (concat bgb_5_4896 bgb_5_4928))) (concat (concat bgb_5_4960 bgb_5_4992) (concat bgb_5_5024 (concat bgb_5_5056 bgb_5_5088))))))))
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
theorem bgb_6_2048 : Interval gbAtlas 6 2048 17 := block_range (n:=17) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 2065 := (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 bgb_6_224))) (concat (concat (concat bgb_6_256 bgb_6_288) (concat bgb_6_320 bgb_6_352)) (concat (concat bgb_6_384 bgb_6_416) (concat bgb_6_448 bgb_6_480)))) (concat (concat (concat (concat bgb_6_512 bgb_6_544) (concat bgb_6_576 bgb_6_608)) (concat (concat bgb_6_640 bgb_6_672) (concat bgb_6_704 bgb_6_736))) (concat (concat (concat bgb_6_768 bgb_6_800) (concat bgb_6_832 bgb_6_864)) (concat (concat bgb_6_896 bgb_6_928) (concat bgb_6_960 bgb_6_992))))) (concat (concat (concat (concat (concat bgb_6_1024 bgb_6_1056) (concat bgb_6_1088 bgb_6_1120)) (concat (concat bgb_6_1152 bgb_6_1184) (concat bgb_6_1216 bgb_6_1248))) (concat (concat (concat bgb_6_1280 bgb_6_1312) (concat bgb_6_1344 bgb_6_1376)) (concat (concat bgb_6_1408 bgb_6_1440) (concat bgb_6_1472 bgb_6_1504)))) (concat (concat (concat (concat bgb_6_1536 bgb_6_1568) (concat bgb_6_1600 bgb_6_1632)) (concat (concat bgb_6_1664 bgb_6_1696) (concat bgb_6_1728 bgb_6_1760))) (concat (concat (concat bgb_6_1792 bgb_6_1824) (concat bgb_6_1856 bgb_6_1888)) (concat (concat bgb_6_1920 bgb_6_1952) (concat bgb_6_1984 (concat bgb_6_2016 bgb_6_2048)))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 44, 45),(inputs.getD 2 zero, 41, 45),(inputs.getD 3 zero, 37, 45),(inputs.getD 5 zero, 13, 45)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 2 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 18, 19),(inputs.getD 1 zero, 17, 19),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 3 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 4 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 37, 45),(inputs.getD 5 zero, 13, 45)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 6 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 22, 30),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 9 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 22, 30),(inputs.getD 4 zero, 3, 19),(inputs.getD 5 zero, 13, 45)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xe888a080c8888080e888a080c8888080e888a080c8888080e888a080c8888080e888a080c8888080e888a080c8888080e888a080c8888080e888a080c8888080
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 9 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 33 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) (SBf 1) :=
    slice_correct (ms:=fixRows 18 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have s2 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 2 zero)) (SBf 2) :=
    slice_correct (ms:=fixRows 44 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
  have s3 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 3 zero)) (SBf 3) :=
    slice_correct (ms:=fixRows 40 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds3 certs3)
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (3901268096 * 2 ^ 32 + 3364388992) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_15133.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,1]⟩,⟨.and,[2,3]⟩,⟨.or,[0,7]⟩,⟨.and,[4,8]⟩,⟨.and,[0,2]⟩,⟨.and,[5,7]⟩,⟨.or,[1,11]⟩,⟨.or,[9,10]⟩,⟨.and,[12,13]⟩,⟨.and,[6,14]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,15⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 9) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3901268096 * 2 ^ 32 + 3364388992) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3901268096 * 2 ^ 32 + 3364388992) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_15133

open PEqualNP.Outside.L_meta_15133 in
theorem PEqualNP.Outside.L_meta_15133 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3901268096 * 2 ^ 32 + 3364388992) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3901268096 * 2 ^ 32 + 3364388992) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
