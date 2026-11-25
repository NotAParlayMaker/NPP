import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_15931.Model
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


end PEqualNP.Outside.L_meta_15931.Model

namespace PEqualNP.Outside.L_meta_15931
open PEqualNP.Outside.L_meta_15931.Model
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

def SBf (j : Nat) : Nat := [4, 4, 8, 6, 7, 7].getD j 0

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

def mirrorSteps : List Move := [swapRows 84]

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

end PEqualNP.Outside.L_meta_15931

namespace PEqualNP.Outside.L_meta_15931
open PEqualNP.Outside.L_meta_15931.Model
def s0K3 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s0K3 (i*5) 5
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s0K3 (6+((h/1+packedAt s0K3 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xfff01fffe03ffffffc07ff81ffe07ffff38e3f
  | 3 => 0xfffe01fffc03fc07ff81ffe07ff81f01cf3cc
  | 4 => 0xf000001fffffc0007fffe00007fffe001f03f0
  | 5 => 0xffffffe0000000007ffffffff80000001ffc00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x12108144220484901058a2a288a8a2154534d5
  | 2 => 0xa4aa528a51a9292a2e055511554455aa928a2a
  | 3 => 0x88c954d294a3b20aceac19d4467511c0d8d34c
  | 4 => 0xce8d9b1d193223b377367061879e78831f03b0
  | 5 => 0xf0e1c1e1e3c3c3c7bc79e79e418610c1fec00
  | _ => 0
def s0Atlas : Atlas := ⟨3,rawDecor 62 s0Pos s0Neg, 0xccc0ccc0ccc0c0c0ccc0ccc0ccc0c0c0ccc0ccc0ccc0c0c0ccc0ccc0ccc0c0c0ccc0ccc0ccc0c0c0ccc0ccc0ccc0c0c0ccc0ccc0ccc0c0c0ccc0ccc0ccc0c0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_15931
namespace PEqualNP.Outside.L_meta_15931
open PEqualNP.Outside.L_meta_15931.Model
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
  | 2 => 0x7f01fff80fffe07fe07e0f83ff07fe07f44e73
  | 3 => 0x7ffe03fff01fff81ff800ffc1ff83ff818739c
  | 4 => 0x800003ffffe00001fffff0001fffc0001f83e0
  | 5 => 0xfffffc0000000001ffffffffe00000001ffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x108100881024000028a1104220842a28194a5
  | 2 => 0x2aa529946a548ae8f0548aa35546b415544a52
  | 3 => 0x4c954aa528d91a2b75410ce919d23950586318
  | 4 => 0x68d9b3464c91d34db9e7a8421ee710619e83e0
  | 5 => 0x70e1c3878f1e1c71de79cf73908421861f7c00
  | _ => 0
def s1Atlas : Atlas := ⟨3,rawDecor 61 s1Pos s1Neg, 0xaaaaaaa0aaa0aaa0aaaaaaa0aaa0aaa0aaaaaaa0aaa0aaa0aaaaaaa0aaa0aaa0aaaaaaa0aaa0aaa0aaaaaaa0aaa0aaa0aaaaaaa0aaa0aaa0aaaaaaa0aaa0aaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_15931
namespace PEqualNP.Outside.L_meta_15931
open PEqualNP.Outside.L_meta_15931.Model
def s2K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K6 : Nat → Nat
  | 0 => 0x90c00b800000296188c00f0040e803c00c00340101100002241a38a014c492a726090a2066ca993e2ce000e2050600e58000818419b000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x4817e53903bca7205794e40bea9c81dd53902baa7206fd0e40dea1c817e52902faa5206f90a40de214817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c535037c86a06f10d40bfa92817c525037e84a06f50940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40bea9881bf431037a86205f94840bea9081be421037884205f94440bea8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330efa1e61dc43cc2fca5985f54b30ef99661dd32cc2fca3985f54730ef98e61dd31cc2fea9185f95230df2a4613e548c2faa9186f552309eaa4617c548c2faa7187790e30eea1c617e528c2faa518778ca30ee194617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130efa1a61dc434c2fea4985f14930ef99261dd324c2fea2985f14530ef98a61dd314c3f66098778c130bfaa0617e540c2faa8185f15030bf29861de430c3ba86185f94830bea9061de320c3b864185f94430bea8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20bf28e417d51c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3107b88620f610c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20bfa8a41f751482eea2905f14520fa28a417451483de42907b48520fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53082fca4105f94420fb288417651082faa2107d54420baa8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dc8610fa10c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fb10a21f521443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf28821f721043e842085f94010fb88021fa10043ea20087e44010
  | 1 => 0xf5350af8a6a17714d42ae29a85bf4350b7a86a17bd0942df212857f5150af8a2a15fd4142be282857e5410afca6217794c42af298857d5310bbaa6215754c42df21885bc4310afca4216fd0842f721085bd4210bda84215f94442bea88857e5010afaa0215fd5332bf2a6657d54ccaf8a9997790f32eea1e657e51ccafaa3995f94332bea86657f548cafca9195f55232be2a4657d538cbbe87197710e32bf29465df328cbde65195f94632bea8c657e508cafaa1195fd5132dfaa2653f544cafca8995f55132be2a265bc544ca78a8997790d32eea1a65ef324cbbc64995fd4532be28a657f504caf8a0995fd5032bf2a065be540ca7ca8195f55032deaa0653d540caf8a8195f94c32efa1865dc430cafca41977cc832f719065dd320cbda64195f94432bea88657e500cafaa0195f94f41bea9e83bf43d077a87a0df94b41bea9683be42d077885a0df94341bea86837d54906fca720df54e41df21c83bc43906fca520df54a41dfa1483bd42906fca320efd0641fba0c837e50906faa120dfd4d41efa9a835f53506f8a6a0f714d41ae29a83bf435077a86a0dfd4941be29283be425077884a0fdd0541df20a837f50506f8a0a0df95041bf29883de53106bca620df54c41eea98835d531077c8620ef10c41bf290837d521077e8420ef50841bf28883bf41107ec8220ef50441faa08837e50106faa020dfd5331bf2a6637d54cc6f8a998f790f31eea1e637e52cc6faa598f78cb31ee196637e50cc6faa198dfd5231bf2a4637d548c6f8a918df54e31efa1c63dc438c6fca518df54a31ef99463dd328c6fca318f7cc631fb98c637e508c6faa118dfd5131dfaa2633f544c6fca898df55131be2a263bc544c678a898f790d31eea1a637f524c6f8a498f78c931ee19263f7314c7bc6298dfd4131be282637f540c6fca818ef950319f2a0637d540c77aa818cf55031be2a0637e530c7be8618f710c31bf290637d520c7be6418f74c831bf28863df310c7ec6218f74c431fa988637e500c6faa018dfd5321bf2a643be54c867ca990df55321deaa6433d54c86f8a990dfd4f21bf29e43de53c86bca790df54f21eea9e435d53c86f8a790df94321bea86437f54886fca910ef952219f2a4437d548877aa910cf55221be2a4437f53886fca710f794e21af29c437d53887baa710d754e21be29c437d52886fca310fbc8621fb90c437e50886faa110dfd5121bf2a2437d54486f8a890dfd4d21bf29a437d53486f8a690fdc8521f710a437f50486f8a090dfd5021bf2a0437d54086f8a810dfd4c21bf298437d53086f8a610df94821bf28843ef21087ec4210fb48421fa90843e521086fca010df54021bf29e81de53d02bca7a05f54f40eea9e815d53d037c87a06f10f40bf296817d52d037e85a06f50b40bf28e817d51d037e83a06f50740beaa
  | 2 => 0xd06b97f2fa1988b2280744e53a886398498741a2296314c89941407893b9be12e8594ca520caa052a1f34123ed492314141191815006e6a0621982d6734c81e80000000005e00000000000346000000754300010f8002b2308001f60dc4280026b4222753a18348233d0980019c000b4282000518800394666e800267136748a48d42689080e288266811288ef0ee7110117b4a634010205240000d594f07ca58400a91e800000028000000c000017e6b8551250006189f19e1424149e8000006980000009000000000000000338e40780fd01a4911409cce95a2c485c8a8000d2044fa9b20007f5110b3230108419f138e9cc1586150c000ba8780da4c8b88491c430c000000003d468808000000001064780004c96400000000000354a5c3792c0949651c1522027f80000013e00127036000438002140003e04d12a000058f69d90ae2154008d34069400196016738000003b04c0001c94c41344387b0000f46a80d0004d8001f7442000000e7000000c380000043c000000000000000048045c578a20646e05f21d2741012e26036a4ecee8de1e6574b62323d23c87498843c6ec3f8003187141d8003a6000000000009c85181e4fe0002094e3683b12b0924a00000026c4ca2f0000000005d8a994c0b60011e84518c5080d00023200047800194000000310006fc001133e496cf28e02b6208aa80038c000e18002c2920001953f60009402d000984608180d01813500049400000000000000571734f41c51f004018040000000c00004020040202c1403c0a0001304408004000203e0200e0200700c070000409c00000050100200c1e00801000000000100c0700c000180100007014000001b0240700001000110040d00c040540200c0200400010010300a014040080d00001008000080700003004021080702c00000220040200400010020041901400004010180100000014000102701009000130040100012010010680301c010000e02c01008140140106c180040500c00008000040001c01030000000201406008000100b00c0200c000000c00007000020140405c090040f000000280b0181100c010040103803078000000100c0a03802018010280300c0101000000010580002419000000280f060040340000006002fca5a1df54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877c5050efca821df94c43dfa1887de4310f7a8621f750c43cea18877e5210efaa421df94443bea88877e5010efaa021df94f42bea9e85bf43d0b7a87a15f94742bea8e857e50d0afaa1a15f55242bf29c857d5390b7c87216f10e42bf29485bf4290bde85215f94642bea8c857e5090afaa1215fd4d42efa9a855
  | 3 => 0x26e21a91ca8800520000002442429f811a8f1ee534001e00e0000d0974000000000000009d93424304a7f0001703a200000047000515379042469983e1ac1da3fd3205540c0bcd7a4d0b00b0859ea4f601d001a71f4000ab20c000224001140005dc001f400075000000472000d811c262a291780027e8ed118004567e89200002a59d2a8cc236670000242909c0cd8304f2a4d0584315004ce08000a49608f8003be2910c801014000b32913bc000b70980c665c000b9528000838001f82591500f018164819292102105c09415a424460bd00013c001eb1c6000970ea3ae0011384b000011428001dc14c000003de000d480048a000b900029492cd996a31200100a9830876c0295f244000de0003c6000b18000000006d985000000fc98b02e000220002ae8fd0d87e00064945a5a14ea54111c04d2628880191201e848a8749e37d039600b80009e0da2f2000000001ba0000020f39e7b85b02a44c0000000041c570d215831c594a194123c790ea8c71cca2464a20000204321350000000027c004918000620000011ba3438400cfc19a4c64083c81d0004e0d68b04203c4ee0d20b4254000d30665e00025d000000ff83800c5783598d00014066800288000001f00008b8148002f4448c98733623612b8001809f51d26d0fa97c8e97e41a8b45d9c803e4bc9b8001fc930c0800000220b681214c500e59d009c050470cb2f8a11161b73cc17514a1c36c394eb0001640840492d3329c4288e146a3587e91a51a0005a8ba0000b87b09e06a550780000ac1510d2360007b00008b000000000b74f0854000a50007840006a4bc728f3826000445470760008944e0002d22c4b78000002b0000b44481c80da8324e000640101268203605f1f20000028c1b251c071bd304848dc90c1564aced19f31e1306e0eb0681
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x1518825f63546209718d518823e64951209798e544825d63951209d9865448275619512097d8d544825c63551209dd85544827461551208f994544831f54d4d20c7153534823e6494d208f592534825e6394d209d98653482756194d208fd91534823c6454d209dd8553482746154d2097994534831f5414d20c7150534833754d4520cd153514835753d4520d514f51483375414520cd15051483575314520d514c514826e65c8520d914721483645148520d9146204825e63d50209758f540827661d50209d587540823d65950208f990540825e63150209758c540827661150209d584540823e64d4c208f593530827661d4c209d587530825d6594c20c7952530831d5494c20c7951530831d5454c208f990530823d6414c209798c53082766114c209d58453083365494420cd55251083565394420d554e51083365454420cd55151083565354420d554d510826d6588420d954621083655108420d9547200826f6548020b9185200836551480209ed95200825f63553109718d54c425e63153109758c54c423f6454f108f19153c423e6414f108f59053c423e64d4b108f59352c425e63d4b109758f52c423e6494b108f59252c425e6394b109758e52c436452487109798f548425d63d52109798e548425d63952108f993538423d64d4e108f992538423d6494e108fd91528423c6454a1097d8d528425c6354a108f990528423d6414a109798c528425d6314a10d9d48218423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f994544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d1097994534431f5414d10c7150534432f54d4910cb153524434f53d4910d314f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109dd85524426e6514910cbd50524432c5414910d3d4c524434c5314910d958452442766588510d914a21442746548510d9149214436452841109798f540425d63d50109b98b540426d62d50108f596540423e64150109798c540425d63150109b988540426d62150108f993530423d64d4c109b98b530426d62d4c1097596530431e5494c10c7552530431e5454c10c7551530423e6414c108f590530425e6314c109b988530426d6214c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520436461548108f990520423d64148109798c520425d63148109b988520427661148109d597210436552c84109d59421043655208410d954b100427965840109dd9510042e46244010d9549100427b6544010
  | 1 => 0xc71c5450d31c7152324c65e650c931a7590324c71c540c931c7152314c63d6595031c718d540c63e64150319798c540c65d65d0c31c7553430c65d6510c31c7550430c71d54cc83197d95320c69c644c831c7551320c71d54cc43197d95310c69c644c431c7551310c677654c4319798f54c865d63d53219798c54c865d63153218f99353c863d64d4f21c795253c871d5494f21c795153c871d5454f218f99053c863d6414f219798f548865d63d52219798c548865d63152218f993538863d64d4e21c7952538871d5494e21c7951538871d5454e218f990538863d6414e2197d8d544865c63551219ed81544867860551219798c544865d63151218fd91534863c6454d219ed8153486786054d218f990534863d6414d218f990504863d64141219798c504865d631412197d8d540865c63550219798c540865d63150219e980540867960150218fd91530863c6454c218f990530863d6414c219e98053086796014c218f992520863d64948219798e520865d63948218f992510863d64944219798e510865d6394421b958a210866f65484219dd9521086e76548421d9d9521086e460484218fd91500863c645402197d8d500865c6354021d9485500871d5390f40c754c43d031d53d0b40a718d42d031d5350b40c754f41d029c6350740c754d41d031e53d0e40c794d439031e5390a40a758c429031e5310a40c794e419029d6310640c794c419029d63d0240c794f409023e6510d409798c525025d63149408f997425029c63509409798c515025d63145408f997415029c6350540a798e405023f6550c4097d8d521025c63548408f596421029d631084097d8d511025c63544408f596411029d6310440a758f401023f65500409ed95401031c6355330c755343cc31d5410f30c755332cc29c644cb30c755132cc31d54cc730a719131cc31d544c730c758e548c31e5490e30c7951438c31e548ca30a7590328c31e540ca30c7952318c29d640c630c7950318c29d64cc230c7953308c25d63951309bd89544c26c62551309dd85544c274615513097997434c25e6510d30c7550434c23e64149308f590524c25e65cc930a7191324c23e64145308f590514c25e65cc530a7191314c29e648c1309798f540c26e62150309b588540c27661150309d584540c23e6494c308f592530c25d6590c3097d95430c31c5450c308fd91520c23c645483097596320c29d640c8308fd91510c23c645443097596310c29d640c4308f992500c23d6494030a7593300c25f654c0309ed95300c25f63553209718d54c825e63153209758c54c823f6454f208f19153c823e6414f208f59053c823e64947208f59251c825e63947209758e51c825e63d52209758f548825e63952209758e548823e64d4e208f593538823e6494e208f592538823f64546208f19
  | 2 => 0x1f500059800000430000a01d51b00010c97f314010d00df3bc0501d8c226e5e472800110208221bf2981200015c22073c4011c14a078989ac35006000170000090b51461180000014326a5b0ff8003526306f00022a6f82896800000049920094000c494f44200027000154580211b00ce1bc0017a1ae7b8160330000000021404c1a4ce9ae14674cfe0ad372000dd846000000e01c80b0238b7802328000ad066410000000ef0000001c8000002d4450d12c40010f92a0000001e8000004f08c12e1e02d80001500004400000316790438003f00d45605f1d45b40005b2f600006004070341b00406004020005000800004080000a000060000108c040000401004020080300400008018020000101c03028000000001006000070000001402014000000000000008000480c000070080404c030180d004000080004c000240c004140000502c00000080000e0100000803018060080b0c803034010000000000010020100503401004020100f0480000000050070400000c050000000002000010080003400008040201c01c0103424000070040000401000000040e0140702c030180d00403000020040b030030280c01009014010000100003000000000204c0c0069d6490c438fd954310e5f6550c43a7d954310f1f6550c43a71894310e9c6150c43a7d814310f1d4354843c750d5110f1d439404397d8d51d0a5c63547429798e50d0a5d63943429798e5190a5d639464297d8d5090a5c63542428f9974350b1c53d0d42c714d4350b1c53909428f5964310b1d5390c42c754c4310b1d53d08428fd954210a9c6350842c754d4210a6f65508429d98454cca756115332c715143cca3f64547328f19151cca3e64943328f59250cca7661d52329d587548cb1f5410e328f992518ca3d64946328fd91508ca3c64542328f992544ca5f63551328f994544cb1d631513297996434cb1c5490d3297195434cb1c5450d32c7152324ca3d6595032c718d540ca3e64150329798c540ca5d65d0c32c7553430ca5d6510c32c7550430cb1d54cc83297d95320ca9c644c832c7551320ca6f654c83297d8d52d065c6354b41a758c42d065e63943419758e50d065e6394a419758e529069c6350a4197d8d509065c63542418f997435071c53d0d41c714d435071c53909418f994425069d6310941c714c425071c53905418f596431071d5390c41c754c431071d53d08418fd95421069c6350841c754d421071d53d04418fd95411069c6350441c754d411067765504419b98854cc66d6215331c715143cc63f6454b318f19152cc69d640cb318f99250cc63d64943319b98b548c66d62d5231c7d50438c63e6494a318f592528c69c644ca318fd91508c63c64542318f992544c65f63551318f994544c71d631513197996434c71c5490d3197195434
  | 3 => 0x19500010c0009c102000da904000000038e342a3143f224200774001d93743e4d097c0006ac0903c07c004c71831d80d0af9a209e4f86d00016405887210274710a20571c8554a0800000770c380034c000000001ba248d38ed1c240c0019a050428000003be0004a1b80346a8428f6120028da0490f4038698e83de234c082e0000002a00000023c0000d15c2740e0a43fc00094a1a3f4528b09f2010888002263e847c431e10000009900000064c36899000404340912ac000ec0063a26108606a13675c001e742c18c559fd00070883800026000000b340c729098000000000020c338000f680000005c000000604f411800000000000003c6000001b72ee49c749f917c894168001ce738cd96308011ca59cc178828fda1c2ec874d69d41f8574650a227e640998970e05e0128723e6340000002a400000000196538e281b362768cc8000f82bc928c40984840016928e0bce3800290000060eb1343f4001e62046786e0001b67248405235e000f00fb0540011001914e6f0398f838681cf118000012c8c9141405245800b00009cc78002e85ac269970ba2103b9531e454486a0b38c1d4001ea2723ccc29eb24620c0017141c70430165162320bf0a81824748f06b30c1582d00003e2f4828003d8000101750aa1902e2230f241832a1e0fa000670bb13c6d800089000458648cf3d02d0b203a12c76ce807b0e8000be912000350a6800000564cb03f0007c04c1f10a014d018cd1167dcd2204260620788e20440dc960f41700003882908a5403b0212a8845091b21aa000ab8000f0024931920003e8000a60004900000042e1b807810366000000f70c400060095400284f280000067c000000060000000000069400000000000000313223f82c8cc0004b4cc12b22e8146b0ee000000000c7000468b9000000380e691b1a40007aa022b6578308001725b8001821520008480028a0c81c1d6216804978ba21e444e920f03a824361362760004f800000000b98ff0bc59c0013818c634899a32680d8159bd1b286c619f61cc2dcf49582501fc91041284000000000002fce580041a0000280000
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x9806000000003000000000000220000000007800000000000001a458080000000aa0e00801a00000000000000040000049400400200000001c00083000400001431c94354843a28e2a1aa221d1b7050e5010e8ab88a8a1e65459c75410e32838ecaa2641950d7215143cc687396a821c63075d8540c931838ecaa26418c1c76551310c60e3b2a899661071d9544c73083aed2a0651841d76950318c20ebb4a998461431c95410d30a28e2aa0869850d72151430c28ab88a8a1861191d95244010
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 666
  | 4 => 551
  | 3 => 21
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s2K7 (i*5) 5
  | 6 => packedAt s2K6 (i*16) 16
  | 5 => packedAt s2K5 (i*27) 27
  | 4 => packedAt s2K4 (i*38) 38
  | 3 => packedAt s2K3 (i*49) 49
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s2K7 (6+((h/1+packedAt s2K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s2K6 (718+((h/13+packedAt s2K6 (640+(h % 13)*6) 6) % 53)*7) 7
  | 5 => packedAt s2K5 (20202+((h/222+packedAt s2K5 (17982+(h % 222)*10) 10) % 880)*11) 11
  | 4 => packedAt s2K4 (22768+((h/183+packedAt s2K4 (20938+(h % 183)*10) 10) % 728)*11) 11
  | 3 => packedAt s2K3 (1078+((h/7+packedAt s2K3 (1029+(h % 7)*7) 7) % 79)*6) 6
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffc1fffffff03ffff83ffc1fffffcf8f1ff
  | 1 => 0xf03fffe07ffc3ffc1f07fc3ffe1fc0ff473e73
  | 3 => 0xffc0ffff81ffc3ffe007ffc3ffe1ff0387cf9c
  | 4 => 0xfffffe0003fffff80003fffe0003f80fe0
  | 5 => 0xffff0000000003fffffffffc00000003fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x8104044410480000a5090044802254501850a5
  | 1 => 0x248a48832490612c0a42a429521482a9432652
  | 3 => 0x429291090d2206554084ca8265412a0a858b18
  | 4 => 0x6b2ce252483aab9a73d06223b9980c33e80de0
  | 5 => 0x8c30c39c71c333e39ce77330311030c3f6f000
  | _ => 0
def s2Atlas : Atlas := ⟨7,rawDecor 59 s2Pos s2Neg, 0xeeaaee88ee88aa88eeaaee88ee88aa88eeaaee88ee88aa88eeaaee88ee88aa88eeaaee88ee88aa88eeaaee88ee88aa88eeaaee88ee88aa88eeaaee88ee88aa88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_15931
namespace PEqualNP.Outside.L_meta_15931
open PEqualNP.Outside.L_meta_15931.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0xf38000c00300b00234a00905000020610714121520df43be43bc43dc439c43bf42bd42df32dd32bf41bd41df31dd31be40bc40de30dc30
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0xe00280b01928004a30088060000010404794e438ea90871d5110e3ca021c714d428e2a6651c544ca38a6a0c7153318e2a2631e539023ca9184715030
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0xd000808558454cca0d621533183588540c2156115030
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
  | 2 => packedAt s3K2 (155+((h/1+packedAt s3K2 (152+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffff07fffc1ff83ffff07ff07ff07fe7cf3cf
  | 1 => 0xf07fff83fffe1ffc1f07f87ff87ff83fa33cf3
  | 2 => 0xff83fffc1fffe1ffe007ff87ff87ffc1c3cf3c
  | 4 => 0x3ffffe00001fffff80007fff80001fc0fc0
  | 5 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x8108111084820000a5090089008902940c5145
  | 1 => 0x24112209091030940a42485248525028a12492
  | 2 => 0x4222442052210329408495049504a501428a28
  | 4 => 0x6b5b894a43b555ce73d0c447e660318df40fc0
  | 5 => 0x8c630e739c3999f39ce7e660c440c631fbf000
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xeaeae8e8e8e8e8e8eaeae8e8e8e8e8e8eaeae8e8e8e8e8e8eaeae8e8e8e8e8e8eaeae8e8e8e8e8e8eaeae8e8e8e8e8e8eaeae8e8e8e8e8e8eaeae8e8e8e8e8e8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_15931
namespace PEqualNP.Outside.L_meta_15931
open PEqualNP.Outside.L_meta_15931.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x3e0000600000000000d023a0160406796ae1a311a62a65288383921b00003800001489281400b624000a009c0004000018024402f2ca098054491001e84bb0000002b0000001830a0400c10001810a00000ff43fe43be43fd43fc43bc43ff42bf42fe42fd42bd42fc42ff32df32fe32fd32dd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x138769d001780000000c800000000000000000000000019c000000058000000000f40000000964d390005800480003000000000026351b80000002912c782c9108000288000000418746a4f00044004712930e6000023c001b4fa2502001ba2826523b1acfa5a000012600219dd0e8e1c270d200070b4344200000cc7c4a0e47c1e0f8a542414d800c488110009400000011a003184800792d8c00000000000000008000000000080000000f0e22700218ac002f8700000001f800000c80000002e000002e4a94c0000000010a0000190008200001342a08000004619914002418a644000000d8000000000000002001460000000003f48800743424800aea242000d800378001200001fc00000000c0000038000000001200000000000070001d442000002800002c15418000001400980a800006100000468c1e83c002b00000000040180f6684b800e8280002ca0650005c100636a481a5d1795140004f22c28000000200008141c000100c0000008080200010080002000141400018000000008000001008040004018040001000001200008000200008000002000040600004f94e439ea94873e5190e7aa121db94843b6a90873e5310f3ca621eb948439ea9087ad5210e5aa421cf944439ea80873e53d0a7ca3a14f543429eaa4855e5390abaa7214f14d42d7a92853c5150a7ea0a14f95042af298855d5310a7ea9994f15332cf21e659c43ccb3ea9996715332cfa16659d42cca7ca9194f55232aea9c65ad428ca7ea8994f15132cf21a659c434cb5a849967d5132ce2a265cf524cb3e84997390932cea1265cd424cb1a84994f950329eaa0655e530cabca720d754e419f29c839e539063ca720e754e419ea94839f329073a6520cf946419ea84833e531067aa420e7cc841ce990833e511076ca220cf540419f2a6633d54cc7388798db94b31b6a96633e548c67aa918cfd51319e2a2639c434c67ea818cf150319f2a6433d54c86bca790d754f219faa4433c548879a6510cfd51219e2a2433e540867aa810d794c21aea9843cd32086f4a010de540219f29e813d52d033e65a0674cb409f28e813d54902bea6a05714d40cfa9a813c5350338a6a04714d409fa92819f325033a64a04f14540dda82813e541027ea9984f153309f2a4613d548c33887184fd51309e2a2613e540c27aa8186710c30b7290616d520c2eca2185d544309f2a6413d54c82bca7905754f20e6996413e548827aa9104f951209eaa241cd324827ca8104f55020af298415d53082eca2105d544209faa6213c54c427ca9084f552109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0xe0e1e00edd0b288daac20484af4c10002520121700ac6b26c5800000a8025321c01d420000f50c401a0a88a8000d00130c3840014dcda76680018604568300057390030f800024048270000302000028a00141810000600c394d5210f0e63548438798e51d0a1c63543428d98754cca8d62d5332a598754cca8d62153328b195424ca8d6490932a3995424ca8c6550932a3185424ca8f60509329358a539062d6294e41a358a539070e6294e418758a539070d6294e418358a539061f65cca4187d95329070d524c8418718d501068d6210f31c310d52cc68d6210d318798f540c62d62150318e580540c61e63d5221c3d51328861e63d5121c355132087493254021c354932d021e639474093588535022d6214d40a3588535030e6214d4087588535030d6214d4083588535021c65cc94087195325022d6215330a3588438c21d6510c30a3588430c30c4354830c510d510c30d544cb208718d548821c63551208d185544830d544c9208798f54c421c6355210
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x8a0404c70240419c4282b8cc6a9087219c6655093281ae431aa020c0d7298f5448606b94c728e81415c84354430818ecaa26490504715513248206b94c7aa621035c86355210
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 50
  | 4 => 165
  | 3 => 60
  | 2 => 10
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (i*5) 5
  | 5 => packedAt s4K5 (i*16) 16
  | 4 => packedAt s4K4 (i*27) 27
  | 3 => packedAt s4K3 (i*38) 38
  | 2 => packedAt s4K2 (i*49) 49
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (6+((h/1+packedAt s4K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s4K5 (912+((h/16+packedAt s4K5 (800+(h % 16)*7) 7) % 80)*7) 7
  | 4 => packedAt s4K4 (4950+((h/55+packedAt s4K4 (4455+(h % 55)*9) 9) % 316)*9) 9
  | 3 => packedAt s4K3 (2420+((h/20+packedAt s4K3 (2280+(h % 20)*7) 7) % 80)*7) 7
  | 2 => packedAt s4K2 (502+((h/3+packedAt s4K2 (490+(h % 3)*4) 4) % 13)*5) 5
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xf07ffc3ffffc3fc1fe1fc3fe1fffc1fe8cf3cf
  | 1 => 0xff87ffc1f0ffc3fe1fe1fc3fe1c1fe1f733d33
  | 2 => 0xfff87ffe00fffc7fe001ffc7fe01ffe183ce3c
  | 3 => 0x7fffff00007ffffe0007fffe0001fc0fc0
  | 5 => 0xffff80000000007ffffffff800000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x14000408402040004402404802504088045045
  | 1 => 0x212108848148040a0a20841220849414312512
  | 2 => 0x421251102a9220d4a1112a8554092941828a28
  | 3 => 0xb556225281aa96733542207992c0c45d80f80
  | 5 => 0x8c6643b9cce33279dd99f32110303199eff000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeee8eee8eae8eae8eee8eee8eae8eae8eee8eee8eae8eae8eee8eee8eae8eae8eee8eee8eae8eae8eee8eee8eae8eae8eee8eee8eae8eae8eee8eee8eae8eae8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_15931
namespace PEqualNP.Outside.L_meta_15931
open PEqualNP.Outside.L_meta_15931.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x493009c2003aa109b305411e0094585188d32c40418241a0000028005195a440071c180005400f80245ce0300ac001002188f0059480348802e5e0a1c20a060030100040801234000ff43fe43be43fd43fc43bc43ff42bf42fe42fd42bd42fc42ff32df32fe32fd32dd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x7e6f24958046c418681e84469cd42910da4ce08f0014c6e002e1a9380950074ea000015110170018884660023000003f0d914260880070000006094760419460151625000004a9780000300d1205d4280064330389c0048338700c002f91d302818a38325210000023a32138725b00000d6780028c006d2d22488040010c427d0013c00921ea683c9f051dc481f43100206e4b154063c229f0d046158505c000000000233c9a44a0006984e4993a140187f00104b200001e8263e1da900000000000081459305e0002888e2000012d449b00000000b000009a00000010e001aa0852000b0393c12401ec00512c0005a2a2b98d3a97038c0004000388020100830003060380838301800081820000838081858700008003048a09018280840402078300008109000681840003cf94e439ea94873e5190e7aa121db94843b6a90873e5310f3ca621eb948439ea9087ad5210e5aa421cf944439ea80873e53d0a7ca3a14f543429eaa4855e5390abaa7214f14d42d7a92853c5150a7ea0a14f95042af298855d5310a7ea9994f15332cf21e659c43ccb3ea9996715332cfa16659d42cca7ca9194f55232aea9c65ad428ca7ea8994f15132cf21a659c434cb5a849967d5132ce2a265cf524cb3e84997390932cea1265cd424cb1a84994f950329eaa0655e530cabca720d754e419f29c839e539063ca720e754e419ea94839f329073a6520cf946419ea84833e531067aa420e7cc841ce990833e511076ca220cf540419f2a6633d54cc7388798db94b31b6a96633e548c67aa918cfd51319e2a2639c434c67ea818cf150319f2a6433d54c86bca790d754f219faa4433c548879a6510cfd51219e2a2433e540867aa810d794c21aea9843cd32086f4a010de540219f29e813d52d033e65a0674cb409f28e813d54902bea6a05714d40cfa9a813c5350338a6a04714d409fa92819f325033a64a04f14540dda82813e541027ea9984f153309f2a4613d548c33887184fd51309e2a2613e540c27aa8186710c30b7290616d520c2eca2185d544309f2a6413d54c82bca7905754f20e6996413e548827aa9104f951209eaa241cd324827ca8104f55020af298415d53082eca2105d544209faa6213c54c427ca9084f552109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0xec0281ec069a004c000001d7a16a39b0252b9515000002c00c401d720119f1078e26000000522041b34480d9400000242401d104e182003094b996e01a0a122d90c56e0b2d000804184080c102021800e06143860000183c394d5210f0e63548438798e51d0a1c63543428d98754cca8d62d5332a598754cca8d62153328b195424ca8d6490932a3995424ca8c6550932a3185424ca8f60509329358a539062d6294e41a358a539070e6294e418758a539070d6294e418358a539061f65cca4187d95329070d524c8418718d501068d6210f31c310d52cc68d6210d318798f540c62d62150318e580540c61e63d5221c3d51328861e63d5121c355132087493254021c354932d021e639474093588535022d6214d40a3588535030e6214d4087588535030d6214d4083588535021c65cc94087195325022d6215330a3588438c21d6510c30a3588430c30c4354830c510d510c30d544cb208718d548821c63551208d185544830d544c9208798f54c421c6355210
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x1400000202000818047324128282b8cc6a9087219c6655093281ae431aa020c0d7298f5448606b94c728e81415c84354430818ecaa26490504715513248206b94c7aa621035c86355210
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 50
  | 4 => 165
  | 3 => 60
  | 2 => 10
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (i*5) 5
  | 5 => packedAt s5K5 (i*16) 16
  | 4 => packedAt s5K4 (i*27) 27
  | 3 => packedAt s5K3 (i*38) 38
  | 2 => packedAt s5K2 (i*49) 49
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (6+((h/1+packedAt s5K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s5K5 (912+((h/16+packedAt s5K5 (800+(h % 16)*7) 7) % 67)*7) 7
  | 4 => packedAt s5K4 (4895+((h/55+packedAt s5K4 (4455+(h % 55)*8) 8) % 218)*9) 9
  | 3 => packedAt s5K3 (2420+((h/20+packedAt s5K3 (2280+(h % 20)*7) 7) % 80)*7) 7
  | 2 => packedAt s5K2 (505+((h/3+packedAt s5K2 (490+(h % 3)*5) 5) % 18)*5) 5
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf07ffc3ffffc3fc1fe1fc3fe1fffc1fe8cf3cf
  | 1 => 0xff87ffc1f0ffc3fe1fe1fc3fe1c1fe1f733d33
  | 2 => 0xfff87ffe00fffc7fe001ffc7fe01ffe183ce3c
  | 3 => 0x7fffff00007ffffe0007fffe0001fc0fc0
  | 4 => 0xffff80000000007ffffffff800000001fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x14000408402040004402404802504088045045
  | 1 => 0x212108848148040a0a20841220849414312512
  | 2 => 0x421251102a9220d4a1112a8554092941828a28
  | 3 => 0xb556225281aa96733542207992c0c45d80f80
  | 4 => 0x8c6643b9cce33279dd99f32110303199eff000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xeee8eae8eee8eae8eee8eae8eee8eae8eee8eae8eee8eae8eee8eae8eee8eae8eee8eae8eee8eae8eee8eae8eee8eae8eee8eae8eee8eae8eee8eae8eee8eae8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_15931
namespace PEqualNP.Outside.L_meta_15931
open PEqualNP.Outside.L_meta_15931.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xc401c58100320c76b809d10f20107cd9201141568d4aab86e01e4b9841751156ac4d8030b542800000494c7349e64033bb0a550b8a1ab07c88c4700d951a009a40000e80490c042070408080000028d1e280010218685000005fe54007f55005fc54017fd0c01fe43007f50c05fc4300ffd0803bf4200ff90803fd4200ef50803fc4200ffcc803df3200ff8c803fd3200f74c803fc32017fd0401fe41007f50405fc41007fcc401fe31007f4c401fc3100ffc8403fe2100ff48403fc21017fd0001fe40007f50005fc40007fcc001fe30007f4c001fc3000ffc8003fe2000ff48003fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x142001bf18a1002ffe8508017bf428400bff2142005ff50a1002f7a8508017fc428400bff9942005f7cca1002ffc6508017fd328400bee9942005ff0ca10045fac30802bff4184001ff20c2000ff50610057f88308003ff3184001ff18c2000ff4c610007f86308017ff218400bff10c2005ff4861002ff8430800efe6084015ffa042000ff90210007fa810802bfc4084001ff9842000ff8c210007fa6108003fc308400bff9042005ff8821002ff44108017fd208400bfc9042005ff08210007fe2108003f71084001fd8842000ffd9110005fec888003bf64440015fb222009ff99110015fcc888003fd64440017eb222009ff19110015f8c888003bc64440055e3222009ff95110007faa888027fc5444001ffb1a2000bfd8d10007bec688002df6344001ff31a2007bf98d10007fac688002fd6344001fe31a2007bf18d10007b8c688002dc6344013ffa1a2000ff90d10007fa8688027fc4344011ffb122008bfd8910007dec488002ef6244011ff3122001bf98910047fac488022fd6244011fe3122001bf18910047d8c488006ec6244011ffa122008efd0910047fc8488023fd4244011dea122008ff10910047fe6488023df3244011ff1922008ff4c910047ba6488023fc3244013ffa0a2000ff90510007fa8288027fc4144001ff98a2000ff8c510007ec6288003fd3144001fa98a2000ff0c510047fe4288023fe2144011fb10a2008ff48510047ea4288023fc2144013ffa022000ff90110007fa8088027fc4044001ff9822000ff8c110007fa6088003fc3044011ff9022008ff88110047f44088023fd2044011fc9022008ff08110007fe2088003fb1044001ff0822000fd84110007fec808002ff6404009ff3202002bf990100077cc80800abe6404001feb202000bf590100077ac808002bd6404009fe3202002bf19010027fca808003fd5404009fe2a02000ffd8c10005fec608003fe630400f7f3182000f798c10005bcc608003fd63040017eb182000f758c10005bac608003fc630400f7e3182004ffd0c10007fc8608003fd4304009fe2182003ffd881001dfec40800ffe62040037f3102003fb9881000ddcc40800ffd62040077eb102000fb58810005dac40800ffc62040037e3102003ffd081001f7e840800ffe4204007fea102003ef5081001ff8840800fff3204007ef9902003ff8c81001ffa640800fdd3204007fe1902006bf98410027fe8208003fe4104001fea082004ff10410007fe6208003fe3104001fe9882000ff0c41001ffe420800ffe2104007fe9082003ff0841002dfcc008013ff4004001ff2002000ff50010027f88008003ff3004001ff1802000ff4c010007f8600800fff2004007ff1002003ff4801001ff84008003ff1004001fb8802000ff84010007f42008003fd1004001fa8802000fe44010
  | 1 => 0xfdf324c01fff192600fff4c93007fba649801ffc324c001ffb0a6000bfd8530007fcc298003fd614c001fe30a6000bf18530087fe8298003fe414c001fea0a6010ff1053003ffe6298003df314c001ff18a6000ff4c530007ba629801ffc314c01fff90a600fff8853007ffa429803ffc214c021ffa026000ff90130007fa8098043fc404c00fff9826007fecc130007fc6098003de304c01fff902600fff8813007ffa409803ffc204c00fffb206007bfd903003ffcc81800afe640c00fdf3206002af9903003ffac818002fd640c00fdeb206000af5903003ff8c81801efc640c01bff2a06000ff5503006ff8a81801efe630c00fffa186007ff90c3003ffa861801ffc430c00fffb106007bfd883003ffcc418006fe620c00ff73106001bb9883003ffac418032fd620c00ff6b106000bb5883003ff8c418006fc620c019ffa10600cefd0830067fc8418033fd420c019dea10600cff1083003ffe641801fdf320c00fff1906007ff4c830067ba641801ffc320c00fffb086007ff98430005fcc21801ff6610c0017b3086007ff58430005fac21801ff5610c0017ab086007ff1843006ffe8218003fe410c001fea08600dff1043003ffe621801ffe310c001ef1886007ff4c43003ff8621801fdc310c019ff908600cff88430067fa4218033fc210c01d7f300600dffd0030007fc8018003fd400c01bfe2006007ffcc03003fbe601801ffe300c00ffd1806007ff4c030007ba601801ff9300c019ff900600cff88030067fa4018033fc200c001ffb262000bfd931005ffcc98800afe64c4001feb262000bf5931005ff8c98800afc64c4017ff2a62000ff5531005ff8a988003ff63c40017fb1e2000ff98f1003dfcc788003fd63c40017eb1e2000ff18f1003df8c78802fff43c4001ff21e2000ff50f1005ff8878801bff62c400d7fb162006ff98b1000dfcc58801bfd62c400d7eb162006ff18b1000df8c58801bff42c400ddfa162006ff90b10037fa858801bbd42c400dfe2162006ffccb10037be658801bfe32c400dfe9962006f74cb10037f8658802fff41c4001ff20e2000ff5071005ff88388003ff31c4001ff18e2000fd8c710007fa6388003f531c4001fe18e2006ffc8710037fc438801bf621c400dfe90e2006fd48710037f8438802fff40c4001ff2062000ff5031005ff88188003ff30c4001ff1862000ff4c310007f8618801bff20c400dff1062006ff48310037f84188003ff64840017fb24200aff99210015fcc908003fd64840017eb24200aff19210015f8c90802bfe5484001feaa4200aff15210007fec708002ff6384001ff31c2007bf98e10007fac708002fd6384001fe31c2007bf18e10057fe8708003fe4384001fea1c200aff10e1002ffec508016ff628400bff3142001bf98a1002ffac508016fd628400bfe3
  | 2 => 0x400a7fca4a0053fd5250029bea928014ff14940017fe84a000bbf4250005ff2128002ff509400a77a84a000bfc4250029ff9928014f7cc9400a7fc64a0053fd3250029ee9928014ff0c940007fec2a0002ff6150001ff30a8000ff58540007f8c2a0002fc615002bffa8a8000ff94540007faa2a0057fc5150005ffa0a8002efd0540017fc82a000bfd4150001dea0a8002ff10540007fe62a0003fe3150001fe98a8000ff0c5400a7fe42a0053fe2150029fe90a8014ff08540015fec0a0057ff5050001ff2828000ff541400aff8a0a000bff4050005fda028002ff901400077c80a000bfc4050005de2028002fe101400a7fe40a0053fe2050029fe9028014ff0814003ffec99801eff64cc00fff3266002bf9933003ffac998002fd64cc00ffe3266007bf1933009ffca998003fd54cc027fe2a66007ffd0f3003ffc879801ffd43cc00ffe21e6007ffd8b3003dfec59801ffe62cc0037f3166007ff58b30095fac59801ffc62cc0037e3166012ffd0b300977e859804bfe42cc025fea166012ef50b30097f8859801fff32cc00fef9966007ff8cb3003ffa659804bdd32cc00ffe1966007ffd873003ffcc398002fe61cc00ffeb0e6000bf5873003ff8c39804fff41cc001ff20e6000ff5073009ff8839801fff31cc00fef98e6007ff8c73003ffa6398003dd31cc00ffe18e6012ffc8730097fc439804bfd21cc025fe10e6013ffd0330007fc8198003fd40cc027fe2066012ffc8330097fc419804bfd20cc025fe1066000ffd9230005fec918047fe648c0057f3246000ff59230005fac918047fc648c0057e3246011ff95230007faa918047fc548c01f7eb1c6011ffd0e3003ffc8718003fd438c00ffe21c600effd8a30075fec51803bfe628c0037f314600eff58a30075fac51803bfc628c0037e314600effd0a300777e851803bfe428c01dfea14600eef50a30077f8851801fff328c01def994600eff8ca30077fa651803bdd328c00ffe1946000ffd8630007fcc318002fe618c001feb0c6000bf58630007f8c318047ff418c001ff20c6000ff5063008ff8831801fff318c001ff18c6000f78c630007fa631801ffc318c001ee18c600effc8630077fc431803bfd218c01dfe10c6007bf9823008ffe8118003fe408c001fea046011ff1023003ffe6118003df308c00ffd984600effc8230077fc411803bfd208c01dfe1046000ffd9130005fec898003bf644c0015fb226010ff99130015fcc898003fd644c0017eb226010ff19130015f8c898003bc644c0055e3226010ff95130007faa898043fc544c021ffa1a6007ff90d30007fa869801ffc434c01fffb12600fbfd893007ffcc498006fe624c01ffeb12600fbf5893007ff8c498006fc624c01fffa12600fefd093007ffc849803ffd424c01fdea12600fff1093003ffe649803
  | 3 => 0xb98a6200ff8c531007bc6298873ff214c439ff10a621cff485310e7f84298803ff604c4017fb026200ff98131007fac098803fc604c4017e302621dffd01310eff88098873ff204c439ff102621cff481310e7f8409881fff640c40f7fb206207ff99031015fcc81881ffd640c4017eb206207ff1903103df8c81886bfe540c401feaa0621aff1503103dfcc61881fff430c40fff2186207ff50c3103ff8861881fff620c40f7fb106207ff9883100dfcc41881ffd620c4337eb106207ff1883100df8c418867ff420c433dfa106219ff908310cffa8418867bd420c433fe2106207ffcc83103fbe641881ffe320c40ffe9906219f74c83103ff8641886efe610c435ffa086200ff90431007fa821886bfc410c40fff9886207f7cc43103ffc621881ff6310c40ffe9886200f74c43103fea6218867ff210c433ff1086219ff484310cff8421881fff600c40fff3006200bf9803103ffac018802fd600c40ffe300621affd00310d7f88018867ff200c433ff1006219ff480310cff84018803ff65900017fb2c8018ff996400b5fccb200037e659002d3f32c8000ff59640005facb200037d65900013eb2c8018ff196400b5f8cb2000afd6490005ffaa48002ff952400177ca92000bfd5490001deaa48002ff15240007fec720003fe639000f7f31c8000ff58e40005fac720003fc6390031ffa9c8000ff94e40007faa720063fc5390005ffa1c8002ff90e400077c872000bfd4390005fe21c8002ef10e400bffec52005eff629002fff3148001bf98a400bffac52005efd629002ffe3148001bf18a400bffea52005f7f529002fff2948017ff54a400befaa52005ffc5290005ffa148002efd0a40017fc852000bfd429002fdea148002ff10a400bffe652005fdf329002fff1948017ff4ca400bfba652005ffc3290001ffb0c8000ff98640005fcc320003fd61900017eb0c8000ff186400c7fea320003fe5190001fea8c8018ff14640017fe832000bfe4190001df20c8002ff50640017f8832000bbc4190001ff98c8000ff8c640007fa6320003fc319002fff90c8017ff886400bffa432005ffc21900057f3048018ffd4240007fca120063fc5090005ffa048002efd0240017f6812000bfc4090005fc2048017ffc82400bffc412005ffd209002ffe1048000ffd9540005fecaa0057fe655002d7f32a8000ff59540005facaa0057fc655002d7e32a8002bfd9140017fea8a0057bf5450005ff2a28002ff55140017f8a8a000bbc5450001ffb1a8000bfd8d40007fcc6a0003fd6350001fe31a8007bf18d400affea6a0003fe5350001fea9a8015ff14d40017fe86a000bbf4350005ff21a8002ff50d400077a86a000bfc4350029ffb128014bfd89400a7fcc4a0006fe6250029feb128014bf589400a7f8c4a0006fc6250029ffa928014dfd49
  | 4 => 0x806fe6250443feb128221bf5894110ff8c4a0806fc6250443ffa928221dfd494110ffca4a0887fd5250443bea928221ff14941017fe84a080bbf4250405ff2128202ff5094110f7a84a080bfc4250443ff9928221f7cc94110ffc64a0887fd3250443ee9928221ff0c941015fec2a088bff5150401ff28a8200ff54541117f8a2a080bff4150405fba0a8202ff905410077c82a080bfc4150405de20a8202fd1054110ffe42a0887fe2150443fe90a8221ff08541007fec0a0802ff6050401ff3028200ff58141007f8c0a0802fc6050445ffa828222ff14141017fe80a080bbf4050405fe2028221ffc814110ffc40a0887fd2050443fe1028207ffd933103dfec99881ffe64cc4057f3266207ef993310157cc99881ffd64cc4017eb266207ef593310057ac99881ffc64cc40f7e3266220ff95331007faa998883fc54cc40fffa1e6207ff90f3103ffa879881ffc43cc40fffb166207bfd8b3103ffcc598806fe62cc40ff73166201bb98b3103ffac59887efd62cc40ff6b166200bb58b3103ff8c598806fc62cc43fffa16621fefd0b310fffc859887ffd42cc43fdea16621fff10b3103ffe659881fdf32cc40fff1966207ff4cb310ffba659881ffc32cc441ffa0e6200ff90731007fa8398883fc41cc43fff90e621fff887310fffa439887ffc21cc40fffb066207ff98331005fcc19881ffd60cc4017eb066207ff18331107fe8198883fc40cc43fff906621fff883310fffa419887ffc20cc401ffb246200bfd92310f7fcc91880afe648c401df3246202af99231007fac918802fd648c401deb246200af592310f7f8c91880afc648c43dff2a46200ff552310f7f8a918872fd638c43dffa1c6207ff90e31007fa871881ffc438c437ffb14621bbfd8a310dffcc518806fe628c437feb14621bbf58a310dff8c518806fc628c437ffa14621befd0a310dffc851886ffd428c437dea14621bff10a3103ffe651886fdf328c437ff194621bff4ca310dfba651881ffc328c40f7f30c621effd0631007fc8318803fd418c43dfe20c6207ffcc631007be631881ff7318c437ff90c621bff886310dffa431886ffc218c401ffb046200ff98231005fcc118803fd608c4017eb046200ff182310f7fe811887bfc408c437ff904621bff882310dffa411886ffc208c401ffb226200bfd91310effcc89880afe644c401feb226200bf591310eff8c89880afc644c43bff2a26200ff551310eff8a898877ff434c40fff21a6200ff50d3103ff88698873ff624c4397fb12621cff9893100dfcc498873fd624c4397eb12621cff1893100df8c498873ff424c439dfa12621cff909310e7fa8498873bd424c439fe2126207ffcc9310e7be6498873fe324c439fe992621cf74c93103ff86498877ff414c401ff20a6200ff505310eff8829881fff314c40ff
  | 5 => 0x8243005fac12181ffc6090c51ffa848628ff14243017fe812180bfc4090c05de2048627ffc824313ffc412189ffd2090c4ffe1048600ffd9543005fecaa18037f6550c013fb2a8626ff995430b5fccaa1803fd6550c017eb2a8626ff195430b5f8caa18037c6550c2d3e32a8607bfd9143017fea8a180bfe5450c05df2a28602ff551430077aa8a180bfc5450c057fb1a8626ffd4d4303ffca6a1803fd5350c0ffe29a8602ffd0d43017be86a181ffe4350c0fdf21a8607ff10d4303f7886a180bdc4350c4bffb128625bfd894312ffcc4a1806fe6250c4bfeb128625bf5894312ff8c4a1806fc6250c4bffa928625dfd494312ffca4a1897fd5250c4bbea928625ff14943017fe84a180bbf4250c05ff2128602ff5094312f7a84a180bfc4250c0fff9928625f7cc94312ffc64a1897fd3250c4bee9928607ff0c943007fec2a1802ff6150c01ff30a8600ff58543007f8c2a1802fc6150c4dffa8a8626ff14543017fe82a180bfc4150c05de20a8625ffc854312ffc42a1897fd2150c4bfe10a8600ffd8143005fec0a1803fe6050c01feb028600ff18143005f8c0a189bff5050c4dfe2828602ffd01430177e80a180bfc4050c4bff9028625ff8814312ffa40a1897fc2050c01ffb2c8200bfd9641127fccb2085afe6590401feb2c8200bf59641127f8cb2085afc65904057eb248202ffd52411277ea92080bfe5490405feaa48202ff1524101778a920803ff6390401ff31c8207bf98e41007fac720802fd6390401fe31c8224ffd4e41007fca720803fd5390449fe29c8202ffd0e410177e872080bfe4390405fea1c8200ef50e41017f8872088fff62904477fb148223ff98a4100dfcc52088ffd62904477eb148223ff18a4100df8c52088fff5290447bfa948223ff94a4111ffaa52088f7d5290447fe2948202ffd0a410177e852080bfe4290405fea148223ef50a41017f8852088fff3290447ef9948223ff8ca4111ffa652088fdd3290447fe1948202bf98641127fea320803fe5190449fe28c8202ffd06410177e832080bf74190405fe20c8202fd1064111ffe432088ffe2190447fe90c8223ff08641007fec120803fe60904017f3048200ff58241005fac120803fc6090449ffa848224ff14241017fe812080bfc4090405de2048223ffc824111ffc412088ffd2090447fe1048200ffd9541005fecaa08037f65504013fb2a8222ff995410b5fccaa0803fd65504017eb2a8222ff195410b5f8caa08037c655042d3e32a8202bfd9141017fea8a080bfe5450405df2a28202ff551410077aa8a080bfc5450401ffb1a8200bfd8d41007fcc6a0803fd6350401fe31a8207bf18d41117fea6a0803fe5350401fea9a8222ff14d41017fe86a080bfe4350401df21a8202ff50d41017f886a080bbc4350443ffb128221bfd894110ffcc4a0
  | 6 => 0x400400800400400800c01c00800001c00008800400802008001c04000800401001400400801c01400400400c03801800800008c01401808000002400800401002800000000c0180080200000100100700040080000a000000000402006000c01800404002c00c00800c00003400400c01401c0a000403000400000c05402400000002800800401000c00400000c01408401c00400400003c04400400000400001405800400400804c00000003c00c00000c04400800000000c01800000401005400c00802000000002001800001401000400401007004802400001800001401c02000000001402400001400400000400000000c01000004c00001400000000c0000040040040380100b000000c00000004400801803400c01c00000800000400001000c06800402800404401c01c01800001002400400002002401c01400400000801401400001403c0000000080040100080040040000080140000000100a400800800001800401401002800400005c00001402c02801803000c05c00000000401000000001c00c00c00c00c0000640200040100040140100580040200a400002402401c020014057fb22a802ff95154016fca8aa00bfc5455005de2a2a802cf15154007fec6aa002ff6355001ff31aa800ff58d54007f8c6aa01efc6355005ffa1aa802efd0d54017f886aa0a7ff62550537fb12a829ff9895400dfcc4aa0a7fd62550537eb12a829ff1895400df8c4aa00bff4255005dfa12a802ff90954017fa84aa0a7bd4255005fe212a829ffcc95414fbe64aa0a7fe3255053fe992a829f74c95414ff864aa003ff61550017fb0aa800ff98554007fac2aa003fc61550017e30aa802ffd05540177e82aa00bfc4155053ff90aa829ff8855414ffa42aa0a7fc2155001ffb02a800bfd8154007fcc0aa003fd6055001fe302a800bf18154017fe80aa00bfc4055005de202a829ffc815414ffc40aa0a7fd2055053fe102a807ffd964303dfecb2181ffe6590c2d7f32c8607ff59643005facb2181ffc6590c0f7e32c8602bf59243017fea9218a3bf5490c05ff2a48602ff55243017f8a92180bbc5490c0f7f31c8607ffd4e4303ffca72181ffc5390c0fffa1c8607efd0e43017be872181ffc4390c0fee21c8607ffd8a4303dfec52181ffe6290c037f3148607ff58a4313dfac52181ffc6290c037e3148627ffd4a4313efea52189ffe5290c4ffea948627df54a4313ff8a52180bff4290c05dfa148602ff90a43017fa852189fbd4290c05fe2148607ffcca4303fbe652181ffe3290c0ffe9948627f74ca4303ff8652181fff6190c0fff30c8600bf9864303ffac321802fd6190c0ffe30c8628ffd4643147f8a32180bff4190c05dfa0c8602ff1064313ffe432189ffe2190c4ffe90c8627ff0864303ffec12181ffe6090c017f3048607ff5
  | 7 => 0x4516d8604002c343188f2310c0a8a06c9f324a08b6781a91fc91d00180000012a0000c38000000001b71f8ced1528ba00010b9008000000000000000da208e8784952e8ce0991ac8001c25a1a590002261291b2ac01a082a6771371ed109c0617f0000c8c0025b67d119ed7a40a9a1aaea71ee2aa9578ff89b9169b8102cf1a0709085da690725c79821c71fe0fac1cc999ecc579479d39a699e5a3d408000bc2498000000a11b88584000002cc429d7c8e184b870a4e0f21662bb91e017800185a788002651e04000000c49ef03c9938001769491aee882941af8a817d87611190107c6a32032d18a59c14db1eb4ac28cac1a6008816f9235a21598b58e847d9d714e16ec002a10000d6c00ac200000014da990ea285a229338ca1cc42640f85492ede189cab8a4fa6a96c950a0812892582c1aa50a53ad570002cb68716a51506708c097a660f25881f99f1a821188879bb0c41c0c4a0830b71095cdd93d159051cc20b9ab5780e9c4c80015d9080001cb4002040cadceddf800290972a5d00018e930034dc38d69e98c26298000000000000001ec55a48d8f6a1380012265401d90a28623c95a8b60a60001c1a2e09c0288b94af440871acae078d49949fb2610002d30c5c0007300020a2c593a83cc09400144852c96c268171352cb9608a691366d0d9a06460ce0ea09ab0bda4b1bc9b7a3fa75a09c8111905548c9101b627208ad8a1fa08fd21e2b014000400004800800004c00000000800803002800002000000c02001001402c01400001001001001800800401400000400c02400002800c01c00000805c00405003005800c00000002008800c00c00004803400001800c03c00001400401c0040180100080040200100180140280980f00b400c01401401002800000800000400000400c00402400005001c00000400001802800c00002000409000400400400400800000400402000000401800003000400000000000003c01400000000400400000801400400409000800401000801007400000001808c06800400802006000000005000400007c01400002000400402800000c00002000800000001000400400c00400800400404800802800005400c00801400400800800c00005c01801400000000000801004401000404800000000000c00400000000000000800802002c00800000401001409c00c00c06c00c01801401c04001802000c02001403c00800c00800800000800000003000c0a000400000c00000403001402000400000000001000002c00800c00800c00404800002000001c0ac00406c03801800801400000000401800400400406c00804800800400400c0500600100180e801400001803800c05401804005800401001800000001802c03000000801003c08c02400400000403c00001003c00000001801000c00002000
  | 8 => 0x8600000000000000ea360e5c502b407ce4d93c12dc000001f6842c3a09a079ea38000770000000000660001c12558001718cd2469710432800279bd4544000000ca983c000000000000f367a9760000001e415c2bdeb18e28e420393096baa28164000d80558001b112980d000236a0bd0306dc000000001696a8800189a5bda40000fd0e6acb21e10f0001e9e3d1c99398649105144000eac002c440025f04d9c28850bb084235a0dc0024580000016429521c0478284e5aa417f89802f8002b500000000012f8c520d8001612988d662780000000000000012220c0c82658cda568ba47400000011b4b29688000001e8cd328681b2d700000027f0000001db204acc800000000067a2814e827c00108d889860000000b18401b19420001d94000001c50459ae6ce2af988da9c5ba96132890c000ec80000012a9ca83b2b22b81fe400283a2c8c6800000287d238000001968002ce8000001170dfc00266a3e90f4a38138cc06115e1851be1b40000000000000000000000c9a0a4002baa0aa719d900015c80006b0a7c0e000009a2680000000000000002f0e50b98000002d80fb25d8d19e94000000580002a00be06594c02d0000c9d9e8000000000e10378d50000001108d20002c80001ca0001eddbf8002bd8002b098f0002d0a52800082c0002ac0000000012b96ac000040900000001fd8001d491f1411c8de0c000000000dec002850002d885b00b8a400000011797b29d8e99be8001140001c1c9222705889428d9bcd09abeaae8630180002c9a6b0001059b38000000000001aa8000c14cfc000550000000000f3e6e00027980003580000000012feb45530001cd8d58801368000002c88001488001944de4368001c012b25c920800272a1928922125991c16f6cbe60cc6476a4f102026c95c00262951a054000000002a92ca0fb4001a3129e9192ca9380000000016599ee582bd18f8538000000000001778df0a002723489f91fad7ded4af91ac000b1000122c0027b0002901ad9b3d0b0cf8002af0425c940012d29a91280000000010e00009a9280bf9c85541de21119f00012c503a010d729b05340026c9ac20f264000000000000053da480008b1d88000000000000d11f88001211a600020ac00015ce0a1780019a00025a8002bd5250d0000000106ad595f2a80002d2cc200028a6338e486d4028000000000000d8a6728b0000001eda6c0002c3dc90000000dc80004d2061cfa7698310dc5901a8ee8a8400112eb703444499b0001555ee92a5918470eb5ce0cc9d692940009684190c0275c593e8edd438001d400026a1c82481ad0b8aa79bbc0010d1afe140afed6d802d28000a06428000000f10ff0f780025e808c834000b40f38001f1c0019100019a8fc1a01941ebc2980001510d4000001708000000002a5aac0000000
  | 9 => 0x9b213da099d15e5cca4fa60e4b48b32c323b1f09ad599a2d8eb87f01c99dc0a86f23a08d10617707b9b91fa938000057000000040c310c3121a44072149a3829e86200020e13400b0000200f82c08b22b02560d79198c54001844ebe5000011d8001278001f22a604f96d062966a2c0002bb00000021b800284800033cbd0fa0000000144002921cd1670059722c286e19d80002d97893180020c83a8e88189ee44049f5e680014586bc001160001349ccd2485d000111000000000013c0000023e00024c0000001a540840000027e8e95e5a000be9f3a33d9b8e600000005fc031d8c0010457480d904ab11ae22584102187ae188240f882120b2b796225720f9cbdcc8798598d0d582d500006509e16380006b4508b507503380029f80000009e4c4c7b2ba0001c42ae0001078aec00000019abc85280003c2c60001ff1070148de8d7e2b80000002bc000ac8002168001c2cc700012600006c03504394f2bf04281e8e221700808b8001dfc0010e639a3a8001560341f915d05f9d009cc5608700000f11ba085ba9d580002280008a40002b1320001f7e37a9d0002889e520cc6680000000a0e722487d42a00007a4e00160c6d2e2cccaead38779d79b04000fc861808a7903090f800000000123c3eab60000d3a751d606d8000000eb000000169d419ec90180006026213fd628a8a7114428a8000000000000000001b51a295bac713f9da8000f99f788a24a9c20badcb8ad0001dec0000522400001200000000013e00000019d2d60000cb21cc4e0a480009285c8000a0a6980001b800069a67800028e478001b680013b4e82969732d21ae9fee8998940000016ea748000748d418a97e09162209b0ef0dbacc270299992208a730889eba1a9d82a51d22390d09de6018f61950011990002b293d00012e4002549a729e00000000023280018c80020b61a000000000113c001c7c2c80000014280000020200012300000000000028d04600000018b80018680021601f8e38001df0000e78001c6a239ec2a68002438dd0002b380000014c96c28100000013b0000000000001b00000000000e64020001af5818ec2372d1d90056a530f41d98000000b800000003d0000000002102b68dc0000388002d48cea6485249495f9d50df4ae28283bcd75bd0a0c0021f8002740001e080029109d0ec57b80019700000016a010a419e48000001b0d28c8eaad04f2319ab8cf0102c5025c002d00001fc292abf9591eb1269cd4a18000239a782086800000ec89a7e0e92288dda5fab487a9ce6981f70000002c40000795dc80000000009d4002631d0866400000000000000103c3b8000aa9c88000000bcaa22ab9a4c000000c740000029580000000020942b45400000000000000023880000000011b24307e14700028e98b1b44002320000cf4001ef8e6c0
  | 10 => 0xc91402609b4a0d00000015529ca4c9b092280008e09fc440001fb8002cd2c11b30d91bf1cb2518248ecde90290c2e7098e01589194511325b98914b24b8c1e6827d86d10e8ee6738c95da07817511a90fda44521f41eac39a00a460938ab15b26f10342e2491241af0965e291487d0ed8ef93300002e984108a84174081d928c7ac909762d1f149e913a06cb004889ee05e3f1958de2b997a146abc10aa6f96f22aa292618f503900000021280000000383d8001980001a980024d0348d60000c28000000000000f58259989ff9630701ade8195885a12013599c05a8daa7ca9f2aa0a31120ae6ada21a1300c9e60000641758c182961d07909f215954a5c0112069961ea95590247bc090000cb93c8970518a500003f00010eda34689d1e400000000aba0d45640000004a619860954eb3101ecfa5b15e9de990ac485743c457c4b0d280023c0960416cf2330f2e7c1f7605984889d3a54f82503e22316521d8328129da4808b08001ea4f92149431b165e1839bd8001e21568fb80008680012d40000007899c86a1a2c1dcb9c000bf1538000000001a80001caca203300000027a25a0119bc5e79f489300723087124107c07340f400014c5e9029a386f83fa8f0001e0069066d520c10282d100000017013f0a9a0e8000001fdc6c6a49b98f28905f02c7a8c07e8e8c07a5880004c2488aa1ea2d858293a26da092350fe2344ea62a03368097c29c26e8fa81305f0191a518121e826084a7b816ac38000958b8d9e1878f4a050001bc06e9f592f21184ac6a90400016e11e997849e0280017d1cf00012bc07cf31f288580000000000011a5f60000e06150531d308f5690000221c36ab1e894ba931e38b380015107b454d310002688a7498875a5201e40029ba778fda341ba0001fcc7f81d6201389db87a23d8ada8f9d190005f4f00b8400073cc000000000000009da3b91c89522f072d9301a1a10000000000002552b917a84a90da5788267f939244a1f13bd7e81f161a1c87c91a2450ea9a580022514d1502cda970df8c7e182cd5e80498b908908ed6b00000003b5dd18098d1fc40023014a80002b9b583207396781e0a72108d04230c84000ed56800018c00002a9e666b89dc382511245872ac92d9601cea948000baa208af1c600011808f81d1df5dc1fd00000012cc0000e4f09d29d9d361404a904ea53800000082000006a97ad8cee1e30001c4872979800065ca794a04813bad680c0000002420000001d100000000005e1c09e721208a9f8041d378001eee508000000001dd86383010c80022f80000010cdbb80001c0838002a9936c000911f522e8000001a89fe9480b68492638e54bb8a292f48297927600003600016a86ce8e18da8babe0154000c88c590c6ca856c55e4ea2ec048468e30fea0c40024712c03700005c0001e6d9f
  | 11 => 0xb7a89ec6abcdfd5091f86d25739e100fe831c30f9de54000c60510001461aa06baa1842169ad415a00019d481a1b1271648674000001f12b5a2f4f70a6c000
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xd6250010004fd76cc01009ebe64cc010006bd64cc01003ede63cc010006dd63cc010096ee62cc010006ed62cc010004ff768c01003cfd768c01008ebe648c010006bd648c01003ede638c010006dd638c010076ee628c010006ed628c010005f6718c010005f5718c010004ff764c010005bf744c010025bc744c010086be644c010006bd644c01003ede634c010006dd634c01007eee624c010006ed624c01003cff760c010004fe760c010004fd760c01003cfc760c010025be740c010005bd740c01006ebe640c010006bd640c01003ede630c010006dd630c01001dee720c010005ed720c010066ee620c010006ed620c010005f6710c010005f5710c01005ebe64c4010006bd64c4010006de63c4010006dd63c4010036ee62c4010006ed62c4010036f576c4010007b664c4010007b564c4010006f763c4010007d663c4010006f563c4010007d563c4010006d563c4010196f762c4010197e662c4010196f562c4010007e562c4010006e562c4010197b742c4010197b542c4010197d732c4010197d532c4010056be6484010006bd6484010006de6384010006dd638401002eee6284010006ed6284010185f5718401017ef6618401001df9768401002ef9768401000cf97684010007ba6484010007b96484010007da6384010007d9638401018efb628401018fea628401018ef96284010007e96284010006e9628401018fbb428401018fb9428401018fdb328401018fd93284010185f9718401017efa6184010007f26184010004ff7644010005bf7444010025bc744401004ebe6444010006bd6444010005df7344010005dc7344010006de6344010006dd6344010005ef724401001dec7244010046ee6244010006ed6244010005f77644010006f77644010004f77644010007b77444010007b47444010007b66444010007b56444010007d77344010007d47344010006f76344010007d66344010006f56344010007d56344010006d56344010007e77244010157e47244010156f76244010157e66244010156f56244010007e56244010006e56244010157b74244010157b54244010157d73244010157d53244010175f7704401016ef66044010007f24044010007f14044010007f33044010007f03044010157f22044010157f12044010005fb7644010006fb7644010004fb7644010007bb7444010007b87444010007ba6444010007b96444010007db7344010007d87344010007da6344010007d96344010007eb7244010157e87244010156fb6244010157ea6244010156f96244010007e96244010006e96244010157bb4244010157b94244010157db3244010157d93244010165fb7144010007f3714401015efa6144010007f26144010007f24144010007f14144010007f33144010007f03144010157f22144010157f12144010
  | 1 => 0x8c10005ed7218c10006ee6218c1003cff7690c10004fe7690c10004fd7690c1003cfc7690c101467e6590c100067d6590c10016be6490c10006bd6490c1003ede6390c10006dd6390c1013eee6290c10004ff7650c10004fe7650c10004fd7650c10004fc7650c100057f7550c1019d7c7550c101367e6550c100067d6550c10016be6450c10006bd6450c1003ede6350c10006dd6350c1012eee6250c1001def765881001eef765881000cef7658810007ae7458810007ad7458810006ef6458810006ee6458810007ae6458810006ae6458810006ed6458810007ad6458810006ad6458810006ec6458810007ce7358810007cd7358810006ef6358810006ee6358810007ce6358810006ce6358810006ed6358810007cd6358810006cd6358810006ec6358810006ef7458810006ee7458810006ae7458810006ed7458810006ad7458810006ec7458810006ee5458810006ed5458810006ec5458810006ef7358810006ee7358810006ce7358810006ed7358810006cd7358810006ec7358810006ef4358810006ee4358810006ed4358810006ec435881001eef7158810006ee715881001eed715881001eec7158810006ef4158810006ec415881001eef7058810006ee705881001eed705881001eec7058810006ef4058810006ec405881001eec105881005cff7690410014fd76904101267e65904100067d6590410016be6490410006bd6490410006de6390410006dd639041011eee6290410006ed6290410005fa7090410005f9709041005cff76504100057f755041019d7c75504101167e65504100067d6550410016be6450410006bd6450410006de6350410006dd635041010eee6250410006ed6250410004fd76cc410025be74cc410005bd74cc410106be64cc410006bd64cc41003ede63cc410006dd63cc41001dee72cc410005ed72cc4100feee62cc410006ed62cc410004ff768c41003cfd768c410025be748c410005bd748c4100f6be648c410006bd648c41003ede638c410006dd638c4100deee628c410006ed628c4101aef6618c410005fa708c410005f9708c410004ff764c4100eebe644c410006bd644c41003ede634c410006dd634c4100e6ee624c410006ed624c4101a6f6614c41003cff760c410004fd760c4100d6be640c410006bd640c41003ede630c410006dd630c4100ceee620c410006ed620c410005fa700c410005f9700c410054ff7690010014fe7690010014fd7690010024fc769001019d7e75900100057d75900100c67e65900100067d6590010016be6490010006bd6490010006de6390010006dd63900100beee6290010006ed6290010005f67190010005f57190010054ff76500100ae7e65500100067d6550010016be6450010006bd6450010006de6350010006dd63500100a6ee6250010006e
  | 2 => 0x6ee62d8c10014fe74d8c10006be74d8c10014be74d8c10004fd74d8c10006bd74d8c10004bd74d8c10014fc74d8c10004ff72d8c1000cfe72d8c10006ee72d8c1000cee72d8c10004fd72d8c10006ed72d8c10004ed72d8c1000cfc72d8c10006bf42d8c10006bd42d8c10006df32d8c10006dd32d8c10004fe71d8c10006f671d8c10004fe70d8c10006fa70d8c10004fd7698c10006be6498c10006bd6498c10006df6398c10006ee6298c10004dd7698c10006df6498c10006de6498c100079e6498c100069e6498c10006dd6498c100079d6498c100069d6498c10006dc6498c10005df7298c10005dd7298c10006df6298c10006de6298c10007ce6298c10006ce6298c10006dd6298c10006dc6298c100079f4298c100079d4298c1003edf7498c1003ede7498c1003edd7498c1003edc7498c10006de5498c10006dd5498c10006dc5498c1003edf7298c1003cdf7298c1003ede7298c1003edd7298c10004dd7298c1003edc7298c10006df4298c100069f4298c10006de4298c10006dd4298c100069d4298c10006dc4298c1003ede7198c1003edc7198c10006df4198c10006dc4198c10006df2198c10006de2198c10006dd2198c10006dc2198c1003ede7098c1003edc7098c10006df4098c10006dc4098c10006df2098c10006de2098c10006dd2098c10006dc2098c1003cff7658c10006be6458c10006bd6458c10006ee6258c10004ff7458c10014fe7458c10014fc7458c10006df7358c10006df4358c10006dc4358c10004ff7258c1000cfe7258c10004fd7258c1000cfc7258c10006bf4258c10006bd4258c10006df3258c10006de3258c10006dd3258c10006dc3258c1003cff7158c1003cfd7158c1003cff7058c1003cfd7058c10006df7658c1003cdf7658c10006df6458c10006de6458c100079e6458c100069e6458c10006dd6458c100079d6458c100069d6458c10006dc6458c10005df7258c10005dd7258c10006df6258c10006de6258c10007ce6258c10006ce6258c10006dd6258c10006dc6258c100079f4258c100079d4258c10006df7458c10006de7458c10006dd7458c10006dc7458c10006de5458c10006dd5458c10006dc5458c10006df7258c10004df7258c10006de7258c10006dd7258c10004dd7258c10006dc7258c10006df4258c100069f4258c10006de4258c10006dd4258c100069d4258c10006dc4258c10006de7158c10006dc7158c10006df4158c10006dc4158c10006df2158c10006de2158c10006dd2158c10006dc2158c10006de7058c10006dc7058c10006df4058c10006dc4058c10006df2058c10006de2058c10006dd2058c10006dc2058c10006dc1058c10025be7418c10005bd7418c10006be6418c10006bd6418c10005de7318c1003ede6318c10006dd6318c1001dee721
  | 3 => 0xd72d9010006ee62d90100b4fe75d90100067e75d90100b47e75d9010004fd75d90100067d75d90100047d75d90100b4fc75d9010024fd74d901003cfe73d9010006de73d901003cde73d9010004fd73d9010006dd73d9010004dd73d9010004ff72d901000cfe72d9010006ee72d901000cee72d9010004fd72d9010006ed72d9010004ed72d901000cfc72d90100067f52d90100067d52d9010026bf42d9010006bd42d9010006df32d9010006dd32d901005cfe71d9010006f671d9010054fe70d9010006fa70d9010004bd7699010006bf6599010006be65990100073e65990100063e6599010006bc6599010025bf7299010005bd7299010006bf6299010006be6299010007ae6299010006ae6299010006bd6299010006bc62990100073f52990100073d52990100079f32990100079d3299010014ff76590100067e6559010026bc6459010006ee6259010004ff75590100b4fe75590100b4fc7559010006bf7459010006bf5459010026be5459010026bc5459010004ff735901003cfc7359010026bf4359010026bc4359010004ff725901000cfe7259010004fd725901000cfc72590100067f52590100067d5259010026bf4259010006be4259010006bd4259010026bc4259010006df3259010006dd3259010014ff7159010014fd7159010024fc7159010026bc4159010014ff7059010014fd7059010024fc7059010026bc4059010025bf7659010026bf7659010014bf7659010006bf6559010006be65590100073e65590100063e6559010006bd65590100073d65590100063d6559010006bc6559010005bf7259010005bd7259010006bf6259010006be6259010007ae6259010006ae6259010006bd6259010006bc62590100073f52590100073d52590100079f32590100079d3259010006bf7559010006be7559010006bd7559010006bc7559010006bf7359010006be7359010006bd7359010006bc7359010006bf5359010006bc5359010006bf7259010004bf7259010006be7259010006bd7259010004bd7259010006bc7259010006bf52590100063f5259010006be5259010006bd52590100063d5259010006bc5259010006bf32590100069f3259010006be3259010006bd32590100069d3259010006bc3259010026bf7159010006be7159010006bc7159010006bf5159010006bc5159010006bf2159010006be2159010006bd2159010006bc2159010026bf7059010006be7059010006bc7059010006bf5059010006bc5059010006bf2059010006be2059010006bd2059010006bc2059010006bc1059010004ff7655010004fe7655010004fd7655010004fc7655010016be6455010006bd64550100273c545501014eee6255010025be74d8c10005bd74d8c10006be64d8c10006bd64d8c1001dee72d8c10005ed72d8c10
  | 4 => 0xc5101e7b7428c5101e7b5428c5101e7d7328c5101e7d5328c510005f6708c5101e7f2208c5101e7f1208c51003cfc764c510006bf644c5100eebc644c510006df634c51003edc634c510006ef624c5100e6ec624c510005fb704c510005f8704c51003ef4764c51003cf4764c510007b7644c510007b4644c510007d7734c510007d7634c51003ef6634c51003ef4634c510007d4634c5101ddf7724c5101ddf5724c510007e7624c5101d7e4624c5101d7b7424c5101d7b5424c5101d7d7324c5101d7d5324c510007f3704c510005f4704c510007f0704c510005f0704c5101d7f2204c5101d7f1204c510004fe760c510006bf640c5100d6bc640c510006df630c51003edc630c510006ef620c5100ceec620c5101cdf6710c510007d5310c51005cfe76901101c57e75901100057d75901100067f65901100c67c6590110006bf6490110016bc6490110006df6390110006dc6390110006ef62901100beec6290110014ff765011004cfd7650110014fc76501100067f65501100ae7c6550110006bf6450110016bc6450110006df6350110006dc6350110006ef62501100a6ec6250110005f77150110005f47150110004fe76cc110006bf64cc11009ebc64cc110006df63cc11003edc63cc110006ef62cc110096ec62cc110005f671cc110005f571cc110007d531cc110004fe768c110006bf648c11008ebc648c110006df638c11003edc638c110006ef628c110076ec628c110007d6318c11003cff764c110004fd764c11003cfc764c110005bf744c11004dbc744c110006bf644c110086bc644c110006df634c11003edc634c110006ef624c11007eec624c110005f7714c110005f4714c110007d5314c110004fe760c11004dbe740c110005bd740c110006bf640c11006ebc640c110006df630c11003edc630c110045ee720c110005ed720c110006ef620c110066ec620c110005f6710c110005f5710c110007d6310c110006bf64c411005ebc64c4110006df63c4110006dc63c4110006ef62c4110036ec62c4110007bb64c4110007b864c4110007db63c4110007d863c411015dfb72c411015df972c4110007eb62c41101bfe862c41101bfbb42c41101bfb942c41101bfdb32c41101bfd932c4110007f231c4110007f131c41101bff221c41101bff121c4110006bf6484110056bc6484110006df6384110006dc6384110006ef628411002eec6284110045f67684110007b76484110007b46484110005f77384110005f57384110007d76384110007d4638411016df7728411016df57284110007e762841101b7e462841101b7b742841101b7b542841101b7d732841101b7d53284110007f360841101b7f220841101b7f1208411019d7e75d90100057d75d9010026be64d9010005de73d9010005dd73d901001dee72d9010005e
  | 5 => 0x4dd7218d1003edc7218d10006df4218d100069f4218d10006de4218d10006dd4218d100069d4218d10006dc4218d1003edf7118d1003edd7118d1003ed57118d10006df4118d10006dc4118d10006df2118d10006de2118d10006dd2118d10006dc2118d1003edf7018d1003edd7018d10006df4018d10006dc4018d10006df2018d10006de2018d10006dd2018d10006dc2018d10006dd1018d1003cff7690d10004fe7690d10004fd7690d1003cfc7690d100067f6590d101467c6590d10006bf6490d10016bc6490d10006df6390d1003edc6390d1013eec6290d10005f67190d10005f57190d10004ff7650d10004fe7650d10004fd7650d10004fc7650d100057f7550d101c57c7550d100067f6550d101367c6550d10006bf6450d10016bc6450d10006df6350d1003edc6350d1012eec6250d10045ee76d8910046ee76d891000cee76d8910007af74d8910007ac74d8910006ef64d8910007af64d8910006af64d8910006ee64d8910006ed64d8910006ec64d8910007ac64d8910006ac64d8910007cf73d8910007cc73d8910006ef63d8910007cf63d8910006cf63d8910006ee63d8910006ed63d8910006ec63d8910007cc63d8910006cc63d8910007e771d8910047e471d8910007eb70d8910047e870d8910006ef74d8910006af74d8910006ee74d8910006ed74d8910006ec74d8910006ac74d8910006ee54d8910006ed54d8910006ec54d8910006ef73d8910006cf73d8910006ee73d8910006ed73d8910006ec73d8910006cc73d8910006ef43d8910006ee43d8910006ed43d8910006ec43d8910006ef71d8910046ee71d8910046ed71d8910046ec71d8910006ef41d8910006ec41d8910006ef70d8910046ee70d8910046ed70d8910046ec70d8910006ef40d8910006ec40d8910046ed10d8910054fe76905100067f65905101267c6590510006bf6490510016bc6490510006df6390510006dc6390510006ef629051011eec6290510014fc76505100057f75505101c57c75505100067f65505101167c6550510006bf6450510016bc6450510006df6350510006dc6350510006ef625051010eec6250510005fb7050510005f87050510004fe76cc51004dbe74cc510005bd74cc510006bf64cc510106bc64cc510006df63cc51003edc63cc510045ee72cc510005ed72cc510006ef62cc5100feec62cc510005fa70cc510005f970cc510004fe768c51004dbe748c510005bd748c510006bf648c5100f6bc648c510006df638c51003edc638c510006ef628c5100deec628c510005f6768c510006f6768c510007b6748c510007b5748c510007b7648c510007b4648c5101ddf5738c510007d7638c51003ef6638c51003ef4638c510007d4638c51003ed4638c5101cdf7728c5101cdf5728c510007e7628c5101e7e4628
  | 6 => 0xe7655110004fd7655110004fc7655110006bf6455110016bc645511004f3c545511014eec625511003cfe76d8d10006bf64d8d10006bc64d8d10006ec62d8d10014fe74d8d10004fd74d8d10014fc74d8d10006df43d8d10006dc43d8d10004ff72d8d1000cfe72d8d10004fd72d8d1000cfc72d8d10006bf42d8d10006bd42d8d10006df32d8d10006de32d8d10006dd32d8d10006dc32d8d1003cfe71d8d1003cfc71d8d1003cfe70d8d1003cfc70d8d1003cde76d8d10006df64d8d100079f64d8d100069f64d8d10006de64d8d10006dd64d8d10006dc64d8d100079c64d8d100069c64d8d10005df72d8d10005dd72d8d10006df62d8d10006de62d8d10006dd62d8d10006dc62d8d10007cc62d8d10006cc62d8d100079f42d8d100079d42d8d10007d771d8d10007d621d8d10007d521d8d10007da20d8d10007d920d8d10006df74d8d10006de74d8d10006dd74d8d10006dc74d8d10006de54d8d10006dd54d8d10006dc54d8d10006df72d8d10004df72d8d10006de72d8d10006dd72d8d10004dd72d8d10006dc72d8d10006df42d8d100069f42d8d10006de42d8d10006dd42d8d100069d42d8d10006dc42d8d10006df71d8d10006dd71d8d10006df41d8d10006dc41d8d10006df21d8d10006de21d8d10006dd21d8d10006dc21d8d10006df70d8d10006dd70d8d10006df40d8d10006dc40d8d10006df20d8d10006de20d8d10006dd20d8d10006dc20d8d1004dbe7498d10005bd7498d10006bf6498d10006bc6498d10006df6398d10045ee7298d10005ed7298d10006ec6298d10005bf7458d1004dbc7458d10006bf6458d10006bc6458d10005ef7258d10045ec7258d10006ec6258d10004ff7458d10006bf7458d10004bf7458d10014fe7458d10014fc7458d10006bc7458d10014bc7458d10006df7358d10004ff7258d10006ef7258d10004ef7258d1000cfe7258d10004fd7258d1000cfc7258d10006ec7258d1000cec7258d10006bf4258d10006bd4258d10006df3258d10006dd3258d10004ff7158d10006f77158d10004ff7058d10006fb7058d10004fe7618d10006bf6418d10006bc6418d1003ede6318d10006dd6318d10006ec6218d10005de7618d10006de7618d10004de7618d10006df6418d100079f6418d100069f6418d10006de6418d10006dd6418d10006dc6418d100079c6418d100069c6418d10005df7218d10005dd7218d10006df6218d10006de6218d10006dd6218d10006dc6218d10007cc6218d10006cc6218d100079f4218d100079d4218d10007d57118d10007d62118d10007d52118d10007da2018d10007d92018d1003edf7418d1003ede7418d1003edd7418d1003edc7418d10006de5418d10006dd5418d10006dc5418d1003edf7218d1003cdf7218d1003ede7218d1003edd7218d10
  | 7 => 0x9110006ec62d91100b4fe75d9110004fd75d91100b4fc75d9110006bf54d911004ebe54d911004ebc54d911003cfe73d9110004fd73d911004ebf43d911004ebc43d9110004ff72d911000cfe72d9110004fd72d911000cfc72d91100067f52d91100067d52d911004ebf42d9110006be42d9110006bd42d911004ebc42d9110006df32d9110006dd32d9110014fe71d911004cfd71d9110014fc71d911004ebf41d9110014fe70d911004cfd70d9110014fc70d911004ebf40d911004dbe76d9110014be76d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bc65d9110005bf72d9110005bd72d9110006bf62d9110006be62d9110006bd62d9110006bc62d9110007ac62d9110006ac62d91100073f52d91100073d52d91100079f32d91100079d32d9110007b621d9110007b521d9110007ba20d9110007b920d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d9110006bc53d9110006bf72d9110004bf72d9110006be72d9110006bd72d9110004bd72d9110006bc72d9110006bf52d91100063f52d9110006be52d9110006bd52d91100063d52d9110006bc52d9110006bf32d91100069f32d9110006be32d9110006bd32d91100069d32d9110006bc32d9110006bf71d911004ebe71d9110006bd71d9110006bf51d9110006bc51d9110006bf21d9110006be21d9110006bd21d9110006bc21d9110006bf70d911004ebe70d9110006bd70d9110006bf50d9110006bc50d9110006bf20d9110006be20d9110006bd20d9110006bc20d91100057f75591101c57c75591100067f655911004ebc6459110005df7359110005dc7359110005ef7259110045ec7259110006ec6259110004ff75591100067f75591100047f75591100b4fe75591100b4fc75591100067c75591100b47c755911004cff7459110006bf7459110004ff7359110006df7359110004df735911003cfc7359110006dc735911003cdc7359110004ff7259110006ef7259110004ef725911000cfe7259110004fd725911000cfc7259110006ec725911000cec72591100067f52591100067d525911004ebf4259110006bd4259110006df3259110006dd3259110054ff7159110006f7715911005cff7059110006fb7059110005be761911004ebe7619110004be7619110006bf65191100073f65191100063f6519110006be6519110006bd6519110006bc65191100073c65191100063c651911004dbf7219110005bd7219110006bf6219110006be6219110006bd6219110006bc6219110007ac6219110006ac62191100073f52191100073d52191100079f32191100079d3219110007b62119110007b52119110007ba2019110007b92019110004ff7655110004f
  | 8 => 0x56bf42d9210006bd42d9210006df32d9210006dd32d9210006f571d9210056bc41d9210006fa70d9210056bf40d9210014ff7659210056bc6459210004ff75592100b4fe75592100b4fc7559210006bf7459210006bf5459210056bc5459210004ff735921003cfc7359210056bf4359210004ff725921000cfe7259210004fd725921000cfc72592100067f52592100067d5259210056bf4259210006bd4259210006df3259210006dd3259210056bf4159210056bc4059210004ff7655210004fe7655210004fd7655210004fc7655210006bf6455210016bc64552100573c5455210014fe74d8e10004fd74d8e10014fc74d8e10004ff72d8e1000cfe72d8e10004fd72d8e1000cfc72d8e10006bf42d8e10006bd42d8e10006df32d8e10006dd32d8e10006f571d8e10006fa70d8e10004fd7698e10006df6398e1003cff7658e10005bf7458e10055bc7458e10004ff7458e10006bf7458e10004bf7458e10014fe7458e10014fc7458e10006bc7458e10014bc7458e10006df7358e10004ff7258e1000cfe7258e10004fd7258e1000cfc7258e10006bf4258e10006bd4258e10006df3258e10006dd3258e10055be7418e10005bd7418e1003ede6318e10006dd6318e1002dee7218e10005ed7218e1003cff7690e10004fe7690e10004fd7690e1003cfc7690e10006bf6490e10016bc6490e10004ff7650e10004fe7650e10004fd7650e10004fc7650e100057f7550e101f57c7550e10016be6450e10006bd6450e1004cfd7690610006bf6490610016bc6490610014ff76506100057f75506101f57c7550610016be6450610006bd6450610005fb7050610005f87050610055be74cc610005bd74cc61003ede63cc610006dd63cc61002dee72cc610005ed72cc610005fa70cc610005f970cc610055be748c610005bd748c610006df638c61003edc638c61003cff764c61003ede634c610006dd634c610005fb704c610005f8704c610006df630c61003edc630c610014fe7690210014fd76902101f57e75902100057d7590210016be6490210006bd6490210005f67190210005f57190210024ff7650210006bf6450210016bc6450210006df63cc21003edc63cc21003cfd768c21003ede638c210006dd638c210005f6718c210005f5718c210005bf744c210055bc744c210006df634c21003edc634c210055be740c210005bd740c21003ede630c210006dd630c21002dee720c210005ed720c210005f6710c210005f5710c210005f576c4210006f576c4210006f763c4210006f563c42101eef762c42101eef562c42101efb742c42101efb542c42101efd732c42101efd532c4210005f976c4210006f976c421017dfb72c421017df972c42101efbb42c42101efb942c42101efdb32c42101efd932c4210014fe76d911004ebe64d
  | 9 => 0xe74d8f10014be74d8f10004fd74d8f10006bd74d8f10004bd74d8f10014fc74d8f10004ff72d8f1000cfe72d8f10004fd72d8f1000cfc72d8f10006bf42d8f10006bd42d8f10006df32d8f10006dd32d8f10006f671d8f10006f970d8f10004fd7698f1005dbe7498f10005bd7498f10006df6398f10035ee7298f10005ed7298f1003cff7658f10004ff7458f10014fe7458f10014fc7458f10006df7358f10004ff7258f1000cfe7258f10004fd7258f1000cfc7258f10006bf4258f10006bd4258f10006df3258f10006dd3258f1003ede6318f10006dd6318f1003cff7690f10004fe7690f10004fd7690f1003cfc7690f10016be6490f10006bd6490f10005f67190f10005f57190f10004ff7650f10004fe7650f10004fd7650f10004fc7650f100057f7550f101fd7c7550f10006bf6450f10016bc6450f10014fd7690710016be6490710006bd6490710005fa7090710005f97090710024ff76507100057f75507101fd7c7550710006bf6450710016bc645071005dbe74cc710005bd74cc710006df63cc71003edc63cc710035ee72cc710005ed72cc71003cfd768c71005dbe748c710005bd748c71003ede638c710006dd638c710005fa708c710005f9708c71003ef5768c71003cf5768c710007b6748c710007b5748c71003ef6638c710007d6638c710007d5638c71003ef4638c71020df7728c71020df5728c7101afb7428c7101afb5428c7101afd7328c7101afd5328c710005f6708c710007f2708c710007f1708c710006df634c71003edc634c710005f7764c710006f7764c710007d7734c710007d7634c71003ef6634c71003ef4634c710007d4634c710205f7724c710205f5724c7101a7b7424c7101a7b5424c7101a7d7324c7101a7d5324c710005f4704c71003ede630c710006dd630c710007d5310c710005fa700c710005f9700c71004cfd76903101fd7e75903100057d7590310006bf6490310016bc6490310014ff7650310014fc7650310016be6450310006bd6450310005f77150310005f4715031003ede63cc310006dd63cc310005f671cc310005f571cc310007d531cc310006df638c31003edc638c310007d6318c31003cff764c310005bf744c31005dbc744c31003ede634c310006dd634c310005f7714c310005f4714c310007d5314c31005dbe740c310005bd740c310006df630c31003edc630c310035ee720c310005ed720c310005f6710c310005f5710c310007d6310c3101f57e75d92100057d75d9210056be64d92100b4fe75d92100067e75d92100b47e75d9210004fd75d92100067d75d92100047d75d92100b4fc75d9210054fd74d9210056be54d921003cfe73d9210004fd73d9210056bc43d9210004ff72d921000cfe72d9210004fd72d921000cfc72d92100067f52d92100067d52d9210
  | 10 => 0x843003ef6305843003ef5305843003ef43058430006f72058430006f62058430006f52058430006f42058430004ff769043003cfe7690430004fd76904301267e65904300067d6590430016be6490430006bd649043011eee6290430006ed6290430006f66190430006f56190430004ff7650430004fd765043003cfc76504300057f755043022d7c75504301167e65504300067d6550430016be6450430006bd6450430005df735043003ddc735043010eee6250430006ed6250430006f66150430006f5615043003ddd768c430006dd768c430004dd768c4300079e748c4300079d748c43003f9e648c43003f9d648c430245df728c430245dd728c43003edf628c43003fce628c43023edd628c43003fcd628c430006cd628c43023f9f428c43023f9d428c43003dde718c43003fd6718c43003fd6618c430006dd618c43003fd5618c430006d5618c430005dd708c430236de608c43003fda608c43008cff769003003cfe7690030014fd769003003cfc769003022d7e75900300057d75900300c67e65900300067d6590030016be6490030006bd649003003dde7390030005dd73900300beee6290030006ed6290030006f66190030006f5619003008cff76500300ae7e65500300067d6550030016be6450030006bd64500300a6ee6250030006ed6250030006f66150030006f5615003003ddf764c030006df764c030004df764c0300079f744c0300079c744c03003f9e644c03003f9d644c030225df724c030225dd724c03003edf624c03003fce624c03021edd624c03003fcd624c030006cd624c03021f9f424c03021f9d424c030005dc714c03003fd6614c030006dd614c03003fd5614c030006d5614c03003ddf704c03003fdb704c030216de604c03003fda604c03005ebe64d93100b4fe75d9310004fd75d93100b4fc75d931005cfd74d9310006bf54d931005ebc54d931003cfe73d9310004fd73d931005ebf43d9310004ff72d931000cfe72d9310004fd72d931000cfc72d93100067f52d93100067d52d931005ebf42d9310006bd42d9310006df32d9310006dd32d9310006f671d931005ebf41d9310006f970d931005ebc40d9310014ff76593100057f75593101fd7c755931005ebc6459310004ff75593100067f75593100047f75593100b4fe75593100b4fc75593100067c75593100b47c7559310006bf745931005ebe5459310004ff735931003cfc735931005ebc4359310004ff725931000cfe7259310004fd725931000cfc72593100067f52593100067d525931005ebf4259310006bd4259310006df3259310006dd325931005ebc415931005ebf4059310004ff7655310004fe7655310004fd7655310004fc7655310016be6455310006bd645531005f3c545531005dbe74d8f10005bd74d8f10014fe74d8f10006b
  | 11 => 0x3cfe7655030004fd765503003cfc7655030016be6455030006bd645503006f3c5455030005df735503003ddc735503014eee6255030006ef7458830006ee7458830006ae7458830006ed7458830006ad7458830006ec7458830006ee5458830006ed5458830006ec545883003eef735883003eee735883003ece735883003eed7358830066cd735883003eec735883003eef435883003eee435883003eed435883003eec4358830006ef7158830006ee7158830006ed7158830006ec7158830006ef4158830006ec415883003eef315883003eee315883003eed315883003eec315883003ecc3158830066ef7058830006ee7058830066ed7058830066ec7058830006ef4058830006ec405883003eef305883003ecf305883003eee305883003eed305883003eec3058830014fe7498430004fd7498430014fc7498430004ff729843000cfe7298430004fd729843000cfc7298430006bf4298430006bd429843003edf3298430006dd329843003ef67198430006f74198430006f4419843003ef7319843003ef43198430006f72198430006f62198430006f52198430006f42198430006f77498430006f67498430006f57498430006f47498430006f65498430006f55498430006f4549843003ef6739843003ef5739843003ef4739843003ef7439843003ef6439843003ef5439843003ef44398430006f77298430006f67298430006f57298430006f47298430006f74298430006b74298430006f64298430006f54298430006b54298430006f4429843003ef7329843003ed7329843003ef6329843003ef53298430006d5329843003ef43298430006f67098430006f47098430006f74098430006f4409843003ef7309843003ef6309843003ef5309843003ef43098430006f72098430006f62098430006f52098430006f42098430004ff7458430014fe7458430014fc7458430004ff725843000cfe7258430004fd725843000cfc7258430006bf4258430006bd425843003edf3258430006dd325843003ef77158430006f74158430006f4415843003ef7315843003edc315843003ef4315843003ed43158430006f72158430006f62158430006f52158430006f4215843003edf3058430006f77458430006f67458430006f57458430006f47458430006f65458430006f55458430006f4545843003ef7735843003ef6735843003ef4735843003ef7435843003ef6435843003ef5435843003ef44358430006f77258430006f67258430006f57258430006f47258430006f74258430006b74258430006f64258430006f54258430006b54258430006f4425843003ef7325843003ed7325843003ef6325843003ef53258430006d5325843003ef43258430006f67058430006f47058430006f74058430006f4405843003ef7305843003ed7305
  | 12 => 0xf64cc5300079c64cc53003ddf72cc53003fce72cc530275dd72cc53003fcd72cc530005cd72cc53026edf62cc53026edd62cc53026f9f42cc53026f9d42cc530006dc61cc530005de70cc53003edf60cc53003fdb60cc530085be748c530005bd748c530006bf648c5300f6bc648c530265dd738c530006f7618c530006f4618c530005fa708c530005f9708c530006bf644c5300eebc644c530006f7614c530006f4614c53003fd4314c530005fb704c530005f8704c5300079f644c5300079c644c530265df724c530265dd724c53025edf624c53025edd624c53025f9f424c53025f9d424c53003ddf714c53003fd7714c530007d7614c530006dc614c530007d4614c530007db704c530005dc704c530007d8704c53003edf604c53003fdb604c53009cfe76901302557e75901300057d75901300067f65901300c67c6590130006bf6490130016bc6490130014ff7650130084fd765013003cfc76501300067f65501300ae7c6550130006bf6450130016bc6450130005df735013003ddc7350130006bf648c13008ebc648c13003dfa708c13003efb608c1300079f648c1300079c648c130215df728c130215dd728c13024edf628c13024edd628c13024f9f428c13024f9d428c130005dd718c130006dc618c13003dde708c13003edf608c13003fdb608c130004ff75590300b4fe75590300b4fc755903003ebf7459030006bf545903006ebe545903006ebc545903003cff735903003cfe735903003cfd735903003cfc735903003ebe435903003ebc4359030004ff725903000cfe7259030004fd725903000cfc72590300067f52590300067d525903006ebf4259030006be4259030006bd425903006ebc425903003edf3259030006dd3259030004ff7159030004fc715903006ebf415903006ebc415903006cfc705903006ebc4059030006bf7559030006be7559030006bd7559030006bc755903003ebf735903003ebe735903003ebd735903003ebc735903003ebf535903003ebe535903003ebd535903003ebc5359030006bf7259030004bf7259030006be7259030006bd7259030004bd7259030006bc7259030006bf52590300063f5259030006be5259030006bd52590300063d5259030006bc525903003ebf325903003e9f325903003ebe325903003ebd32590300069d325903003ebc3259030006bf7159030006be7159030006bd7159030006bc7159030006bf5159030006bc515903003ebf315903003ebe315903003ebd315903003ebc3159030006bf2159030006be2159030006bd2159030006bc215903006ebf7059030006be7059030006bc7059030006bf5059030006bc505903003ebf305903003ebe305903003ebd305903003ebc3059030006bf2059030006be2059030006bd2059030006bc2059030004ff7655030
  | 13 => 0x9130006bc72d9130006bf52d91300063f52d9130006be52d9130006bd52d91300063d52d9130006bc52d9130286bf32d91300069f32d9130006be32d9130006bd32d91300069d32d9130286bc32d9130006bf71d9130006be71d9130006bd71d9130006bc71d9130006bf51d9130006bc51d9130286bf31d9130286bc31d9130006bf21d9130006be21d9130006bd21d9130006bc21d9130286bf70d9130086be70d9130006bd70d9130006bf50d9130006bc50d9130286bf30d9130286bc30d9130006bf20d9130006be20d9130006bd20d9130006bc20d91300057f75591302557c75591300067f6559130086bc6459130004ff75591300067f75591300047f75591300b4fe75591300b4fc75591300067c75591300b47c7559130084ff7459130006bf745913008cff7359130006df7359130004ff725913000cfe7259130004fd725913000cfc72591300067f52591300067d5259130086bf4259130006bd4259130006df3259130006dd3259130004ff7159130004fc715913009cff7059130006fb7059130005be7619130086be7619130004be7619130006bf65191300073f65191300063f6519130006be6519130006bd6519130006bc65191300073c65191300063c6519130085bf7219130005bd7219130006bf6219130006be6219130006bd6219130006bc62191300073f52191300073d52191300079f32191300079d321913027ebf601913027fbb301913027fb83019130004ff7655130004fe7655130004fd7655130004fc7655130006bf6455130016bc64551300873c5455130014fc7650d300057f7550d302557c7550d300067f6550d301367c6550d30006bf6450d30016bc6450d30005fb7050d30005f87050d30006bf64d8530006bc64d8530014fe74d8530004fd74d8530014fc74d8530004ff72d853000cfe72d8530004fd72d853000cfc72d8530006bf42d8530006bd42d8530006df32d8530006dd32d8530006f721d8530006f421d8530085be7498530005bd7498530006bf6498530006bc6498530006f76198530005bf7458530085bc7458530006bf6458530006bc6458530005ef725853007dec7258530006bf6418530006bc6418530006f56118530014fe7418530004fd7418530014fc7418530004ff721853000cfe7218530004fd721853000cfc7218530006bf4218530006bd4218530006df3218530006dd3218530006f72118530006f42118530004fe7690530004fd7690530004fc76905300067f65905301267c6590530006bf6490530016bc649053003dde7390530005dd7390530004ff7650530004fe7650530004fc76505300057f75505302557c75505300067f65505301167c6550530006bf6450530016bc6450530005de76cc53003ede76cc530004de76cc53003f9e74cc53003f9d74cc5300079
  | 14 => 0x5bf745863008dbc7458630005ef7258630075ec7258630004ff7458630006bf7458630004bf7458630014fe7458630014fc7458630006bc7458630014bc7458630004ff7258630006ef7258630004ef725863000cfe7258630004fd725863000cfc7258630006ec725863000cec7258630006bf4258630006bd4258630006df3258630006dd3258630006f62158630006f5215863008dbe7418630005bd7418630075ee7218630005ed7218630006f56118630004ff7690630004fe7690630004fd7690630006bf6490630016bc6490630004ff7650630004fd7650630004fc76506300057f755063029d7c7550630016be6450630006bd6450630005df735063003ddc735063008dbe748c630005bd748c630006f6618c630006f5618c630005fa708c630005f9708c6300079e748c6300079d748c6302b5df728c6302b5dd728c630236df628c630236dd628c6302379f428c6302379d428c63003dde718c630007d6618c630006dd618c630007d5618c630007da708c630005dd708c630007d9708c63003ede608c630006f6614c630006f5614c630005fb704c630005f8704c630005dd760c63003edd760c63003ddf720c6302addd720c6302a6df620c6302a6dd620c6302a79f420c6302a79d420c63003fd6710c630006dd610c630005dd700c63003fda600c630014fe769023003cfd769023029d7e75902300057d7590230016be6490230006bd649023003dde7390230005dd739023006cff7650230006bf6450230016bc6450230005dd76cc23003edd76cc23003ddf72cc230295dd72cc23028edf62cc23028edd62cc23028f9f42cc23028f9d42cc230005de71cc230006dd61cc23003fda60cc230007da50cc230007d950cc230014fe76d9130086be64d91300b4fe75d9130004fd75d91300b4fc75d9130006bf54d9130086be54d9130086bc54d913003cfe73d9130084fd73d913003cfc73d9130086bf43d9130004ff72d913000cfe72d9130004fd72d913000cfc72d91300067f52d91300067d52d9130086bf42d9130006be42d9130006bd42d9130086bc42d9130006df32d9130006dd32d9130004fe71d9130004fd71d9130086bf41d9130086bc41d913003cfd70d9130086bf40d9130085be76d9130014be76d9130006bf65d91300073f65d91300063f65d9130006be65d9130006bc65d9130005bf72d9130005bd72d9130006bf62d9130006be62d9130006bd62d9130006bc62d91300073f52d91300073d52d91300079f32d91300079d32d9130287bb30d9130287b830d9130006bf75d9130006be75d9130006bd75d9130006bc75d9130006bf73d9130286be73d9130006bd73d9130286bc73d9130006bf53d9130286be53d9130286bc53d9130006bf72d9130004bf72d9130006be72d9130006bd72d9130004bd72d
  | 15 => 0xd425933003edf3259330006dd3259330004ff7159330004fc715933009ebc415933009ebf4059330004ff765533003cfe7655330004fd765533003cfc7655330016be6455330006bd645533009f3c5455330014fe7498730006be7498730014be7498730004fd7498730006bd7498730004bd7498730014fc7498730004ff729873000cfe7298730004fd729873000cfc7298730006bf4298730006bd429873003edf3298730006dd329873003ef6719873003edf319873003ef7319873003ef4319873003edc3098730004ff7458730014fe7458730014fc7458730004ff725873000cfe7258730004fd725873000cfc7258730006bf4258730006bd425873003edf3258730006dd325873003ef7715873003ef7315873003ef43158730004ff769073003cfe7690730004fd7690730016be6490730006bd649073003dde7390730005dd7390730004ff7650730004fd765073003cfc76507300057f75507302bd7c75507302d6bf6450730016bc645073003ddf764c730006df764c7302cddf724c7302cddd724c73003edf624c7302c6dd624c7302c79f424c7302c79d424c73003fd7714c73003fd7614c730006de614c73003fd4614c730005dc704c730084fd76903302bd7e75903300057d7590330286bf6490330016bc6490330014ff765033003cfc7650330016be6450330006bd6450330005df735033003ddc735033029d7e75d92300057d75d923008ebe64d92300b4fe75d92300067e75d92300b47e75d9230004fd75d92300067d75d92300047d75d92300b4fc75d923008cfd74d923008ebe54d9230006dd73d9230286be43d9230286bc43d9230004ff72d923000cfe72d9230004fd72d923000cfc72d92300067f52d92300067d52d923008ebf42d9230006bd42d9230006df32d9230006dd32d9230004fe71d9230004fd71d923008ebc41d9230006fa70d923008ebf40d9230014ff765923008ebc6459230004ff75592300b4fe75592300b4fc7559230006bf7459230006bf545923008ebc545923008ebf4359230004ff725923000cfe7259230004fd725923000cfc72592300067f52592300067d525923008ebf4259230006bd4259230006df3259230006dd3259230004ff7159230004fc715923008ebf415923003cfc705923008ebc4059230004ff7655230004fe7655230004fd7655230004fc7655230006bf6455230016bc645523008f3c5455230005df735523003ddc7355230014ff7650e300057f7550e3029d7c7550e30016be6450e30006bd6450e3003f9c4350e30005fb7050e30005f87050e30006f76198630014fe7498630004fd7498630014fc7498630004ff729863000cfe7298630004fd729863000cfc7298630006bf4298630006bd4298630006df3298630006dd3298630006f62198630006f52198630
  | 16 => 0x8540006dd32d8540056f641d8540056f541d8540006f7619854004df970985400057f75585400ad7c7558540005df7358540005dc7358540005ef72585400a5ec725854005dfb70585400ad7e75185400057d7518540006f561185400b4fe75185400067e75185400b47e7518540004fd75185400067d75185400047d75185400b4fc7518540006bf5418540026bc541854003cfe7318540004fd7318540026bf4318540006bd4318540004ff721854000cfe7218540004fd721854000cfc72185400067f52185400067d5218540026bf4218540006bd4218540006df3218540006dd3218540026bf4118540026f64118540026f54118540026bc4018540004fe7694540004fd7694540004fc76945400067f65945400b67c6594540015be7494540005bd749454030f3c5494540004ff7654540004fe7654540004fc76545400b67e6554540005bf7454540015bc74545400af3f54545400073f75505400adbe75505400adbc75505400073c75505400ad3c7550540006bf6550540006bd6550540005bf73505402d6bc6350540305bf7250540305bd72505402febf62505402febd62505402ff3f52505402ff3d52505402ff9f32505402ff9d3250540015bf7150540017b77150540007b76150540006bc6150540007b46150540007bb7050540005bc7050540007b87050540016bf6050540017bb6050540004fe76cc540004fd76cc54003cfc76cc5400ad7e75cc5400057d75cc540015be74cc540005bd74cc5400a5ee72cc540005ed72cc540004fe768c540004fd768c540004fc768c5400ad7e758c5400057d758c540015be748c540005bd748c540006df638c54003edc638c540004ff764c540004fe764c540004fc764c540015be744c540005bd744c540004fe760c540004fd760c54003cfc760c540015be740c540005bd740c540006df630c54003edc630c540005fa700c540005f9700c5402f4fe76941400b67e6594140015be74941400adbd74941400af3f54941400af7b5094140014fe76541402ecfd7654140014fc7654140005bf7454140015bc74541402ef3c54541400adbe75901400073e75901400ad3e75901400073d75901400adbc7590140006bf6590140006bd6590140005bd7390140286bc63901402e5bf72901402e5bd72901402debf62901402debd62901402df3f52901402df3d52901402df9f32901402df9d3290140005bd7190140006bc6190140015be7090140017ba7090140016bf6090140017bb6090140004ff75593300067f75593300047f75593300b4fe75593300b4fc75593300067c75593300b47c755933003ebf745933009ebe545933003cfc735933003ebe435933003ebc4359330004ff725933000cfe7259330004fd725933000cfc72593300067f52593300067d525933009ebf4259330006b
  | 17 => 0x3cff760c640004fe760c640004fd760c64033e7e650c6400067d650c640285bf740c640015bc740c640005fa700c640005f9700c6400b4fe7694240014fd7694240015be7494240005bd74942400073d5494240337bb40942400b4fe76d95400ae7e65d9540015be74d95400af3f54d9540334ff74d9540014fe74d9540334fd74d95400aebd74d95400acbd74d9540014fc74d95403367f54d95400aebf54d95400ae3f54d95403367d54d9540336bc54d954003cfe73d9540004fd73d95400ae7c53d9540336bf43d9540004ff72d954000cfe72d9540004fd72d954000cfc72d95400ae7f52d95400067d52d9540336bf42d9540006bd42d9540006df32d9540006dd32d9540004fe71d9540004fd71d95400ae7c51d9540336bf41d9540014fd70d95400ae7f50d9540336bc40d95400ae7c65595402ef3c5459540005df7359540005dc735954032dfb70595402ecff7459540006bf74595402ee7e54595402eebc54595402ee3c5459540004ff7359540006df7359540004df735954003cfc7359540006dc735954003cdc73595402eebf4359540004ff725954000cfe7259540004fd725954000cfc72595402eebf4259540006bd4259540006df3259540006dd3259540004ff7159540004fc71595402eebf415954032cff7059540006fb70595402eebc40595400b4fe75d8d40004fd75d8d400b4fc75d8d40006df53d8d40006dc53d8d4008ede43d8d4008edd43d8d40004ff72d8d4000cfe72d8d40004fd72d8d4000cfc72d8d400067f52d8d400067d52d8d4008ebf42d8d40006bd42d8d40006df32d8d40006dd32d8d40004fe71d8d40004fd71d8d40006df6398d40085f97098d400057f7558d400ad7c7558d4009dfb7058d400ad7e7518d400057d7518d4003ede6318d40006dd6318d400a5ee7218d40005ed7218d40004fe7694d40004fd7694d4003cfc7694d400067f6594d400b67c6594d40015be7494d40005bd7494d403273c5494d400af5f5394d40004ff7654d40004fe7654d40004fc7654d400b67e6554d40005bf7454d40015bc7454d400af3f5454d4003cbc7650d400073f7550d400adbe7550d400adbc7550d400073c7550d400ad3c7550d40006bf6550d40006bd6550d40015bf7350d400179f7350d400079f6350d4003ebe6350d4003ebc6350d400079c6350d4003e9c6350d4031dbf7250d4031dbd7250d40316bf6250d40316bd6250d403173f5250d403173d5250d403179f3250d403179d3250d40005bf7150d40007bb7050d40005bc7050d40007b87050d40016bf6050d40017bb6050d400b4fe75d8540004fd75d85400b4fc75d854003cfe73d8540004fd73d8540004ff72d854000cfe72d8540004fd72d854000cfc72d85400067f52d85400067d52d8540056bf42d8540006bd42d8540006df32d
  | 18 => 0xd6554e40005bf7454e40015bc7454e400073d5454e40285bf7590e40005bd7590e40146be6590e400073e6590e401463e6590e400073d6590e40146bc6590e40015be7390e400179e7390e402879e6390e40286bd6390e400079d6390e40285bf7290e40375bd7290e4036ebf6290e4036ebd6290e4036f3f5290e4036f3d5290e402879f3290e4036f9d3290e40005be7190e40287ba7090e40005bd7090e40287b97090e40016be6090e40017ba6090e400c57e75d86400057d75d86400067e65d86400067d65d8640025fa70d86400067e65986400067d6598640006f761986400b4fe7598640004fd75986400b4fc759864003cfe7398640004fd7398640004ff729864000cfe7298640004fd729864000cfc72986400067f52986400067d529864005ebf4298640006bd4298640006df3298640006dd329864005ef6419864005ef54198640006f62198640006f521986400067e65586400067d6558640004ff75586400b4fe75586400b4fc755864004ebe5458640006bd5458640004ff735864003cfc7358640006be435864004ebc4358640004ff725864000cfe7258640004fd725864000cfc72586400067f52586400067d525864004ebf4258640006bd4258640006df3258640006dd325864004ef6415864004ef5415864004ebc4158640006f62158640006f5215864004ebf40586400c57e75186400057d75186400067e65186400067d6518640005de7318640005dd73186400bdee7218640005ed7218640006f56118640055fa7018640004ff7694640004fe7694640004fd76946400b67e65946400067d6594640015bc749464030f3e5494640004ff7654640004fd7654640004fc76546400b67e65546400067d6554640005bf7454640015bc74546400073d5454640005bf7590640005bd7590640126be65906400073e65906401263e65906400073d6590640126bc6590640285be7390640006bd6390640365bf7290640365bd729064035ebf629064035ebd629064035f3f529064035f3d529064035f9f329064035f9d3290640015be7190640017b67190640007b66190640006bd6190640007b56190640007ba7090640005bd7090640007b97090640016be6090640017ba609064003cff76cc640004fe76cc640004fd76cc6400c57e75cc6400057d75cc6403567e65cc6400067d65cc640015be74cc640005bd74cc64003ede63cc640006dd63cc6400bdee72cc640005ed72cc640004ff768c640004fe768c640004fd768c6400c57e758c6400057d758c64034e7e658c6400067d658c640015be748c640005bd748c640006f6618c640006f5618c640004ff764c640004fd764c640004fc764c6403467e654c6400067d654c640005bf744c640015bc744c64003ede634c640006dd634c640006f6614c640006f5614c640
  | 19 => 0x964000cfc72596400c67f52596400067e52596400067d52596400c67c52596402eebf4259640006bd4259640006df3259640006dd3259640004ff7159640004fc71596400c67f51596400c67c5159640014fc70596400c67c505964032d7f76596400c67f76596400b47f76596402ef3e74596400073d74596402ef3c43596400057f72596400057d72596400067f62596400067e62596400067d62596400067c62596402ef3f42596400073d42596400075f32596400075d32596402ef3c41596402ef3f40596402ef7b40596402ef7840596402ee7e74596402ee7d74596402ee7c74596400067f73596400067e73596400067d73596400067c73596402ee7f43596402ee7e43596402ee7d43596402ee7c43596400067f72596400047f72596400067e72596400067d72596400047d72596400067c72596402ee7f42596402ee3f42596402ee7e42596402ee7d42596400063d42596402ee7c42596400067f32596400065f32596400067e32596400067d32596400065d32596400067c32596400067f71596400067e71596400067d71596400067c71596402ee7f41596402ee7e41596402ee7d41596402ee7c41596400067f21596400067e21596400067d21596400067c21596400c67f70596402ee7e70596402ee7c70596402ee7f40596402ee7e40596402ee7d40596402ee7c40596400067f20596400067e20596400067d20596400067c20596400c5bf76552400b6bf76552400b4bf7655240015bf75552400173f75552400b6be65552400c73e65552400b63e65552400073d65552400b6bc6555240285bc73552400c73f5355240385bf7255240385bd725524037ebf625524037ebd62552400c73f525524037f3d525524037f9f325524037f9d3255240005bc71552400c73f5155240005bf7055240007bb7055240007b87055240016be6055240017ba60552400c73c50552400c57e75d8e400057d75d8e400067e65d8e400067d65d8e4006dfa70d8e400067e6598e400067d6598e40006df6398e400067e6558e400067d6558e40004ff7558e400b4fe7558e400b4fc7558e40086be5458e40006bd5458e40086de4358e40086dd4358e40286bc4358e40004ff7258e4000cfe7258e40004fd7258e4000cfc7258e400067f5258e400067d5258e40086bf4258e40006bd4258e40006df3258e40006dd3258e40004ff7158e40004fc7158e40086bc4158e40086bf4058e400c57e7518e400057d7518e400067e6518e400067d6518e4003ede6318e40006dd6318e400bdee7218e40005ed7218e40005f67118e40005f57118e4008dfa7018e4003cff7694e40004fe7694e40004fd7694e400b67e6594e400067d6594e40015bc7494e403273e5494e400c75f5394e40004ff7654e40004fd7654e40004fc7654e400b67e6554e400067
  | 20 => 0x6be7418131014be7418131004fd7418131006bd7418131004bd7418131014fc7418131004ff721813100cfe7218131006ee721813100cee7218131004fd7218131006ed7218131004ed721813100cfc7218131006bf4218131006bd4218131006df3218131006dd3218131006de3118131004ff75590310067f75590310047f75590310b4fe75590310b4fc75590310067c75590310b47c755903103ebf74590310d6be545903103cfe735903103cfc735903103ebe435903103ebc4359031004ff725903100cfe7259031004fd725903100cfc72590310067f52590310067d52590310d6bf4259031006bd425903103edf3259031006dd32590310d4fc71590310d6bc4159031004ff7059031004fc70590310d6bf4059031004ff765503103cfe7655031004fd765503103cfc7655031016be6455031006bd64550310d73c54550310f4ff769043103cfe7690431014fd769043103cfc7690431016be6490431006bd649043103dde7390431005dd73904310f4ff76504310057f755043133d7c75504312d6bf6450431016bc645043103ddf764c431006df764c431004df764c43139ddf724c43139ddd724c43103edf624c43138edd624c43138f9f424c43138f9d424c43103ddf714c43103fd7714c431396de614c43103fd6614c43138fd7214c43138fd4214c431005dc704c431014fe7498031004fd7498031014fc7498031004ff729803100cfe7298031004fd729803100cfc7298031006bf4298031006bd429803103edf3298031006dd329803103efa709803103efb309803103ef83098031006fa2098031006f92098031004ff7458031006bf7458031004bf7458031014fe7458031014fc7458031006bc7458031014bc7458031004ff725803100cfe7258031004fd725803100cfc7258031006bf4258031006bd425803103edf3258031006dd325803103edf315803103ef63158031006dd315803103ef5315803103efb705803103efb305803103edc305803103ef83058031006fa2058031006f920580310c67e65d96402f5fa70d964003cfe73d9640004fd73d9640004ff72d964000cfe72d9640004fd72d964000cfc72d9640336bf42d9640006bd42d9640006df32d9640006dd32d9640004fe71d9640004fd71d96402f4fe70d9640006fa70d964032f3e74996400c73d749964032e7d649964032f3c43996400c57f72996400057d72996400067f62996400067e62996400067d62996400067c629964032f3f42996400073d42996400075f32996400075d329964032f3c419964032e7e609964032f3f409964032f7b409964032f7840996400b4ff76596400c67c65596400067f75596402ee7f54596402ee7d5459640004ff735964003cfc73596400c67f53596400c67c5359640004ff725964000cfe7259640004fd725
  | 21 => 0x661cc631007d651cc631007d551cc631005de70cc6310f5be74d8231005bd74d8231006be64d8231006bd64d8231006be6498231006bd6498231006fb6098231014fe7498231004fd7498231014fc7498231004ff729823100cfe7298231004fd729823100cfc7298231006bf4298231006bd4298231006df3298231006dd3298231006fa2098231006f92098231006be6458231006bd6458231004ff7458231014fe7458231014fc7458231004ff725823100cfe7258231004fd725823100cfc7258231006bf4258231006bd4258231006df3258231006dd3258231006df3158231006fa2058231006f920582310f5be7418231005bd7418231006be6418231006bd64182310ddee7218231005ed7218231006f96018231014fe76d91310eebe64d91310b4fe75d9131004fd75d91310b4fc75d9131006bf54d91310eebc54d91310ecfd73d91310eebf43d9131004ff72d913100cfe72d9131004fd72d913100cfc72d91310067f52d91310067d52d91310eebf42d9131006bd42d9131006df32d9131006dd32d913103cfd71d91310eebf41d9131004fe70d9131004fd70d91310eebc40d91310057f75591313457c75591310eebc6459131004ff75591310067f75591310047f75591310b4fe75591310b4fc75591310067c75591310b47c75591310ecff7459131006bf74591310eebe54591310f4ff7359131006df73591312d6be43591312d6bc4359131004ff725913100cfe7259131004fd725913100cfc72591310067f52591310067d52591310eebf4259131006bd4259131006df3259131006dd3259131104ff7159131006f771591310eebc4159131004ff7059131004fc70591310eebf4059131004ff7655131004fe7655131004fd7655131004fc7655131016be6455131006bd64551310ef3c5455131005df735513103ddc7355131014fc7650d310057f7550d313457c7550d31006bf6450d31016bc6450d3103f9c4350d31005f77150d31005f47150d31104fe7690531016be6490531006bd6490531014ff76505310ecfd765053103cfc76505310057f75505313457c7550531006bf6450531016bc6450531005df735053103ddc73505310edbe748c531005bd748c53103df6718c53103ef7618c5310079e748c5310079d748c531395df728c531395dd728c5313a6df628c5313a6dd628c5313a79f428c5313a79d428c53103dde718c53103edf618c53103fd7618c531005dd708c531014fe74d8131004fd74d8131014fc74d8131004ff72d813100cfe72d8131004fd72d813100cfc72d8131006bf42d8131006bd42d8131006df32d8131006dd32d8131006fb6098131005bf74581310edbc7458131005ef72581310e5ec72581310edbe7418131005bd74181310e5ee7218131005ed7218131006f96018131014fe7418131
  | 22 => 0x9231004bd7699231006bf6599231006be65992310073e65992310063e6599231006bc65992310f5bf7299231005bd7299231006bf6299231006be6299231006bd6299231006bc62992310073f52992310073d52992310079f32992310079d32992313bebe61992313bfb731992313bfb43199231014ff76592310067e65592310f6bc6459231004ff75592310b4fe75592310b4fc7559231006bf7459231006bf54592310f6be54592310f6bc54592310f6bf4359231004ff725923100cfe7259231004fd725923100cfc72592310067f52592310067d52592310f6bf4259231006be4259231006bd42592310f6bc4259231006df3259231006dd325923103cfc71592310f6bc4159231004ff7059231004fc70592310f6bf40592310f6bc40592310f5bf76592310f6bf7659231014bf7659231006bf6559231006be65592310073e65592310063e6559231006bd65592310073d65592310063d6559231006bc6559231005bf7259231005bd7259231006bf6259231006be6259231006bd6259231006bc62592310073f52592310073d52592310079f32592310079d32592312d7b731592312d7b43159231006bf7559231006be7559231006bd7559231006bc7559231006bf73592312d6be7359231006bd73592312d6bc7359231006bf53592312d6be53592312d6bc5359231006bf7259231004bf7259231006be7259231006bd7259231004bd7259231006bc7259231006bf52592310063f5259231006be5259231006bd52592310063d5259231006bc52592312d6bf32592310069f3259231006be3259231006bd32592310069d32592312d6bc32592310f6bf71592312d6be7159231006bc7159231006bf5159231006bc51592312d6bf3159231006be31592312d6bc3159231006bf2159231006be2159231006bd2159231006bc2159231006bf7059231006be7059231006bd7059231006bc7059231006bf5059231006bc50592312d6bf30592312d6bc3059231006bf2059231006be2059231006bd2059231006bc2059231004ff7655231004fe7655231004fd7655231004fc7655231016be6455231006bd64552310f73c5455231014ff7650e310057f7550e3134d7c7550e311367e6550e310067d6550e31016be6450e31006bd6450e31005f77150e31005f47150e31014fe769063103cfd76906311267e65906310067d6590631016be6490631006bd649063103dde7390631005dd73906310d4ff76506310057f755063134d7c75506311167e65506310067d6550631016be6450631006bd6450631005dd76cc63103edd76cc63103f9e74cc63103f9d74cc6310079e64cc6310079d64cc63103ddf72cc63103fce72cc6313b5dd72cc63103fcd72cc631005cd72cc6313aedf62cc6313aedd62cc6313af9f42cc6313af9d42cc63103fd
  | 23 => 0x4bf7259331006be7259331006bd7259331004bd7259331006bc7259331006bf52593310063f5259331006be5259331006bd52593310063d5259331006bc525933103ebf325933103e9f325933103ebe325933103ebd32593310069d325933103ebc3259331006bf7159331006bd7159331106bc7159331006bf5159331006bc515933103ebf315933103ebe315933103ebd315933103ebc3159331006bf2159331006be2159331006bd2159331006bc2159331006bf7059331006be7059331006bd7059331006bc7059331006bf5059331006bc505933103ebf305933103ebe305933103ebd305933103ebc3059331006bf2059331006be2059331006bd2059331006bc2059331004ff765533103cfe7655331004fd765533103cfc7655331016be6455331006bd64553311073c5455331005df735533103ddc735533114eee6255331006ef7458b31006ee7458b31006ae7458b31006ed7458b31006ad7458b31006ec7458b31006ee5458b31006ed5458b31006ec5458b3103eef7358b3103eee7358b3103ece7358b3103eed7358b310fecd7358b3103eec7358b3103eef4358b3103eee4358b3103eed4358b3103eec4358b310feef7158b310feee7158b31006ed7158b310feec7158b31006ef4158b31006ec4158b3103eef3158b3103eee3158b3103eed3158b3103eec3158b3103ecc3158b31006ef7058b31006ee7058b31006ed7058b31006ec7058b31006ef4058b31006ec4058b3103eef3058b3103ecf3058b3103eee3058b3103eed3058b3103eec3058b310ecfd76907311267e65907310067d6590731016be6490731006bd649073111eee6290731006ed6290731014ff765073103cfc76507310057f75507313557c75507311167e65507310067d6550731016be6450731006bd6450731005df735073103ddc735073110eee6250731006ed6250731014fe7498331004fd7498331014fc7498331004ff729833100cfe7298331004fd729833100cfc7298331006bf4298331006bd429833103edf3298331006dd329833103edc319833103efa709833103edf309833103efb309833103ef83098331004ff7458331014fe7458331014fc7458331004ff725833100cfe7258331004fd725833100cfc7258331006bf4258331006bd425833103edf3258331006dd325833103ef6315833103ef5315833103efb705833103efb305833103ef8305833134d7e75d92310057d75d92310f6be64d92310b4fe75d92310067e75d92310b47e75d9231004fd75d92310067d75d92310047d75d92310b4fc75d92310f4fd74d9231006dd73d9231004ff72d923100cfe72d9231004fd72d923100cfc72d92310067f52d92310067d52d92310f6bf42d9231006bd42d9231006df32d9231006dd32d9231006f671d9231004fe70d9231004fd70d
  | 24 => 0xc6594d41015bc7494d413273e5494d411175f5394d41004ff7654d41004fe7654d41004fc7654d410067f6554d410b67c6554d41005bf7454d41015bc7454d410073d5454d412d5bf7590d41005bd7590d410073f6590d41146be6590d41146bc6590d410073c6590d411463c6590d41015be7390d410179e7390d412d6bf6390d410079f6390d412d79c6390d412d5bf7290d413edbd7290d413e6bf6290d413e6bd6290d413e73f5290d413e73d5290d412d79f3290d413e79d3290d41005be7190d412d7b67190d412d7b57190d41016bf6190d41017b76190d41005bd7090d413dcfe769454130e7f65945410b67c6594541015bc749454130f3e549454111777519454130fb44194541014fe76545413d4fd7654541014fc7654541005bf7454541015bc74545410073d54545413d7b44154541005bf7590541005bd75905410073f6590541126be6590541126bc65905410073c65905411263c65905412d5be7390541006bf63905413cdbf72905413cdbd72905413c6bf62905413c6bd62905413c73f52905413c73d52905413c79f32905413c79d3290541015be7190541017b67190541016bf6190541017b76190541005bd70905410067f65d81410067c65d81410b4fe75d8141004fd75d81410b4fc75d814103cfe73d8141004fd73d8141004ff72d814100cfe72d8141004fd72d814100cfc72d81410067f52d81410067d52d814105ebf42d8141006bd42d8141006df32d8141006dd32d814105efa40d81411157e75981410057d75981410067f65981410067c6598141006fb60981410057f75581411157c75581410067f65581410067c6558141005df7358141005dc7358141005ef725814110dec72581410067f65181410067c6518141006f960181410b4fe7518141004fd75181410b4fc7518141026be5418141006bd541814103cfe7318141004fd7318141006be4318141026bc4318141004ff721814100cfe7218141004fd721814100cfc72181410067f52181410067d5218141026bf4218141006bd4218141006df3218141006dd3218141006be4118141026bc4118141026bf4018141026f94018141004ff75593310b4fe75593310b4fc755933103ebf7459331006bf5459331106be5459331106bc545933103cfc735933103ebe435933103ebc4359331004ff725933100cfe7259331004fd725933100cfc72593310067f52593310067d5259331106bf4259331006be4259331006bd4259331106bc425933103edf3259331006dd3259331106bf4159331004ff7059331004fc7059331106bf4059331106bc4059331006bf7559331006be7559331006bd7559331006bc755933103ebf735933103ebe735933103ebd735933103ebc735933103ebf535933103ebe535933103ebd535933103ebc5359331006bf7259331
  | 25 => 0x95410075d32d954130f7741d954130f3c41d954130f7441d954130f3f40d954130e7f74d954130e7e74d954130e7d74d954130e7c74d95410067f73d95410067e73d95410067d73d95410067c73d954130e7f43d954130e7e43d954130e7d43d954130e7c43d95410067f72d95410047f72d95410067e72d95410067d72d95410047d72d95410067c72d954130e7f42d954130e3f42d954130e7e42d954130e7d42d95410063d42d954130e7c42d95410067f32d95410065f32d95410067e32d95410067d32d95410065d32d95410067c32d954130e7f71d95411167e71d954130e7d71d954130e7f41d954130e7e41d954130e7c41d95410067f21d95410067e21d95410067d21d95410067c21d95410067f70d95410067e70d95410067d70d95410067c70d954130e7f40d954130e7e40d954130e7d40d954130e7c40d95410067f20d95410067e20d95410067d20d95410067c20d95411167c6559541405f771595413d4ff7459541006bf7459541004ff735954103cfc7359541004ff725954100cfe7259541004fd725954100cfc72595413d6bf4259541006bd4259541006df3259541006dd3259541404ff7159541006f77159541004ff7059541004fc705954130d7e76195411167e761954130c7e76195413df3e74195411173d74195413de7f64195413df3c43195411157f72195410057d72195410067f62195410067e62195410067d62195410067c62195413df3f42195410073d42195410075f32195410075d32195413de7f61195413df7741195413df3c41195413df7441195413df3f4019541115bc76551410b6bc76551410b4bc7655141015bf75551410173f75551410073f65551410b6be65551410b6bc65551411173c65551410b63c65551412d5bc73551411173f53551413fdbf72551413fdbd72551413f6bf62551413f6bd62551411173f52551413f73d52551413f79f32551413f79d3255141007b77155141005bc7155141007b47155141016bf6155141017b761551411173f5155141005bf70551411173c50551410067f65d8d410067c65d8d410b4fe75d8d41004fd75d8d410b4fc75d8d410f6be54d8d41006bd54d8d410f6de43d8d410f6dd43d8d412d6bc43d8d41004ff72d8d4100cfe72d8d41004fd72d8d4100cfc72d8d410067f52d8d410067d52d8d410f6bf42d8d41006bd42d8d41006df32d8d41006dd32d8d410f6bc41d8d41004fe70d8d41004fd70d8d410f6bf40d8d411157e7598d410057d7598d410067f6598d410067c6598d41006df6398d4110dee7298d41005ed7298d410edf57198d410057f7558d411157c7558d410067f6558d410067c6558d41105f77158d410067f6518d410067c6518d4103ede6318d41006dd6318d41004fe7694d41004fd7694d4103cfc7694d410067f6594d410b67
  | 26 => 0x4ff7558e410b4fe7558e410b4fc7558e41006df5358e41006dc5358e410eede4358e410eedd4358e41004ff7258e4100cfe7258e41004fd7258e4100cfc7258e410067f5258e410067d5258e410eebf4258e41006bd4258e41006df3258e41006dd3258e41004ff7058e41004fc7058e4103ede6318e41006dd6318e410f5f67118e4103cff7694e41004fe7694e41004fd7694e410b67e6594e410067d6594e41015be7494e41005bd7494e413273c5494e411275f5394e41004ff7654e41004fd7654e41004fc7654e410b67c6554e41005bf7454e41015bc7454e411273f5454e4103cbf7650e410073f7550e41125be7550e41125bc7550e410073c7550e411253c7550e41006bf6550e41006bd6550e41015bf7350e410179f7350e4103ebe6350e410079e6350e4103e9e6350e410079d6350e4103ebc6350e41415bf7250e41415bd7250e4140ebf6250e4140ebd6250e4140f3f5250e4140f3d5250e4140f9f3250e4140f9d3250e41005bf7150e41007b77150e41007b47150e41016be6150e41017b66150e41005bc7050e410b4fe7694641014fd7694641015be7494641005bd749464130f3c549464130fb74194641006fb60982410b4fe7598241004fd75982410b4fc759824103cfe7398241004fd7398241004ff729824100cfe7298241004fd729824100cfc72982410067f52982410067d5298241056bf4298241006bd4298241006df3298241006dd3298241056f94098241006fa2098241006f920982410057f75582411257c7558241004ff75582410067f75582410047f75582410b4fe75582410b4fc75582410067c75582410b47c7558241006bf545824104ebc5458241004ff735824103cfc735824104ebf4358241006bd4358241004ff725824100cfe7258241004fd725824100cfc72582410067f52582410067d525824104ebf4258241006bd4258241006df3258241006dd325824104ebf415824104efa405824104ebc4058241006fa2058241006f920582411257e75182410057d7518241005de7318241005dd731824111dee7218241005ed7218241006f960182410b4fe76d95411167e65d954130cff74d954130cfd74d954130e7f54d954130e7d54d954103cfe73d9541004fd73d95411167f53d95411167c53d9541004ff72d954100cfe72d9541004fd72d954100cfc72d95411167f52d95410067e52d95410067d52d95411167c52d954130ebf42d9541006bd42d9541006df32d9541006dd32d9541014fd71d95411167f51d9541004fe70d9541004fd70d95411167f50d95411167c50d95413dd7e76d95410b47e76d95410073f74d954130f3c74d954130f3c43d95410057f72d95410057d72d95410067f62d95410067e62d95410067d62d95410067c62d954130f3f42d95410073d42d95410075f32d
  | 27 => 0xd74d8543106be54d8543006bd54d85433bebe43d85433bebc43d8543004ff72d854300cfe72d8543004fd72d854300cfc72d85430067f52d85430067d52d8543106bf42d8543006bd42d8543006df32d8543006dd32d8543106f641d8543106bc41d8543004fe70d8543004fd70d8543106bf40d85431357e75985430057d75985430067f65985430067c6598543006f761985430057f75585431357c75585430067f65585430067c65585430067f65185430067c6518543006f561185430b4fe7518543004fd75185430b4fc751854303cfd7418543004ff721854300cfe7218543004fd721854300cfc72185430067f52185430067d52185430d6bf4218543006bd4218543006df3218543006dd32185430d6f54118543004fe7018543004fd70185430067f65d81430067c65d81430b4fe75d8143004fd75d81430b4fc75d814303cfd74d8143004ff72d814300cfe72d8143004fd72d814300cfc72d81430067f52d81430067d52d814309ebf42d8143006bd42d8143006df32d8143006dd32d8143004fe71d8143004fd71d814309efa40d81431357e75981430057d75981430067f65981430067c6598143006fb60981430057f75581431357c75581430067f65581430067c65581430067f65181430067c6518143006f960181430b4fe7518143004fd75181430b4fc751814303cfd741814306ebe5418143006bd541814327ebe431814327ebc4318143004ff721814300cfe7218143004fd721814300cfc72181430067f52181430067d521814306ebf4218143006bd4218143006df3218143006dd3218143004fe7118143004fd711814306ebc411814306ebf401814306ef940181431267e65d964130f3c54d9641005de73d9641005dd73d96413ddf671d964130e7e54d964130ebc54d964130e3c54d964103cfe73d9641006de73d964103cde73d9641004fd73d9641006dd73d9641004dd73d964130ebf43d9641004ff72d964100cfe72d9641004fd72d964100cfc72d964130ebf42d9641006bd42d9641006df32d9641006dd32d96413dcfe71d9641006f671d964130ebf41d9641004fe70d9641004fd70d964130ebc40d96410b4ff76596411267c6559641015bc74596411273f54596410067f75596413d67f5459641126bf54596411263f54596413d67d54596413d6bc5459641004ff735964103cfc73596411267c53596413d6bf4359641004ff725964100cfe7259641004fd725964100cfc72596411267f52596410067d52596413d6bf4259641006bd4259641006df3259641006dd3259641014fc71596411267c51596413d6bf4159641004ff7059641004fc70596411267f50596413d6bc40596411257e75d8e410057d75d8e410d5f671d8e411257e7598e410057d7598e41006df6398e4111dee7298e41005ed7298e41
  | 28 => 0x9543006df32d9543006dd32d9543004fe71d9543004fd71d95431367f51d95431367c51d9543004fe70d9543004fd70d95431367f50d95431367c50d95434357e76d95430b47e76d954344f3f74d95433273c74d95433275f43d954344f3e43d954344f3c43d95433275c43d95430057f72d95430057d72d95430067f62d95430067e62d95430067d62d95430067c62d95433273f42d95430073d42d95430075f32d95430075d32d95433273c41d95433273f40d954344e7f74d95433267e74d95433267d74d95433267c74d95433267f73d954344e7e73d95433267d73d954344e7c73d95433267f43d954344e7e43d954344e7c43d95430067f72d95430047f72d95430067e72d95430067d72d95430047d72d95430067c72d95433267f42d95433263f42d95433267e42d95433267d42d95430063d42d95433267c42d954344e7f32d95430065f32d95430067e32d95430067d32d95430065d32d954344e7c32d95430067f71d95430067e71d95430067d71d95430067c71d95433267f41d95433267e41d95433267d41d95433267c41d954344e7f31d954344e7c31d95430067f21d95430067e21d95430067d21d95430067c21d95430067f70d95430067e70d95430067d70d95430067c70d95433267f40d95433267e40d95433267d40d95433267c40d954344e7f30d954344e7c30d95430067f20d95430067e20d95430067d20d95430067c20d95431367c6559543445df735954341cff7459543006bf7459543444ff7359543006df7359543004ff725954300cfe7259543004fd725954300cfc725954341ebf4259543006bd4259543006df3259543006dd3259543004ff7159543004fc7159543004ff7059543004fc70595433257e76195431367e76195433247e76195434373e74195431373d741954343e7f641954343e3f64195434367f63195434375f431954343f3e431954343f3c43195434375c43195431357f72195430057d72195430067f62195430067e62195430067d62195430067c62195434373f42195430073d42195430075f32195430075d32195434373c41195434373f401954303dbc76551430b6bc765514303cbc7655143015bf75551430173f75551430073f65551430b6be65551430b6bc65551431373c65551430b63c65551430079f735514303dbe735514303dbc73551430079c7355143016bf63551430179f63551431373f535514342dbf725514342dbd7255143426bf6255143426bd62551431373f52551434273d52551434279f32551434279d3255143005bc71551431373f5155143005bf70551431373c5055143014fe7654d4341cfd7654d43014fc7654d43005bf7454d43015bc7454d430073d5454d4303f9c4354d430067f65d85430067c65d85430b4fe75d8543004fd75d85430b4fc75d854303cf
  | 29 => 0x32efa40d815432ebc40d81543373c5498154006fb60981542ef3c5458154005df7358154005dc73581542f73c5418154006f960181540b4fd741815403cfe7318154004fd7318154004ff721815400cfe7218154004fd721815400cfc72181542f6bf4218154006bd4218154006df3218154006dd3218154004fe7118154004fd71181542f6f9401815403e7f755964341e7f5459643146bf54596431463f545964341e7d545964341ebc545964303cfe735964303cfc735964303e7e535964303e7c535964303ebf435964303ebd4359643004ff725964300cfe7259643004fd725964300cfc72596431467f52596430067d525964341ebf4259643006bd425964303edf3259643006dd3259643004ff7159643004fc71596431467c515964341ebf4159643004ff7059643004fc70596431467f505964341ebc40596430b4fe75986430067e75986430b47e7598643004fd75986430067d75986430047d75986430b4fc7598643006bf54986430f6bc549864303cfe739864303ebf439864303ebd4398643004ff729864300cfe7298643004fd729864300cfc72986430067f52986430067d52986430f6bf4298643006bd429864303edf3298643006dd329864303ef671986430f6bf41986430f6f5419864303ef7319864303ef43198643004fe7098643004fd70986430f6bc4098643004ff75586430b4fe75586430b4fc755864303cfc7358643004ff725864300cfe7258643004fd725864300cfc72586430067f52586430067d52586430eebf4258643006bd425864303edf3258643006dd325864303ef771586430eef6415864303ef7315864303ef43158643004ff7058643004fc70586430b4fe7598243004fd75982430b4fc759824303cfe7398243004ff729824300cfe7298243004fd729824300cfc72982430067f52982430067d529824308ebf4298243006bd429824303edf3298243006dd3298243004fe7198243004fd719824303efa709824308ef9409824303efb309824303ef83098243004ff75582430067f75582430047f75582430b4fe75582430b4fc75582430067c75582430b47c7558243006bf5458243086bc545824303cfc735824303ebf435824303ebd4358243004ff725824300cfe7258243004fd725824300cfc72582430067f52582430067d5258243086bf4258243006bd425824303edf3258243006dd3258243004ff7158243004fc7158243086bf415824303efb7058243086fa4058243086bc405824303efb305824303ef830582430b4fe76d95431367e65d954303cff74d954303cfd74d95433267f54d95433267d54d9543014fd73d95431367f53d9543004ff72d954300cfe72d9543004fd72d954300cfc72d95431367f52d95430067e52d95430067d52d95431367c52d9543326bf42d9543006bd42d
  | 30 => 0x4000002c001001400000000010004001002801000240060004003000800200480000068001001400500080000004002000400b00080010004003000800800000010000006002400000000000004005000c000000000c000c00200040020014000000c00100040070008001000000a00000010044005001400700100000000005000000100000060000000000000300000030000006001400000040060000002000c0000078000000c00b000400300180060000001000800c002c0020000006000400000000010010001001800100400000004000000000200240000004000000c0000000003000001100500080010000000000e002c00000040020010000000800100400010004003002000000000000000000002c0010004002000c00200040010004000001001200040000024000003000000000000014008000000d001c000000400000040000018002000400200340020000003001c0000000002000800100040040000001000c0010014001000000000000170014005000400a0020003000000000040040000005000800000000010000000000c00100000030000001000400200000010018000001c000000c001000000200080010000003001401600140010008004000c001002c0000008002001c00400000020014002000800000600080008000001800003cfe76d8d544473c54d8d540b4fd74d8d54446de43d8d54004ff72d8d5400cfe72d8d54004fd72d8d5400cfc72d8d54446bf42d8d54006bd42d8d54006df32d8d54006dd32d8d54004fe71d8d54004fd71d8d54004fe70d8d54004fd70d8d54466bf6498d543273c5498d54006df6398d5441f3c5458d54466bf6418d544373c5418d5403ede6318d54006dd6318d5414dee7218d54005ed7218d544073c54d85540b4fd74d855403cfe73d8554004fd73d8554004ff72d855400cfe72d8554004fd72d855400cfc72d8554406bf42d8554006bd42d8554006df32d8554006dd32d8554406f641d8554004fe70d8554004fd70d855430f3c5498554005de7398554005dd7398554006f761985543d73c54585543df3c5418554006f561185540b4fd741855445ebd74185543de7e54185543debc54185543de3c541855403cfe7318554004fd73185543debf4318554004ff721855400cfe7218554004fd721855400cfc72185543debf4218554006bd4218554006df3218554006dd32185543debf41185543def54118554004fe7018554004fd70185543debc401855432f3c54d81540b4fd74d8154456bd74d815432e7e54d815432ebc54d815432e3c54d815403cfe73d8154004fd73d815432ebf43d8154004ff72d815400cfe72d8154004fd72d815400cfc72d815432ebf42d8154006bd42d8154006df32d8154006dd32d8154004fe71d8154004fd71d815432ebf41d8154
  | 31 => 0x1c001000c00a0000000000000000000080000005005c0050000000000c0050000003003000000080000008000000c0060004000000000200000000008000000000400180020000001003c009000c0030000000000800500000130058004001800400000050008000004000b0000001000000100080030024001000000500180010000008000000d0000000001801d00000010008002002400100000040014000000000a0008014000800400580000010001001400000040070000000002000200180000008000000c0020000001002c0000020004000400800040000004000000c001000000000000020000007001400800000000004001002400e00180010000002001000600100000004004001400100000030018002000800000000000044000000002300300010008004004c0250000001000800400080050004000000400500040020000007000c0000000000000c0030000001000400000000030014005000001000100000000000000800400000010004007000800a001000d00140020000000001c001000c00300100020004001004c0000028000001800400000000000001000800e0000002000c009000400000000130010004000c000000800000000070008006000000500080000010003000000600000020000002003400200140000004012001000f001c001000000700000000000003000400000000000000000000000000080000004003002c0030020001004c004000800b00100010004000003c0000008000000000200040000010002000000500080020000000000800200000000038001000000000000000000003001c0000004001001000300000000000002002400100040020008000000c0000004001002400300140030008002003000000100000018008000000000000020000000004800000540130014002000c00f002c0030008000000000400040000000000000000500000000004001001800300300010000000000400000000000014000004c002001400500000000060000000000000040000010003000800b0018002001800e00440000004012000800400000000008001001400000040000010007002000200100010000000000c0040000000001400000000020000004000000b0000000001400b001c001000000100040080000006000000100100040010006000c0020008001004c00300440030018005000c0010010002000c00200240010000002000400000000000014001000c0040000000000000500440040008008000c0000000000002800200040010000003000c00300000190014000000400000080000004006001400100000000010000000000100040030004002002400000040070020004000c000000c001000400000880020034004003400600000050000003001400000000000000003
  | 32 => 0x100180000000001000000100040040048000000000e0024002000000100000000024000001800200180010000005001400100040000038005000400000000000000000000400c000000000000090000002000000100200040000003000000000a0001000c007000800e0004004000800b0004000000400000140030000001000c01700100110008003000400000240000030000000000300040020004000000000f001c00000100030008002000000200000000010009000000000140000008003002c00100000010000006000400100400100020000000000000100110000001000000500000000004001000c000001000400040030008000000000200100010000002001c00100180070008001000000e001800000040000004006000c0080004009001402d0024000001c00a0010003000c002000000e000c0180008001000400000040040018000000c000001800000180010048003000c0090000002000000400000010004005000000000a4000000400000080000004000000c00000000000000001000000100040000004001001c00400000010000000001000100100000000000001800300000020000000000001200000000010009000000100080000000000000000000040000018000002c00000040040014000000000700040000050002000c003000400000040060024001004000300080040024002000800c000000c000800100400000000001000800000000070000001001c0000000003000000c0004000005c00400000000050000002400100480050004000001c0010000001000000000080000004002000400400040000008002003400b000c003000c0000010001001400d0004006003000000000000000002000000000400010004001000400000000080000011000000000080040000000000000b00180010034008002c00100000060018001006400600080000004007000c0040004010002c0010000000001000100040000008000000c0010010003000000000000000000001001c0070010000000c00a0004000003000100080090000000000c0000000000000000e00000030000001001c0030024000002000200100020004016000400400040000000000005400300100040038000000800300000020004000002800400000020000002002000500000030004004000c00200080000000000001800400000010000001000800a00000030004015001800000000070000000000000000000020000000000400000080000090001002000000180000000002005c005001c001000c001000000000080000004005000c004001800100000000018004000800200100000000003000400400000000000000000800000000000010002004c002001c0000004004000000000000000000000000000a000400500000000004000000
  | 33 => 0xc002000000000100000000000000400100140000038000000400000080000008008000000000080000000003000000200000080010000001400600080020034006000400800140020010002001c00b0000005001400200000000000001001000000080020000005000400200000040018006001c005000c006000000b0024002001000000000020004008000000d00000000004013000c00000000090024000001000100000050010004000c001000400100000060000004000800300000020014001000800000040170004002003000000000000000007006000a000000000000070018001000c000000800000100060024003001c0060000000000000c0018000000c0000000005004400200140030000000000800600000010004001000001100040000010004000000100000030000001007c0000000002000800000140020000006000c00000080000004006000000000000010010005000c000000c003000000e0004001000c0000000000000000000400030008002000c000000400000080000008003000000200040000040004000c00f00180000000000000000000000030018003004c00c00080000000002000c00f0014006005800200000000008003001400000000050018002000c0050000000000c005001c00300040030000001000000000040000000003003c000000c000000800100000040000000000800300140090008000000000a00000000004007001000100100020010001002400f00080000068000001400000040010000002001000100000080004002001000500000010000001002c00300000050008007000800000080010004014000c00300080000000001001400a0018001000c001000000100000000000000000001100000000008005000c0000010004000c001000000000080110010000000c0060000001000400500740030000002000000300000000000000000400700180050024001000c01900180000030000000000100080050000000000000200080000008006002c00000280020010005000000200000000000000001400500540020000007000800500040000000002000c00700000030000004006400000140000018000005800600080000000000000000200040190004001001800a000c00200480010004000000400a000800400240060000001000c00600140000028001000400600000020000000000c0030014001002000100000000000000000c00100000080008008000c000000000b000c002000400100000160000000000400800000000000001000c0000008000000c0010000009001800200040070014003001c0000004014002000500000040000002002400600100320000000000000a0000000002000a000000a0018001000000200000020004001001c0020000003003c001001001
  | 34 => 0x323471a9a000278e0ae175e9e1100049c199060925585500985000000000000000ef800006818664ba8000000000000025a4478e322000191e0d11deca0be3ae151000000001982a79cb2000000000000000880f620001a26187a4fc245813283f869000000008e580001d301221e46076000021c70ae3540a2232a94c00003ba65b8000000027911e60208eac000274a4f580000002348205400000000005ff86ed0e282d22a2000000000001ca800000012e202c80008dd82ce89920b64808000000000070700773b3408a6ab02b364b0f7a3ac60600001b576439a206724dbe0e7c0003dd919d5108ed9415091a85d854662a80009af9e1e96c000000005c200027ce44940008b3000034940001c88000000182a2f71c8873d18ec4b31e8600020f6000000000000006f900000001508275a16e00027b0000275c609a79874d000054c26ba557907600003a1246000000000000001aa80ed000018e07f522580102bfa5460000000250000000000006ec000053a9d9c3f3400093900000000000000238e22f8000000201239000ef448ca4044b80002550e842dd00008b580008bea58c8f6000078693e662407aa7b0206617bc1725d3a4181c114ca14415928d899e90000b210000000000024800004521828000000000000000007fa0000756987a000150400012fe00000000000f9a0001e7e2c98bb300000000001cb0000078800003e6230800069b00000001cec0ab00003340a9468b284400000000000af8000115a463000000005ac07e99c60000ffc77691902af889c1c3800000005ed67e5ac43e120ac81b00000000ba30000e4900000008e0000027727341c5e51a002400000000000000ab56b980004662306000059f41b0fe3476000000007867cb800000014fa00003ae0818a1a3db80dc00000002b717da7c0000085b1c0c54e87858ce27ac2d128ac33f82c84be973092f0e2040695be1e6827091541f07e3c55c7458000000016c92886f1000000084080000398cc0348cbb100026f40d5400056700000151576000274e9748000000260c00018a6000248000026b029e80008a48cae00000006cbc85191c87666848000712000035aa4f83bad6dc09f0a460000026000223083400d19b21b5073318fe8e98f161fd8d1509014e500003f6000000000000000000000000006c71280000000e8a00000008ae800040217b8000183a000244500008880001be3000000087d96700000e3486a8284888c90800000006fc1f0a000000013015ed00000000000000000000088a80000000000000000003641110001dd0000000074f9e3b00000000bec2b95d8e1184fdddcc22d0000000000073005960001eee1ab080f00000007f580000000dee0da13a71b580002ad024e000000800000020000004000c00100300040014001000000000
  | 35 => 0x1c26000247e2b1000000000003bd0000747075825300000000870000000000000000e30000854800033a800054597d56c500007dd25bc0000000500881c0000b1c08f00000000b86a1b5d5e016236a15d8e830001d2a4d889f291880de2428fe43e90000000268a000119b778a7743f840008db000024c800000000004c500005a80305441800000006a4090c1ea2331baa8529af5019839ba1b800000000005d5a00269e00003ea496403b8000000000000000000000000360136a0000fcb00000002ebc0009719f7e000000000000002808000000196e000100243500005c39a003331d40000268400000000a9800052c00004e8800000006b41b1800081500009c600000000000000000000000000000a3e14aa3750000000000058302f0a6e0000000000000094518ae0ce09f80000edc00004723120668045000000000003f9c00000005a85d900000000000000045e38f1b9900000009570f4200000005d1000000026ca1f198f80000000000142e4f107f470d524e4d191ca979dd6f36585869fb800036988a87381f767ff800000000002f08b5056880001b9854e6df800077c00000000000000000000000e0000050a2c6224644dc2980000876145893a99a400000000009ce89e064e80000000bfa1db878d000000011e94064358c2ca1b04be69498069dc16661b50ff965c969a8fc157c2d4d9d01a097460c1245e0d527ec22c1b5c3591e665f4c00000000000001fde492800062e000a86e800000000000001dd600003ba00000003c623fc6b0907c02e9e4e1408c26185d634a13a6300e383fc218dbf69c2000000005cc7445024000212a3510df85d50000000000088f800000000000000000a26897000000005e5889d7628000000109e00000000000000000000000000006721f1a5a0158c2570df00001b2800014641ee803e076042c41d250873980008bd8a0c777141400000000000000000011088980007141abe00000005d000009ee080e000000056ee5e66560000069579a2ad82194a8800025c80005f89a366f6000000000008d6000000013fc0001aca3e2d76c583835227505e45fd00002669bfb9911bba91b8000000184c0000000357c000a2462ac00000000b5c0000000b920000ff60000000559800000000000000f0a7fb1a907074a5a6e100000000000764937495c8f838ba800000000001ccd93000000009b600a700000005b1950f000000004a05d5000286518946807d400007ca971026000937d287ac3578000621c00000019067e1c00000000002310000000000000000003b24000000126c84000004ee000022c984e000090985e04684c81f4f901010658f9fd2a230e7642f44604cc952145f80000671960457a0f282a02021869f7187962289008c765b580002d008bd98110f834fc00035700004a99b
  | 36 => 0xdfe5cb8000535004e4b380000000b8862380003d6400091582696a5849b698a4500000180839a8a0a2885b1220263e58e17805c4e10a359873d9c1912007b0dde23512e43528bb906a9c4b3c147a09a215fe0000000253400000027fd000284f0c8e4dc00019fe61780000000cac3670000a07c000000000000026a40000000000145000000001381d57869000000019701fa400000027b6000125a242d23000022846efa7a00001c8200004ca0000bb2000000003e8530812000046f000019300004e580002a1000000028722cb88e00d35f644cb00008139718673c00000001515f4000086405de5df97e6000183269e8000882800000006d910e80007da00000001bf864a0de53c4000000000000000fce000000022992f626a8000099017c0002360000000077180003931a8e510111800023300000000000000000023c43d587728f99eb4a0a40006e015d22c9077c6d024a894824260cc812c0f39c68a12c1e40eee7a855a80000c7800000018f600006920001e9c0001e4c00000008659ef9000098296f800063580003ce1b6b24fda1c8b9938a00002aa000000000013ac000000000000008901f35000000000000009f0800000014d00000000000192e26da82355611a68e28c30674cf06320c8149c2800068881d14edc56c70b80002f4800000000000001a4e0000b6c00008786f381a445f55800000000000000000025f40611db878e93f14ffc7e42471f780ed4d089a808ec1f3009653c96c20f35b351f81c7209853c31a0e1e07a052d81c003d64d722f229486da5fe071000002320000000673000000003f100000006930e3e9770eb44a48000000219c94b838100000002f18b4c000199c0c6c3c383aa16200004364d2800000000006fa800024d8b8090e07742b144326b2131000002df228000000000000f80e1c2ac00922d9000000000003010000a0100003a1c0000000000000000024f000000000002838f471809d280000000540032a000119200001c4000000069d00007ba80001e29b21000287693d18f256e0ca0356d7ea7258000000000006780000000000000000086500007d99c7020f9b6a3ae243e781a5f800008cd00023c78070ca64dd81cc4fa90a30001f5200004cc000000055900000000f1d195a31a69f91960001a4a7339ef601880002df1e325c7014c00000003db03970000f7e49e000047b28469c8800094da17a1b88a3c0000a4c433824c00000005ab10800001344000138c84900000d9400000026540000385523800053d80000000b8c6af00000210000000261e5ea00008879bde16f4a0a2e99c9e000083c19786c5986800000000007eb90fc80d000035b895673c80d420ee5981ea000009104eaa0600004841a3e1d1000069c82b200014380000b428d1800000000000000000045e12e00000000
  | 37 => 0x2100dda71480000000000516088f00000000001d9021b15394258c8c06f8d7800017282b78fbd45665448738bcc47b4cfc41a27b22490d84442558413ea8602e3449600000000000000000227270398e853884b7780850f3701bf278b8000000068a98d045000000002f50000000000083cc96e74d800000024768141c8e43916467a6000000000000000000000000c42a9a8200006e86aaa1b0a1a03749db0e0217aa3ee74c47c200001d6686800000000000000000000183e0000ba21ab80003921fa200000005e9877a31624e000000004fbc0000000eca16781867e7400000021d8430988c0000cb02508000331d9220000000000088a28b0d5500001d04469a1626e800019c8000000243600000000001dd261fa1860000e2461f400039e526666f0db2000000009040ec5c1a3405189fa800000000001e886b4030842282606ad157400000000000000000000092c032e00008bc5428e0071aa4a645708d80a79e4a73e08f65eba40c9aa8bee07ed9a4000273e849800030a18e223a8e441ad8c5a0c68d149848abc46a93c019bdc0106e973c59c8000075000035d000000000006e700001f100002eb25e23ef8cb2591000000008b8524981e3849b3300000000000000000000000021e848318ba0001e431ec0ea000011ae54d000051a000047440007dc800000500000000000769a650552858400000005928000000000007180000000000000000000027fc08300000000e4e76a000052018a274c0be0856a7e286ce2240002164988800000012ba962000093885361768cda560a8a40868000100800074994884fcc0ff000000012000000000000025c87e000051e0000a6700013a800000000b19cbc000000000006d000000000000000702000000000003a2c3d868c15ee00020bc0c30f321e1e68e000000000d8000000000000007262ea000083280000000ff20f09f9e23c9fcc45be7fa31d23c2a284d27000008054dd5f108500002edd4ee0278d42472036a0000c1615400004111d42000053e000063e470cfd20000eda2620000383213c000143511300000000a162e52828954233a626a01a000000075102c219b90df8d4000086f50ca9b980000ff484300015684cf804600000000000f264c0062e7d8c926000065c8a5101246d01182baa79072ea4840000000000000031822340000000000000027400004eea7cc000276442900000000000000093d0000000924065761c063211d1c184ff80000000000000256d00000003e61f9c52300004a100005f1244c3c440007f000000000000000000046b000037f8cb797d40007bf9199000000000002230c5178d00008d067280002e4c00094883ee07b8e0578700000000e27046800088e075a00020f8000267a0000ec27a11cb400012c200000005a51b2d269800000013990d1d
  | 38 => 0x221000013ca7c50b0892327f80fb000048608e209c9f8618a80001e09b4456760f52e162086941cc419826b85ed800000018481a3183d50880009b0c7ec10ba7d889e800037f07082b99b960cc07d40f7830e598848812412d48f71c123e580004c78000964e73200012e85d48000000197e000081000000000000000719139e6d69a3c0af00006062565571533a441078916ca15c0000000000279e08212b20d7800042725a0000126464d27d32cd80004ce5d053c801934c21b607440862081072c2b1800000022ee1e7221a0001d4e0001e540001e2c2010e8e769000000004249c125ce00002ba000123a00026da08f400000006b800000000001e96487d25c621058e8e90ddc0000000224969c1d6400004080000000ee80001cfe00000000000000022000095209435760ce60000000000221654b954c64f800000000007400000000093b002caaa0000000397c0001ff000000008ca000174c0000e9e658800056180002774f8a000260e00022a067c000000000000001bf733d841108b00000000ff70001f1c6f500000001228000242c56a921963b80002cd0000000128a0fde4d200003bf000000034602940001f4000000000000000062800000012460000000000012f000025a11980a64589988291074e95a800041c80008ee800000000000001c767db800074822da0000000000000000022420000000000000067e105606380008128000980820a3960000083800000000000000b5a0000d570000000194049e70412be02d98d415c00003df1e5685300004ce10bc0001520000185487598c842b800051c800082900008b180000b1000034f812d2611236661000061120f08a700000500f1a9fc884e00013e2000000076c25c08a00f3093b9a327e927860de1a4849093de6270e681c906c069b815b4d5023800000003252728000211a9e292a40de800000000000000bd00000ac0000239c3919cf072012e69e708fc3f3094600000003b5800022425240000be662044160001ae2a0182f600dc1d52b840000000c64000000073680000000ae2000039e000000000026624521a425450000000000000003732a080003da12d69569c440c0566e99c0000436075200000000001f3235e9d020001aec0000000000044269d80004874b8e817179174fe538000060c17f9c202c3269000025a8914950c00022f300000000fa85143b2d3c200007760000000a1c000000000002cf00000000000534800017280000001a2e000000000024ac000172a5a49db290380005be00000001e3800000009d48a484fc8e092e440000000858000000000003a0a039e7c00017e900017cc47bde3f1cd908e61180006e88a0400028323cda024189800000007f300000000000af6000000066680001748000926a7bc06f24145ec88f75cd845a602179c
  | 39 => 0xa000000000000005cb000096b035c437225e0edc000a0e40000000000000003380c994c0fc84a80000000000023e28417aa0c196be4d955544dc000034825ec0002575913812a852080a30490b800000000000c8235c000083b400043b80006fe4000000281400000000000000000000000006d50000042000092d1739c414650eba2cc06640001e366eb000000000000e6800021ec00057e00002148000a03128c7d896322a40c000000b7e000152d2dc000000004102999176000018c33893b478f44055241ecc2fa876037a8e9874b1ab2732a2d2972000033b800050248213f800000001f980001e460e712f40000000000000000000007da80000000000000142c0b7a62034b8000000000094f9484944825000024b600000002390000000000000785e600005a2163c0003d1a202468131b000127c3eb190270f918834c237e00012e05d7086a721a08c6c82608748c1e05c007460001ef2000000000009394b0162b00a8000000192000000008eb0d04000150600000004731f290000000000000000025904f34cf06ba000000000001bcd3be00028380001384000202e2b4000077b8f0482b80287e815e2072800050c00001c600001031f5e00000000000518095800019a800000000000000000000000000015e400000000000000593a6c23b4a74800000000001e28000000000000008771c3224b05d681c0ef8a171dbe44c806a4e180500d2800000000000e0c0003031e9237d21bf0fc0f3479c0000475937a19e09fe5bb001b00000006311d0400005f4000000000000000000906000000000000009f4000000021540000000000000000000000002370000127296500000000f9439b00496ad800057da5261d6e5f00001f8000000009e8a75425a000087c800011f000000018237c1a44f570800005d04a20000000731a47b3a080000001b3ca14082c000000000000004d6800000012968d726f23b88fc868200785b417d15a99400206a81e414000023583df00013506a88000669800000000000000bba00000001b200c26cc289c00009a4751c00000000002ef106060a40006bd000000000000001ff85f704847b78000786082e000187b87025020000b3e0000d681a623c00000b6a0000000000247f00000009e00000000065a00011415af00000001fea00000000a70000a2119f400004c857d000000000005744a2e00000009d11900000000052f80005fbc0000001fdc83ec844844863a0000bae3af00002325d6027e97fc045400039c00005d75fb8000000000012b03a500000e09f927e51d8436418785e258c09e909f6006a69a00000009659f8ca12800020f4000810800002ec7d863980000000f0c0000fe52630000000237400000000000de800000006228000000000009f800070d000000000005f8e88e00015b4947
  | 40 => 0x8000000089e00023a04f2c00000009c400000006f4000081c80006109f700000000000000000026d66ff64ae22e800000003a85360000625c000785a7ae58188b60088d594cf27267570000a24835187e1f3a0000fd4198978f00008480000a067c31d72000000047783720000000000000000000006d2d702000233c000241c076d2440000dc851f12d0000000000000000000000000093e00000009f7e3842ae96103070000000000000000000000ae9000000000000000000000625036e0ad000000000005fe9546077cbe20ff99b60000d3371f0ed42fd169685c1c004c10000000189e14a0ed826c267e91202e6000000012e000039ae13f82380004129b6600000001bf43d214d088606fc00087b80009169232000000000000003d39ec400018b6000000085a000856a1bc656c0c067ce14de2d8a6105718ae76028000384267620e0000000110e24491702ce860300011c284e800090d0160000000000019e29f518ac56d40000000ab31e2c54c00023ec7a6a6f6a089ca43ef231003c01b65e1000075e16e200026e200023fe0000832285214400000008cda1b680280003b2234220fc7b600000000000000000000000000000fe5690a0400002cc400071e80000bb800068a000000019c4239400024410927024000000128800010a89d610101578000000090f00007ce1af000000027ca1c70000000166a6d2a156000118458c249e00027c90000000000000000027de79a00005da000026580002db504e40517ca1229b3a00006ee5e4800000004188aa000000000004d30000000105e000000000000005508000000008e107912823c17e40551258966c000000000000000000002464572000000000000001caa000000000000000001be100000007992221a18800000000000001c6c3ee1f462638fae0b7589697524b23db400005600000000000035c000000020b0994000000170c107000033e5a0c08da5843819a3a3d15ed271303564a624d85cc94e8659a2fe43489da2c804ee000007966c862007a00002f208a19e487ee7558000880144c0c7cb2200025ee0b140008f593cc56bc3c076a5698000000000002f4000016b4f7163c1aea80d92f800097c800066300003cc5d0302a800095b800000000001c940003d993fd60a0000000000061480002d7a5710000750000000000010ac3f680008630aa800017201a9c87d0000c6a2d600000000aca19480005738de41598c52876d0de81f9f7a5e8911605bcb5497f21ca53380003af9d3d8d9a54212b8ea80448b322320000000000000000000001d4d25f19120000000653ce198f88000000027400006371f59294755000090893d275e625a38a80000000aee9d9a6ec064a71e0e59f90000099230f8d600000bd80a188e70000c0e0ced456616077879807ea0389082751469
  | 41 => 0xf167b1bc449a8e934900000000153167b8000000000000013d9000000000000000002682000000019985ba00017d2000000000001f490f00004caa78846783f329580002ae00750001c28000283451d26dc67500007ac114680980000000a4258987d70001f560e0103a5d0844e0001f44000015c4ab98b2315080889f000087f000097958a007e000014ba114000000000000003a20bb02ca95fc33d0002000082aa1580000000f0024a00008a980000b612267dd4d539b3049a2ef90ba296230e3a9071200009c8090800000000001098000000216a0001bb6000000015a0310136081e55c94e00000000000063966480008bd00000000fca48fa107000000091e8000672c0000000aac1d580002118ada32712b80000b7700000008bc0d9e53350b400022e0000000000000008b2268c00000002e0a1c8317800000000000002146245cc4c01680001be90e23c700007ef181605dc00029800000001cd600000004b2800045f0a6c40700005dd800000000003a98bda00007b400001561908000463cde209bcfee4df800001a00004f60000000205200026ae000000000011a398280003b745800dd8000782000066025765e9000058d80004cc0d1e95780007c3a4e610514bc7bea3820191eac7c80000000000000025b2000000000014fc000000000000000000d380000c3b45e80000001ee6000235600000009a5997a1209a925e2209a72491fc3bbc000000266a27a0000030000000027408de0000000000000000000001956000000032896f474051a10001c3a000114a0000ff0000000082c000000000008c580006ec91741fc9c1b925813c9e30057000122042c9a46000000062f000041a80167cf00002018adf9629c290000a2400000cf642a16645520e4654e5cc00000002dd8000000000000016a88ad800033714cc8b6110800000000e2159a336000022fc000000000036e800004795350000614000067a5ef000060b1b4c24d01a600b9c7b0000b9c000000058580000000000a1ed2a01e90ff465098c63851f0d4858000000000000800000ba8a2a3bb5a56000180c4fe8000000118e000122200003da61410e8a0b8c14000097f2f78000000000006ec0000000000000000000000000eda3b4248143a00003b20fe000098c800000c960a00015f20000b6e7710c3800020b48cba2186911a7c76197e865aa00647e9b56000000025a93eb5c921c6543511c3e8000000000940001a1800021d46734a72000000003196f675a613e44f1ac661f11ea84d9a14000000000000000000dae92200005a7853a00006441a5287a00000001eb8feb00000000001d88000000038580001a199a25dd0bd6015800003280006e90ec708fc00064a8000101140c00000000000000192000000000003f5a29e5728000000058800000405c10ad499
  | 42 => 0x8ea00005ae8ff88c70b520000000000000000000007669a5c0000000000017800025b629cd46a759909a09881265f5800000015c068a80002c5a30c5f1c2a04e3a50a00000000001acc8ac80003bf16ae8b91c0b01780005cd000089405bb00000004820000000000000000003be98f40c7000091600009a9800061a9dbc3bda55400020be5fc089a0000a6f0001b697838000340152c3e715d634185c079d000035205ae32d800044000006d180005d2968c8330d100001b0487f800000000002b38000777800000015d000021a0000000077e000000027da77000002150cb86998922000000084400000000000905800067a1d9b00000000000000000065880000006a117ed000049d5df00000001ed4000000000006c1000000062a00000000e1179e858a00023f436193980000000000108400000006dd04c66a7168e3e795330001f36853539a71d09f000008a3a085ff000000007cc281c918561200015d400023aa0001b100001570146800000006ca820161e00002828e9c00028d00008a38ac300000005d2282500000001170d220000fcf033902c93f80000000d2600000000001140000000000000002a4800000000007db1c383fa97126e6000007498027210000000214e6e5c00000007840001e808ee00000000581253800000000000001b880000000000000026d000000000000000d5a000000060e00004b6800000020749df1c78231cb1e0000266000262c2f11e20000000000000001bfc0002e3c91419f00002215b9000000008cc9fda7a29fb60000d8c3379cd0a134f6f91280008118cbe353e84862207fa5dbe3b646e42fe0c818e4089d36e52889a00001d1d397600e6d7917f8798000292a004174c0007fd21f03ac96f17541fba0c981704e9400029e01e766b837f192884102800005118c88032000000000000a4c53c0001d941e0e64e79606ea13098a40000000000094a00021a800015e8a25000000000002d3800091800003c50f5d00000002e24d626ffcd566a00741324000008b8000822800000000000000cc26cb800051b061500000009de80000000000000000000002fd73ea1b8000187600013e40001ece31ba7f417ad07a3a484f44c0a3ce0bb000000000000000200220e7fe0470000000191a91b081152c9624836800000027145ada5e809717a0841236e0000e1e159280811c196c4ed9959a1ac0000000c466e09996000277200000000c0c00088b80003f18000000000000000000000a9a000000004297ba386800000000000c5965a3188757238c0000000e5a850c00000000000000000000000000000004719f42000253a0000cc400000001a1000000000005c8800043c80005db9ab954a80003b19afa09ea0e2267028c8aba64a0000000050400068d000018889a88b787
  | 43 => 0x476000143600014c03691588355162c200a3987189adc0f883d40001dca00000000974000000163da2a00000000b8a00000000000000053e0c08cf909800022704f50fb288c929a8ef40002800000000067e0000d98000284c4cd0d367af1f3d000035709ad135311c317a2200388ad00000a6df960000f8617200005510000000078f000088c0000000314000096b9e34000112a0000d82898000019b4b5667680000ab9eba0b8ded8763032515c80005f20000000194e4130f4b0001e9e000000040d80002401fe00000000000000069927825ae1b648210ec06d4a1ea33540a23730af223b800016bc0006f8111288824b449500003dc516e02f962200016c4000000041622620000d583ba9bae8939ef40001aea03580007e684fc9c407bc059011300020d600010a000000008208cec590856f08ecb72000209c00000000001a0a240814679b8e0a00000008b5151c00010c811f800000000000000a3282800000000e2e13a00003b780ea00016d2000160c63e8d3a00003cb46c8f1e33a0d4b8c21b3e000014aa1f020da0ea2b80000cf70001a6a0be422551100006fb0000075c699000265e1a82180931a1bb00019ac3cb918a50f289f9b4000000000000001fc41a982e73dac60e04ac7550001d218bf02c70000000680891193d878e35407144c3827900028160000f4f00008ae0001f6512d4000000257ca208cc60000f3321e4b8748b0000000000000001161c9c00095880000000f5b29f0cc87ada17e321a25c90a95031cfc000000000093093245bb928647f9eed000141225e271a00021cc376000000002b781605f872701fc8d69d9e0000000000004a0000000000132800000000ce80000000ca90000c2a2b30254486994a000165200019362c1000000000520001548000000000008aa00016568c818040000000273288a3c3c37e0001364000216012300000000824000056e51684d633583283a0000000018224e400000000000000000000000006ac000015888742628c725ac9ec679da842000000000020107d700004e3c34204d00703c1c9508419e8200023fa0001f0814321f401700000001d627b580005c74bfc000170a0000d0c65da83e4019d384db2064156161c00000001264000000112458b80000001604a1457260002468000000007d88205021da29418000298984a76a80000000b0e000007400000000001f5804380008998000a25a628000196845b21fa3545502643000000010c05d8270e27889374940000000000083a00006470000375a1c200024821b900003d49f9f3350f970000000000000000000000001df46c01eec00026f049f80000000000000000049e80000c0276272604ac07c8b9e00000001d28c2226b84642d2a7ba026189296345ee16693c672415103438b231a20ca800024f00
  | 44 => 0x40a15ae7518000953800045808a45b6a61600023a20001c8a392c0008178c1a36f09b82e94000000000096705e029927008c91e400001d4800010349ef80000a2cf3a16840000000dca0000000069dbee7761ea400008980000000519834047c91106c7014800000003c4800002414c2000235200000001bd00000001290000000025686ef947a2a25e2d86800026060f283a200026c45e189c6632800080f8df20000000998258b06500007e2826a92298110002694570c87f5681fc2706a56822357581c0a6682b901829ad14a8000269800000003b8103e00017f6000000000000000000000959c0004870000000000000000000c90000000000000027e635f9d8202540001dfa0d20000d17752e24a000000000002cc838000000000006b50df900008da0001a04000000000025f60000eb689e143e3d9000000000009438f740a3520600000003bb000000000001ce000000000000000000000000000007c0000000000015ec6bb80000000fd80000b9812e90f657e4e4a000000010495cc484a81288cd5980002028195000030e4ba486b245c2849b7652703c64c31f54000183018a0c9229d80fd4a78c4200007af000234c00003756ae0bce14905a000019240000000000257e6c1800054fd6085a90000763800022b0000000000000000008b402287782390065800000000000001fd47d81bbc000241027a800078c000000000000000d4623a26ee31720402a700000001ad26bc00000000000000000086890fe25800000001433000223c00010cc00000000d21d08295000000000000000a8e4a0a6ac0ad64a03fa4000000212271800001b0cdf681a88de3978f5e76b07926b007423b15e264298000000152809600002b60c444f406434738d1618d00000001e9039800000000cf8266000039ea800000176a00012608aaa2040001bcc63428b000000f49ea80006d08944610000023d500403101a2762c000000142a2ce00000000d886b610b04231eda3efd61443d25ba5ec18145e50db851ba68600000004e000f842500000000f025b9948600028242398d6154f000000000000000000000083a6ce00f1306000025d0000000085335d898716d1de41ac277e30b9bca677a2b0711942600022c48a319164e800000dc000065d052000001422fda0c41338b2c00000000db04e6528000000004f076000002c48c247088044597800071780000230000098c000a0800005040000000000000013e02d700000271496a0c24b847d0a288088000000000000015ba66380000000000000000074bc0008b0000000024748f1800046b4000000031d000113e99b96c000000005c51d0c569953d474e5d85690fb646a085e31242462ac800020e4c68000079839404f80000e74000000000021080001efc3158000a1d000000000000000
  | 45 => 0x952f2b080008f2800095300000000000134800000d156238ea61802b09583d7086528880001500000000246a67dc740000000000011ab44c0000000000063821bc4ec00000001f2400000000000000000000016d800029380007160000475000000026ea563800046fa3bc02d1f1ba2ac000000258099c80005a8800000000000000000000000044ea12801e957e231815500000002ccc000000000000000009b7a03c6f98f9075c0000000000091c00000000000831840600005a63e351a94609eb22204b8b8cd00fc7e394aa8669c3600001596758da082c8d315c698d80b71c279d58fc447925829d1a40a410100e2e597782b806d200c0e078a18000527800067083500b687060ee4217000062194b00006969b247fc8f4492a839094c800009b00005950aa40df44085941772599000002a665c63099087d3800000661ae00000001dfc000405800000000003c6c2d5000000000000000000000000000000000000001ee4000000015a80008a600009cc10c4744800000000004ea80003e059dca1e12f0000073182a849800015127e342fc61c9676710086461d000006b1523350400000010bf150a3c800000005058fed0739eca1d790cb88ea86a71096d830d914c368a2f874180f632e671280791b53229c0640f11380f756c82bb05783ffa4d49dba09021a078c84d185a6de9db633c800052b0302396c46a000000000000000000252594c00021b94481fdc0007b20000000000078100003c7c00000006aa7e2400000012680000000704400095e000041b8000610c00012480000000eb000000004e6c0003e30000432475d0a380000001d3a73b96ce9331d2253f800000000004948ac839921884e48d2a2a280da7ba000046cc4a011513ec74ecdfa53d1c947391204227e760749180084b00240860000a22400033e91d24eba31208aa062487824756c82fa02a18ce1640ca40002214564000000000e40000000634a41e8f787fe6db8b7a6c29f6f8c602d618c25185cf8fba00025288350d8a22440003a894da88486104541c490000f7397907b26b910787840b55657a7ed13f90be203685200000003e092b400000001cca52a5aa95226b683a307d4d4e6b7897a958000000018b082980002c526921fece8c08d14f048515503e6638635007d96fd62884b48c7e50d19fc000000035b15fa586102059e82ca7afa4d0138814e00000002431c7e75f0000000000013700000001018424156e9fa135e000000039085c4000196b91f434e129a44691e00001161fac00000000001326209971e9b486d7128400010a26b200001f95581b55333891300021de1690000878828105e8000000163a4cdc0001c246de38380003b5d3186cb131757740008a4006e3a255e7a2b8000000000093a8a861c4c0000001238796800000000000000000
  | 46 => 0x4b955c893275083d0b0200003b83198000529a3f8a29a068000156ca278f5803c873c5e61b9e84582e821280001028000a05cef286380000000000000000000007a61fa0e9c00000009a780003f980000000de61c040002e80000000000030f094f00000000b9400016722c20001cd223393f84599fd000000000000000000000000026f80000000000000000000008f900000000f4d0000000000000075a00000000b8390909be00000006c384406c8c000000000000000000000915040000085c9ace8059d6a09b54c491500004d580000001f5a0001e149712268000000000005aa00014dc000000063f00000000e300000000326800032d1e1200011646e4a6a827603641c55556576990443414185bf8f0e3889b9a79c83aa7d31360a10d28073f00004120000000000000011ba7f90c845c580001b4c00000020ce3448000856c0007cf896c3d4168a057a7380001bc256788d21351d6e3c2000065692745e7a32c9248b4875498b42fc1db45b780006a800000000a5e681a1980000000000203a0805f286b59e6243800006c080000001b2a74600000018b6814200000131f8400000000d800001f0d3f500000003a4247c00011145dc0761000000000000005d89ea278f88a25a21bfc1801a8c0001c5c5e0a1e31550efe98aa1b90b91a5e9fa800058a11d011124441e0051c00016ca000145e15211ee3ea22583ab800000006043d300003e6c0003d51d3c06a0000968800035349a22314000000083418926fe51d924c0001bfa0001b228dbe80b40c00009ca80009548d0a000170d0001d6c000000052900006bdc0000fd1b085f9c0008b886856332254000056000000000001f93000040b539991846bc96675d0c1e7fea70c1f7a55641988ad8ee594800e8b66a0b243a237016890f61a62c69419a262406788a5405268dec5e2986e0a68c4a56d82a85bc84de23f8ee636a9d761a39a0e3ec1c5a52b832c0e740006e19e8c8c110520f41d4c0002044103800000000009b0000025d84f600002c006b800063c04305659b8c000227e00000000f066c6783063b422239a00004af29c1faa47c27e08679b683101dfc9ed0f2402e400075fa636427ccc99f200001ca14170000000a0dc000000000080c000000000000000aa200000003738000000000000009940001edc66f800086ca13270de3d238e000083b87967c981d30001b8a0001ffc8fc800000000000001df696980000000000000057454999e000000001c69dc86db24c0000092b000000000007708d900000000000000262e51e1cc80000267000022600000003f240001eb566881e80008159820000195c0000000780000000000000001d13000055268e1af67b425ea443000089a9a7000000009001b9400000000001f040a4832171980005771a240d61ea70ef0e36a1f
  | 47 => 0xe684033480001c588e900004b622123d12c2800097e9a88000220e3dc80002dd43668910000532d6e4621a2dc2f29dae00000004e200765b800005d41a9867014b60001eae52608600000a8c00007d200000007439f1ea09a5b44cb9cea00000000000000874000000000004b71ca0200137c39993780000db05f0000046340000000336779a1206d641447bee0925629bfe185a4c4042000000000002a80190000000053b11334f6800e3f880000000df71088f3e471400093e91d7000084c454800010f000000017d46191d1e5438a1c0001c0427b89ec9708ec429dc8f899207a50000be467c80000d896cc850a6e80000d0266a8f884f380000001c1300000006a19a8a7e44a3609a000085f0000000000001c80002de235e46c00000000000000000000000000001d4955e8a5097dd0c60000409000000044c40004bb10864d0a85443980005651fe60fe9fb447554240c8800082587b839f1bc05ba80a4015623523d17ac51fa1403259f199695f8834d00000000c0a8830baa0e5228a0000556000000000000000000000224ced072d800035c80009328aa6000000030c80000001bd6363a29a5d9800079480000000fb4000000082780001b8049c09b80000a580009a88000000111e821a5da980151e837823a5b520a270a887c75280000000fa694580ae7c2cbb80000000000173800013c80000a6889d863c45a000034f00008c50000000025f40286010001d2e05f9dce473c0008ef860608402f89d3057c48907816180fc039e11c47f88d28937a368a168de059e013002e2678188d2fc00000000000f6a079a59e000031998507f000007547bc14527565186000000087482be9b921c4000000000000000265d1420d40d0000000000000000000000000154e89200000000fde00000000000f221e405dc0000000000000037101614770d2c2c18a7e59605940180e72000191000000001f9c4bc8649eaa2bf0caa48025340000290000229b40300006ee1dd40000de70001e488168000000009a00000000001e4237f65924512182996a44236523e85e3197c1f2800028e000084e000011b80004fb866c08493f42108000000000083213486cd9b4e90a1062000000010e000000006dc9d78d7c1761ea690489ce00000000000000492000002c0000000139400001da70b000000000008818c20092858c1e79fd80001be800000000000000000046c16610a2398800000025ca00021748e30e614988c4e1965c2437ec7489991de86d2593275b4d241ce80000779c6e0ec155a000000020c000093698821d88000088800010aa5f90721d325ff40007f2117232140009f74e6a7bdd25e69011b7513800000000005c146fc75603a60fec00090c00004ec8e280000720747c00089b26400c4834682219380000eee5bf139c00014e4000000
  | 48 => 0x1c6f7002c000000088705124c19ef851c11586ea04b210812c441689f40878f607fd8c3a12500e89cd8ef085780d27df062c7e2c00057fc00079b00005c20000482a27400000000000000000000013103dc1e5013640b800000000000000000000000000014b49c0a4f225fa45f11e0e32000211c6980004000269c53205f284c0e560001f0218619ce00000000001836000000099f22820001c5404e800039a472e00000000f200000000000000222c000000030d00000000ecc73717ee3f4000077e85d70000f2c3d00b6054680002060000000168400005fa257800000000000001b1e00006a266d2796000000000011560000000000000000000001bf93bc0001dc2000209800000000001cde8dcd31600000000001358660a6660000000a190e7e243a2be0978000765978e8f500000000cca00000002a58000000076a80800000000c101c2894574680001f68da840980009c5a7766dca801766162060d0fc207880009c925fe00019d246e03185db50d383b15f02c0099e8ec996406200000cd19b05a080000001fee0000a98000000000006be26f00120001cc20000000466800000000000000f3c31c249c95b1da74a71e5e9fc04d02ed10da000000054e116a408957881e272e9239f187d347f93dc23b095c11267e080000000000645167c713901e0000000a0f000000015bc5fb090d16f000038b11171750ce45078e5212b41c0375110b702a1ec66a0000434400000009909cf126e8bb03e800007bb993000000000002fe01c24c704f22410456190133660b419573600000001bda0000000000118000000000001648742a831000000000003f50001d64501000048d021607700000a900003b0c000000030a381000000001b9665000029ed62a00000007e98000000000000000000000000374a62643b5f121239af2289a094666007c84307c8750c2d42589115710d0f09e680003fa000093b000078f198a636a3280a280009bf200c1d7140e72a1e2a3abe57423020fa3e009c04c88af400012ee2e69f483b907308af1ea09960db47a503ac2748000000000000e4fec17400005efa5d00b4164500004aa00000000000000000083600004130d693d7152800000000000000000000000007f97f288d80002708f780002498000000086f800000000001cd11f61fe272c36d800000000000000000000202c385c03c0001a1e00000002168000000167e6261b7816080008e4a59a7c5c1b0749510a99585000ac00006f20bc00000000000000000000002fc8000225229647e00001e880004e9000014b1dea0bc05e81568a1800000007078000000000064f00000000000000000006d0000505400000020dc00013a65460d5200000000d300000001b165981b126ed0d320bfd9a0a0094823a6dcbe32f13520000eaa71f5af81b31bf48d
  | 49 => 0x256400009de10f80000000000260c00057807e60000000000210e06697f1000147a9d6800094308225028dc200000008dc88cb0540462000000000018561da0000000048600026b615b577a27f00002059b057158e86000102a0000000000000000000006ce47e21d7d4ba8e78e6d00000000000e5c0001aba12c0000419000005a94604b7a63800000000000000000000019391b6254a07c000000000012f80000000a0280000001aa600000000000000684000000000007ef80000b8400000004b465500000f12256000016e3951dba73fc28010d00006dc000099d1f10806254a6049ca28f3225247000007c880003d2594618da6d432e8e18963870c72ba57a0e180009411a946d5253c469114345559441000b9017c0612495a6e054c931a23855011d90000603837b1b389b22c40000056a858883c000000000000018807bac67664980009f1000000000000cfa32691008cf00028ad22bdc9a21e859100000000000000506a8808c0094800003cc4b2112263700001e7400000000000001aae00011340000ca70001e5098903bd86d283606e0363507202a2be8392580803548f02308c7a37c43b11360001d6b9e9a8aa00011538a9119c6c308fa41f80000002158000000000026bc00000000001e0a000064656b02241afe77829d16b099b00005f19e6a00000005e400004fa092a0000000000230a4e3661c00023ea00027d60000000000000000000000001a9e9320c78000239452e017128785ec09e00000000000000234463a8696592564c933961a5491a68455c4482bc040743a8bec000211e41c0f8e149a0ba9440f5a3820000000104200024d653180004d3873e7b0a46b0000000000185c000000000000006bf80000000be87ec05b0000250059d000000011422ca144a00000004c29ee200000001be01b25445c1466192eb0b880009068c7c6df0fa71c7d25d000197800000008308fdc6679da0338183c00017d8000237a00027ff72983a409140007388f4a29a92aa88c5ba06c69c023530c7a4a38b6f2ba22ca862800000000002ab8000000000000000000000000000000066e0a0800011e2000000000000000000000000000049d8f9200017de12923da00000000001fb261880000001f16386c00018216002ed9221174453800005328f80d9a0000837219a8860598e9604fc69e8f406709d082a290800000001ee0000177900000000001ba628e8000000000000008725ba215030214d6000200898e800048b880c0001b8e00000001bd800096a93f60df11e07c7520e00000000000ad2000000051518be0000018000000075e800006f5b62335c0000000000836181a9021552000000000023881f40fa26c612ac0001ea800000000001df218711670bc800073d8c8017a400013680000000d1a000000079105f600018
  | 50 => 0x1afc5f80ef1000000000002b6148800000000000000000000281a19d00001b60000000000000002e00002866919891e1ac800073510fa00000009da827600000000000000000001c00000003d2034f000057e4539ae00121a542170e9a5bc145c8c085be9758d928050129371800000006ec41706a93fe800000005920000000000000000000000000000000000081312f20000000440800089b87dc000000020494f50000000000000000000001bc8000204d5e620a1e2400000007dcc0009e5010457a8000723282a10698de60b80004b194f82e100fe00026460001e8e59b19e482e25de9c8175a00027c60001fce31b0000000000000000006f88000a2419ba4ad92bc24e00002728000043173a88880000cf5420000000000000006d61640000136800009e686124a40000000012e4948d2a4320361b489b38f28000153e054800017f25e017199405229367000000000023f61c78000000000000025d3654876c6cdc00000000007f293409f700000481cb83239b310f9000024b8e6e000000083f1fc60000000000000000000000000000000181022386f00000000000000013ac0000002768033044a04f8c9e1a5c0000000000300812413b0edb16e000000000000000229a1790380000000000000048a9abd50c80000000000879000065410325250f2a1aa17c2208c000502d9ea70c05e22158000000000024c153600000004fb40000000000000000092183490001372000069c0588000000000000022e84e080001ef800000027c0000186c6c99e7880d80006f4874372b0f5f961a42e00009ac0001a5800015de00000009be8506000000001ec00000000009c7165c81ba7e40000000000000036b00001410ece9a0000037410b65be839928815c4000000000000000cf050e5f380008b380000001f341118000000142800021da0784b4656b4a3038996b44aa00009f481381b09aa4021807e73a13662b58a5c95981764c4a34e0e11f2c220a2f79fd8000000000098f08501b111780e619e60000000000000000019d87ae00000001c3c4fc00002618000000000000000004118faa00004e40000000000000047a000018b5c1644b11a25a180003260000476a6525ed203867e99f60000a800001e5c2ff800092e80006cd24e8000057a0
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x8de8758d10040011b90eb1a200800327dd163440100064e3a2c68802000ccc7258d10040111db0db9220080032b993724401000656b26e48802000cce63dc9100400199ac7b9220080023ba1d624401001c7643ac48802000caf745891004001958e8b12200800333dcd62440100066639ac48802000ce662dd910040019c8e5bb220080032de1376440100065a426ec8802000cd783dd910040019a907bb2200800339e0b764401000672416ec8802000cb742dd9100400196a85bb2200800335ccb76440100066a996ec8802000cb776dd1100400196eec3a220080032ddda64440100065bbb2c88802000e356559110040019aeedb9a200800335dd87344010006e2390e688020008f687d8d10040015cb05b1a2008002b561a63440100066bbb4c68802000cd77658d1004001d2cc8b1a2008003a5591634401000763312c68802000ad68758d10040015a90eb1a2008003a5dd163440100074a3a2c68802000ad78258d10040015ab04b1a2008003b11c963440100074ba12c68802000e954258d1004001da100b1a200800335dc1634401000769102c68802000ed12058d10040019ceedb922008003b158f724401000673bb2c48802000ea6645891004001d4ac8b122008003b198d624401000762b1ac48802000ae68758910040555c90eb122008003a9a11624401000752c22c48802000ea7745891004001d48e8b122008003b1a0d624401000762c1ac48802000ec7735891004001d88e6b122008003b8a01624401018770c02c4880202ece77058910040016e30b2022008003b458e404401000770b14808802000ed1635011004001dc2c4a022008003b458f304401000770b16608802000af1860c11004001763081822008002f8608304401000770b10608802000cea62dd910040019d0e5bb220080032ee1376440100065c426ec8802000cdb83dd910040019b107bb220080033ae0b764401000674416ec8802000cbb42dd9100400197285bb2200800336ccb76440100066c996ec8802000cbb76dd11004001976ec3a220080032edda64440100065dbb2c88802000cdb76dcd10040019b6ec39a200800336dda63440100066dbb2c68802000e996458d10040019d6edb9220080033add9624401000755322c48802000ea9645891004001d94c6b122008003b258d62440100057543ac4880202aae8875891004001d5508b122008003aa611624401000755ba2c48802000ea8745891004001d9506b122008003b260d624401000765b9ac48802000ec8735891004001dc502b1220080c3b8605624401016675b8ac48802000ee162dc51004001da2c730a2008003b858a614401000770b14828802000b73855051004001dc2c4a0a2008002bc61b3144010005d8c26628802000be182cc51004001dc2c598a2008003b85883144010
  | 1 => 0x2c538462080033658d708c41000674b12e11882000cb9649c031040019d2c538062080032e591700c41003e6d31ae01882000ce9625c031040010ff0cbac80081770f991759001000637312eb200206587f8759640040bb0fb0eb2c80080030f9d564900100061ebaac92002000c5e7598e40040018baeb31c8008003179d563900100062ebaac72002000c6e7558a40040018daeab1480080033558e719001000672b14e32002000cb5645c640040019aac6b8c80080033958971900100066ab1ce31802000ce5629c630040011ef0cb8c60080033558d718c01000672b12e318020028bc84dd9300402117b0dba260080030f997744c0102864f31ee89802000cae62dd1300400117d0eb2260080122f21d644c0100061fbaac89802000c3c75591300400193ee8b1a6008003271d1634c01000657ba2c49802000cac74589300400517d093b060080022f612760c01000c77414ec18020008ed829d8300400517d08bb060080063ba09760c01003c7ac0aec18020008bf865d0300400187ccaba0600801f2798d740c01000657312e818020008bf87590300400117b0eb2060080030f9d5640c0100061ebaac81802000cae72590300400193ce8b186008003275d1630c01000667392c618020008ef865c8300400195cc8b9060080032b591720c01003e6731ae41802000ccd635c830040011df0eb1060080023b61d620c010006573a2c41802000cad7458830040031eb0d38860080032d992710c0100065ab24e21802000cd5639c430040019ccc538860080033958a710c0100065b322e21802000cb5645c4300400f9acc6b8860080033558d710c01000673312e21802000ce5625c43004001c6acab26200801e3d61f63c401000572c16c78802000e966458f1004001d2ac8b1e2008003b198963c40100056bc12c78802000ad58258f1004001d2e84b1e2008003a550963c401000753322c58802000ea56458b1004001d8cc6b162008003b158d62c401000753422c58802000ea58458b1004001d8d06b162008003b160d62c401018672b8ac50802002cb9769921004009972ecb24200801f365da63840100066cbb2c70802000e996458e10040079d2ecb142008003aa991628401000754b22c50802000eca6358a1004001d92c6b142008003aaa11628401000754c22c50802000eca8358a1004001d9306b1420080c33a5c562840100145e426ec88020018ec82dd9100401317b0dba220080030f997744401000657316e888020008be8759110040091790eb2220080030fdd564440100061e3aac88802000cac72591100400193cc9b9a200800327593734401000667316e68802000c9e641cd100400193ac839a20080033398873440100046f43cc688020078dc8798d100400193ee931a2008003271d2634401000666394c68802000
  | 2 => 0x645881000567418c8b102000acd83191620400159b0d39ac40800333dda735881000747324e6b102000e8d649cd620400159f0cb9ac40800333dd97358810006c6ba2e6b102000e8e645cd6204001d1ac8b9ac4080023ba1f635881000557426c6b102000aad84d8d620400159b0d31ac40800333dda635881000747324c6b102000e8d6498d6204001d1ce931ac408003a35d2635881000667bb2c6b102000e8e6458d6204001d1ac8b1ac408003a39d1635881000746ba2c6b1020008ee8718d620400155d0831ac408002ab610635881000567418c6b102000a6e85dd162040014db0bba2c408002b3a0f745881000566c1ee8b102000aad879d16204001c5ceb3a2c4080032be1d7458810007173aae8b102000e2d755d162040014dd0a3a2c4080029b614745881000557420e8b102000ace831d1620400159b063a2c4080038bd52545881000716aa0a8b102000aae84dcd620400155b09b9ac4080032b5d3735881000566c3ce6b102000e8e749cd6204001d1ae939ac4080032b5d1735881046d73c0ae6b102000ae4815cd620400199f0eb9ac40800333dd17358810007473a2e6b102000ccd745cd6204001d1ae8b9ac408003235d1735881000763c0ae6b102000ec4815cd6204001998e2b9ac40800333dc1735881000666b82e6b102000aae841cd620400155b0839ac408002b3a0c735881000537c2a86b102000a6c8550d62040011dd0e21ac4080023b61c43588100053742886b102000a6d8510d620400199ae738ac4080c2ba60271588100053742882b102000a6d8510562040015d50020ac408002ba600415881018572c0ce0b102000a6e85d0162040014db0ba02c408002b9a04405881000572c0880b102000ce9629c24104001972c8b8482080033a58970904101143ec36eaa082061c3e64dd541040018dcc5baa82080021fa1d655041019c3e43acaa082000c3f755914104001878eab22820800317dd663504100062e3acc6a082000c5f7558d41040018b8eab1a82080031bdd56250410006363aac4a0820028be845db31040031dd04bb662080822fe1974cc4100061f32ae99882007c9e635d3310400195cc4ba662080122fe1d64cc4100045ec3ac99882000c3e75593310400187aeab2662080032b9c964cc4100064f3a2c79882000c9d7458f310400199ce4b1e620807e3be1972cc41000657322e59882000cad645cb310400f99cc6b9662080033358d72cc41001c77c3ac598820008ed8758b310400195ce8b1662080032b5d162cc4100145f426ed18820008bd84dda310400117f0cba462080030f995748c4102d64f31ae91882000cae625d231040ef17f0eb24620816a2f61d648c4100061f3aac91882000c3d75592310400193ce8b1c6208003275d1638c410006573a2c51882000cad7458a31040019d
  | 3 => 0x4b182000a9e841c9630400153b08392c60800327dcb4258c100064eb9684b182000e1f52d0963040011bd0f212c6080023761e4258c100052f42c84b182000a5d85909630400153b09212c608003335ca4258c1000666b9284b182000e8f82509630400193ee4a12c608003a39c94258c100064eb9284b182000e8d72509630400191ae4a12c60800387d494258c100070ea9284b1820008de8710963040011bb0e212c60800297a144258c100052ec2884b182000a9e84109630400153d0938ac608002a76127158c100052f42882b182000a5d8510563040015b50020ac608002b66004158c100046f43e42b1820008dd87c85630400153d0990ac608002a76132158c1000666b9442b1820008de8708563040011bb0e10ac608002a7a102158c100054ec2042b182000ccd7208563040015b50010ac608002b66002158c100054f420e0b182000a9d841c1630400159d04382c608002b36087058c100052f42e80b182000a5d85d0163040015ad02202c608002b56044058c100046f43e40b1820008dd87c81630400153d09902c608002a76132058c100056b40c40b182000ad58188163040011bd0e102c6080023761c2058c100054f42040b182000a9d8408163040015ad02102c608002b56042058c100054f42020b182000a9d84041630400f93cc6ba0c6080022f61e6418c100061f3acc83182000c3d75990630400195ce5320c6080022fe1d6418c100061f3aac83182000c3d75590630400195ce4b20c608003279927318c100064eb24e631820008df8758c630400193ce8b18c608003275d16318c1000667392c631820018ef865c8630400195cc8b90c6080032b5917218c1003e6731ae43182000ccd635c8630400195ce9310c6080032b5d26218c100b43f42ced218200087d859da430400f1bd073b486080063ba0a7690c1000476c14ed218201687c85dd9430402d0fd0b3b286080021f6167650c100046ec1ceca1820018ee829d943040011db053b286080021fe157650c100b43e42aeca18201687e851d943040010fb0a3b286080063ba087650c1000476c10eca18200087d86dd543040c987cc9baa86082271798f7550c1000637316eaa18200087e8759543040010f90eb2a860801e2f21d6450c100061fbaac8a182000c3c7559143040051b90eb1a860800317dd56350c100062e3aac6a182000aad869d1620400195eed3a2c408002abe19745881000657bb2e8b1020008ee87d9162040014dd0bb22c4080029b61764588100056741ec8b102000acd83d91620400155b0d322c4080032bdda64588100071732cc8b102000e2e759916204001c5aeb322c4080032bdd964588100071732ac8b102000e2d655916204001c5ceab22c4080038b5d5645881000477438c8b102000a6e8519162040014db0a322c408002aba1
  | 4 => 0x30400f1bd0f214c6080023761e4298c100052f42c853182000a5d8590a630400199ae5214c608003335c94298c1000747c1285318208ec9f7250a630411dd1ce4a14c608003275c94298c1047746b92853182000c8d7250a6304001c3ea4a14c608003875494298c1003c6f4388531820008dd8710a63040014bd0a214c608002976144298c100052f428833182000a5d85106630400f1bd0f90cc6080023761f2198c100054f426433182000a9d84c86630400199ae510cc60801e37a1c2198c100046ec38433182000a9e84086630400153b0810cc608003335c82198c100056d400433182000ad98008663040014bd0ba04c608002976174098c1003c6f43e4131820008dd87c82630400153d09904c608002a76132098c1000666b96413182000ccd72482630400f1bd0e104c6080023761c2098c100054f420413182000a9d8408263040015ad02104c608002b56042098c100054f426e6b182000a9d84dcd630400159d05b9ac608002b360b7358c100052f42886b182000a5d8510d630400159d0421ac608002b36084358c1000c6e41ee4b1820008f4815c9630400395ce4a12c6080032b5c94258c1000666b9664b1820008de878c9630400153d09192c608002a76123258c1000746a1464b1820018dc874c9630400199ee4992c608003a35093258c100056a40a64b1820008de870c9630400153d08192c608002a76103258c100046f43ec8b182000a5e85d9163040014bb0bb22c608002b3a0b6458c1000566c16c8b182000e1e65991630400153b05322c608003879956458c100070eb2ac8b182000a9f8259163040011bd0e322c60800297a146458c100052ec28c8b182000ace82191630400159b04322c608003279937258c100064eb26e4b1820008df865c9630400193cc8b92c608003275917258c100046f43ec4b182000a9e84d89630400153b09b12c60800237a1e6258c100054f424c4b182000a9d84989630400199ee5312c608003a39926258c1000746b24c4b182000cce879896304001d1d09312c608003a36126258c1003c6f43ac4b182000ccf7258963040011bd0e312c608002a7a106258c100054ec20c4b182000a9f86d09630400153b0da12c60823f27ddb4258c100070f32e84b182000e1d65d096304001d1cc5a12c608003a358b4258c100054fc3284b182000a9d86509630411d93eeca12c608003879954258c100070eb2a84b182000d8d725096304001d1cc4a12c608003a35894258c100052fc2ae8b182000a5c855d163040014bd0a3a2c608002976147458c1000567410e8b182000acd821d16304001c3ea92a2c608003875505458c100046ec3ce4b182000a9e849c9630400153b09392c608002b5e057258c100056a40ae4b182000ccf825c963040019af02b92c608003352057258c100046f438e
  | 5 => 0x8002aea0021590100055cc0042b202000a3e859c1640400147b0b382c8080122fa1f50590100045ec3ea0b202000ab681141640400156b02282c8080122fa1f20590100045ec3e40b202000a3e85c81640400147b0b902c808002a7a0f20590100054ec1e40b202000e8d32c816404001d1a64902c8080022fa1c20590100045ec3840b202000a3e85081640400147b0a102c808002a7a0c20590100054ec1840b202000ab681081640400156b02102c8080028fa1410590100051ec2820b202000c3c54dd9540400117b093b2a80801e37a0e76550100046ec1cecaa020018ee829d954040011db053b2a8080030f151765501003c6f418ecaa020008dd831d954040031dd043b2a8080023b60876550100b45e43ac8aa02016a3c85591540400187ceb326c6080030f5d664d8c1000657394c9b182000c3e75593630400187aeab26c6080032b9c964d8c1000657322e5b182000cad645cb630400195ce9316c6080032b5d262d8c100061f3ace9b182000c3e755d3630400187aeaba6c6080022fe0974d8c100145f426e5b1820008bd84dcb630400195ce9396c6080032b5d272d8c10006573a2e5b182000cad745cb630400195d08b96c6080032b61172d8c1000666c1ae5b1820028bf87d0b630400117b0fa16c60824f0f9d742d8c100061ebae85b182001cae72d0b630400195ae5a16c6080022fe1d42d8c100045ec3a85b182092c3e7550b630400187aeaa16c6080072b9c942d8c1000656b9285b182091c9e74ccb630400193ae9996c608007339cb32d8c1000666b9665b1820018df874cb630412193ce8996c608003275d132d8c1000e6739265b182000ccd724cb6304001d1a84996c608003395ca71d8c1000674b94e1b182000a9e84d8e630400153b09b1cc608002b3a0b6398c1000566c16c73182000a5e85d9263040014bb0bb24c608002b3a0b6498c1000566c16c93182000e1e65992630400153b05324c608003879956498c100070eb2ac93182000a9f8259263040014bd0a324c608002976146498c1000567410c93182000acd82192630400193cc9b94c608003275937298c100064f322e53182000c9d645ca630400153d09b14c608002a76136298c100054f424c53182000a9d8498a630400199ae5314c608003a39926298c1000746b24c53182000ccd8798a6304001d1d09314c608003a36126298c1000666b92c53182000a9e8418a630400153b08314c608002a7e1b4298c100054ec36853182000e1e65d0a6304001c3acba14c608003a398b4298c1000746b16853182000a9f8650a630400153b0ca14c608003879954298c100070eb2a853182000d8d7250a6304001d1cc4a14c608003a35894298c100070faa4a93182000e1d54152630400f99f04b94c60823f27dcb4298c100064eb96853182000e1f52d0a6
  | 6 => 0x61f32ee4b202000c3d65dc9640400117f0cb92c8080030f99572590100045f43ec4b202000a3e85d89640400147b0bb12c808002a7a0f62590100054ec1ec4b2020048be87989640400147d0b312c8080028f61662590100054f41cc4b202000a9d83989640400195ee5312c8080038b996625901000716b2cc4b202000cae879896404001c5d0b312c8080038b61662590100074741cc4b202000e8d83989640400517d0eb12c8080032bdc962590100045f438c4b202000a3e85189640400147b0a312c808002a7a0c62590100054ec18c4b202000a3f86d49640400147b0da92c8082570fddb525901000717316a4b202000e2d62d49640400147f0ca92c8080028f61952590104a61fbb2a4b202000e2e625496404001c5ac4a92c808002a761b325901048e4fbb664b202000e1e65cc96404001c3acb992c808003a398b325901000746b1664b202000a9f864c9640412193eec992c8080038799532590100070eb2a64b202000d8d724c96404001d1cc4992c808003a3589325901000786a9264b202000c3f759d5640400187aea3aac8080028fe1573590100051e42ae6b202000a3e851cd640400147b0a39ac808002aba08735901000556c10e6b202000e1e53d4d640400117d0e29ac8080022f61c535901000557410a6b202000aad8214d640400117b0f392c8080028fa1672590100051ec2ce4b202000a9e839c9640400153b07392c8080032be0972590100045f438e4b202000a3e851c9640400147b0a392c808002a7a0c72590100054ec18e4b202000c3f72d49640400187ae5a92c8080022fa1e52590100045ec3ca4b202000a3d85949640400153d07292c808002a760e525901000717c12a4b202000c3f72549640400187ae4a92c8080022fa1c52590100045ec38a4b202000a3e85149640400153d06292c808002a760c52590100064fb9664b202000c9d72cc96404001c3ea5992c8080038754b32590100045f43c64b2020008bd878c9640400147d0b192c8080028f61632590100054ec1c64b202000cad728c96404001c5aa5192c8080032b5c9325901000716a9264b202000e8f824c9640400193ee4992c808003a39c932590100064eb9264b202000e8d724c9640400191ae4992c80800387d4932590100074729264b202000e1d524c96404001d1aa4992c8080038354932590100045f43864b2020008bd870c9640400147d0a192c8080028f61432590100054f41864b202000a3e851c5640400147b0a38ac8080022fa1c51590100045ec38a2b2020048be87c85640400117b0f90ac8080028fa1721590100051ec2e42b202000a9e83c85640400153b0790ac808003a34ca21590100045f43842b2020008bd87085640400147d0a10ac8080028f61421590100054f41842b202000a9d830856404001d1a6410ac80
  | 7 => 0xdf825cf640400193e84b9ec80805a1fa1772d90100043ec2ee5b2020078de83dcb64040011bb07b96c8080023b61e72d9010006373ace5b202000c6d759cb640400199ce7396c808003335ce72d901000c77c3ae5b202000c6e755cb64040018daeab96c808003339cd72d901000666b9ae5b202000c6e855cb64040018db0ab96c8080032ba1172d901000656c22e5b202000cce835cb640400199b06b96c80805a1fe1f52d90100043ec3ea5b202099c5e73d4b64040018bae7a96c8080071b9cb52d901000636b96a5b20200087f8754b64040010fb0ea96c808263179cd52d90100062eb9aa5b202001c6e7254b64040018dae4a96c8080062fe1d42d90104961f3aa85b202000c3d7550b640411d93ce6a16c808003275cd42d901000e5739285b202000cad7250b640400f1bf0f996c8080023761f32d90104be2f3ae65b202000c5d75ccb640400399ce5996c808003335cb32d90100046fc3a65b2020008dd874cb640412d8bcea996c808003175d532d901000e6739265b202000ccd724cb6404001c9aa4996c808003a350932d90100066ab9ce3b202000ce5729c764040019d2e5386c808002a7a0f65990100054ec1ecb3202000aae82d96640400155b05b2cc808002a7a0c65990100054ec18cb3202000aae82196640400155b0432cc8080030f99572990100051f42ec53202000a3d85d8a640400153d07b14c808002a760f62990100051f42cc53202000a3d8598a640400153d07314c808002a760e629901000656b94c53202000e2e6598a640400195b0f314c8080038ba16629901000716c2cc53202000e8e8398a6404001d1b07314c8080032b5c962990100051f428c53202000a3d8518a640400153d06314c808002a760c62990100055b408c53202000aba8018a640400147f0da94c8080028f61b529901000717316a53202000e2d62d4a640400147f0ca94c8080038b989529901000716b12a53202000a9d86cca6404001c3ccb994c808003a398b329901000746b16653202000a9f864ca6404001c3cca994c808003635c9329901000747312653202000e8d624ca6404001e1aa4994c8080028fa1774590100051ec2ee8b202000a9e83dd1640400153b07ba2c808002aba0b745901000556c16e8b202000c3f75d51640400317909b92c8080032bd0972590100045f43c84b202000a3e85909640400147b0b212c808002a7a0e42590100054ec1c84b2020018bc87509640400195ee4a12c808007339c9325901000666b9264b202000e4d524c96404001d1c84992c808003a350932590100045f43ecab202000a9e83d95640400153b07b2ac808002aba0b655901000556c16cab202000c3f76995640400147b0532ac8080022fa1c65590100054f418cab202000a9d83195640400155d0432ac808002ab60865590100
  | 8 => 0xe9b1462880033918a768c5103bf4a31ce918a2000d35755d231440b5d28c6ba4628801eb5a1b638c5100066b3b6c718a2000e976418e3144001d28c831c6288003b1188638c5100076231ec518a2000cdb631c131440013d304382628801f351db734c51000762310c698a20009e5821c13144001ba6e63826288002f8608704c510004f9430e098a2000cf2861c13144001b650838262880036c610704c510006d9b20e098a2000db0641c13144001ba6c638262880037418c704c510004f9c10e098a2000de2821c131440013e304382628800378608704c510004f0c10e098a2000de3621c13144001bc0c438262880036cd08704c510006d8a10e098a2000dd3321c13144001ba264382628801eb5219310c51038f623126218a2000bd0804c431440310f90cbac80881770f191759011000636312eb202200087f87d9640440710fb0fb2c80880030f9d764901100061ebaec92022000c5e75d8e40440018baebb1c8088003179d463901100062eba8c72022000c6e75d8a40440018daebb1480880032dd90715011003e6a31ce39822007ad4864c730440017a10098e6088003359da318c1100045fc22ec98220028bc845d930440011df04bb260880063b209764c1100045f436e89822000c3c65dd130440a1938c7ba260880032b18b744c11027c5f43ec898220508bc87d91304400187eebb2260880030f1d7644c1100064fba6c69822000c9c74d8d304400195ee9b1260880032b1d3624c11000672316e29822000cd7631c530440019c8c438a608801eb5219314c110005e84026298220028bc849d830440031d9053b060880362f219740c1100061e32ae81822007c9c635d03044001958c4ba060880022fe1f640c11004c5ec3ec81822000c3e75d90304400187aebb2060880032b9cb640c1100064f3a6c61822000c9d74d8c304400199ce5b1860880323b219720c11000657b22e41822000cac645c8304400199ec6b90608801f3318d720c11000477c3ec418220088ed87d88304400195ce9b1060880032b5d3620c1100065bb24e21822000cb4649c430440019aec7388608801f3518e710c11000673b14e21822000ce4629c4304400196ec8b8860880032d191710c1100066bb1ae21822007cd4635c430440019cec4b88608800339189710c110004eac3c621822000cd6768c43044001b8ae518860880272d9db64841100165b3b0c90822000cd676d8e104400f9acec31c2088003b11886384110046733b6c50822000c3e645d7640400193cc939ec8080032799173d901000657322e5b202000c6e7598b64040018daeb316c808003339ce62d901000666b9cc5b20201687f875d764040010ff04baec8080030fd0975d90100062f3ace7b202000c5d759cf640400f1bf0eb9ec808003179d573d90100062ebaae7b2020008
  | 9 => 0x64d891000716328c9b122000e2f751936244001c58ea326c488002b3a1b73d8910006673b6e7b122000d8f74dcf6244001d1ec9b9ec488003a319373d8910006e238ee7b122000ace861cf624400199cec39ec488003a3d9073d891000746320e7b122000cce76d8f6244001d1ec9b1ec488003a319363d891000747ba6c7b122000e8c74d8f62440011db0f31ec488002aba1263d891000556c24c7b122000ace8398f62440011df0eb1ec488002abe1163d891000556422c7b122000ace8618f624400199cec31ec488003a3d9063d891000746320c7b122000e8f7418f6244001d18e831ec488003b160463d891004573436e3b122008aea86dc36244001b96e7b86c48800378dc770d891000717baee9b122000a6e859d362440014db0b3a6c488002aba1274d89100056741ce9b122000acd839d362440014df0aba6c4880029b21574d891000567c1ae9b122000acc835d3624400155d0e3a6c4880032ba1c74d891000717ba8e9b122000e2c751d36244001c5ea92a6c4880038b55054d891000657ba6e7b122000ccf74dcf6244001d1ee9b9ec48800323dd373d891000666ba6e7b122000e8c74dcf624400199ce3b9ec488003331c773d891000666b86e7b122000aae849cf624400155b0939ec488002b3a0e73d891000557c22e7b122000aac845cf624400195ee8b9ec4880e6b9a0473d891000572c08e7b122000ace871cf624400199d0e39ec488003a3dd073d8910007463a0e7b122000ec6811cf6244001d8b0239ec4880029be1543d89100053642a87b1220008ee8710f62440011db0e21ec4880029ba1443d891000536c2887b12202aaea80dc762440014dd0a20ec4880029b61441d891000667b9ee1b12202aae681dc362440014dd0ba06c4880029b61740d89100043f436eaa0a2061c3c64dd541440018d8c5baa82881ee1fa1f655051030c3e43ecaa0a2000c3f75d914144001878ebb22828800317dd763505100062e3aec6a0a2000c5f7518d41440018b8ea31a82880031bdd76250510006363aec4a0a2000cbb641c14144005179093b662880063b20a76cc5100045e432e998a2000c3c655d3314400f938c6ba662880032b18974cc5100045fc3ec998a20008bd87d93314400187cebb2662880030f5d764cc51000657396c998a2000c9e74d8f314400193ae9b1e6288003339cb63cc51000476432e598a2000caf645cb3144001958c8b96628800333d8d72cc51003e6631ae598a20008ef87d8b31440011db0fb1662880032b9d362cc51000656ba6c598a2007cd8639c33144005179093b4628807a2f219748c5100061e32ae918a205ac9c635d23144001958c4ba462880022fe1f648c51004c5ec3ec918a2000c3e75d92314400187aebb246288003279d3638c5100064eba6c718a2000cae74d8a314400195a
  | 10 => 0x31a2000a9c86508634400193ceca10c68800387d954218d100070e32a8431a2000d8d725086344001d1ec4a10c688003a31894218d100074bb22e231a2000e94645c46344001d88c4b88c688002b5a1a2118d10006e2b944231a2000ec4628846344001d88c4908c688003b218a2018d10007e110c4031a2000dc9724806344001d90c4900c688003f04852018d100070faa4a831a2000e1d54150634400f1bf04b90c68801f33e097218d1047e4fb968431a2000c9d72d086344001c3ea5a10c68823fa59c74218d1047f4ab8e8431a20078de8790863440011bb0f210c68800297a164218d100052ec2c8431a208ea9d84908634400199ae5210c688003335c94218d1000747c128431a208ec9f72508634411dd1ce4a10c688003275c94218d1047746b928431a2000c8d725086344001c3ea4a10c688003875494218d104774b38a8431a208ee9571508634400f1bd0e210c6880023761c4218d100052f4288431a2000a5d85108634411f53d08210c68800297a144118d100052ec288231a20078de87c8463440011bb0f908c688002a7a132118d100054ec264231a2000ccd72884634400f1bd0e108c6880023761c2118d100054f4204231a2000a9d84084634400199ae4108c688003b14842118d100056d4004231a2000ad98008463440014bd0ba00c688002976174018d1003c6f43e4031a20008dd87c80634400153d09900c688002a76132018d1000666b964031a2000ccd7248063440015af02900c688002b52052018d1003c6f4384031a20008dd87080634400153d08100c688002a76102018d100056b4084031a2000ad5810806344001d9240100c688002a7e111018d100054e4222031a200087f855da434402d0f90abb4868801e3720d7690d1000477c12ed21a20018ec825da434400196ec938c868801f3518e7190d1003c7a432e321a20009f0805c6434402d0fd0bbb286880021f6177650d1000c77416eca1a20008ed82dd9434402d0fd0b3b286880021f6167650d100043fc2aeca1a201687c855d943440011bf06bb286880023be097650d1000c76412eca1a201687c851d943440010fd0dbaa86881930f1937550d1044e2e31eeaa1a2000c6c62dd543440010fd0fb2a86880021f21f6550d1003c5f43ec8a1a2000c3f75d914344001878ebb22868800a37a1f6350d100062fbaec6a1a2000c5c75d8d434400155d0dba6c4880032b9db74d891000557430e9b122000cae761d3624400195cedb26c4880038bd9764d891000717baec9b122000e2c75d9362440011db0f326c4880029ba1664d891000536c2cc9b122000aae84993624400159d07326c488002b360e64d891000477c3ac9b122000a6f8559362440014d90ab26c488002b3e0d64d89100056641ac9b122000aae86193624400195cec326c4880038bd94
  | 11 => 0x440011bd0f906c6880023761f20d8d100054f42641b1a2000a9d84c83634400199ee5906c68800333dc920d8d100046f43841b1a20008dd87083634400153d08106c688002a761020d8d100056b40841b1a2000ad581083634400f938c6ba4c6880030f9d76498d100061ebaec931a2000cae72d92634400187cea324c6880030f5d46498d1000657390c931a2000c9e74d8e634400193ae9b1cc688003339cb6398d1000657b22e531a2000cac645ca634400199ec6b94c68801f3318d7298d10006573a0c531a2000cad7418a634400117d0fb22c6880030fdd76458d100061e3aec8b1a2000cac72d91634400117d0e322c6880030fdd46458d100061e3a8c8b1a2000cac7219163440031dd0db92c6880032bd937258d1000656326e4b1a2000caf741896344001958e8312c6880030fdd77458d100045ec16e8b1a2000c3f751d16344001878ea3a2c68800327dd37358d100064e3a6e6b1a2000caf74dc96344001958e9b92c68800333dcf7258d1000657c26e4b1a2000cac84dc9634400199f07b92c6880022fe117258d100145e422e4b1a20008df835c963440011ef02b92c6880032bdd07258d10006563a0e4b1a2000ccf731c9634400117d0fa12c68800a2f21f4258d100061fbae84b1a2093c3c75d09634400195ee5a12c6880072b1cb4258d100045f43a84b1a20008bc87509634400187eeaa12c68824b0f1d54258d1000657b9284b1a2001cac7250963440011bd0f992c68800327dd33258d1048e4e3a664b1a2000ccf72cc96344003998e5992c6880063721d3258d100064fba264b1a2090c9c744c9634400199ee4992c688007331c93258d1000746a1264b1a2000ce472dc563440011bf0eb18c688002a7e116318d100054e422c631a2000acf8258c634400159904b18c6880023760a7618d100064f3b6c831a2000e1f65d90634400153b05b20c6880023761e6418d100052f42cc831a2000a5d85990634400159d05320c688002b360a6418d100046fc3ac831a2000a5f8559063440014b90ab20c688002b3e096418d1000566412c831a2000c9e761906344001c3eca320c688003871946418d100054ec10c831a20008de86dc8634400193ec9b90c688003271937218d100064fb22e431a2000c9c645c863440011bf0fb10c688003335cb6218d100046ec3cc431a2000a9e84988634400153b09310c68800237e1d6218d100054fc22c431a2000a9c8458863440011bb0e310c688002a7a106218d100054ec20c431a2000ccd721886344001d1ec8310c688003a31906218d1000666c38c431a2000e8e841886344001d1b08310c688003b16046218d1000764c00c431a2000a9e86d0863440015390da10c688003279db4218d100070fb2e8431a2000e1c65d086344001d1ec5a10c688003a318b4218d100054f43284
  | 12 => 0x2ae2192019110007c4992403222000fa121480644400f1bd07bb2a8880023760f765511000c77416ecaa220008ed82dd95444001878a93b2a8880022fe1176551100046fc1aecaa220078dc835d954440011df04bb2a8880063b20976551100061e2a0ecaa220168be87d91544402d47d0bb22a88800297a1443d8d100052ec2887b1a2000ace8210f634400159b0421ec6880032bdc942d8d1000e5639285b1a2000ccf72ccb634400153d09196c688002a761232d8d1000746a1465b1a20018df874cb634400199ae4996c688003a350932d8d100054f42065b1a2000a9d840cb6344001c3ecbb26c688002a760b64d8d100052f42cc9b1a2000a5d85993634400159d05326c688002b360a64d8d100052fc2ac9b1a2000a5c85593634400159f04b26c688002b320964d8d100070fb28c9b1a2000e1c65193634400153b04326c68800327d9372d8d100064e326e5b1a2000c9f645cb6344001938c8b96c688003335cb62d8d100054f424c5b1a2000a9d8498b634400153f08b16c688002a721162d8d100054f420c5b1a2000a9d8418b634400199ae4316c688003a3d9062d8d1000746320c5b1a2000ccd8718b6344001d1d08316c688003a361062d8d1000762c08c5b1a2000ec98018b634400153d0da16c688002a721b42d8d100070fb2e85b1a2000e1c65d0b6344001d1ec5a16c688003a318b42d8d100054f43285b1a2000a9c8650b6344001c3ecaa16c6880038719542d8d10006c7b9285b1a2000e8f6250b6344001d18c4a16c688003b118a21d8d100076431441b1a2000fc2218836344001b96e4906c688003f048520d8d100052f42ee9b1a2000a5d85dd363440014bd0b3a6c6880029761674d8d1000567414e9b1a2000acd829d36344001c3ea92a6c6880038755054d8d100054f424e5b1a2000a9d849cb634400199f04b96c688002a7a1072d8d100054ec20e5b1a2000ad6811cb63440015ab02396c688002b6a0072d8d100056cc00e5b1a2000c9f72d0b634400193ae5a16c68800387d4b42d8d100046f43c85b1a20008dd8790b63440014bd0b216c6880029761642d8d1000667b9485b1a2000ccf7250b6344001d1f04a16c68800327dc942d8d1000747b9285b1a2000c8f7250b634400193ae4a16c688003a31c942d8d100070fa9285b1a2000e1d5250b63440011bd0e216c6880023761c42d8d100052f42885b1a2000a5d8510b634400153f08b8ec688002a721171d8d1000567c12e3b1a2000acc825c763440014bd0a20ec6880029761441d8d100046f43e43b1a20008dd87c87634400153d0990ec688002a761321d8d100046f43843b1a20008dd87087634400153d0810ec688002a761021d8d100056d40043b1a2000ad980087634400153d09b86c688002a761370d8d100052f42e81b1a2000a5d85d0363
  | 13 => 0x62e3aee6b222000c9f74dcd64440011bb05b9ac88800327d0b73591100062fba8e6b222000c5c751cd644400193ee839ac8880063ba1f725911000637baee4b222000c6c75dc9644400195ee9b92c88800333dcf72591100066639ee4b222000c6f85dc964440018d90bb92c8880032be13725911000656426e4b222000ccf83dc9644400199907b92c8880021fe1572591100b43e42ae4b2220008bf845c964440011bf06b92c88801e3720d725911000477438e4b222000c6f751c964440018d8ea392c8880032bdd0725911000667b98e4b222000ccc731c964440010fd0fa92c88805a1f21f52591100062fb9ea4b222099c5c73d4964440018dee5a92c8880071b1cb52591100043f43aa4b22200087c8754964440018bee6a92c888263171cd525911000637b92a4b222001c6c7254964440031790ea12c8880030fdd542591104961e3aa84b222000c9f73509644411d938e6a12c8880032bdc9425911000e5639284b2220008de87cc9644400f1b90f992c88800317dd732591104be2e3ae64b222000ccf72cc96444003998e5992c88800237a1d32591100046e43a64b222000c5f754c9644412d8b8ea992c88800333dc9325911000e6639264b222000e4d524c96444001d1a84992c8880022f60a76191100061f3b6ca3222000a3d82d94644400187ee5b28c8880022f61e65191100051f42cca3222000a9e83994644400153b07328c888002aba0a651911000556c14ca32220008bf87594644400153f06b28c888002a720d651911000557c12ca3222000aac82594644400187cec328c8880030fd9572191100061e32ae432220008bf87d88644400195ae5b10c8880022f61e62191100051f42cc43222000a3d85988644400153d07310c888002a760e62191100045fc3ac43222000a3f8558864440014790ab10c888002a7e0d62191100054e41ac432220028be87188644400117b0e310c8880028fa1462191100051ec28c43222000a9e83188644400153b06310c8880032b5c8621911000717b28c43222000e2c65188644400195b0e310c8880038ba14621911000716c28c43222000e8e831886444001d1b06310c888003a9604621911000754c00c43222000a3e86d4864440014790da90c8880030f9db521911000717b16a43222000e2c62d48644400147d0ca90c8880028f21952191100061f3b2a43222000e2f625486444001c58c4a90c888002a7a1b32191100064f3b6643222000e1f65cc86444001c38cb990c888003a3d8b321911000746316643222000a9c864c8644400193cec990c88800387d9532191100070e32a643222000d8d724c86444001d1ec4990c888003a3189321911000786a92643222000ea4628846444001f0a65108c888002ad219211911000752312423222000ea8628806444001f4443100c888
  | 14 => 0xc864cb644412193cec996c88800387d9532d9110006c7b9265b222000e8f624cb6444001d18c4996c888003c354932d91100075231443b222000f85328876444001d50c5106c888003e888620d9110007c499241b222000fa121483644400187eeb3aec8880030f5d475d91100051f42ee7b222000a3d85dcf644400147d0b39ec8880028f61673d911000557414e7b222000aad829cf644400156b0239ec8880038794f53d91100045f438a7b2220008bd8714f644400155d0429ec888002ab60853d91100051f42ce5b222000a3d859cb644400153d07396c888002a760e72d911000657c12e5b222000a3e851cb644400147b0a396c888002a7a0c72d91100054ec18e5b222000ab6811cb644400156b02396c888002aea0072d91100055cc00e5b222000c3f72d4b644400187ae5a96c8880022fa1e52d91100045ec3ca5b222000a9e8394b644400153b07296c8880038be0952d91100061fb92a5b222000c3d7254b644400117d0e296c8880022f61c52d91100054f418a5b222000a9d8314b644400193ee5996c888003275cb32d91100070fa9665b222000e1d52ccb644400117d0f196c8880022f61e32d91100051f42c65b222000a3d858cb644400195ee5196c8880038b54a32d911000657b9265b222000e2d524cb6444001d1f04996c88800327dc932d911000747b9265b222000c8f724cb644400193ae4996c888003a31c932d91100070fa9265b222000e8e524cb6444001c3aa4996c888003a354932d911000706a9265b2220008be870cb644400117b0e196c8880028fa1432d91100051ec2865b222000a3e85dc7644400147b0bb8ec8880022fa1c51d911004c5ec38a3b2220008be87c87644400117b0f90ec8880028fa1721d91100051ec2e43b222000a9e83c87644400153b0790ec888003a34ca21d91100045f43843b2220098bd87087644400147d0a10ec8880028f61421d91100054f41843b222000a9d830876444001d1a6410ec888002aea0021d91100055cc0043b222000a3f855c364440014790ab86c8880022fa1f50d91100045ec3ea1b2220008be87c83644400117b0f906c8880028fa1720d91100051ec2e41b222000a9e83c83644400153b07906c888003a34cb20d91100074699241b2220008be87083644401317b0e106c8880028fa1420d91100051ec2841b222000a9e83083644400153b06106c888002ada0420d91100055ac0841b222000c3c64dd564440018d8e5b2ac88800317d9773591100064e326e6b222000c5f651cd6444001938c839ac8880031bd97725911000656326e4b222000c6f7518964440018d8ea312c88800333dcc625911000666398c4b22201687e87dd564440010fb05baac8880030fd0b75591100061fbaee8b222000c3c75dd1644400f1bd0fb9ac88800317dd7735911000
  | 15 => 0xaa16c9080030f5d542d921000656b9285b242097c5e75ccb64840018baeb996c90825b179d532d92100062ebaa65b242001cce724cb648400199ae4996c9080039354932d921000746a1265b242000a3e85dd1648400187eebaa2c9080062f21d425921000657b9284b242001cce724c9648400199ae4992c90800393549325921000746a1264b242000c3c54dd9548400117b093b2a9080030f15176552100046fc1aecaa420078dc835d9548402d17d0fb22a90805a8fa17645521000c6fc3a65b1c2001cce724cb638400199ae4996c708003a350932d8e100056a40a65b1c2000cf1719c3638400517d0fba2c7080030fdd77458e100045ec16e8b1c2000c3f751d16384001878ea3a2c7080022fe117258e100145e422e4b1c20008be87d0963840051790fa12c7080030fdd74258e1049e1e3ae84b1c20008be8750963840011790ea12c7080030fdd54258e104961e3aa84b1c2000c9f74cc96384123938e9992c7080063721d3258e100064fba264b1c2090c9c744c9638400199ee4992c708003a35093258e100046fc3ac631c2007cce635c8638400199ac6b90c7080021fe157690e100b43e42aed21c2028a3e85d92438402d0fd0b3b287080021f6167650e100043fc2aeca1c201687c855d9438400117f08bb2870801e2f21d6450e100061e3aac8a1c2007a9c83591438404947d0bb2483080030f1d5645061003e6731ae598c2000ccd635cb31840013d30438263080023761f630c6100061f3aac92042015a3e85d9140840011bf0eb18610801f3398d720c21000666b1ae41842007cd6635c430840019aac6b886108002b5e0d76c421000573c12ed88420009eb825db108400187aebaa6c8880032bd0b72d91100051f42c85b222000a3d8590b644400153d07216c888002a760e42d911000c5fc3a85b222000cad7250b644400199ee4996c888007331c932d911000726a9265b222000e8e424cb6444001d1a84996c888002a7a0e65d91100054ec1ccbb222000aae82997644400155b0532ec8880030fd9572d911000656b96c5b222000a3e8598b644400147b0b316c888002a7a0e62d91100054ec1cc5b222000a3f8558b64440014790ab16c888002a7e0d62d91100054e41ac5b2220098bd8718b644400147d0a316c8880028f61462d91100054f418c5b222000a9d8318b644400195ae4316c8880038bd9462d911000656c38c5b222000e2e8518b6444001c5b0a316c888003a3a0c62d911000746c18c5b222000ea58118b6444001d5300316c8880028fa1b52d91104ae1f3b6a5b222000e2f62d4b6444001c58c5a96c8880028fa1952d91100051e432a5b222094c3e7654b6444001c5ec4a96c8880038b18952d91100054f43665b222091c9e76ccb6444001c3ecb996c888003a3d8b32d91100074631665b222000a9
  | 16 => 0x19003003e6b39ac32006000cd573586400c00193f09bb2601800327213764c0300046fc16ec98060008dd82dd9300c00193e85bb260180032750b764c0300064fbb6e89806000c9f761d1300c001a38ea3a2601800333a1d624c03022666c3ac49806000e8e84589300c001d1b08b126018003a3dd1624c030007463a2c49806007ccf70589300c00fd96e0b12601800333588714c0300066a38ac29806000cd487585300c001d2ee8b0a6018003a51d1614c0300066bb92c29806000cd572585300c001d2e84b0a6018003a5509614c03003f69b82c29806000c3d75d5364c400317f0ea16c9880032b5c942d931000667b9265b262001ccc724cb64c4001c9aa4996c988003a350932d93100b43f43eeab26200087d82dd564c400187e85baac9880030f1d774593100043fc2ae4b26201687c855c964c40010fd0fa92c98805a1f21f52593100043f43aa4b26200087c8754964c40031790ea12c9880030fdd542593104961e3aa84b262000caf7250964c40018beeb992c98825f171d732593100062fbaa64b262096c5c754c964c400199ee4992c988007331c9325931000726a9264b262000e8d424c964c4001878a93b2a98801e37a0e76553100046ec1cecaa620008bf845d954c4001878a83b2a98805a2f21d64553100b51e42ac8aa62000c3e759d363c400187ceaba6c7880030f5d574d8f100045fc12e9b1e20028be84dcb63c400117b09b96c78800a2fe1f42d8f100045ec3e85b1e2093c3e75d0b63c400187aeba16c7880022fe1d42d8f100045ec3a85b1e2092c3e7550b63c400187aeaa16c788247279d332d8f100064eba665b1e20018df874cb63c412193ce8996c788003275d132d8f1000666b9265b1e2000e8d424cb63c40019e4e2b86c78800333d8d7298f1003e6631ae531e20018dc874c963c400199ee4992c788007331c93258f1000746a1264b1e20008df8758c63c402d0fd0b3b487880021f6167690f101451e42ac921e20078f5869c643c402d0fd0b3b287880021f6167650f100043fc2aeca1e201687c855d943c400f17d0fb2287880030f1d76450f1003d4f41ec8a1e2024a3c8559241c4001878ebb22838800333d8d72cc71003e6631ae598e2077cb5769d231c40b596aecba463880034d5d5748c710005e2c14c718e20009e582dd931c40017a301b1a638800275a1c634c710004f2c10e098e20008df8758c31c4001ba262b8063880030f9d764903100ad1e42ac8a0620008dd87d8c30c400199ec6b90618801f3318d720c3100066bb1ae21862007cd4635c430c40013ab0f1886188003715ca310c3100b43fc3aebb24200087f825d7648400187e84baec90805a1fa1772d92100043ec2ee5b24201687f87d4b64840010fb0fa96c9080021fe1d52d92100043ec3aa5b2420018bf8750b648412587ce
  | 17 => 0x86000ad783551610c00f5a906aa2c2180038d550545843003d6a41ee4b086000ab6849c9610c00156b09392c21801eb5a0e72584300056ac1ce4b086000ad7835c9610c00f5a906b92c218002ada1072584300055ac20e4b086007ad6831c9610c0015ab06392c218002bca00725843000578c00e4b086000e3752d09610c11fd2e65a12c21823fa5cc342584300053b42c84b086000a7585909610c11d56b09212c21801eb5a0e42584300056ac1c84b086000ea782509610c001c6ea4a12c2180038d54942584304774b99284b08608eea632509610c11dd4a64a12c21823ba5cc142584300053b42884b086000a7585109610c11f56d08212c21801eb5a0c42584300056ac1884b086000ad4874c9610c00f5af04992c21801fb1e09325843000763b9264b086000ec4724c9610c001d2e84992c218003b190932584300074aa1264b086000ec5424c9610c001d0a84992c218002b5e0132584300055b420e0b086000ab5841c1610c0015cd04382c218002b960870584300053b42e80b086000a7585d01610c00f5ad06202c218002b560c40584300055b42640b086000ab584c81610c00f5ad07902c218002b560f20584300076299640b086007ad683881610c0015ab07102c21801eb5a0d20584300076299240b0860008f687081610c0011eb0e102c218002ada1020584300055ac2040b086007ad683081610c0015ab06102c218003b8480205843003c7ac3cc3208601687c85dd9410c00f17909bb282180021fe1576504300b43e42aeca08600087d86dd5410c0c387cc9baa82180031b98b75504300043f43acaa08600087c87595410c00187eeab2282180030f1d564504300064eb26e6a086000c6f75589410c0018d8eab12821800333dcd625043003e6639ac4a086000c7775985410c0018e8eb30a821801e3d21d61504300063bbaac2a086000c7475585410c0019aee6b0a821801f351cd615043003e6b38aed1886000c9e845da310c00193b08bb4621800237e09768c4300046ec12ed1886000c9f425da310c00193a84bb4621801f35a05768c43003e6ac0aed1886000c9d769d2310c001a3ceb3a46218003275d9748c4302466743ac51886000ccd8758a310c001d1d08b146218003a3611628c430007473a2c51886000e8d7458a310c00f99ce2b14621801fb19c5628c4300074b3a2c31886000e9574586310c0019aee4b0c6218003355c9618c4300074ba12c31886000e9542586310c00199ac4b84621800335585708c4300043fc32eb200605dc3e645d6400c0018dcc4bac80181961fe1d65900302ec3ec3acb2006000c3e75592400c00187aeab248018003275917390030006373aac52006000c6d7558a400c00f99ce6b148018003335cd62900300063b3acc32006000c7575986400c0018eceab0c80180031d5d56
  | 18 => 0xc11f55d083a2c41801eb3a0c745883006566c18e8b106000e2f54951620c00159f06aa2c41801eb320d545883000716aa0a8b106000aae84dc5620c00155b09b8ac41801eb3a0f715883006566c1ee2b106007acc839c5620c09159f06b8ac41801eb320d715883000557420e2b106000aad841c5620c00f59d0638ac418032b360c715883000666b98e2b106000aea801c5620c0195d30038ac41801eb3a0f415883000566c1e82b106000a6e85105620c0014db0a20ac418112b360e70588300053742e80b106000a6d85d01620c00f59d06202c418002b360c40588300043fc2ae9308601687c855d2610c00199ee4994c218007331c9329843000746a12653086000a7685106610c0014eb0a20cc218002ada1321984300055ac26433086007ad683c86610c0031eb0f10cc218003b14ca219843003c7ac38433086000ab684086610c00156b0810cc21801eb5a0c219843000762990433086000a77855d2610c0014e90aba4c2180029da1474984300053ac28e93086000e3754952610c001c6aa82a4c218002ada1272984300055ac24e53086007ad6839ca610c0015ab07394c218002ada1072984300055ac20e53086007ad6831ca610c0015ab06394c218002bca00729843000578c00e53086000e3752d0a610c11fd2e65a14c2180029da1642984300053ac2c85308608eab58490a610c00f5ad07214c218002b560e429843000753c12853086000e375250a610c001c6aa4a14c21823ba5cc942984304775319285308608eea53250a610c0014ed0a214c2180029d614429843047d5b420853086007ad68310a610c0015ab06214c21801eb5e09329843003f63c12653086000ec7724ca610c001d88e4994c218003a5d09329843000763212653086000e95424ca610c001d8a84994c218003a150932984300055b420e13086000ab5841c2610c0015cd04384c218002b960870984300053b42e813086000a7585d02610c00156d09904c218002ad613209843003d6b41e413086000ad583c82610c001d8a65904c218003b14c920984300047b4384130860008f587082610c00156d08104c218002ad610209843003d6b418413086000ad583082610c00f1b906b92c21823fa50c742584304774a18a84b086000ccf724c9610c003998e4992c218003a350932584300056a40a64b086007ad683d05610c0014ed0a20ac2180029d614415843003c7b43e42b086000ab684c85610c00156b0990ac21801eb5a0f215843003d6a41c42b086000ec532885610c0031e90e90ac21801eb520d21584300055b42042b086000ab584085610c00f5ad0610ac218003b14c821584300057940042b086007ad6839d1610c0015ab073a2c2180029de1574584300053a42ae8b086007ad4835d1610c0014ed0a3a2c2180029d61474584300071baa4a8b
  | 19 => 0x3355c4618c13003c5f43ea8b206000c3f75d51640c00195e84b92c81801e2fa1e42590300051f42c84b206000a3d85909640c00f53d07212c8180062f21d425903000657b9284b206001cce724c9640c001c9aa4992c818003a3909325903000746a1264b20601687e851c5640c0010fb0a38ac8180030fdd6755903003d4e41aeab206000c3d751d5640c11f93e65b92c81823a2f61e72590300051f42ce4b206000a3d859c9640c00f53d07392c818002a760e725903000657c12e4b20608ec9f325c9640c11f17d0e392c8180028fa1472590300051ec28e4b206007a9e831c9640c01b53b06392c8180030fdcb52590300061eb96a4b206099e1f32d49640c00117d0f292c8180022f61e52590304c51ec2ca4b206007a9e83949640c00153b07292c8180038be0952590300061fb92a4b206000c3d72549640c131c3e64a92c8182638b8c952590304c716992a4b2060008be87149640c00117b0e292c8182668fa14525903003d4f418a4b206000a9d83149640c00f53f04992c81801fa3e0932590300064fb9264b206000e8e724c9640c00193ae4992c818003a35c932590300070fa9264b206000e8e524c9640c001c3aa4992c818003a3549325903000706a9264b206000a3f855c5640c0014790ab8ac81801ea720d71590300051f428e2b206000a3d851c5640c00f53d07a8ac818002a760f51590300045f438a2b2060008bd87145640c00117d0f90ac8180022f61f21590300051f42e42b206000a3d85c85640c00f53d0790ac818002a760f21590300074699442b2060008be87085640c00117b0e10ac8180028fa1421590300051ec2842b206007a9e83085640c00153b0610ac818003a34c821590300055d40042b206000ab980085640c00147d0b382c8180028f616705903006c5f43ea0b2060008bd87d41640c00f53d06282c818002a760c505903006c5f43e40b2060008bd87c81640c00147d0b902c8180028f617205903003d4f41e40b206000a9d83c81640c001d1a65902c818003a34c920590300045f43840b2060008bd87081640c00147d0a102c8180028f614205903003d4f41840b206000a9d83081640c00156d02102c818002ad60420590300061e2a6ecaa06000c3c545d9540c00f1b906bb2a81801e2f21d64550300b51e42ac8aa06000c9d64dcd540c0014dd0bba2c4180029b617745883003d6741ee8b10600cacd83dd1620c00199ae7ba2c41823aab61e7458830007173ace8b10608fe8e739d1620c001d1ae73a2c41823fa30c6745883047f47984e8b106000ccd735d1620c00195f0eba2c4180038b9d5745883000716baae8b10608ecaf735d1620c11dd1ce6ba2c41823b2b5cd745883000746b9ae8b106000c8d735d1620c11dd1862ba2c41823ba3cc1745883000537428e8b106000a6d851d1620
  | 20 => 0x1f42cca32260008bf87594644c00187cec328c8980030fd9572191300061e32ae432260008bf87d88644c00195ae5b10c8980022f61e62191300051f42cc43226000a3d85988644c00153b07310c8980022fe1d62191300051fc2ac43226000a3c85588644c00156f02b10c898002ad20562191300145f438c432260008bd87188644c00147d0a310c8980028f614621913027d4f418c43226000cad72188644c00147d0da90c8980028f21b52191300061f3b6a43226000a3e86548644c0014790ca90c8980030f9d9521913000696b92a43226050c9e76cc8644c001c3ecb990c8980038719732191300054e432643226000c9e764c8644c001c3eca990c898003871953219130006c6b92643226000e8f624c8644c001e1aa4990c8980030f15276551300045fc22ecaa260008df835d9544c001878a83b2a89805a2fa1f64551300b51f42ec8aa2600087e86dd5434c0c9878c9baa869821a1fa1f6550d303243e43ecaa1a6000c3f75d91434c001878ebb2286980032ed907050d3000e6739265b0a6000ccd724cb614c001d1a84996c298002b560c21d85300076299043b0a6000af180087614c00187cebb24c2980030f5d764985300061f3a8c930a6000c3d75192614c00117d0fb22c2980030fdd764585300061e3aec8b0a6000cac72d91614c00117d0e322c2980030fdd464585300061e3a8c8b0a6000cac72191614c00195ec9b92c2980032b19372585300047bc3ac230a6000ae482584614c0010ff0aba0c29805a1f215741853000e573928430a6000cad72508614c00199ae5990c298002b5607321853000667b926430a6000e8d424c8614c0015af02990c298002b560f2118530007629904230a6000af180084614c0010ff0abb4829805a1f21576905302864f39ec920a6000c5c655ce414c02d0fd0bbb282980021f61776505300b43f42ceca0a600087d859d9414c02d0f90a3b282980021fa1b755053030e1e326eaa0a600087e87d95414c0010f90fb2a82980030fdd764505300061e3aec8a0a6000c9f849db314c001939093b6629800237e0a76cc5300046ec14ed98a6000c9f429db314c00193a853b66298003279db64cc5300064f3b0c998a6000e1c65193314c00199d0cb9662981373361972cc530006c7422e598a6000d8d845cb314c001b1ec8b9662980036319172cc53003e67b02e598a6007dcb605cb314c00199ae430e62980022f219748c5300061e32ae918a60008bd87d92314c00187cebb2462980030f5d7648c5300070e328c898a60009cd821c1314c0310f90cbac80981770f19175901300043fc3ecb202604a87d87d96404c00187cebb2480980030f5d764901302864e39ec8a026000c5c65dcd404c0a193cedb24609800b279d8648c1300070e328c918260009cf825c6304c00f1bb0e30c60980
  | 21 => 0x76d4b644c00147d0ca96c8980028f21952d91304a61f3b2a5b226000e1f65ccb644c12193cec996c89800387d9532d9130006c7b9265b226000e8f624cb644c001d18c4996c898003c354932d91300061fbacebb226000c3d751d7644c00147d0bb9ec8980028f61773d91302870f29ea7b226000a3e859cb644c00147b0b396c898142a7a0e72d91300054ec1ce5b226000caf825cb644c00147d0a396c8980028f61472d91302854f418e5b226000a9d831cb644c00187ee5a96c8980030f5cb52d91300045f43ca5b2260008bd8794b644c0a153d07296c898002a760e52d913000717c12a5b226000c3f7254b644c00187ae4a96c8980022fa1c52d91300045ec38a5b226050a9e8314b644c00153b06296c89800327dcb32d91300064eb9665b226000e1f52ccb644c001c3aa5996c8980022fa1e32d91300045ec3c65b226000a3e858cb644c00147b0b196c8980032bdca32d913000716a9465b226000caf724cb644c001c5aa4996c898143a30c932d913028747c1265b226000c9f724cb644c001d1ee4996c89800323dc932d91300064eb9265b226000e8c724cb644c001c3ea4996c898003a394932d91300070ea9265b226000e8d524cb644c001c1aa4996c8980028fa1771d91300051ec2ee3b226000a3e859c7644c00147b0b38ec898002a760c71d91300045f438a3b2260008bd87147644c00117d0f90ec8980022f61f21d91300051f42e43b226000a3d85c87644c0a153d0790ec898002a760f21d91300074699443b2260008be87087644c00117b0e10ec8980028fa1421d91300051ec2843b226050a9e83087644c00153b0610ec898003a34c821d91300055d40043b226000ab980087644c00147f0ab86c8980028f21570d91302845f43ea1b2260008bd87d43644c001c74a1a86c8981422fa1f20d91300045ec3e41b226000a3e85c83644c00147b0b906c898142a7a0f20d91300054ec1e41b226000e8d32c83644c001d1a64906c8980022fa1c20d91300845ec3841b226000a3e85083644c00147b0a106c898142a7a0c20d91300054ec1841b226000ab681083644c00156b02106c8980030f19375591300b43f43eeab22600087d82dd5644c00187e85baac8980030fdd774591300061e3aee8b226000c5c75dcd644c0010ff0ab92c89805a1f21572591300045fc22e4b2260008f7815c9644c0011e902b92c8980021fa1f52591300b43e43ea4b22600087e87549644c0010f90ea92c8980062f21d42591300061fbaa84b226092c3c75509644c00195ee4a12c89800317dd732591304be2e3ae64b2260018dc874c9644c0018beea992c89825b171d5325913000667b9264b226000e4d524c9644c001d1a84992c8980022f60a76191300061f3b6ca3226000a3d82d94644c00187ee5b28c8980022f61e6519130005
  | 22 => 0x994c39800333dc9325873000e6639264b0e6000e8d424c961cc02d0fd0bbb483980021f61776907301251e42ac920e6007c9e7359241cc0010ff0abb2839805a1f2157650730004e6c10e098e6015a3c8559140cc00f938e6b22819805a1fe1d75d92300043fc12ebb246000c3f425d7648c02d0fd0bb96c9180021f61772d92300b43fc3ea5b24600087d87d4b648c0010ff0ea96c9180021f61d52d923000c5fc3a85b246092c3e7550b648c00187aeaa16c9180032b5c942d92304be2f3ae65b246000c5d75ccb648c0031bf0e996c91825b179d532d92300062ebaa65b246001cce724cb648c00199ae4996c9180039354932d923000746a1265b246000a3e85dd1648c00187eebaa2c9180062f21d425923000657b9284b246001cce724c9648c00199ae4992c91800393549325923000746a1264b24601687e851c5648c0010fb0a38ac9180030f15376552300045ec24ecaa46000c3c545d9548c02d17d0fb22a91805a8fa1764552300061e3aac8a1c600087f855d2618c02d0f90aba4c31800333dc9329863000e663926530c6000e8d424ca618c0031eb0f10cc318003b14ca21986300061fbaee8b0c60008bd82dd1618c00187eea3a2c3180030f1d4745863000657ba6e4b0c6000cac74dc9618c00195f09b92c3180032b213725863000667c1ee4b0c6000ccc83dc9618c00117f08b92c31800a2f211725863000657ba0e4b0c6000cac741c9618c00117d0fa12c31800a2f21f42586300061fbae84b0c6093c3c75d09618c00195ee5a12c3180072b1cb42586300045f43a84b0c60008bc87509618c00187eeaa12c31824b0f1d5425863000657b9284b0c6001cac72509618c00193ee9992c318247271d3325863000667b9664b0c6000c9f744c9618c121938e8992c31800333dc9325863000e6639264b0c6000e8d424c9618c0039c8e510ac318003b14ca215863000c7a43a42b0c60008f787584618c0019cae4b08c3180021fe1576906300b43e42aed20c6024a3e85d92418c0010ff0abb2831805a1f215765063000477c12eca0c60018ec825d9418c001878eab228318003479d6748c63000567c12c318c6000d59755c2318c00159f04b0863180030f9d5649023003c5f43ec8a046015a3e85d91408c00159f04b0e6118003359c561cc2300061ebaea9b226000a3e8590b644c00147b0b216c898002a760e42d913000c5fc3a85b226000cad7250b644c00199ee4996c8980039354932d91300074721265b226000e8d424cb644c02d0fd0b38ec8980021f61671d91300061fb2ae5b226000cad72d8b644c00147d0b316c8980028f61662d91300051fc2ac5b226000a3c8558b644c00156f02b16c898002ad20562d91300845ec38c5b226000a3e8518b644c00147b0a316c8980032b5c862d91300051f436a5b226095c3e
  | 23 => 0x50d400ae1e3aecaa1a80078bc87595435002b878eab2a86a001ea720d6550d4003d4f436c6a1a8000d1c75d8d4350001a38ea31a86a0002e36086350d400045f436e2a1a8000d3875dc1435002317d0c38286a00021fe1573d85400b43e42ae7b0a8001cce724cb615000199ae4996c2a00039354932d854000746a1265b0a80008f7875846150001878a8ba8c2a005a1fe1d75185400061fc22ea30a8000c3c845d4615000187e86ba8c2a00021fe0975185400061fa12ea30a8000c3f415d4615000187880ba8c2a00022f61f54185400061ebaea830a80778bf8750c61500014790aa18c2a00030f5d543185400b43f42ee430a800087d85dc8615000195e84b90c2a005a1fe1f52185400043ec3ea430a800087f8754861500010fb0ea90c2a024b0f9d542185400061ebaa8430a8097c5e75cc861500018baeb990c2a025b179d532185400062ebaa6430a8001cce724c8615000199ae4990c2a000393549321854000746a126430a8000c3f655d25150005179083b2a2a00030fd5076545403dc9f43eeaa0a80008be87d95415002b878ebb2a82a00570f1d565505402d54e41acaa0a80008be86dcd41500b5938c7b9a82a002e2fa1c61505400051ec28c2a0a8000c3c751854150001a70ebb8282a002a2fa18705054003c5e424ed98a801687e851da31500010fb0a3b462a000a2fa10768c5402d64e31ae918a8000c5e75d8e315002d0fd0a3b262a00021f614764c5400ac9e42ae898a800087f855d8315002d0f90abb062a00564f215740c54003e4e31ae818a80078f8865c0315000187ecbba2a0a005b0f9da759014032c9fc3aeb202805dc3e765d6405000517b0fb2c80a00570f9d765901400b45fc3acb2028015c3e7559640500a153906b2c80a000a2f21973901402864e31ae720280028bd87186405000147b0a30c80a00030f9d461901400065ab88c3202801687e87dd564cc0010fb05baac9980030fd0b755933044e2f996eab266087c3f741d564cc0010ff0ab92c99805a1f21572593300043f43ea4b26601687c87d4964cc0010fd0ea92c9980021f21d525933000c5e43a84b266000c3f7550964cc125878eaa12c9980032bdc942593300062fbaa64b266096c5c754c964cc00199ee4992c99800393549325933000746a1264b26608c8bf845d954cc00f1790eb22a99805a8f21564553300061f3ace930e6077c9e739d261cc00517f0eba4c3980030f9d574987300061ebaae930e605ac9e735d261cc00117f04ba4c39816b27cc974987300145f426e530e60008bd84dca61cc00f1bd07b94c39800a2fe1f42987300045ec3e8530e6093c3e75d0a61cc00187aeba14c3980022fe1d42987300045ec3a8530e6092c3e7550a61cc00187aeaa14c398243279d132987300064eba26530e6000ccd724ca61cc001d1a84
  | 24 => 0xc800293c87551519002d47f0caa2a3200030fdd954546401261f32eeb20c805099e83dd6419000117f0cbac83200930f995759064032d1fc32cb20c80008bf8758e41900a193ce6b1c83200038d99661906400545fc3ac320c8000e3565586419001717f0cb8483200024fe1570906400061f32ae120c801687e859db31900010fb0b3b6632005a1fa1576cc6400043fc32eb98c800087f8759731900010fb0eb2e63201770f9d165cc64000637392cb98c8000c3e655d3319000187acaba66320003275d163cc6400063732ae598c8000c6d655cb319000f99cc6b9663200033358d72cc6400b43f42eed18c800087d85dda319002d0fd0b3b463200021f616768c6400b43f42aed18c800087f865d631900010ff0eb2c63200021f61d658c6402ee1f3a2cb18c8000c3e655d2319000187acaba463200032d5d1618c6400b43f428ec98c800087d851d931900031dd043b263200023b608764c6400061f32ee898c801687e859d831900010fb0b3b0632001e3e61a700c6400063cb2ce018c8000c79655c0319000537108b8063200570f99574942400061eb2ae92848016a3f86552509000587aecaa4a120002cee0154942400045ec26e5b2a8000c3f54dcb655000187ea8b96caa00061fe1d52d95400051fc22a5b2a8015c3d7454b65500018dae4a96caa00022f61d42d95400ad1f42a85b2a809ec9d74ccb655013dc3ea9996caa0277275d132d95404ef0faa265b2a8001cce724cb655000199ae4996caa00039354932d954000746a1265b2a80028be849c765500018b8ca39acaa0003471507359540004e6c10e6b2a805da3e85dd16550001c38a9b9acaa00023760b73595400064fa16e6b2a8000c9f741cd6550001c38a839acaa0002b360873595400061e2a6e4b2a8000c3c545c965500011bf06b92caa001e3720d72595400047bc0ae4b2a80008f4815c965500031790ea12caa00568f21542595400064fb9a84b2a808ec9c73509655000195ee4a12caa000237a1f325954003c6e43e64b2a809ce1c54cc965500011bd0e992caa00023721d32595404df0e2a264b2a8001cce724c9655000199ae4992caa0003a350932595400061e2a0e2b2a809ae3854dc165500018baeba9ec6a0002a761053d8d4000566c10a7b1a8000caf7250b63500031bf0e996c6a0007339c932d8d4000666b9265b1a8000e4d524cb6350001d1a84996c6a00021fe1571d8d400b43e42ae3b1a80008ef825c763500031d904b8ec6a01430fd917518d400046fc3ac631a8000a5c8558c63500a195ec8b90c6a001f3398d7218d4000666b1ae431a8000a5d83d96535000187ecaba4a6a000a2f2107654d400061faa0eca9a808693e87dd54350113878edbaa86a02278718f7550d4043e1fbb0eaa1a8087c3c761d5435010fc38c63aa86a021e2fa1f65
  | 25 => 0x1c9ce4992cb20003175c9325964000726b9264b2c8000c4d724c96590137c3e84992cb2026f9390932596400070ea1264b2c809be4d424c96590001c1a84992cb200021fa1c32596400043ec3864b2c805da3e840c9659000147b08192cb200028fe1171596402ed1f420e2b2c8000a3d841c565900010fd0f90acb200021f61f21596402ed1f42642b2c8000a3d84c8565900014bd0790acb200029760f21596400072699442b2c800087e8708565900010fb0e10acb201768fa1021596400051ec2042b2c8000a5e8308565900014bb0610acb20003934c821596400053d40042b2c8000a798008565900310fd0f902cb200021f61f20596402ed1f42640b2c8000a3d84c8165900014bd07902cb200029760f20596400072699640b2c8000e4d3248165900010fd0e102cb201761f61c20596402ed1f42040b2c8000a3d8408165900014bd06102cb200029760c20596400053b40840b2c8000a7581081659002d47f0cb2aa9200630fdd965552400045ec30e2aa4808bc3e651c554900bb17b0db82a9201970f997705524032e9dbaee0aa48065c3c74995639013f1790eaa2c72005b0f9d55458e4000656b9284b1c80018dc874c9639000199ee4992c720003935493258e4000746a1264b1c801687e85dc563900010fb0bb8ac7200021f61e6518e4000637394ca31c800087f8759463900018dce4b28c72000237e1d6318e400063732ae431c8000c6d655c8639000f99cc6b90c7200033358d7218e400063b32ce231c8000c75659c463900018eccab88c7200031d5957118e4003e6b31ae231c8000cd5635c4639000187ca8bb4a72000297e0d6594e402ee1e3a2caa9c8028c3e65dd1539000187acbba2a72000a4f21d5454e400b51fc32a8a9c8000c3f76551539000117f0cbac87200a30f9957590e400061fbb4cb21c8000e1e6399643900cb47f0cb2c8720003875956390e400045ec34e321c800093d859c6439000187ccb38c872013e2fe197090e400049fc2ae121c8000c3e655c2439000199ee4994c320007331c9329864000726a926530c8000e8d424ca61900031eb0f10cc320003b14ca219864032e1e3a4cab0c808b8bc87551619002d87ceaaa2c32005a1fa1773586400043ec2ee6b0c80008be8790d619000156d0321ac3200032bd0b725864000637b92a4b0c8001c6c72549619000199ee4992c320007331c9325864000726a9264b0c8000e8d424c96190001d8a6510ac3200063d21d21586400043ec3cca30c8000c6e7299461900010ff0eb28c3200031b9c965186400062f32ce630c8000c5d659cc61900018bccab98c3200031759573186400063732ae430c8000c6d655c861900011ef0eb08c320003355cd611864000672b92c230c8000c3e545da51900bb878e8b2aa3200930f99774546400061eb2ee8a8
  | 26 => 0x393549325903100746a1264b20628c8bf845d9540c40f1790eb22a81885a8f21564550311251e42ac92086207c9e73592410c40193d09bb2621880327613764c4310046fc16ec98862008dd82dd9310c40193e85bb262188032750b764c431004e6c10e09886201cce724ca600c40199ae4994c018803a3509329803100c7cc3c413006200ec932482600c40517d0fba2c0188030fdd774580312864e39ee8b0062008bd82dd1600c4a193e65ba2c0188030fdd474580310061e3a8e8b00624fc9c731d1600c40117f08b92c01880a2f21172580310045f43e84b0062028bc87d09600c40187eeba12c018a4f0f1d742580310045f43a84b0062008bc87509600c40187eeaa12c018a4b0f1d542580310064fba264b006290c9c744c9600c40199ee4992c018803a350932580310056c40262b0062018f887481600c401d9264902c0188062fe1d42d964000656b9285b2c8001cce724cb659000199ae4996cb20003a350932d96400ae1eb22e532c8000a3d84d8a65900014bd07314cb200029760e629964000636b94c532c8065a3e8458a65900018dae4b14cb200028f61062996400052f418c532c8000a5d8318a65900014ed02314cb200029d60462996400051fc328532c8000a3d8650a6590001c5ac4a14cb2027b8759332996404ef0eb226532c8000d4d724ca6590001c9cc4994cb2000393589329964000786a126532c8000a3d8494965900014bd07292cb200029760e525964000c3e43aa4b2c8000c6f72549659000399ce4992cb20003335c932596400072729264b2c8000e4d524c96590001d1a84992cb20002c720d74596400043fc32e4b2c800087e87d8965900310fd0f312cb2000297a0e62596400052ec1cc4b2c8000c6f72989659002d0fd0eb12cb200031bdc962596400043f438c4b2c8000a5e8318965900014bb06312cb200029da0462596400053ac08c4b2c8065c3f765096590001c5cc4a12cb200038b58942596404be2fbb664b2c8096c5f764c96590001a9ae4992cb2000393989325964000726b1264b2c8000f0d424c965900018bee739acb200028fe1173596402ed1f420e6b2c8000a3d841cd65900014dd0439acb200029b60873596400061fa16e4b2c805da3e849c9659000147b09392cb2000297a0e72596400052ec1ce4b2c8000c6f825c9659000187e84b92cb200021fa1c72596402ed1f420e4b2c8000a3d841c965900014bd06392cb200029760c72596402ed1fc1284b2c805de2f82509659000187ee4a12cb200030f5c942596400062fb9664b2c8000c5d72cc96590139c3e85992cb200038750b32596400043f43c64b2c800087d878c965900bb47d09192cb200028f612325964000636b9464b2c8000e2d428c965900018dae4992cb200038b509325964000727c1264b2c8000c5f724c96590
  | 27 => 0x7392653046200ccd724ca608c401d1a84994c11881f359c5329823100c7cc3c413046200ec932482608c42d0fd0bba2c1188021f617745823100657b9284b046201cac72509608c40199ee5992c118803335c9325823100746a1264b046200acd82cc5608c4015b50198ac1188063e21d20582310076499240b0462008bd87990608c40187ceb320c1188030f5d6641823100657394c830462008bf87590608c40187ceab20c1188030f5d5641823100657392c83046200cae645c8608c40195ac8b90c1188023ee1d601823100674b92c03046200c3d75d53644c40317f0ea16c8988032b5c942d913100667b9265b226201ccc724cb644c401c9aa4996c898803a350932d91310043fc2ae1b22621687c855c3644c42d0fd0fbaac8988021f60b75591310061fa16eab226200c3c75dd1644c4010ff0ab92c89885a1f21572591310047dc02e4b2262008f8805c9644c4010fd0fa92c89885a1f21f52591310043f43aa4b22620087c87549644c4031790ea12c8988030fdd542591314961e3aa84b226200caf72509644c4018beeb992c898a5f171d7325913100c6e43a64b226200c5f754c9644c52d8b8ea992c89880333dc9325913100e6639264b226200e4d524c9644c401d1a84992c8988030f15276551310045fc22ecaa26200c3c541d9544c42d1790eb22a89885a8f21564551310046f436e6aa26200c3c75d91434c40f17f0eb2482988928f21564905310061e3aec8a0a6200d1e759d2314c4b593cecba462988021fe1574d81310b43e42ae9b026200ccf724cb604c403998e4996c098803a350932d81310047dc3ac03026200c3e759d0604c40187ceaba0c0988030f5d574181310045fc12e830262028be84dc8604c40117b09b90c0988032b9d2721813100656ba4e43026200cae745c8604c40195ae8b90c0988032ba11721813100656c22e43026200cce835c8604c40199b06b90c09880a2fe1f42181310045ec3e843026293c3e75d08604c40187aeba10c0988072b9cb421813100656b968430262008bf87508604c40117b0ea10c098a4b0f9d542181310061ebaa843026201cae72508604c40195ae4a10c098a47279d332181310064eba6643026200ccd72cc8604c4015b301990c098a43279d132181310064eba2643026201cce724c8604c40199ae4990c098803a350932181310056a40a643026207cd5714c8604c40f1bb0f188c098803335ca31181310056cc0462302621687e87dd5640c4010fb05baac8188030fd0b755903144e2f996eab206287c3f741d5640c4010ff0ab92c81885a1f21572590310043f43ea4b20621687c87d49640c4010fd0ea92c8188021f21d525903100c5e43a84b206200c3f75509640c525878eaa12c8188032bdc942590310062fbaa64b206296c5c754c9640c40199ee4992c81880
  | 28 => 0x55cd648c4014790ab9ac91896b8794f53592310045ec3ce4b246200a3e859c9648c40147b0b392c91896aa7a0e72592310054ec1ce4b246200caf825c9648c40117d0e392c9188028fa1472592310051ec28e4b24625aa9e831c9648c40153b06392c9188030fdcb52592310061eb96a4b2462008be87949648c40117b0f292c9188028f61652592312d54f41ca4b246200a9d83949648c401c5f04a92c9188030fdc952592310061eb92a4b2462008be87149648c40117b0e292c9188028fa1452592312d54f418a4b246200a9d83149648c40193ee5992c918803275cb32592310070fa9664b246200e1d52cc9648c40117d0f192c9188022f61e32592310051f42c64b246200a3d858c9648c40153b07192c9188032b5ca325923100716a9464b246200cad724c9648c401c5aa4992c91896ba30c932592312d54fc1264b24625ae8f824c9648c40193ee4992c918803a39c932592310064eb9264b246200e8d724c9648c40191ae4992c91880387d4932592310074729264b246200e1d524c9648c401d1aa4992c9188038354932592310051f428e2b246200a3d851c5648c401c6ca3a8ac9188022fa1c51592312d45ec38a2b246200a3e858c5648c40147b0b18ac91887a2fa1f21592310045ec3e42b246200a3e85c85648c40147b0b90ac91896aa7a0f21592310054ec1e42b246200e8d32885648c40117d0e10ac91896a2f61c21592310051f42842b246200a3d85085648c4b553d0610ac918802a760c21592310074699042b246200aba80085648c4015730010ac9188028fa1770592310051ec2ee0b246200a3e859c1648c40147b0b382c91896aada0670592310054fc1ae0b2462008be87d41648c40117b0fa82c918802ada0450592310055ac08a0b2462008be87c81648c40117b0f902c9188028fa1720592310051ec2e40b24625aa9e83c81648c40153b07902c918803a34cb20592310074699240b2462008be87081648c40117b0e102c9188028fa1420592310051ec2840b24625aa9e83081648c40153b06102c918802ada0420592310055ac0840b246200c3c54dd9548c40117b093b2a9188030f15176552310b45e43ac8aa46216a3c85591548c4010fb0dbaa87189930f9937550e313243f43acaa1c628687c87595438c40187eeab2287188030f1d56450e310065ab26e2a1c625ac9e73592418c4018bccab9c831888a1f61b755063130e1f326eaa0c620087e87595418c4d30f90eb2a83188030fdd564506310061e3aac8a0c6200c9d76993318c401c3ccb3266318803275d964cc6313ae67432e598c6200ccd865cb318c401b1d08b9663188036361172cc631006c7322e598c6200d8d645cb318c40f99cc2b96631881f7198572cc6310061f3acc9b046200c3d75993608c40187ceab26c1188030f5d564d823100e6
  | 29 => 0x82c59887eb360f7058b3100666b9ee0b166207ace839c162cc49b59b07382c59881eb3a0d7058b3100573c0ae0b1662a0ae4815c162cc40155d08382c598802ab6107058b3103d67418e0b16621facd831c162cc43f5cd02382c598802b96047058b3100674b80e0b166200a6e85d0162cc4014db0ba02c59881eb3a0c4058b3100566c1880b16620087d86dd541cc4c387cc9baa83988031b98b755073130c3f43acaa0e627b87c8759541cc40187eeab2283988030f1d564507310064eb26e6a0e6200c6f7558941cc4018d8eab12839880333dcd625073103e6639ac4a0e6201cce724ca60cc40199ae4994c198803a350932983310b43f42ee8b06620087d85dd160cc40399ce4992c198803335c9325833100746a1264b066200c3e645d7648c42d0ff0ebaec9188021fe0975d92310061fa12ebb246200c5e755cf648c42d0fd0bb96c9188021f61772d92310b43fc3ea5b24620087d87d4b648c4010ff0ea96c9188021f61d52d923100c5fc3a85b246292c3e7550b648c40187aeaa16c9188032b5c942d92314be2f3ae65b246200c5d75ccb648c4031bf0e996c918a5b179d532d92310062ebaa65b246200ccd724cb648c401c9aa4996c918803a350932d92310061f32ae53246200a3e85d8a648c40147b0bb14c9188028fa1662992310051ec2cc53246200cad7298a648c40195ae4b14c9188028fa1462992310051ec28c53246200a9d8318a648c40157500314c918802ae60062992310051fc36a53246200a3d86d4a648c40147f0ca94c9188034b5c952992310070f32e653246200a9f864ca648c401c3cca994c918803635c9329923100746b12653246200f0d524ca648c40147d0bba2c9188028f61774592310061fbaea8b2462008be87909648c40147d0b212c9188028f61642592310054ec1c84b2462018bc87509648c40195ee4a12c918803335c9325923100726a9264b246200e8e424c9648c401d1a84992c91885a1fa1770592310043ec2ee0b2462008be87d95648c40187eed32ac9188028f60a65592310045f438cab246200c3e65dc9648c40187acbb92c9188022fe1972592310061f32ae4b2462008be87d89648c40147d0bb12c9188028f61762592310f45f43cc4b246200a3e85989648c40147b0b312c9188032bdca62592310145f43ac4b246200caf72589648c40117d0e312c9188028fa1462592310051ec28c4b246200aba80189648c40157300312c9188028fe1b52592310051ec36a4b246295c3f76d49648c40147f0ca92c9188028f61952592314a61fbb2a4b246277c9f76cc9648c401c3ccb992c9188038759732592314864fbb264b246200e1e654c9648c401c3aca992c918803635c932592310074731264b246200e8d624c9648c401e1aa4992c9188030fdd675592310061eba8eab246200a3f8
  | 30 => 0x93310043ec2ee0b266200c3f759d564cc40f53906baac9988030f5d4755933147e4f996e4b26628e8bd879c964cc40147d0b392c9988028f616725933103d4f41ce4b266200a9d839c964cc40195f04b92c998a3b27cc9725933147c5f438e4b266200a3e851c964cc40147b0a392c99881ea7a0c72593311054ec18e4b266200c3f72d4964cc40187ae5a92c998a6787ccb52593310045f43ca4b2662008bd8794964cc53147b0b292c99881ea7a0e52593310054ec1ca4b266200e2f8254964cc40187ee4a92c9988030f5c952593314c70f992a4b266298e2e3254964cc531c5a64a92c9988022fa1c52593310045ec38a4b266299a3e8514964cc40f53d06292c998802a760c525933103d4fc1264b266207e8f824c964cc40193ee4992c998803a39c932593310064eb9264b266200e8d724c964cc401c3ea4992c998803a394932593310070ea9264b266200e8d524c964cc401c1aa4992c9988028fe1571593310051e42ae2b266207a9e83d4564cc40153b07a8ac9988822fa1c51593310045ec38a2b2662008be87c8564cc40117b0f90ac9988028fa1721593310051ec2e42b266207a9e83c8564cc40153b0790ac998803a34ca21593311045f43842b2662008bd8708564cc40147d0a10ac9988028f614215933103d4f41842b266200a9d8308564cc401d1a6410ac998802aea0021593310055cc0042b266200a3e85dc164cc40147b0bb82c9988028fa1670593310051ec2ce0b266207a9e839c164cc40117d0fa82c9988022f61f505933103d4f418a0b266200a9d8314164cc40117d0f902c9988022f61f20593310051f42e40b266200a3d85c8164cc40f53d07902c998802a760f20593310074699640b266200e8d3248164cc40117d0e102c9988022f61c20593310051f42840b266200a3d8508164cc40f53d06102c998802a760c20593310055b40840b266200ab58108164cc401878a9bb2a9988030f151765533103c6e41aecaa662078bc8759154cc42d4790ab22a9988032759373553310053742ee8b166200a6d85dd162cc40f59d07ba2c59887eb360f7458b3100666b9ee8b16628eaad879d162cc401c5ceb3a2c598a3fa39ce7458b3100746b9ce8b16628fe8c319d162cc51fd1e613a2c598803335cd7458b3100657c3ae8b166200e2e755d162cc401c5aeaba2c598a3b2bdcd7458b314774739ae8b16628ecad735d162cc401d1ae6ba2c598803235cd7458b314774618ae8b16628ee8f305d162cc4014dd0a3a2c5988029b6147458b3147d57420e8b166207ace831d162cc43f59b063a2c5988038bd525458b3100567c1aa8b166207acc8355162cc401c5aa82a2c5989d6b3e0d7158b3103d6741e82b166200acd83d0562cc4014dd0a20ac5988029b6144158b3100557426e0b166200aad84dc162cc40f59d07b
  | 31 => 0x82018bc87509655040195ee4a12caa080333dc9325954100e6639264b2a8200e8d424c9655044987ec8b90caa08021fe1f621954100636b96c432a820087d87988655040147b09310caa080297a0e62195410052ec1cc432a820087f87588655040147f08b10caa085a1fa1c62195410043ec38c432a827ba3e8418865504014bd06310caa08029760c621954100636b90c432a8200a3e8650865504014790ca10caa09870f9d9421954100717b128432a82a4c5e76cc86550547c3ec9990caa0a8b179d9321954150f0fb226432a8200d4d724c86550401c9ec4990caa080393189321954100786a126432a8216a3e86d955450445878edb2aa8a09862fa1871551413de1e328e2aa2827bd37751c5545040117d0db82a8a0a2b0f19770551414fc5fc3aa9b1a8216c3c75553635040195ee4a16c6a080637e1d32d8d4100666b9265b1a8200e4d524cb6350401d1a84996c6a085a1fa1670d8d410043ec2ce1b1a8200c6e72d9663504018dce432cc6a08031bd957298d410063632ae531a8200ccf635ca635040f998c6b94c6a08021fa1f6558d410043f438cab1a827bc3c7419463504011bf0eb18c6a08030f9527694d410052ec1ecb29a8261c3c74d95535040187ecbba2a6a08a30f1977454d410149e43aa8a9a8216a3c865515350401878ecaa2a6a08022f2197590d411461e32aeb21a827ba3e86d964350401878ec32c86a08038718c6590d410070fb2ec721a82778be869c6435040127b0b38c86a08030f1967190d410045e432e121a820093f855c24350401878cab8486a08030fd9774545411261e32ee8a8a8216a3c865515150405878ecaa2a2a0802cd20554545410b45f436eb20a8224c3c65dd641504b533d07bac82a080a2f21975905411261e32aeb20a827ba3e86d9641504c3c6ec3b2c82a080a2f61f63905412d64f39ec720a820093f855c24150401878cab8482a080333dc932d814100e6639265b028200e4d524cb6050401d1a84996c0a09861f21b75581410043f43ecab028200c6c72d9560504010fd0e32ac0a08031b1c865581410062fb2ee6b028200c5c65dcd60504018beca39ac0a080317194735814100637b2ee4b028200c6c65dc960504f787ce8328c0a08023ee1d60181414545fc3aa83028216c3c7555060504010ff0ab98c0a085a1f21573181410045ec3c863028200caf425c860504038dce4a90c0a08031b5c9521814100e67392643028200ccd724c86050401c9aa4990c0a0803a350932181410145ec3c823028200ab980904605040f17d0faa2c9988030fdd7545933100657a12e4b2662078be8790964cc40147d0b212c9988028f616425933103d4f41c84b2662018bc8750964cc40195ee4a12c998807339c9325933100726a9264b266200e8e424c964cc401d1a84992c99885a1fa17705
  | 32 => 0x117d0faa2c1208030fdd7545824127c5e43a86b048200a3c8550d609040187eeaa1ac1208032bd0b72582410043fc2ae4b04821687c855c960904010fd0fa92c12085a1f21f52582410043f43aa4b04820087c87549609040187eeaa12c120a4b0f1d542582410062fbae64b048297c5c75cc960904018beea992c120a5b171d5325824100667b9264b048201ccc724c96090401c9aa4992c120803a3509325824100c7c43a40b048200ec93248160904011f70eb00c1208033a5c960182410051ec24a5b2a8200a5e8394b65504014bb07296caa08061fe1d52d954100636b92a5b2a8200ccf724cb6550403998e4996caa08039394932d954100726a9265b2a8200e8d424cb655040517908b86caa0802c7a0f74d954100636b96c5b2a8200a5e8398b65504014bb07316caa088a1f61c62d95410052f418c5b2a8200a5d8318b65504018dae4316caa09ef0f9d942d954100717b1285b2a8200e2c6250b655052f8bced996caa0a5b179d932d9541006a7b9265b2a8200e4f624cb6550401c98c4996caa0803c350932d95410051ec26e7b2a8261a3e849cf655040147b0939ecaa08029ba0a73d954100536c14e7b2a8200c5d731cf655040187e85b96caa08021f61e72d954130d1f424e5b2a8200a3d849cb65504014bd07396caa08029760e72d954100637c12e5b2a8200c3f425cb65504c347d08396caa08028f61072d95410052f418e5b2a8200a5d831cb65504c347f04a16caa09878be0942d95410061fb9285b2a8200c3d7250b65504018bee5996caa0803175cb32d95415270fa1665b2a8200e1d42ccb65504010fd0f196caa08021f61e32d954130d1f42465b2a8200a3d848cb65504018dee5196caa08038b50a32d954100637b9265b2a8200e2d424cb6550401c9f04996caa080317dc932d954100727b9265b2a8200c4f724cb65504018bae4996caa0803931c932d95415170fa1265b2a82a2e4e424cb6550401c3a84996caa0a8b9350932d954100706a1265b2a820087e870cb65504010fb0e196caa09868fa1032d95410051ec2065b2a826187e87c8765504010fb0f90ecaa09868fa1321d95410051ec2643b2a8200a5e83c8765504014bb0790ecaa0803934ca21d95410043f43843b2a822287d8708765504c347d0810ecaa08028f61021d95410052f41843b2a8200a5d830876550401c9a6410ecaa08029ea0021d95410053cc0043b2a8200a3f845c365504c347908b86caa08028f61070d95410043f43e41b2a820087d87c8365504c347d09906caa08028f61320d95410052f41e41b2a8200a5d83c836550401c9a65906caa0803934c920d95410043f43841b2a820087d8708365504c347d08106caa08028f61020d95410052f41841b2a8200a5d8308365504014ed02106caa08029d60420d95410045fc22e4b2a
  | 33 => 0x335c932d854300726a9265b0a8600e8d424cb6150c2d0fd0b386c2a18021f61670d854353e2eb98cb30a860087e87d956150c010fd0e32ac2a1a1b0f1d065185430047bc3ac230a8600ccf724c86150c01c9aa4990c2a1803a350932185430043fc2ae030a861687c855c06150c0199ee4996c0a18039354932d814300746a1265b02861687e859c76050c010fb0b38ec0a1a261f21b75581430043f43ecab02860087e871956050d4d8bee632ac0a1a1b0f9d065181430047dc3ac0302868a8bf875506050c2d878eaaa0c0a18032bd09721814300e37392a43028600c6d725486050c0f93ae8990c0a1807339c9321814300666b92643028600e4d524c86050c01d1a84990c0a18021fe1571181430b43e42ae23028600c5e659cf6590401a38a939ecb208027360a73d96410070e2a4e7b2c8200acd829cf6590401c38a8b9ecb2080237e0973d96410064fa12e7b2c8200c3c54dcb659040f1bd07b96cb208023760f72d96410061e2a2e5b2c82018bf8750b65904494790aa16cb20a3b279cd42d96410064eb9a85b2c8200cad7250b659040f1bf0f996cb208023761f32d96415270e2a665b2c82008df874cb65904011bb0e996cb20a8b8715132d964100667b9265b2c8201ccc724cb6590401d1a84996cb20a978d15271d96410061e2a2e1b2c8261c3c74dd565904014bd07baacb208030fd5372596410061faa2e4b2c820187c87549659040147f08a92cb208031bdc952596411251f42a84b2c82a3e1f54cc96590543c3ea8992cb2080333dc9325964100e6639264b2c8200e4d524c96590401d1a84992cb2096b0f5917598e410052f42ec731c825acad645ca639040199ec6b94c72081f3318d7298e410062fbaea6b1c8200a9d8414d639040159b0429ac7208032b5c94258e4100c6e43a64b1c8200ccf724c96390403998e4992c720803935493258e4100746a1264b1c821687e851c163904010fb0a382c7208063ba087058e4100476c10e0b1c82008df8758c63904014bf06b2ca7208030f5957494e410061faa6eca9c828693e87dd5439051387eedbaa8720a278798f7550e4143e1fbb0eaa1c8287c3c761d5439050fc3cc63aa872081e2fa1f6550e411261e3aecaa1c8207a9e83d95439050f1790eb2a87208930f1d56550e410068e3acc6a1c8200b8d8298d439040f53f0cb1a8720803471d56350e410ec5ec36e2a1c8200d3775dc54390401a68ea38a87208022f6187050e410061eb2ae928c820087f855ce609042d0f90ab9cc120807339c9329824100666b92653048200e4d524ca6090401d1a84994c1208063e61e209824100764992413048200c3c54dd5609042d0fd0fbaac1208030fa1375582410061ec26eab048200c3f43dd560904010fb05baac1208030fd0b75582410061fa0eeab048200c3c40dd560904
  | 34 => 0x3b265b2a8600d4f724cb6550c01c9ec4996caa18039318932d954300786a1265b2a8600c3f42dcb6550c010fb0f396caa19928fa1272d95430051ec24e5b2a8689a5e839cb6550d594bb07396caa18031be0972d95430061fa12e5b2a8664a3e841cb6550d1347b08396caa1a2697a0c72d95433252ec18e5b2a8600c6d721cb6550cc947f04a16caa19938be0942d95430061fb9285b2a8600c3d7250b6550c018bee5996caa1803175cb32d954355f0fa1665b2a8600e1d42ccb6550cc90fd0f196caa18021f61e32d95433251f42465b2a8600a3d848cb6550c018dee5196caa18038b50a32d954300637b9265b2a8600e2d424cb6550d13c9864996caa1a2793e0932d95430062fb9265b2a8600e4f724cb6550c0189ee4996caa1803175c932d95430072639265b2a86a8e1f424cb6550d51c9c84996caa18038750932d954354726a1265b2a8600e0d424cb6550d1347b09b8ecaa19928fa1271d95430051ec24e3b2a8600c75711c76550c010fd0f90ecaa18021f61f21d95433251f42643b2a8600a3d84c876550d134bd0790ecaa18029760f21d95430072699443b2a860087e870876550c010fb0e10ecaa19928fa1021d95430051ec2043b2a8689a5e830876550c014bb0610ecaa1803934c821d95430053d40043b2a8600a79800876550c0147f08b86caa19928f21170d954344d1ec20e1b2a8600c79701c36550c010fd0f906caa18021f61f20d95433251f42641b2a8600a3d84c836550d134bd07906caa18029760f20d95430072699641b2a8600e4d324836550c010fd0e106caa18021f61c20d95433251f42041b2a8600a3d840836550d134bd06106caa18029760c20d95430053b40841b2a8600a75810836550d558beebb9acaa18022fe11725954300c5e43a84b2a8600caf725096550c031b90e992caa180333dc9325954300746a1264b2a8628c3f645c86550c01a5e84b90caa18021fe1f621954300636b96c432a860087d879886550c0147b09310caa1aa69760e62195430043fc3ac432a8600a3f845886550c2d0fd0e310caa18021f61c62195434351f420c432a8687a5e831886550c018dae4310caa1a1e8fa19421954343d1e4328432a8664c3e765086550c01c5ec4a10caa1a27179db321954343f0fb266432a8686a5c864c86550d518bcec990caa1a1f87d913219543006a6b926432a8600e4f624c86550c01e1a84990caa185a8fa1b655514344e1e3b6caaa28689d1f751cd5450c0171b0439aa8a19de2fa18715514345e1e328e2aa2864f8be86dc15450d15878cbb82a8a18030fd977454d431461e32ee8a9a8607a3c865515350c05878ecaa2a6a181ec720d5454d4345c5fc3aa9b0a8616c3c755536150c0195e84b96c2a18071b9c952d854300636b92a5b0a8607c9d744cb6150c0399ce4996c2a1803
  | 35 => 0xdc86155001878a9b90c2aa0030f15172185544945ec3a8430aa88ba3c85508615500587aeaa10c2aa25f275d332185545a70e2a66430aa896c9d744c86155167c38a8990c2aa007339c9321855400666b926430aa800e8d424c86155001878a8b80c2aa00237e0d701855403c6e41ae030aa8168bd84dcb6055001878a9b96c0aa0030f15172d81544945ec3a85b02a88aa3c8550b605500587aeaa16c0aa25f275d332d81545970e2a665b02a896c9d744cb6055163c38a8996c0aa007339c932d815400666b9265b02a800e8d424cb6055001878a938ec0aa01e37a0e71d81540046ec1ce3b02a8b0cb974d826055001a38a9b9ac0aa23327d9073581540068e2a0e6b02a8009cd821cd60550011f70eb00c0aa007339c9321815400666b9264302a800e8d424c8605500187ea9b92cb218030fd51725964300c3e43aa4b2c8600a3f845496590c018dee4a92cb218a28fa15425964357f0faa264b2c8600ccf724c96590c01c9aa4992cb21803a350932596430061e2a2eb30c861687f875d66190c0187f08bacc3218030f21175986435761fa1aeb30c86aec3d435d66190c010ff04bacc3218030fd0975986435762f992eb30c8600c3f415d66190c0187880bacc3218022f61f54986430061ebaea930c861687e85dca6190c010fb0bb94c32185a1fe1f52986430043ec3ea530c860087f8754a6190c010fb0ea94c321a4b0f9d542986430061ebaa8530c8696c5e754ca6190c018baea994c321803335c9329864300726a926530c8600e8d424ca6190c0199ee4992c321807331c9325864300726a9264b0c8600e8d424c96190c2d0fd0a382c3218021f614705864300c77410e0b0c86008ed821c16190c0399ce4994c121803335c9329824300726a92653048600e8d424ca6090c010ff0ab8cc12185a1f215719824300477c12e330486018ec825c66090c01878a9baac12185a1fa1f75582430061f426eab048600c3d84dd56090d5b87e87baac121ab70f50f75582430043ec16eab048600c3f42dd56090d5b8be65baac1218030fd0775582430061e206eab0486008be87d516090c0187eebaa2c1218021fe1572582430b43e42ae4b04860087e87d496090c2d0f90fa92c1218021fa1d52582430043e43aa4b048600c3f755096090d25878eaa12c12180317dd532582434b62e3aa64b048600ccf724c96090c01c9aa4992c121803a350932582430051ec24a5b2a8600a5d8394b6550c018dae5296caa18061fe1d52d954300636b92a5b2a8600ccf724cb6550c01c9ca4996caa18039354932d954300746a1265b2a8600c76515c76550c018f4a0b86caa18031b5cb62d95435652ec1cc5b2a862687d8718b6550c018dae4316caa1a268f21942d95434361f3b285b2a8600e2f6250b6550c01c58c4a16caa19929721932d95434b62f
  | 36 => 0x4000000000007404a0030080088006022005800400601d000809c000003001804c000054000002000000c000800c01400000b002001a04d0018008004006003800002200100000040060030000010000006000007400600100000b800e000000000c00a05800d800c0080080000000014005000000000001100400000080380010008002001000800004e001001000800000000000040000410138048002001005000400200000000080000000040014006000000001000400700880080060000000000000000000000403c00900201b800205a002801803a005001815400000000000b400400a00080140020000058004020000000800800001600e0008002004000000402a0000068030004001004807800a000007801c002001002002001000d010000401a003001800c00c0010048000012000004806c00000200d0038004005000804c000001004800c000005002803400400000100000180000000018010001006801000e000002803c00400001c000000003a0008040000021017801001800101c0008012000000800403600001180000040010000068006008003007000c0020010014006013000002400200000c8030004000001801000600500280140020120028000008000002000000200d000800400000d015800002e001001000c00c0000040028000005000802c070004002000800200000300100280040050010010000000001c000001000000400200300c80d002001c008800001200500180340060020000010004019000007400401e002000000200f0008018000000000001801800e005004c01e000006803801401900100080340010028064006000000000000201100000000060080020004006007001000404e0440038004004000004000400001500b8028006002000000000200000800000040040068044004006001800800201000c8000010030007800401a002000000000c004002006004000000b800c00e01f011000c002000000800003a000001000800c015002002000000000c80280000090070004022003002006800a001000000000000200a8010010006000000400a0060000040008000002001c00000000300ec000000007800c00000a000022002c00c0000008004000000001000000b004800000a01200d003003e000000800804c00e001004c002001000001c0000040070070000000014000000800000f800000200caf7250b63550031bf0e996c6aa007339c932d8d5400666b9265b1aa800e8d424cb63550011bf0eb18c6aa232a7e116318d5446657b22e431aa800d2c545c8635500f99cc6b90c6aa0033358d7218d5400e6739265b0aa800ccd724cb6155001d1a84996c2aa23327d9273985540068e2a4e730aa8009cd829ce6155001a38a8b9cc2aa0023de1d61185545ad5bc22c230aa8168bd84
  | 37 => 0x70008004026007008000404c002001000001a000000001802a0000018018006008002801c00a00200380800140040010014018008004800401401f00e0000000009000000c00600200000300240020168078002000001800002800100000ac0060170158020008005013802c00c000001004400601b0038014004000001809000800a00280540000010010000056016000001400a0010000010018000004003400200000080040900000010000000000000806c00400d00600900040000168014002005001000802000200480000040270078000000000000800001800900600180040330078008000012000000400e03a007814408001b001000400000c0000008000007002001c02401500000080140070000084012009003004800401e001000c00200100980a0002001002802c00c002002000000c004004802c006006002808c004000000000000003f000000000000a001801c0200000028008000000001002800e001001003002600a00200780100030008008008001000000001000400180080080170010000000004000800c00000000d002400600603b0014016002000002805000200280180060020000038000000000814001200e000002802800b000000000000200001d005000300b807c01e0060018008054004001000003000100180140be0090098074022000000006000a00000000040040080000044002003001000000001d000003400c000003002400000e003800400c0030030000002000003001000000500480b0000000013800003c000000000800400f0040018046019001000c028024000000400401100180300480030000030012001005000000200c0018004004001000800800001f00c000000600000300100020010078084004003000002000a00e001802403401a0030014006004007002400000d000801000e0150010054008007000000c002002003804c014039001801c000004007000001e007001800001200c0000058012000009000800400800880200000120038008002001009000000204e000001c004001006001c00e01803b805c00a021001800c00000b00300140b6002008803000e00600a0054018006000000400c018000000c000001001001c00401700c00000040060080000028000000801c00001400000000480210008060018000001001800001400180080020000000000000002000000c0000420000018006002015000c0000070000010008000000009800800c0010000002016000003402200000180040180090100004000001000000801e00400000000020180018034010029007000803600a002803402a00e000000002c000002800401a00300280c00640030050040000003003800400e0000020010024001000800401800000d80000060270180028012002003001c004002001002
  | 38 => 0x28006001000003400400503d800000a000002800000000800980280000000040004000005002008c03a0010028000002000006001c0760250028008000006003003c00a01300880000000030000008018002003003801800a002002000401300000200000160300014010000029800003e000000000c002017000000401a00e000004c00803c001800002a0010070000016012006000402801c00080a0006006015801400c00100100000000070028040000013008008c00a002003802c00001200180300000060038000064000002800000400200100280de0000038008000002006000000200a000005000000f008000800e000019800c00400900200200060280020018086029000001000605a003001001a01800c000400000e000008005a00300e8000004002000007c006006002806c00001d001000c0020000008000000001001002400e00100280380020150040000002006002001800004600100680000000008004000003000002000401e000000403c003007006000e008005000810e005001817c02a04000c0004028001004007800200a0010030006029002001000000200c805000201a000805801c000000000001c00400000000b40030068030000004000804000e002002002c03a003000000c03c0070028010036013004002c022003003800400800e0120000000005000001003c001003802400e001003003400000800680100020010000048000024000003803e001000000000000e0038000010000001800c02401c001031400001f000004c01e00100480a8000008007000800400000400200000000048054000039005801402c00000e003400a024000000800a00300d01400040020038094004005003005000000c000008c01800000700040100060060008024002000800000200e00e000800a001000001c000008001004404c0030008020000001000000000001400080200020050070000022001018001c01400200700b000400000500000b4002000000800c00000500380060080010024000008005003001800800180080200040028004004005027008802800200280180200010050008032004000000400800d007800401200d00980180040020038030012000000805400400000a002c006003000000400000d000001400c001000000000c0260070000000001000001000800800600040260040010000002005005802c00000f00e802c03a008000806c05000500700b80040100000000004043002000800c0060060000028003004801401200000c000401e01100000100000050040000002003000001c004000003000400800100200c001c00800080e800402f001800000000a0008018004006006803400001000100580000010010078002014002000402e005012802000a0000430004004000004000400000
  | 39 => 0x1dc0000a48906a3f6337135e6d303f43268cf69b81c840dd000000001295cf078e00018120001d9626c000044a9c986f780001ba93aa74441df000000000011de00e23ec997986c7f0547009200009741b204fb267e7020d7e03bc20e000160a0300ac19cb40003a3cdb747296b400001e208b1a1873f88be7988a26000157c0e314b14bb00000000000692800040f223017c9b485220cdb46e8cea4f24ca369e0aa29b402f6000000072584f857605eb29c19fc9a595909631ab22dd06be5f51a5864a92bd053178027415f306f181a4f299a850a903000004e900017a844000009b08421707888813da2a84c722100a90623736000000000580001a5f32800fa43f400006590ca58ea4aa2a7962d92c218608d15a8000058d87b8ad4635042c63c00004a6940d0c196da42e9925000000000000008fc000091b1a9141e985c33f4b2c34fdf283f11c2a5e992025aa06225341d8f47aa5105c8857457786c486c25cc7b4019c0680c7e8ade5c885994581720b5050bd2ca34083127118cc93d684816aa0bf17f60de679a9ac2139130a65c01825d61ed275e62b493aa5507cd15e29879bbc76497a469a82c6471040a41649c09b8a4f512b88ba02b575c3ab1d7e6fe1a382afcd9a4b49e68556850837205fe9328c2a2d394c0004217c5d30d19837834250f1c801068b7789d03364fc1f2e1b29da445792fa01c0550228273461d4df025b9f78600862049aa0126750bcc3c489fc83b26e11c1a3d4625e69815915e44404dec58a2652054188261c51fc19222760ff8b1e8e625f67efa7072971bfe65e24427ab8b0289797bc02209f04a1d79440626c4161e2505128f4202c20966431e4610391083ae9a5c04f8340011a48463f04b4569129e04d212a59c266016ac014282d8617a7e38a998a6ea4528e366ad20142dd543e00005af7029fd0765db1e0a29eee0000000000000059303f243d89529aa96ce17621600b841066579f8000011d223e400038507be24de2c8977a2be0ec0000460000033056860b4937e425a3fa392c01a014000000402001600a0020006011005809001601a0180004006000000802000000000180340120020008004000008001800800200300d000800800b012800001602000a000800201a00300100040020040034002000000001002a0070000004008001001000c002006018000000e02900000a806000100a802c010004023808400800a00b803000000000400240000050008004012008001001403c016002002c008036006002c01401b000004001a006001005800400101b000006200101180000000020010004040009004002c03c0010078000046000001000000004b000000000000000180c4006006002000000200000e000800e0000000020000001004005007c005003001000000f000800000400000080
  | 40 => 0x8a9216470c0a6849681460000000583000040e1e7147b00000000000000025d000000072b0000000094f000206e60a984f00000002dc9b3c7c9898e00019988d19328158e04e0000e4080f9e61302859a4954000515daba8298000000060f00000008dba52a000000052d02fc0b763c803d800000006e42a7643600023960002562000045627e00001ab248700009546e7a5c05520bda4ae87660000000000014909b1a6e9a303f80f80bc4842060e00000c25738218565240644f016f4e9803a277924286318405e3817300013eb3bd1ae25f6a0521284d865c902865ff80004ff1a709ca09768018cfe6918d886502420942965432e875a27095c437e8b0e84a245c39610981469fd68f6004a32491225de121c8d11eec1ca192c8101d5800019e619e99d22d024d24418d960101e445560a2e25e1b8600d04630bf8bae90a185396f119829762bc43d25f23dc8a309930aec8698cad89184d667a81982910b9844c84cc33fd6b055107d89b2932070096041831fce6be0be07a50dc13e31b8006b90ea78219ca1a0012b4ed1bbe58b99ee07f0fe22241f7a08f9ed847001e8459a05e1fede64041000066e8ca856d99dc796a45030081d50eba61624898c0643c00084e831412e4eab9799aa60c0854465f8000719800000002b47848d8e0000af200007bc68d800011448f874180000000afc611091081f9580395a2604af21f4586a6fa00017b25b88000000110b88d9e706df11240001184000009604602108cd8d2b080962440b84555458bc8304a23a6db9f622ef4b922d447b813c400085124481bc233273c0676000000000001ac52b800064d219660e9f0a1cd85788d40d1673f400000000003650b5276280003e3a6882fb159a4670c4f000008c24edb386519e020701e2c14349ee3f300007d705a20000238000204c0000b8257eccbc000111b0489b767d4800000027048b28d5800000007610000444800036fc752878a00a50b804810a093e68c1ff854a0ddd6ca8190000022d000022a30f1d5a10f00007088e4e25fcb9b00000000000000000000000000000001b9c0000cd4000000050c84d216e000000001088a6047c1c080005a01f54000207200283b20001dc800000000000000661c44659c5d727a5c00062e000066053e87da8be51d7247826084ec30d667049312f34538bd65231a752fc016d70804100000db0044a2202170dad5b40dde8fb9538793df581b791649be00007fe925061e247c25e88508ea880249847cc43b9cc20f01c269040dd8212a3524d18a126308de425c937a0c01ccc42b8698117983e87f267c228806b7410b844a826ba296985062f13540850c4894b8cfc25119d05f6d40a3c308ae79f200f32886ba6c1858661259481f990523165d0300012a2505a463003c000579400021a112b00019035870
  | 41 => 0x232469e93320000000809a4604438000000000001592cc26507e21309c4e3c783c21cf1b1c4290fd039180326bb0f820c442b844314518e402561580c044a4150204318ae2d68000173270e2dc000085b8cdd6b30e5e101a1e4934247692d000049d06a6485895c920000026a9176005972a14b800000000003098ed83b212541cd00004aadf4c010a5a483809ba00011363990d62000000000009ae840939894200007e20b648f8a5f04470afa55a0c006e58a029361fdc375a322091d5068448e2e735875857f00004bd800005495da05c09d436d06f66d180d938c80009ba1aa076d57f4609a1dc3e50aac30ac0d4000000000000003b8800b32a800048d22aa75580000fba6420831f920f72578677a62c26c82904a20a901259c8e19b83f02381116225908893b9cf62e70a6d8dc14e64e51c384e71c364b16676000156242d00001fe128415096406319d7449914381024b468da8ca62e18e4a4ea08fc000040c7a80bfe3d003da18757d63b780005d80d5a0b0a4d44361c6e4ba11a60498f4c31e85827318c7147300360018d801ff15746299a9c6fc10e646b13480791a08329cb14040248621d137859182ac00021307bd17628c409da39f043a5c40a9a1dc86da95fa3722e402122470f5841116ec29d8294501148636d6512101e58a5c681a80249a9080b92fe6b60000000209a0da93f63e28f383b982f8059434c5c7936f31484a71d90eb82e821c25aa838e1ab8d2c89c105a9bf1c9c05ca40e3768c29000149e29e000016446c84b595d618697d2610800024c51a800014763ed80dd7948a1e7a4000000024be0598812360c0002fcca3e63c85b0189646e925a224097c4af94c139f90e853f3a640000001aea3342110000023328b22b34ef96929551ec282e800000009f400008781408f881a326445d991b28a141b33275aca65a4ae200000a04ccc000256800018f03468a50739823e54e49e893688c96be00000000001b1671800004b68e722fd49fa01a86a038e000054799cc000235a29dc9cc7fd194e5bf00008959c068e31d6400007f200001249770c86080192606784975ab9c941df09148ce015a4e762b07e1400078e1292382565a0b9126b88b00b6775964d548897070b119252b0d7245e836231a020a1140e9c00004ac4ae04bb65882924d810346831efa23b9b4e8cc108668f01f8270c00077d8dc775f14108908e8a00014480b421ce77c215419e22f683512b649112823db0670036d72c02a15322278bbc68f87fa0001f3a0c100005ed82258cd26cc7c710d20001c18836400000002701ce195000001f00000b2e00002c436294525549a9e6d288f437e16780a3a2260b6964203b0ac40aa9ce489010fe5f910fb77704f069400d72fa52e45cbd9100000204517931209522d492a04345ce98c84f018866c919a3
  | 42 => 0x60c8924643884230001f025b726c0178249a568000030b1b7291007de594009d5c380002ce0a920001dbb0e790b85310d600f31d1266b035e290a3485b251aa11a00009cc80008ec0d329c189606b787146769a2202bdf5e0f29cb48eb04d828880009a18000287dd6e000089a7fb98e81f91bb80001f8e03f00000f980008ba110974785c02bd80002a8055267ea5ee000146a4aaa1ca00020f0000228000000000d20904166d52c12422f48860746000000000019b8000000000000000c74ff0000195600014e4069959c000137b0000bef00022627a3a5580001d82000099823395240611dde18541f466d1cd22231dd27e1800087180001bc912655b00001104a981d2083e5ef86059898595023442e000148a9c6c828450044474e50915a613804a324f43200b7c9179c4461c9d3e305d52000021cc0001d248b00000000000086da27a8ae9dca11d0cca94800f415a800000013718de97c4667800070e878612d4489656000000006381661ad60df10ac00006b60ad9bf62f70d569b2492c6420000615800000005244caa3420c240005d51d4a7221a7e3f51ea20001dbc717800086e800000021980ba0c16672000000018906a59e8b00015cc744c000235925d4d4171c2c48000622164e0f7400007519c013ccb8100023c05b6000085783320550000937a2121e9c2a85334794204000005603de1bb83c615b1c104d711d47f212684119db27edd7f292e8fce76a5e3929b805a6058c9e351d02c9670be272e102a4744f5e06a922828d80008f70e02022c3086038a8878002ec494824478403d483681b183400002c904319199e9e0d3d8ca0868d063821a492178000418191e0000ba90349e142d6215c1f51e822520055000045a6d7885220197f6317cc3a000132e0000000485000000000000000000257a2588a989ea026cf920ac12486d920906f487749129f405d4927657bd2ff18de6da59e85b268b04ca99605267a3091246d8e9e9768000184400000011b0000234c73402524c01aa754d00003cd80000000f1493080007b30000000077e00000000001e8a07a80000000d4c916ca65000100866680008f684e30000b9e00025a04dd818c76fa70841d00009b491dc16f80000001fc2000000009e905e1d31792764e0d6481a2ce23c12b400000000001b8d30b8e300000e660cc233c65da50672402cc38b015c20624880d38d22771888e4d4e6e460f1c4289b92c8952253928f084c95588fa0068674962048d00601600c38fa8678211892319f601e918c26100002fc8b561190f301e8c00080a0a1a12a55500dd82c9476e66800019190000732230800000000000001ac858980000c29edc189c4437c1a27e051000000000006d08000000223c42c06bc52383c400000000dea3a0332000000000008e3926e2ad58cc0091c5221c
  | 43 => 0xf0a5b8d8800085b0ec6078ddad81249000000c25282000000020ac8b18b325798ed61e2a6a412fe26802b156400003494559a9d80802781f4832f86fa01a0970fc800f9f4a628a0105c0944434f80000001a953385b1234ed7ac11280009c717728df10fc82da50296d00000000d9941c800094983ac8c0953c08c14348430102167862111615f45a0c00079bc7243ee9c7424293f86e418665f825b000000779321e6608b802e7bf813c1778daa1a5804c24919684190efc6249a8869d8d2976ba6a8333993c29497c0000062c2b589b860b86440d486d4880941417120ae6d51cfc091822124f05006e4a3066e21a54107043e0000adc09806e25cb8ca5679000042a16f8043800098c800001a081653300000000000000000000000000000acc260596a657000074e9d2623484b684280841fb15601c48f90000151486780005a08a2011e00009bd4bba0000de9023cc774811ba041889200000000000178268780002389bc67a200000e10000108109e66b935687a1d4e06c0ccd4b087b00b447800b64000000000087e0000299d6f20469ece6a49c566639ae659dc5da57501c402400ae5a693a47704ae09c913b05551fa26201ec862924125fc24224b18d421a71fb28f2927c208130275c007656ca30a21b8d2e577000067c8000210a0ca7a488e864f8c627920a401318ecc463800093c0000000000000021bc6d88000746418a9819c5a59d0f0415ecd003310f4e3b70bfa00000006c841de00018e04aa00006b189e60000a7235122c25030d184ff9f7c382a586014926300018680f3832a0a10f46352a01624c2474742d05c158a3c65a386340c7e24c3ec00508bc9b00966a15610e53b9000180c291e4346214b18000000031023163de8cd600015b9000271977080000e0106e06e80f10f5800036140003d89f1e00000121be9a82000065c0001a1918182583ad800014d000081c22ac9b9c72c0002726232833a1220c0b0000576000263000007c089517e80001bb465908334bba702000132d1148b7a6848f3c0e9000059f85e37fb000000000c800017960001c6a4d0000000000000000d89580a5347fc0d679a506529c040001e600006bf078800122146449d29341104c4369608120885a90b80009828000000000020695f568080005b4800073296a017895ae00000003f8230e000251a000002892083d20001a7706387f00070c7f6d485f38a4163c1e5870098409251704c6a35f0da600011ce90aa1ea06009909cb86e85529fe8743653e6ec207c69f02f29c51a6659f02283221dcb300c30b31d014a80218ed000197a5961b40924800000003566480b6e5070958015000034240000001de419f8000000114485e0daf36d800000013705ba8c096b9096a8a48de15de82ea509c02b0e0994248822e2766c48f2bb9f9e7f51f3
  | 44 => 0x1466f94d47400e67806151c85387424df066c3fa95922ce80005b1042200000000000cf035185966f3000003ed4ca4e58000053ce3177380006b114f887c86500000a9f0000ea062a1d60000096864907ca12115d124ccdfd00026e618200000000000000141e16940008a317ee000205a000082405d25006a6672233b80f07a0067c00018c426d000000000ee00008c8344c0005b01728000170c729000083b8c305d01006284257647d1ce979c8ea8671927256590f13980d919ac84959b59eb06aa817d86b85d2299800097d12397d690c244b9cba00005a02c41058781122c2d2225c5a225e862f8000000000035389a682c976a8bc1158127959e8d79864839123600000007da26ac0b8d30c2790856527115200f199218c9ea68ec88e425f9182817d36e25f184c561886604c10842890d11017d4b033d1cae3fb89c49658ebe281a3ae104de5e9b61f44594668092984f243e11420a0173e60c07ae145c53e2a5a61c85f83536f380000001da227d5c5c0002572292800062d212627263d27b59d082229c4879380001aa019a59985e48bb00006e6800018f879a5748df44b8994c1c59b0a243dab01305a065d5925c32c06fe721911a23701d985d800079280003ef1de82070e2053894c20ff00005688b167232116153800080c836e3e6000047864a060d0e7a0001a987f9222a6089c324980b7661da4628ff0bf77b68bc64fbc5100d70fe631eddfa84914082630a9434c1ec477b24fe5c81fde30e0b964741dda6a3000000025aa6cd2386536020624e269274698f82c2a66e947800091a92f02f9000041212a7000244622613ad7eed930303a49878319ce61a40003dd05ac27f812e8748000914a3d032d0b6645a8bac3cd09089cb265c9518e74915a1f638626bd5c21ca61b706282c015720c9c0b82598c6676ad150260032c3f0011c7069726000185b8879324224985809988ac14b226600000000a30686197800086ec69a00021d83971a4257ba5be1939a2467d0000065000067102315b9832646226a037a000000021701530c27000261a54115f24e3a1925b819a613a008600887cb7129c12483127061149ce139800015564b66c200003ff0ce794589f3695901c6979954000000067e1f4e1288000000245a0000000147221a23d96ba000000058b0f2e1a889ca88f800033780003e800008521cdc05ec000000162a52fa5ae1de8ffa208a08a000000000007086c31ff773fd2326a884ef20a8000498800049f838a68680005b183194139b985ae134a45c1c8a3f098d80f41a162ee0ad875e1b7a0c91d0e73e941a0001d767c3966c696c390185d85f19a96ac44cdc00441455903fa5244bc806c4928f794fd0b9a0500f1c448431a2c98946075e5fe87420d868989e2761a56e2e29aae66a95c8311270a1c28fe44ce000022
  | 45 => 0x3a000072095c6046e5940000000000237e0aee1906988002241a29a8e480000000c051db1c3c3f19d4c13d26340d41b3035203866e1d47d88102ae1280c9c2d0a0e228106b060297c836825424d4978a6bc9db4000224a8438af53be8000012c9138701ad05b2118a327c6584d0858a1d1400000010de1e906620b284532a10d822d4cf284f6400073e400016a016c7c58a147871a008ef25d20000deb72c8666275a26c00001782e000008478eb400004370000072423a2b20001f8b26f95f12f78c10624ce9608d4cf80558e6e96d804778b9406333cd3d60c826333c405c5338d786bb98ee0a80cf205f9a287ba1ee23e70540605044c335d784443d71282f57ba11b88b27631e7d2ac244e89381070000db84a542cf00003b11ee800000016e8728a6223c38d8c3a986b4000110a1b300000000000000000000001190001eca513c00023601280000b4c305549400000007fc800082791b432b13e7000219c00003375d2090d14809db000102070900001d4000000005b6000000017411b8000091e00011e237380006260dba0b887442b4e32672f9d5e1d58d370030fd205445040000000359000012a9c5062713e6359400000001c60efc84848f825000000002abc3c80000000713136400022960000b220000e1c0001a3420b1d6a0000000000220635040007741ebe0000cd5662950c00011a406de0fc7a1145a2db00009b54d90478ccb21338e7865980004fa8918758a6b6377cb300000000978800061d06425b309ec1be2248935855c919087e87597321c80ace64d8c641094a16338109258524b832a4000378800095b0c428451dac70393040001caa7f815fe0001d7f4e400002a70e8632d95b821f0a8e1ed975e8e093e4883984e78c4efe2cd9d98000145639415f62e50c970fb06846d702f02828b346119fb613780000a79cf280c0000000000059200003e7993216b800097f04bc00026ed3b6a62441c169016a612e6b0166732cd3082b225140bd06022bf85218fc9ace2fade9a7aca3609a6839218ba13848b84fe5e20ba211da15a03f57386f514f078c90409bd8c652a8437806c92d4181145011000307bc90fa84104dc4a19b5081ec0aa1944eee50c4000147800082c23b84381c623e89a047cf93cb00000000000cda8c70000000000063416f400020a43fe070e78f0abc100a31a07e8d1000000000000000828141225008b600000002ae17ea000216840102130001d36009a6be000099656a80002c80c324651b5a42821a27bf432890996843df00bc1ec9fa4000264015c049a0000f805d297d851f9fca8d58f023a2196017555784a7dbf4612853d00017440be81c89bf97dc7df9d819c3106a6018a3499e00003ba92d0000143a182460d71f154e00010140820c996cd8000000185a39d93fa0cd4bb670b85d43921a
  | 46 => 0xd20000000000000001c300001dba4dc00013ee3671b1b5881fe200000c34cc599c3fa09260001cce9a418009a29c6497616224d39d344a9087a30504164f69c3e26cc6647ff8c0f323ce2857a995229401e62b65988528058020285830db240954e95be3ba0a8a00025d463e4a7e90304e09b781d07eb8ab4342244c044035805099964e105892430f2647e9d2e56ec000312a11c2d1d88e0000123000176c82700002d82612164155e4f6d13e0000c5e69219225f18a3888e0c8c5f89ee00890000306074a971254a06642de093164452595fa00000b94724d9305b9bc8000121026821f07059d1488d018803583e279b45ba07d847b8e907510000000482956a1610b1c77b800000017cc535800017bc00052892807f480009640cfa33495765d902d66b71da644a15466f800002f421e09ab88b00001e7451c80000c557b80001fa86cc8e3c815000099a9f003bc80006ca0b2a000036094748ea1e7a3e067b0730000269e00019096fc84fa78f800082d224436564c661f00000000370493e3be0ee66501d023ba660228295150003ff8f2c307440890c240489f012a7c821a47f31cb623de4c4642846a227013f3a510dc4ee98f7542961e59705dc4d88ac21e447041fa81d87e106e0381945c7e60e905728dee7f1858c17fcb0c34e47f6646251393b03b608e8ee03152140980000000007a69c809d10000000000033c00000003c68795786800000004420001d8093c800000011a287f89d82d860fe000092a00000002ca101a0000bb47ba9c1c95000492af970629ae4ac0ee08620000000000180497e826e0001ec000000b797180003cf84d10001f740ecdaa474c5148488a084000000000001096fb16f6975a0ce0001c72090055a4e79a0538e96ee82894b673d1e96362ca6c4e196cb1489e6c1ea80000b6e2c438f8000000000072c000000011300000000038dd486ff0c3698f80c10000aa8000000000003fa2ff084e00015989a7002c0000a7a8cfa4fa3ce814700003c19600da87e50f18000135a0b726540001da8000191c15f9cef23685236370b7f23d400065b969c0001770342d33a3a3824a0001b444f60c3e99980f85bc00f201344b84f881482ade57098ba50e07594fe5948ed43ee19164ba800027e54409ca80de59a8d1c000064a58e54927d0800053c8d68065d4b85e71699000000073200000002064000000000007a200009cb71e01c2000267400000000b804d010c0000000251c71ea0aa47d62e00a21cea0bb87d6128c424479800000000002a084b094620026d60e930001f12069057d4b00bab8d3800000000003b400005dd00000d100001265e2d57840003c18ec462825045c604330c4c3ba9c0000047b82be497c3684c88c90000000034d00005c5a1aa2465a940000fd600018485a796180001f465fe19e24
  | 47 => 0x35480c67cf0594218270f807245868e884095680be18a929d4cb0412854a438738021679e87c6000106c9b1800035ea60c57c01a930cc93a11f427c61f992e62280ca6f6a47e2d289a215e85303b3a4ce434165e85423fe2032729728000022015e836c9be47ee0ec200003df0688a329a10c8737a99bc15a1e263aa94f45d38d1b90012b5621000026d93b817d1d7a6759d682fa1be88bfa64623f9b3e27b53b600004383a680000000a1c2f75afa6af85ed78a023281a086a967a41669318aa3d805b11bb0192000237854a8d8400013ac1cb8935000000062503d845813e900006e62c125e000011ae47196c20001b784f1800000dc00040988d73ac13d055310aa17b07c432096621518000795232e00012ce52987ee8d28ab100000005fb01ce00018e20938000000258492393d44e800000000dcc63d00000001dba50009622f2a0044c049eb11c0c505df08448f595c03d59af09b206c287980004209d2274a015b00000d80002036000120052924e64d618b61638114882a56a000208601b917217aa6dc59d88aa56d11c287518ac610c40061502b220c18ec2b48a491c41d451a7e60e33896c34cd0af01f7258e17e1b040a8955c6f022ea877929c2cf13ed3709226531a2d64091f242f9800016200781fa0b6232525828638e538b688f2000186789c857f271c027000000078d0bf60000000581966e479445c265c0003df95d002024e051ea2a28031b7e4cf8600047800000004f93780d6e7788000000000050c00008ca800009540007a60064000026a0a60000768628800008329060b6395310683168d92936a142550a2842528e005dd8aaa4d9879015bcff25a98aa6002030f172812508f15fd2541fe683a9bfa7c21c9e178400099ea0f4000033e40406c609d54900889d162931eb6379c4622b997d00000e5a97e18187ab22224038c582341d2a6ed96563391ea383e148081e4d5352340002fba08e0c4046c00015af98a91027ae8da200010f70a722a940f839619592a577508367e310d4027913486822865fe92300c8124100003bc000000026d577e000147436f80002be17de95d0e24000107c0001e42000007314e0f2024b82cd0001d2061c0aa7508802594a22083fb039800014ba295dfa0384a1463a11974000000026555f800000005b925a89cd64442fd00440b95be23678df17c304a62d249f2074c00006f8a6412e9ed4000271a63fdd4247606247540c9805a8c962a9197c54d89322ea186058480353239c2801f89c66fb84d453a036494b0cbe53791fe1c7265603a1c7602c92dc5b7a6728e6882927801d20000fb4461a33a390a134320c5486020000791c3bb00000001900000000161000018de6da0c3453b08cc0b013c28bf1ae84714000000000020f000000000005d18df26db1a0e4df56410a9a6dd0000
  | 48 => 0xa03a8f794606f999283911df244b1a6c0554a2813888a44550f5060702644f815a61e0a088175a0560f35e2b027158c3b2810f781823620e0f24072e2813c0068e198075e8e103e8383115a8be15ac142a5981da8d550b201b861e8c7041e266c64e165b2e221b886519a46259a9a3878000131249e6338fda8250e920000000000000047c8000776e37431700000001e2418c0f4892f03d56368d146148d9838a91f600022ee7650d2a5f28ae87c89ab61e48cae37d923a7d21b3a14a12c31d89b0e1da184b71607ad245942907b09e819a247a79812be9af11622ac9e86261a0e860a10ce7aa9dea63ece1a51f00008ae13d28dd80003018f8604c400097388e93570e9886b0a9b36f11d662ea0cc494dd0226666b458c80006a2842a2de25ca374214c23107da4c500005080d618d60a569c584352fe41f25a5969590f2312155000039c018d000139a563800040c80007839e503a6c72a19323407c69ae06c60ac60001b0236a40006529e790000000000226a00000002cf80005858000000108000025368f992de741c0000000c46607a6180fa51904f7a03f06ad55629a59d846680004a60baa50a00005d090f500018f63068ce69590000000124e0338000000060b8b784147e99e2a475c000098a6a285e898a8db00003a5df704aed08c992800047a1fb05e6800090f84b332e10f298e1990000111e861257c5f0892877800000000a585371e0a13b9120000090e7388325000000016cc01e7cc031c0d98f6e6178d8781d9a5a1560992819872200010e41604fd8812802900012560000b542b2968b0000c568d9176e000204825b17360481ea49c60d24996a0f600a8d0e17c1224787a2d87881f9a266cda167a0bd46c887181739d4086085e869d0c2897b09076189a0a7429eb86468c1b2b79462143d3156f29b1090c8d3a10454540590808369c7708ca164a0f145a66708faa777cef884d8e8c0001f9c830917c000015d2e3025a6b524142f0168a05da0c8796e0d28119b6a31311f1291850e000208c7552648000134c74e26368e51a407e4594491c09643a89a8627d95c2483902834287ce66d894e3e58f9a315d16e0000f4a66c9e7816a9877482125e7f01d662f852f43f784ad8c524023ca82d409c80008ed000000017a02ae800000001b400000000001625000000028a9638000000048ec1673bd80a27ef0d8f27fcc7687e96302f7ce6c96e000076e105625093ab8e202bc8311a849a3800041fa6f415b800053aa32c54c1cda8ed9dc40000000000216a58d00000a680610001d3c62ca5c21430c6c15e63ce00000008be88d9155a13c12a109a095c0004e085fc4f39094762e39e8401668330a5382415dc085615e0076c09a36cc0da18980790001f321b420220ae87ac00017005b5852a000137200000009791ba23fd2318
  | 49 => 0xc50b1d8e00026f031b882e641800042f000068c800000011b70001d87277c5368c000000000d4038980001b583a89b5000004d450600016b218ae28e0000000000084644e877976780005af0eec3eb264e5980bce81100004c9cc08579c44e428a22e88a0a5458f88b84310000000081e74b0f648b4063663591eb3045d6c3e11c5481b067257b126c2c181ed9389296200017a00020f20cad8242a18646266a08d59922b66bd8c7834494f61e100ea01d0296123983d412835535aa2e690b11181c68000000000031bcdca6269e161aa95823071d3334a25225b2944676be38024d13e52bdcf0a0a080004be000036b0872365dbc2841a41c7db88de039439c8669e3670300ba000000045e0418101138a0000804668a1a888d54022fa940e479167247c12a9092e1b4000188c880138894f23a24da933c9a980004ef0d70000197276425495a30000000053a0000ea489480000ea93184321b9458ee36600019fe1bd07781879b8c0180614402805e40880000fa8ea991de31e12f87c88079d9a98f218a1a0a09263f85997378d5452080000e8000062c141876266ec2b0202415c9c347888e52705046637f944e5090ee4924196c86217aa793109c4e8a6b8146186a95e8000000047e000024209d0e623840ebc000000063980000001f140fae3e4578d01e9c3536800021da38f43381b3812c985022f6f11cbc5a88a0c067c5bc0d280004f703d74c585c6000248a05c645426a061c42980cc7cb0c8420e60785c1064b3d11f9653e913808800002b54e161a51ab8000232022999f000000004cc000000025a63dc0a620c780002d115b029d0b1a00024fc5f982bd00000007d5946e2e7456161cc1387e08bf864e9db187b0d366ec80000001e300000162000000061b80000e98dd400001fe540207a583808a769da720ed1f0480f03e496880e62530b5c000000051fc7e0899148b60d80003e90000240978c49a53178f31bd84301c7006ec372615c098308800000000007c60267063d4c84658e7e96ca56643c039a405813a98a1ce82038654490206077f0111767169448e228a10eca4e6c69a1c0001d1086c8bb211c8000269117e0c3044f8da00000d2e13201f225a1ea0066885a21c8ab9e3a00005d31b001ee2da8a551a2800032d5fda2318a8c000000049e00d08e70ba10000d5e803848c000000013840000000c670000eae93d9df4000094d4f1205c00018f315284b20002308831916c3fd9de62161297000000046f80001578000349923c220800e1ae000000000005fddb5600013cc0925ca86e2800091a08eb80b209858d97981e724a417092ac46f14a89991ada00000003e98c0c4c691e03de24c08a25a68000101260b053c8c110b62350d5085896a4008229e00005661a21f603c424cc3331df800014787ea8776661800056e
  | 50 => 0x28fbe20dc0000000c206bf9b1455b89ac0001a4422514fc95a203452c8a6a0138d383b4800000012e04fc62ad5ad9d4407824e400014262ab89d226783186c9800000005a184b1e1800000006eb869e162d05477318652ba9f2a3ab51a01248000000000035d119e7bc0c7200021c882e114632e40000000000000144379ccd458b9000016b40007431db030911d366810ec55026fd7f10ef034306a42b2d21e5bf91045349d3032456d416d048a7519bea52f156611fe68273515085cd0dbb12912a62b6a5926cb9902000152e00016fa94fc00075705fa05f09bc00013b255f982043180e228e81160c6d2b16af10420000000400832e13a8b0814c80e0001e02a726a21550d8bbe6991ffc0878af4490c8860000ab66e9a13e29797b03749f6683984608601cee0cd0000546800047225323d4891a0000ce89431b7473000000000245848a06a92897903a092584cda41e04c8bfb7dc99821369b8e9270a7c26713d60001ee60539ea833600003598ad08529c40322400079da0807e412185f3a30c00000003838c6022d000000008a8883157a526000018c50cc63921c48b486161c7800077fa0c032dc000205235c0eac0002aec0007ad0514000223900005920d69f1073104c06435d52000019d8140000000000082087d0457063a15f000082a074e6278e345e89daa00002f714d432d2b25e9c848031653685120ff66f24868432371906639323c48ea1ee4023a3f402096497fd80009c48f7656123e8073000074c80b40001a2a68408c094e8000000000000000007ce00006eea47200023a66dc271e7dd800045d1fea81d03549c9cbc2000016800015105d6a29c271413603909e1665176800014661ce90367bf191400000006ea92663eb998c4ac000000001ca00018102d7895600023f837000000e525ac23ec7ab00002d83d7000010992e600000002e380003d9a278024400000022a083e800009d8ba656f19b0422953e73e1e4092c80000000000184cf6a14cdaad79b93060618f324c9459f1f08eb242c932b10d80001b610d60000ab95e7800000013f2940d37400000004bf0e047249ebc169c726000128a54395706cb129433180007be0a803f2878c98206127958e2212002681d5025e00004852ec195a41401da2df9ad2221049c9c40d3c4c4061892b8be300025520000dc400003a26d81ba421920dc00026200001e653ec8e80122c37e00000003138834902922a00000001ff83ff215049471f934440300006bd065a0000ddc17ec00074700a600006d251b26b00ea66ce00000004e48000000000021b1f6c164e55c6f400006d9800071a00000000000494521276cc610167128e16925ba694903a00004c84cbcbe700000000000bd21a49111958000012189dc56f51cb93a263a7010a6f61ac21c06d94ee2398b6860e1ce
  | 51 => 0x5797fc294ce546e08ae4145544298080000000ec01a400003c888ec11e54aa66100003da0000473e0384c9a42451322cc000260439a1fb400004653c2051610fcacd20e9a4e8fa91f856224f8368de586f721744ab987b53810766ab0c7c82f03f61ed20427b193ae4e31fac6439eff5d401d103118d20ef9bac768130e36907604b11a2e51910903d5047a176e0585629b8425d13c832292b290204982f6045401d473e0428a0e6f586fc444200017dc876307a2dc45a003d79f9ba85460e6a0b2c55371b02267d910db26227308f09786640009434691142861d3b298136c0370d6c9bb85ee347a06242f96005210d5f7e298fa0001a8e6a0255e69802ce2aa482636b98ea17987f47398dbd6880ba433cc0538d505f602926cd5afc60a7460dfc7bda11a5c50d764c7800091d61720000ca4641000094665ea00015265269ede1ac9e5c4455f504b617ae925173051a1d884531dd85ed02e62721fba3c5a54409f800000014450000000000038800000000000cec1e820be33016cd0189db613f0a0011215123f711da1078db15c
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x188d8460d72d901000513e5d524cb640400144d9754932d901000613e1d524cb640400184d8754932d901000d23e5d424cb640400188f8750932d90100062361d424cb640416dc0e7550932d9010007035d5424cb640400188d835ca62990100062361d8398a6404001a0d8560e62990100058364e6254a640400188f865c9329901000703995724ca640400160d95989329901000583e59524ca6404001a0f86549329901000583656424c96404001a0d8560e62590100058364e62549640400160d92995325901000523e59724c96404001c0e655c9325901000583656624c9640400160f96549325901000583659524c96404001a0f8654932590105bf03dd9524c9640400103f985d475590100052365e724c9640400160d959c93259010007035cb524c9640400148d97949325901000583656524c96404001c0f725493259010007035c9524c9640400188d874c8215901000683615320856404001a893260021590100062361d32c816404001a0d854cb20590100040fa6054dd9540400103e98151765501000623611835cb630400148f9750932d8c100052365d424cb630400388f8750932d8c105b7039d5424cb6304001c0d7550932d8c100052364a645ca630400188d845ca6298c100062361d8498a630400188f865c94298c10006236197250a6304001c0e655c94298c10007035957250a630400121f985505498c10006136157290a630411d88d845ca4298c10007035cb5250a6304001c0d725494298c10006236117208663040018c9726002198c100062361172c82630400148d929917258c1000523e59725096304001c0e655c94258c100070359572509630400121f985505458c100061361572909630400148d979c94258c1000721e45725096304001c84915c94258c10007035cb525096304001c0d725494258c100062361172085630400148d93dd9745881000523653765cd620400148f965d1735881000623e19745cd6204001c0d759917358810007035d5645cd620400122f98550545881000513657745cd620400148d979d17358810007039d5745cd6204001c0d755d17358810007215d3815cd6204001c8574205735881000523650715cd62040014c9901c5735881000523653705cd6204001a858250963c4010006a16118358b1004001a898460d62840100072150932dd910040010d49760963440100063121c7258d1004001a85825096344010005a46508058d10040016c19220163440100053125d835891004001a858460d6244010006b06018358910040018c4871cd624401000694615639011004001a618558a4044010004b8661620c11004001aa18458830440100072250932dd91004001a898460d6244010006b060e815891004001a63855894144010004b866162cc51004001aa18458b3144010
  | 1 => 0x623a1d320876444001a0d854c821d9110006a24c980087644400188e874cb20d91100068361532c83644400184f85e0f725911000623e1383dc9644400144e9754932591100051325d524c9644400184e8754932591100061321d524c9644400348c97509325911000623a1d424c9644400188c87509325911000703dd5424c9644416dc0c7550932591100062360d72188644400188d8760c621911000683615831886444001a89836006219110006a860580188644400160d93189521911000623219724c86444001c0f655c9321911000703195724c8644400148f97d8932191100052365c624c8644400160d95189321911000583a59524c8644400160c96549321911000683219524c86444001c0e765493219110005a1259328846444001688964c92019110006a2219324806444001aa08648520191100040f660549d9544400103e9815076551100050d644541d9544400148d9219372d8d10006b06058018b6344001c0f65dc942d8d10007031977250b634400121f9855054d8d10006136177290b6344001c0f72d4942d8d1000703dc95250b634400188d84dcb20d8d1000623e1383dc9634400148e975093258d100052325d424c9634400388c875093258d1000703dd5424c9634416dc0c755093258d1000523648645c8634400188d845c86218d100062361d8418863440018c9876006218d10006b060580188634400188e865c94218d1000623219725086344001c0f655c94218d100070319572508634400148f97d894218d100052365c6250863440016c2968862018d100053265c62480634400121f985505418d100061361572908634411d88d845ca4218d10007035cb525086344001c0d725494218d10006236117208463440018c9726002118d10006b048580084634400188d845cb2018d100043565c8148063440018c9874802018d10006b06052008063440011e1922017190d100052364e76dd3624400148d949db73d891000523a5b74dcf624400188e86dd373d891000703dd764dcf6244001c0f7519373d891000631a1871dcf624400122f9855054d891000703dd774dcf624400144f955d373d891000703dd474dcf624400148d949c773d89100053264271dcf624400148f945c373d891000623a1f741cf62440019c373608704c51000668a11821c131440019a184608704c51000668a51821c131440019a194608704c51000668d91821c131440019a064608704c51000670a4d821c131440019c193608704c51000670d8d821c131440019c063608704c51000478e63621c131440011e198188704c5100066860b421c131440019a182508704c5100067060b321c131440019c1824c8704c51000760509321c131440013c192201310c510004f0648804c730440013c192201314c11000613615835cb6404
  | 2 => 0xc001a0d854c821d9130006a24c980087644c0a188e874cb20d91300068361532c83644c00144e97549325913000703dd5424c9644c16dc0c7550932591300050b648655c8644c00182d855c862191300060ba1972548644c00182c865c9521913000623219724c8644c001c0f655c9321913000703195724c8644c00148f97d89321913000583a59524c8644c001c0e7654932191300040f660549d9544c00103e9815076551300050764c541d9544c001ac13260021d8530006b04c980084614c001c0c6519172cc53000583656424c9640c00103f985d4755903043d0724d751d5640c00160d959c93259030007035cb524c9640c00148d9794932590304c583656524c9640c001c0f725493259030007035c9524c9640c00188d874c821590300068361532085640c001a893260021590300062361d32c81640c001a0d854cb20590300040fa6054dd9540c00103e98151765503043e0720c545d9540c00184d855cf74588304762361d739d1620c001c0e755cd7458830007035d5735d1620c00122f98550545883043d8324d54151620c00188d845cc715883000e32601731c5620c001a85844c821984300048de6154152610c001685941c93298430005b0640724ca610c001645959093298430475a1652424ca610c001e0752509329843000781549424ca610c001a85844cb2098430006a161132085610c00123798550545843043d8524d54151610c001685941c93258430005b0640724c9610c001645959093258430475a1652424c9610c001e0752509325843000781549424c9610c001a85844cb20584300063861d20081610c001c0e759d1628c430007059d674586310c001c0c751d1624c030007051d474585300c00144e9754932593100051325d524c964c400348c97509325931000703dd5424c964c416dc0c7550932593100040f660549d954c410f81e8315276553100040f660541d954c40014359115076553100052365d424cb63c416dc0e7550932d8f10007035d5424cb63c410f81e831d76450f1000513e5d524cb648400144d9754932d921000d23e5d424cb648416dc0e7550932d9210007035d5424cb648400103d9815376552100040fa60545d9548410f81c83151765521000523a5d424c96384001c0f755093258e105b7031d5424c9638410f81c831d56450e1000583656424cb6444001a0d8560c62d9110006a260d8018b6444001aa18160062d91100058364c6254b644400160d9518932d911000583a59524cb644400160c9654932d911000683219524cb644416fc0e7654932d9110005a1259328876444001688964c920d91100040fe61751d7644400160d951c932d9110005a1a44724cb6444001689901c932d911000703dcb524cb644400148e9794932d911000703dc9524cb6444001c0d7254932d911
  | 3 => 0x3100623611835c8604c4014c49160d7218131006325c980cc8604c40148f9750932181310052365d424c8604c56dc0e755093218131007035d5424c8604c4018c5722053218131004b4640814c8604c4018c972602311813100513a5d524c9640c401c0f7550932590315b7031d5424c9640c40148e97509325803100703dd5424c9600c56dc0c755093258031004b2648804c5600c40348f9750932d96400061360d7298a659013bc0d645c9329964000583e59424ca659000160d96509329964000583652524c9659000181f7620d7459640004c3648835d1659000160d93989425964000513e59724c96590163c0f76509325964000583652724c96590001c0f425c9325964000703dc9424c96590001c0d7250932596400061361d320856590001a0d844c82159640006924c980085659000184d874cb20596400068361132c8165900cb03c98dd95454e400040fe59859c6439000103d989967190e400040fa62655c2439000103e98995709064032e0e5db80552509000103d98d5372d95400040f663545cb655000142d92d5172d954000703d51724cb655000344f9754932d954000583e51524cb655013bc0d7454932d95400052365d424cb655000141e96150735954000613195821cd65500a188f64608735954000643151821cd655000141e97153735954000507a5c541cd655000188f74608735954000683151821cd655000103e98153725954043e0720c54dc9655000142d9215372595400040fa60545c9655010f81c8315172595400060d150815c9655000181c5421d325954003c33261724c96550001c0c545c9325954000531245724c9655000188e8750932595400050d644541c5655000144c9558d7218d4028523e51635c8635010f03e98d957494d4043e07a1875d8d435000190c756086350d400050d644405d4615000103d9721543185400040f2617550c615000144f9754932185400051365d524c8615016dc0e755093218540007035d5424c8615000103d981d461505402ec0f66365dd150500cb03f9761461901400040f66275186405000144e97549325933000703dd5424c964cc16dc0c7550932593300052365d424ca61cc16dc0e755093298730007035d5424ca61cc00144f9754932d92300051365d524cb648c00348f9750932d92305b7039d5424cb648c001c0d7550932d92300040f66054dd9548c00103e98151765523000623e1383dc9618c00148e9750932586300052325d424c9618c001c0f7550932586305b7031d5424c9618c00160d9590932d913000583654624cb644c00160e9654932d913000583259524cb644c16fc0e7654932d91300040fe61751d7644c00160d951c932d913000703dcb524cb644c00148e9794932d913000703dc9524cb644c001c0d7254932d913000623a1d32087644
  | 4 => 0x9040f0ce98dc932d964100703153724cb659040188d8750932d96410050ea40545c3659040124d92a0f75596410040fa6354dc9659040142d92d5372596410040fa63545c9659040103e97e11525964100703d53724c9659040344c97549325964100583e51524c9659040144e95d8d7298e412d523653635ca639050f03c985957494e41006431d58298d439050f81f861d56350e4130c0f261655d2519040103e9721543582410040fa637550d609040144e9754932582410051325d524c96090401c0f7550932582415b7031d5424c960904038c8874c9205824100583652524cb655040181e76a0f74d9541004c364a83dd3655040160d9318942d954159f039d9424cb6550401c0f42dc932d954100583650724cb6550401c0f7250932d9541007035c9424cb655040184e874c821d954100683611320876550401a493260021d954100613a1d32c836550401a0d844cb20d954100d2325d424c9655040184d835c8621954150f03d91724c8655040144f97d8932195410051365c624c8655040160e96509321954100583259424c86550545c0e7650932195413dc0f26076551535040103d981967190d410040fa60655c243504f78347620554545410040fa60655c2415040160d9590932593310040fe61751d564cc50f41c935d4755933100583656724c964cc401c0d72d4932593310052365e524c964cc53160d95949325933100703dc9524c964cc401c0d7254932593310062361d3208564cc401a0d854c82159331006a24c98008564cc40188d874cb20593310068361532c8164cc40103e9815376553310040fa60545d954cc50f81c8315176553310061361573dd162cc51d88d875ce7458b31007039d5735d162cc401c0d755cd7458b310048be615415162cc50f60c935505458b310062361173dc162cc4018e1815c07058b310051365d524cb648c56dc0e7550932d9231007035d5424cb648c40142d9299572992310060b6157298a648c40182f865c9529923100623e19724ca648c401c0e655c9329923100583656424c9648c40142d9299572592310058364a654c9648c401c0e655c9325923100583656624c9648c40160f96549325923100583659524c9648c56fc0f7654932592310040fe61751d5648c40148d979c9325923100583656724c9648c401c0d72d4932592310052365e524c9648c40160d95949325923100703dc9524c9648c401c0d7254932592312d62361d32085648c401a0d854c82159231006a24c980085648c40188d874cb20592310068361532c81648c40103e9815376552310050764c54dd9548c40103e98151765523100703996645cb318c40144e9754932591310051325d524c9644c40348c97509325913100703dd5424c9644c56dc0c7550932591310040f660549d9544c40103d9815076551
  | 5 => 0x181700000c0000000c0100100000e00401000016008000020180a40a00d01002c038010240040280100800003000000010018020080000000000a0280480900a028008010000280200400006003001000008000000020140580100200408801010004018020020040000401a004010000020000080100000c080080020300180200001400002008000010000040040000b0140080100200000c0100600e00000801002000000010000000580600002c000010040000000000200000000000008000060120000b8020300000080500000405806004000000080320000580b00c00001000000000000030360080080300a0080300000c0340480900000000001006004038010120000000000c0080780d0000040200100200001800000000048010060300a01700000c0700400e0280000001002402800000010008010000200582b00003401002000000040010040040000000e0000080001602801013008024008070020000142e961517218d540054364c545c8635510fc0e631517218d5446523e51635c8635500141e96152739855446623d91829ce615500190c5460a739855400507a58545ce615500103d9815372185540050b64854dc8615500103d98151721855400703151724c8615517348d975093218554487035d5424c8615500103e98151701855443e0720c545c061550014359115170185540040f66054dcb605500142d9215372d81540040f660545cb6055001c0c545c932d81545cd2365d424cb6055121c0d7550932d81540040f660549c7605510f81e8315271d815400507a5854dcd605500141e96150735815446623d91821cd605500190c5460873581540040fa6354dc96590c0142d92d5372596430040fa63545c96590d0f03e97e11525964300703d53724c96590c0160f9454932596430050d644405d66190c0144d9754932986435b7039d5424ca6190c01c0d75509329864300513a5d524c96090c01c0f7550932582435b7031d5424c96090c0160d9494932d954344d83259424cb6550cc9a0c8650932d95435c7039d9424cb6550c01c0f425cb32d954300703d0b724cb6550d1360d941c932d954300703dc9424cb6550c01c0d7250932d954300613a1d320876550c01a0d844c821d9543006924c9800876550c0184e874cb20d95430068361132c836550c0142e96d09721954349e0ba11721886550c0184c865c9321954357f03d91724c86550c0144f97d89321954343d83a59424c86550d51c0e76509321954344e43dd5821cd5450c0141d9615273d964100613995829cf65904b588d6460a73d964100643151829cf659040141d9715273d964100683151829cf659040141d9715173d964143e07a0c54dcb659040103d9815172d964143e07a0c545cb659040142d9215172d964100607153874cb65
  | 6 => 0xb8000c5a490000000017c00026c0018d067000000a024c25129800000000001c50000005cc0a02c000000bcc180001283dcf8001088aa15030086c0011991c761671343f92f1a225e000b4034000128fa2890007e906800036000ad8f339e0fc0ce1000081c000000009480000000d3054908f917164e09202c4778508c421688c000003ee5e600119000000001d014457c0028f90898c962704661a42615d054a390480c1ae3f4820259220000018538e558915d73869400023b2445fc58c3528e1540020624d7caf8cad06c00878a6707a0525183fa381d8590000000b5349e41f42ff0b9033ac6a48483a27c8640008580068aef80011d01c711ef5207f6b313099e03c3f12b186000861704001586614036c000004b5b9b89c6f0000009386b0000006b41b8c24e63bc3c1ca0001cc001e84a843c0ba1c3c22dc5807502d2aa01a3741e7b40000000000083000000000000000000000023417e000c3000511110971d3b5ca34b085d078a048683e0001171e80037c1e88a91ca9a01348cf8000000938000442240000000000037000000694c61820280aa2cc00000000c20000004d0098004049b8000002b2000000003ea000728000001140012c80058c0000000008af00003354849d1280000ac8d800000000801f648821ac98093c67100000000005f2306700021e000000005253280000000051e181ce000000ac1480013cc1e800000e98b12016709e1bb42a212669adaa6686080040106243b8b8c842baca2661c80604a9fd24a0de000812e29e011d832d800085c001b0a00cf8004da82102000000474840002760e02140025a7b8108003d4000000000a0716000000000000000050c00135000000119388000000011324d0009a0c50000009740000d43a000001d83a81c4b7c1146c806000270004fc3a11e000214e304e05096409e4a284078f38000006e055c00000248f84000003f050cdc2e617c2b8c0d06a2c1e5520ca08caa0861d484ca81b348d0ae4462822e8bcdb9233b665c7a0432aa1e4599aa286256944be4441a81ad05116a28000000000a53d9290161ec9b0ab000000bbd3012082c001fc000961460108841acbd9f8435000690da17a7c0f58f600a4681d92437400118a03360000c40001f63c1149c01520000000000058085030294a1c4ea1633c5782680008f0001220a0027640000003b000c719a10437457a844be00000096800150758001720865b000000000000003a20004f951000000288002de2e8898ff3982d4f8a8f0009b0a720e0005e1308473db0000708c0004bac783b8d08489980023d000000df2d1654cda48190690cc00023e44800000000000000ed000648000000000002089c00000000089cc089065800000000c010e1a3000f1157000000a79b547200000048000000001c81313510d800003
  | 7 => 0x26a6651680005329c3cc001298f0e107f49e0014a2850581b4a227403a34c0000039a97002cf737a590ac1c6c8252c002013cc38454e2a0006bc5d4001a20000001c18a8d53ba252da9680ac001b287ad582e0000c4c74000008b8000000005a4a28e04600012897d35095a9c00000053e8b00011400092c000c01903788d19200000000000100fca7d2dd000000003585e41000003217a000004fe771190000002d03e23f0000c33d16cbf63a0c0a641594f40001ac7c00031a6f0002b89a6450004440000010e000311394ec00000093000000000002f400047027c7000000000000000000001ef680528004aa2ec68000396328fa4152ec9313580005e000a8e431aa102a088800023c0000040aa200000039203ed88000e00006321f000000e70000599e4400005266f0c896500c000b59903aa6984b9d20005c81c80000019618c5b372440ff2820006745e09843c278a423a000068001e5000000000521d22e02480034296200256000000ba8004c4000d92572d492c2782fa037fc308002ee0010a0000004c4b704b0b461d158ce2301c800272066000f60004ea39883a5b0007a400000064160000000001f26da912b473e000002980000000000000000000000000990b28cc000298f2000000090000b90010d22048020c0017e8000005300012c0000ddf20004a87a914368000df80020468c0000026e0006380000027b1607d9c600066c000fa7753fcee2021780017e0b87cc4c82603e8847c86c3b469ccb1460009133f000019000001742
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xb00980628008ca248528002e5837800000000000200070141a438009a004030000a8000000001070000c00204a0040421001407530a8c14e730aa8009036a4545c9321855400481b522a2e4996c0aa00280ea6151821cd605500120754ea9b9264b2c8687903a9f94549325964300501b4c2a30539ecb2080280da7151829cf6590401406d10a9c3a65b2c8287c031d192a0f755964100481d53aa6e4992cb2080240ea7e51524c965904018073b32541ee9b2a8200c305c990205321813100601eecc9106ba2cb2000240da9d51724cb6550001407530a8c10e6b2a8000a03a9c54608735954000501b442a10e992caa000240ea9151724c9655010f8064c0a8b9264b2a8000d01150915c9325954000630328c9b043826288002884a76094258d10040018424bb08c1ac48802000c3025d8060d6244010
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x3
  | 2 => 0x5
  | 3 => 0x4b
  | 4 => 0x4d
  | 5 => 0x124b
  | 6 => 0x138b
  | 7 => 0x4
  | 8 => 0x94b
  | 9 => 0x94d
  | 10 => 0x124d
  | 11 => 0x138d
  | 12 => 0xcb
  | 13 => 0xcd
  | 14 => 0x12cb
  | 15 => 0x9cb
  | 16 => 0x9cd
  | 17 => 0x12cd
  | 18 => 0x168b
  | 19 => 0x168d
  | 20 => 0xa0b
  | 21 => 0xa0e
  | 22 => 0x6
  | 23 => 0x130b
  | 24 => 0x130e
  | 25 => 0x24b
  | 26 => 0x24d
  | 27 => 0x144b
  | 28 => 0xb4b
  | 29 => 0xb4d
  | 30 => 0x144d
  | 31 => 0x16cb
  | 32 => 0x16cd
  | 33 => 0xb8b
  | 34 => 0xb8e
  | 35 => 0x148b
  | 36 => 0x148e
  | 37 => 0xe8b
  | 38 => 0xe8e
  | 39 => 0x178b
  | 40 => 0x178e
  | 41 => 0x104b
  | 42 => 0x94053
  | 43 => 0x95393
  | 44 => 0x5253
  | 45 => 0x95253
  | 46 => 0x5393
  | 47 => 0x125393
  | 48 => 0x4953
  | 49 => 0x124053
  | 50 => 0x138053
  | 51 => 0x4e
  | 52 => 0xb5393
  | 53 => 0x145393
  | 54 => 0x124953
  | 55 => 0x138953
  | 56 => 0x94e
  | 57 => 0x95453
  | 58 => 0xb4953
  | 59 => 0x94b53
  | 60 => 0x144953
  | 61 => 0x139253
  | 62 => 0x124e
  | 63 => 0x138e
  | 64 => 0x138b53
  | 65 => 0x139453
  | 66 => 0x9d2d3
  | 67 => 0x9c0d3
  | 68 => 0xc9d3
  | 69 => 0xce
  | 70 => 0x1452d3
  | 71 => 0x1440d3
  | 72 => 0xd453
  | 73 => 0x12c9d3
  | 74 => 0x9ce
  | 75 => 0xb49d3
  | 76 => 0x9cb53
  | 77 => 0x16c9d3
  | 78 => 0x9d6d3
  | 79 => 0x10c
  | 80 => 0x130c
  | 81 => 0x1692d3
  | 82 => 0x12d693
  | 83 => 0x12ce
  | 84 => 0x252d3
  | 85 => 0x12c253
  | 86 => 0x12d453
  | 87 => 0x168e
  | 88 => 0xb5693
  | 89 => 0x168b53
  | 90 => 0xb8c
  | 91 => 0x130a13
  | 92 => 0xa1313
  | 93 => 0xa4d
  | 94 => 0x14d
  | 95 => 0xb8a13
  | 96 => 0xa0b93
  | 97 => 0x14cd
  | 98 => 0xe8a13
  | 99 => 0xa0e93
  | 100 => 0x17cd
  | 101 => 0x198d
  | 102 => 0x134d
  | 103 => 0x24e
  | 104 => 0xb4e
  | 105 => 0x144e
  | 106 => 0x16ce
  | 107 => 0x149313
  | 108 => 0x131493
  | 109 => 0x179313
  | 110 => 0x131793
  | 111 => 0x105313
  | 112 => 0x131053
  | 113 => 0xb4253
  | 114 => 0xb5453
  | 115 => 0x24b53
  | 116 => 0x144b53
  | 117 => 0x16d453
  | 118 => 0x1456d3
  | 119 => 0x184c
  | 120 => 0x148b93
  | 121 => 0xb9493
  | 122 => 0xbcd
  | 123 => 0x2cd
  | 124 => 0x178b93
  | 125 => 0xb9793
  | 126 => 0x104b93
  | 127 => 0xb9053
  | 128 => 0x19cd
  | 129 => 0xe9493
  | 130 => 0x148e93
  | 131 => 0xecd
  | 132 => 0x104e93
  | 133 => 0xe9053
  | 134 => 0x5cd
  | 135 => 0x74c
  | 136 => 0x1a4d
  | 137 => 0x194c
  | 138 => 0x180e
  | 139 => 0x28e
  | 140 => 0x1a8c
  | 141 => 0x56d3
  | 142 => 0xd0c
  | 143 => 0x188c
  | 144 => 0xccd
  | 145 => 0x170d
  | 146 => 0xd0e
  | 147 => 0x188e
  | 148 => 0xd4d
  | 149 => 0x1a0d
  | 150 => 0xcce
  | 151 => 0x170e
  | 152 => 0xd4c
  | 153 => 0x1a0c
  | 154 => 0x198a55
  | 155 => 0xcca55
  | 156 => 0x170a55
  | 157 => 0xcca16
  | 158 => 0x170a16
  | 159 => 0x58e
  | 160 => 0x16c053
  | 161 => 0xcd496
  | 162 => 0xcd4d5
  | 163 => 0x171496
  | 164 => 0x1714d5
  | 165 => 0x2d4d5
  | 166 => 0x5d2d5
  | 167 => 0x5cb55
  | 168 => 0xcd7d5
  | 169 => 0x5ccd5
  | 170 => 0x1a57d5
  | 171 => 0x1717d5
  | 172 => 0x17ccd5
  | 173 => 0x134c
  | 174 => 0xbcc
  | 175 => 0xcd796
  | 176 => 0x180a16
  | 177 => 0xcd995
  | 178 => 0x171995
  | 179 => 0xcc2d5
  | 180 => 0x1702d5
  | 181 => 0x29496
  | 182 => 0xd0cd6
  | 183 => 0xd4cd5
  | 184 => 0xcc5d5
  | 185 => 0xccd16
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 47
  | 7 => 1458
  | 6 => 5209
  | 5 => 5019
  | 4 => 661
  | 3 => 26
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
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 9 => packedAt gbK9 (16+((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 2)*1) 1
  | 8 => packedAt gbK8 (1376+((h/22+packedAt gbK8 (1222+(h % 22)*7) 7) % 80)*7) 7
  | 7 => packedAt gbK7 (61338+((h/616+packedAt gbK7 (53946+(h % 616)*12) 12) % 2440)*12) 12
  | 6 => packedAt gbK6 (278732+((h/2050+packedAt gbK6 (250032+(h % 2050)*14) 14) % 9823)*14) 14
  | 5 => packedAt gbK5 (321718+((h/1969+packedAt gbK5 (296121+(h % 1969)*13) 13) % 7091)*14) 14
  | 4 => packedAt gbK4 (49174+((h/264+packedAt gbK4 (46270+(h % 264)*11) 11) % 1151)*11) 11
  | 3 => packedAt gbK3 (2160+((h/9+packedAt gbK3 (2106+(h % 9)*6) 6) % 63)*6) 6
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xffc0ff81fe07ff07fffe03ffd27d19e8cf3cf
  | 1 => 0xf07ff07fe0ff83ff8380ffc0feda2e67733d33
  | 2 => 0xff87ff8000fffc3ffc00ffff031c307983ce3c
  | 3 => 0x7ffffff00003fffff000003e03f81fc0fc0
  | 4 => 0x7ffffffffffc00000000003ffc001fff000
  | 5 => 0xfff80000000000000000000003fffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x8801100120044004a820145000c08a045045
  | 1 => 0x1050502a2048829081024a80a84a0624312512
  | 2 => 0xad06aa810895682d6804952a03143051828a28
  | 3 => 0x84073ccd5a04203e725601820ba03b01d80f80
  | 4 => 0x847cf779cfe73042018060c33ff4001eff000
  | 5 => 0xce6208061018420840601830c3ffbdfe000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xeeeaeee8eee8eae8eeeaeee8eee8eae8eeeaeee8eee8eae8eeeaeee8eee8eae8eeeaeee8eee8eae8eeeaeee8eee8eae8eeeaeee8eee8eae8eeeaeee8eee8eae8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_15931
namespace PEqualNP.Outside.L_meta_15931
open PEqualNP.Outside.L_meta_15931.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 1 := bs0_3_0
theorem alls0 : ∀ k ≤ 3, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_3 i (by omega) hi
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
theorem bs2_3_0 : Interval s2Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 21 := bs2_3_0
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
theorem bs2_4_544 : Interval s2Atlas 4 544 7 := block_range (n:=7) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 551 := (concat (concat (concat (concat bs2_4_0 bs2_4_32) (concat bs2_4_64 bs2_4_96)) (concat (concat bs2_4_128 bs2_4_160) (concat bs2_4_192 (concat bs2_4_224 bs2_4_256)))) (concat (concat (concat bs2_4_288 bs2_4_320) (concat bs2_4_352 bs2_4_384)) (concat (concat bs2_4_416 bs2_4_448) (concat bs2_4_480 (concat bs2_4_512 bs2_4_544)))))
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
theorem bs2_5_640 : Interval s2Atlas 5 640 26 := block_range (n:=26) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 666 := (concat (concat (concat (concat bs2_5_0 bs2_5_32) (concat bs2_5_64 (concat bs2_5_96 bs2_5_128))) (concat (concat bs2_5_160 bs2_5_192) (concat bs2_5_224 (concat bs2_5_256 bs2_5_288)))) (concat (concat (concat bs2_5_320 bs2_5_352) (concat bs2_5_384 (concat bs2_5_416 bs2_5_448))) (concat (concat bs2_5_480 (concat bs2_5_512 bs2_5_544)) (concat bs2_5_576 (concat bs2_5_608 bs2_5_640)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_0 : Interval s2Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_32 : Interval s2Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls2_6 : Interval s2Atlas 6 0 40 := (concat bs2_6_0 bs2_6_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_7_0 : Interval s2Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_7 : Interval s2Atlas 7 0 1 := bs2_7_0
theorem alls2 : ∀ k ≤ 7, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
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
theorem bs4_3_32 : Interval s4Atlas 3 32 28 := block_range (n:=28) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 60 := (concat bs4_3_0 bs4_3_32)
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
theorem bs4_4_160 : Interval s4Atlas 4 160 5 := block_range (n:=5) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 165 := (concat (concat bs4_4_0 (concat bs4_4_32 bs4_4_64)) (concat bs4_4_96 (concat bs4_4_128 bs4_4_160)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 50 := (concat bs4_5_0 bs4_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 1 := bs4_6_0
theorem alls4 : ∀ k ≤ 6, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_2 i (by omega) hi
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
  · exact alls4_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_2_0 : Interval s5Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 10 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_32 : Interval s5Atlas 3 32 28 := block_range (n:=28) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 60 := (concat bs5_3_0 bs5_3_32)
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
theorem bs5_4_160 : Interval s5Atlas 4 160 5 := block_range (n:=5) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 165 := (concat (concat bs5_4_0 (concat bs5_4_32 bs5_4_64)) (concat bs5_4_96 (concat bs5_4_128 bs5_4_160)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 18 := block_range (n:=18) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 50 := (concat bs5_5_0 bs5_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 1 := bs5_6_0
theorem alls5 : ∀ k ≤ 6, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_2 i (by omega) hi
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
  · exact alls5_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 26 := block_range (n:=26) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 26 := bgb_3_0
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
theorem bgb_4_640 : Interval gbAtlas 4 640 21 := block_range (n:=21) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 661 := (concat (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 (concat bgb_4_96 bgb_4_128))) (concat (concat bgb_4_160 bgb_4_192) (concat bgb_4_224 (concat bgb_4_256 bgb_4_288)))) (concat (concat (concat bgb_4_320 bgb_4_352) (concat bgb_4_384 (concat bgb_4_416 bgb_4_448))) (concat (concat bgb_4_480 (concat bgb_4_512 bgb_4_544)) (concat bgb_4_576 (concat bgb_4_608 bgb_4_640)))))
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
theorem bgb_5_4992 : Interval gbAtlas 5 4992 27 := block_range (n:=27) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 5019 := (concat (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)))) (concat (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 (concat bgb_5_384 bgb_5_416))) (concat (concat bgb_5_448 bgb_5_480) (concat bgb_5_512 (concat bgb_5_544 bgb_5_576))))) (concat (concat (concat (concat bgb_5_608 bgb_5_640) (concat bgb_5_672 (concat bgb_5_704 bgb_5_736))) (concat (concat bgb_5_768 bgb_5_800) (concat bgb_5_832 (concat bgb_5_864 bgb_5_896)))) (concat (concat (concat bgb_5_928 bgb_5_960) (concat bgb_5_992 (concat bgb_5_1024 bgb_5_1056))) (concat (concat bgb_5_1088 bgb_5_1120) (concat bgb_5_1152 (concat bgb_5_1184 bgb_5_1216)))))) (concat (concat (concat (concat (concat bgb_5_1248 bgb_5_1280) (concat bgb_5_1312 bgb_5_1344)) (concat (concat bgb_5_1376 bgb_5_1408) (concat bgb_5_1440 (concat bgb_5_1472 bgb_5_1504)))) (concat (concat (concat bgb_5_1536 bgb_5_1568) (concat bgb_5_1600 (concat bgb_5_1632 bgb_5_1664))) (concat (concat bgb_5_1696 bgb_5_1728) (concat bgb_5_1760 (concat bgb_5_1792 bgb_5_1824))))) (concat (concat (concat (concat bgb_5_1856 bgb_5_1888) (concat bgb_5_1920 (concat bgb_5_1952 bgb_5_1984))) (concat (concat bgb_5_2016 bgb_5_2048) (concat bgb_5_2080 (concat bgb_5_2112 bgb_5_2144)))) (concat (concat (concat bgb_5_2176 bgb_5_2208) (concat bgb_5_2240 (concat bgb_5_2272 bgb_5_2304))) (concat (concat bgb_5_2336 bgb_5_2368) (concat bgb_5_2400 (concat bgb_5_2432 bgb_5_2464))))))) (concat (concat (concat (concat (concat (concat bgb_5_2496 bgb_5_2528) (concat bgb_5_2560 bgb_5_2592)) (concat (concat bgb_5_2624 bgb_5_2656) (concat bgb_5_2688 (concat bgb_5_2720 bgb_5_2752)))) (concat (concat (concat bgb_5_2784 bgb_5_2816) (concat bgb_5_2848 (concat bgb_5_2880 bgb_5_2912))) (concat (concat bgb_5_2944 bgb_5_2976) (concat bgb_5_3008 (concat bgb_5_3040 bgb_5_3072))))) (concat (concat (concat (concat bgb_5_3104 bgb_5_3136) (concat bgb_5_3168 (concat bgb_5_3200 bgb_5_3232))) (concat (concat bgb_5_3264 bgb_5_3296) (concat bgb_5_3328 (concat bgb_5_3360 bgb_5_3392)))) (concat (concat (concat bgb_5_3424 bgb_5_3456) (concat bgb_5_3488 (concat bgb_5_3520 bgb_5_3552))) (concat (concat bgb_5_3584 bgb_5_3616) (concat bgb_5_3648 (concat bgb_5_3680 bgb_5_3712)))))) (concat (concat (concat (concat (concat bgb_5_3744 bgb_5_3776) (concat bgb_5_3808 (concat bgb_5_3840 bgb_5_3872))) (concat (concat bgb_5_3904 bgb_5_3936) (concat bgb_5_3968 (concat bgb_5_4000 bgb_5_4032)))) (concat (concat (concat bgb_5_4064 bgb_5_4096) (concat bgb_5_4128 (concat bgb_5_4160 bgb_5_4192))) (concat (concat bgb_5_4224 bgb_5_4256) (concat bgb_5_4288 (concat bgb_5_4320 bgb_5_4352))))) (concat (concat (concat (concat bgb_5_4384 bgb_5_4416) (concat bgb_5_4448 (concat bgb_5_4480 bgb_5_4512))) (concat (concat bgb_5_4544 bgb_5_4576) (concat bgb_5_4608 (concat bgb_5_4640 bgb_5_4672)))) (concat (concat (concat bgb_5_4704 bgb_5_4736) (concat bgb_5_4768 (concat bgb_5_4800 bgb_5_4832))) (concat (concat bgb_5_4864 bgb_5_4896) (concat bgb_5_4928 (concat bgb_5_4960 bgb_5_4992))))))))
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
theorem bgb_6_5184 : Interval gbAtlas 6 5184 25 := block_range (n:=25) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 5209 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 bgb_6_192) (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)))) (concat (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 (concat bgb_6_416 bgb_6_448))) (concat (concat bgb_6_480 bgb_6_512) (concat bgb_6_544 (concat bgb_6_576 bgb_6_608))))) (concat (concat (concat (concat bgb_6_640 bgb_6_672) (concat bgb_6_704 (concat bgb_6_736 bgb_6_768))) (concat (concat bgb_6_800 bgb_6_832) (concat bgb_6_864 (concat bgb_6_896 bgb_6_928)))) (concat (concat (concat bgb_6_960 bgb_6_992) (concat bgb_6_1024 (concat bgb_6_1056 bgb_6_1088))) (concat (concat bgb_6_1120 bgb_6_1152) (concat bgb_6_1184 (concat bgb_6_1216 bgb_6_1248)))))) (concat (concat (concat (concat (concat bgb_6_1280 bgb_6_1312) (concat bgb_6_1344 (concat bgb_6_1376 bgb_6_1408))) (concat (concat bgb_6_1440 bgb_6_1472) (concat bgb_6_1504 (concat bgb_6_1536 bgb_6_1568)))) (concat (concat (concat bgb_6_1600 bgb_6_1632) (concat bgb_6_1664 (concat bgb_6_1696 bgb_6_1728))) (concat (concat bgb_6_1760 bgb_6_1792) (concat bgb_6_1824 (concat bgb_6_1856 bgb_6_1888))))) (concat (concat (concat (concat bgb_6_1920 bgb_6_1952) (concat bgb_6_1984 (concat bgb_6_2016 bgb_6_2048))) (concat (concat bgb_6_2080 bgb_6_2112) (concat bgb_6_2144 (concat bgb_6_2176 bgb_6_2208)))) (concat (concat (concat bgb_6_2240 bgb_6_2272) (concat bgb_6_2304 (concat bgb_6_2336 bgb_6_2368))) (concat (concat bgb_6_2400 (concat bgb_6_2432 bgb_6_2464)) (concat bgb_6_2496 (concat bgb_6_2528 bgb_6_2560))))))) (concat (concat (concat (concat (concat (concat bgb_6_2592 bgb_6_2624) (concat bgb_6_2656 (concat bgb_6_2688 bgb_6_2720))) (concat (concat bgb_6_2752 bgb_6_2784) (concat bgb_6_2816 (concat bgb_6_2848 bgb_6_2880)))) (concat (concat (concat bgb_6_2912 bgb_6_2944) (concat bgb_6_2976 (concat bgb_6_3008 bgb_6_3040))) (concat (concat bgb_6_3072 bgb_6_3104) (concat bgb_6_3136 (concat bgb_6_3168 bgb_6_3200))))) (concat (concat (concat (concat bgb_6_3232 bgb_6_3264) (concat bgb_6_3296 (concat bgb_6_3328 bgb_6_3360))) (concat (concat bgb_6_3392 bgb_6_3424) (concat bgb_6_3456 (concat bgb_6_3488 bgb_6_3520)))) (concat (concat (concat bgb_6_3552 bgb_6_3584) (concat bgb_6_3616 (concat bgb_6_3648 bgb_6_3680))) (concat (concat bgb_6_3712 (concat bgb_6_3744 bgb_6_3776)) (concat bgb_6_3808 (concat bgb_6_3840 bgb_6_3872)))))) (concat (concat (concat (concat (concat bgb_6_3904 bgb_6_3936) (concat bgb_6_3968 (concat bgb_6_4000 bgb_6_4032))) (concat (concat bgb_6_4064 bgb_6_4096) (concat bgb_6_4128 (concat bgb_6_4160 bgb_6_4192)))) (concat (concat (concat bgb_6_4224 bgb_6_4256) (concat bgb_6_4288 (concat bgb_6_4320 bgb_6_4352))) (concat (concat bgb_6_4384 bgb_6_4416) (concat bgb_6_4448 (concat bgb_6_4480 bgb_6_4512))))) (concat (concat (concat (concat bgb_6_4544 bgb_6_4576) (concat bgb_6_4608 (concat bgb_6_4640 bgb_6_4672))) (concat (concat bgb_6_4704 bgb_6_4736) (concat bgb_6_4768 (concat bgb_6_4800 bgb_6_4832)))) (concat (concat (concat bgb_6_4864 bgb_6_4896) (concat bgb_6_4928 (concat bgb_6_4960 bgb_6_4992))) (concat (concat bgb_6_5024 (concat bgb_6_5056 bgb_6_5088)) (concat bgb_6_5120 (concat bgb_6_5152 bgb_6_5184))))))))
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
theorem bgb_7_1440 : Interval gbAtlas 7 1440 18 := block_range (n:=18) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 1458 := (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 (concat bgb_7_96 bgb_7_128))) (concat (concat bgb_7_160 (concat bgb_7_192 bgb_7_224)) (concat bgb_7_256 (concat bgb_7_288 bgb_7_320)))) (concat (concat (concat bgb_7_352 (concat bgb_7_384 bgb_7_416)) (concat bgb_7_448 (concat bgb_7_480 bgb_7_512))) (concat (concat bgb_7_544 (concat bgb_7_576 bgb_7_608)) (concat bgb_7_640 (concat bgb_7_672 bgb_7_704))))) (concat (concat (concat (concat bgb_7_736 bgb_7_768) (concat bgb_7_800 (concat bgb_7_832 bgb_7_864))) (concat (concat bgb_7_896 (concat bgb_7_928 bgb_7_960)) (concat bgb_7_992 (concat bgb_7_1024 bgb_7_1056)))) (concat (concat (concat bgb_7_1088 (concat bgb_7_1120 bgb_7_1152)) (concat bgb_7_1184 (concat bgb_7_1216 bgb_7_1248))) (concat (concat bgb_7_1280 (concat bgb_7_1312 bgb_7_1344)) (concat bgb_7_1376 (concat bgb_7_1408 bgb_7_1440))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 47 := (concat bgb_8_0 bgb_8_32)
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 4 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 4 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 33, 49),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 8 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 33, 49),(inputs.getD 5 zero, 17, 49)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 10, 26)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeeeaeee8eee8eae8eeeaeee8eee8eae8eeeaeee8eee8eae8eeeaeee8eee8eae8eeeaeee8eee8eae8eeeaeee8eee8eae8eeeaeee8eee8eae8eeeaeee8eee8eae8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (17215835209785207528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_15931.Model.Repr at out
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

def mono : List Gate := [⟨.or,[2,4]⟩,⟨.or,[2,3]⟩,⟨.and,[1,7]⟩,⟨.or,[5,6]⟩,⟨.and,[8,9]⟩,⟨.and,[4,5]⟩,⟨.or,[7,11]⟩,⟨.and,[0,12]⟩,⟨.and,[0,1]⟩,⟨.or,[10,13]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (17215835209785207528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (17215835209785207528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_15931

open PEqualNP.Outside.L_meta_15931 in
theorem PEqualNP.Outside.L_meta_15931 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (17215835209785207528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (17215835209785207528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
