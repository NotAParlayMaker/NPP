import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_12923.Model
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


end PEqualNP.Outside.L_meta_12923.Model

namespace PEqualNP.Outside.L_meta_12923
open PEqualNP.Outside.L_meta_12923.Model
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

end PEqualNP.Outside.L_meta_12923

namespace PEqualNP.Outside.L_meta_12923
open PEqualNP.Outside.L_meta_12923.Model
def gbK8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x841fc41083fe62107f8c420fe98841fc31083fe42107f88420fe90841fc21082fca0107fd0020ff20041fd40083f880107fcc020ff18041fd30083f860107fc8020f790041fe20083f440107f48020f690041f920083fea9885fd5310ff2a6217e54c43faa9885f55310fe2a6217c54c43fea7885fd4f10ff29e217e53c43faa7885f54f10fe29e217c53c43fe87887f90f10fea1e21fc43c43fea5885fd4b10ff296217e52c43faa5885f54b10fe296217c52c43fe85887f90b10fea1621fc42c43fe65887f8cb10fe99621fc32c43fe83887f90710fb20e21fd41c43ea83887f10710ff98e21f731c43fc63887f4c710fe18e21f431c43fe43887f88710fb10e21fd21c43ea43887f08710ffa0621fe40c43fa81887f10310ff98621fe30c43fa61887f0c310ff90621fe20c43fa41887f08310ffaa4217f54843fca9085f95210feaa4217d54843f8a9085f15210ffa9c217f53843fca7085f94e10ef29c215e53843faa7085f54e10eea9c215d53843f8a7085f14e10ffa1c21fe43843fa87087f10e10ffa94217f52843fca5085f94a10fea94217d52843f8a5085f14a10ffa1421fe42843fa85087f10a10ff99421fe32843fa65087f0ca10bea8c21ff41843fc83087f50610fe20c21ff31843fc63087f4c610fe18c21ff21843fc43087f48610fe10c217e50843fe81087f90210fd20421fd40843f281087f10210ff98421fe30843fa61087f0c210ff90421fe20843fa41087f08210ff88421f710843f621087fd5110bfaa221fe54442fca8887f55110beaa221fc54442f8a8887fd4d10bfa9a21fe53442fca6887f54d10bea9a21fc53442f8a6887fd0d10ff21a21fd43443f886887fd4910bfa9221fe52442fca4887f54910bea9221fc52442f8a4887fd0910ff21221fd42443f884887fcc910ff19221fd32443f864887fd0510ff20a21f641443fa82887d50510fe20a21ff31443ee62887f8c510fe98a21fc31443e862887fc8510ff10a21f621443fa42887d48510fe10a21ff40443fc80887e90110fea0221f940443f880887fcc110ff18221fd30443f860887fc8110ff10221fd20443f840887fc4110fd88221fe10443ec20887fd5010bfaa021fe54042fca8087f55010beaa021fc54042f8a8087fd4c10bfa9821fe53042fca6087f54c10bea9821fc53042f8a6087fd0c10ff21821fd43043f886087fd4810bfa9021fe52042fca4087f54810bea9021fc52042f8a4087fd0810ff21021fd42043f884087fcc810ff19021fd32043f864085f94410ffa0821fe41043fa82087f10410ff98821fe31043fa62087f0c410ff90821fe21043fa42087f08410bf28021ff40043fc80087f50010fe20021ff30043fc60087f4c010fe18021ff20043fc40087f48010fe10021ff10043ee20087f84010fd08021fd10043ea20087e44010
  | 1 => 0xf214c3fc42987f48530fe10a61ff404c3fc80987f50130fe20261ff304c3f660987f8c130ef18261ff540c2fea8187f95030bf2a061fd540c2faa8187f15030be2a0617e530c3fe86187f90c30fea1861fc430c3fea4187f94830bf29061fd520c2faa4187f14830ffa1061fe420c3fa84187f10830ff99061fe320c3bc64187f4c830fe19061dc320c3fea2187f94430bf28861fd510c2faa2187f14430ffa0861fe410c3fa82187f10430ff98861fe310c3fa62187f0c430ff90861fe210c3fa42187f08430bf28061ff400c3fc80187f50030fe20061ff300c3be60187f8c030fd18061fd300c3ba60187e4c030ffaa6417f54c83fca9905f95320feaa6417d54c83f8a9905f15320ffa9e417f53c83fca7905f94f20fea9e417d53c83f8a7905f14f20ffa1e41fe43c83fa87907f10f20ffa1641fe42c83dc85907f50b20f6a1641fc42c83fe65907f8cb20fe99641fc32c83fea3907f94720bf28e41fd51c82faa3907f14720ffa0e41fe41c83fa83907f10720ff98e41fe31c83fa63907f0c720ff90e41fe21c83fa43907f08720ffa0641fe40c83fa81907f10320ff98641fe30c83fa61907f0c320ffaa4417f54883fca9105f95220feaa4417d54883f8a9105f15220ffa9c417f53883fca7105f94e20fea9c417d53883f8a7105f14e20ffa1c41fe43883fa87107f10e20bea9441ff42883fc85107f50a20fe21441ff32883de65107f8ca20fe99441fc32883d865107fd4620ff28c417e51883faa3105f54620fe28c41ff41883fc83107f50620fe20c41ff31883fc63107f4c620fe18c41ff21883fc43107f48620fe10c417e50883fe81107f90220fea0441fc40883fe61107f8c220fe98441fc30883fe41107bc8220fd90441ff54482fea8907f95120bf2a241fd54482faa8907f15120be2a241ff53482fea69077d4d20afa9a41fe53482fca6907f54d20bea9a41fc53482f8a6907714d20ae29a41ff43483fc86907f50d20fe21a41ff42483fc84907b90920fea1241ed42483f884907fcc920ff19241fd32483f864907fd4520bfa8a41fe51483faa2907f14520be28a41ff41483fc82907f50520fe20a41ff31483fc62907f4c520fe18a41ff21483fc42907f48520fe10a41ff40483fc80907f50120fe20241ff30483fc60907f4c120fe18241ff20483f640907f88120f710241ff54082fea8107f95020bf2a041be540827ca8107f55020beaa041bd540827aa8107f15020be2a041ff53082fea6107f94c20bf29841de53082bca6107f54c20bea9841dd53082baa6107f14c20be29841ff43083fc86107f50c20fe218417e52083fe84107f90820fea1041fc42083fe64107bcc820ff19041fd32083f864107b0c820ffa8841fe51082fca2107d94420bb28841fd51082faa2107d54420baa8841fc51083fe82107f90420fea0
  | 2 => 0x3fc85207f50a40fe21481ff32903fc65207f4ca40fe19481ff51903fca3205f94640fea8c817d51903f8a3207fd0640ff20c81fd41903f883207fcc640ff18c81fd31903f863207fc8640ff10c81fd21903f843205f94240ffa0481bf40903f681207fd4d40bfa9a81fe53503faa6a07f14d40be29a81ff43503fc86a07f50d40fe21a81ff52502fea4a07f94940fea9281fc52502f8a4a07fd0940dfa1281fe42503fa84a06f50940fe21281ff32503fc64a07f4c940fe19281ff51502fea2a07f94540fea8a81fc51502f8a2a07fd0540ff20a81fd41503f882a07fcc540ff18a81fd31503f862a07fc8540ff10a81fd21503f842a07fd0140fda0281fe405037c80a05f95040ffa9881fe53102fca6207794c40af29881fd53102faa6207754c40aea9881fc53103fe86207f90c40fea1881fc43103fea4207f94840bf29081ee52102dca4207f54840bea9081ed52102daa4207f14840ffa1081fe42103fa84207f10840ff99081fe32103fa64207f0c840ffa8881fe51102fca2207d94440bb28881fd51102faa2207d54440baa8881fc51103fe82207f90440fea0881fc41103fe62207f8c440fe98881fc31103fe42207f88440fe90881fc21102fca0207fd0040dfa0081fe40103f480207f50040dea0081f940103fea9985fd5330ff2a6617e54cc3faa9985f55330fe2a6617c54cc3fe87987f90f30ef21e61fd43cc3ba87987f10f30ffa9661fe52cc2fca5987f54b30bea9661fc52cc3fe85987f90b30fea1661fc42cc3fe659877ccb30ff19661fd32cc3ba65987f0cb30ffa8e61fe51cc2fca3987f54730bea8e61fc51cc3fe83987f90730fea0e61fc41cc3fe63987f8c730ef18e61fd31cc3f86398770c730ff90e61fe21cc3fa43987f08730ffa0661fe40cc3fa81987f10330ffaa4617f548c3fca9185f95230feaa4617d548c3f8a9185f15230bea9c61ff438c3fc87187f50e30fe21c61ff528c3fca5185f94a30fea94617d528c3f8a5187fd0a30ff21461fd428c3f885187fcca30ff19461de328c3fa65187f0ca30ee19461ff518c3fca3185f94630fb28c6176518c3faa3185f54630faa8c6175518c3f8a3187fd0630ff20c61fd418c3f883187fcc630ff18c61fd318c3f863187fc8630ff10c61fd218c3f843185f94230ffa0461fe408c3fa81187f10230ff98461df308c3f661187fd5130bfaa261fe544c2fca8987f55130beaa261fc544c2f8a8987fd0d30ff21a61de434c3fa86987750d30fe21a61ff524c2fea4987bd4930b7a9261fe524c3faa4987f14930be29261ec524c2d8a4987fd0930ff21261fd424c3f884987fcc930ef99261fe324c3fa6498774c930fe19261ff514c2fea2987f94530fea8a61fc514c2f8a2987fd0530ff20a61fd414c3f882987fcc530ff18a61de314c3fa62987f0c530ee18a61f
  | 3 => 0xa818ff55031beaa063fc540c6f8a818df94c31ffa1863df430c7fc8618ff50c31fe21863dc430c7fea418ff94831bf29063fd520c6faa418ff14831ffa1063fe420c7fa8418ff10831ff99063fe320c7bc6418ff4c831fe19063dc320c6fca218ffd0431fba0863fe410c7fa8218ff10431fa20863ff310c7be6218ff8c431fb18863fd310c7ba6218fd4c431ffa8063fe500c6fca018ff54031bea8063fc500c7fea990dfd5321ff2a6437e54c87faa990df55321fe2a6437c54c87fea790dfd4f21ff29e437e53c87faa790df54f21fe29e437c53c87fe8790ff90f21fea1e43fc43c87fe8590ff90b21f721643fd42c87da8590ff10b21ff99643fe32c87fa6590ff0cb21ffa0e43fe41c87fa8390ff10721ff98e43fe31c87fa6390ff0c721ffa8643fe50c86fca190ff54321bea8643fc50c87fea910dfd5221ff2a4437e54887faa910df55221fe2a4437c54887fea710dfd4e21ff29c437e53887faa710df54e21fe29c437c53887fe8710ff90e21fea1c43fc43886faa510ffd0a21ff21443fd42887f88510ffcca21ff19443fd32887f86510df94621ffa0c43fe41887fa8310ff10621ff98c43fe31887fa6310ff0c621ff90c43ef21887ee4310ffd4221ff284437e50887faa110df54221fe28443ff54486fea890ff95121bf2a243fd54486faa890ff15121be2a243ff53486fea690f7d4d21afa9a43fe53486fca690ff54d21bea9a43fc53486f8a690f714d21ae29a43ff43487fc8690ff50d21fe21a43ff42487fc8490fb90921fea1243ed42487f88490ffcc921ff19243fd32487f86490ffd0521ff20a43fd41487f88290ffcc521ff18a43fd31487f86290ffc8521fb90a43fe21487dc4290ffd4121bfa8243fe50487faa090ff14121be28243ff54086fea810ff95021bf2a043fd54086faa810ff15021be2a043ff53086fea610ff94c21bf29843fd53086faa610ff14c21be29843ff43087fc8610ff50c21fe218437e52087fe8410ff90821fea1043fc42087fe6410ff8c821fe99043fc32086fca210ffd0421ff20843fd41087f88210ffcc421ff18843fd31087f86210ffc8421f790843fe21087ec4210ff48421f690843f521087fea010ff94021bf28043fd50086faa010ff14021ffa9e81fe53d02fca7a07f54f40bea9e81fc53d03fe87a07f90f40fea1e81fc43d03fea5a07f94b40bf29681fd52d02faa5a07f14b40ffa1681bf42d03fc85a07f50b40dea1681fc42d03fe65a07f8cb40fe99681fc32d03fea3a07f94740bf28e81fd51d02faa3a07f14740ffa0e81fe41d03fa83a07f10740ff98e81fe31d03fa63a07f0c740ff90e81fe21d03fa43a07f08740beaa481ff53903fca7205f94e40fea9c817d53903f8a7207fd0e40ff21c81fd43903f887207fd4a40ff294817e52903faa5205f54a40fe29481ff429
  | 4 => 0x7fcc832ef99065fe320cbdc64197f4c832ee99065ed320cbfea2197f94432bf28865fd510cafaa2197f14432ffa8065fe500cafca0197f54032bea8065fc500cbfea7a0ff94f41bf29e83fd53d06faa7a0ff14f41ffa1e83fe43d07fa87a0ff10f41ffa9683fe52d06fca5a0ff54b41bea9683fc52d07fe85a0ff90b41fea1683fc42d07fe65a0ff8cb41fe99683fc32d07fea1a0ff94341bf28683fd50d06faa1a0ff14341beaa483ff53907fca720df94e41fea9c837d53907f8a720ffd0e41ff21c83fd43907f88720ffd4a41ff294837e52907faa520df54a41fe29483ff42907fc8520ff50a41fe21483ff32907fc6520ff4ca41fe194837e51907fe8320efd0641fba0c83ff50907fca120df94241fea84837d50907f8a120ffd4d41bfa9a83df53506bea6a0ff94d41fea9a83fc53506f8a6a0f714d41ae29a83ff43507fc86a0ff50d41fe21a83ff52506fea4a0ff94941fea9283fc52506f8a4a0ffd0941ff21283fd42507f884a0ffcc941ff19283fd32507f864a0ffd0541fba0a83fe415077c82a0ffd4141bfa8283fe50507faa0a0ff14141be282837e54107fea620ff94c41bf29883de53106bca620ff54c41bea9883dd53106baa620ff14c41ffa1883fe43107fa8620ff10c41ffa9083fe52106fca420fb94841b729083fd52106faa420fb54841b6a9083fc52107fe8420ff90841fea1083fc42107fe6420ff8c841fe99083fc32106fca220ffd0441dfa0883fe41107ec8220ff50441dea0883f541107fea020ff94041bf28083fa50106f4a020ff54041bea8083f950106f2a020ff14041ffaa6637f54cc7fca998df95331feaa6637d54cc7f8a998df15331ffa1e63fe43cc7bc8798ff50f31eea1e63fc43cc7fea598ff94b31bf29663fd52cc6faa598ff14b31ffa1663fe42cc7fa8598ff10b31ff99663fe32cc7fa6598ff0cb31ffa0e63f741cc7fc8398ff50731fe20e63f441cc7fea198ff94331bf28663fd50cc6faa198ff14331ffaa4637f548c7fca918df95231feaa4637d548c7f8a918df15231bea9c63ff438c7be8718ff90e31fea1c63fc438c7b88718ffd4a31ff294637e528c7faa518df54a31fe29463ff428c7fc8518ff50a31fe21463ff328c7fc6518f78ca31fe99463fc328c7b86518df94631ffa0c63fe418c7fa8318ff10631ff98c63df318c7ee6318ffd4231ff284637e508c7faa118df54231fe28463ff544c6fea898ff95131bf2a263fd544c6faa898ff15131be2a263ff434c7fc8698f790d31fea1a63dd434c7f88698ffd4931bfa9263fe524c7faa498ff14931be29263ff424c7fc8498ff50931fe21263ff324c7fc6498ff4c931fe19263ff414c7fc8298ff50531fe20a63ff314c7ee6298ff8c531ef18a63ff504c6fea098ff94131fea8263fc504c6f8a098ffd5031bfaa063fe540c6fc
  | 5 => 0xe43ffa1c87bf4390fbe8721ffd4a43ff294877e5290ffaa521df54a43fe29487ff5190ffca321df94643fea8c877d5190ff8a321ffd4243ff284877e5090ffaa121df54243fe28487ff4350fbe86a1ff90d43df21a87ff5250efea4a1ff94943fea9287fc5250ef8a4a1ffd4543bfa8a87f75150eeea2a1ff94543fea8a87fc5150ef8a2a1fd14543ba28a87ff5050efea0a1ff94143fea8287fc5050ef8a0a1df95043bf29887ff4310f7e8621ff90c43ef21887fd4310f7a8621f750c43ffa9087fe5210efca421ff54843bea9087fc5210ffea221ff94443bf28887fd5110efaa221ff14443ffa8087fe5010efca021ff54043bea8087fc5010ffea7a17f94f42bf29e85de53d0abca7a17f54f42bea9e85dd53d0abaa7a17f14f42ffa1e85fe43d0bfa87a17f10f42ffa8e85fe51d0afca3a17f54742bea8e85fc51d0bfea1a17f94342bf28685fd50d0afaa1a17f14342beaa485ff5390bfca7215f94e42fea9c857d5390bf8a7217fd0e42ff21c85fd4390bf887215f94a42ffa1485bf4290bde85217fd4642ff28c857e5190bfaa3215f54642fe28c85ff5090bfca1215f94242fea84857d5090bf8a1217fd4d42bfa9a85fe5350bfaa6a17f14d42be29a85ff4350bfc86a17f50d42fe21a85ff4250bde84a17f90942df21285ff5150afea2a17f94542fea8a85fc5150af8a2a17fd4142bfa8285fe5050bfaa0a17f14142be282857e5410bfea6217f94c42bf29885fd5310afaa6217f14c42ffa1885fe4310bfa86217f10c42bf29085ff4210b7e84217f90842f721085fd4210b7a84217b50842ffa8885fe5110afca2217f54442bea8885fc5110bfea0217f94042bf28085fd5010afaa0217f14042ffaa6657f54ccbfca9995f95332feaa6657d54ccbf8a9995f15332ffa1e65fe43ccbfa87997f10f32ffa1665fe42ccbdc85997f50b32f6a1665fc42ccbfea3997f94732bf28e65fd51ccafaa3997f14732ffa8665fe50ccafca1997f54332bea8665fc50ccbfea9195fd5232ff2a4657e548cbfaa9195f55232fe2a4657c548cafaa7197fd0e32ff21c65de438cbfa87197750e32fe21c657e528cbfe85197f90a32fea1465fc428cbfe651977cca32f799465ff518cbfca3195f94632fea8c657d518cbf8a3197fd4232ff284657e508cbfaa1195f54232fe28465ff544cafea8997f95132bf2a265fd544cafaa8997f15132be2a265ff434cbfc86997f50d32fe21a65ff424cbfc84997f50932fe21265ff324cbde64997f8c932ef19265ff514cafea2997f94532fea8a65fc514caf8a2997fd4132bfa8265fe504cbfaa0997f14132be28265ff540cafea8197f95032bf2a065fd540cafaa8197f15032be2a0657e530cbfe86197f90c32ef21865fd430cbba86197f10c32bf29065ff420cbfc84197b90832fea1065ed420cbf88419
  | 6 => 0x6e52ec7c8cc0006f28c815e00019604ad7891000000000000200400000000000000100200600000400b00100000100700100901100300200100000700200400000300b00900100000000800d00600100000d00200000300200100500400400000900000400801200200001100900300100300200a00000400400200800700200100401700000900e00000000800100500101b00000200d00000300200100700000b00d00000d01800000100100000300300000300000400300900400001201700100400000001b00000a00001401800600100000100c00300000300401000000100000000500100900800300c00400300000000900400000600100000200100200900000000200000d01502300000000500f00500000600901600000300f00600000000100000400100500b00100001200100000601400000200001300700200200600300000900200200401c00e00000300d00000700000100001200200600000500300100700000000100000901500e01200100600000600500000b00900000100000000000000900000000000100400600100000500500b00600100001100000301a00200000200100200100600e00100300300a00000800000100700600400000600d01200500100200200001400000700201000101200000700901100000100000600000500e00700000000500800000700500800200700200400100300000303800900000600000500001500302500200000300000200600000000100000000100700101000000100200001300200000103001300900200500200000600202600700000e00100000200200000100000300100000600600d00100000000501800100000700000100000000101400300000300300a00400300000300000500001800500c00a00000400200a00300000700a00600100000900100a01601500401a00000201b01100200000200000400401600200000101b00000200a00400600200000101000600400400100000700100801e00b00800000201d00e00b00400300500000600300000200000a00700a00200300601400000000700d00000900d00100200000100400000001201300000600100101d00900200200300800000300200f00700a00200300000200c00500000a00001100800400000100000d00000b00800000000200400200100000600000700b00000701300000300000500000000100900000100500200100000200200100100100000800100000601300000000500000000900a02200000200000700100400100000b00000200300801500600000500100000c022001002002000000ffa9687fe52d0efca5a1fb94b43b729687fd52d0efaa5a1fb54b43b6a9687fc52d0ffea3a1ff94743bf28e87fd51d0efaa3a1ff14743ffa8687fe50d0efca1a1ff54343bea8687fc50d0efaa921df94
  | 7 => 0x4458ba867e0d24a07c26a800003ac9a00093600a0000002a41b00002603f6474328b9c5f2b0c59c30c31a07600000000000070835428242a7ea2e00000001ccd7093a128a1488a0000000000000000000000000005be0000000000009380b05d4506a3c000a40046d82232d8662a038a66a58000470000b32d1e91e7da6c6b9e64ec1c9a81d47e6dd27a0784e3021c7a8d5c37e582000dd800c6125bc1926bec400002e4534000000686c0e000b5e28e1ce5242bc60a608000c1600862ce1094cd7a41e0007e200058c000d58000b5254c70e000bf2d923c80f6000c9400073c986000a3ea261460fc8500b2cd60000442c8430cac7b0cda1840545388668a0bfaa4cbc6da89640e69481d69eabda8089b05080005ac87280cb7200058a5e66c8000da4bb62f4d6220c14cdae43e4cc000000000000000000000000314bfc1a035ed40000bb865005642e336000bc80b855e660d687525507c0350c4a9766c4a289b4a4a4e60006ace542aaa882d89e8e580000e4d5a00010a4cacfad029fad9854872e8aea1e8b2cce6ec1d2914ac225e2fc6a632a4e42ccb6468a87670c01e096e36270512a720007d27385d6cb21b214a3b4a7483c5e07500004720eedaa61c3ac99ed76c4cac6570e12602420ce052a3d012a7680d01be2cecf4000a123620000009f682a5dc000000b4c00000095a000000000e5a00025c13a000000dc43c4cc0cba0000004e21a8a0e886b225de0000e062275a27e0000000a60a80000002746f00000008020008fad6e000b7a448766000000000e3c60018ed74120000000000dcc000098438b0600028089801000000000000041000000068e16800094ac988e8bde5fe00027c39e8ca358e2800079c000000870bbe2e63d4b62af09d80022eca9009a2640fe4fc000814d848c6dc60009c2000620424cb038eba67a6ccca0a2f6ae2000700592000ab00280ba0001984d40009ae0000004940004ae0007de01ab8c774610c4467444cc68658cec0001f07825fc71cad87b2d8e0000000006d4e5200000007429e2c6684d6c53a0001640c2000ddc5c8000000004d94000000bc07b8b18caa0009089cc40e0000000008d27607ae3cc0002be9f89b89166b62423ee578d2ac2aa32a9ae2c0000bc00049a5400000001fce0600080ae18000000e3282e02c0003a00003fc2ea0000004421deaf465c878d46368000492b00594a5a97e000078e40c6cb58aca0c400066c2d0a7c206cde0000002b8e2a3b62dc000180000000c72918000478000000e6699c8740000007b655616c000b1e8ec000b16d5417a4e0e003ae000abeb2e87e77acc8db69aca9c53e000000adedbe000aaa2304b6b4adc84185f0972de89d07360682201e06940225a264c4a8c80216c62c309201ea000000ae8522740780e561528c43dadf2b963905020c09
  | 8 => 0xae63a431e6489348ce0ae4864a4e384340002fe000e080000000b4000af2e2209e6a400023898a444000000000000ad2392aae000cd400050063a0006d86cc0009d4838baa7acbe83ec5ea9e22b41f4c66000000000c0c1ee0000005360000000345b6df823a000000000000dc0b90000000bae00054aabac90162ca2b66d1693031c8682da018cb47ecca611a67ac2881e2b0d56e50464db882800016ad10bfe8400b60245d09e6deedb0d008f67dc61ed7e4c05b4be06bca2430a000000000e268fc6de498800dda3787e80006ea86e00026e748b7600e000d3e1745845ce000404000bea71e1b64f84c8cf852cb3e32ed060002fa00039a19a00012ec360008dcbca0000003f2c008e656ae607cce4aafa7e4d0a254d18b2858e74edd000054e3b8b440f808447c000ba25cca2e088836c5c000b100aa33800049e00000000064a372000bd60000000000006b8b2038cbe6000d8a518b300404dc79025a0001160002721fe0002e80da6d0aa4b428a20006eeca0c880000000000264c6000c5400032c000bd4b8a51cde600042885a0008f4e620001e440a0008300e843204e74c70a7f6932000892552796d0e000c7ac84b542284b4158ac07b49540524aa69ecae572000000398268d906b43a63be182598224a0ca70aec53c7faad0258bd03e416eb1a63e48e9d281cd1c6e4000d4aa960001c23fa8ee000b38ae03b023c22273005c000c82000a8200010c762b9a00000030ea5433a8c0ba0804bba0000bedea00000085257c346c7e248000676716cf623600045c0000004d200000000041c4768fe984acc4be8bcd887ce87ae02000af6c7626c81a56cbbcb268da0646ce6e8720208d32bac33e000a080f09e4cbc2a885eab68269681a61c4000d34000000bb017ce1ca2278c408c5a2f8cd837a75e140a022d4cdc7ee00003c640000000172000000000c0a37000000085c000000000520dce04837c000c324eed5242c8d89242b60dc8243e8000000a6838089400048c0006f493c94e48808e5caaf80000007720000008e41ca0009c4d1ad80b2c402d6421a8a83ba4f45a00007e0a8a000000000cfe6c236ecfc73a14469c526000d4c6aa396df04c4388b08a422881006e09a6000000a4e1ace4ec18000dde000962000000000d96a1610ecd0bf60008e2000aa08540000620000000001243e2de2b883020a0000a3a000e5ccd238ac141881e266876e9de88877ecc450ae5edb4c3a69ab74966000000616386ab24462c2718bf8bce15457a0008605a4d2cadce1ea8000045a9ecdfcc6a7860001f2bd26b2b34b6e1ba7c40720009fc2120005963e0b86000000a6400000000056084e1662024ce156000000ce41343b23f81364e81ae86c0000002900005c0000000b1400019e76a1267549821fa000bcc80661a7a4c2cd726b0000000c7
  | 9 => 0x26626256778ba446a466190c22000320590a00a1a0d8a84000a9e0000000000000005b25e400000000013c92a000d30dbc0000000000004ec2ca834b0ad22734d8c9f06d21040008840000000007d675cdb27268903645c457ec9cd1400000000068c310c50042770000624000d6a00040c000d480007a23d20003fe41670464406e9809dae0cd4272c4f65e28de1b894606ace2a344d6864ab80009700000000002860000000f2ab40001308a60000005b00000000000000000004909aa5c22f0cf20a40008f2000000a484ac44a690374a5c7146feb68a7e2766423d643a330000cb678eaeaa3089c0c8000000000c48000974436a2c00000059e5160000004da2ee266000000000b4e3940003a80003563827bcb8098eca40608489425549c6a8651ab6c44e90e000000544a8c000d2e00000066200024006600000034a306586b921aa4a2bb200000002a6a096a6569f4d20122558c1ed389be6720ca000d1286a00067872a728680000000b942a04de3e6dd4812dfa7ba0000000000004808b45a834c6c0d9ae4260600046c54208a0002c05f67c81c076435c304a6226a1c63ca88218c566106000a6ccf01b440600000046218a2a611248413e02e81877c45e99a8b80003ea9a49880000000c693e12c6d67f8da600000027a000c968426a200065a0867c647e8d00820000000d6c3c5d80900000000000001184965f4012000c42562798440000000880d2833c5046ca88e08c8d6000000ce60007fce0a00097ca44000da2a8eda03c0366a189440801c803eb5c000c92e0e000b1c0006fc5ae8160d4a204fa900cc20002d6ca800034050e142940d3651e000000000b509ba4b8cee000000050000b0200078800036c98cc52e34e4c00000002032274222c00007c000a6000088cad6b700000000ea614000014a92a10ace956be2aee4f2dac6fa692000d50a460000000005ec8d4000c7800052821e2920004d89e071220a05a1bc00000000013800024e5d20000003d8aacdc24684bc7f08c200017e3420a2a563aa6989f2000000724960c6401636ad0c1ec5b8000e6466e746000844000000000000e3ad269bc9ee29ce20000000710dcac343de34e34816045000000000062e0008be9980000000000000000006185c600000000035a4602520006da9dc456564922a6a1864d02a2c10332c2620e0000002de000000de0bec000000a040002d2000aa2234652000000756696214d5e574298bf4a7acb819483e0000008320009960004f0b469a21a20007944b0030632c46000776c8c5e83dc00060e7aab82ac4b5a1027fed7cb6ac021d0636b24094bd8682262070532688a386e266a3c2d9c902c0660c06c8a42ba148000b048aa72203611000000092e3ce9a028a7f2ceadf4278454c4e50cc04d080002e20000008f00003bc24491c000
  | 10 => 0x23eb3c90424c70609c87c9c005e452c8eb4884ab8e2c4b7ce143261a4dd6950c24e2e0fa41455a170d44a6e0ac79e6f80005a689ad66000422000dec000ac8b56000bdc9d64bac58000e24a50000928d24df6ad46dc670058856c6ebf0b3a204b406bae1a000a063527449b209292610882200031229ae04114000666a9490a1788b6b60630000000000c084008ac8b00001da9920003249b69cad4e132abc1f60327d4b78c129780005ba250732218a1c6f6588412000c2e0000000e2000e46000654000000d3a6280007d05da92c6465108e047a0008ba4b29fe97a56ecbecca29624a000000000000000000c9e59a75878a6e6000344000dba426384a5e91a0004eaa98000000c703c63a2634638000000afe07e000000000994000ae4bb40000000dee161dc76c000000000482b2a318b7ee4484c83a79229404c24600000080e00082c11ca7615000095c5eec60b0e0ecbc2b844a643cd04dfe6649ce5fa73ed3c8963341762107d870207a000604ada2841d83082f2952a2aafc20096c000858aa891200000619c3f086228c000de400063cbe46ae0000005809c899014e9061e8bc41f8c380cc00000000000054690c8f88ea00000095e2b2000c8aa525f84c271a81022e15c5763f411e7ca530376c5e7be00000039c514c56aa601c0f4c1a48ae3ee4874a49ccc6d6056867ca7855c2aebee79ac2036000000000065e1e64feb9822ab365aa300c869582acc3ed9e82046e316b12a367f484615a89ece841a0ce2
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x6320427e658c8109f596320427c658c810d7d4e320435c538c810db94a320436d528c8109fd95320427e654c8109f595320427c654c810d794d320435d534c810db949320436d524c8109fd94320427e650c8109f594320427c650c810d7d4c320435c530c8109f992510427d64944109f98e510427d63944109f98a510427d62944109f597410427f65904109f596410433e5490410cf55241043765190410be98241042f960904109fd9541042df6350410b718d410437651504109fd94410427d6510410cf950410433d5410410b798c41042dd6310410bb98841042ed6210410ed50441042fa6010410be580410427d65cc410dd947310427f658c4109f596310435e538c410d754e31042fa608c410be582310427f654c4109fd94310427d650c410d794c310435d530c410dd94431042fa600c410be580310427d65c84109fd96210427d6588410db94a210436d5288410dd94621042fa6088410be582210427f6548410b7d8d21042dc6348410dd945210427f65084109f594210436e5208410db54821042fa6008410be580210427e64940109f592500427e6394010d798e500425e63940109f58e500435d63940109758e500427e62940109f58a500427d61940109f597400427f65900109f596400433e5490010cf55240042f66190010bd586400437a50900109fd95400437a50500109fd94400427e65100109f594400427c6510010cf950400433d5410010b798c40042dd6310010bb98840042ed6210010bd98440042f561100109f597300435f53cc010d714f300427f658c0109f596300435e538c010d754e30042f6618c010bd586300427f654c010d7d4d300435c534c010bbd8930042ec624c0109fd94300427e650c0109f594300427c650c010d794c300435d530c010bd98430042f5610c0109f597200427f65880109f596200436e5288010db54a20042f66188010bd586200427f6548010b7d8d20042dc63480109fd94200427e65080109f594200427c6508010af99020042bd6408010b798c20042dd6308010db948200436d5208010bd98420042f56108010dd597100437754c4010dd553100437653c4010dd14f100437752c4010dd54b10042de6384010b758e10042f56184010dd94610042f96584010de59610042796584010ded5210043795484010f698e10043d96384010be586100437a5184010fc946100427f6544010bdd95100437765440109dd9510043775444010dd55110043765344010dd14d10043775244010dd54910042f76044010dd94110043f24044010fc50110043f23044010fc4c110043f32044010fc08110042fb6544010ded95100427b6544010ded5110043795444010bed8510043f36144010de94510043f25144010fc90510043f14144010fc8c510043f13144010fcc8510043f02144010
  | 1 => 0x43f35084110fc90210443f140841109f98f540427d63d50109f98b540427d62d50109f987540437661d50109f983540437a60d50109f596540433f54950109f98e540427d63950109f98a540427d6295010cfd91540427f63550109f18d540427f62550109f189540427f61550109f585540427f60550109f581540433d5415010b798c54042dd6315010bb98854042ed62150109f990540433e64150109f98c540435e63150109798c540427d6315010d758c540425d63150109f988540436e62150109b988540427d6215010db588540426d62150109f984540437661150109d984540427e6015010de980540427a60150109f993530427d64d4c109f98b530427d62d4c109f987530437661d4c109d987530427e60d4c10de983530427d6594c10d7d4e530427e6494c109f592530427e6294c109f58a530427f6454c109f191530435f6354c109fd89530427c6254c109fd85530427d6154c109fd81530427d6054c10af99053042bd6414c10d754c53042ee6214c10bb588530427e6414c10cf990530423e6414c109f590530433d6414c108f590530427e6314c10d798c530427e6214c10db988530426e6214c109f588530436d6214c109b588530427e6114c10dd984530427e6014c10de980530427f65d0c109f997430427d65d0c109f197430433e54d0c10cf55343042ee62d0c10bb58b430427f6590c109f996430427d6590c109f196430435e5390c10d754e430427f6550c109f995430427d6550c109f195430433e5450c10cf551430435e5350c10d754d43042f76150c10bd185430427f6510c109f994430427d6510c109f194430427e64d48109f593520427e63d48109f58f520427e61d4810dd987520427e60d4810de983520427d6594810dbd4a520427e64948109f592520427e63948109f58e52042df6354810b718d520427f64548109f191520427f6354810d7d8d520425f63548109f18d520435c63548109718d520436f62548109fd85520427d61548109fd81520427d6054810af99052042bd6414810b798c52042dd6314810db548520427e6414810cf990520423e64148109f590520433d64148108f590520427e6314810d798c520425e63148109f58c520435d63148109758c520427e6214810db988520427e6114810dd984520427661148109f980520437a60148109fd97420427e65d08109f597420427c65d0810cf953420433d54d0810b798f42042dd63d08109fd96420427e65908109f596420427c6590810db94a420436d52908109fd95420427e65508109f595420427c6550810cf951420433d5450810db949420436d5250810bdd8542042f46150810bed8142042f860508109fd94420427e65108109f594420427c65108109fd97320427e65cc8109f597320427c65cc810d794f320435d53cc8109fd9
  | 2 => 0x60105109f997314435f53cc510d714f31442fa60cc510be583314437665cc5109d99731442f764cc510bd593314437654cc510dd153314437753cc510f5d4f314437553cc510f514f31443d643cc510f550f31442f562cc510bd98331443f260cc510bc98331443f160cc5109f996314435e538c510d754e31442f6618c5109f195314435f534c510d714d31442fb604c510be181314427e650c510d794c314435d530c510f54c431442f6650c510dd99431442f7640c510bd5903144376540c510dd15031442f6630c510f598c3144377530c510f594c3144375530c510f554c31443d7430c510f510c31442f5620c510f58c831443d4320c510bd980314427e65c8510dbd4b214436c52c8510be98321442f960c85109f99621442f66588510dd99621442f76488510bd59221442f66388510bd18e21442f56288510dd94a21443745288510bd982214427c6548510b7d8d21442dc6348510dbd49214436c5248510bed8121442f86048510dd19521442746548510bdd9121442f56448510f5d8d21442f66348510bd18d21443d46348510b518d21443e76248510f9d4921443765248510dd14921443e45248510f990921443e54248510fcd8121442f46048510fc18121442f060485109f99421442f661085109f997404433f54d0110cf15340442f661d0110bd587404427e6590110be996404437a6590110be592404437a5490110de15240443f36190110be98640443f06190110fc90640443f14190110fccc640443f03190110fc88640443f121901109fd95404427d65501109f195404433f5450110cf15140442f76150110bd18540442f86550110de19540442786550110eed9140443bb5450110de95140443785450110ee15140443bb4250110ee50940443f36150110be18540443f06150110fc90540443f14150110fccc540443f03150110fc88540443f121501109f99440442de6310110b758c40442ee6210110bb58840442f66110110bd58440442fa60101109f997304435f53cc110d714f30442f661cc110bd58730443d431cc1109f99630442f6618c110bd586304427f654c1109f595304427c654c110d7d4d304435c534c110bbd8930442ec624c110bdd8530442f4614c110f50c5304427e650c110f64c0304427e65c8110dbd4b204436c52c8110bd98720442f561c81109f996204427f65481109f595204427c6548110b7d8d20442dc6348110dbd49204436c5248110bdd8520442f461481109f99420442be6408110af59020442de6308110b758c20442f66108110bd58420443e92008110bed9310442f964c4110fc90710443f141c4110fccc710443f031c4110fc88710443f121c4110b798e10442dd6384110bdd9210442f56484110bd98e10443d66384110b598e10443d56384110bd18e10442f76284110bd58a104
  | 3 => 0xd109f990534427d6414d10d798c534427e6214d109f588534427e6114d109f184534427e6014d109f180534427f65d0d109f997434427d65d0d109f197434435f53d0d10d714f43442ee62d0d10bb58b43442f661d0d10bd58743442fa60d0d10be583434427f6590d109f996434427d6590d109f196434433f5490d10cf152434435e5390d10d754e434427f6550d109f995434427d6550d109f195434435e5350d10d754d43442f76150d10bd185434427f6510d109f994434427d6510d109f194434433f5410d10cf150434435f5310d10d714c43442f66110d10bd58443442fa6010d10be580434427e64d49109f593524427e63d49109f58f524436f52949109f992524427d64949109f98e524427d63949109f98a524427d6194910dd586524427d6094910de58252442bf6454910af19152442df6354910b718d524427f6454910cfd91524423f64549109f191524433c64549108f191524427f6354910d7d8d524425f63549109f18d524435c63549109718d524436f62549109fd85524437761549109fd81524437b60549109f994524436d52149109f990524427d64149109f98c524427d6314910db988524427e6114910dd584524427c61149109f980524427c60149109fd97424427e65d09109f597424427c65d0910b798f42442dd63d0910dbd4b424436c52d0910bd98742442f561d0910be98342442f960d09109fd96424427e65909109f596424427c6590910cfd52424433c5490910db94a424436d5290910bd98642442f561909109fd95424427e65509109f595424427c6550910db949424436d52509109fd94424427e65109109f594424427c6510910cfd50424433c5410910dbd48424436c5210910bd98442442f56110910be98042442f960109109fd97324427e65cc9109f597324427c65cc910dbd4b324436c52cc9109fd96324427e658c9109f596324427c658c910d7d4e324435c538c910bd98632442f5618c9109fd95324427e654c9109f595324427c654c910bdd8532442f4614c910bed8132442f8604c9109fd94324427e650c9109f594324427c650c910d7d4c324435c530c910dbd48324436c520c910bd98432442f5610c910be98032442f9600c9109f997414433f54d0510cf15341442fa60d0510be583414427e6590510bd99641443766590510bd59241443765490510dd15241442f66390510bd58a41443f36090510bd98241443f060905109f195414433f5450510cf15141442df6350510b718d41442fb6050510be181414437465505109d19541443b76450510edd5141443765450510dd15141443b45450510cd15141443d76350510bd18d41443d46350510b518d41442f76250510fcd8141442f46050510fc181414427e6510510b798c41442dd6310510bb98841442ed6210510bd98441442fa
  | 4 => 0x794c318435d530c610d794f218435d53c8610db94b218436d52c8610be98321842f960c8610d794e218435d5388610b7d8d21842dc6348610d794d218435d5348610db949218436d5248610bed8121842f86048610d794c218435d5308610d794f408435d53d0210cf952408433d5490210d794e408435d5390210bd98640842f56190210be59640843796590210de95240843ba5490210ee55240843785490210f694e40843d95390210be98640843f26190210fc586408435e5350210d754d40842fb6550210ded9540843bb6450210de95140843785450210f694d40843d95350210eed0940843b94250210be185408433e5410210cf55040842de6310210b758c408435e5310210d754c40842ee6210210bb58840842f66110210bd584408435e53cc210d754f308435e538c210d754e30842f6618c210bd586308435e534c210d754d30842ef624c210bb189308435e530c210d754c30842f6610c210bd58430843d9300c210d794f208435d53c8210d794e208435d5388210db94a208436d5288210bd98620842f56188210b7d8d20842dc6348210d794d208435d5348210af99020842bd6408210b798c20842dd6308210d794c208435d5308210db948208436d5208210bd98420842f56108210fa480208435e53c4210d754f10842f565c4210dd597108437754c4210dd553108437653c4210f594f108435653c4210f554f108437453c4210ddd4b108437552c4210be597108437965c4210bed9310842f964c4210f694f10843d953c42109f98f544427d63d51109f98b544427d62d5110cfd52544427e64951109f98e544427d63951109f98a544427d62951109f586544437561951109f58254443796095110b7d8d54442dc6355110bbd8954442ec6255110cfd91544427f6355110d7d8d544425f63551109f18d544435c63551109718d544427f6255110dbd89544426f62551109f189544436c62551109b189544427f6155110ddd85544427f6055110ded81544427e6515110cf55054442de6315110b758c54442ee6215110bb588544433e64151109f98c544435e63151109798c544427d6315110d758c544425d63151109f988544436e62151109b988544427d6215110db588544426d62151109f984544437561151109f184544427e6015110de580544427c60151109f993534427d64d4d109f98b534427d62d4d10dd587534435f5394d109f992534427d6494d109f98e534427e6294d109f58a534427d6194d10dd586534427d6094d10de58253442bf6454d10af19153442ef6254d10bb189534427f6454d10cfd91534423f6454d109f191534433c6454d108f191534435f6354d109fd89534436f6254d109bd89534427c6254d10db189534426c6254d109fd8553443776154d109fd81534437b6054d109f994534435d5314
  | 5 => 0x538435c6094e109fd91538427c6454e10d7d8d538427f6254e109f189538435f6554e10d7d51538435e5454e10d7551538435c5454e10d7d91538435e6454e10d7591538435c6454e10d7d89538435e6254e10d7589538435c6254e10d7d85538435d6154e10d7981538435c6054e10d754c538427e6414e109f590538435e6314e109f988538427d6214e10dd584538437a6014e109fd97438427e65d0e109f597438427c65d0e10d794f438435d53d0e10bb98b43842ed62d0e10be98343842f960d0e109fd96438427e6590e109f596438427c6590e10d794e438435d5390e109fd95438427e6550e109f595438427c6550e10d794d438435d5350e10bdd8543842f46150e109fd94438427e6510e109f594438427c6510e10d794c438435d5310e10be98043842f96010e10b798f52842dd63d4a10d794f528435d53d4a109f993528427d64d4a109f98f528435e63d4a109798f528427d63d4a10d758f528425d63d4a10dd587528437a60d4a10d794e528435d5394a10dbd4a528427e6494a109f592528427e6394a109f58e528435e5354a10d754d528427f6454a109f191528427f6354a109f18d528436f6254a10af99052842bd6414a10b798c52842dd6314a10d794c528435d5314a10db548528427e6414a10cf990528423e6414a109f590528433d6414a108f590528427e6314a10d798c528425e6314a109f58c528435d6314a109758c528436e6214a10dd584528437a6014a109fd97428427e65d0a109f597428427c65d0a10cf953428433d54d0a10b798f42842dd63d0a10d794f428435d53d0a10be98342842f960d0a109fd96428427e6590a109f596428427c6590a10d794e428435d5390a10db94a428436d5290a109fd95428427e6550a109f595428427c6550a10cf951428433d5450a10d794d428435d5350a10db949428436d5250a10bdd8542842f46150a109fd94428427e6510a109f594428427c6510a10d794c428435d5310a10be98042842f96010a109fd97328427e65cca109f597328427c65cca10d794f328435d53cca109fd96328427e658ca109f596328427c658ca10d794e328435d538ca109fd95328427e654ca109f595328427c654ca10d794d328435d534ca10bed8132842f8604ca109fd94328427e650ca109f594328427c650ca10d794c328435d530ca10be98032842f9600ca10cf953418433d54d0610d794f418435d53d0610be98341842f960d0610d794e418435d5390610cf951418433d5450610b7d8d41842dc6350610d794d418435d5350610bed8141842f86050610b798c41842dd6310610d794c418435d5310610bb98841842ed6210610ed50441842f96010610d794f318435d53cc610be98331842f960cc610d794e318435d538c610d794d318435d534c610bed8131842f8604c610d
  | 6 => 0x3745490710bd98e41c42f56290710bd98241c43f26090710fc58241c42df6350710b718d41c42f76550710ddd9541c43b76450710dd95141c43745450710f5d8d41c42f46350710f518d41c42d46350710bdd8941c42f46050710cf95041c433d5410710b798c41c42dd6310710bb98841c42ed6210710be98041c42f96010710bd59731c437565cc710bdd9331c42f564cc710dd95331c437454cc710ddd4f31c437553cc710f590f31c43d543cc710bd58b31c42f660cc710d794e31c435d538c710be98231c42f9608c710d794c31c435d530c710f54c431c42fa600c710be58031c4375650c710bdd9031c42f5640c710dd95031c4374540c710f598c31c4377530c710f594c31c4375530c710f554c31c43d7430c710f510c31c42f5620c710f58c831c43d4320c710bd98031c43f2600c710fc58031c436e5288710db54a21c42fa6088710be58221c43756588710bdd9221c42f56488710bd98e21c42f46388710dd94a21c43e65288710f954a21c43745288710bd98221c43f26088710fc58221c42df6348710b718d21c42f76548710ddd9521c42f76448710bd59121c43d76348710bd98d21c42f46348710f518d21c42d46348710f9d8921c43765248710dd14921c43e64248710f950921c42f46048710db94821c436d5208710be98021c42f96008710cf95340c433d54d0310bd98740c42f561d0310cf95140c433d5450310bdd8540c42f46150310b798c40c42dd6310310bb98840c42ed6210310bd98440c42f56110310d794f30c435d53cc310bd98730c42f561cc310f50c730c42f6618c310bd58630c435e534c310d754d30c42ef624c310bb18930c42f7614c310bd18530c43d4314c310db94b20c436d52c8310bd98720c42f561c8310b7d8d20c42dc6348310db94920c436d5248310bdd8520c42f46148310af99020c42bd6408310b798c20c42dd6308310bd98420c42f56108310b798f54842dd63d52109f98f548435e63d52109798f548427d63d5210d758f548425d63d52109f98b548427d62d5210dd587548437a60d5210cfd52548427e63952109f58e548427e62952109f58a548437a6095210cfd91548427f63552109f18d548427f62552109f189548433d5415210b798c54842dd6315210bb98854842ed6215210cf990548427e6315210d798c548425e63152109f58c548435d63152109758c548427e6215210db988548426e62152109f588548436d62152109b58854843756115210de980548427e64d4e109f593538427e62d4e109f58b538437561d4e10de983538435f5394e109f992538427d6494e109f98a538427d6294e10d7d52538435e5494e10d7552538435c5494e10d7d92538435e6494e10d7592538435c6494e10d7d8a538435e6294e10d758a538435c6294e10d7d86538435d6194e10d7982
  | 7 => 0x548020ded95200827b6548020ee95120083b95448020f6d8d20083d86348020f694d20083d95348020bed8920083eb6248020de94920083ea5248020fad0920083e84248020fa8c920083e93248020fc94520083f15148020fac8520083e921480209f98f54c427d63d53109f98b54c427d62d5310dd98754c437960d5310cfd5254c427e63953109f58e54c427e62953109f58a54c43766195310cfd9154c427f63553109f18d54c427f62553109f18954c433d5415310b798c54c42dd6315310bb98854c42ed6215310cf99054c427e6315310d798c54c425e63153109f58c54c435d63153109758c54c427e6215310db98854c426e62153109f58854c436d62153109b58854c43766115310de58054c42ee62d4f10bb58b53c427e64d4f109f59353c427e62d4f10db98b53c426e62d4f109f58b53c436d62d4f109b58b53c437661d4f10de58353c435f5394f109f99253c427d6494f109f98a53c427d6294f109fd9153c427c6454f10d7d8d53c427f6254f109f18953c43746154f10d754c53c427e6414f109f59053c435e6314f109f98853c427d6214f10dd98453c43796014f109fd9743c427e65d0f109f59743c427c65d0f10bb98b43c42ed62d0f10bd98743c42f561d0f109fd9643c427e6590f109f59643c427c6590f10d794e43c435d5390f109fd9543c427e6550f109f59543c427c6550f10d794d43c435d5350f10bdd8543c42f46150f109fd9443c427e6510f109f59443c427c6510f10bd98443c42f56110f10b798f52c42dd63d4b109f99352c427d64d4b109f98f52c435e63d4b109798f52c427d63d4b10d758f52c425d63d4b10dd98752c437960d4b10dbd4a52c427e6494b109f59252c427e6394b109f58e52c43766194b109fd9152c427c6454b109fd8d52c427c6354b10dbd8952c436d5214b109f99052c427d6414b109f98c52c427d6314b10db98852c43766114b10de58052c427f65d0b109f99742c427d65d0b109f19742c42de63d0b10b758f42c42f661d0b10bd58742c427f6590b109f99642c427d6590b109f19642c436e5290b10db54a42c42f66190b10bd58642c427f6550b109f99542c427d6550b109f19542c436e5250b10db54942c42fb6050b10be18142c427f6510b109f99442c427d6510b109f19442c42f66110b10bd58442c427f65ccb109f99732c427d65ccb109f19732c436e52ccb10db54b32c427f658cb109f99632c427d658cb109f19632c435e538cb10d754e32c42f6618cb10bd58632c427f654cb109f99532c427d654cb109f19532c42f7614cb10bd18532c427f650cb109f99432c427d650cb109f19432c435e530cb10d754c32c436e520cb10db54832c42f6610cb10bd58432c433e5490710cf55241c42fa6090710be58241c43756590710dd95241c43b65490710ed55241c4
  | 8 => 0x20bb58a31083cc328c420dd9463108375518c420be98231082f9608c4209fd95310827d654c4209f195310833e544c420cf551310835e534c420d754d31082ef624c420bb1893108376514c420dd545310827f650c4209f994310827d650c420cf950310833d540c420d794c310835d530c420f30c83108376510c420dd544310833e54c8420cf553210835e53c8420d754f210837651c8420dd54721082fa60c8420be583210827d6588420cf952210833d5488420d794e210835d5388420dd546210827f6548420cf951210833d5448420b7d8d21082dc6348420d794d210835d5348420dd945210833e5408420cf550210835e5308420d754c21083765108420dd54421082fa6008420be580210827e64940209f592500827e63940209f58e500836f3294020db0ca500827d65d0020cf953400833d54d0020d794f400835d53d0020dd947400837551d00209fd96400827d6590020cf952400833d5490020d794e400835d5390020bb98a40082ed6290020dd946400837551900209fd95400833e5450020cf551400835e5350020d754d40083765150020dd545400827f65100209f994400827d65100209f194400833e5410020cf55040082de6310020b758c400835e5310020d754c40082ee6210020bb58840082f66110020bd58440083765110020dd544400827d65cc020cf953300833d54cc020d794f300835d53cc020f3ccb300837651cc020dd547300827f658c0209f596300833e548c020cf552300835e538c020d754e30082ee628c020bb58a30083cc328c020bd98630082f5618c020dd9463008375518c0209fd95300833e544c020cf551300835e534c020d754d30082ef624c020bb18930083cf324c020dd9453008375514c0209fd94300827e650c0209f594300827c650c020cf950300833d540c020d794c300835d530c020bb98830082ed620c020f30c83008376510c020dd544300833e54c8020cf553200835e53c8020d754f200837651c8020dd547200836f54c8020eb953200836d54c8020eb553200832d54c8020bb98f20082ec63c8020f394f20083cd53c8020f994720083e551c8020cf952200833d5488020d794e200835d5388020bb58a200836e5288020dd94620083755188020ee95220083b95488020f694e20083d95388020be58a200837a5288020fa94a20083eb3288020fa0ca20083f25188020fc546200827f6548020cf951200833d5448020b7d8d20082dc6348020d794d200835d5348020dd94520083755148020bbd95200836f65480209bd95200836f5448020eb951200836d5448020eb551200832d5448020f3d8d20082ee6348020bb18d20083cc6348020b318d20083ce5348020f354d20083e65148020f954520082ef6048020db94120083eb4048020fa10120083ea3048020fa4c120082fb6
  | 9 => 0x951320833d544c820d794d320835d534c8209fd94320827d650c820cf950320833d540c820d794c320835d530c820f34c832082fa600c820be580320836d650c8209b594320836f540c820eb950320836d540c820eb550320832d540c820bb98c32083ce630c820dbd4c32083ce530c820db54c32083cd530c820f390c32083cd430c820fa98032082ed600c820fa58032082e9600c820af99351082bd64d4420cf953510833d54d4420b798f51082dd63d4420d794f510835d53d4420cf952510833d5494420d794e510835d5394420ddd46510827e64944209f592510827e63944209f58e51083775494420dd95251083b65494420cd95251083755494420ed55251083355494420dd15251083775394420dd94e51083d65394420d594e51083755394420f554e51083555394420dd14e51083e73294420f90ca51083776494420dd99251083756494420dd19251083776394420dd98e51083756394420dd18e51083774394420dd90e51083754394420dd10e51083746294420ddd0a51083764294420dd50a51083744294420ddcca51083763294420dd4ca51083743294420dd98251083746094420cf951510833d5454420d794d510835d53544209fd91510827c64544209fd8d510827c6354420ddd9551083775454420dd95151083b65454420cd95151083755454420ed55151083355454420dd15151083775354420dd94d51083d65354420d594d51083755354420f554d51083555354420dd14d51083e73254420f90c951083776454420dd99151083756454420dd19151083776354420dd98d51083756354420dd18d51083774354420dd90d51083754354420dd10d51083766254420ddd0951083764254420dd50951083744254420ddcc951083763254420dd4c951083743254420dd98151083746054420dd08151082be6414420af590510833e5414420cf55051082de6314420b758c510835e5314420d754c51082f66114420dd544510827f65d04209f997410827d65d0420cf953410833d54d0420d794f410835d53d0420dd947410837551d04209fd96410827e65904209f596410833e5490420cf552410835e5390420d754e41083765190420dd546410827f65504209f595410827c6550420cf951410833d5450420b7d8d41082dc6350420d794d410835d5350420bbd8941082ec6250420dd94541083755150420bed8141082f860504209fd94410827e65104209f594410833e5410420cf55041082de6310420b758c410835e5310420d754c41082ee6210420bb58841083765110420dd54441082fa6010420be580410827f65cc4209f997310827d65cc420cf953310833d54cc420d794f310835d53cc420dd947310837551cc4209fd96310827e658c4209f596310833e548c420cf552310835e538c420d754e31082ee628c4
  | 10 => 0x4082be64d4c20af593530833e54d4c20cf55353082f661d4c20bd587530827e64d4c20cf993530823e64d4c209f593530833d64d4c208f593530827e62d4c20db98b530827e61d4c20dd987530827661d4c209f587530837561d4c209d587530827e60d4c20de983530827d6594c20cf952530833d5494c20d7d4e530827e6494c209f592530827e6194c209f586530825d6594c20d7d52530835e5494c20e7952530831e5494c20d7552530839d5494c20c7552530835c5494c20f318a530835f6494c20d7992530835d6494c20d7192530835e6294c20d718a530835f6194c20d7986530835d6194c20d7186530835e6094c20d7182530833e5454c20cf551530827f6454c209f191530835f6354c209fd89530827d6254c20db189530827f6154c209f185530835f6554c20d7d51530835e5454c20e7951530831e5454c20d7551530839d5454c20c7551530835c5454c20f3189530835f6454c20d7991530835d6454c20d7191530835e6254c20d7189530834c6254c20d7d85530835e6154c20d7585530835c6154c20d7981530835c6054c20d708153082be6414c20af590530833e5414c20cf55053082de6314c20d754c53082f66114c20bd584530827e6414c20cf990530823e6414c209f590530833d6414c208f590530827e6314c20d798c530825e6314c209f988530836e6214c209f98453083766114c209d984530827d6114c20dd58453082756114c209f980530837a6014c209fd97430827e65d0c209f597430827c65d0c20cf953430833d54d0c20d794f430835d53d0c20bb98b43082ed62d0c209fd96430827e6590c209f596430827c6590c20cf952430833d5490c20d794e430835d5390c209fd95430827e6550c209f595430827c6550c20cf951430833d5450c20d794d430835d5350c20bbd8943082ec6250c20bdd8543082f46150c20bed8143082f86050c209fd94430827e6510c209f594430827c6510c20cf950430833d5410c20d794c430835d5310c209f992520827d64948209f98e520827d63948209f597420833e54d0820cf55342082de63d0820b758f420835e53d0820d754f420827f65908209f596420833e5490820cf552420835e5390820d754e420836e5290820be98242082f960908209fd95420833e5450820cf551420835e5350820d754d420836e52508209fd94420827d6510820cf950420833d5410820d794c420835d5310820be98042082f960108209f597320833e54cc820cf553320835e53cc820d754f32082ed65cc820db597320836f54cc820eb953320836d54cc820eb553320832d54cc820dbd4f32083ce53cc820db54f32083cd53cc820d354f32082ed60cc8209fd96320827d658c820cf952320833d548c820d794e320835d538c820bb98a32082fa608c820be582320827f654c820cf
  | 11 => 0x7c6550520b7d8d41482dc6350520d7d4d414835c53505209f994414827d65105209f194414833f5410520cf15041482de6310520b758c414835f5310520d714c41482ee6210520bb58841483775110520dd14441482fa6010520be580414827e65cc5209f597314827c65cc520d7d4f314835c53cc5209f996314827d658c5209f196314835f538c520d714e314827f654c5209f995314827c654c520d7d4d314835c534c5209f994314827d650c5209f194314835f530c520d714c31482ee620c520bb58831482fa600c520be580314827e65c8520d7d4f214835c53c8520d7d4e214835c5388520ddd4621483745188520be98221482f96088520b7d8d21482dc6348520d7d4d214835c5348520ddd4521483745148520bed8121482f860485209f994214835f5308520d714c214827e65d0120cfd53404833c54d0120d7d4f404835c53d0120bb98b40482ed62d0120eb50b404827e6590120d7d4e404835c53901209fd95404827d65501209f195404833f5450120cf151404835f5350120d714d40482ef6250120bb18940483ad42501209f99440482de6310120b758c404835f5310120d714c40482ee6210120bb58840482f66110120bd584404827e65cc120d7d4f304835c53cc120bb98b30482ed62cc1209f996304835f538c120d714e30482f6618c120bd586304827f654c1209f595304827c654c120d7d4d304835c534c120bbd8930482ec624c1209f994304835f530c120d714c304835f53c8120d714f20483db53c8120f614f20483ea42c8120fa50b204835f5388120d714e20482ef6488120bb59220483cf5388120db94e204836c5388120f314e204834c5388120fad4220482de63d5020b758f54082f661d5020bd587540827e63d5020d798f540825e63d50209f58f540835d63d50209758f540827e62d5020db98b540827e61d5020dd987540827661d50209f587540837561d50209d587540827e60d5020de983540827d6595020cfd52540827e63950209f58e540827e61950209f586540823d6595020cfd8e540833e6395020cf58e540833c6395020cf98a540833c6295020cfd86540833e6195020cf586540833c6195020cf982540833c6095020cfd91540827f63550209f18d540827f62550209f589540827f61550209f185540833f6555020cfd8d540833e6355020cf58d540833c6355020cf989540833c6255020cfd85540833e6155020cf585540833c6155020cf981540833c6055020cf08154082be6415020cf55054082de6315020b758c54082f66115020bd584540827e6415020cf990540823e64150209f98c540835e63150209798c540827d6315020d758c540825d63150209f988540836e62150209b988540827e6115020dd984540827661150209f584540837561150209d584540827e6015020de9805
  | 12 => 0x151209f984544827d61151209f993534827d64d4d209f987534827d61d4d20d7d53534835e54d4d20d7553534835c54d4d20d7d93534835e64d4d20d7593534835c64d4d20d7d8b534835d62d4d20d7d87534835e61d4d20d7587534835c61d4d20d7d83534835d60d4d20d7d4e534827e6494d209f592534827e6394d209798e534827d6294d20db58a534827e6194d209f586534827d6094d20de582534827f6454d209f191534835f6354d209fd89534836f6254d209bd89534827f6154d209f185534827f6054d20ded81534827e6514d20d754c534827e6414d209f590534835e6314d209f988534827c6214d209f984534827d6114d20b7994534835e6514d2097994534835f5414d20d7950534835d5414d20d7150534835f6414d20d7990534835d6414d20d7190534835f6214d20d7588534835f6114d20d7984534835d6114d20d7184534835f6014d20d7580534835d2014d209fd97434827e65d0d209f597434827c65d0d20d7d4f434835c53d0d20bb98b43482ed62d0d209fd96434827e6590d209f596434827c6590d20d7d4e434835c5390d209fd95434827e6550d209f595434827c6550d20d7d4d434835c5350d20bdd8543482f46150d209fd94434827e6510d209f594434827c6510d20d7d4c434835c5310d20bb98843482ed6210d20be98043482f96010d209f997424833f54d0920cf15342482de63d0920b758f424835f53d0920d714f42482fa60d0920be583424827e6590920d7d4e424835c5390920bb996424836e6590920bb592424836e5490920db15242483cf5390920db94e424836c5390920f314e424834c5390920bb982424827c6550920cfd51424833c5450920d7d4d424835c5350920bed8142482f86050920db195424826c6550920ebd9142483af5450920db951424836c5450920eb15142483cf5350920db94d424836c5350920f314d424834c5350920fad8142482ec6050920fa18142482e860509209f994424835f5310920d714c42482ee6210920eb508424827e65cc920d7d4f324835c53cc920be98332482f960cc9209f996324835f538c920d714e324827c654c920d7d4d324835c534c920bed8132482f8604c9209f994324835f530c920d714c324835f53d4520d714f514827e64d45209f593514827e63d45209f58f514836e42d4520db50b51482de6394520b758e514835f5394520d714e51483775194520afd9151482bc6454520b7d8d51482dc6354520d7d4d514835c5354520d7d4c514835c5314520dd544514827e64145209f590514827e63145209f58c514827e65d05209f597414827c65d0520d7d4f414835c53d0520bb98b41482ed62d0520ddd47414837451d05209f996414827d65905209f196414833f5490520cf152414835f5390520d714e414827f65505209f99541482
  | 13 => 0xbe98043882f96010e20cf953428833d54d0a20b798f42882dd63d0a20be98342882f960d0a20cf951428833d5450a20bed8142882f86050a20d794f328835d53cca20be98332882f960cca20db597328836f54cca20db553328836f53cca20f394f328836d53cca20f354f32883ea60cca20bb58332883e960cca20d7d4e328835c538ca20d794d328835d534ca20bed8132882f8604ca20d7d4c328835c530ca20f34c832882ed650ca20db594328836f540ca20db55032883ce630ca20dbd4c32883cf530ca20db54c32883cc530ca20f390c32883cd430ca20bb58032882de63d4620b758f518837751946209f992518827d64946209f98e518827d63946209fd91518827c64546209fd8d518827c6354620dd544518827f65d06209f997418827d65d06209fd96418827e65906209f59641883765190620dd546418827f65506209f595418827c6550620b7d8d41882dc6350620bbd8941882ec6250620dd945418837551506209fd94418827e65106209f59441882de6310620b758c41882ee6210620bb58841882fa6010620be580418827f65cc6209f997318827d65cc620dd947318837551cc6209fd96318827e658c6209f596318835e538c620d754e31882ee628c620bb58a31883cc328c6209fd95318827d654c6209f19531882ef624c620bb189318827f650c6209f994318827d650c620d794c318835d530c620f30c83188376510c620dd54431882fa600c620be58031883765188620dd54621882fa6088620be58221882df6348620b718d21883765148620dd54521882fb6048620be181218833f54d0220cf153408833e5490220cf55240882ee6290220bb58a408833f5450220cf151408833e5410220cf55040882de6310220b758c40882ee6210220bb58840882f66110220bd584408835f53cc220d714f30883cf32cc220d794e308835d538c220bb98a30882ed628c220f30ca30882f6618c220bd586308835f534c220d714d30882ef624c220bb18930883cf324c220d794c308835d530c220bb98830882ed620c220f30c830882ed65c8220db597208836f54c8220db55320882ee63c8220bb18f20882f965c8220de597208827e63d51209f58f544827e61d51209f587544833f5495120b798e54482dd63951209f992544827e6395120d798e544825e63951209f58e544835d63951209758e544827d6295120db58a544827e61951209f586544827d6095120de58254482df6355120b718d54482f76155120bd185544833f64551209fd8d544835f635512097d8d544827c6355120d718d544825c63551209fd89544836f62551209fd85544837761551209dd85544827c6155120dd185544827461551209fd81544837b60551209f994544833d5415120cf990544827e63151209f58c544827e6215120db588544827c62
  | 14 => 0x5142c836e5350b20db14d42c82ec6050b20cf95042c833d5410b20eb50842c82fa6010b20be58042c835f53ccb20d714f32c835e538cb20d754e32c82fa608cb20be58232c835f534cb20d714d32c835e530cb20d754c32c82fa600cb20be58032c837751947209f99251c827d64947209f98e51c827d6394720b7d8d51c82dc63547209fd9151c827c64547209fd8d51c835f635472097d8d51c827c6354720d718d51c825c6354720db90951c836d4254720dd54451c827f65d07209f99741c827d65d0720bb98b41c82ed62d07209fd9641c827e65907209f59641c827f65507209f59541c827c6550720b7d8d41c82dc6350720bed8141c82f860507209fd9441c827e65107209f59441c82de6310720b758c41c82ee6210720bb58841c82fa6010720be58041c827f65cc7209f99731c827d65cc7209fd9631c827e658c7209f59631c835f538c720d714e31c82fa608c720be58231c827f654c7209f59531c827c654c7209fd9431c827e650c7209f59431c835f530c720d714c31c82ee620c720bb58831c837651c8720dd54721c82fa60c8720be58321c82df6348720b718d21c83765108720dd54421c82fa6008720be58021c833e54d0320cf55340c82ee62d0320bb58b40c83ad42d0320cf95140c833d5450320bbd8940c82ec6250320eb50940c82de6310320b758c40c82ee6210320bb58840c82f66110320bd58440c835e53cc320d754f30c82ee62cc320bb58b30c835f538c320d714e30c82f6618c320bd58630c835e534c320d754d30c82ef624c320bb18930c835f530c320d714c30c827e63d52209f58f548836d62d52209f987548827d61d5220de983548833f54952209f98e548827d63952209f986548827d6195220cfd91548827f63552209f18d548827f61552209f185548833d5415220b798c54882dd6315220bd98454882f56115220cf990548827e6315220d798c548825e63152209f58c548835d63152209758c548836d62152209f984548837661152209d984548827d6115220dd58454882756115220de98054882f661d4e20bd587538827e64d4e209f593538836d62d4e209f987538837661d4e209d987538827d61d4e20dd587538827561d4e20de983538835f5394e209f992538827d6494e209f986538827d6194e209fd91538827c6454e20d7d8d538836f6254e209fd85538827c6154e20d754c538827e6414e209f590538835e6314e20db588538827e6114e209f584538837a6014e209fd97438827e65d0e209f597438827c65d0e20bb98b43882ed62d0e209fd96438827e6590e209f596438827c6590e20d794e438835d5390e209fd95438827e6550e209f595438827c6550e20d794d438835d5350e20bbd8943882ec6250e20bdd8543882f46150e209fd94438827e6510e209f594438827c6510e2
  | 15 => 0xc37551cc430be983310c2f960cc4309f596310c35e538c4309fd95310c35e530c430dd944310c375510c430be980310c2f9600c4309fd97210c27e65c84309f597210c36e52c8430db54b210c27f65884309f996210c27d6588430b798e210c2dd6388430dd946210c3755188430be982210c2f960884309fd95210c27d65484309f195210c2df6348430b718d210c36e5248430db549210c3765148430dd545210c27f65084309f994210c27d65084309f992500c27d6494030d78ca500c35c3294030dd986500c37561940309f597400c27f65900309f596400c33e5490030cf552400c2de6390030b758e400c27f65500309fd94400c27e65100309f594400c27c6510030cf950400c33d5410030b798c400c2dd6310030bb988400c2ed6210030bd984400c2f56110030d7d53300c35d54cc030b798b300c35d52cc030d7947300c2dd638c030d794e300c2f6618c030bd586300c2f9638c030de94e300c3da538c030f68ca300c3d8328c030fc986300c3f1618c0309fd95300c2ef624c030bb189300c2df654c030d7d95300c25f654c030d7d51300c35d544c030f3d89300c2dc624c030f3189300c2cc624c030d7549300c35e514c030b7d81300c35e504c030bed95300c37b654c0309ed95300c2fb634c030f6d8d300c37a534c030f694d300c3eb624c030fa189300c3db314c030f64c5300c27e63d53209f58f54c836e62d53209f98754c827d61d5320de58354c833f5495320b798e54c82dd63953209f98e54c835e63953209798e54c827d6395320d758e54c825d6395320db98a54c827e61953209f58654c833f64553209fd8d54c827c63553209fd8554c827c6155320cf55054c833e64153209f98c54c827d6315320db98854c827e61153209f58454c837960153209f99353c827d64d4f20db98b53c827e61d4f209f58753c837960d4f20d7d4e53c827e6494f209f59253c827e6194f209f58653c827f6454f209f19153c835f6354f209fd8553c827c6154f20d754c53c827e6414f209f59053c835e6314f20db98853c827e6114f209f58453c83796014f209fd9743c827e65d0f209f59743c827c65d0f20bb98b43c82ed62d0f209fd9643c827e6590f209f59643c827c6590f20d7d4e43c835c5390f209fd9543c827e6550f209f59543c827c6550f20d7d4d43c835c5350f20bdd8543c82f46150f20bed8143c82f86050f209fd9443c827e6510f209f59443c827c6510f20bb98843c82ed6210f20cfd5342c833c54d0b20b798f42c82dd63d0b20cf95242c833d5490b20be98242c82f96090b20db59642c836e5490b20eb95242c83ad5490b20db15242c836e5390b20db14e42c82ee6090b20fa98242c83e96090b20cfd5142c833c5450b20bbd9542c836f6550b20ebd9142c83af5450b20db95142c836c5450b20eb1
  | 16 => 0xf5210130db148404c2f66110130bd584404c3b94010130dbd4b304c36c52cc130f690f304c3d943cc130fad4b304c3e852cc130f6ccb304c3d932cc130f68c7304c3d831cc130dbd4a304c36c528c130bd986304c2f5618c130b7d92304c2dd648c130b758a304c3cf528c130d714a304c3cc528c130d314a304c2de618c130f5986304c2d6618c130f5586304c3db508c1309f98f540c35e63d50309f98b540c27d62d50309f987540c27d61d50309f983540c37a60d50309f596540c33f54950309f98a540c27d62950309f986540c27d6195030cfd91540c27f63550309f58d540c27f62550309f189540c27f61550309f185540c33d5415030bb988540c2ed6215030bd984540c2f561150309f990540c33e64150309f98c540c35e63150309798c540c27e6215030db988540c26e62150309f588540c36d62150309b588540c27e6115030dd984540c27661150309f584540c37561150309d584540c27e6015030de980540c27e6494c309f592530c27d65d0c30bb98b430c2ed62d0c309fd96430c27d6590c30cf952430c33d5490c30d794e430c2fa6090c30be582430c27f6550c30d794d430c2f76150c30bd185430c27f6510c309f594430c33e5410c30cf550430c2fa6010c30be580430c36f52948309f992520c27d64948309f986520c27d61948309fd91520c27c64548309fd85520c27c6154830af990520c2bd6414830db548520c2f66114830bd584520c27f65d08309f997420c27d65d0830cf953420c33d54d0830b798f420c2dd63d08309fd96420c27e65908309f596420c36e5290830db54a420c27f65508309f595420c27c6550830cf951420c33d5450830b7d8d420c2dc6350830db949420c36d5250830bed81420c2f860508309fd94420c27e65108309f594420c35e53cc830db94b320c36d52cc830be983320c2f960cc8309f596320c2dd658c830d7596320c25d658c830d7d52320c35d548c830b798a320c35d528c830b7582320c27f654c830d794d320c36e520c830db548320c3cd320c830be980320c2f9600c830d7d50320c35d540c830b7988320c3ce620c830f3948320c35d520c830f3548320c3ce420c830f3508320c3da600c830b7580320c3d9600c830ddd46510c27e64944309f592510c27e62944309f58a510c35e3294430d70ca510c27f64544309f191510c27f62544309f189510c2be6414430af590510c2ee6214430bb588510c37551144309fd97410c27e65d04309f597410c33e54d0430cf553410c27f65904309f996410c27d6590430dd946410c37551904309fd95410c27d65504309f195410c33e5450430cf551410c2df6350430b718d410c3765150430dd545410c27f65104309f994410c27d6510430b798c410c2dd6310430bb988410c2ed6210430be980410c2f96010430dd94731
  | 17 => 0x930dbd48424c36c5210930be980424c2f960109309f997324c36c52cc930b7997324c35e65cc93097997324c2df64cc930b7593324c3cf52cc930d714b324c3cc52cc930d314b324c3ce42cc930f350b324c2de61cc930b7983324c2dd638c930dbd4a324c36c528c930be982324c2f9608c930dbd49324c36c524c930bed81324c2f8604c930b7d91324c2dd644c930f3d89324c3cf524c930d7149324c3cc524c930d3149324c2dc614c930f6d81324c2dc604c930f6181324c27e650c930b798c324c36f520c930dbd4b514c36c52d45309f993514c27d64d4530d790f514c35d43d45309f98b514c27d62d4530bb98a514c2ed6294530dbd4a514c36c5294530ddd46514c2bf6454530af191514c2ef6254530bb189514c36f5254530db149514c36f5214530db148514c37551145309f990514c27d64145309f988514c27d62145309f997414c27d65d05309f197414c2de63d0530b758f414c36f52d0530db14b414c37751d0530dd147414c27e65905309f596414c27c6590530cfd52414c33c5490530dbd4a414c36c52905309fd95414c27e65505309f195414c2df6350530b718d414c36f5250530db149414c27e65105309f594414c27c6510530cfd50414c33c5410530b798c414c2dd6310530bb988414c2ed6210530dbd48414c36c5210530ddd44414c3745110530be980414c2f960105309f997314c36f52cc530db14b314c36f528c530db14a314c377518c530dd146314c2fa608c530be582314c2df648c530b7592314c35e548c530d7152314c2dd628c530f3d4a314c35c528c530f314a314c34c528c530b7986314c35f518c530f5d46314c3d4518c530b7982314c3da608c530b6982314c3d9608c530dbd49314c36c524c530ddd45314c374514c530bed81314c2f8604c5309f994314c36f520c530db148314c3d5310c530b7994314c35e650c530b7d90314c2dd640c530d7950314c35c540c530b7588314c3cf520c530d7148314c3cc520c530d3148314c2de610c530f5984314c35f510c530f5944314c3d5510c530f5d04314c3d4410c530b7980314c27e65c85309f597214c27c65c8530b798f214c2dd63c8530dbd4b214c36c52c85309f996214c27d65885309f196214c2df6388530b718e214c36f5288530db14a214c27f65485309f995214c27c6548530b7d8d214c2dc6348530dbd49214c36c52485309f994214c27d65085309f194214c2de6308530b758c214c36f5208530db148214c2fa6008530be580214c27e65d0130cfd53404c33c54d0130b798f404c2dd63d0130dbd4b404c36c52d01309f996404c36f5290130db14a404c27f65501309f595404c27c6550130cfd51404c33c5450130b7d8d404c2dc6350130dbd49404c36c52501309f994404c2de6310130b758c404c2ee6210130bb588404c36
  | 18 => 0xdd544218c2fa6008630be580218c37651d0230dd547408c33e5490230cf552408c2de6390230b758e408c3765190230dd546408c3765150230dd545408c33e5410230cf550408c2de6310230b758c408c2ee6210230bb588408c2f66110230bd584408c3765110230dd544408c3b94010230dd947308c37551cc230b7597308c35d65cc230d7d53308c35d54cc230b798b308c35d52cc230d7947308c3d651cc230d5947308c3d551cc230be597308c37965cc230fc947308c3f151cc2309f98b544c27d62d51309f987544c27d61d5130cfd52544c2ee6295130bb58a544c27e64951309f58e544c35d63951309f98a544c36e62951309b98a544c27d6295130db58a544c26d62951309f986544c27d61951309f582544c3796095130bbd89544c2ec6255130bdd85544c2f46155130cfd91544c27f6355130d7d8d544c27f6255130dbd89544c26f62551309f189544c36c62551309b189544c27f6155130ddd85544c27761551309f185544c37461551309d185544c27f6055130ded81544c27e6515130cf550544c33e64151309f98c544c35d63151309f18c544c27e62151309f588544c27e61151309f584544c27e65d0d30cfd53434c33c54d0d30bb98b434c2ed62d0d30be983434c2f960d0d309f996434c2de6590d30d7996434c2dd6490d30d7952434c35c5490d30b758a434c2de6190d30b7982434c27c6550d30cfd51434c33c5450d30bdd85434c2f46150d30bed81434c2f86050d30d7195434c25c6550d30e7d91434c39f5450d30d7951434c35c5450d30e7151434c2df6250d30f5d85434c2dc6150d30f5185434c2d46150d30f6d81434c2dc6050d30f6181434c27e6510d30b798c434c27e64d49309f593524c27e61d49309f587524c36f54d4930db953524c36d54d4930db153524c3cf63d4930f390f524c3cd43d4930dbd93524c36e64d4930db593524c36c64d4930dbd8f524c36f43d4930db90f524c36d43d4930db10f524c36f61d4930db987524c36d61d4930db187524c36f60d4930db583524c36f5294930db548524c27e64149309f590524c35e4314930d750c524c27e61149309f584524c2ee6514930db994524c36f5414930db950524c36d5414930db150524c3cd6314930f390c524c3cd4314930dbd90524c36e6414930db590524c36c6414930dbd8c524c36f4314930db90c524c34e4314930db50c524c34d4314930db10c524c36f6114930db984524c36d6114930db184524c36f6014930db580524c36d30149309f997424c27d65d09309f197424c2de63d0930b758f424c36f52d0930db14b424c27e65909309f596424c27c6590930b798e424c2dd6390930dbd4a424c36c52909309fd95424c27e65509309f195424c36f5250930db149424c27e65109309f594424c27c6510930b798c424c2dd631
  | 19 => 0x5438c2f46150e30bed81438c2f86050e30bd987528c2f561d4a30dbd4a528c27e6494a309f592528c27e6194a309f586528c27f6454a309f191528c27f6154a309f185528c2be6414a30af590528c36d5214a30bd984528c2f56114a309fd97428c27e65d0a309f597428c33e54d0a30cf553428c2de63d0a30b758f428c27f6590a309f996428c27d6590a30db94a428c36d5290a309fd95428c27d6550a309f195428c33e5450a30cf551428c2df6350a30b718d428c36e5250a30db549428c27f6510a309f994428c27d6510a30be980428c2f96010a30db94a328c36d528ca30be982328c2f9608ca30d7d52328c35d548ca30f394a328c35d528ca30f354a328c3da608ca30b7582328c3d9608ca30db949328c36d524ca30bed81328c2f8604ca30f34c8328c2dd650ca30d7594328c35f540ca30d7550328c3ce620ca30f3d48328c35d520ca30f3148328c3ce420ca30f3508328c2dd600ca30ddd46518c27e64946309f592518c27e62946309f58a518c35e3294630d70ca518c3775494630dd952518c3755494630dd152518c3775294630dd94a518c3755294630dd14a518c3d63294630f50ca518c3776494630dd992518c3756494630dd192518c3776394630ddd0e518c3764394630dd50e518c3744394630ddd8a518c3766294630dd58a518c3746294630ddd0a518c3764294630dd50a518c3744294630ddcca518c3763294630d58ca518c3753294630dd0ca518c3543294630dd982518c37460946309fd91518c27c64546309fd89518c27c6254630ddd95518c3775454630dd951518c3755454630dd151518c3775254630dd949518c3755254630dd149518c3d63254630f50c9518c3776454630dd991518c3756454630dd191518c3756354630ddd0d518c3764354630dd50d518c3744354630ddd89518c3766254630dd589518c3746254630ddd09518c3764254630dd509518c3744254630ddcc9518c3763254630dd4c9518c3743254630dd981518c3746054630dd544518c27f65d06309f997418c27d65d0630dd947418c37551d06309fd96418c27e65906309f596418c3765190630dd546418c27f65506309f595418c27c6550630b7d8d418c2dc6350630dd945418c37551506309fd94418c27e65106309f594418c2de6310630b758c418c2ee6210630bb588418c3765110630dd544418c2fa6010630be580418c37651cc630dd946318c375518c630be982318c2f9608c630dd945318c375514c630bed81318c2f8604c630dd544318c27f65c86309f997218c27d65c8630dd947218c37551c86309fd96218c27e65886309f596218c2de6388630b758e218c3765188630dd546218c27f65486309f595218c27c6548630b7d8d218c2dc6348630dd945218c37551486309fd94218c27e65086309f594218c3765108630
  | 20 => 0xc2fa6010f30be58043cc36f5294b309f99252cc27d6494b30d790e52cc35d4394b309f98652cc27d6194b309fd9152cc27c6454b309fd8552cc27c6154b30db54852cc27f65d0b309f99742cc27d65d0b30b798f42cc2dd63d0b309fd9642cc27e6590b309f59642cc2de6390b30b758e42cc27f6550b309f59542cc27c6550b30bed8142cc2f86050b309fd9442cc27e6510b309f59442cc2de6310b30b758c42cc36e52ccb30db54b32cc2fa60ccb30be58332cc2df64ccb30b759332cc35e52ccb30f394b32cc3cd52ccb30f390b32cc3cd42ccb30b798732cc2de60ccb30f698332cc3d960ccb30b7d9532cc35f654cb30b7d9132cc2dd644cb30f3d8932cc35e524cb30b718532cc2dc604cb30db94832cc36d520cb30be98032cc2f9600cb30ddd4651cc27e64947309f59251cc27e62947309f58a51cc27f64547309f19151cc35e4354730d750d51cc27f62547309f18951cc37551147309fd9741cc27e65d07309f59741cc2de63d0730b758f41cc27f65907309f99641cc27d65907309fd9541cc27d65507309f19541cc2df6350730b718d41cc27f65107309f99441cc27d6510730b798c41cc2dd6310730bb98841cc2ed6210730be98041cc2f96010730dd94731cc37551cc730be98331cc2f960cc730b759631cc35d658c730b7d9231cc2dd648c730d795231cc35c548c730b758a31cc35e528c730d754631cc2de608c730dd94431cc375510c730f54c431cc2fa600c730be58031cc2df640c730b759031cc35e540c730d715031cc2dd620c730d794831cc3d6610c730f594431cc35d510c730f554431cc3d7410c730f510431cc2de600c730f698031cc3d9600c7309fd9721cc27e65c87309f59721cc2de63c8730b758f21cc27f65887309f99621cc27d6588730b7d8e21cc2dc6388730be98221cc2f960887309fd9521cc27d65487309f19521cc2df6348730b718d21cc27f65087309f99421cc27d6508730b798c21cc2dd6308730cf95340cc33d54d0330b798f40cc2dd63d0330cf95140cc33d5450330b7d8d40cc2dc6350330b798c40cc2dd6310330bb98840cc2ed6210330bd98440cc2f56110330bd987548c2f561d5230d758f548c27e62d52309f58b548c27e61d5230dd987548c27661d52309f587548c37561d52309d587548c37a60d5230cfd52548c27e62952309f58a548c27e61952309f586548c33f64552309fd89548c27c62552309fd85548c27c6155230cf550548c2ee6215230bb588548c2f66115230bd584548c33e6415230d758c548c27e6215230db988548c26e62152309f588548c36d62152309b588548c27e6115230dd984548c27661152309f584548c37561152309d584548c37a6015230cf953438c33d54d0e30bb98b438c2ed62d0e30be983438c2f960d0e30cf951438c33d5450e30bdd8
  | 21 => 0x5110440ed50441102fa6010440be580411027f65cc4409f997311027d65cc440d794f311035d53cc440db94b311036d52cc440dd947311037551cc4409fd96311027e658c4409f596311035e538c440d754e311036e528c440db54a3110376518c440dd546311027f654c4409f595311027c654c440afd9131102bc644c440d794d311035d534c440db949311036d524c440dd9453110375514c4409fd94311027e650c4409f594311035e530c440d754c311036e520c440db5483110376510c440dd544311027f65c84409f997211027d65c8440d794f211035d53c8440db94b211036d52c8440dd947211037551c84409fd96211027e65884409f596211035e5388440d754e211036e5288440db54a21103765188440dd546211027f65484409f595211027c6548440afd9121102bc6448440b7d8d21102dc6348440d794d211035d5348440db949211036d5248440dd94521103755148440bed8121102f860484409fd94211027e65084409f594211035e5308440d754c211036e5208440db54821103765108440dd544211035e53d0040d754f401036e52d0040db54b401037651d0040dd547401039e53d0040e754f40103ae52d0040cf54b40103ad52d0040cb54b40103b651d0040ed54740102bd6490040cf952401035e5390040d754e401036e5290040db54a40103765190040dd54640102f96490040de95240103ba5490040f694e40103d95390040fa94a40103e95290040fc94640103795190040fc546401037151900409fd95401035e5350040d754d401036e5250040db54940103765150040dd54540102bf6550040cfd95401023f6550040e794d401039d5350040eb949401033d5250040eb549401032d5250040ed94540103b55150040afd81401033e5050040bed95401037b65500409ed9540102fb6450040eed91401037a5450040ee95140103da5350040f654d40103bb4350040ee50d40103ea5250040fa54940103f25150040de54540103f15150040dc545401035e63d53309f98b54cc27d62d53309f98754cc27d61d5330de58354cc33f5495330bb98a54cc2ed6295330d798e54cc27e6295330db98a54cc26e62953309f58a54cc36d62953309b58a54cc27e61953309f58654cc33f64553309fd8954cc27c62553309fd8554cc27c6155330cf55054cc33e6415330d798c54cc27e62153309f58854cc27e61153309f58454cc3796015330bb98b43cc2ed62d0f30cf95243cc33d5490f30be98243cc2f96090f30d759643cc35e5490f30e795243cc39d5490f30d715243cc2dd6290f30b798643cc2de6090f30f698243cc3d96090f30bdd8543cc2f46150f30b7d9543cc35f6550f30e7d9143cc35e5450f30d715143cc2df6250f30f5d8543cc2dc6150f30f518543cc2d46150f30b718143cc33e5410f30cf55043c
  | 22 => 0x840dbd85521036e6154840db585521036c6154840db981521036c6054840db10152102de6314840b758c521035e5314840d754c52102ee6214840db54852102f66114840bd584521033e54d0840b798f42102dd63d0840d794f421035d53d0840db94b421036d52d0840be98342102f960d08409f596421035e5390840d754e421036d52908409fd95421033e5450840d794d421035d5350840db949421035e5310840d754c421036e5210840db54842102fa6010840be580421027f65cc8409f997321027d65cc840d794f321035d53cc840db94b321036d52cc8409fd96321027e658c8409f596321035e538c840d754e321036e528c840db54a321027f654c8409f595321027c654c840d794d321035d534c840db949321036d524c840bed8132102f8604c8409fd94321027e650c8409f594321035e530c840d754c321036e520c840db54832102de63d4440b758f511035e53d4440d754f51102ee62d4440bb58b511036e52d4440db54b511035e5394440d754e511036e5294440db54a511037751944409f98e511027d63944409f98a511027d6294440ddd4e51103765394440f594e51103565394440dd54e51103d55394440d554e51103745394440ddd4a51103765294440f994a51103665294440dd54a51103e55294440d954a51103745294440dd19251103776394440dd98e51103756394440dd18e51103774394440dd90e51103754394440dd10e51103776294440dd98a51103756294440dd18a51103774294440dd90a51103754294440dd10a51103773294440dd8ca51103753294440dd0ca51103766094440dd182511035e5354440d754d511036e5254440db549511027f63544409f18d511027f62544409f18951103776554440ddd4d51103765354440f594d51103565354440dd54d51103d55354440d554d51103745354440ddd4951103765254440f994951103665254440dd54951103e55254440d954951103745254440dd99151103776354440dd98d51103756354440dd18d51103774354440dd90d51103754354440dd10d51103776254440dd98951103756254440dd18951103774254440dd90951103754254440dd10951103773254440dd8c951103753254440dd0c951103766054440dd18151103744054440b798c51102dd6314440d794c511035d5314440bb98851102ed6214440db948511036d5214440bd98451103755114440d794f411035d53d0440db94b411036d52d0440dd947411037551d0440be98341102f960d04409f596411035e5390440d754e411036e5290440db54a411037551904409fd9541102df6350440b718d411035e5350440d754d411036e5250440db54941103765150440b798c41102dd6310440d794c411035d5310440bb98841102ed6210440db948411036d5210440dd9444110375
  | 23 => 0xe98032502f9600c9409f98f515027d63d45409f98b515027d62d4540ddd4651502df6354540b718d51502ef6254540bb189515037551145409f98c515027d63145409f988515027d6214540de580515027e65d0540ddd4641503745190540be98241502f96090540b7d8d41502dc6350540ddd4541503745150540bed8141502f860505409f99441502de6310540b758c41502ee6210540bb58841502fa60105409f997315027d65cc5409f197315037751cc540dd147315027e658c5409f596315027c658c540d7d4e315035c538c540be98231502f9608c5409fd95315027e654c5409f195315027e650c5409f594315027c650c540af99031502bd640c540d7d4c315035c530c540ddd443150374510c540be98031502f9600c5409f997215027d65c85409f19721502be64c8540af59321503ad42c8540ddd47215037451c85409f996215027d65885409f196215036f5288540db14a21502fa6088540be582215027f65485409f995215027c6548540b7d8d21502dc6348540eb509215027e65085409f594215027c6508540af99021502bd6408540dbd48215036c5208540ddd4421503745108540be98021502f96008540eed0b40503b942d0140be58740502bd6290140eed4240502ee62d4c40bb58b53102f661d4c40bd587531035f5394c409f98a531027d6294c409f986531027d6194c40d7192531035f6294c40d798a531035d6294c40d718a531035f6194c40d7986531035d6194c40d7186531035e6094c40d7182531027f6254c409f189531027f6154c409f185531035f6554c40d7991531035f6254c40d7989531035d6254c40d7189531035f6154c40d7985531035d6154c40d7185531035e6054c40d7181531035c4054c40b798c531035d5314c40bb98853102ed6214c40bd98453102f56114c40d794f431035d53d0c40bb98b43102ed62d0c40be98343102f960d0c409f596431035d5390c409fd95431035e5350c40bdd8543102f46150c40d794c431035d5310c40be98043102f96010c40b798f52102dd63d4840d794f521035d53d4840bd98752102f561d4840d794e521035d5394840dbd4a521027e63948409f58e521027e61948409f586521036f5394840db94e52103ce5394840d394e521036d5394840f354e521034d5394840db14e521036c6494840dbd8e521036e6394840db58e521036c6394840dbd0e521036e4394840db50e521036c4394840dbd86521036e6194840db586521036c6194840db982521036c6094840d794d521035d53548409fd8d521027c63548409fd85521027c6154840dbd95521036f5354840db94d52103ce5354840d394d521036d5354840f354d521034d5354840db14d521036e6454840dbd8d521036e6354840db58d521036c6354840dbd0d521036e4354840db50d521036c4354
  | 24 => 0x529027c6154a40b798c52902dd6314a40db54852902f66114a40bd58452902de63d0a40b758f429036e5290a40db54a42902fa6090a40be582429036e5250a40db54942902fb6050a40be181429027f65cca409f997329027d65cca40d794f329035d53cca409fd96329027e658ca409f596329027f654ca409f595329027c654ca40d794d329035d534ca409fd94329027e650ca409f59432902fa600ca40be58032902de63d4640b758f519037751946409f98e519027d63946409f98a519027d6294640de982519027f63546409f18d519027f62546409f18951903755114640dd94641903755190640be98241902f96090640b7d8d41902dc6350640dd94541903755150640bed8141902f86050640b798c41902dd6310640bb98841902ed6210640ed50441902f960106409fd97319027e65cc6409f597319037651cc640dd547319027f658c6409f996319027d658c640d794e319035d538c640be98231902f9608c6409fd95319027d654c6409f19531902bf644c640af191319027f650c6409f994319027d650c640d794c319035d530c640dd9443190375510c640be98031902f9600c6409fd97219027e65c86409f597219027f65886409f996219027d6588640dd94621903755188640be98221902f960886409fd95219027d65486409f19521902bf6448640af19121902df6348640b718d21903765148640dd545219027f65086409f994219027d6508640be98021902f96008640af597409033d65d0240cf54b40902f965d0240de59740902f961d02409f98b535027d62d4d409f987535027d61d4d40d7d4e53502ef6254d40bb18953502f76154d40bd185535035d5314d409f988535027d6214d409f984535027d6114d409f99743502ee62d0d40bb58b435035f5390d40d714e43502fa6090d40be582435035f5350d40d714d43502f76150d40bd18543502fb6050d40be181435027e6510d409f98f525027d63d49409f987525027d61d4940dbd4a52502df6354940b718d52502f76154940bd185525036d52149409f98c525027d63149409f984525027d61149409f99742502de63d0940b758f42502be65d0940cf997425039e63d0940e758f425033c52d0940af98342502bd6490940dbd4a425036c5290940be98242502f96090940dbd49425036c5250940bed8142502f86050940ebd8942503af5250940cf14942503ac5250940eed8142502bc6050940ee181425027e6510940af99042503ad42109409f997325027d65cc9409f197325036f52cc940db14b32503ad42cc9409f996325027d658c9409f19632502be648c940af592325035f538c940d714e325027f654c9409f995325027c654c9409f994325027d650c9409f19432502be640c940af590325035f530c940d714c325036f520c940db14832503ad420c940b
  | 25 => 0x35f5394f409f98a53d027d6294f409f98653d027d6194f40bdd8553d02f46154f409fd8953d027c6254f409fd8553d03776154f409dd8553d027c6154f40dd18553d02746154f40d754c53d035e53d0f40d754f43d02ee62d0f40bb58b43d02fa60d0f40be58343d02f76150f40bd18543d035e5310f40d754c43d02fa6010f40be58043d02de63d4b40b758f52d036f5294b409f98e52d027d6394b409f98652d027d6194b409fd8d52d027c6354b409fd8552d027c6154b40db54852d02de63d0b40b758f42d036e52d0b40db54b42d02fa60d0b40be58342d039e63d0b40e758f42d033e52d0b40eb94b42d03ad52d0b40af98342d03ba60d0b40ee58342d02bf6550b40cfd9542d03af6250b40ebd4942d033e5250b40eb14942d02bc6050b40db94842d036d5210b40eb50842d02fa6010b40be58042d027f65ccb409f99732d027d65ccb40db94b32d036d52ccb40eb50b32d027f658cb409f99632d027d658cb40af99232d02bd648cb40d794e32d035d538cb409fd9532d027d654cb409f19532d02fb604cb40be18132d027f650cb409f99432d027d650cb40af99032d02bd640cb40d794c32d035d530cb40db94832d036d520cb40eb50832d037751947409f98e51d027d63947409f98a51d027d6294740b7d8d51d02dc63547409fd8d51d035f635474097d8d51d027c6354740d718d51d025c63547409fd8951d027c6254740b798c51d02dd6314740bb98851d02ed6214740dd54451d037651d0740dd54741d02fa60d0740be58341d02df6350740b718d41d02de6310740b758c41d02ee6210740bb58841d03765110740dd54441d02fa6010740be58041d027f65cc7409f99731d027d65cc740d794f31d035d53cc7409fd9631d027e658c7409f59631d027f654c7409f59531d027c654c740d794d31d035d534c7409fd9431d027e650c7409f59431d02be640c740af59031d027f65c87409f99721d027d65c8740af99321d02bd64c8740db94b21d036d52c8740eb50b21d027f65887409f99621d027d65887409fd9521d027d65487409f19521d02df6348740b718d21d036e5248740db54921d03ad4248740bed8121d02f860487409fd9421d027e65087409f59421d02be6408740af59021d02f661d4e40bd587539035f5394e409f98a539027d6294e409f986539027d6194e40bbd8953902ec6254e409fd89539036f6254e409bd89539027c6254e40db189539026c6254e409fd85539027c6154e40d754c53902ee62d0e40bb58b439035e5390e40d754e43902fa6090e40be582439035e5350e40d754d43902f76150e40bd18543902fb6050e40be181439036f5294a409f98e529027d6394a409f986529027d6194a40b7d8d52902dc6354a409fd8d529035f6354a4097d8d529027c6354a40d718d529025c6354a409fd85
  | 26 => 0x315021d798c540865e63150219f58c540875d63150219758c540867e6215021db988540866e62150219f984540877661150219f980540877a60150219e980540867d6015021de580540867960150219f993530867d64d4c219f98b530876e62d4c219f987530877661d4c219f983530867d60d4c219f596530875f5394c219f992530867d6494c219f982530867d6094c219fd91530867c6454c21d7d8d530867f6054c219f18153086be6414c21af590530875d5314c21be98053086f96014c219f990530873e6414c218f990530867d6414c21cf590530863d6414c219f98c530875e6314c219f988530876e6214c219f98453087766114c219f980530877a6014c219e980530867d6014c21de58053086796014c219fd97430867e65d0c219f597430867c65d0c21cf953430873d54d0c21bb98b43086ed62d0c219fd96430867e6590c219f596430867c6590c21d794e430875d5390c219fd95430867e6550c219f595430867c6550c21cf951430873d5450c21d794d430875d5350c21bdd8543086f46150c219fd94430867e6510c219f594430867c6510c219f992520867d64948219f98e520867d63948219f59742086de63d0821b758f420867f65908219f596420873e5490821cf552420876e5290821bd98642086f561908219fd95420876e52508219fd94420867d6510821cf950420873d5410821eb50842086f66110821bd584420867d65cc8219fd96320867d658c821d794e320875d538c821bd98632086f5618c8219fd95320867f650c8219f594320875e530c821d754c32086f6610c821bd584320867e64944219f592510867e63944219f58e510867d65d04219fd96410867d6590421cf952410873d5490421bb98a41086ed62904219fd9541086df6350421b718d410867f65104219f994410867d65104219f194410873e5410421cf55041086de6310421b758c41086ee6210421bb58841086fa6010421be580410867d65cc4219fd96310867d658c421d794e310875d538c421bb98a31086ed628c4219fd95310867f650c4219f994310867d650c4219f194310875e530c421d754c31086ee620c421bb588310876f54c8421db55321086ed6288421db94a21086f56288421dd94a21087e652884219fd9521086df6348421b718d21086ef6548421dbd95210866f6548421dbd51210876d5448421f3d8d21087cc6348421bbd85210876e5148421f98c521087e53148421bdd95210877765484219dd9521087d76348421f518d21086f76248421f9d8921087765248421f994921087e63248421f94c9210877b50940219f992500867d64940219f98e500867d63940219fd91500867c64540219fd8d500867c6354021dd88550087752154021af99050086bd6414021b798c50086dd6314021de54050086ee62d4f40bb58b53d0
  | 27 => 0x219fd97434867e65d0d219f597434867c65d0d21d7d4f434875c53d0d21bb98b43486ed62d0d219fd96434867e6590d219f596434867c6590d21d7d4e434875c5390d219fd95434867e6550d219f595434867c6550d21d7d4d434875c5350d21bdd8543486f46150d219fd94434867e6510d219f594434867c6510d21d7d4c434875c5310d21bb98843486ed6210d21bd98443486f56110d219f997424873f54d0921cf15342486de63d0921b758f424875f53d0921d714f42486f661d0921bd587424867e6590921d7d4e424875c5390921bb996424876e6590921bb592424876e5490921db15242487cf5390921db94e424876c5390921f314e424874c5390921bb986424867c6550921cfd51424873c5450921d7d4d424875c5350921bdd8542486f46150921db195424866c6550921ebd9142487af5450921db951424876c5450921eb151424872c5450921f3d4d424876e5350921db14d42487cc5350921d314d42487e76150921bb18542487e461509219f994424875f5310921d714c42486ee62109219f997324875f53cc921d714f32486f661cc921bd587324867e658c921d7d4e324875c538c9219f195324875f534c921d714d32486f7614c921bd185324867e650c921d7d4c324875c530c921f34c8324867e65d0521cfd53414873c54d0521d7d4f414875c53d0521bb98b41486ed62d05219f996414875f5390521d714e414867f65505219f595414867c6550521cfd51414873c5450521b7d8d41486dc6350521d7d4d414875c5350521bbd8941486ec62505219f99441486de6310521b758c414875f5310521d714c41486ee6210521bb58841487b54110521be98041486f960105219f997314875f53cc521d714f31486ee62cc521bb58b314867e658c521d7d4e314875c538c5219fd95314867d654c5219f195314875f534c521d714d31486ef624c521bb189314867e650c521d7d4c314875c530c521f54c4314875f53c8521d714f21487d753c8521f514f21487e642c8521f950b21486f560c8521d7d4e214875c5388521bbd9221486ed6488521f3d4e21487cc5388521f9d46214875f53d4121d714f504867e64d41219f593504867e63d41219f58f504876e42d4121db50b50486de6394121b758e504875f5394121d714e504877b5094121afd9150486bc6454121b7d8d50486dc6354121d7d4d504875c5354121d7d4c504875c5314121de540504867e64141219f590504867e63141219f58c504867e63d50219f58f540867e62d5021db98b540867e61d5021dd987540867e60d50219f583540867d6595021cfd52540867e63950219f58e540867e60950219f582540873f64550219fd8d540867c63550219fd81540867c6055021cf55054086de6315021b758c54086fa6015021be580540867e6415021cf990540867e6
  | 28 => 0x980538867d6014e219fd97438867e65d0e219f597438867c65d0e21bb98b43886ed62d0e219fd96438867e6590e219f596438867c6590e21d794e438875d5390e219fd95438867e6550e219f595438867c6550e21d794d438875d5350e21bdd8543886f46150e219fd94438867e6510e219f594438867c6510e21bd98443886f56110e21cf953428873d54d0a21b798f42886dd63d0a21bd98742886f561d0a21cf951428873d5450a21bdd8542886f46150a21eb508428875e53cca21d754f32886f661cca21bd587328875f538ca21d714e328875e534ca21d754d32886f7614ca21bd185328875f530ca21d714c328873e5490621cf55241886ee6290621bb58a41886df6350621b718d418873e5410621cf55041886de6310621b758c41886ee6210621bb58841887b54110621be98041886f96010621d794e318875d538c621bb98a31886ed628c621d794c318875d530c621bb98831886ed620c621f54c431886ed65c8621db597218876f54c8621db55321886f565c8621dd59721886f560c8621b798f50886dd63d4221b798e50886dd6394221ded42508867e64942219f592508867e6394221d798e508865e63942219f58e508875d63942219758e508867f64542219f191508867f63542219f18d508877950142219f98f544867d63d51219f983544867d60d5121cfd5254486de6395121b758e544867e64951219f98e544875e63951219798e544867d6395121d758e544865d63951219f58a544876d62951219f586544877561951219f982544867d6095121b7d8d54486dc6355121bed8154486f86055121cfd91544867f6355121d7d8d544865f63551219f18d544875c63551219718d544867f6255121dbd89544867f6155121ddd85544867f6055121ded81544867b60551219f181544877860551219e181544867e6515121cf550544873e64151219f98c544867d6315121db588544867e60151219f580544867e64d4d219f593534867e60d4d219f583534875f54d4d21d7953534875d54d4d21d7153534875f64d4d21d7993534875d64d4d21d7193534875f62d4d21d758b534875f61d4d21d7587534875f60d4d21d7983534875d60d4d21d7183534875f5394d219f992534867d6494d219f98e534865e6394d219f58a534876d6294d219f58653487756194d219f982534867d6094d219fd91534867c6454d21d7d8d534867f6254d21dbd89534867f6154d21ddd85534867f6054d219f181534867e6514d21d754c534867e6414d219f590534875e6314d219f980534867d6014d21b7994534875e6514d2197994534875f5414d21d7950534875d5414d21d7150534875f6414d21d7990534875d6414d21d7190534875f6214d21d7588534875f6114d21d7584534875d2114d21d7d80534875e6014d21d7580534875c6014d
  | 29 => 0x4c867e63153219f58c54c876e6215321dd58454c867e60153219f58054c86be64d4f21af59353c867e64d4f21cf99353c863e64d4f219f59353c873d64d4f218f59353c876e62d4f21dd58753c867e60d4f219f58353c875f5394f219f99253c867d6494f219f98253c867d6094f219fd9153c867c6454f21d7d8d53c867f6054f219f18153c875d5314f219f99053c867d6414f21d798c53c876e6214f21dd58453c867e6014f219f58053c867f65d0f219f99743c867d65d0f219f19743c875e53d0f21d754f43c86ee62d0f21bb58b43c867f6590f219f99643c867d6590f219f19643c873e5490f21cf55243c875f5390f21d714e43c867f6550f219f99543c867d6550f219f19543c875f5350f21d714d43c86f76150f21bd18543c867f6510f219f99443c867d6510f219f19443c873e5410f21cf55043c875e5310f21d754c43c86ee6210f21bb58843c86de63d0b21b758f42c873e5490b21cf55242c86f66190b21bd58642c876d6590b21db95242c87ae5490b21eb55242c876c5490b21db94e42c876c5390b21bb98642c87e66190b21f958642c86ef6550b21dbd9542c87af6450b21db95142c876c5450b21db94d42c876c5350b21bb18542c873e5410b21cf55042c86f66110b21bd58442c875e538cb21d754e32c86f6618cb21bd58632c875e530cb21d754c32c87cd320cb21bd98432c86f5610cb21cf95341c873d54d0721bb98b41c86ed62d0721cf95141c873d5450721b7d8d41c86dc6350721bbd8941c86ec6250721b798c41c86dd6310721bb98841c86ed6210721be98041c86f96010721d794f31c875d53cc721bb98b31c86ed62cc721d7d4e31c875c538c721d794d31c875d534c721bbd8931c86ec624c721d7d4c31c875c530c721ded4250c867e64943219f59250c867e63943219f58e50c867f64543219f19150c867f63543219f18d50c876e4254321db50950c86be6414321af59050c86de6314321b758c50c877950143219f98f548867d63d5221db58b548877661d52219f983548867d60d5221cfd52548867e63952219f58e548867e60952219f582548873f64552219fd8d548867c63552219fd81548867c6055221cf55054886de6315221b758c54886fa6015221be580548873e64152219f98c548875e63152219798c548867d6315221d758c548865d6315221db588548877661152219f980548877a60152219e980548867d6015221de58054886796015221be98353886f960d4e219f993538867d64d4e21db58b538877661d4e219f983538877a60d4e219e983538867d60d4e21de583538867960d4e21d7d4e538867e6494e219f592538867e6094e219f582538867f6454e219f191538875f6354e219fd81538867c6054e21d754c538867e6414e219f590538875e6314e21db58853887766114e219f
  | 30 => 0x6e5290831db54a420c6f66190831bd586420c67f65508319f595420c67c6550831cf951420c73d5450831b7d8d420c6dc6350831db949420c76d5250831bdd85420c6f461508319fd94420c67e65108319f594420c76e52cc831db54b320c6f661cc831bd587320c67d658c831b7596320c75d658c831b7992320c6dc648c831d7d52320c75d548c831b798a320c75d528c831b7586320c6dd608c8319fd95320c76e520c831db548320c6f6610c831bd584320c6de640c831b7190320c75f540c831d7550320c6de620c831f3988320c7ce520c831d7548320c7cd520c831d3548320c7ce420c831f3508320c7d6610c831b7584320c7d5610c831b5584320c6dd600c8319f992510c67d6494431d7d0e510c75c4394431d78ca510c75c32944319f597410c6f565d0431dd597410c77754d0431dd553410c7d763d0431bd58f410c7d463d0431dd94f410c7d743d0431f510f410c7d632d0431f50cb410c6f560d04319fd96410c67d6590431cf952410c73d5490431b798e410c6dd6390431bd986410c67f6550431b7d8d410c6dc63504319fd94410c67e65104319f594410c67c6510431cf950410c73d5410431b798c410c6dd6310431bb988410c6ed6210431be980410c6f96010431bd594410c77565104319d594410c6f66410431ed990410c7775410431ed950410c7755410431ed550410c7355410431f598c410c6f56310431f558c410c7765310431f5d0c410c7d44310431f9988410c7e56210431f58c8410c7d43210431fc980410c6f56010431fc580410c6f16010431b7993310c6dc64cc431d7d53310c75d54cc431b798b310c7d741cc431f5107310c6dd60cc431b758e310c75e538c431bd992310c6f4648c431bd58e310c776538c431f594e310c7d7438c431f510e310c7d6328c431f50ca310c6f5608c4319fd95310c6df654c431d7d95310c65f654c431b7991310c6dc644c431d7d51310c75d544c431b7189310c6df614c431d7945310c7d7414c431f5105310c6df604c431bdd95310c777654c4319dd95310c6f6644c431bd191310c6f7634c431f5d8d310c776534c431f594d310c7d7434c431f510d310c7d7324c431f54c9310c6f7604c431ded42500c67e64940319f592500c67e62940319f58a500c75e3294031d70ca500c67f64540319f191500c67f62540319f189500c6be6414031af590500c6ee6214031bb588500c7795014031b798f54c86dd63d53219f98f54c875e63d53219798f54c867d63d5321d758f54c865d63d5321db98b54c877561d53219f98354c867d60d5321cfd5254c86de6395321b758e54c867e6395321d798e54c865e63953219f58e54c875d63953219758e54c876e62953219f98254c867d6095321cfd9154c867f63553219f18d54c867f60553219f18154c873d5415321cf9905
  | 31 => 0xd4931af992524c6bd6494931dbd4a524c76d52149319f990524c67d6414931d790c524c75d43149319f980524c67d60149319f997424c67d65d09319f197424c73f54d0931cf153424c6de63d0931b758f424c67e65909319f596424c67c6590931dbd4a424c76c52909319fd95424c67e65509319f195424c73f5450931cf151424c76f5250931db149424c67e65109319f594424c67c6510931b798c424c6dd6310931bd984424c6f561109319f997324c76f528c931db14a324c6f6618c931bd586324c76f524c931db149324c6f7614c931bd185324c67e650c931f34c8324c67e65d0531cfd53414c73c54d0531b798f414c6dd63d05319f996414c67f65505319f595414c67c6550531cfd51414c73c5450531b7d8d414c6dc63505319f994414c6de6310531b758c414c6ee6210531bb588414c7b54110531be980414c6f96010531dd953314c77454cc531f590f314c7d543cc531b7d92314c6dd648c531d7952314c75c548c531d714a314c7d7518c5319f993504c67d64d4131d790f504c75d43d41319f98b504c67d62d4131ddcc7504c75e31d4131ded42504c6bf6454131af191504c6ef6254131bb189504c77950141319f990504c67d64141319f988504c67d62141319f98f540c75e63d50319f98b540c67d62d50319f987540c77661d50319f983540c67d60d50319f596540c73f54950319f98a540c67d62950319f982540c67d6095031cfd91540c75c63550319fd89540c67c6255031dd185540c67f60550319f181540c73d5415031bb988540c6ed6215031be980540c6f960150319f990540c73e64150319f98c540c75e63150319798c540c67e6215031db988540c66e62150319f588540c76d62150319b588540c67e6115031dd984540c67e6015031de980540c67a60150319f580540c77960150319e580540c67e6494c319f592530c67d65d0c31bb98b430c6ed62d0c31b7597430c75d65d0c3197597430c75f54d0c31d7553430c6de62d0c31f398b430c6ce62d0c31f358b430c7d761d0c31b7587430c7d461d0c31b7583430c67f6590c319f596430c73e5490c31cf552430c6de6390c31d794e430c6f66190c31bd586430c67f6550c31d794d430c6f76150c319fd94430c67d6510c31cf950430c73d5410c31bd984430c6f56110c31d7594430c65d6510c31b7990430c79e6410c31d7d50430c79e5410c31d7550430c79d5410c31b7988430c7d66110c31b7584430c7d56110c31b7580430c76f52948319f992520c67d64948319f982520c67d60948319fd91520c67c64548319fd81520c67c6054831af990520c6bd6414831db548520c6fa6014831be580520c67f65d08319f997420c67d65d0831cf953420c73d54d0831b798f420c6dd63d08319fd96420c67e65908319f596420c6de6390831b758e420c7
  | 32 => 0x1cf953438c73d54d0e31bb98b438c6ed62d0e31bd987438c6f561d0e31d7597438c75f54d0e31e7953438c75d54d0e31e7553438c6de62d0e31f398b438c6ce62d0e31f358b438c7d661d0e31b7587438c7d561d0e31b7583438c73e5450e31cf551438c6f76150e31bd185438c6dd6510e31d7594438c79e6410e31d7d50438c75d5410e31b7988438c6dd6110e31b7580438c6fa60d4a31be583528c76f5294a319f992528c67d6494a319f982528c67d6094a319fd91528c67c6454a319fd81528c67c6054a31db548528c67f65d0a319f997428c67d65d0a31b798f428c6dd63d0a319fd96428c67e6590a319f596428c6de6390a31b758e428c76e5290a31db54a428c67f6550a319f595428c67c6550a31b7d8d428c6dc6350a31db949428c76d5250a319fd94428c67e6510a319f594428c6f66110a31bd584428c76e528ca31db54a328c6f6618ca31bd586328c6de648ca31b7192328c75f548ca31d7552328c7ce528ca31d754a328c7cd528ca31f5986328c6dd618ca31f5586328c6dd608ca31db949328c76d524ca31bdd85328c6f4614ca31b7594328c75d650ca31b7990328c6dc640ca31d7d50328c75d540ca31f3988328c75d520ca31f3908328c7cd420ca31b7584328c6dd600ca31cf952418c73d5490631b798e418c6dd6390631b7d8d418c6dc6350631cf950418c73d5410631b798c418c6dd6310631bb988418c6ed6210631ed504418c6fa6010631be580418c6dd65cc631d7597318c6de64cc631b7193318c75f54cc631d7553318c6de62cc631b7583318c6f565cc631dd597318c77654cc631dd153318c6ee62d4231bb58b508c77b50942319f992508c67d64942319f98a508c67d6294231d78ca508c75c32942319fd91508c67c64542319fd89508c67c6254231ddcc5508c77950142319f98b544c67d62d51319f983544c67d60d5131cfd52544c6ee6295131bb58a544c67e64951319f58e544c75d63951319f98a544c76e62951319b98a544c67d6295131db58a544c66d62951319f586544c77561951319f982544c67d6095131cfd91544c67f6355131d7d8d544c65f63551319fd89544c67c62551319fd85544c77761551319dd85544c67f60551319f181544c67e6515131cf550544c73e6415131d758c544c67e62151319f588544c67e60151319f580544c67e65d0d31cfd53434c73c54d0d31bb98b434c6ed62d0d31bd987434c6f561d0d319f996434c6de6590d31d7996434c65e6590d31b7592434c75e5490d31d7152434c6de6190d319f195434c73f5450d31cf151434c6f76150d31bd185434c75c6550d3197195434c79f6450d31e7d51434c75e5450d31d7151434c79c5450d31f5d85434c6dc6150d31f5185434c6d46150d319f994434c6de6310d319f993524c67d64d49319f983524c67d60
  | 33 => 0x950107784254041decc9501077a3254041de4c950107783254041de985501077b4154041de90550107724154041de50550107714154041de10550106de6314041b758c501075e5314041d754c50106ee6214041bb588501076e5214041db54850106fa6014041de540501075e63d53319f98b54cc67d62d5331dd58754cc67e60d53319f58354cc73f5495331bb98a54cc6ed6295331d798e54cc67e6295331db98a54cc66e62953319f58a54cc76d62953319b58a54cc67e60953319f58254cc73f64553319fd8954cc67c6255331ddd8554cc67f60553319f18154cc73d5415331cf99054cc75e63153319f98854cc67d6215331dd58454cc67e60153319f58054cc6ee62d0f31bb58b43cc73e5490f31cf55243cc6f66190f31bd58643cc75d6590f31d795243cc79e5490f31e755243cc75c5490f31b798643cc7d66190f31f558643cc6f46150f31b7d9543cc75f6550f31e7d9143cc75e5450f31d715143cc7d76150f31b718543cc7d46150f31b518543cc73e5410f31cf55043cc6f66110f31bd58443cc76f5294b319f99252cc67d6494b31d790e52cc75d4394b319f98252cc67d6094b319fd9152cc67c6454b319fd8152cc67c6054b31db54852cc67f65d0b319f99742cc67d65d0b31b798f42cc6dd63d0b319fd9642cc67e6590b319f59642cc6f66190b31bd58642cc67f6550b319f59542cc67c6550b31bdd8542cc6f46150b319fd9442cc67e6510b319f59442cc6de6310b31b758c42cc76e52ccb31db54b32cc6f661ccb31bd58732cc76e520cb31db54832cc7cd320cb31bd98432cc6f5610cb31cf95341cc73d54d0731b798f41cc6dd63d0731bd59741cc77565d0731ddd5341cc7b654d0731dd55341cc7b554d0731f598f41cc6f563d0731f558f41cc7d643d0731f550f41cc6f560d0731cf95141cc73d5450731b7d8d41cc6dc6350731b798c41cc6dd6310731bb98841cc6ed6210731be98041cc6f96010731bd59441cc7756510731ed99041cc7775410731dd55041cc7d66310731bd58c41cc7d56310731b558c41cc7d64310731f550c41cc7e66210731f958841cc7f26010731bd58041cc7f16010731bc58041cc77b50943319f99250cc67d64943319f98a50cc67d62943319fd9150cc67c6454331d790d50cc75d43543319fd8950cc67c6254331de54050cc75d63d52319f98b548c67d62d5231dd987548c67e60d52319f583548c73f54952319f98a548c67d62952319f982548c67d6095231cfd91548c75f63552319fd89548c67c62552319fd81548c67c6055231cf550548c6ee6215231bb588548c6fa6015231be580548c73e6415231d758c548c67e6215231db988548c66e62152319f588548c76d62152319b588548c77661152319f980548c77a60152319e980548c67d6015231de580548c679601523
  | 34 => 0x1075e5390841d754e421076d52908419fd95421075e5350841d754d421076e5250841d794c421075d5310841db948421076d5210841eb50842106f66110841bd584421067f65cc8419f997321067d65cc841d794f321075d53cc841db94b321076d52cc8419fd96321067e658c8419f59632106be648c841af592321075e538c841d754e321076e528c841db54a32106f6618c841bd586321067f654c8419f595321067c654c841d794d321075d534c841db949321076d524c841bdd8532106f4614c8419fd94321067e650c8419f594321075e530c841d754c321076e520c841db548321075e53d0441d754f411076e52d0441db54b411079e53d0441e754f41107ae52d0441eb54b41106bd6490441cf952411075e5390441d754e411076e5290441db54a41106f56490441dd95241107b65490441bd98e41107d65390441f554e41107e65290441f954a411067f6550441b7d8d41106dc6350441d794d411075d5350441db949411076d5250441afd95411073f65504418fd95411079f6350441e718d411079e5350441e754d41107ae5250441eb54941106bf6150441cf94541106f76550441ddd9541106776550441bdd9141107b76450441dd95141107b65450441f5d8d41106f46350441f518d41106d46350441f594d41107d55350441edd0d41107b54350441f994941107e55250441edd0941107b54250441b798f50106dd63d4041d794f501075d53d4041bb98b50106ed62d4041db94b501076d52d4041d794e501075d5394041db94a501076d5294041ded42501067e63940419f58e501067e62940419f58a501077b5394041de94e50107da5394041d694e50107795394041f654e50107595394041de14e501077b5294041de94a50107ea5294041da94a50107795294041fa54a50107695294041de14a50107bb4194041fc90650107b94194041fc50650107786494041ded8e501077a6394041de58e50107786394041ded0e501077a4394041de50e50107784394041ded8a501077a6294041de58a50107786294041ded0a501077a4294041de50a50107784294041decca501077a3294041de4ca50107783294041de186501077b4194041de90650107794194041d794d501075d5354041db949501076d52540419fd8d501067c63540419fd89501067c6254041dd90550107754154041ded95501077b5354041de94d50107da5354041d694d50107795354041f654d50107595354041de14d501077b5254041de94950107ea5254041da94950107795254041fa54950107695254041de14950107bb4154041fc90550107b94154041fc505501077a6454041ded8d501077a6354041de58d50107786354041ded0d501077a4354041de50d50107784354041ded89501077a6254041de58950107786254041ded09501077a4254041de5
  | 35 => 0x56190941d7d4d425075c5350941dbd49425076c5250941bdd8542506f461509419f994425075f5310941d714c425067e65cc9419f597325067c65cc941d7d4f325075c53cc9419f996325067d658c9419f196325075f538c941d714e325067f654c9419f995325067c654c941d7d4d325075c534c9419f994325067d650c9419f19432506be640c941af590325075f530c941d714c32506f6610c941bd584325075f53d0541d714f41507d753d0541dd14f41507d453d0541d514f41506f560d0541d7d4e415075c5390541e7d4e415079c5390541edd46415075f53d4141d714f505067e63d41419f58f505067e62d41419f58b50506de6394141b758e505075f5394141d714e505077b5094141b7d8d50506dc6354141d7d4d505075c5354141bbd8950506ec6254141d7d4c505075c5314141de540505067e63141419f58c505067e62141419f58850506ee62d4c41bb58b53106fa60d4c41be583531075f5394c419f98a531067d6294c419f982531067d6094c41f5186531075c6494c41d7d8a531075e6294c41d758a531075c6294c41d7986531075c6194c41d7d82531075e6094c41d7582531075c6094c419fd89531067c6254c41dd185531067f6054c419f181531075f6554c41f5185531075e6454c41d7d89531075e6254c41d7589531075c6254c41d7985531075c6154c41d5185531075c4154c41d7d81531075e6054c41d7581531075c6054c41b798c531075d5314c41bb98853106ed6214c41be98053106f96014c41d794f431075d53d0c41bb98b43106ed62d0c41bd98743106f561d0c419f596431075d5390c419fd95431075e5350c41bdd85431075e5310c41d754c43106f66110c41bd58443106de63d4841b758f521075e53d4841d754f52106fa60d4841be583521075e5394841d754e521076f52948419f98e521067d63948419f982521067d6094841dbd4e521076e5394841f394e521074e5394841db54e52107cd5394841d354e521076c5394841db192521076f6394841db98e521076d6394841db18e521076f4394841db90e521076d4394841db10e521076e6194841db186521076f6094841db982521076d6094841db182521075e5354841d754d521067f63548419f18d521067f60548419f181521076f6554841dbd4d521076e5354841f394d521074e5354841db54d52107cd5354841d354d521076c5354841db991521076f6354841db98d521076d6354841db18d521076f4354841db90d521076d4354841db10d521076e6154841db185521076c4154841dbd81521076e6054841db581521076c6054841b798c52106dd6314841d794c521075d5314841bb988521076d5214841be98052106f96014841b798f42106dd63d0841d794f421075d53d0841db94b421076d52d0841bd98742106f561d08419f59642
  | 36 => 0xb41db54b42d06f661d0b41bd58742d076e5210b41db54842d06f66110b41bd58442d067f65ccb419f99732d067d65ccb41db94b32d076d52ccb419fd9632d067e658cb419f59632d075e538cb41d754e32d06f6618cb41bd58632d067f654cb419f59532d067c654cb41bdd8532d06f4614cb419fd9432d067e650cb419f59432d06be640cb41af59032d075e530cb41d754c32d076e520cb41db54832d077b50943419f98e50d067d63943419f98a50d067d62943419fd8d50d067c63543419fd8950d067c6254341b798c50d06dd6314341bb98850d06ed6214341de54050d075f5394e419f98a539067d6294e419f982539067d6094e419fd89539067c6254e419fd81539067c6054e41d754c53906ee62d0e41bb58b439075e5390e41d754e43906f66190e41bd586439075e5350e41d754d43906f76150e41bd185439076f5294a419f98e529067d6394a419f982529067d6094a41b7d8d52906dc6354a419fd8d529075f6354a4197d8d529067c6354a41d718d529065c6354a419fd81529067c6054a41db54852906de63d0a41b758f429076e5290a41db54a42906f66190a41bd586429076e5250a41db54942906f76150a41bd18542907ad4210a419fd97329067e65cca419f597329067f658ca419f996329067d658ca41af99232906bd648ca419fd95329067d654ca419f195329067f650ca419f994329067d650ca41bd98432906f5610ca41af597419073d65d0641bd597419077565d0641dd94f41906f560d0641b798e50906dd6394241ded42509067e6394241d798e509065e63942419f58e509075d63942419758e509067e62942419f58a509067f63542419f18d509067f62542419f189509077950142419f98b535067d62d4d419f983535067d60d4d41d7d93535075f62d4d41d798b535075d62d4d41d718b535075f61d4d41d7587535075f60d4d41d7983535075d60d4d41d7183535075f5394d41d754c535067e6214d419f588535067e6014d419f58053506de6514d41d7994535075f6414d41d7d88535075e6214d41d7588535075c6214d41d7d84535075d6114d41d7504535075f6014d41d7980535075d6014d41d7180535067e65d0d41d714f43506ee62d0d41bb58b435075f5390d41d714e43506f66190d41bd586435075f5350d41d714d43506f76150d41bd185435067e6510d41d7d4c435075f53d4941d714f525067e63d49419f58f525067e60d49419f58352506de6394941b758e525075f5394941d714e525076f5294941b7d8d52506dc6354941d7d4d525075c5354941bed8152506f86054941d7d4c525075c5314941db548525067e63149419f58c525067e60149419f580525067e65d0941b798f42506dd63d0941d7d4f425075c53d0941d7d4e425075c5390941dbd4a425076c5290941bd98642506f
  | 37 => 0x9e980540ca7d6015032de580540ca7960150329f992530ca7d6494c329f597430caed62d0c329fd96430ca7d6590c32cf952430cb3d5490c32bb98a430caed6290c32d7596430ca5d6590c32b7592430cb5e5490c32e7952430cb9d5490c32d7152430cbce6290c32b758a430cbcd6290c32b7986430cade6090c329fd95430caf76150c32bd185430cadf6550c32d7d95430cb9f6450c32d7951430cb5c5450c32b7d89430cbce6250c32f3589430cbd76150c32b7185430cbd46150c32b5185430cadc6050c329fd94430ca7d6510c32cf950430cb3d5410c32b798c430caee6210c32bb588430ca7e64948329f592520cb5e4394832d750e520ca7d65d0832b798f420cadd63d08329fd96420ca7d6590832cf952420cb3d5490832b798e420cadd6390832bb596420cb6d65908329b596420caed6490832db952420cbae5490832eb552420cb6c5490832f398e420caed6390832f358e420cb6e5390832f390e420cbcd4390832bb982420ca7f6550832bbd95420cb6f6550832ebd91420cb6e5450832db151420caef6350832f398d420cbcd6350832db94d420cbce4350832f350d420caec60508329fd94420ca7e65108329f594420ca7c6510832cf950420cb3d5410832b798c420cadd6310832bb988420cadf64cc832b7593320cbce42cc832f350b320cade61cc832b7983320cadd638c832d794e320caef648c832bb592320caed638c832db94e320cbce538c832f390e320cbcd438c832bb982320ca7f654c832b7d95320cb5f654c83297d95320cadf644c832b7591320cadf624c832d7949320cbce424c832f3509320cadc614c832b7181320caef654c832dbd95320ca6f654c832bbd91320caed644c832bbd8d320cbcf634c832db94d320cbce534c832f390d320cbcd434c832bb181320cb7751944329f992510ca7d64944329f982510ca7d60944329fd91510ca7c6454432d790d510cb5d4354432db909510cb6d42544329fd81510ca7c6054432af990510cabd6414432dd544510cafa6014432be580510cb7b50940329f992500ca7d64940329f986500ca7d61940329fd91500ca7c6454032d790d500cb5d4354032db909500cb6d4254032d7cc9500cb5d32540329fd85500ca7c6154032af990500cabd6414032bd984500caf56114032de540500caee62d4f41bb58b53d075f5394f419f98a53d067d6294f419f98253d067d6094f419fd8953d067c6254f41ddd8553d067f6054f419f18153d075d5314f41d794f43d075d53d0f41bb98b43d06ed62d0f41bd98743d06f561d0f41bd18543d075e5310f41d754c43d06f66110f41bd58443d06de63d4b41b758f52d076f5294b419f98e52d067d6394b419f98252d067d6094b419fd8d52d067c6354b419fd8152d067c6054b41db54852d06de63d0b41b758f42d076e52d
  | 38 => 0x5438cb5f6550e32e7d91438cb5e5450e32e7951438cb1e5450e32e7551438cb5c5450e32b7d89438cbcf6250e32f3189438cbd76150e32b7185438cbd46150e32b5185438cadc6050e32b798f428cadd63d0a32cf952428cb3d5490a32b798e428cadd6390a32cf950428cb3d5410a32b798c428cadd6310a32eb508428cadd65cca32d7597328cadf64cca32b7593328cade61cca32b7983328caed65cca32db597328cb6f54cca32db553328cabe64d4632af593518cb7751946329f992518ca7d64946329f982518ca7d60946329fd91518ca7c6454632d790d518cb5d43546329fd81518ca7c6054632dd544518cb7b50942329f992508ca7d6494232dbcca508ca7e61942329f586508ca7f64542329f191508cb5e4354232d750d508cb5f32542329fd85508ca7c6154232af990508cabd6414232bd984508caf56114232de540508ca7e61d51329f587544ca7e60d51329f583544cb3f54951329f992544ca7d6395132d758e544ca5d63951329f58a544cb6d62951329b58a544ca7e61951329f586544ca7e60951329f582544caf76155132bd185544cafb6055132be181544cb3f64551329fd8d544cb5f63551329fd89544cb6f62551329fd85544cb7761551329dd85544ca7c6155132dd185544ca7461551329fd81544cb7b60551329ed81544ca7c6055132de181544ca7860551329f994544cb3d5415132cf990544ca7e61151329f584544ca7e60151329f580544ca7e65d0d32cfd53434cb3c54d0d32bb98b434caed62d0d329f996434ca7c6550d32cfd51434cb3c5450d32bbd89434caec6250d32bdd85434caf46150d329f994434cb9d4310d329f997424cb3f54d0932cf153424cade63d0932b758f424ca7e65909329fd95424ca7d65509329f195424cb3f5450932cf151424cadf6350932b718d424ca7e6510932eb508424cb6f54cc932db553324cb5f548c932d7552324cbcf528c932b7582324ca7e64d45329f593514ca7e60d45329f583514cb775194532be982514caf96094532dd544514ca7e64145329f590514cb5e32145329f980514ca7d60145329f993504ca7d64d41329f987504ca7d61d4132bd986504caf56194132ded42504cb7950141329f990504ca7d6414132dbcc8504cb5e32141329f984504ca7d61141329f98f540cb5e63d50329f98b540cb6e62d50329f987540ca7d61d50329f983540ca7d60d50329f596540cb3f5495032d798e540cb6e62950329f986540ca7d61950329f982540ca7d6095032cfd91540ca7f61550329f185540ca7f60550329f181540cb3d5415032bd984540caf56115032be980540caf960150329f990540cb3e64150329f98c540cb5e63150329f988540cb6e62150329f984540cb7661150329d984540ca7d6115032dd584540ca7561150329f980540cb7a6015032
  | 39 => 0xaed62d0c429f5964310a7f6550c42bdd854310af46150c42d794c4310b5d5310c42bb9884310aed6210c42b798f4210add63d0842e798f4210b9d63d0842af5924210b3e5490842bb5924210b6e5490842eb9524210b6e53908429fd954210abf6550842cfd954210a3f6550842afd894210b3e5250842bbd954210b6f65508429bd954210aef6450842ebd914210b6e5450842eb9514210b6e5350842ebd0d4210bad4350842ddd465110a7e63944429f58e5110a7e60944429f5825110adf6354442b718d5110a7f6354442d7d8d5110a5f63544429f18d5110b5c63544429718d5110b6e4254442db5095110a7f60544429f1815110ade6314442b758c5110b755114442be9805110af96014442ded425010a7e63940429f58e5010a7e61940429f5865010a7f63540429f18d5010b3f4254042db9095010b3d4254042db5095010a7f61540429f1855010ade6314042b758c5010af66114042bd5845010b795014042d798f54ccb6d62d53329f98754cca7d61d53329f98354cca7d60d5332cfd5254ccb6d62953329f98654cca7d61953329f98254cca7d6095332cfd9154cca7f61553329f18554cca7f60553329f18154ccb3d5415332cf99054ccb5e6315332db58854cca7e61153329f58454cca7e60153329f58054ccaee62d0f32cf95243ccb3d5490f32bb98a43ccaed6290f32bdd8543ccaf46150f32cf95043ccb3d5410f32e750c43ccaee6210f32bb58843ccb3e54d0b32cf55342ccade63d0b32b758f42ccaed6590b32db59642ccb6e5490b32db15242ccaed6390b32bb98242ccb3e5450b32cf55142ccadf6350b32b718d42ccaef6550b32dbd9542ccbaf6450b32db95142ccbae5450b32cb95142ccbad5450b32db15142ccaef6350b32f3d8d42ccbcc6350b32bb18142ccb7751947329f99251cca7d64947329f98251cca7d60947329fd9151cca7c6454732db90951ccb6d42547329fd8151cca7c6054732dd54451ccaf66194332bd58650ccb7b50943329f99250cca7d64943329f98650ccb7661943329d98650cca7d6194332dd58650cca7561943329fd9150cca7c6454332db90950ccb6d42543329fd8550cca7c6154332de54050ccaf661d5232bd587548cb5d63d5232db98b548ca7e61d5232dd987548ca7661d52329f587548cb7561d52329d587548ca7e60d52329f583548cb3f5495232d758e548ca7e61952329f586548ca7e60952329f582548cb3f64552329fd85548ca7c61552329fd81548ca7c6055232cf550548cb3e6415232d758c548cb6e62152329f984548ca7d61152329f980548ca7d6015232cf953438cb3d54d0e32bb98b438caed62d0e32b7596438cb5d6590e32d7952438cb5c5490e32b758a438cade6190e32b7982438cb3e5450e32cf551438caef6250e32bb189438caf76150e32bd18
  | 40 => 0x5310f42d754c43d0b9d4310f42bb98843d0aed6210f42b798f51d0add63d4742d794f51d0b5d53d4742d794e51d0b5d5394742ddd4651d0a7e63947429f58e51d0a7e60947429f58251d0b5e5354742d754d51d0a7f63547429f18d51d0a7f60547429f18151d0ade6314742b758c51d0b5e5314742d754c51d0b755114742be98051d0af96014742b798f50d0add63d4342d794f50d0b5d53d4342d794e50d0b5d5394342ded4250d0a7e63943429f58e50d0a7e61943429f58650d0b5e5354342d754d50d0a7f63543429f18d50d0a7f61543429f18550d0ade6314342b758c50d0b5e5314342d754c50d0af66114342bd58450d0b795014342bd9875390af561d4e42d7d4e5390a7e6194e429f5865390a7e6094e429f5825390b6c6254e429fd855390a7c6154e429fd815390a7c6054e42d754c5390aed62d0e42d794e4390b5d5390e42bb98a4390aed6290e42d794d4390b5d5350e42bbd894390aec6250e42bdd854390af46150e42b798f4290add63d0a42af5974290b3d65d0a42e798f4290b9d63d0a42bb5974290b6d65d0a42bb98f4290bce63d0a42b398f4290bcd63d0a42bb5874290aed60d0a42b798f5190add63d4642ddd465190a7e63946429f58e5190a7e60946429f5825190a7f63546429f18d5190a7f60546429f1815190b755114642ded425090a7e63942429f58e5090a7e61942429f5865090a7f63542429f18d5090b3f42542429fd855090a7c6154242b798c5090add6314242bd9845090af56114242de5405090b6d62d4d429f9875350a7d61d4d429f9835350a7d60d4d42d7d4e5350af76154d42bd1855350afb6054d42be1815350b5d5314d429f9845350a7d6114d429f9805350a7d6014d429f9974350aee62d0d42d7d4e4350b5c5390d42bb98a4350aed6290d42d7d4d4350b5c5350d42bbd894350aec6250d42bdd854350af46150d429f9944350b9d4310d42b798f4250add63d0942bb98f4250bce63d0942b398f4250bcd63d0942bb5874250aed60d0942ebd4a4250abd60909429f98f5150a7d63d45429f9835150a7d60d4542ddd465150adf6354542b718d5150afb6054542be1815150b7551145429f98c5150a7d63145429f9805150a7d60145429f98f5050a7d63d41429f9875050a7d61d4142ded425050adf6354142b718d5050af76154142bd1855050ade6314142b758c5050af66114142bd5845050b7950141429f98c5050b5e63141429798c5050a7d6314142d758c5050a5d63141429f9845050b7661141429d9845050a7d6114142dd5845050a756114142d798e5410b5d6395042d7d4e5310a7e6194c429f5865310a7e6094c429f5825310a7f6154c429f1855310a7f6054c429f1815310b5d5314c42bd9845310af56114c42be9805310af96014c42d794f4310b5d53d0c42bb98b431
  | 41 => 0xd439f9875250e7d61d49439f9835250e7d60d4943dbd4a5250ef66194943bd5865250ef76154943bd1855250efb6054943be1815250f6d52149439f9845250e7d61149439f9805250e7d60149439f98b5150e7d62d45439f9835150e7d60d4543f5d8f5150fd743d4543ed90f5150f7752d4543dd94b5150f7552d4543dd14b5150f7764d4543ddd8f5150f7743d4543dd90f5150f7762d4543dd98b5150f7562d4543dd18b5150f7760d4543dd9835150f7560d4543dd1835150f775194543dd5445150f5f43145439f9885150e7d62145439f9805150e7d6014543bd9945150f766514543f558c5150fd74314543ed90c5150f775214543dd9485150f755214543dd1485150f776414543ddd8c5150f774314543d5d0c5150f764314543dd50c5150f776214543dd9885150f756214543dd1885150f776014543dd9805150f756014543dd1805150f7751d4143dd1475050e7e62d41439f58b5050e7e61d41439f5875050ef66194143bd5865050f775194143dd1465050f7b5094143bbd895050eec6254143bdd855050ef46154143ddd455050f745154143ddd445050f745114143de5405050e7e62141439f5885050e7e61141439f5845050f6e6295043db58a5410eee62d0c43bb58b4310fae62d0c43eb58b4310ebd6490c43cf9524310edd6490c43d79524310f9e5490c43b79864310e7f6550c43bdd854310ef46150c43afd954310f3f6550c438fd954310ebf6350c43cf94d4310fb76150c43ed1854310edf6550c43d7d954310e5f6550c43b7d914310f9f6450c43d79514310f9e5450c43f5d854310edc6150c43f51854310ed46150c43dbd4a5210f5e4394843d750e5210e7e61948439f5865210e7e60948439f5825210e7f61548439f1855210e7f60548439f1815210f6d5214843bd9845210ef56114843be9805210ef96014843ddd465110e7e62944439f58a5110e7e60944439f5825110f5e4354443d750d5110e7f62544439f1895110e7f60544439f1815110eee6214443bb5885110f755114443be9805110ef96014443ded425010e7e62940439f58a5010e7e61940439f5865010f5e4354043d750d5010e7f62540439f1895010e7f61540439f1855010eee6214043bb5885010ef66114043bd5845010f795014043d7d4e53d0a7e6194f429f58653d0a7e6094f429f58253d0b5c6494f42d7d8a53d0b5d6294f42d7d8653d0b5e6194f42d758653d0b5c6194f42d7d8253d0b5e6094f42d758253d0b5c6094f429fd8553d0a7c6154f429fd8153d0a7c6054f42d7d9553d0b5e6454f42d7d8953d0b5d6254f42d7d8553d0b5e6154f42d758553d0b5c6154f42d7d8153d0b5e6054f42d758153d0b5c6054f42d754c53d0b5e53d0f42d754f43d0aee62d0f42bb58b43d0b5d5390f42d794d43d0af76150f42bd18543d0b5e
  | 42 => 0x20012000000080040000000000200020010000000000000002000000000010004002400080000014001000000010004002800180020000000400400010004000000000000004001400080000000001400080020002000000000030008001000000000000000000000000002000000000000002001000200050000000400200000012000400480000012000000000000000005000080010002000000000000004000c00280010000002400380050000000400080020000000400100020000000400080050004000000480000004000800100000006000000000040008000c0000000000600180000000000000000000000000400200008002000000000000008000000000018001000000080018004001200080000000000000000000000000600000008002000000080008005000000000000002000600000000005000000000008000000800000000000000400040000001000200140008000000000100008003000200000010000000000176f5294b439f98652d0e7d6194b439f98252d0e7d6094b43db19252d0f6f6394b43dbd8652d0f6e6194b43db58652d0f6c6194b43dbd8252d0f6e6094b43db58252d0f6c6094b439fd8552d0e7c6154b439fd8152d0e7c6054b43dbd9552d0f6e6454b43db58d52d0f6f6154b43db98552d0f6d6154b43db18552d0f6f6054b43db98152d0f6d6054b43db18152d0f6d5214b43bb98b51d0eed62d4743db94b51d0f6d52d4743db94a51d0f6d5294743ddd4651d0e7e62947439f58a51d0e7e60947439f58251d0f6e5254743db54951d0e7f62547439f18951d0e7f60547439f18151d0eee6214743bb58851d0f6e5214743db54851d0f755114743be98051d0ef96014743bb98b50d0eed62d4343db94b50d0f6d52d4343db94a50d0f6d5294343ded4250d0e7e62943439f58a50d0e7e61943439f58650d0f6e5254343db54950d0e7f62543439f18950d0e7f61543439f18550d0eee6214343bb58850d0f6e5214343db54850d0ef66114343bd58450d0f795014343bb98b4390eed62d0e43af5974390f3d65d0e43eb98b4390fad62d0e43b75974390f5d65d0e43b798b4390fce62d0e43b398b4390fcd62d0e43b75874390edd60d0e43dbd4a5290e7e6194a439f5865290e7e6094a439f5825290e7f6154a439f1855290e7f6054a439f1815290f6d5214a43ddd465190f5f43946439f98a5190e7d62946439f9825190e7d60946439fd895190e7c62546439fd815190e7c6054643dd5445190ef66194243bd5865090f7b50942439f98a5090e7d62942439f9865090f7661942439d9865090e7d6194243dd5865090e7561942439fd895090e7c62542439fd855090e7c6154243de5405090eee62d0d43bb58b4350ede62d0d43f398b4350ece62d0d43f358b4350edd61d0d43b75834350f9f5390
  | 43 => 0x80000001000a000400180000000000400080000002002c00080000004000400080020002003400000050000000000400000004000800000060002000000000000000000000180000014000000080010000000000080030004000000000040000000800000030000001c00000000000000000000000006002400000010014000400680000004000000000030000000c0020000000200000008002000000000038005000000000000001000000300020001000800000000000001a000000000010000002000080000004000c000000200020020002800000000008002800d000200040018000000000000020002000000040000000000000000000001000000000028002000a000c0018008000800000000002000000140000003000000000018005000000000000000000800100048000000200300030001000200080058000000200000000001001600180030005000600040010000000200340028000000800000008000000200000018006000800000000006000e00100000003000e00080008004000000000000000000a00000008000000a0004007800400080000000000100000000001800300060000000800000000004000800000020008000000100000000000000700040000000800000000008000000b000200000020000000a00000000000000000180008004000e00000008001000000000000001000000000000000000000000000000000600000000002001800000018003000000000000000000200000000000000c000800100050004000000080070000000000100010002000c00000050000000000000000002000c0000003000000100000001000600080000000000000000028000000000000000001000e000000200000002000800080040006000000000000000000400080000000000000000020004001c001800700020008000000100040000005000700000004000000200000004001000e0004000000000010008000400480060002001c0000001001400040000000000000300000000000600240000001000000400000002000200000000000000800180000002000c00180000000000000040028000000200280000000000200000020002000000000020002000200000000000000000080020003001200180000000000400100000001000200080010000000000000000003000c00140000002001800140000000000c0000002800000000004001800100000000001800000000004000800000020000000800100000000000000300020000000000000000008000000200020004000000a000200000000001000a00000000002000200040000004000000080000002000000000040000000200100018000000200040000000000200000000001000400040018002000000080000002000000040020000000000000000
  | 44 => 0xd000000000000000000a000000000010000000c0010001000200000000000000600040010003000000000028000000000000000003000000080000000000000000000001000000a000200000006000800000010002000c00080000014000800280020000000000100000018000000000030002000c0010001000000000000000000600000010001000c000000000000002003c0000000000a0004000000400000000008000300000000002800f0000000000080050000000800480000004000000080010002000000000000000000000080030000001800080000000000400200000002000400000010004000000180040006000c00000040006000000000020000000c0008000000600000010000000a0010002000000020000000800a000200080010000000000040010000000000040000002000c000400000000002000c00000000002000400000020000000000000010008000400100000000000000180010000000000100020012000400000040000000000400000000001400100010000000000000010004000400380000006000400000000006002800000010000000000000010002000000000010000000000000030000000000080000008000000100000004000000000020004000400080060002000c0068003000000000018000000c000800080010000000400000010002000400000000008000000600060000000c000000000000004001800100000000008000900000000000800300020000005800000000024000000100020004000800d0002001000080020000000000000000000000400000030000001400500050002001c00080000002000c00000000000000000000050004000000000000012000000000030008000000000020004000000000000018000000080020004001c00000010008000c00180020000000000200000002000400080040000000000000000006000c0010001000000000010001000200000000003000600040010001000000040000000000400000020005000000140008006000000000000001000400000010001000000100038000000400040018000000e000000300000000001800080000006000c001800300080004003000000000030000800000000014000000200240000000800200060000005800000000004000000500000000002800500000004001801000000000000000000080000000800000040004001000000040004004000100160004002800400380000001800300020004002000200000000001000600020018002000e000000040000000000000000028000000a000800000000012000000000010000000000080010002000400180010008000000180020002002c0020000000000000018000000e001400080020000000000000010002001800000070000001400100080000
  | 45 => 0x4000400080000000000000100040006000400000000002000800000020000000000400010002000000280000006000000180000000000400080070002003c00100000000000400000040006000c00000000002000000000090008000c00380000004000000000020000000000100000000000c0038002000000200008000000200000000007000000000000000000000000000004000000040000000000000000000001000000000000001000200000000002000600000068006000600040000003000c00080000005000800040008001000c00000018000000c00040018007000000080000000000000040000000000600180000000000000040008000000200000010004000000140008003000600000000002000000080030002000200000068000000000000008002000a000c00080000000000000000000000000c00300030002000400500000002000400100020004000c000000b000600000000001001000100018000000000000000002000400000000000000000000000000000000000028003000c0004000800d0000000400080010000000c002000000060000000800100000000000000100000010000000300060004003800200000004002800100020000000800100040000001800000220000002000a0004000000000020000000800180000006000000000040006000800000080002001000080050000001400180000006000800280000002000000000000000000400400050002000000180020000000000000010014000800000020000000000000000004000000000030002000000000000000001c001800100000000000000e0000000000000000000000400100010002000c000000c000000100008005000800340020001000000000018001000000000000001000200040000001001000000008000000000000000008000c004800000010010000000280070000002c0008000000a000000180040006000400180020000000000100000002000800000020000000000000010004000000000030000000c000800100260004003000d0004000c0010000000a00000008000001000100000000000400000000002000400000000000000200040008000000000000000000001800000028001000200000000000000a000400080020002000000080020004000000000000000000000080000000000000000070000002000100010000000000180000002000000000070008000400180040008000000000010002000c00200020002001c001000100100034003000000000000000000200020008000000100000000000000000020000000000a000200000008000000000000000000000000200040000000e00000008007000a00040000003000200040008000000200040040002000200040020005000c0004000000300080020001
  | 46 => 0x8001000000000000003000000000000002000600000018004000400040000000000400040008000001a00000018005000a0000000000000000000000000000020008000000100000004000800a000200000000005000600000020000000000040040002001200000000003000600080028000002600000018001000000000010002000000000008000000200000030005000a001400000020002000400000020004000000380010004000400000070002000400000000000000400180000000000000080070000000000080040002001c0008000000400080000001000c00000000004000000200010000000e000400280000008000c001000000000028000000300000008001000d000200180028001000200000000000000200040030000000000000018000000000040000000000000100000000001400040008004000a00080028000000000300028000000000000018003000400040000000000c00080000000000a000000180050000000000180000006000c00080030002000400300000004000000080000004000000100010010000000000010004000000a000100000008000000000040008001000b000200040000001000600080010000000000040000003000000240020001000000200000000000c0014005800200040020001800300000008001000000000000004000100020014000800000000038000000300020000001000000000000000800000100000000000000080000003000e0002001400100030006000000300000000000400080000006000000100030000000000080000002000800000000006001400200010002000c00480060000000000000020000001800080020000001000100000006000400200010002000000000000000000000000020002000800100000002000800200050006001000000000002001000000030000000000080010000000000000000006000c00200020000000000080000000000c0020001000000000000005000000000010001000000000000000000800000000003000400040000002000a0000000000100020014002800100000000000000000000000000801c000200080000000001400000038007000000200008000000800140000008000a00000000001000a00200088003000a000000080010018000800400000004001800080000002000c0018000000000040008000001000340008002000200000000001000200000000000000000140020006000000000018000000200000000004000400000000000000e000000a0002000200000018000000200000040005000400000018003000600040000002000400080008001000800240000000000200000000000000a000c0008000000000100000000000200000018006000200000000001000000040010003001400000010000000
  | 47 => 0x80004001000000020008000000100000014000800200000000000800300040000000800000000004000800000040008000000a0000000000000000002000000080020008000000180010002001400580000000000000080000000000400180000004001400100010000000000000040004000400080020002000c0008000000000000000000001800080000001000000000008000000e00000008000000000080018000000000000000003000a0000000800200000004000000900000004000000c00000000000800000060000005800100000004001800700000000000000400000000000000000020008000000000020000001800c000000000010001000000000000001000000000000001000800080000000000a000400080000008000c00000010004000800180020000000000000060000000000080000000002000080000008000000180000000000c00000010000000000100020004000c0000000000000000028000001600000000004001e00000008000000000100020000000a00000010001000a0008003800a00060000000000b0004000000000010004000000080030000000800100020006001400000010008000800000000004000400380060004000000000030000000000080000006000400280000006001000080070000000c0008000001200080010000000e000400200010006000000280000000000c000000000000010000000400000000000000100000004002000000140000002800300000020000800b000000000000000000000000000000000000080000003000000000008000000c0008001800a0000000000000000006002400280000002001400280000000000400100010000000400500020012000c00080050000000000100030002000000400040000000000080000002000000100000002001c0018001000000000010000000a000000000000006001800000000002000400080000008000c000000d00040004000000000060000001000100060028001000000000014001000000060018003800300020000002800200000014000000100000010000801b0006000000000090006000000000000000000c0000000000c001000180000002000400000000000000000000010004001400000000000000000580020006000800280000000001400100120006000000000010000000000000030004000000800020000000000080010000000000200020000000000300000000000400080000002000000000020002000000280030008000000000020004000000480000000000000100010000000c00480010002000400000090006000c0000001000a00000008000000000180008001000200300000000000c000c0020001000000000020000000400080030006000600000000000000400080048002000a000000
  | 48 => 0xc00001598aaa015d41f600000000dd90000000000013653bc66478000000000004c7c00000000000360c000106814f226280001ac444ea4c5cd468fde28ac23bc74d000000000000000000000000000000000012ce00007840000000047d088c000021ee03c9189962600000000000000026280b740000000000040240000000000000010c68000392a4d150e2157203c0318800000000586254c13292340000792c000000000003cc0049969700000000e2a1d8c00001344000000000000000a8a8000000000003500000000000000001c1424fa00006d100000000481c9fc800000007bb4000000000000000000123c2a602ad900d18130000000000000003b381fb4000000000520000836000000000000000000029aa000000000001d2a00006ab0be900000000000000000006500e7e0734000000006be8000000028880000000000000000000000000000009d5957122d0454508f000032ae00002b880000d7600000000d280ed44d18000000038442a7c000000000000000000000000008d601bd1ec600004cd40000000290e000040b80002702000037180001a2c5f6cd32000000003a1400000000000000000000000000586800023d21e9800000899ebc421037e00000000000081701de1081271a65f115d8000000080641c71e3f40b0087033e09c4109075ec5cc09b33f181c44edc000000000000000099b1d0c00007ab000000005bd80001a8700007bf4000000000000000000155a1488000042085ff421c000000000000d2a51e4000071e4712846c0001c53121e000023d87900000000070b00003e9c000000020c70000000000000003edc148800000002fd05cbc55c0000000000010ff9dc041b0769c164150e2edc12c400000001bba68383ea8c1100005b9ce2f000045ac61e00001d4f000060bc0000000296641acf6787542c4e000000000003eea2f0c000000001a25170197228240fe34ec000000019a04854000206100003c70c7a143a343233c80000000000089442cb800036226ea8de68000299e000000000000000286471d80000000000000000018001000000000010005000000040000000000400000000001000a000000080010004004c0030001000400000048001001c002400080200000000c00000000000000000200000010000000180020000000000080000030002400000000004001400600030004000000080000006000000000000008000400000060000000000080020000001000080000004000400100000004000000200000000000000000000014000000000040000000800000000000000c0000000000c00040000007000800040000000000000000000000002e000000000080002000c000000f00000010000800000000008000000000000014000000700000000000800000000020001800500
  | 49 => 0x2800000000000000005a900003bf805c00b480002bbc000102d92520d7800006fd05132ed0333400010d9000000000000000000000000001680262a78245f295ec2f2c22bcb6717be2c2234f43ea121726b003240410b1343500000000000000000000eb98000000045ed18e13a9000000000000328000052108279cb90000000000011b1365400000000000000000000000a80000000004da0de40000000096f06d22c6e1cd80001e8200001ca0ebb871a434a6ddd1459ab934a43780b55849e27e83e28b9e9c5a028605800001c680000000000000003958000000000000000153cd808000000076148db8a250ff4000000021ab000088040000ca000008f6c84686eb2c202be812a09d606fa0000a488541112a000089b0ec323e21cb8747033f0c5410646f5000002546e2800000000000000000000002168000000013b6195c00008d30f4d37a838e0000020d34ec1e34c98800000000360000000000000000000000018b841700000f2b00000c706b512d500002a3c00002a700006f0cb2f80000000242c49a8000000066e800000000000036400000002424428825f95c10edc000000004b70000000000000000f7a0000de9940b000045e4a2e9ee113700000000000000000000000000000005e88000000000000000000005238500000000000000000000b5000000000354c3e180000000000099c062e470c6c6c4730d5728c200000000000000000007720ac800000000b99000000000000000000000002468bec8af50000280856f0fea25020e2d0a19f4941643e5c000000000002dfc31180000000697401812c60000529903e867710f62c2c00018110000815888a213c2d6c2f44bab8000161c00007988000000000000001c66250e0000000216c41fc0000000106000008514f031897369800000000000000006200000acd3a96000000011550000000000000002f5447a0f560000154200009c4000000000000000000037f800000d78000224400000000000000087248db004d31d400004b7800004c8000000002cc1f3459e0000190300006e30aec000000000000000000000004c44bb38000000000000001cdd3f6458a840a80000872351400300003fcc3fe10d88cc7000000000000d30139a3d1037f9b930000000028119670000135488500002cac00008f080001cd87434000000000007b6518000002b9e0000000195100002778c9a82921bbc00000000000040608f90da8000239c00000000000278a6020b2d11770a520000a401bda119200001530000000000000000dda000060580000000326e417800014bb0dae00000000dae24607eb4000000000007ee87070efa000052500000000000000000001bf000001734ad6949b00000000000118804082a04000000006cc2998000040f3dc438b8640943844260a2840c0d
  | 50 => 0x7432d384a2482b9b90005a7c7cd6a88751c66000055f1c742bb242100000c97000000000000000356000004c2220e0000000000000000ab81320f9680000000428c0000000000000001571dd435b80000e528000391a6704bb19a161f7c55d877820d30cec15001250a86446c573492b0000104868800000000000000001ed0000238a0000cf7800000006f082f20a9500005048701877008645fc11c60000000000000000c4104e600000000000000064180000000000000000000000069800000000000000000000c3800004e05a300001a7f00000000c69800000006220fe98a9123148b90952236d41be1bbd0a122982a804dad1059cf63f0c5c2868f08b604cc238c00006e015e61ad018f9fb939e461b45da18af426c4b5d19e91e507d20000a13000000000000000002c46f80000000000000000000109000000005970000033213e0000000000000000000000000002e5401280000db40000000047d8000005600000000000000000000000000000073144a6a36800000000000193900007170000000015d4114c0001b5e000004e8f039d233f9600000000000000026a49e9909f1a9671e80f490c410c80000b5f1dfb0000000000000000000000000013e000000000a881ab140280000c57075b000000003f48fa6431c6edc000000026a2470c000162500006f700000225269a4ea88af180d00004f98e6100000000000000000000000000100e99bd00000564a0e139f1d2e71207c5a19c104c00000000000000048d81ab1b7500000000000081100002bb8f3384fe00003a7000008cb0c788d200000000000047d4843103c02b60c48eea800020625b0c0000ef643ca0000000000011780000cea087811d051f0e798c8e221200000000000000000002239417000000011ca8000000059b800002810000000079c0000000000000748000176a02ec00000002b0c5c3800005d3145a0000f16800035a0000000015562f3a00005f1800000002cf80001e621f645e00000000000000000000000000000000a6e8d80019415cc07c8000000000000000bc100000000d02147531ac0924000000000008d9c0e380000b5c7204000000007f2260c58f037f01967b80e0180002f5045180001d8628b0700000004fd0000000118d1c6f26ee2a9c870800033860b2800018a60000000067d000000007ad40c7800000007600d8119b100000000ec88c7f00000000d420000076800011ad0fc8248c00008c780000000000000000000000000000020ea00004978000000037fa1b54b38229a000079802418000179414f00001a2a0eb48d7c00000002544000066a800000000000000000000000000000000000003df45ad93621ff200006d38f3713f26a2cb2d84ad2eb00c811cb0000194c5bfcca8045440a800000000000478c5b500001b8300008
  | 51 => 0x50a800000002c285674fb1149d000000000000bab000000000001b0700000000000000036c082346e580001fd6000000023c800000000bc909eb31800000042000000001ff00000000000083d0655800023b4000000000003e38000000006c535a40000000000046080000b1c033d1eca191c6cd00001f8a8f9d0ba000046860000cb98000000000003cb94da0000000071580000b103d74cf20000361c80fd10519fb000025940001f9b000000000001d982e4e000107599ff0000835405a1708244200003ed80001d7600009da000000000000351990a00000000000000000001c9c0dc8cb011ee265c0000000000037380000df500cc00000000000000015bc00000000000171c000235724c000000000000000081dc00000000000000028800000000109400004111b6a67582fa9c6b1a2e64100000184169020ec4750eec3a7a000000000000000000050680000000000000000000a46150800006a112d8000000000c6000000000000000000081ac000059500002ea0000000025f8000000002bd41e41d040001258161a0000d310000449400000000c91032e0000000118430fa0000000000042b40000000102b29bc00000002021362070b8dce89291be8000117b00000000000000009a800005398e818000000063fc0000b8c0294062852107f60000000000000000000000058000001db8000050e111242420000b4f14950000000059b80000000076c000082000004774000000000000000000211802760000000043600000000000000043de00000001bb122e4408918800000000000015a87d600006fa47e3108c17f0088463a1ab811748940af20f873b7a0000000000000000000de610871cf67e58000000017e06554000000000007f306aa000006ca0000000222f000083f4000000029b00000a7d800000000f40da2000023180000000000000000000000000000000000b1880003b6e000000000000000733c058800000000000000000032c20000000000000000000ac7000000001a68591000000000000000000000000000000000000000000000197405ca7d040001bb02b6a000000022a126a60000000000027c28240f97a156140a222483ba3ab00008ea8bc4000000000000000000014000000000000019060000000000000000000000000000000000d06000000007240000071b0000000000000002c64000000018d01126000101b800013b62fc8369911e3e0600002168f77000000000000000000000000000000000000000000000243e000000019961734000013505ea0000820000016bd3fb8002844d8e11266c5e180001c400552059011319df0000019000000000000771820e01d60e9a5d38000000000000000000000020c459bc4bf0000000080042320ee72f825d40bf98
  | 52 => 0x183246e60000000000000000000ac9a2b5000030500000b3222b60000000000000006b6800018e400000000000000000000000000000000002bf4000000000007a349b68d2718da3c24098a13539f0292024b954209b22c203e3a1bd000000000001dee00002be40000000000000000001bbe00000000c5c8000076202e800014683f94021400006e52eda0e406870703325c2f2c9eb982c38267e5057780000000000000009b900000000000000000004da4e861774212c0000000000003f80000c2f99b80000000000000004346094c0000000000000000000000000050d40001dca2d8000000000000020c39900000000000000000000000057c0000ce5000000d6000000014f10000000000000001cc20000000000015c400000001d7e00000000689937024da00000000000454a000112c8000000060fd08a8ec723a4000083200000000603c00000001aba5748000028500000000e1d14cc000040a87c3000009022d00f1a8a673fbe0000000225e0000000000000001f7025e8000000000000000d7b9ed71ebc46480000000000029191da95a800001c7cbcf80002294122c78d13fe06280f1c4190000000000011360a7a039e4bb800022ee00004730e68000000003934000094801b605bc0d2800000003a3c03f22c6322058e49f8000038e0000000000000000000009f0000412843000000000000000000000000000060a488000001f88000000000001e080000000140200001160000000000000000f7f80000000546c0000000000000008e098aa381060b417780003860000033105bb08fe6f151b21f14151400000000000057000000000000000000008fb9d3900003c78bce0bf700000000f8b1c0500000000e3509f31582569502f0000091200000000000000049b8cbf02680f800000000000000006bd4000000000008e7c000000042ce47a846c907f000000005021ae812e065b80001db60000000082b1a4c1c6a0001078000000000000000000000003ab800006123e4659a80000000163239b4752149700d05a3c000080a08160001147000039fe51ac2ee0000000000000000000000000006e6000033465b4800019420d6400011a000000000630cac41c77000022880000000000000000001734000085b89c1800032a400000000b563c8200006ea8827299a10acb2f08b525ea000000008c20000000118484db09740000000000000002dd400010e43670045916d96e229f200005808000449873d096700000170813401c800000001a5069719da46ac116d16000002d9e193870297bf20506cf81cc9b9815f000000001c7f000000000000000000000007310000000000008e50000000000006328000373861649cd0b81391e00000000ebf0000000064e190d0f28388c0000000215a000000000000000000000000000000
  | 53 => 0xb0800000006f3876101771ac66fc4baa8d86419e46e84840608000000000000d331d94732015d88a32f940000000029e192800010d0800002ae1d4506209ca02e878bc0001e283aec35cc10d8b2f00007ea0a8913f304fa00007eb00001bc4000036f14bf018856dccf980000d3c1910803800000007c0400002aa256a0000000114d2ea87a4800000000000197c0001fb5218663543fc000018e0000085d144d000058f800001bb0000335cfe6800000000000bee00002e342554d6f20380000000110280000000000057d8ad331fc53100000e9e00000000911844e24d000000000000452000006f6000000000000b28800015e40fa8000000020a868ec00000b3000008740ed0ab30f742a5c000226a087082e80000000000000009e30000000000009bb0da104840000b8680000000000000004df066c802065291b411604bdc00000002eea000000000000000000000019661668366c1d51c560f3e0000bea0000000069040000caa000080a4b721ce720fc4ef0000123e00002198117800000008798cce02a400001398a648eb536d40000b25000000000000000000000000000ef821f100007c643068afe0000000000009362ed60000000082d112085e4c8080002c9a63b40001a1036d666e44e623a2020e0000e90800000000000000014d00000000000223100007ba40000e013d40172005800003b9819c904d1a08113078b0000000000001a3c0000000000000000000ce1325e274c0000a6f0000000048b06f91cd60000000000032e000000000000000000000000000000000000001d49178836704ec000000000000ff722064650000000000000000000053f800000000000000129e212a00009190a26070a00007a8935e1ff60000000067d087600003e8800000002424e6b0000000074a40000abb000000010ba991f2a3e3b840e88e7700000c58000000009a00000000214b0000000000000000000000000003073b0654a0f380000000074c80000a3d00005754a4f8dd742681c9512d05652a5e0000000000000000000785800000000000000000013307a840000c5e00000000e72800020ca3e00000000000006378d170000000074bc0000000000000011bb82ee00007e7803b0e0c390c45bc389a3911e0c000000016e0000000007b2000000001a0c000000001ee0acc80c09dd1bd200001dc000011fa0000d2c1fa7227a0000777163b37be00007d980002d3018c000008f6000055b8cd4840e00000000b898000000049fc140000000000000ffd9b7111fe195000000000000847c1441fb41d1a2f1c0000000399229c414e077201380838000000000004d5400015c400c00000000000017b40000000000002507fb40000b78000000000000e243348000000000000000000000000000000000080e05123bda0000000
  | 54 => 0x1d67175e8ea0000000013e400002e492112dda00000000000000000003a78000000000000001cd5005e0000000000000000000000000000000000b529fbe40aa58fc08400001342432ce168000087a7c48271821f000000000000000000000000000d9e30ea000031e8000000047c0cf080000000000000000001ce27e74c2a000000000000aed00000000000051c011400004ad85101dc806440000e7718e51b22216c8c2800000e00888000000000004ab0000000000000000000151100003300914000031b6000000000000000000000480002e9800003838e19000048e000011ae2c16149880414af1ffe42bc000152a000000004ac80002b48017800000000000736000000000000726800021642ec200011e18e70000000011a6800038e46d7027580001d36020085c000041543ff065b800025641e740000000000000000000000000000000001d220a32000000005d200000000b6804793a241dec0000000000000000000000000000000000000000000000000000147e56f80000000000052a400000000c6204300000000124000000000f4e42668ae064988a9408c15d40000bcd0000225ceec8569437e000000000001480000000000df419000000000000021c7f15076236909e200004911ba70958000000000002b4e8530000000000001ec8438163400000000000000000000000c74a1042bde390873a800000002a7400d8a2c402a62cc07614ff0a0e49a81c200002cd24bccb3414453846842833f85e1282a6c54c7a81c00794765c48a12da0000000000000000000803400022e520401298228800019487fe800000002a0629cc9861111332037240000000421600001881d0e0fa668ac5d11f26025a1d2c0000000400e33d09b30b66000000000000000000007e4000049a3fd03411023a1f00000000023000000aa20000e6b9c960bbc00f4b2c800007a8838c00008d10000000000001a000005d1855a233542920000e9a9e9c00008840ec222300ec875b514e9f3500000000000107a000081111f319b30000000093620db17262d08ec91160000034fc08016120c201f642519ee3243250b895890c91a621c34000000000000000e9d000000007f180000000000000000000000000089fc0000c3b0000000000015360d5472b8000077813fc0000000000000000000000000025c00000ab1800000000000000000000001868c370000330c00005f300002b3e000000000000000000000012a81dde0000000000004c27c4000015232d6207fd0219976097c5b9800000002b2c8e741a580003a4e6d5071515212738000000000000000741cb3d8000418209e434d9ffe436802240001c42000011c08928000457a00000001ea7000000000001ab6000000001a791343abc00000a3800000000000a9f000000008b0c000058a000
  | 55 => 0xbfa0c39475e354856b000000006ec869307fe310800000000000256069107758000000000006108000310037340000000000074800b58000257c000000021fc1f404c10528800000000000c198000265c00010b28000151000000000a360ad40000d18088a0000000000000001bac0001040800000000000000000000000000000224000004e8c0000d493f464c210091d1502a81eb000022a6099e00000000000141014d80000702109600001d614e500007abc7cb173b34ca85d8cc294ab324a0000dd1800000004971030000000000bd800000004780000000000003d840000ce3800000004750ade08f5000000005fd9d3b299c166c24c0e02011c62d0000222000000000000000000000000f7b204a000000002b095ce16be00000001c5700000294000000018e45034de200000000000029712f8000042c8000000013aa49346b4000000000000000142432fa0000000000000006970cb59ff500008d78e760adc0f362c58c4686a938c2067d1d2083700008520ea30000013403c49048000000010b08ef173e3aaa00009e000003eb80000a1b00002b724474000187700006860000000000000000bd38ede107234c8000229f000000008e2000000000000c64000000000000000000000000000000175b000000006370000000000010c300002f4c0000bbb0ac60fea3484862922b110614c8ecf00002afc737030e8ad437ae8b380000000387e5ebc00009620926000020500001a2a4ad00001b31475845509e692841a1000002ed07c9319e0000e108000000037b40000000000000000000000000000006a60000000020940000000000000000001b571b6c581c29f9d71000000007ab9bd5000077880000000021a7fc90ee0000000060084f4800000005f782799dab000000000000000000000000000000220608908e000001422539c3618000459a3028486876042a04370ea7000000000000b3b99ae28360000000128d34c2000000010230afc00000000000000033580000000000030dc0000000000000000000000000019cc00000000000000095b88c7173c2878f5c9724394c4a84000131e00000000a3397b5187e0fa041e8000172c78c0000000044c60000aaf800000000000000000045ee0000e74819d35be3a8400022ab00000000000000000008dc4000189c003400003078000466283f00000c9f134a0000924000000000000d8600003e166fa000005551584000000003ce01d41c407d21c0924480000582856804406120dad841b00008564000217f4628030827e08e0195a00000000bdb146470f00000bf32878000000000000b3a5fbd1e6024f152400006cb00003f5e000000000000c6674c4704800024100000000203c00000e4800000003b262c600000cbf2e3e00000000d8800006c8c000187600002e9c00
  | 56 => 0x9800000eac000007a00002f9070e0a89800000000000f3200002c4200006458000000058543120000000082880000c4700002abc000000000000000252846a00000000e3c8000000020f832795a900000000c1b84dc0c300800f189ae70000000000000001c8e0e349ca83802b5e000000019990f500000000000000006010253804e1b8c00005e9012c09c488f87ad80002546167000001d3000000000000000000063ed18f0000000000000000000000000000000000009e8d491f2114c4000000000a1d7c1af007400000d2d00005d00000092b21dc5ecc00000000c5000000000bff00005b7d0380000182a3e8c000055e432e8de464505b609441f740998bf4474a23500000000000000000000000000084fc00000000000000105e0000007e00000000000000070d4e1d802100001ca87df800000000000bfc000000000000023800042ba00000000000080222b400017bb1e180000000131900001264215028d29a28ab43870cc200005ae812b0000397e4d3c0000e18079800005bd902400004e5039994b21bb61168900080232b000000008000162002a400000001cc000000000000000081bcb49077d1bec0d7c76c0000000033dc14fa1d1000000000000000000000004021b270000000000000550000000000014b641ce31d42a2000037ec000000000002aa20000000000000000b188f91b50000011180000000000000000000a10000069380001d62000065b4fc68ae144ec718047c800000000000000192d096a12c8f3e800013cc7210000000031968720000000000002200000000021b0180000000000000000000000000000000000000570000210000000001ade000011b203900003a04154080b37cc00000000000000000000000000023a493c000000004d640fce1e875e253e26f4000000000004bb4000000000000000000000000000000000000037e8000000021b903e244a044b0000000024f4ea200003ea02a4cb1a830a00006c340a9000015080000000000000007b600001fab177e00000dc0000000008b8bf30000243c00003f0800000000000c5a800000000000000000042a800000001cb01a9a3d4000006dc00004570711006300002b1d16e05f9000000005c5000000002a9800000000000000055580000000000000011ed17f26d5460180000468154c17f1d1c216600000000000188c3974da10045000000005ba00000000000000022c1356a00000000000000076b00000000000000001cc08680b440000000128f000052b81a3213e35944ca080013b5000062640000bce000025ec00000000000000000000000000440400000000000000092a909a000000000000000000000000001fc200001c60000000024c44e5862a90173e52888498904170000072cf28000000000000000000036280000000000000
  | 57 => 0x4c08d9600000000855c0000c43000061890ae215e00001f900000dbb000000011b71e210000535c6a08f4544d27aa021311870da0294cef410722ba63c7c7be184e000049cc000141e1f6854888a212453c3a0000000133e0000000000000ae000000011648000424c0c9c28000000000212400000001f4a10e891011730000000000007ef264e55e4eb5843c3bb6000000013f526862f7c00000000000000000000000000019400000001e7a0000000038a00006b144ef80000000000000000000f5c000000000001f1800000000000000000000000000000023c800000000000396474e8000315a86b00000000000000000000fb905bc0f0400003dc00000000000000000000000069920232122cf411c81dd00000000f3b90cf34da883cc9112c2008800000001b400000000002820bb06083b640000000000000009068534389457f8ec09257000000000001da000001cbc0000614310600000001a7d34920000ee8800000000000000000031821de8000224200002f60000040d000000007e580000000000000000000c6e0000ea686b80000000000000000c38000000000003ebc00000000cfb000054f00001ae03b1a00000000ef50000000000000000000000000014490ac638749c4800000000000000222b000000000001a55000000000001dba14500000000189000002edc00000002a00000084b8ce00000691c0000fdf32ba16300000db73c9c0000f4c000000004d7c0000000000024c00000521128800008d40bec000000000000000247a54108a1000045f673388a580002a1a8be4f6aa09509b084f400016c400000000000166200007950b9c00000000000073e10e221d201b000000000000000000000000000196400000000000000007d000000003f6898d80000000000000000000b6800003861acc00000000d20157d2c9e0ec000018f90000598468d15f232ee00005f20b6b361e2530dca8cdd37a03a48000000025f400005ea8b7100005a5495e858e2b9217d80000000000007e0072000020a0000119023d60000860461800001662839043e800000001a9456602830000000000019002cc8192cccd00001b1a53bcd8f810200000000e87800014d626550e1800000000000000000039c60ca459c974400000d443db00003c382c68b598000000000001ae02f33b8a68d80000000268459808f2048014b61e9800001bf0c160000e0c800041bc80c8346000000008698b5480000000119c0000000322659ace158b120000000000005f02e0800003048e8b14d4844c24500000000000060f000000005aecbe28ce8000000003c500000000000000000002fa600007c08000010c3e10b00007b072e8d64000150500000d480000000082a0000000000000000000cf8800003e6000036b178c04f40000000000043060000d
  | 58 => 0x1a38000000042fc00012990000000000021e200000c8400022ba0000000073a0000000000003b7800028b26a5c3f2926700004e880001ac8000000002280fe33b5e7a300001b910c404410000000008b20000252048c2a9e77240000000000000000001bae036c00000000000000000007b4800023125264df0819000000000000000000000000ccf9c592fc4000000000000000000103100001f1e5350000000000000000000000000000d1429d800034663b18000159000001538000080f00005af000000a10b6e000000017d200000a540001c8b0000000000000000000702c000000000000000000000000000000adb0000000043ec00000000d9a00000000a9e01f80000000029729206d38f628cdf00006100592000000001e38000065200006ed80000000000000007ca8000285a0000eda800000000000000000000006160000000000007cec3598000000083d516500000130536cdd59e020eae354414382e140cc0000164800000008afc8560582435c55bc93a800021de0000aca0972420c0c190e500000000026400016874264000000000000000000000000b5259200004918000000000985a21b32220c000059a87002dca00000000000470a00009ed80000000389800012ef000068a04e80000461a4eb000005d800000000d77996a0000524cda38f41191e5238c878487294400000000000000072c800017e316c001080001e7b00001b042be8000000000006540000000014f4000000000000000000000028407b68d011c4b3c8816e00001aae42d07f4855a98da18f00000c8883b92d4c7af50f59a4d0000000000000003b4a10300000000344216a400000000000000000005993a660000000176a241e6b94e698b15419627380001a4800006eb00001772119458580001006278209807d1140f357a00004f6000000006630000000028da86e84ab8000000023b4e0f9f8a00002e0c8ec21900000000000000fb0000223c2fd9b3b461600000000000000027944b300001f5a551400000001a026fb400019e300000000000014e29ee8678760000014c24d80cc90000000031dd1a210d500000000d40a1300000000054611a9382a37c4000102700000fe0d0e00001f1a1378be1a2b936f260384f01959156e6f88c61218736f80000613800038da4924db10cbd32967b7853a8fba00000000b93000000005c7000000000000555c0000000403c14782f38def36a480f8000000015c6000000012af0000000000003a733300000bca8000000000000000000260c25ac000000000000000efa000000000000000000000000000000000000000000000000000000000a64000000000000000135d000000000001ca800000000cda8598000000000001a3800000000313948a00002e4814b0000000013e45a68191000000000000aed0
  | 59 => 0x72e049230960000e8b009e18a248988bfa272000000000001431000000007ca000000000000f7a8000059e219400000000000343463180000d6e5b3400000000000000012d000000006620000099031120000000085f1ba85c650110e39268005b859b19ee29fc0000000000000000000000000002a600005951f9834d058187d500001b7c10dc000025b0000000000000001dba038cffe90d238922024000000000000000ce5857600002b54bfca11700008ab800022e0000075b00001a1225d66a8c9f200000a3828550680d1f0000000000000000000058c162000014d80000000000000000000000224b33fa6eec000000000005cd8bc580002d44000055100002344000014a000000006b844880d70000000009c581960000556c00000000a2860ec0000000000054750cd21b72f5a0000d5d129b00006248000000000000000e4720990000000095e00000000000009800000000657cec7978f1f4e000009a8a2e41e200000001f87101800000001374341a6a24000000028180000c56000000624e1cf8401c80ece000041d000017420000000000000005fd8d038000075c768452f800000000000a7405c000000000aac87e33ed800000000000174c7f408d000000000113c00011520000000000020ac0000512c00005fc40e60000b2320b1370a6604d23000000000000abf800020743f8848500002e3c641c1d78002120c2d2c5e8000000003264a71000000008430b262382000071b800000000000000000007210000075cc2f00000bf400000b3819c11c4000036380ac00000001092800000000000e43a03d000036045ff193f00000000bd88000000000000000a312af68b44e920000123c000047200000000000000000000000000000000000000000000000000c8c1f980000000470674b89d3000040e443946a40eb800006ac8000000004148a14000216244b60000024800046c265288c6803400000001002000000006aa0845800003007a7473f965025a27f5400000001d465b20000000023760000c7798a9000001fc2ea0000229e00009c78ad010e811ac00002450000000000000003c4c00000d40679000066010260000000000000908000000001f400000003e9036c05a79f7d0000000000000000562000087515e8000000007e8850300002b140000d9730183080000000000005730000182800000000d91000011b04d58f000853000018150fc8931000081a400000000dda0000000000033540000a22000000000000000000000005e8000023d50c182f08eda0cf300000000000000032ac00000000000000088f40000000000000000000000000000000000000000000009e4000028f600011678000000000004dd80003fd48cc0000000000006f900000000000000011bd80001ef4267cfa980001a8c0000
  | 60 => 0xf8f000000200000104074206b671411c0000032c60fd8e0504bd00001a70afa000000002f140000199000072b4000142b0000000093d00000000000100d80000000000000014bc40ec297801a800022522f3c00016c13c5c4aa42be00000000000000000003d4400000000000000000000000000000000000000000000000000000e5f0000000000000001c6c3c500000048123025686060000285849304c320a3151c8d388fb0c660572693cfb48d5f0000000002a00000000000000000001d4e467816080000000000000006e416ae51309d723a300000000615187119240000000000000000e08faa8000117600000000b6a00000000000000000000000000000016b4000068c000026940000b430000000015b45651cb70000000000000000000000000019331b720000ab31fec3cc218c8000000000001314c9b000000000000000000000002a68000000000003a000000000000052041cb000040ca6bb84b180001bd600000001e20454800002ad02f500000000000000000000000326800000005460000000035e612e4000000043fa00000001af947680000c5384420f7c00001aa8000000077bc878179423f43cfc93492f60000000000020e0000079bca53800034ac000058b800017f85b84d36224100004eb4000196000000000000000000000b58c6e18ba2a62000000000000000000044a0b3c05460000aa8000025fe0000000000000000000be2000000000000000000000000000000163d00002928000000044de0000f9f9a01186c5fdc36a089c0a344754000000000000000ef20d8f00000000e06883500002d8400000002f086af918a8000000000009e185d100006e48000000033842550e720000000000000000b91000016ac0000000153003cce5c03a10000000000002c200000000000000000004c58af1982a0b8200004ab000018467db40000000000000000000cfd000000004f7800000000000625a266000059108cd0000000077dc825800000007004b9d03a93cac00000000000000000007338000000050001d200000000891cdc0800000006e1000000001dfe2d7026e80000f480000000000000003ba0000208336ce6be0800800023360000beb800000001e8800000000000000000022e1303c00000000000183a00000000a3c000061ec2d2800000000000000137c193000001ae86e90000000000016dd0f667574000000000000000000000000003f6d1228f23389e000000009760000000101585a435da4d9c0001320201c000000000003a3600010ec03c420c600000001a45261446a85d9238e000007b01f0800000001cb40001b4b0e2a4a080000b6509de7fcc00017980d602624db494c312be0000a1f159926902374d02a0dd3176000000000002d9800003651c7b3e724f70d7900002ce2000112f8000
  | 61 => 0x2374449640d700eb45e41fc8e8a0dd0303a0000f7e000007ac6dd000018060b122f300c182e70784000000000003ac001600000a8b00000000000000000005364d358000000000000000a653df600000000000000083b800018460b9600005c5834a000035b0fa28000000000000000fd8016459d400000002e6e0000e5099210512000000000000ea000000000000000000000000e6604dc3208b55000000006d20000000000007d98c1b12e312321bcc0ef930d06763b94e510ab90fdc61a09571eb61c5200000000000136c70991c400002f6e2b94000194c00007058f26800000001f7c19c0000322844c0fbf2169000008180000000000000000000000363475501898a2b000088091f0800031a26fb85c216522912841475907cf3e5600000000000225e36980001e53000000000000000000057a80000f63000057c400005a60352000000000000000000108680000bbe000000000002e860000000000037c600005009a8f3b360000ccb8000070e0000479935400000000000000030d45f44c26122919a8192001006c916567e943cf053e155a5670ab8040424543304748000007e44064ae299cc2626588c0001f9500000000000139b000000000000bea00000a606bd80001cf063e02d90000258a000000000000000230c1aa1b43478a0000eb80000000000000001ccc00000000afd1b721ec254d40000000000000008b602bf06e2000000001f00000000107b000000000000cc980002a4c112400011d709401658969800000002a800001d8813266b5014c8cef0c5a000000023d704221758000137818120000896806e2d1605181af000000002ac400000000000000000017fe06783fdc000231710e40000000000000000000e7a9b290000862c00000000124570c05180c7000055b0000170700006824000000004980eccfc0000007067a044b493e9000000000001c9c000089a000000000000000000017fa358632e800000001e3a000000015f90000000000017e7453600000001a830000000112a8f89000000009fe19182e7e86505f79da2000000000000000264c0000b0c000035965b78abd09f8000080280000cb8305c423c3cc093e00be47e4b3c8000245a00002080000000000011ae1e79099688cc95283cb25b615143c30e7a145440e072323e31592089cba7a3c11d187b7084809472972558000007dc17327a450c997e10a601da0a14000000000000eb30c06000000000000000114c0000b36800000000c000001b7600000000000000000002ccc2969c1145fe0000f529c4313e21b2d161018623ce526000000000000000000001c21056000000000003d882138e010000000077d846400001e6c00000000000000000000000000138e0000000000000000000037800000000000000170300000b4848b80000882000
  | 62 => 0xc000000004781984801086a3e5045c4f9900001ed40000000000000000000000000043c0706c000108a00000000000000000000000000000004e20000e951c8310008a0c0000a17000000000001c2c363a5a340001f971d8819c02349caa0000527000000000000000000010cc0c2c0000315800000005bacb8800001f7a00000000000000038f000004c734e2566800017bd01061bc4000120c265e0000000000000000000d63800000000000000116300001740de880000000000078d8000000000000000000082c0000000000000000000000000000000000886154100000000000098519ea87a8db99d722e902230000000013c81f340000000000058b000000000e9250ec0000000000000004d3800021824d38f1b0ce707ee1c18000000017c400007970000000063d8000000000760000029a14e000001a400012c32a7e0000000000000000000794200f0000822c89304290000000000013d1429e000000016b41e668cf0978007100005a24159017b0000283c00020b92a766888a378000402672300000000168c6b4cfe4040936b248cc60580003f602b2c000215800000d04000000000000000000000000002768e6500000b9e85ac000000000000000a270000000067940000000000000003bb0000000000000000900000000000000525261e167c000000000006b640001beb000000000001039066685b4cfd226047660000000000000002f200000000120458900000000000000010688b28000000003248000249c000116800000dec750c00004272b161008cb4800000000000000000000002eb9175857000000000c9a10d0000000000000000000084804d799a625d01be0520994327d86c0d1751653126684249220000000000000000000110a0d5c00000000000000000000000000188400000000000081c55400000000000000000000000000056e80003b9a0000cd807e000004ba4a1f8000000000008128e3d472827480000594000000000000ed113900000000036400001f2074a026d35e80be081f03c002fe72203368f2a3364006031c13b340a033f86ac928e024c5a380001fac2b540cd429c83bd00000000000144000007f10ea50000466800006bf8000000072d4000169000006fec9110e2f1d3e7e140000ec921103fd4b648d6022826db800007b812380000000000006843bf800011970000000000013b13a3057f40338000368a8f2ce54805900000000000143300000000000051f0000000000019e627220000225800000000000630a01f00000000b1400002c9c86ec0000000242636c400019ac000000000000000000034e83470c3807d822748080000000049dcfd880000000788c00000001fe40000000000000003e64d3a0000000000000000000000000000000dc100000000000000028460000000101
  | 63 => 0x3d47165c54eed082f0000000000000000000000000000000000000024f8000000058104598000000000000000000000000000000faf000000003d6959500004a748af8cb30000445c00000000000684cd2180002c1e000000000002b0a1fec000046f00000000000000037348ee04a58f6030c233101379c39000000005980000000000000001b6d00001b6892e800000008b140000ba42f9c000000000000000000000000000000000000008580000000000003fb2b0800010d48000000039f446f8a453b3a000000006f53b62000086f800023320000000000000f81eac3a2885a25b200000e71e6e1d900698f0f0a990000000117f00ed12245830d391a7711c2615514a8f6b3ce2000000000003e42146d1948037182c2a405281c062b060000000000000000000000035300001e30ec100000c142850000000009e8000000000000f46820800000000000000000000000d3212c06e1a0402a920000ded9c9901bc51a504780000000000c000000034bc429451d0000307c73c49e2000000003f4cad8a27a0000078c000211200000000000200600000964000000000001194000231f000058640000000000000003ba0000000000000000efd00000000751000029d20000f950000000000000000000000000000000000286400000001c2035140f3c4be1bf747b00000dd28000000000007fb17fc00000000ad996d543b23120de5157530fc0054b209b5d0e6e4438fec09e3095e16e86e2000000000000000000006de016871800000000000000000002634078400017303a580000000000000003ae8000000041ac0efc783800000002d74978891b2af805f8fc7000034640000e6099e80000000000998b129f80000612000000007b38000203000007d481b48000000000000000000000000000000ef1000066ec0001b3c000044144521da300007d10afb0f0033127fd000018b200002b651399caf3da4404cf8480001caa1e4cf96000041f28738000055f00000000000000000000000ef080002e9200002f680002f4843cc6ba8a370000000042102d400001d7c000000000000000000000000000000a0b00000000785c9b6175e0000000000000003ba67d3518700001fb200000000833000021500000000199600001a4800000005528b2a80000000079072b9dce2d7e00000000a7c00005cb8cb121f22b363d1cfba15440520685000000003e6669500001abb000044ec0e900002cc64a180000000000027a80000996000080d0000000000007ffd11c000003e47f5c9390000000000009df969423583de000016b50000709c00005543c1c45b4ebd000037fc00000000000000069080000e5e000000000000000411476c063600000c080000771000000000000000115900000000ad10dfc0000611000000000000000087e988f000025
  | 64 => 0xd51000033a6000000000002f8c36380f68000000055d0c4d01440b1e0000000050400000000000000000000608d28000000000001035000000007b4c000000005fe68e419ca374152c53c059d00001b08551cc938000268267b400000000000000073b16fc00000000000063500000000935a1b82b424068000031826f40000000000001205b6000000001c380000ac10000214c59f40000000000069ec000000024a60000db41b7a0000000000001be0634000000000001e220000000000000003770bdc8af1477c000000000000000000000006af2d96678800015d6059600006068000172e16fce400fce00000000000000000007a7c10a800000000000b210000237c8290fc1800000000000000000039467090c4299f524e8000034883ab0000000000019d0000000000028a55121c5a28349800000002bb06a20000000028d4e94212204621244fc20000000000007ba800014dc00000000000409e0000bc88e99000000000000000000030cc00020b42db838680000000356e0000000000029248bc4607800007904f48000000014fc689416d15d10480878c2690000000000000000000000054184fb904a00ac000000004f700000000b0d800004fc00002f7000031c251c0b070ad73af274f000000000000000000000002a3c000060c83ff01ea6c60000000000008844000077c439e520823196ae011842f000000000000000076a939d316c465400001362fd20000000104c00006ee868800003716483800000000000187c000000004820000000000000000000000014826167c4c000050b00003df8202800000000000000000032a65a1000000002e287dbd1cd95a60000000000021c243b600000001401000082a0fad000031d863f0000063b31e6000112e073b000052d489d0592000073f800023b00000689c0000000389a0334a1c8be70000025855619083be46f64a9e9c6900004db86d90000437801d48f114f8158600010b300003d20000045f1dbc1d04025ca3c047730ac000000022aa000000004b4137d0dba00000000000000073e8575a22437bc8a0000013c90cb0000041480003ab61a4066d09730000717c0000000000079cc62d000021486b448539d6315cc0bdc16810d303820000000228a000059f000014a52c0405e80000308000000000001f8f3ee60000626800000008f5000005e800006c4d03aa02d000000000000000404857c0e3880000000626c5b98edb34945e38c0d1f99000000000000000148e5fa8eef831e25f66b345c380000000346ca850000077688c800012fd000019e8d058ed30ecc78d014e8000089800000000acf030a7e680001681000009e049a181900006f60000000000000000000000004ae871c0ec0000000000000000000000043d0a45a1e900003570cdf80002b3c82f800013
  | 65 => 0x4604fa3167a45b020150e00000334a000000000000000000115f0d5a00002c3c0000000000000000000be0015e00004c600000000000000000000000000019a000000000000f0c00000000201c000122c47520000000000000002dd800000d20000520cd9a800000006a6cf5180000b0e00000000d7200007a548499be7000000004360f4a000086f8d5486113bd4000000008f1340c78a4000121b0000013062b96400fe27548f9d224d02b853283851b6c43ec27082ec8dcf0000805c581000020e85c04000039d0cbc0000000000037d80000000102e00000000000129a22f4755cb4b015e3eee7d0cd60a23a239047b0c22912036c80000c8700000000000000000e500000000000000000000000000200e1efe00009b7868b45400000000047a000019a8cdb8000099467340e6036800002a7000003c93ee40000f9102ad226a8d88000000000000001199000000000000a858000000041c46698000452200006ec0000000000000000000000007d5060000000000000000000000003d700001d6e2ea62f00c6f81a2000000000000000000054dc00000003df275f4a0500000000000000022180000000000000003986000000000001642000000000000000000000000002cb0895c6c58fed1d58000000000001e74000079a0000263a45f40000fe100001c8c000000000005d940000dca15ee32304ea0262000000011f1000000000000000000007ea000032080000000000000000001ab08e9d1a8046c42206ebc788174b0000380073c9c550000145c00007592e847e04a8b941a35f61e20322800000006cfd0838666036051b000000003a1200000000000131064f00dd1a8806162e38cc10de819d40f7cbb009fd279c069c0000000259800000000000193600002098619000000000000000000000000000000000085840000e0f2b220000e6f0000000000000000d38149a1d38000000020e6009400000000000000000023bf00000000f7380000000725000000000000000029000002cfc7f8c00000003d324aec000022d02326854980229c000000000001ff90000000000000000000233095687f328420001046210220760000dda9ecb3ac800000000000000000000a5800025d40000000000007027dec000033e00003eb04ae80000000000000000000000000000017d500000000000000038383748fad80001274000000006b139140144cd1093741520000743947f00002724000000042f826c80000000000000000000000000061e40000000000000000000a5a000024f0000000000003d2110609390000288cb8c000000008c58000008738c4000000015b418520000345000043ea0000f801d051bfc000000022e30f380b343c288ab26fc0000000000000004d4000000003eec8ac887690a82e4667241ff1d9000000
  | 66 => 0xf2d000000002ac0f210000000017482580d7272240000fc100000000000000022ae42c000000000000000037f13f82a0400006f9954b157e706079916ee3a0289483ed09e144f86cdc00023033d0a0000000000000004198fb290d400000000a02800036e00000e840580000009100002264000000009c2a2b110ba000000022862172716c000000031a887f8d9a02d341848c8909718d2430a394c0000000000008cc00007c1000000009a48000402c0000ae522f330e8000000000004532685c000000004160000cd09e4900000000fc9222a24a064a40000000000000000000000297c22c400016d6201600000001e451aee40340000000344613a49328d93250a87304071b6632b4504c000000000007ea400000000000000056c095831ae282c00002e237d41d750ad800007b200001a7000047a2476cf7b906140fc01b41b6000024e00b989488000190a3f48fdb14553a006244ad70f422fd61a60b58234c2e527e4c49382ea335e386c43f912a28ca591cc0588812812112800017b200000000000000000008a5084e00000000000013d8000242871f0000000000000000000000000000000000000000004928000116900000000000000000005a44000011000002de8000094f00003370dd98000371c5a0cc6286873a8277610959834164654b51ae86150aa42d54481800000007bbc9f40e9631c45a4c00000000000000000003d700000001174800028b66e2400010fc425a1e1000013d51e0265b11e51dbe000000000000ffe471e3150000085e3fbc2874bc480003e085468b63939722324ef8239013d272400009b985b9000043ac00000e6167e171109c0c9d181c624c0000c3a1d9e78dc3e500000b6a4260000000029c6403c6169107405e4560c39069d127e7ba84301e5d43108af007700734738000006d097538340aac023128a34480000c4c224600006a5800000000000000000020f7406c000064823ce09a600000000000000000000001cb300000000a3e870400000000000000000000bb0000066b0000000000000000000000000000dd327a5ed07f79fa123d60000422800000006afc00000002474446c0000ea946300000000000040c80000c950fd40000000000000000000406cb578abd45a60000000000000000000000000002b4000000006920e0226c0a5d08312e22705c1dd000041120000ffe0000000039449f2800026c800009ac84a1377832c4c50000000000000fb3800018de000000000000000000000022e803540778c2d000000007af911a13e200000fc48e8a1fa3a208c848d580000e564334c3d15fb3dd65e8c40e9a8c0000000000014f400000000c328a52000036900000000000035b8d1880000000000000016010000047c000184932e26480000000033d80000000000033ec00000000
  | 67 => 0x28a80000f2a800011ce0000f4400000000576cc5800002630214439c81c619461bf077b877900006c9800001b733aa442c0000000000000000000000475c3f1c28502f219c400009210de6000000000000000000000000001e080000000034680000000491c1d9024803c432c80001efe000000005be8b502a5600000001fd4163a000000000003102235d13394e42ccc57940000efc46cc2ef10d804c900003a808ee0cce0000000000019fe000000000000000000089c472480002f264d68000056b00007eb8c2d867e002e0000c02800000000000c1c000000000000336187043a8514000000000000000098e0000000061ac820188b1934000000000003770000000000000cea7ef40000000000000010188000000000005c780003c7a40d400005081d7205240000a09000078586170000000054e4e3a800000000e50000000000006578b1e189d000037c0d7f91fc00001b985948aff000073a03c9000e00000e2000006433e1e515ce7300000000000000010f20000550c00000000000000049400000d8400000000000342200010670000000047ccf72800013dc0000e85a200000000011e680000000000101000003cca000082c0aa5431800000000000000000000000000000000000000ae400000000000000043ba79a40000000000000000001fc02e7200007c706d9051c066090500003c64390c025800000000000891956b23482a0cb90137240f800000000000398800000001fbf2652223800000000000000072b0ef31a6800008ca02fc359c89d0000115032921a0808d979a3ec2160cfa881f4033430c40000dc8099a11a000001e500005dcc00000000000000000016f3000000000000000000000000000c28000000001928f6d00004a4ca2500003f780d0c7ac05840000000039d0e122e1e69640001617466c0000000000022d4304c00000000000000047f000038621db4000000000000000000012900000000152800003668c98000165435808cac9ef1a7e3e3600000000000107e000000014ac00000000000000045d83d24d712204059c8e4c000000034c0770400021910000000000000002c6c1e9c9f9000000004900d82000000000000e080000000000006e29feb09fe3f0c000000010a0000000014070000000000010e333160000e9a00000850000000021460000487000002a00000000000000000000000000000000000000000000000000000034b21033d54339400003dd433e8f4cc3189600c020000000000023f6000000014f33f3e00000001b16188a8fa00000000000000000001cc702be01e400000000000000000000bc00008648f36010f0dd80000000000000003920609000000000000000000000007f040002278000040a48a18e6a00000000d1615783d1e000000000000000000000000000000
  | 68 => 0xe0f181fd17f13c7400004378000000000001078000392600000001bd645ae13d8000000000000000c13800000000000ade83e20a583d54ba680003e4a00000000000413e17d0000000000003b8c000049c0000657000008a70000000000000000c0c00003da976209d85b18840000005aa10b919d9ef42c56789093c053a40dc13b80000000000000004e30892000000000000000000000000000000267200000000d140baa613c50305912de01c8800000003a3c000112b09cb00006474d5294113df02d388ba089a229c1c7423b1d591b5e36b016b92100a1a1a90db189990fbc00000000ff300003b5043b8000452424840000000197200004ce8000296e000046e0000174a1fa8db786a203cc000000007521c144671048800b198a2db0581a2f00000000103c800032ea00000001bcf3c8434885f585ce00000000aef80001f62000000000002a02092c00005150000575c0000000000000000000f6f000047b8000000000000001143800000000000000000000000000c0a800026120cc488b167235848e64efc835000ba4c3800011962f980000062a17d339c000087d00001ecc46fc19602462740413400003d3000030400001e19312a00011a280003c44149c88a80000000000000013df400600003a305f800006f481c3217e122a0000000126f0000507c7f89131000021d8000000016dc00000920000000000000001d1339a42fc400004400054356c000000000000000000000000000000000000000001e80a9c05e036f60000998000034062eb00000000000033c4f318bc6000046180000000158800000001741000052800001ec90000150c0001e140000893c5fd23cf260a11b800000000a568ee90bd000000000000000000017a80000bec21702a7476fc2780d7e06f016785381aea16a86638156190545de83fcfed11530b5a580c534a33e0d74045c3128000267e11840979e78297a860043189773d084114de38000000052a08a4000000000000d7880000000332814d000016ce82847258ef445e87b6cb2419d1000000005e9800000000000000000026880000b1000000000411800014720a0a0000697800000007e88286000014f600000000000000031f069ca1160000384d03380002d1055880001f3704fe8dac000000017601878000099a444a2c6c9959de01b5014a000000000000000052c160505e200000000000000031f4000000000000000b8d800033b2000000009ab0d9e00001860000000000000000e2800000001073000000008ee40000000000000006d59e0d4124403000000003c2017f4eca0000000000000000000000000008bf00000000000000014863c9e37b80000000047471450ef870b000071747a581f70f5231a832d0474190c000000000003c5600000000000000000000000000177630ac000
  | 69 => 0xcca0000000000005b0018821fa11d218c0000c66a1ec000000003df93cc00007f0c00008081a4816184df80002f067848d9d2035000000004370556000000000000ca100000000a4400000000000083aa005000020651161b9731882304000000021c02d901ef0000330600000000000000000000000000355410480000000000000000568000000008a47b90000380800000000bbe3c260000f138c7e103400904cf0b8924a80000bee8e270000000079c800000004a551738000000000005cd800010700be40000bde34be34482848e6e092803f8000000037e4000022e800000004c9000000000000653819d000000001bc82d180000000000085505062272000000000001b3e00003448000000084500000ae9000036500000000000011586bb00000000802c17698ab40d04b50000141d048e00000000ddf28e20000af380003c08000100c000047925384000000030862e40a3a07ce31040000f680000000041b4000000000004e0800000000000000000000000000000000020f8000000008e4962d1898000000001d4000046ccbe3839c1f3687680d695070e1000000000796197c00008370000000000000001357221a7d3c2a500003a2e2494000094a00004cecb8b80000000000057b000800000000e5f0e0647a00974e5d07d8000013e80000175000010601fe800000000000000000016f8000000013da33c0000000006d1000000011cb930740220000e9f90f825900000931a32a014c68740da800032320000000000000000000441000000001c582d41b0b000000000001de60000879c13e00001ee23f28272a0da22c2000000000000000000000016a800006b3c00000000000000000000000000110c000000000006fe8b7d925a413a7bb800001941e2c00002631fb7238e2b8040a104e000025a80002270000000003a00c9544b02c282f103f000000000f1c05b00000782907498c922ba000000000001e40000000000000fe00000000000000000000000000000000000000000000000000ea897990000675d1a980000000523400000001d5678f00000000000000000000000000000010fc01fd000000000001e8a000046c90b19afc000000010e9800043e81bd0de5800000000000000000043ac000000000000750314800008a5000047f8000223c0000000000009b1309a00000001cbb37ca7520999000000000000c34800000000000000000021cc000045c800035d63c28000000000000000f85000030ae5534000000000007b009ff9e4716402bf000000003cf80000583906735b67b28a20800038ca4c886b38000000004480000000117e8c288bc1f3801223664c71a2f80000889c8d092763b540000134918017b284e480f17900a5e23d0b0680000000000000004623b664a8000001c4440
  | 70 => 0x1940000205d30420001024000000000000a178000000077080000000303e00000000b5841600000000000027f68a24000172d000033d80000d9200005c08423800010f218b1197881f0000000101d9016170023786678ed22bda4818c518000000000004729f7039781af4000000025fc0000da504c100000000f2b8000336c0000000000000000000000000022dc00000001f06234a57cc000238d1a140000a948000444665949c00000000000000000fa900000000b74000000000000c5c00001d7c00011bd0000000000005410000068868a400022a214060000c2080000000200c0000000000000000000db3098488fc4398680347c0000000000000007cd800000000000000000011df40740000000041e00000000000000000007adc000236f2d0a00001f20fec00000000c758c4e09c889ac257142743e600000000c32417063603a4108913b2338c00000000000000015e10760000000000021f70f8c1ebc8739987049a270c78689ff36006aad0c48000000088e4000003a000000000000f73329a3e743c8800000000ff000011e9478e00000000000410c000007394dc10da88ec00000003b860000cf813cf3fe0381c000140600000000000000037726f740001ba4311c03fc0000000000000000001bf31e8c0000d90869f0b7c03bc5d50000000000003b4800016da6cf437400000cba0000a639946371a0000cc5155c0000000000000000000000000000000eea737c0000000258e35880001f71000000000001464000000000002151408a7b748ec800000006e500000000222000000000000000076e40000000268e4de4ee395ab4518000000000000000000000b000000000000000000039ee156c0ee000000000000000000016b2000070a8000308e000113b873e0000407c00010111e480000000099c456c00000000000000056800000000000014440000235354800000000000000000007578e1f2eb4000000000000000733400000000000000000006be00000000c1e8ee62e0043782b61f643b2a8b980000ecc2c5c4ec000007170000000068c800008423ec00000000224e6cb8d1e918236a2260410600001aca26e86df8fd70000000090180003528000000014f500004084000000000006bd800022af3c06286004d88ee000000002f8972b000011e08c1800000007b7ca6999dd0000207800016ca00002154a29000044280000b228d0b121866f8fe4980028322518a550a1f046e863cbbb8761015650f51249b280000000047e098f1e8600000001fe4011a3fd094e06e100000000819907000008d8000023060000000000000001e5800000001a53000000010ce847c00001d60000000000000000411800030cc4dd490ea11c000035ac84d80001a4000009c51d99000036f096219020000000038280001d06000000
  | 71 => 0x3b9a4b0000843c75b8000000033e00002311027e00003540000424e0000ef6047329486364ed687351a9400000000000000081e020380003d3c2c500001145000064b0bfa814005b200004160e650000022c4d5000000000000000000005740000000000000000000000000000005c48000000021fc3a20d9692d600008d2400000002bd25bc8146001100000000a39800046ec5f240000000000067610a392900000025000023b1050877e088f9e6800006fbc74897ab19d80000000000022f8048915b9f24000000006d689cf39c0000008c00003b885c745bf02e400000000000000035403708000000000005bf832b215209080000a0712d2000088200000886317a78cd049a1a70a98000077900001f3e52c00000e0b3fe24500000000034a20000e6003c30000696c06b1766000063f47628000216e8f700001a6311408cfc2548ce40000000065107c4442a12cc0000000013e00007599978000000009ea000000000de400004231eb400000000263000000010388000138a1170acc00003e6200004c9000000000280bdd0caf00008b50dc390ff327027d4331807a21a2523cc019f6800001120ab48000232600007b106551a4600000001e7f00d445d83a3837630306024c9d00002ed8055406b800000000000000000000000000ba880001a8e890c0000000000000010bd8000000000003de00000000000000000000000000000000003ab042f40000b9f0000000011400002ec8711436f90943d7e7ee05d98000000000001e90a9b0b7800000000000000060046c3800000008c94000000000000000bf283a200000000d9280000ff26e6c000000043aa40d000000003e3a29389dd023d298c2ed8000230c454e00008de032a00001df80000a3b00001218dda0000000036e0000000000000000ce7a140000038946200eed225c36a40e481fb392e6d605109dfd31c00e94727032d3256781400000003d5600009b09092381c262c00000000000000000006a7000057088508000000000001f009f6160836a8ea0000000000000b9a800000001cc427422fa0000004863b000002021e04c2e8b09444c0000000025500002c7000000000000775cde0816627640000dcb013723ac0000c4503d800001a1800000001c2885e000004bc1f92241d1cd174700000000e820a87073e000029880000ac40000000146a0270000000000000000000000000002696000086d90f945501ad88238852196a8b48d8c83be28ec0000000147e22d60000000164b000000001f7000000000000425092d204c4e30000000000000000a6111d0003e12d8f4d1a9a42e451e84eb9c2f0000000096515c000007bc40000000350c000083e00000000390424691380268782c04e814f000000000000000000000000000000000000007db80f000000000000000000
  | 72 => 0x9d4835000009b50420796cdbf9d2b000000005070c5b0c7c416800016291e26000000008aa26c63e0cc050000000077f80000158000000000000e5200000000aac000009880000988000d354c33200000ea53a4c5b6800013a1000086545139e4a328e6b60e23843538ce36f4c73000001aa4da0c8580b92fc000006c800000000000107d1dae000042d80000cb40e706ad0628177d196c0000cc880000000000093c8a8d3d0e0000db298f0000000000000000394e2d4c0000000302e0000000000025c40000000000000000000000073c0000173005f194f42e25c580000d790828000076f99ad00008878c7b99de2cfe00000000bfd324c52680000000000000000001ff6350a22a00000e732bb80000ae40000109a0000000158710360454d8f000024cc000009c800012fa61480000d5e0000000000003b5000006f40000b790000000000018c63e9831c4157998d000071cc000000042522fd8000000004121458000000039360000000095225ca7960000084333e87c1d08888b200000b4400008d300008c1400000000000040c000000000000000edd8549061c284909b846d452c71309ec0f8200000000fe395c600003d3c000000000000000b699745000039283e90000000000010139bc9164c6a840be83770000572c00000000000331800000000000000000000000000000000000000000000000000003260000068380000b4e00000001fe900007698000000035fa40c00001f2e00007b98f6a23da00006a004ee1dd02f9641bc00c908e033603a000000000000085061a08bd1af8000026b23330fe80000f2d000023a6696886d10a0000009d48fc224e000000000000000247e3c54000079a3e7c00000000004000087180001ee80000000000000000000000062200000000244c435800000000000000000023c68e1c12f126416a20540bc28fee00000000000000000000000000000006ea75a095f9fef000000007dd80000c840000000226200000000e15000019b600003640cac132223e80d1a08429d68e0400000000aba00000000219459073a88ff97da3b34001c0000000217619b8000000040d874b406e00003538000000006ad000000000001aaf00000000000158d000000000000000000000000000000000000000000000000089b40000000088a00000000ece2d3a7c3505580000000826000000000000000105b1532003827e8e27075c111a727819180000000064c00000000000000030ba34700000000000000000c234a403b800000000000e9c000005223cecef280000000000000010ae000000000000000000048ec000000022ea3ed431b0000000000000000b69266800000000000000000000000000000000000000000008200011420000304a2b9c0ff000000008d509d4000000002f246400000000000001
  | 73 => 0xa98000000052d00000000000000000000303000000000000000396256fc00007c200000000326000029c00000000170900002ee46358000012a00000001bff4396000000000001ed01dcc00006ee000000000000a5600007e800000000419200000001ef200000000000000000000001056910f0af200000000000000000007f30000000000000000000000000008b80000465a3a283038000000000000000000000000000000000000000000000000066e00000000000000000003560000000087b40bc865c16c6614072c0d8c463a3158f458000061a00004ca18fa0a54000000000000000000099b800000008384000031d443e000003c0590415c3a98000204200000001116922500000000fbf88d6393a3b2c0001d0a416e12d04fa15eb1df07aa4000050f000072900060d9d18c80000000000000007b30000000000005480644845f0b8a0000895800000005994000000000008d04fd98000277000000000000000000000000000000000000002378151238785690000396c000111a800022b44b980000cfc0b8c0fbc47608101e2e0dd04d70000218e1ab8a8610c800000000d480a2400000000cee186f2f9e38201b0864a02e68e10162837c223455900f50801000013850e080002c3a77ac78c1b88288e0000805145f0000000119b9d5f155c35b4cf91fe043c800000001ca0000076380000000000000000000000188400000000000000004c80001ead2db20000000236c4510779c00023c4000083bc000129246b65d5800014fd00006e080000b06000000005b900003fc44484000174a0000831800022c7000000000000000000000000001525168e0000071000047405fb000014cb000000000000000187c0000000000000000410000000043c225c4ad91b2f0f0e00000001924028a0000000000000000000baf8000326400000000000000000000000000000053b800000000000000000014b800000000d4c21de00005bbc0001608314862fc00016f11998000000022c40000000119c8b1f000000011111fdb00004d6c000181b00000000c8a80002b2e000000019792fbe8834c119b0901827a9036d80000000857c00005c23d6413c800000000000577400019a70de083b48c71917000072480000000000000011c523b6000000008f788b7000000001ac976f04ec18bc000000022ac0000426000006905a7c0001b061c6e47340000a5d3dd80000bae16b202a27110cf480002ee200000000000416a727c000094e0000848c0000302369e000000007cc00005b140000000000000000000000000000000001fd1143400000000000000067a884c80000000241000020d2213c4a9800000000000000000000000000000000017ed435a757052e000000003f74000000005b63e780000585000000001289faa0000000000001720
  | 74 => 0x7de8b17800009365538e4280000000000000000000000000032d800000000000d410000000000000000000000000003d891650000000010f000023220000000000007e61000bbd21d71e0471b05278fb61c42000069b00002a2800000b68c0500003d4d062800000006678000000000008c1cac48000000064f915999120000489c0190ab0000074450d986fd00e44524000000031dc000000000000000000000023124004000047480002df2000000000001f100000000000000000000917831b00000000000057b000008c841e21a43f9c00003cc9da8341e0000e090d2a020a5ae10170653432c0000b4d96fa00007318b98842000003e400000000455860c0000036000004a9c000155e050c00000001b3329be0000fb51a1a32820000000237d0000000000008ce00000000d560000360a000000010142c1200011cf09e20000000108c800000000000000092f3e2a1134fb5800012da000000017060000279c00018510a6a1980000000000000000000000000007be8c188000140e8a8cea98dc746ea5e08000057a2fe48ce800008cd2496000000000000000707857a23a11d5a665400000000fee3c3c47c00000000846800019680000000000017a918ba152031d095c110e0000000000024f861286110c1b000000a00000315000000000000000000000000000252000000005ca800006f67758000000002d0000000000000000000021f101d0000316077c800039de0000c540000062e0000000000019d644080000000000089f40001e9b2a4800000000000065e0000525800035ae1ca4e5a0000236a36600000000000060e4d1fa265000000000001d6f402000007499ee442760000000000000000000899036e3f200000000025f00000000000107800000000e03977c00003c9c0000c680000000000007fd00000000d9016b700005decf390d40319c0000e1b800006e01afc000000018020000433800027ec00006819e1f210400000000000468c6a650650000000000005c4098000004f584679ec10000000000012cf05266cd8ff097790c524ca807c0f74000000004140df200006040cfc000000004b903341283000066f000000b70000000000004bb1eb2699861a800000000000c298a1b09ce0970d488eaa122200ccb92925109507b201db00003d4c21103c5a05100000000c43000018c068e8000060228cc70940000000000042c486b0000000053140000f5229d40000255043029ec1d1050b000039e0000000001cd00007c5c0000dd3158000000000000000000004170000455260ac0001c3200007bcc01b0000000000000000d1100000000000000000000860f33132100000000000000000000000f3d152c43a4000110e00000278809882a8c8400000001094000025ce06d0920800000006a74eb2800000003881
  | 75 => 0x800000000000000000000000000049c0001b0800000000e559f7803ce0000fab0e983c8c29f4000000007a20000338800000000000e768000173800000000de300001e94000000000000000a018f4000003614000236a00004374f079b39000000000e28a54150a000110b9ce100000000000010a30ce28d0000233800006bf8000058b000062880000000000000000000000250033b499180001a6a25841b9069700000000000177e000000003dc80000000000000001920000000104e158a0000665113080000000000037d0000344c0a8461600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000016c230407a5102900003a980000cfe00000a7040f4f3a000019d231ec000094035c800002ac800000000000000000020ba35c400022fd00007f74cd0000000003eacadc16f80cd214dceb48000000070a490b0d3c1fd0396c69b80c0000000000000664000000000001df300000ac00000bb82a4e884899d1cd90000000043e0fe40000121400003ed0378000000000002eba0000000000000000000c3e12b325ba3e60187a2f5000000000000000130e00001bf000000005fb8e6d000010fc1090ec58000000000000000000000041200001f82000037fc000209731284e38bde017c24620000f58956819524d3104b0000000059d81b18a0c36f034249b8800000005420000000007b66374000088808ae627d053193b0000000071880000e4c19bd0198f93000000000000000000077704d683e72dd8000055d04903f38176c000000000001068a231e2a00005e6c00000002e584f4000013d900000000000105b00000000f87000005160000000000009da000000023de2402587c60e000000000d600000000000000000001f570000000083e800000007104000089e2bcc000000006b528448dfc0001567452600000000e403a840000f98164300000000000003e1d6051886f09b1700000cc04a80000000000000d09d4707342048f3aa34f01ec0000e810eb118b200005b7945e00001c70000000000001db00f7913335cc0000998800000000000000127e000000008b120dc07ca000000015fc104200000c606e200000001114000000003f9c0001d8a000043d82f602f4323400000000c080000643000019c8000048e400000003b52334471914ed274a0000000039e278e00000002319288675a83201d9f08e20000f88a02c02ac000040e00000000236c9458195021226f800002c72006000000020570000000000000004560000000000001d6c39f80001cd40434000000000003ef84e608248e50021655b400000002b024da85970b2c0000359904d800000007a188d810ca011e0000c4b1fbb0000000000000001f5c0000000000040a60000b71800000001474000087a
  | 76 => 0x34de000000012051da000000001f91001e000000014043a603b5c4ad8000000000000001699000000000000000180e00000b11a8e0000000000006030000000000000002b1e65c800000003aac000000000000000000000000002370307c7e69674246e0000cad857f000000000000000456862300678000000000000000000164e76c86b219a842e664589388000000000000001d750c721208d0d8b5e000000011aa8000000026f00001bc000000dcc0001393017a1ea800022e20f063db00000000449000000001d37000000000000891000000004db8000000000000000000000017a45bb8000182e8b2c3891a0a156477fc8419032000050607bb040300e8000000023bd00007b0c0a6089908bc595c4e01288000000009f5823b000015d08b21509173a2ea51de0217064c7c080000000000024044a2800000003c14000097800002490000000001021110602098e16980340000000039c4000000000001fe000002c0800000003538d850000000000000000fd5024600002c9836736fa1bdc000000000008a5c9059d871fa01a982d8905300000000ca29052429a5ab000018422c440000000000000003ca4000000000000000000000000000001104800031d00000a241dd200000000b7b912c0000000000000000000000000023c214981f40b7a92ab2d045ae47d0800000000f543ff800005c6000020f800027c682bcc79000031ce1b18dfa89a6060a4bc8f44800015b6000067f8d0504ce00004b218f11bce00007668c8d080c0000b19a0740000528c50982eb27480000b53800021222828398038900006ea400000001466000000000000fd660489600d0600002da0000000000006a4c0000e342d3402280000000205e00000000a72000034f8355895e00006e6490c1b5a00000000000001e00001ba89a900001c5a16a8caa1aa70000000000000000000000059d89052a382b443960a590adc00010c100003cd67e202bc000029a4000008d000008ea1540eba077125be0000feb0000000017cc0000e4c000076240000000000000002ee919d13447c1400000aa10c480a81fa00001a1e699d1b916fd386c75e000000270000000000011bd343c8f64cb21b411dd40000000031900000000f9a12350000000049703b7000000001c78000000069cc0001a780000000000001ac183400000000000000050c11dd80000b583128aae99c40844000095c000000000000b36000025d88bb4cc79e4000007118d890bba03aa16340001414056c69b86959f6346fc56b0ae398cc1ff48734e658cbc2fac178c00000000000000095ca0d7000040dc00000000000466006603931e327f9400014f205f644f80000d8a0a8c43391d68adf00000000000197f00000a6c67700001b4a20a80bc0000000023482b9000000000000f93867800000da
  | 77 => 0x178085900000000000000030c800000000000000023acdb0800028ee5e9416e0000168a35540000d4f000039a4000000000002c950bb80003e800000000000000006eb4000000000005a8c53012982a3288a471d00000000000116c80001c2e86c800020bf000000000000000000004ac0001a3700000000000212c000043a05c695f80000000096580000238000000000000000000053a000000008394966800009561e8400000001df60000000000011800000000000000000000f5722da3a0c00000000000000000010d1000000001c507c2800000002f5800011ad00004a50d749dfa2ffa00008160a49000039bcefa8c5300000000188891d1d1246411918000000028e49e58755373c0bf4116030109ea0000a278000377e3f0083498bc00000000000000000006718000000047644cb448f8000419a000000000000000652000000002810812c9bd898240b400008e3199d00006af04fd8d82284a000000012e100000000000000044ba40d8cc200000000765800020e2000065ec24e80000000000000017d02f1a17ad0c504b806d633c013a000000008680dd30cd2000000000000000000000000000000000089ec0000bdc374000008f00000000082f4c508000000000001b6941000002ce000000000e94000000017330000350826d00000d88000000007953d1c00000000eda000000000000c5f3eba000015a0f9c44340000266003c0000000000004c03d8e8b74409896e3cda7148fe7800000005fec89b97b80000497c3eb9c82435400000d8800036384a302b2000002d800007de000000003f810920000000000000001cd12f840000c2e11cf255410d000000002aa600005550000056e0000000000000000000000000000000000000208500000000000000000000000eef000040504be47fe832b0282451d16a9f6000001ddc00023e0000000011d31e5100000000000000038c8000063480000000000024a800000000000000000000000000000149e00008d2c1cd8000000000011469555170a1cfd16f800016922ec45218e5409ae6b8c0000f120486396800013ca000038f806700000000000110d80000000000000000000000000000017ac35f4554800000001142000028c023f0000000082880001b4662f83901d61215200005fa800010b8000000012c12c148104000000000002c440000000000073e4ee5814234680000000000000003cf8000001d000000004d0000000000000f90000004d8325800003a00d9817980000000000000000000000071811980001f3d0000575000000000000000051780000000000000000000f003e4800006ce428884c400008b800005b44cd5800000000000f3f000002ec6d7c373a3b7314a000000016ad00004214b33961e000027049020391000000010118e72000069c0000000
  | 78 => 0x88640001ab300003494000000021ae2bc0ffc06512a98306000008c62574000000000000000560038480000000313c00000000000000000000000000166800000000000000000000002ea40000000000000000000000206d00000000a4600e120f60624dd40c3c1ae8143800005a11a864edc0001f89000000003b28cf9000000007541fe7368c7ae07871399086650d0514a31b353c24b09dd820200000000d63070f025c0000b8584ce29421350000214a00005b5c000000000000000000000000000000000000000003278000149610c2076441a2101213a000066c9eba2dd200000000aa433680000f5a000000008f94000000000000000000000014da2cb4000000000000000000197a14605de041b000000000000a76000000001b6011800002dd40c90000076b00000001197000000000000000000042d40000702000000000000f088c0200002314ced8fcc00006090ad8000041d00000000000040b237e5053800009f0000021884fb1c8800009dc834d00003c981f58e0d00002f8400010151e4a0000000000006805c3000011c2000000009960ee0411c0f34ee787c537420000fbc8000000000008cf80000000000000000002084000071f8ed6000000009f380001528621c24715463c760d69166000012e8000000016491ee006c887a800008fa459c69600001292268c000067b1b12000000000000ac00000531996f00000000000000000000000000000000007a4d0c2192311e07d2c00010ec00000000ca21cdb000000000000d69134882cc0000df73f1620340000a770cce0000000000000003db80000fcf00000000b1d0dc0000000000000000000003f4e8f80000000631c0000000000000000000ada1fca6b2400017b00e9800000000000000000000b5000000006bc0a371781016c6cac90d1a75000032ec00005fe46840000b7a1243000028f800021550f76401000006fb0d101838f1f0000000005c46398000000081ec07021e81a3a000000000003478000000000000000088c00014d60000000000000000000000000000c8000056e85d19da400008b7810b000034d20001181000000000e5485a8f220000000038c8eb400000000680000000006bb00001a950000000000000003f483a1000002e80000062cd1a8000000000009cf00000000687c00008560000000094b800033d610bc93088300000000000006810be42498760800000000000423161c00008cb0000000004020000d56800028a219d0000000046020000f3502fa0ea64dfc000229e227e0000000000000005d640001a7a000000006e88000000069f0b908f54184c74f8000000015784c040000cd800008d4439904550b667fdc00022032f42000000010ab00008bf0c0e1c7e1c8a5da49e101eb323600006f2800000007d7c0000000000000
  | 79 => 0x35092d8000290a000000000003d6048b8000000000000000dfc878230fe7bc00001b2400000000000000000000f98000133c00000000bff8282208800009d38000000000009ae092a000000011921f1800000000000000000001d8cf1c800000000000000054740388d8d12a11cb000041a80000000011017bd1a5158c00002744000000011685520b941e5e000000000f700002a668c210db0bad00005a8400015e10000000000001ca00001a1045600430b862e50000000000000000000002300000000a8b0000000018fc000000000008d94342818e02406d5800015773a346800000000000000000b910000404a00000000000000000884c6800000000000000105900004798bcf000000008f7cbcb86570000000000009ac0000000000011af190e38b11371eb31d7a49ecfaa00000000000000007e200000000f240000442c0000000000043a04e1824b09ed234e8278000056700000000000000000002368bc50b70200a54b80001573074644f0f418000000046e400008c4000000000000f3c35ac227c000000000000000a600d9544a600006dd0f67000000000000000024a6278000000012643e4400001f6000000000d58000464e29910e286c0370016bcd6e933333ce47f4e3c0000074c410cfac000022cc00002f28ae811a05f350979807000000000000000000000000000000000000000000000296229e03b1216000000000da49ddd000052b506c80003eb2559400000c32bea57dcf1285010000000112200000000510800000002bfe00004112063000000000001e96000000002eb800000002f7479a85bd098622b8dbf048f00000001043800000000000000000000000000000000000000000000000000000000051000000000b000001d4500000000c8e04080000000000007b7038687b902f8e4f00000000000182200000000e48800038b00000000000033802508889965d39f61c9000000000000000000009410aae5648d2b93ed000088b8f219c7d00005f9000000000000000000000000000016c0002009000000000c080002bc481e80000000000000000000000000000000888bbd17dc00000001835000000010d7800000b80a88fa1216f27ba347031318b704a02544000212a000089f8e0600001bf60000000000000000000e4c0000109e7a5c534024e13d06f80000000000000000000204900000000000000000000000000230f00000000f0d9f1a3bd2786863c80003afe0f8cb82887100008330bc38000000000008788dfd00000000000000000000000000204e205a00000000cde0000000000019d20000149000000000000000000000003a3a000020e9bc8051e5cf000010793ab400000001d250000000000013ef0000822000005770f68518c0fd12d0217c568cfa506343c2a00b800007cb1e5e7d1c9de80
  | 80 => 0x85700007b34a301c343aa073f4add92d8420002fcdc3054b0efe029d061a3dd00000000000000000000000000000000000000000183c345a79705a185a0401821a51409ed10e7a829400003ad2ee074d8000000038660000da6800000000000dcf8b863250172913c93af00000000000239000005dfc5b1000000003fa40001e4c000000000000000000000000000c000000000000001e8000000004fe0000189200000000000000000006538e10371e000000000003dac3ded0cc8c2f23160000f2900000000000000013fa033c00000000000000002911cc0000000050a4000000000000000170030911aa00009f70000000000006d0000019cc88dc0001124000000011b80f79000039a0e1f13ea19861fb110e8b0c000025fc5670205111661b00000ee900000000633893b43300000c0a00002d4800009fe89380000000096e000023460000bdb003800000000000047e1e0660e84bca141000000009fb8613078a866c00000000000000000019f9000000000001296184a000000000003c023ea0f0615d01a04322000014d03d002f5c000027209100000f9e0d501ac268bcab500000c3600000000000199200000c6800000006ef4a9a062225e82e80054000033ee58c109d228f1af40000000000000000000551a3920000558473180000000000107982131694000000017c0000000000001437000069a80001390352431e8ccd80000000000000000000fce0000dfc19c504542e08861182600006f1800014c10000000000000000000000000007891ebe4c0c0001a7900000594a29878f00000000000000030c000009f880000a660000e0e822b319400009c20000264a71d83f4104108a47e98f2f84e020be3f700001613100c5b6c40b21fb3a3230f4f2c9cbd3be2000000017ae000015340000000000008e00000000000000000001e7600000000e318362353e0b7c5f6800000002fa044200003fb20000e07800022382988000000000002aa40000000000000000001ebb0000000000000001f8453e82fb9b53023c0000af0000022105168e7580000080069075e0a57000057b800007b014ec000000018732a1e000000000002ce600005a080003e180
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x863664984520431ab24c2290219598e6114810caac7308a40863964980520432cb1cc029021179cf65d08108bae7b2e840845e73197420422eb98cba10211d9c465d08108f4e032e840861e5458f420430eaa2c7a1021179cc65908108bae632c84084767119642042a639aa52102117dcd65508108b8e6b2a840845e73195420422eb98caa10211d9c46550810a98e6a92840847575d85420423aba8c2a10211e5d46050810cd2a4302840845e73194420422eb98ca210211d9c465108108f4e0328840847671997320421f3a0cb990210f5d065cc81087ce832c640843d74196320423b388cb19021559c7538c810a3ae829c640854d7214e32042a639aa5190211d9c6654c8108f4e132a640845f73595320421f3a0ca990210f5d0654c8108bced29a640843e74194320421eba0ca190211d9c4650c8108f4e0328640845d76d4c32042ab38ea619021175d8530c810a3ae8298640854d7214c320423dbaac1208219518e51504108bce7b28820845d73d944104237396ca208211b5cb65104108f2e0b28820861e5458c410430eaa2c6208218b9516210410c5aa8b108208639549804104237396cb188211b5cb658c410cb2a7304620845e73d96210422eb9ecb108219a54a6088410ca8c728a420845e73d96400422eb9ecb200211ddd561900108bce7b28800845d73d944004237396ca200211b5cb65100108eae2b28800845e73194400422eb98ca200211b9c865100108dae4328800861e5458c400430eaa2c6200218b9516210010c5aa8b1080086355498440042ab38ea798021475d053cc010a9ae429e600847571596300432b29cc3180219554e618c010aace3a9a600855a70d4d300422f3b0a698021475d0534c010a9ae429a600864f531893004326298c4980210f9d0650c01087ae8328600846e721943004236b90ca1802117dd9530c0108eeeab08600845f73597200422e39acb90021179cf65880108bae7b2c400854c7354a200423bbaac3100210f9d3650801087ae9b28400845e73d94200422eb9eca100211d5c5650801087ce8328400843d74194200422f398ca10021175cc6508010c5ac9290400864d639482004316b22a410021531cd5208010c9ac6a90400866552984200423abb6a9880211d5d853c4010a6ae829e20085657214f100423abb6a588021551cd52c40108eaed28c200865663946100423cbb6a908021965966384010cb2cab1c200847976946100423b3b6a8880211d9d85344010a6ae829a20085657214d100423b3b6a488021551cd5244010aace728220087315490110042b8bac6088021d414d3044010bc0e498220085717508110042d8ba04088021745cc2044010ec2a4102200847a76d5110042e8b9ec2880211e9da5144010e62a920a20085d37350510042b9baa62880215c5d72144010
  | 1 => 0x3144362b106418a21745c0320c5108ecebb2442884f27098e214426b39cc110a219318f5248510c98c6292428847475591214426a39ac890a213c1c16448510ca8cbb1a42884767598d214426b39cc690a213c9c26348510ca8ca31a42886c463d49214423b3b0a490a21b118c5248510d88c7212428856475509214436231a8490a21b418f6048510da6c630242886d06318121442793a8c090a219c9d460485109e2e8302428852d72153404431a2a2c3a0221351cd61d0110ba4e7b0c80885727518640442b83aa8320221cc1514190110ba0e6a0c80884f276cc640442783b243202216cdd12190110ba0e690c808845f73595404422e39acaa02211bdc965501108d8e4b2a808852d72151404423d3b0a8a02216a5c85450110a70eaa1280886706590540442b83aa82a02219c1954150110ba0e6a0a80884f276cc5404433832e62a02219c1943150110b62e818a80884f07648540442e839a42a0221e8509215011087ee8b2a608843c745953044237b92ca982211b1c9654c110c9ea6312608864c5318930443623106298221721c9300c1109a8e6b0e408843f74595204421e3a2ca9022117dcd65481108b8e6b2a408864c63d492044326318a490221aa5912008110b90e690040886b16490710442e839a8388221741cd21c41109ace7b2420884d673d8a104436931ea108221ac5924084110da4c720420886d263502104422fb9ac5aa021171cd62d50108bce7306a80845d73983540423a38ac72a02117dcd61550108b8e6b0aa80843f76550540430eaa2c62a0218b5516215010c3cc8b18a80864e639885404326b1cc42a0218b9916215010c9cc6b10a80864d63588540432b31cc22a0219558e6115010cccc5308a80866562984540432d31cc02a0219658e6015010cd4c5300a808669629805404237394c9298211b5ca6494c108dee4b02a60846c72581530422fbb2a629821875915314c10c9aa6b10a60861d6498c5304317324c4298218b5926214c10c5cc8b10a60862d64588530432731ac4298218d5926114c10ccac5308a608639649805304334b14c0298211b9cb65d0c108dae5b2e860846e721974304236b90cba18211d9c465d0c108f4e032e860862e5458b4304316aa2c5a18211d9c66590c108dce432c860846d72196430423b38ccaa18211ddc56550c108dce432a860846d72195430423aba8c2a18218d9506150c10caca630a8608655531854304278b80c2a18211b9c86510c108dae4328860847671194430423d380ca21821179ce60d48108bae7306a40845e73992520422eb9cc929021935c863548108bee6b0aa40845c73585520422fb9ac0a9021171cd60548108deeca90a40862d645485204326b1aa429021879926314810c3ac9318a40861e6458c520430eb22c6290218b5926214810c9ac7310a4
  | 2 => 0xc5a1a211d1d561d0d108f0eab06868846e72d964344236b96cb21a21475cc5490d10a38e8a9c868854c7254e4344237b92caa1a211b1c96550d108eee2b2a868847471195434422f3b4a6a1a21171d95350d10a38e8a9a868854c7254d434423b3aec2a1a213c9c36150d10caca630a8688655531854344237b92ca21a211b1c96510d108bce6328868846e721944344236b90ca21a21175db5310d108e8eab08868863454584434423c3aac021a218e1516010d108bce7324a48845d73992524422fb9ac329221171cd6194910c5ae4322a48861f64d8d524430e326c6a922187d906354910c38c831aa48862c64d89524432631ec4a92218d1936154910c70c9b02a48846f7654852442963a2a429221531cd521491087ce8300a48843d74180524422f398c029221175cc60149108bce7b2e848845d73d97424422f398cba1221175cc65d0910c9cc7a96848864e6314b424423a3aac3a12211e1d560d09108bce7b2c848845d73d964244296b90a9212214b1d15290910a98e6a948488474755864244278382c32122117dcd65509108b8e6b2a848847771595424423db82caa12211b9da52509108d8eca92848852c7454942442a639aa4a122117dcd65109108b8e6b28848845e73194424422eb98ca212211b9c865109108daeda90848847475584424431a2a2c221221351cd61109108f0eab00848843e74d97324421eba6cb992210f9d3658c91087ae9b2c6488474755863244278382c3192210fdd1654c910878e8b2a648847675d85324423d3aec0992210fdd1650c910878e8b28648843e74194324421eba0ca192211d1d5610c910ca8a6b08648866452584324423c3aac0192219a149600c9108bce732c828845d73996414426b39ccb20a213c9c263905109a8e6b1482884f07058a414426b39cc120a215c9d46090510c3ea831a828861c5418d414429b3aec8a0a214d9d254505108ecec2a2828853676151414431b3b0a8a0a21c59cc5450510e2ae62a28288726721514144392b90a8a0a21cc5c05450510ca8cbb1a828871454d8d414431a2a0c6a0a21951946350510e28a831a82886975418d414432b2a0c6a0a21951506350510d28a831a82886145418d414436831ec0a0a21b4d8c60505108ecebb2662884f270d93314423abb4a998a218dd9054cc510aaae62a662885347454f314438a2a48798a21551d543cc5109e4eb3066288672759833144278ba4c198a21471d1538c510a98e4a9c628845e7614d314422fbb2a618a21471d1530c510a98e4a98628847576150314431ab20a818a21745c2530c5108eeeca9862885347454c314426bbb2a618a21651d1530c510b88e4a9862885d37054c314426abb68618a21719cb430c510ba2e1a1862884d57610c314438a2a08618a21745c0430c5109e0e0b106288555750c8
  | 3 => 0xd663d0a108beeab1e850845f7694f428422ebb4a7a142117dd953d0a108baeca9e850845e73996428422eb9ccb21421179cc6590a108bae632c850845e73995428422eb9ccaa1421179cc6550a108bae632a850865653d85428432b298c2a1421179ce6510a108bae7328850845e73194428422eb98ca214219654e6010a10cb2a6b00850843e74196328421eba0cb19421531c9534ca10cb2a7b02650843e74194328421eba0ca19421535ca530ca10cb4a6b00650845d75d8d418422eba8c6a0c21179da53506108b8eca9a830845d7694c418422fbb2a620c219394e6210610c9aa7310830864e535884184326a9ac420c21c554d4110610cb4a6b00830865953580418432d29ac198c219654f604c6108baebb1a430845d7518d218422f3b4a690c21171d95348610caca730c810865653586408432cb2ca7204219659553902108f4ec2a2810845d7598c408422fbaac620421175da53102108beeca98810864e539884084326a9cc4204218b9516210210c5aa8b10810864e535884084326a9ac4204219594e6110210caaa7308810863554584408432b29ac2204219554d6110210caca730c610865553986308432b29ac3184219394f624c210c9aa7b12610864e531893084326a98c4984219594e610c210caca6b0861085c8724c0308432b29cc3104219594d61882108bced29a410845c7654d208422ebacc61042117dd563082108baed298410861e6494c208430eb24a61042117dd95308210c3cc8a98410861d6454c2084316b24a4104218b5915208210caca7308410865553984208432b29ac2104219554d6108210ccaa4b0841086a96448020842e439a4010421d254d2008210aace7aa621086556594f108432ab2aa788421559cf52c4210cb2cb29e21086596554f1084237b92c7aa2211b1c963d51108bee6b16a88845c7358b544422fb9ac32a221171cd6195110aa8e6b0ca88861f6418d5444327b1ec4aa2219318f6255110c5ec8312a88864f631895444326318c4aa2219518f6155110cc8c5b0aa88866862d81544421fbb2a82a221471cd5415110a58e4aa0a8886577158c544432a38ac62a2219398e6215110c9ac7310a88864e635885444326b1ac42a2219598d6115110caac6b08a888666625845444332b12c22a221179cc61151108bae6308a88846e721845444236b90c22a2219698d6015110cb2c6b00a88866a625805444334b12c02a2219c58560151108bce6300a88845d731805444237390c02a2211b5c860151108dce5324a68846d72992534430eb98c8a9a21871936354d10c5ec9b12a68862c64d895344317b20c4a9a218b1906254d10c9ec6312a68863464d85534422fbb2a629a21471d15314d10a98e4a98a68846e72d974344236b96cba1a211b9c865d0d108dae432e868864f5398b434432629c
  | 4 => 0xd4c4b00a9886696258054c433930ac02a6219a98960d4f10a9ce5a9ca78846e7299253c4236b94c929e21539cb6354f108beeca98a7886726158053c4237396cba1e211b5cb65d0f108dce432e878846d7219743c4237394cb21e211b5ca6590f108dce532a878846d7299543c432b298c2a1e219554c6150f108dce4328878846d7219443c432d31ac1a96219c98560d4b10a9ce7a94a58845e7399252c422eb9cc929621539cf6254b108deeca90a58845e73d9742c422eb9ecba1621179cc65d0b108bae632e858845e73d9642c422eb9ecb21621179ce6590b108bae732c858845e7399542c422eb9ccaa16214b1d15250b109e2e2302858845e7319442c422eb98ca21621351cd6110b1087ce9b2c658843d74d9632c432aa9cc3196210f9d0650cb1087ae832865884d47358a41c426b39cc120e211d9d85450710caeca31a83886565418d41c432a2a0c6a0e218e55160107108eaed2a663885557315331c432d29ac018e218d590540c7108eeeca9863884d576d0c31c42e33968618e21555d4320c710d8ac419063884d67398221c426a39ac890e213c1c164487108ecec29243886c46390921c436231a8490e219a94960087109a8e6b0e81886355418540c4327298c4986219354c624c310d88c418a61884d47358720c432631ca4906219318d5248310cacc6b0ea90845e73d89548422eb9ec4aa4210fdd95415210c5aa8b10a90864e639885484326b1cc42a4218b9916215210c9cc6b10a90864d63588548432b31ac22a4219558d6115210cccc4b08a908665625845484338b0cc02a4211b9ca6494e108dae5324a70854e7215253842a6b90a929c21539ca6494e10a9ae5324a7085577159253842ad380c929c21935886294e10ab4e0314a70851e74182538428eba0c129c21539c86094e10a9ae4304a70845e76d51538422f3b0a8a9c21539c85454e10a9ae42a2a70854e7299153842a6b94c8a9c21569c26454e10aaee2b22a708558705895384326b10c4a9c2147dd16154e10a38e8b0aa70854f7258553842a6392c2a9c2117dd95314e10ce2c3300a70846e72d974384236b96cba1c211b9c865d0e108dae432e870864e5398b4384326a9cc5a1c219394d62d0e10c9aa6b16870865953583438432b29ec2a1c219594c6150e10caaa630a870846e721944384236b90ca21c219694d6010e10cacc6b0ea50867161983528422f39cc929421175ce6494a108baed298a50861e6494c528430eb24a62942117dd95314a10c3cc8a98a50861d6454c5284237bb2a4294218b5915214a10c3cc9318a50861d6498c528430f322c629421875916314a10c5ac9310a50863664584528431ab22c2294219598d6114a10caac6b08a50845e73d97428422eb9ecba1421179ce65d0a108bae732e850845e73197428422eb98cba1421175
  | 5 => 0x63554984400832b29cc2200419554e61100208eeeab08801063654584400831aaa2c2200419594d6110020caaa6b08801047576944400832b31ca2200419558e5110020cccc5288801066562944400823bbb2a2200419598d5110020caac6a888010666625444008332b12a2200419359732cc020e1aa9996601062d5498a3008316aa2c5180419354d628c020a9aea194601070d540ca30082e4b8065180411d5d6618c020c6ca930c601063554986300832b29cc3180419554e618c020d886530c601047775586300831b2a2c3180418d551618c020caca6b0c601065553586300823abb4a3180411ddd9518c020c5ca9b12601062d54d89300832729ec4980419354f624c020c5ca8312601062d541893008327298c4980419354c624c02099ced992601064f65cc93008386aa6649804199d8a514c020cc8c528a6010667625453008332312a2980410f9d2650c02087ae9328601043e74194300821eba0ca180418b552620c020c5aa8b10601064e5358830082a6ba86418041c3550320c020cccc4a886010665625443008316aa4c7900418b55063c8020e1aa929e401070d5454f2008392aa4a390041c955151c8020e8aa6a8e401046d7694a200838caa2a7100411e5da5288020e62a8a8c401075153546200830f2a6c690041875536348020c3ca831a401061d5418d200822f3b4a690041171da53480208bceca9a401045c7654d200832bb1ca2900419518e5148020caec6a8a4010654635452008327b9eca90041931cf65480208dcedaa2401052d759512008317b2ca8900418bd955448020e50e0aa2401064f65d8d2008386aa6c6900411b5d66348020c5aa931a40104ce7398d2008316aa0c69004193d946348020e1aa831a401064f5418d20083472a0c690041935506348020d1aa831a401060d5418d2008364b80c690041331da5348020c9ecb29a401070d5494d20082663b2a69004193d955348020e1aa8a9a4010667659452008392aa4a290041b118e5148020ccecaa8a401072554545200836231aa290041d154d5148020c5aa9b02401064c639412008394aa68090041b218f4048020ad2ea20240105c97310120083643188090041785c44048020e52a918240106c8638c120082f0b8c60900413a1d93048020e52a8982401065b73d95200832c39eca900418ed965448020c76caaa2401065b65d8d200832db28c69004196d965348020cb6caa9a40107195454d200836431ec490041ca5525248020ad2eba1240105c973d0920082753b464900419cd965148020ce6caa8a40107315454520083a8a9aa29004172dcd21480208dce5b1aa98846d72d8d54c422f39ec4aa621175cf625531087eecaa0a9886547158c54c432731cc42a6219358e6215310c9cc6b10a98864d6358854c432d31ac02a6219658d6015310c
  | 6 => 0x10829b3a040a88414d5d02054420aace6102a21055573081510821ebb4a8288410fdd95414420c3ca9318a21061d5498c510830f2a2c6288418755163144208baed298a21061e6494c510830eb24a62884117dd95314420c3cc8a98a21061d6454c510831b2a4c2288418d5526114420caca7308a21065553984510823bbb2a2288418d9915114420c6ac8a88a21065663544510832ab1aa228841179ce65d04208bae732e821045e73996410822eb9ccb2084117dcd65504208b8e6b2a821045e73195410822eb98caa0841175d76350420c3ca9b1a821061d54d8d410822eba8c6a0841879506350420c3aa831a821045e7694d410822e3b4a6a0841179d953504208b8eca9a821062d54d894108316aa0c4a084195d8e5150420ca8c728a821065763545410832a31aa2a084199d895150420c72a9b02821067151d81410822f39eca20841175cf65104208bce7328821045d73994410822ebacc620841879526310420c3aa9318821045f7558c410830f2a2c6208418755163104208beed298821045d7694c410822fbb2a620841175d95310420c5aa9310821064e539884108326a9cc4208418b9516210420c5aa8b10821064e535884108326a9ac4208419598e5110420caac72888210666629444108332b14a2208419598d5110420caac6a888210666625444108332b12a2208418e5526010420cb4a73008210659539804108338a8cc0208418e9516010420c72a8b00821065a53580410832ca9ac0208419c9456010420ce2a2b00821043e74997310821eba4cb988410f9d2658c42087ae932c621062d5498a3108326a9cc5188418b551628c420c9aa6b14621054d750ca3108386aa06518841725c0328c420ccac528c621063954982310832ca9cc118841b20ca608c420c72a8b04621065953582310833928ac1188410f9d0654c42087ae832a621062d54d893108326a9ec4988418b550624c4209d2e0312621066762545310821f3a4ca188410f5d2650c420a9aea190621064d650c83108386aa06418841725c0320c420ce2a2b06421061e54d8d210830eaa6c690841879506348420c3aa831a421045e7694d210822e3b4a690841179d953484208b8eca9a421065763945210832a31ca2908418e5526008420cb2a7300421063954580210832ca9ac0108419c9456008420c5aa9314801046f7558a4008316aa2c520041331cd62900208bce7b28801045d73d94400822f39cca20041175ce65100208bce6328801045d73194400822ebacc620041879526310020c3aa9318801045f7558c400830f2a2c6200418755163100208beed298801045d7694c400822fbb2a620041175d95310020c5aa9310801064e539884008326a9cc4200418b9516210020c5aa8b10801064e535884008326a9ac4200411d5d66110020c6ca9308801
  | 7 => 0x2a18419594c6150c20caaa630a861063954d81430832ca9ec0a18411e5d46050c208ece33288610475719944308237390ca218411d9c46510c208eae2328861047a70194430822f39cc929041175ce6494820c3ca931e841061d5498f420830f2a2c7a10418755163d08208beed29e841045d7694f420822fbb2a7a1041175d953d0820c72a8b04841065953980420831d2a2c0210419654d6010820a9ae7aa6641062d655533208296ba6a7990419359653cc820e1aa929e641070e5454f3208386aa2a7990418b55160cc820cb2a6b04641064d654c83208386aa264190418e552600c820c72a8b00641065a535803208364992c0190411b5db540c820a5aeb2a0641070e735503208386b9aa8190418b552630c820c9acb318641070d5498c3208296ba6a619041c3552530c8208deeca98641064e6354c3208386aa2a61904193596430c820e1aa9218641064d6550c3208386aa28619041711c5430c820b90e0a186410729549803208237baac0190418b551600c820e52a8b0064104eb755803208335baac0190419ad51600c820d54a8b006410669545803208354aa2c0190418a551600c820d94a6b0064106c953580320836521ac019041b250d600c820c3ca931ea21061d5498f510830f2a2c7a88418755163d4420c3cc929ea21061d6494f510830f322a7a88418759153d4420a6ce9a8ca21053574d4651082ab39ea328841555cf51944208bee6b24a21045c7359251082ab39ea928841555cf5494420aace62a4a21055573152510829b3a6a7288414d5d35394420e2ca929ca2107155494e510838b2a2a728841c55515394420e88e4a9ca2105367414e510829aba0a728841c95533294420e8aa7994a210725540ca51082f0b80652884155dcd6494420aa8e6b24a2105567319251082aab98c928841599c86494420ae4e0324a21056672d8e51082b9386c728841599cb4394420acae5a1ca2104777650e510823a3b28728841559cf4294420aaae7a14a2105567398251082aab9cc128841179cc64544208bae6322a21047676d5151082ab39ea8a8841555cf54544208ecec2a2a2105567315151082aab98a8a88411d9db5354420a6ce9a9aa21053574d4d510838b2a4a6a8841c55525354420e2ca8a9aa2107155454d51083a2392a6a88411d9d85354420a6ce829aa2105357414d51082b2bae64a8841c95533254420e8aa7992a210725540c951083a2a9864a8841785c03254420aaee6b22a2105547359151082b2392c8a88415c1c16454420aace6322a2105557319151082b3390c8a88415c9c06454420ac8e4b1aa21056672d0d51082b2b9686a88411ddd943544208e8eca1aa21055673d0951082aab9e84a88415c9c04254420ae2e0212a210745320c951082b938064a88415c5c03254420aace7302a210555739815
  | 8 => 0x86195020a74e030ca81051e73182540828eb98c12a0414d9c46095020a6ae2304a81051e73d91540828eb9ec8aa0414d9c76455020a6ae3b22a81045e73d89540822eb9ec4aa041179cc61550208bae630aa81052e72d8d5408296392c6aa0414ddc56355020a68e2b1aa8105387058d540828fb9ac2aa041471cd6155020a58e4b0aa81053870585540828f398c2aa041475cc6155020a5ce430aa81053a70185540828f398c0aa041475cc6055020a6ce2302a81053571181540821fbb2a82a041875526315020c3aa8b18a81063554984540831aaa2c22a041879926315020c3cc8b18a81064e639885408326b1cc42a0418d9926115020cacc7308a810655639845408333314c22a0418d9916115020cacc6b08a810655635845408333312c22a0419658e6015020ce2c3300a81063654987530831aaa4c3a98418d95161d4c20c6aa8b0ea61062d6498b530831b324c3a98418d59261d4c20c6cc8b0ea61063564587530828f3a6a729841475d35394c20aace3a9ca61055571d4e5308237394c9298411ddc56494c208e8e2b24a61055671d5253082aab8ea929841559c45494c20aaae22a4a61070d5418a53082a7394c92984155dc56494c20aa8e2b24a6105567198253082aab8cc129841479d36354c20a3ae9b1aa61055671d8d53082aab8ec6a9841179db5454c20aace3aa2a61055571d51530822f3b0a8a9841559c45454c20aaae22a2a61070e541895308386aa0c4a9841539ca6454c20a98e4b22a6105577159153082aa38ac8a9841561c16454c20c9ec8312a61064d6418953082a7394c2a98419318a6154c20ab4e130aa61054c725855308326310c2a98419318a6054c20aace3302a610555719815308326310c0a9841479d02054c20a3ae8102a61043d76950530821fbb2a829841879526314c20c3aa9318a61045f7654c530830f322a629841875915314c20c6ca9308a61063554984530832aa9cc2298418d9516114c20c6aa8b08a61065553584530830f324c629841875926314c20c5ac9310a61063664984530831ab24c2298419598e6114c20c6cc8b08a61063564584530832b31ac229841999896114c20c72c9300a61067161980530823b38ccba18411d5c665d0c208dae4b2e861046e72197430823b388cba18411d5c465d0c208daeb316861062d5498b430832729cc5a18419354e62d0c209d2e1316861062e5458b4308316aa2c5a18419394d62d0c20c9aa6b16861047671996430823ab8ccb218411d9c46590c208eae232c861047671995430823ab8ccaa18411ddc56550c208e8e2b2a861047671195430823ab88caa18418b5536250c20c9aa7b12861046d751894308316aa0c4a18411d5d76150c20c6ca9b0a861063554d85430832b29ec2a18419554f6150c208eaea30a861063654185430831aaa0c
  | 9 => 0x8a630a869047671194434823ab88ca21a419314e6210d208d8eab10869064c53588434832c29cc021a411e1d56010d208bceb31e849045c7558f424822fbb6a7a1241175db53d09208beec29e849045d7614f42482a739ca921241939945390920c98a7304849065853d81424832c298c0a1241539ce54509208dcec2a2849070c54d4d42482373b4a6a12414b9d25350920a9ce729a849070f5414d4248387b20a6a1241d214f6050920c98a630284907485318142482753a8c0a12419a9d46050920d94e630284906c9731814248365a98c0a12419a94c6050920cd0a630284906c8531814248324298c0a1241b89c46050920dc2e2302849064c539884248387a9a84212419614e60cc920cb6a6302649045e73993514822eb9cc9a8a41179db5354520c3ec9a9aa29061c64d4d514822f3b0a6a8a4187d905354520c38c829aa29047776544514829a3a2a228a4117dcd64145208b8e6b20a29045f73597414822e39acba0a419314e62d0520c98a6b1682904e87058b414822fb9acb20a41171cd65905208bce7b2a829045d73d95414822f39ccaa0a41175ce65505208bcebb1a829045e7518d414822f3b6a6a0a41171db53505208bcec29a829045c7614d414822fb9aca20a41171cd65105208bce6328829045d73194414822f3acc620a41171d563105208beeda98829045d76d4c414822fbb0a620a41175d85310520c9ea7310829064c539884148317aa2c420a4193d4d6210520c98a6b10829066562d44414832da9cc020a419614e6010520c76a8b00829065b53580414832c29ac020a419cd456010520ce0a2b00829055671d4d314821f3a0ca18a410f5d0650c520aaae2298629064c53988314832629ac418a419614e600c520cb0a6b00629065853982214832c29ac110a41179d763485208bcea31a429045e76d4d214822f3b0a690a419314e62d0120c98a6b16809052c7550b404838629a85a02416a1c142d01208bce7b2a809045d73d95404822fb9acaa0241171cd6550120c98a7b12809064c5318940482963aa84a0241c314d42501208beeda98809045d76d4c404822fbb0a620241175d85310120c9ea7310809064c539884048327a9ac4202419314d6210120caea7308809065453984404832ba9ac2202419514d6110120c98a7316609064c5358b304832ba9cc3182419514e618c120caea6b0c609065453586304832629ec49824193d4c624c120c98a6312609064f6414e2048326b20a710241931c963d5020cacc730ea81065563987540832b31ac3aa0419558d61d5020a3ce7aa4a81051d73d52540829b38ea92a0414d5c754950208eee2b1ca8104747158e540822fb9ac32a041171cd6195020a5ce5b1ca8105377158e540829a38ac72a04147dcd6195020a38e6b0ca81051e73186540828eb98c32a0414b9c
  | 10 => 0x46e7615142c82573b0a8a16414b9d25350b2087eecaa085906a94258042c822f3b0a69964117dd9530cb20c98c7212a39062c6450951c832631a84a8e411ddd951147208bce7b2e839045d73d9741c822fb9acb20e41171cd65907208bee6b2a839045c7359541c822f39eca20e41175cf6510720cb6a730463905557114c31c832629ac418e4195d4e618c320ca8a730c619045e7694d30c8327298c4986419354c624c3208baeda98619054c7358b5488334b14c1aa4411ddc563952208e8e2b1ca91045f73586548822e39ac32a4410fdd95415220c9cc6b10a91064d63588548832b31cc22a4419558e6115220ccac5308a91065663584548832ab1ac22a441995896115220ce2c3300a9106716198353882ab38ea729c41559c76354e208beeca98a71066962980538823b388cba1c411d5c465d0e208ece332c871047571996438823b38ccaa1c411d5c66550e208eee2b2a871047471595438832b298c2a1c419554c6150e208ece232887104757119443882ab38ea719441179da534ca208baeda98651055671d4c3288236bb6a619441335db530ca20b8ce3a9865105ca70d4c32882e5380a619441711c5430ca20aace7a8ca31045e73191518822eb98c8a8c411ddd951146208bce732c831045d73996418822fb9acaa0c41171cd6550620ca8c728a831053474545418832a31aa2a0c41179cf65106208bae7b28831043f74595318821e3a2ca98c4193994320c620d9065300631065463945218832a31aa290c41331cd629022087cec2a2811043f7655040883172a2c4204418b5516210220aace3a9e611065653986308832aa9cc318441b10ca618c220aace3a9a611045e7614d3088326298c498441339db324c2208beeca9861104cc735972088237b92c7aa241179ce61d51208bae730ea89064e6358a544832631ec4aa24195d8f6155120ca8c7b0aa89063764185544832bb18c2aa2419518c6155120ccec430aa89065863d81544833830ec0aa2410fdd95415120a68e2aa0a89045f73584544822e39ac22a24155dc554d4d20aa8e2aa6a69055671d9353482aab8ec9a9a41535c864d4d20aace3b16a69055571d8b534832bb0cc3a9a4117dd95314d208eee2b20a69047471590534822ebb4a829a4117dd95414d20aaee2aa0a6905547155053482a6b94c829a4155dc56414d20aa8e2b20a69054d7219053482ab388c829a41555c46414d20ab2e0320a69051e74184534828eba0c229a41535c86114d20caac2308a690559701845348236b96cba1a411b9c865d0d20c9ea7316869064c5398b43482363aac5a1a419314d62d0d209d0e0b16869047671d96434823ab8ecb21a411d9c66550d208eae332a869046f72595434823bb8acaa1a411d1c56550d208f6e0b2a869065753d85434832a29ec2a1a4195d4c6150d20ca
  | 11 => 0x4c327b20a418a6193590520c530e8ce2290629874571148314c3a2294c218a61d114a510c530ba2e128862984d776544314c2ca3a2a218a61d1d49510c530ba6e0a88629874452d04314c26abb08218a61a5590410c530e28a8208629874452104314c2e8b808218a619314a600c530c9cc6296429864d6314b214c26d386c710a61179d46388530c9ec6294429864c6314a214c32631ea490a6193d8c5248530c98c6292429843e74194214c21eba0ca10a619398c5208530c9ac6290429866852980214c334292c010a61351c563d0130c9cc6296809864d6314b404c327b18a4a02619318c52501308deeda90809846d76d48404c32731ea4202619358f52101308deec290809846d76148404c327318a4202619358c5210130ccea5308809866452984404c333a92c220261991496110130d52c4a0080985d07150f304c333a94c3182619914a618c130ccea4b0c609866452586304c26b38ec91826193588528c130c9aec294609864f6414a304c326b20a5182619314a618c130e88a530c60986c752986304c32a294c318261b114a618c130c88a530c609874452586304c36930ea1182611b9c861550308dae430aa81843f76550540c316aa2c42a0618d5516115030c9cc7310a81862e64588540c32731ac42a0619598e6115030cccc5308a81866562984540c31b322c22a0619598d6115030cccc4b08a81866562584540c334b14c02a0619c5866015030c72a9304861865653185430c237bb2a4290618b5915214830ccaa4b08a41861d5498f420c23bb8acaa10611d1c565508308ece232a841847571195420c22ebaec6a10618e5506050830cd2a4302841845d76d52320c386aa28419061721c1420c8308dce4322a21846d72191510c23bbb2a2288618d5915114430ccac4a88a21846e72195410c236b90caa0861879506350430ca8c728a821865463545410c237396ca208611b5cb65104308beeab1c421843e74195210c21eba0ca908619318e5248430ca8c728a421865463545210c22ebb0652806117dd56390030998e4b1c801861d5498c400c3172a2c4200618b5516210030c6ca8b08801863554584400c22fbb2a5980619398952cc0308baed29c60184797694e300c22f3b6a89806193d97624c030c9eca312601864d75189300c327aa0c49806193550624c030c98c4a92601864c62945300c2e8b8ec6980619ad97624c030cd6ca31260186cb63189300c2adbaa62980619a98960d5320c9cc7314a99064d6398a54c821fbb2a82a64117dcd61153208b8e6b08a99045f7654c53c8335312c029e411d9c66550f208eae332a87904777159543c823a38acaa1e41479d35350f20caea630a87906545318543c823b388ca21e411d5c46510f20a9ce72a4859043e7615142c82a739ecaa16416a5c35450b20a9ce72a28590
  | 12 => 0xa9261719c763d4930e18a8a1ea4985c47150f524c317b24c9a9261535cc64d4930acce3b1ea49856571d8f524c236bb687a926159dc543d4930ac8e2a1ea49854d73d87524c237bb2a429261535ca4314930a9ee4a18a4985547150c524c236bb4a8292611bdd95414930acee2aa0a49856471550524c2a73ac8629261c3d514314930b88e2a18a49854d73d90524c2a6b9cc8292618b5906414930a9ae6320a49856671190524c2b2b88c8292615a5c06414930a5ce9b18a49852d74d8c524c2b338ec629261595c763149308daeda18a49854d7690c524c3873248629261c35924314930a9ce3218a49854e7090c524c2b3b8a8629261591c54314930ad6e0a18a4985687050c524c2a7bb28629261c3dd14314930e8ee2a18a49854c7150c524c3a238a8629261511c54314930e96e0a18a49854c7050c524c3a43828629261535cf6114930a9ee6b08a49852e74184524c296ba0c229261535cc6114930ad2e0308a49864e63d4b424c327318a5a12619358c52d0930c9cc6294849864d6314a424c2973a6a4a12611d9c465109308eae2328849852d74148424c327318a4212619358c5210930cd0a5300849864f72997324c22f3aec9992619399752cc930c9ec8296649864d6414b324c32732c8599261531d542cc930c9ccaa16649864c52987324c26d384c3992619314a60cc9309ace3306649866852982324c335a90c099261351c5644c9309b0e0b22649854e75d89324c2a73b0a499261939d8524c930c9ec8292649864d64149324c326290c2992611b9ca64d45308dae5326a29845f7650f514c2aa38a87a8a611b9db5254530c5ec9a92a29862c64d49514c2373b0a4a8a618bd905254530c58c8292a29847776544514c29a3a2a228a611bdc965d05308d8e4b2e829864e6314b414c326b18a5a0a611bdc965905308d8e4b2c829846e72d95414c236b96caa0a6193d8f5250530c98c7a92829864f63149414c326318a4a0a611bdc965105308d8e4b28829846e72194414c236b90ca20a6187d5163105308dceb310829846c75588414c237bb6a420a611b5db5210530c9cc7a90829864d63d48414c237bb0a420a611b5d85210530c9cc6290829864d63148414c32ab1ea220a619ad4a6010530cd0a5300829863b54580414c335a92c020a619a1496010530ce6a2b00829867051580414c334294c118a619a149608c5309b4e1b24629854e72952314c22ebb0a918a61171d5628c530c9ac4294629864d7614a314c327b20a518a6193590528c530e88a428c629864c52982314c3a4294c118a61369d6608c530cb4eb30462986cb52982314c32c294c118a61b214a608c530c90a5304629874852582314c3a3a926218a61175da540c530a9ce52a0629845d76150314c326b10a418a61555c4520c530c9cca290629864d7614831
  | 13 => 0x540ca30aace3aa065184cd76d48328c2e5386a419461635d0520ca30b94e0290651870d54508328c326b106528c61599c85494630acae42a4a3185367414a518c29aba0a528c61d194a3294630aaaea194a318744520ca518c2abb9ac928c618d5906494630aaae6324a31856672192518c2b2b90c928c615c9c06494630acce5b1ca31856572d8e518c2b33968728c61595cb43946308eeeca1ca31855573d8a518c2abb9ac528c615c9c06294630aace7a14a31855573d0a518c2abb9a8528c61551cd4294630aaae1194a318746720ca518c3a33106528c61d15883294630e8c84194a318745420ca518c2aab806528c614d9d06094630a6ae8304a31856672182518c2b2b90c128c611b9c864546308dae4322a31847676d51518c23b3b0a8a8c61599c85454630acae42a2a31847676d49518c23b3b0a4a8c614d9d05254630a6ae8292a318555750c9518c3a3a9064a8c6155dcd6454630c6ac8322a31855573191518c2b3390c8a8c61595c86454630ae4e0322a3185377458d518c29a3a2c6a8c6159dc96354630ac8e4b1aa31856672d0d518c2b2b9686a8c615c9c34354630ae2e1a1aa3184747650d518c2abb9ac4a8c61559cf4254630aaae7a12a31857270109518c2b8b8084a8c615cdc13254630ae0e0992a318745320c9518c23bbb2a228c6195d8e5150630ca8c728a831853474545418c32a31aa2a0c611b9cb65106308dae5b28831853574944418c32b31ca220c619558e5110630cccc5288831866562944418c32b31aa220c619558d5110630cccc4a88831866562544418c338a8cc020c619c9456010630ce2a2b00831867251582318c338a8ec098c619598e5188630caac728c431865763945218c32a31ca290c619518d5148630ce4a2b0043184cc7258e408c32b31ca3204619558e5190230c3aa8b18811862e54588408c316aa2c4204611d5d661102308eeeab08811847576944408c32b31ca2204619558e5110230cccc5288811866562944408c23bbb2a2204619598d5110230caac6a88811866662544408c332b12a220461aa5894010230aace3aa6611864e6254b308c32ab2ca3984619598a51cc230caacaa8e611867165947308c338b2aa3984611b9ca61d51308dae530ea8985547158e544c326b1cc52a26193d8c6255130ccec5b0aa89866462d85544c31bb20c2aa26195d8c6155130ccec430aa89866462185544c334316c0aa2610fdd95415130a68e2aa0a89846e7598b434c2363aac5a1a61539ca5490d309b4e130c86984d671982434c31baa0c2a1a618d1506150d30a9ce52a2869845e76151434c22f3aec4a1a61951976150d30ca8ca30a869865675185434c32aba8c2a1a61a5d506150d30caca830a869865454185434c34a2a0c2a1a61b41876050d30da6c2302869856771553524c2b238aa9
  | 14 => 0xa73008220659539804110335294c0208819a54a6010440ce2a3300822065a53580411032ca9ac0208819a9496010440cd2a4b008220672515804110237394cb988811b5ca65cc4408dce532c622046d729963110237390ca988811b5c8654c440c3ec8a9a622062f645493110316322a4988818dd91514c4408dce5328622046d72994311022f39ccb90881175ce65c84408bce732c422045d73996211022fb9aca90881171cd65484408bce632a422045d73195211022ebaec690881175d463484408bced29a422045c7694d211022f3b2a690881171d95348440c9ec7292422064c639492110317b22a4908818b1915248440c9ec6a92422064c63549211032bb1ca2908819518e5148440c6ec8a8a422065763545211032a31aa2908819a54b6048440ce2a3b02422067151181211022f39cca10881175ce6508440e1ca6a96802070d5354b4010392a94a3a0081c554d51d0040e4aa4a8e802043d76952401023cbb4a920081d254d5290040ea4a6a8c80207515354640103b1292a320081d85495190040c3ecb29a802061f6554d4010317b2ca4a00818bd955250040e1ca6a92802070d53549401031bb2ca2a0081c954a5150040c6ecaa8a8020715535454010392a92a2a008196d965350040cb6caa9a802066b659494010335b2aa4a0081ca9515250040e92a6a928020673659454010339b2aa2a0081d494d5150040ea2a6a8a80207625254540103b0a92a2a0081ccd915150040e6686a8a802073143545401032731cc52a6619398d629533087eecaa0a99854e7295243cc22fbaac521e61359c66090f30a9ce52a2879845e7615143cc32bb28c2a1e61955d46150f30caca830a87986545418543cc369380c2a1e61b45c06150f30c74a8b00879861e6450e52cc2aa38a87296611bdd95214b308ece3b2c859847571d9642cc26cb98c0a1661721c142ccb309ace330665984d47159132cc26c382c899661179da4354730aa8e2a1aa3984777654451cc237396cba0e611b5cb65d07308dce5b28839846d72d9441cc22ebb4a918e61539ca548c7308baec2a4639845d7695031cc2a7394a818e6117dd5620c730d2ac820863985d17010431cc21f3a6cb90e610f5d365c87309b4e1b1c43984d97398221cc296b94a9a0661351c563d0330a5ae52a2819854c7258f548c32ab1cc3aa4610fdd95415230c5aa8b10a91864d63988548c317322c42a4619358d6215230caac7308a91866662984548c332b14c22a4619558d6115230cccc4b08a91866562584548c338b0cc02a4618b95162d0e30c5aa8b16871847575d85438c23aba8c2a1c611bdd95214a30c5ac8a90a51847671997428c23ab8ccba14618755163d0a308ece332c851847571996428c23b388caa14611d5c46550a308ece3328851847571994428c2ab38ea919461175db
  | 15 => 0x4d63548521032b29cc2290819554e6114840ccaa5308a42065653584521032aa9ac2290819954961148408baeb31e842045f7558f421022ebb4a7a108117dd953d0840c9cc7296842064d6394b421032731aa5a10819358d52d0840cd2a4b06842065953980421032ca9ac0210819a94960108408ece332e642047571997321023b38ccb190811d5c6658c8408ece232a642047571195321032ca9ec0990819a54b604c8408ece3328642047571994321032729cc5a88819354e62d4440c9ca6b16a22064d5358b511032731ca5a88819358e52d4440c9cc6a96a22064d6354b51102ab39ea328881555cf5194440acce5a8ca22056572d46511022fb9ac528881171cd6294440acce5a9ca22056572d4e51102b3390a728881595c85394440aace7a94a22055573d4a51103a329ca528881d154e5294440e8ca6a94a2207455354a51102ab398a528881555cc5294440aace6324a2205557319251102b3390c928881595c86494440acce5a1ca22056572d0e511023a3b2872888155dcd6294440aa8e6b14a22055673d0a51102aab9e8528881559ce6094440aaae7304a22047676d4d51102b3396a6a8881595cb53544408ecec29aa2205667214d51102b2b90a6a88811d9db5254440aace7a92a22055573d4951103a329ca4a8881d154e5254440e8ca6a92a22074553549511023b3b0a4a8881559cc5254440aaae6292a2205347458d51102b339686a8881595cb4354440ae4e1a1aa22057170d0d511023bbb286a88815c9c04354440ae2e021aa2205347458951102abb9ac4a8881551cd6254440ae0e0b12a22055673d0951102aab9e84a88815c9c34254440ae2e1a12a2205727010951102b8b8084a88815cdc13254440ae0e0992a2205567398151102aab9cc0a8881559cc4054440aaae6202a2205667210151102b2b9080a8881175da53144408beeca98a22064e539885110326a9cc4288819394d6214440c9aa6b10a22046d76948511032731ca4288819358e52144408deeca90a22064e635485110326b1aa4288819594e6114440caaa7308a220666529845110332a94c2288811ddd95114440cacc6a88a220655635445110333312a228881995895114440ce2a2b06822045c7694d411022f3b2a6a088193d8e5250440c98c7292822064f63549411032631aa4a088195d8e5150440ca8c728a822045d7598c411022fbaac620881175da53104408beeca98822046d75988411032729cc4208819354e62104408deeab10822064e535884110326a9ac4208811b5da5210440c9cc7290822064d639484110237bb2a4208819398d5210440c9ac6a90822065663944411032ab1ca2208819998a5110440ccac5288822065663544411032ab1aa220881999895110440ccac4a88822059473504411038aa9a8220881c95494110440cb4
  | 16 => 0x2ab38ea729c8117dd95314e40a98e4a98a72054c7254e4390278b8cc121c81531c95350e40caca630a872065553185439022fb9ac329481171cd6194a408deeca90a52054c7354852902a639aa521481531cd5250a409e2e2302852047671997329023ab8ccb99481531c953cca40a98e4a9a652055673d46519023bbb2a228c819518e5150640ca8c6a8a8320594735044190358a0ac020c811b9cb658c6408dae5b2c632054c7254e319032ca9cc118c811bdc9654c6408d8e4b2a632054c7254c319022f39ecb10c81175cf65886408bce732c432045d73996219022fb9aca90c81171cd6548640ca8c728a432065463545219022fbb2a629a81531c95314d40aa8e2a98a6a04f171982435032ba98c2a1a819514c6150d408deeca90a4a054c7354852502b238aa42928117dcd61149408b8e6b08a4a04f17118142502c739ec4a12816c5c46050940c5ccaa1664a047771594325023a38aca192811d9c4650c9408eae232864a061d6414c3250316b20a4192819a149600c940d5284b0064a04777654451502aa39aa228a81591c951145408bee6b10a2a045c73588515032a31ea2a0a819518c51505408dee4b2862a046c725943150237390ca18a811b5c8650c540c6ac828862a065853580315033828ac018a81179ce65485408bae732a42a062c65509215034631a8490a8117dcd65085408b8e6b2842a045e73194215022eb98ca10a818d5905108540cd0a4b0042a054e72d4e53102a6b96a729881559c75394c40aaae3a9ca6205567198253102aab8cc129881539ca6454c40a9ae5322a62055870589531028e3a2c2a9881559c66054c40aaae3302a62045f7654c5310326a9cc4298819354d6214c40caaa7308a620655535845310236bacc5a18819394e62d0c40c9aa7316862046f7558b431032729ac5a18819354d62d0c40cb2a6b06862065653d85431032b298c2a18819694d6010c40caca730ea42065553987521032b29ac3a90819554d61d4840a9ce7a94a42054d73d4a52102b338ea529081595c752948408bee6b0ca42045c7358652102b338ea729081595c75394840acce229ca4205657114e5210236bb6872908159dc54394840ac8e2a1ca42054f7358652102a639ac329081539cc6094840a9ae6304a4205667118252102b2b88c1290811b9db5354840acce3a9aa42056571d4d52102373b0a6a9081599c45354840acae229aa42054e7399152102a6b9cc8a90815a1c163548408dceda1aa4205677150d52102b238a86a90815a9c04354840ad2e021aa42052c7458552102a7b9ac2a9081531cd6154840ad0e0b0aa42054e7318152102a6b98c0a9081599c46054840acae2302a42054e7310152102a6b9880a9081175da53148408beeca98a42064e539885210326a9cc4290811bdd95214840c9cc6a90a4206
  | 17 => 0xa438b15162d0521c98a6b168290c5e73d95414862eb9ecaa0a4317dcd65505218b8e6b2a8290c5e75d8d414862f3a8c6a0a43179db53505218b8eda9a8290c5e7614d414862e3b0a6a0a4317ddb53105218baeda988290c5f7614c414862ebb0a620a4393d4e6210521c98a73108290e4f53588414872629ac420a43c5d4d4110521cb6a73008290e5853980414872da9ac020a439614d6010521c98a73166290e4f5318931486aa3aa6218a43179ce64d41218bae7326a090c5e76d4d504870fb26a6a82438719353541218bcec29aa090e1f6414d504870e320a6a82431edd95014121a70e8a80a090c5e73181540862eb98c0aa0430fdd95415021c3aa8b18a810e3954580540870f322c62a0439398e6215021c9ac7310a810e5563984540872d31cc02a0439658e6015021cd4c5300a810e3a64580540872d31ac02a0439658d6015021cd4c4b00a810e72615805408637394c92984317dd95314c21c3ac8a98a610e5953580530870eb24c6298438b5926214c21c6ac9308a610e3a64980530871cb24c0298438e9916014c21c72c8b00a610e5a635805308735312c0298439c9856014c218dce432e8610c7a70197430863cb80cba18431b5d662d0c21c5aa93168610c7a70196430863cb80cb218431d9c66550c218f4e032a8610c7970195430863aba8c2a18438d9506150c21c6aa830a8610e5653185430872aa98c2a18431b9c86510c218ece23288610c7a70194430863cb80ca21843179ce64948218bae7324a410c5e73d96420862eb9ecb210438d552619082187ce9b2c6410c3d74d96320872aa9cc3190431bdd562904218bce7b288210c5d73d94410862f398ca20843175cc6510421c3ca8b188210e1d5458c4108716aa4c4208438e9516010421c72a8b008210e4d5398a310861f3a0ca188430f5d0650c4218daed2944210c757694a21086373b6a89084393d976348421c9eca31a4210e5765d8d210872bb28c690843179cc64540218bae6322a010c7b76540500871cb22a0280439658d5014021a9ce5a9ca7a045f7654c53d02aa38aa629e81551c553d0f40c9ca731687a064d5398b43d02aa38aa621e81539cf5294b408deeca90a5a064e6394b42d032731aa5a1681639cf6250b40b1ce7a9285a05a970d4942d02573b0a4a1681aa5096010b40c5ccaa1665a047671d9632d023ab8ecb1968187991538cb40aa8e2a9c65a04777159532d023a38aca99681551c5530cb408bee6b14a3a045c7358a51d023bbb2a228e81551cd5114740aa8e6a8e83a05547354441d0338a8ac020e811b9ca65cc7408dae532e63a05547154f31d02aa38aa698e81179cf65c87408bae7b2e43a045e7399721d022eb9ccb90e8117dcd65487408b8e6b2a43a064c6394921d032631aa490e818b1954248740d18c6a1243a06a942d8121d
  | 18 => 0x553218bae6302a990c3f7655054c870eb9cc9a9e438b59262d4f21c6cc8b0ea790d1e74d4e53c868f3a6c6a9e4317dd95314f21cccc4b08a790e4e5398b43c8726a9cc5a1e43475ce5490f21a3ce9a9c8790d1e74d4d43c862f3b0a6a1e4395d4c6150f21ca8a630a8790c7a7019443c863cb80ca21e4317dd95310f21a9ce72a48590d4e7395142c86373b0a8a16434b9d25350b21c6ca8b088590e565358432c870f2a0c6a0e43875506350721c5aa83128390d1e74d4e31c862f3b4a698e43175db530c721a3ce9a986390c7b7654050c862f39cc1aa443175ce60d522187eecaa0a910e4e635885488726b1ac42a4439698e6015221cb2c7300a910e6962980548872d31ac02a4439658d6015221cd2c4b00a910e72615805488734b14c1a9c439c98560d4e21ab4e1a9ca710d5a70d8d538862fbb2a629c439958a6114e218f4e032e8710c7970197438863d384cb21c431e5c26590e218f4e132a8710c7970995438872b298c2a1c439554c6150e218f4e03288710c797019443886ad386a719443179da534ca218baeda986510d5a70d4c3288716aa2c420c439394d620c621ab4e7a84a110e4f7258e5088726392c728443961c163942218bce6322a110c5d73191508863dbb2a028443179ce60d51218bae7306a890e4e6358a544872a31ec2aa24396d8f6055121cb0c7b02a890e3b64181544872db18c0aa2439618c6055121cd6c4302a890e73611815448738b88c0aa2430fdd95415121a70e0aa0a890d5b7055353486ac382a9a9a43555c764d4d21a9ae4326a690d5a70d8b53486acb86c5a9a43479d361d4d21a3ae9b0ea690d4d72d8353486aab88c1a9a4317dd95314d218baed2a0a690c5f7655053486adb82a829a43561c15414d21a9ae5320a690d577159053486a6b90c829a43555c46414d21ab4e0320a690d597019053486aab8cc029a4353dc96014d21a3ce8300a690d1d7418053486a6b90c029a43555c46014d218dae5b2e8690e4f5398b434872629cc5a1a431b1d562d0d21c98a6b168690c7a70d96434863cb86cb21a431ddc56550d218f6e0b2a8690c7870595434863b3aec2a1a439514f6150d21caea630a8690e5453185434863d380ca21a431e5c06510d21c98a73108690c6c75588434872629ac421a439514e6110d218e8eab088690c5e7598f424862e3aac7a124317ddb53d09218baeda9e8490c5f7614f424862ebb0a7a1243539ce5490921ca8a7b0a8490e545318542486973aec8a12434b9d25450921a9ce72a28490c6e7615142486973b0a8a12438b9d85450921a5ae02a28490f0c54d4d42486373b4a6a12434b9d25350921a9ce729a8490f0f5414d42487862a0a6a1243c3d905350921e88a7b0a8490f4453185424872629cc4212439514e61cc921caea630a6490d4c754c8324872629cc5a
  | 19 => 0x8b00a818e5a63580540c735312c02a0639a5896015031ce4c2b00a818e5471597430c66ab8cc5a18639359662d0c31c9ea93168618e4d5498b430c76338cc5a1863b15c662d0c31c9acab168618d5575d87430c72ab2ec3a1863b158b61d0c31d8cc430e8618dd170187430c71aaa4c32186317dd95410c318beeab088618c3e74181520c61eba0c0a90631bdd95214831c5ac8a90a418e6952580520c70eaa4c7a1063355c663d08318f6e0b2a8418c7870595420c63d380caa10631e5c06550831c98c6a928418e3554185420c732a90c2a1063175d4648c8318beecaa46418e1e64552320c62ebacc819063355c4640c8319b2e03206418d4d72d50320c70f322a819063535d6620c831a9eeca906418e4f76548320c6a7ba2a419063531c1520c83199aed2106418d4d75908320c6a6baa8419063c3551420c8319aeeab086418e5775584320c66a3a2c21906395d51610c831caaa8b086418ec642584320c762a12c21906335dc1610c831c9aa4b006418d4e72d0e510c62ebb08728863555d763d0431b8ce5b1e8218d5575d0f410c6e339687a0863555d443d04319acec1968218d96740cb410c62fbaac720863875526310431c5ca8b108218e2d54588410c71d2a2c0208638e5516010431a6aeb3208218d3575950410c63bbb2a8208634ddd95410431c6eecaa08218f1473550410c72ab2cc620863c555263104318eeeab188218e556558c410c78aaa2c6208639558e5310431aaaeba188218e5565d0c410c78aaa68620863719cb4310431aaaea2188218e556510c410c732b2cc420863c95526210431ccacab108218f2554588410c762b1ac420863955963210431b2ce91908218f15548c8410c66abb06420863955943210431e2aa81908218e7165980410c798aa4c0208638d5516010431ce2cab008218f3154580410c76931ac020863b458d6010431dc4c4b008218ee162580410c739aa2c020863ac9516010431ce2a8b008218eb154580410c718aa2c020863b49cd6010431da2e6b008218ed343580410c76821ac020863b48c96010431da064b008218cce72993310c62fbb2a9988638799154cc431d2cc9a0e6218d5575107310c6e8b808398863175da538c4319e2e03246218c757694e310c74b3268718863719cb438c4318baeb3226218cce72991310c62f3b6a898863171d9544c431c38c8aa26218e9464d05310c6aaba88298863c5550414c431b8ae420a6218dd170105310c63abacc898863555d7434c431d28c9a1a6218dc572d0d310c66b3b66498863175d83294031ab2e0194a018c6e72191500c636b90c8a80630f9d0625403187ae8312a018c7b76540500c71cb22a0280639a5895014031cacc6b0ea990d1e73d5254c872bb8ac72a643951c56395321c9cc7314a990e4d6398a54c868f39ec8aa643179cc6
  | 20 => 0x171d095010794a1084a80835c9c44254041ae2e2212a020d3a748c9501069cba464a80835c9c63254041ae2e3192a020d73714c950106b838a64a80835c9ce4154041ab6e6a0aa020d58735055010799ba282a8083d4dcd4154041ae0e6a0aa020f507350550106a839a82a8083ccd0d4154041e6286a0aa020f33425055010798a1282a8083569cc4154041ab2e620aa020d6a7210550106b4b9082a8083175da53140418beeca98a020e4e539885010726a9cc4280839394d6214041c9aa6b10a020c6d76948501072731ca4280839358e52140418deeca90a020e4e635485010726b1aa4280839694e6014041cb2a7300a020e6a529805010734a94c0280831edd95014041cb4c6a80a020e59635405010735312a0280839a5895014041cacc6b0ea998e4e6398a54cc72731ac52a6630fdd95415331a9ce52a48798d4e7295143cc62f3b0a8a1e6395d976150f31caca830a8798e545418543cc71b2a2c221e63879914394b31aa8e2a1ca598c6f7654852cc70f2a0c6a0e631d5db5410731caacb3188398cd57690c41cc66bbb28620e63b158e6210731ccacab108398ec56358841cc768b1cc020e639c5956010731da4c6b008398ed16358041cc771312c020e63b85896010731ce6a8b008398e715458041cc76921ac020e63b450d6010731aa8e2a1aa198c7b7654050cc72ab1cc3aa4630fdd95415231c9ac7310a918e4d63588548c72cb1cc02a4639a98a6015231cd2c5300a918e5963580548c735312c02a4639a5896015231ce4c2b00a918e4d6598b438c727aa4c5a1c639355262d0e31c9acab168718ec662987438c71b2a0c2a1c63175db5410e31ad4e1a94a518c6f76548528c63d384cb214631e5c26590a31c9ac72948518d2c74549428c66a39ac221463175d6648ca31c3cc9aa46518cd571190328c66cb80c81946317dd9540ca31c3aa8b188318cce72993318c62fbb2a998c638799154cc631ae2e02a66318d6a72d42508c62ebb46528463565c032942318dce4322a118c6d72191508c63dbb2a0284638bd516295131c9ac7314a898c3f76550544c696b94c82a2638bd5162d0d31c58a8b168698d4e72952434c71a2a6c2a1a63539ca5450d318bcec2a28698e5465d85434c66b3a8c2a1a63959d46150d31caca830a8698e5454185434c716b26a5292631bdd95214931aa8e2a18a498e1f5458f424c66a38ac7a12631e9c065109318f2e03288498c5e7598c424c70e2a6c6a0a63539ca548c531c3ac82a46298c6e72993504c636b94c9a8263551c543d413187ce9316a098c3d7498b504c63dbb2a0282639518c61550318dce4302a818c6d72181540c61fbb2a82a0638b5516215031c72a8b00a818e4e63988540c717322c42a0639398d6215031ccac5308a818e5a63980540c735314c02a0639a58a6015031c74c
  | 21 => 0x752a12c2210831e9c265cc8418f2e132e6420c7a70996321063cb84cb1908387991538c841c3ac8a9c6420e2d6494a321072aa9cc3190839554d618c841ccca4b0c6420c7a70195321063cb80ca990839554f614c841ccaa5b0a6420cb574185321063d384ca190831e5c2650c841e1aa6a968220c3d76952411063abb4a920883d154d52904418b8ed29a8220c5e7654d4110727b1ca4a08839318e5250441c9ec6a928220e4c63549411070fb9ecaa0883871cf6550441c3ecbb1a8220e1f6518d411070fb2ca6a088387d955350441c5ecb2928220e2f655494110786a9aa4a088395dcf6550441ca8e7b2a8220e5765d8d411072bb28c6a0883a595063504419a8ed29a8220e576594d411066a3b2a6a088395d955350441d28c7a1a8220da572d0d4110733b2ca4a0883b118e5250441ccecaa928220ec46354941107a2a9aa4a0883655cf4250441d28c7a128220e9463509411072729cc5a80839354e62d4041c9ca6b16a020e4d5358b501072731ca5a80839358e52d4041c9cc6a96a020e4d6354b50106ad39ea128083565cf5094041ad4e5a84a020d6972d425010637b92c7280831b1c963940418bee6b14a020c5c7358a50106b5396a7280835a5cb5394041ea0e2a9ca020d6a7214e50106b4b90a728083569cf5294041ab2e7a94a020f4a5394a50107a4a9ca528083d294d5294041e92a6a94a020d5a7314a50106acb98a5280834edd54194041ae6eaa0ca020dd07350650106ad398c928083565cc6494041ad4e4324a020d697219250106b938ec7280835adc96394041ad0e4b1ca020d6a72d0e50106b4b9687280835cdc54394041ab6e6b14a020d587358a501069d3a0c528083569cc6294041ab2e6314a020d727118a50106ad39e8528083565cf4294041ab6e6a0ca020d5873506501062f398c4a8083175cc6254041aa8e6a0aa020c7a76d4d50106b5396a6a80835a5cb5354041ea0e329aa020f507154d501063d3b0a6a80835a9c85354041ad2e429aa020c7a76d4950106ad39ea4a8083565cf5254041e94a7292a020f495394950107a529aa4a8083d254d52540418f4ec292a020d5a7314950106acb98a4a8083c654f4154041e52a5a0aa020f525390550107a8a9c82a8083d894a4154041ec2a520aa020d3b75505501078ca9a82a8083ca5494154041ae6eaa0aa020dd07350550107a929a82a8083d454d4154041ec4a4a0aa020f615250550106b938ec6a80834e1d16354041ad6e4b1aa020d687258d50106b838ac6a80835a9cb4354041ad2e5a1aa020d7271d0d50106b8b8e86a80835cdc54354041ae4e221aa020d717110d501069c3a2c4a808356dcd6254041ab0e6b12a020d7071589501069d3a0c4a8083569cc6254041ab2e6312a020d727118950106ad39e84a8083565cf4254041ae4e3a12a020d7
  | 22 => 0xa83569c06214d41ab2e0310a6a0d557198053506a7b92c029a83531c96014d41a3ae8300a6a0d4e7218053506a6b90c029a83555c46014d41c98a731686a0e4c5358b435072a29cc321a839514f6150d41caea630a86a0c5e73983525062eb9cc1a9283179db53549418bcec29aa4a0e5b53d81525072c29ec0a928396d4c6054941cb0a6302a4a0c6f7654852506b4382a42928317dcd60149418b8e6b00a4a0c5f76d4f425062fbb0a7a12839514e6190941ca8a6b0c84a0e5453d85425072a298c2a1283539cb534c9418f4e032864a0c7970194325070f320a61928387590530c941a9ae429864a0e5453984325072a29ac2192839514d60d05418bce7316a0a0c5d7398b505062f3b6a6a8283179d85354141c9ea7b12a0a0e4c53d895050727a98c4a82839314c62541418f6eca80a0a0d6872540505062fb9ac428283171cd6214141a9ce5a9ca620d4d72d4e53106ad386a729883565c35394c418dee4b04a620c6c7258253106ab38cc12988353dc96094c41a98e4b04a620d4e7299153106a6b94c8a9883479d26254c41aace3312a620d5471589531072b310c2a9883951886154c41ca8c3b02a620d5671981531068e3a2c0a988353dc96054c41a98e4b02a620d5471581531062fbb2a6298839354e6214c41c9aa6b10a620e5953980531072ca9ac0298831b5d662d0c41c9ca73168620e4d5398b4310637baac5a18839394d62d0c41c9aa6b168620e5553587431072b29ec2a18839594d6110c41cb4a7306a420e5953983521072d29ac1a90839654d60d4841a9ce7a94a420d4d73d4a52106b5386a5290835a5c352948418bee6b04a420c5c7358252106b5386a7290835a5c35394841e88e2a9ca420d6a7014e52106b4b80a7290834b9d36394841acce3b1ca420c6d76d0e52106b3b8a872908353dcd6094841a98e6b04a420d2e7418252106a7398c129083535cc6094841acce2304a420c5e73181521062eb98c0a90831b9db5354841ad4e1a9aa420d6970d4d52107a238aa6a90831b9d85354841ad4e029aa420d697014d52106a739cc8a9083535ce6454841ac8e2b1aa420c6e76d0d52106b3b8a86a9083599c44354841acae221aa420d4e7310552106a6b9882a90834b1d16054841a9ee6b02a420d4c7358152106b238ac0a90834b9d06054841a9ce6302a420d4d7318152106b3388c0a9083175da53148418beeca98a420e4e539885210726a9cc4290831bdd95214841c9cc6a90a420e4d63548521072d29cc0290839654e6014841cd2a5300a420e5a53580521072ca9ac0290839a54960148418baeb31e8420c5f7558f421062ebb4a7a108317dd953d0841c9cc72968420e4d6394b421072731aa5a10839358d52d0841ccaa4b0e8420f0d53508421072aa9cc221083351cd6110841caaa6b088420e66525844210
  | 23 => 0x50e32caca830a871969654185438cb0b2a0c2a1c65a55506150e32ca8a830a871945d75181438cb0f2a2c621465359c660cca32a6ce9a8ca31945c7650d518caaa38a86a8c651ddd95114632aa8e2a1aa11955a70cc9508ca3dbb2a0284651e9c261d51328f2e130ea89947671983544ca3ab8cc1aa26595d8c6155132ce6c3b02a89967061d81544cb2db18c0aa2659ad886055132ce6c2302a89967061181544cb2cb98c0aa2650fdd95415132c5ea8b16869961e6550c434cb0faa2c7a12658b9954210932ad0e0aa6649955471552324caac382a9192659cd4560945328eeeca88a29967161d42504ca3dbb2a028265565c23214132c9cc7314a81947a70185540ca3cb80c2aa0651d9c460550328eae2302a81943f76550540cb1aaa2c22a0658e5516015032c6cc8b08a81965663584540cb33312c22a065951cd6115032ce4c3300a81967161980540cb1d322c02a0659698d6015032cd4c4b00a81967261580540cb38b0ac02a0658b5526290c32aaae22a4861955970152430ca2fbaac521865175d66090c329ace3304861945e76151430caaab88a8a1865565c05450c32a9eeab1286195c870589430cb62b16c2a1865335c86150c32caeca30a86196c662185430cb2aba8c2a1865959506150c32ca8a830a86196c672185430cb62b90c2a1865879914394832c3aa931c841956571152420cab4b80a9210651bdd56390832a9aeb21c841964d6590e420cb872a48721065935954390832b88e2a1c841946e76151420cab2b88a8a10655a5c05450832a9eeab1a84195c47158d420cae4382c6a10654b9d25350832a9aeb21a841970c5450d420cae238a86a1065a359142cc8329ace3306641945d7694e320ca36bb4a719065a3591438c832b88e2a1c641945f75591320ca6a38ac899065361c1644c832d1ec8a12641946f75591320ca74382c899065a3d91434c832b8ee2a1a641947a70191510ca3cb80c8a8865179da4354432aa8e2a1aa21962c64509510ca3bbb2a2288658d5915114432ce2a2b00a21947671191500ca3ab88c8a8065551c54354032ad0e0a12a01955a70cc9500caac38264a80651edd95014032c72c8a80a01967161540500caa7396a729e8317dd95314f41c9ca731687a0e4d5398b43d06a739ea529683179cc6054b418bae6302a5a0c6f7654852d072731ca5a16839398d52d0b419a8e6b0885a0c7b7059532d063c382ca996831bdc963943418d8e4b1ca1a0c5f7358a50d062e39ac5286831edd950143418beeca98a720e56531854390637bb2a429483531cd5290a41a98e6a928520d5473597419063dbb2a02848393d8a62d4d41a9ce5b0ea6a0d4d72d8753506a7396c1a9a83535cb60d4d41aaae2306a6a0c5f7654c5350637b92c029a831b1c96014d41a3ae8310a6a0e4d6218853506aab88c429
  | 24 => 0x30a8621d8d729514310f2bb2ec2a188795d946150c43caaea30a8621e96541854310eaa38a87290871d9c460548438eae2302a421c6f765485210f32a92c2290879a5496014843aace321aa221d547150d5110e3bbb2a228887995895114443ce2a2b00a221d547150d5010e3b388c4a80871d5c462540438f6eca80a021e69625405010f38b0aa0280871d9c66094f428eae3304a7a15567119253d0aaab88c929e85569c06494f42ab2e0324a7a151e7418653d0b2ab08c329e85559c66094f42aaae3304a7a154f7258253d0a8f3a0c129e8555dc56254f42aa8e2b12a7a155b7058953d0aac382c4a9e85471d16154f42caac230aa7a151e7498153d0aab38cc0a9e85555c66054f42a9ee4b02a7a145f7654c53d0b26a9cc5a1e859394d62d0f42caca7b0a87a16565318543d0aca38a8621e859394e6210f428bce7304a3a145d7398251d0a2ebb4a628e8517dd953147428eeeca88a3a165a5398051d0b2ca9cc028e859694d6014742cb2a6b00a3a16715158051d0a2f39ec2a8685175cf61543428baed298a1a145f7654c50d0b2b29cc2286859554e6114342caca6b08a1a16555358450d0a3dbb2a0286859c5855014342aace3a9ca721476719825390a3ab8cc129c8517dd95314e42caca630a8721655531854390b0eb2cc7a14858759563d0a42c9acb31e852164d6558f4290aab39ea328c85179ce60946428bae7304a321477765445190a3b38ec6a84851d5c763542428bce7b0aa12145d73d855090a3dbb2a02848517dd95314d42aa8e2a98a6a15587054c5350b2ba98c2a1a859514c6150d42b28e2a1886a158e73d4a4250a3bbb2a228a85551cd5114542ae0e0a88a2a14777158f5050a3a38ac7a828517dcd61d41428b8e6b0ea0a147b765405050aac39aa0282855c1c55014142c9ee4b18a0a164c7258c5050b2b31cc2282859558e6114142cacc6b08a0a1655635845050a3b38cc1298851d5c66094c428beeca98a621655535845310b2ca9ac0298859394e62d0c4287aed2a4842146d769524210ac6b9ca8a1085691c543508428bce7304a22145d739825110b2631c84a88859318d42544428eeeca88a221655635445110b38a8ac0288851edd95014042cb2c6a80a021671615405010a3b38cc1aa6651d5c660d533287eecaa0a99964e6358854ccb172a2c421e658755263d0b328dced2a2859952e7695142ccb173b4a8a16654b5c25450b3299ae630285994777654451cca3dbb2a0286659558e61d5232a6ce3aa4a91953671d91548ca3b388c0aa4651d5c4605523287eecaa0a91964d63988548cb16aa4c5a1c65359c66090e32c6ca830a871963554185438ca2f3b4a8a1c65479da5450e32c3ced2a2871965765d85438cb8b2a6c2a1c65879506150e32caeca30a871971654185438cb62310c2a1c65955d461
  | 25 => 0x2002000000000800500000040000040020004008004007801400c0000000000000003000800400200600100080020020010000002002000000000000000180200020000010004006010002800800e002000000400600a000800001200000000000080040020040002002004000400a001000000800a00000080140080060018004000000001801000000000980000060060000000000000000000c0020000000010000003001000c002017000002800000400180100020000018000004000000800c000000003000000401a000000400600000080000020000000000004000000000c000000000801400000400080040120130000010000000000800000a0050000000002000000001800e000001800800a00000000000040010050004002001004801c0080010000000000000009801400a00000180080000000005667119252d0eb2b88c9296875a9c06494b43ad2e0324a5a1d6671d8e52d0eb2b8ec729687535cf6194b43a9ee6b0ca5a1d2e7418652d0ea7b9ac1296874b9d06094b43a9ae6304a5a1d667118252d0eb2b88c1296879a5806094b438ece2302a5a1c757118152d0eb3b8ac6a9687591c56354b43ad6e0b1aa5a1d687058d52d0ea7b9ac2a968753dcd6054b43a5ce8302a5a1d4d7318152d0eb3388c0a9687595c46054b43cd2c0302a5a1c6f7654852d0e36bb4a428e871bdd952147438eeeca88a3a1e6a5298051d0f34a94c028e879a9496014743cd2a4b00a3a1e715158051d0e36bb4a4286871bdd95214343ccca5308a1a1e655298450d0f33292c2286879954961143438f6eca80a1a1e716154050d0f16b2cc5a1c878b59562d0e43c9acb3168721e4d6558b4390e37bb2a429487539cb4394643aaae3a1ca321c77765445190e3dbb2a028487639cb5390d438ece3306a4a1c75719835250e37bb2a4292875a1c15214943b8ce5b1ea2a1dc672d0f5150eb9b82a5a8a875c1c152d4543acce5b1ea2a1d6572d8f5150eb339687a8a87595cb43d4543aaae7b16a2a1e73609835150eaab98c1a8a871ddd95114543a9ce5a18a2a1d5571d0c5150ee33968628a871d5da52145438eeeca90a2a1d73705485150eb8382a428a87599cb6314543acae5b18a2a1d7270d8c5150eb8b86c628a87599cb4314543acae5a18a2a1d5672d0c5150fa33968628a87519cb4314543e8ae5a18a2a1d5570d0c5150eaab9ec428a8755dcd6214543a6ae8310a2a1d55731885150eb9380c428a875c5c06214543aaae7b00a2a1d55739805150e9aba0c028a87555cc6014543acce4300a2a1d65721805150f38b00c028a871d9c662d41438eae3316a0a1c7676d455050f33b16a2a82879918b51541438ecec28aa0a1e67621455050f32310a2a82871edd95014143ad0e4a80a0a1c3d769524310e2ebb4a9218878dd976150c43c6eca
  | 26 => 0x801000000b000001000a000001003800400300100040140000010014002000001801400c0040018008002000005805c000001002000000c0180000000000008000802400000b001000c00e01e00380180020020000000002001004001001a001000800c000000003800000200300100400140050008014026007000000000200100000040000000020000022002000000400200100000040020060060004008001000000400400f000801c0000020020008006000001801000200100500000000010010010000001002000c0000000020004006001000800c00000c0020004004000000000c014006000000001400a0008000002000002000000001c000001400800000000000040000000008000002001800400200100280000020010000000004001001800c00400b000000000000a001000000000300000100220000000000000004002800001400000000040040030000024000000000002c00200000b0010036000000000400000900200000000010000000002001000002800c0000000000018003003000c01e01100180000000040008048000001000001800c001000801000400500100040280490008010022005002001400000a000000c0040000008018000008000000000a000000000800000a000001400802b007002000c003000000400000000100040000000018000006000000000800000300000000000000020058004000000002400200000500000000000038000002000001802800400000000240060170000018002005003000800000000280040020000018008002007000000000200000000040020060000000006000000000400e0010000008014015001002c0000010000000008000000000400c0010000000000001000800800c000003000c0060000010008004000004001c00c003001800c002000001000c00000f0000004000002000800801200000000080060000008020004001000003800000300680000000010028000000000001801800a000000800800c0040028000000007000001c00200000000080160000030000004001003001c000002000002c014004001800002c001003000000a0020000004006004001000c006002002000800600a0020018004002000000c008004001001000600c001800c0120010070020000004001000c008002000000c00e000003800000a0000020004008006000001000e0010000008004003002804c00000300000000020010008000000000001800003c002002800c00000200380000020020060000006000000000800200600280040140060000038000001001001c000004000000c000001001801c008001000800000400001180380160000000000000009000001c002002000003400c000002000c00000200d0010004000000802c0040000020000004004001000
  | 27 => 0xb281ee36f80001c69722000000030f9cf434c8000721834027a00006d800003298000727800000000020030008000000000000000400a0100000008000003000000000e00f000801001000300f800000200600300000060000008014004004001001c0000070008004000008002800000800700580000000060000008002000000000c00000800080000000000010008004000001801800a004000800401c001002002400800b0010008006001001000000200600000000000000000028018000000000c0000030000008002009003000000000000000240020000000018006006000000000600b000000401800400080100000010000000018000000001000200d001000400200c000801800000000000000100010030010000000000002000a00300080080020030008044008002002803000600b002001000400400080300000010080000000000003003801c00e0010000000000000001400200b004800000e0070000000008002001800001400300000000000050008004012000001802c0020000000000002014003002c00000e005000c00e00100000040020000058000000008007000000c0030030008000001000000401e0000000004000003001800000200000300000020000000000000009003000401a0000000008000000000800000a0000000004002001000002c00200500300080020000000008000000000000800000000000000020020000010004005000800000a0010000004004001000800000c0050008008000010007800800000300380280000030000010002001002000000200000280040000010028014002001000000000a00100000140040000040018000001004000c00c004008800001c007001000000200100280000000030000004006000001001800200000000100020030000000000002001000001801000080000060100000004016000006800000800b00380180060000018000002001000800000200100180140040070038000006000000000c0220000000008018000000000000e00600480140160010000000022000002800000a00a009000400200500100200200010010000010000000800400200800d800800e004001800c00200200080000000000030000006002000800000400300000040340000020004004001001800400600000800000000000020010000001003800c00a00400100000000040018000002000000800400200b000000400400b000800400a005001000801a0040018000002000002800000000e002800400c003000800c00000100300040140000000000002006000001000000400680040000000000000002006000000401000a000800c00000300080000040090078000000000000001800800000080040000000008000012006004005c014001000000000a000004000801000
  | 28 => 0xf860000000000000000010a23d8843420f187e62a000014e00000001a0200000000ad0000000000020d8ea06678000594000060280700000b54644926009880002aa000029a006200000002268000000000012d166000000005c11da400000000eb80002d280000000fb02bb1aac000000035080007d8a1024d501582fd0000000000000014aa0c80c8a0000e860001ad46a69ce481500827658a782968ad86d0a0387478eee34c1fb419f801670b00003d404242a9000062085460000ccc0fd913c0000b2a69b144603b1b4e000000059d15644ff00007bba09c2c78e58235210660a148200000003ba04a25b3100c7a793f073f95307e59c303fd02960678000000018800002a600000001a202d600013b600000004cd151e00013e200004285ce8000000000030380000cb80000000000575816264e15243f484627e91360000082826f069600000000000000000000004b000000015bc00000002fc934e70a000000000005cb9518000016612b881805105787c914f031a098400000001fb80002e6000000000003788e380001a360000b9600013267a6212a4a580006d1a0a627813383610bfe410000031715260001e620000000000031000008003428ae60000000000090a0001e3c11d0bea850000000000c670e800000009b83d2917600014e246f00007b3800029400004f986a870500000000000000000074700000000934000000000005401159450000000003c80003b89e201031dda62197720001a8e00008721b88000000000083c8000000145600000004f90000000095434a12e233512ac0000000370000023e02164ac0e42000000000014880260c2e00000006b5800000010543e70e520001cae000000057e000000019841079388000000063b00000001102033866e2149e2e588191e4869962288800052b85ca465a0e80b1996400000002869a78000000079a9f1e42317ae28917b0000000023400000000ce41130c9400014382f2000084b8f8217000003cf1ede5679e0a000000000019ba000000029705683d800000001b5881600000ba801200007f07899d08000012200000004900000000119a000197a7ff1cb4344049679498b22fe8306772800000020a285588fc3b580fe54a9b74781153c7d507fa1211af24c0916a4ce98c422a1f0608a8c4a25e9cce0a0051e70e000045f00002e80000664800000017ce000215a19c8d8c00020060000000202988e2d19b94000051200005c462300007e100001ef95ae8118c6a4df1ad855f003a1c01bc262b07504450046000084a00018a0182203e0001dc8823904439502087a097fe7da07dc7c895b04c780003a6800036500000c000003ce9a341eb96e07348e5c64111e00000c3c00000004f709603a8800000014c824e000071100003d706dc35480005aa84b800000002
  | 29 => 0x12de85f0000000000059f02826a6055c00000005fc11f208b20b0161a0925b5094600001540f202482241baa3cf8a020cf97a8000000000000006d6872a077000000000000000e68000002a65a013a696800018c92c8653821867901fc00000006db000000016fa6a995e01dd0000768000020714ec645994400009ea07680000000416846800000010e400000000000b8000000003c803c65cc20402bd000000000002a28e6c38b9fe05480cde000022e000089617d80b408180000978ae482e80000000000270000026d0000000000000000000001e360000000000000084980000000d341bd84e000000006ff141a06a07f26fd00000001b1c2ee80000000000000000083d83340000c32470858c2f0040a7aa897200012521b39fa80000a2a13d0ed06ff9f0e61492f408904862ba94dc323139882286d65ed88aa0001d5849120625c200005850000000000000000000001bf800000000000000304000069e8fce5e6a042000000000013186c8000041880000000000000074c0000c5a77b9f6646a11780001ace000100a56888703218db608d085800000d864a993e6fb005200005d600007c85a880001379c4279600005d58000112896c717972831d84dc2359e088279dd87c690241a980943bd0cfe7671422000011800006de00000003c18344000166a0000d0611202ee000000036e800075a99482c18c8059685f47360000000000000007602979c56650969600000004b18fc2000000060580000001ea000001cc00002ca000000080800000001a181511a063e6124a000000028d0000000000055480000000000000198a6010f7a0001c740000d802390294000000047480004d79c985750000458800000002b2000200006e168246a94860000dfa5f6000072880001bf0a147e8965457318e25398bc66960638508218c2e3800000000006e1000043606543a093065d18c980000000000000000018b60001a6265280005a6800000000000001448460972c3120000000000000012a800000006290000380800050395e20001e565cd80000001de400000001a617f428f0000513000001100005670f220000f445fa171e2471a7271a879244a92d010e18aa4218f6c7920f3012c17de4b0909c4b59c407df154c4e88e1045219260db9db06f6213a7de911c627907671f114659b8000673800057d80f400007b420b81f610c1f824ac9fc800011ea854163a6eb97ec33b0ebe016077a45004c46ef034861d99667389e406c608a200c0e741a29bd220486bc05399d400096f40d904881850000000000075890805ef0cae01915e484a1e8e26a20ac5620d724f48a866268000000000000000000000000000200c000000000000000000de856997420000b0836680007fc800039287867e3000056a000078700004f40000000217e0000
  | 30 => 0x27d9e78222000015e9e7005b000056f8000590915c1c9a15e32a80002ed07a8000000046d8c5e542949a60c1cf8216819682a08605ae08d2000000000013b200016bc0000c4c35a00000a180000001cfa5a7800027e019400004e20001fb8000000000000000001d780000000047846a00000000000908000209800000002328620691000031e80000000000000000051004ca0f600001c28000594967208015b608981483eb096825e1e4c000139e00012021f518e60000000000000058e21104db939600000004bf00001e080003a493225070dfc0000000532973e5b0000000000001d2800009f0000000000000004c00000000000000037c8000749800018180000000000478800000005520000000000000000000000001d906460000842800082920763559dcc74c80001c18000000000045595f0000000057114027d09d6600016e62c8126673b00000238050195986634b80005f917be31994705a380001e5001c0e49ff4000053621b9b320f2939c5b20c562ff1ba40e591902388ac244e10502e404e6009800000017600f995ee7d114fa0001032345000024a9d5a774126402797960000aa046802f080c0b7c7dc03d24cb1e94000000008d800000000005b600000000000000000085d800000019a803a9d6c3c998624261dc02b694be0050776000000000000004b483b000018d05f4954600000004459f580000c243d614344021e160000d465d30806000000004705cc43c1a203e483a48351e80021a0ec856000000000720cc8ae243b800056120da43aa03a814185003a201e1298000000000071380005b08ffc00020bc00003564d40b9e00008ba00000000000dfe000049c1ad00001918000566060a00019a600014ee71a002c2ae8be400000000000c88775004e85e815011f80001d9106e6581fb20000cf42750fc614016da000197e190069e4fa9b907b7071e6cf000049a8c4200000000001774000000066b0000586800011c901a19880000001fc40000020000000000000000000f9434780000001eca158155837780000000a422be00000000810632820a31d02aa8621b886f79ca800005ac65e00000d700000000000000145855f978608c80006d0000015f800000020d20d380003e7913a4a81d5e31500000001a5e000000000010de000000000000000001e8800001b25d498de0000f1e00000000c6982c7ab80000001ac60000d78282130c2eb819a000000068b8000404867883a80000001d2200010f20001df867996c428813d8489095861800000000000535800007a000000014de4cd96028599782084087a000088c2640ae83270f70000000033f20665c48e9600000000001c0c7fe84d25ac190800000001cf17fa6e800000000000000214233a01200000a5256d05b60000000515000073120720000000
  | 31 => 0x20001f7e41f90a448700000001b22000160c6fc00dc3980000000211c55a82e630100003d58000000103c7bd80003a9000001b961275f00001f9852e4340b507e985ce0001dc60e311be293005443518c81dc884e00000002e49cd06c30b007618000051925800000000001dd211180000bfa0841a80000704830802718ba000052670780007a988f46e194bc0e7908247f89c660381000001958000156038e800000013c2000000000000000000000000000000011d00001af836f0f5e000137e0330000252074840580002fa015a5de0000540951c0001fca40e8000000207e2fb08440fb96fe3ee9abe48d00d00001dfc0000c7c7d016f22de9dbe000000055514c2000108a1b100000000d740f0979c0af975a2e08000000000000000780001bcc00000000001f563e28000000000057080000000000495866c39312bc00016c63a10a2e1a0930418a9a301d6050e00000006e70cf82960cea45b9f6026711e604f1f6c00016f800000003aa00007f30bd80001056000024c27617d63fe17da70702e04d600007f41df42c903464c806603df87ec5681ba87248ebc0001b561650edc00000006d7149c03109ac4b9848e0000d5c3f2000000000007290e8c00018ae63d02d4488964800007da2b10ac052d05920fe83e26be800036200000001d0c725000000000001e8800033280000001b0a3b38102000000070900003f7000007117b400000000000bbe0810cfa0000000000000000005e400000006aa8f681b300004510bc2723146a0000a721e719de33380006ac119c38f9606104000000017060001ab87c99af00001b4c00000000b680000000000000005c8258000000000000017aa3d3000000000003b0000011e800000009ee00000000000000000138c000124c00000004259d000e000000000b785c81e5a375a052000000023200006aa0ff206808983cd978826d872e00000002cf80000000000606a11e3bc0c1e0000000000205c0000000000125e4c5000000000002950000410800000000007d184d611d800035d800000014d847e0000000000079f86fe7c2023c00003f43f78000372800000000000000000765037884f0000000000000000004b680000000000212189018091b25e5000000018a26e6135600016f00001cb000003ec0000384000000a000091a000080859180000000000813028c50580004bb20de17f09d27e482d014917682630834000000008e8ce60001a1274500007121a96000000000000001d511c81f085a2447893c0909540221000076c944200000005740000000173213c037a71605840000000000000000011c62e205dc61008d807788b64a7066606a80606e2800067d800000000007dd1f2875b800084c9b9a20f800000000000001be6000136a1be8000000000000000000a3878e12520c0000
  | 32 => 0x18da870281d041a02b87d49de6199120a20c212038d1fea00000002298c46000140c5da842e72d95921e78000000000029d0cb400000000001e74029938600008f2000000000010bc000000000000007f1864e853172675081b03a00000000000036c84cc1e903dc753114a30d93827551da8550824a6441b6806880000001a4600001380001fbc0f6800000008801c40f0e0000f1a59997a65e4188056a96fc14680000000cc0000146c000000059d800000000005fd843200000001d087ce0061d9a0d090b65a4035e42e0e6600013ba1bd0000840216e00000002958fa00000000000202c0000ad05a19fd61450000778070200014c400000000000000000079648010ae2a50a0013a80007bd17a027c000000009fe7409340000000000010480000c9216b9308670800027c8d000000510783800070d1a7c7a30000000000062100001ef00000000d8641a800000000000000bcc00000000000000000000000011fa79800002918000000000021889ca30a80005c286f2000218a0000000119849a34880005ca9ea825780000000cee00007787a40bf8588927e098000046b80000000c6e343800072f86a4326800000021487501dbc000000021180000000000000026a0000b4e703a036372120600019d22df80f0000000028e00003c49f3e67b16d00448000735800063680001a380005ad0d9c37a8bde00001bc000000000000000000fe030a06044cc800000015341100000000128c86080c00ed9a8600003540001d983e415560001c1000000003f900006ee9e6c61180004be00006f214a43df000000000006cc08e8000045a38b00003ef800000002bc68b00000000000000057c0001eb6000000000000004b110520001d680a9000017a0d0423105a60000e444e41b803b28000000000085d0dee000000079280843640b280001a4e25a86be00000005c687d63f680003c08000000000060c99ee43f9684000000003e826e85e0a4a85509ce0000bd4000000060617ee5091db8000128000019f2000000000000000ea00001969c8e00010780000000463000030e0000604876800000000000ce26c39d1a00000b22d580000000ed8000202200011b40000000000000066c80000000c18000000049e1276167000018e8c502a01c5c6b6909006700000001bc6000000000000002bc80000a111ac0001d1600019c80000134000201000000001ee0000000068c09d0000000000069a8000000000083e800000000000000000304800055980000000d620000b7033680003371dfe80a1eec4ca08b20cb00003ce000002b85de52880000001bd06b7867c6021b102c69ab44a100004d28fb8722800081b8aee10210a800021366c9000022f0000435919e000000055c187024114e43d000000c28000000000018d9e840001f14824195a4689bf
  | 33 => 0x9c0000000000028a4dd064c0ca112832f800074491f610385b483292823b309280000da20000000000000013f800018a05f800000007e3910a2ad800000000002b300007ac000009d8d8255410063f89632000189200012ce000075e580000052a0fb458a00002ab00005bd8ec2227800000000000001fee000000000004fa00019f04e3800026b80004c28b38083125a57619546c100001b005a800014444d314805f5000014600006088000059059a09395c000000000000c1a0001eda4c009d0591158e29f13cc51993ee7801e06531829e521000022b985e40a843c488058808e00000000efe21001241ce15de51c99b80970b3267d1d8a2d60a6a01a0c4e000111a1db84b64ea8000000000000000002ec0ace46e12080d680007c0882a0001fe801780001ec8b8a0001ebc000000005b90fc000000000004bc43980000000f420000000000000000003ac4530c6c1521f107e418c0000113441317f244c9c167689d3815c800000020ae000160e6d8a0b2000000032400002ec800048f06c21eea16837d9c4666911f07e180004449a14000121200020c8000000000007ac4a68f8c00010fa0001e24000140081f00005c5800075c933e0c10000299112c716959019c14e0000000035c000013c800000012c042100000a68af06b3152c78609700001fda0000000633143e682945a62f951054f800064512300001c7600021041488dc426e800069286ba0f38000000000000006e00000000084921832a18107370a7600020e638814ac15d0e7e7190bd2000000080600c80e3998221d8e9c42500003fb80000000000000000071405022ce870e83c03666a904d884b0000243800061585500000ea658d9ed8000000052d8e2228a00000001c7a84600000be05320000e1a00000007f7198c0000000637000036c117a577000000017cc51f8d7a000000000000002151a0e153000061a0000000000054300006700000000000050a800015900000000000131971c4ec16102da0bce81212b8375214400006845ff1fb05400c0a7da89b030991040001fde00000000738a12000136877e80002a6167a0ec86f04770000000000000000000b080000001ee475213460809bb01cc203234689003e9923a00a19b653f01c20638eb4000048200017a23be98ce69d800076b9a8800018f00000570000014a00000004e682a800000002798000000000000012720001f301d100004ca80007c310025f09bb400000004c7000000009da000089400020822680e98000000064a078a1889a0813a1ba61780c147548000303000076385d007010c669f8160194a10e8570000012800005700003d3843663a81d2000000073200001f18f9a0000000000000004a12900001b0200003506eb0000046808805f214e74a800074b104e7d2000000018026110e884f
  | 34 => 0x386000073e4f280004c91b824c49664000054e18f16701c51a687cf1be22bd83f86b990ca2731ddc61c8d12000000000011e821e0000260800050e87f6000173453a9a6611b9fba00000000000fb63988b0c10500be5240a3a55113a00001e7a0bb09360000000000000020115fc7f0086a6fe897600000d252c002e25880f8000200235984c200000002a4043e087a05e4ed0000000000e66a9a8c109845e162937222f9c6c44f800067a8000430800070a8000283961850a0ce000000000000000000000047780005af86444e906da36e17c40000de026c9ee81da95783500c024d6925c0ef8eb000012dc14200001291c7e5d5148c43880001c5800000000005650000000079a00014da00000005178f1429c133c6308d160000452000107000000006908e0c00000000001a0c00004fc253800037689147a598f248300b82409f5e00000904f51c62861800016f165c00000002c10000000000000001563da800000000000001010000003600006000000df821402cc0000000000000000002904a18000000000075d839405e8cc27ad0b9400000001fd000053e000000020d6283133041c80006b90c5257690f8366000000000000000dd00000de6000000007e00000001a8000000000f00000000000001f9d34522841c000000060ea02a6df096e61f0a100000bd07611fd40000000000090c40880008450fa40000000000000063580000b211300000000000000025000003cd00001e31d8048a982a01d989878c1a4032c89c478514f47db99b07b4800010600007c480007c015865901caa458173839a910e000176e4750fd81569e1e0000cd06428f740000d3c7cb00006bd0d0c00010aa61a915415d95a416786ec19e832a0000000023000012b000065d01e002803e47b50ff64661ea4000000000008324a880002fc000038c197600000001e800000000e6e000000000000001ca00005e30d6c79c8000000000010680000001a1e2591ef284e017200000003de006678f80000001fd200000000000cf00c611241e000000e70dc230b1d74603116c858186e000150813d800000012a400000006d2035283d00006f0124e821800000000002c380345cf10cc00009200000000000000000004f8000000023d8000334848a00000007f39e420da8000000000000013fa0000000417800006f80003b509e208a00a44bc0000848852c14f18487270000000039047399f8126000003800002a10e4800000001c10ba453f87d2654a0808051f720f11cac00013f867612aa721154a0fa8ad4000066a02898fe648881412000001878ab85a480000000534000000037c05ee000146200000005a9000000000002a79c962a21fbe60f02b02cc000000019ca0000000000000000017c8000031e7c60b766b40e723fa062e0cc0c587ba8b
  | 35 => 0x118037995e18b0d544650f641529f9e5128c9680d027a57184505c08ef67f89a4815880000001b000000000504000072980000002064000000000000001ea80002cb00f65b28000000000000000000d2800040b1c4c03f114e0000cc44499ff8066164e416141457a14d27b0918635b8d0254e831255382e86c490b24079b38000000000003364118558607800034a90f60000000000000008f9bd400000000001a2a049969c4e50000000000007b09a6751080c3870be28421cca25980006db9c360c3109a54d97e23c61d60424996c000175e0000174000000000011a650f04d000019ae00000005b7800000018966c78a3050c050c82200000001a38209033876780006091b9e3e014f64050fec0000d4440a0e407080910708800005480004ba82580000922124899e5f40a1629817185d912cc308018a000048c00005fa00012a600016a63fa916400003ba396993a382000000016dc6c58a6239f1ac4000000000016e82300d202d20da40000000839000000005661a480006e880001ae14263b49c907eb13c4000026400000003ad800065000000001452000000000005560001b140000cba000000000000000b3800000018ee000000070b9f9800008ec000000000f000043681867ca80000000f84000000000000000000000000000000000002b70f5200000000001a563100b442818a40000000034e9506000000000000004dc0000000179819d00000001b5e000000049f0f08000212400018b400000005c900000000000000000085c0abc000000014f9b8e6a500000001e28000000048f80001760000407000080214c000004541f6000047586e6000077066708167e8000014a85287789bda48d947a00000000000afc00000000000000000000000013a600012fa00000006e300000000000000000000000001c90000000102e3f3186c00005fe00000005d40000000051c088a06a0000a7e000156c08808b035381ae1368cac2509878462941e183984e35601c635f02a00b8963423983227098f00000073a5a5127052e17403ae0292091869000892e000000006da86d269d1ce07e718f88068ffa2f698367cd038a48580961f900006780000000000020b00006a7902000000007c29d3a12c800000000002a59e2c0000952091107c53301f4263951a64b800000000000c98baa73f20260369c3238a88dc3239ac86a800000ae9a3c0001e022db82de0000bdc8059fe600000006a29f360000f0400000000ce80000000fd00000000000000085b02f40df13ce5ee96a86619a1c3fc0d9e00000006d1107407280002e1881a0001e5c050000054481b406000000dc8e168318aa631900004a28b365b48d24760910c0000d2c0000000000104a000053a0000000000000032e0000585800052501c8000001000000003c9000038980000
  | 36 => 0x60b8000374800000780002f100000000000000157400000000001988000000066d00000839e38556800000003f000003aa000081e3681a1a7f9000000000000000000720122e0000d487ea80005020dd80001792432097e3b81c6600000002d49cf016401f272c80000001cee5ba935c0691cde0001a0411b0b1c22d155e4bc80004f0000038780004950f9668e800030c04902559e4661913be8459c3c0000000000131a000021a000010a06400001609464000130e45d00000000d9223a84ee5a20000000062675900005489cea5e380000000d5a0db029c444000083085e6000025a0001a640791e6457c9d4e3891a527bc0e46289800049a07b0000000068580000000eda0001ab200000005df80008331c4a000168a000000021d0b027ff865034205b20000e94000197000000003579efa171800000016e400003a25ee00003290000000000000000005a30a9c59788de34e1b703f518d87b000007ac8df442813e07c800003ac8000527800068a04c8000013600001761a01c0212a89e40308ee40000000000000015a800022e0000000000000000008449b52189000000000008360fe60000000000000000000005138b5a000089200000003e88000000000024900007c591f403b9e9c0001afc00014d41b618001338a4469c07fe1b2207a83e19d667f85ba7b89e3a6ba8b745ad96ac00000001f780001089d1038493de4ae85046fd9ed0000000084d00006de000040c14963d518a67480f6e62509dc23f8f4649d07f8203886838604583d980006d9076c00002686408b3479f192085a800000017000000000460000017c800012a00004e2985a00009860000000000000037711fc67183bc57a8d5018400005d89e92463a05609491704a60f886438686589000076980002a08000000197200004e46cf8000000108800012287b98000471115a50600000000000000163e2d991720001d3e2461626000000000000000000000000000000000006f2800000000000000a040001bce00000002d780000001fec7d683760000eac108208c16a86ee0000ec8000000000000002b80ca064d1f4e175204e74f00000dd00002e1126c78311924f58000145893a0799b3462c0e3639d8e4e83400002fd82560000000000000071c05800000000000000028f83b828d80000001dc46f802f6784128e24583601c7000000007c07438762487a1305721ff01b41e5e6e5887e00000000001c8200004a06419714000160a6ca899846912be6891be802c05b8000178002a027e3ca0642346047c70010ce5df088e0000cc60000000000000000013f6000122c804800013500000000000000158a4481cb86ca00000b11a10609a17228b10e8000000024982b60000afe00000000a601f065591ee50d80003ff800082e216455d8000000000057993640001
  | 37 => 0x5e2660000000000000001ac02418a0a7268fc026280004c589de0001b3a0000000000000083f000068880000000000000000014810b4533800000000000ff00000000d7e0000bac794000042f8000000000054c800050c9292860070c0e090c40000000000000060e20780000a1e000000000000001d3921407882c0265967e0158130075899454512ae0000000000017851d0000825099a0000a92000000007e82ac84f99a200011087de16985dd9b660000f720000000000196a48102fa2f5936678d1a322db1e868388000000044e07500000001bee74b8ef208700003cb1a4c7b809a25e296ae4d21a3e46c05c819710f45958000490905a000039a0d89f1c55c800060509be0000a6617c01920b71a5465f1c1a16900006ef81fe05a07e851a1b5422285da00000000c5000005a8d6021799a024b813e16598fc8518f0a09512f60001b76000000075e9e224b9000072e8b120000bb600002d2665206082d8000302015e64c1f880000c346ae80006b8800054a00002009ab65fe03fe861129e74d93c8773800058f149821916302af80001c880007939cc0336000046ea00e00000003a39bb80000f8e0000de41b280aa1f417ca1df1568828000000017ac000000024f90e05570000253199842b0000000000049880006f5894a5028cd666387ea45f958c784985866f18b83801f3a7571dc25e7891e45997e63838ac609b1a9201093ec59e1f0436b8b9a359082036d1aca7eb97c64dd800000001a661308c600015ec48380004701cf65a81b36000064a5929d0681115b224c80bc000036809986345d215ac0a217ea41e83705d386ea00680006de8eba6a89b1a2d000003a2901800300000000612423800058b89aa5e111582ac93da17b00000001404000000000000000000000596000025f03a07bf0000238000000000000000c1636b1a6e00000005f0000000019900000b18000000036380000001d7e0c7209a0e60e5e0000000000000000000000000000000000021700000000000000000031e0fbc0000ba60001db400000008169af600020fe00011003739aec4cb800000000002da9854000206864f12462449f9400001100001f2e00011ca0451c3e000000041900000000cf2000000059893780000000264875c60f9a90739a03c22700001ed8aaa0000f5a6ab80000000006000000000000002c280005b390ba7d2991c6f906681a688ee5810e3c00000002d0a04a0b900000000fae733061a013000011e1f507a2800082f95b8221800000019e206d800080117b20000000185800029e8000000000083700007b180005729f643b1065e2a38bbc751992c63812d856596802368106545861c00018bc64d90ec14c0fb22a68c9e00000747010000000000000019be2cf1dea32f00002b79a002d81b5040d0faa50b87c41a71c6e
  | 38 => 0x60d10661d0010e2d90b22000004831c000058a98e84e100000001f8a08500000f81152000000003518f604c85be54e0d960fa000034980007a685a04d88e7a00000b66019ac22099aee000000023e800034fa0ee000000041713e800000000000000308833c41800006fa80000000000560000010a9dde09e000000000002f2863e4d495828588d8a00009c200000000000000328827011a0daa215800000019d0000000000012fe1661fb60001d284001e540000fd652480001b181840900f1000000000c9000063181ba254000019600000001e2a5d10ac800000000001b7e7b20e5000009746348000369856e00000000c38000697000031c800062208827be037e000007c3cb8c6200013f45280000715000013b00ac29b1eb800000000000bee65b808a000000005f89301ac956e026800000007e22b480007b30fca0e2000061d000049e884c764800048e0000219800000013f20001ae80001e1a33200000000f16000018c000000000000000328cb624b0000000000000020245f717580bc93fe0001d4a5180000104977a00003d03d200001cc8000000049e23c00006af00000001e44002000000000008381ae073500000000000000074627d0ba8000000000000000000000000000061280006cb80000200b10210800075c123267e9a9c0000cb00000a1c0001ebe2c5864800008ac3070dec0001c062e300000001daa00001082309d5651700002f8122600020ce4ad000000000001e20000000000009c80000000000233000000011ec57489ec3c32074000190000000001b90aae000000020e800059a0b622570756000046000000004e013440d30000000000000000000000000646800000000003b18000403800035a800051f16080000fa80001f9a1ab000039c046440f8f1c1709ed602e90264731d0a430000062280000000000000199a7999e6e5048092831002456e9d0477a01160000efc0001f8000014b200000000000c606f11a2664c936c72f00007ae80000001ec40000e7800015f43718eaa000005a00000003211b2c5b8800057e800042c05545d7215200000000001e7664905060001f5c31f80005bb8358000000051d96b20b600003cc80006b70000000071800000000000a6e1e60000000000044880007ab00001860000000095a4b5200a77d8d4a722109e0000d3611117a4293840459300000000000174957a0010eae40d80000000734714800000000003be00004579250627040079a03d610e86d40000000000152e373000001a804000003d40000000461000077c11da000174a0001b082d71c72041147804a844267306303990eea5238cf643486aa6081ca01be047054120aa00001ac00000000bf000000000006a1214a7ce000000007ca00007121f8159a78c85ea731950e1d69d18060995c04b8000000
  | 39 => 0x3810d1c5bb0b2e0000000000000000018e400008221cd807a76200007020ab000000003f10a320000000038800000000000000c3a2a319504de9cf21ac00000000000000199600002ae21f1a5046209fa0001946000000041b0a4873680000001dec0000676000000000000004a51c607d314ba6b49310749185c00f942c00000007f099da0000a1800000000000000000202e0000302000181c0000000000139238a110600007cc1cb1db653a003227200006e4926e71e14d040e0afa00019e8000072053c92b64ef069457f80e60001bdc38500000000f7600014060000000000086c000114251b976c1e411682ee162c00000005c400004ea00000000c446dc84ba47900006710be64b280004eb83a60a8800026000005f800000001b06275856c00000000001a60000201c0fc9a820001004843000000000000000e560c580007308000000190c00000004ee000008c0708000000000009fc81c000061080d6000000000000004eb06a2000128800000000000f2a30197705ae8b4c43704067f610a676b19fc6c980000001dba000000038c966c7dd85b01ab80000000000000000000001d877c934204300000000000587800070604020000000142970c3a40d4c5d98000000003800007840001bb200000000001d506ed87a600000000000e063bb1ff667700005589ce8000094409411364bb8ba263e860c00000000000b721ba0b1400009881ff000082d187a3001d8c7a880002ad00001170ee64ba03b40000000573800000011d812f98d4269154820e000001b0000053000010b00e45b58e0a52981ea2c981700000000229161c1ad81427758000000000045400006bf88a0492000044b877e000000081b000000000003b780000f3000000000002b580006d283de00000000000000653055e7cc970e00000000001d3032080000000e9e16380001d488ce0000aa21d98000000000015092107bf800
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xe5190230a448158e6295130a44825d46150d30a46829506150d30d04541c543d4930d07541c54314930944815ce6414930c25645c46414930c29645c0641493094a809c64314930946819c24314930d4071dc14314930d43711c14314930c48529c261cc930c44529c660cc930a4481590524c930a4a80d90528c530d40525c2510c53094687d49510c530d0474d49510c530a1586150410c53094587148410c530e0564148410c530c91645c0410c530d40525c0410c530a448158c52d0130a4681d90528c130d09541c1420c830ac181d8c624c030a1684d4c6150f20a488358a60d5220c147418d5150620c15745846114d20c48531c162d0d20a4b8714c6050920a498714c6050920e40539c46050920cc1735c46050920e40535c46050920c48531c162d0520d08531c142d0120a44815906254c20a48805906254c20c48629c26154c20c44629c66054c20c29545c262d0c20e09544c9600c820b04815cd540c820b08805cd540c820945851c5430c820c45651c5430c820d05541c5430c820e0a83551600c820e0983551600c820e095494d600c820e095454d600c820e095490d600c820e095450d600c820ac08150d600c820d21545c03294420d21545c03254420d41535c03254420d41325c03254420d09545c0328c420e09540ca608c420c29545c0624c420c49655c0320c420d09545c0320c420c0d541cd6290020d09545c0328c020c45750ca618c020e05540ca618c020ac1800ca618c020c0e76553324c020b09831c15448020b21811c15448020a0d859506348020e08805506348020e09545c06348020c0c765525348020c0c765515348020e055418e5148020e055418d5148020a448654d5148020e095418f40480208c98718c4048020c497518c4048020cc0635c44048020e095418e3048020d21545c63048020cc0635c63048020c287655130480208c8865cf42480208ca86dcd2148020a48805886254e109148754d4110610c89641cd20082109488754d2008210e096454d2008210a148454c6150d10a448254c6150d10c14541cd6110910d05735c85450510d11735c05450510d21725c05450510c16871506350510c15871506350510e06821506350510e05821506350510e11801506350510c1576150430c510d10545c0430c5108b1841c1620c510914845d4320c510ac080588320c510cc1625c0320c510c447518d4248510c14541cd61d0110d10541cd4190110c50651cd4150110c30655d03150110ca0765092150110b20855092150110d80735092150110c89641cd2008110a48835486050810a4681d4c624c010a4a80d4c624c010a0d8414c624c010c0d641cd520801084c8758d5208010b118414d3044010b418214d3044010d40531c93044010d21745482044010b40835482044010d41735482044010
  | 1 => 0xdac906e808cab700048007c698012c0017afc90000004cb288542611e3466a18622d568b83e1945340c0092ba9892470023578385297d42000000146003aa0508780014c98a700001600002800ce9408a08e600001853625610003a000030cf64f473319e2c5631000460580000b46a00054005f000a8004b8006a291f8000000323201844002695ea9000000051000197a5a000013a000000000d73d2307400368f4401800000000007800008b3e86c0000358cc7c4d00354460013b00004b13000d2800f07176402c314007625138603c6cb3800a010800c600002490eab00000000e1cae4005e3ca0c6c220021400006e000002844804009360800000000329325c04000d0b563001b400001d1a4d100140000035000de91512d848713600000000000a001a00c020203868020a008001c0000040000d0000402000080002010780804000080c1e00030001801000000201000000000010000e12038480a0102000043c02824020100000240801800000800000000094681dcd6094b43944825ce6014543c31745806014543c61725806014543a85829506150c43a14845846154f42ac08058b6150c328c5879886150c32a51801506150c32b05811514350832b09801514350832d04541c54350832c85641c5438c832a29801914254432c49625c06214d41c84735096110841e05535096110841c84635cb4350441a448654d52504419508794d41540419508754d4154041d40739494154041d40735494154041950835c44254041d21425c44254041931841c53254041d1073d0d4154041b2182d0d4154041b1183d094154041d1073d094154041d10735094154041a46829506150f31c16641c54394b31a46829506150d318c58798861d0c31cc2625c061d0c3190d841c1520c831948805d5420c8318d1801d1610c83185487551610c831c8474509610c831e0554509610c8318c5869cb4310431c45659cb4310431d05549cb4310431e055458d6210431c15659d23210431917875523210431c15765503210431e115498d6010431e115458d6010431e21549896010431e21545896010431e10835516010431e11549cd6010431a90845cd6010431e11545cd6010431ac0825cd6010431a5185d0d6010431e1154d0d6010431ac282d0d6010431a92848c96010431e11548c96010431e11540c96010431d05545c8414c431d11545c0414c431c84645cb434c431a1684d4c6150f2191687d4d4110521a448154e62d0f40c16641c5538cb40a50835456010740a448254c6150e40a90835056010640a488254e608c640d04735494110440a46829506150f30c16641c54394b30c91645c0410c730a448258e61d5230b0584148329463094682dcd6494630a4686d483254630b40804c83254630c147418d5150630a31849456010630a448258
  | 2 => 0xee005731c840065800767e3804000006dac4cc003f80082164f954a4001581c0045000c800b306855b01a5c00164de4f05148720b8dd74622d829546e4a958ba9c648000003021
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x479a000226c14000838028032bac03431802218e02401c016ab6000080e8000029048000808210800002a03202a0e2a1a841964020d425c44254041c8039b05a1a82a8083481901d142584320c68092eaa284b086418e01619549cb4310431d00aa104b9ac020863a0154a0b43580410c642730aa464b008218e0161d64148410c530e00b20a4b808218a614419714d7118142482c0122c1aa8b0064104906548150d600c820d00aa102a1ac019041841756003298630083402a8c006530c601050265c805506348020b00c8900aa0c690041c015418d718c1200830110eb22a6900410860161d821506350510c08c3b002a0c6a0a21a01826005418d4144250328402c419062886081d8855092150110c80428e6a1242a02215019414c724c110043202e841aa41022008450261735482044010
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 40
  | 6 => 1844
  | 5 => 9193
  | 4 => 4295
  | 3 => 223
  | 2 => 30
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
  | 5 => packedAt gbK5 (395294+((h/3064+packedAt gbK5 (349334+(h % 3064)*15) 15) % 17765)*15) 15
  | 4 => packedAt gbK4 (229058+((h/1431+packedAt gbK4 (210455+(h % 1431)*13) 13) % 6860)*14) 14
  | 3 => packedAt gbK3 (14046+((h/74+packedAt gbK3 (13380+(h % 74)*9) 9) % 323)*9) 9
  | 2 => packedAt gbK2 (2190+((h/10+packedAt gbK2 (2130+(h % 10)*6) 6) % 48)*6) 6
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfe0fff1fc1ffff83c78fc7e07fe3fff83331ff
  | 1 => 0x1ff03fe3fe07fc7c07f1f8ff83fc7e00cdce7c
  | 2 => 0x1fffc003fff87ffff801ff0003ff8fff0e0f8f
  | 3 => 0xe0000003ffff807ffffe000003fff007f00ff0
  | 4 => 0xfffffffc0000007ffffffffffc000007fff000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x422284204c1008004182412118a092501110b5
  | 1 => 0xc4618a048471108c0290c8470964243045465c
  | 2 => 0x885124910a360358801920a224909a30e0b0a
  | 3 => 0x81ce2c922946395ad7240014539240c5f00de0
  | 4 => 0x11083000318442632449249860000106aaa000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 31 gbPos gbNeg, 0xfeeee8a0feeee8a0feeee8a0feeee8a0feeee8a0feeee8a0feeee8a0feeee8a0feeee8a0feeee8a0feeee8a0feeee8a0feeee8a0feeee8a0feeee8a0feeee8a0, gbN, gbR, (fun _ _ => 0), gbI⟩
end PEqualNP.Outside.L_meta_12923
namespace PEqualNP.Outside.L_meta_12923
open PEqualNP.Outside.L_meta_12923.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 30 := block_range (n:=30) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 30 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_96 : Interval gbAtlas 3 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_192 : Interval gbAtlas 3 192 31 := block_range (n:=31) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 223 := (concat bgb_3_0 (concat bgb_3_96 bgb_3_192))
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
theorem bgb_4_1248 : Interval gbAtlas 4 1248 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1344 : Interval gbAtlas 4 1344 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1440 : Interval gbAtlas 4 1440 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1536 : Interval gbAtlas 4 1536 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1632 : Interval gbAtlas 4 1632 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1728 : Interval gbAtlas 4 1728 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1824 : Interval gbAtlas 4 1824 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1920 : Interval gbAtlas 4 1920 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2016 : Interval gbAtlas 4 2016 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2112 : Interval gbAtlas 4 2112 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2208 : Interval gbAtlas 4 2208 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2304 : Interval gbAtlas 4 2304 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2400 : Interval gbAtlas 4 2400 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2496 : Interval gbAtlas 4 2496 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2592 : Interval gbAtlas 4 2592 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2688 : Interval gbAtlas 4 2688 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2784 : Interval gbAtlas 4 2784 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2880 : Interval gbAtlas 4 2880 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2976 : Interval gbAtlas 4 2976 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3072 : Interval gbAtlas 4 3072 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3168 : Interval gbAtlas 4 3168 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3264 : Interval gbAtlas 4 3264 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3360 : Interval gbAtlas 4 3360 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3456 : Interval gbAtlas 4 3456 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3552 : Interval gbAtlas 4 3552 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3648 : Interval gbAtlas 4 3648 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3744 : Interval gbAtlas 4 3744 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3840 : Interval gbAtlas 4 3840 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3936 : Interval gbAtlas 4 3936 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4032 : Interval gbAtlas 4 4032 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4128 : Interval gbAtlas 4 4128 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4224 : Interval gbAtlas 4 4224 71 := block_range (n:=71) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 4295 := (concat (concat (concat (concat (concat bgb_4_0 bgb_4_96) (concat bgb_4_192 (concat bgb_4_288 bgb_4_384))) (concat (concat bgb_4_480 (concat bgb_4_576 bgb_4_672)) (concat bgb_4_768 (concat bgb_4_864 bgb_4_960)))) (concat (concat (concat bgb_4_1056 bgb_4_1152) (concat bgb_4_1248 (concat bgb_4_1344 bgb_4_1440))) (concat (concat bgb_4_1536 (concat bgb_4_1632 bgb_4_1728)) (concat bgb_4_1824 (concat bgb_4_1920 bgb_4_2016))))) (concat (concat (concat (concat bgb_4_2112 bgb_4_2208) (concat bgb_4_2304 (concat bgb_4_2400 bgb_4_2496))) (concat (concat bgb_4_2592 (concat bgb_4_2688 bgb_4_2784)) (concat bgb_4_2880 (concat bgb_4_2976 bgb_4_3072)))) (concat (concat (concat bgb_4_3168 (concat bgb_4_3264 bgb_4_3360)) (concat bgb_4_3456 (concat bgb_4_3552 bgb_4_3648))) (concat (concat bgb_4_3744 (concat bgb_4_3840 bgb_4_3936)) (concat bgb_4_4032 (concat bgb_4_4128 bgb_4_4224))))))
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
theorem bgb_5_4128 : Interval gbAtlas 5 4128 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4224 : Interval gbAtlas 5 4224 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4320 : Interval gbAtlas 5 4320 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4416 : Interval gbAtlas 5 4416 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4512 : Interval gbAtlas 5 4512 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4608 : Interval gbAtlas 5 4608 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4704 : Interval gbAtlas 5 4704 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4800 : Interval gbAtlas 5 4800 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4896 : Interval gbAtlas 5 4896 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_4992 : Interval gbAtlas 5 4992 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5088 : Interval gbAtlas 5 5088 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5184 : Interval gbAtlas 5 5184 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5280 : Interval gbAtlas 5 5280 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5376 : Interval gbAtlas 5 5376 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5472 : Interval gbAtlas 5 5472 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5568 : Interval gbAtlas 5 5568 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5664 : Interval gbAtlas 5 5664 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5760 : Interval gbAtlas 5 5760 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5856 : Interval gbAtlas 5 5856 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5952 : Interval gbAtlas 5 5952 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6048 : Interval gbAtlas 5 6048 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6144 : Interval gbAtlas 5 6144 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6240 : Interval gbAtlas 5 6240 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6336 : Interval gbAtlas 5 6336 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6432 : Interval gbAtlas 5 6432 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6528 : Interval gbAtlas 5 6528 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6624 : Interval gbAtlas 5 6624 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6720 : Interval gbAtlas 5 6720 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6816 : Interval gbAtlas 5 6816 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6912 : Interval gbAtlas 5 6912 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7008 : Interval gbAtlas 5 7008 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7104 : Interval gbAtlas 5 7104 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7200 : Interval gbAtlas 5 7200 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7296 : Interval gbAtlas 5 7296 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7392 : Interval gbAtlas 5 7392 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7488 : Interval gbAtlas 5 7488 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7584 : Interval gbAtlas 5 7584 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7680 : Interval gbAtlas 5 7680 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7776 : Interval gbAtlas 5 7776 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7872 : Interval gbAtlas 5 7872 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_7968 : Interval gbAtlas 5 7968 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8064 : Interval gbAtlas 5 8064 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8160 : Interval gbAtlas 5 8160 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8256 : Interval gbAtlas 5 8256 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8352 : Interval gbAtlas 5 8352 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8448 : Interval gbAtlas 5 8448 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8544 : Interval gbAtlas 5 8544 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8640 : Interval gbAtlas 5 8640 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8736 : Interval gbAtlas 5 8736 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8832 : Interval gbAtlas 5 8832 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_8928 : Interval gbAtlas 5 8928 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9024 : Interval gbAtlas 5 9024 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9120 : Interval gbAtlas 5 9120 73 := block_range (n:=73) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 9193 := (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_96 bgb_5_192)) (concat bgb_5_288 (concat bgb_5_384 bgb_5_480))) (concat (concat bgb_5_576 (concat bgb_5_672 bgb_5_768)) (concat bgb_5_864 (concat bgb_5_960 bgb_5_1056)))) (concat (concat (concat bgb_5_1152 (concat bgb_5_1248 bgb_5_1344)) (concat bgb_5_1440 (concat bgb_5_1536 bgb_5_1632))) (concat (concat bgb_5_1728 (concat bgb_5_1824 bgb_5_1920)) (concat bgb_5_2016 (concat bgb_5_2112 bgb_5_2208))))) (concat (concat (concat (concat bgb_5_2304 (concat bgb_5_2400 bgb_5_2496)) (concat bgb_5_2592 (concat bgb_5_2688 bgb_5_2784))) (concat (concat bgb_5_2880 (concat bgb_5_2976 bgb_5_3072)) (concat bgb_5_3168 (concat bgb_5_3264 bgb_5_3360)))) (concat (concat (concat bgb_5_3456 (concat bgb_5_3552 bgb_5_3648)) (concat bgb_5_3744 (concat bgb_5_3840 bgb_5_3936))) (concat (concat bgb_5_4032 (concat bgb_5_4128 bgb_5_4224)) (concat bgb_5_4320 (concat bgb_5_4416 bgb_5_4512)))))) (concat (concat (concat (concat (concat bgb_5_4608 (concat bgb_5_4704 bgb_5_4800)) (concat bgb_5_4896 (concat bgb_5_4992 bgb_5_5088))) (concat (concat bgb_5_5184 (concat bgb_5_5280 bgb_5_5376)) (concat bgb_5_5472 (concat bgb_5_5568 bgb_5_5664)))) (concat (concat (concat bgb_5_5760 (concat bgb_5_5856 bgb_5_5952)) (concat bgb_5_6048 (concat bgb_5_6144 bgb_5_6240))) (concat (concat bgb_5_6336 (concat bgb_5_6432 bgb_5_6528)) (concat bgb_5_6624 (concat bgb_5_6720 bgb_5_6816))))) (concat (concat (concat (concat bgb_5_6912 (concat bgb_5_7008 bgb_5_7104)) (concat bgb_5_7200 (concat bgb_5_7296 bgb_5_7392))) (concat (concat bgb_5_7488 (concat bgb_5_7584 bgb_5_7680)) (concat bgb_5_7776 (concat bgb_5_7872 bgb_5_7968)))) (concat (concat (concat bgb_5_8064 (concat bgb_5_8160 bgb_5_8256)) (concat bgb_5_8352 (concat bgb_5_8448 bgb_5_8544))) (concat (concat bgb_5_8640 (concat bgb_5_8736 bgb_5_8832)) (concat bgb_5_8928 (concat bgb_5_9024 bgb_5_9120)))))))
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
theorem bgb_6_1632 : Interval gbAtlas 6 1632 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1728 : Interval gbAtlas 6 1728 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1824 : Interval gbAtlas 6 1824 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1844 := (concat (concat (concat (concat bgb_6_0 bgb_6_96) (concat bgb_6_192 (concat bgb_6_288 bgb_6_384))) (concat (concat bgb_6_480 bgb_6_576) (concat bgb_6_672 (concat bgb_6_768 bgb_6_864)))) (concat (concat (concat bgb_6_960 bgb_6_1056) (concat bgb_6_1152 (concat bgb_6_1248 bgb_6_1344))) (concat (concat bgb_6_1440 bgb_6_1536) (concat bgb_6_1632 (concat bgb_6_1728 bgb_6_1824)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 40 := block_range (n:=40) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 40 := bgb_7_0
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 9, 11),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 5 zero,inputs.getD 4 zero]
def fullWord : Sig := 0xfeeefeeefeeee8a0feeefeeefeeee8a0feeefeeefeeee8a0feeefeeefeeee8a0feeefeeefeeee8a0feeefeeefeeee8a0feeefeeefeeee8a0feeefeeefeeee8a0
theorem fullBound (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have low := boundgb certgb
  have lift := lift_ok (u:=true) (ms:=fixRows 32 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 5 zero,1,33)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 5 zero,1,33)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277075694 * 2 ^ 32 + 4277069984) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_12923.Model.Repr at out
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

def mono : List Gate := [⟨.or,[4,5]⟩,⟨.or,[0,2]⟩,⟨.or,[0,1]⟩,⟨.and,[0,2]⟩,⟨.and,[6,8]⟩,⟨.or,[1,10]⟩,⟨.or,[6,11]⟩,⟨.and,[7,12]⟩,⟨.or,[9,10]⟩,⟨.and,[3,13]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075694 * 2 ^ 32 + 4277069984) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075694 * 2 ^ 32 + 4277069984) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_12923

open PEqualNP.Outside.L_meta_12923 in
theorem PEqualNP.Outside.L_meta_12923 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075694 * 2 ^ 32 + 4277069984) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075694 * 2 ^ 32 + 4277069984) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound allgb)
