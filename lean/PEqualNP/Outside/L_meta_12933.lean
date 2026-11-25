import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_12933.Model
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


end PEqualNP.Outside.L_meta_12933.Model

namespace PEqualNP.Outside.L_meta_12933
open PEqualNP.Outside.L_meta_12933.Model
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

end PEqualNP.Outside.L_meta_12933

namespace PEqualNP.Outside.L_meta_12933
open PEqualNP.Outside.L_meta_12933.Model
def gbK8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x41fd30083f860107fc8020f790041fe20083f440107f48020f690041f920083fea9885fd5310ff2a6217e54c43faa9885f55310fe2a6217c54c43fea7885fd4f10ff29e217e53c43faa7885f54f10fe29e217c53c43fe87887f90f10fea1e21fc43c43fea5885fd4b10ff296217e52c43faa5885f54b10fe296217c52c43fe85887f90b10fea1621fc42c43fe65887f8cb10fe99621fc32c43fe83887f90710fb20e21fd41c43ea83887f10710ff98e21fe31c43ec63887f4c710fa98e21fc31c43fe43887f88710fb10e21fd21c43ea43887f08710ffa0621fe40c43fa81887f10310ff98621fe30c43fa61887f0c310ff90621fe20c43fa41887f08310ffaa4217f54843fca9085f95210feaa4217d54843f8a9085f15210ffa9c217f53843fca7085f94e10fea9c217d53843f8a7085f14e10ffa1c21fe43843fa87087f10e10ffa94217f52843fca5085f94a10fea94217d52843f8a5085f14a10ffa1421fe42843fa85087f10a10ff99421fe32843fa65087f0ca10bea8c21ff41843fc83087f50610fe20c21ff31843fc63087f4c610fe18c21ff21843fc43087f48610fe10c217e50843fe81087f90210fea0421fc40843fe61087f8c210fe98421fc30843fe41087f88210fe90421fc20843fe21087dc4210fd88421ff54442fea8886fd51109faa221fe54442fca8887f55110beaa221fc54442f8a8886f151109e2a221ff53442fea68877d4d10afa9a21fe53442fca6887f54d10bea9a21fc53442f8a6887714d10ae29a21ff43443fc86887f50d10fe21a21ff52442fea4887bd4910b7a9221fe52442fca4887f54910bea9221fc52442f8a4887b14910b629221ff42443fc84887f50910fe21221ff32443fc64887f4c910fe19221ff41443fc82887d90510fea0a21f541443f882887fcc510ff18a21f631443fa62887d4c510fe18a21ff21443fc42887d88510fe90a21f521443f842887fd0110ff20221fd40443f880887fcc110ff18221fd30443f860887fc8110ff10221fd20443f840887fc4110fd88221fe10443ec20887fd5010bfaa021fe54042fca8086f950109f2a021fd54042faa8086f550109eaa021fc54042f8a8087fd4c10bfa9821fe53042fca6087794c10af29821fd53042faa6087754c10aea9821fc53042f8a6087fd0c10ff21821fd43043f886087fd4810bfa9021fe52042fca4087b94810b729021fd52042faa4087b54810b6a9021fc52042f8a4087fd0810ff21021fd42043f884087fcc810ff19021fd32043f864085f94410ffa0821fe41043fa82087f10410ff98821fe31043fa62087f0c410ff90821fe21043fa42087f08410bf28021ff40043fc80087f50010fe20021ff30043fc60087f4c010fe18021ff20043fc40087f48010fe10021ff10043ee20087f84010fd08021fd10043ea20087e44010
  | 1 => 0xe520c2dca4187f54830bea9061ed520c2daa4187f14830ffa1061fe420c3fa84187f10830ff99061fe320c3fa64187f0c830ffa8861fe510c2fca2187d94430bb28861fd510c2faa2187d54430baa8861fc510c3fe82187f90430fea0861fc410c3fe62187f8c430ef18861fd310c3f86218770c430ff90861fe210c3fa42187f08430bf28061ff400c3fc80187f50030fe20061ff300c3be60187f8c030fd18061fd300c3ba60187e4c030ffaa6417f54c83fca9905f95320feaa6417d54c83f8a9905f15320ffa9e417f53c83fca7905f94f20fea9e417d53c83f8a7905f14f20ffa1e41fe43c83fa87907f10f20ffa1641fe42c83dc85907f50b20f6a1641fc42c83fe65907f8cb20f719641fd32c83da65907f0cb20ffa8e41fe51c82fca3907f54720bea8e41fc51c83fe83907f90720fea0e41fc41c83fe63907f8c720fe98e41fc31c83fe43907bc8720ff10e41fd21c83da43907f08720ffa0641fe40c83fa81907f10320ff98641fe30c83fa61907f0c320ffaa4417f54883fca9105f95220feaa4417d54883f8a9105f15220ffa9c417f53883fca7105f94e20fea9c417d53883f8a7105f14e20ffa1c41fe43883fa87107f10e20bea9441ff42883fc85107f50a20fe21441ff32883fc65107f4ca20fe19441ff51883fca3105f94620fea8c417d51883f8a3107fd0620ff20c41fd41883f883107fcc620ff18c41fd31883f863107fc8620ff10c41ee21883fa43107f08620f610c417e50883fe81107f90220fea0441fc40883fe61107f8c220fe98441fc30883fe41107bc8220fd90441ff54482fea8907f95120bf2a241fd54482faa8907f15120be2a241ff53482fea6907f94d20bf29a41fd53482faa6907f14d20be29a41ff43483fc86907f50d20fe21a41ff42483fc84907b90920fea1241ed42483f884907fcc920ff19241ee32483fa64907b4c920fe19241ff51482fea2907f94520fea8a41fc51482f8a2907fd0520ff20a41fd41483f882907fcc520ff18a41fd31483f862907fc8520f790a41fe21483fa42907b48520fe10a41ff40483fc80907f50120fe20241ff30483fc60907f4c120fe18241ff20483f640907f88120f710241ff54082fea8107f95020bf2a041be540827ca8107f55020beaa041bd540827aa8107f15020be2a041ff53082fea6107f94c20bf29841de53082bca6107f54c20bea9841dd53082baa6107f14c20be29841ff43083fc86107f50c20fe218417e52083fe84107f90820fea1041fc42083fe64107f8c820fe99041fc32083fea2107f94420bf28841f651082eca2107f54420bea8841f551082eaa2107f14420ffa0841fe41083fa82107f10420ff98841fe31083fa62107f0c420ff90841fe21083dc42107f48420fe10841ec21082fca0107fd0020ff20041fd40083f880107fcc020ff18
  | 2 => 0x2fea6a07f94d40fea9a81fc53502f8a6a07fd0d40dfa1a81fe43503fa86a06f50d40fe21a81ff52502fea4a07f94940fea9281fc52502f8a4a07fd0940dfa1281fe42503fa84a06f50940fe21281ff32503fc64a07f4c940fe19281ff51502fea2a07f94540fea8a81fc51502f8a2a07fd0540dfa0a81fe41503fa82a06f50540fe20a81ff31503fc62a07f4c540fe18a81ff21503fc42a07f48540fe10a81ff40503f680a07f90140df202817e54103fea6207f94c40bf29881de53102bca6207f54c40bea9881dd53102baa6207f14c40ffa1881fe43103fa86207f10c40ffa9081fe52102fca4207b94840b729081fd52102faa4207b54840b6a9081fc52103fe84207f90840fea1081fc42103fe64207f8c840fe99081fc32103fea2207f94440bf28881f651102eca2207f54440bea8881f551102eaa2207f14440ffa0881fe411037c82207f50440fe20881bc41103fe62207f8c440fe98881fc31103fe42207f88440fe90881fc21102fca0207fd0040dfa0081fe40103f480207f50040dea0081f940103fea9985fd5330ff2a6617e54cc3faa9985f55330fe2a6617c54cc3fe87987f90f30ef21e61fd43cc3ba87987f10f30ffa9661fe52cc2fca5987f54b30bea9661fc52cc3fe85987f90b30fea1661fc42cc3fe659877ccb30ff19661fd32cc3ba65987f0cb30ffa8e61fe51cc2fca3987f54730bea8e61fc51cc3fe83987f90730fea0e61fc41cc3fe639877cc730ff18e61fd31cc3ba63987f0c730ff90e61fe21cc3fa43987f08730ffa0661fe40cc3fa81987f10330ffaa4617f548c3fca9185f95230feaa4617d548c3f8a9185f15230bea9c61ff438c3fc87187f50e30fe21c61ff528c3fca5185f94a30fea94617d528c3f8a5187fd0a30ff21461fd428c3f885187fcca30ff19461fd328c3f865187fd4630ff28c617e518c3faa3185f54630fe28c61ff418c3fc83187f50630fe20c61ff318c3fc6318778c630fe98c61fc318c3b863187fc8630ff10c61fd218c3f843185f94230ffa0461fe408c3fa81187f10230ff98461df308c3f661187fd5130bfaa261fe544c2fca8987f55130beaa261fc544c2f8a8987fd0d30ff21a61de434c3fa86987750d30fe21a61ff524c2fea4987f94930fea9261fc524c2f8a4987fd0930ff21261fd424c3f884987fcc930ef99261fe324c3fa6498774c930fe19261ff514c2fea2987f94530fea8a61fc514c2f8a2987fd0530ff20a61fd414c3f882987fcc530ef98a61fe314c3fa6298774c530fe18a61ff214c3fc42987f48530fe10a61ff404c3fc80987f50130fe20261ff304c3f660987f8c130ef18261ff540c2fea8187f95030bf2a061be540c27ca8187f55030beaa061bd540c27aa8187f15030be2a0617e530c3fe86187f90c30fea1861fc430c3fea4187f94830bf29061e
  | 3 => 0xa018ff54031bea8063fc500c7fea990dfd5321ff2a6437e54c877ca990cf95321feaa6437d54c877aa990cf55321fe2a6437c54c87fea790dfd4f21ff29e437e53c87bca790d794f21fea9e437d53c87baa790d754f21fe29e437c53c87fe8790ff90f21fea1e43fc43c87fe8590ff90b21fea1643fc42c87fe6590ff8cb21fe99643fc32c87fe8390ff90721fea0e43fc41c87fe6390ff8c721fe98e43fc31c87fea190ff94321bf28643fd50c86faa190ff14321ffaa4437f54887fca910df95221feaa4437d54887f8a910df15221ffa9c437f53887fca710df94e21fea9c437d53887f8a710df14e21ffa1c43fe43887fa8710ff10e21bea9443ff42887fc8510fb90a21fea1443ed42887f88510ffcca21ff19443ee32887fa6510fb4ca21fe194437e51887fe8310ff90621fea0c43fc41887fe6310ff8c621fe98c43fc31887fe4310fbc8621fb90c43ff50887fca110df94221fea84437d50887f8a110ffd5121bfaa243fe54486fca890ff55121beaa243fc54486f8a890ffd4d21bfa9a43fe53486fca690ff54d21bea9a43fc53486f8a690ffd0d21ff21a43fd43487f88690ffd0921ff21243fd42487f88490ffcc921ff19243fd32487f86490ffd0521ff20a43fd41487f88290ffcc521ff18a43fd31487f86290ffc8521fb90a43fe21487dc4290ffd4121bfa8243fe50487faa090ff14121be28243ff54086fea810ff95021bf2a043fd54086faa810ff15021be2a043ff53086fea610ff94c21bf29843fd53086faa610ff14c21be29843ff43087fc8610ff50c21fe218437e52087fe8410ff90821f721043fd42087da8410ff10821ff99043fe32087dc6410ff4c821f699043fc32086fca210ffd0421ff20843fd41087f88210ffcc421ff18843fd31087f86210ffc8421f790843fe21087ec4210ff48421f690843f521087fea010ff94021bf28043fd50086faa010ff14021ffa9e81fe53d02fca7a07f54f40bea9e81fc53d03fe87a06fd0f40ff21e81fd43d037a87a07f10f40ffa9681fe52d02fca5a07f54b40bea9681fc52d03fe85a06fd0b40ff21681fd42d037a85a07f10b40ff99681fe32d03fa65a07f0cb40ffa8e81fe51d02fca3a07f54740bea8e81fc51d03fe83a06fd0740ff20e81fd41d037a83a07f10740ff98e81fe31d03fa63a07f0c740ff90e81fe21d03fa43a07f08740beaa481ff53903fca7205f94e40fea9c817d53903f8a7207fd0e40ff21c81fd43903f887207fd4a40ff294817e52903faa5205f54a40fe29481ff42903fc85207f50a40fe21481ff32903fc65207f4ca40fe19481ff51903fca3205f94640fea8c817d51903f8a3207fd0640ff20c81be41903fa83207f10640de20c81ff31903fc63207f4c640fe18c81ff21903fc43207f48640fe10c817e50903fe81206fd0240fda0481ff535
  | 4 => 0xff90b41fea1683fc42d07fe65a0ff8cb41fe99683fc32d07fea1a0ff94341bf28683fd50d06faa1a0ff14341beaa483ff53907fca720df94e41fea9c837d53907f8a720ffd0e41dfa1c83fe43907fa8720ef50e41fe21c83ff52907fca520df94a41fea94837d52907f8a520ffd0a41dfa1483fe42907fa8520ef50a41fe21483ff32907fc6520ff4ca41fe194837e51907fe8320efd0641fba0c83ff50907fca120df94241fea84837d50907f8a120ffd4d41bfa9a83fe53507faa6a0ff14d41be29a83ff43507fc86a0ff50d41fe21a83ff52506fea4a0ff94941fea9283fc52506f8a4a0ffd0941ff21283fd42507f884a0ffcc941ff19283fd32507f864a0ffd0541fba0a83fe415077c82a0ffd4141bfa8283fe50507faa0a0ff14141be282837e54107fea620ff94c41bf29883fd53106faa620ff14c41ffa1883bf43107fc8620ff50c41dea1883fc43107fea420ff94841bf29083fd52106faa420ff14841ffa1083bf42107fc8420ff50841dea1083fc42107fe6420ff8c841fe99083fc32106fca220ffd0441dfa0883fe41107ec8220ff50441dea0883f541107fea020ff94041bf28083fd50106faa020ff14041ffaa6637f54cc7fca998df95331df2a6633e54cc7faa998df55331deaa6633d54cc7f8a998df15331ffa1e63fe43cc7fa8798ff10f31ffa9663fe52cc6fca598fb94b31b729663fd52cc6faa598fb54b31b6a9663fc52cc7fe8598ff90b31fea1663fc42cc7fe6598ff8cb31fe99663fc32cc7fe8398ff90731fea0e63fc41cc7fea198ff94331bf28663fd50cc6faa198ff14331ffaa4637f548c7fca918df95231feaa4637d548c7f8a918df15231bea9c63ff438c7fc8718f790e31fea1c63dd438c7f88718ffd4a31ff294637e528c7faa518df54a31fe29463ff428c7fc8518ff50a31fe21463ff328c7be6518ff8ca31fe99463dd328c7f86518df94631ffa0c63fe418c7fa8318ff10631ff98c63df318c7ee6318ffd4231ff284637e508c7faa118df54231fe28463ff544c6fea898ff95131bf2a263fd544c6faa898ff15131be2a263ff434c7fc8698ff50d31fe21a63ff524c6fea498ff94931fea9263fc524c6f8a498ffd0931ff21263fd424c7f88498ffcc931ff19263fd324c7f86498ffd0531ff20a63fd414c7f88298ffcc531fb98a63fe314c7bc6298ffd4131bfa8263fe504c7faa098ff14131be28263ff540c6fea818ff95031bf2a063fd540c6faa818ff15031be2a0637e530c7fe8618ff90c31ef21863fd430c7ba8618ff10c31ffa9063fe520c6fca418ff54831bea9063fc520c7fe8418ff90831fea1063fc420c7fe6418f7cc831ff19063fd320c7ba6418ff0c831bf28863ff410c7fc8218ff50431fe20863ff310c7be6218ff8c431fb18863fd310c7ba6218fd4c431ffa8063fe500c6fc
  | 5 => 0x843bf29087ee5210edca421ff54843bea9087ed5210edaa421ff14843ffa8887fe5110efca221ff54443bea8887fc5110ffea021ff94043bf28087fd5010efaa021ff14043ffa9e85fe53d0afca7a17f54f42bea9e85fc53d0bfe87a16fd0f42ff21e85fd43d0b7a87a17f10f42ffa8e85fe51d0afca3a17f54742bea8e85fc51d0bfea1a17f94342bf28685fd50d0afaa1a17f14342beaa485ff5390bfca7215f94e42fea9c857d5390bf8a7217fd0e42ff21c85fd4390bf887215f94a42ffa1485bf4290bde85217fd4642ff28c857e5190bfaa3215f54642fe28c85ff5090bfca1215f94242fea84857d5090bf8a1217fd4d42bfa9a85fe5350bfaa6a17f14d42be29a85ff4350b7e86a17f90d42fea1a85bd4350bf886a17fd0942f7a1285fe4250b7c84a17fd4542bfa8a85fe5150bfaa2a17f14542be28a85ff5050afea0a17f94142fea8285fc5050af8a0a15f95042ffa9885fe5310afca6217794c42af29885fd5310afaa6217754c42aea9885fc5310bfe86217f90c42fea1885fc4310afca4217fd0842dfa1085fe4210bdc84217f50842dea1085ed4210b5a84217fd4442ff288857e5110bfaa2215f54442fe28885ff5010bfca0215f94042fea80857d5010bf8a0217fd5332bfaa665fe54ccafca9997f55332beaa665fc54ccaf8a9997fd0f32ff21e65de43ccbfa87997750f32fe21e65ff42ccbfc85997f50b32fe21665ff51ccbfca3995f94732fea8e657d51ccbf8a3997fd4332ff286657e50ccbfaa1995f54332fe28665ff548cafea9197f95232bf2a465fd548cafaa9197f15232be2a4657d538cbfe87197f90e32fea1c65fc438cafca5197fd0a32ff21465ee428cbfa85197b50a32fe21465ff328cbbe65197bcca32ffa8c65fe518cafca3197f54632bea8c65fc518cbfea1197f94232bf28465fd508cafaa1197f14232ffaa2657f544cbfca8995f95132feaa2657d544cbf8a8995f15132ffa1a65fe434cbbc86997f50d32eea1a65fc434cbfe84997f90932f721265fd424cbda84997f10932ff99265ef324cbfc6499778c932ffa8a657f514cbfca2997f54532fe28a657c514cbfea0995fd4132ff28265fd504cbf8a0995f14132ffaa0657f540cbfca8195f95032df2a0653e540cbfaa8195f55032deaa0653d540cbf8a8195f15032bf29865ff430cbfc86197f50c32fe218657e520cbfe84197f90832fea1065fc420cbfe641977cc832ff19065ee320cbfa6419774c832f699065cd320cbfea2197f94432bf28865fd510cafaa2197f14432ffa8065fe500cafca0197f54032bea8065fc500cbfea7a0ff94f41bf29e83de53d06bca7a0ff54f41bea9e83dd53d06baa7a0ff14f41ffa1e83fe43d07fa87a0ff10f41ffa9683fe52d06fca5a0fb94b41b729683fd52d06faa5a0fb54b41b6a9683fc52d07fe85a0
  | 6 => 0x1000001405001200400000401600e00000600000c03000e00202000a00200000400201400000000802000a00801600001004400a00001200200009200200000400c00200200400401000200800200200001a00000400200000800000400001001200800402602400400e00600000a00200200000000000c00000600001000e01000600800600800000000003c00401000200200400200000200000600a00600000001200000000201601200000c00800001801400a00000204e00202a00000000800001200200200000000401201601401200201000000000200400200601000201e00200000000000a00800000000c00000001600600601400a00a00201e00a00001000000e00000400803a00603600a01a00000002600002401400000800600004000400200201201001c00000401c00001600002400600001000c02200000001000001e00000e00600201002400e00800600000600801401800a00e00200000000801200e00e00a01400600c00200600200801000000000001000002801600000200000000001e00c00402e00400000c00c01600c00800601202600601e00800600802600600402200200000601200200002800000800a00201200001400000a00201600000201e00600200600001202000000200200c00000000a01200001000004600000200000402200e00000c00005e00e00200200000000800200000801000200c00000000200000800800800c00000800400400400a00402200a00000201400400200000400000200200400200000400600403402400200e03202a00000000e01600a00000400000800c01e00000000200200802000600000a00c00400200e00000600401400800001601000200000600200201a01000e01801800c00c00001a01000002000400604000000001e00800200000400401400000e00000200000200000000600002400002a02c00200400c00e00000600200400400000001e00001600e00e00000000400c02202200204800600000000200c00000000800400c00000602e00000800200600000a00401200800000200401400a020002008008001ff52d0ffca5a1df94b43fea96877d52d0ff8a5a1ffd4743ff28e877e51d0ffaa3a1df54743fe28e87ff50d0ffca1a1df94343fea86877d50d0ff8a1a1df55243bf29c87ff4390f7e8721f7d0e43ffa9487fe5290efca521ff54a43bea9487fc5290ffea321ff94643bf28c87fd5190efaa321ff14643ffa8487fe5090efca121ff54243bea8487fc5090ffe86a1f7d0d43ff21a87be4350ffea4a1dfd4943ff29287fd5250ff8a4a1df14943ffa8a877f5150ffca2a1ff54543fe28a877c5150ffea0a1dfd4143ff28287fd5050ff8a0a1df14143bf2a0877e5310ffe8621efd0c43ff21887de4310ffa8621ef50c43eea18879d4310ffea421ff94
  | 7 => 0xc88f529187d4dd818000fd1340000000b1029058c0000013e800000170435c001bc1b500007ec000a84000000000000001d30314f2c000d44c90000001a352480000010600000000011ac0005a01c08005c8d415e8000bc5c84610000ff000cde93198b0ca000129c0017d97393a464d4910184f400112c2b12f80012b908c00024cc29630000000001a996f0fec0003cdbe91a9abdb34f940000757c839c1bc59060c0019b852d2d40017d11bc4803e50fc3b000159d74043d4c8680ca96d9050000be8000411c79b9dcc80013dc895a940014a1bc9c6095886ca75d952547ac000000be11200fcd3c1f8000add7c000120c14197109d7991611b8f0c7c40012a40099b5c58f84af49dc2386bcf50c3c695d9859448c334000000a486f841dc6d73d9f137d4b8001b60dc98c82b48615401f053d7e5cad6615fdcf16f56acd302808c42dc8f1764dfc530e8dbad1f414dd200014119a858528d7100018ad6455e5514a80f983a896db39c640018452dc0000000008093cc9a80e4728da05d9314fe4c7d6915a5b75744a58cac7e05ed5f0e7457cb69c7cd61068e24c5c440bc129459950c74923cc893940016a0000000001b24964ba97d465d0291793e4000b540000000009d0000001891cb581c0000000012b01d8001b08878d50350000bbcfcc588091310508c6002415cef19fc000b5d7c4494001600f6438c0a97cd42065902522442c0000000002880000000000000a0e841e831804400000000066c81503800017d2bc1198b410c5803ad0483d8af17bccbd9a47dd05d4b00000b4afcda525c9b00000017a045c000230c800000000000f85e58548a0ad4001119b0d664f58434c4400066903482138425c001694000001c40000000000000aa1d687400000adbe1d187b09fd1c51e99549d9d5184db79c397510d892caa80019200017687994a4000ccd791ca00417ac1796c58cc000d08f680010a84ec001ccc90d508c313700000000002707580011c00005380941dc001641b3cd5857473da7c7fccd80009b8001558b08b8cd6cc9cdec9cc769a9d51c18da180553a0fd5250420acd9f4ea8224bc93ed45531c6f00dd0bdc5d3b800170c0019c40000005605e8d4800002c164ba0614ff4001a096cc00000000122d4edd24eb994826555000000181194c001ba00c43dd6e000000000000000c00a00200400200601200000600600801000c02801200001a00003600400600000201200200200400001e02202200800200400000200000a00000000600c00603000200200000404800800000800000203a00802200c00200000000600401400a01001a06e03800200000200800a01400000000000000c00600400400a00000c00200400a00000200200200000a00200200000000200800000c00200000400003c002010002000008002002002
  | 8 => 0x1074e1152d960fa11945c1b5d68d86474c564c180ecc2571cb75ba8268f096dce9d2746b0a14e284b4e580c947d145058d246881a89ecbe56a5874b1c1910dca312f411c5e1a24160029b70f187807442e03f589d758fc5a3c03c5187742156281740009107b40c06a840479d69808c2040015dc1d467c000000970bdce3000000000104c4fc001bf8935ab80003bd45cd1dd60000000000918ed8000000d1478800000000000020ca38001b45204000b0000000001517db4d7edce893cd89614f78ce0fb06257855209680001e10053b4dcc00009800000004cfa59245fc000000a21d0d268d0c000ab03040000000000013c8f80cc9869c300009e97e0a28000b7c12d5110c1d88000c2c12400159000003416c000000001d04000e154e00018290e55012800006d55c8000f918848443e0c580008ec1fc0016b0000c6c0000018a4001ad4cf5aac6e8941ce5015988f318611a475423c0cc0015e142885ce906d124400000000029899cbccb847d9108d04f21010631cedb0532d32148d3600019a0c78cc00005f98c0ea45d51a19ec98cf01c24000001980001c1da20930a05a118c55280000002f4000329cd40000000000000009c4de0001bb4000000eec7600019c141c08116400161167c170ec4000000135b2040c000038061a8c4e800019c4f84840007d5cbd0816d4000faceb06ad574b3196c890c706e1c9cf7d625a4992c7bd75d2a9235b6c000f400011914bc848c55c753d4f34000b40dd4000b50355a844e4b6da70618ac8000cf96691f9b1d3c4ff8000ed0a446a59787e800000198d4780018e400000169d168000390000868000001d4cc8c000000001c14de4000d390ec7c0001919135bcc2d939d218000a78000001acc9299b00000009d456c8cc0007e4000000300948001a91984568400000000e34000000000001708ac400109076c3c44b9344a6cd5c7140000001e55ec09c000471d291993e0000001298c046e548902080465434514cc144450f97616b8249531464e00f14ca4a01b3055cb350b1a89c701a117535436119d9d1b00000d4ca1c794954b99b88ad8e5d66d36c0013c1a580012405700012d144c00065000101c000a34001170b640014b400174d484000000001a04501c2dc688c1700d28f3c0017b80002544dc00174869882c6c1659ac4dc04a11d4b88001b48aad56979d53c0000000011ec3d4d68a242792a16480019680015d80000019e0408000d20f554cc000a40000e2c00100cd18000b94d8d5604d9c8062c49da14af881c0000000013bdc0dc51284764104981458fd8000c092ac0002a40018893482b98a9288000e980005c507c59db8c9f9cb0c4044c50c000640000f88d110c430962cba4a3c000eb52d897800036c324000001b84d55380cd52000012780007a44d0f8cdb4c00001cf40008
  | 9 => 0x47c000dc51b446cd952c14f4000001d080000000010a46b40019d8524000a6149c851a1c2590b8770001c481c807c9e5d45801bc4cfdc191d9d85bf02e80000000000019941808e8048884001ca8000c380007c93783b40010cdbd00010b5af8004ed484c1095f4725bb15954d4ac09a06900008ac9007a99913d837164c418b70f70b2c5a502d4946605d0700529cf906ce200009acb20e8960c000e70b18e415b00006783c8fc069d0445f5ab5a691848254f95049e00000000000004500009c9cc146ce4c0000012700014183a0b385cc6fd0940015c52c9c4d111870a55a741a5115620888e0d554065d14001d4983c6c9af17a40000000000008180009f1674dad95c648000639aa8a8c994f4400177c0005a87307cc0016884643ec9b5d7cf5c8b87f8d9dad0e386cdb9954d35c6f4a4c339b7c001104b90c9930d4142fd7b59e40005f1139c8ce80d7cbfd93933ca994acef8f755f80000001f45ad82d93c988000b7825000157c13ce446657f90d50302c97fc0019f8001c11a78c742349601d03800895a9374000a10f38c345040017786042d5634fe1734001a5c1ec0000000011500009094d1b1427d2c4685054378c0d15934c5dc8e1570c51d580002e48fcebd3f18e8100000a656e8718000b80000000db17f0fdd8ec001678000600000cc5bd8000abdbdccdc5b0000000ae8d7832cc681540015c09bd4008597a800001d519ac8e61a3800029515400000113d4e4d00000f61d6500000146862000199c0000000010e00000000000000000011800000000780017e96e5d401c565cf04001c0885434c68cdf4000000914739b184d588c874f9dae9998188a88d2dc448d82adba5bb88b5a6c3d18fc0e87513912f12cd2100a4284000000001a55d8cfc972d619ae0001c88d90115078000e780000011e0c84db9914001d6c3400018416ed448000ea152400189924c3e91258f822cbb16845b57f5cc4f1c0013f51dd9bc478468b3ca0c0000000f46c4000bd891d2fc000000001d357dc0002ec5449f50c91fdb694d8a2d8d04a80000000000018d40000014242cc000644ab9c908f829dcfc5116c0110dd0634198a0805d1d0554ae5bd5a8161d4c1581548efc4cc8bc0b80841cd444c2121c72d719c2036518800165426d4c4455b814f1ac19759005b8499b91638260b4dce1cd8000000e051300014317303a5d11c291cc00063d3d0d64ce4000e7c0b06080000002218d80d8fe9aec0010e80000018dd8258a1c980005bd4702f8c11788448c4c000a90001351928ad0001afc000000ffc00061c4c89454600000002c4000a940016d1d79cd000088dbf4000828bec0000000001440000000013010a1c940000019640003f0000549388000ec8514a7d5bd42da4c80c395cb926446071163da60da99cc3c0475368ef5588cb00004e
  | 10 => 0x1c54000000001835064a5c0016a9755d90558374578000000cb53f892400006c0001b0e4883976c0012b4001820df98780000018940000000bccec369b946ecdd8000321851c358f51400f1af5228bd4438b15940aec000ee93289c00015ac898001a0c00000194475c834000df0f11d81930ec1259a2d604b9c120d708b18b90f19e95658487044b1aa04899d4358e3cfbd91d089831bbceac2187780010ad9342f178d721d74674e502095b90400000000006d99084c510094d9500000000000000007b800033c540edc001bfc000001adc00155d880b2853527c8dc81095d208210881a451280004ac67000000190400103ccb88d58088a80000000014fc000000001714720000000010001a40ddda50148001534000384000000000bb8dbd18d30851dd3800000000000154454c9217b000000180ce08ab5d540011f0130eccd7497c128f6cd8037ce683fd474fa8000e18000784b44001c3c87c28c0012ec000491ca42002412e156c4bd0f59dd724000429bed23033138c8d0fb80001955cc0009753a805997dd006b9ab18f14380d00000000000000003f80007f516c950a9c000998001480000b04001339b540698141ac000bf910c520000aa583878c4588e4830c95408a700016c915db29260000d98430ce95848a4000790000001650000991221795d2da2800185c2a0000a187f0f4c0013fcc1c30c018000151538001a64000000000000139a00000001070864001859599434d34000001b5831d5d40000006a10d16bd40c0004a58bd6f84c02c04f19ac0e1d3d57822926ccd0001ae400000000000109800000140514986c9040000000000000303895d0bb59581693051b0000735084bd0f25805b1070d440c48b0d324ae0000001aa4629771214001c01d5d780000b25cdc21d9110080d55b51c800071c001498001399b2d2e8000000000e54fb51e498400024400070800000111ca695a00002bd6fce953b00007a19c94a80000000018e000167000145190ce640000701b4b60001b40399364414310001334b58000000938bf405158c02018415800143c7d0ee4000c648716b52e54e8b482d1d1c00084055000042400000077d608000e1c9a5680cf00003b8348000275a30f29b64e6c001d702a8d8400089cf493adbe572883cbf06dcee0baca51238000001775ad8001331359c041b8
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xf400436e52d0010db54b400427f65900109f596400433e5490010cf552400435e5390010d754e400436e5290010db54a40042f66190010bd586400427f6550010cf951400433d5450010d794d400435d5350010db949400436d52500109fd94400427e65100109f594400427c6510010cf950400433d5410010b798c40042dd6310010d794c400435d5310010bb98840042ed6210010db948400436d5210010bd98440042f561100109f597300433e54cc010cf553300435e53cc010d754f300436e52cc010db54b300427f658c0109f596300433e548c010cf552300435e538c010d754e300436e528c010db54a30042f6618c010bd586300427f654c010cf951300433d544c010d794d300435d534c010db949300436d524c0109fd94300427e650c0109f594300427c650c010af99030042bd640c010cf950300433d540c010d794c300435d530c010bb98830042ed620c010db948300436d520c010bd98430042f5610c0109f597200433e54c8010cf553200435e53c8010d754f200436e52c8010db54b200427f65880109f596200433e5488010cf552200435e5388010d754e200436e5288010db54a20042f66188010bd586200427f6548010cf951200433d5448010d794d200435d5348010db949200436d52480109fd94200427e65080109f594200427c6508010af99020042bd6408010cf950200433d5408010b798c20042dd6308010d794c200435d5308010db948200436d5208010bd98420042f56108010cf953100433d54c4010d794f100435d53c4010db94b100436d52c4010dd597100437754c4010ed953100437554c4010ed553100433554c4010ddd4f10043d653c4010dd54f10043d553c4010d554f100437752c4010f994b100437552c4010f954b100436552c4010cf952100433d5484010d794e100435d5384010db94a100436d5284010bd58610043765184010be596100437965840109e59610043ba5484010ee55210043da5384010f654e10043ea5284010fa54a10042f96184010de94610043f251840109fd9510042bf6444010af191100433e5444010cf55110042df6344010b718d100435e5344010d754d10042ef6244010bb189100436e5244010db54910042f76544010ddd9510042776544010edd9110043b46444010ddd5110043b65444010dd55110043b55444010cd55110043d76344010f518d10043775344010f594d10043755344010f554d10043555344010f9d8910043e46244010ddd4910043e65244010dd54910043e55244010d954910042f76044010dd94110042fb6544010ded95100427b6544010eed9110043b86444010ee95110043b95444010f6d8d10043d86344010f694d10043d95344010fad8910043e86244010fa94910043e95244010bed8510043f36144010de94510043f25144010
  | 1 => 0x427d65908109f196420433e5490810cf552420435e5390810d754e420436e5290810db54a420427f65508109f995420427d65508109f195420433e5450810cf551420435e5350810d754d420436e5250810db54942042f76150810bd185420427f65108109f994420427d65108109f194420433e5410810cf55042042de6310810b758c420435e5310810d754c420436e5210810db54842043ad42108109fd97320427e65cc8109f597320427c65cc810cf953320433d54cc810d794f320435d53cc810db94b320436d52cc8109fd96320427e658c8109f596320427c658c810cf952320433d548c810d794e320435d538c810db94a320436d528c8109fd95320427e654c8109f595320427c654c810cf951320433d544c810d794d320435d534c810db949320436d524c810bdd8532042f4614c8109fd94320427e650c8109f594320427c650c810af99032042bd640c810cf950320433d540c810d794c320435d530c810db948320436d520c810f34c8320427e64944109f592510427e63944109f58e510427e62944109f58a510427d65d0410cf953410433d54d0410b798f41042dd63d0410d794f410435d53d0410bb98b41042ed62d0410db94b410436d52d04109fd96410427d6590410cf952410433d5490410d794e410435d5390410db94a410436d5290410dd94641042fa6090410be582410427f6550410cf951410433d5450410d794d410435d5350410db949410436d5250410dd945410427f65104109f594410433e5410410cf550410435e5310410d754c410436e5210410db54841042fa6010410be580410427d65cc410af99331042bd64cc410cf953310433d54cc410d794f310435d53cc410bb98b31042ed62cc410db94b310436d52cc4109fd96310427d658c410cf952310433d548c410d794e310435d538c410db94a310436d528c410dd94631042fa608c410be582310427f654c410cf951310433d544c410d794d310435d534c410db949310436d524c410dd945310427f650c4109f594310433e540c410cf550310435e530c410d754c310436e520c410db54831042fa600c410be580310427d65c8410af99321042bd64c8410cf953210433d54c8410b798f21042dd63c8410d794f210435d53c8410db94b210436d52c84109fd96210427d6588410cf952210433d5488410d794e210435d5388410db94a210436d5288410dd94621042fa6088410be582210427f6548410cf951210433d5448410d794d210435d5348410db949210436d5248410dd945210427f65084109f594210433e5408410cf550210435e5308410d754c210436e5208410db54821042fa6008410be580210427e64940109f592500427e63940109f58e500427e62940109f58a500427d61940109f597400433e54d0010cf553400435e53d0010d754
  | 2 => 0x5314c10bb98853042ed6214c109f990530433e6414c108f990530427d6414c10cf590530423d6414c109f98c530435e6314c109798c530427e6214c10db988530426e6214c109f588530436d6214c109b588530427e6114c10dd98453042766114c109f980530437a6014c109fd97430427e65d0c109f597430427c65d0c10cf953430433d54d0c10d794f430435d53d0c109fd96430427e6590c109f596430427c6590c10cf952430433d5490c10d794e430435d5390c109fd95430427e6550c109f595430427c6550c10cf951430433d5450c10d794d430435d5350c10bdd8543042f46150c109fd94430427e6510c109f594430427c6510c10cf950430433d5410c10d794c430435d5310c10e750c43042ee6210c10bb58843042be64d4810af593520433e54d4810cf55352042de63d4810b758f520435e53d4810d754f520427e64d4810cf993520423e64d48109f593520433d64d48108f593520427e63d4810d798f520425e63d48109f58f520435d63d48109758f520427e61d4810dd987520427e60d4810de983520427d6594810cf952520433d5494810d794e520435d5394810dbd4a520427e64948109f592520427e63948109f58e520426d6594810dbd52520436e5494810eb952520432e5494810db55252043ad5494810cb552520436c5494810dbd4e520436e5394810f394e520434e5394810db54e52043cd5394810d354e520436c5394810dbd92520436e6494810db592520436c6494810dbd8e520436e6394810db58e520436c6394810dbd0e520436e4394810db50e520436c4394810db986520436c6194810db982520436c6094810cf951520433d5454810d794d520435d53548109fd91520427c64548109fd8d520427c6354810dbd89520427f61548109f585520427f60548109f581520436f6554810dbd51520436e5454810eb951520432e5454810db55152043ad5454810cb551520436c5454810dbd4d520436e5354810f394d520434e5354810db54d52043cd5354810d354d520436c5354810dbd91520436e6454810db591520436c6454810dbd8d520436e6354810db58d520436c6354810dbd0d520436e4354810db50d520436c4354810db985520436c6154810db981520436c6054810db04152042be6414810af590520433e5414810cf55052042de6314810b758c520435e5314810d754c52042ee6214810db548520427e6414810cf990520423e64148109f590520433d64148108f590520427e6314810d798c520425e63148109f58c520435d63148109758c520427e6214810db988520426e62148109f984520437661148109d984520427e6014810de980520427f65d08109f997420427d65d08109f197420433e54d0810cf553420435e53d0810d754f420436e52d0810db54b420427f65908109f996420
  | 3 => 0x110f9884204433f54c4110cf153104435f53c4110d714f104436f52c4110db14b10443bb54c4110ee15310443db53c4110f614f10443eb52c4110fa14b10443f241c4110fc50710443f231c4110fc4c710443f221c4110fc487104433f5484110cf152104435f5384110d714e104436f5284110db14a10442f76484110bd59210443b75484110ed15210442f76384110bd58e10443d75384110f514e10442f76284110bd58a10443e75284110f914a10443f35084110b798f54042dd63d5010bb98b54042ed62d50109f98f540435e63d50109798f540427d63d5010d758f540425d63d50109f98b540436e62d50109b98b540427d62d5010db58b540426d62d50109f987540437661d50109f983540437a60d50109f596540433f54950109f98e540427d63950109f98a540427d62950108f596540433f6395010cf98e540433d6395010cf18e540433f6295010cf98a540433d6295010cf18a540433e6195010cf186540433e6095010cf182540433f64550109fd8d540427c63550109fd89540427c62550109fd85540427d61550109fd81540427d6055010cfd95540433f6355010cf98d540433d6355010cf18d540433f6255010cf989540433d6255010cf189540433e6155010cf185540433e6055010cf181540433c1055010af990540433d5415010b798c54042dd6315010bb98854042ed62150109f990540433e64150108f990540427e6315010d798c540425e63150109f58c540435d63150109758c540427e6215010db988540426e62150109f588540436d62150109b588540427e6115010dd984540427661150109f980540437a6015010af99353042bd64d4c10cf953530433d54d4c10bb98b53042ed62d4c109f993530433e64d4c108f993530427d64d4c10cf593530423d64d4c109f98b530436e62d4c109b98b530427d62d4c10db58b530426d62d4c109f987530437661d4c109f983530437a60d4c109f596530433e5494c10cf552530435f5394c109f992530427d6494c109f98a530427d6294c1097596530435f5494c10d7952530439e5494c10c7952530435d5494c10e7552530431d5494c10d7152530435f6494c10d7992530435d6494c10d7192530435f6294c10d798a530435d6294c10d718a530435e6194c10d7186530435e6094c10d7182530433e5454c10cf551530427f6454c109f191530435f6354c109fd89530427c6254c109fd85530427d6154c109fd81530427d6054c10d7d95530435f5454c10d7951530439e5454c10c7951530435d5454c10e7551530431d5454c10d7151530435f6454c10d7991530435d6454c10d7191530435f6254c10d7989530435d6254c10d7189530435e6154c10d7185530435e6054c10d7181530435c1054c10af99053042bd6414c10cf950530433d5414c10b798c530435d
  | 4 => 0xfd50314433c540c510d7d4c314435c530c510dbd48314436c520c510bd98431443d5310c5109f99721442be64c8510af593214433f54c8510cf15321442de63c8510b758f214435f53c8510d714f214436f52c8510db14b21442fa60c8510be583214427e6588510cfd52214433c5488510d7d4e214435c5388510dbd4a214436c5288510bd99621443766588510bdd9221442f56488510edd5221443b45488510bdd8e21442f56388510f5d4e21443d45388510bd58a21443e75288510dd94a21443745288510f914a21443645288510f990a21443e54288510f98ca21443e53288510bd982214427c6548510cfd51214433c5448510d7d4d214435c5348510dbd49214436c5248510bed8121442f86048510dd19521442746548510bdd9121442f56448510edd5121443b45448510bdd8d21442f56348510f5d4d21443d45348510f9d8921443e75248510dd94921443745248510f914921443f36048510bd18121443f060485109f994214433f5408510cf150214435f5308510d714c214436f5208510db14821442f66108510f9484214427e65d0110cfd53404433c54d0110d7d4f404435c53d0110dbd4b404436c52d0110bd98740442f561d0110ed507404427e6590110cfd52404433c5490110d7d4e404435c5390110dbd4a404436c5290110ed906404427f65501109f595404427c6550110cfd51404433c5450110d7d4d404435c5350110dbd49404436c5250110bdd8540442f46150110ed505404427e6510110cfd50404433c5410110b798c40442dd6310110d7d4c404435c5310110bb98840442ed6210110dbd48404436c5210110bd98440442f56110110ed904404427e65cc110cfd53304433c54cc110d7d4f304435c53cc110dbd4b304436c52cc110bd98730442f561cc110f54c7304427e658c110cfd52304433c548c110d7d4e304435c538c110dbd4a304436c528c110f58c6304427f654c1109f595304427c654c110cfd51304433c544c110d7d4d304435c534c110dbd49304436c524c110bdd8530442f4614c110f54c5304427e650c110af99030442bd640c110cfd50304433c540c110d7d4c304435c530c110bb98830442ed620c110dbd48304436c520c110bd98430442f5610c110f58c4304427e65c8110cfd53204433c54c8110d7d4f204435c53c8110dbd4b204436c52c8110bd98720442f561c8110f9487204427e6588110cfd52204433c5488110d7d4e204435c5388110dbd4a204436c5288110f9886204427f65481109f595204427c6548110cfd51204433c5448110d7d4d204435c5348110dbd49204436c5248110bdd8520442f46148110f9485204427e6508110af99020442bd6408110cfd50204433c5408110b798c20442dd6308110d7d4c204435c5308110dbd48204436c5208110bd98420442f56108
  | 5 => 0x424427c6550910cfd51424433c5450910d7d4d424435c5350910dbd49424436c52509109fd94424427e65109109f594424427c6510910cfd50424433c5410910b798c42442dd6310910d7d4c424435c5310910dbd48424436c5210910eb50842442f66110910bd58442442fa6010910be580424427f65cc9109f997324427d65cc9109f197324433f54cc910cf153324435f53cc910d714f324436f52cc910db14b32442f661cc910bd587324427f658c9109f996324427d658c9109f196324433f548c910cf152324435f538c910d714e324436f528c910db14a32442f6618c910bd586324427f654c9109f995324427d654c9109f195324433f544c910cf151324435f534c910d714d324436f524c910db149324427f650c9109f994324427d650c9109f19432442be640c910af590324433f540c910cf150324435f530c910d714c324436f520c910db14832443cd320c910bd98432442f5610c910be98032442f9600c9109f997414433f54d0510cf15341442de63d0510b758f414435f53d0510d714f41442ee62d0510bb58b414436f52d0510db14b41442fa60d0510be583414427e6590510cfd52414433c5490510d7d4e414435c5390510dbd4a414436c5290510bd99641443766590510bd59241443b75490510dd95241443745490510ed15241443345490510bd58e41443d75390510f514e41443b74390510ed50e41442f56290510f9d4a41443e45290510edd0a41443b54290510bd982414427c6550510cfd51414433c5450510d7d4d414435c5350510dbd49414436c5250510bed8141442f86050510dd19541442746550510edd9141443b75450510dd95141443745450510ed15141442f76350510f5d4d41443d45350510bdd8941443e75250510f914941443f36050510bd18141443f060505109f994414433f5410510cf150414435f5310510d714c414436f5210510db14841442f66110510ed504414427e65cc510af99331442bd64cc510cfd53314433c54cc510d7d4f314435c53cc510bb98b31442ed62cc510dbd4b314436c52cc510be98331442f960cc5109f996314433f548c510cf152314435f538c510d714e314436f528c510db14a31442f6658c510dd99631442f7648c510bd59231443b7548c510ed15231442f5638c510f5d4e3144376538c510dd14e31443d4538c510d514e31443d6438c510f550e31442f5628c510f9d4a31443e4528c510f5cca31443d5328c510bd982314427c654c510cfd51314433c544c510d7d4d314435c534c510dbd49314436c524c510bed8131442f8604c510dd1953144274654c510bdd9131442f5644c510edd5131443b4544c510f5d8d31443d7534c510dd94d3144374534c510f514d31442f7624c510f9d4931443e4524c510fcd8131442f4604c510fc181314427e650c510c
  | 6 => 0x27e65d0d109f597434427c65d0d10cfd53434433c54d0d10d7d4f434435c53d0d10bd98743442f561d0d109fd96434427e6590d109f596434427c6590d10cfd52434433c5490d10d7d4e434435c5390d10bd98643442f56190d109fd95434427e6550d109f595434427c6550d10cfd51434433c5450d10d7d4d434435c5350d109fd94434427e6510d109f594434427c6510d10cfd50434433c5410d10d7d4c434435c5310d10e750c43442ee6210d10bb58843442f66110d10bd58443442fa6010d10be580434433f54d4910cf153524435f53d4910d714f524427e64d49109f593524427e63d49109f58f524436f54d4910ebd53524432f54d4910db953524436d54d4910db15352443ac54d4910cb153524436f53d4910f3d4f524434f53d4910db94f524436d53d4910db14f52443cc53d4910d314f52443e761d4910dbd93524436e64d4910db593524436c64d4910dbd8f524436e63d4910db58f524436c63d4910dbd0f524436e43d4910db50f524436c43d4910dbd87524436d61d4910dbd83524436d60d4910af99252442bd6494910cfd52524433c5494910b798e52442dd6394910d7d4e524435c5394910dbd4a524427e6494910cf992524423e64949109f592524433d64949108f592524427e6394910d798e524425e63949109f58e524435d63949109758e524427e62949109b98a524427d6194910dd586524427d6094910de58252442bf6454910af191524433f5454910cf15152442df6354910b718d524435f5354910d714d524427f6454910cfd91524423f64549109f191524433c64549108f191524427f6354910d7d8d524425f63549109f18d524435c63549109718d524436f62549109fd85524437761549109fd81524437b60549109f994524433f5414910cf150524435f5314910d714c524436d52149109f990524427d64149109f98c524427d6314910db988524427e6114910dd584524427c61149109f980524427c6014910bb994524436e65149109b994524436f5414910ebd50524432f5414910db950524436d5414910db15052443ac5414910cb150524436f5314910f3d4c524434f5314910db94c524436d5314910db14c52443cc5314910d314c52443e56114910dbd90524436e6414910db590524436c6414910dbd8c524436e6314910db58c524436c6314910dbd0c524436e4314910db50c524436c4314910dbd84524436d6114910d9584524436f6014910db580524436d10149109fd97424427e65d09109f597424427c65d0910cfd53424433c54d0910d7d4f424435c53d0910dbd4b424436c52d0910bd98742442f561d09109fd96424427e65909109f596424427c6590910cfd52424433c5490910d7d4e424435c5390910dbd4a424436c5290910bd98642442f561909109fd95424427e65509109f595
  | 7 => 0x5c4210ddd53108437554c4210ddd4f108437553c4210ddd4b108437552c4210be597108437965c42109f98f544427d63d51109f98b544427d62d5110edd87544433f63d5110cf98f544433d63d5110cf18f544433f62d5110cf98b544433d62d5110cf18b544433f61d5110cf587544433f60d5110cf583544433f5495110b798e54442dd6395110bb98a54442ed62951109f992544423e64951109f98e544435e63951109798e544427d6395110d758e544425d63951109f98a544436e62951109b98a544427d6295110db58a544426d62951109f586544437561951109f58254443796095110b7d8d54442dc6355110bbd8954442ec6255110cfd91544427f6355110d7d8d544425f63551109f18d544435c63551109718d544427f6255110dbd89544426f62551109f189544436c62551109b189544427f6155110ddd85544427f6055110ded81544427e6515110cf550544433e64151109f98c544427d63151109f988544427d62151109f984544437561151109f184544427e60151109f18054442be6515110cf994544423e6515110ed584544433f6315110cf98c544433d6315110cf18c544433f6215110cf988544433d6215110cf188544433f6115110cf58454443356115110cfd80544433d6015110cf440544433f54d4d10cf153534427e64d4d109f593534427e62d4d109f58b534435f54d4d10e7d53534431f54d4d10d7953534435d54d4d10d7153534439c54d4d10c715353443d761d4d10d7d93534435e64d4d10d7593534435c64d4d10d7d8b534435e62d4d10d758b534435c62d4d10d7d87534435d61d4d10d7d83534435d60d4d10af99253442bd6494d10cfd52534433c5494d10d7d4e53442ee6294d10bb58a534427e6494d10cf992534423e6494d109f592534433d6494d108f592534427e6394d109798e534427e6294d10db98a534426e6294d109f58a534436d6294d109b58a534427d6194d10dd586534427d6094d10de58253442bf6454d10af191534433f5454d10cf15153442ef6254d10bb189534427f6454d10cfd91534423f6454d109f191534433c6454d108f191534435f6354d109fd89534436f6254d109bd89534427c6254d10db189534426c6254d109fd8553443776154d109fd81534437b6054d109f994534433f5414d10cf150534435d5314d109f990534427d6414d10d798c534427e6214d109f588534427e6114d10dd584534427c6114d109f980534427c6014d10b7994534435e6514d1097994534435f5414d10e7d50534431f5414d10d7950534435d5414d10d7150534439c5414d10c715053443d56114d10d7d90534435e6414d10d7590534435c6414d10d7d88534435e6214d10d7588534435c6214d10d7d84534435d6114d10d5584534435f6014d10d7580534435d1014d109fd974344
  | 8 => 0x10d754e438427f6550e109f995438427d6550e109f195438433e5450e10cf551438435e5350e10d754d43842f76150e10bd185438427f6510e109f994438427d6510e109f194438439d4310e10bb98843842ed6210e10be98043842f96010e109f993528427d64d4a109f98f528427d63d4a10dd587528437a60d4a10dbd4a528427e6494a109f592528427e6394a109f58e528427f6454a109f191528427f6354a109f18d528436f6254a10af99052842bd6414a10b798c52842dd6314a10db548528427e6414a10cf990528423e6414a109f590528433d6414a108f590528427e6314a10d798c528425e6314a109f58c528435d6314a109758c528436e6214a10dd584528437a6014a109fd97428427e65d0a109f597428427c65d0a10cf953428433d54d0a109fd96428427e6590a109f596428427c6590a10db94a428436d5290a109fd95428427e6550a109f595428427c6550a10cf951428433d5450a10db949428436d5250a10bdd8542842f46150a109fd94428427e6510a109f594428427c6510a10b798c42842dd6310a10eb50842842fa6010a10be580428427f65cca109f997328427d65cca109f197328435e53cca10d754f328427f658ca109f996328427d658ca109f196328436e528ca10db54a328427f654ca109f995328427d654ca109f195328435e534ca10d754d328436e524ca10db54932842f7614ca10bd185328427f650ca109f994328427d650ca109f19432842be640ca10af59032843cd320ca10be98032842f9600ca10cf953418433d54d0610b798f41842dd63d0610bb98b41842ed62d0610be98341842f960d0610cfd52418433c5490610cf951418433d5450610bed8141842f86050610cfd50418433c5410610af99331842bd64cc610d794f318435d53cc610bb98b31842ed62cc610be98331842f960cc610d7d4e318435c538c610d794d318435d534c610bed8131842f8604c610d7d4c318435c530c610af99321842bd64c8610b798f21842dd63c8610db94b218436d52c8610be98321842f960c8610dbd4a218436c5288610db949218436d5248610bed8121842f86048610dbd48218436c5208610cfd53408433c54d0210cf952408433d5490210bd98640842f56190210cfd51408433c5450210cf950408433d5410210b798c40842dd6310210bb98840842ed6210210bd98440842f56110210d7d4f308435c53cc210d794e308435d538c210bd98630842f5618c210d7d4d308435c534c210af99030842bd640c210d794c308435d530c210bb98830842ed620c210bd98430842f5610c210dbd4b208436c52c8210db94a208436d5288210bd98620842f56188210dbd49208436c5248210af99020842bd6408210b798c20842dd6308210db948208436d5208210bd98420842f56108210bd59710843756
  | 9 => 0x4ca31c42f6608c710fc98231c43f1608c710d7d4d31c435c534c710bdd9531c4377654c710bdd9131c42f5644c710f5d8d31c43d7534c710dd94d31c4374534c710f514d31c42f7624c710bd18131c435e530c710d754c31c43d5310c710be98031c42f9600c710af99321c42bd64c8710b798f21c42dd63c8710dbd4b21c436c52c8710db94a21c436d5288710be98221c42f96088710dd59621c42f76488710bd59221c42f76388710bd58e21c43765288710f994a21c43e55288710dd14a21c43e64288710f950a21c43e63288710f94ca21c42f66088710fc98221c43f16088710dbd4921c436c5248710bdd9521c43776548710bdd9121c42f56448710bdd8d21c42f56348710f9d8921c43e75248710dd94921c43745248710f914921c42f46048710db94821c436d5208710f948421c42fa6008710be58021c433e54d0310cf55340c42f661d0310bd58740c43b541d0310cfd5240c433c5490310ed90640c433e5450310cf55140c42f76150310bd18540c43b54150310cfd5040c433c5410310b798c40c42dd6310310bb98840c42ed6210310bd98440c42f56110310ed90440c435e53cc310d754f30c42f661cc310bd58730c43d531cc310d7d4e30c435c538c310f58c630c435e534c310d754d30c42f7614c310bd18530c43d5314c310af99030c42bd640c310d7d4c30c435c530c310bb98830c42ed620c310bd98430c42f5610c310f58c430c436e52c8310db54b20c42f661c8310bd58720c43e521c8310dbd4a20c436c5288310f988620c436e5248310db54920c42f76148310bd18520c43e52148310af99020c42bd6408310b798c20c42dd6308310dbd4820c436c5208310bd98420c42f56108310f988420c427e63d52109f58f548427e62d52109f58b548437561d5210de983548433f54952109f98e548427d63952109f98a548427d6295210cfd91548427f63552109f18d548427f62552109f189548433d5415210b798c54842dd6315210bb98854842ed6215210cf990548427e6315210d798c548425e63152109f58c548435d63152109758c548427e6215210db988548426e62152109f588548436d62152109b58854843756115210de980548427e64d4e109f593538427e62d4e109f58b538437561d4e10de983538435f5394e109f992538427d6494e109f98a538427d6294e109fd91538427c6454e10d7d8d538427f6254e109f18953842be6414e10af590538435d5314e10bb98853842ed6214e109f990538433e6414e108f990538427d6414e10cf590538423d6414e10d798c538427e6214e10db988538426e6214e109f588538436d6214e109b58853843756114e10de980538427f65d0e109f997438427d65d0e109f197438433e54d0e10cf553438427f6590e109f996438427d6590e109f196438435e5390e
  | 10 => 0x3c427d6294f10db58a53c426d6294f10dd98653c427f6454f109f19153c435f6354f109fd8953c427c6254f10d754c53c427e6414f109f59053c435e6314f109f98853c427d6214f10dd98453c43796014f109fd9743c427e65d0f109f59743c427c65d0f10cfd5343c433c54d0f10bd98743c42f561d0f109fd9643c427e6590f109f59643c427c6590f10d7d4e43c435c5390f10bd98643c42f56190f109fd9543c427e6550f109f59543c427c6550f10cfd5143c433c5450f10d7d4d43c435c5350f109fd9443c427e6510f109f59443c427c6510f10e750c43c42ee6210f10bb58843c42f66110f10bd58443c427e64d4b109f59352c427e63d4b109f58f52c437661d4b10de58352c42be6494b10af59252c42de6394b10b758e52c436f5294b109f99252c433e6494b108f99252c427d6494b10cf59252c423d6494b109f98e52c435e6394b109798e52c427d6394b10d758e52c425d6394b10dd98652c427f6454b109f19152c427f6354b109f18d52c436f6254b10db54852c427e6414b109f59052c427e6314b109f58c52c436e6214b10dd98452c43796014b109fd9742c427e65d0b109f59742c427c65d0b10cfd5342c433c54d0b10bd98742c42f561d0b109fd9642c427e6590b109f59642c427c6590b10dbd4a42c436c5290b10bd98642c42f56190b109fd9542c427e6550b109f59542c427c6550b10cfd5142c433c5450b10dbd4942c436c5250b109fd9442c427e6510b109f59442c427c6510b10b798c42c42dd6310b10eb50842c42f66110b10bd58442c427f65ccb109f99732c427d65ccb109f19732c435f53ccb10d714f32c42f661ccb10bd58732c427f658cb109f99632c427d658cb109f19632c436f528cb10db14a32c42f6618cb10bd58632c427f654cb109f99532c427d654cb109f19532c435f534cb10d714d32c436f524cb10db14932c427f650cb109f99432c427d650cb109f19432c42be640cb10af59032c43cd320cb10bd98432c42f5610cb10cfd5341c433c54d0710b798f41c42dd63d0710bb98b41c42ed62d0710cf95241c433d5490710be98241c42f96090710dd59641c43765490710ed95241c43b55490710dd15241c42f56390710edd0e41c43b54390710bd58a41c43b74290710ed50a41c42f66090710fc98241c43f16090710cfd5141c433c5450710bdd9541c43776550710edd9141c43b75450710dd95141c43745450710ed15141c42f76350710bdd8941c42f46050710cf95041c433d5410710ed50441c42fa6010710be58041c42be64cc710af59331c435f53cc710d714f31c42ee62cc710bb58b31c435e538c710d754e31c42fa608c710be58231c4375658c710bdd9231c42f5648c710dd94e31c43d6538c710f554e31c4374538c710f590e31c43d5438c710bd58a31c43d7328c710f5
  | 11 => 0x3e54d0020cf553400835e53d0020d754f400837651d0020dd547400827f65900209f596400833e5490020cf552400835e5390020d754e40082ee6290020bb58a40083765190020dd546400827f6550020cf951400833d5450020d794d400835d5350020dd945400837551500209fd94400827e65100209f594400827c6510020cf950400833d5410020b798c40082dd6310020d794c400835d5310020bb98840082ed6210020bd98440082f56110020dd944400837551100209f597300833e54cc020cf553300835e53cc020d754f300837651cc020dd547300827f658c0209f596300833e548c020cf552300835e538c020d754e30082ee628c020bb58a3008376518c020dd546300827f654c020cf951300833d544c020d794d300835d534c020dd9453008375514c0209fd94300827e650c0209f594300827c650c020af99030082bd640c020cf950300833d540c020d794c300835d530c020bb98830082ed620c020bd98430082f5610c020dd9443008375510c020cf953200833d54c8020d794f200835d53c8020dd947200837551c8020dbd5320083ae54c8020db55320083ad54c8020cb553200836f53c8020f394f200836d53c8020f354f200834d53c8020bb98720083e651c8020db54720083e551c8020d9547200833e5488020cf552200835e5388020d754e20082ed6288020db94a20083765188020dd54620083ba5488020ee55220083da5388020f654e20082f96288020de94a20083ea5288020fc94620083f15188020fa88620083e821880209fd95200833e5448020cf551200835e5348020d754d20083765148020dd54520082ef6548020dbd95200826f6548020dbd5120083ae5448020db55120083ad5448020cb551200836f5348020f394d200836d5348020f354d200834d5348020bb18520083e65148020db54520083e55148020d954520082ef6048020db94120082fb6548020ded95200827b6548020ee95120083b95448020f694d20083d95348020bed8920083eb6248020de94920083ea5248020fc94520083f151480209f98f54c427d63d53109f98b54c427d62d5310dd98754c437960d5310cfd5254c42de6395310b758e54c42ee6295310bb58a54c427e6395310d798e54c425e63953109f58e54c435d63953109758e54c427e6295310db98a54c426e62953109f58a54c436d62953109b58a54c43766195310cfd9154c427f63553109f18d54c427f62553109f18954c433d5415310cf99054c427e63153109f58c54c427e62153109f58854c43766115310de58054c427e64d4f109f59353c427e62d4f109f58b53c437661d4f10de58353c42be6494f10af59253c435f5394f10bb98a53c42ed6294f109f99253c433e6494f108f99253c427d6494f10cf59253c423d6494f109f98a53c436e6294f109b98a5
  | 12 => 0x54420ddd9551083775454420dd95151083b65454420cd95151083755454420ed55151083355454420dd15151083775354420dd94d51083d65354420d594d51083755354420f554d51083555354420dd14d51083e46254420ddd9151083766454420dd59151083746454420ddd8d51083766354420dd58d51083746354420ddd0d51083764354420dd50d51083744354420dd98951083774254420dd90951083754254420dd10951083773254420dd8c951083753254420dd0c951083766054420dd18151083742054420af99051082bd6414420cf950510833d5414420b798c51082dd6314420d794c510835d5314420bd984510837551144209fd97410827e65d04209f597410833e54d0420cf55341082de63d0420b758f410835e53d0420d754f41082ee62d0420bb58b410837651d0420dd547410827f65904209f996410827d6590420cf952410833d5490420d794e410835d5390420dd946410837551904209fd95410827d65504209f195410833e5450420cf551410835e5350420d754d41082ef6250420bb18941083765150420dd545410827f65104209f994410827d6510420cf950410833d5410420d794c410835d5310420dd944410837551104209fd97310827e65cc4209f59731082be64cc420af593310833e54cc420cf553310835e53cc420d754f31082ee62cc420bb58b310837651cc420dd547310827f658c4209f996310827d658c420cf952310833d548c420d794e310835d538c420dd9463108375518c4209fd95310827d654c4209f195310833e544c420cf551310835e534c420d754d31082ef624c420bb1893108376514c420dd545310827f650c4209f994310827d650c420cf950310833d540c420d794c310835d530c420dd9443108375510c420af99321082bd64c8420cf953210833d54c8420b798f21082dd63c8420d794f210835d53c8420db94b210837651c8420dd54721082fa60c8420be583210827d6588420cf952210833d5488420d794e210835d5388420dd54621082ed6588420db596210826d6588420dbd5221083ae5488420db55221083ad5488420cb552210836f5388420f394e210836d5388420f354e210834d5388420bb98621083e65188420db54621083e55188420d954621082ed60884209fd95210833e5448420cf551210835e5348420d754d210836e5248420dd945210833e5408420cf550210835e5308420d754c21083765108420dd54421082fa6008420be580210836f5408420eb950210836d5408420eb550210832d5408420dbd4c21083ce5308420db54c21083cd5308420d354c21082ee6108420f998421083e65108420db54421083e55108420d954421083ea6008420bb58021083e960084209f992500827d64940209f98e500827d6394020db886500836c21940209f59740083
  | 13 => 0xd7951530839e5454c20c7951530835d5454c20e7551530831d5454c20d7151530835f6454c20d7991530835d6454c20d7191530835e6254c20d7189530835f6154c20d7985530835d6154c20d7185530835e6054c20d7181530835c2054c20af99053082bd6414c20cf950530833d5414c20b798c530835d5314c20bd98453082f56114c209f990530833e6414c208f990530827d6414c20cf590530823d6414c209f98c530835e6314c209798c530827e6214c20db988530826e6214c209f98453083766114c209d984530827d6114c20dd58453082756114c209f980530837a6014c209fd97430827e65d0c209f597430827c65d0c20cf953430833d54d0c20d794f430835d53d0c209fd96430827e6590c209f596430827c6590c20cf952430833d5490c20d794e430835d5390c209fd95430827e6550c209f595430827c6550c20cf951430833d5450c20d794d430835d5350c20bbd8943082ec6250c209fd94430827e6510c209f594430827c6510c20cf950430833d5410c20d794c430835d5310c20e750c43082ee6210c20bb588430827e64948209f592520827e63948209f58e520827d65d0820cf953420833d54d0820d794f420835d53d08209fd96420827d6590820cf952420833d5490820d794e420835d5390820db94a42082fa6090820be582420827f6550820cf951420833d5450820d794d420835d5350820db949420827f65108209f594420833e5410820cf55042082de6310820b758c420835e5310820d754c42083ad4210820be98042082f960108209f597320833e54cc820cf553320835e53cc820d754f320827f658c8209f596320833e548c820cf552320835e538c820d754e320836e528c820be98232082f9608c8209fd95320833e544c820cf551320835e534c820d754d320836e524c8209fd94320827d650c820af99032082bd640c820cf950320833d540c820d794c320835d530c820f34c832082fa600c820be58032082be64d4420af593510833e54d4420cf55351082de63d4420b758f510835e53d4420d754f510833e5494420cf552510835e5394420d754e510837751944209f992510827d64944209f98e510827d6394420ddd5251083765494420ed95251083365494420dd55251083b55494420cd55251083745494420ddd4e51083765394420f594e51083565394420dd54e51083d55394420d554e51083745394420f918a51083776494420dd99251083756494420dd19251083776394420dd98e51083756394420dd18e51083774394420dd90e51083754394420dd10e51083746294420ddd0a51083764294420dd50a51083744294420ddcca51083763294420dd4ca51083743294420dd98251083746094420cf951510833d5454420d794d510835d53544209fd91510827c64544209fd8d510827c63
  | 14 => 0x8d21483e76148520f9d45214836c5148520f914521483eb6048520bb18121483e860485209f99421482ee6208520f9484214827e65d0120cfd53404833c54d0120bb98b40482ed62d0120eb50b404827e65901209fd95404827d65501209f195404833f5450120cf15140482ef6250120bb18940483ad42501209f99440482de6310120b758c40482ee6210120bb58840482f66110120bd584404827e65cc120d7d4f304835c53cc120bb98b30482ed62cc120f34cb304827e658c1209fd95304827d654c1209f195304835f534c120d714d30482ef624c120bb18930483cd324c1209f99430482be640c120af59030482ee620c120bb58830482f6610c120bd58430483ea42c8120fa50b20483ea32c8120fa4cb20483eb21c8120fa48720482ef6488120bb59220482ef6388120bb58e20482ed6188120db14620483eb5088120b798f54082dd63d5020bd98754082f561d50209f98f540835e63d50209798f540827d63d5020d758f540825d63d50209f98b540836e62d50209f987540837661d50209d987540827d61d5020dd587540827561d50209f983540837a60d50209f596540833f54950209f98e540827d63950209f986540827d61950208f596540833f6395020cf98e540833d6395020cf18e540833e6295020cf18a540833f6195020cf986540833d6195020cf186540833e6095020cf182540833f64550209fd8d540827c63550209fd89540827d62550209fd85540827c6155020cfd95540833f6355020cf98d540833d6355020cf18d540833e6255020cf189540833f6155020cf985540833d6155020cf185540833e6055020cf181540833c2055020af990540833d5415020b798c54082dd6315020bd98454082f561150209f990540833e64150208f990540827e6315020d798c540825e63150209f58c540835d63150209758c540827e6215020db988540826e62150209f984540837661150209d984540827d6115020dd584540827561150209f980540837a6015020af99353082bd64d4c20cf953530833d54d4c20bd98753082f561d4c209f993530833e64d4c208f993530827d64d4c20cf593530823d64d4c209f98b530836e62d4c209f987530837661d4c209d987530827d61d4c20dd587530827561d4c209f983530837a60d4c209f596530833e5494c20cf552530835f5394c209f992530827d6494c209f986530827d6194c2097596530835f5494c20d7952530839e5494c20c7952530835d5494c20e7552530831d5494c20d7152530835f6494c20d7992530835d6494c20d7192530835e6294c20d718a530835f6194c20d7986530835d6194c20d7186530835e6094c20d7182530833e5454c20cf551530827f6454c209f191530835f6354c209fd89530827d6254c209fd85530827c6154c20d7d95530835f5454c2
  | 15 => 0x4835e5350d20d754d434827f6510d209f994434827d6510d209f194434833f5410d20cf150434835f5310d20d714c434839d4310d20bb98843482ed6210d209f997424833f54d0920cf15342482fa60d0920be583424827e6590920bb996424836e6590920bb592424836e5490920db15242482ed6390920dbd4e424836d5390920bb58642482ee60909209f195424833f5450920cf15142482fb6050920be181424836c65509209b19542483af6450920ebd51424836e5450920db15142483ac5450920cb15142482ef6350920dbd4d424836d5350920ebd0d42483ad4350920bbd8542483eb6050920bb18142483e860509209f99442482de6310920b758c42482ee6210920eb508424827e65cc920d7d4f324835c53cc920be98332482f960cc9209f99632482ee658c920db99632482ef648c920bb592324836f548c920db55232482ed638c920db94e324836c538c920bb58632482ee608c9209f195324835f534c920d714d32482fb604c920be181324836c654c9209b19532482ef644c920bb591324836f544c920db55132483cf634c920f3d4d324836e534c920db14d32483cc534c920d314d32483ce434c920f350d32482ef614c920fad8132482ec604c920fa181324827e650c920af99032482bd640c920bb98832483cd320c9209f993514827d64d45209f98f514827d63d4520ddd4651482bf6454520af19151482df6354520b718d514837551145209f990514827d64145209f98c514827d6314520db908514836d4214520db8c8514836d32145209f997414827d65d05209f19741482de63d0520b758f41482ee62d0520bb58b414837751d0520dd147414827e65905209f596414827c6590520cfd52414833c5490520bb98a41482ed6290520eb50a414827f65505209f995414827c65505209f994414827d65105209f194414833f5410520cf15041482ee6210520bb58841483ad4210520ddd4441483745110520be98041482f960105209f997314827d65cc5209f19731482be64cc520af59331482ee62cc520bb58b314837751cc520dd147314827e658c5209f596314827c658c520d7d4e314835c538c520bb98a31482ed628c520f34ca314827f654c5209f995314827c654c5209f994314827d650c5209f194314835f530c520d714c31482ee620c520bb58831483cd320c520ddd443148374510c520be98031482f9600c5209f99721482be64c8520af59321482de63c8520b758f21482ee65c8520db997214826e65c8520bbd9321483ae64c8520bb59321483ad64c8520ab59321482ef63c8520f398f21482ed63c8520f358f21482cd63c8520db14721482ee60c8520bb58a21483775188520dd14621482fa6088520be58221483775148520dd14521482fb6048520be18121482ef6448520bb59121482ef6348520bb5
  | 16 => 0xd654c6209f195318835e534c620d754d31882ef624c620bb1893188376514c620dd545318827f650c6209f994318827d650c620d7d4c318835c530c620be98031882f9600c620af99321882bd64c8620b798f21882dd63c8620dd94621883755188620be98221882f96088620dbd52218836d5488620dbd4e218836d5388620f9946218836d5188620f954621883ea6088620bb58221883e96088620dd94521883755148620bed8121882f86048620bb594218836d6508620dbd50218836d5408620dbd4c218836d5308620f9984218836d5108620bb580218833f54d0220cf153408833e5490220cf55240882ee6290220bb58a408833f5450220cf151408833e5410220cf55040882de6310220b758c40882ee6210220bb58840882f66110220bd584408835f53cc220d714f308835e538c220d754e30882ee628c220bb58a308835f534c220d714d30882be640c220af590308835e530c220d754c30882ee620c220bb58830882f6610c220bd58430882ed65c8220db597208836f54c8220db553208836f53c8220db54f20882ee61c8220db54720882f965c8220de597208827e63d51209f58f544827e61d51209f587544833f54951209f992544827e63951209f58e544827d6295120db58a544827e61951209f586544827d6095120de58254482df6355120b718d54482f76155120bd185544833f64551209fd8d544835f635512097d8d544827c6355120d718d544825c63551209fd89544836f62551209fd85544837761551209dd85544827c6155120dd185544827461551209fd81544837b60551209f994544833d5415120b798c54482dd6315120cf990544827e6315120d798c544825e63151209f58c544835d63151209758c544827e6215120db588544827c62151209f984544827d61151209f993534827d64d4d209f987534827d61d4d20d7d4e534827e6494d209f592534827e6394d209f58a534836d6294d209f986534827d6194d209f58253483796094d20afd9153482bc6454d20bdd8553482f46154d209fd91534833f6454d208fd91534827c6454d20cf191534823c6454d20d7d8d534827f6254d20dbd89534827f6154d20ddd8553482776154d209f18553483746154d209d185534827f6054d20ded81534827e6514d20af99053482bd6414d20d754c534827e6414d20cf990534823e6414d209f590534833d6414d208f590534835e6314d209f988534836d6214d209f188534827e6114d209f584534827f65d0d209f997434827d65d0d209f197434833e54d0d20cf553434835f53d0d20d714f43482ee62d0d20bb58b434827f6590d209f996434827d6590d209f196434833f5490d20cf152434835e5390d20d754e43482ee6290d20bb58a434827f6550d209f995434827d6550d209f195434833e5450d20cf55143
  | 17 => 0x320bd58440c835e53cc320d754f30c82ee62cc320bb58b30c83cd32cc320d794d30c835d534c320bbd8930c82ec624c320f34c930c82be640c320af59030c82ee620c320bb58830c82f6610c320bd58430c827e63d52209f58f548836d62d52209f987548827d61d5220de983548833f54952209f98e548827d63952209f986548827d6195220cfd91548827f63552209f18d548827f61552209f185548833d5415220b798c54882dd6315220bd98454882f56115220cf990548827e6315220d798c548825e63152209f58c548835d63152209758c548836d62152209f984548837661152209d984548827d6115220dd58454882756115220de980548827e64d4e209f593538836d62d4e209f987538827d61d4e20de983538835f5394e209f992538827d6494e209f986538827d6194e209fd91538827c6454e20d7d8d538827f6154e209f18553882be6414e20af590538835d5314e20bd98453882f56114e209f990538833e6414e208f990538827d6414e20cf590538823d6414e20d798c538836d6214e209f98453883766114e209d984538827d6114e20dd58453882756114e20de980538827f65d0e209f997438827d65d0e209f197438833e54d0e20cf553438827f6590e209f996438827d6590e209f196438835e5390e20d754e438827f6550e209f995438827d6550e209f195438833e5450e20cf551438835e5350e20d754d43882ef6250e20bb189438827f6510e209f994438827d6510e209f194438839d4310e20bb98843882ed6210e20cf953428833d54d0a20be98342882f960d0a20cf951428833d5450a20bed8142882f86050a20b798c42882dd6310a20eb508428835e53cca20d754f32882fa60cca20be583328835e534ca20d754d32882fb604ca20be18132882be640ca20af59032883cd320ca20ddd46518827e64946209f592518827e63946209f58e51882bf6454620af19151882df6354620b718d518827f6454620cfd91518823f64546209f191518833c64546208f191518827f6354620d7d8d518825f63546209f18d518835c63546209718d51882be6414620af59051882de6314620b758c518837551146209fd97418827e65d06209f597418833e54d0620cf55341882de63d0620b758f41882ee62d0620bb58b418827f65906209f996418827d6590620cfd52418833c5490620dd946418837551906209fd95418827d65506209f195418833e5450620cf55141882ef6250620bb18941883765150620dd545418827f65106209f994418827d6510620cfd50418833c5410620be98041882f960106209fd97318827e65cc6209f59731882be64cc620af593318835e53cc620d754f31882ee62cc620bb58b318827f658c6209f996318827d658c620d7d4e318835c538c620dd9463188375518c6209fd95318827
  | 18 => 0x9f59443c827c6510f20e750c43c82ee6210f20bb58843c833f54d0b20cf15342c833e5490b20cf55242c82fa6090b20be58242c836d6590b20db95242c83ae5490b20eb55242c836c5490b20bb58e42c836f5390b20db54e42c82ed6190b20bb98242c83ea6090b20fa58242c833f5450b20cf15142c82ef6550b20dbd9542c83af6450b20ebd5142c836e5450b20db15142c83ac5450b20cb15142c82ef6350b20dbd4d42c836d5350b20ebd0d42c83ad4350b20bbd8542c82ec6050b20cf95042c833d5410b20b798c42c82dd6310b20eb50842c82fa6010b20be58042c835f53ccb20d714f32c835e538cb20d754e32c82fa608cb20be58232c836d658cb20bbd9232c82ed648cb20dbd5232c836d548cb20db94e32c83ce538cb20f354e32c836c538cb20bb58632c82ee608cb20fa98232c83e9608cb20d7d4d32c835c534cb20bbd9532c836f654cb20bbd9132c82ed644cb20dbd5132c836d544cb20f3d8d32c83cf534cb20db94d32c836c534cb20f314d32c834c534cb20f390d32c83cd434cb20bbd8532c82ec604cb20af99032c82bd640cb20d794c32c835d530cb20f34c832c82fa600cb20be58032c82be64d4720af59351c82de63d4720b758f51c837751947209f99251c827d64947209f98e51c827d6394720db90a51c836d4294720db8ca51c836d32947209fd9151c827c64547209fd8d51c827c6354720dd54451c827f65d07209f99741c827d65d0720b798f41c82dd63d0720bb98b41c82ed62d07209fd9641c827e65907209f59641c833e5490720cf55241c82ee6290720bb58a41c83ad42907209fd9541c827d65507209f19541c827f65107209f99441c827d6510720cf95041c833d5410720bb98841c82ed6210720eb50841c827f65cc7209f99731c827d65cc720af99331c82bd64cc720bb98b31c82ed62cc7209fd9631c827e658c7209f59631c835e538c720d754e31c82ee628c720bb58a31c83cd328c7209fd9531c827d654c7209f19531c827f650c7209f99431c827d650c720d794c31c835d530c720bb98831c82ed620c720f34c831c82be64c8720af59321c82de63c8720b758f21c837651c8720dd54721c82fa60c8720be58321c82ef64c8720eb99321c82ed64c8720eb59321c82ad64c8720bbd8f21c83ce63c8720bb58f21c83cd63c8720b358f21c836e51c8720f994721c83e551c8720bb98321c83ea60c8720fa58321c82ef6548720dbd9521c82ef6448720bb59121c82ef6348720bb58d21c83e76148720f9d4521c836e5148720f914521c82ec6048720dd94421c83755108720f948421c82fa6008720be58021c833e54d0320cf55340c82ee62d0320bb58b40c83ad42d0320cf95140c833d5450320bbd8940c82ec6250320eb50940c82de6310320b758c40c82ee6210320bb58840c82f6611
  | 19 => 0x210c33d5408430db948210c36d5208430dd944210c37551084309f992500c27d6494030d78c6500c35c31940309f597400c33e54d0030cf553400c36e52d0030db54b400c37651d0030dd547400c27f65900309f596400c33e5490030cf552400c2de6390030b758e400c36e5290030db54a400c3765190030dd546400c27f6550030cf951400c33d5450030db949400c36d5250030dd945400c37551500309fd94400c27e65100309f594400c27c6510030cf950400c33d5410030b798c400c2dd6310030bb988400c2ed6210030db948400c36d5210030bd984400c2f56110030dd944400c3755110030cf953300c33d54cc030db94b300c36d52cc030dd947300c37551cc030d7d53300c39e54cc030d7553300c39d54cc030c7553300c3ce52cc030d754b300c3cd52cc030d354b300c2de61cc030f5947300c35d51cc030f5547300c35551cc030cf952300c33d548c030b758e300c35e538c030db94a300c36d528c030dd946300c375518c030ee952300c3b9548c030be58e300c37a538c030f694e300c3ea528c030fa54a300c3f2518c030fc546300c3da318c030f60c6300c27f654c030cf951300c33d544c030db949300c36d524c030dd945300c375514c030b7d95300c35f654c03097d95300c35f544c030e7951300c35d544c030e7551300c31d544c030f3949300c35d524c030f3549300c34d524c030b7185300c3d6514c030d7545300c3d5514c030d5545300c2df604c030d7941300c2fb654c030ded95300c27b654c030ee951300c3b9544c030bed8d300c3db634c030de94d300c3da534c030fa949300c3e9524c030fc945300c3f1514c0309f98f54c827d63d5320db98b54c827e61d53209f58754c837960d5320cfd5254c827e63953209f58e54c836e62953209f98654c827d6195320cfd9154c827f63553209f18d54c827f61553209f18554c833d5415320b798c54c82dd6315320cf99054c827e6315320d798c54c825e63153209f58c54c835d63153209758c54c836e62153209f98454c827d6115320de58054c827e64d4f209f59353c836e62d4f209f98753c827d61d4f20de58353c835f5394f209f99253c827d6494f20db98a53c827e6194f209f58653c827f6454f209f19153c835f6354f209fd8553c827c6154f20af99053c82bd6414f20d754c53c827e6414f20cf99053c823e6414f209f59053c833d6414f208f59053c835e6314f20db98853c827e6114f209f58453c83796014f209fd9743c827e65d0f209f59743c827c65d0f20cf95343c833d54d0f20bb98b43c82ed62d0f209fd9643c827e6590f209f59643c827c6590f20d794e43c835d5390f20bb98a43c82ed6290f209fd9543c827e6550f209f59543c827c6550f20cf95143c833d5450f20d794d43c835d5350f209fd9443c827e6510f20
  | 20 => 0xc3744294430ddcca510c3763294430dd4ca510c3743294430dd982510c3746094430cf951510c33d5454430db949510c36d52544309fd91510c27c64544309fd89510c27c6254430ddd95510c3775454430dd951510c3b65454430cd951510c3755454430ed551510c3355454430dd151510c3d46354430ddd49510c3765254430f9949510c3665254430dd549510c3e55254430d9549510c3745254430ddd91510c3766454430dd591510c3746454430dd98d510c3774354430dd90d510c3754354430dd10d510c3776254430dd989510c3756254430dd189510c3774254430dd909510c3754254430dd109510c3773254430dd8c9510c3753254430dd0c9510c3766054430dd181510c3743054430af990510c2bd6414430cf950510c33d5414430bb988510c2ed6214430db948510c36d5214430bd984510c37551144309fd97410c27e65d04309f597410c33e54d0430cf553410c2de63d0430b758f410c2ee62d0430bb58b410c36e52d0430db54b410c37651d0430dd547410c27f65904309f996410c27d6590430cf952410c33d5490430db94a410c36d5290430dd946410c37551904309fd95410c27d65504309f195410c33e5450430cf551410c2df6350430b718d410c36e5250430db549410c3765150430dd545410c27f65104309f994410c27d6510430cf950410c33d5410430db948410c36d5210430dd944410c3755110430af993310c2bd64cc430cf953310c33d54cc430d794f310c2ee62cc430bb58b310c36e52cc430db54b310c37651cc430dd547310c2fa60cc430be583310c27d658c430cf952310c33d548c430db94a310c36d528c430dd546310c2dd658c430d7596310c25d658c430d7d52310c39e548c430d7552310c39d548c430c7552310c3ce528c430d754a310c3cd528c430d354a310c2de618c430f5946310c35d518c430f5546310c355518c430b7582310c27f654c430cf951310c33d544c430d794d310c36e524c430db549310c376514c430cf950310c33d540c430db948310c36d520c430dd944310c375510c430be980310c2f9600c430d7d50310c39e540c430d7550310c39d540c430c7550310c3ce520c430d7548310c3cd520c430d3548310c2de610c430f5984310c3d6510c430d7544310c3d5510c430d5544310c3da600c430b7580310c3d9600c4309fd97210c27e65c84309f597210c2be64c8430af593210c33e54c8430cf553210c2de63c8430b758f210c36e52c8430db54b210c37651c8430dd547210c27f65884309f996210c27d6588430cf952210c33d5488430db94a210c36d5288430dd946210c37551884309fd95210c27d65484309f195210c33e5448430cf551210c2df6348430b718d210c36e5248430db549210c3765148430dd545210c27f65084309f994210c27d6508430cf95
  | 21 => 0x6115030dd984540c27661150309f584540c37561150309d584540c27e6015030de980540c27e6494c309f592530c27d65d0c30cf953430c33d54d0c309fd96430c27d6590c30cf952430c33d5490c30d794e430c2fa6090c30be582430c27f6550c30cf951430c33d5450c30d794d430c27f6510c309f594430c33e5410c30cf550430c39d4310c30bb988430c2ed6210c30be980430c2f96010c30af993520c2bd64d4830cf953520c33d54d4830bd987520c2f561d4830cf952520c33d5494830dbd4a520c27e64948309f592520c27e61948309f586520c36f5494830db952520c3ae5494830cb952520c36d5494830eb552520c32d5494830db152520c36f6494830db992520c36d6494830db192520c36c6394830dbd0e520c36e4394830db50e520c36c4394830dbd86520c36e6194830db586520c36c6194830db982520c36c6094830cf951520c33d54548309fd91520c27c64548309fd85520c27c6154830dbd95520c36f5454830db951520c3ae5454830cb951520c36d5454830eb551520c32d5454830db151520c36f6454830db991520c36d6454830db191520c36e6354830dbd0d520c36e4354830db50d520c36c4354830dbd85520c36e6154830db585520c36c6154830db981520c36c6054830db0c1520c2be6414830af590520c33e5414830cf550520c2ee6214830db548520c2f66114830bd584520c27f65d08309f997420c27d65d0830cf953420c33d54d0830db94b420c36d52d08309fd96420c27e65908309f596420c33e5490830cf552420c36e5290830db54a420c27f65508309f595420c27c6550830cf951420c33d5450830b7d8d420c2dc6350830db949420c36d52508309fd94420c27e65108309f594420c33e5410830cf550420c2de6310830b758c420c36e5210830db548420c3ad4210830cf953320c33d54cc830d794f320c36e52cc830db54b320c2fa60cc830be583320c27d658c830cf952320c33d548c830db54a320c27f654c830cf951320c33d544c830d794d320c36e524c830af990320c2bd640c830cf950320c33d540c830db948320c36d520c830f34c8320c2fa600c830be580320c2be64d4430af593510c33e54d4430cf553510c2ee62d4430bb58b510c36e52d4430db54b510c33e5494430cf552510c36e5294430db54a510c37751944309f992510c27d64944309f98a510c27d6294430ddd52510c3765494430ed952510c3365494430dd552510c3b55494430cd552510c3745494430f518e510c3775294430dd94a510c3e65294430d994a510c3755294430f954a510c3655294430dd14a510c3776494430dd992510c3756494430dd192510c3746394430ddd0e510c3764394430dd50e510c3744394430ddd8a510c3766294430dd58a510c3746294430ddd0a510c3764294430dd50a510
  | 22 => 0x530b758f414c2ee62d0530bb58b414c37751d0530dd147414c27e65905309f596414c27c6590530cfd52414c33c5490530b798e414c2dd6390530e750e414c27f65505309f995414c27c65505309f994414c27d65105309f194414c33f5410530cf150414c2de6310530b758c414c39d4310530ddd44414c3745110530be980414c2f960105309f997314c2be64cc530af593314c2ee62cc530bb58b314c2de65cc530d7997314c25e65cc530b7d93314c39e64cc530b7593314c39d64cc530a7593314c3ce62cc530b758b314c3cd62cc530b358b314c35c51cc530b7983314c2dd638c530ddd46314c374518c530be982314c2f9608c530ddd45314c374514c530bed81314c2f8604c530b7d91314c2dd644c530b7d89314c3d7614c530f5d45314c35c514c530f5145314c3db604c530b7181314c3d8604c5309f994314c2de630c530f54c4314c27e65c85309f597214c27c65c8530af993214c2bd64c8530b798f214c2dd63c8530ddd47214c37451c85309f996214c27d65885309f196214c2de6388530b758e214c36f5288530db14a214c3cd32885309fd95214c27e65485309f195214c2de6348530b758d214c27e65085309f594214c27c6508530b798c214c2dd6308530dbd48214c36c5208530f34c8214c3775108530dd144214c2fa6008530be580214c27e65d0130cfd53404c33c54d0130b798f404c2dd63d0130e750f404c27e65901309fd95404c27d65501309f195404c33f5450130cf151404c2df6350130b718d404c39d43501309f994404c2de6310130b758c404c2ee6210130bb588404c2f66110130bd584404c3da43cc130f650f304c3db32cc130f64cb304c3db31cc130f64c7304c2df648c130b7592304c2dd628c130b7586304c35c518c130f6d42304c2ee62d5030bb58b540c2f661d5030bd587540c27e63d5030d798f540c27e62d5030db98b540c26e62d50309f58b540c36d62d50309b58b540c27e61d5030dd987540c27661d50309f587540c37561d50309d587540c27e60d5030de983540c27d6595030cfd52540c27e62950309f58a540c27e61950309f586540c23d6595030cf98e540c33c6395030cfd8a540c33e6295030cf58a540c33c6295030cfd86540c33e6195030cf586540c33c6195030cf982540c33c6095030cfd91540c27f63550309f58d540c27f62550309f189540c27f61550309f185540c33f6555030cf98d540c33c6355030cfd89540c33e6255030cf589540c33c6255030cfd85540c33e6155030cf585540c33c6155030cf981540c33c6055030cf0c1540c2be6415030cf550540c2ee6215030bb588540c2f66115030bd584540c27e6415030cf990540c23e64150309f98c540c35e63150309798c540c27e6215030db988540c26e62150309f588540c36d62150309b588540c27e
  | 23 => 0xb588408c2f66110230bd584408c2dd65cc230d7597308c35f54cc230d7553308c35d52cc230b7987308c35d51cc230be597308c37965cc2309f98b544c27d62d51309f987544c27d61d5130cfd52544c27e64951309f58e544c35d63951309f98a544c27d62951309f986544c27d61951309f582544c3796095130bbd89544c2ec6255130bdd85544c2f46155130cfd91544c27f6355130d7d8d544c27f6255130dbd89544c26f62551309f189544c36c62551309b189544c27f6155130ddd85544c27761551309f185544c37461551309d185544c27f6055130ded81544c27e6515130cf550544c2ee6215130bb588544c33e64151309f98c544c35d63151309f18c544c27e6215130db988544c26e62151309f588544c36d62151309b588544c27e61151309f584544c27e65d0d30cfd53434c33c54d0d30be983434c2f960d0d309f996434c2de6590d30d7996434c2dd6490d30d7952434c35c5490d30b758a434c2dd6190d30b7982434c27c6550d30cfd51434c33c5450d30bed81434c2f86050d30d7195434c25c6550d30e7d91434c39f5450d30d7951434c35c5450d30e7151434c31c5450d30b7d89434c2df6150d30f6d81434c2dc6050d30f6181434c27e6510d30b798c434c39d4310d30bb988434c2ed6210d309f993524c27d64d4930d790f524c35d43d49309f987524c27d61d4930dbd4a524c2bf6454930af191524c2f76154930bd185524c2be6414930af590524c36d52149309f990524c33e64149308f990524c27d6414930cf590524c23d64149309f984524c27d61149309f997424c27d65d09309f197424c33e54d0930cf553424c2de63d0930b758f424c39d43d0930dbd4b424c36c52d09309f996424c27d65909309f196424c33f5490930cf152424c2de6390930b758e424c27f65509309f995424c27c6550930cf951424c33d5450930e750d424c27e65109309f594424c27c6510930cfd50424c33c5410930b798c424c2dd6310930dbd48424c36c5210930eb508424c27e65cc930b7997324c35e65cc930b7d93324c2dd64cc930d7d53324c35d54cc930d714b324c2dd61cc930b7983324c2dd638c930dbd4a324c36c528c930be982324c2f9608c930dbd49324c36c524c930bed81324c2f8604c930b7d91324c2dd644c930d7d51324c35d544c930f3d89324c3cf524c930d7149324c3cc524c930d3149324c3ce424c930f3509324c2df614c930f6d81324c2dc604c930f6181324c27e650c930af990324c2bd640c930b798c324c3cd320c9309f993514c27d64d45309f98b514c27d62d4530ddd46514c2bf6454530af191514c2ef6254530bb189514c37551145309f990514c27d6414530d790c514c35d43145309f988514c27d6214530d7cc8514c35d32145309f997414c27d65d05309f197414c2de63d0
  | 24 => 0x548c27d6195230cfd91548c27f62552309f189548c27f61552309f185548c33d5415230bb988548c2ed6215230bd984548c2f56115230cf990548c35d63152309f988548c36e62152309b988548c27d6215230db588548c26d62152309f984548c37661152309d984548c27d6115230dd584548c2756115230de980548c33e54d0e30cf553438c2fa60d0e30be583438c33e5450e30cf551438c2fb6050e30be181438c39d4310e30bb988438c2ed6210e30dbd4a528c27e6494a309f592528c27e6194a309f586528c27f6454a309f191528c27f6154a309f185528c2be6414a30af590528c36d5214a30bd984528c2f56114a309fd97428c27e65d0a309f597428c33e54d0a30cf553428c27f6590a309f996428c27d6590a30db94a428c36d5290a309fd95428c27d6550a309f195428c33e5450a30cf551428c2df6350a30b718d428c36e5250a30db549428c27f6510a309f994428c27d6510a30b798c428c2dd6310a30eb508428c36e528ca30db54a328c2fa608ca30be582328c36e524ca30db549328c2fb604ca30be181328c2be640ca30af590328c3cd320ca30ddd46518c27e64946309f592518c27e62946309f58a518c2bf6454630af191518c2ef6254630bb189518c27f6454630cfd91518c23f64546309f191518c33c64546308f191518c27f6254630dbd89518c26f62546309f189518c36c62546309b189518c2be6414630af590518c2ee6214630bb588518c37551146309fd97418c27e65d06309f597418c33e54d0630cf553418c2de63d0630b758f418c2ee62d0630bb58b418c27f65906309f996418c27d6590630cfd52418c33c5490630dd946418c37551906309fd95418c27d65506309f195418c33e5450630cf551418c2df6350630b718d418c3765150630dd545418c27f65106309f994418c27d6510630cfd50418c33c5410630be980418c2f96010630af993318c2bd64cc630bb98b318c2ed62cc630dd946318c375518c630be982318c2f9608c630d7d52318c35d548c630d754a318c3d6518c630d7546318c3d5518c630f6982318c2dd608c630f6582318c376514c630dd545318c2fb604c630be181318c2dd650c630d7594318c35f540c630d7550318c35d520c630f5984318c35d510c630b7580318c27f65c86309f997218c27d65c8630af993218c2bd64c8630b798f218c2dd63c8630db94b218c36d52c86309fd96218c27e65886309f596218c3765188630dd546218c27f65486309f595218c27c6548630b7d8d218c2dc6348630db949218c36d5248630dd945218c37551486309fd94218c27e65086309f594218c2fa6008630be580218c33f54d0230cf153408c33e5490230cf552408c2de6390230b758e408c33f5450230cf151408c33e5410230cf550408c2de6310230b758c408c2ee6210230b
  | 25 => 0x2f96010f30dbd4a52cc27e6494b309f59252cc27e6194b309f58652cc27f6454b309f19152cc35e4354b30d750d52cc27f6154b309f18552cc2be6414b30af59052cc36d5214b309fd9742cc27e65d0b309f59742cc33e54d0b30cf55342cc2de63d0b30b758f42cc39d43d0b309fd9642cc27e6590b309f59642cc2de6390b30b758e42cc36e5290b30db54a42cc27f6550b309f59542cc27c6550b30cf95142cc33d5450b30e750d42cc36e5250b30db54942cc27f6510b309f99442cc27d6510b30b798c42cc2dd6310b30eb50842cc36e52ccb30db54b32cc2fa60ccb30be58332cc2df64ccb30b759332cc35f54ccb30d755332cc35e52ccb30f394b32cc3cd52ccb30b758732cc2de60ccb30f698332cc3d960ccb30b7d9532cc35f654cb30b7d9132cc2dd644cb30d7d5132cc35d544cb30f3d8932cc3cf524cb30d794932cc3cc524cb30f390932cc3cd424cb30b7d8532cc2dc604cb30af99032cc2bd640cb30db94832cc36d520cb30f34c832cc2fa600cb30be58032cc2be64d4730af59351cc2ee62d4730bb58b51cc37751947309f99251cc27d6494730d790e51cc35d43947309f98a51cc27d6294730d7cca51cc35d32947309fd9151cc27c64547309fd8951cc27c6254730dd54451cc27f65d07309f99741cc27d65d0730b798f41cc2dd63d0730bb98b41cc2ed62d07309fd9641cc27e65907309f59641cc33e5490730cf55241cc2de6390730b758e41cc39d43907309fd9541cc27d65507309f19541cc27f65107309f99441cc27d6510730cf95041cc33d5410730b798c41cc2dd6310730e750c41cc2be64cc730af59331cc2ee62cc730bb58b31cc37651cc730dd54731cc2fa60cc730be58331cc2df64cc730e799331cc2dd64cc730e759331cc29d64cc730f398b31cc2dd62cc730f358b31cc2cd62cc730d794731cc3d651cc730f554731cc2de60cc730f698331cc3d960cc730b7d9531cc35f654c730b7d9131cc2dd644c730b7d8931cc3d7614c730f5d4531cc35e514c730f514531cc2dc604c730dd94431cc375510c730f54c431cc2fa600c730be58031cc27f65c87309f99721cc27d65c8730af99321cc2bd64c8730b798f21cc2dd63c87309fd9621cc27e65887309f59621cc2de6388730b758e21cc36e5288730db54a21cc3cd32887309fd9521cc27d65487309f19521cc2de6348730b758d21cc27f65087309f99421cc27d6508730b798c21cc2dd6308730db94821cc36d5208730f34c821cc33e54d0330cf55340cc2de63d0330b758f40cc39d43d0330cf95140cc33d5450330b7d8d40cc2dc6350330e750d40cc2de6310330b758c40cc2ee6210330bb58840cc2f66110330bd58440cc35d63d52309f98b548c27d62d52309f987548c27d61d5230de983548c33f54952309f98a548c27d62952309f986
  | 26 => 0x1cc4409fd96311027e658c4409f596311035e538c440d754e311036e528c440db54a3110376518c440dd546311027f654c4409f595311027c654c440afd9131102bc644c440d794d311035d534c440db949311036d524c440dd9453110375514c4409fd94311027e650c4409f594311035e530c440d754c311036e520c440db5483110376510c440dd544311027f65c84409f997211027d65c8440af99321102bd64c8440b798f21102dd63c8440d794f211035d53c8440db94b211036d52c8440dd947211037551c84409fd96211027e65884409f596211035e5388440d754e211036e5288440db54a21103765188440dd546211027f65484409f595211027c6548440afd9121102bc6448440d794d211035d5348440db949211036d5248440dd945211037551484409fd94211027e65084409f594211035e5308440d754c211036e5208440db54821103765108440dd544211033e4194040cf106501035e53d0040d754f401036e52d0040db54b401037651d0040dd547401039e53d0040cf54f401039d53d0040c754f40103ae52d0040cf54b40103ad52d0040cb54b40102be61d0040ed947401033d51d0040ed547401033551d0040af592401033e5490040d794e401035d5390040db94a401036d5290040dd94640103755190040be592401037a5490040ee95240103da5390040f654e40103ea5290040fa54a40103f25190040fc54640103ba4190040ee106401027f6550040d794d401035d5350040db949401036d5250040dd94540103755150040afd95401033f65500408fd95401039e5350040cf54d401039d5350040c754d40103ae5250040cf54940103ad5250040cb54940102bc6150040ed945401033d5150040ed54540103355150040afd81401033e5050040bed95401037b65500409ed9540102fb6450040eed91401037a5450040ee95140103da5350040f654d40103ea5250040fa54940103f25150040fc545401035e63d53309f98b54cc27d62d53309f98754cc27d61d5330de58354cc33f5495330d798e54cc27e62953309f58a54cc27e61953309f58654cc33f64553309fd8954cc27c62553309fd8554cc27c6155330cf55054cc2ee6215330bb58854cc33e6415330d798c54cc27e6215330db98854cc26e62153309f58854cc36d62153309b58854cc27e61153309f58454cc3796015330cfd5343cc33c54d0f30cf95243cc33d5490f30be98243cc2f96090f30d759643cc35e5490f30e795243cc39d5490f30d715243cc2dd6290f30b758643cc2de6090f30f698243cc3d96090f30cfd5143cc33c5450f30b7d9543cc35f6550f30e7d9143cc39f5450f30d795143cc35c5450f30e715143cc31c5450f30b7d8943cc2df6150f30b718143cc33e5410f30cf55043cc39d4310f30bb98843cc2ed6210f30be98043cc
  | 27 => 0x409f595321027c654c840afd9132102bc644c840d794d321035d534c840db949321036d524c8409fd94321027e650c8409f59432102be640c840af590321035e530c840d754c321036e520c840db54832103cd320c840b798f51102dd63d4440d794f511035d53d4440bb98b51102ed62d4440db94b511036d52d4440d794e511035d5394440db94a511036d5294440ddd46511027e63944409f58e511027e62944409f58a51103b46494440ddd4e51103765394440f594e51103565394440dd54e51103d55394440d554e51103745394440ddd4a51103765294440f994a51103665294440dd54a51103e55294440d954a51103745294440dd19251103776394440dd98e51103756394440dd18e51103774394440dd90e51103754394440dd10e51103776294440dd98a51103756294440dd18a51103774294440dd90a51103754294440dd10a51103773294440dd8ca51103753294440dd0ca51103766094440dd182511035e5354440d754d511036e5254440db549511027f63544409f18d511027f62544409f18951103776554440ed19151103775354440dd94d51103d65354440d594d51103755354440f554d51103555354440dd14d51103775254440dd94951103e65254440d994951103755254440f954951103655254440dd14951103766454440ddd8d51103766354440dd58d51103746354440ddd0d51103764354440dd50d51103744354440ddd8951103766254440dd58951103746254440ddd0951103764254440dd50951103744254440ddcc951103763254440dd4c951103743254440dd98151103746054440dd10151102de6314440b758c511035e5314440d754c51102ee6214440bb588511036e5214440db54851102f66114440dd544511033e54d0440b798f41102dd63d0440d794f411035d53d0440bb98b41102ed62d0440db94b411036d52d0440dd947411037551d0440be98341102f960d04409f596411035e5390440d754e411036e5290440db54a41103755190440af596411033d65904408f596411039e5390440cf54e411039d5390440c754e41103ae5290440cf54a41103ad5290440cb54a41102be6190440ed946411033d5190440ed54641103355190440af582411027f6550440cf951411035e5350440d754d411036e5250440db54941103765150440d794c411035d5310440db948411036d5210440dd94441103755110440be98041102f96010440e794c411033d5310440e754c411031d5310440eb948411033d5210440eb548411032d5210440af98441103b66110440ed944411033d5110440ed54441103355110440ee98041102bd6010440ee580411027f65cc4409f997311027d65cc440af99331102bd64cc440d794f311035d53cc440bb98b31102ed62cc440db94b311036d52cc440dd94731103755
  | 28 => 0x59321502de63c8540b758f215037751c8540dd147215027e65885409f596215027c6588540af99221502bd6488540dbd4a215036c5288540eb50a215027f65485409f995215027c6548540af99121502bd64485409f994215027d65085409f19421502be6408540af590215036f5208540db14821503ad4208540ddd4421503745108540be98021502f96008540eed0f40503b943d0140eed0b40503b942d0140eed0740503b941d0140af58e40502bd6290140af586405033c5190140eed4240502ee62d4c40bb58b53102f661d4c40bd587531035f5394c409f98a531027d6294c409f986531027d6194c40d7192531035f6294c40d798a531035d6294c40d718a531035f6194c40d7986531035d6194c40d7186531035e6094c40d7182531027f6254c409f189531027f6154c409f185531035f6554c40d7991531035f6254c40d7989531035d6254c40d7189531035f6154c40d7985531035d6154c40d7185531035e6054c40d7181531035c4054c40b798c531035d5314c40bb98853102ed6214c40bd98453102f56114c40cf953431035e53d0c40d754f43102fa60d0c40be583431027d6590c40d754e431027f6550c40cf951431035e5350c40d794c431035d5310c40e750c43102ee6210c40bb58843102fa6010c40be58043102de63d4840b758f521035e53d4840d754f52102f661d4840bd587521035e5394840d754e521036f52948409f98e521027d63948409f986521027d6194840dbd4e521036e5394840f394e521034e5394840db54e52103cd5394840d354e521036c5394840db192521036f6394840db98e521036d6394840db18e521036f4394840db90e521036d4394840db10e521036f6194840db986521036d6194840db186521036e6094840db182521035e5354840d754d521027f63548409f18d521027f61548409f185521036f6554840dbd4d521036e5354840f394d521034e5354840db54d52103cd5354840d354d521036c5354840db991521036f6354840db98d521036d6354840db18d521036f4354840db90d521036d4354840db10d521036f6154840db985521036d6154840db185521036e6054840db181521036c4054840b798c52102dd6314840d794c521035d5314840bb988521036d5214840bd98452102f56114840cf953421035e53d0840d754f421036e52d0840db54b42102fa60d0840be583421027d6590840d794e421035d5390840db54a421027f6550840cf951421035e5350840d754d421036e5250840b798c42102dd6310840d794c421035d5310840db948421036d5210840eb50842102fa6010840be580421027f65cc8409f997321027d65cc840d794f321035d53cc840db94b321036d52cc8409fd96321027e658c8409f596321035e538c840d754e321036e528c840db54a321027f654c8
  | 29 => 0x35027d6114d409f99743502be65d0d40cf997435033c53d0d40af58b43502bd61d0d40af98343502bd6490d40d7d4e435035c5390d40be98243502f96090d40d7d4d435035c5350d40bed8143502f86050d40e7d8d435039f5350d40cf14d435039c5350d40c714d43502bf6250d40afd8543503bb6050d40af18143503b86050d409f99443502be6410d40e750c43502ee6210d40bb588435027e63d49409f58f525033f43d4940cf50f525027e61d49409f587525036f5294940b7d8d52502dc6354940bdd8552502f46154940b798c52502dd6314940db548525027e6314940d798c525025e63149409f58c525035d63149409758c525027e61149409f584525027e65d0940af997425033e65d0940af58f425033f53d0940cf14b42502bd61d0940af98342502bd6490940dbd4a425036c5290940be98242502f96090940dbd49425036c5250940bed8142502f86050940afd8d425033f5350940ebd8942503af5250940cf14942503ac5250940cb14942502bf6150940eed8142502bc6050940ee181425027e6510940af99042502de6310940b758c42503ad42109409f997325027d65cc9409f19732502be64cc940af593325039d43cc940dbd4b325036c52cc9409f996325027d658c9409f19632502be648c940af592325035f538c940d714e32503ad428c9409fd95325027e654c9409f19532502be644c940af591325039d434c940eb509325027e650c9409f594325027c650c940af99032502bd640c940d7d4c325035c530c940dbd48325036c520c940f34c8325027e63d45409f58f515027e62d45409f58b51503775194540b7d8d51502dc6354540bbd8951502ec6254540dd544515027e63145409f58c515033f4314540cf50c515027e62145409f588515033f4214540cf508515027e65d0540b798f41502dd63d0540bb98b41502ed62d0540af997415033e65d05408f997415039e63d0540af58f415039d63d0540a758f41503ae62d0540af58b41503ad62d0540ab58b415033c51d0540af98341502bd6490540ddd4641503745190540be98241502f96090540ddd4541503745150540bed8141502f86050540afd8d41502bf6250540edd8541503b75150540cf14541503b45150540eed8141502bc6050540ee181415027e6510540af99041503b541105409f997315027d65cc5409f19731502be64cc540af59331502ee62cc540bb58b315037751cc540dd147315027e658c5409f596315027c658c540af99231502bd648c540d7d4e315035c538c540e750e315027f654c5409f995315027c654c540af99131502bd644c5409f994315027d650c5409f19431502be640c540af590315035f530c540d714c315039d430c540ddd443150374510c540be98031502f9600c5409f997215027d65c85409f19721502be64c8540af
  | 30 => 0xbe6408740af59021d036e5208740db54821d03ad4208740d7d4e539027e6294e409f58a539027e6194e409f586539027f6254e409f189539027f6154e409f185539035d5314e40bb98853902ed6214e40bd98453902f56114e40d794e439035d5390e40be98243902f96090e40d794d439035d5350e40bed8143902f86050e40e750c43902ee6210e40bb588439036f5294a409f98e529027d6394a409f986529027d6194a409fd8d529027c6354a409fd85529027c6154a40b798c52902dd6314a40db54852902f66114a40bd584529036e5290a40db54a42902fa6090a40be582429036e5250a40db54942902fb6050a40be18142902de6310a40b758c42903ad4210a409fd97329027e65cca409f597329035e53cca40d754f329027f658ca409f996329027d658ca40db94a329036d528ca409fd95329027d654ca409f19532902bf644ca40af191329035e534ca40d754d329036e524ca40db549329027f650ca409f994329027d650ca40af99032902bd640ca40f34c8329037751946409f98e519027d63946409f98a519027d6294640b7d8d51902dc6354640bbd8951902ec62546409fd8d519035f635464097d8d519027c6354640d718d519025c63546409fd89519036f62546409bd89519027c6254640db189519026c6254640b798c51902dd6314640bb98851902ed6214640dd54451902de63d0640b758f41902ee62d0640bb58b41903765190640dd54641902fa6090640be582419033d5390640cf54a41903b65190640cf54641903b55190640ee98241902bd6090640ee58241903765150640dd54541902fb6050640be18141902bd6510640cf594419033d5310640cf54841903b66110640cf54441902bd60106409fd97319027e65cc6409f59731902be64cc640af593319035e53cc640d754f31902ee62cc640bb58b319027f658c6409f996319027d658c640dd9463190375518c6409fd95319027d654c6409f19531902bf644c640af191319035e534c640d754d3190376514c640dd545319027f650c6409f994319027d650c640be98031902f9600c6409fd97219027e65c86409f59721902be64c8640af59321902de63c8640b758f219036e52c8640db54b219027f65886409f996219027d6588640dd946219037551886409fd95219027d65486409f19521902bf6448640af191219036e5248640db54921903765148640dd545219027f65086409f994219027d6508640be98021902f96008640af597409033d65d0240cf54f409033d52d0240af987409033d51d0240be597409037965d02409f98b535027d62d4d409f987535027d61d4d40d7d4e53502ef6254d40bb18953502f76154d40bd185535035d5314d40bb98853502ed6214d409f988535036e6214d409b988535027d6214d40db588535026d6214d409f9845
  | 31 => 0x54f409fd8553d027c6154f40d754c53d02ee6214f40bb58853d035e53d0f40d754f43d02fa60d0f40be58343d033e53d0f40e794f43d039d53d0f40af58b43d02bd61d0f40af98343d03ba60d0f40ee58343d02bf6550f40cfd9543d039f6350f40e7d4d43d033e5350f40e714d43d02bf6250f40afd8543d02bc6050f40d794c43d035d5310f40e750c43d02ee6210f40bb58843d02fa6010f40be58043d036f5294b409f98e52d027d6394b409f98652d027d6194b409fd8d52d027c6354b40cfd0d52d033d4354b409fd8552d027c6154b40b798c52d02dd6314b40db54852d036e52d0b40db54b42d02fa60d0b40be58342d02bd63d0b40cf54f42d033e52d0b40eb94b42d03ad52d0b40af58742d02be60d0b40ee98342d03b960d0b40afd9542d033f6550b40afd8d42d033d5350b40ebd8942d03af5250b40cf94942d03ac5250b40afd8542d02bc6050b40b798c42d02dd6310b40db94842d036d5210b40eb50842d02fa6010b40be58042d027f65ccb409f99732d027d65ccb40af99332d02bd64ccb40d794f32d035d53ccb40e750f32d027f658cb409f99632d027d658cb40af99232d02bd648cb40db94a32d036d528cb40eb50a32d027f654cb409f59532d027c654cb40af99132d02bd644cb40d794d32d035d534cb40e750d32d036e524cb40db54932d03ad424cb409fd9432d027e650cb409f59432d02be640cb40af59032d03cd320cb40b798f51d02dd63d4740bb98b51d02ed62d4740ddd4651d027e63947409f58e51d033f4394740cf50e51d027e62947409f58a51d033f4294740cf50a51d027f63547409f18d51d027f62547409f18951d03755114740b798f41d02dd63d0740bb98b41d02ed62d0740dd94741d037551d0740be98341d02f960d0740e798f41d02bd63d0740e758f41d029d63d0740eb98b41d02bd62d0740eb58b41d02ad62d0740cf94741d03b651d0740ed54741d02be60d0740ee98341d03b960d0740afd9541d033f6550740afd8d41d02bf6250740edd8541d03b75150740cf94541d03b45150740af18141d03765110740dd54441d03b54110740be98041d02f960107409fd9731d027e65cc7409f59731d02be64cc740af59331d02ee62cc740bb58b31d027f658c7409f99631d027d658c740af99231d02bd648c740d794e31d035d538c740e750e31d027f654c7409f59531d027c654c740af99131d02bd644c7409fd9431d027e650c7409f59431d02be640c740af59031d035e530c740d754c31d039d430c7409fd9721d027e65c87409f59721d02be64c8740af59321d02de63c8740b758f21d027f65887409f99621d027d6588740af99221d02bd6488740db94a21d036d5288740eb50a21d027f65487409f59521d027c6548740af99121d02bd64487409fd9421d027e65087409f59421d02
  | 32 => 0x1bb982420867f6550821cfd51420873c5450821bbd95420876f6550821ebd9142087af5450821db951420876c5450821eb151420872c5450821bbd8d420876f5350821db54d42087af4350821eb50d42086ef6150821bb181420867f65108219f594420873e5410821cf55042086de6310821b758c42086ee6210821eb50842086f66110821bd584420867d65cc821d7d4f320875c53cc8219fd96320867d658c821d794e320875d538c821bd98632086f5618c821db596320866d658c821bbd9232086ed648c821dbd52320876d548c821bb58e320876e538c821f394e32087cd538c821db14e32087e6618c821bb58632087e5618c821b958632086ee608c8219fd95320875f534c821d714d32086ef654c821dbd9532086ef644c821bb591320876f544c821db55132087cf634c821f3d4d320876e534c821db14d32087cc534c821d314d32087ce434c821f350d32086ef614c821bb181320867f650c8219f59432086be640c821af590320875e530c821d754c32086ee620c821f34c832086f6610c821bd584320867e64944219f592510867e63944219f58e510876e4294421db50a510876e3294421db4ca510867d65d0421b798f41086dd63d0421bb98b41086ed62d04219fd96410867d6590421cf952410873d5490421bb98a41086ed6290421eb50a410867f65504219fd94410867e65104219f594410867c6510421cf950410873d5410421bb98841086ed6210421eb50841087b541104219f59731086be64cc421af59331086ee62cc421bb58b310867f658c4219f596310875e538c421d754e31086ee628c421bb58a31087cd328c4219fd95310867f650c4219f994310867d650c4219f194310875e530c421d754c31086ee620c421bb58831087cd320c421f54c431086be64c8421af59321086de63c8421b758f21086ef64c8421eb99321086ed64c8421eb59321086ad64c8421bbd8f21087ce63c8421bb58f21087cd63c8421b358f21086ee60c8421bb58a210876e5288421bd58a21087765288421f994a21087e64288421f950a21087e63288421f94ca210867f6548421bbd95210876f65484219bd9521086ef6448421bb59121086ef6348421bb58d21086ef6148421db94521087e74148421f910521087e73148421f90c521086ec6048421bdd95210877765484219dd9521086f76248421f9d8921087765248421f994921087e74248421f910921087e73248421f90c9210877b50940219f992500867d64940219f98e500867d63940219fd91500867c64540219fd8d500867c6354021db909500876d4254021db8c9500876d3254021dbc8550087762154021db48550087752154021af99050086bd6414021b798c50086dd6314021de540500875f5394f409f98a53d027d6294f409f98653d027d6194f409fd8953d027c62
  | 33 => 0x93314875f53cc521d714f31486ee62cc521bb58b314867e658c521d794e314875d538c5219fd95314867d654c5219f195314875f534c521d714d31486ef624c521bb189314867e650c521d794c314875d530c521af99321486bd64c8521b798f21486dd63c8521ed99321487b564c8521f598f21487d563c8521bd583214876f5488521db552214876f5388521db54e21487e75188521bb582214867e64d41219f593504867e63d41219f58f504877b5094121afd9150486bc6454121b7d8d50486dc6354121af99050486bd6414121b798c50486dd6314121de540504867e6414121cf990504863e64141219f590504873d64141218f590504867e6314121d798c504865e63141219f58c504875d63141219758c504876e21141219f98f540867d63d50219f98b540876e62d50219f987540877661d50219f983540867d60d50219f596540873f54950219f98e540867d6395021db98a540867e60950219f582540873f64550219fd8d540867c63550219fd81540867c6055021cf55054086de6315021b758c54086fa6015021be580540867e6415021cf990540867e6315021d798c540865e63150219f58c540875d63150219758c540867e6215021db988540867e6115021dd984540867e6015021de980540867a60150219f580540877960150219e580540867e64d4c219f593530867e62d4c21db98b530867e61d4c21dd987530867e60d4c219f583530867d6594c21d7d4e530867e6494c219f592530876e6294c219f982530867d6094c219fd91530867c6454c21d7d8d530867f6054c219f18153086be6414c21af590530875d5314c21be98053086f96014c219f990530873e6414c218f990530867d6414c21cf590530863d6414c219f98c530875e6314c219f988530876e6214c219f98453087766114c219f980530877a6014c219e980530867d6014c21de58053086796014c219fd97430867e65d0c219f597430867c65d0c21cf953430873d54d0c21bb98b43086ed62d0c21bd98743086f561d0c219fd96430867e6590c219f596430867c6590c21d794e430875d5390c21bb98a43086ed6290c21bd98643086f56190c219fd95430867e6550c219f595430867c6550c21cf951430873d5450c21d794d430875d5350c219fd94430867e6510c219f594430867c6510c21e750c43086ee6210c21bb588430867e6494821cf992520863e64948219f592520873d64948218f592520867e6394821d798e520865e63948219f58e520875d63948219758e520867d65d0821cfd53420873c54d08219fd96420867d6590821cf952420873d5490821bd98642086f56190821db596420866d6590821bb592420876e5490821eb95242087ad5490821db15242086ed6390821dbd4e420876d5390821f998642086ed6190821f958642086e5619082
  | 34 => 0x887ad4210621af99331886bd64cc621bb98b31886ed62cc621d794e318875d538c621bb98a31886ed628c621f34ca318875e530c621d754c31886ee620c621bb58831887cd320c621af99321886bd64c8621b798f21886dd63c8621bb597218876d65c8621bbd9321887ae64c8621bb59321887ad64c8621ab59321886ef63c8621f398f21886ed63c8621f358f21886cd63c8621bb98321886f565c8621dd59721887b664c8621ed59321887d663c8621f558f21886f560c8621ded42508867e64942219f592508867e63942219f58e508867f64542219f191508867f63542219f18d508876e4254221db509508876e3254221db4c9508876f2154221af99050886bd6414221b798c50886dd6314221de540508867e63d51219f58f544867e60d51219f583544873f5495121b798e54486dd63951219f992544867e6395121d798e544865e63951219f58e544875d63951219758e544867d6295121db58a544866d62951219f586544877561951219f982544867d6095121cfd91544867f63551219f18d544867f6255121dbd89544867f6155121ddd85544867f60551219f181544867e6515121cf550544873e64151219f98c544867d63151219f980544867d60151219f993534867d64d4d219f983534867d60d4d21af99253486bd6494d21d7d4e534867e6494d21cf992534863e6494d219f592534873d6494d218f592534867e6394d219f58a534876d6294d219b58a534867d6194d21dd586534867e6094d219f582534867f6454d219f191534875f6354d219fd89534876f6254d219fd8553487776154d219fd81534867c6054d219f994534875d5314d219f990534867d6414d21d798c534867e6014d219f580534867f65d0d219f997434867d65d0d219f197434873f54d0d21cf153434867f6590d219f996434867d6590d219f196434875f5390d21d714e434867f6550d219f995434867d6550d219f195434873f5450d21cf151434875f5350d21d714d43486ef6250d21bb18943486f76150d21bd185434867f6510d219f994434867d6510d219f194434879d4310d21bb98843486ed6210d219f997424873f54d0921cf15342486f661d0921bd587424867e65909219f195424873f5450921cf15142486f76150921bd185424867e6510921b798c42486dd6310921eb508424867e65cc921d7d4f324875c53cc921bd98732486f561cc9219f996324867c654c921d7d4d324875c534c921bdd8532486f4614c9219f99432486be640c921af59032487cd320c9219f997414873f54d0521cf15341486de63d0521b758f41486ee62d0521bb58b414867e6590521cf952414873d54905219fd95414867d65505219f195414873f5450521cf15141486ef6250521bb189414867e6510521cf950414873d54105219f99731486be64cc521af5
  | 35 => 0xd53543219fd9150c867c64543219fd8d50c867c6354321af99050c86bd6414321cf95050c873d5414321b798c50c86dd6314321d794c50c875d5314321de54050c86de63d5221b758f548867e63d5221d798f548865e63d52219f58f548875d63d52219758f548876d62d5221dd987548867e60d52219f583548873f5495221b798e54886dd63952219f98e548875e63952219798e548867d6395221d758e548865d6395221db58a548867e60952219f582548873f64552219fd8d548867c63552219fd81548867c6055221cf550548873e64152219f98c548867d6315221db588548877661152219f980548867d6015221af99353886bd64d4e219f993538873e64d4e218f993538867d64d4e21cf593538863d64d4e21db58b538877661d4e219f983538867d60d4e21af99253886bd6494e21d7d4e538867e6494e21cf992538863e6494e219f592538873d6494e218f592538876d6294e219f982538867d6094e219fd91538867c6454e21d7d8d538867f6054e219f181538875d5314e219f990538867d6414e21d798c538876d6214e21dd984538867e6014e219f580538867f65d0e219f997438867d65d0e219f197438873f54d0e21cf153438875e53d0e21d754f43886ee62d0e21bb58b438867f6590e219f996438867d6590e219f196438873e5490e21cf552438875f5390e21d714e43886ee6290e21bb58a438867f6550e219f995438867d6550e219f195438873f5450e21cf151438875f5350e21d714d43886f76150e21bd185438867f6510e219f994438867d6510e219f194438873e5410e21cf550438875e5310e21d754c438879d4310e21bb98843886ed6210e21cf953428873d54d0a21bd98742886f561d0a21bb596428876d6590a21db952428876c5490a21bb58e428876f5390a21db54e42886ed6190a21bb982428873e5450a21cf55142886f76150a21bd185428876f6550a21ebd91428876e5450a21eb951428872e5450a21eb551428876c5450a21bbd8d428876f5350a21db54d42887af4350a21eb50d42886ef6150a21f9d8542887e46150a21bb18142886de6310a21b758c42887ad4210a21d794f328875d53cca21bd98732886f561cca21bb596328876d658ca21bbd9232886ed648ca21dbd52328876d548ca21db94e328876c538ca21bb58632886ee608ca21d794d328875d534ca21bdd8532886f4614ca21dbd9532886ef644ca21bb591328876f544ca21db55132887cf634ca21db94d32887ce534ca21d394d32887cd534ca21db14d32887ce434ca21f350d32886ef614ca21f9d8532887e4614ca21bb18132886be640ca21af59032887cd320ca21b798f41886dd63d0621bb98b41886ed62d0621cf952418873d5490621bb98a41886ed6290621eb50a418873e5410621cf55041886ee6210621bb58841
  | 36 => 0x4f21e795253c871e5494f21d755253c879d5494f21c755253c875c5494f21d7d9253c875e6494f21d759253c875c6494f21d798a53c875c6294f21d7d8653c875d6194f21d7d8253c875e6094f21d758253c875c6094f21cf95153c873d5454f219fd9153c867c6454f21d7d8d53c867f6054f219f18153c875f6554f21d7d5153c875e5454f21e795153c871e5454f21d755153c879d5454f21c755153c875c5454f21d7d9153c875e6454f21d759153c875c6454f21d798953c875c6254f21d7d8553c875d6154f21d7d8153c875e6054f21d758153c875c6054f21af99053c86bd6414f21cf95053c873d5414f21d754c53c867e6414f21cf99053c863e6414f219f59053c873d6414f218f59053c875e6314f21db98853c87756114f219f98053c867d6014f219fd9743c867e65d0f219f59743c867c65d0f21cf95343c873d54d0f21d794f43c875d53d0f21bd98743c86f561d0f219fd9643c867e6590f219f59643c867c6590f21cf95243c873d5490f21d794e43c875d5390f21bd98643c86f56190f219fd9543c867e6550f219f59543c867c6550f21cf95143c873d5450f21d794d43c875d5350f21bbd8943c86ec6250f219fd9443c867e6510f219f59443c867c6510f21cf95043c873d5410f21d794c43c875d5310f21e750c43c86ee6210f21bb58843c873e54d0b21cf55342c875e53d0b21d754f42c873e5490b21cf55242c875e5390b21d754e42c86f66190b21bd58642c873e5450b21cf55142c875e5350b21d754d42c873e5410b21cf55042c86de6310b21b758c42c875e5310b21d754c42c87ad4210b21bd98442c86f56110b21cf95332c873d54ccb21d794f32c875d53ccb21cf95232c873d548cb21d794e32c875d538cb21bd98632c86f5618cb21cf95132c873d544cb21d794d32c875d534cb21af99032c86bd640cb21cf95032c873d540cb21d794c32c875d530cb21f34c832c86f6610cb21bd58432c873e54d0721cf55341c86de63d0721b758f41c875e53d0721d754f41c86ee62d0721bb58b41c873e5490721cf55241c875e5390721d754e41c873e5450721cf55141c875e5350721d754d41c86ef6250721bb18941c873e5410721cf55041c875e5310721d754c41c87b54110721af99331c86bd64cc721cf95331c873d54cc721d794f31c875d53cc721bb98b31c86ed62cc721cf95231c873d548c721d794e31c875d538c721cf95131c873d544c721d794d31c875d534c721bbd8931c86ec624c721cf95031c873d540c721d794c31c875d530c721f54c431c86be64d4321af59350c873e54d4321cf55350c86de63d4321b758f50c875e53d4321d754f50c873e5494321cf55250c875e5394321d754e50c877b50943219f99250c867d64943219f98e50c867d6394321cf95150c873d5454321d794d50c875
  | 37 => 0xd7d53320c75d54cc831d794b320c7ce52cc831f354b320c7d661cc831b7587320c7d561cc831b5587320c6de60cc8319f596320c6dd638c8319fd95320c6df654c831d7d95320c6df644c831b7591320c75f544c831d7551320c7cf624c831f3d49320c75e524c831f3149320c7ce424c831f3509320c6df614c831b7181320c6be640c831af590320c6de630c831db948320c76d520c831f34c8320c6f6610c831bd584320c67e64944319f592510c75e4394431d750e510c75f3294431d74ca510c67d65d0431b798f410c6dd63d0431bb98b410c6ed62d04319fd96410c67d6590431cf952410c73d5490431b798e410c6dd6390431e750e410c67f65504319fd94410c67e65104319f594410c67c6510431cf950410c73d5410431b798c410c6dd6310431e750c410c7b54110431af993310c6bd64cc431bb98b310c6ed62cc431b7d93310c79e64cc431b7593310c79d64cc431a7593310c7ce62cc431b758b310c7cd62cc431b358b310c6de60cc431b758e310c75e538c431bd58e310c776538c431f594e310c7d6438c431f550e310c7d7328c431f54ca310c67f654c431b7d95310c75f654c43197d95310c6df644c431b7591310c6df624c431b7d85310c75e514c431f5d05310c7d4414c431b7181310c6f7654c431ddd95310c677654c431bdd8d310c7d7634c431dd94d310c7d6534c431f5d0d310c7d4434c431f58c9310c7d4324c431ded42500c67e64940319f592500c67e62940319f58a500c67f64540319f191500c75e4354031d750d500c67f62540319f189500c75f3254031d74c9500c75f3154031dd8c5500c75d3154031dd4c5500c6be6414031af590500c6ee6214031bb588500c7795014031b798f54c86dd63d53219f98f54c875e63d53219798f54c867d63d5321d758f54c865d63d5321db98b54c877561d53219f98354c867d60d5321cfd5254c867e63953219f58e54c867e60953219f58254c873f6395321cf98e54c873d6395321cf18e54c873e6295321cf18a54c873f6195321cf58654c873f6095321cf98254c873d6095321cf18254c873f64553219fd8d54c867c63553219fd8154c867c6055321cfd9554c873f6355321cf98d54c873d6355321cf18d54c873e6255321cf18954c873f6155321cf58554c873f6055321cf98154c873d6055321cf18154c873d5415321b798c54c86dd6315321cf99054c867e6315321d798c54c865e63153219f58c54c875d63153219758c54c876e6215321dd58454c867e60153219f58054c86be64d4f21af59353c873e54d4f21cf55353c867e64d4f21cf99353c863e64d4f219f59353c873d64d4f218f59353c876e62d4f21dd58753c867e60d4f219f58353c873e5494f21cf55253c875f5394f219f99253c867d6494f219f98253c867d6094f21d7d5253c875e549
  | 38 => 0x324c6bd640c931f34c8324c67e65d0531cfd53414c73c54d0531b798f414c6dd63d0531bb98b414c6ed62d05319f996414c73e5490531cf552414c67f65505319f595414c67c6550531cfd51414c73c5450531b7d8d414c6dc63505319f994414c73e5410531cf550414c6be64cc531af593314c6ee62cc531bb58b314c7b664cc531ed593314c7e662cc531f958b314c6f560cc531d7d52314c75d548c531d7d4a314c7d7518c531b7582314c67e64d41319f593504c67e62d41319f58b504c77b5094131afd91504c6bc6454131bbd89504c6ec6254131af990504c6bd6414131bb988504c6ed6214131de540504c67e6414131cf990504c63e64141319f590504c73d64141318f590504c67e6214131db988504c66e62141319f588504c76d62141319b588504c75e31141319f98f540c75e63d50319f98b540c67d62d50319f987540c77661d50319f983540c67d60d50319f596540c73f5495031d798e540c67e62950319f58a540c67e60950319f582540c73f64550319fd89540c67c62550319fd81540c67c6055031cf550540c6ee6215031bb588540c6fa6015031be580540c67e6415031cf990540c67e6315031d798c540c67e6215031db988540c66e62150319f588540c76d62150319b588540c67e6115031dd984540c67e6015031de980540c67a60150319f580540c77960150319e580540c67e6494c31cf992530c63e6494c319f592530c73d6494c318f592530c76e6294c31db58a530c67d65d0c31cfd53430c73c54d0c319fd96430c67d6590c31cf952430c73d5490c31bd986430c6f56190c31d7596430c65d6590c31b7592430c75e5490c31e7952430c79d5490c31d7152430c6dd6290c31f5986430c6dd6190c31f5586430c6d56190c31b7982430c67f6550c31cfd51430c73c5450c31b7d95430c75f6550c31e7d91430c79f5450c31d7951430c75c5450c31e7151430c71c5450c31b7d89430c6df6150c31b7181430c67f6510c319f594430c73e5410c31cf550430c6de6310c31e750c430c6ee6210c31bb588430c6f66110c31bd584430c76f52948319f992520c67d64948319f982520c67d60948319fd91520c67c6454831d790d520c75d43548319fd81520c67c6054831af990520c6bd6414831db548520c6fa6014831be580520c67f65d08319f997420c67d65d0831cf953420c73d54d0831b798f420c6dd63d0831e750f420c6f661d0831bd587420c67f65908319f996420c67d6590831b798e420c6dd6390831db94a420c76d5290831bd986420c6f561908319fd95420c67d65508319f195420c73e5450831cf551420c79d4350831db949420c76d52508319fd94420c67e65108319f594420c6de6310831b758c420c7ad4210831db94b320c76d52cc831bd987320c6f561cc831b7d93320c6dd64cc831
  | 39 => 0xc67d6590a31cf952428c73d5490a31b798e428c6dd6390a319fd95428c67d6550a319f195428c73f5450a31cf151428c79d4350a31bdd85428c6f46150a319fd94428c67e6510a319f594428c73e5410a31cf550428c6de6310a31b758c428c76e5210a31db548428c7ad4210a31b7597328c75d65cca31b7d93328c6dd64cca31d7d53328c75d54cca31d794b328c6dd61cca31b7983328c76e528ca31db54a328c6f6618ca31bd586328c76e524ca31db549328c6f7614ca31bd185328c6df644ca31b7591328c75f544ca31d7551328c7cf624ca31d7949328c7ce524ca31d3949328c7cd524ca31f3909328c7cd424ca31b7d85328c7d7614ca31f5185328c6dc604ca31af990328c6bd640ca31f34c8328c6de63d0631b758f418c6ee62d0631bb58b418c73e5490631cf552418c6de6390631b758e418c79d4390631cf950418c73d5410631b798c418c6dd6310631e750c418c6be64cc631af593318c6ee62cc631bb58b318c6dd65cc631d7597318c6df64cc631e7993318c6dd64cc631e7593318c69d64cc631f398b318c6dd62cc631f358b318c6cd62cc631b7983318c6f565cc631dd597318c7b664cc631ed593318c7e662cc631f958b318c6f560cc631ded42508c67e64942319f592508c67e62942319f58a508c67f64542319f191508c75e4354231d750d508c67f62542319f189508c75f3254231d74c9508c75f3154231af990508c6bd6414231bb988508c6ed6214231de540508c67e62d51319f58b544c67e60d51319f583544c73f5495131bb98a544c6ed62951319f992544c67d6395131d758e544c65d63951319f98a544c76e62951319b98a544c67d6295131db58a544c66d62951319f586544c77561951319f982544c67d6095131cfd91544c67f6355131d7d8d544c67f62551319f189544c67f6155131ddd85544c67f60551319f181544c67e6515131cf550544c73e64151319f988544c67d62151319f980544c67d60151319f997434c73f54d0d31cf153434c6f661d0d31bd587434c67e6590d319f195434c73f5450d31cf151434c6f76150d31bd185434c67e6510d31e750c434c6ee6210d31bb588434c67e64d49319f593524c67e60d49319f583524c6be6494931af592524c76f5294931db548524c67e64149319f590524c67e60149319f580524c67e65d09319f597424c67c65d0931cfd53424c73c54d09319f996424c67d65909319f196424c76f5290931db14a424c67f65509319f995424c67c6550931cfd51424c73c5450931b7d8d424c6dc6350931dbd49424c76c5250931bdd85424c6f461509319f994424c67d65109319f194424c6de6310931b758c424c7ad42109319f997324c76f528c931db14a324c6f6618c931bd586324c76f524c931db149324c6f7614c931bd185324c67e650c931af99
  | 40 => 0x5414b31db54852cc67f65d0b319f99742cc67d65d0b31cf95342cc73d54d0b31db94b42cc76d52d0b31bd98742cc6f561d0b319fd9642cc67e6590b319f59642cc73e5490b31cf55242cc76e5290b31db54a42cc6f66190b31bd58642cc67f6550b319f59542cc67c6550b31cf95142cc73d5450b31b7d8d42cc6dc6350b31db94942cc76d5250b319fd9442cc67e6510b319f59442cc73e5410b31cf55042cc6de6310b31b758c42cc76e5210b31db54842cc7ad4210b31cf95332cc73d54ccb31db94b32cc76d52ccb31bd98732cc6f561ccb31cf95232cc73d548cb31db54a32cc73e544cb31cf55132cc76e524cb31af99032cc6bd640cb31cf95032cc73d540cb31db94832cc76d520cb31f34c832cc6f6610cb31bd58432cc73e54d0731cf55341cc6de63d0731b758f41cc6ee62d0731bb58b41cc76e52d0731db54b41cc73e5490731cf55241cc76e5290731db54a41cc73e5450731cf55141cc6df6350731b718d41cc76e5250731db54941cc73e5410731cf55041cc76e5210731db54841cc7b54110731af99350cc6bd64d4331cf95350cc73d54d4331bb98b50cc6ed62d4331db94b50cc76d52d4331cf95250cc73d5494331db94a50cc76d5294331ded4250cc67e64943319f59250cc67e62943319f58a50cc73e5454331cf55150cc76e5254331db54950cc67f64543319f19150cc67f62543319f18950cc6be6414331af59050cc73e5414331cf55050cc6ee6214331bb58850cc76e5214331db54850cc7795014331bb98b548c6ed62d5231d758f548c67e62d5231db98b548c66e62d52319f58b548c76d62d52319b58b548c77661d52319f983548c67d60d5231cfd52548c6ee6295231bb58a548c75d63952319f98a548c76e62952319b98a548c67d6295231db58a548c66d62952319f982548c67d6095231cfd91548c67f62552319f189548c67f60552319f181548c73d5415231cf990548c75d63152319f988548c67d6215231dd984548c67e60152319f580548c73e54d0e31cf553438c6f661d0e31bd587438c6dd6590e31d7596438c75e5490e31d7152438c6dd6290e31b7586438c6de6090e31cf951438c73d5450e31bdd85438c6f46150e31d7d95438c79f6450e31d7951438c79e5450e31c7951438c79d5450e31d7151438c6df6250e31b7d85438c7d76150e31f5185438c6dc6050e31e750c438c6ee6210e31bb588438c6be64d4a31af593528c6be6494a31af592528c76f5294a319f992528c73e6494a318f992528c67d6494a31cf592528c63d6494a319f982528c67d6094a319fd91528c67c6454a31d790d528c75d4354a319fd81528c67c6054a31db548528c67f65d0a319f997428c67d65d0a31cfd53428c73c54d0a31b798f428c6dd63d0a31e750f428c76e52d0a31db54b428c67f6590a319f996428
  | 41 => 0x8419f59432106be640c841af59032107cd320c841cfd0e511073d4394441cfd0a511073d4294441b798f41106dd63d0441bb98b41106ed62d0441e798f41106bd63d0441e758f411069d63d0441eb98b41106bd62d0441eb58b41106ad62d0441af98341106bd6490441cf95241106f56490441dd95241107b65490441edd0e41107b54390441edd0a41107b542904419fd9541106bf6550441cfd95411063f6550441afd8d41106bf6250441afd85411073e5150441af18141106f76550441ddd9541106776550441bdd9141107b76450441dd95141107b65450441ed90d41107b44350441ed90941107b44250441ded42501067e63940419f58e501067e62940419f58a501067f63540419f18d501073f4354041cf50d501067f62540419f189501073f4254041cf509501073f4154041dd905501073d4154041dd50550106de6314041b758c50106ee6214041bb58850107795014041bb98b54cc6ed62d5331d798f54cc67e62d5331db98b54cc66e62d53319f58b54cc76d62d53319b58b54cc77561d53319f98354cc67d60d5331cfd5254cc67e62953319f58a54cc67e60953319f58254cc73e6395331cf18e54cc73f6295331cf98a54cc73d6295331cf18a54cc73f6195331cf58654cc73f6095331cf98254cc73d6095331cf18254cc73f64553319fd8954cc67c62553319fd8154cc67c6055331cfd9554cc73e6355331cf18d54cc73f6255331cf98954cc73d6255331cf18954cc73f6155331cf58554cc73f6055331cf98154cc73d6055331cf18154cc73d5415331bb98854cc6ed6215331cf99054cc75e63153319f98854cc76e62153319b98854cc67d6215331db58854cc66d6215331dd58454cc67e60153319f58054cc73e54d0f31cf55343cc73e5490f31cf55243cc6f66190f31bd58643cc73e5450f31cf55143cc73e5410f31cf55043cc79d4310f31bb98843cc6ed6210f31bd98443cc6f56110f31af99352cc6bd64d4b31cf95352cc73d54d4b31cf95252cc73d5494b31dbd4a52cc67e6494b319f59252cc67e6094b319f58252cc76f5494b31db95252cc7ae5494b31cb95252cc76d5494b31eb55252cc72d5494b31db15252cc76f6494b31db99252cc76d6494b31db19252cc76c6394b31dbd0e52cc76e4394b31db50e52cc76c4394b31dbd8652cc76d6194b31dbd8252cc76e6094b31db58252cc76c6094b31cf95152cc73d5454b319fd9152cc67c6454b319fd8152cc67c6054b31dbd9552cc76f5454b31db95152cc7ae5454b31cb95152cc76d5454b31eb55152cc72d5454b31db15152cc76f6454b31db99152cc76d6454b31db19152cc76e6354b31dbd0d52cc76e4354b31db50d52cc76c4354b31dbd8552cc76d6154b31dbd8152cc76e6054b31db58152cc76c6054b31af99052cc6bd6414b31cf95052cc73d
  | 42 => 0xf580525067e65d0941dbd4a425076c5290941bd98642506f56190941dbd49425076c5250941bdd8542506f461509419f99442506de6310941b758c42507ad42109419f997325067d65cc9419f197325075f53cc941d714f325067e658c9419f596325067c658c941dbd4a325076c528c9419fd95325067e654c9419f19532506bf644c941af191325075f534c941d714d325076f524c941db14932506f7614c941bd185325067e650c9419f594325067c650c941af99032506bd640c941f34c832506de63d0541b758f41506ee62d0541bb58b41507d663d0541f558f41507e662d0541f958b41506f560d0541cfd4e415073f5290541edd4641506bd60905419f98f505067d63d41419f98b505067d62d4141ded4250506df6354141b718d50506ef6254141bb18950506de6314141b758c50506ee6214141bb588505077950141419f98c505075e63141419798c505067d6314141d758c505065d63141419f988505076e62141419b988505067d6214141db588505066d6214141cf904505075e6395041d758e541076e6295041db58a541075f5394c419f98a531067d6294c419f982531067d6094c419fd89531067c6254c419fd81531067c6054c41d754c53106ee6214c41bb58853106fa6014c41be580531075e53d0c41d754f43106f661d0c41bd587431073e53d0c41e794f431079d53d0c41af58b43107b661d0c41af58743107b561d0c41ad58743106be60d0c419f59643106bd6490c419fd9543106bf6550c41cfd95431079f6350c41e7d4d431073e5350c41e714d43106bf6250c41afd8543106bc6050c41af990431075e5310c41d754c431079d4310c41bb98843106ed6210c41bd98443106f56110c41dbd4a521067e63948419f58e521067e60948419f582521067f63548419f18d521073f4354841cf50d521067f60548419f18152106de6314841b758c521076d5214841be98052106f96014841db94b421076d52d0841bd98742106f561d0841af58f421073d53d0841cf94b42107ae52d0841eb54b42107b661d0841af58742107b561d0841ad58742106be60d08419f59642106bd64908419fd9542106bf6550841cfd9542106bf6350841cf54d42107af6250841ebd49421073e5250841eb14942106bf6150841af18142106be6410841b798c42106dd6310841db948421076d5210841eb50842106f66110841bd584421067f65cc8419f997321067d65cc841af99332106bd64cc841d794f321075d53cc841e750f32106f661cc841bd587321067f658c8419f996321067d658c841af99232106bd648c841db94a321076d528c841eb50a32106f6618c841bd586321067f654c8419f595321067c654c841af99132106bd644c841d794d321075d534c841e750d321076e524c841db54932107ad424c8419fd94321067e650c
  | 43 => 0x50d06de6314341b758c50d075e5314341d754c50d06ee6214341bb58850d076e5214341db54850d07795014341bb98b53906ed62d4e41d7d4e53906ee6294e41bb58a539067e6294e41db98a539066e6294e419f58a539076d6294e419b58a539067e6094e419f582539067f6254e419f189539067f6054e419f181539075d5314e41af597439073d65d0e41cf94f43906bd62d0e41af58743906be60d0e41d794e439075d5390e41bd98643906f56190e41d794d439075d5350e41bdd8543906f46150e41e7d8d439073e5350e41e794d439071e5350e41e754d43906bf6250e41afd8543907b76150e41ed18543906bc6050e41e750c43906ee6210e41bb58843906de63d4a41b758f52906de6394a41b758e529076f5294a419f98e529075e6394a419798e529067d6394a41d758e529065d6394a419f982529067d6094a419fd8d529067c6354a41cfd0d529073d4354a419fd81529067c6054a41db54852906bd65d0a41cf59742906bd63d0a41cf54f429073e52d0a41af58742906be60d0a41db94a429076d5290a41bd98642906f56190a41db949429076d5250a41bdd8542906f46150a41afd8d429073d5350a41ebd89429073e5250a41eb949429072e5250a41eb54942906bf6150a41edd8542907b46150a41af18142906de6310a41b758c42907ad4210a419fd97329067e65cca419f59732906be64cca41af593329079d43cca41db94b329076d52cca419fd96329067e658ca419f59632906be648ca41af592329075e538ca41d754e32907ad428ca419fd95329067d654ca419f19532906be644ca41af591329079d434ca41eb50932906f7614ca41bd185329067f650ca419f994329067d650ca41af99032906bd640ca41d794c329075d530ca41db948329076d520ca41f34c832906de63d0641b758f41906ee62d0641bb58b41906bd65d0641cf597419079e63d0641af58f419079d63d0641a758f41907ae62d0641af58b41907ad62d0641ab58b41906be60d0641bd597419077565d0641f598f41907d563d0641f998b41907e562d0641bd583419077b50942419f98e509067d63942419f98a509067d62942419fd8d509067c6354241cfd0d509073d43542419fd89509067c6254241cfd09509073d4254241cfd0550906de6314241b758c50906ee6214241bb588509077950142419f98b535067d62d4d419f983535067d60d4d41d7d4e53506ee6294d41bb58a535075d5314d419f988535067d6214d419f980535067d6014d419f997435075f5390d41d714e43506f66190d41bd586435075f5350d41d714d43506f76150d41bd185435067e6510d41e750c43506ee6210d41bb588435067e63d49419f58f525067e60d49419f58352506de6394941b758e525076f5294941db548525067e63149419f58c525067e60149419
  | 44 => 0xb6e3254032d74c9500cb6d3254032d34c9500ca7f61540329f185500cabe6414032af590500cb3e5414032cf550500cbcd3214032bd984500caf56114032de540500caee62d4f41bb58b53d075f5394f419f98a53d067d6294f419f98253d067d6094f41d719253d075f6294f41d798a53d075d6294f41d718a53d075f6194f41d758653d075f6094f41d798253d075d6094f41d718253d067f6254f419f18953d067f6054f419f18153d075f6554f41d799153d075f6254f41d798953d075d6254f41d718953d075f6154f41d758553d075f6054f41d798153d075d6054f41d718153d075d5314f41bb98853d06ed6214f41d794f43d075d53d0f41bd98743d06f561d0f41d754e43d075e5350f41d794c43d075d5310f41e750c43d06ee6210f41bb58843d06f66110f41bd58443d06de63d4b41b758f52d075e53d4b41d754f52d075e5394b41d754e52d076f5294b419f98e52d067d6394b419f98252d067d6094b41dbd4e52d076e5394b41f394e52d074e5394b41db54e52d07cd5394b41d354e52d076c5394b41db19252d076f6394b41db98e52d076d6394b41db18e52d076f4394b41db90e52d076d4394b41db10e52d076f6194b41db58652d076f6094b41db98252d076d6094b41db18252d075e5354b41d754d52d067f6354b419f18d52d067f6054b419f18152d076f6554b41dbd4d52d076e5354b41f394d52d074e5354b41db54d52d07cd5354b41d354d52d076c5354b41db99152d076f6354b41db98d52d076d6354b41db18d52d076f4354b41db90d52d076d4354b41db10d52d076f6154b41db58552d076f6054b41db98152d076d6054b41db18152d06de6314b41b758c52d075e5314b41d754c52d076d5214b41d794f42d075d53d0b41db94b42d076d52d0b41bd98742d06f561d0b41d794e42d075d5390b41db54a42d075e5350b41d754d42d076e5250b41b798c42d06dd6310b41d794c42d075d5310b41db94842d076d5210b41eb50842d06f66110b41bd58442d067f65ccb419f99732d067d65ccb41d794f32d075d53ccb41db94b32d076d52ccb41bd98732d06f561ccb419fd9632d067e658cb419f59632d075e538cb41d754e32d076e528cb41db54a32d06f6618cb41bd58632d067f654cb419f59532d067c654cb41afd9132d06bc644cb41d794d32d075d534cb41db94932d076d524cb419fd9432d067e650cb419f59432d06be640cb41af59032d075e530cb41d754c32d076e520cb41db54832d07cd320cb41b798f50d06dd63d4341d794f50d075d53d4341bb98b50d06ed62d4341db94b50d076d52d4341d794e50d075d5394341db94a50d076d5294341ded4250d067e63943419f58e50d067e62943419f58a50d075e5354341d754d50d076e5254341db54950d067f63543419f18d50d067f62543419f189
  | 45 => 0x195032cfd82540cb3e6095032cf582540cb3c6095032cfd91540ca7f61550329f185540ca7f60550329f181540cb3f6555032cf98d540cb3c6355032cf989540cb3c6255032cf0c9540cb3f6155032cf985540cb3d6155032cf185540cb3f6055032cf981540cb3d6055032cf181540cabe6415032cf550540ca7e6415032cf990540ca3e64150329f98c540cb5e63150329798c540ca7e6215032db988540ca6e62150329f984540ca7d61150329f980540ca7d60150329f992530ca7d6494c329f597430cb3e54d0c32cf553430ca7f6590c329f596430cb3e5490c32cf552430cb5e5390c32bb98a430caed6290c329fd95430cb3e5450c32cf551430cb5e5350c329fd94430ca7d6510c32cf950430cb3d5410c32e750c430caee6210c32bb588430ca7e64948329f592520ca7d65d0832cf953420cb3d54d08329fd96420ca7d6590832cf952420cb3d5490832b798e420cadd6390832db94a420ca7f6550832cf951420cb3d5450832db949420ca7f65108329f994420ca7d65108329f194420cb3e5410832cf550420cade6310832b758c420cbad4210832cf953320cb3d54cc832d7d53320cb9e54cc832d7553320cb9d54cc832c7553320cb3e548c832cf552320cadd638c832d794e320cb6f548c832eb952320cb6d548c832eb552320cb2d548c832bb58e320cacd638c832db94e320cbce538c8329fd95320cb3e544c832cf551320cadf654c832d7d95320ca5f654c832d7d51320cb9e544c832d7551320cb9d544c832c7551320cadf624c832d7949320cbcf424c832f3909320cbcd424c832f3109320caef654c832dbd95320ca6f654c832dbd51320cbae544c832db551320cbad544c832cb551320caef634c832f3d8d320cb6e534c832f394d320cbcf434c832f390d320cbcd434c832f310d320cbcf654c832b3d95320cb4f654c832f3d91320cbce644c832f3591320cbcc644c832f3d51320cb4f544c832f3951320cb8e544c832f3551320cb4d544c832e3551320cb0d544c832f3151320cbcf614c832f3985320cbcd614c832f3185320cbcf604c832f3981320cbcd604c832f3181320cabe64d4432af593510cb3e54d4432cf553510cbcd32d4432cf952510cb3d5494432f34ca510cb7751944329f992510ca7d6494432d7cca510cb6e3294432d74ca510cb6d3294432d34ca510ca7e60944329f582510cb3e5454432cf551510cbcd32544329fd91510ca7c64544329fd81510ca7c6054432af990510cabd6414432cf950510cb3d5414432f34c8510cb755114432be980510caf96014432af993500cabd64d4032cf953500cb3d54d4032f34cb500cb3e5494032cf552500cbcd3294032ded42500ca7e64940329f592500ca7e61940329f586500cb3e5454032cf551500cbcd32540329fd91500ca7c6454032d7cc9500c
  | 46 => 0x329f587544ca7e60d51329f583544cb3f5495132bd986544caf561951329f992544ca7d6395132d758e544ca7d6295132db58a544ca7e6195132dd986544ca7661951329f586544cb7561951329d586544ca7e60951329f582544cb3f64551329fd8d544cb5f63551329fd89544cb6f62551329fd85544ca7c61551329fd81544ca7c60551329f994544cb3d5415132cf990544cb5d6315132db588544ca7e61151329f584544ca7e60151329f580544ca7e65d0d32cfd53434cb3c54d0d32bb98b434caed62d0d329f996434cade6590d32d7996434cadd6490d32d7952434cb5c5490d32f3d8a434cade6290d32f318a434cade6190d32b7582434ca7c6550d32cfd51434cb3c5450d32bbd89434caec6250d32d7195434ca5c6550d32e7d91434cb9f5450d32d7951434cb5c5450d32e7151434cb1c5450d32f3d89434cadc6250d32f3189434cacc6250d32b7185434cadf6050d329f994434cade6310d32e750c434caee6210d329f997424cb3f54d0932cf153424cade63d0932b758f424cb9d43d09329f996424caee6590932db996424caed6490932db952424cb6c5490932f3d8e424caee6390932f318e424cbce4390932f350e424caee6190932bb582424ca7f65509329f595424ca7c6550932cfd51424cb3c5450932b7d8d424cadc6350932e750d424caec6550932db195424ca6c6550932ebd91424cbaf5450932db951424cb6c5450932eb151424cb2c5450932f3d8d424caec6350932f318d424cacc6350932ebd0d424cbce4350932eb50d424cbcd4350932e350d424caec6150932bbd81424ca7e6510932b798c424cadd6310932bb988424cbad4210932bbd93324caed64cc932f390f324cbcd43cc932bb987324caed60cc932b7d92324cadd648c932f3d4a324cbce428c932f350a324cade618c932b7582324cabe64d4532af593514ca7e64d4532cf993514ca3e64d45329f593514cb3d64d45328f593514ca7e60d45329f583514cabe6494532af592514cb775194532dd544514ca7e64145329f590514cb5e4314532d750c514cb6e4214532db508514ca7e60145329f580514ca7e64d41329f593504cb5e43d4132d750f504cb6e42d4132db50b504ca7e61d41329f587504cb7b5094132afd91504cabc6454132bdd85504caf46154132af990504cabd6414132bd984504caf56114132de540504ca7e6414132cf990504ca3e64141329f590504cb3d64141328f590504ca7e6114132dd984504ca7661141329f584504cb7561141329d584504ca7e63d5032d798f540ca7e62d5032db98b540ca7e61d50329f587540ca7e60d50329f583540ca7d6595032cfd52540ca7e61950329f586540ca7e60950329f582540ca3d6595032cf98e540cb3c6395032cf98a540cb3c6295032cfd86540cb3e6195032cf586540cb3c6
  | 47 => 0x98e54cca7e61953329f58654cca7e60953329f58254ccb3f64553329fd8554cca7c61553329fd8154cca7c6055332cf55054ccb3e6415332d798c54ccb6d62153329f98454cca7d61153329f98054cca7d6015332cfd5343ccb3c54d0f32cf95243ccb3d5490f32bb98a43ccaed6290f32d759643ccb5e5490f32e795243ccb9d5490f32d715243ccade6290f32f398a43ccbcd6290f32b798643ccadd6090f32cfd5143ccb3c5450f32b7d9543ccb5f6550f32e7d9143ccb9f5450f32d795143ccb5c5450f32e715143ccb1c5450f32b718943ccadc6150f32b7d8143ccb3e5410f32cf55043ccb9d4310f32bb98843ccaed6210f32cf95342ccb3d54d0b32b798f42ccadd63d0b32e750f42ccb3e5450b32cf55142ccadf6350b32b718d42ccb9d4350b32b798c42ccadd6310b32eb50842ccabe64d4732af59351ccb7751947329f99251cca7d6494732d790e51ccb5d43947329f98251cca7d60947329fd9151cca7c64547329fd8151cca7c6054732dd54451ccb7b50943329f99250cca7d64943329f98650cca7d61943329fd9150cca7c6454332d790d50ccb5d43543329fd8550cca7c6154332af99050ccabd6414332bd98450ccaf56114332de54050ccaf661d5232bd587548cb5d63d5232db98b548ca7e61d5232dd987548ca7661d52329f587548cb7561d52329d587548ca7e60d52329f583548cb3f5495232db98a548ca7e61952329f586548ca7e60952329f582548cb3f64552329fd85548ca7c61552329fd81548ca7c6055232cf550548cb3e6415232d758c548cb6e62152329f984548ca7d61152329f980548ca7d6015232cf953438cb3d54d0e32bb98b438caed62d0e32cf951438cb3d5450e32bbd89438caec6250e32e750c438caed6210e32cfd53428cb3c54d0a32cf952428cb3d5490a32b798e428cadd6390a32bb596428cb6d6590a32db952428cbae5490a32eb552428cb6c5490a32bb98e428cbce6390a32f358e428caee6190a32bb582428cb3f5450a32cf151428caef6550a32dbd95428cbaf6450a32ebd51428cb6e5450a32db151428cbac5450a32cb151428caec6350a32ebd0d428cbad4350a32bb185428caef6050a32cf950428cb3d5410a32b798c428cadd6310a32eb508428cadd65cca32d7597328cb5f54cca32d7553328caed65cca32db597328caef64cca32bb593328caee61cca32bb583328cabe64d4632af593518cb7751946329f992518ca7d6494632db90a518cb6d4294632d7cca518ca7e60946329f582518ca7f64546329f191518ca7f60546329f181518cb755114632ded42508ca7e64942329f592508ca7e61942329f586508ca7f64542329f191508cb6e4254232db509508cb5f32542329fd85508ca7c6154232af990508cabd6414232bd984508caf56114232de540508ca7e61d51
  | 48 => 0x50af46154142b798c5050add6314142bd9845050af56114142de5405050a7e6314142d798c5050a5e63141429f58c5050b5d63141429758c5050a7e6114142dd9845050a7661141429f5845050b7561141429d5845050b5f5394c429f9865310a7d6194c429f9825310a7d6094c42d71925310b5e6294c42d718a5310b5f6194c42d79865310b5d6194c42d71865310b5f6094c42d79825310b5d6094c42d71825310a7f6154c429f1855310a7f6054c429f1815310b5f6554c42d79915310b5e6254c42d71895310b5c4254c42d7d855310b5e6154c42d75855310b5c6154c42d7d815310b5e6054c42d75815310b5c6054c42b798c5310b5d5314c42cf9534310b5e53d0c42d754f4310aee62d0c42bb58b4310a7d6590c42d754e4310a7f6550c42cf9514310b5e5350c42d794c4310b5d5310c42e750c4310aee6210c42bb5884310b5e53d0842d754f4210b9e53d0842cf54f4210b9d53d0842c754f4210abd6490842cf9524210b5e5390842d754e4210aed6490842ab5924210b6e5490842eb9524210bce5390842db54e4210bcd5390842d354e4210a7f6550842d794d4210b5d5350842afd954210b3f65508428fd954210b9e5350842cf54d4210b9d5350842c754d4210abf6250842cf9494210aef6550842dbd954210a6f6550842bbd914210baf6450842db9514210bae5450842f394d4210b6d5350842f354d4210b4d5350842ebd0d4210bae4350842eb50d4210bac4350842ebd954210aaf6550842cbd954210baf6350842eb98d4210bad6350842eb18d4210baf5350842eb94d4210b8e5350842eb54d4210b2d5350842e354d4210b0d5350842eb14d4210baf6150842eb9854210bad6150842eb1854210baf6050842eb9814210bad6050842eb1814210ade63d4442b758f5110b5e53d4442d754f5110bad42d4442d794e5110b5d5394442eb50a5110b7751944429f98e5110a7d6394442cfd0a5110b6e4294442cf50a5110b6d4294442cb50a5110a7e60944429f5825110b5e5354442d754d5110bad42544429fd8d5110a7c63544429fd815110a7c6054442b798c5110add6314442d794c5110b5d5314442eb5085110b755114442be9805110af96014442b798f5010add63d4042d794f5010b5d53d4042eb50b5010b5e5394042d754e5010bad4294042ded425010a7e63940429f58e5010a7e61940429f5865010b5e5354042d754d5010bad42540429fd8d5010a7c6354042cfd095010b6e4254042cf5095010b6d4254042cb5095010a7f61540429f1855010ade6314042b758c5010b5e5314042d754c5010bad4214042bd9845010af56114042de5405010af661d5332bd58754ccb5e63d5332db58b54cca7e61d5332dd98754cca7661d53329f58754ccb7561d53329d58754cca7e60d53329f58354ccb3f5495332d7
  | 49 => 0x6d5214043bd9845010ef56114043de5405010ef661d4f42bd58753d0b5f5394f429f98653d0a7d6194f429f98253d0a7d6094f429fd8553d0a7c6154f429fd8153d0a7c6054f42d754c53d0b5e53d0f42d754f43d0aee62d0f42bb58b43d0b3e53d0f42e794f43d0b9d53d0f42af98b43d0bae62d0f42eb58b43d0abe61d0f42af58343d0abf6550f42cfd9543d0b9f6350f42e7d4d43d0b3e5350f42e714d43d0abc6250f42af18543d0abf6050f42d794c43d0b5d5310f42e750c43d0aee6210f42bb58843d0ade63d4742b758f51d0b7751947429f98e51d0a7d6394742cfd0e51d0b3d43947429f98251d0a7d60947429fd8d51d0a7c63547429fd8151d0a7c6054742dd54451d0b7b50943429f98e50d0a7d63943429f98650d0a7d61943429fd8d50d0a7c6354342cfd0d50d0b3d43543429fd8550d0a7c6154342b798c50d0add6314342bd98450d0af56114342de54050d0af661d4e42bd5875390b5f5394e42db98a5390a7e6194e429f5865390a7e6094e429f5825390a7f6154e429f1855390a7f6054e429f1815390b5d5314e42d794e4390b5d5390e42bb98a4390aed6290e42d794d4390b5d5350e42bbd894390aec6250e42e750c4390aed6210e42af5974290b3d65d0a42cf54f4290aed65d0a42db5974290aed63d0a42bb9874290aed60d0a42b798f5190add63d4642ddd465190a7e63946429f58e5190b3f42946429f9825190a7d60946429fd8d5190a7c63546429fd815190a7c6054642dd5445190b7b50942429f98e5090a7d63942429f9865090a7d61942429fd8d5090a7c6354242cfd095090a7f61542429f1855090ade6314242b758c5090af66114242bd5845090b7950142429f9875350a7d61d4d429f9835350a7d60d4d42d7d4e5350af66194d42bd5865350b5d5314d42db5885350a7e6114d429f5845350a7e6014d429f5805350a7e65d0d42af9974350b3e65d0d42cf14f4350baf62d0d42af98b4350bac62d0d42af9874350abd60d0d42af5924350b5f5390d42d714e4350aee6290d42bb58a4350b5f5350d42d714d4350aef6250d42bb1894350b9f6350d42e7d4d4350b3c5350d42e714d4350b1c5350d42ebd894350abc6250d42eb1894350aac6250d42af1854350abf6050d429f9944350abe6410d42e750c4350aee6210d42bb58f4250baf43d0942eb50f4250aee61d0942bb5834250abd6390942ebd4a4250abe6190942af5824250ade63d4542b758f5150a7e63d4542d798f5150a5e63d45429f58f5150b5d63d45429758f5150a7e60d45429f5835150ade6394542b758e5150b775194542dd5445150a7e63145429f58c5150b3f4314542cf50c5150a7e60145429f5805150a7e63d41429f58f5050b3f43d4142cf50f5050a7e61d41429f5875050b7b5094142b7d8d5050adc6354142bdd855
  | 50 => 0x90d439f9875250e7d61d49439f9835250e7d60d4943dbd4a5250ef66194943bd5865250f6d52149439f9845250e7d61149439f9805250e7d6014943bb98b5150eed62d45439f98b5150f6e62d45439b98b5150e7d62d4543db58b5150e6d62d45439f9835150e7d60d4543bb98a5150eed6294543ddd465150f7551145439f9885150e7d62145439f9805150e7d60145439f98b5050e7d62d41439f9875050e7d61d4143ded425050eef6254143bb1895050ef76154143bd1855050eee6214143bb5885050ef66114143bd5845050f7950141439f9885050f6e62141439b9885050e7d6214143db5885050e6d62141439f9845050f7661141439d9845050e7d6114143dd5845050e756114143af5924310f3e5490c43b75924310e9d6490c43d79524310f9e5490c439fd954310ebf6550c43cfd954310e3f6550c43afd8d4310f3e5350c43b7d954310f5f6550c4397d954310edf6450c43e7d914310f5e5450c43e79514310f9f6550c43a7d954310f1f6550c43e7d894310f9e6250c43e75894310f9c6250c43e7d854310f9e6150c43e75854310f9c6150c43e7d814310f9e6050c43e75814310f9c6050c43e750f5210f9d4394843dbd4a5210e7e61948439f5865210e7e60948439f5825210faf4394843f390e5210fad4394843f350e5210f8d4394843db1925210f6c6394843dbd0e5210f6e4394843db50e5210f6f6194843db9865210f6d6194843db1865210f6f6094843db9825210f6d6094843db1825210f9d4354843cfd0d5210f5e4354843cf50d5210f5d4354843c750d5210e7f61548439f1855210e7f60548439f1815210f6f6554843ebd0d5210fce4354843eb50d5210fcd4354843e350d5210f6e6454843db98d5210f6f4354843cbd0d5210f6e4354843d390d5210f6d4354843cb50d5210f4d4354843c350d5210f6c4354843dbd855210f6e6154843db5855210f6c6154843dbd815210f6e6054843db5815210f6c6054843e750c5210eee6214843db5485210f9d43d4443bb98b5110eed62d4443db94b5110f6d52d4443e750e5110f6e5294443db54a5110f775194443cfd0e5110f5e4394443cf50e5110f5d4394443c750e5110e7e62944439f58a5110e7e60944439f5825110f9d4354443db9495110f6d52544439fd895110e7c62544439fd815110e7c6054443e750c5110eee6214443bb5885110f6e5214443db5485110f755114443be9805110ef96014443e750f5010eee62d4043bb58b5010f6e52d4043db54b5010f9d4394043db94a5010f6d5294043ded425010e7e62940439f58a5010e7e61940439f5865010f9d4354043db9495010f6d5254043cfd0d5010f5e4354043cf50d5010f5d4354043c750d5010e7f62540439f1895010e7f61540439f1855010f9d4314043bb9885010eed6214043db9485010f
  | 51 => 0x40000000000400200000010000033000400300000110000001000000600280000004000000c000001001100000010014000000000a000c001002800d00200050010003000400000000060020005002c00b000000000740200040012000001000000150000005000002200100000018000000800a0004011000400800080030028000000003a006000000040000000002001000200340020000005000800000000020008009000000100280010000005000400800040160020002000c01e003c007000c00b000c0010028000001c000000400100000000000000003c004007400000c40000000004003c00b0004001005000000000000074000001800200000000018003001000200000020000004000800f000801e0030005000c001004400000000010004019000c0020044024000c010001000d000400b00000010008014000801000000190010012000400c004000400000040004006002c0020000003000000800300050000000001c0040018001004c0030080000003c000001000500000030014001000c0020000005001800e0058000000000900040080010001000400400180080000016000000400180070000000000000a0000000003803a00000500008002000000900380030000003000000a0008002000c0000008001000400b000002f0038001000000400180000008000000c00e00000050038011001c003004800000200090054000001000b0050001005c012000001d00bc00000300020028007003000000000010004005000000301300250000000000c000001400a001400100880010002f661d4b43bd58752d0f6f5294b439f98652d0e7d6194b439f98252d0e7d6094b439fd8552d0e7c6154b439fd8152d0e7c6054b43db54852d0eee62d4743bb58b51d0f7751947439f98a51d0e7d62947439f98251d0e7d60947439fd8951d0e7c62547439fd8151d0e7c6054743dd54451d0f7b50943439f98a50d0e7d62943439f98650d0e7d61943439fd8950d0e7c62543439fd8550d0e7c6154343bb98850d0eed6214343bd98450d0ef56114343de54050d0ebd65d0e43cf5974390edd65d0e43d75974390edd62d0e43b79874390edd60d0e43bd9875290ef561d4a43dbd4a5290e7e6194a439f5865290e7e6094a439f5825290f3f4354a439fd855290e7c6154a439fd815290e7c6054a43db5485290eee62d4643bb58b5190f775194643cfd0e5190e7e62946439f58a5190e7e60946439f5825190e7f62546439f1895190e7f60546439f1815190f755114643ded425090e7e62942439f58a5090e7e61942439f5865090f3f43542439fd895090e7c62542439fd855090e7c6154243bb9885090eed6214243bd9845090ef56114243de5405090edd62d0d43b79874350edd60d0d43e7d4e4350ebd6290d43af9864350ebd60
  | 52 => 0x3c00400040040004007004401200200080000001000801b000400f001c00b001400300500000004003000000b0008003002800a0000000006c000000401400000000014005000002400440000000005000000000240000008001000000c0000004000000c00100000038001000800300080010020003002c0090008010000c00100080000004004002000500c8007000400100040020008000000401100140030018008002c005001c004000c00000e40180004001002000e0008000003c000000000300600000008000000000200000040000000003400200080030014000000001b00000040004002003800100000030018000003c00f003c000002c0000000003000000f004000300080110064001000c001008c00200300110040002001800100040010000002002000200080030040001001400100680000000000001c000002c022000001a00040030028001001c007002c00000080150010002000800700280010000004000400a00000110010004002400f000c014000c0110004001004000400000000000017000c0150004007000800e0000006000000e005c0020000008001c000004000200340000000000000c01c00d800a00080060014000002401c006800200080060000000000800900140060000003000c007001c001000c0000020001007800200140040000007000001d0010000001002a008c000001000000980020004001001c00300e40160010000000800800000050000013000002900540010000012001000500100050024004002400700440000024023000801e000400000280010014001001400100680170020001000c00f002000000040000034004004c0030014000001c002006c00500200060000014002000200040000000018006002a00000070030000000801b000801f000000000700030004005000000f0014002000000100000090004002000000000040080018001000c00c002c004000000000400050004004000000400080160088000000c00000140050004007000c001001c00e002c00b00280010004011002c00700000230008000000000000040300018009002c00b000400e000800200040010010000000c0050048003003c001005800200240010004010001c0000008001000400500540040004000000000000000010004003000c007006000e000c00f0008019002400000000020004000003c0030000000008c00600040000000002000000100000010018000002400000080000028001000001900000140018000000000a000000b000c00100080010000006003c010000c00800080000008001000000d0000000001000000040060038020002000300040010000000003c000002800200000020044000000000f0008000000000b00000010038001003003200000000004002000c001000
  | 53 => 0x8002000400c00080000000003002c00b0000027000c00700040030038004003c00000040000034000000000600080070010002002400a0000001002c000001000600640090000000000c0010000003000c000001c0000004000004800c001c00400100050014004000000300100080004003001800b003c002000000000080010038003006000000280080080029006000d0020000006801a00100000010003000000800080040010000000800500000010024008002c00000040000018001000800b000c00b00000020040001000400e000000300140030000001005400200040000000001000000e00180030000002002800000080010004011000c000000000500040000014003000c0040000007005400c000801200700000008001000400500080010030001000000900340050000006000000000040090000001000000a000c0000050004000c000002801e003c000000000000000000020000000c00500040000004001000c00400080000010011000400b0000004002001c0030000000800000140070000000001000300380190064000002000200040010034000000000b00040010010000000400200040000000003000400000000030004030006c0000008000000400200000020050001000000000000050010009000800000080010000002000800800100010000009001c0090008002000400b00100010004005002000000980000008005002c00200540210000000002800000080110048005002c0060018006001800d00040090000000000c016000000000000050010003000c005000000200000050054000000800e000000a00080030014000005400200000010000001003800d002400600340150008004000c001000400600100020008001000000400000000014002000400b000003c005c00500000010000003000000a000000900440030020005000000000000020014000000000000080000000000002400300040000034001000000800080020048002000c0060000000000c0000030000000400500380090004001000400b00340000004005000400b0004008008c00200640080004001001c015000804000500000040003003800800f0014000c00100000000004000000800600080000010006001c000000c00c0010000000000400080140000000001400200000020000000000400000000060000003000800000280020024000001400200340000010000001c0000010000001c001000400b000c0030000001001401b0020005000c0030038000003400000140180034000001c00000180000014009004400a00000000004001000000000840030008001000400000440040004004001400b000800100280000008001001c001001c001000000200000080000001007c001000400200000010078003002400d001c00
  | 54 => 0x2003c000001400600180030008005007c00f0000002000c00c00000000000008007402800280020000009000c00c00200020050015000000a00000010000001001801e002c00500300030038000001c00000100010008000001800c000c00000000090000001000c0000004009000c0080004003003800300340040000002000c00100340030000007001400000000020008009000c001001400e0008000000c00200480040024001000400100100030004000004400100440020000007000800300100020000003002401e000000200140050014005000000200080140000003000c00e00000020000008000c003000400000e40070000003000400000080090000001000801100000000000001004c000000c00c0000003002c001000c0010000009009800700100050000004000800700080010000002009000c000000800300010008010004000000080120040005000c0090028008006c00f001400000000060018000000000700080000014000000001f00100150004009000c0030004002000400700000060000007002400a000000500000010000000000c0000010004000c000000801500040040000004000000000040040008004003801700000020018000004002600200070004003000800b00000120000000000000000040060028000000800000040010014000006400400600010010009000400100000030040000000001e000400900480070088001001c00000680020000000000001c0008003000c000000001b00500090004000004404b00000060004003000000000480000008001000c0070004009000000000000020004008000000a00140120000003001400e00000330040017002c0020010000004c0000020000000402900140000004014000c00000140020020000000c013001400000080000030007000c00500140020004001000c000000000500080290008000002c000000c001000002b00180000018006003c00f0004003001800600240030000005000000000080000014005001c00300340000000013000801100000000054006004400000000040044000001c01a00040180000003000c001000000a00200310060001000c014000000a00000220008007000400d0000002001802100cc0000000000001c001000800d0000006002000300500120000005003400000240020000004000401300240050000013000000500000090000009001c00000000060004004005c0000004023001c00000040070000008002800100000000038005000c00a00000040000000004800300100000018011003c002000000000540000044000000c0010000003000c002000c00900080020000008001000500c4008000800000700010000040009400700100050000000003800000040130000008000c00a000000f00a000400
  | 55 => 0x400900480000014000000400400280010010001000000400000030004007000400100380110014002000400600040020000006004403a000400b0010000000000a0008001000c002001c01f000000800000030008000000000000000020024002000400a001400000000030000025002801000040020020002000401100a0005000000000000040078000005400200140080008001000400000100030008000001400900300020054008002c000002400000080010004000003401700080100010008001c0030000049002c003000800200e40010074000002c0100064006000c0060024000000400c001400d000401000000000000002000400300000050020001000800b00300040038007003404700100000008021001c00d001400000340000068003001c0060010007000400100000130044006000402b0014004006c002001c00000040000020001000400c00080010050000001c05200140020000004000000100040040000006000000000100000000009000000000340050004007002c002001c004000000200000080004000000002d00580060014000003800a000000a0000001001800a000401c0008001000000100040060008001000000300000030008000002c0020000001000000f000000200000040000007001c0010000001000c007000c00000040020000000000c0070020000000000000380040008001003400c0008001001c00000080000068008002400700000020044008001000f0000003000c007000000300000050004010000000a0004000000c003000000d000000100380000024000000000a0030001007c004004c00400040000000001002000f0004001000800000040000000005000c0030000001000c006000000000040030008007000800900080030008005000000d0134023003c01300ec0020004002001400200100020004004004801200100210020001001001000940120000009005400400a0002000c000006c0000018000000007a000800400200020024010000c00700180090014000000401000080020000002000001b00200070008001002c008005c00000040080000005000c0120004003000400100080000000000000000400080000004000005c0110000001000400f0088002000800000080050000001000c00400180010004000001c0020000001001800c000001c0000019007c0010020000002800b00000010018003000000a007801200340000008007002c00800180040050000000000000000000000002000800200600030008015000401a00180020014004002000000040040014001002c00000140060024009002800700080000004002000001e00200010000002000400f000c00300040010008000001401400d0005000c0080000000002000600000030020000006000900100
  | 56 => 0x1c00400b00000000001000400e0000001000c00100440030004006008800300000000020005000401900080010008015001c00000000010024008006000b001000000080090010001001400000180000000000000800e00080050028003001c002000c00300140000014000002800100000030010000000000200100010018003000000a0030000001c0140008001000000500000020000001002800c003c009000000100140030010004000000d0008005007c001000401b0000004002800400180000068000001c0050004003000400e00000000020004002000000180000004000000400000140000004000000000400c0002000c005000801b00300060004000000c003004000d0000000000c0030004000001400a0008006000803600380100000003001c0010034000000c0070024002000800000440040038000002400c00280030000000001400e000800000000010078009001c005001c0010000006005c0020038004000400d000c01e005000600140020000004001800f0004000001c000003000d00080080010000002400c000000100100010004000000803c00480030014001000001e000800100200080008002000000a0004000001400000000030010006000002c00280000000002001400200000000038001000800100040000038002000c00300040010000003000c00200180000008002002800300240000000000000000600580050014008000001200080000000001005000a000000000000010004000000801500140010000000001c00100100050004001000001400000020008000002c006000c003003c0020008001008000f00100040004001003000300000020000009001c00200280070000012000800100100040004000003000500140010070008002400000c40020010003002c000001c0060004001000c000000000000400030008008000c0010010019000000200040020018003000400600140060000002000c001000000500040000028017000c003000c003000400900000040024000000400900040060004003001800100140020004004000c002000400f0004016000400300080000000000000000000100010000000000000d0038001003c001002400300000010000007002c011000c00200040000008000000c000002000200000050008001005400700300000080002001c007001c011002800a000c00c0000005005c005000001800000020000010000400100100010000008000c01000000000000001000000b00040070000001000000f001c0000030000000c000000c000000000d0000005000400000200100010006002c029001c00700040000008000000c002000c010000000000080060008004000401f001001a000c004001000400400010000008000800000000030000000000c0070
  | 57 => 0x67e13db22a30e8eac34a2a066420260d00097a3b94af808b8f8d856353fc476000019b72b2655940000000000094acde9000014ae60e0000283545f000005d7199415ce312865b800000000000efba90506887be4ab799bb2abc2c44f08007a56602ff41b8260b50805428b25995706c4740c160a39d47ae834cdf88c09136e3d8000004b153f80000000084d0000000000000004c60ad1400000000000000127b0e9c091c27f804389e4476e6aecd6c8000000043f8417a9e606909d2cd79198b00004fe8000000050fa1dd95342667000081e50a6989e2a0a000117200001d366a9c23e8874000092e45838a20547c00000001d313f4227c800024514a80000130a203953460018000000000200140000014000000c0000004004000000000040000038001005001c000000300000090000000000800100040100010008003400000040010000002000c0030010003001400000040030008002002400300000180028008000000200a000d000800600a4003006400000200000024003000000000040020048001000000000000040000000000400400000060028000000c0110058000000400b000000a00000030000001000c0030004000000003200180030000002000c00b0000015000800200100090000002001c00700300020004003000c00900800000000000002800300100070008002001800300040060008000000801600080020004002003c00e000000b00c4004000000100000000004005002400100080020000006006c008008400900000010010002006800100140010048008000c0090000000000400100000020004003002000000000010004000001c00100000020004012005801c0014003001c00200040000030001001800d0000000000400f0028000000c0010008003001400100040130000000001000000040070018006003800000740000004004005c00100080070004001003801000380000004004009c0010000000000000200000020000009002400000000070038003000c003000c009000400000040030014001000000900000040024005000000700040000004006001000100000010010002003800800080000020001000c000000000100040310014000000c002002800100180060000003001800601140020000026000c00500200020008000001800100000000034000001c0050000001000c00000140020024000000c000002c0030018000000400a0010006000800000000010004000000400500040170004000000c0060004000000800d0018003000000000040120010003000c004001000000200020004005001800900140060000012000000000240120004001005c00d000800c0004003001c00000000070024015000800100000000010000000c006000400300080000010000000000700300080028
  | 58 => 0x127b068a0000f788ffc36c47dd80001fe821aa00004959fcc26300000caa0e82000000005d4800021d40000b5a000032140000000000000000000000083a0c1c148000022f33bf6000157e0000395c0e7c00000000e6ea4902e580000000729cce19b1b0000908045c9c314d3a0000fed9c680000000000000ee3704163c00000002e60000000000003c0a32746bda0970000000133229a2056c223d49d27f6185c10cd57ba5c633a422f4e8ea47f23968cec7eaa74516be19c14e626514bd6167d47e29542350ac182a7a41e2a983a98efb28c20bb605e80000cb8000092704528945049a2050000000036c60000efd135e28cc0594aab1b36503c61e00001ca03f3240f0d7087184c8c4f6d00a8f25462822180000ab200002a44906800000007ad93b980002c8888b50c8000044b47b50a569b8052965afd3d716711bee000157112853e30143cc2f0000000014b0dcb161f37601bc800024934a5e0000f44095a421630a8c0e8d3909b01bec83184cb00004afc000149e0db66b4113381310f28420c89d0d8f1626715c768a370000091a0000218b000000003809d1952aca0dc00000000f0c26f804c28e800001bf80000b3453bc6618c7687310000193447499cf000082213d184120000000000007ed433028f40001738471e000000019360d187510000000031fc9435200000000006de479ca5e148808c4c2f923333ac4000129980004180388c00005fd156e000110500003e528fb867e82ac226a88406cf80552f9c0001135a8794af42bed3f195d710aa000057f0bfe0e945b300c1038530e8202000025952608000089924d82c00000095e800055f46cb48669c67500438587ee1a4c1678a5189c5851324dc6c1c40d992c102603443c188624556000000020db528084b140823542b9a0000000237808ec2d8800000ea000095f4000000003dc0000000205c2cf831c801487174d04381800000001b7c362c8e88000262c346c8640b6c559e086926da5412c20096107fa22427960c3c8d22443133886f0ca09dbb3e3c1e203bc265949505744980991507e4266c3c013fd272e043d54d8b2a1b422b20a391b674cd694fc4cea31244e467404b286b43d5e5fdc60a0a01220e03d0221874110f8a618b37111c22de057c2fc0da93b082e7cba20eae39f00b382c6040838fc000040600000000072c0000000245e54054fd1fa30fc40294d100000355a46ed1268000305c000030c0924000000009d6800026426bd911f00004b762a50da593e8043c0780acd9cf6302a3c013c5000049f61cd53ad0000000006152b8000024461a4800010a60000000033b216755d4000133e000000004c143cf063548a83740ca41d9a261092d506193592ebe4d353120000000067053d88000329a86a400000000000000075200003194000000000000000
  | 59 => 0xa560400007f20b5238ed334800000009bf881baa3526465145435816c15c288ccf50a24902b4815cbd080002572056c00014e231b87888000000012602fd86f5908a447857d46362a5308aa026d16c93e034e681d81021aba32842c94da494a6200691b4aaa80000000a8f48c39c0d09342e24d7b97fb124c0000e2e957f10b600013b3109601201f0c7f821471ec6aa0c0000000139e57b4df0a720377a03047cd299109380160f21a10754546f9cc989ff4395237092b616b53fde27dd05e219f12760efc69822c51eb63208ddc8a624fa85f08788a1c53e869c6c2ca193a3942944c7ae9e0f270e54a0fe920af2f76450c00000004c76927c3cb9ab94ae88c8861f054520c0a5c888b9c711ac44a5800006a219140000a150000000000000001183425e00004c700260fc607988ce04920ec42e7512c09e92dba5e4ccd11a7a00000000f67856519a82bfc0002374000015ecd698c6203baab2463384203f3a1d2c5c61c3736648cd000000000fe03e70000000000002204f33a47c527083b8d0ba6f32eb652151c403821d0e4330c6d800003e48e094c71b9f4e767e9cf01a55e1fac06e49ebaa48513a5d5816480004896abb0063a52311cc000142426ef0000439c00007494bde4a08c1f8d2f04d018443f324f7248400c14bd15782a602d90000000000001900000000000004769082a11800000000b4512b000005b440000000123283240000aa01e7074700ef190f000000002e48000122e0000b5b8ef22e8c154000002f3440674ccecf1bb6550e67fc1e517e72c8a4fac0000c7b0c3e449080b8000531a51d8000000056182920e971a3040743e31503186108962cc065d8b1c0000764c5aa08491c6e84a53eb914d19329c780038244528e000096e0b36000011ac0002a551a8210b8000000017868c851e1148d000056d11dd80004bba00012e90560106644d87db19921d1e6cd029f24f84366000000000002c223a58d9c862046d60000bd506d91c369020476085e22e862654820ad24702568808f1be4000027584b12b2100002370fdb2ac037ee92f8e380e07126631bc3e11e8700007e941c5200800002f68e6e9a8c2938064042002fe4b4456e07ae068100000000da700003d1264a0d60055d113454510bfa3db42540000dff8000020600000000b3100001be800000004f5400008879a7d500c000000000000df80000a9a290d0000a91800005b331542c143bc9ab6228c8804000069f561e00000000000000000000000b7d0000768000000002cde269c15287523e1a6190a2b92303c3e9bac28daa6c2c146f3ccd304293b585bc849d171f4be40540b3c25542476506539b8445524257bc257269a3ecc1254a3d000011b61db4fc79aa400007d79239a4e6000000007130c872826a4a10e38876046c63e116a890354082ec01b4
  | 60 => 0xd80993a729b30ee800db4092a04400000003f3e1ae80001b5424222694df30000000043acc3aa64a4132251cbcc9fa832ce04310a2831d135a46c42552ac832fe7b8c83da37d4b0027e86068e7a02441bc07269909263e314512f000001120000ed80e13224a0000341a18a06840000cd2999000001720000000005fe569cd811e7908262c40ba90000046e155c148115f00005694e29935f355e00009f21a020890900801f190b416c011cd618b0050b08528000000016d226401e405a03fca59595a30000000000000000000397e000000000004b1a35a0cd88000000085400000a3214be4fb07bda8801c72000000013a74fe80f7496b89bd2ffa73650758953239c33b92909f212f1a30906568c4720320aa14682a893cac3d9cb9e1c23333637bc94a8000475608a8817845e000009d400012da000014101099c483f2600004da0000389a61b85ae00001a2a436c8f503ad209a1e3c000231c13f0568400008da0608973926a8c8329b280740000b440bc460c0939000050e200013b90bb90000000039700001572000119f20661fbe0678000000000000001294917b25eca8852280c94521857f124f287a1c82667934f8566333e927555e8000217e323c5c382f418788e7c7f022c73b4e65c149e21b7004ea3903cc00002dbc000000000000000a5354d70000401229280001c0b510c06dc00021bd1788a87865a14384d647ed4baa8000491e480400004fe00005e04599873850da4dd0d8f9ef731d463a0760286e16ba47a4699a2002d165804c22016a2c627ec0be4840e36ea8eb91678425439ea36852093d100009c3497f940635d4744479f800024c09640affa32d2266560c6cc03894f660580642a084158a1d3089d896900003108def9cb710fc0ac800028a00d5a4574ad027150ee4529d2fd8acb4d804164db8000053722ba45a4a376029835cc25597ef422e017cb16943c3b9a02ece09117501424858e0d0e5a29982fc858a8b9a13f87b3909298223f168f29453996f4ef20000b969dfc38be94152df1f3600985fc400007692f9416c10b7286007a231e80000ff8000000000001bf049b46268f6815a405ce17ed04308370dcc374c9531e9403d8a5f46da80001fdc7578b9d25e24a027998f76825f140c0000f34060d34e45b8000003c01f264a10675800013aa698400000004c5615b40000e863b52000006b85df00000000000000000005e4400000002a4060d80001d6400004fb94039e071d3400000001c4e15cc0000000000000000000000000038d214bc73321d400007f40f040000000097605ffa96f0000998c47f0000000000000002a1432f0000000002af205018149030ee300001b340ba8000118a38901bb8000000007c000003b300009c255a089da08600000000120700000610a7f17a32ba60b78264a5b52d1
  | 61 => 0x5be00007fe800000006e40b132afd0b7ca38400011aa3d4059a003780000000856c0002a8548307ab14ee800056448cc40002a7907b45c600001cc8120c5c50eee24a0048436280001efa431a86705f7000024245d2cb1587702ec027d12109b840fd23c791e60856143662754b31354000066593739cad28580c000000000000000000001a51563a7934f1c160e40d400000000a7a00009f00e858000509a1d514ba8e854e4c6034f06117c319a50c146c9ace0d4ea5dce4403ac1a163dd472210f5343c2e180000000198eac9800000000000262c0001c0746209674e452910000000007310000000001a088280000000a98c26c807611d60000ae0240f4e18000029509b818e256d8f251061000000000001a0c0aea0000e882a912f6e70711398dfc29543f60350138d41da83b08c6800043467170d37147455542ab80001c270000701511ca20f42fa8ff8f7f1a1631be85b54e780003be0000127c800000001a400000000026e00000002b18208e539d53b1f0a35fc65ec00000000c0c00000002a410000404852f0000361c48ccdb5a05500000000def099600004f58fa996eb00007b8800011bf0fae0ef062200002b2e7d085a79a22000059d40000000345856a86d1800037c600007e11cb02c407ba8981946704327d6c3118468000054ac0001d6b2a940f59016a42215d4a9f0f720a4500000bd8d2e26664e449740a31003201f4077024da71d0fd6a1f000024234c1218fccdc8aa41bac58d8cf8a7e13e8a5f8000017b90000000000000001aec0000f1e00b2000018d8bc822144726693c15102b33bfc62d8627151603c65c2443292dd49b258a0fca0eb70d96ab64a541ff20ec8877d4dc20940bd221acd17901a1d742b7c8f324a306ec00015a1241d0cb2096933802223a4072f41eca05f00007ff051d0784489c83bd3a029d7368e6b502988c8d351600008c289410d4c9e94a8100002d7829402f40cf8000000013800db302220000fab9d92000000000001a6b3c023a255178b7537964ed46b6228f3c7637fd4419e230e085a0d1c31b402a5849bcca30980472e43e840f161b44844f71123158625f4275d1959f493912000109f1c6018e04f413e894c2100e98654ed1c2a251816f4c88ab3735a200005b926560e1a13d52d200000000a1e05e71f62343422a51d60a0400007c080002a22000000011da1aab39e40af000017e2031e0ed000029074e660000c4097984e50000127fa0e5000000007ad0a35000002882b080004cee0000000000000009ae08a38e6e115a1d6caa695703b2084692b725681ddca2407491411000064d0c8f00cb3efa649942212813e4c614cddd13663d1eaa8c9720b20169831905bd023042260000000028a401430e083a1379151897a8421a2750000354c167a4ed4e86487d14
  | 62 => 0xc119640000a27c8d90efb28a663e874c20e754100818420aaa236c269b44b58637359412fc9979e3d33909b353cb80004d4e675000023fc2440712c9f3000022fa30bc99f25591df894d4f4f800021602dd8ce693c90000000018b0d6d000003c4000000000000000000000000000000f38000009b600000001aae00003dbc0000000528479c800000003ace1acc000293d3c4a0000aef800000006634000000000005a5800005ad00003500383000000001bc51590246039430300d9a63841e667dd30082cc4d7405f52d2a3b5216ea7e400014f70000000048484024cb6279c00005e600006ac0bc1812916b000f4613a95f0d72152cbdf150f3a3435110cf0ef43e602e28000119800006b1938f9647307c52ac9ed1bfe07e63b84000000032ac000101f144b4ad4119549886bb07060000b02207d38dc91905aca1ff4bcea7bca5c8000400a7d50271800000003bd4000125d31e874e8ff980000000774512a1d490c9ca7a000000002a5ea8140002385000039300000a1252a29b980000000000000000001b5d1bb2000000026a34be0000136e026a298000000000000000000000001d2b27560000fb69d2530484560c709c1449942ead4119072290e333011c88d434d23db8dc509201722a5b8a72149b537c92a92170dcb0dfea300151802c1246372536980003fae1314000019d0264861000001c71a4661944c929021c5c0001025258716281c4514e000035366405452177100008614a2a80003b5c48c85dc0e3053b65498000272542e2a65003f00000000aa0502583933e2e5be466d06d04ea200000000000000022d937905862f0a000064b90f02b9e16980d6a47154b0789944117c0000039d4df62045080c959c000000006e258d501da63e12dc4f381b1825e0cf464ace250fa42f3e3bb4767a09800003530d149b1700004eb097980002d2600004a1aaae0000000008994db3ce2a7c49f5000000000c640001b1d1d16abd4c7609b10e9049b4fa6800022cc00010aa800042c46584000000000000000538973f2c5215a11a3997d242e13791690e202752371125b8218390200000b4847e00bc00010c0000000007700cbe1bc2554800001e71b3c00004b212eb8000149871b45fa9fbf0000000040d10ba3534a3b05e98cf700005c291c8800000000000d15a2e31602000005406243b90000009500000000847494499493c58acec4ec9b152794751883210e3095e428d28a82611466427c000268c27ec36c00ed951a345a835d0e815d41b9e772d1832a62519e77b92ea000008820a2c1b203464aa480a8dec14b10eea0000d4798a0323e7930070841d20d033a400014b200000001132a1cc175ea5a48241fc840880ea105ea02f0000000159aa69736547a094348a2741648b080002ab640365bc400014d01eca000000005d600
  | 63 => 0x5dc6e8542f0c0700008d44d8429f2000004908f18bc20456a6cc00017944b5a1b1cc0300004d666078f8e80002bba543800020d100004344e719db900000000000000000000001232aab10000000130987423fc000002779e6307da0000d4021ac000055b53f7000000003c34000258f01586df54239ae400005f200b20fec424e94e9323800000000000000000000005bb8000000000000000d931dcc0000218cbb60302205a282800000000a8c57b0000000001a80254000000000004f10f60a27a0000000147f1f7c22021fb8000000017407944172800005b8000000019580000000102700002b1e00000000ecb13c60000000000021ec8a2cc5980000238aae4000072a287e3fc8d2c0499000032f4532204c2d0c2b593ad91d51bb4a5c4a260ab514d000009dd1fc7347832fc73f9ce93ef45725455277c532471f400006f53e580000cd5988a0cbe8771553929a0e0e4488dc7a0933ec84fc89cc04d154f6a571118109d34ee0000e0798821b585f44962aab836fe1ba10e19dc5000091880000000276289a4f3ea1c405727e900000000000073b8153023f4b4c59200001e7f00003aac4aa800000009030a470d2c165ca1d838512b41ed20db85cd97f45326a19c1b014524b8e066caa1259a44a427009dda2d826b85728a7a80003634000000006ab456a28fd55812e13b02429c9158ded0000093c39e000000000000000217826c00000bd49d522daa00000001bbf0bea07acd8929132e1c35d00001b5a4f64529072e11120ff65490c4a88c0463611e800006673acc28d91071d68533c39b4c5e825541d011ecafda3360a420e985a3a26e00000e047c8996a098656500000000000000000000013000000003c8267f1f5c000123c80000b8800002ea0682125000000001d0e00008aec000098f1e9a479d33620b935148a848770000108ea3b8559800042083d48c90000012083d7cf8a90543adc12f400000004a62949042d0753246200004efa54a000000007750000000072900710d6919f607d08dd297014b834f03caa50c0000a8e820d000000002118945904f153603d4b8d80000000086c000102c0000000000002d4426a67b874e964a0f669c4d33000d9262a6e5c00000000000580c0001694000062f000000000000000000000000000856884989db555a0000000000046a400002cb800014ca921c8e5260a473845ac000087f36b2a2d065f1e6228146b60e3d0000000036e10d2a64e3ea475b476700003a304420b63a2e10862039930a8000309200006948000000005540000226128433c042c808b0c06145c9efa80b00000000000035e00004218000242c371c82c5212aa9a141a0000bb280001e325e94f1424b61cf01e44f3f147750582d00a35867150ae0000d10800019c6632400001bf0b029c38d1c23002f400000e
  | 64 => 0xa9c000206230746024000000036263aa80000000423c00001a7945f11508f65557a3e35600000116a20dc04a49284c2c00000c00000037b0000000000000000000341e710cfc50f8120006fd000003d512fe4ed8e0f8e3800001098b33800029826f690b32a7d165000000002620000000008589e314cdc8de443926682f5c765911328d404f26d15244a87e000079040000000000000000001f8e1e880000000236036421fd40000000000001b09f81090353a00000000c1d095a01e03910d5f3d7049d93cf1b6500008c8c0b8922d0c700c5d0f8a85d25e888fcf5e8ced00000000ca21ad64f927afce5980002514538000020ca000071242e119b000000000780856e10fa00004c882eb0000668cae300000f8e1c2077e97d80000000032880000000607d4a901392336411851c0e6f19d00318c5f139415620e2d5628f7f24183aec870274412da04a00001d0d0bde55f443891a536e800000af1df2167c2d3529ea30248eea1fc44a9c6b2a2e494132183b73efe503c7dc248648782ab446b8f4b000072f046923ba0000147823018100000387d288800000000000caa822110326f005b9800016484914000000000002b8959919dd13c400000000000000042b41f580002a6200008c48f59361e966c1fd8c4b15b63c1c21f00fc294a1b1543a28810f24946131329ec0000139c00000000000016d2f4000000003b688d117b61ca87f9812180181b4e2da82651a372746000095016612c1819680d6000000004879595800000006dcc89180003a8000011d30d0c10d200000000a4b0000a0f00000be00fec2f142cc9df13d9245f80ae9d7a0bb427c1174a94f24742b3473580000f600000cd380001ffe00009a1247800008868000007d1ac61aa49779e523dac81ecf281b2200007da11dc0cd631ee084854404bb2e5c957128f80004948000000000000000075c000281b2f883664000000000006b54a9f843c000000000811d3d0a3078d8c778000203c39dc872219900000000c83000000007b4800013cc0000000072888af04fc137446808d9000048f00000cca12b87ee00000000489a88888081c4f0000105c6e6803800003ef13b2952909f200000001ee8324669d129a1471094c7af857c80000000000000022ed29f8a03caef191c00e680980f5128820fe1d6548c017927e8976519929970d947ecc9df1c6a0800852442c11f4284a42ec0000b7800007fa94ec8000473c7d74d25000035dc000064f80003266000049aa8c548d2113cbf20b22309c8894aaa0c6a4cb474281ca097733e829f00ea098536e200000ab800f000057a5203208b4fb2a2985b001d618a600004b804e100000c787cc09ab2acc52540c3985113603908cb028660ffc81cd312a7d84b3c0c60e7988510000333800012f9534c00007c400005
  | 65 => 0x4f20337c43d0f6a0000000050f035519ea9c3c5bb894e06362110bb1a0512b204020daaa2eb2d9a9ce4ba6800022d879243d3ab013b8ca2f450e920b1748624018f9d05136a3b98eac0b7e00005c6491b0000000000006b3000000000000000000037a0000000003f4000032bc6b7054900000fa934425393a8e0cec8a4254612c696800da937648a654c8639889c3d1697b4fe70a131ff471b0c921fe44a9a7a58b72140b00001eb42b509162fda7a611be1cff286e194cae3800008ae0000c10a61f224ca31d1489d7220ec11994470d93477a8ed88a7069a47422d54fee98114408058443ba73f420c00a82f62b24365636b443c80000d4872a08a8237e203e7ef066f138351bc1924000077b15204da12fe0e8e45327ee4ff59be500007fd500823561bc6459c000093c328e000000008700000000000004c7204c9e1800018ee250e7e000000000483e2e4121b898c2ca421200000ace30aca54098b9f190000731d25280001f581cb4a44aa9541aa748cc0a072b190096100000d4724e88f740cca64f3794005111c0000545a0be4000000047bc2e1548a87163ba481a0cb88da239883728e75855b00006bf4000000009e429bc479930900006d906c6048100009e107ab96ef2adc0000000158e000025e400028ea2f145db93df8000516200000002586000043846c49acd000084640001dde1d44a994d970fa930ae9a8063b9ec2429e046c1dd011520bea45052325c208a2a4ad37f85730000875c90c800052f620407f21f331eec003428e8ca5000099708c8297c3aee3b40000295e1ee4803805d0000416047c146d8fab55b00fd484582973a123dc12939dec3710784542610c920126ff44671a5453585794a0d876f341c76bc9ac1bce275c2bad17882ca1dc418c4f730f0e0fb68f248dc15db268e13a872e9eb0098496a8ac60abd069a4c70538193549240170a1a02811846628cccc03222636a70cefe9fb1374000007450a34353c5d649b81af81c4466281e4800026769034ce004ed00000000c3b1e9700002c6414a9997475e6c140001a1100000000000000005ee0000ef78000405600000000000000000011cc800005ae3af9593800049341c1400026b60000417128e83be46741ff40000c1948cc5dd0b79a286511a629063187ac1fe88d84e77a00d0c16000135e170c427886e80c900000e86000020a8b9903da0000587a9e400e08acd48d800008a0272d0e101ba0e1630dc00000002ba47f0009e8fc7000047340000c8b553c050cf00000000000000000120e15a88ef911586bd24268b78000298924b28744000247b43e8a9a49b9826747e08d9004ea345312268a80000d6427821400000000000003d3d34000000000000007283db03f077b48028bd5559a000015baa9f421800000001f8c134c48f884210d80b8e9b28
  | 66 => 0xec6a2e02cb692a47b2009c52ba27408b4a81449c088300001e21114431b42169d5f3682a48ceb510c52e0c15654cf95212cbe78e40001e272180a7cd0520166517e3354a18800049dc000000000000b5c5a010ae88f220e200008c88000181c00812a18a491e6c00000000000000000012cc96f551664b6c9d91cd22b461fb0000000000001ac400011b310c245100000000172a5b2432a04b321a48c9c840056f081268004e99f862d320e01342282b53185e54fa88a54275e8b7d3c28dee07b08a053d800003782a0008a9922e29d00101325a6fd0694739548702e300005c2012e0f4636a421808488e6554d422cc3af1fc9159e2448000000042b0a60445a8000062490540001ced218400014bc12774efe01140b80e1839869da4a7610f800007ce08db00ca411a9614a76800000008f14b6da48221d0a66c4812339039c00011c58000464a00000002b170d000000c78262f30d22774fa317573ffc1748132057123f018e86dea1cb0e360d84c35800012805070a21836f12b22a680000000529220c917d14163e4a06042500000319c7e581521a2800629d044078a3b560800f00419afa5498a81cc05000000004008f198000024c0000245231d280837c0bd5968200000000c25000000004570a4081a02e0253d839487e0512293ace9da45228c251207b121ca08f807cd512000048567fe8b1f0d790000a24c0000eca22400000f6e17e12bdc000000028a2288223850ed8000078c000049b800000007c1089b80000a1a601cbcb913c2ad40000000000033961f011fc00c208442ed4c938000530800000001a2705da54540001fac0a1413f0b98896a000037480000000002c2dc159e00002fb494580000afd43d0885c00025692da89cc4000184f551497354960000000000011e725035456500000000000000000127080000836000000021fa30b453200001bb800000000000000001720000000000000006544c3d000030728ddc0000000322c82dc8b02296202a2b908821349000002450a000d20a6e6f88e4b1a66128c0a7044a170300c262d0000178b461885312bf9be84fd23e5400011a11aa20001469030a00009f4c0000989534098f054680001006a4a50aa000000004cd52b30d8725380000e19059030a49314b5580004ba20000fa50000286a0000e1c140830e4380c05724b43bd652f4c440000000080c4000177300000d6c898000000002efcbe68ee9104c9b40935a23b062800000001e470b7e1d1888c14031872000000026b421b8108c000001727784364ca9a11b30d408001ba16301c9e7e0547c9efd0000000000000000000000000002d52bfa91a800007682e7259fd1920b2c072a08e800011d3461e00005e48000122260a80001bc42ba00ef481205b5302463103bf20fd087e17608d6059e182475cd04e85d9
  | 67 => 0x90850140d4b62738000000012750b5b2c6611240000f34272697c4928a092513869a000000000000620c000064b00f80000fd014f1317451f818d15d8292000000000b7131aa9af87cf817c37507e5cc7a80f60d14a7587851c28000000000000000000023d8cb61d3800000e9c99f9d7c2ac8000069f124f247252cd404886740e800002e693655294034cffd800000001fa021aa251000017540000198000000005fe000000008ec137200000000000072500004dd80820000000000009ab8d5012672a8688e937da4df000035754d79748443e4e4428428fb25da9bd48ff8fb029f4a2646c68e31564620ecae29f371a8a3b344f71bd7469c70882e01a860190000114a0aca047847b8fee0fb14b4e9cd8389125b3032abf81f62826368800012d606282be80cbce6d04b609a4000113186cc1b063124bcf25fe22d02e5828f972053a830b02bf0000000085bc3a71a47117c8dfcfeaa7301e90a3982f19929500a000000007b607c4987117100000b38810d29c0000000016ec0000e254ee05c3d12a821500000000000133c00000000dcd000000001f486e08dc6000013fcbb795513ef00000000140c2b16376c000060800005274a7801c91d7a051448f8000267073593d40830462e43880000247369e00000001b8c0cd269900002ac117f29370000000000000000be580003b8800001ac8ed71f2e9fb483500000000000076aa35d0000000095500000000000011c0c4820b4a0ccf938e91064e2868334018a16ce87a400026111cd40001454000013280000f89800000000000000137b321ca0c93f200004e749889144800000000001062838750d400008f8866c42385bd9409a7a91d505a60000169a2cf47af06530000569cab6c1928de506a61fcc000137200000000d7301060000000105198251ade0000000208700001ccc0000000331020b400027af000000000001c91000000000000551038c55704a8205a44320aed3e909540cee9b1868ea58111566994cad0000014e5c4c0000000196091683d018b231289f093baa6ed000032d40a70f8f07c2098000000002c6422c400011ad00000000000124e00003318a85800000005f1800000002ae4786000028980000000000003b854ce38d5147000048c217fc000249848de5d3839629bb4cae619841fa47d0fbc0000e76154042f69a485270b5e20c40000c81180c4f7c74180001d561c64513c602146e1dba800478fa4630000000135e80001e0c57080001f0943721188313a504109c18890892a60085e5c113b7851100006395064227620ce065d2bca2b940d200001908be51bea00015a0092154e0956c76c8000000045900001d8f45269650c5805c634a022f000010a81fda000000000001dd05b0c5608e8c511e00000001d5a3b4c56690941caa15de9540ba19ef300000fc
  | 68 => 0x12d88000119a00009b58000080867e89a7051c347275d0000152e196425e82d892ae45ba7b2c54c8fa700000000000083c0e26511108a1b1e00000000d5a80002df80f9c118a7c1338c000000000002b588bd54830e9f372617f098c998e0c8e00009a880000dd4a2bd01a9ef43f4430c506308040dc20000000000020e63254000000000004990c6a100d00004564000000028d83b254e1015313540bc49b61ccc111612f0f320000486043f120d949338aa02d0bd419254e94aaf8458000042901b455019f2050c40000ccc89861c1807051451adb1f2c022852d8a2e4ada41e09d40000000013203d50bf019489ba094f234d3aae00012db9155000068d4000000052ca000000000000000000000021bb1bc0000014c80001d1aa629067a4e22d5004b490e8df90000a7394cd21e0000016e400000004e14acfd3ca25d53ab8516524b9e1b3fe07264ad4146833682e7855e283820a00000c472aca2abe6c2cdb3253754865bb01b522dc00007b6484a96c84a909241114024e2f5e10051f298181c5637c80000bbd552e47e4035a7062d4c1eecb0980000000000000013640000023d4ff800045300000000000000006f1515d0d34000011d1563842728fa3690d350d27000097784f01615000071d0215800015b400000001bdc000029e157004e2551a8bc847d19f242ee24b83ce000022f400000848edf562000000001a9c000002f918c9cde0000734c1770f9b4d2072180001618458257110c900003c6a5ef4d49a9341b0c7b0c85914e9198806f15358ae32cca000000000000000858c000000033f64fe00001a6c30fc64f04470ef7000023591e69c1745945f6d5440d2201000000cc11eef42bc9ef49ab13290a50920cf37a5551efa00000001e5c235c9a9400007ba4c8000008bb9fca00004971205174f3e907ddc4bc00000f6a000077c000000001c80000205409227ea80000000000033815211845454c6dbce89a30a29861f1400000002a240000354000049288d081be00000000522c6e60000002479ec5a08db90cc018a90a0a0cb3b2e9bd142980003138053ce83814d15064df54d413b9025600015619efc2392051cd489b4d3352aae910387d90ea2ac7c70721fb02a857d8ffb8000482e91d53e2800021241fe910e8da000008a5cb2780464960000013e1a7932d00135246000000002eb0eff8176386ca8ed28529bf00008f3c30784820b240000b9a80003f20a9905680000000012e40000000000082f845300000f526a6455125a34c3a59a49e380ad2baa179cba9824a00009044e3c0000434868153f583504e0849b0e4e0f944d2c0000000000012ea0b6145b9bb12a005e70661889d408e5fc83039f0b39e23d28181a6530000342084e121406704ce407800000b6c8045340aacc3d0c3fac17093d8066c0000cf590f
  | 69 => 0x67000012dc4d79e2a39180b80d918000213c40e400027a400000001239004331820000c9c00002fd425a000021eb00000000b690b32313e4e5515a04720000000000000002d440000886a4ef0f78492551e08185116334485c01fc4b92a0910010e1249223f9862928e23d444280501830c4c9000000002a4904dc000009fa5e9442a7a90d562b394312209c6e28000374a00000000000000078b8a1e9f3b43445ba4000000022260000000000000002c38d78219500000ff8d880e1c000000004188bec4d32122c00000002cd6000147f9a0600000000000161635ca7e6d52d04ee295ea10c5fc0d122c383d38f8880001ea68c2c1248eb142a20f7c0002716000046bc986800024008f840000000449896f400000004dee137c0000000000053cd1b39aa24f6ea9d0f1b80004e8e624c9c001330ec07dc04f997501fd285381888a391db8a72cdfb025d086e0000a2f095e185a0000000000018603db0a30003500000de832b89f100000000000100b002a000000029033ade0000ea08f144d580000bd80000382200001d09e8e46e232791af1488461a63fc7fb800053f65190000000000000000d3880000000000000009603a6a2f90b6b0d1a078e1ce8e0c0c10396237a8c059cf50a3200008e90000468600000000fce0ed6000000000001a065d84000000021e20000cd70d9d1e54000015680002c0a0001269a64537560000b2c27fe14ba537800017fe000000005d10fb248d68d4034a00000ffe82e86fe80000000506000000000000000129d8000000040acb031b201d02723495913b70da4332c78d163d4b2c5b140000815000078785fd0000000098c80000b2600000000c431c7741e80000c1ea5a800008698969066f485e7cac6aa000031cc2ced5962962237ca91c4171bf523d07f7d1900a891a2e3b0432ea1f02b3c59306ef12e640fc700858517dd4c2048fc7d6907732ca4bac9f49b463d4664fc2b9297301fc2a2cbe7a9d34eac000107a8e081eda0110ec4934b4d7e82d05080e2a04b6676047ba6fc12107e2144b1aef46f4336c32100510a4c0894a2c22f400006e24a039f2e00008d7022c8d180b86516800001a85018a66422b000000003e10ec00c403db00448ced13571b7e7b692a9a8be4008a5907a822cb000000002121bdd39ae5e98cbb284100000a840000000378e5da548e01860000228c00018d3241088d400026391f2055806a4000000004d542a187c620ca84e0000000051ac178551828f12bd623d4a5d000000000000000048f10b84790b9515cb3b7a4f540001ede55de2d94074262d3c249f74da40c2113440e904bb21ef2f1e762015f9dcf000035c419008bb0000224893e0dab0000000000000004efa840545e05302ac6816400000004ca826cd1a61cc90390212867620603edc03792e996372ace00
  | 70 => 0xcbc9ba8d5e0000000126b06d303706320738817e220000012880000000000009589c6500009d8c5f3183b0fa80e786d51b1109d699e52ba87503ede618d2dc83133814116d066800000006ea950c8000319e43182f699a84ac2541cac21b6c299a43952ff8a9c034892ecec2a2fd122613f4af511c1298a081c0282a86450457e5432867346de98685d9852b2ed61879138a35f000089004028af700000000000261e0d6a163800000001604000031a1c413dc000003848d3613066285036a08e01861e1c00018ad25a245c892c000000002e0035800000000734146c1bf254dc49f4000130a0ac87da45e02a3128804bed2009609486800002f58536000005cc00017ee256c2ea8414800000001704b961f6728e000014db1c79039e960d0a204b44700000132a800003d029587b407a2000036c40002544000087c94db800000326164000000022a8123457900004c68706d361800010686d5cdc30a372732000035b1caf0000903800010aa199e00000000000000041287e818dd25be716ce1f0c3f418e135d50b2a1348ba00000001ec400000000000086e3d8c000000000004ab439cd3a9827455ae11dc6bba780300a891cb9b8730348452f14f39c39265483e86ab163a057420094619ea733e000010bd0ff54cde408145d8d46536a9aa017206c900000000149008e231814ec1359b7b334800008caa04832ee11a8000000048ac0000cb700001d2000003e510383a3eabc88c78a86000000006fdaae9163c9cf1478290a11820000000151c00000000038a908000014d541b2963392000000000a550000007cde300001bc415ace678000000066e8e68852e3614000133da7c42ef60000807992d3080000000001d00d3c06f93141dbf0e8a4c98afd12ab3d5400006750000282835e80000ca952402f34000217444fc02a40001511246a57215542820304e81e8000060243ac98a817aa8393eaa3bbc00003b930020f941fe026200508100b362a9836743ef8aa9000000002a1c0c88000079e34d4e1a8fda102c0000fb8800000002794000086a516a3f780000000211c97d41048117126c727d2b588e51cf616885e800003f88000113d80000000001419f800011f819f430d8d883a0200008f028922c5c49d43dca0202f5a27347e6083554b888b8e51867e46120bc11fd1e8d221c110916180002434a1289f38000505a7a44594a78e0000000000011cc347c3c8c5182ae636d20000000120200005ddd2660b6f4f32000000000000dd60000dbc1449172e1998c6900004ac64758316822747243d251341d450be88c440001b29118800009b09c8e25ac3ccd0ec17d503844e78cc1aa2e3c9e7de453d85b7357a1a74d0e15a91e2c2c8d28da3f74bac884533b15451c048834e711c9b4ea87b154f0157412726c9ce43a777225c0ba8ade93
  | 71 => 0xb5007646f8026a9ca2271c5d041ad0232113c0000000114f00008090f99281200ca00012901fb20000042c0001c1637488e346ae29194db64b0525c16ca47be00008381475275487b80001b1419c8a8306499fbd20ba21d540e803f0f4aa1149b1879d1a6444e00001e9b44b2049408fa4cd11ba10314561de3435c8abc0001527174a8a683c69670269068244ae9e932d7a74554e8204d2326124cf2a97e3542400013bb07e414e8933863c0354231461186ea038e4a9c5f14ce624ad3ce834ec09f18ac33088adc97880000000a86017c1baf00002724e7300000000726145b0d9e2db2000006e9e3f00004900fb900002fae0000180829337d4432800000000000782d25d25f650ea00001a7067407ee8ad936c1b0c40e0718c4b88c063fb24db87892a1034fe2f78128298b4736677c000200c4558000048727ea00ae0b747af0cab4f420000f570d8e21ac0084000161d2aa05ccd3e81a254084067c0f12b022558a83cee1891b495c644d363918231b41f852bf07cb29fe7ffc4ef2b030d0e6afc3fc85800000299cf1f0000108400007020000416a000041286c6502c00010538000000000011b2989200000001014194a000036ed4738000000000000001a1941b000009ff0e141f440000000043d2cc400006b51a8d3c60a70000013880000095000020640000694c814a78c1fb60040000054d000035f0000295800007e109fa80002df480607971265141c7e4550480003ca8a40054f1ba24d4892011fb13bd1b0a00006f42b33550824888a00dae49fa442d1f39ae2158c15695a623261e6264300002260329e14c8a751d020e3282787b99edf30508e9d01119872edaa4dd12702fd533a225d55486100dbc2cfc9c2006024f209cc16580000000916000008d500008e1c00000002e220d9d0c3088836d03bac442000000004b4c00013cf10c800010fc800000000dcc5df00000480a1c02b8000024fe44f800006f42b5655c40001cfb538200000000b2f000051ed29b25884f1a0001487826535087c483c296d8000005611e58000039a42d00001bb44032000055594d54c1c68d0b5d832e1cd82ba08bc28c8382645c4d9d848040a48da026e22d6129662ed39217ec42fc23785539b51489081fc0fb8ac319fc79f04e18ab81672ac700278b4b30f290c8add28b00910306836192a84e569ac075381a739c877900001a3a00005ff09940000387605a0aa9ab142496745d344a21b00004fec2c89e8a24127a992cc11b429600368eee8000000017911838c7449887aa0381221601e4217400027f718a869892ee13322c043b2000000000000000037ea355000029d534a936d000050ec00016841e7a00000670000083e027c0000000000014681fc0e581c9c92bccf7a0d60bfc00000001e2d43c838253cd00001e763d98812987108f0a
  | 72 => 0x7818b601c615054691877200001b287eb4066a9262c76a5393fda0a9000076315530aa644e06cdcab5a12200000000105917f090e67a4a488e8000920cc00001826507e049c58e8000000094188208e674028695445204a7519260c81ff87c42a44000147a26b11f40000000000000000000059aaa940000aca00000341432ea5a8a570d14215ea07018688fb43684d754cc1d7d00003b50ce210162102076049487bd0000ab580001d5d04da000130900004edc000136498c600000001444234150de5158965809a11186d80eec04e048880000d480c5625800000e8b000017420000429aa3f3bbea65400000000f7e8d689d2000000000b6d14218d8435a00008b980002cf227fc81a89ef342015e8b7a000000000000db9006d040688f43f291d42d7c1a3c0000079342a2da03b380000000ac5813d075a4dd2000153f000043ce000000000002a1a89f40b69396000063800000f5604aca8cc4c4098700002831475a30304769de0000000011048304381aab4293e65e800000002e80000156aa9412c7ea9000002a3600008b4089589dc50a249e009d16b61bd21c5427b93f73b0c0000c6ca5324da4aa9400009c40000000122fa0d44dc44ad51a50ad31d5e3f8800012b814e40000d760db24aee623c0002b491228528c299a10d3236652ce49000039aa65308988b8e00006c6112da9270c7242302ac00003a9e9450c57960d2e4e792d2c52ae404482428330a6aa3f06922c3e6191d385617b84dca1262458192098f00000000a05c000280100000000a8400253fa66a49009a6c801ee7db01699f5a0000000007e829b1c2a13d00002a592d3e13412c90534176e9ee9174207708b873c0f81800029c639d80000523000000000000000119e7d593fe0d7820ae3c2470d000002d647082af9c7612fc96a431300002d840000a37a652000056b856600004ffe000000007d60000639c81f171536943ebc0001176000000000ec92542dfe00013d31cbe0ee2606d046000015880e7000018d103884bc81a60f714cfa00005c180000000434ca3999b83d5a142400000004abe48e05011eb12fb25bb5005a31a06120b1c0000000000000002d5986710cca2940000000031059d8000058a539a14f4c4595592a0629b4236000007fa17d800000000000000112519e8022c0000000122534060000dca28b9074a3ea0e17244500000000002078139b07b440000000000016608a50a28486c19b800000b03cd247751f513b330a8a1840001c5617e8689879911f71a22389cdcda6c200000000000280a39d03ac12252ade325e35650401bd609f40a611b91dbc1e0a2750c55a2771050385c2481c5e560e85d53f2a16a3c9c20ac09e069701d87c3d31e9eeb1f1a4bd400013ed00006ed400015f21142000033c01f9445e6a380000f2707ae2824b9b1
  | 73 => 0x111c6490000460800000001bbe000000013d0157e188c04388d580000000000079e00000c28aa6400000000000570c00000001a0c00ed3220369300069050f9a1ab314a1a10c9513921db02244000293b00003958ba621e34d3c36f07bd042a00002234ed9a727379a000000021f800008b4ccc89db7380050480000000000000000370000444080d00e980000a9c238082d922a396a5ac50df14390c2e00000fd8734035e805d010a07800004158b80012c00000000ad98000341400010bc9aa332b60001081a52e00003e2c2548000538e19eca9aa7cc501097cc0001482036c239000024880000000000000000000a54c000000000004e6cd24258c14f2a8c8eac94ee3d20abc0196066d4e305ca4aed124113da80b0658872100000000eea247a203600008c222a034480cb465b1bed0000722c000053f1c1e000063ca4101d862690dd6288a000094887e08695000000000000000223e3314f5a9eb30b26000106227b921ae41f08a5a7ab2d4e5a44c890000000020f4000279534aea6706e395910380168c3ef9e6a19a6000000024163af63de462628943a941df00002721000008a47309a1f33ce00013780086279a9a9936d0d8005d09c8c00000004ee21548fc28ba700002aec44291fd3394000106605a1356e288c03f86990fa22e4c93997b3269400000002a0d1f72774cef505962e8aabb4000000000006e78000271408f200000001f9c0000217cf8d0000000038a546600004b864b6400023ed09984c3cbef12d01ef027e4283148a0000000157980004fe678d11ca91611908785c00026ce4c4616680000c8c34ec756c2b3aa9253bea880f729fed000000003290c612a467580e28a407000000000000d91076031b862aa2a213a21f4c00003e923d800007c38aa3032a1f344290ee50000a754c9f18a810a80000000121850f616091661ecc4b4294a80000daf2dbe00011baa70300003594000283e4f041928be802863c8075c48ca296d2744a0e8e921877268c0000ef30d040000437489fa51719b051b40001a0800000000ce100001a3800008a284a100008e0c000000000002c9c3fb8a2b49366f4514f00000000a12ca9d80001ace14900000000015604c0c0d0000000073700000956000076f80000000000000000001f9a43ec00008050a7d06ae00009b8968c36627aad152a3fd000072688f78000000064108ef8cf13e542591158a25f2e8e1e64ed400002a125ac8f9f00001966000000010e9000000002ee00001c6c8cdd0318bdc1fe26b08b7804b83a7ea4e4627878e1f6e426cb3ba0bf259e7d2d450a9110bf200000000af436f43f10138800008da7ad00a49b5c18680634000082a1d6434f508782b500000d44b6706041c147f44bc4236355d00a14828a8951a8400011e1823d1f6a
  | 74 => 0x236487fc854000003b30a7900004d9612d4a688dba459a637800015d60082302862e000000001de80000000413830ed4719b7c00000000000162400000000a5c000027040000bb8000000006e645169d434744052000000001c7e00006198000274000006b09c0e00008280c39858518ea96d86330a813c341f24e96a8563baca225070a09055a20000024158752e80cc8adca8182e16593870e800031c40000b21268e02ce16d137d0a510f16ac281d1a3984852232400000004f948990f7701a30ed8745000016a51e847be09431478000079cc1f326873b9c3f1400001d21cc67dcc22c016f1c7a0000fbd90bd00005e30996800000008a48000000042204a48d22800015c02cf4e2290a4460a6b74ff1a5ae00003af118f000000001ab8c7b01a1000000011148000387e3fa0e908e193366ac44000000026de000114fa71037b223609c088c21d663ad90909c1925ca3c90eec82b800004fe40000d703fd8836864800bd24c241b4d3024bf05cc000000021b2317e6e98a500000000040cd57f8000000000000000000000097680000d2d000000004f5000000001794166800027908f6823180000a949594554800047a600000000000000050bc6dba66149782e343d921c10000855c00000000000024c72bab470b705ab4ea40b630000000000006bf14225dc81e20ea90000000025121640000a34502b000000000000952141f55e25ee02bc157a00006cb1507000000006c700159ae93232650cca014c90c1211cd0509a6f3bd05e390f285052768658c03114ca4c2ea4040270ffe1e742f5d0090f0c280a3f254bf921529f0a8000fb1c7307242a1478798f20000a6009630938329c207d05d8c6045884b50ab4900416569d9d36208f4474647d400000000000000000004e600007eb8000139c000062e0000067f00006f4ce04934f20ea51183cd166d210e3ea954b2a782c82108458fa6e50000a78913a142d2bb88754000072300000000000015c327a71d45dd04a32a20a8d108a99390000000120a2366559ca0849ec8000079600000002266467eaac892b8000249877e0ed5800000000000dfe1fc22b1a0cf4000026c0000394d47a800020f26d0c0000000306a00000002082144a952c578840f000092c400000001a943340267000000000000fb080e74e845a2000017d34e6a6b3d0d512e2053e0000000136a2dcc00006a70b450ad8406000020aa00000f35197997e098844a4b04063c17d00dec0000000080a2860c5b8000000011c000000001c6800000000000000000000460ec22e44a3c84be8000000065648ef0000484e0000a6200004d36000063e000000002479484800036bc56584711df300000000000000032e41f200001da2415613b0ed5086d000028c5501020d00002e3c19a9a2e195c7dac00000001f145950000
  | 75 => 0x208c72ccc714848d02d10bd431f90900a005496365531b169513080f8c32301df1b082dec67e0ab4300481d4ec71f2330de471803d89f63bae10d8cd028154276a0a4f2c21231c8c97b0640a08900004700000000000001edc0000c4d12f600006ec0000000043c8000000001aca5ac086800000000000d6faa2346a65df0c2422410000a72490da23102e40000961897454be4b383a7a1d9135c20d84a6811d3eca93208cba05e49e62fec0a0a152336c8ea052199b533ae5b7088518cb3c146a0d29615bc4ffa0001539296116f82d9872480000000a56400003903ec079d8000151b00000000000000000001c313c900003cf08b9c7e925e61f90a0f44e2930e2130688c724000049d886444d000000000890c8ed8bb13c26746c58611a01ba261f14271b6a051a37cc2a6124d24b41260963a560000000002c2000000009a2c00000002506760c105000000000001587241a46027350000029a00004c6944394470912032400013d200005a251378a691a9e4050e5d25c44b9400000fd166a360c676466000003152625c54b8000000011b8583056254bc00000d280000d0c0000000211120fa00004ec15ce11687400d9f27ce05d8638d1972b443e4490f800013e504500074535aa4e2f0872753030ea547a23044607a4c932343d1c80600000000245455d00004cbc00014aba100000047ec00021a04966ad280000f403d00a8740001e151c7c48a43769345010a1d7d1ea11e537904bdd4f700001de05a4072004f8000084e54e88248372a0148a4c9657544c259849a159249a46f5020526af1cd2895c0000a592da07a54cde24f41a961060000135329be3b9d0f30bc719128ba94d38b7f4e5863003a227cf39fa80c81c40a423dea8508549074d33e6970462810220eba6fb856016123dec2f0493119141514220000022450000337000001932cba3a80eb4a9a1214200008f69306000048d11c821ea204e19c86db000006f0546000000000000169458580001294000142100001e20000126129481e8266692720ad9560a083d0dc28a30000041c000000000008ffc0001a3d000070b0c20800050e670f05a50e93362c1ead11b199d492a3e194b387890d3679dc000142200ac49193ce02be349c00012748000037a838c00001aa47de5d500001bb21a7e53f4ce39e424306858516328b81c6698e932684fb4d1eaafc4e9073e0d1a30584e383371cfc23213c480000000265ceda1860398c0000000166342e40000411aa0a33c60000fdb922127f80000d690c5f034c30a4b59a33000006210f640ba34dc200001ae90110000ab7c000103400009f684109fa92fa475d52f2a1f729a81cbc9f885161cf258a80001ac12d3aa5547518caa22584b8cad6aad2394a40384ab8927349a00007dd1fd627181ae0e912338000000000000000078
  | 76 => 0xa0630c00025b300000000a89972100009aec000000021b40000000070f11a6714062d800015ea3d1400000002a926ca00000000483200013f311dc180001a8000221c39588bdd0209fbb399685a000000001a4800013559bf94b7000000002b2d00000000000012e11de34411f8a0ad075286a065604f32f6a99d49bf120426a40f513af95af232400011541c7c4e2e2c2000000000be65054d058c1845a2000000019d60000000024285d700005e88000000056100000faf80003bca6f541b60a7708729b040000ce231720c20100a033184a7ef8568882400000000cef0000000000000000b6d0b4e0000000113d1fb28b993da00001a0000003cd95e64cca000149289bb00007d3c00026f6073a0000a729ec00000000000000002268a038000149600004558000176a50e442940000000000026a4ffb22ef25ce36942c5986208a6816c2a100000000494ce39064c4f588970e60938548e873e4d4286ce3dd20484fb19acb1e5a0000000000000000000000000048b82000eca00003efc2f6d4729e162a72000000000002d9e0000a4b9f390b9e699c4449d42000032e42ab000010407c04ef09782010250ac0001ee708be0000976000000e4000134293300000000000014103068a5d8d7a9e200000141c00000003e0e0000e1d03c30000ab10a2527f52aec000076d8ade42e05fe8000099800000000a329244436a3a0c331a9ba48e0000000004d600001bbd55da93e0daca5a0a5f8b5023c425cc55601e73a64000031f00003c64087c0000000339c00010339fba388e2a8400006c10000a82ccbc80000a28a6a80001102019868ed0e48b810d881e3113f86a50eac000150e01fe000024140000aed131a459544b8736017e3dd0000281f283c4a3818e0000000000000001ac82c92663c14412c92a824ba1314a9ad157c0a1c0000000444600009f9a0a2505e762c0000579000066147f78210505ca0c02af0000217200003b320810000758c0001cfc00000000cc00000000000000000000000071300000000000082b00000000000000002be8aaf507657c41ac1e3a00003cd4f29827800003478f2baa6f410a0000000000000009bb80000cc100009ad534180000000294808c8fa13e203f35099a01c006e480d13e19322b306e48e94000000000000000205d2ce89644004866a00000ac099d000000008558d9e95891a026575411002220a654648da809e3e989c6914805953e0c2730d9f8326000060b000000df2fcc09d8586a60f148e41b9348a029443c0d48000000012305284c2a90df00002be136b8900185011380e6000031ac58e0aca8a1f19220038b059b0100000c1800002c43e883e74d44a12426486258601276b058012f904b23d003b45c58000107e53c29180cf284403e7e5cac0000f8510f043fc0001a4b422c401cd0
  | 77 => 0xf40beb384a149559a159f1f3c0000d2d00002aea00000000000000000003bf9c0853b824bc0001d87000015fc0000773459c000115c045a233e4e2525398f351b83e015388c572c4a19f0b738064048223281cd1e75178c00003a015063b84000106100001aa48c3906caa8c4f3024a8000000000004a3527aa66a0000326cb740e970aa617c00000253386800000000b370a882f849a080003d380ec4fe5969c0000000000000004342130079600000b9c000000023f30000339c00000003d3c03554c398042c44898497c24d426a0483c5398235161281ac3fe215c000000008c3000048bc4430000000029b0000024e8f213a6808cca54a8ad49bc59544481c9522da65991c480004f5a221d4768f7c3d32000118a8000526474a55269110000042202631390270c000000010a906fe038157384d31c8a00014fc000010aeace0d700000000073d152e85b214eca615205822c26b68b24f8712ca3a9a1f6075a21d34e240000f97920a0000676c498800047c8a804714000013460bec5ad00000000000122b9ac91e1660a450786dc09b41d5cdc884032658000107c18a255008f1d525064f38cc34c400023d60066000151297d6006c0000000000000000000000000043c20b0893f000000004c74000162700003398989861255b875e4c660000264e000120986253cbc19ac27224f200003004a8e80002fec25494ad862b451809bc3d88b8400ce397873e8b213a960000000007518b4000050b16d31a04893d52b8ba6452a0000d5c2a8f396864dc537044c127e34a019e00003e380000000298252c000290a18a9d42ec8eb538108ba0000911c00000000000000000014f900004d0c0002530035c94f830aa48e1deca6d114380000000232c000000032000aa4f6e813646d414e095982ab2064242c00011a63e2c1ca000d098a49f443f46b91c33088c86094999f4e31ae8bb80a20000392600007dea31824c648dcc1b92a23b3e0000000039600000001336800027a6000075f9ccd46589f805821bbc23883c5c6ba91fa428c2f74f4e96fe271e04501cba08a37d20cac02d05d04a242584a6e80af01d2820c78403073af0a8dc71620df042297e400006e30d262f3101e80002132000000001e1087495c8000192e00008f8007c876126689c7000007a30000000146500000d464b10ce89f353beaacf8aa7068e4c00184c94ca4cb55a661ed36a9d980f7c0000d3d840d3fce5410d58979a20024e7ca511b5b2b04000133a041400005b5d3f80a2c17a8000038822c01afe2fb4cdf00002f7e7cd06218b1603860000000000045f812583ee960f00006fe8bb100004a98000142d26cf061c3394b438fd70000737c4e5288c00001858147800054b6668400027483bb400000002558000042ad2ae985c0000610c000205841bc9590000000001
  | 78 => 0xf041be4dd3a0dd3d6e03b507116e20dd22f88079a4fe115c0000e75090c00005e492d927643fe2ac4c54aaa1f522e7b340001052284c8779104014b012c1e591ca08aa549eab8d00394cf02e8130443d9c832fd600005a1a4c352985d7158ca39a0d1220f884698b50096ace8d59082215d887689f0a3a002fe000000000000000000000000002c8c00000001833504a75fce930f26183849288de834b25d22a10cd797b2388c440c000165005a4a89d110800000007b542590000223447ac0002362357800000000000000040e92ce14eb4fde87b0ad301c50000a690425801c50a455f00000b181728000025203492b6a0000bbf95f832c45d991550e05565c000147c0d2609e0166c651209a3dc2000088f075c000047142a38d1900004ee0000033e35e86924a7a14d200009ae433c964326f411bd01f87ef00008fac000000029c2000006e00004416a2100000000248e886000024261ce80000aa40a1c404e98b85038df624ac6c64000153d000000006ac1623233c00907b58f0424868efc1619ae34eae07909ef031526c4282c632800000000000756a507051c951c00000000e7a31f532c000000008e300900000414a00000000000000090a000010ac00009d60c362b4b000000000000000000039c800023a53a9c06c863400004de20000000116e489ea7b47ea1e8c48ec8fd036415cc1b4c1230dfc28fa22504130e55a51e082030d400000000000a31000000002d249cf800000000000000000000000000a718bbc82bd000080c0f94000038600000000115107dc578ce4200001be20000000000019f20de400000000f4c00000002acb296c000126799d30be20000d5995e7266600000000000000046c00000f02066271640000000000007c48f08000075698cc00026f8444e3f74000000006467da938c8d380000aa751cb00003fdc5174e0097510000000000000000000611c5b5953600000a44d769ef237de69f03801b0d0bf453580f484e92bc86231030980e2d8c4208b4298985092556c9a213a61a2c220c49f03bb50b8298c59d1c102d4842cc53f9da107a49f0c05512fc26fe640c6cb0ca72b76000000000000d548d10692800000009b440000263000000003228fe33e2800006f625bf0b8a90141c790ae000000000000000000000007e3000000008c7c7b09f50409e88183d401562f1200000001beb2542626c0000d1f36ac000000000002622000092f235b00000001470000000000000e9788e300006754af11fcf41a0718800000004a504c50000131245ae76940011aa6144c2474f2e985b469e6a5c2d4261b2316973cf0ca92d0d0a00008969e144b560000b97971a376e67f128c90ce000020e0d6623a413d600014fb88983cc26a50f30000048660000000016e00007540a270fe10000502501e260d2eba34391
  | 79 => 0xef3a74d2be69d2400020ae4bb66130fda049e10985ced5508259043a0000000259f00002b1cee38bad00000000a8f212d01469a1890e1de0000000000000000000033c904a938a0c3a12193b016212dc68cf408800004f022f591c71424405ca3dc4771fe210e65b2c82a833903a229853ba1a1333d889592a11705145e000066b8bd937521f9d4018501383a3df8000259700005ab000003c247ea47642c424a21a42173000000000000a1190be146900000000e7f0e43486a40d957c9cf753789d74ace069622c420b021a2af6000067d42b48cba00001184f8f800035fe000000000000eb08af82d51210531000000000d131bce00003e70000000086380cd161e0000604d318a1a7129e00012a899e4188a2fdce61000044544a8c00027f237066ccd1ea82941f86523d3b094e61c160000b288b532d0241b0d8182f240dea6c869b9b380000266553b80001da675f8000027f2c726d08844809245b608bd0e694be07c09d4155621fe00000000bee000000009da862ca03700004378b8392d52186431cb0c833438de858030c880b3b14058cb8b8270273a5e590e9023e000000001288714251e4b81547096f0000000055500000a740000ed8886f04f6000035600000c7a97140000000339260592b89a5e33c40234000000050b2a37c000000011f255dc7e506c252340000961140d2ab423a0044114927ba35400000000000040750b28d8135020000b729c40016aabd0ffc0d9a3bb60000cca9bfb0000000000007ea153ea4494a2800029060000000204600007cb488b00001d8eaadc34e22ec000032594778000259888b00000066000060acd21998c0000863c4fd807421a80000529a752310e1804ed212d81432a9591a4280d00000e1861b13bf165a18c80000000000000013011a0d33c2a9e8e9b16a90000594d07b0f9200000000650000029f62075293140105de0ca409aaab50c5c370133d11a7113263c524b0f4c065424b528e1d3e0eee8af0aeca3dc000000000000eb51790a0c4000169b566c0000000000041f22bd903600002e921af000000000c3499c4bff80003c1c8f2000000002a7895ccb26953e137e14f15558d3a000077a5339a68a00008f60000000035f287d46f200000d803f443208ca12e685ec40501c044fc4a9cd56e9268305e0001101000044d447c8bfc01592f007ebc00000002604000000025f42e468d6000010fb193433cce5c0000000000010af800017e638b46be87744c0803e0e891c1e253044852718cc22a8e7e5400000000000000000007d52958778922aa8ce0c42a56855fa8cb031c9e1cb2f03e40000377c4cf09822d820000954a6374bc8a2e909f9c823e18307c0000000075c2d844f6113933584530609872500000000c1e278300009d65436143617be5134fac9d2c4256842037211883
  | 80 => 0x32100d71136a26c487087f4561195c14543088c340809561605010129dca0496a154f760b170b127674511187d13423a511940e680000302c3ed05ac4fbe0808ad90eac1a14963898816b800000001559a2853a6e000000010e60000000004b8515305a0000000000000002435592a7cd42d600009cd05f700007314a3c8eb8287484248e8100622367910d5521e215302e7093480003c9003fd54116ea114eaa407da24c1136c4425158179d0000716800028040000a33438f80c019ec7a6870895570c5e0d5858900000a72854c00000e31e6012e8953a2fb4902425cea615b024cc0ed80d820f20000a19060aab1a26568af40000000070847d89801fc309a83d50241850e0f421394ece0282000068c838d1fc63b9200009ffa5492b324b3554590cf0ec600000002234318a370c00014b53eb01a445dd8000380c00010ce8d49000000014bc852d32a07f680000d90252e296800000002cb82fbc8249ada23fc00004a48000101a9aa467084f1491a8ec539902d6124a00015a680002840000000009810b0e55ec0000000000000000000000170400000000000459027043938000206081c9371ab150f9e671501b29f4318477546440178503200005e90bbc2ce60d9516d00000000a4c000004190000000000028ae00002aa000029f6454e29b000027bc1ca058f13700db40000000000026a1364a0000000142e3f30222800020f00000a7110b6001e0d7c82a000000004360000000016da000000000000000036244a839da4410c1400002161aa93eb800001cc9ab44b808e28c8ba0380dae3d0d20e055c000056f921e801b027603150e00e7014287d008a9171046b289e400009013b64395478a818c088857f832aa6724ff0a9401da8d5a00729ab5595243b225e60214e40a8f4faa22fcd0d80b84c7e805833299b24f9090fc2422788000001500d4a7c626d261b42c6a50e563c0a78edc000000007e3466e97e90cbc56c44229921016210ec0000000000015d0185a4c04c6a0e44f2293c216a2617c0000aee00006c252f7000027a81190e5d9bcc0c385519007822d4ebca7146b029fd55d62e608cd22120000852c4660011000000000001248350ea42c62c06e52d54397c00000001cb6787085f1486451a88dd1d4896c175012c0238a8c63cd659011028be9375a30acb570af32ce44bc0a639f4149a06a5800000001298000085e165920462c0d2260ccd34240d1c000000005903798ba50a82000034240000000139000000c487240000000092fa4d103fa4d011e327d60000697c0000000000000001999c150000000142f80004b78a78c00000000f5c0000000000000000000a658000184c736c0001c9700003b4808086e712f883f14549d76000000000000d5b0000000046f82341aaea4740001c3d4dbcab512c1060c1b2e02f0
  | 81 => 0xc381b81000000001118000320a8ca452000003d02000000007a400007654bd38100000079194d8000025280000998969e0000942ca148000485451711f92a61000011343ee26df00000000000000000005e1d313a827427a940012ba70708700000977000003de0000005800000002d206829c8f2d5e47f13da80001a5c2470000292a00002fc40000ad800007150d80000000000000000000056360000000002317249eec00000d84488955c000000045f200002d7800037860000000000018ba87750870000426c7b2857d1b7e00000f3038e1b2f18100000eda9d6c06480000f528000154a3a650789cca000000004fea5e3190c7f5037c0000311200000000000000041a416d1c2d000093746cd9b7712be133c00025b4485a23c400000001eaa1fd0bf2a6b707bc60712531eba24a4416094016f71d086d4ca631bb30000505c000173d000000000000000523c700d46e9e1d05007cf0000000046801fc40001fe954fe766c87b8ac94f4e5b84879a6ea0e7e9f1cd6b836b33fa63e4133115a0950413853025024874727881e94ef425c69e14d290b540dc866c17e0e210da867b4102a0003a54a74936e990d2efa9f7086218fd49e22b54bf40fea4ff2a8e11f310440dba4f0024b85bc30626e8cd441a0132606dd8c75890f354a19700b1213a0376256096f1ce10000586832d94da14d4000136a1325000083dc000108f2928a35c51e000028661a613c889672b6e21b01d5063b56123e98b471d273b740000eaa1a6332bc0001218942747540000000038c0518962c00007d0000052d00001b8b000000003b717284fe2213c0001e2f4c82000122302d044a60000000000042646cd4daf800000000000000083900000000000201a00008ab4cf500002bd00000a69a943450097dc00014ce0000892c83d000000003e38e2100004db20fc400020651b04000020b00001c5e24f4000081c346204615222ac600001ebc0002130042c91b800000004464a3d80040000000099e0000248500006f6c8b1a6490a20062d4558000491426c800011c804fa000000012af101470a498609e81fe60658c26a403080e2f3c5c5850b0b9447ccab40c6b04d27e7888e9580139c266857e04a52c285da078e958a4170a6a4efa24ab384c6c905f525760000634058d17f9346666713ef0d9c4aac0a8021921ed3980a7a8a1f000000006e14afb83fa0c869a6005b8ddc1d8c516c700a7a2182e7e1c00018ae151c256c00008b8340e782474f1712138c17810e70000432c8afc0001edb4d26468c3cfa8344eb89de88a11c641a5423e10db000000000000b7c1cb64eda5114dac0ede2e84507464e000021e88620314a6620bba0000000000000000000c911b8d000083a924c965a1cb2a63cfef2449261668d8837a57b07368d244342616373a8718d2e8502
  | 82 => 0x8c7000000000000000033a55a00000107080102a40d0c00000002df6664c208aa451cf800013cea131016600000ea99dc122063f1069299631f6ab94fa39f08000000000001ca61a9a3e64e7d170d3d068ca860f26940af88d2d53306e00f820000be380003d0a40c400020b300004a75351003a0c5879e800000002d725068021030500002934dc3810515ae8338ac403282ac2392cffc8be30aec000138092933e0000002aa1d3c0000000000014804b12972cbf997ba1c78425062098e4055c5c98e86000006ea00011e0a1bf23ae99083280a44423e18ccfc480004f3e00000002abc04e4a9d404a000025fc0a0cd0a225d0928000000019aa3cbe1c78e7028d32d6027d49f7813421d83ecc1e99aa117a279b41711842171054305d90f18466a03ac0002a6d187a79682aa99182f866624379a60700007e98000066254340000000000042b200000000000145200000000f283a6000000001c240000000100300002ece068944f0fc00568048c39902d955b44a4400022a91bfc306c34580002dfa553c12610664ff443b517281774b5e9f9c5bca1930000a0694f8052900007f60a2112701374000000020fe000000004739aa81e5e52313a60000000023f554e08961d72334927e010a0dc41a212f02944487259ed39e9114318e000046309ac284645c12b79eff2f787b4c36c00000c6081c43fc240911586bad56117df29aeab84fe29e02126400003761ec70b3a8428234aa390bbc00009e18bca21448604af094505182285c459196b41220b18c53019420d62d5c5580d430000894000027db00009d8822ea45900008f88b038d6b2e04000000029eb4c584f14d2b252d2a4a00000000ff626f85a3c000075535b8a1a000001e50000000154980001b900000000276c0e4c0000f92153828c651f091e9b4c237803100319e843df63b151c2104b1de20000e1088121636641c01705a441c8a7a479124c600000000bb2000051e68bfc478000047f258bc000000000009a708e19eb93ae0000000004ac0d6e0ac4d3a80000ba246007508c6900000000f5da5093a3c37851f483f91f067b5cd638fd34c06a4fc350a45b1442000110482c5482472c80ce00000d5e8ab8a9692ba55404304d4a940e2cfc45a80000e5200003774fe080000a1841013e5a34600004e8455b279b564007fc000000000000000d4f86443a1e884d3cb089f3b5a455c63b253c2e385cc91de13362a6e410d221167d1e36426839c83af1c74033c822a19a4f704af08ce98500d9e54cd03e2a510eca754cd22051241d23321414122452447a48602903b10229d540a317d420bc3e0840306b249088f4836f9a824fd000d09ad2b31484825440000b6e301e92b0ea88e6000008a905ba090735bc75547069bf310a0348050280004c184d301b6aa280efa872
  | 83 => 0xdc00016c4000637d0000236e0000696ce0617cc0000000132f83a22b7ea3a4e8214280000152038700001a56a354c429e24000000000a88000353009dc32b0a9650c600011b496a12af20000d7980004c9807d536b0a081c0089881afaa153de072501e800002ad80000baf15f0403c65140001786358800010479a403cca6bf07f3952a2f82977c8210e470000660527806f7413e9494bcda0fb08ce000102980000000060c93d06da00000000000000056528ecca5b80000aeea6ac00009442760000064c0fbb24d483803da20e647f62345184079307d05de07df98b1462c657d0d79b6e2c2e00007c480000000abec664800014b003bc0000bcb3c08a94861910ef4d1a00000002b3d286459807f2800026ee800c00013e30000384000000003b460000000235739ce000000005412ac40fbc4de10d029309e3d1b6a91f2e7c50080000ec434e03bcd011a10207ec8cf0686954b54529d3c99e8f77497a2520cd69255197805ec0c0271100006db40001ae8266e86c4f9e9141000097f40001a7e000033e822a292f35f6226c51f0dd755f058d0ee08000000019d4601a562480891b000024d718748fb00000d5500a6224d2fd16a34af0931c95288ed053a5dd4000289a000002908170000000055100000000220c8f112878b46255aa8b0ddd87821e52449cd98115b4b2600012590a6632e8654949a8fcb51fa9ca477d05ba25fa4aed1e00c8e2b3a0000d78800000000000000000000001b54082216952fc1da8789805d12e4994000009e115e028540348ca82fe07e4800022fe373065a4000000000ee00000000000000000000001b044e0a51a917800003e6286300842050000001642291a3f4b9811d477600001d104af810a000000004a7c3dc1d991ea24578b161e2903569514000000000005e9100fa734238e0000000008400009dec0000fa556865eb0b8e8000000004e000011793c1a40fc1b30000278c9fb00008372000013a0000000000004e94c469817000000000001e6c144848a14f2a983000067f80001e5900007dd4f3703c532da796c63f92054cfc2a00000052713cc537112400001c3c55740000000005e0df800013e24d8a69481cc0000000000013c580000000000010e0efe08fe87f0000246725d400013a70f2b00000000c3f8000357c2d08a108000000046dc0000000265c4c1c810972516a4600c4071085327646586e7099301f684dc94d97581b50000000000e4343a0000cdf8eff000044445a70000000055cccf30000426824b0225000000000f701be800000001334cf00ed61670000149b1181000c02d80000c2017b09be4b5000004b600000e2c15584e5c000040b9c200000a26c00008c3093e8ec8732148415ca6eb923f0ef94e5a00000000f3e4e5ea2c820f2990014c7aa438e800000009da13bf000
  | 84 => 0x93885d3071a33fc0000000000093940001cb909ec46640002a542fea2654e6701b400000be8c259d9145eca150cfb2885222a37e8cfc808219e8953c5f393220f141960b8f09c200003d61302800004400000000000050a09c2045b90cb358a8a210b982450000000000000004c1099754de80002372000010b977a00003c80af00000000000015a415c12d7423a8174a5ba3046000014b0000083863a400000005362046800000002eb41488eb0800029763a54de4a5081946939d05319bd0018000010629ca00009d180000000256e4888b4b9a1850b6a86c000000000007f3538580001f9e00006838df84bf0000113c2793000000010c388a02a3e6440000000019de160c56e08ff3c56000000000004c3071ec000111945060a10e3f8289432800b4fd58d7e00003b805ab1b9c149e000000000001f46a13c00000003ffa00000001ae746f60000188000000000000000122746e6000150b800053ea29f8ff080002cc89ca800011a9244c343c000101c000000000001820000054e8efc9d0800002a4d04d840b26407200155177634b20000f5912903b6c61747fd90b618bc00012742b1200002b74000251a000026a148b149a53b08db0c4025c83e7400000001c44314e7c14eb280002f68000143b9973239e8a7478e1c852efc65d4fba147f292400000a50000133e0e800000bb6385e3c0c0001724000000014972a11000040a89bc262119b21bb8000000000000000000000017680000000004a02840000ac28dd500003c
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x862d64548200432731aa4100219358d5208010c6ca9308400863554984200432b29cc2100219554e6108010ccaa5308400863654584200431aaa2c2100219594d6108010caaa6b084008666525842004332a92c2100211d5db54c4010aaae7aa6200856572d53100423abb6a7880214d5d353c4010acae5a9e20087155494f100438b2a2a788021c555153c40108eaeda96200853574d4b10042aab9ea588021c955252c4010e8aa729620087265454b1004392aa2a588021d194d52c4010e8aa6a96200847576946100431cb2ca9080218e5955484010cb2cb29c20086596554e100438caa2a7080219a5965284010cd2caa9420087295454a10043a4a9aa5080211e5da518401087ced2a2200843c76951100421f3b2a8880210f1d95444010c3ca9b1a200861d54d8d100430f2a0c6880218755063440108bced29a200845c7694d100430fb24a6880218719253440108bceca9a200845c7654d100430fb22a688021871915344010c5ca9b12200862d54d89100432729ec4880219354f6244010c5ca8312200862d541891004327298c4880219354c62440108dced292200846c769491004317b24a4880218b1925244010c9ec7292200864c6394910042373b2a4880211b1d95244010c5ec8a92200862c645491004327b1aa4880219318d5244010c6ee9b2a200863474d95100432bb9eca88021951cf6544010ccee5b2a200866472d95100431bb2ec8880218dd9464440108ecedaa2200855573d5110042b2b96a8880214d5d65444010c6ecb2a2200863765551100429b3b2a8880214d1d95444010caecbb1a200871554d8d100432bb28c688021a51906344010e2aa831a200847676d4d100429aba6a688021595cb5344010aaaeb29a20086576594d100438aaa4a68802195d955344010e2ca8a9a20087155454d10042ab3b2a688021551d95344010e2ec8a9a20087146454d1004333b2ec488021c95536244010e8aa7b122008667651891004352320c488021c95506244010d88c6312200874553189100423b3b6a4880214d5d35244010aaae7a922008565759491004333b2ca488021c95525244010e8aa729220086676554910043932a2a488021c95515244010e8ca6a9220087455354910042b33b2a488021591d95244010e4ec8a9220087246454910043a3b1aa488021d118d5244010c6aa9b02200865553d811004332a96c0880218edd36544010c70e9b2a200865b73d95100432c39eca880219adcb6544010cd0e5b2a200863b65d91100431db28c8880218ed965444010c76caaa2200865b65d8d100432db28c68802196d965344010cb6caa9a20087195454d1004335b2ec4880219ad946244010cd6cb292200866b655491004394aa2a488021d254d52440108f4ed28a20087315494510043a8a9ca288021d854a5144010
  | 1 => 0x500422fb9ac328021171cd61940108dee4b0ca00846c72586500431aaa4c3200219554e6190010ccaa530c800847775586400431aaa2c3200219554d6190010ccaa4b0c800845e73d94400422eb9eca200211b9cb65100108dae5b28800845e73994400422eb9cca200211b9ca65100108dae5328800847571594400422f398ca20021175cc65100108dce4328800846d72194400422ebacc620021879526310010c3aa9318800845f7558c400430f2a2c6200218755163100108beed298800845d7694c400422fbb2a620021175d953100108daeb310800862e549884004316aa4c4200219394e6210010c9aa7310800846f7558840043172a2c4200218b5516210010c9ca6b10800864d535884004237bb4a4200211b5da5210010c9cc7290800864d639484004237bb2a4200211b5d95210010c9cc6a90800864d63548400431aaa4c2200219594e6110010caaa73088008666529844004332a94c2200218d9516110010c6aa8b08800865653584400432aa9ac220021999496110010ccaa4b08800863554986300432aa9cc3180219954a618c0108eeeab0c600863554586300432aa9ac31802199549618c01087ce9b28600843d74d943004237396ca180211b5cb650c01087ce9328600843d749943004237394ca180211b5ca650c0108eae2b28600843e74194300421eba0ca180211b9c8650c0108dae4328600843d75990300421fbaac8180210fdda540c01087aed2a0600843f76550300421ebb2a81802187992530c010c3ac9298600861e6454c300430eb22a6180211b5d6620c010c5ca9310600862d54988300432729cc4180219354e620c0108deeab10600862e545883004316aa2c4180219394d620c010c9aa6b10600846f769483004236bb4a4180218b992520c010c5ac9290600846f765483004236bb2a4180218b991520c010c5ac8a90600863654984300431aaa4c2180219554e610c010ccca5308600866552984300431b2a2c2180218d551610c010caca6b086008655535843004333292c21802199549610c010c6aa930c4008655539862004332a94c3100211ddd56188010c6aa8b0c4008655535862004332a92c3100210f9d3650801087ae9b28400845e73d94200422eb9eca100210f9d2650801087ae9328400845e73994200422eb9cca100211d5c5650801087ce8328400843d74194200422f398ca10021175cc650801087aeb320400843f75590200421fbb4a8100210f5da540801087eecaa0400843d76550200422ebacc610021879526308010c3aa9318400845f7558c200430f2a2c6100218755163080108beed298400845d7694c200430f324a6100218759253080108beeca98400845d7654c200430f322a610021875915308010c5cc9290400862d64948200432731ca4100219358e5208010c5cc8a9040
  | 2 => 0xa4210214bdd54210810a5aeaa10840862f655084204316b2a8421021a358d4210810e1ca6a10840870d53508420421f3a4cb990210f5d265cc81087ce832e640843d74197320423b388cb990210f9d2658c81087ae932c640843e74196320421eba0cb190211d9c4658c81087ce932a640843d74995320421f3a0ca990210f5d0654c8108ece232a640854c7254d32042a639aa4990211d5d7614c810c6aa9b0a640865553d853204332a96c2990211d5d4614c810c6aa830a6408655531853204332a90c2990210f9d3650c81087ae9b28640843e74994320421eba4ca190210f9d0650c81087ae8328640847671194320423d380ca190210f5d6640c81087eeab20640843f76950320421ebb4a8190210fdd9540c81087aecaa0640861e6494c320430eb24a619021535ca530c810c3cc8a98640861d6454c3204317324a4190218b592520c810a9ae7290640862e645483204316b22a41902153dd5320c810a9aea990640864f654c83204326b2a6419021a3591320c810e1ca8990640870d544c8320422f39cc928821175ce64944108dce5324a20846d72992510421f3a4c7288210f5d263944108dce531ca20846d7298e510421f3a4c5288210f5d262944108bce7314a20845d7398a510430f2a4c7a08218755263d0410c3ca8b1e820861d5458f410422fbb4a7a0821175da53d04108beeca9e820845d7654f41043172a4c5a08218b55262d0410c9ca7316820864d5398b41043172a2c5a08218b55162d0410c9ca6b16820864d5358b4104237bb4a5a08211b5da52d0410c9cc7296820864d6394b4104237bb2a5a08211b5d952d0410c9cc6a96820864d6354b410431caa2c1208219654e6010410cd2a5300820863a54580410432ca9ac0208219a549601041087eed2a6620843d76953310421fbb2a9988210f5d954cc410c3cc929e620861d6494f310430f322a7988218759153cc410c5ca9316620862d5498b310432729cc5988219354e62cc410c5ca8b16620862d5458b310432729ac5988219354d62cc4108deed296620846d7694b3104317324a5988218b59252cc4108deeca96620846d7654b3104317322a5988218b59152cc410cb2a6b046208639549803104334a94c0188218e551600c410cb4a6b00620866952580310421fbb4a9908210f5da54c841087eecaa6420843d76553210430f2a4c7908218755263c8410c3ca8b1e420861d5458f210422fbb4a790821175da53c8410c3cc929e420861d6494f210422fbb2a790821175d953c8410c3cc8a9e420861d6454f2104317324a5908218b59252c8410c9cc7296420864d6394b2104317322a5908218b59152c8410c9cc6a96420864d6354b2104334a92c1108218e5526008410cb2a7300420863954580210432ca9ac0108219a949600841087ee8b0ca00843c74586
  | 3 => 0x9263d4810c3ac931ea40861e6458f520430eb22c7a90218d59261d4810caac730ea40852e74d4a5204296ba6a529021539cf5294810a9ae7a94a40854e73d5252042a6b9ea929021539cc5494810a9ae62a4a40852e74d4e5204296ba6a729021c39525394810e1aa929ca40870e5454e5204386aa2a7290214b9d05394810a5ae829ca40862d6419252042a7398c929021535cc6494810a5ce831ca40852d7418e5204326b18c7290211b9d843948108daec21ca40870d4310e52042973a0c1290214b5d06094810a9ce6304a40854d73182520422f398c8a9021175cc645481087ce831aa40843d7418d52042973a6c4a90214b5d36254810a9ce7b12a40854d73d89520421f3a6c2a90210f5d361548108bce7b0aa40845d73d8552042373b6a8a9021539cf5454810a9ae7aa2a40846e7615152042a7398a8a9021535cc54548108dceda9aa40852e74d4d5204296ba6a6a9021c39525354810e1aa929aa40870e5454d5204386aa2a6a90211b9d85354810a5ce829aa40852d7414d52042b238ac8a90218b5906454810a9ce6322a40854d7319152042b238ac6a90214b9d06354810a5ae831aa40864d6318d52042b3b8a86a9021591c543548108dcec21aa40846d7610d5204386a1886a90214b9d06054810a5ae8302a40854e7318152042a6b98c0a90214b9d01054810a5ae8082a40854e7304152042a6b9820a90210f5da541481087eecaa0a40861e5498c520430eaa4c629021879516314810c3aa8b18a40845d7694c520430f324a6290218759253148108beeca98a40861e6454c520430eb22a6290218b9526214810c5aa9310a40864e539885204326a9cc4290211bdd95214810c5cc8a90a40862d64548520432731aa4290219358d5214810c3cc9318a40861d6498c520430f322c629021875916314810c5cc9310a40862d64988520432731cc4290219358e6214810c6cc9308a40863564984520432b31cc2290219558e6114810c72c9300a40865963980520422f39ccba1021175ce65d08108bce632e840845d73197420423b388cba1021179ce65908108bae732c840845e73196420422eb98cb210211d9c465908108bce732a840845d73995420422f398caa1021175cc65508108ece232a840852c7255142042963a2a4a10211d5d76150810c6aa9b0a840865553d854204332a96c2a10211d5d46150810c6aa830a8408655531854204332a90c2a1021179cf65108108bae7b28840845e73994420422eb9cca21021179cc65108108bae6328840847671194420423d380ca210214b5ca54108108baeb318840861e5498c420430eaa4c62102117dd56310810c3ca8b18840861d5458c420422fbb4a621021175da53108108beeca98840845d7654c4204296ba4a4210219398e5210810c9ac7290840864e635484204326b1a
  | 4 => 0x5ac4312a80851e73181540428eb98c0aa0214b9c86055010a5ae4302a80843f76550540430eaa4c62a021875516315010c5aa9310a80862d54588540430f324c62a021879916315010c5cc9310a80864e639885404326b1cc42a0218b9916215010c9cc6b10a80864d63588540432b31cc22a0219558e6115010cccc5308a80866562984540432cb1cc02a0219a58a6015010c5ca9316a60862d5498b53043172a2c5a98218b55162d4c10c5cc9316a60862d6498b5304317322c5a98218b59162d4c10c6ac930ea60866562987530428f3a6a729821475d35394c10a9ce5a9ca60854d72d4e53042a7396a929821535cb5494c10a9ce42a4a60854d72152530430eb20c929821539c86494c10a9ae4324a60851e7418a530428eba0c529821935886294c10a3ce8304a60851d7418253042a7390c129821535c86094c108dce4322a60846d72191530428f3a6c6a9821475d36354c10a9ce5b1aa60854d72d8d530421f3a0c4a98210f5d06254c1087ce9b0aa60843d74d855304237396c2a98211b5cb6154c108bcedaa2a60854e72d5153042a6b96a8a9821179d85454c10a9ce42a2a60854d7215153042aa38ac8a9821875906454c10a9ce4322a60854d7219153042aa38ac4a9821479d06254c10a3ae8312a60864d62189530428f3a0c0a9821475d06054c10a9ce4302a60854d72181530428f3a020a9821475d01054c1087aed2a0a60843f76550530430f2a4c629821875526314c108beeca98a60861e6454c530430eb22a6298218b9526214c10c5aa9310a60864d5398853043172a2c4298218b5516214c10c9aa6b10a60861e6498c530430eb24c6298218b9926214c10c5ac9310a60864e639885304317322c4298218b5916214c10c9cc6b10a60863664984530431ab24c2298219998a6114c10ccac5308a608639649805304334b14c0298211b9ca65d0c108dae532e860846e721974304236b90cba18211d9c465d0c108dce532c860846d729964304237390cb218211b5c86590c108ece232c860846e729954304236b94caa18211b9c86550c108dae432a860847671195430428e39aa8a1821471d15350c108eaebb0a860863554d85430432aa9ec2a18211d5d46150c10c6aa830a8608655531854304237396ca218211b5cb6510c108dce5328860846d729944304237390ca218211b5c86510c108ece2328860847a70194430428eb9ca821821475d25310c10a3eeaa18860851d7550c430430fb2a8621821875954310c108daeb310860862e549884304316aa4c4218219394e6210c10c9aa7310860846f7558843043172a2c4218218b5516210c10c9ca6b10860864d535884304346a1ac4218218795263d4810c3aa931ea40861e5458f520430eaa2c7a90218799253d4810c3ac929ea40861e6454f520430eb22a7a9021879
  | 5 => 0x863454584404432ba9ac2202219514d6110110ccea4b08808866452584404425abb482202218d9964110110d2ac720880886a562904404432a29cc398221551d531cc110caccb18c608843e74d95304421eba6ca982211b9cb654c1108dae5b2a608843f74595304421e3a2ca982211bdc9654c1108d8e4b2a608863454d853044332296c2982218d150614c110caea630a60886645218530442aa3aa6298221741c1314c11087eedaa0608843d76d50304421fbb0a8182210f5d8540c110c3cc9a98608861d64d4c304430f320a61822187590530c110c5ea9310608862c549883044327a9cc4182219314e620c110c5ea8b10608862c545883044327a9ac4182219314d620c1108deeda90608846d76d483044317326a4182218b593520c1108deec290608846d761483044317320a4182218b590520c110c6ea9308608863454984304432ba9cc2182219514e610c110ccea5308608866452984304431baa2c2182218d151610c110caea6b086088654535843044333a92c21822199149610c1109aaed1886088656658c4304434ab246218221b158a310c110cc8a530e408856475487204433332c43102210f9d3654811087ae9b2a408845e73d95204422eb9eca902210fdd16548110878e8b2a408845f73595204422e39aca902218d1536148110ca8a7b0a408863454185204432a298c29022199d486148110ac8ea90a40885e070485204421fbb6a8102210f5db540811087eec2a0408843d76150204430faa4c610221871526308110c3ea8b18408861c5458c204422fbb6a610221175db5308110c3cc9a98408861d64d4c204422fbb0a610221175d85308110c3cc8298408861d6414c2044317326a4102218b5935208110c9cc7a90408864d63d482044317320a4102218b5905208110c9cc6290408864d63148204431baa4c2102218d1526108110caea73084088654539842044333a94c2102219914a6108110c6ea8b08408863454584204432ba9ac2102219514d6108110ccea4b084088664525842044272bb44210221999962108110d4ac910840886c563884204438a2a0a708221c91505284110e88a6294208864e6398b5404326b1cc5aa0219398d62d5010c9ac6b16a808655639875404332b14c3aa021479cf5495010a3ae7aa4a80852e72d525404296b96a92a0218758c6395010a5ce431ca80852d7218e540428f398c52a021475cc6295010c5ac4314a80851e73182540428eb98c12a0214b9c86095010a5ae4304a80851e73d91540428eb9ec8aa0214b9cb6455010a5ae5b22a80846e7218d5404236b90c6aa021179cc62550108bae6312a80845e73d85540422eb9ec2aa0211b9cb61550108dae5b0aa8085347158d540430eb18c6aa0214b9c86355010a5ae431aa80853471589540428f398c4aa021475cc6255010c
  | 6 => 0x144359b20c0a0a218d1526110510a68eaa0882887145350441443922928220a210f9d664cc510878eab26628843f76d53314421ebb6a998a210fdd854cc51087aec2a6628861e64d4f314430eb26a798a218799053cc510c3ac829e628846e7598b3144317aa4c598a218b15262cc510c9ea7316628864c5398b31442363aac598a218bd5162cc510c58a8b16628864f5358b314432629ac598a211bddb52cc5108daeda96628862e64d4b3144316b26a598a211bdd852cc5108daec296628862e6414b3144316b20a598a219614e60cc5108ecebb2462884e572d92314431b328a918a2195997538c510e2ea829c62887145414e31442aa3aa8718a21d114f528c510cccca29462887245414a31443a2298a518a21551d5328c510cb6a6302628847475591314432a32ec698a211d9d8534c510e28a829a62887245414931443a2298a498a212d5d0604c5109cae430262886d363181314432a29cc218a21551d5310c510e28a89886288744524c4314421f3acc990a210f1d564c851087eedaa6428843d76d53214421fbb0a990a210f5d854c85108bceb31e428861f5498f214430e2a4c790a21171d563c8510c3ea8b1e428861c5458f214422fbb6a790a21175db53c8510c3cc9a9e428861d64d4f214422fbb0a790a21175d853c8510c3cc829e428861d6414f2144317326a590a218b59352c8510c9cc7a96428864d63d4b2144317320a590a218b59052c8510c9cc6296428864d6314b2144334294c190a211d9d764885109aae7b24428863665152214423b3aec710a212d5d36388510cacca29c42887145414e214433332ea510a21c9d505288510e48a829442887475314a21443a2298a510a21591d54288510ac8ea994428866b52181214423a3aac890a211d1d56348510e28a829a428866465d89214423b3b0a490a21c91505248510e88a629242884b574181214426ab98c090a21b8d886048510cc8a530842885647548421443922a24210a21d114d2108510c68a930e808853475507404431b32c8320221179cf65501108bae7b2a808846e72d954044236b96caa022117dcd65501108b8e6b2a808846f725954044236392caa02219514f6150110cc8a5b0a808863754185404432a298c2a0221991486150110a68eaa0a80885b070505404430faa4c620221871526310110c3ea8b18808861c5458c404422fbb6a620221175db53101108beec298808845d7614c4044317aa4c4202218b1526210110c9ea7310808864c539884044317aa2c4202218b1516210110c9ea6b10808864c535884044237bb6a4202211b5db5210110c9cc7a90808864d63d484044237bb0a4202211b5d85210110c9cc6290808864d63148404431baa4c2202218d1526110110caea73088088654539844044333a94c2202219914a6110110c6ea8b08808
  | 7 => 0x3a12218d15161d0910ca8a6b0e848845e73d96424422eb9ecb2122117dcd65909108b8e6b2c848863754986424432a29cc3212219914a61909108e8eab0c8488654535864244332292c321221179cf65509108bae7b2a848845f73595424422e39acaa12211ddc56550910a5ce5aa2848852e74d49424422f39eca21221175cf65109108bee6b28848845c73594424422f398ca21221175cc6510910a5ae42a0848845e7598c424430faa4c6212218715263109108b8eab18848861f5458c424430e2a2c62122117ddb53109108baeda98848845f7614c424422ebb0a6212219398f5210910c9ac7a90848852d741484244327318a4212219358c5210910a5ceaa10848852c75508424431732a84212218b1954210910d1ac6a10848870f53508424438629a84212218d1526110910cc8a530884886a542984424423a3aac2212218e1526010910cd0a53008488478755804244354a12c0212210f9d365cc91087ae9b2e648843f74597324421e3a2cb992218d15261cc910ca8a730e648866752987324423a3aac3992218d15161cc910ca8a6b0e648843e74d96324421eba6cb192210fdd1658c910878e8b2c648863454986324432ba9cc3192219914a618c9108e8eab0c6488634545863244332292c3192210f9d3654c91087ae9b2a648843f74595324421e3a2ca992211ddc5654c910a9ce5a9a648854e73d49324421f3a6ca192210f5d3650c91087ee8b28648843c74594324421f3a0ca192210f5d0650c91087ceb320648843c75590324421fbb6a8192210f5db540c91087eec2a0648843d76150324430f326a61922187593530c910c3cc8298648861d6414c32442a6b90a6192218b993520c910c5ac9a90648862e641483244316b20a419221535cc520c910a9cea990648854c754c8324432732a641922193195320c910d1ac8990648870f544c832443862a264192219514e610c910cc8a530864886c532984324423a3aac2192219614e600c910cd0a53006488478755803244364992c019221179d663d0510c3ea931e828861c5498f414422e3aac7a0a2187d5163d0510c38a8b1e828845f76d4f414422ebb6a7a0a2117dd853d05108baec29e828846e7598b4144317aa4c5a0a218b15262d0510c9ea7316828864c5398b41442363aac5a0a218bd5162d0510c58a8b16828864f5358b414432629ac5a0a211bddb52d05108daeda96828864e63d4b4144326b1ea5a0a211bdd852d05108daec296828864e6314b4144326b18a5a0a218e15260d0510c6ccbaa4828871454d4e414432b328a720a21c51505390510a68eaa1c828872454d4a4144333328a520a21c91505290510e88a629482885347550a414431daa0c0a0a218d19764505108ecec2a282887145414d41443922a0a4a0a21d114c52505109aae630282884e5721814
  | 8 => 0x54310d10c38caa18868846e759884344317aa4c421a218b1526210d10c9ea7310868864c5398843442363aac421a218bd516210d10c58a8b10868864f53588434432629ac421a21a350d6210d10c68a9308868865453984434434aa1cc221a211d1d56110d10c70a9300868865853980434423c3aac021a21a650d6010d108bce7326a48845d73993524421f3a4c7a92210f5d263d4910a9ce72a6a48854d7395352442a7b9aa9a9221531cd54d4910e4ae22a6a48870f54d4f52443862a6a7a92214b9d253d4910a5ae929ea48852f7454f52442963a2a7a9221c3d5053d4910e18a829ea4887457114f5244317b24c9a9221539ce64d4910a9ae7326a4885657119352442973a4c7a92214b5d263d4910c9ec731ea4885657118f52442373b087a92211b5d843d4910e1a8621ea48852f7458752442963a2c3a922153dcd61d4910a98e6b0ea48861f5498e524430e2a4c72922187d516394910c38a8b1ca48861e64d4e524430eb26a729221879905394910c3ac829ca48862e64d4a5244316b26a5292219398f5294910c9ac7a94a48861e6498e524430eb24c729221879916394910c3ac8b1ca48843e76d51524421f3b0a8a922187d536354910c38a9b1aa48861f5418d524430e2a0c6a9221179db5354910c3ec9a9aa48861c64d4d524422f3b0a6a922187d905354910c38c829aa48861f64d8d524430e326c6a922187d906354910c38c831aa48862f64d895244316326c4a922193d8f6254910c98c7b12a48863464d85524432a31ec2a92211bdd95214910a5ee8a90a48852c7454852442a7b9aa429221531cd5214910a5ce9310a48852d7498852442a739cc429221535ce621491087ce8300a48843d74180524422f398c029221175cc6014910c5ccbaa0a48846d7695052442a739ca829221535ce54149108deecaa0a48854f7355052442a639aa8292218b9945414910e4ae22a0a48864e65d4c5244387aa6a629221c315353149108daed298a48852e7494c5244296ba4a6292211bdd95314910a5ee8a98a48852c7454c5244327328a629221c3d505314910e18a8298a4887457114c5244393aa2c229221c91516114910e8ea6b08a4887445358452442b2b8ec8292218b5906414910a9ce6320a48854d7319052442b2b88c8292215a5c06414910acae3b18a48852e7418c5244296ba0c6292219358c6314910acae2318a4885697018c52442b338e8629221595c74314910acce3218a4885657190c52442373b086292211b5d84314910e1a86218a48852e74d845244296ba6c229221539cf6114910a9ae7b08a48866561d805244332b0ac0292214bdd11014910a58e8880a48854f7344052442a639a2029221179cf65d09108bae7b2e848845f73597424422e39acba12218d15261d0910ca8a730e848866752987424423a3aac
  | 9 => 0xec9b1aa88861f6418d5444317b26c4aa22193d8f6255110c98c7b12a88862f641895444327b18c4aa2219318c6255110ca8c7b0aa88866462d85544421fbb2a82a22147dcd5415110a38e6aa0a88852f725505444296392a82a221479ce6415110a3ae7320a88852e729905444296b94c82a221179cc60151108bae6300a88846e721805444236b90c02a2214d5c76315110c3ac6318a88852e7218c5444296b90c62a2214d5c46315110a72e0318a88853571d88544428f398c42a221475cc6215110c5ac4310a88853571188544429cb80c42a221479cf6115110a3ae7b08a88852e72d845444296b96c22a2218d5876015110c6ac2b00a88846e729935344236b94c9a9a210f9d262d4d1087ae9316a68854e7295353442a6b94a9a9a2153dc954d4d10a98e4aa6a68871571153534430fb24c9a9a21539ca64d4d10a9ae5326a68855571193534428f3a4c5a9a21475d262d4d10c9ec5316a6885557118b534428fba2c3a9a21471d161d4d10a9ee4b0ea68854c72587534430f326a729a21875935394d10c5ea9314a68862c5498a5344327a9cc529a218bd516294d10c58a8b14a68864f5358a5344317324c529a218b5926294d10c5cc8b14a68862d6458a534421f3b6a8a9a210f9d85454d10c5ea9b12a68862c54d895344317aa0c4a9a218b1506254d10c3ec9b1aa68861c64d8d5344317b26c4a9a218b1936254d10c9ec7b12a68862f641895344316320c4a9a2193d8c6254d10c68c9b0aa68866462d85534422fbb2a629a2147dd15314d10a38e8a98a68854f7254c53442a6392a629a21479d26314d10a3ae9318a68854e7298c53442a6b94c629a210f9d06014d1087ae8300a68846e721805344236b90c029a21879975414d108baed2a0a68854e7295053442a6b94a829a2117dd95414d10a9ee4aa0a68854c72550534430f328a829a21c55c45414d10e2ea8b08a6887145458453442aab8ec829a21875906414d10a9ce4320a68854d7219053442aab88c829a21565c06414d10aaae3b10a68851e74188534428eba0c429a21935886214d10aaae2310a68855970188534428f3a6c229a21475d36114d10a9ce5b08a68854d72d84534432ab0ec029a21955856014d10a3ee8880a68851c744405344237396cba1a211b5cb65d0d108dee4b2e868846c72597434431a2a4c3a1a2195d4e61d0d108e8eab0e8688634545874344237396cb21a211b5cb6590d108dee4b2c868846c72596434431baa4c321a219514e6190d108e8eab0c8688654535864344237396caa1a211b5cb6550d108dee4b2a868846c72595434423bb8acaa1a21479cf5450d10a3ce9a9a868846e72d944344236b96ca21a211bdc96510d108d8e4b28868846e721944344236b90ca21a21475cc5410d10a3ae8298868851e7550c434428e3aa8621a218799
  | 10 => 0x635645845384333312c229c21995896114e108dce432e870846d721974384237390cb21c211b5c86590e108dee4b2a870846c725954384237390caa1c211b5c86550e10a38e6aa2870851c7454d4384237396ca21c211b5cb6510e108dce4328870846d72194438430fb2a8621c21875954310e10d1a86b10870869943580438422f398c8a9421175cc6454a1087ce831aa50843d7418d5284237bb2a4294218b5915214a10c9ac6a90a50861e6498c528430eb24c629421879916314a10c3ac8b18a50862d649885284326b1cc4294218d9916114a10c6ac8b08a50865663584528432ab1ac229421179cc65d0a108bae632e850845e73196428422eb98cb2142117dcd6550a108b8e6b2a850845e73195428422eb98caa14214b1c95450a10a58e8a92850845e73d94428422eb9eca21421179cc6510a108bae6328850862f655084284316b2a8421421a358d4210a10d5284b00850843e74197328421eba0cb994210f9d0658ca1087ae832c650843f74595328421e3a2ca994210f9d0654ca1087ae832a650854c7254d32842a639aa4994210f9d3650ca1087ae9b28650843e74194328421eba0ca1942193d95320ca10c9aca990650868d644c83284364992c0194218795163d0610c3aa8b1e830862e5458b4184316aa2c5a0c21475cc5490610a5ae42a4830843e76951418421ebb6a820c21475cc5410610a5ae42a0830861d6494f318430eb22a798c219394d62cc610c9aa6b16630851d7414e31842a6b90a718c21179da534c6108baeda98630851d7414c31842a6b90a618c218b59252c8610c9ac7296430862d6454b2184326b1aa590c214b5d05288610a9ae6294430846e769492184236bb6a410c214b5d05208610a9ae6290430851d731534084296b90a9a04210f9d85450210a3ae62a2810852d72151408421fbb2a820421879516310210c3aa8b18810862e545884084316aa2c4204218d9516110210c6aa8b08810851d7414f30842a6b90a798421179d8534c210a3ae829a610854d7214d308430eb24a61842117dd9530c210c3ac8a98610864e535883084326a9ac4184219594d610c210caaa6b08610852d7414b20842a6b98a5904211b9d85248210a5ae8292410854d731492084316b24a4104219358e52082108deeca90410862d645482084326b1aa410421999496108210ccaa4b0841085377459710842abb9acb8842159dc965c42108dce531ea88846d7298f544422f39cc5aa221175ce62d5110c3ec731ea88852e7298f5444296b94c7aa2214d5c463d5110a3ce7316a88851d7398b5444317b14c5aa2214d5c462d5110a3ee6b0ea88851c735875444297b92c3aa2214b1c961d5110c3ea931ca88861f5458e5444317aa4c52a2218bd516295110c9cc7314a88864d6398a544432731ac52a2219358d6295110c3
  | 11 => 0xc422eb9ccaa16214b9cb5450b10a5ce9a92858845e73d9442c422eb9eca21621179cc6510b108bae6328858862e6550842c431632a8421621a358d4210b10d4a85308858843e74d9732c421eba6cb996219514d61ccb1087ce9b2c658843d74d9632c4332292c3196210f9d3654cb1087ae9b2a658843e7499532c421eba4ca99621539cb534cb10a9ce7a92658843e74d9432c421eba6ca196210f9d0650cb1087ae8328658864e654c832c432632a6419621a3591320cb10d8a65308658861f5458f41c430e2a2c7a0e218bd5162d0710c58a8b16838851d7395241c4296b94a920e21655ce5490710b4ae52a4838843e7615141c426ab9ecaa0e21395cb6550710b62e1aa283884767615141c425b3b0a8a0e21355cc60507109cae4302838851d7395041c4296b94a820e210fdd95410710d6282b00838861d64d4f31c430eb20a798e2193d4d62cc710c98a6b16638851d7494e31c42a6b94a718e21395cb648c710b2ae929c63885c57294e31c422f3b0a698e212d5d3654c7109cae5b2a63885d170d4d31c423b3b0a698e21359d8534c71096ae830263884e57218131c428eba4a618e21535ca530c7108beeca9863886d13158031c4316b26a590e219358f52c8710c5ac8296438864d6314b21c4296ba4a510e21535ce52887109aae7b2443884b574d8e21c42d2ba4a510e21715ce52887108dcec29243884b574d9521c426ab9eca90e21785c352487108ecec29243884e67614921c425aba0c090e21355cc6048710a5ae9290438854d7394821c4237bb2a410e21b84856008710a3ae72a6818852d7295340c421f3b4a8a0621475ce5450310a5ae52a2818843d76d5040c430faa2c620621871516310310c5ea8b10818862c5458840c431baa2c2206212d5da4110310d2ac720881886a56290440c428eba4a798621535ca53cc3108bced29a618851d7494d30c42a6b94a698621175db530c310c3ac9a98618861d6414c30c4327a9ac4186219314d620c310caea6b0861884d5768c430c434ab246218621b158a310c310a5ae9296418854d7394b20c42373b4a4906214b5d25248310a9ae7292418846d76d4820c4316b26a4106219358f5208310c5ac8290418864d6314820c4333a92c210621395da2108310d4ac910841886c56388420c4237390c6aa4211b5c863552108bce6312a90845d73189548421fbb2a82a421875516315210c5aa8b10a90861e6458c548432731cc42a4219358e6215210c5cc8b10a90864e635885484326b1ac42a4219598d6115210caac6b08a908666625845484332b12c22a4211b9c86454e108dae4322a70843e74189538421eba0c4a9c2117dd95314e10c3ac8a98a70864d53588538430eb24c629c218b9926214e10c5ac9310a70862e645885384316b22c429c219398d6214e10c6cc8b08a708
  | 12 => 0x180419354e620c020c5ca8b10601062d54588300832729ac4180419354d620c0208eaeb308601063654984300831aaa4c2180419594e610c020caaa7308601047775584300831b2a2c2180418d551610c020caca6b08601065553584300823abb4a2180418d992510c020c6ac92886010666629443008332b14a2180411ddd9510c020c6cc8a886010635645443008333312a21804199589510c020a9ae7aa6401056571d532008296ba6a790041595c753c8020e1aa929e401070e5454f2008386aa2a7900418b55261c8020c9aa730e40107255494720083a2a9ca3900411bdd951c8020cccc2a8e4010726545472008392aa2a390041d194d51c8020e8aa6a8e4010667765472008236bb4a5100411e5da5288020e62a8a8c40107515354620082373b6a890041535cf5448020acae3aa2401052d759512008317b2ca8900418bd9554480208dceda9a401052d74d4d20082b2b8ea690041535d65348020c9ecb29a401070d5494d2008327b2aa690041c39515348020e1aa8a9a401062d541852008326a98c29004199d965148020e4aa928a401074553945200833230aa29004199d955148020e4ca8a8a40107255454520083a329aa290041d154d5148020cc8eca8a401062d54d812008326a9ec0900418ed965448020c76caaa2401065b6594d200832db2aa690041ca5525248020e92a72924010673659452008339b2aa290041cc5515148020ea2a6a8a4010762525452008237394c7aa6211b5ca63d53108bce7316a98845d7398b54c430faa2c72a6218bd516295310c9cc7314a98864d6398a54c432731ac52a6219358d6295310cacc730ca9886556398654c4333314c32a6219958a619531087eecaa0a98851d7399054c4296b94c82a6211b9ca64d4f108dae5326a78843e7498b53c421eba4c5a9e21875935394f10c9ea6b14a78862e6498a53c4316b24c529e218b9916294f10c5ac8b14a7886366498653c431ab24c329e219998a6194f10ccac530ca78845f7654c53c428eba4c629e21535ca6314f108dce5b2e878846d72d9743c431a2a2c3a1e211b9cb6590f108dae5b2c87886545358643c4237396caa1e211b5cb6550f108dce532a878846d7299543c428f39ea8a1e21479d35350f108dce5b28878846d72d9443c4237390ca21e211b5c86510f10c3ccaa18878861c6550c43c4346a1ac421e21a550e6110f108bce7326a58845d7399352c421f3a4c7a96210f5d263d4b10c5ac9a94a58864d63d4a52c430f324c729621875926394b10c3cc8b1ca58861d6458e52c431b324c3296218d5926194b10cacc730ca5886556398652c4237bb2a4296214b5d26214b10a9ae7310a58845e73d9742c422eb9ecba16218d15161d0b108bce7b2c858845d73d9642c4332292c321621179cf6550b108bae7b2a858845e7399542
  | 13 => 0x624c420c5aa8312621064d531893108333b12a29884199189514c42087ce9328621043d74994310821ebacc9908410fdd564c842087aed2a6421043f76553210822ebacc7908418795263c8420c3aa931e421045f7558f210830f2a2c7908418755163c84208baed29e421061e6494f210830eb24a79084117dd953c8420c3cc8a9e421061d6454f2108316b24a5908419358e52c8420c6cc928e421063564947210832b31ca3908419558e51c8420c6cc8a8e421063564547210832b31aa3908419558d51c8420ce2a2b064210666715962108236bb6a910841535cf5488420acae3aa4421062d659522108316b2aa9108411b5db5388420a5ae9a9c421056571d4e2108326b2ca710841c35525388420c9acaa9c421070e5454e2108386aa2a710841995965188420e4aa928c42107455394621083932a2a310841c95515188420e8ca6a8c4210745535462108316aa2c1108419354d6088420ccaa2b04421063954980210832ca9cc0108418e5516008420cb2a6b0042106725158021082a6b9ea810841595c75408420a5aeb2a0421052d74d4c21082b2b8ea610841535d65308420e1aa9298421070e5454c2108386aa2a6108418b5526108420c9aa73084210565759842108392aa4c210841d154e6108420e4aa928842107455394421083932a2a210841c95515108420e8ca6a8842107455354421082b3bb2a21084199dd95108420e52a93004210749539802108316aa2c0108419354d6008420e52a8b00421074953580210837130ac0108411b5d82194020c5aa9314801064d5398a4008237baac5200418b5516290020c9aa6b148010666625464008332b12a320041179cf65100208bae7b28801045e73994400822eb9cca20041179cc65100208bae6328801045d7598c400830f2a4c6200418755263100208beeab18801061e5458c400830eaa2c62004117dda53100208baed298801045f7654c400822ebb2a6200418b5526210020c9ca7310801064d5398840083172a2c4200418b5516210020c9ca6b10801064d53588400823abacc2200418d9526110020c6aa9308801065653984400832aa9cc2200411ddd56110020c6ca8b08801063554584400832b29ac2200419554d61100208eaed288801065663944400832ab1ca2200419998a5110020ccac5288801047776544400832b31aa2200419558d5110020cccc4a888010665625444008316aa4c5180419354e628c0208deeab14601062d5458a3008326a9ac51804199989518c020ccac4a8c601043e74d94300821eba6ca180410f9d2650c02087ae9328601043e74194300821eba0ca180410f5d6640c02087eeab20601043f76950300821ebb4a8180410fdd9540c02087aecaa0601061e6494c300830eb24a61804187991530c020c3ac8a98601062e549883008316aa4c4
  | 14 => 0xe531ca2107154310e51082b33908728841595c84394420aace6214a2105557310a5108392a1085288414d9d03294420a6ae8194a210745320ca510829b3a0c1288414d5d06094420aace6304a21055573182510823b3b6a8a8841559cf5454420aaae7aa2a2104767615151082ab398a8a8841555cc54544208eceda9aa21053674d4d510829aba6a6a8841c59525354420e2aa929aa2107165454d510838aaa2a6a88411d9d85354420a6ce829aa2105357414d51083932a0c4a8841c95506254420e8ca6312a2107455318951082ab39cc8a8841555ce6454420acce5322a21056472591510829b3a4c6a88414d5d26354420acce531aa2105647258d51082b3b9286a8841591c94354420e2a8621aa2105667210d51082b2b9086a88414d9d26254420a6ae9312a2105567398951082aab9cc4a8841559cc4254420aaae6212a2107254210951082b938084a88415c5c04254420a6ce8192a210535740c951083a299064a88415c9c03254420ae2e0192a21053674181510829aba0c0a8841559cc6054420aaae6302a21053674081510829aba040a8841559cc2054420aaae6102a21043d76950510821fbb2a828841879526314420c3aa9318a21061e5458c510830eaa2c628841175da5314420c3cc9298a21061d6494c510822fbb2a628841879915314420c3ac8a98a21063654984510831aaa4c2288419594e6114420caaa7308a21047776544510831b322a2288418d5915114420cacc6a88a21065563544510822f39ecba0841175cf65d04208bce732e821045d73997410822ebacc7a08418795263d0420c3aa931e821045f7558f410830f2a2c7a08418755163d04208beed29e821045d7694f410822fbb2a7a0841175d953d0420c5aa9316821064e5398b4108326a9cc5a08418b95162d0420c5aa8b16821064e5358b4108326a9ac5a08419598e51d0420caac728e8210666629474108332b14a3a08419598d51d0420caac6a8e8210666625474108332b12a3a0841179ce65904208bae732c821045e73195410822eb98caa08411b5d76250420c5aa9b12821064d53d894108316aa0c4a08419354c6250420ccec4a8a821066462545410822f39cca20841175ce651042087ce9b2e621043d74d97310821f3a4cb988410f5d265cc42087aeb326621043f75593310821fbb4a9988410f5da54cc42087eecaa6621043d76553310830f324a7988418759253cc420c3cc8a9e621061d6454f31083172a4c5988418b55262cc420c9aa7316621062e5458b3108316aa2c5988419394d62cc420c9aa6b16621063664947310831ab24a3988419998a51cc420ccac528e621063664547310831ab22a3988419998951cc420ccac4a8e621043e74996310821eba4cb188410f9d0654c42087ae832a621046d75d893108316aa6c4988419354f
  | 15 => 0x5e76d5153082ab38ea8a9841555c75454c208bcec2a2a6105567115153082aab88a8a9841531c96454c20c3ac8322a61054e72191530828f3a0c4a9841475d06254c20a3ce9b0aa61051d74d8553082a7396c2a9841531c96154c20a3ce8302a61051d7418153082ab388c0a9841555c46054c20a3ce8102a61051d74081530821ebb4a8298410fdd95414c20c3ca9318a61061d5498c530822fbb2a629841879915314c20c3ac8a98a61063654984530831aaa4c2298419554e6114c20c6ca8b08a61063554584530832aa9ac229841879926314c20c3ac9318a61062e649885308316b24c4298418d9926114c20c6ac9308a610656639845308333314c2298418d9916114c20c6ac8b08a610656635845308333312c2298419c5866014c208ece332e8610475719974308237390cba18411d9c465d0c208eae232e861047671996430823ab8ccb218411b9c86590c208ece232c861047571196430823b38ccaa18411d5c66550c208dce432a861047671195430823ab88caa1841471cd5450c20a38e8a9a861046d75d894308316aa6c4a18419354f6250c208daea312861062d541894308326a98c4a18411d9c66510c208eae3328861046d725944308237390ca218411d9c46510c208eae2328861051d73950430828eba4a62184147dd54310c20a3aeaa18861061f6550c430830eb2a86218411b5d66210c20c5ca9310861062d54988430832729cc4218419354e6210c20c5ca8b10861062d54588430832729ac4218419354d6210c20d1a86b10861063954582420822f39eca21041175cf6510820a5ae4aa0841045d7598c420830f2a4c6210418755263108208beeab18841061e5458c420830eaa2c62104117dda53108208baed298841045f7654c420822ebb2a6210418bd954210820c5acaa10841068d63508420838729a8421041c354d4210820c74a8b00841065953582320821f3a6ca190410f5d3650c82087aeb320641043f75590320821fbb4a8190410f5da540c82087eecaa0641043d76550320830f324a61904187592530c820c3cc8a98641061d6454c32082a6b92a61904193d95320c820c9aca990641068d644c832083872a26419041c3551320c820cb4a6b00641061e5498f510830eaa4c7a88418795163d4420c3aa8b1ea21061e6494f510830eb24a7a88418799153d4420c3ac8a9ea21053674d46510829aba6a328841559cf5194420aaae7a8ca21045e73992510822eb9cc9288410f9d2639442087ae931ca21055673d5251082aab9ea928841559cc5494420aaae62a4a21053674d4e510829aba6a728841c59525394420e2aa929ca2107165454e510838aaa2a7288414d9d05394420a6ae829ca2107255418a51083a2a98c528841559ce6494420aaae7324a21056672992510829b3a4c7288414d5d26394420acc
  | 16 => 0x831732a8520a4117dcd65105208b8e6b28829045e73194414822eb98ca20a41475cc5410520c58a8b10829052c75508414831632a8420a41c95085110520d5284b00829043e74197314821eba0cb98a418d99351cc520c6cc828e629066562147314828eba0a718a412b5d2628c520a98ea994629064e654ca314821fba2ca18a410f1d1650c52087ce8328629043d74194314828eba0a618a419314d620c520a98ea990629064c654c831483a2990a218a41b24c9600c5208dcebb2642904cd73d93214831732cc990a418b99564c85208dcebb1e42904ad74d8f214832732cc790a41a359263c8520c9ccab1e429068e6458f2148346b22c790a418b59051c8520c9ac628e42904ad741812148266b98c090a412b5d2620852099ae7310429051d7315340483162a2c5a02414b1d542d01208bee6b2a809045c73595404828eb98a8a0241335cc6250120a58eaa12809062c65509404828eba0a7982419314d62cc120a98ea996609043f74595304821e3a2ca98241475d0534c12095ae8312609054c754c9304832632a64982416a5d321c8120b92e790e40904af745862048267b9ac310241995845188120c9ac7316a81065663987540832ab1cc3aa0419598d61d5020caac6b0ea810666625875408332392c3aa041479cf5495020a3ae7aa4a81053671d52540829ab8ea92a0418758c6395020a5ce431ca81051e7318a540828eb98c52a041479cf6195020a3ae7b0ca81052e72d86540828f398c12a041475cc6095020a6ce2304a81053571182540828f39ec8aa041475cf6455020a6ce3b22a81053571d915408237390c6aa041179cf61550208bae7b0aa81052c7258d540830eb18c6aa0414b9c86355020a3ce6312a81051d73189540828f39ec2aa041475cf6155020a5ce5b0aa81052c72585540828f398c0aa041475cc6055020a6ce2302a81053571181540821fbb2a82a041875526315020c3aa8b18a81063554984540831aaa2c22a041879926315020c3cc8b18a81064e639885408326b1cc42a0418d9926115020cacc7308a810655639845408333314c22a0418d9916115020cacc6b08a810655635845408333312c22a0419c5866015020c6ca930ea61063554987530831b2a2c3a98418d55161d4c20c5ac9316a61063664987530831ab24c3a98418d99161d4c20c6ac8b0ea610666625875308332392c3a9841479d35394c20a3ae9a9ca61055671d4e53082aab8ea729841559c75494c20aaae3aa4a6105567115253082aab88a929841875906494c20a9ce4324a61051e7418a530828eba0c529841479d36194c20a3ae9b0ca61054e72d86530828f3a0c129841475d06094c20aace2304a610555711825308237390c8a9841479d36354c20a3ae9b1aa61055671d8d53082aab8ec6a98410f9d36154c2087ae9b0aa6104
  | 17 => 0x84419554d610c220a5ee8a8e411054f73547208833330aa39044117dcd61d51208b8e6b0ea89061f6418d5448326b90c6aa2419318f6255120caec7b0aa89065463d85544831bb20c2aa24195d8c6155120ca8c630aa89066762185544821fbb2a82a241471cd5415120a68e2aa0a89061d5458c544830f322c62a2419398d6215120c9ac6b10a89045e73188544822eb98c42a2410fdd161d4d20878e8b0ea69061d731915348316b90c8a9a41871936354d20c58c9b12a69063764d85534831a326c2a9a418dd906154d20c68c830aa690657631855348333b10c2a9a4117dd95314d20a38e8a98a69061d6454c53482aa38aa629a41871cd6414d20c3ac9318a69062e645885348316b22c429a410f9d06214d2087ae8310a69047671d97434823ab8ecba1a41471cd54d0d20a68e2aa6869051d7414f43482363aac5a1a411d9c76590d208eae3b2c869051d73152434828e3a2a721a41551c55390d208d8eab14869046f72595434823bb8acaa1a411d1c56550d2087ced2a2869043c76551434828e39aa8a1a414d1c55450d208bced29a869045c7654d434828e3a2a6a1a41551c55350d208dae5b28869047771594434823a38aca21a410f9d06510d208bce6328869046e72194434821ebb6a821a41475cc5410d208baeda98869051d7414c434828f3aa8621a41471d54310d20c3ecaa18869061d6550c43482363aac421a418bd516210d20c58a8b10869064f53588434832629ac421a41a350d6210d20a3ae62a6849054d731524248237bb2a7212414b1d15390920ac8e2a9c849051d7315142482973aec8a12414b9d254509208dcec2a2849054d7315142482c6b98a8a12414b9d85450920c5cec2a2849070e731514248296b98a8a1241c35cc5450920a1ae62a2849052e7115142482363b2a6a12414b1d15350920ac8e2a9a849052c75d0d4248387a9e86a12414b1d54350920e1aa6a1a849046e75d854248266b9ec2a1241335cc60509209cae2302849068d63508424828eba0a7992411b9d7648c9209cae3b24649046f7655232482a639aa919241591c5548c920a5ae829c649051d7414d32482363aac8992411b1d9544c920a98e6aa264905647155132482a73aec699241539ce534c9208dcec29a649052d7414d32482c6ba0a699241539d8534c920c9cec29a649070e7414d32482a6ba0a699241c35d0534c920a1ae829a649054e7114d32482a63ac8699241c3d52434c920a98eaa1a649070d5450d32482373aec2992412b5d3614c92095ae830264904e5711813248346b2264192411ddd95114520a68e8a88a2905547354451482b2b8c8428a4159dc54214520acae3190a290567714c8514822f398cba0a41175cc65d0520cacc7a8e8290656631474148332b10a3a0a41475cc549052099ae7314829052c7550a414
  | 18 => 0x39472087ae931ca39062e6450a51c832731a6528e411ddd951147208bce7b2e839045d73d9741c822f39ecb20e41175cf65907208bce732c839045d7399641c8316aa4c520e41335ce6290720c5ccaa1483905357195041c821f3a6cb98e410f5d365cc72087ce9b2c639043d74d9631c821f3a4cb18e410f5d2658c72095ae9314639064d5398a31c832732a6518e41555c6530c72099ae7b2643904ad74d8f21c8346b24c790e41a399163c8720d1ac8b1e439062d6494721c8326b1ca390e41aa59160c8720d92c6b0643905e170d4521c82733b0a290e412b5d0604872099ae630243906e12158021c8316aa0c4a0641335cc625032095ae8312619064d5318930c822fb9ac3aa441171cd61d522087eecaa0a91061d5458c548831aaa2c22a441879916315220c9cc6b10a91064d63588548832b31cc22a4419558e6115220ccac5308a91063664584548832b31ac22a4419558d6115220ccac4b08a91043f74587538821e3a2c3a9c4117dd95314e20c3ac8a98a71065553584538830eb24c629c418b9916214e20c5ac8b10a71063664984538831ab24c229c419958a6114e20c6cc8b08a71063564584538832b31ac229c41995896114e208ece232e871047571197438823b388cb21c411d5c46590e208eee2b2a871047471595438823b388caa1c411d5c46550e20a38e6aa2871051c7454d438823b388ca21c411d5c46510e20c3ecaa18871061d6550c4388346a1ac421c41a358d4210a20d1ac8990651045e73992518822eb9cc928c410f9d2639462087ae931ca31063571191518830fb26c6a8c41871936354620c3ec831aa31061c6418d518832ab88c6a8c411ddd95114620c6ac8a88a31065563544518822f39ecba0c41175cf65d0620c3ca8b1e831061d5458f41883172a2c5a0c418b55162d0620a3ae62a4831053571152418829a3a2a320c4117dcd65506208b8e6b2a831045e73195418822eb98caa0c410f9da545062087aedaa0831051d73150418829ab88a820c410f9d365cc62087ae9b2e631061d6494f318830eb22a798c419394d62cc620c9aa6b16631051d7414e31882aab88a718c41551cd518c62087ee8b2a631043c74595318821f3a0ca98c410f5d0654c6208bced29a631045d76d4c318828eba0a618c41555c4530c620a5ee8a8c431054f735462188236bb6a810c4159dc554086208daeda9843105677154c2188297ba2a210c4153dcd5108620a3ae62a6811053571153408821f3b0a8a0441475cc5450220a6ae22a2811043f76550408830f2a2c620441875516310220c5ca8b10811062d54588408831b2a2c2204418d5516110220a3ae829e61105557114f308822f3b0a698441475d0534c220aaae229a611061d6494c308822fbb2a61844187591530c220c9ca6b10611064d53588308832b29ac21
  | 19 => 0x6a90801864d63548400c23abacc2200618d9526110030c6aa9308801866652984400c332a94c2200611ddd56110030c6ca8b08801863554584400c333292c2200619954961100308eaed288801865663944400c32ab1ca2200619998a5110030ccac5288801847776544400c32b31aa2200619558d5110030cccc4a88801866562544400c2a6b96a998061555c754cc030e1aa9296601870e5454b300c386aa2a5980618755261cc030c9aa530e601871554947300c3a2a94a39806117dd951cc030cacc2a8e601871654547300c38aaa2a398061d194951cc030e8aa4a8e601865776547300c22ebb4a7180611e5da538c030e62a8a8c601876152546300c22f3b6a898061535cb544c030aaae3aa2601851d75951300c30fb2ca89806187d95544c030c9ecb292601870d54949300c327b2aa498061c3951524c030e1aa8a92601861d54185300c326a90c29806195d96514c030e2aa928a601874552945300c32a30aa29806195d95514c030e2ca8a8a601871554545300c3a3292a298061d1549514c030ca8eca8a601861d54d81300c31db2ca8980618ed95544c030e32a929a601866b65949300c335b2aa498061d294d524c030ce6cb28a601867365545300c398aa2a298061d494d514c030ec2a4a8a601854d7398b54c822f39ec2aa641175cf615532087eecaa0a99061d5458c54c830f322c62a6419358e6215320a5ae9316a79043e74d8553c821eba6c2a9e4117dd95314f20c3ac8a98a79061d6498c53c8316b24c429e411d9c765d0f208eae3b2e879047671d9643c823ab8ecb21e411d9c66550f208eae332a879051c7355143c828e3a2a6a1e4187d954310f20c3acaa18879068d4358843c828eb98a9a1641535cc5490b208deeab0c859043e7615142c828eb98a8a16416a5c35450b208dcec2a2859054d7315142c82573b0a8a1641635cc5450b20a5cec2a2859062e7615142c8387398a8a16414b5cc5450b20e1ae62a2859050d7315142c8297388a8a1641ca5c05450b208dceda9a859052c7454d42c82963ae86a16414b1d54350b20e1aa6a1a85904cd73d8542c8266b98c0a1641395c46050b2087eecaa0859061e5458c42c830eaa2c621641a358d4210b20d5284b00859051d7414f32c8272b8ec9196414b5d0538cb208deeab0c659045e7614d32c828eba0a6996411b9db544cb20a98e6aa265905c970d4d32c82373b0a6996414b5d0534cb2099cec29a659058d7414d32c82a73b0a699641939d8534cb20e1ce829a659054d7414d32c8386ba0a699641435d0534cb20a9ce229a65907497014d32c82a63ac8699641531d5434cb20e1aa8a1a65904ad74d8532c8256ba0c099641395c4604cb20c3ac9298659045f7654c32c830eb22a619641a3591320cb20d9264b00659045e7399251c822eb9cc928e410f9d26
  | 20 => 0xd6394b410c237bb2a5a08611b5d952d0430c9cc6a96821864d6354b410c32b31ca3a08619558e51d0430cccc528e821866562947410c32b31aa3a08619558d51d0430cccc4a8e821866562547410c237394cb208611b5ca65904308dce432a821846d72195410c22ebaec6a0861875536350430c3aa831a821864f63549410c32631aa4a086195d8d5150430ca8c6a8a821846e72994410c236b94ca208610f5d664cc43087eeab26621843d76953310c21fbb2a9988618759253cc4308daeb316621862e5498b310c316aa4c5988611bdd562cc430c5ca8b16621862d5458b310c32729ac5988611b5da52cc430c5cc9296621862d6494b310c237bb2a5988618b99152cc430c5ac8a96621863664947310c31ab24a3988619998a51cc430ccac528e621863664547310c31ab22a3988619998951cc430ccac4a8e621867151583310c32b38acb18861175db548c430a9ae5aa4621855571d52310c30eb2ca91886187595548c430c9acb294621870d5494a310c326b2aa518861c3951528c430e1aa8a94621865565946310c38aaa4a318861d154a518c430e2ca8a8c621871554546310c3a3292a318861d1549518c430c3aa8b04621864d52582310c32aa8ac1188618e552600c430cd2a5300621863954580310c334a92c0188619c945600c430a9ae5aa0621855571d50310c28ebaca818861c3552520c430e1ca8a90621870d54548310c30eaa4c218861555d6610c430e2aa9308621874552984310c38aaa4a218861d154a510c430e2ca8a88621871554544310c3a3292a218861d1549510c430aaeeca88621865776544310c38caa4c018861d254a600c430c3aa8b00621864d52580310c38caa2c018861d2549600c430da4c2b00621843e74d97210c21eba6cb908610f9d265c843087ae932e421843d75993210c21fbaac9908610fdda54c843087aed2a6421843f76553210c21ebb2a9908618795263c8430c3aa931e421861e5458f210c30eaa2c7908618b99252c8430c5ac9296421864d6394b210c317322a5908618b59152c8430c9cc6a96421864d6354b210c31b324a3908618d59251c8430cacc728e421865563947210c31b322a3908618d59151c8430cacc6a8e421865563547210c21f3a4cb108610f5d2658843087ce832a421843d74195210c22ebaec690861875536348430c3aa831a421864f63549210c32631aa49086195d8d5148430ca8c6a8a421843e74994210c21eba4ca10861175d83194030c3aa931c801845f7558e400c30eaa2c7200619398d5290030c9ac6a94801865663546400c32ab1aa320061875526310030c3ca8b18801861d5458c400c236bacc4200618b9526210030c5aa9310801846f75588400c3172a2c4200618b55162100308daed290801864e63948400c326b1ca4200611bdd95210030c9cc
  | 21 => 0x30eaa4c621061879516310830c3aa8b18841852d74948420c32731ca4210619358e5210830c9cc6a90841864d63548420c297baa84210614b5d54210830c5ecaa10841862d65508420c346b1a84210619a54960cc83087aeb320641843f75590320c21ebb4a8190610fdd9540c830c5cc9290641862d64948320c317322a4190618b591520c830d1ac8990641870e544c8320c386aa264190619a949600c830c5ca9316a21862d5498b510c3172a2c5a88618b55162d4430c5cc9296a21862d6494b510c317322a5a88618b59152d4430a6ce9a8ca21853574d46510c2b3396a328861595cb51944308dce5324a21846d72992510c21f3a4c5288610f5d26294430acce5aa4a21856572d52510c2b3390a928861595c85494430e2aa831ca21853674d4a510c29aba6a528861c99525294430e4aa9294a2187265454a510c392aa2a528861d118d5294430a6ce8294a2185357414a510c2ab39cc928861599ca6494430acae5324a2187154310e510c2b33908728861595c84394430a6ce9314a2185357498a510c2ab39cc528861559cc4294430aaae6214a2187254210a510c29b3a065288614d5d03294430e8a64194a21853674182510c29aba0c128861599c86094430acae4304a21847676d51510c2b3396a8a8861595cb54544308ecec2a2a21856672151510c2b2b90a8a8861c59506354430e2aa831aa21847676d49510c29b3a6a4a88614d5d35254430e4ca9292a21872554949510c3a231ca4a8861c99515254430e4aa8a92a21874463549510c23b3b0a4a88614d9d05254430a6ae8292a21855673991510c2b3394c8a8861595ca6454430aa8e6b22a2185367498d510c29aba4c6a8861599ca6354430acae531aa2187154310d510c2b339086a8861595c84354430ae4e021aa2185717010d510c29b3a4c4a88614d5d26254430aace7312a21855473589510c2abb9a84a8861551cd4254430aace6212a21855573109510c392a1084a88614d9d03254430a6ae8192a218745320c9510c2b938064a88615c5c03254430a6ce8302a21853574181510c2b3390c0a8861595c86054430a6ce8182a218535740c1510c2b339060a8861595c8305443087aed2a0a21843f76550510c3172a4c4288618b5526214430c5ca8b10a21862d54588510c236bb4a4288618b9925214430c5ac9290a21846f76548510c317322a4288618b5915214430c6ca9308a21863554984510c333294c2288619954a61144308eeeca88a21863664544510c31ab22a228861999895114430ccac4a88a21846e72d97410c236b96cba08611b9ca65d04308dae532e821861d5498f410c30f2a2c7a08618755163d04308daeb316821862e5498b410c316aa4c5a08611bdd562d0430c5ca8b16821862d5458b410c237bb4a5a08611b5da52d0430c9cc7296821864
  | 22 => 0xa610f5d06508530a5ae8290429864d63148214c32632a6410a61d14c85108530d9264b00429852d72153404c30e2a2c7a0261471d543d0130a5ae42a280984cd7218d404c28e3aa86a0261871954350130b32e998e60985c972cc7304c24fba2c31826133dc9618c130caac228c609864e6358b540c333314c3aa0619958a61d5030cacc6b0ea81866662587540c332b12c3aa061951cd61d5030a5ce5aa4a81852d72d52540c29b38ea92a0614d5c75495030a5ce431ca81852d7218e540c28f398c52a0618b5886295030a3ce7b0ca81852e72d86540c296b96c32a0614b9c86095030a5ae4304a81853671182540c29ab88c12a0614b9cb6455030a5ae5b22a81853671d91540c29ab8ec8aa0611b9cb61550308dae5b0aa81852e7218d540c296b90c6aa061471cd6255030a3ce6312a81862d62189540c28f39ec2aa0614b9cb6155030a5ae5b0aa81851c73585540c297390c0aa0614b5c86055030a6ce2302a81853571181540c21fbb2a82a0618b5526215030c5aa8b10a81863554984540c31aaa2c22a0618b9926215030c9cc7310a81862e64588540c32731ac42a0618d9926115030cacc7308a81866662984540c332b14c22a0618d9916115030cacc6b08a81866662584540c332b12c22a0619c5866015030c72a8b04861851d73550430c30fb2a8621861875954310c308daeb310861862e54988430c316aa4c4218611bdd56210c30c5ca8b10861862d54588430c346a1ac4218618e9516010c30c6ca930ea41863554987520c31b2a2c3a90618d55161d4830a5ce9a94a41852d74d4a520c2b338ea529061595c75294830acce3aa4a41856571d52520c2b3388a929061595c45494830c5ac8324a41854e73192520c2973a0c7290614b5d063948308daec21ca41870d4310e520c2973a6c3290614b5d36194830a9ce7b0ca41852e74182520c296ba0c129061599c46094830acae2304a41843e74d85520c21eba6c2a90611b9db5454830acce3aa2a41856571d51520c2373b0a8a9061599c45454830acae22a2a41854c73591520c316b20c8a9061539cc64548308dcec21aa41870d4310d520c2973a6c2a90614b5d36154830a9ce7b0aa41854c73585520c2973a0c0a90614b5d06054830acce2302a41856571181520c2973a060a90614b5d0305483087aed2a0a41843f76550520c3172a4c4290618b55262148308deeca90a41862e64548520c316b22a4290618d9526114830c6aa9308a41866552984520c31b2a2c2290618d5516114830ccaa4b08a41847671997420c23ab8ccba10611d9c665908308eae332c841847671195420c23ab88caa10614b1c954508308baebb1a841861d54d8d420c30eaa0c6a10614b1d15250830c9ec6a92841864c63549420c23b38cca210611d5c66510830a5ae52a0841861e5498c420c
  | 23 => 0x4863087ae832a431852d72153408c29ab88a9a04610f9d85450230a5ae42a2811853571151408c21fbb2a820461879516310230c3aa8b18811862e54588408c316aa2c4204618d9516110230c6aa8b08811851f74547308c2a7b92a3984619598551cc2308dee4b0ea89846c72587544c317b20c4aa26193d8c6255130c9ae6312a89866762d85544c332316c2aa2618dd906155130caec630aa89866762185544c332310c2aa2610fdd95415130a58e4aa0a89853471550544c316aa2c42a2619358e6215130c5cc8b10a89864d63588544c296b90a9a1a61535c85490d30a5ae42a2869851e75d91434c28f3a4a8a1a61179d85450d30a9ae42a2869858d72151434c28f3b0a8a1a61879d85450d30e1ce42a2869851d72151434c386b90a8a1a61435c85450d30a3ce22a2869845e75d85434c266b96c2a1a61335c86050d309aae2302869868d43588434c21fba2c3a92610f1d161d49308deeca90a49852c74548524c316b22a429261591c55214930c58e4b20a49852c72553424c29a38aa9a12618719543d0930e1a87a96849852d7414b424c296b90a9212610f9da5450930a58e4aa2849853471551424c30e32a86a12611ddc565109308e8e2b28849843d76d50424c296b90a82126187d516310930c38a8b18849864d63d48424c296ba0a4212619358c5210930a5ceaa10849852c75508424c316b2a8421261a358d42109308bcebb2664984d571d93324c22fbb2a999261531c954cc930aa8e2aa6649851d7414b324c296ba0a5192614b5d0524c930a98e4aa2649855471551324c2a73aec499261475d0524c930b1ae8292649854e76149324c3273b0a499261c39d0524c930a9ae8292649870d74149324c286ba0a499261539c4524c930a98eb212649870f54909324c2a63aa8499261c3551424c9308bcebb0a649849d74d85324c24eba0c099261355c4604c930d1ac8990649847776544514c29a3a2a228a61591c95114530aaae3218a2985577150c514c2aab8e6428a6155dc532145308dce432e829846d72197414c333316a3a0a619558c51d0530cccc428e829852d72152414c266b94c720a61471d54390530c3ccaa1c829846f72594414c236392ca20a611b9c865105308dae4328829852d72150414c30e2a2c620a61471d54310530c38caa18829871543144414c34ca1ac020a61179d764cc53099ae5b26629861e65993314c30f32ac998a619399662cc530d1ac9316629864e6558b314c347322c598a61a359162cc530c3ac828e629864d62147314c24eba0c098a61335c8604c53093ae9318629843e74197214c21eba0cb90a618d99351c8530c6cc828e429865563147214c24eba4c710a614b5d05288530c9cca994429845e7598d214c24eba4c690a61335ca634853087ee8b28429843c74594214c21f3a0ca10
  | 24 => 0x2a2879858d7215143cc28f3b0a8a1e61879d85450f30e1ce42a2879851d7215143cc386b90a8a1e61435c85450f30a3ce22a287987197015143cc266b96c2a1e61335c86050f309aae2302879843f7655043cc3172a2c421e618b5516210f30d1a86b1087986994358043cc30e32286a96610f9d36154b3087ae9b0aa59846f7654852cc316b22a4296611d9c765d0b308eae3b2e859847671d9642cc23ab8ecb216614b1c95450b30c38caa1a859852c7454942cc386a1aa4a16618bd954210b30c5acaa10859868d6350842cc26ab8ec99966117dd561ccb308bcedaa2659854c7255132cc2e4b86a499661339d8524cb30b1ae8292659854c7550932cc386aa28499661275d3614cb3093ae830265984d57118132cc316b24a4196618b591520cb30d1ac899065986c93258032cc237394c928e611b5ca6494730c3cc8a1ca39843e7498a51cc21eba4c528e619398932947308eeeca88a39846e72d9741cc236b96cba0e611b9cb65907308dae5b2c839846e7299641cc236b94cb20e6187552639073099ae531c839861e6550e41cc29ab8ca820e61335cb64cc730d1ac9316639868e6458b31cc346b22c598e618759251cc730c9ac528e63986996458331cc364b12c198e61745c3514c7309acec28a639849d7418131cc266b90c098e61b44c5600c73087ce9b2e439843d74d9721cc21f3a6cb10e610f5d3658873087ce932c439843d7499621cc24eba4c710e619398d5288730c9cca994439849d7498d21cc2b2b8ca410e6187550635033099ae431a819846f72587548c236392c3aa4610fdd95415230c5aa8b10a91863554584548c326b1cc42a4618b9916215230c9ac6b10a91865563984548c333314c22a4619958a6115230c6cc8b08a91865563584548c333312c22a461995896115230d1a86b10871846f76548528c316b22a429461995496114a308eee2b2a851847471595428c23b388caa14611d5c46550a30a58e4aa2851852c74549428c317b2a84214618b5954210a30d1ac6a10851868d644c8328c237394c928c611b5ca649463087ce9314a31843d7498a518c31ab88c8a8c618bd936254630c58c9b12a31862f64189518c316320c4a8c611ddd95114630c6ac8a88a31866562544518c237396cba0c611b5cb65d0630c3ca8b1e831861d5458f418c3172a2c5a0c618b55162d0630a5ae42a4831853571152418c29a3a2a320c611bdc965506308d8e4b2a831846e72195418c236b90caa0c610f9da545063087aedaa0831852d72150418c29ab88a820c6147dd1518c630a9ee4a8c631845d76d50318c2abb8aa818c6155dc5520c630a3ee8a88631854f72544318c21f3a6cb90c610f5d365c8630c5ac9296431864d6394b218c316b22a590c619358d52c8630ac8e4a8c431843f74595218c21e3a2ca90c610f9d065
  | 25 => 0x53548411029abacc220881c554e6110440e4aa53088220715539444110392a94a220881c594d5110440e2aa6a888220726525444110392a92a2208814ddd95110440c6eeca888220719539804110394a94c0208818754d6010440c5aa4b008220719535804110394a92c020881ac98560104408dce5b2e622046d72d973110237394cb988811b5ca65cc440c3ac929e622061e6454f311030eb22a7988811b5d662cc440c9ca7316622064d5398b3110237baac5988819394d62cc440c9aa6b16622046f7694b3110236bb4a5988818b99252cc440c5ac9296622046f7654b3110236bb2a5988818b99152cc440c5ac8a96622063664947311031ab24a3988819998a51cc440ccac528e622063664547311031ab22a3988819998951cc440ccac4a8e622046e729963110236b94cb188811b9c8654c4408dae432a622043d75d91311030fb22a69888187191534c440c5ec8a92622062c64549311031bb22a2988818d191514c4408dce5328622046d72994311022f39ecb90881175cf65c84408bce732e422045d73997211022ebacc79088117dd563c84408beed29e422045d7694f211030f324a7908818759253c84408beeca9e422045d7654f211030f322a7908818759153c8440c5ac9296422064e6394b2110326b1ca5908818b99152c8440c5ac8a96422064e6354b2110326b1aa5908818d99251c8440c6ac928e422065663947211032ab1ca3908818d99151c8440c6ac8a8e422065663547211032ab1aa390881179ce65884408bae732c422045e73195211022eb98ca908810f5d76448440c3ec8a9a422061c6454d2110317b22a4908818b1915248440c6ec8a8a422063464545211022f39cca10881175ce650844087aec20ca02070d5394b401038729aa5a0081c354d52d0040c3aa730e802062d52987401038aa9ca3a0081c954a51d004087eeca8e802063661547401038b29aa3a0081c554d51d0040e4ca4a8e802072552547401031bbb2a3a00810f5da54900408f2ed2a480207515354640103b0a92a32008187d965350040c3ecaa9a802062f659494010386a9ca4a00818bd955250040e1ca6a92802070d53549401030ea98c2a00818b5486150040c6ecb28a8020715539454010392a94a2a00818d1855150040c6ecaa8a802071653545401038aa9aa2a0081c99495150040e4aa4a8a802063476545401032db2ca6a008196d955350040e34a8a9a802066b659494010335b2aa4a0081ca9515250040ce6cb28a80206736554540103992a2a2a0081d454d5150040ec2a4a8a802054d7298f54cc237396c2aa6611b5cb615533087eecaa0a99862d5458854cc317322c42a6619398d6215330a5ae42a6879854d7215243cc22fbaac321e610f9d85450f30a5ae42a2879859970d5143cc22f3b0a8a1e61535c85450f3093cec
  | 26 => 0xb3396a328881595cb51944408dce531ca22046d7298e511022f39cc528881175ce6294440acce5a9ca22056572d4e511038a322a728881599c85394440acae429ca22055673d4a51102aab9ea528881d194e5294440e8aa7294a2207465354a51103a2a9aa528881c91915294440aace6294a2205557314a511029b3a4c728881599ca6394440acae531ca2207154310e51102b33908728881595c84394440a6ce9314a2205567398a51102aab9cc528881559cc4294440aaae6214a2207254210a511029b3a065288814d5d03294440e8a64194a2205567318251102aab98c128881599c86094440acae4304a22047676d4d51102b3396a6a8881595cb5354440e28c929aa2207146454d511023b3b0a6a8881599c85354440acae429aa22047676d4951102ab39ea4a8881555cf5254440e8ca7292a220745539495110392324a4a8881d194d5254440e8aa6a92a22072464549511023b3b0a4a8881559cc5254440aaae6292a2205567399151102aab9cc8a8881599ca6454440acae5322a2205367498d51102b3394c6a8881595ca6354440a68e8b1aa2207154310d51102b339086a8881595c84354440ae4e021aa2205717010d511029b3a4c4a8881559ce6254440aaae7312a2205347458951102ab39884a8881555cc4254440e4a84212a2205727010951102b8b8084a88814ddd13254440a68e8992a220536740c9511029aba064a8881d14c83254440aace6302a2205557318151102b3390c0a8881595c86054440aace6202a2205557310151102b339080a8881595c840544408baed298a22045f7654c511032729cc4288819354e6214440c9ca6b10a22064d535885110236bb4a4288819398e5214440c9ac7290a22046f76548511032731aa4288819358d5214440caca7308a220655539845110333294c2288819954a61144408eeeca88a22065663544511032ab1aa228881999895114440ccac4a88a22045d7598f411022fbaac7a08818795163d04408baed29e822045f7654f4110236bacc5a08819394e62d0440c9aa7316822046f7558b41103172a2c5a08819394d62d0440c9aa6b16822046d7694b411032731ca5a08819358e52d04408deeca96822064e6354b4110326b1aa5a08819598e51d0440caac728e8220666629474110332b14a3a08819598d51d0440caac6a8e8220666625474110332b12a3a08819c54560d0440c6ce2b2c822061d6594e411030eb2aa7208818b5965290440e1aa7294822062d6554a411038729aa520881c354d5290440c6acb28c8220715539464110392a94a320881c594d5190440e2aa6a8c8220726525464110392a92a3208818754d6090440c5aa4b04822063551582411032ca9cc0208819a54a6010440cb2a6b00822066952580411033928ac020881c354e5210440e1ca6a90822070d
  | 27 => 0x81175cc6508540c5ac829042a054d73148215031632a8410a81c95085108540d5284b0042a059973d0740502d4b9683a028127dcd619014095ee4b0c80a06356114640502a7396a729881535cb5394c40aace3a9ca62055571d4e53102a7390c929881535c86494c40a3ce8314a62064d6218a531028f3a6c329881539cb6194c40a9ae5b0ca62054e7218253102a6b90c129881559c46094c40aaae2304a62046e72d855310236b96c2a9881471d16254c40a3ce8312a62064d62189531028f3a6c2a9881539cb6154c40a9ae5b0aa62051c7458553102a7390c0a9881535c86054c40aace2302a62055571181531022fbb2a6298819354e6214c40c9aa6b10a62065553984531032aa9ac2298819654d60d0c408daeb310862064e539884310326a9cc4218811bdd56210c40c9ca6b10862064d535884310346a1ac4218819694d6010c40caca730ea42065553987521032b29ac3a90819554d61d4840a9ce7a94a42054d73d4a52102b338ea529081595c75294840acce3a9ca42056571d4e52102b3388a729081595c45394840a9ce6324a42054d7319252102973a0c7290819358c63948408daec21ca42070d4310e52102973a6c329081539cf6194840a9ae7b0ca42054e7318252102a6b98c129081599c46094840acae2304a42045e73d85521022eb9ec2a90811b9db5354840acce3a9aa42056571d4d52102373b0a6a9081599c45354840acae229aa42052c7458d52102973a0c6a90819358c63548408dcec21aa42070d4310d52102973a6c2a9081539cf6154840a9ae7b0aa42052c7458552102a7398c0a9081535cc6054840acce2302a4205657118152102a739880a9081535cc40548408baed298a42045f7654c521032729cc4290819354e62148408deeca90a42064e635485210326b1aa4290819594e6114840caaa7308a42066552984521032b29ac2290819554d6114840ccaa4b08a42066952583421022ebacc62108117dd563108408baed298842045f7654c421032731ca4210819358e5210840c9cc6a90842064d635484210346b1a8421081c394d4210840e1aa6a10842066a52580421023b38ccb990811d5c665cc8408ece332c642047571996321023b388ca990811d5c4654c84087aebb22642061f6454d321030e322a699081531c9534c840c5ec8a92642062c6454932102a639aa4990811d9c6650c8408eae3328642061e6494c321030eb24a619081535ca530c840c3cc8a98642061d6454c3210317324a4190818b592520c840a9ae7290642062e645483210316b22a41908153dd5320c840a9aea990642064f654c83210326b2a6419081a3591320c840c9ca7316a22064d5398b511032729ac5a88819354d62d4440c9cc7296a22064d6394b511032731aa5a88819358d52d4440aace7a8ca22055573d4651102
  | 28 => 0xca40c9eca990652064d654c83290346b2264194811b9ca63946408dae531ca32045e7398a519022eb9cc528c8193d8f6254640c98c7b12a32064f631895190326318c4a8c811ddd95114640caac6a88a32066562544519028fb9aa320c814bdc95190640a6ee2a98832053771548419028fb9aa220c814bdc951106408dce5b2e632046d72d97319030eb24a798c818759153cc640c9ca6b16632064d5358b31902aa39aa318c811bdc9654c6408d8e4b2a632046e721953190236b90ca98c81179cf65c86408bae7b2e432062d6494b2190326b1ca590c818b59152c8640c9ac6a96432056472546219022fb9aca90c81171cd65486408bce632a432045d73195219028fb9aa3a04814bdc951d0240c6cc2a8e812046f725875350236392c3a9a8117dd95314d40a98e4a98a6a05547154c5350326a9ac429a814b5c853d0d40a9ae429c86a054d7214d435028f3aec6a1a814b5c85350d40b1ae429a86a051e7614d435030f3b0a6a1a81c39c85350d40a3ae429a86a070d7214d4350286b90a6a1a81479c45350d4087cebb0a86a04ad72d854350256b90c0a1a812d5c46050d40d1a86b1086a045f73587525022e39ac3a92811bdd95214940a98e6a90a4a064d6354852502b238aa429281475cc52d0940a9ae629484a054d7314942502973aec4a1281475cc5250940b1ae629284a052e7614942503173b0a4a1281c39cc5250940a5ae629284a070d731494250286b98a4a12814b9c4525094087cebb0a84a049d73d85425024eb98c0a12812d5c46050940d1ac6a1084a061c6550f3250386a1ea599281535cc52cc940a9ae429c64a062c6550a3250387a9a85192810f9d6644c94096ae332264a061c6550d325031632a84992811ddc5650c9408e8e2b2864a061d64d4c325030eb20a619281535c8530c940c5ac9a9064a062d6414832502a6b98a419281539d5320c940a98ea99064a064d654c83250346b2264192811ddd95114540aa8e6a88a2a056472544515029ab8e8628a814ddc54314540a6ae3a10a2a053771508515030f32cc7a0a818799563d0540c5ccb31682a068d6398b415031732ac5a0a81a398d62d0540d1ac6b1682a061d631474150316b10a3a0a81275cc605054095ae430282a046e721973150236b90cb98a819998b51cc540c6ac828e62a0666621473150256b94c918a81535c8538c540c3ccaa1c62a043e75991315024eb9cc898a812b5ca644c5408dee4b2862a046c725943150237390ca18a811b5c8650c540c3ac829862a054d7214c315030e32a8618a81c550c510c540d3286b0062a045e73197215022eb98cb90a819598f51c8540c6ac828e42a065663147215024eb9cc910a81535cc5288540c5ccaa1442a043e75991215024eb9cc890a812b5ca64485408bee6b2842a045c73594215022f398ca10a
  | 29 => 0x986410e8d644c83208762994c219043179ce64944218bae7324a210c3e7498e510861eba4c7288438b9914294421c9cc6994a210c5e73d96410862eb9ecb208438b552629042199ae73148210c5e73194410862eb98ca208438b195421042187ce9b2c6210c3d74d963108656ba4c5188439354e628c42187ce83286210c3d74194310872632a6418843335cf64c842195ae9b1e4210e8d6498f2108747322c790843a359163c84218daed2944210d2d7494a21086a6b9ca5108431d5da5288421b4ae92944210dc57394a2108637baac8908431bdd5634842195ae9b0a4210ccd73d8521086733b68290843719cf4148421d4ac820a4210ce676cc521086d33a66290843b158c314842195ae83024210ccd7318121086d33a4a490843719ce52484219ccec2124210dc67310921086733b06490843699d032484218bce6322a010c5d73191500861f3a0c6a80430f5d06354021acae3212a010e2c6450950086b2b8c64a80439318d3254021a5ae990aa010d4d73c8550086b538642a80435a1c121540218f6eca80a010e3964540500872cb1aa0280431b9cb6154f408dae5b0aa7a045f7654c53d0326a9ac429e810fdd561d0f40b32e1a9a87a049e7614d43d02c6b90a6a1e812b5cb6150f4095ae430287a04b57118143d032729ac421e819354d6210f40d1a86b1087a06994358043d030e31a86a9681179cf6154b408bae7b0aa5a046f7654852d0326b1aa4296810fdd561d0b40a58e4a9a85a05a970d4942d02573b0a4a1681635cc5250b4093ae7b0a85a049d7318142d025ab88c0a16819358e5210b40c9ac6a9085a068d6350842d0354a12c0216811d9c765ccb408eae3b2e65a047671d9632d023ab8ecb196812d5c6644cb40a98e4a9a65a061c6550d32d02a639aa499681c350d524cb40c58caa1265a070d5350932d0327b2a641968193595320cb40d1ac899065a046e7298e51d0236b94c728e818798d43947408bce7314a3a045d7398a51d03173128528e811ddd95114740d1ac731683a068e6358b41d0346b1ac5a0e818758e51d0740c5ac528e83a06996358341d0354b12c1a0e816c5c3515074096cec28a83a049d7318141d0256b90c0a0e81ac50560107408dce5b2e63a046d72d9731d0237396cb18e811b5cb658c7408dce532c63a046d7299631d0256b94c918e8187991538c740c3ccaa1c63a04ad7299131d02aab8ca618e81179cf65c87408bae7b2e43a045e73d9621d022eb9ecb10e81179ce65887408bae732c43a049d7399221d0317322a510e818b995428874093ae732243a05657194821d022fbb2a629c819354d6214e40caaa6b08a72068d435884390237bb2a4294819358d5214a40ccaa4b08a52068d63508429023bb8aca994811d1c5654ca408ece232a65204757119532902a6392a699481531cd524
  | 30 => 0x458c504870eb22c6282438b5922114121c9ac7108a090d6970884504862f39cc5aa043175ce62d5021a9ae7316a810c5e73181540862eb98c0aa0430fdd95415021c3aa8b18a810e3954580540870f322c62a0439358e6215021cb4c7300a810e5963980540871d322c02a0439698d6015021cb2c6b00a810e6a62580540873930ac02a0430f9d262d4c2187ae9316a610d2d7498b530861f3a0c0a98430f5d06054c218beeca98a610e1d6454c530872ca9ac029843875926314c21c5ac9310a610e3a64980530871cb24c0298438e9916014c21c72c8b00a610e5a635805308735312c0298439c9856014c218f4e032e8610c79701974308636bacc5a18431d5d661d0c218f4e032c8610c79701964308636bacc5218431d5d66190c218dce532a8610c7671995430863d380caa18431e5c06550c21a38e6aa28610d1c7454d4308637390ca218431e9c06510c218f2e03288610e1f6550c430870eb2a86218431b5d66210c219cae33108610e8d43588430870f324c729043875926394821c3cc8b1ca410e1d6458e520868eb98a9a10434e5c054d08218bce7b2c8410c5d73d9642086a6b98a9210435a5c054908218daeda9c8410c6f755864208673baac32104399dd561908218daeb3048410d2e72d51420861f3b0a8a1043475cc5450821a72e02a28410da671d5142086373b0a8a1043535cc5450821ad2e02a28410cae7615142086c6b98a8a10436a5c05450821a5cec2a28410e2e761514208787398a8a10434b5cc5450821e1ae62a28410d0d731514208697388a8a1043c99c45450821e54e02a28410d2d701514208794b80a8a10434a5c054508219cae3b1a8410c6e76d4d42086963a2a6a10434b1d74350821b4ce3a1a8410d2c7550d4208786a9a86a1043335cf615082199ae63028410ce571181420862f39eca21043175cf651082187eecaa08410e1e5458c420870eaa2c621043a358d4210821d4a853088410d1d7414f32086acb80a7990430f9d3658c82187ae9b2c6410c6d75d923208672b8ec9190431b5db548c821a5ae829c6410d697014e3208637baac31904339dd5618c821cceeab0c6410c6d7598232086a7396a699043179d8534c821a3ae829a6410d597014d3208672b8ec8990431bdd5644c8218dcedaa26410d4c7355132086e338ea6990431b9d8534c821a5ae829a6410d697014d32086673b0a699043635d0534c821b92e029a6410d4e7614d32087273b0a699043c39d0534c821a9ae829a6410f0d7414d3208686ba0a699043539c4534c821e8ce229a6410f4a7014d32086a6b80a699043d25c0534c821a92e029a6410d4c7590d32086e338c8699043531d5434c821e1aa8a1a6410cad74d853208656ba0c099043395c4604c82187ce9b286410c3d74d94320870eb24a61904317dd9530c821c3ac8a
  | 31 => 0xe32a8621c438b9516210e21c5aa8b108710e4e535884388726a9ac421c43a350d6210e21a3ae72a68510d4d739524288636bb6a7214434b9d35390a21a3ae72a28510e355418542886373b4a8a1443535ce5450a21b1ae72a28510d2e7695142887173b4a8a1443c39ce5450a21a5ae72a28510f0d739514288686b9ca8a14434b5c25450a21a5ce9a9a8510d2f75d0d4288786a9e86a14434bdd54350a21e1ea6a1a8510da47150d4288666b9ec2a14431b5d46050a2199ae63028510ce5711814288746b1a8421443475d253cca219cae3b246510c6d76d5232886a739ea9194434b5d2538ca21a3ae929a6510e555318532886a739ea8994431b9da534ca21a5ae929a6510d8d7494d32886a73b4a699443939da534ca21e1ce929a6510d4d7494d3288786ba4a699443435d2534ca21a9ae129a6510d4f7590d3288786aa4869944353dd5434ca21e1ea8a1a6510dc47150d3288656ba6c2994431b5d4604ca2195ae83026510ce5711813288746b226419443475ce549062199ae73148310d1d7395041887172a2c420c43475d2538c62195ae93146310d1d7494c318872729ac418c43335cf64c8621c5acb3264310e2d655932188656ba6c790c439359663c8621d1ac931e4310e4d6558f2188747322c790c43a359163c8621c6acb3264310e3565593218872ab2cc790c43a599263c8621caacab1e4310d2d74c8550886a6b9e42a84435a9c321542218f6eca80a110c6d7298f544870faa2c72a2439398d6295121c9ac6b14a890e5663586544862f39ec2aa243175cf61551218bce6302a890c5d73181544861fbb2a82a243475ce64151218dae5326a690e1d64d4e5348717322c529a438b5916294d21c6cc8b0ca690c3e74d85534861eba6c2a9a430f9d06054d2187ae8302a690c5f7654c534868eba4c629a431b5cb65d0d218eae3b2e8690c6d72d96434863ab8ecb21a431b5cb6550d218f6e0b2a8690c7870595434868f39ea8a1a43479d35350d218dcebb128690c6e75189434863b3aec2a1a431b5cb6510d21c3ccaa188690e1c6550c43486363aac421a43a350d6210d219c8e2b108690e3454587424871732a8421243a358d4210921ca8a6b0e6490e4e654c83248746b22641924387d5163d0521c38a8b1e8290e2f5458b41487162a2c5a0a43475ce5490521a5ae52a48290c5e73d95414862eb9ecaa0a430f9d85450521a3ae72a08290d2d72950414869ab8ca820a430fdd95410521c3ac9a9e6290e1d6414f3148727a9ac598a439314d62cc521a3ae929c6290d4d7294e314861f3a6ca98a430f5d3654c5218bcec29a6290d1d7494c31486a6b94a618a43555c6530c5218beeca986290e966498f214862f39cc9a8243175ce64d412187ce931ea090c3d7498f504863dbb2a028243879926314121c3ac9318a090e1e6
  | 32 => 0x39554e61d0f21c6ca8b0e8790e355498643c872b29cc321e439594d6190f21a38e6aa28790d1c7454d43c8716aa6c4a1e439354f6250f21c5aa83128790e4d5318943c868eb9ca821e43475d25310f21a3eeaa188790d1d7550c43c870fb2a8621e43875954310f21c5ca93108790e2d5498843c872729cc421e439354e6210f21c5ca8b108790e2d5458843c872729ac421e439354d6210f21d1a86b108790e355498642c872b29cc3216439594d6190b218baeb3188590e1e5498c42c870eaa4c62164317dd56310b21c3ca8b188590e1d5458c42c862ebb4a62164317dd95310b21d1ac6a108590f0e5350842c8786a9a84216438d9526110b21c6ca930c6590e555398632c871b2a2c3196430f5d6640cb2187eeab206590c3d7695032c861fbb2a81964387992530cb21c3ac92986590e1e6454c32c870eb22a619643a3591320cb21e1ca89906590f0d544c832c872b29cc219643175d663d0721c3ca931e8390e1d5498f41c862fbaac7a0e438795163d0721c3aa8b1e8390c5d7694f41c862fbb2a7a0e438b55262d0721c9ca73168390e4d5398b41c87172a2c5a0e438b55162d0721c9ca6b168390e4d5358b41c8716aa6c4a0e439354f6250721c5aa83128390e4d5318941c878b29a8220e430f5d664cc72187eeab266390c3d7695331c861fbb2a998e438799253cc721c3ac929e6390e1e6454f31c870eb22a798e438b95262cc721c5aa93166390e4d5398b31c87172a2c598e438b55162cc721c9ca6b166390e4d5358b31c8716aa6c498e439354f624c721c5aa83126390e4d5318931c878b2a26218e438795263d4321c3aa931ea190e1e5458f50c870eaa2c7a86438799253d4321c3ac929ea190e1e6454f50c870eb22a7a8643179cc64543218bae6322a190c3e7418d50c861eba0c6a86430f5da541432187eecaa0a190e1e5498c50c870eaa4c628643879516314321c3aa8b18a190c5d7694c50c870f324a6286438759253143218beeca98a190e1e6454c50c870eb22a6286431edd95014321c9ae531ea910e4e6358b548872ab1cc3aa4439958a61d5221a3ce7aa4a910e1f5458e548872731ac52a4439358d6295221a3ce7b22a910c5e73181548862eb98c0aa4430fdd95415221a3ae7320a910e1d739935388716b94c9a9c438b99162d4e21c6ac930ea710e6562987538868f3a6a729c43875935394e21c38e6b24a710e2e6458a5388716b22c529c43479d36354e2187ce8302a710c3d74181538862fbb2a629c43475d26314e21a3ce7aa68710d1d7494f438868eb9ca921c43479d35390e21a3ce7aa28710c3e76151438868f3a6a6a1c43179d85350e219cce5b0a8710c7a70194438863cb80ca21c43475ce5410e2187eecaa08710d1d7494c438862fbb2a621c4347dd54310e21a3aeaa188710e1e6550c438870
  | 33 => 0x831c5ac8a90a418e6952580520c74aa1cc3a10631e9c065508318f2e032a8418d2c72551420c70e32a86a10634b1d15250831e1a86a928418cd57198c420c717b2a84210638b5954210831d1ac6a108418cd571d93320c66bbaac39906395dd561cc8318baeb3066418cd571d91320c62fbaac899063179db544c831a98e4aa26418dc671d49320c6673b0a499063635d0524c831b92e02926418dc671909320c6a63aa8499063c3551424c83193ae9b0a6418c9d74181320c66ab88c0990638b592520c831c5ac8a906418e8d644c8320c762994c219063879914394431c3aa931c8218ccd7298e410c70e32a8620863335cb64cc431d1ac93166218e8e6458b310c746b22c598863175da538c431a3ae929c6218c757694e310c6caba4a718863715ca538c4318beeab226218c9d74d85310c66b3b68298863719cb414c431d2ac820a6218c9d74181310c666b90c098863659d2534c431b8ce529a6218cd67610d310c6e33908698863359d8324c431b2ce81926218c6e72191500c636b90c8a8063555c64354031c38c8a1aa018c3e74189500c61eba0c4a8063555c73254031c98c4992a018d1d74cc5500c6a6b9662a8063569c33154031ab0e098aa018c7b76540500c71cb22a0280639a5895014031c9ac7316a990e566358754c8733312c3aa643479cf5495321a3ae7aa4a990d3571d8e54c870eb18c72a6434b9c86395321a3ce6314a990d1d7318a54c869d380c52a6434e5c06295321a3ce7b0ca990d1d73d8654c868f398c12a643475cc6095321a5ce4304a990d357118254c868f39ec8aa643475cf64553218bce6302a990c5d7318154c869ab8cc6aa6434b1c96355321c3ac631aa990d2e7218d54c868f398c4aa643475cc6255321a3ce7b0aa990d1d73d8554c8697394c0aa6434ddc56055321a3ce6302a990d1d7318154c8697390c0aa6434d5c4605532187eecaa0a990e1d5498c54c870eaa2c62a643879926315321c3cc8b18a990e4e6398854c8726b1cc42a6438b59262d4f21c6cc8b0ea790e666258753c868f3a6a729e43475d35394f21aaae3b24a790e1d6419253c86a7390c929e43479d06294f21a3ae8314a790d5a7018a53c86acb80c529e43479d36194f21a3ae9b0ca790d1e7418253c868eba0c129e43539c86094f21aaae2304a790d1e74d8d53c868eba6c6a9e430f9d06054f2187ae8302a790c5e76d5153c862f3b0a8a9e43555c66454f21a98e4b22a790e1d6419153c86a7390c8a9e43479d06254f21a3ae8312a790d1e74d8553c868eba6c2a9e43539ca6054f21aaee2b02a790d1e7418153c868eba0c0a9e43539c86054f21aaae2302a790c3d7695053c861fbb2a829e4317dd95314f21c3cc8a98a790e1d6454c53c870f324c629e43875926314f21c5cc9310a790e2d6498853c871b2a4c3a1e4
  | 34 => 0x8518c3f76550428c70f2a2c621463875516310a31a5ae92908518e4d63948428c726b1aa4214634bdd54210a31a5aeaa108518e2e65508428c746b1a8421463355c764cca318baedaa66518d4e72d53328c68eba4a5994634b5d2528ca31a5ae92926518d4e72d51328c68eba4a499463635d2524ca31a9ced2926518e4e76949328c7873a4a499463535d2524ca31e1ae92926518d0d74949328c6a6b84a49946353dd6424ca31e1aa92126518d4f75509328c787aa28499463711c5424ca3193ae9b0a6518c5d75181328c64eba0c099463355c4604ca31d1ac89906518d2d72952418c666b94c720c6365dc54390631a5ae52a08318e1e5458c418c666b96c998c638759664cc631c3acab266318e4d6598b318c746b24c598c639359562cc631d1cc8b166318e8d6458b318c71ab2cc998c638d59564cc631ccacb3166318ea66498b318c732b2ac598c63475d33154231a9ae598aa118d5a70cc5508c63dbb2a0284638bd516295131c9ac7314a898e4d6358a544c733312c32a2631b9c860551318dae4302a898c3f76550544c696b94c82a2638d15161d0d31c3ccaa188698e8d43588434c716b26a5292631bdd95214931a5ce5aa28498c5e7518d424c6973a6a4a1263351c56310931c5ccaa108498e2c65508424c746b1a842126393995320c931d1ac89906498e1f5458f414c70e2a2c7a0a638bd5162d0531c58a8b168298d1d73952414c696b94a920a630f9d85450531a3ae72a08298d2d72950414c69ab8ca820a630fdd95410531d4cc93166298c6e72993504c636b94c9a82630f9d262d413187ae9316a098c7b76540504c717324c4282638b5926214131c5cc8b10a098e2d64588504c70eb2462282639358a3114131ab2e1188a098d4d7298f540c637390c0aa0631b5c8605503187eecaa0a818e2d54588540c71caa2c02a0638b9916215031c9cc6b10a818e6a62980540c734b14c02a0638e9916015031cb4c6b00a818e6a62580540c734b12c02a0639c9856015031c5cc9314a618e2d6498a530c717322c5298638b5916294c31a5ae42a68618d3970153430c6a6b90a921863565c05490c318beeab0c8618cd775586430c72bbaac321863175d66090c31a3ce7aa28618c3e76151430c696b90a8a18634e5c05450c31b2ce3aa28618c5e76151430c6a6b90a8a1863565c05450c3193cec2a28618d8d72151430c6ccb80a8a1863479d85450c31c3cec2a28618f0e72151430c68eb90a8a1863c35c85450c31a1ae42a28618d1e71151430c78b388a8a1863c69c05450c31a3ae02a28618f1970151430c68cb80a8a1863355c76250c3199ae5b0a8618ccd72181430c66ab88c0a18630fdd95410c31c5ca8b108618e2d54588430c746a1ac421863a550e6110c31c38c8a1aa418c3e74181520c61eba0c0a90631bdd95214
  | 35 => 0x90e52cc636bb08729663c350c4394b31a5ce9b0ca598d2d74d8652cc6973a0c1296634b5d06094b31a9ce6304a598d657118252cc61f3a0c0a96630f5d06054b318dcedaa2a598c6e7615152cc6b2b8cc8a9663531cd6454b31c5ac8322a598d4e7319152cc6373b086a9663c350c4354b31a5ce9b0aa598d2d74d8552cc6a739cc0a966359dc56054b31a5ce8302a598d2d7418152cc6a7398c0a9663595c46054b3187aed2a0a598c3f7655052cc637bb2a4296638b9915214b31c5ac8a90a598e365498742cc732a94c3a16638d95161d0b31c6aa930c8598e665298642cc733292c3216634b1c95450b31c3aa9b1a8598e1d5418d42cc6963a2a4a166393d8d5250b31c98c6a928598d2d7295042cc70f2a4c621663875526310b31c3ca8b188598e1d5458c42cc696ba4a4216639398e5210b31c9ac72908598e4e6354842cc726b1aa4216634bdd54210b31a5aeaa108598e2f6550842cc716b2a8421663a358d4210b31c6ca930e6598e655298732cc71b2a2c3996630f5d6640cb3187eeab206598c3d7695032cc61fbb2a8196638b992520cb31c5ac92906598e2e6454832cc716b22a419663a3591320cb31e1ca89906598f0d544c832cc733294c2196638755263d0731c3ca8b1e8398e1d5458f41cc636bacc5a0e638b95262d0731c5aa93168398c6f7558b41cc7172a2c5a0e638b55162d07318daed2968398e4e6394b41cc726b1ca5a0e631bdd952d0731c9cc6a968398e4d6354b41cc70eaa6c6a0e63875506350731c9ec6a928398e4c6354941cc7932928220e638b95262d4331c5aa9316a198e2e5458b50cc716aa2c5a86638b99252d4331c5ac9296a198e2e6454b50cc716b22a5a86631b9c864543318dae4322a198c3e7418950cc61eba0c4a86630f5da541433187eecaa0a198e2e5498850cc716aa4c4286638b9516214331c5aa8b10a198c6d7694850cc717324a4286638b59252143318deeca90a198e2e6454850cc716b22a4286631edd95014331c9ac7316a918e4d7398b548c72ab1cc3aa4639958a61d5231a5ce5aa4a918e2f5458a548c726b1cc52a4639358d6295231a5ce5b22a918c6e72181548c636b90c0aa4630fdd95415231a5ae5320a918d2d72953438c6a6b94a921c634b5ca5450e31c6aa830a8718c5e76951438c6a6b94a8a1c63635ca5450e31a3ced2a28718e1e76951438c787394a8a1c63475ca5450e31e1ae52a28718d0d72951438c68eb84a8a1c63335cb6150e318baea3028718ccd72181438c66ab88c0a1c63a350d6210e31a5ce9a94a518e2d64d4a528c716392c9294630f9d06054a3187ae8302a518c6f76548528c697396a9a146387d9543d0a31a5ae92968518f0d4354b428c696b94a9214634b9cb5450a3187cec2a28518e1f6550d428c66b39ec2a1463a550c6150a31a5ae52a
  | 36 => 0x31cc5a0a831b9ca63d41418dae531ea0a0c5e7398b505062eb9cc5a82831edd95014141c9cc7310a0a0e4d63988505072731ac4282839358d6214141c3ac7208a0a0e2d62904505069cb8482282839398e6295041c9ac7314a820e4e6358a5410726b1ac52a0831b9c86054c418dae4302a620c5f7654c5310726a9ac4298839654d6014c4196eeab0e8620e3775587431061ebacc1a1883659c75350c4193cec29a8620d8d7214d43106ccb80a6a18832d5c76250c4195ae5b0a8620cad72181431065ab88c0a18839394d6210c41c9aa6b108620e8d43588431074aa1cc2218838718d43548418bce6302a420c5d731815210637bb2a4290839358d5214841cd2a4b00a420cb775587421071bbaac3a10830f5d660d084196ae3b1a8420d2c7254d42106d338ea4a10832b9d85250841b1ae62928420da970149421064eb9ec2a1083275cc605084196ae23028420e4d639484210726b1aa421083a358d4210841d4a853088420e95439873210752a14c3190831e9c0654c8418f2e032a6420cb571991321061fbaac899083531c9534c841c38caa1a6420d4c735493210786a1aa4990838b195424c841e1aa6a126420cb5719903210727b2a641908393595320c841d1ac89906420e8d6398b411074731ac5a0883a358d62d044187aed2a48220c757695241106cab9ca920883695ca549044193ae63028220cad7218141106cb39ca8a0883699ca545044196cec21a8220da67210d411065b3b084a0883659cc42504418dce431aa020c6d7218d501069ab8e86a80838718d43540418bce6312a020c5d73189501069ab8e84a80838b1894254041a3ae7a0aa020d2d72d05501069d38682a80834e1c141540418f6eca80a020e59635405010734b12a0280839398d62d5331cacc6b0ea998e666258754cc697396a92a6634b5cb5495331a5ce431ca998d2d7218e54cc69d380c72a6634e5c06395331a6ae3b14a998d1e7318a54cc716b10c52a6634b9cb6195331a5ae5b0ca998d1e7318254cc697390c12a6634b5c86095331a6ae2304a998d2e72d9154cc696b96c8aa6631b9c860553318dae4302a998d2e7218d54cc696b90c6aa6634d5c66255331a38e6b12a998d1e7318954cc716b10c4aa6634b9cb6155331a5ae5b0aa998d1e7398154cc69bb8ac0aa663479cc6055331a5ce4302a998d2d7218154cc69ab88c0aa6630fdd95415331c5aa9310a998e2d5458854cc717324c42a6639398e6215331c5cc8b10a998e4e6358854cc71aaa4c321e631b5d66210f31c5ca93108798e2d5498843cc637baac421e638b9516210f31c5aa8b108798e8d4358843cc71b2a4c221e634b9d35294b31a5ae9a94a598d6571d9252cc716b20c929663539cc6494b31a5ce831ca598d2d7418e52cc6b5380c7296635a5c06394b31acce321ca598d6571
  | 37 => 0x1bdd95214b41c9cc6a90a5a0e4d6354852d072b29cc3a16839954a61d0b41caca6b0e85a0c5d7598c42d062fbaac621683175da5310b418beeca9885a0e4e6394842d0726b1ca4216839398d5210b41c9ac6a9085a0e8d6350842d078729a8421683c354d4210b41ccca530885a0e565398732d0732a94c3996839594d61ccb41caaa730c65a0e665298632d0733292c31968387d91534cb41c38c8a9a65a0d4c7254d32d0717b22a4996838b191524cb41a98e6a9265a0e1e6494c32d070eb24a619683535ca530cb41c3cc8a9865a0e1d6454c32d0717324a4196838b592520cb41a9ae729065a0e2e6454832d0716b22a41968353dd5320cb41a9aea99065a0e4f654c832d0726b2a6419683a3591320cb41c9ca7316a1a0e4d5398b50d072729ac5a86839354d62d4341c9cc7296a1a0e4d6394b50d072731aa5a86839358d52d43418dce431aa1a0c6d7218d50d062f398c4a8683175cc62543418baed298a1a0c5f7654c50d072729cc4286839354e6214341c9ca6b10a1a0e4d5358850d0636bb4a4286839398e5214341c9ac7290a1a0c6f7654850d072731aa4286839358d52143418f6eca80a1a0d4e72d4e5390727a9ac529c831b9c86054e418dae4302a720c5f7654c5390696b94a7a1c83535ca5390e41a9ae529a8720d2d7294d43906c6b94a6a1c83479da5350e41c3ced29a8720f0e7294d439068eb94a6a1c83c35ca5350e41a1ae529a8720d1d7094d4390656b96c2a1c830f5d46050e4195ae43028720cb5711814390746a1ac421c83539cf5294a41c9ac7a94a520c5e73181529062eb98c0a94831bdd95214a41a3ae72968520d4d7394a42906a6b9ca4a1483475ce5250a41b1ae72928520d2e7694942907173b4a4a1483c39ce5250a41a5ae72928520f0d739494290686b9ca4a14834b5c25250a4193ae7b0a8520c3d75181429064eb98c0a14832d5c46050a41d1ac6a108520e1f6550f32906a6b9ca599483c350d52cca41a9ae529c6520e2f6550a3290786a9a85194832d5c6644ca41c3ecaa1a6520e2f65509329065b3a6c299483a550c614ca41d4a8430a6520e1d6494c32906a6b94a61948387591530ca41c5ac92906520d4d739483290716b22a41948353dd5320ca41a9aea9906520e4e654c83290746b2264194838759663d0641c3acab1e8320e2d6598b4190746b1cc5a0c838b59562d0641d1cc6b168320e8d6358b419072ab2cc7a0c839559563d0641ccacb3168320ec66398b4190732b2ac5a0c83475cf4154241a5ae5a0aa120d3a70d05509063dbb2a02848393d4d6294d418beeca98a6a0e1e6550c4350746a1ac421a839358f52949418deeca90a4a0e2e655084250746b1a84212830f9d4644c941a9ce5a9a64a0d4e73d49325065a38ac81928393995320c941c98ca99064a0e8d644c83250763
  | 38 => 0x32e1aa9b0a641954d75985320cac73a4c299065635d2614c832e1aa930a641954f75585320cb86aa2c299065c3550614c832d8ac230a641970d54d81320caa6bacc099065c3552604c832a9eeab02641958f74581320cac63a2c099065c3551604c832b8ee2b0264195c471581320cac73a0c099065635d0604c832e1aa830264195c671181320cae2b88c09906533dd932d4432d1cc8996a21968d644cb510cb86aa265a8865c39513294432e1aa8994a21964f764ca510cb263b26528865935913294432e8ee2994a219744714ca510ca1fba2c1288650f1d16094432c9a64b04a21970d544c9510ca1f3a0c0a88650f5d0605443287aed2a0a21943f76550510ca67bb26428865a39913214432d1ac8990a21970e544c8510cb86aa264288651ddd95114432c74a9300a21963954980510cb64994c0288658e9516014432c72a8b00a2196c932580510cb38a8ac02886533dd932d4032d1cc8996a01968d644cb500cb872a265a8065c355132d4032e1aa8994a01943f74586500ca1e3a2c328065c39513254032e1aa8992a01964f764c9500cb263b264a806593d913254032e96e0992a019748704c9500ca1f3a0c2a80650f5d06154032c9a6430aa01943d76950500ca1fbb2a82806533dd93214032d1cc8990a01968d644c8500cb86aa264280658d9526114032c6aa9308a0196c532984500cb1b2a2c2280658d5516114032d8a64b08a01947b76540500cb38b0aa028065539cb5394f41a9ae5a9ca7a0d4e7219253d06a6b90c929e83569c06494f41ab2e0324a7a0d5571d8a53d068f3a0c529e83935886294f41a9ce5b0ca7a0d4d72d8653d068f3a0c129e83539c86094f41a9ae4304a7a0d557118253d0637390c0a9e831b5c86054f41aaae3312a7a0d1c7458953d068f3a0c4a9e83935886254f41a9ce5b0aa7a0d4d72d8553d068f3a4c0a9e8355dc56054f41a3ce8302a7a0d4e7218153d06a6b90c0a9e83555c46054f418beeca98a7a0e4d5398853d0726a9ac429e839554e61d0f418daeb31087a0e4e5398843d0726a9cc421e831bdd56210f41c9ca6b1087a0e4d5358843d0746a1ac421e839594e6110f41a9ce7a94a5a0d4d73d4a52d06a7398c929683535cc6494b41ad4e0324a5a0d697019252d06b2b8ec7296834b9d06394b41c9ac631ca5a0d6671d0e52d06b2b8e87296831b5d84394b41e1a8621ca5a0d4e73d8652d06a6b9ec3296834b9d06094b41a9ce6304a5a0d4d7318252d06b2b88c129683179cc6054b418bae6302a5a0c6e76d4d52d06373b0a6a9683595c66354b41a58e8b1aa5a0d2e7418d52d0726b18c6a96831b9d84354b41e1a8621aa5a0d4e73d8552d06a6b9ec2a96834b9d26054b41acee2b02a5a0d2e7418152d06a7398c0a9683535cc6054b41acae2302a5a0c5d7694c52d062fbb2a629683
  | 39 => 0x849964c6590d424cac6ba486a1265c31524350932a58eaa1a849962c6550d424caa63aa86a1265931954350932e18eaa1a849950c7550d424cb87b2a86a1265a31954350932e18caa1a849960c6550d424cac638a86a126563dc14350932d1a8630a849968d43d81424cb46b1a8421265399c764cc932d1ac921e649968f6450f324ca6b38ec919265a3592428c932d1ec8a14649963571993514cb1ab26a328a651ddd95114532e1a86a10a29943f74580514ca1e3a2c028a651d9c664d41328eae3326a09970d4350b504ca1f3a4c3a82650f5d261d41328f6eca80a09963664984504cb1ab24c2282658d9916114132c6ac8b08a09965773584504cb2a39ac22826599dc96114132cc8e4b08a09951e73d86540ca97396c32a0658d5846195032a3ce6304a81952e72182540ca9b388c12a0654d5c460950328ece2302a81947571181540ca9b38cc6aa0654d5c66355032a6ce3312a81953571989540ca8f39ec2aa0654b9cb6155032a3ce730aa81952e72985540cb1ab08c2aa065471cd6055032a58e4b02a81953771581540ca9a38ac0aa065479cc6055032a5ce4302a81953671181540ca9ab88c0aa0650fdd95415032c5aa9314861946f7558a430cb16aa2c52186587d954310c32c3acaa18861962d54988430cb172a2c4218658b5516210c32d1a86b10861961d5498e420ca2fbaac721065875516390832c3aa9318841961e5458c420cb0eaa2c6210658bd954210832c5acaa10841968d63508420ca2ebb4a7190651b5da538c8328bcedaa2641951d75951320cb0fb2ca89906587d95544c832e1ce4aa2641970c72551320cb0eaa6c499065535d7424c832e1aa9a12641970d54909320cb86aa28499065535d4424c832e1aa8212641946e76d51320ca96baca8990658bd96544c832c5ecaaa2641970e73551320cb8639aa8990658b553634c832e1aa9b1a641970d5494d320caa6bae8699065c3553434c832e1aa921a641970d5450d320caa6ba88699065c3550434c832c9aebb2a641964e76d95320caa6ba6ca99065539c7654c832a9ae1b2a641954d75991320cae338cc899065715c6644c832a9eeab22641968d64191320ca673b6a899065539db544c832c9cedaa2641954e71d51320caa6b86a899065535d6544c832b1aeb2a2641950d75951320cb47b2ca899065c3d96544c832a9cecaa2641954c76551320cb87ba2a899065c3d91544c832e18c8aa2641954c71551320caa7b82a899065c3dd5544c832d1ecaaa2641970f65551320cb87bb2a899065c39d9544c832e1aecaa2641970c76551320cb87b8aa899065c39c5544c832e1ae2aa2641970c71551320cb87b82a899065c39c1544c832e1ae0aa2641970c70551320ca673b0a899065539d4544c832b1ce82a2641970d54151320cac73a6c299065635d3614c8
  | 40 => 0x805110b54a12c0288859c545601444295eeca16a02168e6350b5010b46b1a85a8085c394d42d4042e1aa6a16a02170d5350a5010a2fb9ac328085171cd6194042e1ca6a12a02170d535095010b17bb284a80858b1d94254042c5ec6a12a02172b705095010b9438284a8085179cc61540428bae630aa02162d421855010a2ebb4a62808517dd9531404295eeca10a02168e635085010b46b1a8428085c354d4214042caca7308a021655539845010b52a14c2280859594d6114042caaa6b08a0216a5425845010a3dbb2a0280859c5855014042c9cc6b16a9996656298754ccb2b31ac3aa665951cd61d5332a6ce3aa4a99953671d9154cca3b388c0aa6651d5c4605533287eecaa0a99964e6358854cca9b38ea9a1e654d9c75450f3287cec2a2879958d72d5143ccacb38ea8a1e65179d85450f3293cec2a2879951e7615143ccb0f3b0a8a1e65c35c85450f32a3ce22a2879951d7015143cca1fbb2a821e658b9516210f32c5aa8b10879968d4358843ccb0eaa0c6a1665631c94350b32d1ac6a10859953674d4651ccb0f3228728e650f9d0605473287ae8302a3994777654451cca1fba2c3286650f1d16194332c38c8a1aa19947b7654050ccb26b1cc5aa4659558e61d5232cccc4b0ea91966472587548ca9b38ea92a4654d9c764552328ece2302a91947571181548ca1fbb2a82a4659358e6215232c5aa8312871968d43588438ca9b38ea9a14654d9c75450a3287cec2a2851958d73d51428cad338ea8a14651b9d85450a3295cec2a2851952e76151428cb173b0a8a1465c35cc5450a32a5ce22a2851952d70151428cb4631a86a14650fdd95410a32c3ca8b18851961d5458c428cb46b1a8421465559c754cca329cce3b26651953674d46518cb173228528c650f9d0605463287ae8302a31947776544518ca1fba2c3284650f1d16194232c58c8a12a11947b76540508cb1baa2c32a2659558e6195132ccac530ca89947671181544ca3ab88c0aa2650fdd95415132a6ae3320a89964d63588544cb162a2c5a1a65559c65490d32b8ce3b14869954e7518a434ca67394c321a65331c96090d32a3cebb22869951e74951434caab38ca8a1a65179d85450d32a3cec2a2869961e76151434cb86b90a8a1a65479c45450d32a3ae02a286994ce75189434cb273a8c4a1a65339c46250d3299ae0312869961c5458f424ca8e3aa87a1265631c943d0932acce32a484995c671d8e424caa73a8c721265531d54390932e18a8a1c84994ce73986424ca6639ac121265471d54350932c38caa1a849958c7250d424ca973aec8a12654b9d25450932acce32a2849946e76151424ca973b0a8a12658b9d85450932e1ae62a2849952e71151424ca96b80a8a1265339d46350932c9cea31a84994ce7118d424ca66b80c6a12658b1974350932d18c7a1a
  | 41 => 0x92c1a1a85479d76350d42a3cec29a86a161e7614d4350b86b90a6a1a85479c45350d42a3ae029a86a14ae751894350b173a8c4a1a852b9c46250d4295ae031286a168d63d0f4250b2ab1ea328a851ddd951145428bee6b00a2a145c735805150a3b38cc7a82851d5c663d41428bce730ea0a145d739875050a3dbb2a0282859598e6114142caac7308a0a1656635845050b2ab1ac2282858ddd16114142c68e8b08a0a1667725845050b32392c228285479d36194c42a9ce5b0ca621655611865310a8f3a0c129885539c86094c42aace2304a621555711825310a3b388c0a98851d5c46054c42aace3322a621555719915310aab38cc4a9885555c66254c42a3ce9b0aa62154e72d855310a8f3a4c2a9885539ca6154c42caac230aa62151c745815310aa6392c0a988555dc56054c42aa8e2b02a62151e741815310aa7390c0a9885559c46054c42aaae2302a62145f7654c5310b26a9ac5a18859354e6210c42c9ca6b10862168d435884310a1ebb4a9210851b5da5490842c3ecb29a842161f6554d4210b87392a6a1085c31c95350842c9ecb29a842164f6554d4210b872a2a6a1085c39d15350842e1ec8a9a842170d53d0d4210a96bac86a1085c354e4350842e1aa621a842162d75d954210b173b6caa10854b5cf6550842a5ce3b2a842152d70d954210a96bacc6a1085699c66350842b4ae331a842152f7558d4210b46b18c6a10852b9db5350842b1aeb29a842168f6594d4210b87b2ca6a10854b9d95350842a58eca9a842170f6354d4210b8631aa6a10854b1c55350842a5ee0a9a842170f7554d4210b47b2aa6a1085c3d955350842e1eeca9a842170e7654d4210b86bb2a6a1085c31d95350842e1ee2a9a842170e7154d4210b86b8aa6a1085c31c55350842e1ee0a9a842170e7054d4210b86b82a6a1085c31c1535084295cec29a842158e7314d4210b86a98a6a1085639cf6150842b1ae7b0a842170d53d854210a96bacc2a1085639ce6150842b1ae730a842170d539854210a97baac2a1085c354d6150842e1aa630a84216a5611854210b86a9ec0a10854b5d66050842e1aa7302842152f755814210ac7b9ac0a1085631cd6050842e1aa6b0284215a7715814210ad238ac0a1085639cc6050842b1ae6302842170d531814210ad3388c0a1085695c4605084295eeca16a22168e6350b5110b46b1a85a8885c354d42d4442e1ca6a14a22170d5350a5110b17bb285288858b1d94294442c5ac6a14a2217277150a5110b9238a852888517dcd60944428b8e6b04a22162d425825110b86a9a84a8885179cc60544428bae6302a22145d7694c5110a2fbb2a6288852bdd94214442d1cc6a10a22168d635085110b8729a8428885c354d42144428eeeca88a22165a539805110b2ca9cc028885aa50a6014442cb4a6b00a221659535
  | 42 => 0x3dd54394843e1eeaa1ca421d2e74d865210ea739ec329087995846194843a5ce8304a421d4e731825210eb3388c129087595c46094843c3eeca1aa421e1c7650d5210f87b9286a9087c31c94354843c3a8630aa421e1d43d815210e3b388c0a90871d5c46054843a5eeaa1aa421d4f7550d5210ec7baa86a9087c3dd54354843e1ecaa1aa421d66719915210eb2b8cc8a9087599c66354843acae331aa421f0f7350d5210f8731a86a9087c3dd14354843e1cc8a1aa421f0f7650d5210f873b286a9087c35d94354843e18eca1aa421f0f7150d5210f8738a86a9087c35c54354843e18e2a1aa421f0f7050d5210f8738286a9087c35c14354843e18e0a1aa421f0d4310d5210e973a6c2a9087539cf6154843e1a87b0aa421d2e749855210ea739cc2a9087c350e6154843e1a86b0aa421f0d431855210f32b08c2a9087c350f6054843e1a87302a421d2c745815210ea639ac0a9087c350d6054843acee2b02a421d64715815210e973a0c0a9087539cc6054843e1a86302a421d66711815210eb2b88c0a908727dd94314843d1a87310a421c6f765485210f86a1aa42908727dd943d4443d1a87316a221e8d4358b5110f86a1aa5a8887c350e5294443e1a86a94a221e1f7650e5110f0e3b28728887c5dc54394443e28e2a1ca221e1d4358a5110f0ea1ac1288871bdc960944438d8e4b04a221f0d435495110e37390c0a88871b5c8605444393eeca18a221e8d439885110f46a1ac4288871b5da5214443e1a87290a221c6f765485110f86a1aa4288871ddd95114443d3287300a221e6a529805110f34a94c028887a650d6014443cd4a4b00a221e69525805110f38a8ac02888727dd943d4043d1a87316a021e8d4358b5010f86a1ca5a8087c350d52d4043e1a86a94a021c6f725865010e36392c328087c350e5254043e1a86a92a021e1f7650d5010f0e3b286a8087c6dc14354043e30e0a1aa021e1d43d895010f0ea18c2a80871b9c861540438dae430aa021c9f7650c5010f46a1cc428087a350d62140438daed290a021c6f765485010f86a1aa428087a550e6114043ccca5308a021e65529845010f4aa1ac228087999496114043ccaa4b08a021c7b765405010f38b0aa028087559c75394f428ece2302a7a14757118153d0a2fbb2a629e85635cb5350f42b2ce3a9a87a149e7614d43d0b26a9ac421e85a350d6210f42aace7a8ca3a161e6350e51d0a2f398c0a8e85175cc60547428eeeca88a3a145f7358650d0a2e39ac3286858718d43543428f6eca80a1a155671d4e5390a3b388c0a9c851d5c46054e428beeca98a72168d435884390aab39ea328c85179cc60546428bae6302a321477765445190a2fb9ac328485171cd61942428f6eca80a121657535865350a2fbb2a629a85699c762d0d42a5cea31686a14ae729874350a563
  | 43 => 0x6000c0010004001000c002000c00000280020048003001000d001000900000010014001007c00300540370000000000000100600050000005009400b000000b000800a000000e000000400240000018000000000600040010004005000800200400140000007007c005007800000000040014001000000a00040040000003008c000000000300000170018001003800b001c009002800a00280010004000000000000040000000003001c00000000010004000000c00100000010004000000000b00000050008002000800900100050030000000c0120000002000c008001c00c000c0000000000001c004002c000000400a0004006002400200000020000000001800000200030014001000000a002800a000401000040030004000009c0020008000009c0000004004002000600cc001000000800c80010028001000000c0014001002000200180040008001000c00e000000e00840000078000001400c000400500000190000001001400300000020010002000000000200070030000000400700100080008006000000000000000000000000c0050010000000800300040000000006000000a002800000080060000004001001800000000008001000000000000280000000001c00900200000000000004c00000b800b003c001000c000000c00f00000070028000001c013000800200080040000001007c000000000000000110000000000800200000010004002000000f0000027003000400400010050000000000800180000018000001000400000060038000002c0010000001000eb338ea5296871d9c46054b438eae2302a5a1c6f7654852d0eb3396a328e871b9c860547438dae4302a3a1c777654451d0e37b92c3286871b1c961943438f6eca80a1a1d6671d4a5290e3b388c0a94871d5c46054a438deeca90a521d6672d465190e37390c0a8c871b5c860546438eeeca88a321c6f725865090e36392c3284871edd95014243ccea4b0ca4a1c6f765485250f32b16a328a871ddd951145438dee4b00a2a1c6c725805150e3b38cc5a82871d5c662d41438dce530ea0a1c6d729875050e3dbb2a0282879998a6114143ccac5308a0a1e66625845050f32b12c2282878ddd16114143c68e8b08a0a1e57735845050f2a39ac2282870f5da5490c438baed2a48621e1d75d954310f0f3b6caa1887475cb6550c43a3ce3b2a8621d1d70d954310e8ebacc4a1887659c66250c43b2ae33128621d1f755894310f46b10c4a1887639cb6150c43b1ae5b0a8621d1d759854310ec7394c2a1887635ca6150c43a3eeab0a8621e95611854310e8ebacc0a188747dd56050c43b1ee4b028621d8c725814310ecbb8ac0a1887651c56050c43b1ce43028621d8d721814310ecb388c0a1887655c46050c4393eeca1ea421d2f7550e5210ea7baa87290876
  | 44 => 0x40200014000000000900440000010000003c002000800300080000004004000001d0008003001400a00040030038004001c001001000a007000d00080020014007000800600000020008002000400100a4010001800e00540040014000001c000002c000000400700840010018022000801700180000004007003400e00040080000003000c00100000000000001000400100080010000004007400c000c000001400100600010008009001800a0000009003c002001001a000c001003c002000400a00080070024008000000000000010000001003c000000c00d0014002001401900380000010002000000300100070004003000c000001c0000044055000000900000010000005000401d001c002000001c0004000001400000a80020008020000001e0000006000800100680000008000001000c0008012005c01a00180100018008005c000001c0010050000002c00000000090010000000400300000000008000000c001000c000000801c00040070000009000001a002000000000060004000000c001001c00b00000020018007002c00000a40050050000001c000002000f00480030000003001400200100050048005000c00a000000c000001d00000010024023002c0030000004001000100100040000002006000800000000000000000000000040000004000000400d002000c00280010004006002800000040000044004000800100540070000001000c005000401a000000700100040004005000c00000040070014000004c001004000000740050000001000c01600bc00300000020008011000c006000c0000004000007000c002c0000004003002400000280000094000000400900040000000008003c0040000001004400000040010000004000400400180040000001003c00000000000004004007c00000000020054005000000a00180000038000003400100380120008011004c00900000030008012009c000002000200140130004009001000100080010018020002c0040018000002000100000010010004001800300200060008002000003c00080120000011000400e00240150008007000c000001000000780020000002004000c0000004002000000100040000002002800000000020000001000000b0008006001400c0000009000c004000c00300140010054000001800000ac0030008000002c0040004001005400800080000020001002800400240010070000001001f0020001000c005000c00700080000028007014000c001802c00180000004000001c001003c002000002300380100000004000000d0004000000c0000008003001400300000000004000000c007005c013001800100300010010014000c003001000b0000001000000b0000010002c000000400100200010000000000800e001c00a000800
  | 45 => 0x6001000200500010000000007000d0030004000401a0004000000c011000000100000010024004000c006000c0070034001001c001001000000140020004013000c00200400010000003000c0060048009003c0010084001000800b000400000040000000001000c002002000500040000008002009400100580000000014000c00f0000002001400100240140040000001000100000000030002000800600000020004000000000600000010008000001001e000c0030000003000400d0018000005c0050034001000400e00140090018021000c000005c003001400e001401900240010000017000400000000010008002000000000280000000007003c0040000023008c00900a800000000020004001000000700040000038000002c00000040000014000004c00500200120024002000800000100060010002005400100500000008001000400000040370070002000000000000030000001005000200000000050018001c023000800400000000000003002000000040010008001000c009005c001004c001001400100000000008004001400200000330000018003000100000190000008001400100080000018001000c006000004d001400700000010004003002c0080004000000000100000110030002000400500000000084000005800100d40080010001002000b003000300140000008021000c00e00040000010002000800d001c0040010001000000600000040014010000000c001400000040000000005000400200000080028000000000000000020000001000800f0024001000c0000000008001401e000c0010018016000000100080010000009000000200040060010000002c00e0004000001000000000010004001000c003001c0000000003000800b005800400000030024002000c00100100160030000002000900040030028001001c00100040010010003001800200040040028002003401e0000000000000500140000120006001c00f0000000000000300000230008000002402d001c001002401b00140040024008000c001000000b0144012004000000080030054004000400a008800300040000008002001800400000020000002000800400080000068002004800c000c00000140010004002001800100480060000008002c00100000000000004000000500180170008001001800e0008003000400b0018010001c007000000c000400100040110094001004c009002000000000270008016000000b001c00400040000038006000400e000000a00000010018001000c00100040020014021000002b001400900000180000001000400b000800a004c000001400a0140003000c00200400030074003000400000080010004001002c05500040020004001000000100100000004008000c0010038005009000200
  | 46 => 0x2001c00a0004000002c0020018008001c001002800a00000050010001000401f00040210004000000000200040010018008000800a0010005000000a000400600000050000014000400300440040048009000000800300160008015000000a0024000001c001001000500000010000008002800700040000050008000000000000050000000003000c00040020000006000000400080100000003001c004000c000001000200080040004000000000600280080060004002400100200010014000001c0000014000004c001000000000040050008000001c007001000a000000000c800b0098000002c00000000000000006000c004000000a000c002001c000000400000040090024007001c0010050003000402100480400058000005c0000010002009400200a0000000400600000020004001000c01100000090004000005000700000020010001000000b000c0030000000001800000000000000002001400000040040000000000801b0054001008c0100004005000401900000010008002000001f0000004001000a00000000000001000c003000000f00100030060009001800e0000002000000300000000008003000c0000050006000c01b00140020000000000c010001c00000000200000000004c0050004001005c01500580020014000000000f00000010088001000000300000080000006000000000900040004000001c00b000800c0000002000000b000000200140070018011000400d000001100080130008002000000000080040008002000c003001000a000c00000200020010000002802300040000040000001000100000230004001008000000380070008000003800000000070018000000000300000000004011002c0020060007001c000000000100280030004004000801200100000028000000c00f00000000004004000c00a00240190004001001001200480000008000000c00200680030050000000000a00040020028003000000a0000004001000b000000b0034000003c000003001000240050004014000000000140000078035000000100580020010013002c00000040020008007002001f0024003000000000100010000000006c00700840020004003001c001000400b0098001001000000300100020003000402f0028000000c007001c007000000b0000001000800000300110000001000000c006000a00000130000011003400300000060004001001400300040000000003002800000600030000009004404b000400e0000006000c00a00440020040001004400000200050090001000c00e0004004001c00400480040008005000000b000000100000090028002001400300000010000007002c0000054000000c02b0014001000c00100140050004015003000a000c00400040000004004000c0
  | 47 => 0x33b80000001e286eaabf6000000000036ea00019ce225a7980001dcc3a5800017b26aac5db89800022c244b0cd0a3923aa3393214346186600000000f00000d690000b308fd4824ace4a7caa4ca68a9487c5b678b4c12c27f5ac804acb3d22f6a4780a513e62ae065e5ee88e6000000089a375e00c00003bfa0de1b02c720002f2c0002a764949f548412c1e0a986266eb37dc000000000000005ab2e28071af6e792a5a4dc2a3a292aaf4ac30b0b036fa66267f88a80003146ccf04a8d2d1cee5c1845635505fe0002a7e5819a0ac1202443e50e843f581f828883640000000000009c0000ffac769b16df40b909cbb4264db80004a30000dbb8000c82208ebe0800049900009ec229200035c800000007b9979c23f80000002650756000075503b46b88f2600018bcc9f1da8be780000000234000000018d0c6ede32f0a830a48a7150000d1080000002efc03b22a4aa32136ad2800088c21d86708d42ae50b24acb95aca469834c70986ae1f948447584ba5bc922476297b87762816601812c0000baaa7610b25ec099cb0eb6a4a69800079aaa1e0001ace0000498159b0a6209a8da9e0afe0bd6a986ce88000002c0000004015000000100280000000001000402900040000000000001400200100020010001002c0000000000001000900000060008008003c005005c005001400000200000000004000000200040010004000000800a001c00100140020018006001000e00000040040000007800a002800c0000001000000400000010000000001000200000020010006000000b0000005001800200000050028003001c003001800e0008001000c000000001e00040020020000004c008000c01100000270028002000401a00000000000001005800500100010004001000c00400040030000001000c00100000000004011000c00000080080004002000000000400010010000000c000002400000080050004001000000200080060018000006800b004800500040000000002000000600040080008002000800800a800b000401b0008008000c0000000005004c00300040050000000000401f0020000000c00a0004000000000000000000000000001c0000054000000c004000000e002c00200140080008003000000400080090004016004800200000030000000009000600500000008008002c000000000100000150004009001c0020004001000000200040000028010000800a000c0020060001000000000200020000012004c00000000030004000000000900280020044005000800700580020000001000801600040020004029000000d003400c000800100340000004000000400b00080010010005000800b000400e00100000024000013000500080000000005005000900080010000000001800000240030
  | 48 => 0x20902130000add800000025728592bc4539000079897ea0003338c209f1e5900000b13013022d287e7e608160000000d2412fc1b715b00358756a13aa42b22b7d8e150000c84a946af580000000f4a47e86324cc00000712fe2512b170aa08d74485838a50984f604a961ce1f05382200dce87c1a523efa86671a0d381a4a332671a66a000010498123ee1f1994655c2b7c9f1993a96d97ae8c20a760000f32babb39280601f02c8862445ea5f453505741218ac86d9000019080001e7000014921760001d8c0002f966d00000bfe00004d080000000000769a576d0f36f870e15bed7f120089834ce6efa3ce8a2385865081fa6bd27e2a0480003f025d83d9ab0c000000083d33e273f80000000bea4fe000065430460741c6629d0a7e659b2fc82688ac9ff800024180000001a22287ad7200000005e58f50be600006ba0f860001b8c3f11bc40000000c1611f2a4ca0ba0002d58235ac5cc5d2b5ebf7a47c283101c49f808872b000052d16d800000006fa806c000168e616064e62880000001e7038e20a69f72a345881e14311a9c439a094244288eaa232dc61342a26135aa4680814a80001cd6b2d91f002e0000000268e640b10c048963600033ee000000040a272a000261a6ffa6fe0000fc8000093802298e0c59abdc3da01de0688d5214980003f800007a1800000012541ffa0ce3d480007f01da20b8a8cca901f6634213687db2c9800e377000000000001a7e024a44830f0a84b3ea35c924923c0000a724c880acab6284472e885630b800000006902f2236c7fda0948b8b7620d49794000158cbf4b0be7c70efc7b800001422e3a0000000000000076e000001aa2fe00000006cb0000000000029b00009ad80000000dc400014be119308a0002a4a14b032254f08f86bb9fe060ab3badef80e4aa92384af3050c00011ecca780001699c2e000234400037aa000000097c8e0a00000001f4131acf380003b1000040380002a52c203c880002e99772000000000037168a7334c0000134181a124d4124145b480009c480000b2b79c9ea9a1c70793fa95294008780324d60b7ba4c7ae1e5fbaf8e4cd05ae156a336c020ec290d14ac837100408b061e658a8c0daa14ce9dc02d2c66a130a270d281be86a6d391dde92d9d721f3a7343cd1a060c62c0c5462506dc9988c17e1b206c72316a002412000183e80381b611c9b46b90a4ec6b6b6041250d2e586b33617186642631e3a5caa9360f301d427a0000501254246eacca000000000018207c08000b979c58d7eb5d46a2a222343b81435784b6000021869e075e0fa800036ab2400a300003f387200658000bb416a6a6db6b200034924c185b8552325c0000436c0bae705b7800036629ae9a994a00000864bd80dd0733850e00022bc5ed8000722a840dc700008008000886af22d760
  | 49 => 0x9bf2aab0a465840000ce604fe7f897c0806823c43daa3847a1574710b0203d0b04a1d899da1ac8602c138000da5b44e6548556b5e84405fb35084bca9904430000000000000021b0b9e05a05932952d779dc4348326096b9c4c8261352213800000011e623900005b080000001f10b0a21e28d3b3ec000000000022120000000172800042600000002ae66d21a4a0000478df20000000042e49a0c9c2350274926ad5c00000000003218000000047e1df20001b4a0002de690e80004e000009fd04d260b0000146b7da0ae0000ccb0148ba18e78c0e00000000f6296100006680000000273650b2c64106000023095a8c94aa56a50000092934b08cd0000b8f1f9c8aaae5024715e45d98fc2ae4260800025d20001122907315e5cc04b23fe3236cad9440743b7d2914b158cbc0ece0001f9248a0000962ac022eb17f2543ae74000079a4bc1c9e0000000000212aae7246e059800027400004211c3e2efb8046d51d6200000008a02028bbb00000000000000000000023c82548c2c0651188b8f8000551adb20e311949bc28e60000000cdd800000006ea51b37eeaa595ea240af9a399a7deb6d3394420a0ae7eb80005dc2a1c81d97e20002d1e80fb760000000023d800000000000000000210027c63d33c8255832a29207de00000d22e725c46c30000e1e081219b80009b000000000000092800000000000000000c830000000000072882f05030a4c3df336a63f27307e18000000193cc8f8000289a156000000ca81076a13b93b40002c7e00027b87a10cc22852cb40001032ce6ad160002a480000f080000e18420314e9312fb2212814e0000c345d2156a77db2720000fb000008ee983207acb2800069888dc83300005f800000002b880bd86f82e3aae275ea51cbd50d9e3ad11b0dcb000000038ae199a6ba4b28000ca88d1096380006e2b6164ea0000d2780009b0800000026460000e72014a29800021c063cb8b23762f10d93a11a4b712322c414c841798a83c90f0ad0b8cf892e09de2dca9e685f018a32a86101a08000000362459c291e0002c404b7800047d00000001adeb1e8000000000000000000ce262c8400eb616405824e59b6cd1da9348921fdad118e7e80d800057a1f9a000123e00010920000bd6892800046b1680cafac683dd094eae5b73c26a9a30a9a8000ad0a36e00000003aaa4d69ca2cc60000894e2b041655ca1a6d789362359a2f22050772cc387940000cea5b6945400014faa490d560c5ac62cb380009d080000768190c9a8220000000000033561148000aaf0000603000095e1b7803a8000bea80009e598ee5ce83a40003440b4d80000001ad61fb266ecc094b272c2fd0000000092200001711f24b02050ac9d80006ec80000620000417190c00008841108000b81b666381b15c00021ea00030b4d962460
  | 50 => 0x8e200e6594a6280000000b349dce62b8202c18091eb90367e1c38f14a7a21a4000082241d873c3bd374ca9900000c51044c8ea43cddfac54be880008aeb8b65fe20f259e0f9a00000005f9847c006a34697293d6d8f0adac8d246a62423ac6c5107ccd224c02fb9fb414780005980b06148af7657d24b0e11967e5198e6a504830ac4ab7087341ea49282d4800b800081710a6a0e1ac2b492b489d1269c35d986836cb4e6b38917ccab9f748f7aa02bf61d3c097b3d027d80004520ef66372f88a840012cba85aa552870a245090a00019b6bc3800000011280000900381000091780007f6246648410f85f60ea0934000087d28b2882a32aa7f1b74d20352222ab7b04b9040a0002ef835900006bd881081900003399de62f0800080489f4232000000000000000afc00000000000000adb8ad6313000000025ee00025bc69a80008dc0f929ab000000033e400000003b400003a780001b41198085256c00022f0cb10a7a4918732000207c00003e4b26b7b6943892e108072cd651f42018008e9dd9e10206ada40001dc2a0fb2a461d011c5c10000b420718524810a4190448d4da81c386800000003700002e941b2803a19a8c384fb2a08a81971e32d0730d512c7c6ca2270081180a542800081984e0dd3832cbbd800000034b6902a33ec330000c2394a2afd0d6c489b50661da6f400000003dc0000ad30000000321ad899db40000000d7400000000000000000010130ae5e790ac00001a01228964000000038000009d4a596dd4aada369000016d80009698000000000000004745fd32b81b61bd83419e522b4b15adae8000222091287c87d20000572000000030390fc0002b0212d343ad6c3228cff324e2ff24c2cd81d842009e1a3081d5e0fb99fc15216421f28c5c7fa800043c320015e8000b148000000087247425002a232b04228fca12b263037c1af23e336604152a70b6a998445995fe00000009008b70000124a00036180002b0a00016aa0000da86f03130d4b29c800018d2d42b80c0002004a3e8afe4b600004338000a0aa0d8000216a000000034f0ccc72680006180454b6217c2d958000a56800018320105d10a620001f2c3c780007391fa661fad520002b4e7c48000686305ea838000572a23a8c9800084419a2a118000537ad562a628203e90000a3800008ed00005f1800010e94d6d1725e69d980bac758000000317cbaa21fca31245a6e794a6667a7385da9aa200025cc3a9819e4cf0000b6f2c180001d7007930649dcb6024079cc218d8246b1d92ec49ab4de2460e48c52a0e80433532545a8d8000011251a072e9d7b76883f123067b2ba634305f4949036e8bd8000bf6a178389023800019564d72312dc9239cce105e882716a40feb4b200000008a1955800033e6015163c20b31a07fc0f185d5b8502b1
  | 51 => 0x1f32aec80004f4800046400000003434adca22a83986984f180002b40000621b22e30c00002e59a36272b1060000000c402dea986259a4d6800000000000002d2c5720432c27820a15aa4e80000000af0000000000000000e1cad18000e0729ea000184ea5780005cc8b9a5a3175c06706bc4f88000000166a0000000314ac9c219b87a0cc318c72a99720000ec8000378a457800047480008671e487fb13360438df4000034424c386a0000b86bba35c2405a8ae000158a1bf9e06000278c0002cdeb2f22720002432bb58e804d4000000000000000000a308000a1f085a21500003de80005a2866ce25ab56df815dee13859ed661994c261922003ad6ed0691542188ae829484149da28f012f8ad408ea05ea319cda9e69f56ba48ca8606b646c380156b5d354035fa47e6af970e2ad37207d436864381d9a827a6be1b08326a65855c00010c47a31dc88f814fe3338000d9a8b5679f8000988a50c9910000a1cb09c6100bde5079fc48b81d60de485e400137e80daabac09c0000aa72218b3b827aabd00009b100000000000a1580000001e0a000000000015d80de8074dfc08006b180000001944dc5311200000000002dae00029fe0000bb02da9fde000000058c9940bb3331000000003a18000961800000025a82a184cc611383092f9a207c29a3cb048e767e289a00000a4471fb4b8b94881ec442cb8d18a4dc86082ae58f800032b80006319ccaa970000ce72ae05ed2c9e98d352e0000000000000000000006ad00001bbb6b0a45000081b9f280002d80a2a10de0000000aef121800038482c29e4cac400907d7b7ec93200009b2a3bc000290247600001f8956c37800004ce28ba1a791cc0f587a0de82fce9fd8000000000000000000000000c1bb5a05bf93b2097115ad7f8c9a90000000001cf6606270e37928a2c479bf499008ba6469e22600a3da1dbb31a15827be15c000066492707469658bca0d2cc6380dabc9235a000377a00019e4b7c800074c043800013ee4a6aa1a0000e2c000069a6ed00000000c18aae8000000117080e26b08748000d482c6ec268000793998a00015080001e40c6c271e6570eea2ac040c41590dabba83be9998b3ed58a4d4b14308cc718cf651d201e1c119bce179c7a37a928a33face6c1689049019aae02aa9bc00025aabeb01064679dbca9808c6000196e49799ac4aa8000bed000003b816cbe8360000007608911e7adc6b79632f2518dd61c00bc80000000000013caabe0000000000274ad343250e1c9752223166483bb556000118e0002232d6eb190c089a0e00016fcbdf0000822a2dca7e9e664ba80004a9800000000000000000a37087a7f5000000000009e1b59e7b7a3a6a052898560b4bc00021842d69b5cc77000005b9ef66b98000158925c51c8830c2818b2e1a000000000000cd000
  | 52 => 0x3800000000002bc600010482c380007751ece0000000dd989a68ee8fecb7d8000840aab855e03d8000056899b215a00000004c4281a8450ee4ddb853a26f000000008741e79b0693ca6d0bc1ad5ea178000b4511de1e0067c83282ec327ab66a8285de50414f2d3130ac000114c694259450aacd098f8f7848d0d36de39c9258b8742b089ba421f9612bf2827264b8d482eb81ca7afb6be83fa246d3ba88e59b1b7039638346971aba0002a3cc390af0a45b2d0b778bd81d410e86df8444237800086330ce9eb940a987a7c046dae08b0019e00000000b411738d6000000b80c8a726325ea4b86503f982a400000000002eca84c8ee8000000081f936c00003b0b05800000000001e98bc600000001b39aa4b2e8000875833a000159a459351ad8c237ae1803b296321c4796174e34c80000001ba800027f0761a55c0002aa8a2e05a4dae342a00008a2dcdaa900000d5a234839cd71800000000000001a3200000000001b6e7e82f181bb000000000000000000140800000036069398000b70380e00000000000000000135e2561e32743000000034c20000ca6000000023c07e00000bc05180000b109c946e2034ac8e1e2cc8ab36e000330a000148a307b80000000000001a4625180001ad096600004da000177e6990fe4848a4de00025664409b8210480001db00000bf0a9ab5d97d600027c286e319871f00a2b4b862c7f991780362bec0001c4e000388618b800085b0000b03a558000000000038229ed8af6c58800000000f8a0c2f1c469003e2d90acc4aa00007480d1ad1780000000fda00034f03a21ecc00002120d816b013081e8000093ec96a9c0b4180008b530f0000200c017af528d4b5beba129be0170000cd8ae609982ec472d17824b992605c40118a168d8ab9ca6748f59010c7e9cb86388320862afa495880b0c96135403c88440000a5c000142277b01442730000000000073482c00df32485de848800030bc000113c6e8b4242f9024c7531e5c18e2aee427980453a07d689300009590000c00af6895a1928b138000ad6800024b1dc664d855860430746d9a408371aab6d85225676c896c3fc28b4292a2b2abe87b800008580002f3ed628000c100000275250447196281e88000a622a28000381203db668049b2cc0001c124838f20de00d4c28b159c9de0000a9b1d0400000004a815028ba873672400000000000bcb900a3c71a8c2aa8000bcd9e5680c800000000004583842cf082d6aa12150afa1cde0fd9a7699202cc5108520b72103e0001c7860c0000c931fe8000322c0543710a7d32622b63050e0b00000000700d3691aa1758ef80000000335160a69c972e00010c23048000a219d48cfc04a27f90000c0f2570b8c000032e89480af8000000092200028748e28dbc3808000e1329988a51a109d429eca741eca00
  | 53 => 0xa78c65906a7c80a426c90014d9b80000002320b9a267e752832ec40a14a12321ee1f12992d28abfc460a73a59db14c6bf9b42c24312000000000000000cf78c60dff0000b8b2f082c7173400019889fe00000000000000000001e9a6c50e1ce83d52bba4c300000002f70ab2902a0e01c809f100007502e144220000c15a162000068a21700fe00035ae77d38b052b928eaed3328378b4006730000d1d1f903452f947aa205622813ae912997e413b3266292fc837b09ae99f0000c9080000002d023ca851c00013da9b1a11e00010d620e000000000000fb02b69e8a55494226c84c000004508000c1319d09e4a55a835b79a897188a3eaad8200034dcbe033c00000304deb80000000000000000000000001d2a5b82b2a5f088121be25e336ca1a2888000149600022ca00009a874c97aa7b23588a6c8804deb385c133800000000a05fe8e98d7b22c4bf5ac582a78000099ad0a0000fac2119ac04102f66428a1904710368000000097d803ca25a31a139ad4a7bf223c00000005419de033b105203893ac000388adde020e27100005888e32612290a2328aa895380009b5002c3ff00000001a820002be200000007170000405000004502d8a3a30ba0000000000230e28d2362745122c9f200004ba00000000000bb1b3200000000ca480000002d3450f8000dff9c0c53b22c00000000000000000016b60000000000000000016d03a88000d9d8000612b1be5c01d16644800042e196a54a2b821f527b20000d1e7be00004f0a3f200019a68df80006f90000b118000000000085503a000019a8000000000004b813c0b5eddc978cb670a247c8b03209b0000641000280998b800000002cc00000002dcc21a29d67f387ae7da800000034209c80d042b120a011ea3582600000813328200008c48a79b006a6a854b028fa2c6a21b2bdf9ffe61c053200034889e9878856228de0000ddc55a00000001740d68ad40d232d0c0cd880820f9434d791108c1e888a91c0000b6c13caa27ae6eb401c9631291c81a50000a560f0e8ac123800033ca00019c400034ac17c0000a242b2adf3b494729b1864292e82111a33a4f40000000145cc3606a81209b7c00000002e49ea697b00000001e02d52000054481ec7b4a3b2c8133e062f96b84c49138633313a2ae91e072189c87019e468fda8f69db830e127ab44d132a0cd1525a2325b164ca0080ec011f0ecbea21c5b52a16a349c1c1bc2b24bad3018453b31454ba6e00000000021264200d9ffc3ed898eba9947e6f0a9ca26b00009b9166e94b1932a8aa69ea3aaf92c32aeac0000c1658e0000d76868e6c6895416899e655790ea0000280b2531324a90c1050c98b680d324aa709f78226062a86481582b92cbe152956287280009960d9a74d353090a0000852000000707163f89f80000152000021
  | 54 => 0x50200007820000000000354c00017ac0001e00a1a951e00017926658000488000000012ba0f50ae2293a3beb07365c79f09e60000000490380263fac30530000067db66c00023f0a8c95c61d30000b829e26000000000019f037980000002b7a000097694280001d62c2a00000007158e0edb498f8009116a4be00002af23e600d00000002c440000000629a528000123ae26a142a6a93c83ca1a940002f648b19f763110000000000049d9faa2d6000000000000002e361edb2f65da338eb53800063527189971db000000e0c5b897269200000908f0000035f054699146e42ca8130037e3d319b0000056c34a81fcd1b0986c2cab1cac9ae98bda800007ca97200000004c7000000020c00000a3213180000001cb2000329600000000001ec40000164144869c00027da28d9882d2eb00e00000000000b9e431b01600023cc3202ac2c340000328ab36a6e9eea00016fadb080000001d183cf0000323b3521ce968233c1a5a4da9242000292602f00000002d860000726c5217267ba00006a5b3dcb0fa6ea2a900000001898000081c29b83820000000d22962c88212c000025c02629f2a6fdb43e8cc1ff278224ae2cb9c264c59ad00992ecec290000081aee464f820c33c97420000cfcac38712000000000002a2bee0614af2000000010be00000000000252000000013781700001778ce5b2fec2a8ace7188426c25a3c243b89107dfac4ad3fb012488937c0331c52765b86c00005e69348f2c7ee0b400000b04c5eb58c1f980007a023246700a8c27aadbeaf48dd6aa834708f6125602c8000310b7fa00018ba61b800062d37b8308896adb62cf2dc1a39484618c4000000000022be000000000000000001bca000144621c00003681390db2800027fac360002cf686785ce00029189e4000000000000002638cc6080c446800000000004e084fc0b19b0e00000000002484ba3b8200000000000000072ba90cab3800058e80003bb36086248000a3b000038787f40000000000000000028d0000000042f23640be2ad6299a5145a40e3c8d036721df970836384aa0001ad4b381b38b43b29441b093482c11a05600e2684596c8b761a26cb80aac8e0ae4800000000dd000096ca682bc51c7022e35ce61700007642202280293c29900000002754cc30000166a97c4c11e7694d348ed1b800066a8ec0585807249e000092512025921b08a08800004400002788dfcc7aaae8d92ac5a045809a4b3305477293c040f0a8e4e2b72a0000000a4429e006c0cb87e7acd80b519fa0002b0474b9f705ec8140c743386acf89f24402cfedb89532da7b892555a00accba9644821c886269afa0f2917632b13ba5e01c1671b937a16ea6cec91805aa6c05101b81144567a68a9950ef062b1046274b596b123852d943742d4037bc76b8ab269627e035723dc0
  | 55 => 0xd9216a0344ab386a82f8c9db1a92c898000c3180000000f16b2aa8bc00000000002a88000174c65da9e4db789f81dc2a6844e8cc00000ba0ccc36ecb7b183a000362a382172014a2ef40000000000046ede1a0bc000368e131319e46f000026c92c4000000052686ae0001eb244d384424f1ec06f48000000328e4c833320ba901a7a281ac90aa41829ab244a7198d8ac5a94addb3444284306c1509bb0bfc0c8c6f1800000036c80001ce2338826ec4f10e47448000cd610b4a0e8adc05188b631cade01cd14cc9c09308711aec228c2b8c00031fcc051e9a675800081222b43d7a2d21ea09ee74200000001b929d69a884851a9c000000000000000000ae600008600000000d16085205db26800000000000eda1200000dd1aa7a7848000a6305507609e546d12600ce931d8779239e00030062cd989e90b8000c310c54e2e2edc5861bfa00026fc73eadda00006d4db39ef44963278bce36320001f4a01c000000028a645d05303d900007670000b300c3ed7baaf200016ea0002ad20001e90db51204000129404eabd40b3acac25a0000523b192af800008681132a449b52dcc8468000245880ba4260001bbc3eb8d90cb604a61c90d7838a08d893fa5d69f5abfac7830f2a149ea09ff00002f38232b89a38c5dd0cd60d5a26e51e9b10a4c1d2800020e4660a3f4d5a80003d19dea0000000d4d3070000000000003004601328513987ce2a3574709244200023980002d9a06e80000001aaa00015760002598000196c0001a041781cea8ba1262cd1a05a4b4251a2a4a0680003824461000088980000000000000000000035120000000a672ffc0000000cd38000c21078ab180000361800034faac80000000aeda88096b00005530000994ae5800002987768c8400021dc00020d2d0e172800024ea000267a984916e00030ec000016000013a400000000001d52b6822d8cdf800075b8000a032db8c792dd22d4312c7878000dcc00f47c315b80000000dbd8e74843235e7052704913011a03c2b3a506b3080000000c2d871ecfda9f80000bd20000e120a5877400025d08658000a9c853e2ce176c000000041ca9d2794000000025be0001586000000066d15108d22b323fa31c049309260001b2a9b310c0000000056989b000000000002eb0dd5800000029a4d6a16d6000217077e840600010245d28e7a5218bc428a36aeca32ec8ba5af74653b2b2da709dc39b950c68e15f200038b4000129ec5e0328c1e12a20000000d2a0554bfab306070065a5e200000003222cde155cadc2ed88be0d2233e843c0f0a48e01da78a6981d6c2d81d42d992db600017dcb2085fa8208c980001adcbd8acf40002b640c40604c0280002e8800007d169a55900000000000df28f1a358800093ea8820a2b3aa66698c23a2a0146d3157a00024229c5a1ce0002
  | 56 => 0xc700d22a94c1111eab50b79e09695e626e947c921839e68e8e4e49436e0b7280002270c26a888000b49a59c9faaba06e70000ae000005c700008019ed09480798cc1085e0000000cbc8000af981e24d90000a5d800000018322c217ca00032d419600065192ddc0002a50ce41f40000019a0bd000083100001241e2e0000000000328a1e180000b9afe6b3100000000000000000052a9dfc91430340b7b46018f34842e609b46c7a3b067aaa360ebae443aeae902719eda53296c4000298a36b0ee078f00000a200007d39bda19121c61078d7a5a591c200000000001754d83a4fc62000000000000a189872bdc80005f6b15200028a05781d462fc81021ca173c16380a47f180beb1aaac6c5b33d851e284274fa05200000001b1000000000000000000d14342c0001e72c0c31225f22e5458396aed671eec00011fc717b7e657f0cc481ab4c6bfb0de89448d50554018c0000aaec5aab923e231de5d780006c8aa8e00032e800030ee00000944498000d8f997019f9deec1a800000014d0d5eaf301e48fde5788000bf300000000000da636b495024463b8b3e85f52b30012000035c80000beb1240001494385a62a0000000ce785f613e80009d58d4e83228ce825b53800014f0000261000001280001cfcb1d2994000083c00000000002e9a7e20000a9e0d469eb253265f00000000bf87f4b3b4486b65291db2a04ad912e1881c9c2d3877aa02ac06224842ac3d040865938748662d620000bb4b2480000002a5e0001ea2cc929006b308bc1c7347e5ef00009c2a106000000036000009069b180000226dbc296a0000000da30000a410142000276a52c22ac8a3b27aaa680009aa000067206e42459ffaac796b2af3a0e01fdb4365ba226a0002d4c7478834b4694b65cb3578000000000030dc7d330102ec938c5f4a4eec7e0e10a229a2c4fa87d89d3283424c8000d380bf40001bf8ac524408a88c5a68000000000000472ac8e02db29a0d7000091c800080e9fa40000000000024e000142803200000000000db687641c404240a0b61c0000000c500000000065200000004d21cf49f50000b4e37b452600000000000cee1d10bde219400000000000bf0000000040c000000000009be80008fe8648bbc08c00002b2c05d2bee00034866761ed6b2122f407da87852094fcd3ca7e6a98b7a86390100d3b23ec2de212016c2536e2537a6c6caf7a4b19ca417324306fa2f4ebed86ac46f9c1a1f2074435016a268bb89e86db4f6a14000000000008cf0a50d9c000000038080001cf23d000220002f3cd028d02000335c4ef34d85b88000bf1000000000005680000a9536120a496e08fa0f4ea5ba86c4020c82d9125cea66a0f00fc24e00f4a78882a000020c85be8d4367c7ada6025732f2ab320940c6b08faca418c0d509e9824a02fe8c2921e
  | 57 => 0xea580d006499a421a21282000000000016ec4b380680002592beeb47a44900ce7758000cec9284000215e83e1b04d4a00000000e94000000000004e8a4829444fa0000bae29a0318800021e1af0000000092b1112c248000b9686dad470000bbe8000b9285646832aa65a50000b5400a80002d540000f5a116320600031a6000000017405345aeb5020d31ab2d9e82906b921a849b16347ab119631397ce60220747c103024fd9ccc462b50c9288d347a2109025b924ea600c066092c66cd9b4ea5ea225289610ae39c0ca4b7400008d299584f1014a64a9fb6dfaa3b80f431fe00012e27d20000a18273c2d20c660002e9e8f885d8000208c46195000000000ced86d20002e8cc0e800000016460002be40ccb0c00000000c9b95922df93b80f699f80000000000000009000003d225e208703fc2bb971a3af800000011b4000000000028024bd0000d5280009af24c6bc5b1b49880000000297a71a8000000254c00029cc86b80002d10000000181e5752254a098cd24ce973e04b85eec690b188c408e25d61ed861b0000c68800063691b211300000000d707cb81b269e8000d868e4a72312fa0f22f4258500004219abc8cb8000000309497730de87a256e1951340a3e2b981eb2126018b2f42480a3c69a36cccb180007181b3a56a983895580006c0981c4c28b1a25680009328000d901b36141aa4471027107fe17e8a2100b4a3f2186add2a7c24ea06cda033eac5524f015312da1c6b0280a682ee15fa3fedd2806456f053c48aab5c085b83ee19b7009cb00007b9021051109d89e3839a9b603c60f81dc08f4adf40279baedab000074e91aeb24105aa5f8f9807206840000db8d3f0000c170000a750000a4eaa144cb00000000fd800003663daa7e804d8908d16b59a4a480009578000c950000731031e86f0b766358e56daf2416a5d1f1a000000000000004bdaa4e9c0228a8c11d8edf79ab01ce022e94c2f500981edc06623860f726da3aa063a23b1aac76a93766c2a0b870d078e75585ea77a000031f29de70f0a3e104354e32206e20578bf6a2a9d0ab9a834606e2d1877e20be5770e9067ba07865225fe83eb7340c1846ac7280009959e741f309e4a5a2eb252e1dacd4631b69c312b41a300001ec1480000355ea9b95c075e320a000000075706debec204e9ac8e22000000009a00003e7897e3db18ec4ef9e1cb0999e200012900002b28a0631f2aa1856e16cb3f27cd805805c85d2e2e96924d9a16800025e400027f20001418d300000661800000000003b30000000000000000009f400005aa000000000000000b2c41990cc00000000001a2a0001e20d5bb35a00000000000000000217400011ee3e40000de0b230418100600002b2befac96dca051621b1a16265962437234562af8f8a2a429b4799386e000000000016e652f
  | 58 => 0x12bae4f917a0b87214ed74a158c3f95f80029b56a550ef2000310a0000f2e06f261c00022d61f0a31896d1dbe20e8186a509c8e61086182ce85e2536ab9e39680509dd04707a7b27e501b71270a85dc1839a70c62119a78fb7c0d3d09dad12a11c39902844b582bcb23103ad14b5b8bd61d6aa0ca9702b80f5c41e02acb0d170259420d0b4a00000000000000000000003e800010a8c7c00000002b506b20000bc7b0862b08dd45bc0000000100200017c47df08483c1b0fccd90e9c165a8080000bbcd7d0ebc000017eafc800000027467d800000002eaadfe00002651e42cdd03a6c83b3d6933178ecd5000068d29dc531000000014a4491184600008cc000125a00000003b180005939e1641880006ae0000a43a5c845fb5e00002266b0b16ee00007963b5a3f870827264e7808049f122e7890000a32302a8901716c42000000011a26da1f5a12113d886880000000000aff8000246a48000020800002420252800080700006458c7e5c28000bbb8000778ada220d953ac8408da0000000b65146a0600000b488db0a801b12000153643d2ac4030825000000000eb212c3fdae020000842c9d1fb000003089df800000015380001d2c58037b2be400000d0041ca608b543ceaea203293f0000336889408862ed8000cb9000076eaaf8000363800023a03e58e60260800075135142d9948c45a2ffa7aab82a000134eb5f285c2cf000085b8a2000027642f311ce0000000000337c00026d200015ec1e30600515800095d22e6000000053ba2b89159248cb08c5e00026ec6900078c9c0c8616f34ca26634a022083a25a7b7c65270000a418000d87b118238286ed0c16f4000221000037d68792ebc7a70aea0000000000322478380000001d8048d8b209231ac411b00000002e767de8044822160c68690f265526709fe897c0000f02c388a083511a4ec878b0263a9f963f436e89ed000000033b0dfd2dfc00000003a91df03090a54a0908a457db150c8cb3bc6d62376b472ad00001b506473136c221f82d4fb3801feb5ea53e24623700b2aaf620ec1f01ef289e80005b00b142e1329c1a91d22d72a3fc8a986b660f12662d198e8c6b8678c43b0d4553b33ae16800013235ac117b72e1aa8514000000016483a8000289237e022215e38362d8a61494f040e000368855ba93806ba4d86e194904c602f2926000022687848f00c361fa8000069b8703850c48b15a7bc0002ec05e6147629f24a81fc800000000006f526780000000368894488f995a0b9099a00000009d800007470086ada17468c887e4187296260a33fe000000073b32e200000003002ffe538000080b00006f992ee07a843e2d0907e58126e66ff00000e49eee0530d9c64214f400031babd01fd072f1a5e00000de4793628e210504b7ea2fc095256ad1202763dbb5266a0161
  | 59 => 0xcc98e8806ab7115856cadce0002f26600388289f99ca31927cc9f62e1aa0b90003eeb75ad1a000053d8000759800000016cc2cc8000a01190ade12694997aa664ae27e4324389c3158000ca6325600001a408a1feeb3f154455535b47010cc6000000031031f4000218e88a256064900006a61762adb14e60000e621d0000000c800085197e4b7f9f640000a1c1ae9206dc31386b6a1a7cd01ad8c2f28b4c000204a8150354948a94c00034aa437026a9e8070235a00103c400002808000aea0e52bf099d4373054e2de9a54000000063c08b04ab8a2a030086e0000000da42f3400003c476d80004a1893616b00001502c70484902229c24f8d8eb794306915640b0b52a8f8066b4826b42862aaac7a00000001b2e88db49c74932ee000000026fa686afe25461d1b1424cbb2b4b67acae8089fba9a48824b858358938aaa27e381c2434a76202981384b826a26d3a5c6881a36084e8f1287e910e476a7ca9df1b6096c2a3ae01859cdb1b180aac8c763dcb5cca4b175a40b80000260f8216506c88d5a6b808c2da6866b2aa6418e341280d820000000283895c9e700000000000d549ad8b8b8000b041f720000000c030cd82fe95a20c694d80001f063ff97fc58203de8c1aeb6dc08974e0600001c3352a00000000b72d66000284a410a3a800007a40000ba80370000000045a206000075380000002afc70d8ba4aabb0c86281ca86770000d8b800000019000000000c6e14023919296bfd10586190000086926e000213c24321345e2ac3c1fe0000a5e10e24a6290869d00004ff8b82000134ccc7b160a6b26a019eb8a2c14b75000005c21c2000005a1fca126800000000000002a240000000d8880000001a5600022904b227849d600001eea2ae0002b54337b33e88036a600018840000000000205870a0396603800064c1b804e69ef090b029e151237c4de1894bb8861690f82ba8b2119cc1cb41e000000000000000002cda00000000002e8a6670fb2000000000015fa00007480000000a9628b04ed8dde7b19bf05e180004fca4da3ce00008832f44de4000087e26e8660194c5160d6e5c307f01ae0a3a1a1918cbd7a496d331f8c0799fb2759000044c0fdc2962632924331c9090000154800093d800031438166ba81d6c3698ca15f185291b0000000000000007066ed80000000000000000072daaec0000000d4ea26c0001424838800000025a05c8a5880098000b338000000000011f8a600001b6a00017cc00015b4d6418500002d5aac697500002cf841d291cbe990aa6cc8b8c04f013e68080000001cd43fcac8849ca396ac1adc4000373e0960b8000000000ef1f38483326441ea714b1e0c2a00031e20003156842227600006965e438a49b7001e45c800044433a844a800020800000e40000000000043e885065a0000ce0800030
  | 60 => 0x8c9a1ee0400008140630c468eca59a10180002a8ace338320638000000226200009b85e11b30ac6000000008d036493145081360000157e00000008c7b49a000000095209f00001c02000306686b11e2d020c02805b654394173627f0000d6990380001150000179a000000024390fe0c318563aba2daa969f58db72e0c338375406a260ed009470574b55c000187aba91af854c20aca8627ba2b7a864b3b0df26b2a1522bca49e80c146266437e231d144c22410ecd3e8262c8080000000000a76af32554b1cc0058c7a056901223c8000643a2240000a2e92c800000014505058000d5c048e4d1855eb63998ca84b5243f1882e3ac31440003370b9f11a885800080002950c738536d98982e2dd3558b4413f4d34a8d41ef30e6391159658999be739a5502fb007c000184cdc10a40df08000981800000023e40000000303373a5fd845c8e9046282aa5ba000347c3cdb634000004678600005c50000000004ed38b3f47cc0000b649cc06cd0000000000000029e20000000d97800022391186152fe4ab798140000000464abda88b838e9780000000000000006f400025102640e5e000225a1b300002f431344d621cc00000002f99388534800000000005d933c6cb695269bda2849fbacdcb51217e9e03876ce280000a7367464b000000000000002d845f43694e200d1699d98f61461826dd913e0000243644f82247831f14bae8000a488000275a9f04452ee000012ac9c1a53898babca1bc99104a2039474aa9ce79ba1dabc111a614004962ee9b7208da7ce94e8f442c9a2a800030ea0000f84d59a2cc4270a38870a234b81000000000006f81f5c00006be59e8c789c2044eb5b04ae8ad8b8a74daf8677718fa9fb13ce7a0a9667402cd6dc6332266e000055f2dee0002cea0000c3a6d792800d7b02caad000025c304238a9ed41000fa0913844a4700d4a055033c85e935678c00005e9381a000052e70295ae5db99ba71c939400000000000000829240eac4800018a386487b0b4a66902aa00a9b760000ff400026ae000239a4ff087c89e166232c01822be23ea0000b0c97533d4457000000030683b60a047a5852a07baf12de22b86b052e222f8b0d2aec0d600fd20462ff940e1bf064a0001e340232d96d5a0000977a9b8beb92d40000000a2b00000000000bf00eeed518000000000000000000002cccc7215347eb000000000000000000b9580008a580000000000d638fd2025800000032c08d9b0e84751fdc88780007c980001ca800000026980001ad2cbb00000318f0400033886088000054ab8e595004ad881c640000000592800019810360001dd28be8aa013890d4de8b71e3708000b9e93de00000005ad1fa282122ee8a31b7a4340674202a1ba38f900c2b02624a2f946ec499c840000000de61d680001c4aad80000264b7
  | 61 => 0xa03b6d600000003498000000000000000000b08c58ba00aa60001e8e00000008eb965e5910000c6700e871db682b3a143ac202374bc338400000b1e25e8edc949a15c3a6ae469a2158406f9f46db13482c4108761370000000000000030f800000000000000da4800000000004df80009bc800064d082ab2cb722d6198de4d100ae597165a32da008000383c19721aa59f0b7c933a8f293925fcaf400006ee84a45279674d1e00005c900d477427948b42e4c8b919986fb82a0b6287ee2c4ae246e5aae4d550000000000065d0000960005600015ba0a1a5e8d352e0eb092b5817f0fa8451800094780006e503120001ff456d8c6803f152ca1e800000000005e880000000b6e0001b5a7ad0588b758000cf6ade8985a0443b7a724b99b6c06f732ac00000000002f003070670a0a381e00000001b1af8a00037f6cf3000094f80007c2230cae680000780dda0002b0883180000000f601b58000b8a80000000000563a73e00019201c52220cd019aecdc863e6f3857600000000000376000000000000000000000000246822790b600015a42ee000060d800000014ea4ec00005b19e36000000000025c2b790e820d8ad600001cc8000111c35f2ed44e10e5c21a93dc7ef1d7400000003a49938e2a800000000000003334c612f48a613748ae29f3c5450dfe6998000c2a0000cd29da400027d2b5a000083da7a83622342393000050b835ab6b0000e028bdc00010a00000960000000084a1542d7700000002ebe75694880480a80e1287b2625b69ad8d80000ee9bb892d245486014303e380000002dd478e01dc000000037d9d945c4b56cb298000d7ca1fe8ed8000689341806100000002baa000007e1a00000afa800000000000000d84ca180009b8800051693322adaf4c000382600000000d3956622b9c10570b3beb9721de94ab8a66aa0000000222c4c3b5929931a90b709f84dfc8fee54935107beb4989458d6a3248eb2b5a8b5c4770350aa783e24dd0dca818031c1848fb4dbd0662571375c26d8000452800000007aa108ae00639adf8b9f8000e0e30d6b5c0000c7485dad6ab350d6132baad88a5a81c0000cb4b2a64f50b1687982c810c10e6ddd360cb282c1a54a8da661e02c4b882040df114087f08f760ff86408dc9d9297ea6962a73576dbeb2dcd1cb68a000000000002b46bb00000f380005b3b37a0000000d458be8cd0892a0002214abd89c019180000002ad40000f587ab80008f42b4097e000000010b00000000573800001000000b40000d79800017cb12e30cafee0000000d840000a29000080aa3c666cad987f311b81958af47ac1ab66930bd4b17b03edaa94363cc0000bdb000000000002ca000000011360000256a2dae627cf8000741b06238c2d3e2780000074a74ed25a6de4dca9f6a0f064cb5933c4b9b2efeb
  | 62 => 0x2b7e0000000abc24baa1200000000000c5c83f20e1350e0000000000000000021b4325214c57588a698992bcd3a061a844b1388f1346a8ca323c5efad4671d10c89e7836c99904d870b1a1236d0a56d540672907816aa9499607982ede7ea2f56cb790ba4239a6e6a79cf084fb26c7ef8dae580b076ab330b823d1816b4492fe7d12a2e64784340001da07361e920000000000000048731d444186a20002e34d03388c4c080006bf028e000341049e85c8d0899f4000000039b18c83630000c881b98d0ca9560fe271c2cd1c5a1ff0eac58c04b016316bc5f7a8fe11d81ce91e99d23ef0d24bbca36a5a21b84a019686b6e8a826f8ab6a5662fa8c09351ec0d991878a9d7c5fc225e0002fdc0000e2e85c8000a7b823ee1889a4810b64c000000076620b4ac0208600000006e8000000014149768000ceb0000000155a1bd8eb8702000000000000000000c99800088580003e700000000000257b3a60000000000000073832f80000042c71116cc1f8000cc0033e000000025880003f3000005e800074e04e4dbc800000000004e708b23748000000000000020009de800071400000001020c62862237b9e446a18924951321649d17182bb0000000020093d266800013705121fc80083168b0ba1d4000000044599de60480004f3269a390a7480002c3200034040000e3a95e945275d80000002140a26a95c8c700000002c0447da404acf27402da1cf800000003322ff6c4f80007e5355a073099e36e82a89a12d3a8e007e813a815c10a0a96c002d9098299f232c98d0b4f0000993b83a71232e6162b3f8e222b52a1da65a0e22c38328228287206765df0000da100000922858b28b31613d08e841a075c79a23d43d5a3ca0000e7cc3e88ce3df800004c80003fa80008e49398000156000018ced7d9bd0000022a574000000036e400000004d284d45b9000000034f8be12a2c0ed8000c6a911e10b21886a38b88d2f8608119b01a5ff8000de900005a138a00000e36ba2341262380000000e5400000000000000cb2185adddb6e699cb6a00000000000000000001b41d6a68c531800000030f616a35603ee13aa00024bc262000030234c8d3584920821162aefb4a6abfaa92a3b80003bea0b2d6c827e27eb1e666380000f98000ba70000a6391fe5b7365add00000893800089935c4929943c0de0000d4f0e40c7b2ba4599907045018b0047b4664250a5e75425900001888e15ade240d22420000000ac826360000d0a36520241d38cdc12f321c0000000000109a0000c14dad905077f8a0600000002531bec920b35e58a9b3c8742edadc3b2880000d3aa8c110400000000001e9478126903cf83429c89760883802820a2368c4596f827b0000170000037e80000000000b290c6cdbf9d9e2c015f03a3106ea0da9a823f09a24e3994aaa60
  | 63 => 0x229acaf360a00000008cb2ed2d0500008ce0000af0800022f97a62858000a1300007bf80003e01c3a00018aa79b24380002a74d7e01fe000000000004ca00002b068a165600000002542f5ca1c06e8bef2b348a80584740a57ea040ccadb420d46911326c6f1a3ea53ae388b7af0285104505af800005f0fa60000000c4a006e00000000000c6a3b536fc1f71ebcae11c6c00020627d880004132474c4700000001e5a0003828409a10e8c09bd689d115272800000002552859800000000007d48124df91d88b21ab22682341ccaa07681b9ad78000185e0002ab0284800000000000001c3200028e2a4f9c22000388e9cc8000dce04f872fa34c0ee03860001d7e9b5a49c80f0e0c79e1cc665787da30a37d4c7ba40c6b834281a8317e8bb000000000005dd80000003194000000000000007060000000271ac2889840000c0a4230598b3c25ea1d98000a4a945eb1b3344000151c0000be0000227c0ea9e5ed759d26538ae124cfaa800340000412b4ae00000c40002e4e000000000002e80000000000000052e80006c9ae1010699e87b8800000000000000e20842a4440000000000000000007b40000000000060ad5c969cc0714dc8c514c21d500fa828800000021f60000a1a0002df0576a6a40000afa00033ae0000a68042000019a00004e89c44cc48000be70000000073e65e0000d5f8ce80001c829bb8000bb98000000000033680000000000000197a00000001e4000061896caab0000000004ec00000000001b3eba80000000275c59ca52e01300005412bb8a35a2ce00000002e500000001f68000376a000356498f000083a90d80000402d90912000024107c0341600000006f310ca36d8752bfa2fd495f2b787cd07be7b09cdc00031f62a8a96c1de1eba6271f3a0000000000000033d00001ddb77c4a72894a078000000000091900000002e182a28000d03a3780001a14cfeb2d6bd180003b99aa61c8b5e8c452bf05a634640002354d8b2d32151b89000000009e9139257bb3a000025820002cb027095944caaa204ac35c06e6877c3c328cac1f357c0dc95224b4821e4afa38e425953eabaaff23a3a59e56401d8e0b8d1c00005867ae37446e3ad7e2738b6c0b6800084b81aa00000006a1000088e1c0ed291540bce8000c0780004e98ed2da885b432f86b04c91bc86f781921182ba2c09abdeccaa0720000000175016200016f6000000000635bc3659ba6a4a1f180001b62000239000031821600d58d6d800000003988c03284bf180827db800000000009be0000000299e00028f4b4a8000000141c0000000992a45c0000d3009e2e64b352680bc6920a00013a012720b605e20da0000a0a70c0000a0b0000
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x84294420d05744c83294420d05435c84354420d05735084254420d05744c83254420a61859856008420e21549856008420e4153985600842090d829cf5450f1090d829d35350f10a0d821954310f1090d839cb5450b1090d839d35250b10a0d831954210b1090d849cb534cb1090d849cf524cb10a0d84195320cb1090d821cd5450e1090d821d15350e10a0d82d954310e1090d831c95450a1090d831d15250a10a0d83d954210a1090d841c9534ca1090d841cd524ca10a0d84d95320ca10c0f635ca63d5110c0d73d8a62d5110c0d635c86315110c19635c06315110c0d735886215110c29625c06215110c0f645ca64d4d10c0d74d8a62d4d10c0d645c86414d10c19645c06414d10c0d745886214d10c49625c06214d1090d829cf5450d1090d829d35350d10a0d821954310d10a0d831516210d10a0d8414d6210d10a0e8550d6210d10a0c8550d6210d10c0c7550d6210d10a148550e6110d10c187550d6010d10c0f645ce64d4910c0d74d8e63d4910c0e7650c43d4910c0d645cc6414910c29645c06414910c0d7458c6314910c49635c06314910c0d7650c431491090d839cb545091090d839d35250910a0d821516310910c0d7458c5210910a0d831954210910a0c8558d4210910c0e7558d4210910c0c7558d4210910a0f86d4d4210910a0d8614d4210910a248550a6110910c2875509601091090d849cb534c91090d849cf524c910c0d645c8530c910c0d645cc520c910a0d84195320c910a0c85591320c910c0e75591320c910c0c75591320c910a0f86d51320c910a0d86151320c910a44854ca610c910c48754c9600c910991831c141501109a1821c14150110991841c1314c1109c1821c1314c1109a1841c121481109c1831c12148110c0d635c86395010c0d735886295010c0d635c86355010c0d735886255010c0d645c86494c10c0d745886294c10c0d645c86454c10c0d745886254c1090d821cd5450c1090d821d15350c10a0d82d954310c10a0d839516210c10a0d8494d6210c10a0f8550d6210c10a0d8550d6210c10c0f7550d6210c10c0d645cc6494810c0d7458c6394810c0d7650c4394810c0d645cc6454810c0d7458c6354810c0d7650c435481090d831c9545081090d831d15250810a0d829516310810c0d7458e5210810a0d83d954210810a0f8558d4210810c0f7558d4210810c0d7558d4210810a0d8694d4210810a0d8654d421081090d841c9534c81090d841cd524c810c0d645ca530c810c0d645ce520c810a0d84d95320c810a0f85591320c810c0f75591320c810c0d75591320c810a0d86951320c810a0d86551320c810a14865506344010c14761915344010a24865506244010e055418c6244010a448654c6244010e046454c6244010c24761915244010c447618d5244010e046418d5244010
  | 1 => 0x1d09749c0534c821c4a765c0534c821d0a745c0534c821d09745c0534c821d42715c0534c821949801d6434c821949801d5434c821a0d839914294421a0d8498d3294421c0d545ce6290421a0d831954210421c0d7454e628c421a0d84195320c421a0d831914254021a0d8418d3254021929841c12154021949831c12154021a0d8298d4394740a0d839894294740a0d82991538c740a0d82995438c740a0d839915288740a0d839954288740a448154d6214d40c45631c55214940c0d645c8530c940c0d645cc520c94084c87595320c940a4481595320c940c0e75591320c940c0d645c8530c540a0d82195430c540c0d645cc5208540a0d831954208540c0f7550d6210c40c0d7650c4394840a0f8558d4210840a0d8694d4210840c0d645ca530c840c0d645ce520c840c0f75591320c840c0d75591320c840d05435c84394440d05735084294440d05744c83294440d05435c84354440d05735084254440d05744c83254440a31859856010440e11539856010440e21529856010440a0d829914394730a0d849893294730c0d545ca6390730a0d829954390730a0d8498d5288730a0d849953288730c0d545c86350330a24815516215130c25641c55214930a0d831c96414930a0d821516310930c0d7458c521093082c875954210930a24815954210930c0e7558d4210930b0481551424c930a0d821516310530a0d821954310530c0d7458c5208530a0d841953208530a0d8215163d0130c0f7550d6210c30c0d7650c4394830a0d829516310830c0d7458e5210830c0f7558d4210830c0d7558d4210830a0f85591320c830a0d86951320c830d05435c84394430d05735084294430d05744c83294430d05435c84354430d05735084254430d05744c83254430a5185985600c430e1154985600c430e4152985600c430a0d839914294720a0d8498d3294720c0d545ce6290720a0d839954290720c0d7454e628c720a0d84995328c720c0d545cc6250320c0d7454c624c320a14815516315120c0d735c86454d20c15641c55314d20a0d821cd6414d20a0d82d954310d2081c875954310d20a14815954310d20a0d831516210d20a0d8414d6210d20a0e8550d6210d20a0c8550d6210d2090c8754d4350920a0c8654d4350920b048154d435092090c87551434c920a0c86551434c920b0481551434c920a0d831516210520a0d831954210520a0d8414d620c520a0d84195320c520a0d8315162d0120a0d8414d62cc120a0d825954310c20a0d839516210c20a0d8494d6210c20a0f8550d6210c20a0d8550d6210c20a0d825516310820a0d83d954210820a0f8558d4210820a0d8694d4210820a0d8654d4210820c0d645c9530c820a0d84d95320c820a0f85591320c820a0d86951320c820a0d86551320c820d05435c84394420d057350
  | 2 => 0xd94254042b21811c14254042c0d735086154042a0f8654d4214042c0f7654d4214042e055350a6114042e05535096114042c0e765c85450f32b0681d954350932a8681d9143cc932a8681d91428c932b06819c9544c832b05819c9544c832b06819cd544c832b05819cd544c83290d849c7654c83290f845c3654c832946819d9544c832b0681dd9544c832b0581dd9544c832b06819d9544c832b05819d9544c832c0d761d9544c832a0e86dc5544c832a0e869c5544c832d05711c5544c832a0c865c1544c832b07815c1544c832b04815c1544c832a0e861c1544c832b06811c1544c832b05811c1544c83290d859d3614c83290f87553614c83290f87552614c83290d87552614c832e0554584614c83290e87551604c83290c87551604c832d0554dc5604c832d05541c5604c83290d859d0604c83290f87550604c832d05549c4604c832d05545c4604c832c0f7655132d4432a0d84dd93294432c0f744c96094432a0d869513214432e09544ca6014432e0a544c96014432e09544c96014432a0d841d93254032b41811c13254032c0d744c86154032a0f865513214032c0f765513214032e05544ca6114032e05544c96114032c0f7550d6210f41c0d7650c4394b41a0f8558d4210b41a0d8694d4210b41c0d645ca530cb41c0d645ce520cb41c0f75591320cb41c0d75591320cb41c0d645ca530ca41c0d645ce520ca4184e87995320ca41c0d75591320ca41a8481591320c941a1980195434c841a2980195424c841a0d8218d4354041a0d831894254041919831c14154041929821c14154041c0f7550d6210f31c0d7650c4394b31a0d829516310b31c0d7458e5210b31c0f7558d4210b31c0d7558d4210b31a0f85591320cb31a0d86951320cb31a0d831c96494a31a0d829516310a31c0d7458e5210a3182e879954210a31c0d7558d4210a31a0d829516310631a848158d4210931c16769c45450c31d09729c05450c31c1a765c05450c31d0a725c05450c31d09725c05450c31d12715c05450c31a19801954350831949801d5424c831c0d545ca6390431a0d821914354031a0d841893254031919841c13154031949821c13154031a0d839516210f21a0d8494d6210f21a0f8550d6210f21a0d8550d6210f21a0f8558d4210b21a0d8694d4210b21a0f85591320cb21a0d86951320cb21c0d735ca64d4e21a0d821cd6494e2181e879954310e21a19801954310e21a0d839516210e21a0d8494d6210e21a0f8550d6210e21a0d8550d6210e21a0d839516210621a0d8494d620c62190d829cf5450d2190d829d35350d21c0c7550d6210d21c85431c56210d2190d839cb5450821d09739c05450821c2a765c05450821d0a735c05450821d09735c05450821d22715c05450821929801d74350821929801d5435082190d849cb534c82
  | 3 => 0x244e1c040802ac164eb91abb962c00748eb423004818338b38000000039800003d885000280c8b48006580060800dc850f5330b93c4b68002a80000000001a86994c9ca2ef733ee1a2cab1b40d818003a80002cee9b845210cf384b5bd004b7c7a8708101c558000eb769b800ae38c43b603e96025a1800000002903909acd3a43c15a1d8882e0ac432580010a0f8a690b9024828903a0cc8d65512a64000bdaaaae80001006008000000d00c110cc190000001c0202c050bc04050030640a02c06044070100800026000010000b01838004210780001c1a0502e02c050080c014000101b00c1c03002048060182600000014070342b004000740000406030100040400c0d00c0800801058000b80100001008080000400c07028000000002c02018320000000401004000040300403040020000b004000043223c060640202405050020040f03402000000001d06c0401c00064000200f0a4280000400c04038030000002843028050040e0000c0241490d829c76550c4390f825c36550c4390d859cb6150c4390d859c86050c43a1681dd94354843b068198d4354843b058198d4354843b06819914354843b05819914354843b0681dd94354843b0581dd94354843b06819d94354843b05819d94354843a0e86dc54354843a0e869c54354843a0d869c54354843d05711c54354843a0f865c14354843a0c865c14354843b07815c14354843b04815c14354843a0e861c14354843b06811c14354843b05811c1435484390f8750f615484390f8750e6154843e0543584615484390c8750d6054843d0543dc56054843d05431c5605484390f8750c6054843d05439c46054843d05435c46054843a0f8650d52d4443a0d82dd94394443c0d43dc96094443c0d7650e5214443e094354a6014443e09439496014443e09435496014443a0d821d94354043b11811c14354043c0d435c86154043a0f8650d5214043c0f7650d5214043e054354a6114043e05435496114043b06819c95350842b05819c95350842b06819d15350842b05819d1535084290d839c7655084290f835c36550842926819d95350842b0681dd95350842b0581dd95350842b06819d95350842b05819d95350842a0e86dc55350842a0e869c55350842d05711c55350842a0c865c15350842b07815c15350842b04815c15350842a0e861c15350842b06811c15350842b05811c1535084290d859cf615084290f8754f615084290f8754e615084290d8754e6150842e0553584615084290e8754d605084290c8754d6050842d0553dc56050842d05531c5605084290d859cc605084290f8754c6050842d05539c46050842d05535c46050842c0f7654d42d4442a0d83dd94294442c0f735096094442a0d8694d4214442e095350a6014442e0a535096014442e09535096014442a0d831
  | 4 => 0xc6b26002f28da306a804aa086921ae750302fbd66200001a54839dc63abc30b8e041a0319246fa8adba62bf862d396c5f284149a2502940017226000c1b74d72c4d5038000e07a38a0001e2c80000000a08009b0003b1922a1c2a98a49d8d09a9d05d9307cb48c49988794206926ec96ad3136540548a86492aaed6b82f2974dea749736c9305e0d32eb73a2d91866ca50d29ee2d1b07f9222c06cb08badf880b5246829c80abd2090a235026e52f4cb3b84b80cc0966be91617000daaea0b8e2e200000000c2000e5a7e748fc0811e79bb4e988485800003c27f32a0009c0039e7e9d60004073800000006131e002004d222003b015800c3090de2a022968001acf32b4ba0227780010866a8a98da19c3329ceb07e440007db16809f46f13c87128003daca2961a2f000112f793ab20f600000128008323e1f000d1b14668e81388e208f837904d00009a19ece946633801c8f21eb5ed12c057352003c834a78368c4000000013200000afbce5b85abf12c7e180aca3cb8b98c825642000d5800512cc4003c9100000324f039ad40445f878a6a2881a347c370b280013000a388c2d89e9e800869c4000000022602270003c6eda7c3d194718fea900eea97a5794a37170b1b188c9784f80000292ef00098000bb10600000822668e336002b61ba8694a80762d8c42880c9ec62a647891cd8952d98bc769ca000ca96a9e938d888000002e073000c70ceb7800002d0001180025e0000000058563926d800b9948d63be793e0c2af802b0e78000c10ae690000500000322a3046849ba53b9c000ee4806a058ea252
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 40
  | 6 => 1895
  | 5 => 11087
  | 4 => 7262
  | 3 => 497
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
  | 7 => packedAt gbK7 (718+((h/13+packedAt gbK7 (640+(h % 13)*6) 6) % 49)*7) 7
  | 6 => packedAt gbK6 (58737+((h/631+packedAt gbK6 (51165+(h % 631)*12) 12) % 2502)*12) 12
  | 5 => packedAt gbK5 (473036+((h/3695+packedAt gbK5 (421306+(h % 3695)*14) 14) % 14635)*15) 15
  | 4 => packedAt gbK4 (389718+((h/2420+packedAt gbK4 (355838+(h % 2420)*14) 14) % 9586)*14) 14
  | 3 => packedAt gbK3 (31470+((h/165+packedAt gbK3 (29820+(h % 165)*10) 10) % 597)*10) 10
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfc3ffff87ffffff03f0fe1fff87ffffe88f1ff
  | 1 => 0x7fc1f0ff83e1f0ffc7f0fe1c3f870e1f774e93
  | 2 => 0x7ffe00fffc01ff1ff800ffe03ff80fe1878f1c
  | 3 => 0x800000fffffe001fffff00003ffff001f80fe0
  | 4 => 0xffffff000000001fffffffffc0000001fff000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x4000008000000000001002400090200001025
  | 1 => 0x89461111942a102c31062089882245c334692
  | 2 => 0x510caaa228d548355888b5412d5049c5858b18
  | 3 => 0x43a94cc452906a59adaa11023664e089d80dc0
  | 4 => 0x6231888763198c9e36ccd99384408111eee000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 31 gbPos gbNeg, 0xeeeaeaa8eeeaeaa8eeeaeaa8eeeaeaa8eeeaeaa8eeeaeaa8eeeaeaa8eeeaeaa8eeeaeaa8eeeaeaa8eeeaeaa8eeeaeaa8eeeaeaa8eeeaeaa8eeeaeaa8eeeaeaa8, gbN, gbR, (fun _ _ => 0), gbI⟩
end PEqualNP.Outside.L_meta_12933
namespace PEqualNP.Outside.L_meta_12933
open PEqualNP.Outside.L_meta_12933.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bgb_3_288 : Interval gbAtlas 3 288 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_384 : Interval gbAtlas 3 384 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_480 : Interval gbAtlas 3 480 17 := block_range (n:=17) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 497 := (concat (concat bgb_3_0 (concat bgb_3_96 bgb_3_192)) (concat bgb_3_288 (concat bgb_3_384 bgb_3_480)))
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
theorem bgb_4_4224 : Interval gbAtlas 4 4224 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4320 : Interval gbAtlas 4 4320 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4416 : Interval gbAtlas 4 4416 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4512 : Interval gbAtlas 4 4512 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4608 : Interval gbAtlas 4 4608 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4704 : Interval gbAtlas 4 4704 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4800 : Interval gbAtlas 4 4800 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4896 : Interval gbAtlas 4 4896 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_4992 : Interval gbAtlas 4 4992 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_5088 : Interval gbAtlas 4 5088 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_5184 : Interval gbAtlas 4 5184 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_5280 : Interval gbAtlas 4 5280 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_5376 : Interval gbAtlas 4 5376 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_5472 : Interval gbAtlas 4 5472 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_5568 : Interval gbAtlas 4 5568 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_5664 : Interval gbAtlas 4 5664 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_5760 : Interval gbAtlas 4 5760 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_5856 : Interval gbAtlas 4 5856 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_5952 : Interval gbAtlas 4 5952 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_6048 : Interval gbAtlas 4 6048 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_6144 : Interval gbAtlas 4 6144 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_6240 : Interval gbAtlas 4 6240 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_6336 : Interval gbAtlas 4 6336 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_6432 : Interval gbAtlas 4 6432 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_6528 : Interval gbAtlas 4 6528 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_6624 : Interval gbAtlas 4 6624 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_6720 : Interval gbAtlas 4 6720 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_6816 : Interval gbAtlas 4 6816 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_6912 : Interval gbAtlas 4 6912 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_7008 : Interval gbAtlas 4 7008 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_7104 : Interval gbAtlas 4 7104 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_7200 : Interval gbAtlas 4 7200 62 := block_range (n:=62) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 7262 := (concat (concat (concat (concat (concat (concat bgb_4_0 bgb_4_96) (concat bgb_4_192 bgb_4_288)) (concat (concat bgb_4_384 bgb_4_480) (concat bgb_4_576 (concat bgb_4_672 bgb_4_768)))) (concat (concat (concat bgb_4_864 bgb_4_960) (concat bgb_4_1056 (concat bgb_4_1152 bgb_4_1248))) (concat (concat bgb_4_1344 bgb_4_1440) (concat bgb_4_1536 (concat bgb_4_1632 bgb_4_1728))))) (concat (concat (concat (concat bgb_4_1824 bgb_4_1920) (concat bgb_4_2016 bgb_4_2112)) (concat (concat bgb_4_2208 bgb_4_2304) (concat bgb_4_2400 (concat bgb_4_2496 bgb_4_2592)))) (concat (concat (concat bgb_4_2688 bgb_4_2784) (concat bgb_4_2880 (concat bgb_4_2976 bgb_4_3072))) (concat (concat bgb_4_3168 bgb_4_3264) (concat bgb_4_3360 (concat bgb_4_3456 bgb_4_3552)))))) (concat (concat (concat (concat (concat bgb_4_3648 bgb_4_3744) (concat bgb_4_3840 bgb_4_3936)) (concat (concat bgb_4_4032 bgb_4_4128) (concat bgb_4_4224 (concat bgb_4_4320 bgb_4_4416)))) (concat (concat (concat bgb_4_4512 bgb_4_4608) (concat bgb_4_4704 (concat bgb_4_4800 bgb_4_4896))) (concat (concat bgb_4_4992 bgb_4_5088) (concat bgb_4_5184 (concat bgb_4_5280 bgb_4_5376))))) (concat (concat (concat (concat bgb_4_5472 bgb_4_5568) (concat bgb_4_5664 bgb_4_5760)) (concat (concat bgb_4_5856 bgb_4_5952) (concat bgb_4_6048 (concat bgb_4_6144 bgb_4_6240)))) (concat (concat (concat bgb_4_6336 bgb_4_6432) (concat bgb_4_6528 (concat bgb_4_6624 bgb_4_6720))) (concat (concat bgb_4_6816 bgb_4_6912) (concat bgb_4_7008 (concat bgb_4_7104 bgb_4_7200)))))))
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
theorem bgb_5_9120 : Interval gbAtlas 5 9120 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9216 : Interval gbAtlas 5 9216 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9312 : Interval gbAtlas 5 9312 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9408 : Interval gbAtlas 5 9408 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9504 : Interval gbAtlas 5 9504 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9600 : Interval gbAtlas 5 9600 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9696 : Interval gbAtlas 5 9696 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9792 : Interval gbAtlas 5 9792 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9888 : Interval gbAtlas 5 9888 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_9984 : Interval gbAtlas 5 9984 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_10080 : Interval gbAtlas 5 10080 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_10176 : Interval gbAtlas 5 10176 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_10272 : Interval gbAtlas 5 10272 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_10368 : Interval gbAtlas 5 10368 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_10464 : Interval gbAtlas 5 10464 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_10560 : Interval gbAtlas 5 10560 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_10656 : Interval gbAtlas 5 10656 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_10752 : Interval gbAtlas 5 10752 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_10848 : Interval gbAtlas 5 10848 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_10944 : Interval gbAtlas 5 10944 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_11040 : Interval gbAtlas 5 11040 47 := block_range (n:=47) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 11087 := (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_96 bgb_5_192)) (concat (concat bgb_5_288 bgb_5_384) (concat bgb_5_480 bgb_5_576))) (concat (concat bgb_5_672 (concat bgb_5_768 bgb_5_864)) (concat (concat bgb_5_960 bgb_5_1056) (concat bgb_5_1152 bgb_5_1248)))) (concat (concat (concat bgb_5_1344 (concat bgb_5_1440 bgb_5_1536)) (concat (concat bgb_5_1632 bgb_5_1728) (concat bgb_5_1824 bgb_5_1920))) (concat (concat (concat bgb_5_2016 bgb_5_2112) (concat bgb_5_2208 bgb_5_2304)) (concat (concat bgb_5_2400 bgb_5_2496) (concat bgb_5_2592 bgb_5_2688))))) (concat (concat (concat (concat bgb_5_2784 (concat bgb_5_2880 bgb_5_2976)) (concat (concat bgb_5_3072 bgb_5_3168) (concat bgb_5_3264 bgb_5_3360))) (concat (concat bgb_5_3456 (concat bgb_5_3552 bgb_5_3648)) (concat (concat bgb_5_3744 bgb_5_3840) (concat bgb_5_3936 bgb_5_4032)))) (concat (concat (concat bgb_5_4128 (concat bgb_5_4224 bgb_5_4320)) (concat (concat bgb_5_4416 bgb_5_4512) (concat bgb_5_4608 bgb_5_4704))) (concat (concat (concat bgb_5_4800 bgb_5_4896) (concat bgb_5_4992 bgb_5_5088)) (concat (concat bgb_5_5184 bgb_5_5280) (concat bgb_5_5376 bgb_5_5472)))))) (concat (concat (concat (concat (concat bgb_5_5568 (concat bgb_5_5664 bgb_5_5760)) (concat (concat bgb_5_5856 bgb_5_5952) (concat bgb_5_6048 bgb_5_6144))) (concat (concat bgb_5_6240 (concat bgb_5_6336 bgb_5_6432)) (concat (concat bgb_5_6528 bgb_5_6624) (concat bgb_5_6720 bgb_5_6816)))) (concat (concat (concat bgb_5_6912 (concat bgb_5_7008 bgb_5_7104)) (concat (concat bgb_5_7200 bgb_5_7296) (concat bgb_5_7392 bgb_5_7488))) (concat (concat (concat bgb_5_7584 bgb_5_7680) (concat bgb_5_7776 bgb_5_7872)) (concat (concat bgb_5_7968 bgb_5_8064) (concat bgb_5_8160 bgb_5_8256))))) (concat (concat (concat (concat bgb_5_8352 (concat bgb_5_8448 bgb_5_8544)) (concat (concat bgb_5_8640 bgb_5_8736) (concat bgb_5_8832 bgb_5_8928))) (concat (concat bgb_5_9024 (concat bgb_5_9120 bgb_5_9216)) (concat (concat bgb_5_9312 bgb_5_9408) (concat bgb_5_9504 bgb_5_9600)))) (concat (concat (concat bgb_5_9696 (concat bgb_5_9792 bgb_5_9888)) (concat (concat bgb_5_9984 bgb_5_10080) (concat bgb_5_10176 bgb_5_10272))) (concat (concat (concat bgb_5_10368 bgb_5_10464) (concat bgb_5_10560 bgb_5_10656)) (concat (concat bgb_5_10752 bgb_5_10848) (concat bgb_5_10944 bgb_5_11040)))))))
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
theorem bgb_6_1824 : Interval gbAtlas 6 1824 71 := block_range (n:=71) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1895 := (concat (concat (concat (concat bgb_6_0 bgb_6_96) (concat bgb_6_192 (concat bgb_6_288 bgb_6_384))) (concat (concat bgb_6_480 bgb_6_576) (concat bgb_6_672 (concat bgb_6_768 bgb_6_864)))) (concat (concat (concat bgb_6_960 bgb_6_1056) (concat bgb_6_1152 (concat bgb_6_1248 bgb_6_1344))) (concat (concat bgb_6_1440 bgb_6_1536) (concat bgb_6_1632 (concat bgb_6_1728 bgb_6_1824)))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 5 zero,inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero]
def fullWord : Sig := 0xfffffffceeeaeaa8fffffffceeeaeaa8fffffffceeeaeaa8fffffffceeeaeaa8fffffffceeeaeaa8fffffffceeeaeaa8fffffffceeeaeaa8fffffffceeeaeaa8
theorem fullBound (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have low := boundgb certgb
  have lift := lift_ok (u:=true) (ms:=fixRows 32 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 5 zero,2,34)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 5 zero,2,34)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4278124270 * 2 ^ 32 + 4277071584) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_12933.Model.Repr at out
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

def mono : List Gate := [⟨.or,[4,5]⟩,⟨.and,[3,6]⟩,⟨.or,[3,6]⟩,⟨.or,[2,8]⟩,⟨.or,[0,1]⟩,⟨.and,[9,10]⟩,⟨.and,[2,5]⟩,⟨.and,[4,12]⟩,⟨.or,[11,13]⟩,⟨.and,[2,7]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124270 * 2 ^ 32 + 4277071584) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124270 * 2 ^ 32 + 4277071584) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_12933

open PEqualNP.Outside.L_meta_12933 in
theorem PEqualNP.Outside.L_meta_12933 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4278124270 * 2 ^ 32 + 4277071584) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4278124270 * 2 ^ 32 + 4277071584) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound allgb)
