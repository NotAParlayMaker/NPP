import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_13709.Model
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


end PEqualNP.Outside.L_meta_13709.Model

namespace PEqualNP.Outside.L_meta_13709
open PEqualNP.Outside.L_meta_13709.Model
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

def SBf (j : Nat) : Nat := [4, 5, 4, 6, 7, 7].getD j 0

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

end PEqualNP.Outside.L_meta_13709

namespace PEqualNP.Outside.L_meta_13709
open PEqualNP.Outside.L_meta_13709.Model
def s0K3 : Nat → Nat
  | 0 => 0x7
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s0K3 (i*3) 3
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s0K3 (4+((h/1+packedAt s0K3 (3+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffffbecf
  | 2 => 0xffffffffffffffffffffffffffffffffffdf73
  | 3 => 0xefbc
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xffffffffffffffffffffffffffffffffff4205
  | 2 => 0x2412
  | 3 => 0x1828
  | _ => 0
def s0Atlas : Atlas := ⟨3,rawDecor 14 s0Pos s0Neg, 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_13709
namespace PEqualNP.Outside.L_meta_13709
open PEqualNP.Outside.L_meta_13709.Model
def s1K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s1K4 (i*5) 5
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s1K4 (6+((h/1+packedAt s1K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x1ffe07fffff81c1fffff03fe0fffff007e73fc
  | 2 => 0xfffff81f81ffffe0f81ffffff0780fff93fccf
  | 3 => 0xe0ffffe001ffffff001ffc1fff800fffe38f0f
  | 4 => 0xfffffffe001fffffe0001ffffff001fc0ff0
  | 5 => 0xff00000000001fffffffffe000000001fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xc22231451041240529272126048a690c26315c
  | 2 => 0x444450c8229208a05a09464a9050a25490d4c5
  | 3 => 0x8aa8a2035525154b0512a9152d014ca9630b0a
  | 4 => 0x14d1049260365a729640c219ca658031d80ea0
  | 5 => 0x18e1c71c79c79f9ce79cf3818c4608c1ffe000
  | _ => 0
def s1Atlas : Atlas := ⟨4,rawDecor 61 s1Pos s1Neg, 0xfaaaf0a0faaaf000faaaf0a0faaaf000faaaf0a0faaaf000faaaf0a0faaaf000faaaf0a0faaaf000faaaf0a0faaaf000faaaf0a0faaaf000faaaf0a0faaaf000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_13709
namespace PEqualNP.Outside.L_meta_13709
open PEqualNP.Outside.L_meta_13709.Model
def s2K3 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 3 => 1
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 3 => packedAt s2K3 (i*4) 4
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 3 => packedAt s2K3 (5+((h/1+packedAt s2K3 (4+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffbfcffcf8fff873f3
  | 1 => 0xffffffffffffffffffffffdff39fff1c3ffc9f
  | 3 => 0xebfc1f3fe03f8f1c
  | 4 => 0xf3ffe03fffc00fe0
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffff4061010824892131
  | 1 => 0x2088281109124486
  | 3 => 0x1523506a42a52b18
  | 4 => 0xe0a1ab493064ec0
  | _ => 0
def s2Atlas : Atlas := ⟨3,rawDecor 27 s2Pos s2Neg, 0xeeaacc88eeaacc88eeaacc88eeaacc88eeaacc88eeaacc88eeaacc88eeaacc88eeaacc88eeaacc88eeaacc88eeaacc88eeaacc88eeaacc88eeaacc88eeaacc88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_13709
namespace PEqualNP.Outside.L_meta_13709
open PEqualNP.Outside.L_meta_13709.Model
def s3K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0xa006288e30000a5a480600bf43bd43be42bc42bf41bd41df31dd31be40bc40de30dc30
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x403040008ea98852c525065ca5205554430
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 4
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
  | 4 => packedAt s3K4 (208+((h/4+packedAt s3K4 (192+(h % 4)*4) 4) % 15)*5) 5
  | 3 => packedAt s3K3 (112+((h/1+packedAt s3K3 (108+(h % 1)*4) 4) % 10)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x3fff83fffff07e0ffffc1ffc1ffff03e79f3f3
  | 1 => 0xc3fffc1f83fffff0783fe1ffe1e07fffa63c9f
  | 2 => 0xfc1fffe003ff87ff803ffe1ffe007fc1c7cf1c
  | 4 => 0x1ffffffc0007ffffc0001fffff8001f80fe0
  | 5 => 0xffe00000000007ffffffffe000000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x8040888500808002904c02240229109408d131
  | 1 => 0x10891048252442502a11214921422528a22486
  | 2 => 0x895229034a480ca58426541654054a85454b18
  | 4 => 0x2a9c4252606d57394e83111b99960309f00ec0
  | 5 => 0x3318739c738e67ce773b998311180c31ffb000
  | _ => 0
def s3Atlas : Atlas := ⟨5,rawDecor 55 s3Pos s3Neg, 0xeaeae8e8eaeac8c8eaeae8e8eaeac8c8eaeae8e8eaeac8c8eaeae8e8eaeac8c8eaeae8e8eaeac8c8eaeae8e8eaeac8c8eaeae8e8eaeac8c8eaeae8e8eaeac8c8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_13709
namespace PEqualNP.Outside.L_meta_13709
open PEqualNP.Outside.L_meta_13709.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x21000030000000003eb538236002031cb171d2e913001e412883ca4e00001c030000150a62586800a0000c00010220000d01004c01130a0a800051192120002f006402b16020038304040952a000000c04080ff43bf43fe43fd43bd43fc43ff42fe42be42fd42fc42bc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fa30fd30f930fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x1040000002540000001f8d41200000000b170280000130000000000000000000014800000f49049001b8008d310a4007b0015c001c001fc8c4d4280042390014c0050198d4000008800000000000005a0006c00000000000000000000001580000004490c00584194896003993c00a23600000003780000440b97c007d1e00032184d14526154122c4e0016800008800000e20000000003f368a04a37001ac0002001d000002e00cc000000c0000006a60d2013d25c1c00000585e5e000000000001c80096001dc00000f99800231c2388a000f1548e222e84000a12a00084003a80098590018d0e0f000f80000000140013000006c1d160ec0000000000000000e9464000200000000000000000000080000190005b0612800091500102913c2180e56270012867000013c6803000f88a0023c00324c801203410090001a4e0c53e005000000004e98400703282000003b000007900000009200001360000210288c00008030081c00000000000000000800020000000000080c060a010080a00008180001000040201030040200000040000008000001018000400000080603004f94b439ea8e873e50d0e7aa921de94243bca84879f5350e78a4a1cfd45439e282873e5410ef4a021de54043bd28485795090a7aa7214f94a429ea8c853e5090b74a1214e94242dca84853d5310a7ca4216b948429ea88853e5010a7ca9994f55332bd286657950cca7ea9194f152329faa2653c544ca7ca8194f55032bb2886575510caf4a0195e540329ea9e833e52d067ca1a0cf55241bda828378505067ea6a0cf14941dba8a83bb5050678a0a0ee141419c282833e541067ca998cf55331bd286637950cc67ca918cf552319f2a2633d544c67ca818cf55031b7290636d520c6f4a018de540319faa6433c54c867ca910cf552219faa2433c54486bea690d714d21bda824378504867ca810cf55021af298435d53086f4a010de540219ea9c813e529027aa3204f94240af298815d531033ca6204f54c40cea98811d531027ca4204f544409f28081ba501027ca9984f55330cea1e613f548c278a9186e90230dc20461bb548c370a9185e54e30dda1c61b9438c37485186e10a30dda0c61b9418c27ea8984f15130cea1a61ba404c37080986ed5130dc2a261db534c37686987690d30dca1a61d9434c33286986e90930dc21261da324c3b064986ed0530dca0a61db314c3b262984f950309eaa0617a500c27ca9904f553209f2a4413d54882bca7105754e20dc204413f5448278a8906e101209faa0413c540827ca9884f55310dc206213f5484278a9084fd51109e2a2213e540427aa8085794c10aea98216e52042daa4086e10010
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x110010156390000380005d011000050000189806a4140000946374c58780302d7090035c004871d803a09b15004802a4ed0700007c03a3400200000002f60b519900c549464041b35600f1b420600006065c20200101001028184280c0088e98252d0e3860547439658e5090a1d6394242a658e5090b1a63942428e58e5090b1963942428658e5090a3860544428e983548ca3a60d51328e98252d065963141418758c50506996314141c698c50506396314141c658c505061963141418e181548c62c62551318e181544c63a60d53218e181548871a6054c40c654e501022e62d5230a658f548c2aa62d5230a658c548c23a6590a308e195418c21c6550d30a6592434c29a6550d30a6195434c2986250d30a6d85434c23a6590930a658c424c29b648c930a6590324c2d1610c930a658f414c2386550530a6593314c299644c530a658c40883195310220a658c404823a60d50208758c54082356115020a658c40c421d63152108e59440042996310010c654c40043295210010
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0xc2000000900349c08290420cb98c0a8885065ce6094b41832e7306a990c19731815488684b94c0a9881229ca6550d30910e4b22629841973983540820cbb2a6200218258d5210010
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
  | 3 => packedAt s4K3 (2420+((h/20+packedAt s4K3 (2280+(h % 20)*7) 7) % 88)*7) 7
  | 2 => packedAt s4K2 (502+((h/3+packedAt s4K2 (490+(h % 3)*4) 4) % 15)*5) 5
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xf0fffc0f0f87c7c7c3c3c7fe3c1e1c3f21fc93
  | 1 => 0xff0ffff00ffffff803fff87fc01ffffe3e30ff
  | 2 => 0xfff07ffff007f87ffc03ff87ffe01fc1c7cf1c
  | 3 => 0x7ffffff8007ffffc0007ffffe001f80fe0
  | 5 => 0xffff80000000007ffffffff800000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x1623446293498c41e0e0c4ce24d2449d20dc91
  | 1 => 0x204008802402000801050810400489200a2026
  | 2 => 0x42051124011400924402510289401284454518
  | 3 => 0x8aa624888409564aa68044532994009b00ac0
  | 5 => 0x8ccc438ece67267f33b3a66023118331ffb000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xfce8fce8fcc8fcc8fce8fce8fcc8fcc8fce8fce8fcc8fcc8fce8fce8fcc8fcc8fce8fce8fcc8fcc8fce8fce8fcc8fcc8fce8fce8fcc8fcc8fce8fce8fcc8fcc8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_13709
namespace PEqualNP.Outside.L_meta_13709
open PEqualNP.Outside.L_meta_13709.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x248060a30a000302380071658000268489b34001064e00ba91e10a2a4c54e803c711900a215804a25200007cc8d4404001608968005f040042ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x3c34f884f4bc2030dd68e8b92424014c00004400d4000158015c005400013d0c00980140000000b00000c4804070681490e4009c001c7d44d8a800ec008cb429305000cc012148604c5c00000010c00114e078087401500000d049550538c9186c1800fd6560000000005800010000651094f0391ca4a134052c2d28ac8801080c0000040208000a022000000216020616040002040a02020000000602020008057a5090ef2a121de94242bca84853e540ca7aa819734c832bb2886575510caf4a0195e540329f286833d54906f6a0a0de14141dba8a83bb5050678a0a0ee141419c282833e541067ca918cf55231b7a92636c524c67ca818cf55031b7290636d520c6f4a018de540319f2a4433d54886bea690d714d219f2a0433d54086bca610d754c21bd2804379500867aa3204f94240af298815d53102dca4205b54840bb2888175511033ca6206754c40d729081ad521036ca2204f54440daa888135511027ca0206e940409f2a6613d54cc2dca5185b54a30dc204613f544c278a8986e101309f2a6413d54c82bca7105754e20dc204413f5448278a8906e101209f2a6213d54c436a83886e103109faa4213c548427ea8884f15110daa0a213e540427aa8085794c10aea98216e52042daa4086e10010
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x1e380000190a805006a4c0088c028b1800000200a70010000000021600048002602e00080004004000007453254432c698c50507196314141ca988505072962141418e181548c6386055221c354d52103165354440c554d51103265254440c954951103306054440ca548408c2b16110230ac584404c3195310220ac58440882b16110120ac18141c42b161103108d19541442396510010c654c40043295210010
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x1004c08000018258d6214141a22e6302a220521721815110310a92c2204618454d6110220
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 44
  | 4 => 91
  | 3 => 25
  | 2 => 5
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
  | 5 => packedAt s5K5 (788+((h/14+packedAt s5K5 (704+(h % 14)*6) 6) % 53)*7) 7
  | 4 => packedAt s5K4 (2697+((h/30+packedAt s5K4 (2457+(h % 30)*8) 8) % 133)*8) 8
  | 3 => packedAt s5K3 (998+((h/8+packedAt s5K3 (950+(h % 8)*6) 6) % 52)*6) 6
  | 2 => packedAt s5K2 (249+((h/1+packedAt s5K2 (245+(h % 1)*4) 4) % 11)*4) 4
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x1fe3fffc0e3c78e3c71f8fffc7070e1e19fc93
  | 1 => 0xe1fc3e3ff03ffffc07e3f1c0f807fffe6640ff
  | 2 => 0x1ffc03fffc07f1ff803fe00fff80fe1878f1c
  | 3 => 0xfe00003fffff801ffffc0000fffff001f80fe0
  | 4 => 0xffffffc00000001fffffffff00000001fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x44288c0460489100c1048246c131224c089c91
  | 1 => 0x8410048809020040221108808024490224026
  | 2 => 0x94881491240940294802a41252500944858518
  | 3 => 0x4012a9224820125295480024a4a4a009580ac0
  | 4 => 0x991330038d32649f2693493800c0c191f76000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfeeafcc8feeafcc8feeafcc8feeafcc8feeafcc8feeafcc8feeafcc8feeafcc8feeafcc8feeafcc8feeafcc8feeafcc8feeafcc8feeafcc8feeafcc8feeafcc8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_13709
namespace PEqualNP.Outside.L_meta_13709
open PEqualNP.Outside.L_meta_13709.Model
def gbK8 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x3e24000014848c0076000000008e00361272620c7044902c006674026a5c340046547e4e2e5220000016640e421000786c3006880000263c00000000005e0000861e008a001a000000605a38924c4a00000000000a2a6e328050685608000000007c0000180058000048820022043a401c28007a021420008002840a080040000104000c0000218080017fd50057f54017f95005fd54015f55005fc5401ffd4c077f5300ff94c07fd53005f54c03fc53017fd0c03fe43017f50c03fc4301ffd4807fe52005f94807fd5201ff148077c52017fd0805fe42017f50805fc4200ffcc801fe32007f4c803fc3201ffd44077f5101ff94407fd51005f54407fc51017fd0405bf41017f90405fd41006f50405fc4100ffcc401fe31007f4c403fc31007fc8401fe21007f48401fc2101ffd4007fe50005f94007fd5001ff140077c50017fd0005fe40006f90005fd40017f10005bc4000ffcc001fe30007f4c003fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x284003bf99420085faca1000efc650800bbe32840039f1942007dfec81000afe640801f7eb204002bf1902007efea81003f7d54080017fb184001bf98c20005fac610006fc6308021bfa984000df54c20095fcc4100477e5208023be2904004bf98420005fac2100437f5108001bea88400fefd04200077a821003afe600800bbf2804005df1402002f7c8010017bc4008001f79004000fe88020007da4010003f920080097fb2e2003bf99710026fccb8800e7e65c401b7eb2e2004df59710004facb88012fc65c40097fb262002bf993100277cc98800abe64c40197eb262004ef593100057ac988012fc64c4019bfaa6200cdf55310025fec788006fe63c40017eb1e2004bf18f1006efea7880037d53c40097fb162000bf98b10005fac588012fc62c4001bf296200ddf14b10026fea3880137d51c4009dfa0e2004fd907100277a8388033f541c4001daa0e2000df9431006ef8a188003be40c4019de206200bbfd961002efecb080027f65840077f32c200bbf5961001df8cb080177c65840073e32c2006bfd921002f7ec908002bf64840057f3242006bf59210015f8c908017bc64840055e3242006dfd5210036faa908002ff63840037f31c2000bf58e1000df8c70802f7f5384001bea9c2000bfd8a10005fcc508002fd62840017e3142000df94a1005ef8a508026fd6184017bfa8c2000df546100377e8308003bd41840097f3042005df9421002ef8a108017be408400bde2042000fe8c210007f26108003fa2084001fc9042000fdc4210027f6210802aff6544001bfb2a20009fd951001dfcca8802afd65440077e32a200adf1951001cf8ca88026ff6444001dfb222000afd9110015fcc888026fd64440057e3222009ef1911001578c8880277f5444013beaa22000bfd8d1000dfcc688002fd63440037e31a200adfd4d10006faa688002ff62440017f3122000bf58910005f8c4880037e5244015be292200adfd4510006faa288027bf4144013fb20a2000ef5051004fea8288003b54144001bf282200adf141100077c8088027bc4044001fd1822000fe4c110007f44088003f92044009fd8822000fd84110025feca0800efe6504009bf32820039f9941003dfaca080137d65040013eb282004bf19410025fec80800afe6404009df3202002af99010045fac808013bd64040015eb202004bf19010046fea8080237d54040097fb182001bf98c10027bcc608006de63040017eb182004f758c10005bac608012fc630400fbfa982000df54c10025fec408002fe6204009f73102000bb98810005fac408013ed620400176b102004bf18810006fca40801f7c52040097f3082004dfd4410026faa208013bf4104009dea082006bf9801002efca0080177c500400bdf2002005ef10010027ee2008013fa1004001fa8802004fe44010
  | 1 => 0x73c5090037df9848005ef0c2400d5fecb180177f658c0013fb2c6003bf996300d5facb1800efc658c00bbe32c60039f196300cdfec91800afe648c0337eb246002bf192300cefea9180677d548c0037eb1c6001dfd4e3000efaa718002fe628c0017eb146000df94a300d6f8a518012fe618c0017eb0c601adfd4630006faa318067bf418c001dea0c6001bf9823002efca1180177c508c033fda046005ef9023002f788118067f8408c033dc2046001f7cc23000ff66118007f8308c0317fb2a6000dfd9530004feca9800efe654c0317eb2a6003bf195300c6f8ca9800e7c654c02f7fb226000efd91300057ec89800afe644c02f7eb226002bf191300bf78c89800abc644c02fbfaa26017df5513000dfec6980077f534c003ef29a6001df54d300c7baa6980035d534c003ef21a6017f750d30005fec498002fc624c001bf2926018df14930007bc6498007dc324c0017fb0a6004bf185300c6fea2980037d514c02fdfa0a6000ef5053000fbe6298003dd314c0037fb026000df941300c6f8a09805ffb404c001df2026017ef101300bff0809805fb8404c003fd9826000f78c13000fb86098007f8304c02d7fb2e4003bf997200b6fccb9000e7e65c802d7eb2e4000df59720004facb9000efc65c80257fb264002bf993200977cc99000abe64c80257eb264000ef593200057ac99000afc64c8025bfaa64012df55320005fec790006fe63c80017eb1e4001bf18f200b6fea7900037d53c8023bf2964011df14b20097dc859004bed42c80097f30e4000bf587200b6fea3900037d51c8025dfa0e4000ef50720007de4390003ed21c8001bf2864016df143200077c819004bbc40c802b7fb2c4003bf996200aefccb1000e7e658802b7eb2c4000df59620004facb1000efc658801d7fb244002bf99220075fac91000afc648801dbfaa4400edf55220005fec710006fe6388001ef31c4001b798e20005fac710003dd63880016eb1c4001bf18e200aefea7100037d53880277eb144000df94a200aef8a510012fe61880017eb0c4015dfd4620006faa31003bbf4188001dea0c400fbf9822002efca1100177c508800bdf2044005ef10220007f46110003f93088001f79044000fec82200a5feca900037f65480013fb2a4003bf995200a5faca9000efc6548029be32a40039f1952009dfec890003bf64480015fb224002bf9912009dfac89000afc6448027de3224002af1912009efea89004f7d54480017fb1a4001bf98d20005fac690006fc6348029bfa9a4000df54d20006fca4900537c5248027f72124013fb50920005fec290012fc6148029bfa8a4000df5452009f7e8290003bd4148001f790a4000fb48520006fca0900537c5048001df2024013ef10120007f46090003f93048001fd9024000fb88120085feca100177f65080013fb
  | 2 => 0x21025f8c7108977f5388401bea9c4222bf58a21006fca5108977c52884097f30c4204dfd4621026faa310813bf4188409dea0c4204fd8c621007ea6310813ef2188401fb90c4200bf98221005fac1108977c5088449de2044223bfd9521006feca908027f65484077f32a4223bf5952101df8ca9088f7c65484073e32a4222bfd9121015fcc89088afd64484057e3224222dfd5121116faa890802ff6348401efb1a4200b7d8d2100dfcc690802fd63484037e31a4200f718d2100db8c69088f7f5348401bea9a4200df9492111ef8a490803ee3248401f69924223dfd4521006faa29088bbf4148401dea0a4200fd8c521007ea6290803f72148409f710a4200bfd8121005f8c09088f7c5048445de2024204bfd942101dfcca108137e65084073f3284220bf59421026faca108027d65084097e3284204bfd9021015fcc810813be64084055f320421fbf590210277ac810802bd64084097e320421fdfd50210fefaa810812ff63084037f3184204f798c2100dbcc610802fd6308409eeb184200b758c21025f8c6108837f5308401bea984221bf9882108efca4108477c52084097f3084204dfd4421026faa210813bf4108409dea084204fbc8421027ec4210813ed2108401fa9084200bf98021027f4c010802fa60084017eb004204fe58021005f2c0108837c500843fde2004205dfd92500f4fec92807b7e649403dbeb24a01e9f5925002ef8c9280177f639403bbf31ca000df58e50004fac7280177c639403dbfa1ca01ddf90e500f6fa87280777c439400bbfb14a000df98a50004fcc5280037d629400bbe314a01edfd0a500f6fc852807b7d429403dbe214a01ddfcca50006fc65280037d329403bbe194a005dfd8650006fcc3280037d61940013eb0ca005df186500f6fe832807b3f419403dbf20ca01edf506500067a832807b7c419403bbf98ca000df8c650006fa63280777c3194001bf90ca000df88650006fa43280037c219400bbf304a0039f9825001ef4c12807b7f409400bbf204a01edf5025002ef881280173c409403bbf984a005df0c25002f7ecb200173f6590039df32c801cef5964002f78cb200173c659000bdfb1c801bef98e400077ac720017bc6390039dfa9c801ccfd4e400df7ca720073bd53900019ea9c801bef14e4002f7ec520003be6290001deb148005ef18a400e77ea520073be52900019f294801cef54a400e778a5200733c5290037df9948000ef8ca400077a652006fbc329000bdfb0c8000ef986400077ac320002bd619000bde30c801cefd46400e67ea320073be5190039dea8c8000cf546400e778a32006fbf3190001df18c8000ef4c6400df786320003bf2190001df10c8000ef48640007784320017be60900055f3048002ee982400e77ea120017be509000b9f284801cef5424002f78a12001
  | 3 => 0xe31aa22edfd0d5116efc86a88bb7d435445bbe21aa200dfd8951006fcc4a88037d6254401be312a2009f18951176fe84a88bb7e425445dbea12a22edf1095116efe64a88037e3254401be992a22ddf0c95101efec2a880e7f6154407bbb0aa22edfd05511767e82a88137e415445dbea0aa204df1055116efe62a88137c3154401bfb02a200df98151006fac0a88037c60544013e302a22edfd0151176fc80a88bb7d405445dbe202a22ecf1015116efe60a88b77c3054459dfb2a822cef995411667ccaa08b3bd65504019eb2a822cef195410077ec6a08afbe6350401deb1a822bef18d411677ea6a08b33f5350457df29a822cef54d410067aa6a08afbc5350401dfb128200ef989410077ac4a0803bc6250459dfa92822cef949410067ca4a08b3bd5250459de292822ccf1494115f7e64a0803be3250401de992822bef0c9410177ec2a080abf6150405dbb0a822cefd45411667ea2a0813be5150459dea8a8200cf5454102778a2a08afbf3150409de18a8200efd81410077cc0a0803bd6050401de3028200af181411677ea0a08b3be5050459dea82822cef1414116678a0a08afbf3050457de1828204bfd963101dfccb188137e658c4073f32c622abf59631026facb188027d658c4097e32c6204bfd9231015fcc918813be648c4055f3246229bf592310277ac918802bd648c4097e3246229dfd523114efaa918806fd638c403bfa9c6201df54e31005fcc518802fd628c401bf294622adf14a31007bc6518807dc328c4097f30c6204dfd4631026faa318813bf418c409dea0c6204f7cc63100fee6318813f4318c4017f3046200bf58231156f8a1188a7bc408c4517fb2a6203bf99531146fcca9880e7e654c4517eb2a6200df59531004faca9880efc654c44f7fb226202bf9913113dfac89880afc644c44fbfaa26227df55131025fec6988077f534c403bea9a6200bfd8931005f8c4988037e524c451be2926201f7cc931007ba6498806ff614c451bfa8a6200df5453113f7e8298803bd414c403fb98a6204f78c531027b86298807f4314c4017fb026200bf18131146f8a09889fbc404c403ef9826226bfd972108efecb908027f65c84077f32e4226bf5972101df8cb908477c65c84073e32e4221bfd9321015fcc990886fd64c84057e3264221dfd532110efaa990802ff63c84037f31e4200bf58f2100df8c79089b7f53c8401bea9e4211df94b2108ef8a590803ee32c8401f69964226dfd4721006faa390887bf41c8401dea0e4200bf98321005fac19089b7c50c8443de2064204bfd962101dfccb108137e65884073f32c4225bf59621026facb108027d65884097e32c4204bfd9221015fcc910813be64884055f3244224bf592210277ac910802bd64884097e3244224dfd5221126faa910812ff63884037f31c4200bf58e
  | 4 => 0x90000000060280082a00a084008030000000180a00e03c030320d0004018200000180400404a04c008020020080c00804a0080081601208400000006118000000000040200a0020340b00d0ae008000000000240001500406c0080000000c040100180240200300001c0100000e00c0080f04600c0c80201400c0880900e0003181202a02406008000090070190d600800003008020008010a60540480802a004000000000000180009e01009008042000078000080000b00100007c02800000000000370000000600300c0000080002a0480286800003801817010004070d77f6454c6b3fb22a635df991531aefac8a98d67d6454c6bbe322a601dfd8d5300cfec6a980f5f6354c03bfa1aa601df90d5300efa86a98077c4354c01bfb12a600df98953006fac4a98037c6254c013e312a635dfd09531aefc84a98d77d4254c6bbe212a601dfcc95300ef864a98037f6154c013fb0aa600df98553006fac2a98037c6154c6bbfa0aa635cfd05531aefc82a98d77d4154c6bbe20aa601dfcc55300ef862a98037f6054c01bf302a600df58153006f8c0a98027c6054c6bbfa02a635df901531aefa80a98d77c4054c6b9e202a601dfcc15300ebe60a98077c3054c23bfb24a4349fd92521a6fcc9290d37d64948693eb24a411df1925208efec7290cf7e6394801beb1ca4009f58e5208ef8c7290d37f4394867bf21ca434df50e5219ef887290477e62948073f314a403db98a521a6fe85290477e4294869bea14a411df10a5219efe65290477c3294823bfb0ca400df98652006fac3290027d6194823be30ca434dfd06521a67e83290d37e4194869bea0ca434df1065219efe63290cf7c3194823bfb04a400df98252004fcc1290037d6094823be304a434dfd02521a6fc81290d37d4094869be204a434cf1025219efe61290cf7c30948657fb2c6411dfd9632004fecb1900efe658c8657eb2c6403bf1963208ef8cb1900e7c658c8637fb246402bf9923218dfac91900afc648c863bfaa46431df5523200dfac7190077f538c803bea9c6401bf98a3208efca5190477c528c803ef9946401fbcca3200fd86519012fe618c8017eb0c6432dfd463218f7e8319007dc318c8017f3046400bf58232196f8a1190c7bc408c803ef9846430bfd9532006feca990027f654c8077f32a6430bf5953201df8ca990c37c654c8073e32a642fbfd9132015fcc8990befd644c8057e322642fdfd513217efaa899006ff634c803bfa9a6401df54d3200dfec4990037e524c861be2926401fbcc932007bc6499007dc324c803f61926400bfd8532025f8c2990c37f514c85fdfa0a6401f7cc532005fec099002fc604c861be282642fef10132176fec8a88ba7f645445dbf322a22edf59151174fac8a88bb7c6454401bfb1aa2009fd8d5116efcc6a88037d635445bb
  | 5 => 0x14c9a21100d995690e05c9519a98b101f0001e79f98f21a711f8cc0e09cb0001ee9551d19af80917e9462101c70991cd0290619dba01a0b10c8a30bf1318b389a1e00000501250000000c61fe8000e40c511487880000008a10f9bc82e82d92681108b07487b1230050dc00001d17718c1561490000b40940000d317806c9409bd8000001a49978000d206b9a511817f9939ee13e93f8a184c84316880007600003d18409d9a28541f08001eb15495583597380002e1ab18d0000b492980000009380019a8f619a0fc1309ac1369378468f516f17915b8000ef8b09e38360001418fb89f1249e11b894c0728001af0000199d31f411e00012a13a850a0d02b8001f38270000b68001b39d39e99089da1138000001681dc86980017485985a9ba8000000000d700010d0709968c00d11901c300003f07f09b8000000228000000e895100000000008f05f00014b0f312a97f0ec8001430b300001300c16e1438b8800000080a0500a13b0000be1a11032010000879338798d01c38f290015d19320803798e12791c9488000001d582995e8510139c41d097b20c03f84f96d20d9801ea85d98d9a19ff0000000141bf9741df9570e200010e96c8fe1f19988a28a79761038ea00008298f9e90771160e70989e090689789010b9d998f1bd1ed9db00011b82a10094e85e96100014400004f0260000000000001d899f0a59508241b681e08b8c29b78bf84c0058ce83e0429b5a0b80000d0931fd8648e680001680000001784d0928000001470000e61ae8000000000000a980006400000000014d80016b00019e94d00018c95b01e9b98029360d89fb8000888088279261831fb0000b58768001798000520ac0000000000000000ce0af1f799e03c9a3197182a0891685b800159047a058ab0861c59ca1df04908d1620269ce83415f80014595280000009f8000000000959b31288cb0000000001020b70001ec80000000011204180003aa0a9c01b90f10ad9a3a079301220b01bc0211ac83008e0078250310a08018d58fb0d09500750608ee07800009518186b0ef0668600030000520000100700201000000032038000080080000980a0060380000100200c0a80b000004008060020000080302000000802006020000020060280300f0000140080002603804812006050220010000000680401a0180580200001c00000006014038060020000b8000e2038048220020000103600002801005000018018000000002d00000c000018000000400400900a000110120020040000000603400011006000158050240200001a04e010000020040040000600a004010140020401280500400006001000090040180002080e000002078000070040140180c00c01c0002100400000819004010000120120000385200000c0201200c01014802024028000080040
  | 6 => 0x328001c68e10000351d796415c9b18001608000128001078d69451779e60ba8481631420aa0471f20410fa8779639ab80011b0eb16280000000018200000013a00613e0000620851060919e307d93299208c1cf19501212c94785914a03c1d01bb1750910000258691ec12d8720d19899110000840e7a111538e81ae12813901c8001348f902483a00b16e80004d9188a68e28001e28000ea80e9109f71690049e68c19b51ed1948fd1d68101940000000560001bf0000160461210611598569f000e09b00f9c09170320081b080000006da0f9650f99a408a84503b1b72099530209fe1658188bd0368bd8920f58e31028a414f9d40870ff1540b79c89661ffa049311b610b05b08c85c1fa80000004b80000000000000011d0fe99b00013c0218000538f68000000001070ca94980690906e0000001de17c0791dd04080000010d92e8660c49810cd0d40001f60001e800015214f0e01cc80000000006f83300019901d80103886e81b1c98000000de11910a971009a0419b8689911cd8cd9ef16799c1140a20d297d8318b62029b815c00012907c92c1789c90001850001a812b1e58d48c982b1019a081187409498a98b9259fd13993f10504a87c1869fa07f8c41ad09c0810969320839578fa1c28d512282d0570549c18e48530c80881cba0c8970f70020230cc8f788208304589d06296a0fc9e50448008370c10a48998000f08a91178bc96a8e38001380000338000001da8040000559480ac81f8cf04887a9359980b19c48731a58ae9699b01be12416b8701a6a001f88801d80869fc98b0421dc0000c70ab85d05f9a61809960000e59618000aa98587395e1e21958c08b986795a0a38a820319197206a1048001d51a79b108d9880589f69388f019d98898711306f06a8bc09c9151d102f1208b213d0442071e70fd89090f1468961c80000bb8000529d291e8bea0e0ca06700700000000000012d10a0000000000758dc8ad20a0000001b484000001b8650ed0ae0c58a50ed8000000221768db1ca95884e1669758f889a92020680d8d399d1aa10813711c1ba01817000f01a9be92f03492716f9ea0b90191159129849cf80014007d00001a0000001c20000d79d48e999085a0f80000000c380002f8c880a8000ff95a9ad964a0215d97a89e9d61e191da0e97e1d71f100017080006c0550a60201448d80438000ba0c784a0d906d1f91f482800012b8c913d98e88183b9eb80020914e1b289800300001c03915f00c91a88f8890b81fc0e514b9732108e18001f52060000001d90000a882a8da0518f495805e0dd8f414287e9f58148dd06804997a1351f80898630c31b40238039e402c0cf9098eb97c9f30df87a0398c693b8de96013306396d810a0f19297183e8150df10401702c90c0000848859119198001ce0718a007b80016c
  | 7 => 0xee8ec1011e89de82888e80b8b29ef97b8710b51239a89a90380308cb84e9729dd9f29861cc14a9891340da9c118a1218f38e90f189e12e14119c8bb0a11c50d60af905857a0087e04b0a71838659aa91a1b21879bb99993c9672039e481597d0db92f91f1c60580000000001a000019f9c78c200003d9d20
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc75d8d100047f7558d1001c7c7558d10004bf7458d10014bc7458d10004ef7258d10004ec7258d100047e7654d100047c7654d100063f6454d101ae3c6454d1001c7e75d89100047d75d891001c7e75989100047d7598910014be7498910004bd74989100047f755891001c7c7558910004bf7458910014bc7458910004df735891000cdc735891008c7c75189100047e769491008c7c76949100063f64949101a63c64949100057a709491001c7c76545100063f64545101763c6454510005787054510027701054510014bc76505100063f65505101663c65505101b7375150510007355150510005b87050510016b7765051004db47650510016b47650510014b476505101b73675505100073575505100073765505101b73465505101b73753505100073553505100073652505101b7345250510007b3705051002db47050510007b07050510026b76050510027b360505101b734505051006c7e76941100063f64941100f63c6494110007354194110064be76901100063f65901100e63c65901100ceb8648c110007b1418c110024f8764c1100beb8644c11000759534c110007b1414c110005d97388110007b14188110024f87648110007b14148110024f6768411002db774841100047f74594100047d74594100047f735941008c7c72594100247f71594100247d71594100263f41594100263d415941002c7e705941002c7c705941002e3e405941002e3c40594100063e75590100063d75590100063f53590100063c5259010024bf7159010024bd71590100263f51590100263d515901002cbe705901002cbc705901002e3e505901002e3c5059010026b7105901001c7e7558c100065f5358c100065e7558c100065d7558c100065f5458c100065d5458c100065c5258c100265f5158c100265d5158c100269f4158c100269d4158c1002e5e5058c1002e5c5058c1002e9e4058c1002e9c4058c10026da1058c10026d91058c100047f7654c100047d7654c101ae3e6454c100063d6454c1000e5e6354c100065d6354c1008c7c759881008e6c529881008e6f759881008e6c75988100066f54988100066d54988100066f53988100066d53988100266f51988100266d5198810026af4198810026ad419881002e6e509881002e6c509881002eae409881002eac40988100047f755881001c7c75588100066c52588100066f75588100066c75588100066f54588100066d54588100066f53588100066d53588100266f51588100266d5158810026af4158810026ad415881002e6e505881002e6c505881002eae405881002eac4058810026ea1058810026e9105881008c7f76948100047d76948101a63e64948100063d649481019e5e63948100065d639481008e6e62948100066d6294810004f77644010006b5644401002f725044010
  | 1 => 0x1200e63c65901200ceb8648c12000cf8764c1200beb8644c12000759534c12002c7f74d94200047d74d94200047d73d942008c7e72d942002e6e72d94200047d71d94200063f41d942002c7e70d942002e7a70d942002e3e40d942002e3c40d942002c7c75d8c200047f7558c2001c7c7558c2002c7e7654c2002c7c7654c2000e5e6354c200065d6354c200047f755842001c7c755842002c7c76544200267661544200067561544200063f65504201663c6550420026b66150420006b5615042002db87050420004ef764802002f6a5048020004fb764802008f6a52480200047f74597100047d74597100047f735971008c7c72597100263f41597100263d41597100063c40597100063e75593100063d75593100063f53593100063c52593100263f51593100263d51593100063c505931001c7e7558f100047f7654f100047d7654f101ae3e6454f100063d6454f1008c7c7598b100047f7558b1001c7c7558b10004df7358b1000cdc7358b1008c7f7694b100047d7694b101a63e6494b100063d6494b10025b77650710046b776507101bf3675507100073575507100273665507100273565507101bf3753507100073553507100073652507101bf34525071002db470507101bf3450507100547d76943100f63e64943100063d649431000735419431004cbd76903100e63e65903100063d659031002c7f74d96100047d74d96100047d73d961008c7e72d961002e7571d96100063f41d961002e7a70d961002e3e40d961002e3c40d961002e3f75d921002e3c75d92100063f53d92100063c52d921002eb571d92100063f51d921002eba70d921002e3e50d921002e3c50d921002c7c75d8e100047f7558e1001c7c7558e10004bf7458e10014bc7458e1002c7e7654e1002c7c7654e100063f6454e101ae3c6454e1000e5e6354e100065d6354e1001c7e75d8a100047d75d8a1000cde73d8a10004dd73d8a1001c7e7598a100047d7598a10014be7498a10004bd7498a100047f7558a1001c7c7558a10004bf7458a10014bc7458a1002c7c7518a1002c7e7694a1002c7c7694a100063f6494a101a63c6494a1002d7a7094a1002c7c76546100063f64546101763c645461002d78705461002cbc76506100063f65506101663c655061004eb5615061002db87050610024f9768c21002eb8648c2100beb8644c21000759534c210024f97688210005d9738821002eb764c421001c7e76d95100063c64d95100047f74d95100047d74d95100047d73d951008c7e72d95100547d71d95100063f41d951002c7e70d951002c7c70d95100063c40d9510014be76d91100063f65d91100063c65d91100063f75d91100063c75d91100063f53d91100063c52d911004cbd71d91100063f51d911002cbe70d911002cbc70d91100063c50d911001c7
  | 2 => 0x4bc76505300063f65505301663c65505300071d5350530005b87050530024dc764c5300055d754c530026d4614c5301d798404c5301cc7e76941300063f64941300f63c649413002f38409413002f5830941301c4be76901300063f65901300e63c65901300071d53901301c5ba709013002d5f758c13002f98408c13001c7f76597200063e64597200047f74597200047d74597200047f73597200047f71597200063f41597200063c4059720014bf76593200063e65593200063d65593200063e75593200063d75593200063f535932008e3e525932008e3c5259320004bf71593200063f51593200063c505932001c7e75d8f200047d75d8f20014be74d8f20004bd74d8f2001c7e7558f200047f7654f200047d7654f201ae3e6454f200063d6454f2008d6c7254f2001c7e7558720014be74587200047f76547200047d76547201763e64547200063d6454720004bf7650720004bd76507201663e65507200063d6550720005b87050720024ed76c87200a47d76943200f63e64943200063d649432009cbd76903200e63e65903200063d659032001c7f76596200047f74596200047d74596200047f73596200047f71596200063f415962002c7e705962002e3e405962002e3c405962001c7e75d8e200047d75d8e20004dd7698e200065e6598e200065d6598e2001c7e7558e200065f5358e2000cdf7658e200065e6558e200065d6558e200065e7558e200065d7558e200065f5458e200065d5458e200065c5258e200065f5158e200069f4158e2002e5e5058e2002e5c5058e2002e9e4058e2002e9c4058e200047f7654e200047d7654e2000e5e6354e200065d6354e200a47d7694a2019e5e6394a200065d6394a2001c7e75586200047f76546200047d765462016e5e63546200065d63546201663e65506200063d655062015e9e63506200069d6350620026b66150620006b5615062000cf9768c22000eda634c22000759534c22001c7e76d95200063c64d95200047f74d95200047d74d95200047d73d952008c7e72d952008c7c72d95200047d71d95200063f41d95200063c40d9520014be76d91200063f65d91200063c65d91200063f75d91200063c75d91200063f53d91200063c52d9120004bd71d91200063f51d91200063c50d912001c7c75d8d200047f7558d2001c7c7558d20004bf7458d20014bc7458d20004f77158d20024f47158d200047e7654d200047c7654d200063f6454d201ae3c6454d200056c7254d200ac7e76949200063f64949201a63c649492001c7c75d8520014bc74d85200047e76545200047c76545200063f64545201763c6454520004be7650520004bc76505200063f65505201663c6550520024ec7648520026e461485200b47e76941200063f64941200f63c6494120094be76901200063f659
  | 3 => 0xe6054e401af3a6054e400df1f3054e400e53e7598a400053d7598a400053f7558a400e53c7558a4002e3f6558a4002d3e7694a4002d3c7694a400053d7394a4021d3e7294a400e72e7294a400053d7194a4002d3e7094a401a63e6094a401a73a6094a400053f758ca400e53c758ca400053f754ca400e53c754ca400e53e75986400053d759864002eb761986400053f75586400e53c755864002e3f655864002e3c65586400063f75586400063c75586400063f53586400063d53586400063e52586400063c52586400063f515864002cbc705864002e3e505864002e3c505864002eb6105864002eb4105864002d3e765464002d3c76546400053f73546400053c72546402153f71546400e73771546400063d615464002d3c70546401763e60546401773a605464002cbe768c640004bd768c6400e53e758c6400053d758c6400e53e754c6400053d754c6400053f75c86400e53c75c864002cbe7688640004bd76886400e53e75886400053d75886400053f75486400e53c75486400059f73486400dd9c734864002cbe7608640004bd76086400e53e75086400053d75086400dd9e73086400059d730864002dba7008640005b9700864002c7f74d96300047d74d963002e5d73d963008c7e72d963002e6e72d96300046e72d963002e6d72d96300047d71d96300063f41d963002c7e70d963002e7a70d963002e3e40d963002e3c40d963002e5f30d963001c7e7598a300047d7598a30014be7498a30004bd7498a3008e6c5298a300047f7558a3001c7c7558a300066c5258a3002c7e7694a3002d7a7094a3020f384094a300047f755863001c7c755863002c7c76546302073840546300063f65506301663c6550630026b66150630006b5615063002db8705063001c7e76d95300063c64d95300073840d95300047f74d95300047d74d953002c7f73d95300ec7d73d953008c7e72d95300047d71d95300063f41d95300063c40d9530014be76d91300063f65d91300063c65d91300063f75d91300063c75d91300de3f53d91300de3d53d91300063c52d9130004bd71d91300063f51d91300beba70d91300deb970d91300063c50d913001e5f7654d300c55c7654d3001e5c7654d3001c5c7654d301fd5f7454d301fd5d7454d300071f6454d301f71c6454d300055c7254d300055f7154d301f71f4154d300075b7054d3002d5c7054d30007587054d3000e5f6054d3000f5b6054d301f75b4054d301f71c4054d301f7584054d301f7184054d3001c7e75d89300047d75d893008c7c75189300047e769493008c7c76949300063f64949301a63c64949300057a70949301ef3840949300055f758c9301e798408c93001c7c75d8530014bc74d85300047e76545300047c76545300063f64545301763c64545301df384054530004be7650530
  | 4 => 0x8c210065f5358c210065e7558c210065d7558c210065f5458c210065d5458c2108e5e5258c2108e5c5258c210265f5158c210265d5158c210269f4158c210269d4158c21026cf2158c21026d62158c21026cd2158c210065c5058c210069c4058c210047f7654c210047d7654c211ae3e6454c210063d6454c2100e5e6354c210065d6354c2108d6c7254c21004f77648421006d5634842108f66524842102c7c759802102cbc749802102e78509802102eb8409802102e7b759802102e78759802102ebb749802102eb874980210067b54980210067954980210067b539802100679539802108e7a529802108e7852980210267b5198021026795198021026bb4198021026b941980210047f755802101c7c7558021004bf7458021014bc7458021006785058021006b840580210067b7558021006787558021006bb7458021006b874580210067b54580210067954580210067b535802100679535802108e7a525802108e7852580210267b5158021026795158021026bb4158021026b94158021026eb2158021026e9215802102e5c6358e500047f7458e500047d7458e500ee5e4358e500065d4358e5008c7c7258e500ee5c3258e500047f7158e500063f4158e500ee5f3158e5002c7e7058e5002c7c7058e5002e3e4058e5002e3c4058e5002e5e3058e5002e5c3058e500f53e7498a500053d7498a5008c7f7498a5008e3e7498a500047d7498a5008e3d7498a500043d7498a500047d7398a5008e6e4298a500066d4298a500066f3298a5008e6c3298a500047d7198a500063f4198a5002c7e7098a5002c7c7098a5002e3e4098a5002e3c4098a5002e6e2098a5002e6c2098a5008c7f768ca500065d638ca500047f764ca5002c7c764ca500f53e74986500053d74986500047f74586500047d74586500047f735865008c7c72586500063f415865000676415865000675415865002c7c705865002e3e405865002e3c405865002e76105865002e7410586500063e76506500063d76506500063d63506500063e62506500f53f71506500f73771506500073661506500063d615065000735615065000635615065002d3c70506502263e60506501673a605065002c7e768c6500047d768c6500f53e748c6500053d748c6500047d764c6500065d634c65008c7f76c865008e6e62c865002c7e76886500047d76886500f53e74886500053d74886500047f764865002c7c76486500055f73486500ed5c73486500066e624865002c7e76086500047d76086500f53e74086500053d74086500ed5e73086500055d730865002d7a70086500057970086500053f7558e400e53c7558e400beba6058e4002d3e7654e4002d3c7654e400dd3f7354e400e71f7354e400df1e6354e400071d6354e400053c7254e400053f7154e4002d3c7054e401c63
  | 5 => 0x65f73595310066f725953108c7c72595310066c72595310046c725953122c7f71595310067771595310063f415953102c7c70595310063c405953116e5f305953101c7e75d89310047d75d89310066c52d893101c7e75189310047d7518931014be7418931004bd741893108e6c5218931004fa7018931004f970189310047d76949310055d7394931005757194931024dc764c93101c7f765453116c7d76545310055f73545311663e65505310063d655053102794315053101c7e75d81310047d75d8131014be74d8131004bd74d813101c7e75181310047d751813108c7f74d97210047d74d97210047d73d972108e6e72d972108e7571d97210063f41d972102c7e70d97210063c40d972108c7c75d8f210047f7558f2101c7c7558f2108c7e7654f2108c7c7654f21024ed768cb2108c7c765472108d6c72547210276621547210063f65507211663c655072101c7e75983210047d759832100cde7398321004dd73983210047f755832101c7c7558321004bf7458321014bc74583210047f74596210047d74596210047f73596210263f41596210263d415962102c7c70596210063c40596210063e75592210063d75592210063f53592210063c52592210263f51592210263d515922102cbc70592210063c505922101c7e7558e210047f7654e210047d7654e211ae3e6454e210063d6454e210056c7254e2111c7d7694a211a63e6494a210063d6494a2108f6652c862102c7c759822102cbc74982210047f755822101c7c7558221004bf7458221014bc745822101c7e76d95210047f74d95210047d74d95210047d73d952111c7d71d95210063f41d952102c7e70d95210063c40d952101c7c75d8d210065f53d8d2100cde76d8d210065f65d8d210065c65d8d210065f75d8d210065c75d8d210065f54d8d210065d54d8d210065c52d8d210065f51d8d210069f41d8d210065c50d8d210069c40d8d210047f7558d2101c7c7558d21004de7618d210065f6518d210065c6518d210047e7654d210047c7654d210065f6354d2100e5c6354d2112c7e76949210065f639492119e5c639492100ecc638c921024ec764c92101c7c76545210065f635452116e5c63545210056c72545210276421545210063f65505211663c65505210069f635052115e9c6350521027a4215052100ed4638c521007c6328c52100cf4764c521007c5324c52101c7e75d81210047d75d8121014be74d8121004bd74d8121006b840d812102c7c751812102eb840181210047f74594210047d74594210047f735942108c7e725942108c7c72594210263f41594210263d415942102c7c70594210063c40594210063e75590210063d75590210063f535902108e3e525902108e3c52590210263f51590210263d515902102cbc70590210063c505902101c7e755
  | 6 => 0xd74189510047d73189510066f321895108e6c32189510063f411895102c7e70189510063c401895108c7c768c9510065f638c9510047f764c9510047c764c9511753e74d81510053d74d81510073840d81510557571981510053f74581511753c745815105d77715815116d5e73181510055d731815100738401815102c7f74181510047d741815102e5e73181510047d731815102e5d73181510045d731815108c7e72181510063f41181510067b401815102e3c401815102e78401815102e3840181511663f76595410053f73595410053c72595412153f71595410073771595412153771595411763f61595411773761595410073b70595410053c70595410073870595410053870595411653e75d8d410053d75d8d411653e7558d4123db77158d410053f7654d410053d7654d4115d3f7354d411671f7354d410053c7254d410053f7154d412363f6154d411af376154d410053c7054d4115f1f3054d411653e75d89410053d75d89410063d65d89411653c7598941115b571989410053f75589411653c75589410063d65589410059f735894115d9c735894110db77158941005bb7058941005b870589411653e75189410053d75189410053f76949410053d76949410053d739494121d3e72949411672e72949410053d71949411a63f61949411a73761949410053e70949410053f758c9411653c758c9410053f754c9411653c754c941005b7714c941025b4714c9412153f76545411753d76545410053f73545410053c72545410253f71545411673771545410263f61545411773761545410053c70545410273710545411653e75d81410053d75d81410073850d81411653c75981410063e65981410063d659814104db571981410053f75581411653c7558141035b771581411653e75181410053d75181410063e65181410063d651814115d9e73181410059d7318141005ae7218141005ad721814100738501814102e3e751814102e3d751814102e9e731814102e9d73181410063f53181410063d531814102eae721814102ead72181410063e52181410063c521814102eb571181410063f51181410063d5118141006bb501814102e3c501814102eb8501814102e3850181410047f74596310047d745963108c7c72596310263f41596310263d415963102c7c70596310063c40596310063e75592310063d755923115e3f535923115e3d53592310063c52592310263f51592310263d515923102cbc70592310063c505923108c7c7598a31024f67198a310047f7558a3101c7c7558a3108c7f7694a310047d7694a311a63e6494a310063d6494a31005757194a3102c7c759823102cbc74982310047f755823101c7c7558231004bf7458231014bc74582310056c725953122d7771595310047f74595310047d745953116c7f7359531
  | 7 => 0xa02000809008000028000000180980202a0440200f00400401000024070028010120340802c0020780101f00c0000281c008008020000040580401c00200c0381f0460040380907a00000000008040008050000100c8160000040080b00c000098041855d73989531955f73589531ad3e74189530053d741895308c7f741895308e3e74189530047d741895308e3d74189530043d741895301c7d731895308e6e321895324e6d32189530047d71189530063f411895302c7e70189530063c401895324e5f30189530047f74d85530047d74d855301c7d73d855308c7e72d85530063f41d855322e7631d855302c7e70d85530063c40d855322e5f30d85531ad3e74985530053d74985531455d73985531555f73585530056f72585530056c72585531ad3e74185530053d74185531ad3e74d81530053d74d81530c55d73981530056e72981530056d72981530053f74581531ad3c74581530d55f735815302c7f74181530047d741815301c7d731815302e5d731815308c7e72181530047d71181530063f411815302e3c401815302e5f301815302e7a30181531ce79301815308e5c6358e520047f7458e520047d7458e5208c7e7258e5208c7c7258e5208e5e3258e5208e5c3258e520047f7158e520063f4158e5219e5f3158e5202c7c7058e520063c4058e521a53e74986520053d74986520047f74586520047d74586520047f735865208c7c72586520063f415865208e77215865208e74215865202c7c70586520063c405865219d5e73982520055d739825200738409825202c7f74982520047d749825202e5e73982520047d739825202e5d73982520045d739825208c7e72982520047d71982520063f41982520067b409825202e3c409825202e78409825202e38409825208e7b209825202e7820982520053f74582521a53c745825200738405825208c7f74d96320047d74d963208e5d73d963208c7e72d963208e6e72d96320047d71d96320063f41d963202c7e70d96320063c40d963219e5f30d96320047f755863201c7c755863201c7e75982320047d75982320047f755823201c7c7558232004bf7458232014bc745823201c7e76d95320047f74d95320047d74d953208c7f73d953219c7d73d95320047d71d95320063f41d953202c7e70d95320063c40d953224c7e769493201c7c75d853201c7e75d81320047d75d8132014be74d8132004bd74d813202c7c751813216e5e63d8d510047f74d8d510047d74d8d5108c7e72d8d5116e5c32d8d5101c7d71d8d510063f41d8d5116e5f31d8d5102c7e70d8d510063c40d8d510056f7258d510056c7258d51245777158d5111d7571989510055f735895116d5c73589511357771589511753e74189510053d741895108c7f741895108e3e74189510047d741895108e3d74189510043
  | 8 => 0x151734e0440d53b70b03bf00004f23500042936c10a4090000001a33f400000026924c1464c03440fa27446641804d2414ab0ef1331873cf0000e233c0005394942670a219e1a843500019d3bc3581445071cc4e112b14e3ee0bf27537132d0572fd01b09847407a2b22c72013eb37c0002580380002031592312932c10002ae32450948d1fd00a4634730b42dd21035e17d00023a4401c20001033073e83510003de52c0df00051d2910f50990001cb2f209a22000000028607e1c84883324670963b34d61911fc27a3662bd0183062c545a1e90004ed2d21a103711c00046a2640a526128d4ee43f3a41072091504ba0434432a331c2a14520005293204554d200004a0263d30000a72150280003b046c4874320000004100000000000000000f334300000000007637a4e52954fc1f830400000020e1b903200000000011025e4c939b47f00000022300000039e4fd12f00008400029f0045201d106c00051938f24935d1360004a60004120004b227b4d830d0000003ea3102794854ff3e90005164dd3f20222962d81d22de47b2330b200011230852e00047205f4992890254f12ec0d03652b54ca11d0915223a307223d31215406a54252151c0004de1da0873a648f2a803101e03c4cd0cf3914f709e49e0d214900042b2391a419007000027342020b31714131117545900000046f2ad3fd00b00000300a0080300002c0000002c02000800800000000018320060040d80a000000028000200280080400001c0001101a008000030340201701303a00c0280c0040200e8070300280c0040060000101a0160040800001c00c04005064058000010100100080100204802001026000038010020500a004058058000020020000200000a000048080000000000400a0a0288800080140880200a0000300900e004038040640001780205c00808000018000010060000002401f0180340a8010080040000000200800018050074078090120100400600201c0f82300004c090250000000202b0020440101102000000800000014190080040000081801c0000001f0000001081500400c010050760480200e00a0380100001a0100081d0000180800400a0000000100400402002000010000240320940581008e0100300200600001809012104008140000280000a01a0000000b02e02c178010000380d01101200800000004008160000140080280700803c1300002e06c0000203e000088000000080780c00c018018040000c80400000600c01800010014000020420d40100f0040040100304807c1280000200c1080b000028000020000040280600c008000010a000003001024008040100140040301a0040200000b0060000280000c0000280d0420005982c01001c2200101a0041000005a01009002024028000080160a8010000020700000500
  | 9 => 0x3b548c1203734be0ff3363c60002f428c0e10b32162ba03951b5064bd2211932b734b04e00050316600016b0863aa19f4303e200015c0002bc4d40004b447500008f0000121f10001ac4c22462b40004b11c63250002e14f30000004f800015f00013b0000000000004374fb0002f300038a0003f61af3cd1c048107700016700000024b0003d62ac00037b53543b4a81760003ca00000047149f2240001ea45022b05d4110b54c615a0002921e411a1813002e94f03e44b02e853a0003a51ef11e0004952d50000f44d70000de0000d724000000000000000010f0002e250f1ee1315265130fe3852eb27227c3194a542146408e0d144c3b837d44522507b2df00000035200003e0001150004dc00028e4a725f0fb2ee40d47c13001d38d4685380880003c24762974044e840000c2a74464cc0001371924280000005404d04a04c715753e0004af2d310002000025b1f617b02a4931b709700000043d06e3dd1c53473af0403c51581652f05021ae1624031740bc31e4382f807d1be21d15b1aa4ea53c0000000730003283e73611350004020000002ef3a007f52822909b00023b2c33ff2c901f0c40a100015d0d810e18a1ba1e14e300050c0fc1a23d02c241900033f00006b0274e91ff4420003ed0cb46510c26017f4e226f44f0000ea1642763fc3603500a63c335f19c17a46b08104515e42748915210219933130230909032f1b414b1221ab0170151e84b80002ce00050a0aa5310a852f1280002362e74440003f510b33940c0b91062cd0002dc2f708034f38413253402d3da32944b3f905b41723f2e60ae32e0001173ce2ff11b31f00320f4973cb0c93d45230114c32a02304ec34a34836b34d50015619b3763374ae53636e0dc32c1263d53cc05521c0c23d91782770001181a950e0fd4f545c0342084563880ac0e35120144a313a0002904693453673be1160004800c31f00001fb00014a4cb06702419826d39a10100000011f01900d17740a0530005330002780003560d91712cb49c25500000000000000039818f3260000002e30af0000000002db0000003860000000004df5182272a506f2683833901c400000017c2e50002c60002d11344ef4601e54a904808a1b00003a753b1843c80001e028a1e32cc2b93ba24513c45f41e28b02336910409229c36f40613f35c0890f63b11d80f744a41b3ad36a0cc02f2073801a55442281434a12b824f4363a20103db0e019a52d12342f22e2c80ba25d00009d0c50000004770003fa00038e3754792f90461b627e02b3140f833a20212700023e38b19748b1eb05836453229d09c0063a929942c3c93683814241dd12e18e3fb18927f18b2d03bd1851693e13221684ad3b61ec2883892be21f1b14512ed37048a0002441bb3b226c4330db0713550a93954054410753f13fe1d630
  | 10 => 0x39d0000002d63f70004980b71e74fa1f725c00011436d0000001d700851f1480000001b30000000000000dd00009f0000000004d30001c90330000e90423c420c2320003f04e71241821a620054104c4b63a148616d4bc4b32f527027d00030a52b4fe0004131ed03b1400822ab1790681732ea3162cf2e000002100023c24800052449600000025146d17200047e30c4083bb05605900034107c2344b52191fe42e45e1d512a2fa00001a1ad24222d00000049d24300000001c0ad0002f64f600039c0001470000005080001b23793783492b03632871f93b94624845040c732712943a35b4f41960002fb05240f1ca47a4a221e3ae0644ce26600049125448e3c12fe0000003ec1631602d71bd49220a20d1cf4582aa0623963e63592941c71193ac3f346151540710508b00014d2812651ce0930301951de1864e60350eb0a31b52fc22a0e51dc3d11554d90ca0c64bf2bf16e3d71e60b81f443c04129b21a47d4eb3ab24d44d1612af02c0830020633f80003822ca0001b84d54c14222060ab2a900005c51a3a85372d441f3384341c353039305104924e1df45b4010074153e01d922f3460794140a410831344e4234e40e410912d0c82800614310cd14c31b37700145728223837f3b433325a3993df0293dc39f1fa18d4f24f900f04b0b15140e70854ac4834c841a13d49a3e324a37441c4a428314f07803f2e40ce2bb42518c0e629a0942a63c713802e1214db2631d40164cf06544715312531d2621c10bd51e26b1f510d4531f31f25273403540be21b3941bf00e1e20740d450b0692a429e2b32524aa33029833d4d10601830004b749b1395430d334208d05e3870c014526e1cd42a37e4393ef05400041d0f231a2171110052223d81d000050d0000004785110000000000ec2560002125250003341510da2d90002842da20500003a2c453f08c0002534c50000d600014216f31504721405006600000021300016c00003d1bc0f12182110003180004820c118818052a38c23735a3e546e2f12502c02043053033622470004e003613e5101a70000ed0000b63235014c400017e0001130000000000092714bb06d0f928541630e2b645d05a22c22612c39749044819433534c00000000030f43e0003570ee0000003c009500026a32b0002b140b44953d42628f0000001a00131703534b900000039250516a00000042d0f00bb2571d32594542a233b0001db40e4da32a33e4703210000a000030b3d20000e8372
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xa1d83141640842349904baac6108021761c5058c210054ac0880b18421186c825d95308423898e4b1aa6108471994b764842108f23292c69084200a598314160084014b3063aac010802ac604745802108d34412a6b00420083f815d2629400b07d00ba4c5280160f2017498a500041ec3e83314a000a35819d94194001475013b283280028de0576506500041ec3cc4a0ca005c3670585419400b868e0b0a83280020f61376486500062639cc490ca00591c8758d539007fc34c0b1aa7200160fa187254e400041f438a4b0c8000a3581149619000b07d0c392a3200024b209754c64008e17424e5b2c6011c2d849cb658c00b85c81396cb180170b10272d963002e27984e5b2c6005c4d309cb658c00185ce5a0ecb180028b6105258a3000517416caa0c6000a3581d95418c00ba36e6206ca98002cc60440d95300051ac0881b2a604da3a80dd7644c00143b063aec8981328ea0075d91300041f438a5b226000c1c76d91534c00123b08392a69801656a007254d300068c200e4a9a6000d1840dc5534c07d63509b82a6980030e10276949300061c324e1292600585e86dd6324c001a3081bac64980030e10076545301650e432a6a0a6000c38651c1414c001a32a6382829801617219754c530004a6412ea98a6000d18405d5314c00b4390ca9c80980e3079d953901301c68d382a72026000a358110165c800143b06282c9900161b2097654f200061d328e0a0e4005878805d1658800143b0932cc710002876126558e200050ec24eab1c4005a5880551638800143b08292c7100020f6137654e200041ec26eca8c4000a5b8654d308800146b02206ca9012e8ea0375d91200041f438a5b224000a1d83143644800125b08392a6900fb86191534c120005a4412a6982400585c8758d530800b0e90eb0aa2100028d60765504200051ac0880b2e204aa38805d564c400107b0e292c9880028760c505931008c36412eca9e2000a37865d541c400166100baa83880db0d5d9419431002c1f438a5b24200585c8758d538407dc30c8a9a61080020fa1c52d91100050ec18a1b222000c38649c252440012b307384a4880030e1907054510004acc18e0a8a2036a3581d9541440594690ca8a82880bb0d1d951505100061c328e0a0a2000d31511c141440014690cbaa82880bb0d1d9755051000598402eaa0a2000c3476d95414406b868eca9a82880d30d1da525051000599404a4a0a2000d31751c14144001723063828288002e8608705051002d1a432832822037c3676506504400b66100a0ca088016ac219418c1101f70c322a69822017ab0865053044001e22a6a0a6088003645cd418811002c3c402e8b282005a38805d5640400107b0e292c808016962015458c100050ec20a4b182000a2d84149620400145b083aac4080169a2015458810
  | 1 => 0xe60ba0c4a98470bc81741895308e3210ae2312a60083d87d046254c0107b0e200c4a98028d60440189530051ac0881b0aa64fc1d73d046054c0b0f501ba2c7290028d6044058e5202e1d38080b1ca400a35811016194801a32e6204c129002cc604409825202e1c202e7304a405c1e405ce609480b83880b9cc12901716101739825202e0c202e7304a405c5a105ce609480183ae7a0cc1290168e20341982520062cb9e81304a405c3b76101609480166302202c1290028d60440d963202e1d38081b2c640587a80dd3654c80146b02206ca990170e9c040d953202c3c402e9b1aa200a3581103635440b870e0206c6a893e0fe05741895102c1e402e8312a20083d87d04625440107b0e200c4a88028d604401895100598c0881b02a200d1973100605440166302200c0a88170e101731815102e0f202e6302a205c1c405cc605440b8b080b98c0a881706101731815102e2d082e6302a200c1d73d04605440b47101a08c0a88168ea1340181510062cb9e80302a200d3371dc1655040123b06382caa08030edd8705954100699b88e0b2a8205c3b861c16550401a3506382caa08034660c705954100698c08e0b2a8200c3b611c16550401a66c2382caa08024d6077654d4100496412eca9a8200937815d9535040127100bb2a6a08020f6187254d410049ac08e0a9a8200a3880597625040147100b2ac4a08030e59470589410049ac0eed292820093a80dda525040126f02bb4a4a08024760e70949410049ac0ce1292822c83d861c9515040123b06382a2a090a4de0575d81410058cc18a1b028200b3181143605040b4750132cc0a08168e20165981412161ab8cca3028205a3880594605040185acab90c0a08168ee1850181410058cc18a03028200b3181140605049d86ae3a98c0a08168e203531814102d1c402a63028205a3a80948605040107b0e290c0a090f0d5c4521814102d1c400a43028242c3571d44605040b47101a88c0a08168e201511814102d1d42ea03028205878805d1658c40146b02202cb188170e1c040596310051c402eab24620083d87149648c40143b06282c9188170e1c0505923108c36412e8b2a6205878805d1654c40189ee6392ca988470ba10725953108e16c20e4b2a6200c4f301c9654c401858e5a0aca988030b1c840595310051ac0880b2a6205c3870101654c40145b08296c4988028b20965505310051ac0881b2e4205c3a7010365c840b0f100ba2cb108028d604405962102e1c38080b2c4200a38805d5648840107b0e292c9108028760c50592210051ac08a0b244205c3870141648840146b02206ca908028761065d8d210050ec20ebb1a4200a1d8414b63484010bd0e286c690802a560440d8d210050ec20ca31a420083d841d95348401898c6392a290802ac60440d81210051ac0880b284200
  | 2 => 0x2b0910004418c0035409394ba01067454003e8112a89c0004640d143f4ce0bcc20006500000000801e84a160003d0fc000d0000ec29000000b52880012cdb3fd160004144c000010b21c00250003b4a03cc8f218474081e224a600c16260642580d00000000fb0b000000002943825c0003c2800013234c400000120b0000003ac5005cb42fc7e008273d4730003e00062174000000017cb110072348a116c99328be2a01f00000000f9254002f4b6000003a4003340041cb83f8b927c000b43700000000430004e3dc14364003208343c00041110f000000000003d0006f0000000000000791a8f0000e1108240009001c00000c10002e0000000000001103e000434da4180c00000000cb0e4491b4741840b1688a3bc00018bc350ea1e021000d323025004d8425173c41b420ee144710e8e4020c92dc32130b21ac1a03904274a300026000000fc9231d0a1a40a0000039800014af07000000000001508cc6378df3140000000430cf29c001f000000000002237000170000a4dd0ac0015000000000008e00093400000006c1d4000009e000e8048600607f414000d031178b3134001b8e030035000000003330c1935c001143b208ae330563d8e32a44f210ab14800000300a8000009a0740000000000e74047715c000d88b43800214d13c8d6204bb14c76388682b4551f4881c1121ec660002026c00164010180816000000810010181c1600000340006018101201018000000008040a090400c4a01020005200000040000000100601010080a030280006100003012070086826010180002000a848040d0400002000080014000000400030000804060182406000001002000041fc0ae8312a60583c805d06254c0183
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x26b88af0e5d89c0058700000c215000000f008110000a002a32018000060812342c00c005002504902891a7cda14c0001e00280294eb44063a0000058015a302000c0000e00101040c008000c40302e0c9c181101639480191173604409825202e0620173d06609480b8327060440d963202e0c9c181103654c80191173604401815102e0620173d04605440b8188660c70595410064460d811c1655040b038906187254d4102e06181839c2525040b8186060c705454102d0a241655c8605040b0389061c525923102e061c183141648c40102d981c84059531006091c981101654c40b8327060440d972102c0e24187149648840b8187060c505922102e0c1c181141648840b228906105258a3002e44dcd81103654c001119981007254d3000544644401c9534c001511911037154d300050c644409da524c00b81a86103758c9300054464440dd6324c00b4189654c705053002e06218405d5314c00190882101754c53000544644405d5314c00b218906127558e2002c8624184149638800130994209534c12000606191839c252440018186460c705451002d0c259511c1414400b830762017550510004c464c805d5414400b83076a025250510004c464e80949414400b430965d47050510006485d5821c1414407da108654d414c11002c0e24187149640400b218906105258c1002c8a24184149620400b228906107558810
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x40008260008426a482101754c53000620104c8880baa62980170107664c805d5414400b8083b327404a4a0a2005a08299756087050510
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x4
  | 2 => 0x5
  | 3 => 0x6
  | 4 => 0x2
  | 5 => 0x1
  | 6 => 0x124d
  | 7 => 0x4e
  | 8 => 0x4d
  | 9 => 0x94d
  | 10 => 0x94e
  | 11 => 0x124e
  | 12 => 0x138d
  | 13 => 0x138e
  | 14 => 0x128d
  | 15 => 0x8d
  | 16 => 0x8e
  | 17 => 0x3
  | 18 => 0x150d
  | 19 => 0x98d
  | 20 => 0x98e
  | 21 => 0x128e
  | 22 => 0x150e
  | 23 => 0x9cd
  | 24 => 0x9ce
  | 25 => 0x12cd
  | 26 => 0x12ce
  | 27 => 0x130c
  | 28 => 0x130e
  | 29 => 0x134c
  | 30 => 0x134d
  | 31 => 0x20d
  | 32 => 0x20e
  | 33 => 0x154d
  | 34 => 0xb0d
  | 35 => 0xb0e
  | 36 => 0x140d
  | 37 => 0x140e
  | 38 => 0x154e
  | 39 => 0xb4d
  | 40 => 0xb4e
  | 41 => 0x144d
  | 42 => 0x144e
  | 43 => 0xb8c
  | 44 => 0xb8e
  | 45 => 0xbcc
  | 46 => 0xbcd
  | 47 => 0xccd
  | 48 => 0xcce
  | 49 => 0x15cd
  | 50 => 0x15ce
  | 51 => 0x164c
  | 52 => 0x164d
  | 53 => 0xecd
  | 54 => 0xb8956
  | 55 => 0xb9396
  | 56 => 0x10c
  | 57 => 0x14c
  | 58 => 0xb49d5
  | 59 => 0xbc9d5
  | 60 => 0x15c9d5
  | 61 => 0x1649d5
  | 62 => 0xec9d5
  | 63 => 0x9ced5
  | 64 => 0xbd2d5
  | 65 => 0x1652d5
  | 66 => 0x19cd
  | 67 => 0x44d
  | 68 => 0x14d
  | 69 => 0x19cc
  | 70 => 0x184c
  | 71 => 0x16cd
  | 72 => 0x16ce
  | 73 => 0x44c
  | 74 => 0x138155
  | 75 => 0x98155
  | 76 => 0x9d355
  | 77 => 0x9c155
  | 78 => 0x1a4d
  | 79 => 0x184e
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 74
  | 6 => 1059
  | 5 => 1349
  | 4 => 280
  | 3 => 50
  | 2 => 5
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
  | 7 => packedAt gbK7 (2092+((h/24+packedAt gbK7 (1924+(h % 24)*7) 7) % 116)*8) 8
  | 6 => packedAt gbK6 (43066+((h/353+packedAt gbK6 (39183+(h % 353)*11) 11) % 1271)*12) 12
  | 5 => packedAt gbK5 (69691+((h/449+packedAt gbK5 (64752+(h % 449)*11) 11) % 1619)*12) 12
  | 4 => packedAt gbK4 (17357+((h/93+packedAt gbK4 (16520+(h % 93)*9) 9) % 407)*10) 10
  | 3 => packedAt gbK3 (3612+((h/16+packedAt gbK3 (3500+(h % 16)*7) 7) % 73)*7) 7
  | 2 => packedAt gbK2 (408+((h/1+packedAt gbK2 (405+(h % 1)*3) 3) % 8)*4) 4
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x3ff1e0e0ff07fffe3c0781c0fc33e43e19fc93
  | 1 => 0xc1fe00ff07f87807c007fffffccd07c66640ff
  | 2 => 0xfe0fff0007ff8007fff801ff030e38f9878f1c
  | 3 => 0xffffff8000007fffffe0003f03f01f80fe0
  | 4 => 0xffffffffffff80000000003ffc001fff000
  | 5 => 0xfff00000000000000000000003fffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x1290602049008a36243484425810641a089c91
  | 1 => 0x412200490248504040012894a0450144224026
  | 2 => 0xa404a900059500928950012a090a08a8858518
  | 3 => 0x108952b2d000012532a6540012b03601580ac0
  | 4 => 0x210f9cdca6e665c000c0180c23ef8001f76000
  | 5 => 0x39c01818c0c4460023046030c3fffff6000000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 63 gbPos gbNeg, 0xfeeafce8feeafcc8feeafce8feeafcc8feeafce8feeafcc8feeafce8feeafcc8feeafce8feeafcc8feeafce8feeafcc8feeafce8feeafcc8feeafce8feeafcc8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_13709
namespace PEqualNP.Outside.L_meta_13709
open PEqualNP.Outside.L_meta_13709.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_4_0 : Interval s1Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 1 := bs1_4_0
theorem alls1 : ∀ k ≤ 4, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_4 i (by omega) hi
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
theorem bs3_3_0 : Interval s3Atlas 3 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 4 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 12 := bs3_4_0
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
theorem bs4_2_0 : Interval s4Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 10 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 60 := block_range (n:=60) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 60 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_96 : Interval s4Atlas 4 96 69 := block_range (n:=69) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 165 := (concat bs4_4_0 bs4_4_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 50 := block_range (n:=50) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 50 := bs4_5_0
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
theorem bs5_2_0 : Interval s5Atlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 5 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 25 := bs5_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 91 := block_range (n:=91) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 91 := bs5_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 44 := block_range (n:=44) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 44 := bs5_5_0
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
theorem bgb_2_0 : Interval gbAtlas 2 0 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 5 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 50 := block_range (n:=50) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 50 := bgb_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_96 : Interval gbAtlas 4 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_192 : Interval gbAtlas 4 192 88 := block_range (n:=88) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 280 := (concat bgb_4_0 (concat bgb_4_96 bgb_4_192))
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
theorem bgb_5_1344 : Interval gbAtlas 5 1344 5 := block_range (n:=5) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 1349 := (concat (concat (concat bgb_5_0 (concat bgb_5_96 bgb_5_192)) (concat (concat bgb_5_288 bgb_5_384) (concat bgb_5_480 bgb_5_576))) (concat (concat (concat bgb_5_672 bgb_5_768) (concat bgb_5_864 bgb_5_960)) (concat (concat bgb_5_1056 bgb_5_1152) (concat bgb_5_1248 bgb_5_1344))))
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
theorem bgb_6_1056 : Interval gbAtlas 6 1056 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1059 := (concat (concat (concat bgb_6_0 (concat bgb_6_96 bgb_6_192)) (concat bgb_6_288 (concat bgb_6_384 bgb_6_480))) (concat (concat bgb_6_576 (concat bgb_6_672 bgb_6_768)) (concat bgb_6_864 (concat bgb_6_960 bgb_6_1056))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 74 := block_range (n:=74) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 74 := bgb_7_0
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 4 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 5 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 4 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 6 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 9 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeafce8feeafcc8feeafce8feeafcc8feeafce8feeafcc8feeafce8feeafcc8feeafce8feeafcc8feeafce8feeafcc8feeafce8feeafcc8feeafce8feeafcc8
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 9 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 49 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) (SBf 1) :=
    slice_correct (ms:=fixRows 2 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276813032 * 2 ^ 32 + 4276813000) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_13709.Model.Repr at out
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

def mono : List Gate := [⟨.and,[2,5]⟩,⟨.or,[1,2]⟩,⟨.and,[3,7]⟩,⟨.and,[0,1]⟩,⟨.or,[4,6]⟩,⟨.and,[1,2]⟩,⟨.and,[0,10]⟩,⟨.or,[11,12]⟩,⟨.or,[9,13]⟩,⟨.or,[8,14]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,15⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 9) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813032 * 2 ^ 32 + 4276813000) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813032 * 2 ^ 32 + 4276813000) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_13709

open PEqualNP.Outside.L_meta_13709 in
theorem PEqualNP.Outside.L_meta_13709 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813032 * 2 ^ 32 + 4276813000) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813032 * 2 ^ 32 + 4276813000) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
