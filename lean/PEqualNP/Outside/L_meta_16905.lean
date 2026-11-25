import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_16905.Model
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


end PEqualNP.Outside.L_meta_16905.Model

namespace PEqualNP.Outside.L_meta_16905
open PEqualNP.Outside.L_meta_16905.Model
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

def SBf (j : Nat) : Nat := [5, 6, 6, 8, 8, 5].getD j 0

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

end PEqualNP.Outside.L_meta_16905

namespace PEqualNP.Outside.L_meta_16905
open PEqualNP.Outside.L_meta_16905.Model
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
  | 1 => 0x1ffe07fffff81c1fffff03fe0fffff007e73fc
  | 2 => 0xfffff81f81ffffe0f81ffffff0780fff93fccf
  | 3 => 0xe0ffffe001ffffff001ffc1fff800fffe38f0f
  | 4 => 0xfffffffe001fffffe0001ffffff001fc0ff0
  | 5 => 0xff00000000001fffffffffe000000001fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0xc22231451041240529272126048a690c26315c
  | 2 => 0x444450c8229208a05a09464a9050a25490d4c5
  | 3 => 0x8aa8a2035525154b0512a9152d014ca9630b0a
  | 4 => 0x14d1049260365a729640c219ca658031d80ea0
  | 5 => 0x18e1c71c79c79f9ce79cf3818c4608c1ffe000
  | _ => 0
def s0Atlas : Atlas := ⟨4,rawDecor 62 s0Pos s0Neg, 0xfcccf0c0fcccf000fcccf0c0fcccf000fcccf0c0fcccf000fcccf0c0fcccf000fcccf0c0fcccf000fcccf0c0fcccf000fcccf0c0fcccf000fcccf0c0fcccf000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_16905
namespace PEqualNP.Outside.L_meta_16905
open PEqualNP.Outside.L_meta_16905.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x50080821c20199695000008cdf43dc43df32dd32bf41bd41df31dd31be40bc40de30dc30
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x340808e2a26538505069aa598d354830
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 4
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (i*5) 5
  | 4 => packedAt s1K4 (i*16) 16
  | 3 => packedAt s1K3 (i*27) 27
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (6+((h/1+packedAt s1K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s1K4 (208+((h/4+packedAt s1K4 (192+(h % 4)*4) 4) % 16)*5) 5
  | 3 => packedAt s1K3 (111+((h/1+packedAt s1K3 (108+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x3fffe07ffc0ff07ffffc1fff03fe07e7e7e73
  | 2 => 0xfc1ffffffffffff81f03fe0fffffffff918fff
  | 3 => 0xffe07ff81fff07ffe003fff0ffc1ff81e1f39c
  | 4 => 0x7fffe00007fffffc0000fffe0001fe03e0
  | 5 => 0xffff8000000007ffffffffff00000001fffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x48430231448521016514c0513213212c263631
  | 2 => 0x11042442091082280a41120a44644a509088c6
  | 3 => 0x28894890d2242d52a09265609a919505615318
  | 4 => 0xb2d6712483b6b79cd3d83148ef390619fa03e0
  | 5 => 0xc31861c71c38c6e71ce3b98c0c201861ddec00
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfaaafaa0f0a0f0a0faaafaa0f0a0f0a0faaafaa0f0a0f0a0faaafaa0f0a0f0a0faaafaa0f0a0f0a0faaafaa0f0a0f0a0faaafaa0f0a0f0a0faaafaa0f0a0f0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_16905
namespace PEqualNP.Outside.L_meta_16905
open PEqualNP.Outside.L_meta_16905.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x3a560004ca0200511064003ef42ec42ee32ed32bf41bd41ef21ed21be40bc40ee20ec20
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x6420962a26538505069aa790d354c20
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 12
  | 3 => 4
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (i*5) 5
  | 4 => packedAt s2K4 (i*16) 16
  | 3 => packedAt s2K3 (i*27) 27
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s2K5 (6+((h/1+packedAt s2K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s2K4 (208+((h/4+packedAt s2K4 (192+(h % 4)*4) 4) % 15)*5) 5
  | 3 => packedAt s2K3 (111+((h/1+packedAt s2K3 (108+(h % 1)*3) 3) % 5)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xfffffe07f03fff07fe0ffffff03c0ffe67fe4f
  | 1 => 0xf81ffffffffffff81ff07c0fffffffff988fff
  | 3 => 0xffe07ff8003f07ffe0007ff0ffc00f81e0f38c
  | 4 => 0x7fffffc007ffffff8000fffff001ff03f0
  | 5 => 0xffff8000000007ffffffffff00000001fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x48850231214a210166029451522444b4233645
  | 1 => 0x12422442441082280890290a2449294888889a
  | 3 => 0x614b6890eda4af5aa18a4f68bea0ae0de0d38c
  | 4 => 0x4594512489063594d32b0240cb32c411750360
  | 5 => 0x861861c70e38c6e71dcc738c0c030861deec00
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeeeaa88cccc8888eeeeaa88cccc8888eeeeaa88cccc8888eeeeaa88cccc8888eeeeaa88cccc8888eeeeaa88cccc8888eeeeaa88cccc8888eeeeaa88cccc8888, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_16905
namespace PEqualNP.Outside.L_meta_16905
open PEqualNP.Outside.L_meta_16905.Model
def s3K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K6 : Nat → Nat
  | 0 => 0x40e225c59e004c00c30587840000005248ce9a2001300000000d00500a12a011250418d83321d200389c01f14804831541c8153003042000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x4817e53903bca7205794e40bea9c81dd53902baa7206fd0e40dea1c817e52902faa5206f90a40de214817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c535037c86a06f10d40bfa9281ef52502dea4a05f14940f6292816c525037e84a06f50940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40bea9881bf431037a86205f94840bea9081be421037884205f94440bea8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330efa1e61dc43cc2fca5987b94b30b7296617d52cc3daa5985b54b30ef99661dd32cc2fca3985f54730ef98e61dd31cc2fea9185f95230df2a4613e548c2faa9186f552309eaa4617c548c2faa7185f94a30bea94617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130efa1a61dc434c2fea4985f14930ef99261dd324c2fea2985f14530ef98a61dd314c3f66098778c130bfaa0617e540c2faa8185f15030bf298617e520c2faa4185f94430bea8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20bf28e417d51c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea9441ef42883d885107b8ca20f6994417e51882faa3107b88620f610c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a417e53482faa6905f14d20bfa8a417c51483de42907b48520fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53082fca4107bd0820f621041ee32083da64105f94420fb288417651082faa2107d54420baa8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3085f94210fd18421f930843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fb10a21f521443f460887e4c110fd88221f610442fea8085f95010df2a0213e54042faa8086f550109eaa0217c54042fea6085f94c10ef298215e53042faa6087754c10aea98217c53042fea4085f94810f7290216e52042faa4087b54810b6a90217c52042fca2085f94010fb88021fa10043ea20087e44010
  | 1 => 0xd5190afca1215f54242bfa9a857c5350b7e86a16f50d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42ef298855e5310afaa6217754c42aea9885be4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332ef21e65dd43ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa7195f94a32f721465ed428cbbe65197bcca32bf28c657d518cafca1195f54232bfaa265bf544ca7ea8995f95132beaa2657c544cb78a8994f15132ef21a65dd434cbdc84997b50932f799265de324cafea2995f14532bfa82657c504cafea8195f95032df2a0653e540cafaa8196f550329eaa0657c540cafca6195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef50f41bf296837d52d077c85a0ef10b41bf286837d50d06faa920df94e41bea9c83be43907788720df94a41f7294836e52906faa520fb54a41b6a9483bf429077a8520df94641dfa0c83f741906fca120df54241bfa9a83df53506bea6a0df14d41ee29a835c535077e86a0ef50d41bfa92837c525077c84a0ef10941fba0a83be41506fea0a0df14141bf2a0837e53106faa620ef90c41de218837e52106faa420efd0841dea10837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331bf296637d52cc6fca198df54331bfaa4637e548c6faa918df15231bea9c63df438c7b88718df94a31bea9463df328c7ba6518df94631ef98c63f7318c6fca118df54231bfaa263bf544c67ea898df95131beaa2637c544c778a898cf15131bfa92637c524c7ee6298f78c531bfa82637c504c6fea818df95031df2a0633e540c6faa818ef550319eaa0637c540c6fca618f7d0c31ee218637e520c7dca418db94831bea9063ed520c6daa418f7cc831ee990637e510c7be6218fd8c431ee98863f5310c6fca018fe94031bd280637d500c7f2a018de54031bfaa6437e54c877ca990cf95321beaa643bd54c867aa990df15321bfa9e437e53c87bca790d794f21bea9e43dd53c86baa790df14f21f7a1643ec42c87dc6590fb4cb21bf286437d50c86fea910df95221df2a4433e54886faa910ef552219eaa4437c54886fea710df94e21bea9c437c53886faa510df94621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21f7a1243ec42487dc6490fb4c921fb90a43ee21486fea090df14121bfaa0437e54086faa810df15021bfa98437e53086faa610df14c21bf290437e51087de4210fd88421f690843f521086fca010df54021bf29e817d53d037c87a06f10f40bf296817d52d037e85a06f50b40bf28e817d51d037e83a06f50740beaa
  | 2 => 0x20442b9b52440005a08727e7a00000031e000001010ec000000003320000000000004c0017443885c9695b000000000012a6000002015160000680035a00073000000000412150000009880000000027a530000004e0a9190000001a80000012180006869c0012b00012000000282000cf24e000000000000000000024800000000000000000bd0f00000000000028c5cc000000000013525934c0010f12e000570f622b00e86902983000694ef9c00000012927c30e0ac650000000009a17d000494001db414988b200000000000064170934001bf000000b09da0ac00113a6533e4452a897114000000000008dc000372ee000418940d200139000144860000000000500016529e650311fe2160003d8000009dc0027d0000007687d20ca30aa0004081dcc40da000000000000000009c0004d8000f51430000d46029418606c8511212c3ec3908f4849d14403f2d07e82825429a000000004280004200001c028caa33000000000005041bcae8e82f6000592380f827d1a9ac3f03943a8450087d80000024e8889b1b927c00066800000098000d20006eccb8fa0000000000000003cff8004bc0000008643a4f000000000000b00003423b92f8d80006dc00000000000200af27a3900022e000000001af20e9cd3f800000000000002ce0a03f2510000000000037866c8980012a6f4000650ba424fb8004f028c0b950000000d50060880ccd99eb06c4a47494e00400a00c0000400400c010110000000080400800002800008000010110020040000c00e0000000300000c0380e0080000001a000004008000020000000300000800003016000000010000100080500000009000000044000020180000080e00a00409800000018000140140300a002006014000020020080400300e0000e00300000000801002000018000040000800104a0040280000202c0080000200001007002004010020000000000001a00c0000100a01400002004014000070080140000000600000000000004008000020340580001e00406802006030008000080200000100c0040580b0040240300b00000405802012018000020020040080000c00000000028008008000040080200000c0000200000000400802000008000010000000680300200c0400001400802800bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421fb94843b7290877d5210fdaa421db54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7216f90e42de21c857e5290b7e85217bd0a42bf28c857
  | 3 => 0x350000000006800000041a430699d54f4000002610000e0119261f8a288400031a4393a97800000000000000000e80005240000000000071c000d1258624000cc3da00000000326280b11e02e038c3c00052a0002197f48e0011219c00057c000000004e80013b00092cf88293ac1cc0012421e6683300003e260000000000010c9de0001a80000000047cbaa4f000048000000001c0fa0001220000000000036cc61e40007282fa3d00045cad00000048c238003ce0000016d000000610000f20000000016200000285000464758c1000600b5842060000001f500015478a4400029c001d91fc000e4880000a34e180029600064a8e18a000000cb3f6000b18001500080028304035c270bf416760170000000000000050c000e60003f20010d80000078c001c60006b8000000006c4f30160002050823b1782f8638050008bc0002a000434000242fc6a400000000000000000006acab0000000007a0ce0005a8ee9844da8e40017c1ac0002d0f21d89acb4a411aa484e5a690b69c02584c33a800f82303166e0b3135072a1025019062544d21b20002d8e70004528f9188993b82d400000000000520000ce440a11280d67cc1e8ac00000111800000379078084b69f86c88c0a60000d2960006e87100030a00059800000000001982985785580023a000a4800238000b8a344de15000258360000019c24b40007780000095d499553220013225c3442940002502a6d842800266000001031b8514c81be0001fc001d43c48f0001183de3d4ac9a31740010105c0003e4eba324943e00000009a898000000000000011b1ce2a80e82723437514287000000f29f22b0000a210413a0e8a0246000000e20004a00008a9370006493d8520160c8799054d0930248090dc000b78003fa0f0000a60000002898200024c4d800000638b71b452e78504a1339a74430a67474400002071a0528a922d28e5201609a410894080002645e400000454000361fc00087c5d80018c8b0980000002850192f32c2412b068442088441570009b8108001fe9e40009e3828d800000000974001860000002f0000005b0001cf0000005e800000838bb08b082a001f0182e4458e426648a3dc8f0cf314a402c0b91be9d88a0633d22b47b03b15c0bd488b03dc0003a00c1120010600011a000000000003a8620000000012000038a848000e0000a3d408000b2180368b73a400038a6300000000000124070810e10009800007a40c0010893942c481101d3000604168000000000f0000003f42300000000144a3f0002393892a49
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x53c823e64947208f59251c825e63d52209758f548823e64d4e208f593538823e6494e208f59253882cd6310a20ab191328823f64546208f191518825f63546209718d51882ae64886208f992544826f62551208f994544823e6494d208f592534826d6294d208fd91534823c6454d209dd8553482746154d209b997214832c54c8520cb151214832c54881209798f540825d63d50209d987540827561d50208f596540832c62550208f990540825e63150209758c540827661150209d584540823e64d4c208f593530827661d4c209d587530825d6594c20c7952530831d5494c20d398a530831e5454c20c7551530823e6414c208f590530825e6314c209d98453082756114c20cb553420826d6510820b358c420826d658c820cb55232082ac644c820cb551320834e534c820cd95251083355494420d594e51083555394420cd95151083355454420d594d51083555354420d9d0951083644254420d98c9510836532544209b59621082ae6488420d954621083655108420d9547200826f6548020ab191200836551480209ed95200826e62d53109b58b54c425f63553109718d54c423f6454f108f19153c423e6414f108f59053c426e6214f109b58853c423e64d4b108f59352c423e6494b108f59252c425e6394b109758e52c425e63d52109758f548426f62552109b189548423e64d4e108f593538423e6494e108f592538426e6294e109b58a538423f6454a108f191528423e6414a108f590528425e6314a109758c528423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f994544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d1097994534431f5414d10c715053443596014d10cbd53524432c54d4910d3d4f524434c53d49108f992524423d64949109798e524425d63949109b98a524423f64549108f191524425f63549109718d524426e6514910cbd50524432c5414910d3d4c524434c5314910d9584524436452885109d1952144358538c1109e195304425e63d50109758f540426e62d50109b58b540423d65950108f990540425e63150109758c540426e62150109b588540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c108f990530423d6414c109798c530426e6214c109b588530427a6014c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520423e64148108f590520425e63148109758c520426e62148109d984520436552c40109e596100435953840109dd95100436552440109ed9510043595344010
  | 1 => 0xc63e649513197d8d544c63e6515131c7152314c66e62d50319b58b540c67a60d50319e583540c63d6595031c718d540c63e64150319b988540c66d62150319e980540c6796015031c7553430c65d6510c31b3588430c72e5494831cb552520c72e5454831cb551520c71d54cc831a7191320c71d544c831d3949320c65f654c431a7191310c677654c431ce952500c7395494031da94a500c7695294031ce951500c7395454031da949500c7695254031d6d0d500c7584354031d6cc9500c7593254031d6cc5500c75931540319798f54c865d63d5321cb18954c865e63153219758c54c863e64d4f218f59353c871e5494f21c755253c874e6294f21c795153c871d5454f218f99053c863d6414f21cb55342c86cd6310b21cb55232c86ac644cb21cb55132c874e534cb218f993538863d64d4e218f990538863d6414e219e98053886796014e21cb953218865f63551219718d544867b60551219e181544863f6454d218f191534867b6054d219e181534863e6414d218f590534866e65d0921b358c424866c654c921ab19132486e4614c921ab992214863e64141218f590504865e63141219758c504866e62d50219798c540865d63150219e980540867960150218fd91530863c6454c218f990530863d6414c219b988530867a6014c219e580530863e64948218f592520865e63948219758e520863e64944218f592510866f65484219dd95210863f64540218f19150086ad6210f409b98a51d026d6294740a718d41d026e6294e409b58a539034e6294e40d358a539031e53d0e40c794d439031e5390a40a758c429031e5310a40c794e41902ae6290640c794c419031e53d02408f99443502ad6210d409798c525025d6314940d398c525034d6314940cb90c525032c43149408f997425032c52d0940cb149425023e65d0540cb14b415029c6350540cb149415029e6390140cb14a405023f6550c408f596421029d631084097d8d511025c63544408f59641102ae62904408fd9540102ac62500409ed95401026e62d53309b58b54cc31c63553309b98854cc26d6215330c755343cc2cd6210f30cb95252cc32d5494b30cb95152cc32d5454b30c755332cc29c644cb30c755132cc34e524cb30a719131cc31e548c630c7950318c2d9600c630c7953308c26f62551309b189544c27761551309d185544c25e65d0d30b3588434c23e64149308f590524c29c644c930b6181324c23e64145308f590514c26e62145309b588514c25e65cc530a7191314c29e648c1309798f540c26e62150309b588540c27661150309d584540c23e6494c308f592530c23f64548308f191520c23f64544308f191510c25d658c430b6580310c23e64940308f592500c25f654c0309ed95300c25e63153209758c54c823f6454f208f19153c823e6414f208f59
  | 2 => 0x63cfd11a07c000ee0001f822cac8003d633400112334344da8dc1ee4e8f00000007f80017a0105f80000015c80c0015e156000a1073000000328002da000ec83c40a6e07e887072140de1030b2130000463de864629db2420b8ab1fb0360d4e2201150024958150001707f8a338e41802029000324468da0005a40021724a570d40000001b02291419c7f01b0063140004483a000000c08191ba7449a8e71605e40005d16601c000122f82b4c30110be5a09c81e3e6148a39990f6810661cd15e3889199300064841800000670b98002000886d80e424658651f532e284ad8200000010109e1380940680003061c8080030a3a8e09cf000000000000000004f86b2ca4d0bf90b36e7c800000000214878ec000000001980000000000000001006034030000000c00000030180300c0e02c0302c0404c00008000040000c000000001c00000300000200001000000000000c360040b0000a0000002000010001140201c0c0141600c000001000000014020000100c00034000341c008000000001800014030040200c000040c02c000000d0180100c0101802004020100801c0000c000101501401020000480e020000183c01c1401c160080c060390340200800014010140602c000280101001004000180001c020200000c0d02000034040000d00400014010080302402000260080003043000010080101c00004010326e62947439b58a51d0e6f62543439b18950d0e3f6550c4397d954310f2f4354843d390d5210f2d4354843d350d5210e5f63547429718d51d0a5e63943429758e50d0aad6210e428f9974350a3d6590c42c754e4310b1d5310c42ab5884310b1d53d0842d354e4210a3f6550842c754d4210a6f6550842d354d4210a7a60d53329e58354cca3f64547328f19151cca3e64943328f59250cca7661d52329d587548ca3e64946328f592518ca3f64542328f191508ca3e64951328f994544cb1d6315132cb588544cb1c5490d3297195434cb2c5490932e390e424ca6c6550932e350d424ca3d65950328f990540ca5e63150329b988540cb1d54cc832cb552320ca5f654c832c7551320ca6f654c832cb551320ca9d6310b419798e50d065d6394341ab588439065e6394a419758e529074e6394a41d358e529072e4394a41cb10e529072e52d0a41cb949429072e52d06419b988535066d6214d41d3988535074d6214d418f997435071c53d0d41c714d435071c53909418f994425069d6310941c714c425071c5390541ab98a415063d6590c41ab588431063f65508418fd95411069c63504419dd95411066f62540419b189501066e62153319b58854cc63f6454b318f19152cc63e64943318f59250cc66e62d52319b58b548c6cd6210e318f992528c63d6494a31a7191328c63f64542318f191508c66f62542319b189508
  | 3 => 0x9404f000740c89cc000145048003760e0309ac2ce240d39e7000104c00d00003b417a0c03819cb60002ba000000a22607a4cf06f336230001462867b45b05b2e47c00000016e04c690000006d0ef05a2ee2510500035662ca294b14c1a4249ec3122107c9bf36615cd29f708458ca49b10043187c2112b003cf513c01849c0001a3ac0fcb88e40f8500810bd000000cf9e50004bd0d0d711c70c001ca0005bc000003ae3ac001901401786a08a14877c160f342c7086a9740005d8180161267e40002d0003c4601c510c7007f0001f60000013f000384658001820000006d00000039000000310000b5000134000004162e08600041a000001481580000006613631c4b9290000000000000033ce98c23e24c4a60000004149c14d2ae000000000000006f1940007e00000023e0000014e3900044c1040462e8000680c06c01d9a22123a4258212264c88890a0f4774838370fc5f431200006690d198d17c204488780001d48c87922c854731c933a5280006e3c26e8000bf2361c04d188266680c20a50005c0001d440e000b71af000000001d537c0000008826e0ac000713ec440e9118152274718d90ec25419164000788a88002d6138b01542885e0b08430204786b02826c014050e5066050782060fa128ff8542b40f47a90d4207383192032a26435152172638320c84261590414108e29cdc8341e82005d9cb34c630e312c11e0c50a0004303a0951e323a598db122000160f417b35a6b85890e000000000003fa248000530004b8000000007d0410000000010796a0ee2c8d9044000000000df2a6074001e627a4ec6995503e1548a84000009cf2175048540d4924000838de92d0001d00013e0000004b0ef0000008b80000000015000000360f71821ec120930bc00057cc181704c3e8ec1aa00000000000000420000000163c8000e01864707714f3b42a8d08001685883f80
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x12c63cc4891cd00551800e1000165c309354029100840b01801c2118358d6215132a1ae72928520d0d7214d435070629cc520a83435c86355031838ecaa26418d497210d500c68c3a264a8063461d13154031a1ae6312a990c2c7655132c8686b94a6a1c818394e6290640a1ae629284a060c631494150307318a520281435c86355330838ecaa2659861a54580318c286b98c4aa0410b1d9544c820a8ae6212a210524744c95108313322a310841891915148020
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x40b000080d8714e629054180d8794e629064080d8718c525054080d8798c5290140
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 664
  | 4 => 539
  | 3 => 25
  | 2 => 4
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s3K7 (i*5) 5
  | 6 => packedAt s3K6 (i*16) 16
  | 5 => packedAt s3K5 (i*27) 27
  | 4 => packedAt s3K4 (i*38) 38
  | 3 => packedAt s3K3 (i*49) 49
  | 2 => packedAt s3K2 (i*60) 60
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s3K7 (6+((h/1+packedAt s3K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s3K6 (718+((h/13+packedAt s3K6 (640+(h % 13)*6) 6) % 53)*7) 7
  | 5 => packedAt s3K5 (20359+((h/221+packedAt s3K5 (17928+(h % 221)*11) 11) % 1059)*11) 11
  | 4 => packedAt s3K4 (22272+((h/179+packedAt s3K4 (20482+(h % 179)*10) 10) % 711)*11) 11
  | 3 => packedAt s3K3 (1265+((h/8+packedAt s3K3 (1225+(h % 8)*5) 5) % 31)*6) 6
  | 2 => packedAt s3K2 (243+((h/1+packedAt s3K2 (240+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x87fff83ff87ffe0ff87f87fe1fc0fffd38f39f
  | 1 => 0xf81fffc1fffe1ff07f87f87fe1ffe07ec73cf3
  | 2 => 0xffe0fffe007fe3ff8007ff8ffe00ff8307cf1c
  | 4 => 0xffffff8003fffff8000fffff0003f80fe0
  | 5 => 0xffff0000000003fffffffff000000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0xa0840888409400029809009402442a30185185
  | 1 => 0x2421104902020502082882220924148432432
  | 2 => 0x114aa214354906b50444d50b540a950b058e18
  | 4 => 0x5594c4a1240d4b29cd50440d992c0613a80bc0
  | 5 => 0x66188739c67193ce7667664110301863f6f000
  | _ => 0
def s3Atlas : Atlas := ⟨7,rawDecor 55 s3Pos s3Neg, 0xeeeee8e8ececa8a8eeeee8e8ececa8a8eeeee8e8ececa8a8eeeee8e8ececa8a8eeeee8e8ececa8a8eeeee8e8ececa8a8eeeee8e8ececa8a8eeeee8e8ececa8a8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_16905
namespace PEqualNP.Outside.L_meta_16905
open PEqualNP.Outside.L_meta_16905.Model
def s4K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K6 : Nat → Nat
  | 0 => 0x600000002c4800000813224844a25005d380007c0891c68008463c987183450000700003c6ca80000058000002003a000000000c8004002a12060180000020101000c08e001408eff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x4817e53903bca7205794e40bea9c81dd53902baa7206fd0e40dea1c817e52902faa5206f90a40de214817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c535037c86a06f10d40bfa92817c525037e84a06f50940bfa8a81f751502eea2a05f14540fa28a8174515037e82a06f50540fda0281be40502fca8205f94c40bea9881bf431037a86205f94840bea9081be421037884205f94440bea8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330efa1e61dc43cc2fca5985f54b30ef99661dd32cc2fca3987d94730bb28e617d51cc3eaa3985d54730ef98e61dd31cc2fea9185f95230df2a4613e548c2faa9186f552309eaa4617c548c2faa7185f94a30bea9461de328c3b865185f94630bea8c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130efa1a61dc434c2fea4985f14930ef99261dd324c2fea2985f14530ef98a61dd314c3f66098778c130bfaa0617e540c2faa8185f15030bf298617e520c2faa418778c830ee190617e510c2faa2185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20bf28e417d51c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3105f94220fd18441f930883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20bfa8a41f751482eea2905f14520fa28a417451483de42907b48520fd18241f930483f640907b88120bfaa0417e540837ca8104f95020beaa041bd540827aa8105f15020bfa98417e53083bca6105794c20bea9841dd53082baa6105f14c20bf290417e51083eca2105d94420bea8841f551082eaa2105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dd0610fa20c21f631843ea63087dc8610fa10c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a217e53442faa6885f14d10bfa92217e52442faa4885f14910fb10a21f521443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf28821f741043e882087d8c410fa98821f721043e842085f94010fb88021fa10043ea20087e44010
  | 1 => 0x65190aeca3215f54642faa8c85755190afca1215f54242bfa9a85df5350abea6a15f14d42ee29a855c5350b7e86a16f50d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42bea9885be4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332bf28e657d51ccafca1995f54332bfaa4657e548cafaa9195f15232bea9c65df438cbb887195f94a32ef99465ef328cafca3195f54632bf284657d508cafea8996fd51329faa2657e544cafaa8995f15132de2a2653c544cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf29865df430cbb886195f94832ef99065ee320cbba64197b4c832bf28865f6510caeca2195f54432faa886575510cafca0197e94032bd280657d500cbf2a0195e54032bf29e837d53d077e87a0ef50f41bf296837d52d077c85a0ef10b41bf286837d50d06faa920df94e41bea9c83be43907788720df94a41bea9483bf429077a8520df94641dfa0c83f741906fca120df54241bfa9a837c535077e86a0ef50d41bfa92837c525077c84a0ef10941fba0a83be41506fea0a0df14141bf2a0837e53107bca620d794c41bea9883dd53106baa620ef90c41de218837e52106faa420efd0841dea10837e511077e8220fd90441dea0883f541106fca020df54041bfaa6637e54cc6faa998df15331ef21e63dd43cc6fca598df54b31ef19663dc32cc6fca198df54331bfaa4637e548c6faa918df15231bea9c637e528c6faa518df94631fb20c63f5418c7be6318fdcc631bf284637d508c6fea898efd51319faa2637e544c6faa898df15131de2a2633c544c7bc8698f750d31bfa92637c524c7bc6498f70c931fb20a63f5414c7ee6298f78c531bfa82637c504c6fea818df95031df2a0633e540c6faa818ef550319eaa0637c540c6fca618df94831bea90637e510c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c877ca990cf95321beaa643bd54c867aa990df15321bfa9e437e53c86faa790df14f21bf286437d50c86fea910df95221df2a4433e54886faa910ef552219eaa4437c54886fea710df94e21ef29c435e53886faa710f754e21aea9c437c53886faa510df94621fba0c43f441887ec6310fd4c621f790c43f721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21fba0a43f441487ec6290fd4c521fb90a43ee21486fea090df14121bfaa0437e54086faa810df15021bfa98437e53086faa610df14c21bf290437e51087de4210fd88421f690843f521086fca010df54021bf29e817d53d037c87a06f10f40bf296817d52d037e85a06f50b40bf28e817d51d037e83a06f50740beaa
  | 2 => 0x22122200027c48e2c4e78003567d84727900051cfe1840006b927a48000000178b80000014504d00058c4b0003940011f975214000000000007ec55209000089208000885582ea2c34406c0793c506a30e01540a24a07e1d227a4dd2f04a0009e0c81ba3f09e885800188910da87147a5550010426823cae0892900007d00b43a47cbd132000298b40000427a4001a45109a8b80783b64b4cf16b1b67200000c40a455038002f8000b600049221c000730005a4561ef49c0b4000f100010d40a544da388d912b4ee0a4f82751040006aa5b3d86cd2e8672eca24000b50003e4000631ba97d1a8005047303814c0001851b11e1500d479857148a4d4301d2f6000831213c050d008b9410000210550466dceb00032e000000000b64fc00017000050d09640ac26415a803ce3a01b8000063f497800000249251f400007c001ff08a2f868000000654099af0004c4d02581f03640018300078c000ed43c6f44d27f2580013789f4aa5c8b68a71de30d058000002000015f4523303f02c0e88352e0844b41b10604b50e01cf427142a000c91f52b0349471d34460005980000052cdd80018c1ac8a1a54400784f1743786e0001f21200a83d80616c1d9232513bc1dd0e1e62763201d1e215699cad9864cc6a8ca0000b8000028000928949c9cb180000548d40008ecee03906600134a7b0be0003e9a83b24c0aca951ac45812a37478000270001be194f702e30a6c0bb8521608e84ea56000a101c0f43c800046800000000c5000484624ed00002c030f4010180100c010000a000040280302814010000800204c28004000000100c0101404014020000000001000000540003c4f000080100002c0a0380400408010020a4050000100c000080600016018100140c02017008080400800c02000070200003801018020480405000024040180100000030160080400417004080040903c040100301c0401c080400103803000020240300400000040081700c09004030180e04803008140001102000060100340401405004020000003c0d00c03030010140e00002010250ec020100a010020180c000110c8050001508c0200422000040580902411014000040c01c010181301818000010200904c0300003014030140500800054010040200c010000804c02bf296877d52d0efca3a1df54743bf286877d50d0efaa921df94e43dfa1c87df4390efca521df54a43bf28c877d5190efca121df54243efa1a87be4350efea4a1df14943bfa8a877c5150efea0a1df14143bf2a0877e5310f7e8621f790c43dea1887dd4310efca421df54843bf28887f65110eeca221df54443faa8887755110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7216f90e42de21c857e5290b7e85217bd0a42bf28c85f
  | 3 => 0x671081cc774000360000f4000e43be25c002032746b4d39b12a00253206a09e2bc7809500022c000000bc060000462f0104f98f644ca591080043449c000540008600006825435d0903c1ee13002214174400ce05821a64c181f92c08c8241072aea486394f0763c8b29b949a32481a8545670cd49c23ae8cc418004e6000000ca18a4f8001fa42e8e000000462000409ed2de525360003320400421628c2281922d48a724b724b52e578a71132fc0000011b24c4e12c8502844444e2020e428d4693300014d020dc2948381f8192804485d99a0380053000020a000a20912f2384c69192a42b94a23426c5a871a2a3109c0b315d15a45c760002188bcb38002fa335290b7000930b99231d44742c92951e9f92ba6325c0007f80d00062c0006e3c2a2cfb9c41407c4050bc2c46fc432111b0840b88022fe1883c9d05226040018e1262d00889b4726011121f39a4813400038e3041f0d137c659201fd000308748001300000a8e733a1f0e2800000000000004860000021341454467a243a89d09211014a0008086f000438db1353d463ce30bd0009401215a304865358314e44882391c3ca1fce70661b42fc878d31286985086404c94c3aa0610a000a28de4ec1807d85a0f4038b08f500050537000368494d614d4602303686944e8f814040234394c8a2843628930a0f23032d3e8fe1d68b8a98123b067c591fe4c4380e881a0000581a00000061c139a3520660e0800336754100ee3d66313290
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x153c823e6414f208f59053c82766114f209d58453c823e64947208f59251c825e63947209758e51c825e63d52209758f548827761552209d185548823e64d4e208f593538823e6494e208f59253882766194e209d586538823f64546208f191518823e64951209798e544825d63951209d9865448275619512097d8d544825c63551209dd85544827461551208f994544831f54d4d20c7153534823e6494d208f592534825e6394d209d98653482756194d208fd91534823c6454d209dd8553482746154d2097994534831f5414d20c715053483596014d20cdd53514833454d4520d5d4f514835453d4520cdd5051483345414520d5d4c51483545314520d91472148358538c1209e195304825e63d50209758f540827661d50209d587540823d65950208f990540825e63150209758c540827661150209d584540823e64d4c208f593530827661d4c209d587530825d6594c20c7952530831d5494c20c7951530831d5454c208f990530823d6414c209798c53082766114c209d584530827a6014c20cd95251083355494420d594e51083555394420cd95151083355454420d594d51083555354420d9547200835953880209bd95200836551480209ed95200835953480209798c54c425d63153108fd9153c423c6454f108f99053c423d6414f108f99352c423d64d4b109798f52c425d63d4b108f99252c423d6494b109798f548425d63d52108f993538423d64d4e108f992538423d6494e108fd91528423c6454a1097d8d528425c6354a108f990528423d6414a109798c528425d6314a10b558c41842b4644c610ad993218423e64951109dd85544423e65151108f992534423d6494d109d586534423f6454d108f191534426f6254d109b189534423e64949108f592524423f64549108f191524425f63549109718d524427761549109d996214433454885109d19521443345448510cd152104425e63d50109758f540426e62d50109b58b540423d6595010cd185540423e64150109798c540425d63150109b988540426d62150108f993530423d64d4c109b98b530426d62d4c1097596530431e5494c10c755253043566194c10c7951530431d5454c108f990530423d6414c109798c530426e6214c109b588530423e64d48108f593520425e63d48109758f520426d6594810cb952520432d5494810d394e520434d5394810cb951520432d5454810d394d520434d5354810d9185520423e64148108f590520425e63148109758c520426e62148109d984520433554d0410d954b41042756510410b558c410436552104109d5963104335548c410d954a31042b4644c410cd5513104356534c410d9549310427565c8410ad993210436552c84109d59421043655208410d954b100427965840109dd9510042b46444010d9549100427b6544010
  | 1 => 0x63f6550441c754d41106776550441d554d411067a60d53319e58354cc63f6454b318f19152cc69d640cb31b658032cc63e64943318f59250cc66e62d52319b58b548c63e6494a318f592528c63f64542318f191508c63e64951318f994544c71d6315131cd584544c71c5490d3197195434c71c548c931a7590324c71c540c931b5984324c6d9600c931cd152414c79643905319d195414c79543505318f596540c63e64150319798c540c6766115031c7553310c735548c43197d95310c71d544c4319dd95310c735544c4318f99353c863d64d4f218f99053c863d6414f219e98053c86796014f219798f548865d63d5221cd185548865e63152219758c548863e64d4e218f593538871e5494e21c755253887566194e21c7951538871d5454e218f990538863d6414e21cd55341886d56310621cd55231886b4644c621cd5513188756534c621ad993218865f63551219718d544867b60551219e181544863f6454d218f191534867b6054d219e181534863e6414d218f590534867665d0521b558c4148674654c521ad19131486e4624c521ad993214863e64141218f590504865e63141219758c504867661d50219798c540865d63150219e980540867960150218fd91530863c6454c218f990530863d6414c219d984530867a6014c219e580530863e64948218f592520863e64944218f592510865e63944219758e510866f65484219dd95210863f64540218f19150086b56110f409d98652d02756194b40a718d42d02766194e409d58653903566194e40d5586539031e53d0e40c794d439031e5390a40ad986429031e5310a40c794e419029d6310640c794c419031e53d02408f99443502b56110d408f997425029c63509409798c515025d6314540d598c51503556314540cd90c51503344314540cdd08515033542145408f997415033451d0540cd145415029e6390140cd146405023f6550c4097d8d521025c63548408f59642102b661908408f596411029d63104408fd9540102b461500409ed95401027661d53309d58754cc31c63553309d98454cc2756115330c755343cc2d56110f30a719132cc3365494730cd55251cc3365454730cd55151cc31d54cc730a719131cc31d544c730d594531cc31e548ca30c7950328c2d9600ca30c7953308c26f62551309b189544c27761551309d185544c25e65d0d30b5584434c23e64149308f590524c27661149309d584524c25e65cc930a7191324c23e64145308f590514c29c644c530b6181314c29e648c1309798f540c26e62150309b588540c27661150309d584540c23e6494c308f592530c23f64548308f191520c25d658c830b6580320c23f64544308f191510c23e64940308f592500c25f654c0309ed95300c27661d53209d58754c825f63553209718d54c823f6454f208f19
  | 2 => 0x92a0dc000af98e26e00000139000604241fe416298000002a800006000000000f7000000000278003f626c000ad0001cc000e026821c001a9000528b99a4060000000000008503b80037e000000000000c89700007c000000aa1603b800000000000de9a2000000000000003380c9d31f4000001500002a0000633cc000000000000000018d2c2140e080004a4cc000000120200000000019486800000738001d400000000000000000000af3e23a0e01681301340004c3e00005d8000fa4b4000001c20008e0003e4000000e50860000004e2cc46c001a60e00010380000000091047180000000000002ac8100002800000000000754858001663544e8000003ec001550000000000000000200c0200800a00400005006000000010020000680500600c09800000004010040000040700000000c03805000000018000040000100200000406802000000008000000000000200c01c00000000000008000000000000101e000008000020000080100a0000280100e00000803004000010010020100100200400001008002000000040040100180a00000800001000008028070000080201100601c0080000000800805000000010020000040000100001c0000600400001801000000000030000000600000a00401000000008008020040000000100400c028000040000580000001000001002004008000000000000d00400e766194b439d58652d0e7761543439d18550d0e3f6550c4397d954310f374354443d590d5110f354354443d550d5110e5e63943429758e50d0ab56110e429798e5190a5d6394642d598e5190b556394642cd90e5190b344394642cdd0a5190a766114d429d5845350b566114d42d55845350a3e65d0d42c714f4350b1c5350d42c714e4250ab661909428f5964310ab56110c428fd954210a9c63508429bd954210a7761540429d1855010a7661153329d58454cca3f64547328f19151cca3e64943328f59250cca7661d52329d587548cad56110e328f992518ca3d64946328fd91508ca3c64542329dd85508ca7461542328f992544ca5f63551328f994544cb1c548c9329d987540ca7561d50329e983540ca7960d50328f596540cb1c63550328f990540ca7661150329d584540ca7a60150329e580540cb1d54d0c3297594430cad56110c3297d95320ca9c644c8329bd95320cb365494432cd552510cb365454432cd551510cb3a5494032ce552500cb725194032dc546500cb3a5454032ce551500cb725154032dc545500cb5b4354032d610d500cb5b3254032d64c9500ca5f6354b419718d52d06b66190b419798e50d065d6394341ad584439069c6350a418f99743506b661909418f994425063d6590c41c754e431071d5310c41ad584431071d53d08418fd95421069c6350841c754d421071d53d0441d554e411
  | 3 => 0x16000000000001f5434270ba059000168000003a27dc821230000002b20621207800000148000fb00000025c000000004f4fe15e000224719ff01c360840000000480008b00000000000000000000000000000001727626800000000000000002f2000000003083680020a0f4714000683b00286200042a5a400000000000000000006d4000670000000000037629c9615d26c080db8d93361141c000000000000002fe7649880030c00008180330774001270000005280042c3f40008331862c008940d60006e8001e8000b02133b80c40008e000428f52190000000019a00065000055000258300b200056c50000108748390000000000000000000000000000000fa01f3ac000002171ec4580d8000005ac94800000348760000004f04080000000090a100000005f0001260000d00020a0000000000083c00000226000b50000003c8688000007880e99d33275c000001de5e8d596e218334ae1eb0d230c5b800000398001de000000001a52e479c00011000000e780013c000000000002f4000000a6538ca985132000a180016c000000000e843c000f3000000178001ae000db0000006e40020c408000288002d864c00034074128002111bc824001001740d4001871467808c91a0000000010122e0001f8710006b40000000000000000358000a48000003c46500000008833000000000890b80000004fa121ac00062800000000478f83d2000a41e5000000001c94304c80019f0000185a0850002540000f000000f20ff2f0000932010000007f01c4041008c17e0007203a8003785907a800000000001d0000058258cf0000005894c3068380000028e388000000004bc00024000318d714622a0a08f0000000009f1402ec1b42a1e3178308ab06a1b8350b38000c4000000003540009405b0d86e0929c600043801000000000000570000000000005a00000037000000000d0000000000000000840000000a00000000000000000e40000000000000008d040bf00053c000000001f86d8391ee684d8800000728ab9970c26a0d3807000124a1000000548f6000374000c400000000000000000000000000005449597d0c8450f40030005dc000b9076000000002b4710001030002d449000000000000000000001500028200074800114000000000f80001e19c12000048846056000df00018e3ac000003f20000000035e4c00000031e784001fd3401488305d3da3c000000000534000002f800000000000000d8079000108000000002847c8cc0000001e800000000000001f8000e3826248644001da082708ac00d04e218b69b4304648fd1cd000000221f80de62864962110000b8815000000570000b85c00000000000102800000000001350002084611f000000000000f6000001533980009c000000000b293a0f0658881b231239cbd
  | 4 => 0xb00000000011a00054800000000000000000ccc800b00000083800190000cf0001da514000000000000005f41a37c699593664447517506c72c148a22de000000000080000005e23a000608000005100013f0fe80c001df3b67bce19f30000b80000015804d0000000058c000000000604000024032c000760000000000029600000000346000
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x28240550000030000718b3800014c05565d10120002006093401033c000010000209455c45350d42c28a730c84a15157118d540caa8b8886a8065461d1325403292ae730c84a0e1563584544c60ebb0a81926386151600c931a2ae630aa910c3476551318868ab8ca6a1c818594e6190a40a28e6a10a2a051573145415030b318a320281455c46355330838ecaa2639861a54580328c28ab98c2aa0219158d5210410868ecaa26208624645493104313322a590821891915244010
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0xa60008158714e61909428158794e6190a40815861cd42145408158798c5190140
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 664
  | 4 => 539
  | 3 => 25
  | 2 => 4
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
  | 6 => packedAt s4K6 (731+((h/13+packedAt s4K6 (640+(h % 13)*7) 7) % 69)*7) 7
  | 5 => packedAt s4K5 (20138+((h/221+packedAt s4K5 (17928+(h % 221)*10) 10) % 797)*11) 11
  | 4 => packedAt s4K4 (22451+((h/179+packedAt s4K4 (20482+(h % 179)*11) 11) % 1040)*11) 11
  | 3 => packedAt s4K3 (1273+((h/8+packedAt s4K3 (1225+(h % 8)*6) 6) % 37)*6) 6
  | 2 => packedAt s4K2 (243+((h/1+packedAt s4K2 (240+(h % 1)*3) 3) % 6)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0x87fff83f0ffffe0f0fff87fe1c0ffffc78f27f
  | 1 => 0xf83fffc00ffe3ff00f87f8ffe00fe0fe473c73
  | 2 => 0xffc0fffff07fc3fff007ff0ffff0ff0387cf9c
  | 3 => 0xffffff8003fffff8000fffff0003f80fe0
  | 5 => 0xffff0000000003fffffffff000000003fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0xa1040888121400030289011404412c50185225
  | 1 => 0x128a9106a52862708542c8ab20aa42aa432c52
  | 2 => 0x922212014004941004920249209208858498
  | 3 => 0x552cc4a4880cab29a9d0408d92cc0433680b60
  | 5 => 0x66308738ce7133cece6764c1030818c3f6f000
  | _ => 0
def s4Atlas : Atlas := ⟨7,rawDecor 47 s4Pos s4Neg, 0xfae8fae8f8a8f8a8fae8fae8f8a8f8a8fae8fae8f8a8f8a8fae8fae8f8a8f8a8fae8fae8f8a8f8a8fae8fae8f8a8f8a8fae8fae8f8a8f8a8fae8fae8f8a8f8a8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_16905
namespace PEqualNP.Outside.L_meta_16905
open PEqualNP.Outside.L_meta_16905.Model
def s5K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s5K4 (i*5) 5
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s5K4 (6+((h/1+packedAt s5K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0x1ff87c3f0ffffc3c3c38ff038f03ffff21c27f
  | 1 => 0xe1ffffc00ff87fc03fff0ffff003f83e3e7c73
  | 2 => 0xfe007ffff0ff87ffc03ff003fffc3fc1c78f9c
  | 3 => 0x7fffff0007ffffc00003ffffc001f80fe0
  | 4 => 0xffff8000000007fffffffffc00000001fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x8824c4889454440e1610992109124b2920c225
  | 1 => 0x44500806222080c00849021a902890940a1c52
  | 2 => 0x491111202800950402a2048a2482484470498
  | 3 => 0x596662a4883556a6ae8088934cb30119b80b60
  | 4 => 0x91844338ccc6673b3334cce008c20621f5e000
  | _ => 0
def s5Atlas : Atlas := ⟨4,rawDecor 31 s5Pos s5Neg, 0xfcecf8a8fcecf8a8fcecf8a8fcecf8a8fcecf8a8fcecf8a8fcecf8a8fcecf8a8fcecf8a8fcecf8a8fcecf8a8fcecf8a8fcecf8a8fcecf8a8fcecf8a8fcecf8a8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_16905
namespace PEqualNP.Outside.L_meta_16905
open PEqualNP.Outside.L_meta_16905.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xa401a00816803a0c712664410050dca001e0000800d921362b1a090a112ae008c0003600080000178b0cc800a7000b077279d9500d402220c132100a8c1c745c6273e34c8000000000000000560c381821404000040850002380850000001017fd5005fe54017f55005fc5400ffd4c03fe5300ff54c03fc5300ffd0c03fe4300ff50c03fc43007fd4801fe52007f54801fc52017fd0805fe42017f50805fc4200ffcc803fe3200ff4c803fc32007fd4401fe51007f54401fc51017fd0405fe41017f50405fc4100ffcc403fe3100ff4c403fc31007fc8401fe21007f48401fc21007fd4001fe50007f54001fc50017fd0005fe40017f50005fc4000ffcc003fe3000ff4c003fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x42004ff0821001ffe2108003f71084007fd8842000ffd9510005feca880037f65440013fb2a2000ff99510005fcca88003fd65440017eb2a2000ff19510005f8ca880037c65440013e32a200affd9110055fec888003bf64440015fb22200aff99110015fcc88802bfd64440157eb22200aff19110015f8c88802bbc64440055e322200affd5110057fca88802bfd5444015fe2a22009ffd8d1004dfec688027fe63440037f31a2009ff58d1004dfac688027fc63440037e31a2009ffd4d1004ffca688027fd5344013fe29a2009ffd0d1004ffc8688027fd4344013fe21a2000ffd8910005fec488003fe62440117f3122000ff58910005fac488003fc62440117e3122000ffd4910007fca488003fd5244001fe292200affd0910057fc848802bfd4244015fe2122009ffcc91004ffc6488027fd3244013fe1922000ffd451001ffca288003fd5144007fe28a200affd051001ffc828802bfd4144007fe20a2009ffcc51001ffc6288027fd3144007fe18a2000ffc851001ffc4288003f62144001fe90a2000fd4851001ff84288003ff5044001ff2822000ff54110007f8a08802bff4044015ff202200afe90110057fa808802bf94044015fe2022009ffcc11004ffc6088027fd3044013fe1822000ffc8110007fc4088003fd2044001fe1022003ffc411001ff62088003fe1044001fb0822004ffd941001dfeca0800ffe65040017f3282003df99410004fcca0800ffd65040017eb282003df59410004faca08013fc65040077e3282004ffd901001dfec80800ffe64040057f3202003ef990100157cc80800ffd640400d7eb202003ef590100057ac808013fc64040077e3202006ffd5010037fca80801bfd540400dfe2a02004ffd8c1001dfec60800ffe63040037f3182003f798c1000dbcc60800ffd630400b7eb182003f758c10005bac608013fc63040077e3182005ffd4c1002ffca608017fd530400bfe2982005ffd0c1002ffc8608017fd430400bfe2182004ffd881001dfec40800ffe62040117f3102003fb98810005dcc40800ffd62040017eb102003fb58810005dac408013fc62040077e3102000ffd4810007fca408003fd5204001fe2902006ffd0810037fc840801bfd420400dfe2102005ffcc81002ffc6408017fd320400bfe1902003bf9841001ffea20800ffe5104007fea882003ff1441001ffe820800ffe4104007fea082003ff1041001ffe620800ffe3104007fe9882003ff0c41001ffe420800ffe2104007fe9082003ff0841003dfcc008003ff5004009ff2802000ff54010027f8a00801bff4004009ff2002006ff50010027f88008017ff3004009ff1802005ff4c010027f86008003ff2004009ff1002000ff48010027f8400800fff1004007fb8802004ff8401001ff4200800ffd1004001fa8802003fe44010
  | 1 => 0x3fd61080017eb084008fd58420005eac210013fc6108001ffa884000ff94420007faa210003fc510801fffa08400fff9042007ffa821003ffc410801dff988400eff8c420077fa621003bfc3108011ff9084008ff88420047fa4210023fc21080217f3004000ffd4020027fca010003fd5008009fe280400fffd0020027fc801003ffd4008009fe200400effcc020027fc601003bfd3008009fe1804008ffc8020047de4010013fe2008011fd1004008ff48020007da4010023f92008007ffb2e2003bfd971001ffccb88002fe65c4007feb2e2000bf5971001ff8cb8800efc65c4007ffb262003bfd931001ffcc98800afe64c4007feb26200dbf5931001ff8c98800efc64c401bffaa6200dff9531006ffaa988037fc54c4007ffb1e2003bfd8f1001ffcc788006fe63c4007feb1e200cbf58f1001ff8c78800efc63c4019ffa9e200cff94f10067faa788033fc53c4019ffa1e200cff90f10067fa8788033fc43c4007ffb162003bfd8b1001ffcc588022fe62c4007feb162000bf58b1001ff8c58800efc62c4001ffa962000ff94b10007faa588003fc52c401bffa16200dff90b1006ffa8588037fc42c4019ff996200cff8cb10067fa6588033fc32c4007ffa8e2003ff9471001ffaa38800ffc51c4007ffa0e2003ff9071001ffa838800ffc41c4007ff98e2003ff8c71001ffa638800ffc31c4007ff90e2003ff8871001fec438800ffd21c4001fa90e2003ff08710007fea188003fe50c4001fea862000ff1431006ffe8188037fe40c401bfea06200dff10310067fe6188033fe30c4019fe986200cff0c310007fe4188003fe20c4001fe9062000ff08310027fecb08002ff6584001ff32c2000bf99610007facb08002fd6584009fe32c2000bf19610027fec90802eff6484017ff3242002bf9921005ffac90802efd6484009fe3242002bf1921005ffea90802ffe5484017feaa4200bff15210027fec70801eff638400fff31c2001bf98e1003ffac70801efd6384009fe31c2001bf18e1003ffea70801ffe538400ffea9c2007ff14e1003ffe870801ffe438400ffea1c2007ff10e10027fec508002ff6284001ff3142008bf98a10007fac508002fd6284009fe3142008bf18a10007fea508003fe5284001fea942000ff14a1005ffe850802ffe4284017fea14200bff10a1003ffe650801ffe328400ffe9942007ff0ca1004dfac308003ff5184007ff28c2000ff5461001ff8a30802fff4184007ff20c200bff5061001ff8830801fff3184007ff18c2007ff4c61001ff86308003ff2184007ff10c2000ff4861001ff8430800efe6084001ffa842004ff94210007faa108013fc5084017ffa042004ff9021005ff4810802ffd4084017fca042004ff1021003ffe6108013fe308400ffe9842004ff0c210007fe4108013fe2084001fe9
  | 2 => 0x20087fe8710043fe4388021fea1c4010ff10e2008dfac510003ff5288011ff2944000ff54a20047f8a51004fff4288011ff2144013ff50a20047f88510043ff3288011ff1944010ff4ca20047f86510013ff6188001ff30c4003bf98620007fac310002fd6188009fe30c4000ffd4620007fca310003fd5188001fe28c4013ffd062009ffc831004ffd4188027fe20c4010ffcc620087fc6310043fd3188021fe18c4008ffc8620007fc4310003fd2188011fe10c4008bf98220007fea110013fe5088001fea844004ff1422009ffe8110013fe4088027fea044004ff10220087fe6110013fe3088021fd1844010ff4c220087f26110013fc3088011ff9044000fbc8220047f64110003ff65480017fb2a4000dfd9520004feca90003fe65480017f32a4000ff59520005faca90003fc65480017e32a4000df19520004f8ca9004bff64480257fb224012ff99120015fcc89004bfd64480257eb224012ff19120015f8c89004bff5448025ff2a24012ff55120097f8a890047ff63480237fb1a4000f7d8d20005bec690047fe63480037f31a4011ff58d2008dfac690047fc63480037e31a4011f718d2000db8c690047ff5348023ff29a4011ff54d2008ff8a690047ff4348023ff21a4011ff50d2008ff88690003ff5248011ff2924000ff54920047f8a49004bff4248011ff2124012ff50920047f88490047ff3248011ff1924011ff4c920047f86490003ff61480017fb0a4000ff98520007fac290003fc61480077e30a4000ffd4520007fca290003fd5148001fe28a4012ffd0520097fc829004bfd4148025fe20a4011ffcc52008ffc6290047fd3148023fe18a4008ffc8520007de4290003fe2148001fe90a4000fb48520047f84290003ff5048001ff2824000ff54120007f8a09004bff4048025ff2024012ff50120097f88090047ff3048023ff1824011fe8c12008ffa6090047f93048023fe1824008ffc8120047f64090003fe2048001f71024004ffd9420045feca10023fe65080017f3284008df99420004fcca10023fd65080017eb284008df59420004faca10013fc65080117e3284004ffd9020045fec810023fe64080057f3204008ef990200157cc810023fd640801f7eb204008ef590200057ac810013fc64080117e320400fffd502007ffca81003ffd540801ffe2a04004ffd8c20045fec610023fe63080037f3184008f798c2000dbcc610023fd630801d7eb184008f758c20005bac610013fc63080117e318400effd4c20077fca61003bfd530801dfe298400effd0c20077fc861003bfd430801dfe2184008bf98820047fea410023fe5208011fea904008ff14820047fe8410023fe4208011fea104008ff10820047fe6410023fe3208011fe9904008ff0c820027fec210023fe61080077f3084008fd98420005ecc21002
  | 3 => 0xe10aa000ffd4150007f6a0a8003fe5054001bf282a01cffd01500e7fc80a8073fd4054039fe202a01bffcc1500dffc60a806ffd3054037fe182a01abf99450027fec82805eff641402fff320a002bf990500bffac82805efd6414009fe320a002bf190500c7fea82805f7f541402fff2a0a017ff550500befaa828063fc5414009ffb18a016bfd8c500b7fcc628006fe631402dfeb18a016bf58c50027f8c628006fc6314031ffa98a016dfd4c500b7fca62805bfd531402dbea98a018ff14c500b7fe862805bfe431402dfea18a016ff10c50027fec428003fe62140117f310a000ff58850005fac428013fc6214031ffa90a000ff94850006fca428003fd5214031fe290a000df148500bffe842805ffe421402ffea10a017ff108500b7fe642805bfe321402dfe990a016ff0c850027fec228003fe61140077f308a000ff58450005fac228013fc6114031ffa88a000ff94450006fca228003fd5114031fe288a000df144500bffe822805ffe411402ffea08a017ff104500b7fe622805bfe311402dfe988a016ff0c450007fe4228003fe2114001fe908a000ff084500cdfcc028063ff5014001bfa80a004ff94050007f4a028003fd5014001bea80a000fe540500bffe8028013fe401402ffea00a004ff100500b7fe6028013fe301402dfe980a004ff0c050047fecb90022ff65c8011ff32e4000bf99720047facb90002fd65c8011fe32e4008bf19720047fec990022ff64c8011ff3264002bf99320047fac990056fd64c8011fe3264008bf193200affea990057fe54c802bfeaa64015ff15320047fec790022ff63c8011ff31e4001bf98f20047fac790052fd63c8011fe31e4008bf18f200a7fea790053fe53c8029fea9e4014ff14f200a7fe8790053fe43c8029fea1e4014ff10f20047fea590023fe52c8011fea964008ff14b20047fe8590023fe42c8011fea164008ff10b20047fe6590023fe32c8011fe9964008ff0cb20047fec390023fe61c80077f30e4008ff58720005fac390023fc61c8001ffa8e4000ff94720007faa390003fc51c802bffa0e4015ff907200affa8390057fc41c8029ff98e4014ff8c7200a7fa6390053fc31c8011ff90e4008fbc8720047fc4390023fd21c8001f690e4008ff08720007fea190003fe50c8001fea864000ff143200affe8190057fe40c802bfea064015ff103200a7fe6190053fe30c8029fe9864014ff0c320027fecb10002ff6588001ff32c4000bf99620007facb10002fd6588009fe32c4000bf19620027fec91004eff6488027ff3244002bf9922009ffac91004efd6488009fe3244002bf1922009ffea91004ffe5488027feaa44013ff15220027fec710042ff6388021ff31c4001bf98e20087fac710042fd6388009fe31c4001bf18e20087fea710043fe5388021fea9c4010ff14e
  | 4 => 0x6bfc43d4031ffb16a000ff98b50045fcc5a8003fd62d40017eb16a018ff18b500c7fea5a80037f52d4001ff296a000ff54b50006faa5a8063fc52d403dffa16a01eff90b500f7fa85a807bfc42d4035ff996a01aff8cb500d7fa65a806bfc32d4031ffb0ea000ff9875001dfcc3a8003fd61d40017eb0ea018ff187500c7fea3a80037f51d4001ff28ea000ff54750006faa3a8063fc51d403dffa0ea01eff907500f7fa83a807bfc41d4035ff98ea01aff8c7500d7fa63a806bfc31d4001ff90ea000ff88750007fa43a8003fc21d403dffa06a01eff903500f7fa81a807bfc40d4035ff986a01aff8c3500d7fa61a806bfc30d40377eb2ca004ffd92500edfec928077fe64940057f324a01def992500157cc928077fd649403b7eb24a000ef592500057ac928013fc64940057e324a01dffd52500eefea928077fe549403bfeaa4a01ddf552500eff8a928013ff63940337fb1ca019ff98e5000dfcc728067de63940036f31ca019ff58e500cdfac728003dd63940016eb1ca004ff18e5000df8c728067ff5394033bfa9ca019ff94e500cffaa7280677d5394033fe29ca019ffd0e500cffc8728067fd4394033fe21ca004ffd8a50007fcc528022fe6294001feb14a000bf58a50027f8c528003ff5294001ff294a000df94a50007faa528003fc5294001be294a01dffd0a500effc8528077fd429403bfe214a019ffcca500cffc6528067fd3294033fe194a004ffd8650007fcc32800efe6194001feb0ca000bf58650027f8c328003ff5194001ff28ca000df94650007faa328003fc5194001be28ca01dffd06500effc8328077fd419403bfe20ca019ffcc6500cffc6328067fd3194033fe18ca000ffc8650007fc4328003fd2194001fe10ca016bf98250007fea1280037f5094001fda84a01dffd0250027fc8128077fd4094009fe204a019ffcc250027fc6128067fd3094009fe184a01cffd91500e5fec8a8073fe64540057f322a01cff591500e5fac8a8073fc64540057e322a01cffd51500e7fca8a8073fd5454039fe2a2a01bffd8d500ddfec6a806ffe63540037f31aa01bff58d500ddfac6a806ffc63540037e31aa01bffd4d500dffca6a806ffd5354037fe29aa01bffd0d500dffc86a806ffd4354037fe21aa000ffd8950005fec4a8003fe6254001feb12a000ff18950045f8c4a8003ff5254001bfa92a000ff94950007faa4a80037d5254001fe292a01cffd09500e7fc84a8073fd4254039fe212a01bffcc9500dffc64a806ffd3254037fe192a000ffd8550005fec2a8003fe6154001feb0aa000ff1855001df8c2a8003ff5154001bfa8aa000ff94550007faa2a80037d5154001fe28aa01cffd05500e7fc82a8073fd4154039fe20aa01bffcc5500dffc62a806ffd3154037fe18aa000ffc8550007fc42a8003fd2154001f
  | 5 => 0x462101ffaa31080ffc5188407ffa0c4203ff9062101ffa831080ffc4188407ff98c4203ff8c62101fec631080ffd3188447fa98c4203ff0c62101ffe431080fef2188411fb90c4203ffd822101ffcc110802fe6088407feb044200bf5822101ff8c110893ff4088449ff2044224ff50221127f8811088fff3088447ff1844223ff4c22111ff86110803ff65484017fb2a4200ff99521005fcca90803fd65484017eb2a4200ff19521005f8ca9088bff64484457fb224222ff99121015fcc89088bfd64484457eb224222ff19121015f8c89088bff5448445ff2a24222ff55121117f8a890887ff63484437fb1a4221ff98d2100dfcc690887fd63484437eb1a4221ff18d2100df8c690887ff5348443ff29a4221ff54d2110ff8a690887ff4348443ff21a4221ff50d2110ff88690803ff5248411ff2924200ff54921047f8a49088bff4248411ff2124222fb90921117fa849088bed4248411fe2124221ffcc921047fc6490887fd3248411fe1924200ffd452101ffca290803fd5148407fe28a4222ffd052101ffc829088bfd4148407fe20a4221ffcc52101ffc6290887f63148443fe98a4221fd4c52101ff86290823ff2148411fb90a4203ff8852101fdc4290803ff60484017fb024200ff98121007fac090803fc60484017e3024222ffd0121117fc809088bfd4048445fe2024221ffcc12110ffc6090887fd3048443fe1824203ffd942101dfeca1080ffe65084017f3284203ff59421005faca1080ffc65084077e3284203ffd902101dfec81080ffe64084057f3204203ff59021105fac81080ffc64084077e3204220ffd5021107fca810883fd5408441fe2a04203ffd8c2101dfec61080ffe63084037f3184203ff58c210fdfac61080ffc63084077e318421fffd4c210fffca61087ffd530843ffe298421fffd0c210fffc861087ffd430843ffe2184208bf98821047fea410823fe5208411fea904208ff14821047fe8410823fe4208411fea104208ff10821047fe6410823fe3208411fe9904208ff0c82101dfcc21080fff5108407ff2884203ff5442101ff8a21080fff4108407ff2084203ff5042101ff8821080fff3108407ff1884203ff4c42101ff8621080fff2108407f79084203ff8842101fec421080ffd2108407f69084208fd4842101ffec01080ffe60084017f3004203ff58021005fac01080ffc6008441ffa004220ff90021107fa8010883fc400843fff980421fff8c0210fffa601087ffc3008431ffb26a01ebfd93500f7fcc9a800afe64d403dfeb26a01ebf593500c7f8c9a800afc64d4031ffaa6a01eff953500f7faa9a8063fc54d4031ffb1ea01abfd8f500d7fcc7a8006fe63d4035feb1ea01abf58f500c7f8c7a8006fc63d4031ffa9ea01aff94f500d7faa7a8063fc53d4035ffa1ea01aff90f500d7fa87a8
  | 6 => 0x7feb20a228bf5905101ff8c82880efc6414431ffaa0a228ff95051147faa828863fc5414407ffb18a203bfd8c5101ffcc628806fe6314407ef318a201b798c5101ffac62889efd6314407eeb18a200b758c5101ff8c62880efc6314431ffa98a227ff94c5113ffaa628863fc531444fffa18a227ff90c5113ffa862889ffc4314407ffb10a203ff98851045fcc42880ffd62144017eb10a203ff188510c7fea4288037f5214401ff290a200ff54851006faa428863fc5214451ffa10a228ff90851147fa84288a3fc421444fff990a227ff8c85113ffa642889ffc32144077f308a203ffd445101efea22880ffe5114407fb288a203ff5445101efaa228803f55114407ffa08a203ff9045101ffa822880ffc4114407ff988a203ff8c45101ffa622880ffc3114407ffb00a203ff98051005fcc02880ffd60144017eb00a203ff18051147fe80288a3fe4014451fea00a228ff1005113ffe602889ffe301444ffe980a227ff0c051047fecb90822ff65c8411ff32e4200bf99721046fccb908027e65c8411feb2e4200bf59721046facb908027d65c8411fe32e4208bf19721047fec990822ff64c8411ff3264202bf993210477cc99080abe64c8411feb264226bf593210477ac990802bd64c8411fe3264208bf19321137fea99089bfe54c844dfeaa64226ff15321047fec790822ff63c8411ff31e4201bf98f21047fac790896fd63c8411fe31e4208bf18f2112ffea790897fe53c844bfea9e4225ff14f2112ffe8790897fe43c844bfea1e4225ff10f21047fea590823fe52c8411fea964208ff14b21047fe8590823fe42c8411f72164208ff50b21137da8590823fc42c8411ff9964208ff8cb21047fa6590823fc32c8401ffa8e4203ff94721007faa39080ffc51c844dffa0e4203ff90721137fa839080ffc41c844bff98e4203ff8c72112ffa639080ffc31c8411ffb064208ff98321005fcc190823fd60c84017eb064208ff18321137fe819089bfe40c844dfea064226ff1032112ffe6190897fe30c844bfe9864225ff0c32101ffecb1080eff6588407ff32c4200bf9962101efccb108027e6588407feb2c4200bf5962101efacb108027d6588407fe32c4203bf1962101ffec91080eff6488407ff3244202bf9922101ffac910892fd6488407fe3244203bf19221127fea910893fe5488449feaa44224ff1522101ffec71080eff6388407ff31c4201bf98e2101fbcc710806de6388407feb1c4223bf58e2101fbac710802dd6388407fe31c4203bf18e2111ffea71088ffe5388447fea9c4223ff14e2111ffe871088ffe4388447fea1c4223ff10e2110dfac510803ff5288411ff2944200ff54a21047f8a510893ff4288411ff2144224ff50a21047f8851088fff3288411ff1944223ff4ca21047f8651080efe6188407ffa8c4203ff9
  | 7 => 0xa88a6ff63d4453ff31ea201bf98f5114ffac7a88a6fd63d4431fe31ea201bf18f510c7fea7a88a77f53d4453ff29ea229ff54f5114efaa7a8863fc53d4453ffa1ea229ff90f5114ffa87a88a7fc43d4431ffb16a200ff98b51045fcc5a8803fd62d44017eb16a218ff18b510c7fea5a8803fe52d4401bf296a200ff54b510c7f8a5a88037c52d445dffa16a22eff90b51177fa85a88bbfc42d4453ff996a229ff8cb5114ffa65a88a7fc32d445dffa0ea203ff90751177fa83a880ffc41d4453ff98ea203ff8c75114ffa63a880ffc31d4431ffb06a200ff98351005fcc1a8803fd60d44017eb06a218ff18351177fe81a88bbfe40d445dfea06a22eff1035114ffe61a88a7fe30d4453fe986a229ff0c351155facb2880fff64944077fb24a203ff99251015fcc92880ffd649445b7eb24a203ff1925101df8c9288b7ff549445bff2a4a22dff5525116ff8a92880fff63944077fb1ca203ff98e5100dfcc72880ffd63944597eb1ca203ff18e5101df8c7288b3ff5394459ff29ca22cff54e51167f8a7288b3ff4394459ff21ca22cff50e51167f8872880fff6294407ff314a208bf98a5101ffac528802fd6294407fe314a200ffd4a51006fea528803fe5294401fea94a200df54a51007f8a5288b7ff429445bff214a22dff50a5116ff885288b3ff3294459ff194a22cff4ca51167f8652880efe6194407ffa8ca203dfd4651007eea32880fff4194407ff20ca203ff5065101ff8832880fff3194407ff18ca203ff4c65101ff8632880fff6094407ff304a200bf9825101ffac128802fd6094407fe304a22dffd025116ffc81288b7fd409445bfe204a22cffcc251167fc61288b3fd3094459fe184a22bffd915115dfec8a8803bf64544015fb22a22bff99151015fcc8a88affd64544577eb22a22bff19151015f8c8a88afbc64544055e322a22bffd515115efea8a88affe5454457feaa2a22bdf5515115ff8a8a88abff63544557fb1aa22aff98d5100dfcc6a88abfd63544557eb1aa22aff18d5100df8c6a88abff5354455bfa9aa22aff94d51157faa6a88ab7d5354455fe29aa22affd0d51157fc86a88abfd4354455fe21aa200ffd8951005fec4a8803fe6254401feb12a200ff18951045f8c4a8803ff5254401ff292a200df94951007faa4a8803fc5254401be292a22bffd095115ffc84a88affd4254457fe212a22affcc951157fc64a88abfd3254455fe192a200ffd4551007eea2a880ffe5154407bf28aa22bffd055101ffc82a88affd4154407fe20aa22affcc55101ffc62a88abfd3154407fe18aa200ffd8151005fec0a8803fe6054401feb02a200ff18151005f8c0a88afff4054457ff202a22bff5015115ff880a88abff3054455ff182a22aff4c151157f860a88a6fe6514407ffb20a203bfd905101ffcc82880afe641440
  | 8 => 0xf98e5200dfcc729023fd63948697eb1ca408ff18e52045f8c7290d3ff5394869ff29ca434ff54e521a7f8a7290d3ff4394869ff21ca434ff50e521a7f88729022fe6294811ffa94a408dfd4a52007dea529023ff4294811ff214a408ff50a52047f88529023ff3294811ff194a408ff4ca52047f86529023ff6194811ff30ca403bf98652047fac329002fd6194811fe30ca435ffd06521affc83290d7fd419486bfe20ca434ffcc6521a7fc63290d3fd3194869fe18ca408ffd8252047fcc129002fe6094811feb04a400bf58252047f8c1290d7ff409486bff204a435ff502521aff881290d3ff3094869ff184a434ff4c2521a7f861290cfff64548677fb22a433ff99152015fcc8a90cffd64548677eb22a433ff19152015f8c8a90cfff5454867bfaa2a433ff9515219ffaa8a90cf7d5454867fe2a2a432ffd8d52195fec6a9003df63548016fb1aa432ff98d5200dfcc6a90cbfd63548657eb1aa432ff18d5200df8c6a90cbdc63548036e31aa432ffd4d52196fea6a90cbfe5354865fea9aa432df54d52197f8a6a90cbff4354865ff21aa432ff50d52197f886a9003ff5254801f7a92a408ff94952046fca4a90cfff4254811ff212a433ff50952047f884a90cbff3254811ff192a432ff4c952047f864a9003ff61548017fb0aa400ff98552007fac2a9003fc61548077e30aa433ffd055219ffc82a90cffd4154867fe20aa432ffcc552197fc62a90cbfd3154865fe18aa400ffd8152005fec0a9003fe6054801feb02a400ff18152005f8c0a90cfff4054867ff202a433ff5015219ff880a90cbff3054865ff182a432ff4c152197f860a90c6fe6514811ffb20a408bfd9052047fcc82900afe6414811df320a402af99052047fac8290c2fd6414811deb20a400af59052047f8c829022fc6414831ffaa0a430ff95052187faa829063fc5414811ffb18a408bfd8c52047fcc629006fe6314811feb18a42fbf58c52047f8c629022fc6314831ffa98a42fff94c5217ffaa629063fc531485fffa18a42fff90c5217ffa86290bffc43148117f310a408ffd4852046fea429023fe5214811f7290a408ff54852046faa429003ed5214811ffa10a408ff90852047fa8429023fc4214811ff990a408ff8c852047fa6429023fc3214811ffb08a408ff9845201dfcc229023fd61148017eb08a408ff18452187fe82290c3fe4114861fea08a430ff1045217ffe62290bffe311485ffe988a42fff0c452047fec029023fe60148017f300a408ff58052005fac029023fc6014861ffa00a430ff90052187fa80290c3fc401485fff980a42fff8c05217ffa60290bffc3014831ffb26a22ebfd9351177fcc9a880afe64d445dfeb26a22ebf593510c7f8c9a880afc64d4431ffaa6a22edfd5351177fca9a88bbfd54d445dbeaa6a218ff153510c7fec7
  | 9 => 0x400a00501a00000000100604c00902400800c00900200000801400200301400102700501100900300000606300200400000300000d00200a00000501600101401000300000901400100400002800100a00a00000100600100304500000400100400c01800101100c00100000a01100a00a00300001200100000200001100200601300200100400101600003201504206d00000200800400300600301e00100100400c00903900000300700900000201500000300003500200300d00400603000700003800000301200200800000400300a01e00900301f00000500000000200100400300100200f01900100400000200000000a00100300001801900000b00000001800500e00600000000000000403700100200100000200400700601500000801b00000700b01600000b00000a01100a03b00100700600200a00400000000501700a00200600100900000401a00900401800400000b00000700300500000200200200602300000001600d00201f00300200000200000200001c00000d00000a00000600001e01900700900400500402301a00800200c00000400100000200100100001200200c00401b00500400301000500600300400000000500500d02b04400702500f00e01d00600300200100000400000b01700200000600300000100600a00200000000100000400300000100600000300100100000801100000600000001c00000101c00300100200401e03900001900100300501500100502301300101700900000200000002000000102f00000500600000900000600c00000f02000602e00000d00100100001600204300500200600100300300100904f00000000001500300500300401f0090000210000000180060090010000020030c7fec9a90daff64d486dff326a402bf993521b7fac9a90dafd64d4831fe326a402bf193520c7fea9a90db7f54d486dff2a6a436ff553521b6faa9a9063fc54d4831ffb1ea431bfd8f5218ffcc7a9006fe63d4863feb1ea431bf58f520c7f8c7a9006fc63d4831ffa9ea431dfd4f5218ffca7a90c7fd53d4863bea9ea418ff14f5218ffe87a90c7fe43d4863fea1ea431ff10f521b7fe85a9023fe42d486dfea16a408ff10b5218ffe65a9023fe32d4863fe996a408ff0cb520c7fec3a9003fe61d48077f30ea400ff58752005fac3a9063fc61d486dffa0ea436ff907521b7fa83a90dbfc41d4863ff98ea431ff8c75218ffa63a90c7fc31d4831ffb06a400ff98352005fcc1a9003fd60d48017eb06a418ff183521b7fe81a90dbfe40d486dfea06a436ff1035218ffe61a90c7fe30d4863fe986a431ff0c352195facb29023ff64948117fb24a408ff99252015fcc929023fd649486b7eb24a408ff19252045f8c9290d7ff549486bff2a4a435ff552521aff8a929023ff63948117fb1ca408f
  | 10 => 0x200031018081bc00029d00000004de18d18f41860002e993b883002800004d84ce2eb190853430a0ee2e10000e9e2b511196d0e4828a0000b1c36628100012e40360000ac11b48046362da809853a1cb00019d06f82da2780da0a3245b330a05485266a15b891c5780001a580004f84353c892ac7702961419e38af61662a51180ef600018f0000752068000122ccc0328247929800045e0000a30c22000000128c00044c36f8c5c39c40a0000c40cb03ca000000000051d31c0280e4e06d03c165c3da25b2269d900006962919cc40000000001ee00001dc2b205247d437e0d1904c5b277d298000102656133498b4eea74e3508204de60003d81538dde228360033cae06703681d50fe84d41b59a88b1a3653e01e6820203d01d020cf0a486338876053e765233800000073c11c17fc0003af1050640eb600000009f81d25ee3470464a3c6c93e59b480002923d38880f621111f604d0d1e2db11499c81fc3bb10d8fc41fe0c91cd8d906ea6b3056049062a10204610402a012b0de800012e4363ce094c1f21e51b09b9406400015480007c26d502e000000001e0c00000e86000224015c52a6dc0b180009ea00023e8000e067500e98000000360000095c0001ba2b510b08c81393be08840a274c26e9b149100540b211c057203313712a01a27323331e485ea4be30084dceac5053ea9e603e60a9004036cd961b20021ba000013f2ab1a48af24490441dc8e742ca10400002f25e60071e881cc000107000000015d2209cb00580ed20d92d042c77e25b8c34d205281ef03d0aa47e1078908408032011b191c5c462e2f801347e453c26c1fd45de7be0dfa008bce53d0aa810c378170348994c04661a20c90c4d7600501200200303600202100100000000300600800900000700300002200002001700c01900300100c01700500100200d00000b01901900203a02400100500003300500000800501700000000400000100a00b00200a00000200000300a01e00000000000a00500b00001600001701b01f00302400000000700a00900500900b00000600900001f00001b03309d00000400a00000100f00200500100000102500702f00400000101f00e00000300600a01600900400300e01402800900200000200001d00f00000700f00200000800000000100600000300e00800400603501200100201300100200700000400900200000100000000200000901f00100001f00e00400e00300200300001202303800300101202402600200000300500100301000000800000800d01201801300900a00100800c00000400100000000000000000d00301600000800000000f00200400700000200100401300100802000200000400800000100900000f00402700000f02403800200500100000600000c01700000002401f03d0030090020000000040
  | 11 => 0xb0000000000000000000000029300000005e12a587645285d505a93340005ba000098800055a21100000003853ac16ec0e203e00000000002aa1bd8000be872f0c895e021a0c41a10218aca7a41279f1858c5102a195dc0e84772ff205cd4e80740607c49d43f640c0f14ad03b3001178c530000000086082e6e9145931c72e0f620417b40fe47c32e0000000000069800038e51715290040006a8000080873054f00013dc11c00038e80000000000cc01740002651b3800000000012b083025224b172000063a19f32483ad00875a00007a04f27f20000000c7840005800000007001b60cc8e9253f27d8ed8d6251f38f0e4000021028686840003660001e9822608b1381f44c3e1df3ca80001a033d2ec08689be5eb000064c00033135f13481f05030249920824721300014840a47940181f47004850710000b543a32f980005f64af0d49ee809c00000016acf9281424c8e487566cc0da1eb88766bc371990000059020f8b70f360001471950d0e4090001b687fa65f000126827a33f2f78d7c01880f00017ecd600002b58000fe000027300000000001eb1c1c4c2000107800000018600e1de429c0ef34400000003342281890fd2000000193819400024991c40000001f81b784d43fc05c863c23a3072d3800075c6ca0ba90a8a22000136154c0906ee0b00000ab800000000bcd4c48a3e9800070667f30a800055800000004f0b0c70500005b8f164b11cd094008240c2289110cbc51424f916400000b2fe86243fa1a52d00000b42000055000083c4520001b080004950001d14a9000000014904e84680000f404fe0000c112a8c4c7e400005c8c1e0000000c183f07eb02294046e63a20af029c71075f016935c1a40000000000efe5473ed00000001ac29c85fcd9c4ec0ca87540ac00022b0930c7c000000118c8840001b90ac404017c000150018a4ca03d1c284222bf0f193b40002dd0000000a267380348a403926f937a85ac2a43d206b07fcace7200b6931085c2f81509c509180f036c87285da50c2fc16e011a22f05b926c1ce6cd3e51488e445b9378153477e78d2a2161c32853719a9f481b84e416a98145bc5731a70420f9c6b605a155407019c26e027c6261cf1680a8836277a3890cb45666291f793f893c6fd22e870c15a80d305013cd167193b597206b403b19b13c4b9a0793730584e7e5093c5139cb5c03019316bcd006ad0880f24a5460d2ac1ca00965d11251ab87407632a8a0648065992c29a60e1e66c2e514800142bd0e28274b0078c30907e44ee12709d82c4d0269d0301ebcea62a6095169044e1422228e04b106a338d99f417c69e00019e4c9e2c300880002003a700000000000000000a440003d816587bc00000000000000002d6009851101000023f90901905710001f50f0000027c800006a0912af07f862
  | 12 => 0x120d82e000000001b600c87c02947462b49db465400000000000000001289d5c0001320001b4400024409802ec5d21382630a202c404a3db8eb4de24272078a7800e11e38817d8f100001b513545463e81e19abcbc468c05b181ced803114c800033c1ab1611b18e2a5830d208f8c547a33e69f2000059337f848025c3491bc89ac5ae217223000000024939810f0fdc00007a9c249e4000118000024c2f733d800070e2800c38a902125fa3548e4cba44d01448c603a03a80000aa04f64470f71d286360d40000428d542313f000000004c52ca8e843027663948160d2836920386a000000006e9e589d000000012e03b600029d80002b47b2403000005219d0000818ea4000232800079875c19800001c67b41ec9bf800022a3b88ec8b980001dd000020646f21f00000007a81c88914ca43a50000bd8ed013a0eb802400023500002240c67bd00009340001830000cbc8d200010e09bc10048300009a46a611632303e8000000000179400000039e80007188012aba0580ea2761160ffc93a5fc2ae84148223291690bb8cb666405094cc6a04960df0df42fa1e625200000003522e318380004062d100000000003e198eccde65631b8bf44e65a33639b9cc462972370c040d46b912e94842ec39f3a119b8fd06e037600000008111a79adc7f44a52a48000a0c2f32070000edc1331918000d8811f33f190c59a21e0988304c7270412903004d07b90dc920496c7332509b209286040fa121cf780993d606ec0b25f12c11fdc6b60fc11911a8bb443f314166895c2c13b81cec21604c090985865c699219856c5f844a31804bc0a07db0150e500782cf18002a01b24d32610f3c17450703b9fbc3341431cf1fc42180030b98118ae801217905707d62ae03298fc1ca0550c508d0c984c01b79bec84a6d40c604542fc7fe1f68564f8a027162915c0447ed1e00550056000319065c82c31622011883540ec1069ad43d657d00019340004ef2749fe4cec43727b0000e102ba0309074d7e0000f480000005c91db8de08603c61f200009821b829a0d5418c0b806d07504aa3f40e30e10e3824601b073464a80b0001830dae51a18704a022459c0529514e5a5591270d50dba59d2b7001892e1990001c987a80002938000df45541fb8f6c5081f50b41394a626b427994d4000141162176c00065d3bb98e87cc01000014b000014725e8000afe00000b1f8c29e50025e11d084667800000740001d13e2129c0001c40bd059cba066700018ac1342643041ca86380000001c68b7c42b0f11364bd06f63e08000dd47372af9dd81044b324111842e20b229916fce82275000011003414c39a87ec43a5e932118404bc45f22a9eb4ffa2600ee826017a0d7037026c35c4391eb8cac00042807d9c3028051808d12344720932271e187dc28d2e1847001e29b36
  | 13 => 0x368054aa05d726714f86b24bf00019dc0000002f50a180000001e10338ec216c17191e80003431e38014d1a74837107680006ba3970000fb80002ef8f3861600014280000000003aa8d600c835e0000000b8e5411331e5057c30830591700005dc00017dc4f40bc19d80dc4065cb27c181800000000012c01c20001e09be012c2c01fc1ed4d400003d09a7c4826e137a0000bc00003af1da442a7781e58c4814850f24817503e43d53c103cc0000003b780000001060bb88b4e04414259163c2967c20001a1839874716481cc61424011988e89f87bb0000000cd600016a017c4b46ed08d9438976382138843c0000003c98e640fc0ae2b9180c000773196000000011428200004025251c700003903051e405580000e00ba1d9c00031f0001b0404805a0d397b03c03700911160b8a047042879cf0e7902de1efc9d63a600015804267b328e0000f984321159b6055600000008dcb080012361168b9e3b109684608d649c08218740005dd1c3000071e5bd0558d1ceb224800016c000037f000061000012500016c44783713d29f6431618d0000c0c4085f50000c102a20662db0864fc4762000007c44c61403380000000002811ea46c62b007b9448a5c4380f21f3ce3e0003619e78d364e12a30000000224233206cc426b22168188b6e0002c59710d380003f3000000036200000000000000a282287be61c39c9244f060141500c6480a36e25107008ea34d37b97584be4d131989c87e68053250de8ff47161ba1ff059841c05980e4ed47e504a92488341531df0be8c827d80cb05a448628f3d5184c6047891590b9491c4cb2568000dd652900003080007b63288ea80420000001c1891200009f1d3445c0003a200340003cd17305ecf4032221799f06ba1071d20908b501f7331880067c6313229e647fc65a32a837c84014811e8ddd0005a923b0db45fe0003fc082457634000000007ce1d602d9c941d0713000000000081016f83a80001233e395f099e0001058060b4c6753eb8fd40006bd0000a9cd4a6f21de80008e659100000001204c93448c3cc4a2d128594ac9743f921d0cdc5d40530001fa850e42628a90547605921ce005c7144ac3450a4c90821f0000b848f60001de0bc41084e210a1e10cd02fe1f285e0dc80fd0790ab464e3b51e88000c6a0002850000d042b42b78f7481a34a2641c8c6ae4f42e08704b124a026b02985e073e38880fc6724803e80a703244e30001e7ce2e0002ba874856c4e027f95d8340000049192cb9c56227d032c9b658132b8a080f60003808e748e472b2c619e80de5961ab1a543f44a90da8708c681e127e9fcccda05e035800087a6cf0001fece6c71816986c0ab600034217e4e1c5e400020480002e70000334f5677400000007d2333000186400059e000000068280a16c17c80007de2cf821c7
  | 14 => 0x74b2840ba08a815f17a113cd701ec3ef845c0e02b800015b44b81ad10900b86747f631603540d860940d1b4cc5e67331380006a27972d913306ec0e40001c2ca2c80e2ef15e840e443000000059034832816cca6c7ec0db896421c2ec186023c62823f05f8e54c362e03ce8d183443e24049aac8f051b0510be44fa5382ca1638d0a1f63c0966c9b45d93ae863876854c34d028cdb652d0f50fec5345421e21010acc3da2b186200e434c0d795b0d264c330f0ce02ae4b503b1ab059c40b33296b004a3962cc16b42ca3ac0000d700000341f1800077261800001f0e1a0000cd84d4ea23d337e000086812c3ee800000009c2d2998889665934b9a0cc443453b00c900002af2c50e2c00000012a1f9c00047e00000000003440578c2471a78f13c0f7044a16f35208ec1281fc02108884b033c3eb185c0007400001910000734000000018e0cc0ef000000000004f05a834c0003ff914c7c0263297851893057e1
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0xf7458810006ee7458810006ed7458810006ec7458810006ef5458810006ee5458810006ed5458810006ec5458810006ef7358810006ee7358810006ed7358810006ec7358810006ef5358810006ee5358810006ed5358810006ec5358810006ef4358810006ee4358810006ed4358810006ec435881001eef715881001eee715881001eed715881001eec715881001eef515881001eee515881001eed515881001eec515881001eef415881001eee415881001eed415881001eec415881001eef315881001eee315881001eed315881001eec3158810026ee7058810026ec7058810026ee5058810026ec5058810006ef4058810026ee4058810006ed4058810026ec4058810006ef3058810026ee3058810006ed3058810026ec305881001eef105881001ee71058810026ee105881001eed1058810026ec10588100c4ff76d4810024fe76d4810004fd76d4810024fc76d48100c67e65d48100067d65d48101b6be64d4810006bd64d481018ede63d4810006dd63d4810046ee62d4810006ed62d4810044ff7694810024fe7694810004fd7694810024fc76948100067e65948100067d65948101aebe6494810006bd64948101a6de6394810006dd6394810046ee6294810006ed6294810004ff7654810024fe7654810004fd7654810024fc76548100067e65548100067d655481019ebe6454810006bd6454810005df735481002ddc7354810196de6354810006dd6354810046ee6254810006ed6254810005fb7054810025f87054810044ff7614810024fe7614810004fd7614810024fc76148100c67e65148100067d6514810035be7414810005bd7414810186be6414810006bd641481017ede6314810006dd6314810046ee6214810006ed6214810004fd76d40100c67e65d40100067d65d40100f6be64d4010006bd64d40100d6de63d4010006dd63d4010006ee62d4010006ed62d4010004ff76540100067e65540100067d65540100e6be6454010006bd64540100dede6354010006dd6354010006ee6254010006ed6254010004fd76c80100067e65c80100067d65c80100aebe64c8010006bd64c80100a6de63c8010006dd63c8010046ee62c8010006ed62c8010004ff76480100057f75480100057c75480100067e65480100067d6548010096be6448010006bd6448010005df734801002ddc734801008ede6348010006dd6348010046ee6248010006ed6248010025f77644010006f77644010004f77644010007777544010007747544010027766544010027756544010007b774440101bfb47444010027b66444010027b56444010027d66344010027d56344010026f76244010027e66244010006f56244010027e56244010006e56244010025f7704401001ff37044010026f66044010027f26044010027f25044010007f15044010
  | 1 => 0x901001ebe315901001ebd315901001ebc315901001ebf215901001ebe215901001ebd215901001ebc2159010036bf7059010026be7059010036bd7059010026bc7059010026be5059010026bc5059010006bf3059010026be3059010006bd3059010026bc3059010026be2059010026bc205901001ebf1059010026be105901001eba105901001ebd105901001eb91059010026bc1059010006df7558c10006de7558c10006dd7558c10006dc7558c10006df7458c10006de7458c10006dd7458c10006dc7458c10006df5458c10006de5458c10006dd5458c10006dc5458c10006df7258c10006de7258c10006dd7258c10006dc7258c10006df4258c10006de4258c10006dd4258c10006dc4258c1001edf7158c1001ede7158c1001edd7158c1001edc7158c1001edf5158c1001ede5158c1001edd5158c1001edc5158c1001edf4158c1001ede4158c1001edd4158c1001edc4158c1001edf2158c1001ede2158c1001edd2158c1001edc2158c1002edf7058c10026de7058c1002edd7058c10026dc7058c10026de5058c10026dc5058c10006df4058c10026de4058c10006dd4058c10026dc4058c10026de2058c10026dc2058c1001edf1058c10026de1058c1001edd1058c10026dc1058c10046ef7598810046ee7598810046ed7598810046ec7598810046ef7498810046ee7498810046ed7498810046ec7498810006ef5498810006ee5498810006ed5498810006ec5498810046ef7398810046ee7398810046ed7398810046ec7398810006ef5398810006ee5398810006ed5398810006ec5398810006ef4398810006ee4398810006ed4398810006ec439881001eef719881001eee719881001eed719881001eec719881001eef519881001eee519881001eed519881001eec519881001eef419881001eee419881001eed419881001eec419881001eef319881001eee319881001eed319881001eec3198810026ee7098810026ec7098810026ee5098810026ec5098810006ef4098810026ee4098810006ed4098810026ec4098810006ef3098810026ee3098810006ed3098810026ec309881001eef1098810026ee109881001eed1098810026ec1098810004ff75588100c4fc7558810004ff7458810014fe7458810004fd7458810014fc7458810004ff735881000cfe7358810004fd735881000cfc7358810024ff7258810026ef7258810006ef4258810006ee4258810006ed4258810006ec4258810006ef3258810006ee3258810006ed3258810006ec325881001cff715881001cfe715881001cfd715881001cfc715881001eee215881001eec2158810044ff7058810024fe7058810044fd7058810024fc7058810026ee2058810026ec205881001ef71058810006ef7558810006ee7558810006ed7558810006ec7558810006e
  | 2 => 0x67d74994100c67c74994100c67f73994100067e73994100067d73994100c67c73994100067f43994100067e43994100067d43994100067c43994100c67f72994100067e72994100067d72994100c67c72994100067f42994100067e42994100067d42994100067c42994100067f32994100067e32994100067d32994100067c329941001e7f719941001e7e719941001e7d719941001e7c719941001e7f419941001e7e419941001e7d419941001e7c419941001e7f319941001e7e319941001e7d319941001e7c319941001e7f219941001e7e219941001e7d219941001e7c21994100267e70994100267c70994100067f40994100267e40994100067d40994100267c40994100067f30994100267e30994100067d30994100267c30994100267e20994100267c209941001e7f10994100267e109941001e7d10994100267c1099410024ff75594100267f7559410004ff7459410014fe7459410004fd7459410014fc74594100067f54594100067e54594100067d54594100067c5459410004ff735941000cfe7359410004fd735941000cfc73594100067f53594100067e53594100067d53594100067c5359410004ff7259410044fc725941001cff715941001cfe715941001cfd715941001cfc715941001e7e515941001e7c51594100c4ff7059410024fe70594100dcfd7059410024fc70594100267e50594100267c50594100067f74594100067e74594100067d74594100067c74594100067f73594100067e73594100067d73594100067c73594100067f43594100067e43594100067d43594100067c43594100067f72594100067e72594100067d72594100067c72594100067f42594100067e42594100067d42594100067c42594100067f32594100067e32594100067d32594100067c325941001e7f715941001e7e715941001e7d715941001e7c715941001e7f415941001e7e415941001e7d415941001e7c415941001e7f315941001e7e315941001e7d315941001e7c315941001e7f215941001e7e215941001e7d215941001e7c21594100267e70594100267c70594100067f40594100267e40594100067d40594100267c40594100067f30594100267e30594100067d30594100267c30594100267e20594100267c205941001e7f10594100267e105941001e7d10594100267c1059410006bf7559010006be7559010006bd7559010006bc7559010006bf7359010006be7359010006bd7359010006bc7359010006bf5359010006be5359010006bd5359010006bc5359010006bf7259010006be7259010006bd7259010006bc7259010006bf3259010006be3259010006bd3259010006bc325901001ebf715901001ebe715901001ebd715901001ebc715901001ebf515901001ebe515901001ebd515901001ebc515901001ebf315
  | 3 => 0x4648851001fd6738851001fd573885101eef763885101eef563885101e5f57288510046f66288510046f46288510025f6708851001ef7608851001ff360885101dff240885101dff14088510044fc76485100067f65485100067c6548510006bf6448510116bc6448510006ef6248510046ec624851001fe42148510005fb7048510005f87048510046f47648510044f47648510007776548510007746548510007b764485101cfb464485101d6f763485101d6f5634851001df7724851001fe77248510007e76248510046f66248510046f46248510007e462485101cfe642485101cfe54248510007f37048510025f47048510007f0704851001ef7604851001ff360485101cff240485101cff1404851001cfe76d41100067f65d41100c67c65d4110006bf64d41100f6bc64d411001df671d4110005f571d4110004fe76941100067f65941100067c6594110055be7494110005bd7494110006bf64941100eebc649411004dde7394110005dd73941100c4ff7654110004fd765411001cfc76541100067f65541100067c6554110006bf64541100e6bc6454110005f7715411001df47154110004fe76141100067f65141100c67c6514110006bf64141100bebc641411001cfe76c811001cfc76c81100067f65c81100067c65c8110006bf64c81100aebc64c8110006ef62c8110046ec62c811001df671c8110005f571c8110007e521c8110004fe76881100067f65881100067c6588110006bf648811009ebc6488110044ff7648110004fd764811001cfc76481100057f75481100057c75481100067f65481100067c6548110006bf6448110096bc6448110005df734811004ddc7348110006ef6248110046ec6248110005f7714811001df47148110007e52148110004fe76081100057e75081100057d75081100067f65081100067c6508110055be7408110005bd7408110006bf640811007ebc640811004dde7308110005dd730811001df67108110005f571081100067f65841100067c6584110006bf648411005ebc648411001dfa708411001efb608411001df67684110026f6768411001cf67684110007776584110007746584110007b764841101c7b46484110025f77284110005f57284110025f67084110026f7608411001ff36084110027f240841101c7f14084110024fe75994100267e75994100c4ff7499410014fe7499410004fd7499410014fc74994100c67f54994100067e54994100067d54994100c67c54994100c4ff739941000cfe7399410004fd739941000cfc73994100c67f53994100067e53994100067d53994100c67c5399410044fe7299410004fd729941001cfe719941001cfc719941001e7e519941001e7c5199410024fe7099410024fc70994100267e50994100267c50994100c67f74994100067e7499410
  | 4 => 0x91101f6be31d9110006bd31d91101f6bc31d91101f6be21d91101f6bc21d91101f6bf70d9110056be70d9110056bd70d9110056bc70d9110006bf30d9110006be30d9110006bd30d9110006bc30d91101f6bf10d9110056bd10d91101f6bc10d9110044fe76d89100067f65d89100067c65d8910006bf64d8910006bc64d89100c4fe75d8910004fd75d8910004ff74d8910014fe74d8910004fd74d8910014fc74d8910004ff73d891000cfe73d8910004fd73d891000cfc73d8910006ef32d8910006ec32d891001cfe71d891001cfc71d8910024fe70d8910024fc70d89100057e75989100057d75989100067f65989100067c6598910055be7498910005bd7498910006bf6498910006bc6498910006ef62989100057f75589100057c75589100067f65589100067c6558910005bf7458910055bc7458910006bf6458910006bc6458910005df735891004ddc7358910004ff75589100067f75589100047f75589100c4fc75589100067c75589100047c7558910004ff7458910006bf7458910004bf7458910014fe7458910004fd7458910014fc7458910006bc7458910014bc7458910004ff7358910006df7358910004df735891000cfe7358910004fd735891000cfc7358910006dc735891000cdc7358910006ef7258910004ff7158910006f77158910004ff7058910006fb7058910004fe76189100067f65189100067c6518910006bf6418910006bc6418910046ee6218910006ed62189100c4ff76d4910004fe76d4910004fd76d49100c4fc76d49100067f65d49100c67c65d4910006bf64d49101b6bc64d4910044ff7694910004fe7694910004fd7694910044fc76949100067f65949100067c6594910006bf64949101aebc649491001df67194910005f57194910004ff7654910004fe7654910004fd7654910004fc76549100067f65549100067c6554910006bf645491019ebc6454910005df735491004ddc7354910044ff7614910004fe7614910004fd7614910044fc76149100067f65149100c67c6514910055be7414910005bd7414910006bf6414910186bc641491001df67114910005f57114910005fa7014910005f97014910004fe76d45100067f65d45100c67c65d4510006bf64d4510176bc64d4510005fa70d4510005f970d4510004fc76545100067f65545100067c6554510005bf7454510055bc7454510006bf645451015ebc6454510005fb7054510005f8705451001ff01054510004fe76c8510024fc76c85100057e75c85100057d75c85100067f65c85100067c65c8510055be74c8510005bd74c8510006bf64c8510136bc64c8510006ef62c8510046ec62c8510005fa70c8510005f970c8510005f6768851001ef6768851001f76758851001f757588510007776588510007746588510007b764885101dfb
  | 5 => 0xcfe7399510004fd739951000cfc7399510044fe7299510004fd7299510004fd71995100c6f57199510004fd70995100c6f97099510005bf7459510055bc7459510006bc64595100067f7559510004ff7459510006bf7459510004bf7459510014fe7459510004fd7459510014fc7459510006bc7459510014bc7459510004ff735951000cfe7359510004fd735951000cfc7359510004ff7259510044fc7259510004ff7159510006f77159510004ff7059510006fb7059510004fe76195100067d6519510006bc64195100c67e75195100c4ff7419510014fe7419510004fd7419510014fc74195100c67f54195100067e54195100067d54195100c67c54195100c4ff731951000cfe7319510004fd731951000cfc73195100c67f53195100067e53195100067d53195100c67c5319510044fe7219510004fd721951001cfe711951001cfc7119510024fe7019510024fc70195100057e76195100067e76195100047e76195100067f64195100067e64195100067d64195100067c64195100073c64195100063c64195100067f63195100067e63195100067d63195100067c63195100077a40195100077940195101ff7b10195101ff7810195100c67f74195100067e74195100067d74195100c67c74195100c67f73195100067e73195100067d73195100c67c73195100067f43195100067e43195100067d43195100067c43195100c67f72195100067e72195100067d72195100c67c72195100067f42195100067e42195100067d42195100067c42195100067f32195100067e32195100067d32195100067c32195100c67f71195101fe7e71195100067d71195100c67c71195100067f41195101fe7e41195100067d41195101fe7c41195100067f31195101fe7e31195100067d31195101fe7c31195101fe7e21195101fe7c21195100c67f70195100067d70195100067f40195100067e40195100067d40195100067c40195100067f30195100067e30195100067d30195100067c30195101fe7f10195100067d10195101fe7c1019510055be76d9110056be76d9110014be76d9110006bf65d91100073f65d91100063f65d9110006be65d9110006bd65d9110006bc65d91100073c65d91100063c65d9110006bf63d9110006be63d9110006bd63d9110006bc63d91101f7bb70d9110057b870d91101f7bb10d91101f7b810d9110006bf75d9110006be75d9110006bd75d9110006bc75d9110006bf73d9110006be73d9110006bd73d9110006bc73d9110006bf53d9110006be53d9110006bd53d9110006bc53d9110006bf72d9110006be72d9110006bd72d9110006bc72d9110006bf32d9110006be32d9110006bd32d9110006bc32d9110006bf71d91101f6be71d9110056bd71d91101f6bc71d91101f6be51d91101f6bc51d9110006bf31d
  | 6 => 0xc7058a10026ee2058a10026ec2058a100c4ff76d4a10024fe76d4a10004fd76d4a10024fc76d4a100c67e65d4a100067d65d4a10044ff7694a10024fe7694a10004fd7694a10024fc7694a100067f6594a100067c6594a10004ff7654a10024fe7654a10004fd7654a10024fc7654a100067e6554a100067d6554a10005df7354a1003ddc7354a10044ff7614a10024fe7614a10004fd7614a10024fc7614a100067f6514a100c67c6514a1005dbe7414a10005bd7414a10025fa7014a10005f97014a100c67e65d46100067d65d4610025fa70d4610005f970d46100067e65546100067d6554610005bf745461005dbc7454610005fb7054610025f870546100057e75c86100057d75c861005dbe74c8610005bd74c8610046ee62c8610006ed62c8610025fa70c8610005f970c8610044ff7648610046ee6248610006ed6248610005fb7048610025f870486100267f65d42100267c65d42100267f65542100267c6554210026ef62c8210026ec62c82100057f75482100057c7548210005df734821003ddc7348210026ef6248210026ec6248210025f576c421001ef576c4210026f762c4210006f562c4210027f260c4210006bc64d9510004ff74d9510014fe74d9510004fd74d9510014fc74d95100067f54d95100067e54d95100067d54d95100067c54d9510004ff73d951000cfe73d9510004fd73d951000cfc73d95100067f53d95100067e53d95100067d53d95100067c53d9510044fe72d9510004fd72d95100067f64d95100067e64d95100067d64d95100067c64d95100073c64d95100063c64d95100067f63d95100067e63d95100067d63d95100067c63d95100077a40d95100077940d95102077b10d95102077810d95100067f74d95100067e74d95100067d74d95100067c74d95100067f73d95100067e73d95100067d73d95100067c73d95100067f43d95100067e43d95100067d43d95100067c43d95100067f72d95100067e72d95100067d72d95100067c72d95100067f42d95100067e42d95100067d42d95100067c42d95100067f32d95100067e32d95100067d32d95100067c32d95100067f71d95102067e71d95100067d71d95102067c71d95100067f41d95102067e41d95100067d41d95102067c41d95100067f31d95102067e31d95100067d31d95102067c31d95102067e21d95102067c21d95102067f70d95100067d70d95100067f40d95100067e40d95100067d40d95100067c40d95100067f30d95100067e30d95100067d30d95100067c30d95102067f10d95102067c10d95100067f6599510055be7499510005bd7499510006bc64995100c4fe75995100047e75995100c4ff7499510014fe74995100c6be7499510014be7499510004fd74995100c6bd7499510004bd7499510014fc74995100c4ff7399510
  | 7 => 0x4b1001df67114b10005f57114b1001df77648710006f7764871001ef76348710216f5634871001fe7724871001fe76248710046f6624871001ef4624871001fe4624871020fe6424871020fe54248710025f470487100c67e65d43100067d65d431001df671d4310005f571d43102067f65943102067c659431006dbe7494310005bd7494310065de7394310005dd73943100067e65543100067d6554310005f7715431001df471543101fe7f65143100c67c6514310046ee62c8310006ed62c831001df671c8310005f571c8310007e521c8310025f47188310044ff76483100057f75483100057c7548310005df7348310065dc7348310046ee6248310006ed6248310005f7714831001df47148310007e521483100057e75083100057d750831006dbe7408310005bd7408310065de7308310005dd730831001df67108310005f57108310024ff74d9610014fe74d9610026be74d9610014be74d9610004fd74d9610026bd74d9610004bd74d9610024fc74d96100067f54d96100067d54d9610024ff73d961000cfe73d9610026de73d961000cde73d9610004fd73d9610026dd73d9610004dd73d9610024fc73d96100067f53d96100067d53d9610044fe72d9610004fd72d9610026f571d96102067e51d96102067c51d9610026fa70d9610004fd76996100267f65996100c4ff7499610014fe7499610004fd7499610014fc74996100c4ff739961000cfe7399610004fd739961000cfc7399610044fe7299610004fd7299610024fe70996100267e50996100267c50996100267c65596100267f7559610004ff7459610014fe7459610004fd7459610014fc7459610004ff735961000cfe7359610004fd735961000cfc7359610004ff7259610044fc7259610024fc70596100267e50596100267c50596100c4fe75196100267e7519610024ff7419610014fe7419610004fd7419610024fc74196100c67f54196100067d5419610024ff731961000cfe7319610004fd7319610024fc73196100c67f53196100067d5319610044fe7219610004fd7219610026f571196101fe7e51196100c67c5119610026fa70196100c4fe75d8a10004fd75d8a10024ff74d8a10014fe74d8a10004fd74d8a10024fc74d8a10024ff73d8a1000cfe73d8a10004fd73d8a10024fc73d8a10026f571d8a10026fa70d8a10004fd7698a10026ef6298a10026ec6298a10044ff7658a100057f7558a100057c7558a10005df7358a1003ddc7358a10026ec6258a10004ff7558a100067f7558a100047f7558a100c4fc7558a100067c7558a100047c7558a10004ff7458a10014fe7458a10004fd7458a10014fc7458a10004ff7358a10006df7358a10004df7358a1000cfe7358a10004fd7358a1000cfc7358a10006dc7358a1000cdc7358a10026ef7258a10024f
  | 8 => 0x6dd63d442001ef661d4420006f561d442001cff7694420024fe7694420004fd76944200067e65944200067d659442016ebe6494420006bd6494420166de6394420006dd639442001ef66194420006f56194420004ff7654420004fd7654420024fc76544200067e65544200067d6554420005bf745442007dbc745442015ebe6454420006bd6454420156de6354420006dd635442001ef66154420006f56154420005fb7054420025f8705442001cff7614420024fe7614420004fd76144200c67e65144200067d6514420146be6414420006bd6414420075de7314420005dd731442013ede6314420006dd631442001ef66114420006f56114420004fd76d40200c67e65d40200067d65d40200f6be64d4020006bd64d40200d6de63d4020006dd63d4020006f661d4020006f561d4020004ff76540200067e65540200067d65540200e6be6454020006bd64540200dede6354020006dd6354020006f66154020006f56154020025ef7648020006ef7648020004ef76480200076f75480200076c75480200276e65480200276d6548020027ae6448020027ad6448020007cf734802022fcc7348020027ce6348020027cd6348020027e66148020006ed6148020027e56148020006e56148020025ef7048020047eb7048020026ee6048020027ea6048020027ea5048020007e9504802001e7e75997100c4ff7499710014fe7499710004fd7499710014fc74997100c67f54997100067d54997100c4ff739971000cfe7399710004fd739971000cfc73997100c67f53997100067d5399710044fe7299710004fd729971001cfe719971001e7e519971001e7c519971001e7f7559710004ff7459710006bf7459710004bf7459710014fe7459710004fd7459710014fc7459710006bc7459710014bc74597100067f54597100067d5459710004ff735971000cfe7359710004fd735971000cfc73597100067f53597100067d5359710004ff7259710044fc725971001cfc715971001e7e515971001e7c5159710004ff7558b100c4fc7558b10004ff7458b10014fe7458b10004fd7458b10014fc7458b10004ff7358b1000cfe7358b10004fd7358b1000cfc7358b1001eef7258b10006ee4258b10006ed4258b1001cfc7158b1001eee2158b1001eec2158b100c4ff76d4b1001cfe76d4b10004fd76d4b1001cfc76d4b102267f65d4b100c67c65d4b10044ff7694b1001cfe7694b10004fd7694b1001cfc7694b100067e6594b100067d6594b1001df67194b10005f57194b10004ff7654b1001cfe7654b10004fd7654b1001cfc7654b1021e7f6554b1021e7c6554b10005df7354b10065dc7354b10005fb7054b10005f87054b10044ff7614b1001cfe7614b10004fd7614b1001cfc7614b100c67e6514b100067d6514b1006dbe7414b10005bd741
  | 9 => 0xf4158c20006de4158c20006dd4158c20006dc4158c20046df2158c20046de2158c20046dd2158c20046dc2158c20076df7058c20026de7058c20076dd7058c20026dc7058c20026de5058c20026dc5058c20006df4058c20026de4058c20006dd4058c20026dc4058c20046df2058c20026de2058c20046da2058c20046dd2058c20046d92058c20026dc2058c20026de1058c20026dc1058c2001ef7759842001ef6759842001ef5759842001ef4759842001ef7749842001ef6749842001ef5749842001ef47498420006f75498420006f65498420006f55498420006f4549842001ef7739842001ef6739842001ef5739842001ef47398420006f75398420006f65398420006f55398420006f45398420006f74398420006f64398420006f54398420006f4439842001ef7729842001ef6729842001ef5729842001ef47298420046f75298420046f65298420046f55298420046f45298420046f74298420046f64298420046f54298420046f44298420046f73298420046f63298420046f53298420046f43298420026f67098420026f47098420026f65098420026f45098420006f74098420026f64098420006f54098420026f44098420006f73098420026f63098420006f53098420026f43098420046f72098420026f62098420046f52098420026f42098420004ff75584200c4fc7558420004ff7458420014fe7458420004fd7458420014fc7458420004ff735842000cfe7358420004fd735842000cfc7358420026f77158420006f74158420006f64158420006f54158420006f44158420006f73158420006f63158420006f53158420006f43158420046f72158420046f4215842001cff7058420046ef2058420026f61058420026f41058420006f77558420006f67558420006f57558420006f47558420006f77458420006f67458420006f57458420006f47458420006f75458420006f65458420006f55458420006f45458420006f77358420006f67358420006f57358420006f47358420006f75358420006f65358420006f55358420006f45358420006f74358420006f64358420006f54358420006f44358420046f77258420046f67258420046f47258420046f75258420046f65258420046f55258420046f45258420046f74258420046f64258420046f54258420046f44258420046f73258420046f63258420046f53258420046f43258420026f67058420026f47058420026f65058420026f45058420006f74058420026f64058420006f54058420026f44058420006f73058420026f63058420006f53058420026f43058420046f72058420046e72058420026f62058420046f52058420026f420584200c4ff76d4420024fe76d4420004fd76d44200c67e65d44200067d65d4420176be64d4420006bd64d442014ede63d4420
  | 10 => 0x94200467d20994200267c20994200267e10994200267c1099420024ff75594200267f7559420004ff7459420014fe7459420004fd7459420014fc74594200067f54594200067e54594200067d54594200067c5459420004ff735942000cfe7359420004fd735942000cfc73594200067f53594200067e53594200067d53594200067c5359420044ff7259420044fe7259420044fd7259420044fc72594200467e52594200467c5259420004ff715942001cfc7159420024fe7059420024fc70594200267e50594200267c50594200067f74594200067e74594200067d74594200067c74594200067f73594200067e73594200067d73594200067c73594200067f43594200067e43594200067d43594200067c43594200467f72594200467e72594200467d72594200467c72594200467f42594200467e42594200467d42594200467c42594200467f32594200467e32594200467d32594200467c32594200067f71594200067e71594200067d71594200067c71594200067f41594200067e41594200067d41594200067c41594200067f31594200067e31594200067d31594200067c31594200467f21594200467e21594200467d21594200467c21594200267e70594200267c70594200067f40594200267e40594200067d40594200267c40594200067f30594200267e30594200067d30594200267c30594200467f20594200267e20594200467d20594200267c20594200267e10594200267c1059420006bf7559020006be7559020006bd7559020006bc7559020006bf7359020006be7359020006bd7359020006bc7359020006bf5359020006be5359020006bd5359020006bc5359020046bf7259020046be7259020046bd7259020046bc7259020046bf5259020046be5259020046bd5259020046bc5259020046bf3259020046be3259020046bd3259020046bc3259020006bf7159020006be7159020006bd7159020006bc7159020006bf3159020006be3159020006bd3159020006bc3159020046bf2159020046be2159020046bd2159020046bc215902007ebf7059020026be705902007ebd7059020026bc7059020026be5059020026bc5059020006bf3059020026be3059020006bd3059020026bc3059020046bf2059020026be2059020046bd2059020026bc2059020026be1059020026bc1059020006df7558c20006de7558c20006dd7558c20006dc7558c20006df7458c20006de7458c20006dd7458c20006dc7458c20006df5458c20006de5458c20006dd5458c20006dc5458c20046df7258c20046de7258c20046dd7258c20046dc7258c20046df5258c20046de5258c20046dd5258c20046dc5258c20046df4258c20046de4258c20046dd4258c20046dc4258c20006df7158c20006de7158c20006dd7158c20006dc7158c20006d
  | 11 => 0x57e75885200057d75885200067f65885200067c658852008dde7388520005dd7388520006df638852011edc638852024ded7288520006f7618852001ef46188520005fa7088520005f9708852001cfc76485200067f65485200067c6548520006df634852010edc6348520006f7614852001ef46148520047e42148520005fb7048520005f8704852001cec76485200076f65485200076c6548520246ef6448520246ed6448520007cf634852023fcc6348520045ef7148520047e77148520007e7614852001eee614852001eec6148520007e4614852023fe6314852023fe53148520007eb7048520025ec7048520007e87048520046ef6048520047eb604852023fea304852023fe93048520044fe76d41200067f65d41200c67c65d4120006df63d41200d6dc63d4120045ee72d4120005ed72d4120004fe76941200067f65941200067c6594120095be7494120005bd749412008dde7394120005dd7394120006df63941200cedc63941200c4ff7654120004fd7654120044fc76541200067f65541200067c6554120006df63541200dedc6354120005ef7254120045ec7254120004fe76141200067f65141200c67c6514120006df63141200b6dc63141200067f65881200067c6588120006df6388120086dc6388120045fa7088120046fb60881200076f65881200076c6588120007cf6388120237cc6388120005ed7188120025ee7088120026ef6088120047eb6088120027ea3088120237e93088120024fe75994200267e75994200c4ff7499420014fe7499420004fd7499420014fc74994200c67f54994200067e54994200067d54994200c67c54994200c4ff739942000cfe7399420004fd739942000cfc73994200c67f53994200067e53994200067d53994200c67c5399420044fe7299420044fc72994200467e52994200467c529942001cfe7199420004fd7199420024fe7099420024fc70994200267e50994200267c50994200c67f74994200067e74994200067d74994200c67c74994200c67f73994200067e73994200067d73994200c67c73994200067f43994200067e43994200067d43994200067c43994200467f72994200467e72994200467d72994200467c72994200467f42994200467e42994200467d42994200467c42994200467f32994200467e32994200467d32994200467c32994200c67f71994200067e71994200067d71994200c67c71994200067f41994200067e41994200067d41994200067c41994200067f31994200067e31994200067d31994200067c31994200467f21994200467e21994200467d21994200467c21994200267e70994200267c70994200067f40994200267e40994200067d40994200267c40994200067f30994200267e30994200067d30994200267c30994200467f20994200267e209
  | 12 => 0xd65d8d20006dc65d8d200075c65d8d200065c65d8d20006df64d8d20006de64d8d20006dd64d8d20006dc64d8d20267db70d8d2008fd870d8d20267db20d8d20267d820d8d20006df75d8d20006de75d8d20006dd75d8d20006dc75d8d20006df74d8d20006de74d8d20006dd74d8d20006dc74d8d20006df54d8d20006de54d8d20006dd54d8d20006dc54d8d20006df72d8d20266de72d8d2008edd72d8d20266dc72d8d20266de52d8d20266dc52d8d20006df42d8d20266de42d8d20006dd42d8d20266dc42d8d20006df71d8d20006de71d8d20006dd71d8d20006dc71d8d20006df41d8d20006de41d8d20006dd41d8d20006dc41d8d20266df21d8d20266dc21d8d20266df70d8d2008ede70d8d2008edd70d8d2008edc70d8d20006df40d8d20006de40d8d20006dd40d8d20006dc40d8d20266df20d8d2008edd20d8d20266dc20d8d20004fe76d49200067f65d49200c67c65d4920006df63d492018edc63d4920005fa70d4920005f970d4920004fc76549200067f65549200067c6554920005df735492008ddc7354920006df6354920196dc6354920005fb7054920005f87054920047e820549200067f65d85200067c65d8520006df63d8520006dc63d85200c4fe75d8520004fd75d8520004ff74d8520014fe74d8520004fd74d8520014fc74d8520004ff73d852000cfe73d8520004fd73d852000cfc73d8520006f741d8520006f441d8520024fe70d85200057e75985200057d75985200067f65985200067c659852008dde7398520005dd7398520006df6398520006dc6398520006f761985200057f75585200057c75585200067f65585200067c6558520005bf7458520095bc7458520005df735852008ddc7358520006df6358520006dc63585200067f65185200067c6518520006df6318520006dc631852001ef66118520006f56118520004fe76d4520004fd76d45200c4fc76d45200067f65d45200c67c65d4520006df63d452014edc63d4520004fe7694520004fd769452001cfc76945200067f65945200067c6594520006df6394520166dc6394520045ee7294520005ed7294520004ff7654520004fe7654520004fc76545200067f65545200067c6554520005bf7454520095bc7454520006df6354520156dc6354520004fe7614520004fd761452001cfc76145200067f65145200c67c651452008dde7314520005dd7314520006df631452013edc6314520045ee7214520005ed7214520005fa7014520005f97014520005ee76c8520046ee76c85200476e75c85200476d75c85200076f65c85200076c65c8520047ae74c8520047ad74c852025eef64c852025eed64c8520007cf63c8520257cc63c852001eee61c852001eec61c8520025ee70c8520046ef60c8520047eb60c8520257ea30c8520257e930c8520
  | 13 => 0x95200067e71d95200067d71d95200067c71d95200067f41d95200067e41d95200067d41d95200067c41d95200067f31d95200067e31d95200067d31d95200067c31d95202767f21d95202767c21d95202767f70d95200067d70d95200067f40d95200067e40d95200067d40d95200067c40d95200067f30d95200067e30d95200067d30d95200067c30d95202767f20d95202767c20d95200067f659952008dde7399520005dd7399520006dc63995200c4fe75995200047e75995200c4ff7499520014fe7499520004fd7499520014fc74995200c4ff739952000cfe73995200c6de739952000cde7399520004fd73995200c6dd7399520004dd739952000cfc7399520004fd72995200c6ed729952001cfe7199520004fd7199520004fd70995200c6f97099520005df735952008ddc7359520006dc63595200067f7559520004ff7459520014fe7459520004fd7459520014fc7459520004ff7359520006df7359520004df735952000cfe7359520004fd735952000cfc7359520006dc735952000cdc7359520004ff7259520006ef7259520004ff715952001cfc7159520004ff7059520006fb7059520004fe76195200067d6519520006dc63195200c67e75195200c4ff7419520014fe7419520004fd7419520014fc74195200c67f54195200067e54195200067d54195200c67c54195200c4ff731952000cfe7319520004fd731952000cfc73195200c67f53195200067e53195200067d53195200c67c5319520044fe7219520044fc721952001cfe7119520004fd71195200057e76195200067e76195200047e76195200067f64195200067e64195200067d64195200067c64195200067f63195200067e63195200067d63195200067c63195200075c63195200065c63195200077a301952000779301952026f7b201952026f7820195200c67f74195200067e74195200067d74195200c67c74195200c67f73195200067e73195200067d73195200c67c73195200067f43195200067e43195200067d43195200067c43195200c67f721952026e7e72195200067d72195200c67c72195200067f421952026e7e42195200067d421952026e7c42195200067f321952026e7e32195200067d321952026e7c32195200c67f71195200067e71195200067d71195200c67c71195200067f41195200067e41195200067d41195200067c41195200067f31195200067e31195200067d31195200067c311952026e7f211952026e7c21195200c67f70195200067d70195200067f40195200067e40195200067d40195200067c40195200067f30195200067e30195200067d30195200067c301952026e7f20195200067d201952026e7c201952008dde76d8d2008ede76d8d2000cde76d8d20006df65d8d200075f65d8d200065f65d8d20006de65d8d20006d
  | 14 => 0xcfe7359620004fd735962000cfc7359620004ff715962001cfc7159620024fc70596200267e50596200267c50596200c4fe75196200267e7519620024ff7419620014fe7419620004fd7419620024fc74196200c67f54196200067d5419620024ff731962000cfe7319620004fd7319620024fc73196200c67f53196200067d5319620026ed721962026e7e52196200c67c521962001cfe7119620004fd7119620026fa70196200c67e65d4a200067d65d4a20025fa70d4a20005f970d4a200067e6554a200067d6554a20005df7354a20085dc7354a20005fb7054a20025f87054a20026f76198620026f461986200057f75586200057c7558620005bf745862009dbc7458620026f46158620004ff75586200067f75586200047f75586200c4fc75586200067c75586200047c7558620004ff7458620006bf7458620004bf7458620014fe7458620004fd7458620014fc7458620006bc7458620014bc7458620004ff735862000cfe7358620004fd735862000cfc7358620024fc7058620026f61058620026f410586200c4ff76d4620024fe76d4620004fd76d46200c67e65d46200067d65d462001cff7694620024fe7694620004fd76946200067f65946200067c6594620004ff7654620004fd7654620024fc76546200067e65546200067d6554620005bf745462009dbc745462001cff7614620024fe7614620004fd76146200067f65146200c67c6514620085de7314620005dd7314620025fa7014620005f970146200057e75886200057d7588620085de7388620005dd738862001ef66188620006f56188620025fa7088620005f9708862001cff764862001ef66148620006f56148620005fb7048620025f870486200267f65d42200267c65d42200267f65542200267c6554220025ed76c8220046ed76c8220006ed61c8220027ea60c8220006dc63d9520004ff74d9520014fe74d9520004fd74d9520014fc74d95200067f54d95200067e54d95200067d54d95200067c54d9520004ff73d952000cfe73d9520004fd73d952000cfc73d95200067f53d95200067e53d95200067d53d95200067c53d952001cfe71d9520004fd71d95200067f64d95200067e64d95200067d64d95200067c64d95200067f63d95200067e63d95200067d63d95200067c63d95200075c63d95200065c63d95200077a30d95200077930d95202777b20d95202777820d95200067f74d95200067e74d95200067d74d95200067c74d95200067f73d95200067e73d95200067d73d95200067c73d95200067f43d95200067e43d95200067d43d95200067c43d95200067f72d95202767e72d95200067d72d95202767c72d95200067f42d95202767e42d95200067d42d95202767c42d95200067f32d95202767e32d95200067d32d95202767c32d95200067f71d
  | 15 => 0xd61540500257f70540500267e60540500c5fb7654050006fb7654050004fb7654050025fb75540500277b75540500c6fa65540500c77a65540500467e75997200c4ff7499720014fe7499720004fd7499720014fc74997200c67f54997200067d54997200c4ff739972000cfe7399720004fd739972000cfc73997200c67f53997200067d5399720044fe72997200467e52997200467c529972001cfe7199720004fd71997200467f7559720004ff7459720014fe7459720004fd7459720014fc74597200067f54597200067d5459720004ff7359720006df7359720004df735972000cfe7359720004fd735972000cfc7359720006dc735972000cdc73597200067f53597200067d5359720044fc72597200467e52597200467c5259720004ff715972001cfc7159720004ff75587200c4fc7558720004ff7458720014fe7458720004fd7458720014fc7458720004ff735872000cfe7358720004fd735872000cfc7358720046f77158720006f63158720006f53158720046f72158720046f421587200c4ff76d4720044fe76d4720004fd76d47202967f65d47200c67c65d472001cff7694720044fe7694720004fd76947200067e65947200067d6594720045ee7294720005ed7294720004ff7654720004fd7654720044fc765472028e7f655472028e7c6554720005bf74547200adbc7454720005fb7054720005f8705472001cff7614720044fe7614720004fd76147200c67e65147200067d65147200a5de7314720005dd7314720045ee7214720005ed7214720045ef7648720006ef7648720046ef6448720286ed6448720047e77148720047e7614872001eee614872001eec6148720047e4614872027fe6314872027fe53148720025ec70487200c67e65d43200067d65d4320045ee72d4320005ed72d43202767f65943202767c65943200adbe7494320005bd74943200a5de7394320005dd73943200067e65543200067d6554320005ef7254320045ec725432026e7f65143200c67c6514320024ff74d9620014fe74d9620026be74d9620014be74d9620004fd74d9620026bd74d9620004bd74d9620024fc74d96200067f54d96200067d54d9620024ff73d962000cfe73d9620026de73d962000cde73d9620004fd73d9620026dd73d9620004dd73d9620024fc73d96200067f53d96200067d53d9620026ed72d96202767e52d96202767c52d962001cfe71d9620004fd71d9620026fa70d9620004fd76996200267f65996200c4ff7499620014fe7499620004fd7499620014fc74996200c4ff739962000cfe7399620004fd739962000cfc739962001cfe7199620004fd7199620024fe70996200267e50996200267c50996200267c65596200267f7559620004ff7459620014fe7459620004fd7459620014fc7459620004ff7359620
  | 16 => 0x48500047d769485026d7f74948503157d749485026d7f739485030d7d73948500c57e729485026e7d62948501fd7e71948500057d70948502767e6094850004ff76548503067e6554850005df73548500b5dc73548500c57f74148500c73e74148502fd7d74148500c73d74148500053d74148500c57f73148502f57d731485026d7e72148500c76e72148500c76e621485026e7d62148500c76d62148501fd7e71148500c77a70148500057d70148500c77970148502767e6014850026f76198450026f46198450005bf74584500bdbc7458450026f46158450004ff7458450006bf7458450004bf7458450014fe7458450004fd7458450014fc7458450006bc7458450014bc74584500067f54584500067d5458450004ff735845000cfe7358450004fd735845000cfc73584500067f53584500067d5358450004ff7258450044fc72584500067e52584500067c52584500c6f751584500c6f45158450006f64158450006f54158450006f63158450006f53158450026f61058450026f41058450004fd76944500057d76944501fe7d76944500047d76944501fd7f74944502ed7d74944501fd7f73944502e57d739445026d7e72944500067d62944500c57e71944501fe7d61944500057d70944502067e6094450004ff76544502de7e6554450005bf74544500bdbc74544500c57f74144502d57d74144500c57f73144500c75e73144502cd7d73144500c75d73144500055d731445026d7e72144500067d62144501fd7e71144500c77671144500c77661144501fe7d61144500c77561144500c77a70144500057d70144500c77970144502067e6014450044ff76c8450024fe76c8450004fd76c84500c57e75c84500057d75c84500bdbe74c8450005bd74c8450046ee62c8450006ed62c845001cff7688450024fe7688450004fd76884500c57e75884500057d75884500b5de7388450005dd738845001ef66188450006f56188450004ff7648450004fd7648450024fc76484500057f75484500c57c7548450046ee6248450006ed624845001ef66148450006f56148450005fb7048450025f8704845001cff7608450024fe7608450004fd76084501fd7f75084500c57c75084500c57f74d40502c57d74d40500c57f73d40502bd7d73d405026d7e72d40500067d62d40501fd7e71d40500067d61d40500257d70d40500267e60d40500c5f975940500c6fa65940500277a6594050027ba7494050027b974940500c77b54940502b7795494050027da7394050027d973940500c77b53940502af7953940500077a52940500c77852940500077a51940500c7785194050004ff76540500257f76540500067f76540500047f76540502a57f74540502a57d745405029d7f735405029d7d735405026d7c72540500067d62540501fd7c71540500067
  | 17 => 0x46ec6254950005fb7054950005f870549500447c765495036e7f645495036e7d64549500075f73549503675c73549503667f63549503667d63549500076f72549500076f62549500467e62549500467c62549500076c62549500057f715495021e7c61549500077b70549500257c7054950007787054950004fe761495035d7e75149500e5be7414950005bd7414950004ff74d8550014fe74d8550004fd74d8550014fc74d8550004ff73d855000cfe73d8550004fd73d855000cfc73d8550044fe72d8550004fd72d8550006f741d8550006f441d8550006f76198550005bf74585500e5bc74585500ddde7318550005dd731855001ef66118550006f56118550004fe76d45500057e76d45500067e76d45500047e76d45503567f64d45503567d64d455034e7f63d455034e7d63d45500057d72d45502967c62d455001e7e61d455001e7c61d45500257e70d45500c67f60d45503457d7594550006f7619455001ef46194550005fa7094550005f9709455001cfc7654550005bf74545500e5bc7454550006f7615455001ef46154550005fb7054550005f8705455001c7c76545500073f745455033f3c745455033e7f645455033e7d64545503367f63545503367d63545500057f725455028e7c625455000777715455000777615455001e7e615455001e7c61545500077461545500077b70545500257c7054550007787054550004fe761455032d7e75145500ddde7314550005dd7314550004fe76c8550004fd76c8550044fc76c85500057e75c85500057d75c85500e5be74c8550005bd74c8550004fe7688550004fd768855001cfc76885500057e75885500057d75885500ddde7388550005dd7388550004ff7648550004fe7648550004fc76485500057e75485500057d7548550004fe7608550004fd760855001cfc76085500057e75085500057d7508550005fa7008550005f970085500c77b52d41500077952d41500c77b51d41500077951d41500e5be7494150005bd74941500ddde7394150005dd73941500273e74941500273d74941503267f64941503267d64941500275e73941500275d739415031e7f639415031e7d63941500057d72941502767c62941500057d71941502067c61941500077b6094150026ef6298850026ec6298850005df73588500b5dc7358850026ec6258850004ff7458850014fe7458850004fd7458850014fc74588500067f54588500067d5458850004ff7358850006df7358850004df735885000cfe7358850004fd735885000cfc7358850006dc735885000cdc73588500067f53588500067d53588500c6ef52588500c6ec5258850006ee4258850006ed4258850006ee3258850006ed3258850004ff715885001cfc7158850026ee2058850026ec2058850004fd76948500057d769485026e7d769
  | 18 => 0xf73946503d57d73946503cf5e63946500075d63946502757e72946500067d62946502077661946502067d61946500077561946502077a70946500057d709465020779709465001cff7654650005bf74546500edbc745465015ebe6454650006bd6454650156de6354650006dd635465001ef66154650006f56154650005fb7054650025f87054650146be6414650006bd64146500cdde7314650005dd731465013ede6314650006dd63146500057d76146502067d76146502057f74146503c57d74146503bf3e64146500073d64146502057f73146502075e73146503b57d73146502075d73146500055d73146503af5e63146500075d63146502757e72146500067d62146502077671146502067d61146500057d7014650044ff76c8650024fe76c8650004fd76c86500057e75c86500057d75c86500edbe74c8650005bd74c8650136be64c8650006bd64c865012ede63c8650006dd63c8650046ee62c8650006ed62c865001cff7688650024fe7688650004fd76886500057e75886500057d7588650126be6488650006bd64886500cdde7388650005dd738865011ede6388650006dd638865001ef66188650006f56188650004ff7648650004fd7648650024fc76486500057f75486500057c7548650116be6448650006bd644865010ede6348650006dd6348650046ee6248650006ed624865001ef66148650006f5614865001cff7608650024fe7608650004fd76086502057f75086502057c7508650106be6408650006bd64086500fede6308650006dd6308650025fa7008650005f970086500f6be64d4250006bd64d42500d6de63d4250006dd63d42500257d76d42500067d76d42503a57f74d42503a57d74d42500273e64d42500273d64d425039d7f73d425039d7d73d42500275e63d42500275d63d42502757e72d42500067d62d42502057e71d42500067d61d42500277a40d42503977940d42500277a30d425038f7930d4250005f976d42500c6f976d4250397ba64d4250007b964d42500c77b54d42503977954d425038fda63d4250007d963d42500c77b53d425038f7953d4250004ff74d8950014fe74d8950004fd74d8950014fc74d8950004ff73d895000cfe73d8950004fd73d895000cfc73d8950006ef32d8950006ec32d895001cfe71d8950004fd71d8950006ef6298950005df73589500dddc73589500e5be7418950005bd7418950046ee6218950006ed6218950004fe76d49500057e76d49500067e76d49500047e76d49503867f64d49503867d64d495037e7f63d495037e7d63d49500467e62d49500467c62d49500057d71d49502267c61d49500257e70d49500c67f60d49503757d7594950006ef6294950046ec6294950005fa7094950005f97094950044fc7654950005df73549500dddc7354950006ef6254950
  | 19 => 0x8e50006de7458e50006dd7458e50006dc7458e50006df5458e50006de5458e50006dd5458e50006dc5458e50006df7258e50006de7258e50006dd7258e50006dc7258e50006df4258e50006de4258e50006dd4258e50006dc4258e50006df7158e50006de7158e50006dd7158e50006dc7158e50006df4158e50006de4158e50006dd4158e50006dc4158e500cedf7058e50026de7058e500cedd7058e50026dc7058e50026de5058e50026dc5058e50006df4058e50026de4058e50006dd4058e50026dc4058e50026de2058e50026dc2058e50026de1058e50026dc1058e50006be6498a50006bd6498a50006de6398a50006dd6398a50026ef6298a50026ec6298a50006be6458a50006bd6458a50006de6358a50006dd6358a50026ec6258a50004ff7458a50014fe7458a50004fd7458a50014fc7458a500067f5458a500067d5458a50004ff7358a5000cfe7358a50004fd7358a5000cfc7358a500067f5358a500067d5358a50004ff7158a5001cfc7158a50026ee2058a50026ec2058a501b6be64d4a50006bd64d4a5018ede63d4a50006dd63d4a501aebe6494a50006bd6494a501a6de6394a50006dd6394a50046ee6294a50006ed6294a50025fa7094a50005f97094a502757f7494a504257d7494a5041f3e6494a500073d6494a502757f7394a504157d7394a5040f5e6394a500075d6394a502776e6294a502767d6294a500076d6294a502057e7194a502777a7094a500057d7094a50277797094a50044ff7654a5019ebe6454a50006bd6454a50005df7354a500cddc7354a50196de6354a50006dd6354a50046ee6254a50006ed6254a50005fb7054a50025f87054a500edbe7414a50005bd7414a50186be6414a50006bd6414a5017ede6314a50006dd6314a500057d7614a502767d7614a502757f7414a502773e7414a504057d7414a502773d7414a500053d7414a503ff3e6414a500073d6414a502757f7314a503f57d7314a503ef5e6314a500075d6314a502776e7214a502767d6214a502057e7114a500057d7014a50006be6498650006bd6498650006de6398650006dd6398650026f76198650026f46198650006be6458650006bd6458650006de6358650006dd6358650026f46158650004ff7458650014fe7458650004fd7458650014fc74586500067f54586500067d5458650004ff735865000cfe7358650004fd735865000cfc73586500067f53586500067d5358650004ff7258650044fc72586500067e52586500067c5258650026f61058650026f41058650176be64d4650006bd64d465014ede63d4650006dd63d465016ebe6494650006bd6494650166de6394650006dd639465001ef66194650006f56194650025fa7094650005f970946502057f74946503e57d74946503df3e64946500073d64946502057
  | 20 => 0xc77970d4b50005df7354b500d5dc7354b500057f7654b500067f7654b504467f6454b504467d6454b500075f7354b503075c7354b503067f6354b503067d6354b500c76f7254b500467e6254b500467c6254b500057f7154b5021e7e6154b500257c7054b500c6f7619875001ef461987500c6f46158750004ff7458750014fe7458750004fd7458750014fc7458750004ff735875000cfe7358750004fd735875000cfc7358750004ff7258750044fc72587500c6f751587500c6f4515875001c7d76d47500c67f64d475043e7d64d47500c67f63d47504367d63d47500057d72d47502967e62d475001e7e61d47500c77661d47500c77561d475001e7c61d47500257e70d47500c77a70d47500c77970d4750005bf74547500f5bc74547500057f76547500067f76547500073f745475042f3c745475042e7f645475042e7d64547502de7f63547502de7d63547500057f725475028e7e62547500c777715475001e7e615475001e7c61547500257c7054750044ff76c87500c4fe76c8750004fd76c87500c57e75c87500057d75c87500f5be74c8750005bd74c875001cff76887500c4fe7688750004fd76887500c57e75887500057d75887500d5de7388750005dd7388750004ff7648750004fd76487500c4fc76487500c57e75487500057d7548750005fb7048750005f8704875001cff76087500c4fe7608750004fd76087500c57e75087500057d7508750025bf76592500eebf7659250014bf76592500ef3e75592500073d7559250026bf6359250006be63592500279e63592500069e6359250006bd6359250026bc63592500073f53592500073d5359250026bf6259250026bc6259250026bf6159250026bc61592500eebf75592500eebe7559250006bd75592500eebc7559250006bf7359250006be7359250006bd7359250006bc7359250006bf5359250006be5359250006bd5359250006bc5359250006bf7259250006be7259250006bd7259250006bc7259250006bf3259250006be3259250006bd3259250006bc3259250006bf7159250006be7159250006bd7159250006bc7159250006bf3159250006be3159250006bd3159250006bc31592500eebf7059250026be70592500eebd7059250026bc7059250026be5059250026bc5059250006bf3059250026be3059250006bd3059250026bc3059250026be2059250026bc2059250026be1059250026bc1059250025df7658e500cedf7658e5000cdf7658e500cf5e7558e500075d7558e50026df6458e50006de6458e500279e6458e500069e6458e50006dd6458e500279d6458e500069d6458e50026dc6458e500075f5458e500075d5458e50026df6258e50026dc6258e50026df6158e50026dc6158e500cedf7558e500cede7558e50006dd7558e500cedc7558e50006df745
  | 21 => 0xc725452101fe421545210c4fe75d8121004fd75d8121004ff74d8121014fe74d8121004fd74d8121014fc74d8121004ff73d812100cfe73d8121004fd73d812100cfc73d8121006fb60981210057f75581210057c7558121005bf7458121115bc7458121005df735812110ddc73581210057e75181210057d7518121115be7418121005bd741812110dde7318121005dd7318121006f960181210c4fe75181210267e75181210047e7518121004fd75181210267d75181210047d7518121024ff7418121014fe7418121026be7418121014be7418121004fd7418121026bd7418121004bd7418121024fc7418121024ff731812100cfe7318121026de731812100cde7318121004fd7318121026dd7318121004dd7318121024fc731812101cfe759942101e7e75994210c4ff7499421014fe7499421004fd7499421014fc74994210c67f54994210067d54994210c4ff739942100cfe7399421004fd739942100cfc73994210c67f53994210067d5399421044fe7299421044fc72994210467e52994210467c529942101cfe719942101cfc719942101e7e519942101e7c5199421024fe7099421004fd709942101cff755942101e7f7559421004ff7459421014fe7459421004fd7459421014fc74594210067f54594210067d5459421004ff735942100cfe7359421004fd735942100cfc73594210067f53594210067d5359421044fe7259421044fc72594210467e52594210467c525942101cfe715942101cfc715942101e7e515942101e7c5159421004ff7059421024fc70594210c4fe7598021004fd7598021024ff7498021014fe7498021004fd7498021024fc7498021024ff739802100cfe7398021004fd7398021024fc7398021024fe7098021026fa7098021026fa4098021006f94098021026fa3098021006f93098021046fb2098021026f8209802101efb1098021026f81098021004ff75580210067f75580210047f75580210c4fc75580210067c75580210047c7558021004ff7458021014fe7458021004fd7458021014fc7458021004ff735802100cfe7358021004fd735802100cfc735802101eef215802101ef6215802101eed2158021046f5215802101efb7058021006fa4058021006f94058021006fa3058021006f93058021046fb2058021046f8205802101efb105802101ef810580210c6ef6298b50046ec6298b500c6ec6258b50004ff7458b50014fe7458b50004fd7458b50014fc7458b50004ff7358b5000cfe7358b50004fd7358b5000cfc7358b500c6ef5258b500c6ec5258b50004ff7158b5001cfc7158b500447d76d4b500c67f64d4b504567d64d4b500c67f63d4b5044e7d63d4b500467e62d4b500c76e62d4b500c76d62d4b500467c62d4b500057d71d4b502267e61d4b500257e70d4b500c77a70d4b50
  | 22 => 0x8e2145edc2058e2101edf1058e2101ede1058e2101edd1058e2101edc1058e210c67e65d4a210067d65d4a2118ede63d4a21006dd63d4a2101df671d4a21005f571d4a210067e6554a210067d6554a21005df7354a2111ddc7354a21196de6354a21006dd6354a21005f77154a2101df47154a21047e72154a210c4fe7598221004fd7598221024ff7498221014fe7498221004fd7498221024fc7498221024ff739822100cfe7398221004fd7398221024fc739822101cfe719822101cf67198221026fa7098221026fa4098221006f94098221026f7109822101efb1098221026f81098221004ff75582210c4fc7558221004ff7458221014fe7458221004fd7458221014fc7458221004ff735822100cfe7358221004fd735822100cfc735822101cfc715822101eef215822101eed215822101efb7058221006fa4058221006f9405822101efb105822101ef81058221004ff74d9521014fe74d9521004fd74d9521014fc74d9521004ff73d952100cfe73d9521004fd73d952100cfc73d9521024fe70d9521004fd70d95210067f65995210c4fe75995210c4ff7499521014fe7499521004fd7499521014fc74995210c67f54995210067d54995210c4ff739952100cfe7399521004fd739952100cfc73995210c67f53995210067d5399521004fd72995210c6ed72995212967e52995210c67c5299521004fd71995210c6f571995212267e51995210c67c5199521024fe7099521004fd7099521005bf7459521115bc7459521005df735952110ddc7359521005fb7059521005f870595210067f7559521004ff7459521006bf7459521004bf7459521014fe7459521004fd7459521014fc7459521006bc7459521014bc74595210067f54595210067d5459521004ff7359521006df7359521004df735952100cfe7359521004fd735952100cfc7359521006dc735952100cdc73595210067f53595210067d5359521004ff7259521006ef725952128e7e525952128e7c5259521004ff7159521006f7715952121e7e515952121e7c5159521004ff7059521006fb7059521004fb7059521024fc7059521006f87059521004f87059521004fe76195210067d65195210c67e75195210c4ff7419521014fe7419521004fd7419521014fc74195210c4ff731952100cfe7319521004fd731952100cfc7319521024fe7019521004fd701952101cfe76d49210067f65d49210c67c65d492101df671d4921005f571d492101cfc76549210067f65549210067c6554921005df735492110ddc7354921005f7715492101df47154921047e42154921044fe76d45210067f65d45210c67c65d4521045ee72d4521005ed72d45210c4ff7654521004fd7654521044fc76545210067f65545210067c6554521005bf7454521115bc7454521005ef7254521045e
  | 23 => 0x67d72996210c67c72996210067f42996212967e42996210067d42996212967c42996210067f32996212967e32996210067d32996212967c329962101e7f719962101e7e719962101e7d719962101e7c719962101e7f419962101e7e419962101e7d419962101e7c419962101e7f319962101e7e319962101e7d319962101e7c319962101e7f219962101e7e219962101e7d219962101e7c21996210c67f70996210067e70996210067d70996210c67c70996210067f40996210067e40996210067d40996210067c40996210067f30996210067e30996210067d30996210067c30996212967f20996212967c209962101e7f109962101e7e109962101e7d109962101e7c109962101e7f7559621004ff7459621014fe7459621004fd7459621014fc74596210067f54596210067e54596210067d54596210067c5459621004ff735962100cfe7359621004fd735962100cfc73596210067f53596210067e53596210067d53596210067c535962101cfc715962101e7e515962101e7c5159621004ff7059621024fc70596210067f74596210067e74596210067d74596210067c74596210067f73596210067e73596210067d73596210067c73596210067f43596210067e43596210067d43596210067c43596210067f725962128e7e72596210067d725962128e7c72596210067f425962128e7e42596210067d425962128e7c42596210067f325962128e7e32596210067d325962128e7c325962101e7f715962101e7e715962101e7d715962101e7c715962101e7f415962101e7e415962101e7d415962101e7c415962101e7f315962101e7e315962101e7d315962101e7c315962101e7f215962101e7e215962101e7d215962101e7c21596210067f70596210067e70596210067d70596210067c70596210067f40596210067e40596210067d40596210067c40596210067f30596210067e30596210067d30596210067c305962128e7f205962128e7c205962101e7f105962101e7e105962101e7d105962101e7c1059621006df7558e21006de7558e21006dd7558e21006dc7558e21006df7458e21006de7458e21006dd7458e21006dc7458e21006df5458e21006de5458e21006dd5458e21006dc5458e2111edf7258e2145ede7258e21006dd7258e2145edc7258e2145ede5258e2145edc5258e21006df4258e2145ede4258e21006dd4258e2145edc4258e2101edf7158e2101ede7158e2101edd7158e2101edc7158e2101edf5158e2101ede5158e2101edd5158e2101edc5158e2101edf4158e2101ede4158e2101edd4158e2101edc4158e2101edf2158e2101ede2158e2101edd2158e2101edc2158e21006df7058e21006de7058e21006dd7058e21006dc7058e21006df4058e21006de4058e21006dd4058e21006dc4058e2145edf205
  | 24 => 0xd715972121e7c71597210067f415972121e7e41597210067d415972121e7c41597210067f315972121e7e31597210067d315972121e7c31597210467f21597210467e21597210467d21597210467c21597210067f70597210067e70597210067d70597210067c70597210067f40597210067e40597210067d40597210067c40597210067f30597210067e30597210067d30597210067c30597210467f20597210467e20597210467d20597210467c205972121e7f105972121e7c1059721006bf7559321006be7559321006bd7559321006bc7559321006bf7359321006be7359321006bd7359321006bc7359321006bf5359321006be5359321006bd5359321006bc5359321046bf7259321046be7259321046bd7259321046bc7259321046bf5259321046be5259321046bd5259321046bc5259321046bf3259321046be3259321046bd3259321046bc3259321136bf7159321466be7159321006bd7159321466bc7159321466be5159321466bc5159321006bf3159321466be3159321006bd3159321466bc3159321046bf2159321046be2159321046bd2159321046bc2159321006bf7059321006be7059321006bd7059321006bc7059321006bf3059321006be3059321006bd3059321006bc3059321046bf2059321046be2059321046bd2059321046bc2059321466bf1059321466bc10593210c67e65d47210067d65d4721176be64d4721006bd64d4721045ee72d4721005ed72d47210067e65547210067d6554721005bf7454721135bc745472115ebe6454721006bd6454721005ef7254721045ec725472101fe621547210c4fe7598321004fd7598321024ff7498321014fe7498321004fd7498321024fc7498321024ff739832100cfe7398321004fd7398321024fc739832101cfe729832101cee7298321026fa7098321026fa3098321006f93098321026ef2098321046fb2098321026f82098321004ff75583210c4fc7558321004ff7458321014fe7458321004fd7458321014fc7458321004ff735832100cfe7358321004fd735832100cfc735832101cfc7258321046f62158321046f52158321046fb7058321006fa3058321006f93058321046fb2058321046f8205832101e7e75996210c4ff7499621014fe7499621004fd7499621014fc74996210c67f54996210067e54996210067d54996210c67c54996210c4ff739962100cfe7399621004fd739962100cfc73996210c67f53996210067e53996210067d53996210c67c539962101cfe719962101e7e519962101e7c5199621024fe7099621004fd70996210c67f74996210067e74996210067d74996210c67c74996210c67f73996210067e73996210067d73996210c67c73996210067f43996210067e43996210067d43996210067c43996210c67f72996212967e7299621
  | 25 => 0x4451007b7745445146fb4745445101fd6635445101fd56354451024ff7498051014fe7498051004fd7498051024fc7498051024ff739805100cfe7398051004fd7398051024fc7398051044fe7298051004fd7298051026fa70980510c6fb5098051026f85098051026fa4098051006f9409805101efb1098051026f81098051004ff7458051014fe7458051004fd7458051014fc7458051004ff735805100cfe7358051004fd735805100cfc7358051004ff7258051044fc72580510067f52580510067d525805101e7f515805101e7d515805101efb70580510c6fb50580510c6f85058051006fa4058051006f9405805101efb105805101ef810580510467e75997210c4ff7499721014fe7499721004fd7499721014fc74997210c67f54997210067e54997210067d54997210c67c54997210c4ff739972100cfe7399721004fd739972100cfc73997210c67f53997210067e53997210067d53997210c67c539972101cfe72997210467e52997210467c5299721024fe7099721004fd70997210c67f74997210067e74997210067d74997210c67c74997210c67f73997210067e73997210067d73997210c67c73997210067f43997210067e43997210067d43997210067c43997210467f72997210467e72997210467d72997210467c72997210467f42997210467e42997210467d42997210467c42997210467f32997210467e32997210467d32997210467c32997210c67f71997212267e71997210067d71997210c67c71997210067f41997212267e41997210067d41997212267c41997210067f31997212267e31997210067d31997212267c31997210467f21997210467e21997210467d21997210467c21997210c67f70997210067e70997210067d70997210c67c70997210067f40997210067e40997210067d40997210067c40997210067f30997210067e30997210067d30997210067c30997210467f20997210467e20997210467d20997210467c20997212267f10997212267c10997210467f7559721004ff7459721014fe7459721004fd7459721014fc74597210067f54597210067e54597210067d54597210067c5459721004ff735972100cfe7359721004fd735972100cfc73597210067f53597210067e53597210067d53597210067c535972101cfc72597210467e52597210467c5259721004ff7059721024fc70597210067f74597210067e74597210067d74597210067c74597210067f73597210067e73597210067d73597210067c73597210067f43597210067e43597210067d43597210067c43597210467f72597210467e72597210467d72597210467c72597210467f42597210467e42597210467d42597210467c42597210467f32597210467e32597210467d32597210467c32597210067f715972121e7e71597210067
  | 26 => 0x14fe74d8151004fd74d8151014fc74d8151004ff73d815100cfe73d8151004fd73d815100cfc73d8151044fe72d8151004fd72d8151006fa30d8151006f930d815115dbe7498151005bd7498151006bf6498151006bc6498151155de7398151005dd7398151006fb6098151005bf745815115dbc7458151006bf6458151006bc6458151006bf6418151006bc6418151006f96018151024ff7418151014fe7418151004fd7418151024fc74181510067f54181510067d5418151024ff731815100cfe7318151004fd7318151024fc73181510067f53181510067d5318151044fe7218151004fd72181510067e52181510067c52181511fe7e51181511fe7c5118151026fa3018151006f9301815113edf7558c510c6de7558c5113edd7558c510c6dc7558c51006df7458c51006de7458c51006dd7458c51006dc7458c510c6df5458c51006de5458c51006dd5458c510c6dc5458c51006df7258c51006de7258c51006dd7258c51006dc7258c510c6df5258c510c6dc5258c51006df4258c51006de4258c51006dd4258c51006dc4258c5101edf7158c5101ede7158c5101edd7158c5101edc7158c5101edf5158c5101e5f5158c5101ede5158c5101edd5158c5101e5d5158c5101edc5158c5101edf4158c5101ede4158c5101edd4158c5101edc4158c5101edf2158c5101ede2158c5101edd2158c5101edc2158c51006df7058c51006de7058c51006dd7058c51006dc7058c510c6df5058c510c6dc5058c51006df4058c51006de4058c51006dd4058c51006dc4058c5101edf1058c5101ede1058c5101edd1058c5101edc1058c51004ff7458851014fe7458851004fd7458851014fc7458851004ff735885100cfe7358851004fd735885100cfc735885101eef72588510c6ef52588510c6ec5258851006ee4258851006ed425885101eee215885101eec2158851004ff7058851024fc70588510447d76d48510c67f64d485148e7d64d48510c67f63d48510c75e63d48514867d63d48510c75d63d48510065d63d48510467e62d48510c76e62d48510c76d62d48510467c62d48510c77671d48512257d71d48510c77571d48512267e61d48510c77661d48510057e70d4851004fd769485121d7d75948512967e65948511a6de6394851006dd6394851004ff7654851005df735485113ddc7354851196de6354851006dd635485121d7f76548510067f76548510047f765485121e7f645485147e7d64548510075f73548514775c735485121e7f635485121f5e63548514767d635485121f5d63548510065d63548510c57f72548510c76f72548510467e62548510467c625485121d7f715485121e7e615485121f7661548510057c705485101df77654451006f77654451004f7765445101df7755445101f7775544510c6f6655445101f76655
  | 27 => 0x9405825101efb105825101ef8105825115dbe76d915115ebe76d9151014be76d91514d73f75d915115f3c75d9151006bf63d9151006be63d9151006bd63d9151006bc63d91510073f53d91510073d53d91514d73e51d91514d73c51d91514d6bf75d915115ebe75d915115ebd75d915115ebc75d9151006bf73d9151006be73d9151006bd73d9151006bc73d9151006bf53d9151006be53d9151006bd53d9151006bc53d9151006bf72d9151006be72d9151006bd72d9151006bc72d9151006bf32d9151006be32d9151006bd32d9151006bc32d9151006bf71d91514d6be71d915115ebd71d91514d6bc71d91514d6be51d915115ebd51d91514d6bc51d9151006bf31d91514d6be31d9151006bd31d91514d6bc31d91514d6be21d91514d6bc21d9151006bf70d9151006be70d9151006bd70d9151006bc70d9151006bf30d9151006be30d9151006bd30d9151006bc30d91514d6bf10d91514d6bc10d9151006bf64d8951006bc64d8951004ff74d8951014fe74d8951004fd74d8951014fc74d89510067f54d89510067d54d8951004ff73d895100cfe73d8951004fd73d895100cfc73d89510067f53d89510067d53d89512267e51d89512267c51d8951024fe70d8951004fd70d895115dbe7498951005bd7498951006bf6498951006bc6498951006ef6298951005bf745895115dbc7458951006bf6458951006bc6458951005df7358951155dc7358951005fb7058951005f87058951006bf6418951006bc6418951046ee6218951006ed6218951004fe76d4951006bf64d49511b6bc64d495101cfe7694951006bf64949511aebc6494951006ef6294951046ec629495101df67194951005f5719495101c7e769495128d7f74949514cd7d74949510073f64949514c73c649495128d7f73949514bd7d739495128d7e729495128e7f62949510076f629495128f6c629495101d7e719495128f76719495128f75719495101d7c71949510057d709495101cfc7654951006bf645495119ebc6454951005df7354951155dc7354951006ef6254951046ec6254951005f7715495101df47154951004fe761495115dbe7414951005bd7414951006bf6414951186bc64149510057e761495128e7e76149510047e761495128d7f741495128f3e74149514b57d741495128f3d74149510053d74149510073f64149514af3c641495128d7f73149514a57d731495128d7e721495128f6e721495128e7f621495101d7e711495101d7c71149510c67f61149510057d701495101d7e75d455101e7f65d4551006bf64d4551176bc64d455101df675d455101ef765d455101f7765d4551007b764d455149fb464d45510c77754d455149f7554d45510c77753d45514977553d45510077652d45510c77452d4551006bf64d8151006bc64d8151004ff74d8151
  | 28 => 0x4b512967d7694b512957f7494b515257d7494b512957f7394b5151d7d7394b512967d6294b5101d7e7194b5101d7c7194b510057d7094b51005df7354b5114ddc7354b5101c7d7614b510c57f7414b510c73e7414b515157d7414b510c73d7414b510053d7414b510c57f7314b5150d7d7314b510c76e7214b510c76e6214b512967d6214b510c76d6214b5101d7e7114b510c7767114b510c7757114b5101d7c7114b510057d7014b51175be7498351005bd749835114dde7398351005dd73983510c6fb609835101cfe7598351024ff7498351014fe7498351026be7498351014be7498351004fd7498351026bd7498351004bd7498351024fc74983510067f54983510067d5498351024ff739835100cfe7398351026de739835100cde7398351004fd7398351026dd7398351004dd7398351024fc73983510067f53983510067d5398351044fe7298351004fd72983510067e52983510067c52983512067e51983512067c51983510c6fb5098351026f850983510c6f8605835101cfc7558351004ff7458351014fe7458351004fd7458351014fc7458351004ff735835100cfe7358351004fd735835100cfc7358351004ff7258351044fc72583510c6fb50583510c6f85058351004ff7458a51014fe7458a51004fd7458a51014fc7458a51004ff7358a5100cfe7358a51004fd7358a5100cfc7358a5101eef7258a51006ee4258a51006ed4258a51006ef3258a51006ec3258a5101eee2158a5101eec2158a51004ff7058a51024fc7058a512257d76d4a510067d76d4a512267f64d4a515067d64d4a512267f63d4a514fe7d63d4a510467e62d4a510467c62d4a512257d71d4a510057e70d4a51046ee6294a51006ed6294a5101df67194a51005f57194a51044ff7654a51005df7354a51165dc7354a51046ee6254a51006ed6254a51005f77154a5101df47154a510447f7654a5121e7f6454a514f67d6454a510075f7354a514ef5c7354a5121e7f6354a514ee7d6354a510076f7254a510467e6254a5121f6e6254a5121f6d6254a510467c6254a5121d7f7154a51007777154a5121f747154a510057c7054a5116dbe7414a51005bd7414a5101df576d46510c6f576d465101f7675d46510c77754d46514e77554d46510c77753d46514df7553d4651024ff7498251014fe7498251004fd7498251024fc7498251024ff739825100cfe7398251004fd7398251024fc7398251044fe7298251004fd7298251026fa7098251026fa4098251006f9409825101efb1098251026f81098251004ff7458251014fe7458251004fd7458251014fc7458251004ff735825100cfe7358251004fd735825100cfc7358251004ff7258251044fc72582510067f52582510067d525825101e7f515825101e7d515825101efb7058251006fa4058251006f
  | 29 => 0x195dc7358152006df6358152006dc6358152006df6318152006dc6318152006f96018152024ff7418152014fe7418152004fd7418152024fc74181520067f54181520067d5418152024ff731815200cfe7318152004fd7318152024fc73181520067f53181520067d531815226e7e521815226e7c521815201cfe7118152004fd7118152026fa4018152006f94018152186bf75590520c6be7559052186bd75590520c6bc7559052006bf7359052006be7359052006bd7359052006bc73590520c6bf5359052006be5359052006bd53590520c6bc5359052046bf7259052046be7259052046bd7259052046bc7259052046bf52590520463f5259052046be5259052046bd52590520463d5259052046bc5259052046bf3259052046be3259052046bd3259052046bc3259052006bf7159052006be7159052006bd7159052006bc71590520c6bf51590520c6bc5159052006bf3159052006be3159052006bd3159052006bc3159052046bf2159052046be2159052046bd2159052046bc2159052006bf7059052006be7059052006bd7059052006bc70590520c6bf50590520c6bc5059052006bf3059052006be3059052006bd3059052006bc3059052046bf2059052046be2059052046bd2059052046bc2059052045ef7654852006ef7654852004ef7654852045ef75548520476f75548520c6ee65548520476e6554852047ae6454852047ad6454852007cf735485252fcc7354852004ff7458452014fe7458452004fd7458452014fc7458452004ff735845200cfe7358452004fd735845200cfc7358452046f771584520c6f751584520c6f45158452006f63158452006f53158452046f72158452046f42158452004ff7058452024fc7058452024ff7498052014fe7498052004fd7498052024fc7498052024ff739805200cfe7398052004fd7398052024fc739805201cfe7198052004fd7198052026fa70980520c6fb5098052026f85098052026fa3098052006f93098052046fb2098052026f82098052004ff7458052014fe7458052004fd7458052014fc7458052004ff735805200cfe7358052004fd735805200cfc73580520467f52580520467d5258052004ff715805201cfc7158052046fb70580520c6fb50580520c6f85058052006fa3058052006f93058052046fb2058052046f820580520c6ef6298b51046ec6298b51005df7358b5114ddc7358b510c6ec6258b5101cfc7558b51004ff7458b51014fe7458b51004fd7458b51014fc7458b510067f5458b510067d5458b51004ff7358b51006df7358b51004df7358b5100cfe7358b51004fd7358b5100cfc7358b51006dc7358b5100cdc7358b510067f5358b510067d5358b510c6ef5258b510c6ec5258b5121e7e5158b5121e7c5158b51004ff7058b51024fc7058b510057d769
  | 30 => 0xf735865200cfe7358652004fd735865200cfc7358652046f77158652006f74158652006f44158652006f63158652006f53158652046f72158652046f42158652004ff7058652024fc7058652024ff7498252014fe7498252004fd7498252024fc7498252024ff739825200cfe7398252004fd7398252024fc739825201cfe7198252004fd7198252026fa7098252026fa3098252006f93098252046fb2098252026f82098252004ff7458252014fe7458252004fd7458252014fc7458252004ff735825200cfe7358252004fd735825200cfc73582520467f52582520467d5258252004ff715825201cfc7158252046fb7058252006fa3058252006f93058252046fb2058252046f82058252195de76d8d52196de76d8d5200cde76d8d525475f75d8d521975c75d8d52006df64d8d52006de64d8d52006dd64d8d52006dc64d8d520075f54d8d520075d54d8d525475e52d8d525475c52d8d52546df75d8d52196de75d8d52196dd75d8d52196dc75d8d52006df74d8d52006de74d8d52006dd74d8d52006dc74d8d52006df54d8d52006de54d8d52006dd54d8d52006dc54d8d52006df72d8d52546de72d8d52196dd72d8d52546dc72d8d52546de52d8d52196dd52d8d52546dc52d8d52006df42d8d52546de42d8d52006dd42d8d52546dc42d8d52006df71d8d52006de71d8d52006dd71d8d52006dc71d8d52006df41d8d52006de41d8d52006dd41d8d52006dc41d8d52546df21d8d52546dc21d8d52006df70d8d52006de70d8d52006dd70d8d52006dc70d8d52006df40d8d52006de40d8d52006dd40d8d52006dc40d8d52546df20d8d52546dc20d8d520457e75d49520467f65d4952006df63d495218edc63d4952045ee75d4952046ef65d49520476f65d49520c76f54d495253f6d54d4952007cf63d4952537cc63d49520c76f53d49525376d53d4952006df63d8552006dc63d8552004ff74d8552014fe74d8552004fd74d8552014fc74d85520067f54d85520067d54d8552004ff73d855200cfe73d8552004fd73d855200cfc73d85520067f53d85520067d53d85522967e52d85522967c52d8552024fe70d8552004fd70d8552195de7398552005dd7398552006df6398552006dc6398552006f76198552005bf745855219dbc7458552005df7358552195dc7358552006df6358552006dc6358552005fb7058552005f87058552006df6318552006dc631855201ef66118552006f56118552006df63d8152006dc63d8152004ff74d8152014fe74d8152004fd74d8152014fc74d8152004ff73d815200cfe73d8152004fd73d815200cfc73d815201cfe71d8152004fd71d8152006fa40d8152006f940d815219dbe7498152005bd7498152195de7398152005dd7398152006df6398152006dc6398152006fb6098152005df7358152
  | 31 => 0x805000c00100280080480020000004000000008001000a00b0038008006001002800001c00c005000000c007005800804c009001801801000000b80480000020288004036000006800400401000080240100130000004008000005001400400000000100120100018078002004001807c00a04c001801001600f0060054004003012000401c00e00000680040020038000014000000801806a002007800c00603201b8000000014004800000200b00a000000e006002802800201400080180040020050030004001000000c00400100180e0008000004000c0000020060008016006000000800e022002003c0180070000008008007000802c00a0010008030030000003801c004001001800000e0000010000016006000000401c00100a00000a2003021800801e00600000000020010020008026010007801400e003001800c01a00c003805001c0000020014016004003000000200100000f80100020000008004001001803001400300780b400000000000d40120000038010000008029001400e002001800c00400c001003c00000c005800c014005002804c00c002004800004200800f8004002002007801c0460430000040004000000000806800b00480680000070058000000000003010800600100400000000010018000000006004001c00000000080040160000000000008002000000800a00a00000ec01601c0c6f7619875201ef46198752005bf74587521b5bc74587520c6f46158752044fc7558752004ff7458752006bf7458752004bf7458752014fe7458752004fd7458752014fc7458752006bc7458752014bc74587520067f54587520067d5458752004ff735875200cfe7358752004fd735875200cfc73587520067f53587520067d535875228e7e525875228e7c52587520c6f751587520c6f45158752004ff7058752024fc70587521b5be7498352005bd749835218dde7398352005dd73983520c6fb6098352044fe7598352024ff7498352014fe7498352026be7498352014be7498352004fd7498352026bd7498352004bd7498352024fc74983520067f54983520067d5498352024ff739835200cfe7398352026de739835200cde7398352004fd7398352026dd7398352004dd7398352024fc73983520067f53983520067d53983522767e52983522767c529835201cfe7198352004fd71983520c6fb5098352026f850983520c6f86058352044fc7558352004ff7458352014fe7458352004fd7458352014fc7458352004ff735835200cfe7358352004fd735835200cfc7358352004ff715835201cfc71583520c6fb50583520c6f85058352045ed76d4a520c6ed76d4a520476e75d4a520c76f54d4a525576d54d4a520c76f53d4a5254f6d53d4a52004ff7458652014fe7458652004fd7458652014fc7458652004f
  | 32 => 0xe00500e001c000000000800400000900000180220310000010000000002000c014001000002805a000004801801400d0068008016008000000000000a001007c00000000080040060000008014000002029000000001400000000000140068168000000003001c00602b0008024000002001000400a003000002400c00f0000018002000000000403c02c017802400a000007800400400800c000c000037003801000200900a003400400100001100100040010004000061000800404e01c000802000c00000a009c066003002802000e011004005c004036004000400c007008800401200a0018054000002002807001c000001001800000800600000220000008008000001000803c00200c02d8020004028003001001a00e00c800401604100a806402e004000001000000400100000360000000000000004000004001000f004000003c002000001803c00d008000003800500080000100250000008014002000006800001800680240060010068028002006002001800401500080000120050000010000000002000001801200c0050012005000800802600101480a00a60360000000004007001002801c00000180140020010010018020005000000000c001008803c00800000180e005e00f000801c002013000002800000401a000800200000080440100010018004000004000002c02c001001800002600a0038018024008000003403a000001001000400400080600120090088000004004000004c020003003800400a0010008038000005006809401c00400000b400000700000000060080080028000002004000402c001001805c0100010000014006036005801000001800000ac01e000005003401c003000000c03200901c008401800500280040040000038000022006004800c0040700038048016003000003c00e0000010008018000005800003600000400040120060008030008001008801400600200380000020130000000002008000000c008002006802c002001003001c00800100b0040026025000002801600800100000000340008000074026000800001c012000801400201a009802400801d004000c000010000000000401701100dc030001000006c00c01400a800800e001002000c00c00200180200300000018008028000003801c07400101600d0014000005000000200900600440020000010000058038001800001202a0018000012005005001801600700f800400c016001000000400100300040040000008004010006007000400400f0048004006010001000c058026005800800e001001001c00c01000800700300000088004068000010000000c00b03e80040040090000018014001004003c00801b000005001600400000a801c0030000014000000002003c00000100100000040010040014002004000
  | 33 => 0x4003000200301180840020080070004002003000007800600300f800c02400000a8000008009001800000000600180a800002100e8004000008004000000c012000004c028010000000000a000007800c0200000000000002000013000000400100400080960000158000028000000005402e00d000013000e007007001409e000000003c02c00f000007000c00000000180280000068000004000003000002e0050030008008003003801400a00500c000000800a000004c00c0000210004032000000801002400700a00300080000078000004006001001003a008002800000a01b01c8000006006001800400e002000000c000012003000000e00000000240000240000044004005006800004c0090030030016009004802c048000000000c006002000804c0000000010000000000000800c0280270070008000008007000c00e03d00980a803c00c000800000400100d8088012009000001801000503780680200020008174004003010000000a00201080140060010010010000001001802000200b004000002a00600180000020010000000000018006800000000600c0008000011011812402e00c002002c0cc000004007c0000020028090000002002000000001f00b001000400a0028014006005000000c004005003000800200100000000000000000014008008005800402003200b000c006001003800000200a000801800c001001011408c01000980500220000018000002000001009000600b00d8038012003001000000a0190010008000001000001000c005005000800400800480500180020080024000002000005c00a0330008000018003002800000200b006802000602a000000c00200200000700020060000014002017004800807e01200000ac00c00b00a000001200c00000940180000050000008002000000800a0210008084004000000000000001701a8000012015000800800a012000000400000200280000020000000108012003006803000000a0008000008004004000002801400000040020010000010000000000005800a003000000000800a003800c008001002010c002000000801c006000001801402e006001803401e00100200200020000038000002000001800800000a002800401000000a0008006026013800800a001001800c00c02300f0148000003007801000600000000000320000008124026003006000801a00000000a00060020030000006000000001001c00600180040040220080004004000003000800600400080080000020010038012007001806c01001401b00c408a013008000403200200600040020000018000014003000000800000001c800801803100200b400a057004800c00001100d801c000005003800000400400380280180000018010006000005002401c00001a800800
  | 34 => 0x68e017a62106565ac071480922b83c1a6c07f50d1e68586547910b986f89d188cc0064a0da6866f389600c305a85e29a4c1dc1aaa3cda89622c8f6a6d593040000a384d10e181bf9776711a32416387fa75d00004d4a5f4250875254b8ca4600235a7621f8288fa3ea2bb8d367ab9a783f88ac07e4a6ac000000000004ae000272e57380005a100004bd047066594ea0001148000251c76411ba0001e6655686ce0000e120001f52388057e28f000045f19108bb09d467e8ea067504d05e710fe3851f065f79ba66998a0023e0000841a27e223954a4a59dac74021424b700009a38af879e084c88214aa83588c0a4f12c218300009db92307c90f102a094ee36300000001b6c014945e9e91b183eea9d06c51e2c6d88db241d974863aa2e65fb247e4db91c60af9d60661049a480205a62093b059a99e202f812a1698f3c32b8000187133e000000000000007ca0a1c73808b868981863e08000000045600000000000000662800000025300000000000000059a00006f909784e99ee40ca119a901a772a59935812d933c48a8b728d287d265986de18103b497a095a8621c9659e22187e89a2a7df852a1d9a9d858b118000000000c09fa83ff13548b893685658000a601e067fc150019c800064d153e92d01340b9018a93718ac1ad873e56d00000000640561a6d4a522390841066400016307fda91a5191ec40089f7a0001edc0001da4987068c895832e6138a648f391a60051598a3d8f30714899c60d1c4214588ca3689d8a814a59a2ed940c72b042028410fc028a1169b615660f9a696000140e000000000000005c307fe33497829aca5da174188c00019760000e64474097a000000034706a2a5c0000645a19e5ce93f49318adc90b8a5a00014489e587be0fea49e4ca902058ca15e4ff15b80001c8a07392025f500002270f48003800402a009008804000400c00000180120050288000006004000000c05a00200100140080000008008000020006800001000a000000400200d0000030000002006802400801d0000020000007002000004600000c000400000100300300040000030004004005000800c0020030000004004001001000800e02100b000c00001200000ec034029000800c014001006802c0020010010008000007000801400c000004006400800000300ac01201d004800002c005000006c00000101680080100000000090016008001000400200d002800001003e007000400000d005000402801e000809400c0090018008016000006000800600000000540040090070004004012001001c0080140068010014022000001800a0050040008110000000801000600000000a800400b0000020040000002800001403a003800000200600100f400000801c800003a003001000006a002001800400c000000000402a00400
  | 35 => 0x9e7029029cc71996c83c088d2a62881a0b810360d31a741d093e69da939e58e16d225d0eb400f12bc13d03ca4369cc28e71a322c1249800016a20ec80a6999082823080000e70000000246ca7aa6e43321ffea3900009e7a7f8a019d924298c54000235c0d90d46a4326b647f255885e113a0fb87c2000000000000007ad800000006ea96400000000f860000000437000013200006a7854c8ec087e12420424f800008bc1bc42eb80004749dd278d913c7aa91e80000cea0000952279a520668a2ee6b81c2c0000a3473a8000a49a71a3001d8c3dd19c4000237e61b02128118ee09a4000065a800000023963718000919a0d898c8f2209a21020808f4a784a2782d70e4836d17ea800a668196a9921d320445bd1b3aa73a49670a8e5e2ba243e0cd8ad27249fbe67421387369068484000035c8e2c82f82fa0680aa088d90d6293a9ec00000129f51db05bb0f3e6579f741ee22a08921a36842233e20e89804079314a77894a00016f618b0eca89699aa6978f5c4418234884157e9408dfa9b3266e466009e98e9efc8f207a615a92fa19a252803311765ea12a204e18887f215bc62412789ed8e506c31012397230470822f805d9c6e0f40000000000000021ca052a7322ff000021a000052898a45e8063e4b191f476d228600026060002582285192007d0632000000061a000084b20a800000d4000219c0000b403e38000364256c5e007041b60abe0000000958a932a7ea0a0520a93461f0a6a59c09883f793c495c020a0001e163318a4203f974462e800053494e81d9239e7b89f68000000000023600001e1e7ff1fb69f101f84df8c14000000040f8dba0da1c3a7980cfa45282f21e6187e96b8000933275e2888d3815b809063618128b206b800001202f9179e089107e36908960f21d20000113e978865c12200007171410000171e4d788ba7f728a0000124272b8000000000000000000001a2017d000000019f85d6a2e45101c5e7fd1d4a0b78314115055471298380d223e22ec1fba47e032c3a89d5252c099801706360988850621a61a49aa32846212d258282f60b392385a7800619304fa30e19480ed802896b17d83fc23fa91aa736849081e3b9a7d0042a18e21594a029e0de42e688e845b9572944265603716603c30eec81927ec71215208ac07f2217038e8c3819837c079027486166038a6c951a1c049b0ae207f8a184f3000039e9e10000000000003be0001e2414500001eb87c074aa9bc4e80af4514845e85291da793879c858947817a800089e80001ed86a812fa0329a11c8887f1bb084a1e6a0aba26600000000000cfe113000000020e6996000032f8afa42d804a38a9a1200020d09f992a04e2800090623d600000000000c129890000656163a53200008cf125693384e027429042b6270c9a508d02ff99f03a61024
  | 36 => 0xe5049f8c00008105009a62396800038e994a37da19679f112c9ce01547f98c4e3d3a8c81e4804639000005bb868e716a1a84ac031e59f000038ca4ec3460a621509ae2a0b23183bc0d8a765800021804ba8d180000001bb800000000000d1a6582170000000000012b600009c60001a540001f704dd252c69c925c4248c0200012d84d71a085f09736000212a00018066fa000086f800006ca5047a0861289000684fe86ac9d10000000000000026c60001276457992c8ac8000000121a000136400000000000000a0417dc00018f6a2f9502922208861d197e11f17429299d5073e1a7e0001a8423da9da91f209e29528aa00003580000ebe6ef0f0030a87c81f603cc88921f644e0870a4709d84929c8210b958c377a73a18d13986ac1c7a7450c9c5078d5213296423ed1d9c3a380006a58758000130c6d18000a23182608d9ccc0daa57298117ac4f595ba000000000000007ca800034181620001f0a000277e9451cc07ec98fa82c1c987fb8c6a0251e480001ba2000000095ba5d80000f1800007ec0159d02669906c0001904a0e812210d000019e800047800000e42378565238a45fa32690e000037b96a464f032612b1dea75d81aa00000000000d488e900000951f7836f14268802250218a2222ce008244700001fe07fc0fa9c68306a3a29580c0a28c9b7c000096296e8882000059a00000000001b524119f26761a7ba8562048a3a26ba6ae1f309f38a506ee9cc492c1194836a7f68571a24a751ed84c491526669d12a0101c86af8dc4244212001b855c18805cc72006c631827aea5c9c764e18e9405f8d9e2da1ef41d706425de155408501ae1a616ba20b19b07268de26800eb899221bc35b856c2262862956a69c56885e2902a5c2972899e8c304da7579846140910e1b214800000a565c917fa2a300005b127143e600004f002860000000000000093000006f2800000000000000000783000064c80000002338a3b9d728c023c491380005af123e0ac1dcc0899e98032a9f8000000054b0000a02000000c1baa43380000000972000295e7fe80000ec00000001636579000000000004209a8851ea75257180000cc8a440001eac00013c260623fe8fc985875117d05c292466320f589d096a012880c282986d410e22ca685023a9c12306000232ea6aa40044213805aa89ec41c216890a00002c8845259b07389c727067b3800043a17606cb25e429726fc5260fd67e60b4621c86aa1e928a81171ab25d8848416e881c00021b00b0a4865061e5a1b001c052b00768a09bf63ac217e48a15482eca00a112882491291783c7a96e3ea050a69409a80d08f0e16d1f14000036e0ae15587c0973000020fe02ca90275e146e69c06cc3ba861a49a063c1a5060092f9e7655084de2108a12715885a3b4a8720001e202e08e749ab8206680
  | 37 => 0x98f5a00028b600010f8000007a76ea4e466b86a6064800026c1022278a2460001ce6544919065680000000bd48dd899a041922200021ac191975e839137845926789c580008d5a5b28c417fc66d861e89811b44fc152430f8ce45fda1128bd949e1c200406cf267279289ba996800000000000a8271200013d25c68af60001b1c3ffa1c2838a8d669380008aa1c8e0520b92000000000000003ce8e04031981c60b88b666e0000858127e5548f28000000039c9e74229000085a9b7aa17961832c94168758000049807e0919fca2960562a388b4c4b015168331026430004c17b249455e0dae1a68ef800000f65848c823d40cf4a32960c00013b400023f60000e261c899886d200000001d1e3a706f23ad8000000000020aa7ea1b90e3e4a08e08088044205097f48ab8000000213615603bca6b26bc4a728688eb8000513800032412b4000000084714b400024260000d0899d894e8ec8bdc638053e2219c748351634053a3ca9538dd60a41c8640b85606cca58030b000000005908ad802e1808000000296c95495fe35aa5945540cac2a70fd80001bcc0001488000104e000276802ba7300002990199984c70a228e97f1e720002414000000018600005638000a4d84c2000000065a28263ec25a2134977e2ab9f3287d20942e5859832595ac52d9f4c44795ee00e94f890aa3126ab931c138a8d08d0000097794be000000079029882000000882800045689a24c58c5ea2c1e8a6839b1ea0a91ec00000005ca8f9a61d86825d5111431404145ed85660a21be0000000058ba268763a9f04d000006141cf2612800050c209227f9f5890580003919d822aa23481a821d22b30e1e81991561eb0ef6329a4527b42688585880a3558000109899648ea8344639860623a8fa35a102a09390c8967a7a2634243c4a51064023a60a8d98000000220e9dda6de52292d097500d25fa00002918d268fa0000000079652b870c6e029c43ab22909f69c0683204b800000000000c664b3940858a03947600d546a98dac6b303d88f6221684395a47c30be0638a58a21e0b3c00015caa16185450d0fe03b902d85e588545b00024999873600011260f793e46e28cec70f113424f10c43e301e609d95921f780002ee2766a0e1184a491f385111b68478a95680e834e7698b54732067654380185fb80005eca23c14e837880a093021f02dc9b428c068298d431e1b8228b91ca04c83842a983720001a906baa7027a78c86119000068195686761ac0000097c000000022b000000023d40000d5a28300000002556832945427b82f875007e603820fa000000000000000001fbc20600000001f3e00016ae00000003fd25b681d8000000161e8dc14c4823800098b00000ad00003dc8000000000055c23c092080006ed87007d900006c112e0000000075a923610a013
  | 38 => 0x3a2e90c5867000f02d826aa9a903e263c1ec01542074000250c6ec87ee58427fe00012ae75097d624595b60a88a9e644a5247e0040a0449262681160e4d690ca1da800019882bc80d23e600029b61b68eaa9de034a48f04a43f700005601060219800000028bc07c94da5b0a1ec3428a1e0b69d243a30000054a774000010800005c40000bf21b080000001758212a2fe758800059c80005709bf236a80000000a7a270101021da64288e93f252e157424b258c1d81d3a000199242e1832000001c0fc95fc68a0000a290000737114015d20f29f2873ca3f0000884a8b400023322e19b74261800004600000001bfe000000011b800069b800072900e8776159e1df920a562a98459929e08020000903905404f000000023621ba0c921d203406531ba09db04f62c0a9ba0000c1e813221c647000008c00003ba22740a0109e04b8e44000085843c0ba88a624742d08000317207c000124c7d2a2fa64d80e45b624a466900002bb09001bb80002b087507bc9dce9a8138457d92ba370000002a1c00000130a1539350149181690d8d2251582a83440f348d6091220100006a5161a3aa1c08000170e27f04d47521e5e358058c1049c38160111006714e01248292538800000029627c809ac000104400020f013ba1762a49ed41180000000000064a000025705bc0001b20643200c9951f86000265ca5a80000000e540ff138e2ac844e8dd000071912da607a8f459895469d3027410f86808b69f489ac072825a9dc84b2857a0ada54c5c48000a6d289e82c8000000175c36c09204cd0ca8328a4f60eaa84e00004e6775800000023ee1979e7a446800065ba72a8949c2623d02d26399b4c0001b0667c8000000000023b89385950000000000000020509f8a6a2000078a5ae04aa51c81f600000ee4cca446000203e169222a72f10001da05305da153636e13764e2169860c0a7235da1de526a93048d253a1cb9c90a1e9e1469b000036111ae95f01ea525968827d000050a0a1a98c000000001fc0001102444946686000003f20dc281f9dfa52c800001687a09c905120bb85f69d8134608592de1b881724bb9f3a035a9546ab1a3e5f1901c15000009b729e62758754062052c38322d88088000000054a7e2816e1ac229200003620d186100001f1857300007aea72c0002734339a28c63c822206c160839a83a209aa132715098e4d21a3c18e97720248f601f126e82d29adc847a950000148c92100000000678000000068e974e39b051e5f007e00678e340001e7e074850600000007fc80000900ede6be80000000000000128657688f214d0000322a63857c8ae053792a409f00000f1188a35f1e3c950996243525d60f728280a600aa2f10086a0828c27e397a66e905825019aec630280ca4a21847420d126db832a30c80008558000000005e0e
  | 39 => 0xcc800043b9d34000000029fa91418511248c28000000294200019de000204a00000008c5a3360001ee041093627ea98b2000160211201142820000a479514000059c74f192a0b986b20b295a68a982cc912091804e93de98d842c99c1af428b0b7c03e8cda0000000106a59897c996c6500cc017080000002844303000050ba0829e31aba5fc01e431c18bc3f4000059116861c6231a50107a8a4f85a098b921676e1ad800012326492134a7ba52a038a7104540f4455b8f7a7e11b9c003000020ca7467f420ae000000067685d40000a28000285a000000083a93ac00000001e680000c20d34000046c7a9018e47083a8104245015794005128578000000083e0e6200014bc62f80000000c7aa2e80da00027be6b1190a48787f4460a9c07990b3e71110cc94f95226d5266a0000000000189200003ce16e1de00229ad64c427540120b1ea70800013b16b69e994fa9cf108863118a0a518f565f4984263300001bb1584000060ea2722ea2b5914c90480009c99a2ca3822c643b20a20aa97e428f9ca800015dc4c810c69c8a464a0891c4a7596a6745a13e0001d323a002d000015c801a80004dc1cf61460caa2bc8e920a3162a430800073580003e410047cb204042d1ec600023a8000197203a902c2891c3264012fe76fa618617240c00000000d517380000e4c00025aa0000c2800029160001a86654934e00000001ca879e5b1a422018800000024f0374823c00010e47298d6682700003501bea943a17c4d59cfe38280003dd9fc68ed88ec897a03887e80009fd13926640b2a000071071009a40e0893a0000bac64f80008b8128474405842f6881280c296032c1a483bf8000000086e0001b169a080002c4894c915800000021e035391ce1d780009979fb401614f09b983d653da53808c8d5e4fa95d80000000467904a72fa0a400001d40bc0d44a65189892e000000005e066616fc47c80001bc1d7a00017bc4ed8b14000000013723646fb1efa011077600027c216b80002e500506d60bb41318aa48c7800010222de0001cec9fb81782b999f6092a28000022be37421a604b10963df91a44fe220600013be535800007c295c0e3289a00011185fc9a447e5000000019c89ca09b60610906000000010e98ca0000a745338cd60000beea2496ea6169cb8a1d12149b1264449b983c8c200985119756702a4fc8489b9a23f80007a88d202fe896c9780dbe75b82080000070000000076827b400027849f60d9240d13a417614323ef8cdc6fd00005d41f0e934800000000000000ab66bf1a3417c8000593993a39e05d215a05320001b1a00000007f912f60db0000236997c38000006b99e809939814423927a116120464b8a688da0c261470e9627a9f222eaa9ca546a1e68d4a578110089e0fa27d655924684d98e38496003229d80004e0a9
  | 40 => 0x5a442c9b9e1a491a8886a7cc2c690525299f108fb19fc90d029c22f9b3460813d081c05ac24b95c000e155c3e7a1b87788bf6a12086a3be92e611c80549d39f4217f1bee03d0fce1039b424af9ff8600903c2e3176a52e91b8151971479b927036d8c725998c64916128ca72278e497a5a89401f66096890e09e83241ad27dc5c6068414209c851821d0645064e0998ce00c28f547f49f5e9ef1fec32614386bc9b70303973c77c86961c81dbc06591b0000277051a10ea73b880e000000065e9cde9c21532299a49a00028ce9a6049c6b51e326719a4666ea94e46f233a95409646cda59687ca95a04124549a79c22483157a9bb83da0cc00000001cca66500007b692f0679863891000000001df00f9007ca1ba68c39d888000023be5f10d30149a7488568cf8a6985006b083f660b281e794a60048ba14054201bc0c819428ef142095901b89de9c3ea7f1ca24c18dfe82f00740479a826c4a37c71423d283b8648162994e0001a6425206522fc00003da1e0411ea9fe35c1c346fe165ea79221e00012ea100a41e972078c40697da3238b36173920e47700000001efe15200427eb23baa2193082b691cc07e905c000060a0001e5400002e818200001d3a5be00020de0000000a7d932800000005948e2e85980007f61c6c86c86d24f286a46840482261289037d20c000014a829c028290b0d8e372a05e77f803689c20ac20e2090a2b031006a23ac00018568a90f04574800045d245e54f0ec624d98d6788897e0d4a17a3fb0a9668ba51e5c10bc290828f81bf035638f18784ac829a627197837618b02d4855a2e996007fa02d62a8898ca3c1018000101403012a609b80008a127504df210c000117a3e893e823f201004909de977070a8738446a5da38e0001f404dc9fde6fc02ac88d2762000100641322264fb96406011b0e2c30316000000000000000000000000010282021460dd9ef89bd9f2e1c69dae331202c9c0035c359291800000005b88e8a37f1b8457c10a42339c0c0000bf8000146200025e63d1800063ba00400010ac7559a9a93f87021fa8ac604d978e3d011ea63904440cf00001df0000000059624723225ec19642de20d24c616066958f1246a873400003fe33b8ae41311a5200000003b700007bb9530000000002918449c79b02a5e93b2700a7869e70f84000000097a8000000214c45b18dc7250000a1c00005f200000001d4e0000a8a9489b2296c219a93ca88e5d185d6531868a7cd82e259ea1727ba09903ce08b41af1d54395a4e80001d2844a967400027f00002394039802000016b297b00006a0280a0aca8dc983977027a023e31da906000021827e00001f3918a00010e0322090287a1170936000037c91a26f5000032f1ec293b8eae40300002088000a362238a228b1c8718a943389f6c76681685428d823
  | 41 => 0x4fb25c619b1bc826c8c84a19286a2021bc07fa86f60778000000264616a95763998f5e5d9a88873884fe0c89a8e43424da8f809e0298154404a16f000006fa00005fa376a0b8955110c3dc11f6000286634a899496982280000aba00000004c39e5800021a074180006af19ee4821f446d68e9000029b84da800057b1722000264a3fa26260001fc000026208cb16f800000004c690e200014d8795862604428ae0bf0c7e00025c0809a0e890c1c8c631a63c057071c3c58d042f40370a398f4c000206c6b7800028d80000000e02254244200020aa655a34429f11fe18a8d1614b9172502a3c251d064489700002aa8cfc02594585b41d9e1f58c4649f0d0e815050c3f491969d68b1874c192200000004eea67c41f03880001bde0691bc27e710484cb1a9c97400002ba8b8e000133633a0b262378ef274b18246ca02044ba0000051000000019ce74f8000000263e0000000071076e84ba92aa6a29ae9f18b7a3309bd67820000a10029e13921943c2991a4e702c436a0000826865054e95f8749986a9aa27902e007303f09ea6647a6140001bfc3df01ba116988017795a02cba53c82610aa2c823820dd1dc02f3216e8bf0f808e1894051090a22b394906670cd050f0ec85dba4b20fc12241f909c47aca8327f6936c072a11410c02a6a1519e0a0f8fc6a11a5687d885760c4a02a7338c440fe0ee293d182261888528aa827e776a0fc634a18c14d9a4a7ee177472c8b8a26b9d6462595289a4981007b88940bd1ecc927253457d00006a8825e4792680541a7f2148237a02d9d0c1b40a8453410ba8d79740000105e0780d800840c9a6df885e4648eee39c06e09e604fc1c98976304255c68600004f613e245a16e4037a1da696000075b09b842c179057a9cd841d176c00588344348be285227d2094a7c8314a7928d40d9c8b720560001dd06f992520000dce0ce8622256000065c00000001e9a80780004670000a44a1260002198a4e11466830968000087a000279a00000008a7016c5c99f606439dc48f78fe4794091e70109042c9248c9b38462a0b94d40000ea4971299e32e000077e000000000105c810be7dca26a55300000000d7a78e800026480001361b886e6098a54e08aa63f02483d90da072d0450499a7b82728ecea632186396105851da67451a8cd435b031c508883e9bf94fc6f499387b48b3aa21006697b892439480003d0a48a5f3a9a4679201847c0f14350826035625bc0001e2a13a25fa1dca43289913aa8b112c8876256a26828d4257800006880b462d868823a800034ca24200780004058000000000000006305cc800000000003cb205855f1eb0000000000015e892891584271624192a01a9389e1863f8fa63b525881be0bce5558f2e2111e90916a2769171a1a48719b289c837c79729006be0a8822a039e5eea
  | 42 => 0x81b471889700fb0a521fa1f1a98591d875728b2a5d139a0e2939600000003010e222360b6207a000091880005d30dea77d97944d288927908f94420105a8fc00b84eb8e682b50bbe6e49b64a04906e000084e70580004551e38000142c03418b45d4848a4a6000028800002f4a75c379a65000000003929ec87f31c7c1f41360a05a7826c999d27090bd88a525f68a280000c1095669d88c68830cb60000ba035f89c24ea0b340000e7c2388000000239a4a3800000017ae0000b900001e1a3280d880001ad28af13ce00019a02f98000998965c00000005410e2800025f000000006e585f092b278a87c0b4800024d49329da816c11a0320129e3e81a7c6a3036686e8ff230d80a023811ee3a11ebe39386ca8f426345271eb469e800a24f9c7e4ef1302587259c84ea21417b92c43ef06dc3980c3c179280042514cc75c1f340e5a0c225500c48ee078617a05a2071849813a9b40a3c8d989bc8c08907011c1678000499000007b23345e8a882630a70a70515d0a1d8160660894406b1ed61510b9c76c8cd84b31692588254499f869c0ce1166a0680007e4035a04c27c00001b2a0001cc696d01be0002078a5116e00000ec00001b78596102852900003eba60c0000504087800063a062e3ae89fa7071906176816420b800060da67a77783b8162053c00000005af9a5c6ea073a5308f6c6bb98a200000000001b943720f260000e9e0001c78228800031a0000a6580000000f2440e89088ba0cb471383f4a6380006100c300001136602180c0ba8b164269e025498344133a2ce7eb9b5e5d2800049c95fa12c00ac591880c4d08ade2c408c852491282d1000076da85036190500001e4c8fe1626840186499b0ab400020f405a900808000003571e3e747047842300008c700000e48000146a8189bb07b491b9fc293102fe490000075f9d660ae947e00023800002258125867c72a87840a1107880816ac00000f234b88b02fd10fa59d93b89b217fe50508bc7ae11602f196f21718078941a11808a9b869a2800005584040001f0831b8faa4039f502fa274a973933a02126fa70c0ad09421b6a62688405bf8b500d8150c7d598de12d28fe7e814c0386a84a28188268e20ed027c93229e01e8624987328258f2a88a047477700001fc000084c000010a8b7400013da37700043fe9d5a87b8a862299a1e08e254a6d3a922493a6600940eb200f84d6a3b24924cba9b0a5f1d4c00007561ae9e2ea0c0000875022e5ef9c18000000035d000000009829460788000173e6aa2084000000022300026c400000001bfa87903a0273186e2e7a3982f0077458500000469ebc8c524faa1e077a85489345c70000901006c877183a6980000a5a0ff61b5a6a675a257631d0000000000000028142058b0e05d041651f1ab60002940a071f969878b300000300
  | 43 => 0xc19800ec50ea07a32e9656a7d133005f0e2464982c881c88a07718b7e4941f5a0dea29e036156049529a086ba54899499ec3730724003818255b1a1c0000ba23a0820c6900794000000094c9dd49ea8552381a4244a6954e8938c245ca20c497e07cc6ce287c5de948ea7490986ba0000000021c00013005b788ae239000074897ca5fe20f623c12802b2a8a66b28e6e00000000001e687a30d4aa1b0000479a62a9ec24ba7da8b6ca17052819a84a050a91004c908880a51c9e090800089112ec000240891c80007df25fe448a84200028da365169c636a58ea2610a000000000001ee61ab937a0000000000224c9bc020e6a4a8240d7a55e0001534000010c02690bc592274000024762d900008649d7c4be000044c945a8ca99a86bf80005710000018014681a99809ea078018900005a0159067a25922828bc8057a47089b02785798422445800003382c017999747f80000655297e28104865a3a52e46b25841afa6da6cfa0142331b5c0c6172e4508c1c6b40fb80069d1a00004365f31bda34e8802779163e63d194642b8a26000000060281663109de83e5a2cc2019fce6541e8400001a60000000000068652116823e2276413c83ba0f516ce00000009358c4a6bda34e3b09fa4235195c49227ac8928836161a2c01c18740690a5366dc924478c0abc7a2069e0c191b673a0c944378c163f5187017287460138d7892d8c3a82d8c2000985c06c0256606d85b6562114e05003e083716b467f8afc16529be44ba14e24c95a88b0a1106a2a4de7f5a87e7f104cc5e4814c2e127fc19b848e7b28e86646030e4881f1ea421f0471c155e2051ea872e8a4828c2852544294a000187a60a15e077b981a07418aa00000002d622545e68000a48091a2d380009b8000072710408ad25b827c000098a165a9280cf65ea87d47130000642213c5478a90000000007624c2000131e19f80000000914791a3a010f12d4441243a0e60000a43968a9e50de831f0e1c70b8dec00000002dba0ec00012a83f318529821e8e4fd94ca475239231317648510f7818a19dc38d87aaa7c80002ee91c82ae000005686f40f004326dd800059b8564000292c000129200000001ec91302d592ac00000009241ca000004b249680000001a982daa6c2101a6be8e100003699cd46d4257aa34800073e9b307c5944c2d6a08c3230fac0001aa4402a7e83c700003909a6a9b59b4a8ff0b2c6b697a48381d8453c9b0a7042354a42982a56c99c25b701d68d09b8ea4b9f5c5ee1cb04ae0b063f2a23082d025600011de76a8a4c0f19784378082056092e29b49c6a78707789f808741ec156a89b89e42c21c123a6876277d0b00984a77c8daa18228581dc629841e2fa9f3c37509aa76608305a41c1a4f18df86e428cc7d507ca3af071e4ff802c12a0270578941c24880bc3d9
  | 44 => 0x5c800000002a380006e3000010300003450000000000060f819438c0f529428a02906a1c45a6886488ba26200019866d980008880fc471624ea08b108400019ac00000000001066000000062b8ed8023069092a89bc7348bd69e80d0021200000000d4c11d9c1e3a980002a61cd07518c9e768a7b213e0fea7e2000021b0a6e5c00cf23bf008066380727e68c1899021ea80580f86b2000026980005f80a4a86a90f2880a70e6199bd01db0000000088a822a1c80a5849e56f90a81b99e9c4e8846a0730ac84f70a5e00014362370fb653d238c2240c349888d628a69e265751d940000ab07a80e106f6204ea1300007bb00000001e007c71902045977c2518000a440000000000042280000600000770a2d680389664a280007b7a51a1250034000000056b91be34a00fc1e083d291e0f627a58b284e4121800021b400007165c1a2ac0000bbc7d1938c4510000076892800023da73d09dc0dfa3c600018ce99310d80000b665ed280e231050e40e1f9e6120d248b517e274e18f85779e6c100187293e152a7db890a72d99bc00000005c58000800105600020ba96800000eb000000000006a81650000173410604f0000000007080c83c223aa627a8807a504662d793d45a528ea9c6000015c828a934164a34fa2320001a223fe015000002583f9a3a610919ea0220d3c000299c9c821e200a80000d4000051418947bc12e45b2800044800003a2199e00000005c419bea560000a0094dc0001a68489a06223994e45b5210a74b8c40739000058100002f7a44477280001ee8000a6890f612322f40000d5041a80002c2a190818100296185b28c0951c3338f9c742810e59f99301c38000301800033c028e000247a00000000000000984000050f80002211d045a30e0e9ae0af0a789b245e19f12000134c5be85fe9d6051049d1eea7a49de6a28896e8318ed678a05f80631af021180b0a31a06826fa5124e506741819a5a066800048b0f6e7f896221cb170809314fe4c9a83c5091f4e470236c3158fee1d11bbe484871211f91624a2026c8019d580f090e6932241039f831a1ef0fa48a22998672a02e9bd03345b6841c0b1a6027ec257480483a48f928b87bda6ea4bf298273c0ec45b324e00bb053886880001f180000001e0a3ec96d61f707a20001f764818d96000033e00005220000000424000000000000000000000000078d1c840000000332a9642fb14ec85b0fda58f1ac68bc95620000000a311bae02e95d6a6680000000a801f8a18a3b3090c45a82a451b205c20f21fe900a1b68d3107a2bf8d0c62a215095f8a0e6511ab468c17980970b7000016a824aa20400000004759d0e9be0658a7a0000000236e8f323f400000000001e0e0000000846a7fa6b910329f7a69a00000000000000a53046809919d616f80083b6a15485d172
  | 45 => 0x235959c000273e000000055000003169d36442a8948a58c6c42195b09e2067080da4ae12f0cde85920865a5906228a800000001e23c68ac4a37a2a21558000a77000053990f43e28c48385857c67326e2366838028e9c601e39290546275687e1bac923a5164aaa5d23c800004bc8c62000103017714864618000a61a1cc1d294701fd800062e19b489f1dfca180c2271c80001298f9200005709ad1bb452525402ab00000000000798a5cc0001b2e00015aa000145c1f6a2d26b39dec92a297800019f47e980000001b08703a06e5e30b7692f1f002f2800026d06c48b412d623ea9c60e6800004000006d10158a5497889f9201ca158fc02a680005ba118c8ed185e5b9a526506a1a44f20000130021a6f1926005c000034b222c02700009399bdc34082d441c915c56689da33303ae8aea3dc70d875a27d8272a6c8b8809100005c0a44c5f991fa273889a00000006d80480064203c66318ec833964c0e193388c826ca00023720000ef491805922cc91b20000c2e9201cfc00
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xa6e85cc262040014db0b984c40800e3d20574588100247743e84b102000ace83d09620400159b07a12c4080123b21d425881001d7240a84b102000a6e8510962040014db0a212c4080123ba1f32588100247643a64b102000a6e850c962040014db0a192c408002aba10325881000556c2064b102003ae6810c962040095d500192c408002b3e0d75588100056641aeab102004ae8805d5620400155d083aac408002ab61075588100056741ce8b102000acd839d162040015cf02ba2c40800eb9205745881000537428e8b102000a6d851d16204001c5ea92a2c408002b9e05545881001d7240aa8b102000a6e851cd62040014db0a39ac408002aba10735881000556c20e6b102003ae6811cd62040015cb0239ac408012baa00735881000574c00e6b102000e4f5394d62040095d50129ac408002ba602535881001d7340c86b102000ae58190d62040014dd0ba02c4080029b61740588100053742e60b102000a6d85cc16204009d9060982c4080123be1d62d48100243fc3acb29020018dc83dd952040011bf06bb2a4080063720d76548100247c402eca902000c5c7399552040090f90eb2aa408003171cd65548100064e39ac8a902004cb87059152040011bb0db9aa4080031799773548100062eb2ee6a902000c9e64dcd520400193ac9b9aa4082a33398b73548100046f43ac6a9020008dc8758d52040091d90eb12a40800333dcd62548100066639ac4a902000c7965dc15204001972c9b82a4080033a58b70548100145f422ec2902000c3e74594520400117f0cba0a4080630f99574148100061eb2ae82902000c9e635d0520401195cc4ba0a4080022fe1d64148100045ec3ac82902000c9e7458c520400193ae8b18a4080032b9d1621481000656ba2c4290200487d855db50040090f90bbb2a0080123b60976c801000c6e41eec90020048ec82dd9200400187cc9baa40080031798f754801027637316ea9002000c3e641d520040018bcc63aa40081371b98875480100043f43cca900201887c8799520040018b8e732a40080021fa1d65480100043e43aca9002000c5c73595200400187eeab2240080030f1d564480100064e39ac890020118dd86dcd20040018bccbb9a40080031759773480100064f326e69002000c9d64dcd200409999cc5b9a400800237a1d634801002c6e43ac69002000c5f7558d20040018b8eab1a40080031bdd56248010006363aac49002000ccf735892004001998e6b1240080032d1d376440100063bc2eec8802000c7485dd9100400196f09bb220080032d21376440100063bbb6ea8802000c77761d51004001a68e83aa20080032dddb744401000733baac48802000e64755891004001d4ee8b122008003a91d1624401002673b82c48802003ee3705891004009dc4a0b122008003b85895044010
  | 1 => 0xce9b284088003179cf65081102063b38eca102201887f8719420440010fb0e32840880030f9d065081100062f398ca102203fc7671194204401f1790cba040880030fd9574081100061e32ae810220008bf87d90204401517b0fb2040880030f9d764081100061ebaec81022000c9e73d90204407d96ce3b20408800317d9573081100062e32ae61022000c9f645cc2044001938c8b9840880031dd9571081100063a32ae21022000cb7645c42044001968c8b8840881031d9db65841100c63b3b0cb0822000e3464196104407d96cedb2420880121f21574994100c61fba4a9328200487c855ce65040318bee729cca080121f21572994100046fc1ae532820018dc835ca650403187ee93a4ca0806317dce73994100052fc1ae53282000a5c835ca65040014bd07a14ca080029760f42994100c43f43885328200087d8710a65040310fd0e194ca080021f61c32994100051f420653282000a3d840ca65040074ed02194ca080029d60432994100253d400653282000a79800ca65040310fd0fa04ca080021f61f40994100c43f43e61328200087d87cc265040071e902ba2ca0800b0f9d354594100243f43ca8b282000c3f7495165040090f90eaa2ca08007179cf53594100243f43ca6b282000c5f7394d65040090f90ea9aca080030fdd274594100053bc0ae8b282003a74815d165040018bee739aca080129ea0273594100053cc04e6b282003a768190d65040014eb0321aca0800297e0d72594100052e41ae4b282004a78805c9650400147d08392ca080028f61072594100052f41e84b282000a5d83d0965040010fd0e212ca080021f61c42594100043f43864b28200087d870c9650400147d08192ca080028f610325941001d3b40864b282000a75810c965040094f500192ca080029e60032594100043f43e80b28200087d87d0165040010fd0f982ca080021f61f30594100061fbaceab2020adab7815d5640400756902baac80800eada0673590105655ac0ce6b202000e1f5394d64040095750129ac808002ae60253590100054f41ee4b202000a9d83dc9640415756f02b92c80800ead20572590100051f428e4b202000a3d851c9640400117d0e192c8080022f61c32590100051f42864b202000a3d850c9640400756d02192c808002ad60432590100255d40064b202000ab9800c9640400147d0b982c8080028f61730590100274c18260b202000c5f759d56304001c3ea92a2c60800297a147258c100052ec28e4b182000a9e841c9630400153b08392c60800eb5a047258c1002d6ac08e4b182004ada801c9630400b5b300392c60800237a1f4258c100046ec3e84b182000a5e8510963040014bb0a212c60800297a174058c100052ec2e80b182000e2f549526204001c9ea729cc4080029ba17409881000536c2e813102000
  | 2 => 0x473589100064fba0e6b122000c9c741cd6244001998e7b92c4880032d1d371589100063c3aee0b1220008ef87588624400159906b10c4880221f21576d49100045fc22eda9220028bc845db524400117f08bb4a48800a2f21176949102063b38ecb29220048f4865c65244001968c8b8ca48800a2fa1376549100045ec26eca9220018de839d952440011bb073b2a4880022fe1176549100145e422eca9220008df835d952440031b906bb2a4880023ee0176549100443f43ecaa922000c5c73d9552440018b8e632aa488003271cf64549100062fb2ee6a922000c5c65dcd524400193ec9b9aa4880032719373549100145e424ec29220008bf845d8524400517908bb0a4880030f9d365149100045e432e82922000c3f655d05244031878caba0a4880022fe1f64149100045ec3ec829220048f4865c452440318f0cb380a48800e3e21970149100c63c32ce1a8a20009b9849c35144005179083b2a2880030f1d365545100061e3a0caa8a20008be86dd1514400187ecbba2a2880030f19774545100045f43ec8a8a20008bc87d9151440018f6ca382a28800a2f21276c85100043f434eb90a2000c3c649d721440010f90cbae42880030f19175c85100043fc3ecb90a200087d87d97214400187ce9b2e42880621fe1c65c85100043ec38cb90a2000c3e7419721440011790cba642880030fd9574c85100061e32ae990a20008bf87d93214400117b0fb2642880030f9d764c85100061ebaec990a2000cb4649da2144001c68c832c42881039908765485100063c32ee090a2000c78651c121440013730838242880038d190654851000733b28c490a2000bb1841c12144005179093b4a0880030f9d365941100062f39ecb2822000c3e7419650440018bce632ca0880762f21974941100061fb2ae92822000c3c655d2504400117f0fb24a08802a2f61f64941100064f39ec92822000c5f655ce50440018b8cab9ca08800327d9173941100064e322e728220008bf845d9504400517908bb2a0881031d1c765541100065a326e2a822004ae48648720440091eb033b440880021fe1576481100c43e42aec90220008bf845d9204400517908bb2408800237e0d764811000c6e41aec902203f87e86dd52044001878c9baa40881021fa1875481100061e320ea902204d87e87d9520440810f90fb2a4088003171cf65481102743f438ca902201887c8719520440018b8e632a40880030fdd764481100061e3aec89022000c9c73d9120440018becbb9a40880031719773481100064fb26e69022000c9c64dcd2044001998e7b1240880123da1b71481100065a326e290220049e48748520440095c90c90a4088012f820121481100145e424ec10220048f4819d82044001878c93a840880030f19175081100043fc3eca102200087d87d94204400187
  | 3 => 0x832a2000e1d831906544001c7300320ca880021f61e63195100051f424c632a2000a3d8498c65440010ff0eb18ca880028fe1163195100051e422c632a2000a6f8258c65440014d904b18ca880038e19240195101fd3c4328032a2018c3f749d065440318bee7398ca88063171cd73195100053d4008632a2000a798010c65440014bf06b90ca880029720d72195100052f41e8432a2000a5d83d0865440014f501a10ca880029e60342195101fd3b40c8432a2000a758190865440310fd0e210ca880021f61c42195100c43f4386432a200087d870c8654400147d08190ca880028f61032195101fd3b4086432a2000a75810c865440014f500190ca880029e60032195100051fc22e232a2000a3c845c4654400147d09988ca880028f61331195100053d4066232a2000a7980cc465440310fd0fa00ca880021f61f40195100053bc0a8032a203fa748150065440014bd06200ca880029760c40195100c43f43e6032a200087d87cc0654400147d08180ca880028f61030195100061f3b6cbb2220008bd87997644400147d0b32ec8880022fe1d65d91100051f430cbb222000c3e76197644400117b0f31ec8880028fa1663d91100051ec2cc7b2220008bf8758f644400147f0ab1ec8880028f21563d911000557c12c7b222000aac8258f644400187aea3aec88800387d4e53d91100051f42ce5b222000a3d859cb644400153f06b96c888002a720d72d91101f55b408e5b222000ab5811cb644400117d0e196c8880022f61c32d91100051f42865b222000a3d850cb644407d56d02196c888002ad60432d91100055d40065b222000ab9800cb644406f57501b8ec8880022fa1f31d91100045ec3e63b222000a3e85cc3644400147b0b986c8880022fa1c30d91100545ec3861b222000ae5810cb62440015d300196c4880030f9d365989100061f3a0cb3122000c3f655d26244001878caba4c4880030f9d764989100061ebaec93122000c3e75192624400187aea324c4880021fa1f65589100061e3a6cab122000c5c73d9562440010fd0e32ac4880030f1d065589100062e398cab1220028be86dd1624400187ecbba2c4880030f19774589100045f43ec8b122000c3f75d916244001878ebb22c488003271cf64589100045f438c8b122000c3f751916244001878ea322c488003271cc64589100062fb2ee6b122000c5c65dcd624400193ec9b9ac4880032719373589100061fbaee8b122000c3c75dd162440010ff0aba2c4880621f21574589100046fc1ae8b1220018dc835d162440011ef02ba2c4880030fdd474589100061e3a8e8b122000c5f75dcd62440018b8ebb9ac48800327dd373589100064e3a6e6b12200087f855cd62440310f90ab9ac4880022fe1173589100145e422e6b1220008ef825cd62440018beea39ac488003171d
  | 4 => 0x5c40070f90eaa2cb8800b0f1d154597100045fc22e6b2e20028bc845cd65c40070f90ea9acb8800e3b21d4258b100443e42aeda9620008bf845db52c400517908bb6a58810e1f61e6594b1001c3fc3acb296200887d85dd952c400117f08bb2a58800a2f2117654b100046fc1aeca9620018dc835d952c40890ff0eb28a5880630f9957414b100061eb2ae8296203f87f8759750c40810fd0f32aa18800b0f9d354d96100143fc3aa9b2c2002c3e7455365840038bce7a9ecb080061fe1d53d961000e2f39aa7b2c20008ef825cd65840111d904b9acb0800237e0d721961000c6e41ae432c200087f855d162840310f90aba2c50800237e0d7458a1000c6e41ae8b1420018de87dcd62840018beebb9ac508003171d77358a100043fc2ae6b14201887c855cd62840011bd0e39ac50800317dd47358a100062e3a8e6b14200087f855d952840011bf06bb2a5080063720d7654a100043f43ccaa94200487c8759552840310f90abb0a5080021f61f6514a100061fb2ae82942018c3c655d052840810ff0eb2ea3080fe1fa1e65546100161e3a6a9b2a2000c3d7495365440014f3012a6ca8800a1fe1d54d95100062eb9ca7b2a200187f8754f65440038bce6a9eca8800297a0c64d95100052ec18c9b2a2000e1e831936544001c3b06326ca880038e60064d95100051f424c7b2a2000a3d8498f654400147f08b1eca880028f21163d951000537c12c7b2a2000a6c8258f6544001c70c9206ca881029e21940d95100061eba0e9b2a2000a5e831d365440014bb063a6ca880029ea0074d95102053cc00e9b2a2000c5f739cf65440018bae639eca8800297a0f72d95100052ec1ee5b2a2000a3e849cb654400147b09396ca880029d60472d95100052f41e85b2a2000a5d83d0b65440010fd0e216ca880021f61c42d95100043f43865b2a200087d870cb654400147d08196ca880028f61032d95102053b40865b2a2000a75810cb65440014f500196ca880029e60032d95100051f426e3b2a2000a3d84dc765440014bd07b8eca880029760f71d95100051f42663b2a2000a3d84cc765440810fd0fa06ca880021f61f40d95100052f41881b2a2000a5d8310365440810fd0f986ca880021f61f30d95100051f42061b2a2000a3d840c3654400187ce9b2cca880030fd9574995100c61e32ae932a2000c3f75dd165440010ff0aba2ca880023de0574595100061fba8e8b2a200087f855cd654400117f08b9aca8800a2f211735951000477c12e6b2a20088ec825cd6544001968e9b8aca880021fe1d65195100051fc22ca32a2000a3c8459465440310f90aba0ca880630fdd254195100c43e42ae632a2018c5c535cc65440011bf06b90ca880063720d72195100043ec3cc832a200087f8759065440014bd06320ca880029760c64195100070f418c
  | 5 => 0x28f61431590200051f42e60b204000a3d85cc164080018beeb3aac6102c2b3e097558c2004566412eab184008ace829d1630815f59b053a2c61000387d525458c200256d404a8b184000ad980951630800153d09b8ac610002a76137158c2057567c12e2b184008acc825c563080014bd0a38ac610002976147158c200046f43882b1840008dd8710563080014bd0a20ac610002976144158c200456741082b184000acd8210563080095b50020ac610002b66004158c200052f42e80b184000a5d85d016308009d3080a02c6100038dd5254984200072ba9ca73084000a7685d0261080014eb0ba04c2100029da1730984200053ac2e6130840088ec825cd61080091ed0fa0ac2100123d21d41584200053b42882b084000a758510561080015ad0620ac210002b560c41584200457341082b084004af28010561080091ed0f98ac210002ada1331584200055ac2662b0840048f4874c561080115c90498ac2100029da1431584200053ac2862b084000ab7845d5610800156908baac210012bc20175584200056b418eab084000ad5831d561080014ed0a3a2c2100029d61474584200056b418e8b084000ad5831d161080115cd043a2c210002b9608745842002579400e8b084000af1801d16108001c6ea92a2c210012bca02545842000578c04a8b084000ab6849cd610800156b0939ac210002b9e09735842004572412e6b084000a76851cd61080014eb0a39ac21000395d4e535842000573c12a6b084008ae48254d61080115cd05a1ac210002b960b43584200053b42e80b084000a7585d016108009d6080a02c2100029da1730584200053ac2e60b0840028bc84dd9510800117f08bb2a21000a2f21176544200061e3a4caa884000c3c74595510800117b0dba2a2100030f99774544200061eb2ee8a884000c9e63dd1510813596cc3ba2a2100022fa1d64544200045e43ac8a884000c9f7458d5108001938e8b1aa210013361c163544200065bba2c2a884000cb47458551080018f2cbb82a2100033658f705442000678b0ee0a8840018de835d851080018bce6b28a210003279cd64144200046fc32e62884018c5e655cc51080018bacab98a2100032799173144200064eb22e62884003cd6615cc51080011bf0eb18a2100023761d63144200066b39ac22884000cd57358451080090fb0abb6a0100121f21776540200066639eec9004000c6f85dd920080018d90bbb2401000333e0f76480200066641eec9004000c6f76dd520080018deec3aa4010003531cc754802000667bb6e69004000e67755852008001cc8eab0a4010003b1dcd61480200076239ac29004008ee3705852008009dc4a0b0a4010003b8585504802001c3e42ae532e20008df835ca65c40031b906b94cb8800a2fa1f74597104d45f438e8b2e2002c3c74d516
  | 6 => 0x61fb2ee8a8a4000c3c65dd15148001938c7ba2a29000327dd363545200064e3a6c6a8a40018dc839d851480011bf06bb0a2900063720d76145200062f39eca28a40008dc865cc51480018becab98a2900631719573145200046fc3ec628a40008dd87d8c51480318f0cb380a2900033318e76c852000726318cb90a400087e869d621480018b8c73ac42900021f21975885200062e31aeb10a400087d87d9621480018bce7b2c42900021f61c65885200062f398cb10a40008dc865ce21480018becab9c42900031719573885200046ec3ec710a4000c5e75d8e21480018baebb1c429013b9908765485200063c32ee090a4000c78651c121480013b30638242900039318c654852000733b28c290a4000bc9831c121480031b9073b4a0900030f9d365941200062f39ecb2824000c3e7419650480018bce632ca0900030fd9574941200061e32ae92824000c9c635d250480331b90cb9ca09000317d9573941200062e32ae728240008df87d8e50480231bb0fb1ca090003279d363941200064eba6c728240008df835d950480031b906bb2a09013b1b1cb65541200066631ee4a82404ec6e76d9620480318dcec32c40900039318c6588120266673b6c7102400487c855d2650803187ee92a4ca100121f21573994200c62fb9ca7328400487c855c6650800117f08b8cca1000a2f21171994200c61fba4e93284018c5f739ce650800147f08b8cca100028f21171994200c43f43883328400087d8710665080014bd0620cca100029760c419942004537410833284000a6d8210665080094f50020cca100029e60041994200051f426633284000a3d84cc665080310fd0e18cca100021f61c31994200c43f43e81328400087d87d0265080310fd0f984ca100021f61f30994200161f3a6a8b28400487e87951650800187ee92a2ca100121f21d545942004476412e6b284001c5e73d4d65080090fd0f29aca1000317dce53594200243e43aa6b284000c3f749d165080094f5013a2ca100029e60274594200062fb9ce6b284000a6f825cd65080114d904b9aca100229ba0b435942000536c1686b284000a3f845c5650800147908b8aca100129e20171594200052f418e2b284000a5d831c565080010fd0e20aca100021f61c41594200052f41882b284000a5d8310565080114dd0420aca100029b60841594200253d40082b284000a7980105650800147d0998aca100028f61331594200043f43862b28400087d870c565080010fd0fa02ca100021f61f40594200043f43e60b28400087d87cc1650800187eeb3aac81000387d4e53590200051f428e2b204000a3d851c5640800153d0638ac810002a760c715902004557410e2b20400faad821c564080095750038ac81003eae60071590200045f43e62b2040008bd87cc5640800147d0a18ac81
  | 7 => 0x3e8418c654800147b08318ca9000387a1063195200070ec20c632a4000e598018c6548001cb0c7180ca901369e21930195200c61fba4e832a4018c3c745d065480318bee7398ca900029ea0043195200053cc008632a4000a5f835c865480014b906b90ca9000297a0f42195200052ec1e8432a4000a7a80d0865480014f301a10ca900028fe1171195200051e422e232a401887e8710465480010fb0e208ca9000297a0c41195200052ec188232a404da6e8210465480014db04208ca900029ea0041195200053cc008232a4000a3e84cc4654800147b09988ca900029ea0331195200053cc066232a404da6e828c465480014db05188ca900621fa1c31195200043ec386232a401887e87d0065480010fb0fa00ca9000297a0c40195200052ec188032a401887e87cc065480010fb0f980ca900029be09301952026d364126032a4000a3e840c0654800147b08180ca90003179db65d8d200046ec3ccbb1a4000a5e8599763480011bf0eb2ec69000297a1865d8d200062f3b0cbb1a40008dd8799363480014bd0b326c6900029761664d8d200046fc3ac9b1a4000a5f8559363480014b90ab26c690002b5e0564d8d200056a40ac9b1a4000c5d751d76348001c3ea92a6c690116b6a0372d8d200046f43e85b1a40008dd87d0b63480014bd0b38ec6900029761671d8d200054fc22e3b1a4000a9c845c7634809959d0438ec690002b360871d8d200046f43883b1a40008dd8710763480014bd0a20ec6900029761441d8d202656741083b1a4000acd8210763480015b50020ec690002b660041d8d200052f42e81b1a4000a5d85d0363480011bd0e206c6900463761c40d8d200c63c32ce1a9240009d9839c352480031b9063b2a490003171cf65549200062e398caa9240008de86dcd52480018becbb9aa4900031719773549200046f43ec6a9240008dc87d8d52480018f6ca382a490002b960841d852000578c0083b0a4000c5e73d9661480018bce632cc29000317d9573985200062e32ae730a4000c5e75d8e61480018baebb1cc290003179d463985200062eba8c730a400087e87d956148001878e9b2ac290003171cf65585200043f438cab0a4000c3c7419561480018b8e632ac2900030fd9774585200061e32ee8b0a40018de86dcd61480018becbb9ac2900031719773585200046f43ec6b0a4000c5f75d8d61480018b8ebb1ac29000327dd363585200064e3a6c6b0a40008de8718d61480018beea31ac290003171d463585200064fba0c6b0a4000c9c7418d61480011ef0eb08c290002ad21161185200046fc1aeda8a40018dc835db51480011bf06bb4a2900063720d769452027637396cb28a4000ccc635ca51480031bd07bb2a2900023760f76545200145f424eca8a40008bd849d95148001878e9b2aa2900030f1d065545200
  | 8 => 0xeaa2cb9000637a1f73597205446f438e6b2e4001c5c73d4d65c80110f90ea9acb90007171cd53597200447a43a62b0e400387c855db51c80011bf06bb6a3900063720d76d472028c3ec3ccb28e400387d85dd951c800117f08bb2a39000a2f21176547200046fc1aeca8e40018dc835d951c80a50ff0eb28a3900631799573147200062eb2ae628e404d87f8759750c809d0fd0f32aa19000b0f9d354d96200143fc3aa9b2c4002c3e7455365880038bce7a9ecb100061fe1d53d962000e2f39aa7b2c40008f7815d165880071e902ba2cb100022fe1171196200145e422e232c404e87f87597528809b0fd0f32aa5100030fdd774586200061e3aee8b0c400087f855d161880310f90aba2c3100030fdd474586200061e3a8e8b0c400087f855cd61880310f90ab9ac3100022fe1173586200145e422e6b0c40008bf845d9518800517908bb2a3100021fa1e65546200043ec3eca28c4000c5f655cc51880318b8cab98a3100030f5d254d95200143fc3aa9b2a4002c3e7455365480038b8e7a9eca90003175ce53d95200053cc04a7b2a400187f8754f65480014bd07326ca900029760e64d95200052fc1ac9b2a4000a5c8359365480014ef02b26ca900029d20564d95200051f420c7b2a4000a3d8418f6548001c3d0831eca900038761063d95200072cc00c7b2a4000e58638c3654809d4f10c986ca900030fdd274d95200061eba0e9b2a4000a3e841cf654800147b0839eca90003175cc73d95200053d400e7b2a404ea79801cf654800147d09b96ca900028f61372d95200052f41ee5b2a4000a5d83dcb65480014bd07a16ca900029760f42d95200051f426e3b2a4000a3d84dc765480014bd0738eca900029760e71d952000536c10e3b2a400087e8710765480010fb0e20eca9000297a0c41d95200052ec1883b2a404ea6e8210765480014db0420eca900029ea0041d95200053cc0083b2a4000a3e84cc7654800147b0998eca900021fa1c31d95200043ec3863b2a404e87e87d0365480010fb0fa06ca9000297a0c40d95200052ec1881b2a404e87e87cc365480010fb0f986ca900028fa1030d95200051ec2061b2a4000c5e73d9665480018becab9cca900631719573995200043fc2ae8b2a40008df835d165480031b906ba2ca900023de05745952001c7a40ae8b2a4000c5f75dcd65480010ff0ab9aca900023be0973595200062fba8e6b2a4000ccc73dc965480010ff0eb28ca9000297e0d65195200052e41aca32a401887c855d06548031878a8ba0ca900621f21573195200c62fb9ca632a40008bf845c4654800517908b88ca900021f61e64195200052f41cc832a4000a5d8399065480010ff0eb20ca9000297e0d64195200052e41ac832a4000a778159065480014e902b20ca900021f61e63195200043fc3ac632a4000a
  | 9 => 0x75886500061f3aac910ca000c3d75592219400193ce6b24432800237e1973886500064f322e710ca000c9d645ce21940011bf0eb1c43280023761d63886500062f3aac710ca000c5d7558e21940018eaeab0c43280132e9c164086500266d382c610ca018978855c02194001972c8b8043280033658d70086502743fc3ac5a84a04ec6e7258b50940810ff0eb0ea1281031d9c561d42500065d322eda84a000cda635db5094001972ecb26a128003365d963d42500074cb22c7a84a000a6d850cb62540015d300196c4a80022fe1171d89500145e422e3b12a04ec3f655d062540011df0eb10c4a8002b320d62189500145f424eda92a0008bd849db525400147b093b6a4a80030fa1276d49500061ec24eda92a04487c865c75254001998e7b12a4a82a3171db73549500043f436e2a92a0008df835cb61540031b906b96c2a80029d61441d855000578c0083b0aa040c5f655cc61540011ef0eb08c2a8002ad211611855000c6f41ceda8aa0008dd839db51540014bb073b6a2a800317a0e76d45500062ec1ceda8aa05287c865cb5154001968e9b0aa2a826b0f1db74545500043f436e4a8aa00887c859db21540070f90b3b442a80021fa1a75485500243e432ea90aa004978805d521540810fd0d3a842a813a1f219729415027636312e5282a04087c865c650540818e8c2b8ca0a800237e0d745885000c6e41ae8b10a04d87c8755162140038b8e7a9ac4281361f21d535885000e2e39aa6b10a0048ec875096214001c5aa8a12c428007331ce325885000727a9c64b10a0048ec874c9621403187ec4ba0a4280634b989741485026e1eb12e8290a018d2d625d0521409d87cc0ba0a4280634e98174148500161e3a6a8b08a03f87c875516114005878e8aa2c2280022fe1173584500145e422e6b08a03f87c8754d611407f0fd0f292c2280fe9da0652584500043f438a4b08a000a3d84149611407f4ed02292c22800b2d1d241584500071baa482b08a0048f48750561140091e90e98ac2280039554d315845026c3fc3ac5288a04dc6e7258a51140318bec2b98a2280635598573144501fe2eb0ae6288a018d55615cc51140818bcc0b98a2280635698173144500043fc3ac4288a000c5d73588511409b8dce4b10a2280221f61576c845004657312e9908a018c6e7558b211400195ae8b16422800e1f615768845001e6b30ae7108a018c767558621140019aae6b0c42280022fe1176484500145e422ec908a0008df835d921140031b906bb242280021f61b754845002674382c4908a004cf070585211409b0ff0eb16a0281371b9c962d40501fc3fc3ac3a80a03fc7671587501409b0f90eb12a0281371b1c962540501fc3e43ac2a80a03fc7471585501400117f08b8ccb9000a2f21171997200046fc1ae8b2e40018dc835d165c80110f9
  | 10 => 0xb1ca000e1e64551639400159f04baac728002b32097558e5039d6dc02eab1ca0b3a5e859d163940014bb0b3a2c728002b3a0a7458e5000566c14e8b1ca000e1f5495163940095b5012a2c728002b66025458e500052fc2ae4b1ca07ea5c855c963940334bd0a392c728002976147258e500054f420e4b1ca000a9d841c9639400199ae4392c728002b5a047258e500056ac08e4b1ca004ada801c963940335b300392c72800237a1f4258e500046ec3e84b1ca000a5e8510963940014bb0a212c728002a7a137158e500054ec26e2b1ca000a5f855c563940ed4b90ab8ac72806697a147158e500052ec28e2b1ca0008de8710563940011bb0e20ac72800297a144158e500052ec2882b1ca000ace82105639400159b0420ac728012b6a004158e500056cc0082b1ca000a5e85d0163940014bb0ba02c72813a1fa1f5458a500161f3a2a8b14a04e87e87d4d62940038b8e7a9ac52800a2fa137158a500045ec26e2b14a004cda7058e52940019b2c6b84a5280038b5916294a5000726b1ac5294a000c9c735915294009970e0b22a5280023761b7354a500064f326e6a94a000c9d64dcd52941651b90eb1aa5280032e5937054a501845fc32e8294a000c9e635d0529403b17f0eb20a528003279d16314a500064eba2c6294a000c3e645d852940018bcc6bb0a5282024fe197414a500068f31ae8294a04ec3f625d0529409d87ac4ba0a5280630f9817414a500049ec3ac8294a000c3d7659052940018baecb18a528003475d16314a502043f43ea8b0ca002c3c74d5161940810fd0fa9ac328007179cd535865000c6f41ee4b0ca0008dd83dc961940010fd0f292c3281029da0652586502043f438a4b0ca000a3d8414961940814ed02292c3280132e9c164946500065cb22e128ca00087f8758a519409d8dce4b14a3280038d59161946500072ab1ac328ca0008bd86dd1519400193cc7ba2a3282c62f21d64546500064fba2c6a8ca000c9c7458d51940099b0e0b1aa3280033658f70546500064f39ac828ca0278df865cc519400193cc8b98a3280032759173146500cc6fc3ac628ca000c3e645d851940018bcc6bb0a3280030f5d964146503b4afc32e628ca000d1e645cc5194001a3ac8b98a32810317d8573146502062eb0ae628ca018c5e605cc51940012bb0eb18a328003175d963146502743fc3ac428ca000c5d73588519409d8dce4b10a32800a2fa1176c86500061f324eb90ca000c5e639d7219400187cc8bae43280031798d75c86500045fc32e990ca000c9e635d3219400117f0eb2643280022f61d64c86500061f3aac990ca000c3d7559321940018bceab1e4328003175d563c86500064f3a2c790ca000c9d7458f21940018daeab16432800637a0d76886500061f324eb10ca000c5e639d6219400187cc8bac43280031798d
  | 11 => 0x884071f10ea02c1108223d60774d952101c76c16e7b2a42008df835ca65484031b906b94ca908022fe1171995210145e422e332a42008df835d165484031b906ba2ca908023ee0174595210247c402e8b2a4202c3c74d5165484050f90eaa2ca9080b0f1d154595210064fba6e6b2a4200c9c74dcd654840117f08b9aca9080a2f21173595210047dc02e6b2a42048f8805cd654840193ee839aca90803271d0735952100e2e39ea6b2a420187c8754d65484038b8e6a9aca908032edd370595210065c3a6e0b2a4200cdb73dc165484019b0e7b82ca908031edd470595210065dba0e0b2a4200cb8741c165484019b6e6382ca90803361cc70595210063daa0e0b2a4200c79541c165484018f6a6382ca908031e54c70595210063d290e0b2a4200c78521c165484018f4a2382ca908031e14470595210043fc3aca32a4200a788059465484a30fb0fb2ea49094a1fa1c655492121c3ec3ecba8a42008bf845d9514840517908bb2a29080237e0d765452100c6e41aeca8a424487e87195514840117f08baec09080a2f21175d81210046fc1aebb0242018dc835d760484011f70eb00c0908029e21560181210263c402ea3024204cba105d060484099b440b98c09080e1f21d545942101c3e43aa6b284218c79801d560084010ff0aba2c0108621f21574580210043fc2ae6b00421887c855cd60084071f10ea02c01080e3e21d30580210145f426e2b16a0008bd84dc562d40010ff0cb8ea5a8003171cf7654b500062fbb6e6a96a04387d86dc552d40878ecc3b8aa5a800637a0f72587500046ec1ee4b0ea00087f865cb51d4001878e9bb2a3a80030fddb745475028c3ec36e4a8ea051c6e62dc951d40090fd0bbb243a80125e2017548750004bcc28e090ea03f87f865d421d403b47f0cbaac928002cd20575592500070ec2cc6b24a000e1e63d4d6494001c3cc6a9ac928002ade0575592500055a40aeab24a074abb805d5649416947d0b39ac9280028f61673592500055b40ce6b24a000ab5819cd6494001c3ea729ac928012aea0253592500055cc04a6b24a000a9e83dc9649400153b07b92c9280028fe1572592504051e42ae4b24a01da3e851c9649400147b0a392c9280022fa1c32592500045ec3864b24a000a3e850c9649400147b0a192c928002ada0432592500055ac0864b24a004aba800c9649400157300192c9280028fe1571592503c51e42ae2b24a01da3e851c5649400147b0a38ac928002a7a0c71592500054ec18e2b24a000aae821c5649400155b0438ac9280032d5c471592500255d400e2b24a01dab9801c5649400117d0f98ac9280022f61f31592500051f42862b24a000a3d850c5649400147d0b982c9280028f61730592500cd2fc32eab1ca000b4c825d56394001c3b0b322c728013a61416458e500070f326a8
  | 12 => 0x80297a0c40597210052ec1880b2e4208a6e8210165c84014db04202cb908021fa1f30597210043ec3e60b2e4200a3e840c165c840147b08182cb908229ba08305972100536c1060b2e4200c3f759d564c8401c3ea729ac990adaabe0971593210045f43e62b2642008bd87cc564c840147d0bb82c9908028f617705932104557414e0b26424baad829c164c840156f02b82c990a32ad20570593210054f418e0b264200a9d831c164c8401972e0382c9908028fa1730593210051ec2e60b2642008be870c164c840117b0e182c9908631b99572d47210061e3a4caa8e4200c3c7459551c840117b0dba2a3908030f99774547210061eb2ee8a8e42008bc8759151c84018dacbb92a39080a2fa1375583210045ec26eab0642088f8874c160c84070f90aba4cb108630f151749962101c3e42ae732c4218c5f7394e658843187ee93a4cb108630f1d174996210c62fb9ce732c4200a5f835ca65884014b906b94cb1080297a0f42996210052ec1e8532c4200a3e849c2658840147b09384cb1080297a0e70996210052ec1ce132c421887e87d0265884010fb0fa04cb1080297a0c40996210052ec188132c421887e87cc265884010fb0f984cb108029be093099621295364126132c4200a3e840c2658840147b08184cb1080e3d205745962101c3f43ca8b2c4200c3f7495165884070f90eaa2cb1080b0f1d1545962100e2f39ea6b2c420387e8794d65884018bee729acb1080e1f21d53596210061fba4e8b2c4200a77815d165884074e902ba2cb108030f5d074596210051f424e6b2c4200a3d849cd65884018bee739acb1080e9da0673596210053ac0ce6b2c4200a7a809cd65884014f30139acb1080e9da0643596210053ac0c86b2c4200a3f845c9658840147908b92cb1080297e0d72596210052e41ae4b2c4200a7b805c965884014f100b92cb1080297a0f42596210052ec1e84b2c4200a3e849c1658840147b09382cb1080297a0e70596210052ec1ce0b2c4203a76819c165884010fd0fa02cb108021f61f40596210052f41880b2c4200a5d8310165884074ed02202cb108029d60440596210043f43e60b2c420087d87cc1658840147d08182cb108028f610305962101d3b40860b2c4200a75810c165884018beeb3aac71080387d525458e215ad6bc0ae4b1c42008de87d0963884011bb0fa12c71080297a177058e210052ec2ee0b1c4203ad6819c1638847b5ab03382c710802b3e097058e2145d66412e0b1c4200a9e841c1638840153b08382c710803365c07058e210052f42e80b1c4200a5d85d0163884011bd0e202c7108023761c4058e210c63b32ae3a944200c5c7399552884018b8e6b2aa5108023761b7354a210062f32ee6a944200c5d65dcd52884011b90eb1aa5108031d5977154a2100c6f41eeab0442008dd83dd560
  | 13 => 0x45f438c8b02a2b1c3d7519060544011f70eb00c0a880b0f9d3541815100e2f39ea6302a2008df835c860544031b906b90c0a88021f61e52181510051ec20a4302a200e5b534c060545714bf0aba2c628862972157458c510c70faa4a8b18a218a5e859c9631456f4bb0b392c62886297a147258c5113d2ec28e4b18a200a9e841c9631440153b08392c62880eb5a047258c5113d6ac08e4b18a200ada801c963144015b300392c62880237a1f4258c510046ec3e84b18a218a5e8590963144014bb0b212c62880eb5a064258c510056ac0c84b18a218a5e8510963144014bb0a212c62886297a177058c5113d2ec2ee0b18a275a5f855c163144314b90ab82c628802b3e097058c5100566412e0b18a200a9e841c1631440153b08382c62886297a174058c510052ec2e80b18a200a5f8550163144314b90aa02c628802b5e054058c5101d6a40a80b18a2008de8710163144011bb0e202c62880e3b21d42588510c62fb8ac7a90a244c5d7158f52144010fb0d386a4288031758e70d485121e2ebaac7290a2018dc83dd952144651bb0db9aa42880237a1d635485113c6e43ac6a90a200c5c73dd952144018bf07bb2a4288031720f76548510062fbb6e6a90a200a5e8758d521451d4b90eb1aa42886317dc963548510c727b92c6a90a243c5f7158d52144878bae2b1aa4288031758c70548510065a3a6eca88a200cb776dd151144011bf06b94c0288063720d729805100477c12e6b00a2088ec825cd601449d0fd0fa92c02880e3e21d405805101d7840a80b00a20887c855d265c843187ee92a4cb908221f21573997210c62e29ae732e4218c3f749d265c84318bee739ccb90863171cd73997210051fc22e332e4200a3c845c665c840147d0998ccb908028f61331997210051f424e132e4200a3d849c265c84014bd07384cb908029760e70997210c43f43e8132e420087d87d0265c84014ef02a04cb909129d20540997210052f4188132e4200a5d8310265c84310fd0f984cb908021f61f30997210051f4206132e4200a3d840c265c840587ce9aa2cb908221fa1e54597210061fba4a8b2e420887c8755165c84071d904b9acb908221fa1e53597210062fb9ca6b2e420887c8754d65c84038b8e6a9acb908030fdd274597210052f41ce8b2e4200a5d839d165c84114dd053a2cb908029b60a74597210053d404e8b2e4200a79809d165c84018bee739acb908029be09735972104536412e6b2e4200c5d731cd65c84114dd05a1acb908029b60b43597210051fc22e2b2e4200a3c845c565c84014bf06b8acb908029720d71597210053dc02e2b2e4200a78805c565c840147d0998acb908028f61331597210051f424e0b2e4200a3d849c165c84014bd07382cb908029760e705972104537414e0b2e420087e87d0165c84010fb0fa02cb90
  | 14 => 0xc855c1641480156f02b82c829002ad20570590520054f418e0b20a400a9d831c1641483147d0b982c8290028f61730590520051fc2a60b20a418a3c854c1641480155f04982c829022ab20930590520045f43860b20a4008bd870c16414801998e7bb2a42900333ddb73548520447a43a62b08a4008bf845c6601480517908b8cc0290023de05745805201c7a40ae8b00a4088f8874c160148115d104982c02900237e0d7458b5100c6e41ae8b16a25287c8755162d44038b8e7a9ac5a894a1f21d5358b5100e2e39aa6b16a20095f835da52d443187ec4ba0a5a894b0f5897414b512043fc32e0296a204cba105d260d440587ce9aa4c1a880b0f9d1549835100e2f39ea7306a201c5e7354e60d44010fb0e294c1a88028f610529835101c7643a84b14a200a6d850c9629440155b08192c52880eb9a043258a5100574c0064b14a200a3f845db5294401998e6b12a528aa317ddb7354a51006abb9ee2a94a20087d861c152944a387acaba0a52880237e0d729825100c6e41ae5304a24d87c8754960944071f10ea02c1288022f61e63d91510055d404c7b22a200ab98098f645440117f0eb1ec8a8a6a8f21953d91515cd1f428e7b22a29aa3d851cf645453556d0239ec8a8802ad60473d91510070fa9ca7b22a296a3e85dcb645453547b0bb96c8a88ae8fa1672d91510051ec2ce5b22a200a9f835cb645440153906b96c8a88022fa1c32d91510045ec3865b22a200a3e850cb645440147b0a196c8a8a6aada0432d91510055ac0865b22a200aba800cb645440157300196c8a8a368fa1771d91510045f43e63b22a2008bd87cc7645440153d07386c8a8802a760e70d91510051fc2ae1b22a22ba3c855c3645450b47d0a386c8a8a6a8f61470d91510051f42e61b22a200a3d85cc3645440117d0e186c8a88022f61c30d915158e1eba8c9b12a25187d87d536254405878e8aa6c4a89461f61f53d895100e2f39ea7b12a2008be87d916254401938e7b22c4a88022fa1c64589510064e398c8b12a200c9f64dcd6254401938c9b9ac4a88032ed9370589510065c326e0b12a200cbb641c16254401970c8382c4a88023be1d62189510065a322e3292a29ac3e76d925254401c5ec9b14a4a88fe1f21970949510064e39ec8a92a200c9f64dcd5254401938c9b9aa4a880a2f21276149511845e432e8292a2008bf87d90525445717b0fb20a4a88030f19276149510061fc24ec292a200c3c849d8525452d2790cba0a4a89470fd89741495128e1eb12e8292a218c3f615d05254431a6ec2ba0a4a88024fe1f64149510061f3b6c8292a29ae3765d9351544031f70e986c0a8803279cf64981510064f398c9302a200c9f645ce6054401938c8b9cc0a88133618173981510066cb9ec1302a2028be86dd160545351790dba2c0a88022fa1f645815100
  | 15 => 0x140000000040800ac08800c02004000801000c00c00800400c00800008c05400803403c00004400402005c00800400401001c0380ac00c00802c00400805c0980040000c401c00402400c08000802c00800009000003405c05402400801401400400c0180c804400000409c0240000840680080ac00001001001c0000000000440080080e800c0080141f403400c02801402400400000003003400000001400001001805c01800000005801407005878e9aa2c3a91121f21d54587520161e3a2a8b0ea4008bf845cd61d480517908b9ac3a91121f21d53587520161f3a6a9306a402c3e7455260d48099b440b9cc1a9007179cf539835200e2f39aa7306a400a758510561948015ab0620ac329022b9a08415865200578c0082b0ca4088f4874c5619480117f08b8cc12900a2f21171982520447c43a60b04a4008dd8799363548015b501326c6a9002b660264d8d520046fc3ac9b1aa4a8a5c8655363549774bd0a3a6c6a92a29761474d8d5254567410e9b1aa400acd821d36354801c3ea92a6c6a929697a1772d8d520046f43e85b1aa4008dd87d0b635491d4bd0bb8ec6a92a29761771d8d521952f42ce3b1aa400a5d859c7635480153f08b8ec6a9002a721171d8d520046f43883b1aa4008dd8710763548014bd0a20ec6a90029761441d8d525456741083b1aa400acd8210763548015b50020ec6a9002b660041d8d520054f424e1b1aa400a9d849c363548014bf0ab86c6a90ca9721570d8d523052f428e1b1aa4a8a5d851c363548014bd0ba06c6a90029761740d8d520046f43881b1aa4008dd871036354951c9ecbb1ea4a92cb175d463d855221c3ec3ea9b0aa402c3e74d5361548870fb0fa9ec2a9007171cd53d85520046f43ec6b0aa400c9f74d8d6154801938e9b1ac2a900237a1c63585520064fba0c6b0aa400c9c7418d61548019b6c7b82c2a90033618f70585520066db18e0b0aa400cd8631c161548011ef0eb08c2a900a3ee1d40d81520265c302e9302a400c9e74d8e605480193ae9b1cc0a9003279d063981520064eba0c7302a400cb974d8260548031bd0db9ac0a92a23721b73581520046f43ec6b02a4008de8718d60549658baea318c0a90023ee1d60181520161f3a6a8302a401c5e73d4c605480117f08b88c0a900a2f21171181520071daa280302a4baa3f855cd64148314790ab9ac82906387d4e53590520c51f42ce2b20a495a3d859c5641483147d0a38ac8290c28f61471590520054f418e2b20a400a9d831c5641481155d0438ac8290c2ab60871590520055d400e2b20a400ab9801c5641480117d0f98ac8290022f61f31590520c51f42c62b20a400a3d858c5641481155d0518ac829002ab60a31590520c51f42862b20a400a3d850c5641483147d0bb82c8290c28f61770590523fd1fc2ae0b20a418a3
  | 16 => 0x71609a543200e82750b84ee0000077903411037b2268fe0bf25b321613fd04807222ba0208cc7473b6890c36056d21205e492a00024b10188947123f694280ba000000000031e5a600000007cc1241a999cc07a81444a800000000004c1acc220000306002005806000c03c0040000000e400401000000804401c0001d409400c00002c12003002800401003400002800c01800402c0140480f400003801808c00c00400802c03801400c03000800400802004400005c01000c00000001800000000800406800c03401000003000000001400c02c02000001400401c00c0000141280b800404401402401000000407400407000800003402800001c00402401800800800004800804400006400401002801404000000000001c0140000080a400400000001c01c02c0000000540740000d80000000ac01c01014c06807c00400800802c00000000800001c0c802000800c00008400006002002000001c00c00800c00c04404809c00c00002c0c400c00000c00000c00000400400404003c00005400404000002000403002800800400401000003002c00000003409c00004800001002400800c04c01801c00c01800401c0780a403800c06403c0000140040dc10801c00001c02000c03402001c00806000002403800403c00000400c09801000c02c00400c01405c0481440000000080d001c00800002c00802000001000400c0000000e401403801c0040000a40500d001404c07401401005000000403403400000400c25c0a000000004404c00000006800c03800808000800000801400001801000007401001c00401400402801807000800000c02001407804c00005400808807400800c00001c01c03c00c03000000403401401404801402400008c09403802402003800801400803000004003c02403403c03c00000003000c0000340240580041a000800002c00000c00001800005c01400000400c00c00405406800007400000801802406001805400815001005400c0040080140000300080140100a401402800c0040200000f404800002800c00800800c04c02c02400c00000401000c02800800400000000c00400401803402803c00000009000001801000800000401802804000c00400000416000001800408c03c00c01404000c00000007000403817c00400401c00c0a004805400400005800c00c00402000c00000802800002801c03801c01400401800800804c03400002000000400000000003400002001c00005405800004001002001402c00404004c08402c02405400c0000100040900000440000240080a800c02402c02802003400c0980000040180300080a403008002803c03401401000c04000401800c00000409805402800000400c03000800400400c00001800001400802800403800401004401010804001401c030120
  | 17 => 0xe858674c25f0090dae2982c406740547073540ae8820000395864cab400015504d0d94373019000000028a09c194cf220000e8800074e5af0221a5800043119188c40000001559ac82742bd000211811a5712fc0000ac6097057a068bba7600000000de80002029fd020071f37d0e54cca2b21a604bc16c61623d09882662fc2d100000007c53b18000e261083ff9470de206e26821e8fc41fe0d68bacab230924900f867678637c004055800531183486105c5280809895c23544117643907da0d5197103e2d0000208099c2661c91e00a5432f23b9af40003490fd07e02880ad01406f40000fb19500009f243711e901ca425de0e39e986780001701a7510000000016e00006611ef01b000015503d8000e7043843c0e580001a137a8a88dce63f43d91f07fc5172b78e10a8e3e5323811cbf47810b21fece9c2c03ec0f7c1545893059828d3c36240c85ec79c46c1e487f4c1a5fe3cf1f9413652929e0bc486a42e03594c8c904fa3df17480527ad14489c0bd87e305e1f6cefa1b62b20fb890c81b3d49cc85a443a0760a745968520b98540da22871c5808c69466d1098118b184c31d0111452c3463d098a40e22190f005b8fea46b35f8518b1e5ee3d51e4ca5678f10e993c7ae7511f60b4c7d61981d780002e41e900010e49fc7370e180f059a5e10418cd026c5ca252a18d0c42b810412744505842ea02e4b6a00000196681aa6b636da1090b437d2c58cdc7382ca3d58074d4073d11913e07945cd00010fd0aa6f90c71e140006cb16d800015014105a137c1463d31bb2094ae443b17700006f2000273908103a0fc446952ce4c00005995dc94400016290bc3080c20ba9d588dc385207056cd4e7711230be075c1dc4409ca8ac074d1ac800042a4172f906a0f583052fa8da06b800012900003666c438f00009a431f00018500006801e321d800022f0001c54b1400028a81fc0ec57526b8000b902bb0be04c81127d9384865c760000000000067c3da0cf8d8c0ee58e3e483d0fde7161c78d084960004418e903d456a0330514c881813b081e484e55f0002084c2a714000166456076526d85f400014a0000000dc800000010506901b702f0000df60003d8a0fc0001c03111fe4960000000199818c14e32b89f4a507530e584650e055d1f417c04242bf43b9bac59234b000124c0001470001c2c00000422e0000cba8392b10b5c91c3e23ac9dd400057000000003c2000000215000012d3818fa838c4b53a400000005a8000000000067620595fd07a0001821edc6322410dc8950cac03b3aa00950e806a054800072e55c00013d0cea3f10d20a0000058700e1c883de0e54130bdc28481500000002e82a50001b2431488b0001e889204191d9000000000016700fc42c10200000000004543cf8ee42427ca20e175c5f470d0ae00003625b
  | 18 => 0x8e0d10e50e48186029954864825641b9da0928000000000000057c20f86705d843635d04fc2623a80501a188240da15220f811c6d302a037c0ae48928c210ccaa0092d719c90de5820399ba00005980f900000000000001d184dc5a52f014781ea00042d8d000008480000f7062a26d159a1c4f324691e9077c00000000015246420002e2022c7346410159fe031a7e0378000000010e22700003065390001d9822200000000005060000000c2800020e00016b400011710100001000003bb89a8b924f61870ba4000374000042c000000000171904e000116880c4d600000003282cc0db2468000aa00003c904f40002a302d1a445e04092f10db81c084a2a1970ca824c839f08cc0000002b982f424c1ed12e9d60d8450601618383942930658fd501a00013d92088e8586405077501e81828792f42bc79d06687a08f2118380147c00070e29a0fec0003813de88142ca0000001b489a62512f89808fa858006c01f00002e31f9896042800009c993444439d0571fa0a0671d23f14640006260001b186fc4812db133c2087d508480000000000000b58d2000039e00000003330001c9c408000310932c000000000165c9680003138ad902c209000174c03c6bc1e5990c2a229f44797cc90e16c00d9d0c24e5cf1c8120c3287fa3a087f01f03010fb80004800e92b30f3021e83522d853c26a0081981104a76307163046c8f652410f9c68fa000e3680000ffc3174031a70b426683d2844c5fe5480c41dfc97865b1501cd4a5c3601d50d542444cc1891d010b024f36094149da3772fb9980ab611d303167c77e6df14a1dc80d212b04d074c9ac75d14c84309d623601ca0c4d1c6ad11398ac98c2781d88bd85ce6ec0ef0bd061e3613da0d506365df20996b09545833160264a741960580fe834e2a90bf0064fd46240d60ecc0002e40dd9094e6c2812b29ac4f820ea1ff87607040310d18c940005ce179050cd6e000000056825c40227e8000000161000000000051b2e590546b465915a03fc0000000278d40b761f10688678d8088e3940bb46ac8283560dc08ac4af052055c4de0940139b34b9803a00004c0f6c0000001f84000000298929c0000000001bb8f300002b381540003a51af8180cf224e14d9e5497e6ff1af12648782dc00000dc7da6773f98a78d4c0001fe14e00002550b580000000000000000da82a7000000000016d0e20000d1000007880000007c63290db0000500000149c2280000000000000000000000024042b3c181244c67a41129f98ec826c2fb09688440002a2928510a2c20b399bc51c273265010c3aa0f71251db0c26000408019400086e1e4000000021c20410843c456b30f8000000000000176ca6e7f62fe8388000000148088c1ba85c11e1268d7200031f08fd0d428641a0000802745266833081884b0b01c
  | 19 => 0xb94000177188939435e230000097c00001a0001a08cd40000d4930086663525c80001f200000000004fe05211a000041a5bd06284581d622b4289758f346ae3f4918c8da41e1328390fdc4c910785a450866b4160d10c6e00024602e88bc50c3ae20c0b800000a58eac45c0850000000f361d70d7181034040a00000000007dd2779c445fc45f2dd0000718327085074800000032505509e264e41d1a28fee6090000b5079e000000000006600040b80003c6000003103c52e72c300803036a3a626a00481fa4f71fb0e20a0e1be32f1b94ed44604039f7c09813e00000008ea0000b18d1c4c03642c0a11400053f22c803c00067f0001534f7454020200007e82a1382029cd3e7f13cb16c46620002ee1aece964f22eaa19023e5c228406f0c3c2072119f486444b243f0768fac5a91249a1c25027c3851e28f04585056186ca08239409935482c08c01a95e10ea1cd2931e307700c3355073c52a2291de09a094c20026d1d2428081c17313701a055e07320bcdec0cf2390c7843009626c12e8ce085606497accd80013229560d288443679658d861f505f1cb450a3cd1a6896403e5b419e93890525690591b58c660a503f127045876222581a0a340f636385bc4ec31413486c8e76187208983c8840703e60da449a7af35a83b80a05161baa100a4481e11213c01b84ab4021c20ce25b018603c091e389270813871a1e41868000fce5e51c39d08f8044400018a8edc1521f18c4c69e33511d1d54ece7943ee00003e815830d1f44e042c72df079476a0000001438a125420000ed0f3823737796e4b265ff0bf801cf7e86b10890008e02df432804500463d13d1260000318010017c08207a083942c0000000e602c48867ce0000c087b0452025861441406237e8be47744ac1eb18009887de1c98c688547f038ca1e4ef00003f61100af64b60000a680000f21900ba80006e326280011104a30001f1d0da1ce362969c89008a1e1976087a1ff2f78fdcb4869729f11447c22792a99b783044f50e817403843c013a0cfd0fe2202811894c406d51d08ff48e222139c92283f602f2299448908860000000000075a053018400000034196a85248570098000f7818902000002348411cc9d403e60c014118b8d1e00019b21c800032b33200b80006d80001ba88de67e0dd1f100006e92ab0bcc9662771569da42e077427318c10fa63606981d0c50465448048c8fa33840497910cc0670da14b09b219b08e1374188084138838c7a833900007c0ff800015700000002c834480000006fe3ab971cf0e68d2a6192ccb068b34911308b05bf3710cb478e0151461b30a8c82e3409c1901c07d00000b4c840860ca813401a6e63c68b64a402421a280000000000dc08306ae10337000009d267c342800064c77e0001c80cc663403a9378a6674a3e595100003
  | 20 => 0x6842540e180001683929dd8ce88320f39ea0700093079a2447a015318199f40004a905087045de0e1000000057c7b80f585206f853642c8c0000000042391d800063229a9c5c0a252f19d0f741da5112f49188d7c5ab3578dacc7853002c89904c242939f80084202da13f0e44c206ce27018ecd463321948f8073c44f04e12907de2f541585e004425b0250abcd5662f00c0338f2051012e02fc97635d1d69190b3c61d12282e051a25336e1a60d5200023f970487c6080000ef4ef225e2a5224c86000022e90d015676b2ca138d1283f215315e40007b942485888c25e71b7a1f0c7456e122219c3b617a02d8000bb41ee04090a0e9e18022481e00000002398f90cb415d1a91a94ac20b500008a80005a000004a4b781a5092841822a3e937087242e200000013b073e0000c60000d342d100006444160d60ab0d048ce42d16c180cc380424019a6c7f20c81db22100902911c5100c00000037e0000e020003f59de80602fd4270000c72000000000000019a00008680000003260a2c8b400038d914010e7231a880010025550411f2049820138293f08343060489b2000078900007b0a9e0d400008787367880001ca406849744619a4000000000000000000011308ec29a7a330c1c405ba0a20001df0a7a36a3089c303a866707386486167b30809f5c3565b204f016098e3a92aa03f80144680639f0c83000012400840005e82c81ff48aa5f4223079893617629680001ae3db0000a7102249f1b8800109e83633c21308f01f609e02ec9e678b00002485bc4880001244ba200018ea1780000001db80d8d706b40000000ea48330fc8eec00038301c149502406d2f195d8ca846a27721a033262d1d1019090a267323181442e7b214415a0b38822096018c9842b71e0817051e2c4337165440c0003b79e5c93c4a02d189d4b240de1281634e382b920d955c31641d0379f3d0ba3a300a1ccc1f480c12b85246f06f72a8a0009d08890001c84ae886c1f38aa100a78e0000000d3288600000006386071d613447e00002bd0000784000000166ca286da27d8274f4e5fc3dd80000000000001b64ee675e4118f44a9c0000000001070000166221c0007e409500007b24b104aa0b509a00006c9f4c69c6492ce84ec00080b44518c491621b1b280006da35b1589644ca264008f0af0e620161df0d6059e2723e69cc00007a02238b88e5e1a62bf023c5f63d500000000000003d81a846583102f520f026e77b26097ec00043202b0d98d261bf3e1002ceb60c116a8c580003282f6800002e4e40000f140000000eb0000afa65f0001ac10c285030c80002d40001a198e0000000000000000000000010980006f31238dfd12450d3460d9ce304b838780002b27443521cb90be00000000000007ae3af9cd0de40b70af8000ad867b4298
  | 21 => 0x61700020ecdba7b5434800013e873415194047c3c42568e6056a00033d000021a1050001a88dda480022998838a32e000184829837a0000000a260000000dc80001d908912dc0000001741798fe451d11c0000000000048148cf08
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x1aa02cc30308941ca010027008000417e61731cd65c840103f985d074596210050e650521c1654840145993144705952100607e1a635d0529400181f869917314650006866118018f654800103f985d074d9520006866118018c6548001c44751cd61480200068660d80193654400105f985cc73d95100068660d801906544001c24751d16244010
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x4
  | 2 => 0x5
  | 3 => 0x2
  | 4 => 0x1
  | 5 => 0x4c
  | 6 => 0x4d
  | 7 => 0x124c
  | 8 => 0x3
  | 9 => 0x94c
  | 10 => 0x94d
  | 11 => 0x124d
  | 12 => 0x138c
  | 13 => 0x138d
  | 14 => 0x8c
  | 15 => 0x8d
  | 16 => 0x128c
  | 17 => 0x98c
  | 18 => 0x98d
  | 19 => 0x128d
  | 20 => 0x150c
  | 21 => 0x150d
  | 22 => 0x14c
  | 23 => 0x14d
  | 24 => 0x6
  | 25 => 0x134c
  | 26 => 0x198c
  | 27 => 0xa4c
  | 28 => 0xa4d
  | 29 => 0x134d
  | 30 => 0x198d
  | 31 => 0x20c
  | 32 => 0x20d
  | 33 => 0xb0c
  | 34 => 0xb0d
  | 35 => 0x140c
  | 36 => 0x140d
  | 37 => 0x154c
  | 38 => 0x154d
  | 39 => 0x2cc
  | 40 => 0x2cd
  | 41 => 0x19cc
  | 42 => 0xbcc
  | 43 => 0xbcd
  | 44 => 0x14cc
  | 45 => 0x14cd
  | 46 => 0x19cd
  | 47 => 0x44c
  | 48 => 0x44d
  | 49 => 0x1a0c
  | 50 => 0xd4c
  | 51 => 0xd4d
  | 52 => 0x164c
  | 53 => 0x164d
  | 54 => 0x1a0d
  | 55 => 0x94055
  | 56 => 0x124955
  | 57 => 0xb0955
  | 58 => 0xb0954
  | 59 => 0x140955
  | 60 => 0x94b14
  | 61 => 0x140954
  | 62 => 0x130a
  | 63 => 0x14a
  | 64 => 0x134a
  | 65 => 0xb1395
  | 66 => 0xb1394
  | 67 => 0xd4a
  | 68 => 0x1a0a
  | 69 => 0x98094
  | 70 => 0x128994
  | 71 => 0xb0994
  | 72 => 0xb0995
  | 73 => 0x98b14
  | 74 => 0x154994
  | 75 => 0x154995
  | 76 => 0x12cb
  | 77 => 0x14b
  | 78 => 0x134b
  | 79 => 0xb1514
  | 80 => 0xb1515
  | 81 => 0xbcb
  | 82 => 0x19cb
  | 83 => 0x14a54
  | 84 => 0x14a55
  | 85 => 0x134154
  | 86 => 0x134155
  | 87 => 0x15994
  | 88 => 0x15995
  | 89 => 0x142d4
  | 90 => 0x142d5
  | 91 => 0xbd994
  | 92 => 0x154d4
  | 93 => 0x154d5
  | 94 => 0x14454
  | 95 => 0x14455
  | 96 => 0xd5994
  | 97 => 0x15654
  | 98 => 0x15655
  | 99 => 0x134a54
  | 100 => 0x134a55
  | 101 => 0xa59d4
  | 102 => 0xbca54
  | 103 => 0xbca55
  | 104 => 0xa4bd4
  | 105 => 0x19ca54
  | 106 => 0x19ca55
  | 107 => 0xa5a14
  | 108 => 0xd4a54
  | 109 => 0xd4a55
  | 110 => 0xa4d54
  | 111 => 0x1a0a54
  | 112 => 0x1a0a55
  | 113 => 0x199354
  | 114 => 0x199355
  | 115 => 0x135994
  | 116 => 0x135995
  | 117 => 0x2d354
  | 118 => 0x1342d4
  | 119 => 0x2d355
  | 120 => 0x1342d5
  | 121 => 0x14d354
  | 122 => 0x1354d4
  | 123 => 0x14d355
  | 124 => 0x1354d5
  | 125 => 0x45354
  | 126 => 0x134454
  | 127 => 0x45355
  | 128 => 0x134455
  | 129 => 0x165354
  | 130 => 0x135654
  | 131 => 0x165355
  | 132 => 0x135655
  | 133 => 0xbd995
  | 134 => 0x19d994
  | 135 => 0x19d995
  | 136 => 0xd5995
  | 137 => 0x1a1994
  | 138 => 0x1a1995
  | 139 => 0xb4b
  | 140 => 0xd0a
  | 141 => 0xbc2d5
  | 142 => 0xd42d4
  | 143 => 0xd42d5
  | 144 => 0x1a02d4
  | 145 => 0x1a02d5
  | 146 => 0x19cbd4
  | 147 => 0x19cbd5
  | 148 => 0xbc454
  | 149 => 0x44bd5
  | 150 => 0xbc455
  | 151 => 0xbd654
  | 152 => 0x164bd5
  | 153 => 0xbd655
  | 154 => 0x1a8a
  | 155 => 0x19d4d4
  | 156 => 0x19d4d5
  | 157 => 0xd54d4
  | 158 => 0xd54d5
  | 159 => 0x1a14d4
  | 160 => 0x1a14d5
  | 161 => 0x19c454
  | 162 => 0x19c455
  | 163 => 0x19d654
  | 164 => 0x19d655
  | 165 => 0xd4454
  | 166 => 0x1a0d54
  | 167 => 0x1a0d55
  | 168 => 0x1a4b
  | 169 => 0x1a1654
  | 170 => 0x1a1655
  | 171 => 0x5555
  | 172 => 0x4b55
  | 173 => 0x59d5
  | 174 => 0x9414
  | 175 => 0x8d14
  | 176 => 0x9a14
  | 177 => 0x74a
  | 178 => 0x5cb
  | 179 => 0x135a94
  | 180 => 0x135a55
  | 181 => 0x141554
  | 182 => 0x155415
  | 183 => 0x2cd54
  | 184 => 0x2d954
  | 185 => 0xbda55
  | 186 => 0x457d5
  | 187 => 0xd5a94
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 2076
  | 6 => 5376
  | 5 => 2198
  | 4 => 14
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
  | 8 => packedAt gbK8 (1700+((h/20+packedAt gbK8 (1560+(h % 20)*7) 7) % 88)*7) 7
  | 7 => packedAt gbK7 (85116+((h/692+packedAt gbK7 (76812+(h % 692)*12) 12) % 2492)*13) 13
  | 6 => packedAt gbK6 (281344+((h/1792+packedAt gbK6 (258048+(h % 1792)*13) 13) % 6452)*14) 14
  | 5 => packedAt gbK5 (138466+((h/732+packedAt gbK5 (129682+(h % 732)*12) 12) % 2638)*13) 13
  | 4 => packedAt gbK4 (1000+((h/4+packedAt gbK4 (980+(h % 4)*5) 5) % 19)*5) 5
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x3fe1e0781c3fe01c3c03fffff0d38f1f21c27f
  | 1 => 0xc3fe007fffc1ffffc003fc07f32c48e63e7c73
  | 2 => 0xfc3fff801ffe001ffffc1ff80c3070f9c78f9c
  | 3 => 0x3fffffe000001fffffe0000fc07f01f80fe0
  | 4 => 0x3fffffffffffe0000000000fff8001fff000
  | 5 => 0xffc0000000000000000000000ffffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x460642908132108241125634041830b20c225
  | 1 => 0x42860012244048d6402a4814a10448640a1c52
  | 2 => 0xa80a888016a4024489481290243010b0470498
  | 3 => 0x235355f4011049b32b38020cbc06d01b80b60
  | 4 => 0x2039de659b39970020c100c10efa8001f5e000
  | 5 => 0x3300180602201802030203060fbf7ede000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeefae8fcecf8a8feeefae8fcecf8a8feeefae8fcecf8a8feeefae8fcecf8a8feeefae8fcecf8a8feeefae8fcecf8a8feeefae8fcecf8a8feeefae8fcecf8a8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_16905
namespace PEqualNP.Outside.L_meta_16905
open PEqualNP.Outside.L_meta_16905.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_3_0 : Interval s1Atlas 3 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 4 := bs1_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 12 := bs1_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_5_0 : Interval s1Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_5 : Interval s1Atlas 5 0 1 := bs1_5_0
theorem alls1 : ∀ k ≤ 5, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 4 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 12 := block_range (n:=12) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 12 := bs2_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 1 := bs2_5_0
theorem alls2 : ∀ k ≤ 5, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_0 : Interval s3Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 4 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 25 := bs3_3_0
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
theorem bs3_4_160 : Interval s3Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_192 : Interval s3Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_224 : Interval s3Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_256 : Interval s3Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_288 : Interval s3Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_320 : Interval s3Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_352 : Interval s3Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_384 : Interval s3Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_416 : Interval s3Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_448 : Interval s3Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_480 : Interval s3Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_512 : Interval s3Atlas 4 512 27 := block_range (n:=27) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 539 := (concat (concat (concat (concat bs3_4_0 bs3_4_32) (concat bs3_4_64 bs3_4_96)) (concat (concat bs3_4_128 bs3_4_160) (concat bs3_4_192 bs3_4_224))) (concat (concat (concat bs3_4_256 bs3_4_288) (concat bs3_4_320 bs3_4_352)) (concat (concat bs3_4_384 bs3_4_416) (concat bs3_4_448 (concat bs3_4_480 bs3_4_512)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_64 : Interval s3Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_96 : Interval s3Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_128 : Interval s3Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_160 : Interval s3Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_192 : Interval s3Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_224 : Interval s3Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_256 : Interval s3Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_288 : Interval s3Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_320 : Interval s3Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_352 : Interval s3Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_384 : Interval s3Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_416 : Interval s3Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_448 : Interval s3Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_480 : Interval s3Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_512 : Interval s3Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_544 : Interval s3Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_576 : Interval s3Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_608 : Interval s3Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_640 : Interval s3Atlas 5 640 24 := block_range (n:=24) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 664 := (concat (concat (concat (concat bs3_5_0 bs3_5_32) (concat bs3_5_64 (concat bs3_5_96 bs3_5_128))) (concat (concat bs3_5_160 bs3_5_192) (concat bs3_5_224 (concat bs3_5_256 bs3_5_288)))) (concat (concat (concat bs3_5_320 bs3_5_352) (concat bs3_5_384 (concat bs3_5_416 bs3_5_448))) (concat (concat bs3_5_480 (concat bs3_5_512 bs3_5_544)) (concat bs3_5_576 (concat bs3_5_608 bs3_5_640)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_32 : Interval s3Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 40 := (concat bs3_6_0 bs3_6_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_7_0 : Interval s3Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_7 : Interval s3Atlas 7 0 1 := bs3_7_0
theorem alls3 : ∀ k ≤ 7, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_2 i (by omega) hi
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
  · exact alls3_6 i (by omega) hi
  · exact alls3_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_0 : Interval s4Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 4 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 25 := block_range (n:=25) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 25 := bs4_3_0
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
theorem bs4_4_512 : Interval s4Atlas 4 512 27 := block_range (n:=27) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 539 := (concat (concat (concat (concat bs4_4_0 bs4_4_32) (concat bs4_4_64 bs4_4_96)) (concat (concat bs4_4_128 bs4_4_160) (concat bs4_4_192 bs4_4_224))) (concat (concat (concat bs4_4_256 bs4_4_288) (concat bs4_4_320 bs4_4_352)) (concat (concat bs4_4_384 bs4_4_416) (concat bs4_4_448 (concat bs4_4_480 bs4_4_512)))))
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
theorem bs4_5_640 : Interval s4Atlas 5 640 24 := block_range (n:=24) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 664 := (concat (concat (concat (concat bs4_5_0 bs4_5_32) (concat bs4_5_64 (concat bs4_5_96 bs4_5_128))) (concat (concat bs4_5_160 bs4_5_192) (concat bs4_5_224 (concat bs4_5_256 bs4_5_288)))) (concat (concat (concat bs4_5_320 bs4_5_352) (concat bs4_5_384 (concat bs4_5_416 bs4_5_448))) (concat (concat bs4_5_480 (concat bs4_5_512 bs4_5_544)) (concat bs4_5_576 (concat bs4_5_608 bs4_5_640)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_32 : Interval s4Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 40 := (concat bs4_6_0 bs4_6_32)
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
theorem bs5_4_0 : Interval s5Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 1 := bs5_4_0
theorem alls5 : ∀ k ≤ 4, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 14 := block_range (n:=14) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 14 := bgb_4_0
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
theorem bgb_5_2176 : Interval gbAtlas 5 2176 22 := block_range (n:=22) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2198 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 bgb_5_224))) (concat (concat (concat bgb_5_256 bgb_5_288) (concat bgb_5_320 bgb_5_352)) (concat (concat bgb_5_384 bgb_5_416) (concat bgb_5_448 (concat bgb_5_480 bgb_5_512))))) (concat (concat (concat (concat bgb_5_544 bgb_5_576) (concat bgb_5_608 bgb_5_640)) (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 bgb_5_768))) (concat (concat (concat bgb_5_800 bgb_5_832) (concat bgb_5_864 bgb_5_896)) (concat (concat bgb_5_928 bgb_5_960) (concat bgb_5_992 (concat bgb_5_1024 bgb_5_1056)))))) (concat (concat (concat (concat (concat bgb_5_1088 bgb_5_1120) (concat bgb_5_1152 bgb_5_1184)) (concat (concat bgb_5_1216 bgb_5_1248) (concat bgb_5_1280 bgb_5_1312))) (concat (concat (concat bgb_5_1344 bgb_5_1376) (concat bgb_5_1408 bgb_5_1440)) (concat (concat bgb_5_1472 bgb_5_1504) (concat bgb_5_1536 (concat bgb_5_1568 bgb_5_1600))))) (concat (concat (concat (concat bgb_5_1632 bgb_5_1664) (concat bgb_5_1696 bgb_5_1728)) (concat (concat bgb_5_1760 bgb_5_1792) (concat bgb_5_1824 (concat bgb_5_1856 bgb_5_1888)))) (concat (concat (concat bgb_5_1920 bgb_5_1952) (concat bgb_5_1984 bgb_5_2016)) (concat (concat bgb_5_2048 bgb_5_2080) (concat bgb_5_2112 (concat bgb_5_2144 bgb_5_2176)))))))
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
theorem allgb_6 : Interval gbAtlas 6 0 5376 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 bgb_6_192) (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)))) (concat (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 (concat bgb_6_416 bgb_6_448))) (concat (concat bgb_6_480 (concat bgb_6_512 bgb_6_544)) (concat bgb_6_576 (concat bgb_6_608 bgb_6_640))))) (concat (concat (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 (concat bgb_6_768 bgb_6_800))) (concat (concat bgb_6_832 bgb_6_864) (concat bgb_6_896 (concat bgb_6_928 bgb_6_960)))) (concat (concat (concat bgb_6_992 bgb_6_1024) (concat bgb_6_1056 (concat bgb_6_1088 bgb_6_1120))) (concat (concat bgb_6_1152 (concat bgb_6_1184 bgb_6_1216)) (concat bgb_6_1248 (concat bgb_6_1280 bgb_6_1312)))))) (concat (concat (concat (concat (concat bgb_6_1344 bgb_6_1376) (concat bgb_6_1408 (concat bgb_6_1440 bgb_6_1472))) (concat (concat bgb_6_1504 bgb_6_1536) (concat bgb_6_1568 (concat bgb_6_1600 bgb_6_1632)))) (concat (concat (concat bgb_6_1664 bgb_6_1696) (concat bgb_6_1728 (concat bgb_6_1760 bgb_6_1792))) (concat (concat bgb_6_1824 (concat bgb_6_1856 bgb_6_1888)) (concat bgb_6_1920 (concat bgb_6_1952 bgb_6_1984))))) (concat (concat (concat (concat bgb_6_2016 bgb_6_2048) (concat bgb_6_2080 (concat bgb_6_2112 bgb_6_2144))) (concat (concat bgb_6_2176 bgb_6_2208) (concat bgb_6_2240 (concat bgb_6_2272 bgb_6_2304)))) (concat (concat (concat bgb_6_2336 bgb_6_2368) (concat bgb_6_2400 (concat bgb_6_2432 bgb_6_2464))) (concat (concat bgb_6_2496 (concat bgb_6_2528 bgb_6_2560)) (concat bgb_6_2592 (concat bgb_6_2624 bgb_6_2656))))))) (concat (concat (concat (concat (concat (concat bgb_6_2688 bgb_6_2720) (concat bgb_6_2752 (concat bgb_6_2784 bgb_6_2816))) (concat (concat bgb_6_2848 bgb_6_2880) (concat bgb_6_2912 (concat bgb_6_2944 bgb_6_2976)))) (concat (concat (concat bgb_6_3008 bgb_6_3040) (concat bgb_6_3072 (concat bgb_6_3104 bgb_6_3136))) (concat (concat bgb_6_3168 (concat bgb_6_3200 bgb_6_3232)) (concat bgb_6_3264 (concat bgb_6_3296 bgb_6_3328))))) (concat (concat (concat (concat bgb_6_3360 bgb_6_3392) (concat bgb_6_3424 (concat bgb_6_3456 bgb_6_3488))) (concat (concat bgb_6_3520 bgb_6_3552) (concat bgb_6_3584 (concat bgb_6_3616 bgb_6_3648)))) (concat (concat (concat bgb_6_3680 bgb_6_3712) (concat bgb_6_3744 (concat bgb_6_3776 bgb_6_3808))) (concat (concat bgb_6_3840 (concat bgb_6_3872 bgb_6_3904)) (concat bgb_6_3936 (concat bgb_6_3968 bgb_6_4000)))))) (concat (concat (concat (concat (concat bgb_6_4032 bgb_6_4064) (concat bgb_6_4096 (concat bgb_6_4128 bgb_6_4160))) (concat (concat bgb_6_4192 bgb_6_4224) (concat bgb_6_4256 (concat bgb_6_4288 bgb_6_4320)))) (concat (concat (concat bgb_6_4352 bgb_6_4384) (concat bgb_6_4416 (concat bgb_6_4448 bgb_6_4480))) (concat (concat bgb_6_4512 (concat bgb_6_4544 bgb_6_4576)) (concat bgb_6_4608 (concat bgb_6_4640 bgb_6_4672))))) (concat (concat (concat (concat bgb_6_4704 bgb_6_4736) (concat bgb_6_4768 (concat bgb_6_4800 bgb_6_4832))) (concat (concat bgb_6_4864 bgb_6_4896) (concat bgb_6_4928 (concat bgb_6_4960 bgb_6_4992)))) (concat (concat (concat bgb_6_5024 bgb_6_5056) (concat bgb_6_5088 (concat bgb_6_5120 bgb_6_5152))) (concat (concat bgb_6_5184 (concat bgb_6_5216 bgb_6_5248)) (concat bgb_6_5280 (concat bgb_6_5312 bgb_6_5344))))))))
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
theorem bgb_7_2048 : Interval gbAtlas 7 2048 28 := block_range (n:=28) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2076 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 bgb_7_224))) (concat (concat (concat bgb_7_256 bgb_7_288) (concat bgb_7_320 bgb_7_352)) (concat (concat bgb_7_384 bgb_7_416) (concat bgb_7_448 bgb_7_480)))) (concat (concat (concat (concat bgb_7_512 bgb_7_544) (concat bgb_7_576 bgb_7_608)) (concat (concat bgb_7_640 bgb_7_672) (concat bgb_7_704 bgb_7_736))) (concat (concat (concat bgb_7_768 bgb_7_800) (concat bgb_7_832 bgb_7_864)) (concat (concat bgb_7_896 bgb_7_928) (concat bgb_7_960 bgb_7_992))))) (concat (concat (concat (concat (concat bgb_7_1024 bgb_7_1056) (concat bgb_7_1088 bgb_7_1120)) (concat (concat bgb_7_1152 bgb_7_1184) (concat bgb_7_1216 bgb_7_1248))) (concat (concat (concat bgb_7_1280 bgb_7_1312) (concat bgb_7_1344 bgb_7_1376)) (concat (concat bgb_7_1408 bgb_7_1440) (concat bgb_7_1472 bgb_7_1504)))) (concat (concat (concat (concat bgb_7_1536 bgb_7_1568) (concat bgb_7_1600 bgb_7_1632)) (concat (concat bgb_7_1664 bgb_7_1696) (concat bgb_7_1728 bgb_7_1760))) (concat (concat (concat bgb_7_1792 bgb_7_1824) (concat bgb_7_1856 bgb_7_1888)) (concat (concat bgb_7_1920 bgb_7_1952) (concat bgb_7_1984 (concat bgb_7_2016 bgb_7_2048)))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 28 := block_range (n:=28) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 60 := (concat bgb_8_0 bgb_8_32)
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 5 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 16, 18),(inputs.getD 2 zero, 8, 12),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 33, 49),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 33, 41),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 8 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 8 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 5 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 2, 18)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 2, 18),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefae8fcecf8a8feeefae8fcecf8a8feeefae8fcecf8a8feeefae8fcecf8a8feeefae8fcecf8a8feeefae8fcecf8a8feeefae8fcecf8a8feeefae8fcecf8a8
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277074664 * 2 ^ 32 + 4243388584) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_16905.Model.Repr at out
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

def mono : List Gate := [⟨.and,[2,3]⟩,⟨.and,[2,5]⟩,⟨.or,[1,2]⟩,⟨.or,[4,7]⟩,⟨.or,[0,6]⟩,⟨.or,[3,4]⟩,⟨.and,[1,9]⟩,⟨.and,[5,11]⟩,⟨.or,[8,13]⟩,⟨.and,[10,14]⟩,⟨.or,[12,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074664 * 2 ^ 32 + 4243388584) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074664 * 2 ^ 32 + 4243388584) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_16905

open PEqualNP.Outside.L_meta_16905 in
theorem PEqualNP.Outside.L_meta_16905 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074664 * 2 ^ 32 + 4243388584) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074664 * 2 ^ 32 + 4243388584) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
