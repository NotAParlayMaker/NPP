import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_12917.Model
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


end PEqualNP.Outside.L_meta_12917.Model

namespace PEqualNP.Outside.L_meta_12917
open PEqualNP.Outside.L_meta_12917.Model
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

end PEqualNP.Outside.L_meta_12917

namespace PEqualNP.Outside.L_meta_12917
open PEqualNP.Outside.L_meta_12917.Model
def gbK8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x28800361541a125138730989203290023180001e008400000089832e1149f1620a8000580003834e8000888801e187014a00004e0020840420c244bff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x41ff20083de40107f88020fd10041fd20083da40107e48020ffaa6217f54c43fca9885f95310df2a6213e54c43faa9885f55310deaa6213d54c43f8a9885f15310ffa9e217f53c43fca7885f94f10fea9e217d53c43f8a7885f14f10ffa1e21fe43c43fa87887f10f10ffa96217f52c43fca5885f94b10fea96217d52c43f8a5885f14b10ffa1621fe42c43fa85887f10b10ff99621fe32c43fa65887f0cb10ffa0e21bf41c43fc83887d90710fea0e21bd41c43ea83886d50710fe20e21ff31c43fc63887f4c710fe18e21ff21c43fc43887f48710fe10e21ff40c43fc81887f50310fe20621ff30c43fc61887f4c310fe18621ff20c43fc41887f48310fe10621ff54842fea9087f95210bf2a421fd54842faa9087f15210be2a421ff53842fea7087f94e10bf29c21fd53842faa7087f14e10be29c21ff43843fc87087f50e10fe21c21ff52842fea5087f94a10bf29421fd52842faa5087f14a10be29421ff42843fc85087f50a10fe21421ff32843fc65087f4ca10fe194217d51843fe83086fd0610ff20c21fd418437a83087f10610ff98c21fe31843fa63087f0c610ff90c21fe21843fa43087f08610bf28421ff40843fc81087f50210fe20421ff30843fc61087e8c210fe98421f930843f861087fc8210ff10421fa20843fa41087e48210fe10421ff10843ee21087ec4210ffaa2217f54443fca8885f95110feaa2217d54443f8a8885f15110ffa9a217f53443fca6885f94d10fea9a217d53443f8a6885f14d10ffa1a21fe43443fa86887f10d10ffa92217f52443fca4885f94910fea92217d52443f8a4885f14910ffa1221fe42443fa84887f10910ff99221fe32443fa64887f0c910ffa0a21bf41443fc82887d90510fea0a21bd41443ea82886d50510fe20a21ff31443fc62887f4c510fe18a21ff21443fc42887f48510fe10a21ff40443fc80887f50110fe20221ff30443fc60887e8c110fe98221f930443f860887fc8110ff10221fa20443fa40887e48110fe10221ff10443f620887f84110fb08221ff54042fea8087f95010bf2a021be540427ca8087f55010beaa021bd540427aa8087f15010be2a021ff53042fea6087f94c10bf29821de53042bca6087f54c10bea9821dd53042baa6087f14c10be29821ff43043fc86087f50c10fe21821ff52042fea4087f94810bf29021ee52042dca4087f54810bea9021ed52042daa4087f14810be29021ff42043fc84087f50810fe21021ff32043fc64087f4c810fe190217e51043fe82086fd0410ff20821fd410437a82087f10410ff98821fe31043fa62087f0c410ff90821fe21043fa42087f08410bf28021ff40043fc80087f50010fe20021ff30043fc60087f4c010fe18021ff20043fc40087f48010fe10021ff10043ee20087f84010fd08021fd10043ea20087e44010
  | 1 => 0xe430c3fa86187f10c30ffa9061fe520c2fca4187f54830bea9061fc520c3fe84187f90830fea1061fc420c3fe64187f8c830fe99061fc320c3fea2187f94430bf28861fd510c2faa2187f14430ffa0861bf410c3fc82187f50430dea0861fc410c3fe62187f8c430fe98861fc310c3fe42187f88430fe90861fc210c2fca0187fd0030ff20061fd400c3f880187fcc030ef98061fe300c3f460187f4c030ee98061f9300c3fea9905fd5320ff2a6417e54c83faa9905f55320fe2a6417c54c83fea7905fd4f20ff29e417e53c83faa7905f54f20fe29e417c53c83fe87907f90f20fea1e41fc43c83fe85907f90b20f721641fd42c83da85907f10b20ff99641ef32c83fc65907f4cb20fe19641ec32c83fea3907f94720bf28e41fd51c82faa3907f14720ffa0e41bf41c83fc83907f50720dea0e41fc41c83fe63907f8c720fe98e41fc31c83fe43907bc8720ff10e41fd21c83da43907f08720ffa0641fe40c83fa81907f10320ff98641fe30c83fa61907f0c320ffaa4417f54883fca9105f95220feaa4417d54883f8a9105f15220ffa9c417f53883fca7105f94e20ef29c415e53883faa7105f54e20eea9c415d53883f8a7105f14e20ffa1c41fe43883fa87107f10e20bea9441ff42883fc85107f50a20fe21441ff32883fc65107f4ca20fe19441ff51883fca3105f94620fea8c417d51883f8a3107fd0620dfa0c41fe41883fa83106f50620fe20c41ff31883fc63107f4c620fe18c41ff21883fc43107f48620fe10c417e50883fe81107f90220fea0441fc40883fe61107f8c220fe98441fc30883fe41107bc8220fd90441ff54482fea8906fd51209faa241fe54482fca8907f55120beaa241fc54482f8a8906f151209e2a241ff53482fea6907f94d20bf29a41fd53482faa6907f14d20be29a41ff43483fc86907f50d20fe21a41ff42483fc84907b90920fea1241ed42483f884907fcc920f799241fe32483fa64907f0c920f619241ff51482fea2907f94520fea8a41fc51482f8a2907fd0520dfa0a41fe41483fa82906f50520fe20a41ff31483fc62907f4c520fe18a41ff21483de42907f88520fe90a41ed21483f842907fd0120ff20241fd40483f880907fcc120ff18241fd30483f860907fc8120fd90241fe20483dc40907fd5020bfaa041fe54082fca8107f55020beaa041fc54082f8a8107fd4c20bfa9841fe53082fca6107f54c20bea9841fc53082f8a6107fd0c20ff21841fd43083f886105f94820ffa1041fe42083fa84107f10820ff99041fe32083fa64107f0c820ffa8841fe51082fca2107f54420bea8841fc51083fe82106fd0420ff20841fd410837a82107f10420ff98841fe31083fa62107f0c420ff90841fe21083fa42107f08420bf28041ff40083fc80107f50020fe20041ff30083fc60107f4c020fe18
  | 2 => 0x3faa6a07f14d40be29a81ff43503fc86a07f50d40fe21a81ff52502fea4a07f94940fea9281fc52502f8a4a07fd0940ff21281fd42503f884a07fcc940ff19281fd32503f864a07fd4540bfa8a81fe51503faa2a07f14540be28a81ff415037e82a07f90540fea0a81bd41503f882a07fcc540ff18a81fd31503f862a07fc8540ff10a81fd21503f842a07fd0140fda0281fe405037c80a05f95040ffa9881fe53102fca6207794c40af29881fd53102faa6207754c40aea9881fc53103fe86207f90c40df21881fd43103f886206f10c40ffa9081fe52102fca4207b94840b729081fd52102faa4207b54840b6a9081fc52103fe84207f90840df21081fd42103f884206f10840ff99081fe32103fa64207f0c840ffa8881fe51102fca2207d94440bb28881fd51102faa2207d54440baa8881fc51103fe82206fd0440ff20881fd411037a82207f10440ff98881fe31103fa62207f0c440ff90881fe21103fa42207f08440bf28081ff401037e80207f90040fd20081fd401037a80207e50040ffaa6617f54cc3fca9985f95330feaa6617d54cc3f8a9985f15330ffa1e61fe43cc3bc87987f50f30eea1e61fc43cc3fea5987f94b30bf29661fd52cc2faa5987f14b30ffa1661fe42cc3fa85987f10b30ff99661fe32cc3bc65987f4cb30fe19661dc32cc3fea3987f94730bf28e61fd51cc2faa3987f14730ffa0e61bf41cc3fc83987f50730dea0e61fc41cc3fe639877cc730ff18e61fd31cc3ba63987f0c730ff90e61fe21cc3fa43987f08730ffa0661fe40cc3fa81987f10330ffaa4617f548c3fca9185f95230feaa4617d548c3f8a9185f15230bea9c61ff438c3fc87187f50e30fe21c61ff528c3fca5185f94a30f7294616e528c3faa5185f54a30f6a94616d528c3f8a5187fd0a30ff21461fd428c3f885187fcca30ff19461fd328c3f865187fd4630ff28c617e518c3faa3185f54630fe28c61ff418c37e83187f90630fea0c61bd418c3f883187fcc630ff18c61fd318c3f863187fc8630ff10c61fd218c3f843185f94230ffa0461fe408c3fa81187f10230ff98461df308c3f661187fd5130bfaa261bf544c27ea8987f95130bf2a261fd544c2faa8987f15130be2a261bc544c278a8987fd0d30ff21a61de434c3fa86987750d30fe21a61ff524c2fea4987f94930fea9261fc524c2f8a4987fd0930ff21261fd424c3f884987fcc930ff19261de324c3fa64987f0c930ee19261ff514c2fea2987f94530fea8a61fc514c2f8a2987fd0530dfa0a61fe414c3fa82986f50530fe20a61ff314c3be62987f8c530fe98a61dd314c3f862987fc8530ff10a61fd214c3f842987fd0130ff20261fd404c3f880987fcc130fd98261fe304c3bc60987fd5030bfaa061fe540c2fca8187f55030beaa061fc540c2f8a8185f94c30ffa1861f
  | 3 => 0x8790ff10f21ffa1643fe42c87fa8590ff10b21ff99643fe32c87dc6590ff4cb21f699643fc32c87fe8390efd0721ff20e43fd41c877a8390ff10721ff98e43fe31c87fa6390ff0c721ffa8643fe50c86fca190ff54321bea8643fc50c87fea910dfd5221ff2a4437e548877ca910cf95221feaa4437d548877aa910cf55221fe2a4437c54887fea710dfd4e21ff29c437e53887faa710df54e21fe29c437c53887fe8710ff90e21fea1c43fc43886faa510ffd0a21ff21443fd42887f88510ffcca21f799443fe32887fa6510ff0ca21f6194437e51887fe8310efd0621ff20c43fd418877a8310ff10621ff98c43fe31887fa6310ff0c621ff90c43ef21887ee4310ffd4221ff284437e50887faa110df54221fe28443ff54486fea890ff95121bf2a243fd54486faa890ff15121be2a243ff53486fea690f7d4d21afa9a43fe53486fca690ff54d21bea9a43fc53486f8a690f714d21ae29a43ff43487fc8690ff50d21fe21a43ff42487fc8490ff50921fe21243ff32487fc6490fb8c921fe99243ed32487f86490ffd0521dfa0a43fe41487fa8290ef50521fe20a43ff31487fc6290ff4c521fe18a43ff21487ee4290ff88521f710a43ff50486fea090ff94121fea8243fc50486f8a090ffd5021bfaa043fe54086fca810ef950219f2a043fd54086faa810ef550219eaa043fc54086f8a810ffd4c21bfa9843fe53086fca610f794c21af29843fd53086faa610f754c21aea9843fc53086f8a610ffd0c21ff21843fd43087f88610df94821ffa1043fe42087fa8410ff10821ff99043ef32087fc6410ff4c821fe19043ec32086fca210ffd0421dfa0843fe41087fa8210ef50421fe20843ff31087fc6210ff4c421fe18843ff21087de4210ff88421fb10843fd21087da4210fd48421ffa8043fe50086fca010fe94021bd28043fd50086faa010fe54021bca8043fc50087fea7a07f94f40bf29e81fd53d02faa7a07f14f40ffa1e81fe43d03fa87a07f10f40ffa9681fe52d02fca5a07f54b40bea9681fc52d03fe85a07f90b40fea1681fc42d03fe65a07f8cb40fe99681fc32d03fea3a07f94740bf28e81fd51d02faa3a07f14740ffa0e81bf41d03fc83a07f50740dea0e81fc41d03fe63a07f8c740fe98e81fc31d03fe43a07f88740fe90e81fc21d02faa9207fd4e40ff29c817e53903faa7205f54e40fe29c81ff43903fc87206f90e40fea1c81fc439037887207fd4a40ff294817e52903faa5205f54a40fe29481ff42903fc85206f90a40fea1481fc429037885207fcca40ff19481fd32903f865207fd4640ff28c817e51903faa3205f54640fe28c81ff419037e83207f90640fea0c81bd41903f883207fcc640ff18c81fd31903f863207fc8640ff10c81fd21903f843205f94240ffa0481bf40903f681207fd4d40bfa9a81fe535
  | 4 => 0xef10d41ffa92837f52507fca4a0ff54941fe292837c52507fe84a0efd0941ff21283be42507fa84a0ef50941fe21283bc42507fe64a0ff8c941fe99283fc32507fe82a0fdd0541ff20a83be41507fea0a0dfd4141ff28283fd50507f8a0a0df14141dfa9a83be535077aa6a0ef14d41dfa9283be525077aa4a0ef14941df99283be325077a64a0ef0c941dfa8a83b7515077ea0a0ef94141dea8283bc50506fca820cf95041ffa9883fe53106fca620ff54c41bea9883fc53107fe8620ff90c41fea1883fc43107fea420ff94841bf29083fd52106faa420ff14841ffa1083fe42107fa8420ff10841ff99083fe32107fa6420ff0c841bf28883ff411077e8220ff90441fb20883fd411077a8220fd50441ffa8083fe50106fca020ff54041bea8083fc50107fea998dfd5331ff2a6637e54cc7faa998df55331fe2a6637c54cc7fe8798ff90f31fea1e63fc43cc7fea598ff94b31bf29663fd52cc6faa598ff14b31ffa1663fe42cc7fa8598ff10b31ff99663df32cc7fc6598ff4cb31ee99663fc32cc7fe8398efd0731ff20e63fd41cc77a8398ff10731ffa8663fe50cc6fca198ff54331bea8663fc50cc7fea918dfd5231ff2a4637e548c77ca918cf95231feaa4637d548c77aa918cf55231fe2a4637c548c6faa718ffd0e31ff21c63fd438c7f88718ffd4a31ff294637e528c7faa518df54a31fe29463ff428c7fc8518ff50a31fe21463ff328c7fc6518f78ca31fe99463fc328c7b86518df94631ffa0c63bf418c7fc8318ff50631dea0c63fc418c7fe6318f7cc631fb98c63ff508c7fca118df94231fea84637d508c7f8a118ffd5131bfaa263fe544c6fca898ff55131beaa263fc544c6f8a898ffd0d31ff21a63fd434c7f88698ffd4931bfa9263ef524c6dea498ff94931fea9263fc524c6f8a498fb14931b629263ff424c7fc8498ff50931fe21263ff324c7be6498ff8c931fe99263dd324c7f86498ffd0531dfa0a63fe414c7fa8298ef50531fe20a63ff314c7ee6298ff8c531ef18a63ff504c6fea098ff94131fea8263fc504c6f8a098ffd5031bfaa063fe540c6fca818ef950319f2a063fd540c6faa818ef550319eaa063fc540c6f8a818df94c31ffa1863fe430c7fa8618ff10c31ffa9063fe520c6fca418fb94831b729063fd520c6faa418fb54831b6a9063fc520c7fe8418ff90831fea1063fc420c7fe6418ff8c831ef19063fd320c7f86418f70c831bf28863ff410c77e8218ff90431fea0863bd410c7f88218ffcc431ef98863fe310c7ec6218ff4c431ee98863f5310c7fea018ff94031bf28063fa500c6f4a018ff54031bea8063f9500c6f2a018ff14031ffaa6437f54c87fca990df95321feaa6437d54c87f8a990df15321ffa9e437f53c87fca790df94f21fea9e437d53c87f8a790df14f21ffa1e43fe43c87fa
  | 5 => 0xa42ffa8c85fe5190afca3217f54642bea8c85fc5190bfea1217f94242bf28485fd5090afaa1217f14242ffa9a857f5350bfca6a17f54d42fe29a857c5350bfe86a17f90d42fea1a85fc4350bfe84a17bd0942ff21285be4250bfea2a15fd4542ff28a85fd5150bf8a2a15f14542ffa82857f5050bfca0a17f54142fe282857c5050afca8217fd4c42ff298857e5310bfaa6215f54c42fe29885ff4310bfc86217f50c42fe218857e5210bfe84216fd0842ff21085ee4210bfa84216f50842f6a1085ff5110bfca2215f94442fea88857d5110bf8a2217fd4042ff280857e5010bfaa0215f54042fe28085ff54ccafea9997f95332bf2a665fd54ccafaa9997f15332be2a665ff43ccbfc87997f50f32fe21e65ff42ccbfc85997f50b32fe21665ff51ccbfca3995f94732fea8e657d51ccbf8a3997fd4332ff286657e50ccbfaa1995f54332fe28665ff548cafea9197f95232bf2a465fd548cafaa9197f15232be2a4657d538cbfe87197f90e32fea1c65fc438cafca5197fd0a32ff21465fd428cbf885197fcca32ef99465ef328cbfea3197f94632bf28c65fd518cafaa3197f14632ffa8465fe508cafca1197f54232bea8465fc508cbfea8995fd5132ff2a2657e544cbfaa8995f55132fe2a2657c544cbfe86997f90d32fea1a65fc434cbfe84997f90932fea1265fc424cbfe64997bcc932ff19265de324cbfea2995fd4532ff28a65fd514cbf8a2995f14532ffa82657f504cbfca0997f54132fe282657c504cbfea8195fd5032ff2a0657e540cbfaa8195f55032fe2a0657c540cafca6197fd0c32ff21865fd430cbf886195f94832ffa1065fe420cbfa84197f10832ff99065df320cbfc64197b8c832fe99065dd320cbda6419734c832ffa8865fe510cafca2197f54432bea8865fc510cbfea0197f94032bf28065fd500cafaa0197f14032ffa9e83fe53d06fca7a0ff54f41bea9e83fc53d07fe87a0efd0f41ff21e83be43d07fa87a0ef50f41fe21e83bc43d07fea5a0ff94b41bf29683fd52d06faa5a0ff14b41ffa1683bf42d07fc85a0ef90b41fea1683bd42d07f885a0ef10b41ff99683fe32d07fa65a0ff0cb41ffa8683fe50d06fca1a0ff54341bea8683fc50d077ea7a0ef94f41dea9e83bc53d077ea5a0ef94b41dea9683bc52d077e65a0ef8cb41de99683bc32d077ea1a0ef94341dea8683bc50d06faa920cf55241ffa9c83fe53906fca720ff54e41bea9c83fc53907fe8720ff90e41fea1c83fc43907fea520ff94a41bf29483fd52906faa520ff14a41ffa1483fe42907fa8520ff10a41ff99483fe32907fa6520ff0ca41bf28c83ff419077e8320fdd0641ffa8483fe50906fca120ff54241bea8483fc50907fea6a0dfd4d41ff29a83fd53507f8a6a0df14d41ffa1a83bf43507fc86a0ef90d41fea1a83bd43507f886a0
  | 6 => 0xe00001800402c00c00203600202000200a00001400003604800200600e00a00a00001202800e03800800002602000400800201c00800200000000200000200600800001400800400a00200400c02600200600a00000200401001000400000200400005e00200601000200600600200600400a00001400000000200a00200201000201602800200e00201000a00401800000c00a00c00000400401c00401600000a00400000401200600202600201e04600201200200c00201201a01a00401c00200001203000002000800000602600000800800e02400c00201a00401200000001c00000600200402c02601201a00600000600c00400200001600400e00c01000000a00a00000600801800000000400200e00001800400a02c00a00201000200600a00600e00000000403400a01400c00000001e01401800800400400a00201e00200e00400e00202800002801000c00c00003400000200c02000e04402e00400000000400000603200a02401000600000800000200000600000000000a00c00800600001200000001000000200200000602800600400c01a01800000000200000201c00000002200200000c00000200800001200a01201200200000800000200200000c00e00200200000400401200c00400000c00000000201000400600400800800200000c03800200e01603a00c00001400001200a00c00400401200a01000400600402400c00000404600600a01a00e00a00601400a00000400401000800000000200000200400000801400200800200401203c00001800600800a00c00200401200000000600002c006000002006004003ff52d0ffca5a1df94b43fea96877d52d0ff8a5a1ffd4743ff28e877e51d0ffaa3a1df54743fe28e87ff50d0ffca1a1df94343fea86877d50d0ff8a1a1df55243bf29c87ff4390f7e8721f7d0e43ffa9487fe5290efca521ff54a43bea9487fc5290ffea321ff94643bf28c87fd5190efaa321ff14643ffa8487fe5090efca121ff54243bea8487fc5090ffe86a1f7d0d43ff21a87be4350ffea4a1dfd4943ff29287fd5250ff8a4a1df14943ffa8a877f5150ffca2a1ff54543fe28a877c5150ffea0a1dfd4143ff28287fd5050ff8a0a1df14143bf2a0877e5310ffe8621efd0c43ff21887de4310ffa8621ef50c43eea1887ff5210ffca421df94843fea90877d5210ff8a421ffd4443ff288877e5110ffaa221df54443fe28887ff5010ffca021df94043fea80877d5010ff8a021ffd4f42ff29e857e53d0bfaa7a15f54f42fe29e85ff43d0bfc87a17f50f42fe21e85ff51d0bfca3a15f94742fea8e857d51d0bf8a3a17fd4342ff286857e50d0bfaa1a15f54342fe286857d5490bfea7217f94e42bf29c85fd5390afaa7217f14e42ffa1c85fe4390bfa87217f10e42bf29485ff4290b7e85217bd0
  | 7 => 0x240000013b0000c0c074afd231d2404000103c2089e94f0608618ec82d0000000a61b840006e8000000d68f5c000bedb64e11a28b60deda257180013800000002057ec000444e50ce835934dc95425bfc2e5b19e1d01c2b0e3dbb91d42509a8000000ce187511c001b10000001b387203a00000000005e99e5d81b8d5d4000000000db1745ab4ad51a5841d1963dc5152800068d3e51843cc000884f4929c0000000000a000000031da09a98559ad0624c2c000cec000000cd87cc6c930193ccd18054bcae83e8ab580c8983b1aa8000d480003e13240004c0000e08001d545a5664664b4c00199891c8400000017bc3106e00000000012140019b9bec0000009b44f1d842592c0ba0a5c000e0d210000e48c456048740005f01a1de49f40000000000953f1ba06a5144998ca14280013500004d0fc450538ca208540100001680001b4e8832c000cb55556cc198000bb4d413a4b28001b00e4149db5cf80c7806c000415c9ce1c3057b01d585d3e9c4558d0401d1e11c709ed829d313551c192842800000190c881be0dbc791478b891490715f48ac10c8dc981710000de4000001bcd38400003459c7ec2dc000001b80d711280153cc019558001b609686447b0f85bc400146c1a9b6c5451b52e8a29ac80004516757e9e08640b1cf98c55644988db582c000000409c195c40000013ac0014b82a5ca5508d08275a51175d6c2791acdd49e56fcc40000ef178565cc25d71e49d7c000ae0001a48d6000000001c0000000000010003d80ed9a58a537dc88000ffd885c58000e9c0002294ed2ed571b8926c001c5c62000003c538c589b00dd6b92cc9a40013590ec0016a4299c65a3c07827c6f18e0bb1a6087c3a4c6dd741b08a9da91b9b04425894cf917c5b008dd49ab949400600800c01800000000200400201400200000600200c00400a00200e00800000000a00000a00000001400000800000c01c00002200a00000201a02202c00600e00000800a00200000200400200200000202200000000e00800000400e00000c02400400600201c01a00400000208c00c00201c01000000400000400000401200201400c02801a00a00c00e00200200001800200004000800400800400e00000a01600000000400000601a00000600c00002400a01600a00000000c00000600e00000000c00e00000201200400400403a00400602a03600802202a00200400600000801400000000e01600000000200600600602600001000600800000000402800600800c00a00200001600a01400001800000200800600200600e01400001a00600a00000e01a00400200600a00600001200c00000000a01c00401600000201200400601a01400600000000000200200600001600800a00000000001400800000000202e03e02c00800000000e00200000e010000004010
  | 8 => 0xc76c460ac961c520000d20550000fdc000000aa00000000003c15dc000a311b024457c164000f000000001386553b8adc0012d8fcc0018d4001d2c3d4abc2cd2554913b5dc8f58d0036489166c3b88d0d7449821426dae8000f10df0af1be59340d4481af03f00e4ff4df57790dd4083f52ac0003344e4b9800000000000171dcb0ecc00013dcbc93c00000000000164c0011f865886c7f0c9570000179d2684f80000004adac06f400114c97c06400129800095cad04d91a8f600011143447c4ea9d217301d83c8d65865dcc0008c58f0ca8920001574c8850cfa047d480ef9631125bd0f8d7f0a7c7f99e1520001c38000001539e5c000f40cbc2d5188000a51b951f545500584800000175ccdc000ce5811b20f68d8de15740b65069bf4a6945880d10c0017540007d40000000004ec000448000990c517a15698f99680000000008a49c50b06ad519318f888f009cf385a8c9cec000011436d2f09d8ad8730b540999eccccdd8cd52b900c79d6e000168000167c3d0000000000001e21aa41f936ce5db51541c2867878d2c80018b4435b40a81aa0e95e4430cc7c935d5c001a8055d02000023d288a04d94b6c3088590ac0000000007840000000012496c1600d51305c78388000f9c6102180012b00015fc1315300b15104f4c680000014a41fdaec0000017c4000000000000d3d464001cf141cb25e64848000ba4ca55999bc0000010d471c028354b214c54f9870f140004100016385b5afd83527d860bbcb048a19600000016f840cb48000b9c8cc00112ca640000013d54757a5054844bd40016d00019008b45cd854291a680013f40000d9178001158a0800153cd6c000000001d500000016217f4f6cb0d58145c9d5a7c7280007ac8045414c1048140369d45815de9280249a59acc050000fac53c0000017b816043c000000e216b4d04000001b2dca8bacdddc3dbac464000000000338000cfd04491977c7c816c00099c9f09b8754d5c399420820000000b35774000001b140002c19a00000010f19f92d067138999cb10c75d1ce85180da468574c2bd130000e38001535241018000001b4d4a0c652fd25856935c51800000000190449d7d4c493d9cfc1dd6a11d9b3c8b1c2d9b0db8f218f59ddc1d8c5b70484fed69c758000a14ac44b804c0000000000008680000001185803bc0016400011eca39a40000bb96d80000007d0000174001400000001e180019509513bc771be8000931a940000e18bc000000000810000d34000001a9c0000000003718fc19547c0000012d423077d1c483d1cd0b86512940306b4e048e4ec5abd4d1af9d59780f544e0420d78088000000340df8928f0c5dcfb80015f8000de00000605f4808000000000a2dcd5944a18000c9000095400106594d36126489d62c00069c29cc119d0e8c0005d19550b50
  | 9 => 0x314000491c558200014d4a01e4c7101485fc628bf96186dc00181c0000001b80011700a89855016094cc510ba9594974000001399080000001d79cc4000000000000000001a6459518d56448d2dc85dab1988eece98cc1939ae08c1919ced2e02359e8a888f8185de0b2c2007e970c3190c17097ac159204dc800066c72c470418000000889d0960c8012798886bcd280009bd07c000001db9234001da1e400006a87dcc34000000829e2da14750d1c001b440000000008d8e6458dc4c90dbdc8158ad5bd654c21b5968420d0e0000e35bb4178001b34b31d2815d0bc51cee541441de34000548b84ff0ff8280000024e780000c40f9e6000045cd88a940017fc5c000148c18c1c4bf58ed1bdc80220000d10255c99015b080007f4001488a4400144c1ccf19da4000744e1579846d78c000001dec001a780001e10299f463400000000028cfe90797d99a836054c00122400000008494c000000000668fd8000708b74000d80001cdd4ad1640000013281246c0f909a00001bd39d868774d15a718d8648ebc6d18a08256a88700018c8bd8120000001908efc0017940010082f56dc02c25d68d0757dcfe46155e4001751db19ac0016ec000a9956c001418395b1c7fcfd5150fb00000015a80011954f5a04a489400459840000018c188c0b8000ed8000b3c0000000010d02940000016ac0000000013304a09055796bc5e0001441060af80019309c8000ead06c000fa5d343fcd7c000001c4964847813400000000096c2b44b1db5ae5ca0e189e184d0fd4357e50d800172131c9c0be99cc189d69011949261dd0e708bc699b5537439dd893906d93788c9c409f8f28760c18570c60851df8001110680001cc0714d980016e90cdcc800000084c3b52f4514ab873cd90c853c995d23d51ca7559d4fcdac0007a11fc0001e51f0f3c001a31e38b7ddadb90001758000000000cc4b5158400130991c9d022c7b9c8c000000494c1c8b9838431765704dc176000070d0c84bd338001af4000000000181d8d5b12a00000018d0155724cc90500c8000001e3d42c0004a40008d504d4b0001dbd941140971a34001c604d40000000010a00000009100012b5484000da17f82615c1d41c68000a6c00168955119c000001ce8c80f7c939c110c4ee94c8000000a78474000000000000e7d9c5c7c0553f984462d6b01a4000894ed1d95825ddd15d21cea50e5658b009ddbf0a9cd5860cd4c38509cfc89080691341280014a8795d05bf80480017c0001e50000001371c75369404e24001a0c5982c40000000006d59d9544e7400000007d7d00007e00000015912e4000288438f70b08fe1c202d8565461109e2589916cfd1561221980da82b927550c7b412d431bb1819729d0c7e40ac00191151474059000000005c001b300002ec000f34000a340019f1c34bd
  | 10 => 0xe19758008ecaece286f98081f0d2d610000584818e2c001b9c00122d5d03eca1c3e41ec000fb4900b15b24000000000000e585d88e0400001bc8000000c140000014e80013a09cc878788001cb875c000000798915e69a2c21124c830000240e6da5db692c40bce4dcd8ae44cdbc11d07681105559d5ba40390983dd958324104001e54000e805090387a4000330d4550400000dc01349b2902c268531c31c247811e5ad5190d9c8f5a200006b0000000000000cb87bc7019fd7b400052c000c0800183c091290edc000170cf1dd8860000000c719b592c2a93200005e4001a8c661094500001768e61a000000000e94480000013dc001238bc4865b7da1d7a96f00000000fc5b80000016c8c3ccb0f51c09bbd4703000f0000000000aac000001ac4978001678348b8d670000d2597d2854b55f00000005ed218e3042c37c00000162569105800019c0015c9e0400074c0000003a8000ef42a18788fd6340000000002700017480000000cddc000120c7498cc6007a9a840005c882cb18000000058454001920000000000a8c000001244000405915614e68be4ee16689ac48800000000125cb680002f8001c918e5cb49fc00000044dba80000005a04c892d20800105c000bf14d98dc0000000013e0000001105168f082c8001394000b90f1d4dc0000005ad3ec239588000000c38000000000000bd00011185340000011dc949b7494400000064c924f30000000000000dcd72c1446c4dc5bd4bfc000560379a38cf58a9198351c84459add525270224b80f44eb83c55ad7cddfdd64bc908976cacceb063cd54000c30a91c055b8f950f8ed4020689d9998d0910f5650724ea017c0c0468001695d90b4400081c108a3c0000000013112a932c7380000019c0a0c0014e463908428400140c1ac959df0000000f253c021c6ec778000000d84001b796e4c040000012501c98e8d0dce00015cd2bc0019c9ad8b705284e87c16d41c0328000dfc0005f96600001900017e115578800108dd9c578a40001cf80007d8000e453c4c980000012280f4000081a18bc103173557ca544dc6b8000100fa91e9334000b5835c0000005bd100000000f05bd9a91a75cf5201830a10390675991b48fbd970001850dd1890588b395ec56d88145189caa88e9d3c24d790000000e00f2c2f10a9dd5c0d410000001445a6c0011e06a1469d156f55b4d315a01f4734d18e549940d15e0be000173800096061d87cc000000000003800000000012f84a9b0d97800076586cc28000c4c001b99a886cc11c0011a12a4001cd0f64ac0a85d010a513c00488c009858aa4af45c58b8a580a465da4d30d964c5d0e83f928c001139a4533c001161c14604c8ca4c6fd54da54f78001e0c1e800000173d9240b4631e59aad5498b0b78f7469000000155d43896415014c000000000
  | 11 => 0x1dc53d0e9098c704bcc4fd314a244b42ad77052433d035ccc0006e5c6c000001e280014e083599543d3642e8b95ce4a70cac2fd3a871996c071120001628000b416c5345e000015d9d4c000001a10fc1cac4c4000b5ceb53fd499e30d3832038c26552ddf571469434cde95e9d39698000f4c3ac3755a5d61d10574ab13405d483867c4411c97c82
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xf400435d53d0010db94b400436d52d00109fd96400427d6590010cf952400433d5490010d794e400435d5390010db94a400436d5290010bd98640042f561900109fd95400433e5450010cf551400435e5350010d754d400436e5250010db549400427f65100109f994400427d65100109f194400433e5410010cf55040042de6310010b758c400435e5310010d754c40042ee6210010bb588400436e5210010db54840042f66110010bd58440043b940100109f597300433e54cc010cf553300435e53cc010d754f300436e52cc010db54b300427f658c0109f596300433e548c010cf552300435e538c010d754e30042ee628c010bb58a300436e528c010db54a30042f6618c010bd586300437a508c0109fd9530042bf644c010af191300433e544c010cf551300435e534c010d754d300436e524c010db549300437a504c0109fd94300427e650c0109f594300427c650c010cf950300433d540c010d794c300435d530c010db948300436d520c010bd98430042f5610c0109f597200433e54c8010cf553200435e53c8010d754f200436e52c8010db54b200427f65880109f596200433e5488010cf55220042de6388010b758e200435e5388010d754e200436e5288010db54a20042f66188010bd586200437a50880109fd9520042bf6448010af191200433e5448010cf551200435e5348010d754d200436e5248010db549200437a50480109fd94200427e65080109f594200427c6508010cf950200433d5408010d794c200435d5308010db948200436d5208010bd98420042f56108010af99310042bd64c4010cf953100433d54c4010d794f100435d53c4010db94b100436d52c4010edd0710043b541c4010dd59710043b664c4010ed593100437754c4010ed953100437554c4010ed553100433554c4010f594f10043d553c4010f994b10043e552c4010cf952100433d5484010d794e100435d5384010db94a100436d5284010bd58610043765184010be596100437965840109e59610043ba5484010ee552100437b5384010f694e10043795384010f654e10043595384010ded4a10043ea5284010de54a10043e95284010da54a10042f96184010de94610043f25184010eed0610043b941840109fd95100433e5444010cf551100435e5344010d754d100436e5244010db54910043b74144010ed50510042f76544010ddd9510042776544010ddd5110043b65444010dd55110043b55444010cd55110043d65344010f554d10043e65244010f954910042f76044010dd94110042fb6544010ded95100427b6544010ee95110043b95444010ded4d10043da5344010de54d10043d95344010d654d100437b5244010fa94910043795244010fa54910043695244010bed8510043f36144010de94510043f25144010eed0510043b94144010
  | 1 => 0x436e528c810db54a320427f654c8109f995320427d654c8109f195320433e544c810cf551320435e534c810d754d320436e524c810db54932042f7614c810bd185320427f650c8109f994320427d650c8109f194320433e540c810cf550320435e530c810d754c320436e520c810db54832043cd320c8109f992510433e64944108f992510427d6494410cf592510423d64944109f98e510427d63944109f98a510427d62944109f597410433f54d0410cf953410433d54d0410cf153410435e53d0410d754f410436e52d0410db54b41042bd65d0410cf597410423d65d0410cfd4f410433e53d0410e794f410431e53d0410cf54f410439d53d0410c754f410433c53d0410cfd4b410433e52d0410eb94b410432e52d0410cf54b41043ad52d0410cb54b410433c52d0410cf947410427f65904109f59641042bd6490410cf952410433d5490410d794e410435d5390410db94a410436d5290410dd94641042fa6090410be582410427f6550410cfd51410433e5450410cf551410433c5450410d794d410435d5350410db949410436d5250410dd94541042bf6550410cfd95410423f6550410cfd4d410433e5350410e794d410431e5350410cf54d410439d5350410c754d410433c5350410cfd49410433e5250410eb949410432e5250410cf54941043ad5250410cb549410433c5250410edd85410433e5150410cd945410427f65104109f59441042be6410410cf950410433d5410410d794c410435d5310410db948410436d5210410be98041042f960104109f597310433e54cc410cf553310435e53cc410d754f310436e52cc410db54b310427f658c4109f59631042be648c410af592310433e548c410cf552310435e538c410d754e310436e528c410db54a31042fa608c410be582310427f654c410cf951310433d544c410d794d310435d534c410bbd8931042ec624c410db949310436d524c4109fd94310427d650c410af99031042bd640c410cf950310433d540c410d794c310435d530c410bb98831042ed620c410db948310436d520c410be98031042f9600c4109f597210433e54c8410cf553210435e53c8410d754f210436e52c8410db54b210427f65884109f59621042be6488410af592210433e5488410cf552210435e5388410d754e210436e5288410db54a21042fa6088410be582210427f6548410cf951210433d5448410b7d8d21042dc6348410d794d210435d5348410db949210436d52484109fd94210427d6508410af99021042bd6408410cf950210433d5408410b798c21042dd6308410d794c210435d5308410db948210436d5208410be98021042f960084109f992500427d64940109f98e500427d63940109f98a500427d62940109f586500433f4194010cf506500427d65d0010cf953400433d54d0010d794
  | 2 => 0x5350c10d754d43042fb6050c10be181430427f6510c109f994430427d6510c109f194430433e5410c10cf550430435e5310c10d754c43042be64d4810af593520433e54d4810cf55352042de63d4810b758f520435e53d4810d754f520427e64d4810cf993520423e64d48109f593520433d64d48108f593520427e63d4810d798f520425e63d48109f58f520435d63d48109758f520427e61d4810dd987520427e60d4810de983520427d6594810cf952520433d5494810d794e520435d5394810dbd4a520427e64948109f592520427e63948109f58e520426d6594810dbd52520436e5494810eb952520432e5494810db55252043ad5494810cb552520436c5494810dbd4e520436e5394810f394e520434e5394810db54e52043cd5394810d354e520436c5394810dbd92520436e6494810db592520436c6494810dbd8e520436e6394810db58e520436c6394810dbd0e520436e4394810db50e520436c4394810db986520436c6194810db982520436c6094810cf951520433d5454810d794d520435d53548109fd91520427c64548109fd8d520427c6354810dbd89520427f61548109f585520427f60548109f581520436f6554810dbd51520436e5454810eb951520432e5454810db55152043ad5454810cb551520436c5454810dbd4d520436e5354810f394d520434e5354810db54d52043cd5354810d354d520436c5354810dbd91520436e6454810db591520436c6454810dbd8d520436e6354810db58d520436c6354810dbd0d520436e4354810db50d520436c4354810db985520436c6154810db981520436c6054810db04152042be6414810af590520433e5414810cf55052042de6314810b758c520435e5314810d754c52042ee6214810db548520427e6414810cf990520423e64148109f590520433d64148108f590520427e6314810d798c520425e63148109f58c520435d63148109758c520427e6214810db988520426e62148109f984520437661148109f980520437a60148109e980520427f65d08109f997420427d65d08109f197420433e54d0810cf553420435e53d0810d754f420436e52d0810db54b420427f65908109f996420427d65908109f196420433e5490810cf552420435e5390810d754e420436e5290810db54a420427f65508109f995420427d65508109f195420433e5450810cf551420435e5350810d754d420436e5250810db54942042fb6050810be181420427f65108109f994420427d65108109f194420433e5410810cf550420435e5310810d754c420436e5210810db548420427f65cc8109f997320427d65cc8109f197320433e54cc810cf553320435e53cc810d754f320436e52cc810db54b320427f658c8109f996320427d658c8109f196320433e548c810cf552320435e538c810d754e320
  | 3 => 0x109758f540427e62d5010db98b540426e62d50109f58b540436d62d50109b58b540427e61d5010dd987540427e60d5010de983540427d6595010cfd52540427e63950109f58e540427e62950109f58a540423d6595010cfd8e540433e6395010cf58e540433c6395010cfd8a540433e6295010cf58a540433c6295010cf986540433c6195010cf982540433c6095010cfd91540427f63550109f18d540427f62550109f189540427f61550109f585540427f60550109f581540433f6555010cfd8d540433e6355010cf58d540433c6355010cfd89540433e6255010cf589540433c62550108fd85540433e61550108f585540433c6155010cf981540433c6055010cf04154042be6415010cf55054042de6315010b758c54042ee6215010bb588540427e6415010cf990540423e64150109f98c540435e63150109798c540427d6315010d758c540425d63150109f988540436e62150109b988540427d6215010db588540426d62150109f984540437661150109d984540427e6015010de98054042be64d4c10af593530433e54d4c10cf55353042ee62d4c10bb58b530427e64d4c10cf993530423e64d4c109f593530433d64d4c108f593530427e62d4c10db98b530426e62d4c109f58b530436d62d4c109b58b530427e61d4c10dd987530427e60d4c10de983530427d6594c10cf952530433d5494c10d7d4e530427e6494c109f592530427e6294c109f58a530425d6594c10d7d52530435e5494c10e7952530431e5494c10d7552530439d5494c10c7552530435c5494c10d7d92530435e6494c10d7592530435c6494c10d7d8a530435e6294c10d758a530435c6294c10d7986530435c6194c10d7982530435c6094c10cf951530433d5454c109fd91530427c6454c10d7d8d530427f6254c109f189530427f6154c109f585530427f6054c109f581530435f6554c10d7d51530435e5454c10e7951530431e5454c10d7551530439d5454c10c7551530435c5454c10d7d91530435e6454c10d7591530435c6454c10d7d89530435e6254c10d7589530435c6254c10d7985530435c6154c10d7981530435c6054c10d704153042be6414c10af590530433e5414c10cf55053042de6314c10d754c53042ee6214c10bb588530427e6414c10cf990530423e6414c109f590530433d6414c108f590530427e6314c10d798c530425e6314c109f988530436e6214c109b988530427d6214c10db588530426d6214c109f98453043766114c109f980530437a6014c109e980530427f65d0c109f997430427d65d0c109f197430433e54d0c10cf553430435e53d0c10d754f430427f6590c109f996430427d6590c109f196430433e5490c10cf552430435e5390c10d754e430427f6550c109f995430427d6550c109f195430433e5450c10cf551430435e
  | 4 => 0xe980314427e65c8510dbd4b214436c52c8510ed50721442fa60c8510be583214427e6588510af99221442bd6488510ed506214427c6548510b7d8d21442dc6348510dbd49214436c5248510ed50521442fb6048510be181214427e6508510af99021442bd6408510b798c21442dd6308510ed50421442fa60085109f997404433f54d0110cf15340442f661d0110bd58740443b541d01109f996404433e5490110cf55240443b541901109fd95404427d65501109f195404433f5450110cf15140442f76150110bd18540443b541501109f994404433e5410110cf55040442de6310110b758c40442ee6210110bb58840442f66110110bd58440443b541101109f997304435f53cc110d714f30442f661cc110bd58730443b541cc1109f99630442ee628c110bb58a30443b5418c110be996304437a658c110be58e304437a538c110de14e30443ea628c110be58a30443e9628c110ba58a30442fa618c110eed0630443f2418c110ee50630443f1418c110ec506304427f654c1109f595304427c654c110afd9130442bc644c110d7d4d304435c534c110bdd8530442f4614c110ed50530442f8654c110de1953044278654c110eed9130443b8644c110f6d8d30443db534c110de94d3044378534c110f614d30443da434c110f650d30442fb624c110f68c930443d8324c110fcd8530442f8614c110fc18530443bb414c110fc90530443b9414c110fc50530443b1414c110f6cc530443d9314c1109f99430443b5410c110be98030443d9300c1109f997204436f52c8110db14b20442f661c8110bd58720443b541c81109f99620442de6388110b758e20443b54188110be996204437a6588110bed8e20443da6388110be58e20443d96388110b658e20442f96288110de94a20443785288110be98620443bb4188110fc90620443b94188110fc50620443b141881109fd95204427d65481109f19520442bf6448110af191204436f5248110db14920442f76148110bd18520443b54148110be195204437865481109e19520443bb6448110ee19120442fb6348110be58d20443eb6248110fad49204437a5248110de14920443e85248110fa90920443e94248110facc920443e83248110fcd8520442f86148110fc18520443bb4148110fc90520443b94148110fc50520443b14148110fac8520443e921481109f99420443b54108110be98020443e92008110af99310442bd64c4110ed50710443ba64c4110ee59310442fb63c4110be58f10442fb62c4110be58b10443bb41c4110fc90710443b941c4110fc50710443b141c4110edd0610443b54184110bdd9210442f56484110fcd4210443f23084110fc4c210443f22084110fc48210442de63d5010b758f54042ee62d5010bb58b540427e63d5010d798f540425e63d50109f58f540435d63d5
  | 5 => 0x524427c6454910cf191524423c64549109fd8d524435f635491097d8d524427c6354910d718d524425c6354910dbd89524427f6154910ddd85524427f6054910ded81524427e6514910db548524427e64149109f590524427e63149109f58c524436e62149109f984524427c61149109f980524437960149109f180524427f65d09109f997424427d65d09109f197424436f52d0910db14b42442f661d0910bd587424427f65909109f996424427d65909109f196424433f5490910cf15242442fa6090910be582424427f65509109f995424427d65509109f195424427f65109109f994424427d65109109f194424433f5410910cf150424436f5210910db14842442f66110910bd58442442fa6010910be580424427f65cc9109f997324427d65cc9109f197324436f52cc910db14b32442fa60cc910be583324427f658c9109f996324427d658c9109f196324435f538c910d714e32442fa608c910be582324427f654c9109f995324427d654c9109f195324427f650c9109f994324427d650c9109f194324435f530c910d714c324436f520c910db14832443cd320c910bd98432442f5610c910be98032442f9600c9109f997414433f54d0510cf15341442fa60d0510be583414433f65d0510cf997414433d65d0510cf197414433f53d0510cf94f414433d53d0510cf14f414433f52d0510cf94b414433d52d0510cf14b41443ba60d0510ee583414427e6590510af59241442f66590510dd99641442f56490510ad59241443765490510dd15241442f660905109f195414433f5450510cf15141442fb6050510be181414433f6550510cf995414433d6550510cf195414433f5350510cf94d414433d5350510cf14d414433f5250510cf949414433d5250510cf14941443b76150510eed8141443b86050510dd19541442746550510edd9141443b75450510dd95141443745450510ed15141443b74350510ed90d41443b54350510ed10d41443b74250510ed90941443b54250510ed10941443f36050510bd18141443f06050510edd9541443376550510ed19541443346550510edd8d41443b66350510ed58d41443b46350510edd4d41443b65350510ed54d41443b45350510edd8941443b66250510ed58941443b46250510edd4941443b65250510ed54941443b45250510edcc941443b63250510ed4c941443b43250510edd8141443b36050510ed98141443b56050510ed18141443b060505109f99441442be6410510bd98441443b541105109f997314435f53cc510d714f31443b541cc510be98331442f960cc5109f99631442be648c510af59231443b5418c5109f195314435f534c510d714d31442ef624c510bb18931443b5414c510bed8131442f8604c5109f99431442be640c510af59031442ee620c510bb58831443b5410c510b
  | 6 => 0x36e5288210db54a20842f66188210bd58620842f96588210de59620842fb6388210f698e20842f96388210f658e20842d96388210de94a20843ea5288210fa54a20843785288210be98620843f26188210fc58620843bb4188210ee50620842bf6448210af191208436f5248210db14920842fb6548210ded9520843bb6448210ee19120842fb6348210be58d20843eb6248210fad49208437a5248210de14920843e85248210fa90920843e94248210facc920843e83248210be18520843bb4148210ee50520843eb2148210fa485208436e5208210db54820842f66108210bd58420843e92008210af99310842bd64c4210edd0710843b541c4210bd597108437565c4210ed99310843b564c4210ddd53108437554c4210be597108437965c4210ee99310843b964c4210bed8f10842f963c4210bed8b10842f962c4210eed0710843b941c42109f98f544427d63d51109f98b544427d62d5110cfd52544427e64951109f98e544427d63951109f98a544427d62951109f586544437561951109f58254443796095110b7d8d54442dc6355110bbd8954442ec6255110cfd91544427f6355110d7d8d544425f63551109f18d544435c63551109718d544427f6255110dbd89544426f62551109f189544436c62551109b189544427f6155110ddd85544427f6055110ded81544427e6515110cf550544433e64151109f98c544427d63151109f988544427d62151109f984544437561151109f184544427e60151109f180544427e64d4d109f593534427e62d4d109f58b534435f5394d109f992534427d6494d109f98e534427e6294d109f58a534427d6194d10dd586534427d6094d10de58253442bf6454d10af19153442ef6254d10bb189534427f6454d10cfd91534423f6454d109f191534433c6454d108f191534435f6354d109fd89534436f6254d109bd89534427c6254d10db189534426c6254d109fd8553443776154d109fd81534437b6054d109f994534435d5314d109f990534427d6414d10d798c534427e6214d109f588534427e6114d109f184534427e6014d10de580534427c6014d109fd97434427e65d0d109f597434427c65d0d10d7d4f434435c53d0d10bd98743442f561d0d109fd96434427e6590d109f596434427c6590d10cfd52434433c5490d10be98243442f96090d109fd95434427e6550d109f595434427c6550d109fd94434427e6510d109f594434427c6510d10cfd50434433c5410d10d7d4c434435c5310d10bd98443442f56110d10be98043442f96010d109f993524427d64d49109f98f524427d63d4910dbd4a524427e64949109f592524427e63949109f58e524427e62949109f586524437561949109f58252443796094910afd9152442bc6454910b7d8d52442dc63549109fd91524433f64549108fd91
  | 7 => 0x454a10cfd91528423f6454a109f191528433c6454a108f191528427f6354a109f18d528436f6254a10db548528427e6414a109f590528427e6314a109f58c528436e6214a10dd584528437a6014a109fd97428427e65d0a109f597428427c65d0a109fd96428427e6590a109f596428427c6590a10cfd52428433c5490a10db94a428436d5290a10be98242842f96090a109fd95428427e6550a109f595428427c6550a10db949428436d5250a109fd94428427e6510a109f594428427c6510a10cfd50428433c5410a10be98042842f96010a109fd97328427e65cca109f597328427c65cca10db94b328436d52cca10be98332842f960cca109fd96328427e658ca109f596328427c658ca10d794e328435d538ca10be98232842f9608ca109fd95328427e654ca109f595328427c654ca10bdd8532842f4614ca109fd94328427e650ca109f594328427c650ca10d794c328435d530ca10db948328436d520ca10f34c832842fa600ca10be580328433e54d0610cf55341842fa60d0610be583418433e65d0610cf597418433f53d0610cf94f418433d53d0610cf14f418433f52d0610cf94b418433d52d0610cf14b41843ba60d0610ee583418433e5450610cf55141842fb6050610be181418433f6550610cf195418433f5350610cf94d418433d5350610cf14d418433f5250610cf949418433d5250610cf14941843b76150610eed8141843b86050610d794f318435d53cc610be98331842f960cc610af99231842bd648c610d794d318435d534c610bbd8931842ec624c610bed8131842f8604c610af99031842bd640c610bb98831842ed620c610be580318436e52c8610db54b21842fa60c8610be58321842be6488610af59221842df6348610b718d218436e5248610db54921842fb6048610be18121842be6408610af59021842de6308610b758c21842f96008610cfd53408433c54d0210cf952408433d5490210bd98640842f56190210cfd51408433c5450210cf950408433d5410210b798c40842dd6310210bb98840842ed6210210bd98440842f56110210d7d4f308435c53cc210d794e308435d538c210bb98a30842ed628c210bd98630842f5618c210be5963084379658c210de94e30843da538c210f654e3084378538c210fa98a30842f9628c210fa58a30842e9628c210be98630843f2618c210fc58630843bb418c210ee50630842bf644c210af191308435f534c210d714d30842fb654c210ded9530843bb644c210ee19130843db634c210f6d4d308437a534c210de14d30843d8534c210f690d30843d9434c210bed8930843da324c210f60c930842f8614c210eed0530843b9414c210f6cc530843d9314c210d794c308435d530c210bd98430842f5610c210f64c0308436f52c8210db14b20842de6388210b758e2084
  | 8 => 0x10db94a21c436d5288710ed50621c42fa6088710be58221c433e5448710cf55121c42df6348710b718d21c436f5248710db14921c43b54148710af99021c42bd6408710cf95021c433d5408710b798c21c42dd6308710db94821c436d5208710ed50421c42fa6008710be58021c433e54d0310cf55340c42f661d0310bd58740c43b541d0310cf95240c433d5490310ed50640c433e5450310cf55140c42f76150310bd18540c43b54150310cf95040c433d5410310b798c40c42dd6310310bb98840c42ed6210310bd98440c42f56110310ed50440c43b94010310cf95330c433d54cc310d794f30c435d53cc310bd98730c42f561cc310ed50730c433e548c310cf55230c42ee628c310bb58a30c43b5418c310afd9130c42bc644c310cf95130c433d544c310d794d30c435d534c310bdd8530c42f4614c310ed50530c433e540c310cf55030c43b5410c310cf95320c433d54c8310db94b20c436d52c8310bd98720c42f561c8310ed50720c433e5488310cf55220c42de6388310b758e20c43b54188310afd9120c42bc6448310cf95120c433d5448310db94920c436d5248310bdd8520c42f46148310ed50520c433e5408310cf55020c43b541083109f98f548427d63d52109f98b548427d62d5210dd587548437a60d5210cfd52548427e63952109f58e548427e62952109f58a548433f64552109fd8d548427c63552109fd89548427c6255210cf55054842de6315210b758c54842ee6215210bb588548433e64152109f98c548435e63152109798c548427d6315210d758c548425d63152109f988548436e62152109b988548427d6215210db588548426d6215210dd584548437a6015210bb98b53842ed62d4e109f993538427d64d4e109f98b538436e62d4e109b98b538427d62d4e10db58b538426d62d4e10dd587538437a60d4e10d7d4e538427e6494e109f592538427e6294e109f58a538437a6094e10afd9153842bc6454e109fd91538433f6454e108fd91538427c6454e10cf191538423c6454e10d7d8d538427f6254e109f189538435d5314e109f990538427d6414e10d798c538427e6214e109f58853843756114e10de980538427f65d0e109f997438427d65d0e109f197438427f6590e109f996438427d6590e109f196438433f5490e10cf152438435e5390e10d754e43842fa6090e10be582438427f6550e109f995438427d6550e109f195438435e5350e10d754d438427f6510e109f994438427d6510e109f194438433f5410e10cf15043842fa6010e10be58043842de63d4a10b758f528427e64d4a109f593528427e63d4a10d798f528425e63d4a109f58f528435d63d4a109758f528437561d4a10de983528436f5294a109f992528427d6494a109f98e528427d6394a10de98252842bf6454a10af191528427f6
  | 9 => 0x59052c427e6314b10d798c52c425e6314b109f58c52c435d6314b109758c52c436e6214b10dd98452c43796014b109fd9742c427e65d0b109f59742c427c65d0b10cf95342c433d54d0b10bd98742c42f561d0b109fd9642c427e6590b109f59642c427c6590b10cf95242c433d5490b109fd9542c427e6550b109f59542c427c6550b10cf95142c433d5450b10bed8142c42f86050b109fd9442c427e6510b109f59442c427c6510b10cf95042c433d5410b10bd98442c42f56110b109fd9732c427e65ccb109f59732c427c65ccb10cf95332c433d54ccb10d794f32c435d53ccb10dbd4b32c436c52ccb109fd9632c427e658cb109f59632c427c658cb10cf95232c433d548cb10d7d4e32c435c538cb10db94a32c436d528cb109fd9532c427e654cb109f59532c427c654cb10cf95132c433d544cb10d794d32c435d534cb10db94932c436d524cb109fd9432c427e650cb109f59432c427c650cb10cf95032c433d540cb10d7d4c32c435c530cb10dbd4832c436c520cb10f34c832c42f6610cb10bd58432c433f54d0710cf95341c433d54d0710cf15341c42bd65d0710cf59741c433f53d0710cf94f41c433d53d0710cf14f41c433f52d0710cf94b41c433d52d0710cf14b41c433e5490710cf55241c42fa6090710be58241c43756590710dd95241c43b65490710ed55241c43745490710bd98241c43f26090710fc58241c433f5450710cf95141c433d5450710cf15141c42bf6550710cfd9541c433f5350710cf94d41c433d5350710cf14d41c433f5250710cf94941c433d5250710cf14941c43b76150710bdd9541c43776550710edd9141c43b75450710dd95141c43b65450710cd95141c43b55450710dd15141c43b45450710edd0d41c43b64350710ed50d41c43b44350710edd0941c43b64250710ed50941c43b44250710bd18141c43b76550710add9541c43376550710edd8d41c43b66350710ed58d41c43b46350710edd4d41c43b65350710ed54d41c43b45350710edd8941c43b66250710ed58941c43b46250710edd4941c43b65250710ed54941c43b45250710edcc941c43b63250710ed4c941c43b43250710edd8141c43b66050710ed58141c43b46050710cf95041c433d5410710ed50441c42fa6010710be58041c433e54cc710cf55331c435f53cc710d714f31c43b541cc710af99231c42bd648c710cf95231c433d548c710d794e31c435d538c710ed50631c42fa608c710be58231c433e544c710cf55131c435f534c710d714d31c42ef624c710bb18931c43b5414c710af99031c42bd640c710cf95031c433d540c710d794c31c435d530c710bb98831c42ed620c710ed50431c42fa600c710be58031c433e54c8710cf55321c436f52c8710db14b21c43b541c8710af99221c42bd6488710cf95221c433d54887
  | 10 => 0x836d5448020db94d200836c5348020db54520083af4148020eb50520082ef6048020db94120083eb4048020fa10120083ea3048020fa4c120082fb6548020ded95200827b6548020eed9120083b86448020bed8920083eb6248020de94920083ea5248020fad0920083e84248020fa8c920083e93248020de54520083bb4148020ee50520083eb2148020fa485200827e63d53109f58f54c427e62d53109f58b54c437661d5310de58354c433f54953109f98e54c427d63953109f98a54c427d6295310dd98654c43b66195310cfd8e54c433e6395310cf58e54c433c6395310cfd8a54c433e6295310cf58a54c433c6295310cf98654c43366195310cf18654c433f6095310cf58254c433f64553109fd8d54c427c63553109fd8954c427c6255310cfd9554c43b66155310cfd8d54c433e6355310cf58d54c433c6355310cfd8954c433e6255310cf58954c433c6255310cf98554c433c6155310cfd8154c433d6055310cf55054c433e64153109f98c54c427d63153109f98854c427d6215310dd98454c43796015310af99353c42bd64d4f10cf95353c433d54d4f109f99353c433e64d4f108f99353c427d64d4f10cf59353c423d64d4f109f98b53c427d62d4f10dd98753c437960d4f10cf95253c433d5494f10d7d4e53c427e6494f109f59253c427e6294f109f58a53c433e5454f10cf55153c42ef6254f10bb18953c427f6454f109f19153c435f6354f109fd8953c436f6254f109bd8953c427c6254f10db18953c426c6254f10af99053c42bd6414f10cf95053c433d5414f10d754c53c42ee6214f10bb58853c427e6414f10cf99053c423e6414f109f59053c433d6414f108f59053c435e6314f109f98853c436e6214f109b98853c427d6214f10db58853c426d6214f10dd98453c43796014f109fd9743c427e65d0f109f59743c427c65d0f10cf95343c433d54d0f10bd98743c42f561d0f109fd9643c427e6590f109f59643c427c6590f10cf95243c433d5490f109fd9543c427e6550f109f59543c427c6550f10cf95143c433d5450f10bed8143c42f86050f109fd9443c427e6510f109f59443c427c6510f10cf95043c433d5410f10bd98443c42f56110f10af99352c42bd64d4b10cf95352c433d54d4b109f99352c433e64d4b108f99352c427d64d4b10cf59352c423d64d4b109f98f52c427d63d4b10dd98752c437960d4b10cf95252c433d5494b10dbd4a52c427e6494b109f59252c427e6394b109f58e52c433e5454b10cf55152c42df6354b10b718d52c427f6454b109f19152c427f6354b10d7d8d52c425f6354b109f18d52c435c6354b109718d52c436f6254b10af99052c42bd6414b10cf95052c433d5414b10b798c52c42dd6314b10db54852c427e6414b10cf99052c423e6414b109f59052c433d6414b108f
  | 11 => 0x5d530c820db94832083cd320c820be98032082f9600c820af99251082bd6494420ddd46510827e6494420cf992510823e64944209f592510833d64944208f592510827e63944209f58e510827f64544209f191510827f63544209f18d51082be6414420af59051082de6314420b758c510837551144209fd97410827e65d04209f597410833f54d0420cf953410833d54d0420cf153410833f65d0420cf997410833d65d0420cf197410833f53d0420cf94f410833d53d0420cf14f410833e52d0420cf947410833d51d04209fd96410827e65904209f59641082bd6490420dd946410837551904209fd95410827d65504209f195410833f5450420cf951410833d5450420cf15141082ef6250420bb18941083765150420dd54541082fb6050420be181410833f6550420cf995410833d6550420cf195410833f5350420cf94d410833d5350420cf14d41083af6250420eb189410833e5250420edd85410833e5150420ed94541083365150420cf54541083b55150420cd54541083bb6050420ee181410827f65104209f994410827d6510420af990410827f65cc4209f997310827d65cc420d794f310835d53cc4209fd96310827e658c4209f59631082be648c420af5923108376518c420dd546310827f654c4209f595310827c654c420d794d310835d534c420bbd8931082ec624c420dd9453108375514c4209fd94310827e650c4209f59431082be640c420af59031082ee620c420bb58831082fa600c420be580310836e52c8420dd947210837551c8420be98321082f960c84209f59621082be6488420af592210827f6548420b7d8d21082dc6348420db94921082be6408420af59021082de6308420b758c21083765108420dd54421082fa6008420be580210827e64940209f592500827e6394020d798e500825e63940209f58e500835d63940209758e500833f4194020cf506500827d65d00209fd96400827d6590020cf952400833d5490020bb98a40082ed62900209fd95400827f65100209f994400827d65100209f194400833e5410020cf55040082de6310020b758c40082ee6210020bb58840082f66110020bd584400827d65cc020d7d4f300835c53cc0209fd96300827d658c020d794e300835d538c020bb98a30082ed628c0209fd9530082bf644c020af191300835f534c020d714d300827f650c0209f994300827d650c0209f194300835e530c020d754c30082ee620c020bb588300836f54c8020db553200836e53c8020db14f200836d51c8020ebd0720083ad41c8020b798e20082dd6388020bb58a200836e5288020f698e20083d96388020be58a200837a5288020fa94a20083795188020eed0620083b941880209fd9520082bf6448020af19120082ef6548020dbd95200826f6548020ebd9120083ac6448020dbd512
  | 12 => 0x10120bb98840482ed6210120eb90840482f66110120bd58440483b940101209f997304833f54cc120cf153304835f53cc120d714f30482ee62cc120bb58b30483cc32cc1209f996304833f548c120cf15230482ee628c120bb58a304827f654c1209f595304827c654c120afd9130482bc644c120cfd51304833c544c120d7d4d304835c534c120bbd8930482ec624c120f30c9304827e650c120cfd50304833c540c120f64c0304833f54c8120cf15320483bb54c8120ee15320483ea42c8120fa50b20483eb32c8120fa0cb20482f961c8120eed0720483b941c8120fac8720483e921c8120cfd52204833c5488120b798e20482dd6388120bbd9220482ed6488120ebd5220483ac5488120bb98e20483ce6388120b398e20483cd6388120bb18e20482ed6188120ebd0620483ad4188120fad42204827e63d50209f58f540827e62d5020db98b540827e61d50209f587540827e60d5020de983540827d6595020cfd52540827e63950209f58e540827e61950209f586540833f64550209fd8d540827c63550209fd89540827d62550209fd85540827c6155020cf55054082de6315020b758c54082f66115020bd584540827e6415020cf990540827e6315020d798c540825e63150209f58c540835d63150209758c540827e6215020db988540826e62150209f984540837661150209d984540827d6115020dd584540827561150209f980540837a60150209f993530827d64d4c209f98b530836e62d4c209b98b530827e61d4c209f587530827e60d4c20de983530827d6594c20d7d4e530827e6494c209f592530827e6194c209f586530827f6454c209f191530835f6354c209fd89530827d6254c209fd85530827c6154c20af99053082bd6414c20d754c53082f66114c20bd584530827e6414c20cf990530823e6414c209f590530833d6414c208f590530827e6314c20d798c530827e6214c20db988530827e6114c20dd98453082766114c209f58453083756114c209d584530827e6014c20de980530827f65d0c209f997430827d65d0c209f197430833e54d0c20cf553430827f6590c209f996430827d6590c209f196430835e5390c20d754e43082ee6290c20bb58a43082fa6090c20be582430827f6550c209f995430827d6550c209f195430833e5450c20cf551430835e5350c20d754d430827f6510c209f994430827d6510c209f194430827e64948209f592520827e63948209f58e520827d65d08209fd96420827d6590820cf952420833d5490820db94a42082fa6090820be582420827f6550820db949420827f65108209f594420833e5410820cf55042082fa6010820be580420827d65cc820db94b320827f658c8209f596320835e538c820d754e32082fa608c820be582320827f654c8209fd94320827d650c820d794c32083
  | 13 => 0xdbcc8514836c3214520de580514827e65d05209f597414827c65d0520cfd53414833e54d0520cf553414833c54d0520bb98b41482ed62d0520eb90b41483ad42d0520cfd9741482be65d0520cf997414823e65d0520cf59741482bc65d0520cf197414823c65d0520cfd4f414833e53d0520cf54f414833c53d0520eb98b41483ad62d0520ebccb41483ac32d0520cfd47414833c51d05209f996414827d65905209f19641482bd6490520cfd52414833c5490520bb98a41482ed6290520be98241482f960905209fd95414827e65505209f195414833f5450520cf951414833d5450520cf15141483ae4250520eb509414833f6550520af995414833e65505208f995414833d6550520af195414833c65505208f195414833f5350520cf94d414833d5350520cf14d41483ae6250520eb58941483af3250520eb0c941483b76150520cfd45414833c51505209f994414827d65105209f19441482be6410520cfd50414833c5410520bb98841482ed6210520be98041482f960105209f997314827d65cc5209f197314833f54cc520cf153314835e53cc520d754f31483cf32cc520ddd47314837451cc5209f996314827d658c5209f19631482be648c520af592314833f548c520cf152314835f538c520d714e31482ee628c520bb58a31483cc328c520be98231482f9608c5209fd95314827e654c5209f195314833f544c520cf151314835e534c520d754d31482ef624c520bb18931483cf324c5209f994314827d650c5209f19431482be640c520af590314833f540c520cf150314835f530c520d714c31482ee620c520bb58831483cc320c520ddd443148374510c520be98031482f9600c5209f997214833f54c8520cf15321482ee65c8520db99721482ef64c8520bb59321483af54c8520eb15321482ee63c8520bb18f214836f53c8520db54f214836c51c8520ebd0721483ad41c8520fad8321482ee60c8520fa18321482be6488520af592214833f5488520cf15221482ed6288520ddd4621483745188520be98221482f96088520cfd51214833c5448520b7d8d21482dc6348520ddd4521483745148520bed8121482f86048520bbd9121482ed6448520ebd5121483ac5448520f3d8d21482ee6348520bb18d21483cc6348520b318d214836f5348520db54d21483e76148520f9d45214836c5148520f914521483af4148520eb50521483eb6048520bb18121483e860485209f99421482be6408520af590214833f5408520cf15021482de6308520b758c21482ee6208520be980214827e65d0120cfd53404833c54d0120bb98b40482ed62d01209f996404833f5490120cf15240483ae42901209fd95404827d65501209f195404833f5450120cf15140482ef6250120bb189404827e6510120cfd50404833c5410120b798c40482dd63
  | 14 => 0x92534833e6494d208f992534827d6494d20cf592534823d6494d209f98e534827d6294d20db58a534827e6194d209f586534827d6094d20de58253482bf6454d20af191534833f5454d20cf15153482f76154d20bd185534827f6454d20cfd91534823f6454d209f191534833c6454d208f191534835f6354d209fd89534836f6254d209fd8553483776154d209dd85534827c6154d20dd18553482746154d209fd81534837b6054d209f994534833f5414d20cf150534835d5314d209f990534827d6414d20d798c534827e6214d209f188534827e6114d209f584534827f65d0d209f997434827d65d0d209f197434833f54d0d20cf15343482ee62d0d20bb58b434827f6590d209f996434827d6590d209f196434833f5490d20cf152434827f6550d209f995434827d6550d209f195434833f5450d20cf15143482ef6250d20bb18943482fb6050d20be181434827f6510d209f994434827d6510d209f194434833f5410d20cf15043482ee6210d20bb58843482fa6010d20be580434827e65d0920cfd53424833c54d0920be98342482f960d09209f996424833f5490920cf15242482ee6590920db99642482ed6490920ebd52424836e5490920db15242483ac5490920cb15242482ee6390920bb58642482ee60909209f195424833f5450920cf15142482fb6050920be181424836c65509209b19542483af6450920ebd51424836e5450920db15142483ac5450920bb18d42482ef6150920fad8142482ec6050920fa18142482e860509209f994424833f5410920cf15042482ee62109209f997324833f54cc920cf153324835f53cc920d714f32482fa60cc920be583324836e65cc9209b99732482ef64cc920bb59332483af54cc920eb153324836f53cc920f3d4f324836d53cc920f314f32482ed61cc920bb98332483ea60cc920ba98332483e960cc9209f996324833f548c920cf152324835e538c920d754e32482ee628c9209f195324833f544c920cf151324835f534c920d714d32482fb604c920be181324827e650c920cfd50324833c540c920d794c324835d530c920f34c832482ee650c920db99432482ef640c920bb59032483af540c920eb15032482ee630c920f398c324836f530c920f394c324836d530c920f354c324834d530c920bb58432482ee600c920cfd53514833c54d4520cfd93514827e64d45209f593514833c64d45209f98f514827d63d4520af99251482bd6494520cfd52514833c5494520ddd4651482bf6454520af191514833f5454520cf15151482df6354520b718d51482be6414520af590514833f5414520cf15051482de6314520b758c514837551145209f990514833e64145208f990514827d6414520cf590514823d64145209f98c514835e63145209798c514827d6314520d758c514825d631452
  | 15 => 0x8833d5350620e754d418831d5350620cf14d41883af6250620eb18941883b76150620cf94541883b65150620cd945418833d5150620ed545418833551506209fd94418827e65106209f594418835e5310620d754c41882fa6010620be580418827f65cc6209f997318827d65cc620d794f318835d53cc6209fd96318827e658c6209f59631882be648c620af592318835e538c620d754e31882fa608c620be582318827f654c6209f595318827c654c620d794d318835d534c620bbd8931882ec624c6209fd94318827e650c6209f59431882be640c620af590318835e530c620d754c31882ee620c620bb58831882fa600c620be580318835e53c8620d754f21882be6488620af592218835e5388620d754e21883765188620dd54621882fa6088620be58221882df6348620b718d218835e5348620d754d21883765148620dd54521882fb6048620be18121882be6408620af59021882de6308620b758c218835e5308620d754c21882f96008620d794f408835d53d0220cf952408833d5490220d794e408835d5390220bb98a40882ed6290220d794d408835d5350220cf950408833d5410220b798c40882dd6310220d794c408835d5310220bb98840882ed6210220bd98440882f56110220ee500408835e53cc220d754f308835e538c220d754e30882ee628c220bb58a30882bf644c220af191308835e534c220d754d308835e530c220d754c30882ee620c220bb58830883d9300c220d794f208835d53c8220bb597208836d65c8220dbd53208836d54c8220db94f20883ce53c8220d394f20883cd53c8220db14f208836d51c8220ebd0720883ad41c8220be597208837965c8220f694f20883d953c8220be58720883bb41c8220ee507208827e63d51209f58f544827e61d51209f58754483af62d5120af587544833f63d5120cf98f544833d63d5120cf18f544833f62d5120cf58b544833f61d5120cf987544833d61d51208f587544833c61d5120cfd83544833d60d5120cfd52544827e64951208f992544827e63951209f58e544827d6295120db58a544827e61951209f586544827d6095120de582544833f64551209fd8d544827c63551209fd89544836f62551209fd85544827c61551209fd81544837b60551209f994544833d5415120cf990544827e63151209f58c544827e6215120db588544827c62151209f984544827d6115120af994544833e65151208f99454483ad6215120af584544833f6315120cf98c544833d6315120cf18c544833f6215120cf588544832d6215120cfd84544833e6115120cf584544823d6115120cf184544833f6015120cf580544833d2015120cfd53534833c54d4d209f993534827d64d4d20db58b534827e61d4d209f58753482be6494d20af592534833f5494d20cf152534835f5394d209f9
  | 16 => 0xe63152209f58c548835d63152209758c548836d62152209f984548837661152209d984548827d6115220dd58454882756115220de980548827e64d4e209f593538836d62d4e209f987538827d61d4e20de983538835f5394e209f992538827d6494e209f986538827d6194e20d7d52538835e5494e20d7552538835c5494e20d7d92538835e6494e20d7592538835c6494e20d7d8a538835d6294e20d7d86538835e6194e20d7586538835c6194e20d7982538835c6094e209fd91538827c6454e20d7d8d538827f6154e209f185538835f6554e20d7d51538835e5454e20d7551538835c5454e20d7d91538835e6454e20d7591538835c6454e20d7d89538835d6254e20d7d85538835e6154e20d7585538835c6154e20d7981538835c6054e20d754c538827e6414e209f590538835e6314e20db588538827e6114e209f584538837a6014e209fd97438827e65d0e209f597438827c65d0e20d794f438835d53d0e209fd96438827e6590e209f596438827c6590e20d794e438835d5390e20bb98a43882ed6290e209fd95438827e6550e209f595438827c6550e20d794d438835d5350e20bed8143882f86050e209fd94438827e6510e209f594438827c6510e20d794c438835d5310e20be98043882f96010e20cf953428833d54d0a20d794f428835d53d0a20be98342882f960d0a20cfd52428833c5490a20d794e428835d5390a20cf951428833d5450a20d794d428835d5350a20bed8142882f86050a20cfd50428833c5410a20d794c428835d5310a20d794f328835d53cca20be98332882f960cca20d794e328835d538ca20d794d328835d534ca20bed8132882f8604ca20d794c328835d530ca20f34c832882de63d4620b758f518835e53d4620d754f51882be6494620af592518835e5394620d754e518837751946209f992518833e64946208f992518827d6494620cf592518823d64946209f98e518827d6394620de982518835e5354620d754d518827f64546209f191518827f63546209f18d51882be6414620af59051882de6314620b758c518835e5314620d754c518837551146209fd97418827e65d06209f597418833f54d0620cf953418833d54d0620cf153418835e53d0620d754f418833f65d0620cf997418833d65d0620cf197418833f53d0620cf94f418839e53d0620c794f418833d53d0620e754f418831d53d0620cf14f418833e51d0620cf547418827f65906209f996418827d6590620d794e418835d5390620dd94641883755190620be98241882f960906209fd95418827d65506209f195418833f5450620cf951418833d5450620cf151418835e5350620d754d41882ef6250620bb18941883765150620dd545418833f6550620cf995418833d6550620cf195418833f5350620cf94d418839e5350620c794d41
  | 17 => 0x4720db0ca51c827f64547209f19151c827f63547209f18d51c82be6414720af59051c82de6314720b758c51c837551147209fd9741c827e65d07209f59741c833f54d0720cf95341c833d54d0720cf15341c82ee62d0720bb58b41c83ae42d0720eb50b41c833f65d0720cf99741c833d65d0720cf19741c833f53d0720cf94f41c833d53d0720cf14f41c83ae62d0720eb58b41c83af32d0720eb0cb41c833e51d0720cf54741c827f65907209f99641c827d6590720bb98a41c82ed62907209fd9541c827d65507209f19541c833f5450720cf95141c833d5450720cf15141c83ae4250720eb50941c82fb6050720be18141c833f6550720cf99541c833d6550720cf19541c833f5350720cf94d41c833d5350720cf14d41c83ae6250720eb58941c83af3250720eb0c941c83b76150720cf94541c833d5150720eed8141c83b860507209fd9441c827e65107209f59441c82ee6210720bb58841c827f65cc7209f99731c827d65cc720d794f31c835d53cc720f3ccb31c827f658c7209f99631c827d658c720af99231c82bd648c720bb98a31c82ed628c720f30ca31c827f654c7209f59531c827c654c720d794d31c835d534c720bbd8931c82ec624c720f3cc931c827f650c7209f99431c827d650c720af99031c82bd640c720bb98831c82ed620c720f30c831c82fa600c720be58031c837651c8720dd54721c82fa60c8720be58321c82ef64c8720bb59321c82ee63c8720bb18f21c836f53c8720db54f21c836e51c8720f994721c83e551c8720ebd0721c83ad41c8720bb98321c83ea60c8720fa58321c82be6488720af59221c82df6348720b718d21c82ef6548720dbd9521c82ef6448720bb59121c83cf6348720bb98d21c82ec6348720f318d21c82cc6348720dbd4d21c836d5348720f9d8521c836e5148720ebd0521c83ad4148720bb18121c82be6408720af59021c82de6308720b758c21c83765108720dd54421c82fa6008720be58021c833e54d0320cf55340c82ee62d0320bb58b40c833f5490320cf15240c83ae4290320cf95140c833d5450320bbd8940c82ec6250320cfd5040c833c5410320b798c40c82dd6310320bb98840c82ed6210320eb90840c82f66110320bd58440c835e53cc320d754f30c82ee62cc320bb58b30c83cc32cc320bb98a30c82ed628c320afd9130c82bc644c320d794d30c835d534c320bbd8930c82ec624c320f30c930c82de63d5220b758f548827e63d5220d798f548825e63d52209f58f548835d63d52209758f548836d62d52209f987548827d61d5220de983548833f54952209f98e548827d63952209f986548827d6195220cfd91548827f63552209f18d548827f61552209f185548833d5415220b798c54882dd6315220bd98454882f56115220cf990548827e6315220d798c548825
  | 18 => 0xd7d53300c35d54cc030d794b300c35d51cc030e7d07300c39d41cc030b758e300c35e538c030bb98a300c2ed628c030be58e300c37a538c030f694e300c3ea628c030fa58a300c379518c030eed06300c3b9418c0309fd95300c2bf644c030af191300c2df654c030d7d95300c25f654c030e7d91300c39c644c030d7d51300c35d544c030d7949300c35d514c030e7d05300c39d414c030b7d81300c35e504c030f6d01300c3d8404c030bed95300c37b654c0309ed95300c3bb644c030ee191300c2fb634c030f6d8d300c37a534c030f694d300c3db434c030f610d300c3db324c030f64c9300c379514c030eed05300c3b9414c030f6cc5300c3d9314c030b798f54c82dd63d53209f98f54c835e63d53209798f54c827d63d5320d758f54c825d63d5320db98b54c827e61d53209f58754c837960d5320cfd5254c827e63953209f58e54c836e62953209f98654c827d6195320cfd9154c827f63553209f18d54c827f61553209f18554c833d5415320cf99054c827e63153209f58c54c836e62153209f98454c827d6115320de58054c82be64d4f20af59353c827e64d4f20cf99353c823e64d4f209f59353c833d64d4f208f59353c836e62d4f209f98753c827d61d4f20de58353c835f5394f209f99253c827d6494f209f98653c827d6194f209fd9153c827c6454f20d7d8d53c836c6254f209fd8553c827c6154f20d754c53c827e6414f209f59053c835e6314f20db98853c827e6114f209f58453c83796014f209fd9743c827e65d0f209f59743c827c65d0f20d794f43c835d53d0f20bb98b43c82ed62d0f209fd9643c827e6590f209f59643c827c6590f20cf95243c833d5490f20be98243c82f96090f209fd9543c827e6550f209f59543c827c6550f20bbd8943c82ec6250f209fd9443c827e6510f209f59443c827c6510f20cf95043c833d5410f20d794c43c835d5310f20bb98843c82ed6210f20cf95242c833d5490b20be98242c82f96090b20db59642c836e5490b20eb95242c83ad5490b20db15242c82ee6390b20bb58642c82ee6090b20fa98242c83e96090b20bbd9542c836f6550b20ebd9142c836e5450b20db15142c82ec6350b20bbd8542c82ec6050b20cf95042c833d5410b20be98042c82f96010b20bb59732c836d65ccb20bbd9332c82ed64ccb20dbd4f32c836d53ccb20bb58732c82ee60ccb20d794e32c835d538cb20be98232c82f9608cb20d794c32c835d530cb20f34c832c82fa600cb20be58032c836d650cb20bbd9032c82ed640cb20f398c32c836f530cb20f394c32c836d530cb20f354c32c834d530cb20bb58432c82ee600cb20fa98032c83e9600cb20af99251c82bd6494720ddd4651c827e6494720cf99251c823e64947209f59251c833d64947208f59251c827e63947209f58e51c836f329
  | 19 => 0x2430c35e5390c30be982430c2f96090c309fd95430c35e5350c309fd94430c27d6510c30cf950430c33d5410c30be980430c2f96010c30dbd4a520c27e64948309f592520c27e61948309f586520c27f64548309f191520c27f61548309f185520c2be6414830af590520c36d5214830bd984520c2f561148309fd97420c27e65d08309f597420c33e54d0830cf553420c27f65908309f996420c27d6590830b798e420c2dd6390830db94a420c36d5290830be982420c2f960908309fd95420c27d65508309f195420c33e5450830cf551420c36e5250830db549420c27f65108309f994420c27d6510830db94b320c36d52cc830be983320c2f960cc8309f596320c35e538c8309fd95320c35e530c830db948320c36d520c830f34c8320c2fa600c830be580320c2be6494430af592510c37751944309f992510c33e64944308f992510c27d6494430cf592510c23d64944309f98a510c27d62944309fd91510c27c64544309fd89510c27c6254430af990510c2bd6414430bb988510c2ed6214430dd544510c27f65d04309f997410c27d65d0430cfd53410c33e54d0430cf553410c33c54d0430cfd97410c33e65d0430cf597410c33c65d0430cf94f410c33e52d0430cf54b410c33e51d0430cf547410c27f65904309f996410c27d6590430af592410c3765190430dd546410c27f65504309f595410c27c6550430cfd51410c33e5450430cf551410c33c5450430b7d8d410c2dc6350430dd945410c3755150430bed81410c2f86050430cfd95410c33e6550430cf595410c33c6550430e7d8d410c39c6350430cf94d410c33e5250430cf549410c3b76150430cf945410c3b65150430cd945410c33d5150430ed545410c3355150430eed81410c3b860504309fd94410c27e65104309f594410c2be6410430d794f310c37651cc430dd547310c2fa60cc430be583310c27d658c430af992310c2bd648c4309fd95310c35e534c430bbd89310c2ec624c430af990310c2bd640c430bb988310c2ed620c430dd944310c375510c430be980310c2f9600c4309fd97210c27e65c84309f597210c36e52c8430db54b210c27f65884309f996210c27d6588430af992210c2bd6488430dd946210c37551884309fd95210c27d65484309f195210c2df6348430b718d210c36e5248430db549210c3765148430dd545210c27f65084309f994210c27d6508430af990210c2bd6408430b798c210c2dd6308430be980210c2f960084309f992500c27d6494030db98a500c36d6294030cfd06500c33d41940309f597400c27f65900309f596400c33e5490030cf552400c2de6390030b758e400c27f65500309fd94400c27e65100309f594400c27c6510030cf950400c33d5410030b798c400c2dd6310030bb988400c2ed6210030bd984400c2f56110030
  | 20 => 0xc33f54cc530cf153314c2de65cc530d7997314c2df64cc530b7593314c39f54cc530e7153314c2de62cc530d7d4b314c35c51cc530e7d07314c39d41cc530f6d83314c2de60cc530f6183314c2be648c530af592314c33f548c530cf152314c2dd638c530ddd46314c374518c530be982314c2f9608c530cfd51314c33c544c530bbd89314c2ec624c530ddd45314c374514c530bed81314c2f8604c530b7d91314c2dd644c530e7d51314c39c544c530f3d89314c2dc624c530f3189314c2cc624c530d7d49314c3d7614c530f5d45314c35c514c530f5145314c39f414c530e7505314c3db604c530b7181314c3d8604c5309f994314c2be640c530af590314c33f540c530cf150314c2de630c530bb988314c2ed620c530be980314c27e65c85309f597214c27c65c8530cfd53214c33c54c8530b7d8f214c2dc63c8530f38cb214c37751c8530dd147214c27e65885309f596214c27c6588530af992214c2bd6488530cfd52214c33c5488530b798e214c2dd6388530dbd4a214c36c5288530f30ca214c2fa6088530be582214c27f65485309f995214c27c6548530cfd51214c33c5448530b7d8d214c2dc6348530f38c9214c27e65085309f594214c27c6508530af990214c2bd6408530cfd50214c33c5408530b798c214c2dd6308530dbd48214c36c5208530f30c8214c3775108530dd144214c2fa6008530be580214c27e65d0130cfd53404c33c54d0130b798f404c2dd63d01309f996404c33f5490130cf152404c39e43901309fd95404c27d65501309f195404c33f5450130cf151404c2df6350130b718d404c27e6510130cfd50404c33c5410130b798c404c2dd6310130e790c404c2ee6210130bb588404c2f66110130bd584404c3b94010130cfd53304c33c54cc130eed53304c3b854cc130f690f304c3d943cc130f68cb304c3d832cc130be587304c3bb41cc130ee507304c3db31cc130f64c7304c33f548c130cf152304c2ee628c130bb58a304c2df648c130b7592304c39f548c130e7152304c2de628c130f398a304c2ce628c130f358a304c2dd618c130e7d06304c39d418c130f6d42304c27e63d5030d798f540c27e62d50309f58b540c27e61d50309f587540c27e60d5030de983540c27d6595030cfd52540c27e62950309f58a540c27e61950309f586540c33f64550309fd8d540c27d63550309fd89540c27c62550309fd85540c27c6155030cf550540c2ee6215030bb588540c2f66115030bd584540c27e6415030cf990540c27e6315030d798c540c25e63150309f988540c36e62150309b988540c27d6215030db588540c26d62150309f984540c37661150309d984540c27d6115030dd584540c27561150309f980540c37a60150309f992530c27d6494c309f597430c27f6590c309f596430c33e5490c30cf55
  | 21 => 0x5410d30b798c434c33f54d4930cf153524c27e64d49309f593524c27e61d49309f587524c2be6494930af592524c33f5494930cf152524c36f5294930afd91524c2bc6454930cfd51524c33c5454930bdd85524c2f46154930cfd50524c33c5414930db548524c27e64149309f590524c27e61149309f584524c27e65d09309f597424c27c65d0930cfd53424c33c54d0930b798f424c2dd63d09309f996424c27d65909309f196424c33f5490930cf152424c27f65509309f995424c27c6550930cfd51424c33c5450930b7d8d424c2dc6350930bed81424c2f860509309f994424c27d65109309f194424c33f5410930cf150424c2de6310930b758c424c2fa6010930be580424c27e65cc930cfd53324c33c54cc930cfd52324c33c548c930dbd4a324c36c528c930be982324c2f9608c930b7d92324c2dd648c930e7d52324c39c548c930b798a324c35f528c930f3d4a324c3cc528c930b7586324c2de608c930f6982324c2da608c930f6582324c33f544c930cf151324c36f524c930db149324c2fb604c930be181324c27e650c930cfd50324c33c540c930f34c8324c2de650c930d7994324c2df640c930b7590324c39f540c930e7150324c2de620c930f3988324c35f520c930f3948324c3cd520c930b7584324c2de600c930cfd53514c33c54d4530cfd93514c27e64d45309f593514c33c64d45309f98b514c27d62d4530af992514c2bd6494530cfd52514c33c5494530ddd46514c2bf6454530af191514c33f5454530cf151514c2ef6254530bb189514c2be6414530af590514c33f5414530cf150514c2ee6214530bb588514c37551145309f990514c33e64145308f990514c27d6414530cf590514c23d64145309f988514c36e62145309b988514c27d6214530db588514c26d6214530d78c8514c35c3214530de580514c27e65d05309f597414c27c65d0530cfd53414c33e54d0530cf553414c33c54d0530b798f414c2dd63d0530e790f414c39d43d0530cfd97414c2be65d0530cf997414c23e65d0530cf597414c2bc65d0530cf197414c23c65d0530e798f414c39d63d0530cfd4b414c33c52d0530e78cb414c39c32d0530cfd47414c33c51d05309f996414c27d65905309f196414c2bd6490530cfd52414c33c5490530b798e414c2dd6390530be982414c2f960905309fd95414c27e65505309f195414c33f5450530cf951414c33d5450530cf151414c39e4350530e750d414c33f6550530af995414c33e65505308f995414c33d6550530af195414c33c65505308f195414c39e6350530e758d414c33f5250530cf149414c39e3250530e70c9414c3b76150530cfd45414c33c51505309f994414c27d65105309f194414c2be6410530cfd50414c33c5410530b798c414c2dd6310530be980414c2f960105309f997314
  | 22 => 0x630ed545418c33551506309fd94418c27e65106309f594418c36e5210630db548418c2fa6010630be580418c36e52cc630db54b318c2be648c630af592318c36e528c630db54a318c376518c630dd546318c2fa608c630be582318c2ef624c630bb189318c36e524c630db549318c376514c630dd545318c2fb604c630be181318c2be640c630af590318c2ee620c630bb588318c36e520c630db548318c2f9600c6309fd97218c27e65c86309f597218c36e52c8630db54b218c27f65886309f996218c27d6588630af992218c2bd6488630db94a218c36d5288630be982218c2f960886309fd95218c27d65486309f195218c2df6348630b718d218c36e5248630db549218c27f65086309f994218c27d6508630af990218c2bd6408630b798c218c2dd6308630db948218c36d5208630be980218c2f96008630db94b408c36d52d0230cf952408c33d5490230b798e408c2dd6390230db94a408c36d5290230db949408c36d5250230cf950408c33d5410230b798c408c2dd6310230bb988408c2ed6210230db948408c36d5210230bd984408c2f56110230ee500408c36e52cc230db54b308c2dd65cc230d7597308c35f54cc230d7553308c35e52cc230f394b308c34e52cc230f354b308c35d51cc230e7d07308c39d41cc230be597308c37965cc230fa94b308c3e952cc230be587308c3bb41cc230ee507308c27e62d51309f58b544c27e61d51309f587544c39f63d5130af587544c33f63d5130cf58f544c33f62d5130cf98b544c33d62d5130cf18b544c33f61d5130cf987544c33d61d51308f587544c33c61d5130cfd83544c33d60d5130cfd52544c27e64951308f992544c27d6395130d758e544c27e62951309f58a544c27e61951309f586544c27d6095130de582544c33f64551309fd8d544c35f63551309fd89544c27c62551309fd85544c27c61551309fd81544c37b60551309f994544c33d5415130cf990544c27e6315130d758c544c27c63151309f988544c27d62151309f984544c27d6115130af994544c33e65151308f994544c39d6315130af584544c33f6315130cf58c544c31d6315130cfd88544c33e6215130cf588544c33c6215130cfd84544c33e6115130cf584544c23d6115130cf184544c33f6015130cf580544c33d30151309f997434c33f54d0d30cf153434c2fa60d0d30be583434c27e6590d30cfd52434c33c5490d30b7996434c35e6590d30b7592434c39f5490d30d7952434c35c5490d30e7152434c31c5490d30b798a434c2dd6190d30b7982434c27c6550d30cfd51434c33c5450d30bed81434c2f86050d30d7195434c25c6550d30e7d91434c39f5450d30d7951434c35c5450d30e7151434c2dc6250d30b7d85434c3db6050d30b7181434c3d86050d30b6181434c27e6510d30cfd50434c33c
  | 23 => 0xf986548c27d6195230cfd91548c27f62552309f189548c27f61552309f185548c33d5415230bb988548c2ed6215230bd984548c2f56115230cf990548c35d63152309f988548c36e62152309b988548c27d6215230db588548c26d62152309f984548c37661152309d984548c27d6115230dd584548c2756115230de980548c33e54d0e30cf553438c2fa60d0e30be583438c33f5490e30cf152438c33e5450e30cf551438c2fb6050e30be181438c33f5410e30cf150438c36f5294a309f992528c27d6494a309f986528c27d6194a30dbd52528c36e5494a30db552528c36c5494a30dbd92528c36e6494a30db592528c36c6494a30dbd8e528c36f4394a30db90e528c36d4394a30db10e528c36f6194a30db986528c36d6194a30db186528c36e6094a30db182528c27f6454a309f191528c27f6154a309f185528c36f6554a30dbd51528c36e5454a30db551528c36c5454a30dbd91528c36e6454a30db591528c36c6454a30db58d528c36f4354a30db90d528c36d4354a30db10d528c36f6154a30db985528c36d6154a30db185528c36e6054a30db181528c36d5214a309fd97428c27e65d0a309f597428c36e52d0a30db54b428c27f6590a309f996428c27d6590a30b798e428c2dd6390a30db94a428c36d5290a309fd95428c27d6550a309f195428c36e5250a30db549428c2fb6050a30be181428c27f6510a309f994428c27d6510a30db948428c36d5210a30be980428c2f96010a30db94b328c36e528ca30db54a328c2fa608ca30be582328c36e524ca30db549328c2fb604ca30be181328c36d520ca30f34c8328c2ee62d4630bb58b518c36e52d4630db54b518c2be6494630af592518c36e5294630db54a518c37751946309f992518c33e64946308f992518c27d6494630cf592518c23d64946309f98a518c27d6294630de982518c36e5254630db549518c27f64546309f191518c27f62546309f189518c2be6414630af590518c2ee6214630bb588518c36e5214630db548518c37551146309fd97418c27e65d06309f597418c33f54d0630cf953418c33d54d0630cf153418c36e52d0630db54b418c33f65d0630cf997418c33d65d0630cf197418c33e52d0630eb94b418c32e52d0630cf54b418c3ad52d0630cb54b418c33e51d0630cf547418c27f65906309f996418c27d6590630db94a418c36d5290630dd946418c3755190630be982418c2f960906309fd95418c27d65506309f195418c33f5450630cf951418c33d5450630cf151418c2df6350630b718d418c36e5250630db549418c3765150630dd545418c33f6550630cf995418c33d6550630cf195418c39f6350630e718d418c33e5250630eb949418c32e5250630cf549418c3ad5250630cb549418c3b76150630cf945418c3b65150630cd945418c33d5150
  | 24 => 0x32cc2dd658cb30d759632cc2df648cb30b759232cc35d528cb30b758632cc2de608cb30db94832cc36d520cb30f34c832cc2fa600cb30be58032cc2df640cb30b759032cc3ce620cb30f394832cc35d520cb30f354832cc34d520cb30b758432cc2de600cb30f698032cc3d9600cb30af99251cc2bd6494730ddd4651cc27e6494730cf99251cc23e64947309f59251cc33d64947308f59251cc27e62947309f58a51cc35e3294730d70ca51cc27f64547309f19151cc27f62547309f18951cc2be6414730af59051cc2ee6214730bb58851cc37551147309fd9741cc27e65d07309f59741cc33f54d0730cf95341cc33d54d0730cf15341cc2de63d0730b758f41cc39e43d0730e750f41cc33f65d0730cf99741cc33d65d0730cf19741cc39e63d0730e758f41cc33e52d0730cf54b41cc39e32d0730e70cb41cc33e51d0730cf54741cc27f65907309f99641cc27d6590730b798e41cc2dd63907309fd9541cc27d65507309f19541cc33f5450730cf95141cc33d5450730cf15141cc39e4350730e750d41cc2fb6050730be18141cc33f6550730cf99541cc33d6550730cf19541cc39e6350730e758d41cc33e5250730cf54941cc39e3250730e70c941cc3b76150730cf94541cc33d5150730eed8141cc3b860507309fd9441cc27e65107309f59441cc2de6310730b758c41cc37651cc730dd54731cc2fa60cc730be58331cc2df64cc730b759331cc2de62cc730d754b31cc35e51cc730f594731cc3d551cc730e7d0731cc39d41cc730b798331cc3da60cc730f658331cc2be648c730af59231cc2ef624c730bb18931cc2df654c730d7d9531cc2df644c730b759131cc3cf624c730b718931cc3cc624c730b318931cc35d524c730f5d8531cc35e514c730e7d0531cc39d414c730b718131cc2be640c730af59031cc2ee620c730bb58831cc376510c730dd54431cc2fa600c730be58031cc27f65c87309f99721cc27d65c8730b7d8f21cc2dc63c8730db94b21cc36d52c8730f38cb21cc27f65887309f99621cc27d6588730af99221cc2bd6488730b798e21cc2dd6388730f30ca21cc27f65487309f59521cc27c6548730b7d8d21cc2dc6348730db94921cc36d5248730f38c921cc27f65087309f99421cc27d6508730af99021cc2bd6408730b798c21cc2dd6308730f30c821cc2fa6008730be58021cc33e54d0330cf55340cc2de63d0330b758f40cc33f5490330cf15240cc39e4390330cf95140cc33d5450330b7d8d40cc2dc6350330cfd5040cc33c5410330b798c40cc2dd6310330e790c40cc2ee6210330bb58840cc2f66110330bd58440cc2ee62d5230bb58b548c35d63d52309f98b548c36e62d52309b98b548c27d62d5230db58b548c26d62d52309f987548c27d61d5230de983548c33f54952309f98a548c27d62952309
  | 25 => 0x2bf6448440af19121102df6348440b718d211035e5348440d754d211036e5248440db54921103765148440dd54521102fb6048440be181211027f65084409f994211027d6508440af99021102bd6408440b798c21102dd6308440d794c211035d5308440db948211036d5208440dd94421103755108440be98021102f96008440cf90e501033c4394040cf90a501033c4294040cfd06501033d4194040d794f401035d53d0040db94b401036d52d0040dd947401037551d0040af98f401039e53d0040e754f40102be62d0040eb94b40103ad52d0040af58740103b651d0040cf54740103b551d0040cd54740102bd6490040cf952401035e5390040d754e401036e5290040db54a40103765190040dd54640102f96490040de95240103ba5490040f694e40103d95390040ee90e40103b84390040fa94a40103e95290040ee90a40103b84290040fc94640103f15190040eed0640103b941900409fd95401035e5350040d754d401036e5250040db54940103765150040dd54540102bf6550040cfd95401023f6550040af18d401039e5350040e754d40102bc6250040eb94940103ad5250040afd8540103b65150040cf54540103b55150040cd54540102bf6050040cf94140102fb6550040ded95401027b6550040bed9140103bb6450040de95140103ba5450040f694d40103d95350040eed0d40103b94350040fa94940103e95250040eed0940103b94250040fc94540103f15150040ee90540103b84150040bb98b54cc2ed62d5330d798f54cc27e62d5330db98b54cc26e62d53309f58b54cc36d62d53309b58b54cc27e61d53309f58754cc37960d5330cfd5254cc35e63953309f98a54cc27d62953309f98654cc27d6195330cfd9154cc27f62553309f18954cc27f61553309f18554cc33d5415330cf99054cc35e63153309f98854cc27d62153309f98454cc27d6115330de58054cc33e5490f30cf55243cc2fa6090f30be58243cc35d6590f30d795243cc39e5490f30e755243cc35c5490f30b798a43cc2dd6190f30b798243cc3da6090f30f658243cc2df6550f30d7d9543cc39f6450f30d795143cc35c5450f30b718943cc2df6150f30b718143cc33e5410f30cf55043cc2fa6010f30be58043cc2be64d4b30af59352cc36f5294b309f99252cc27d6494b309f98652cc27d6194b309fd9152cc27c6454b309fd8552cc27c6154b30db54852cc27f65d0b309f99742cc27d65d0b30b798f42cc2dd63d0b30db94b42cc36d52d0b309fd9642cc27e6590b309f59642cc33e5490b30cf55242cc2fa6090b30be58242cc27f6550b309f59542cc27c6550b30b7d8d42cc2dc6350b309fd9442cc27e6510b309f59442cc33e5410b30cf55042cc2de6310b30b758c42cc36e5210b30db54842cc36e52ccb30db54b32cc2fa60ccb30be583
  | 26 => 0x254440ddd9551103b66454440ddd4d51103765354440f594d51103565354440dd54d51103d55354440d554d51103745354440ed90d51103b44354440ddd4951103765254440f994951103665254440dd54951103e55254440d954951103745254440ed90951103b44254440dd99151103366454440ddd8d51103766354440dd58d51103746354440ddd0d51103764354440cd90d51103754354440dd10d51103344354440ddd8951103766254440dd58951103746254440ddd0951103764254440cd90951103754254440dd10951103344254440ddcc951103763254440dd4c951103743254440dd98151103746054440dd10151102de6314440b758c511035e5314440d754c51102ee6214440bb588511036e5214440db54851102f66114440dd544511033e54d0440d794f411035d53d0440db94b411036d52d0440dd947411037551d0440be98341102f960d0440af98f411033e53d0440e794f411031e53d0440cf54f411039d53d0440c754f41102be62d0440cf94b41103ae52d0440cb94b411033d52d0440eb54b411032d52d0440cf94741103b651d0440cf54741103b551d0440cd54741103ba60d0440af58341103b960d0440ae583411027d6590440af592411035e5390440d754e411036e5290440db54a411037551904409fd95411033e5450440d794d411035d5350440db949411036d5250440dd94541102bf6550440cfd9541102bc6350440cf94d411039e5350440c794d411033d5350440e754d411031d5350440af189411033e5250440eb949411032e5250440cf54941103ad5250440cb54941103b76150440cf94541103b65150440cd94541103b55150440afd8141102be6410440d794c411035d5310440db948411036d5210440dd94441103755110440be98041102f960104409fd97311027e65cc4409f59731102bf64cc440af193311035e53cc440d754f311036e52cc440db54b311037651cc440dd547311027f658c4409f996311027d658c440af99231102bd648c440d794e311035d538c440db94a311036d528c440dd9463110375518c4409fd95311027d654c4409f19531102bf644c440af191311035e534c440d754d31102ef624c440bb189311036e524c440db5493110376514c440dd54531102fb604c440be181311027f650c4409f994311027d650c440af99031102bd640c440d794c311035d530c440bb98831102ed620c440db948311036d520c440dd9443110375510c440be98031102f9600c4409fd97211027e65c84409f59721102bf64c8440af193211035e53c8440d754f211036e52c8440db54b211037651c8440dd547211027f65884409f996211027d6588440af99221102bd6488440d794e211035d5388440db94a211036d5288440dd946211037551884409fd95211027d65484409f1952110
  | 27 => 0x40dbd8e521036e6394840db58e521036c6394840dbd0e521036e4394840db50e521036c4394840dbd86521036e6194840db586521036c6194840db982521036c6094840d794d521035d53548409fd8d521027c63548409fd85521027c6154840dbd9552103ac6454840dbd4d521036e5354840f394d521034e5354840db54d52103cd5354840d354d521036c5354840eb90d52103ac4354840db991521036f6354840db98d521036d6354840db18d521036f4354840db90d521036d4354840db10d521036f6154840db985521036d6154840db185521036e6054840db181521036c4054840b798c52102dd6314840d794c521035d5314840bb988521036d5214840bd98452102f56114840d794f421035d53d0840db94b421036d52d0840be98342102f960d08409f596421035e5390840d754e421036d5290840af596421033d6590840af98e421039e5390840e754e42102be6290840eb94a421033d5290840eb54a421032d5290840af58642102bd60908409fd95421035e5350840d754d421036e5250840d794c421035d5310840db948421036d5210840be98042102f96010840af98c421039e5310840e754c42102be6210840eb98842103ae5210840cf54842103ad5210840af58442103ba6010840af58042103b96010840ae580421027f65cc8409f997321027d65cc840af99332102bd64cc840d794f321035d53cc840db94b321036d52cc840be98332102f960cc8409fd96321027e658c8409f59632102be648c840af592321035e538c840d754e321036e528c840db54a32102fa608c840be582321027f654c8409f595321027c654c840afd9132102bc644c840d794d321035d534c840db949321036d524c8409fd94321027e650c8409f59432102bf640c840af190321035e530c840d754c321036e520c840db54832103cd320c840b798f51102dd63d4440d794f511035d53d4440bb98b51102ed62d4440db94b511036d52d4440d794e511035d5394440db94a511036d5294440ddd46511027e63944409f58e511027e62944409f58a51103b66494440ddd4e51103765394440f594e51103565394440dd54e51103d55394440d554e51103745394440ed90e51103b44394440ddd4a51103765294440f994a51103665294440dd54a51103e55294440d954a51103745294440ed90a51103b44294440dd19251103776394440dd98e51103756394440dd18e51103774394440dd90e51103754394440dd10e51103776294440dd98a51103756294440dd18a51103774294440dd90a51103754294440dd10a51103773294440dd8ca51103753294440dd0ca51103766094440dd182511035e5354440d754d511036e5254440db549511033e64544409fd8d511027c6354440cf90d511033c43544409fd89511027c6254440cf909511033c4
  | 28 => 0x59032503cd320c940be98032502f9600c940cfd93515027e63d45409f58f515027e62d45409f58b51503775194540b7d8d51502dc6354540bbd8951502ec6254540dd544515027e63145409f58c515027e62145409f588515027e65d0540af997415033e65d0540cfd4f415033c53d0540cfd4b415033c52d0540cf14741502be60d0540af59241503775190540dd14641502fa6090540be58241503775150540dd14541502fb6050540be181415033f5350540cf14d415033f5250540cf14941503b76150540cfd4541503b75150540cdd45415033c5150540ed14541503bb6050540af18141503b86050540ae181415027e6510540af99041503b541105409f997315027d65cc5409f197315027e658c5409f596315027c658c540af99231502bd648c540d7d4e315035c538c5409fd95315027e654c5409f19531502ef624c540bb189315027e650c5409f594315027c650c540af99031502bd640c540d7d4c315035c530c540bb98831502ed620c540be98031502f9600c5409f997215027d65c85409f197215027e65885409f596215027c6588540af99221502bd6488540dbd4a215036c52885409fd95215027e65485409f19521502df6348540b718d215027e65085409f594215027c6508540af99021502bd6408540b798c21502dd6308540dbd48215036c5208540be98021502f96008540eed0740503b941d0140cf14e405033c5290140af586405033f5190140eed4240502ee62d4c40bb58b53102f661d4c40bd587531035f5394c409f98a531027d6294c409f986531027d6194c40e7192531035c6494c40d7d8a531035e6294c40d758a531035c6294c40d7d86531035e6194c40d7586531035c6194c40d7982531035c6094c409fd89531027c6254c409fd85531027c6154c40d7d95531039c6454c40d7991531035f6254c40d7989531035d6254c40d7189531035f6154c40d7985531035d6154c40d7185531035e6054c40d7181531035c4054c40b798c531035d5314c40bb98853102ed6214c40bd98453102f56114c40d794f431035d53d0c40be98343102f960d0c409f596431035d5390c40af596431033d6590c40af98e431039e5390c40cf54e431039d5390c40c754e43102be6290c40af58643102bd6090c409fd95431035e5350c40d794c431035d5310c40be98043102f96010c40af98c431039e6310c40e794c431033d5310c40e754c43102be6210c40af58443103ba6010c40af58043103b96010c40ae58043102de63d4840b758f521035e53d4840d754f52102f661d4840bd587521035e5394840d754e521036f52948409f98e521027d63948409f986521027d6194840eb192521036f5394840db94e52103ce5394840d394e521036d5394840f354e521034d5394840db14e52103ae4394840eb10e521036c64948
  | 29 => 0x29027d65cca40af99332902bd64cca40db94b329036d52cca409fd96329027e658ca409f59632902be648ca40af592329035e538ca40d754e329027f654ca409f595329027c654ca40afd9132902bc644ca409fd94329027e650ca409f59432902bf640ca40af190329035e530ca40d754c329036e520ca40db54832903cd320ca40be98032902f9600ca40ddd46519027e63946409f58e519027e62946409f58a519033d64546409fd8d519027c6354640cf90d519033c43546409fd89519027c6254640cf909519033c4254640b798c51902dd6314640bb98851902ed6214640dd54451902bd65d0640cf59741902be63d0640cf94f419033d53d0640af98b419033e52d0640cf54b419033e51d0640af58341903765190640dd54641902fa6090640be58241903765150640dd54541902fb6050640be18141902bc6350640cf94d419033d5350640af189419033e5250640cf54941903b76150640cf94541903b65150640cd945419033d5150640ed54541903355150640afd8141903bb6050640ee181419027f65cc6409f997319027d65cc640afd9331902bc64cc640d794f319035d53cc6409fd96319027e658c6409f59631902be648c640af592319027f654c6409f595319027c654c640afd9131902bc644c640d794d319035d534c640bbd8931902ec624c6409fd94319027e650c6409f59431902be640c640af59031902ee620c640bb58831902fa600c640be580319027f65c86409f997219027d65c8640afd9321902bc64c8640db94b219036d52c86409fd96219027e65886409f59621902be6488640af592219027f65486409f595219027c6548640afd9121902bc6448640b7d8d21902dc6348640db949219036d52486409fd94219027e65086409f59421902be6408640af59021902de6308640b758c21902fa6008640be58021902bd65d0240cf59740902be63d0240af98b40902bd61d0240cf54740902f965d0240de597409027e62d4d409f58b535027e61d4d409f587535035f5394d40bb98a53502ed6294d40d754c535027e6214d409f588535027e6114d409f584535027e65d0d40d7d4e435035c5390d40be98243502f96090d40d7d4d435035c5350d40bed8143502f86050d409f994435027e63d49409f58f525027e61d49409f58752502de6394940b758e525036f5294940db548525027e63149409f58c525027e61149409f584525027e65d0940dbd4a425036c5290940be98242502f96090940dbd49425036c5250940bed8142502f860509409f994425027e65cc9409f597325027c65cc940d7d4f325035c53cc9409f996325027d658c9409f196325036f528c940db14a325027f654c9409f995325027c654c940d7d4d325035c534c940dbd49325036c524c9409f994325027d650c9409f19432502be640c940af
  | 30 => 0x7d6294f409f98653d027d6194f409fd8953d027c6254f409fd8553d027c6154f40d754c53d035e53d0f40d754f43d02fa60d0f40be58343d035e5310f40d754c43d02fa6010f40be58043d036f5294b409f98e52d027d6394b409f98652d027d6194b409fd8d52d027c6354b409fd8552d027c6154b40db54852d036e52d0b40db54b42d02fa60d0b40be58342d036e5210b40db54842d02fa6010b40be58042d027f65ccb409f99732d027d65ccb40be98332d02f960ccb409fd9632d027e658cb409f59632d02fa608cb40be58232d027f654cb409f59532d027c654cb409fd9432d027e650cb409f59432d02be640cb40af59032d03cd320cb40ddd4651d027e63947409f58e51d027e62947409f58a51d033e64547409fd8d51d027c63547409fd8951d027c6254740dd54451d037651d0740dd54741d02fa60d0740be58341d033e53d0740cf54f41d033e52d0740cf54b41d033e51d0740ed94741d033d51d0740ed54741d033551d0740af98341d03ba60d0740ee58341d02bf6550740cfd9541d033e5350740cf54d41d033e5250740cf54941d03b76150740edd4541d033e5150740ed14541d02bc6050740dd94441d03755110740ed50441d02fa6010740be58041d027f65cc7409f99731d027d65cc7409fd9631d027e658c7409f59631d02be648c740af59231d027f654c7409f59531d027c654c740bbd8931d02ec624c740bed8131d02f8604c7409fd9431d027e650c7409f59431d02be640c740af59031d02ee620c740bb58831d02fa600c740be58031d027f65c87409f99721d027d65c87409fd9621d027e65887409f59621d02be6488740af59221d027f65487409f59521d027c6548740b7d8d21d02dc6348740bed8121d02f860487409fd9421d027e65087409f59421d02be6408740af59021d02de6308740b758c21d02fa6008740be58021d02ee62d4e40bb58b539035f5394e409f98a539027d6294e409f986539027d6194e409fd89539027c6254e409fd85539027c6154e40d754c539035e5390e40d754e43902fa6090e40be582439039e5390e40cf54e439039d5390e40af98a43902bd6190e40ee98243902bd6090e40ee582439035e5350e40d754d43902fb6050e40be18143902bd6510e40cf594439039e6310e40cf54c43902be6210e40af58443902bd6010e40b798f52902dd63d4a40dbd4a529027e6394a409f58e529027e6194a409f586529027f6354a409f18d529027f6154a409f185529036d5214a40db94a429036d5290a40be98242902f96090a40af98e42903ae5290a40cf54a42903ad5290a40af58642903ba6090a40af58242903b96090a40db949429036d5250a40bed8142902f86050a40af594429033d6510a40af98c42903ae6210a40cf54842902bd6110a40af580429027f65cca409f9973
  | 31 => 0x884219fd95210873e5448421cf55121086df6348421b718d210875e5348421d754d21087b74148421ed50521086ef6548421dbd95210866f6548421eb95121087ad5448421f3d8d21086ee6348421bb18d21087cc6348421b318d210876f5348421f394d210876d5348421f354d210874d5348421bbd85210876e5148421ebd0521087e64148421eb50521087e54148421e950521086f76548421ddd9521086776548421ed95121087b55448421f5d8d21087d46348421f594d21087d55348421bdd8921087e76248421dd94921087e65248421f990921087e54248421af99350086bd64d4021cf953500873d54d4021b798f50086dd63d4021d794f500875d53d4021cf952500873d5494021d794e500875d5394021ded42500867e64940219f592500867e63940219f58e500873f4194021cf506500877b5494021de95250087ba5494021ce95250087795494021ee55250087395494021de152500877b5394021de94e50087da5394021d694e50087795394021f654e50087595394021de14e50087eb3294021fa0ca50087bb4194021ee50650087eb2194021fc88650087e92194021fc486500877b6494021de99250087796494021de192500877b6394021de98e50087796394021de18e500877b4394021de90e50087794394021de10e50087786294021ded0a500877a4294021de50a50087784294021decca500877a3294021de4ca50087783294021de186500877b4194021ced06500877a4194021de50650087394194021de106500877b3194021de8c650087793194021de0c6500877b2194021de88650087792194021cf951500873d5454021d794d500875d53540219fd91500867c64540219fd8d500867c6354021dbcc9500876c3254021cfd05500873d4154021dbc85500876d2154021ded95500877b5454021de95150087ba5454021ce95150087795454021ee55150087395454021de151500877b5354021de94d50087da5354021d694d50087795354021f654d50087595354021de14d50087eb3254021fa0c950087bb4154021ee50550087eb2154021fc88550087e92154021fc485500877b6454021de99150087796454021de191500877b6354021de98d50087796354021de18d500877b4354021de90d50087794354021de10d500877a6254021ded09500877a4254021de50950087784254021decc9500876b3254021de8c950087793254021de0c950087683254021de985500877b4154021ced05500877a4154021de50550087394154021de105500877b3154021de8c550087793154021de0c5500877b2154021dac85500877a2154021de48550087692154021de08550086be6414021af590500873e5414021cf55050086de6314021b758c500875e5314021d754c50086fa6014021de540500875f5394f409f98a53d02
  | 32 => 0x19fd94420867d6510821cf950420873d5410821d794c420875d5310821bd98442086f561108219f597320873e54cc821cf553320875e53cc821d754f32086ed65cc821db597320866d65cc821eb95332087ad54cc821dbd4f32087ce53cc821db54f32087cd53cc821d354f32086ed61cc8219fd96320867d658c821cf952320873d548c821d794e320875d538c821bb98a320876e528c821bd98632086f5618c8219fd95320873e544c821cf551320875e534c821d754d320876e524c8219fd94320867d650c821cf950320873d540c821d794c320875d530c821f34c832086f6610c821bd584320876d650c8219b59432087ae540c821eb55032086ee630c821f398c320876f530c821f394c320876d530c821f354c320874d530c821f998432086ed610c821f9584320867e6494421cf992510863e64944219f592510873d64944218f592510867e63944219f58e510876f3294421db0ca510867d65d0421cfd53410873e54d0421cf553410873c54d0421d794f410875d53d0421af597410873d65d04218f597410873f53d0421cf94f410879e53d0421c794f410873d53d0421e754f410871d53d0421cf14f410873e52d0421ebccb41087ac32d0421cf947410867f65904219f59641086bd6490421cf952410873d5490421d794e410875d5390421bb98a41086ed62904219fd95410873f5450421cf951410873d5450421cf151410875e5350421d754d41086bf6550421cfd95410863f6550421cfd4d410873e5350421e794d410871e5350421cf54d410879d5350421c754d410873c5350421cf94941087af3250421eb0c941087b76150421cf945410867f65104219f994410867d65104219f19441086be6410421cf950410873d5410421d794c410875d5310421bb98841086ed62104219f597310873e54cc421cf553310875e53cc421d754f31087cf32cc421ed507310867f658c4219f59631086be648c421af592310873e548c421cf552310875e538c421d754e31086ee628c421bb58a31087cc328c4219fd95310873e544c421cf551310875e534c421d754d31086ef624c421bb18931087cf324c4219fd94310867e650c4219f594310867c650c421af99031086bd640c421cf950310873d540c421d794c310875d530c421bb98831086ed620c421f30c831087b5410c421be98031086f9600c421cf953210873d54c8421d794f210875d53c8421eb95321087ad54c8421bb98f21086ec63c8421dbd4f21087ce53c8421db54f21087cd53c8421d354f21087af41c8421eb50721086be6488421af592210873e5488421cf552210875e5388421d754e21086ed6288421db94a21087b74188421ed50621087b66488421ed59221087b65488421ed55221087d65388421f554e21086f56288421dd94a21087e65288421f9cca21087e432
  | 33 => 0x91540867f63550219f18d540867f60550219f181540873f6555021cfd8d540873e6355021cf58d540873c6355021cf989540873c6255021cf985540873c6155021cf085540873f6055021cf981540873d6055021cf18154086be6415021cf55054086de6315021b758c54086fa6015021be580540867e6415021cf990540863e64150219f98c540875e63150219798c540867d6315021d758c540865d63150219f988540876e62150219f984540877661150219f980540877a60150219e980540867d6015021de58054086796015021af99353086bd64d4c21cf953530873d54d4c21be98353086f960d4c219f993530873e64d4c218f993530867d64d4c21cf593530863d64d4c219f98b530876e62d4c219f987530877661d4c219f983530877a60d4c219e983530867d60d4c21de583530867960d4c219f596530873e5494c21cf552530875f5394c219f992530867d6494c219f982530867d6094c2197596530875f5494c21d7952530879e5494c21c7952530875d5494c21e7552530871d5494c21d715253087cc6294c21d7d92530875e6494c21d7592530875c6494c21d798a530875c6294c21d7986530875c6194c21d7d82530875e6094c21d7582530875c6094c21cf951530873d5454c219fd91530867c6454c21d7d8d530876c6254c219fd81530867c6054c21d7d95530875f5454c21d7951530879e5454c21c7951530875d5454c21e7551530871d5454c21d715153087cc6254c21d7d91530875e6454c21d7591530875c6454c21d7989530875c6254c21d3189530875e6154c21d7185530875c2154c21d7d81530875e6054c21d7581530875c6054c21af99053086bd6414c21cf950530873d5414c21b798c530875d5314c21be98053086f96014c219f990530873e6414c218f990530867d6414c21cf590530863d6414c219f98c530875e6314c219798c530867e6214c21db988530866e6214c219f98453087766114c219f980530877a6014c219e980530867d6014c21de58053086796014c219fd97430867e65d0c219f597430867c65d0c21cf953430873d54d0c21d794f430875d53d0c21bb98b43086ed62d0c21bd98743086f561d0c219fd96430867e6590c219f596430867c6590c21cf952430873d5490c21d794e430875d5390c219fd95430867e6550c219f595430867c6550c21cf951430873d5450c21d794d430875d5350c21bbd8943086ec6250c219fd94430867e6510c219f594430867c6510c21cf950430873d5410c21d794c430875d5310c219f992520867d64948219f98e520867d63948219f597420873e54d0821cf553420875e53d0821d754f420867f65908219f596420873e5490821cf552420875e5390821d754e42086f66190821bd586420867f6550821cf951420873d5450821d794d420875d535082
  | 34 => 0x4875c538c921bb996324876e658c9219b99632486ed638c921f3d4e324876e538c921db14e32487cc538c921d314e32486ee618c921bb582324867c654c921d7d4d324875c534c921bdd8532486f4614c921db195324866c654c921f3d8d32487cf534c921db94d324876c534c921f314d324874c534c921f9d8532486ec614c921f918532486ef604c9219f994324875f530c921d714c32486ee620c921f34c8324867e65d0521cfd53414873c54d0521d7d4f414875c53d0521bb98b41486ed62d0521cfd97414873e65d0521cf597414873c65d0521cfd4f414879f53d0521c7d4f414873e53d0521cf54f414873c53d0521e714f414871c53d0521eb98b41487ad62d0521eb8cb41487ad32d05219f99641486bd6490521d7d4e414875c53905219fd95414867d65505219f195414873f5450521cf151414875f5350521d714d41486ef6250521bb189414873f6550521cf995414873d6550521cf195414873f5350521e7d4d414871f5350521cf94d414873d5350521cf14d414879c5350521c714d41487af6250521eb18941487ae3250521eb4c941487b761505219f99441486be6410521d7d4c414875c53105219f997314875f53cc521d714f31486ee62cc521bb58b31487cd32cc5219f99631486be648c521af592314875f538c521d714e31487ce328c521ed506314867f654c5219f595314867c654c521d7d4d314875c534c521bbd8931486ec624c521f34c931487b5414c5219f99431486be640c521af590314875f530c521d714c31486ee620c521bb58831487ce320c521be98031486f9600c521d7d4f214875c53c8521edd0721487b541c8521f5d4f21487d453c8521f98cb21487e532c8521af99221486bd6488521d7d4e214875c5388521eb99221487ad6488521bbd8e21486ed6388521f3d4e214876e5388521db14e21487cc5388521d314e21487e75188521ebd0621487ad4188521bb582214875f53d4121d714f504867e64d41219f593504867e63d41219f58f504873f41d4121cf50750486de6394121b758e504875f5394121d714e504877b5094121afd9150486bc6454121b7d8d50486dc6354121d7d4d504875c5354121d7d4c504875c5314121de540504867e64141219f590504867e63141219f58c504873f4114121cf50450486de63d5021b758f54086fa60d5021be583540867e63d5021d798f540865e63d50219f58f540875d63d50219758f540867e62d5021db98b540867e61d5021dd987540867e60d5021de983540867a60d50219f583540877960d50219e583540867d6595021cfd52540867e63950219f58e540867e60950219f582540863d6595021cfd8e540873e6395021cf58e540873c6395021cf98a540873c6295021cf986540873c6195021cfd82540873e6095021cf582540873c6095021cfd
  | 35 => 0x565c8621dd59721887b654c8621ed55321886be64d4221af593508873e54d4221cf553508873e5494221cf552508877b50942219f992508867d64942219f98e508867d6394221cfd06508873d4194221cf951508873d54542219fd91508867c64542219fd8d508867c6354221dbcc9508876c3254221cfd05508873d4154221dbc8550886be6414221af590508873e5414221cf55050886de6314221b758c508877950142219f98f544867d63d51219f983544867d60d5121cfd5254486de6395121b758e544867e64951219f98e544875e63951219798e544867d6395121d758e544865d63951219f58a544876d62951219f586544877561951219f982544867d6095121b7d8d54486dc6355121bed8154486f86055121cfd91544867f6355121d7d8d544865f63551219f18d544875c63551219718d544867f6255121dbd89544867f6155121ddd85544867f6055121ded81544867b60551219f181544877860551219e181544867e6515121cf550544873e64151219f98c544867d63151219f980544867d60151219f993534867d64d4d219f983534867d60d4d21d7d53534875e54d4d21d7553534875c54d4d21f3d8b534875f64d4d21d7993534875d64d4d21d7193534875f62d4d21d758b534875f61d4d21d7587534875f60d4d21d7983534875d60d4d21d7183534875f5394d219f992534867d6494d219f98e534865e6394d219f58a534876d6294d219f58653487756194d219f982534867d6094d219fd91534867c6454d21d7d8d534867f6254d21dbd89534866f6254d219fd8553487776154d219fd81534867c6054d219f994534875d5314d219f990534867d6414d21d798c534876d6214d219f980534867d6014d21b7994534875e6514d2197994534875f5414d21d7950534875d5414d21d715053487cd6214d21d7d90534875e6414d21d7590534875c6414d21d7d88534875d6214d21d3588534875f6114d21d7584534875d2114d21d7d80534875e6014d21d7580534875c6014d219fd97434867e65d0d219f597434867c65d0d21d7d4f434875c53d0d219fd96434867e6590d219f596434867c6590d21d7d4e434875c5390d21bb98a43486ed6290d219fd95434867e6550d219f595434867c6550d21d7d4d434875c5350d219fd94434867e6510d219f594434867c6510d21d7d4c434875c5310d21bb98843486ed6210d21bd98443486f56110d219f997424873f54d0921cf153424875f53d0921d714f42486f661d0921bd587424867e6590921cf952424873d5490921d7d4e424875c53909219f195424873f5450921cf151424875f5350921d714d42486f76150921bd185424867e6510921cf950424873d5410921d7d4c424875c53109219f997324875f53cc921d714f32486f661cc921bd587324867e658c921d7d4e32
  | 36 => 0x4e21af593538873e54d4e21cf553538867e64d4e21cf993538863e64d4e219f593538873d64d4e218f593538876d62d4e21dd987538867e60d4e219f583538873e5494e21cf552538875f5394e219f992538867d6494e219f982538867d6094e21cf951538873d5454e219fd91538867c6454e21d7d8d538876f6254e219fd81538867c6054e21af99053886bd6414e21cf950538873d5414e21d754c53886fa6014e21be580538867e6414e21cf990538863e6414e219f590538873d6414e218f590538875e6314e21db58853887766114e219f980538877a6014e219e980538867d6014e21de58053886796014e219fd97438867e65d0e219f597438867c65d0e21cf953438873d54d0e21bb98b43886ed62d0e219fd96438867e6590e219f596438867c6590e21cf952438873d5490e219fd95438867e6550e219f595438867c6550e21cf951438873d5450e21bbd8943886ec6250e219fd94438867e6510e219f594438867c6510e21cf950438873d5410e21bd98443886f56110e21cf953428873d54d0a21bd98742886f561d0a21cf952428873d5490a21cf951428873d5450a21bdd8542886f46150a21cf950428873d5410a21cf953328873d54cca21d794f328875d53cca21bd98732886f561cca21db59732887ae54cca21eb553328876f53cca21f394f328876d53cca21f354f32887e661cca21bb58732887e561cca21cf952328873d548ca21d7d4e328875c538ca21cf951328873d544ca21d794d328875d534ca21bdd8532886f4614ca21cf950328873d540ca21d7d4c328875c530ca21f34c832886ed650ca21db59432887ae540ca21eb55032887ce630ca21dbd4c32887cf530ca21d3d4c328876d530ca21f314c32886ed610ca21cfd53418873e54d0621cf553418873c54d0621af597418873d65d0621cfd4f418873e53d0621cf54f418873c53d0621ebccb41887ac32d0621cf952418873d5490621bb98a41886ed6290621cfd51418873e5450621cf551418873c5450621afd95418873f6550621cfd4d418873e5350621cf54d418873c5350621ebcc941887ac3250621edd85418873e5410621cf55041886ee6210621bb588418873e54cc621cf553318875f53cc621d714f31887cf32cc621af99231886bd648c621cf952318873d548c621d794e318875d538c621bb98a31886ed628c621f30ca31887b5418c621cf951318873d544c621d7d4d318875c534c621bbd8931886ec624c621f3cc931887b5414c621af99031886bd640c621cf950318873d540c621d794c318875d530c621bb98831886ed620c621f30c831886fa600c621be580318873e54c8621cf55321887b741c8621ed50721886ed65c8621db59721887ae54c8621eb55321886ee63c8621bb18f218876f53c8621db54f21887af41c8621eb50721886f
  | 37 => 0xd7d4e53c867e6494f219f59253c876e6294f219f98253c867d6094f219fd9153c867c6454f21d7d8d53c867f6054f219f18153c875d5314f219f99053c867d6414f21d798c53c876e6214f21dd58453c867e6014f219f58053c867f65d0f219f99743c867d65d0f219f19743c86f661d0f21bd58743c867f6590f219f99643c867d6590f219f19643c86ee6290f21bb58a43c867f6550f219f99543c867d6550f219f19543c867f6510f219f99443c867d6510f219f19443c86ee6210f21bb58843c873f54d0b21cf15342c873e5490b21cf55242c86f66190b21bd58642c873f5450b21cf15142c873e5410b21cf55042c86f66110b21bd58442c875f53ccb21d714f32c875e538cb21d754e32c86f6618cb21bd58632c876d658cb21db94e32c87ce538cb21f354e32c876c538cb21bb98632c87e6618cb21f958632c86ed608cb21d7d4d32c875c534cb21bbd9532c876f654cb21f3d8d32c87cf534cb21db94d32c876c534cb21f314d32c874c534cb21bb18532c86ef604cb21d794c32c875d530cb21f34c832c86f6610cb21bd58432c873e54d0721cf55341c86ee62d0721bb58b41c873e65d0721cf59741c873f53d0721cf94f41c873d53d0721cf14f41c87ae62d0721eb58b41c87ae32d0721eb4cb41c873e5450721cf55141c86ef6250721bb18941c873f6550721cf19541c873f5350721cf94d41c873d5350721cf14d41c87af6250721eb18941c87ae3250721eb4c941c87b76150721d794f31c875d53cc721bb98b31c86ed62cc721f34cb31c87b541cc721af99231c86bd648c721d7d4e31c875c538c721f38ca31c875e534c721d754d31c86ef624c721bb18931c87cd324c721af99031c86bd640c721d7d4c31c875c530c721bb98831c86ed620c721f38c831c87b5410c721be98031c86f9600c721b798e50c86dd6394321ded4250c867e64943219f59250c867e6394321d798e50c865e63943219f58e50c875d63943219758e50c873f4194321cf50650c86bf6454321af19150c867f6454321cfd9150c863f64543219f19150c873c64543218f19150c867f63543219f18d50c873f4154321cf50550c877950143219f98f548867d63d5221db58b548877661d52219f983548867d60d5221cfd52548867e63952219f58e548867e60952219f582548873f6395221cf98e548873d6395221cf18e548873f6295221cf58a548873e6195221cf186548873f6095221cf982548873d6095221cf182548873f64552219fd8d548867c63552219fd81548867c6055221cfd95548873f6355221cf98d548873d6355221cf18d548873f6255221cf589548873e6155221cf185548873f6055221cf981548873d6055221cf181548873d5415221cf990548867e63152219f58c548876d6215221dd984548867e60152219f58054886be64d
  | 38 => 0x9310c7ce524c431d7549310c7cd524c431d3549310c6df614c431d7945310c79f414c431f5905310c79d414c431f5505310c795414c431bdd95310c777654c4319dd95310c7b6544c431ed551310c6f7634c431f5d8d310c776534c431f594d310c7d6434c431f550d310c7e7624c431f9189310c7e6524c431f9549310c6be64d4031af593500c73e54d4031cf553500c6ee62d4031bb58b500c76e52d4031db54b500c73e5494031cf552500c76e5294031db54a500c77b50940319f992500c67d64940319f98a500c67d6294031cfd06500c73d4194031ded52500c77a5494031ee952500c73a5494031de552500c7b95494031ce552500c7785494031ded4a500c77a5294031fa94a500c76a5294031de54a500c7e95294031da54a500c7785294031f68ca500c7d83294031eed06500c7b94194031f6cc6500c7f23194031f64c6500c7f13194031ded92500c77a6494031de592500c7786494031de18e500c77b4394031de90e500c7794394031de10e500c77b6294031de98a500c7796294031de18a500c77b4294031de90a500c7794294031de10a500c77b3294031de8ca500c7793294031de0ca500c7786194031ded06500c73b4194031de906500c7794194031ce506500c7784194031decc6500c77a3194031de4c6500c73e5454031cf551500c76e5254031db549500c67f64540319f191500c67f62540319f189500c75e3254031d70c9500c73f4154031cf505500c75f3154031d74c5500c77b6554031ded51500c77a5454031ee951500c73a5454031de551500c7b95454031ce551500c7785454031ded49500c77a5254031fa949500c76a5254031de549500c7e95254031da549500c7785254031f68c9500c7d83254031eed05500c7b94154031f6cc5500c7f23154031f64c5500c7f13154031ded91500c77a6454031de591500c7786454031de98d500c77b4354031de90d500c7794354031de10d500c77b6254031de989500c7796254031de189500c77b4254031de909500c7794254031de109500c77b3254031de8c9500c75a3254031de4c9500c7783254031d60c9500c77a6154031ded05500c73b4154031de905500c7794154031ce505500c7784154031decc5500c75b3154031de8c5500c7793154031d64c5500c7783154031af990500c6bd6414031cf950500c73d5414031bb988500c6ed6214031db948500c76d5214031be980500c77950140319f98f54c867d63d5321db98b54c877561d53219f98354c867d60d5321cfd5254c867e63953219f58e54c867e60953219f58254c873f64553219fd8d54c867c63553219fd8154c867c6055321cf55054c873e64153219f98c54c867d6315321db98854c877561153219f98054c867d60153219f99353c867d64d4f21db98b53c877561d4f219f98353c867d60d4f21
  | 39 => 0xc76c4354831db985520c76c6154831db0c5520c76f6054831db981520c76d6054831db181520c6be6414831af590520c73e5414831cf550520c6ee6214831db548520c6fa6014831be580520c67f65d08319f997420c67d65d0831cf953420c73d54d0831b798f420c6dd63d0831db94b420c76d52d0831bd987420c6f561d08319fd96420c67e65908319f596420c73e5490831cf552420c76e5290831db54a420c67f65508319f595420c67c6550831cf951420c73d5450831b7d8d420c6dc6350831db949420c76d52508319fd94420c67e65108319f594420c73e5410831cf550420c76e5210831db548420c73e54cc831cf553320c75e53cc831db94b320c76d52cc831bd987320c6f561cc8319f596320c73e548c831cf552320c76d528c831b7596320c75d658c83197596320c79e548c831e7552320c6de628c831f394a320c75d528c831f354a320c74d528c831b7586320c67f654c831cf951320c73d544c831d794d320c76e524c831cf950320c73d540c831db948320c76d520c831f34c8320c6f6610c831bd584320c79e540c831e7550320c6de620c831f3988320c7ce520c831d7548320c7cd520c831d3548320c7d6610c831b7584320c7d5610c8319f992510c73e64944318f992510c67d6494431cf592510c63d6494431d78ca510c75c32944319f597410c73f54d0431cf953410c73d54d0431cf153410c76e52d0431db54b410c6bd65d0431cf597410c63d65d0431cf94f410c73e52d0431eb94b410c72e52d0431cf54b410c7ad52d0431cb54b410c79e32d0431e70cb410c73e51d04319fd96410c67d6590431af592410c73e5490431cf552410c6de6390431b758e410c76e5290431db54a410c67f6550431cfd51410c73e5450431cf551410c73c5450431db949410c76d5250431afd95410c73f65504318fd95410c73e5350431cf949410c7ae5250431cb949410c73d5250431eb549410c72d5250431e78c9410c79c3250431edd85410c73e51504319fd94410c67e65104319f594410c67c6510431af990410c73e5410431cf550410c6de6310431b758c410c76e5210431db548410c73e54cc431cf553310c76e52cc431db54b310c79e54cc431e7553310c6de62cc431f394b310c75d52cc431f354b310c74d52cc431e7d07310c79d41cc431af992310c6bd648c431cf952310c73d548c431b758e310c75e538c431db94a310c76d528c431edd06310c7b5418c431ed992310c7b5648c431ed952310c7b5548c431bd58e310c776538c431f594e310c7e6528c431f954a310c7d6328c431f50ca310c67f654c431cf951310c73d544c431bbd89310c6ec624c431db949310c76d524c431edd05310c7b5414c431b7d95310c75f654c43197d95310c79e544c431e7551310c7cf624c431b7189310c7cc624c431b318
  | 40 => 0x5210531dbd4b314c76c52cc531edd07314c7b541cc531f9d4b314c7e452cc531f5ccb314c7d532cc531af992314c6bd648c531dbd4a314c76c528c531e7992314c79d648c531b758a314c7cf528c531d714a314c7cc528c531d314a314c7d7518c531e7d06314c79d418c531b7582314c76f52d4131db14b504c67e64d41319f593504c67e62d41319f58b504c73f41d4131cf507504c6ee6294131bb58a504c76f5294131db14a504c77b5094131afd91504c6bc6454131bbd89504c6ec6254131dbd49504c76c5254131dbd48504c76c5214131de540504c67e64141319f590504c67e62141319f588504c73f4114131cf504504c6ee62d5031bb58b540c6fa60d5031be583540c67e63d5031d798f540c67e62d5031db98b540c66e62d50319f58b540c76d62d50319b58b540c67e61d5031dd987540c67e60d5031de983540c67a60d50319f583540c77960d50319e583540c67d6595031cfd52540c67e62950319f58a540c67e60950319f582540c63d6595031cf98e540c73c6395031cfd8a540c73e6295031cf58a540c73c6295031cf986540c73c6195031cfd82540c73e6095031cf582540c73c6095031cfd91540c67f62550319f189540c67f60550319f181540c73f6555031cf98d540c73c6355031cfd89540c73e6255031cf589540c73c6255031cf985540c73c6155031cf0c5540c73f6055031cf981540c73d6055031cf181540c6be6415031cf550540c6ee6215031bb588540c6fa6015031be580540c67e6415031cf990540c63e64150319f98c540c75e63150319f988540c76e62150319b988540c67d6215031db588540c66d62150319f984540c77661150319f980540c77a60150319e980540c67d6015031de580540c67960150319f992530c67d6494c319f597430c73e54d0c31cf553430c67f6590c319f596430c73e5490c31cf552430c6f66190c31bd586430c67f6550c31cf951430c73d5450c319fd94430c67d6510c31cf950430c73d5410c31bd984430c6f56110c31af993520c6bd64d4831cf953520c73d54d4831be983520c6f960d4831cf952520c73d5494831dbd4a520c67e64948319f592520c67e60948319f582520c76f5494831db952520c7ae5494831cb952520c76d5494831eb552520c72d5494831db152520c7cc6394831dbd92520c76e6494831db592520c76c6494831db18e520c76f4394831db90e520c76d4394831db10e520c76e6194831db186520c76f6094831db982520c76d6094831db182520c73e5454831cf551520c67f64548319f191520c67f60548319f181520c76f6554831dbd51520c76e5454831eb951520c72e5454831db551520c7ad5454831cb551520c76c5454831f318d520c76f6454831db991520c76d6454831db191520c76e6354831dbd0d520c76e4354831db50d520
  | 41 => 0x1319f58a544c76d62951319b58a544c67d6195131dd586544c67e60951319f582544c6ef6255131bb189544c6fb6055131be181544c73f64551319fd8d544c75f63551319fd89544c76f62551319bd89544c67c6255131db189544c66c62551319fd85544c77761551319fd81544c77b60551319ed81544c67c6055131de181544c67860551319f994544c73d5415131cf990544c67e62151319f588544c67e60151319f580544c67e65d0d31cfd53434c73c54d0d31bd987434c6f561d0d319f996434c73e5490d31cf552434c67c6550d31cfd51434c73c5450d31bdd85434c6f46150d319f994434c73e5410d31cf550434c67e64d49319f593524c67e60d49319f583524c76f54d4931db953524c76d54d4931db153524c7cf63d4931dbd93524c76e64d4931db593524c76c64d4931dbd8f524c76f43d4931db90f524c76d43d4931db10f524c76f61d4931db587524c76f60d4931db983524c76d60d4931db183524c76f5294931db548524c67e64149319f590524c67e60149319f580524c6ee6514931db994524c76f5414931db950524c76d5414931db150524c7cd6314931dbd90524c76e6414931db590524c76c6414931dbd8c524c76f4314931db90c524c76d4314931db10c524c76f6114931db584524c76d3114931dbd80524c76e6014931db580524c76c60149319f997424c67d65d09319f197424c76f52d0931db14b424c67e65909319f596424c67c6590931b798e424c6dd6390931dbd4a424c76c52909319fd95424c67e65509319f195424c76f5250931db149424c67e65109319f594424c67c6510931b798c424c6dd6310931dbd48424c76c5210931bd984424c6f561109319f997324c76c52cc931b7997324c75e65cc93197997324c7cf52cc931d714b324c7cc52cc931d314b324c6de61cc931b7583324c6dd638c931dbd4a324c76c528c931bd986324c6f5618c931dbd49324c76c524c931bdd85324c6f4614c931f3d89324c7cf524c931d7149324c7cc524c931d3149324c7d7614c931b7185324c7d4614c931b7d81324c67e650c931b798c324c76f520c931f34c8324c67e65d0531cfd53414c73c54d0531b798f414c6dd63d0531dbd4b414c76c52d0531cfd97414c73e65d0531cf597414c73c65d0531e798f414c79d63d0531cfd4b414c7af52d0531cbd4b414c73c52d0531eb14b414c72c52d0531e7ccb414c79d32d05319f996414c6bd6490531dbd4a414c76c52905319fd95414c67d65505319f195414c73f5450531cf151414c6df6350531b718d414c76f5250531db149414c73f6550531cf995414c73d6550531cf195414c79f6350531e718d414c73f5250531ebd49414c72f5250531cf149414c7ac5250531cb149414c79f3250531e74c9414c7b761505319f994414c6be6410531dbd48414c76c
  | 42 => 0xf186548c73f6095231cf982548c73d6095231cf182548c73f64552319fd89548c67c62552319fd81548c67c6055231cfd95548c73f6355231cf58d548c73f6255231cf989548c73d6255231cf189548c73e6155231cf185548c73f6055231cf981548c73d6055231cf181548c73d5415231cf990548c75d63152319f988548c67d6215231dd984548c67e60152319f580548c73e54d0e31cf553438c6f661d0e31bd587438c73e5490e31cf552438c73e5450e31cf551438c6f76150e31bd185438c73e5410e31cf550438c6be64d4a31af593528c73e54d4a31cf553528c73e5494a31cf552528c76f5294a319f992528c67d6494a319f982528c67d6094a31cf951528c73d5454a319fd91528c67c6454a319fd81528c67c6054a31af990528c6bd6414a31cf950528c73d5414a31db548528c6fa6014a31be580528c67f65d0a319f997428c67d65d0a31cf953428c73d54d0a31b798f428c6dd63d0a319fd96428c67e6590a319f596428c73e5490a31cf552428c67f6550a319f595428c67c6550a31cf951428c73d5450a31b7d8d428c6dc6350a319fd94428c67e6510a319f594428c73e5410a31cf550428c6f66110a31bd584428c73e54cca31cf553328c73e548ca31cf552328c76e528ca31db54a328c6f6618ca31bd586328c79e548ca31e7552328c7ce528ca31d754a328c7cd528ca31f5986328c6dd618ca31f5586328c73e544ca31cf551328c76e524ca31db549328c6f7614ca31bd185328c73e540ca31cf550328c7cd320ca31b7594328c75d650ca31e7950328c79d540ca31f3988328c7cf520ca31d7548328c7cc520ca31b7584328c73f54d0631cf953418c73d54d0631cf153418c6bd65d0631cf597418c73e52d0631cf54b418c79e32d0631e70cb418c73e5490631cf552418c6de6390631b758e418c73f5450631cf951418c73d5450631cf151418c6bf6550631cfd95418c73e5250631cf549418c79e3250631e70c9418c7b76150631cf950418c73d5410631b798c418c6dd6310631cf953318c73d54cc631edd07318c7b541cc631b7597318c75d65cc631e7953318c79d54cc631b798b318c75d52cc631e7d07318c79d41cc631bd597318c77565cc631ed953318c7b554cc631af993508c6bd64d4231cf953508c73d54d4231cf952508c73d5494231ded42508c67e64942319f592508c67e62942319f58a508c73f4194231cf506508c73e5454231cf551508c67f64542319f191508c67f62542319f189508c75e3254231d70c9508c73f4154231cf505508c75f3154231af990508c6bd6414231cf950508c73d5414231bb988508c6ed6214231de540508c67e62d51319f58b544c67e60d51319f583544c73f5495131bb98a544c6ed62951319f992544c67d6395131d758e544c67e6295131db98a544c66e6295
  | 43 => 0x321073e544c841d794d321075d534c841db949321076d524c8419fd94321067e650c8419f594321073e540c841f34c8321073e53d0441cf54f411073e52d0441cf54b41106bd6490441cf95241106f56490441dd95241107b654904419fd95411073e5450441afd95411073f65504418fd95411073e5350441cf54d411073e5250441cf54941106bf6150441cf94541106f76550441ddd9541106776550441bdd9141107b76450441dd95141107b65450441cd951411077b50940419f98e501067d63940419f98a501067d6294041cfd06501073d41940419fd8d501067c63540419fd89501067c6254041cfd0550107764154041cf50550107754154041b798c50106dd6314041bb98850106ed6214041de540501075e63d53319f98b54cc67d62d5331dd58754cc67e60d53319f58354cc73f54953319f98a54cc67d62953319f98254cc67d6095331cfd9154cc67f62553319f18954cc67f60553319f18154cc73d5415331cf99054cc75e63153319f98854cc67d6215331dd58454cc67e60153319f58054cc73f54d0f31cf15343cc73e5490f31cf55243cc6f66190f31bd58643cc73f5450f31cf15143cc73e5410f31cf55043cc6f66110f31bd58443cc76f5294b319f99252cc67d6494b319f98252cc67d6094b319fd9152cc67c6454b319fd8152cc67c6054b31db54852cc67f65d0b319f99742cc67d65d0b31bd98742cc6f561d0b319fd9642cc67e6590b319f59642cc6de6390b31b758e42cc67f6550b319f59542cc67c6550b319fd9442cc67e6510b319f59442cc6de6310b31b758c42cc76e52ccb31db54b32cc6f661ccb31bd58732cc75e52ccb31f394b32cc7cd52ccb31b798732cc7d661ccb31f558732cc6dd60ccb31b7d9532cc75f654cb31f3d8932cc7cf524cb31d794932cc7cc524cb31b718532cc6df604cb31db94832cc76d520cb31f34c832cc6f6610cb31bd58432cc73e54d0731cf55341cc6de63d0731b758f41cc73e65d0731cf59741cc79e63d0731e758f41cc73e52d0731cf54b41cc79f32d0731e74cb41cc73e5450731cf55141cc6df6350731b718d41cc73f6550731cf19541cc79f6350731e718d41cc73e5250731cf54941cc79f3250731e74c941cc7b76150731bb98a50cc6ed6294331ded4250cc67e64943319f59250cc67e6294331db98a50cc66e62943319f58a50cc76d62943319b58a50cc73f4194331cf50650cc6bf6454331af19150cc67f6454331cfd9150cc63f64543319f19150cc73c64543318f19150cc67f62543319f18950cc73f4154331cf50550cc7795014331d758f548c67e62d52319f58b548c77661d52319f983548c67d60d5231cfd52548c67e62952319f58a548c67e60952319f582548c73f6395231cf58e548c73f6295231cf98a548c73d6295231cf18a548c73e6195231c
  | 44 => 0x79f328c941ebcca32506be618c941af58632506be608c941af58232506bf654c941af99532506bd654c941af19532507af324c941e78c932506bf614c941edd8532506b7614c941af18532507b4614c941ad18532506bf604c941af18132506bf650c941af99432506bd650c941af19432506be630c941e7d4c325079c530c941af98832507af520c941eb148325079f320c941eb8c8325079d320c941eb4c8325078d320c941af98432507b6610c941ad98432506bd610c941ed58432506b5610c941af98032506bd600c941af98f51506bd63d4541cfd4f515073c53d4541af98b51506bd62d4541cfd4b515073c52d4541af98351506bd60d4541edd8f51507b663d4541ed58f51507b463d4541edd4f51507b653d4541ed54f51507b453d4541edd8b51507b662d4541ed58b51507b462d4541edd4b51507b652d4541ed54b51507b452d4541edccb51507b632d4541ed4cb51507b432d4541edd8351507b660d4541ed58351506b560d4541ed18351506be63d4141af58f50506be62d4141af58b50507b761d4141cfd4750507b751d4141af98e50506bd6394141cf94e505073c5394141af98a50506bd6294141cf94a505073c5294141ed58650507b75194141af982505073f5094141eed4250506bf6354141e7d8d505069f6354141af18d505079c6354141a718d50506bf6254141ebd8950506af6254141af18950507ac6254141ab18950507b76154141edd4550507bb5054141cf94150506be6514141af98c505079e6314141a798c50506bd6314141e758c505069d6314141cf94c505073c5314141af98850507ae6214141ab98850506bd6214141eb58850506ad6214141cf948505073c5214141ed584505073f5114141edd44505073f5014141ee940505073d5014141ee54050507395014141cf98e541073d6395041cf98a541073d6295041cf982541073d6095041d7d4e531067e6294c419f58a531067e6094c419f582531067f6254c419f189531067f6054c419f181531075d5314c41bb98853106ed6214c41be98053106f96014c41cf953431075e53d0c41d754f43106f661d0c41bd587431067d6590c41cf952431067f6550c41cf951431073e5410c41d794c431075d5310c41bd98443106f56110c41dbd4a521067e63948419f58e521067e60948419f582521067f63548419f18d521067f60548419f18152106de6314841b758c521076d5214841be98052106f96014841cf953421076e52d0841db54b42106f661d0841bd587421067d6590841cf952421067f6550841cf951421073e5410841db948421076d5210841bd98442106f561108419fd97321067e65cc8419f597321073e54cc841d794f321075d53cc8419fd96321067e658c8419f596321073e548c841db94a321076d528c8419fd95321067d654c8419f195
  | 45 => 0x190941ed58642506be6090941af582425076f5250941db14942506f76150941bd18542506bf6350941af18d42507af6250941ebd49425073c5250941eb14942507b76150941af18542507b46150941afd8142506bc60509419f99442506be6410941af994425073e6510941af98c42506bd6310941af98842507ae6210941cfd4842506be6110941af98042506bd60109419f997325067d65cc9419f19732506bf64cc941af99332506bd64cc941af193325076f52cc941db14b325067e658c9419f596325067c658c941afd9232506be648c941af59232506bc648c941d7d4e325075c538c9419fd95325067e654c9419f19532506bf644c941af99132506bd644c941af19132506f7614c941bd185325067e650c9419f594325067c650c941afd9032506be640c941af59032506bc640c941d7d4c325075c530c941dbd48325076c520c941f34c832506f6610c941bd58432507b743d0541ed90f41507b543d0541ed10f41507b742d0541ed90b41507b542d0541ed10b41506f560d0541af98e41506bd6390541af98a41506bd6290541edd4641506be6090541af582415067e63d41419f58f505067e62d41419f58b505077b5094141b7d8d50506dc6354141bbd8950506ec6254141b798c50506dd6314141bb98850506ed6214141de540505067e6314141d798c505065e63141419f58c505075d63141419758c505073e4314141cf10c505067e6214141db988505066e62141419f588505076d62141419b588505073e4214141cf10850506be62d4d41af58b53506be60d4d41af58353506be6394d41cfd4e535079f5394d41af98a53506bd6294d41af58653507b56194d41ad58653506be6094d41af582535079f5354d41cf94d53506bf6254d41ebd8953506af6254d41af18953507ac6254d41ab18953506bf6154d41edd8553506b76154d41afd8153507bb6054d41aed8153506bc6054d41ee18153506b86054d41af994535073f5314d41e794c535073d5314d41e754c53506be6214d41af58853506be6014d41af58053506be63d4941af58f52506be60d4941af58352506be6394941af58e52506be6294941cfd4a52507af5294941af58652507b56194941ad58652506be6094941af58252506bf6354941e7d8d525069f6354941af18d525079c6354941a718d52507af5254941cf94952506bf6154941edd8552506b76154941afd8152507bb6054941aed8152506bc6054941ee18152506b86054941af99452506be6314941af58c525073f5214941eb948525073d5214941eb54852506be6014941af58052506bf65cc941af99732506bd65cc941af19732507af52cc941eb14b32506be61cc941af58732506be60cc941af58332506bf658c941af99632506bd658c941af19632506bd638c941e7d4e325079c538c941af98a3250
  | 46 => 0x41a798c50d06bd6314341e758c50d069d6314341cf94c50d073c5314341af98850d07ae6214341ab98850d06bd6214341eb58850d06ad6214341cf94850d073c5214341ed58450d073f5014341ee94050d073d5014341ee54050d07395014341d7d4e539067e6294e419f58a539067e6094e419f582539067f6254e419f189539067f6054e419f181539075d5314e41bb98853906ed6214e41be98053906f96014e41d794e439075d5390e41bd98643906f56190e41d794d439075d5350e41bdd8543906f46150e41dbd4a529067e6394a419f58e529067e6094a419f582529067f6354a419f18d529067f6054a419f18152906de6314a41b758c529076d5214a41be98052906f96014a41db94a429076d5290a41bd98642906f56190a41db949429076d5250a41bdd8542906f46150a419fd97329067e65cca419f597329075e53cca41d754f329067f658ca419f996329067d658ca41db94a329076d528ca419fd95329067d654ca419f195329075e534ca41d754d329076e524ca41db54932906f7614ca41bd185329067f650ca419f994329067d650ca41f34c832906f6610ca41bd58432906bd65d0641cf597419073e53d0641cf54f419073e52d0641cf54b41906f565d0641dd59741906f560d0641ded42509067e63942419f58e509067e62942419f58a509073f41942419fd8d509067c63542419fd89509067c6254241cfd0550906de6314241b758c50906ee6214241bb588509077950142419f98b535067d62d4d419f983535067d60d4d41d7d4e53506ef6254d41bb18953506fb6054d41be181535075d5314d419f988535067d6214d419f980535067d6014d419f99743506be65d0d41cf997435073c53d0d41af98b43506bd62d0d41af98743506be60d0d41af58343506bd6490d41d7d4e435075c5390d41bd98643506f56190d41af98e435073f5390d41e7d4e435079c5390d41af98a43506bd6290d41af98643507b66190d41ed58643506be6090d41af582435075f5350d41d714d43506f76150d41bd185435079f6350d41e7d4d435073c5350d41e714d43506bf6250d41af18943507b76150d41af18543507b46150d41afd8143506bc6050d419f99443506be6410d41af994435073e6510d41af98c435079e6310d41cfd4c43506be6210d41af58843506be6110d41af98043506bd6010d419f98f525067d63d49419f983525067d60d4941dbd4a52506df6354941b718d52506fb6054941be181525076d52149419f98c525067d63149419f980525067d60149419f99742506be65d0941cf99742506be63d0941af58f425073c52d0941af98742506be60d0941af58342506bd6490941dbd4a425076c5290941bd98642506f56190941af98e42506bd6390941af98a425073f5290941ebd4a42507ac5290941af98642507b66
  | 47 => 0x18d42d07af6250b41cf94942d06bc6150b41afd8142d06bc6050b41db94842d076d5210b41bd98442d06f56110b41af98c42d06bd6310b41eb98842d07ae5210b41cf54842d07ad5210b41af98442d07b66110b41ed58442d06be6010b41af58042d067f65ccb419f99732d067d65ccb41afd9332d06be64ccb41af59332d06bc64ccb41db94b32d076d52ccb419fd9632d067e658cb419f59632d06bf648cb41af99232d06bd648cb41af19232d075e538cb41d754e32d067f654cb419f59532d067c654cb41afd9132d06be644cb41af59132d06bc644cb419fd9432d067e650cb419f59432d06bf640cb41af99032d06bd640cb41af19032d075e530cb41d754c32d076e520cb41db54832d07cd320cb41ded4250d067e63943419f58e50d073e4394341cf10e50d067e62943419f58a50d073e4294341cf10a50d067f63543419f18d50d067f62543419f18950d06de6314341b758c50d06ee6214341bb58850d07795014341af98b53d07ae62d4f41ab98b53d06bd62d4f41eb58b53d06ad62d4f41af58753d07b561d4f41ad58753d06be60d4f41af58353d073f5394f41e7d4e53d06be6294f41af58a53d06be6094f41af58253d079f5354f41cf94d53d06bf6254f41af18953d06bf6054f41af18153d073f5314f41e794c53d073d5314f41e754c53d06be6214f41af58853d06bd6114f41ed58453d06b56114f41af98053d06bd6014f41af98f52d079e63d4b41a798f52d06bd63d4b41e758f52d069d63d4b41af58752d07b561d4b41ad58752d06be60d4b41af58352d06be6394b41af58e52d073f5294b41ebd4a52d06be6094b41af58252d06bf6354b41af18d52d07af5254b41cf94952d06bf6054b41af18152d06be6314b41af58c52d073f5214b41eb94852d073d5214b41eb54852d06bd6114b41ed58452d06b56114b41af98052d06bd6014b41afd9732d06be65ccb41af59732d06bc65ccb41eb94b32d07ad52ccb41af98732d06bd61ccb41af98332d06bd60ccb41afd9632d06be658cb41af59632d06bc658cb41e794e32d079d538cb41e7cca32d07af328cb41af98632d06bd618cb41af98232d06bd608cb41afd9532d06be654cb41af59532d06bc654cb41ebcc932d079e324cb41afd8532d06bc614cb41afd8132d06bc604cb41afd9432d06be650cb41af59432d06bc650cb41e794c32d079d530cb41eb94832d07ad520cb41e7cc832d07ae320cb41e74c832d07ad320cb41e34c832d06be610cb41af58432d06be600cb41af58032d06be63d4341af58f50d06be62d4341af58b50d07b561d4341af98e50d06bd6394341cf94e50d073c5394341af98a50d06bd6294341cf94a50d073c5294341cfd4250d07bb5094341afd8d50d06bc6354341afd8950d06bc6254341eed4150d073e5054341af98c50d079e63143
  | 48 => 0x20cade6390832b758e420ca7f65508329fd94420ca7e65108329f594420ca7c6510832cf950420cb3d5410832b798c420cadd6310832b7987320cadd60cc832b758e320cb5e538c832bb58e320cacd638c832db94e320cbce538c832bb986320caed608c8329fd95320cadf654c832d7d95320ca5f654c832b7d89320cb5e524c832f3d09320cbce424c832f3509320cbcc424c832b7185320cadf604c832bbd95320cb6f654c8329bd95320caef634c832f3d8d320cb6e534c832f394d320cbcf434c832f390d320cbcd434c832f310d320caec614c832bbd81320cbcf654c832b3d95320cb4f654c832f3d91320cbce644c832f3591320cbcc644c832f3d51320cbce544c832f3551320cbcc544c832f3d85320cbce614c832f3585320cbcc614c832b3185320cbcf604c832b3d81320cbce604c832f3581320cbcc604c832f34cb510cabe6494432af592510cbcd3294432ddd46510ca7e6494432cf992510ca3e64944329f592510cb3d64944328f592510ca7e60944329f582510cbcd32544329fd91510ca7c6454432d7cc9510cb6e3254432d74c9510cb6d3254432d34c9510ca7f60544329f181510cabe6414432af590510cbcd3214432dd544510cafa6014432be580510cbcd32d4032f34ca500cb7b50940329f992500ca7d64940329f986500ca7d6194032afd91500cabc6454032f34c9500ca7f6454032cfd91500ca3f64540329f191500cb3c64540328f191500ca7f61540329f185500cabe6414032af590500cbcd3214032bd984500caf56114032de540500caee62d4f41bb58b53d075f5394f419f98a53d067d6294f419f98253d067d6094f419fd8953d067c6254f419fd8153d067c6054f41d754c53d075e53d0f41d754f43d06f661d0f41bd58743d073e53d0f41e794f43d079d53d0f41af98b43d06bd62d0f41af98743d07b661d0f41ed58743d06be60d0f41af58343d06bd6590f41cf59643d073d5390f41af98a43d06bd6290f41af98643d06be6090f41af58243d06bf6550f41cfd9543d079f6350f41cf94d43d06bf6250f41af18943d06bc6150f41afd8143d06bc6050f41d794c43d075d5310f41bd98443d06f56110f41e798c43d079e5310f41cf54c43d079d5310f41af98843d06bd6210f41af98443d07b66110f41ed58443d06be6010f41af58043d06de63d4b41b758f52d076f5294b419f98e52d067d6394b419f98252d067d6094b419fd8d52d067c6354b419fd8152d067c6054b41db54852d076e52d0b41db54b42d06f661d0b41bd58742d06be63d0b41af58f42d073e52d0b41eb94b42d07ad52d0b41af98742d07b661d0b41ed58742d06be60d0b41af58342d06bd6590b41cf59642d06be6390b41af58e42d073d5290b41af98642d06be6090b41af58242d06bf6550b41cfd9542d06bf6350b41af
  | 49 => 0xdd65cca32d7597328cade61cca32b7583328caed65cca32db597328caed61cca32af992518cabd6494632ddd46518ca7e6494632cf992518ca3e64946329f592518cb3d64946328f592518cb6f32946329f982518ca7d60946329fd91518ca7c6454632d7cc9518ca7f60546329f181518cabe6414632af590518cb755114632be980518caf96014632af993508cabd64d4232ded42508ca7e64942329f592508ca7e61942329f586508ca7f64542329f191508cb6f32542329fd85508ca7c6154232de540508ca7e61d51329f587544ca7e60d51329f583544cb3f5495132bd986544caf561951329f992544ca7d6395132d758e544ca7d6295132db58a544ca7e6195132dd986544ca7661951329f586544cb7561951329d586544ca7e60951329f582544cb3f64551329fd8d544cb5f63551329fd89544cb6f62551329fd85544ca7c61551329fd81544ca7c60551329f994544cb3d5415132cf990544ca7e61151329f584544ca7e60151329f580544ca7e65d0d32cfd53434cb3c54d0d32bb98b434caed62d0d329f996434ca7c6550d32cfd51434cb3c5450d32bbd89434caec6250d329f994434cb9d4310d329f997424cb3f54d0932cf153424cade63d0932b758f424ca7e65909329fd95424ca7d65509329f195424cb3f5450932cf151424cadf6350932b718d424ca7e6510932eb508424caed61cc932f3d4a324cadd618c9329f993514ca7d64d45329f983514ca7d60d4532af992514cabd6494532ddd46514cabe6414532af590514cb755114532be980514caf960145329f990514cb3e64145328f990514ca7d6414532cf590514ca3d6414532dbcc8514cb5e32145329f980514cb7a60145329e980514ca7d6014532de580514ca7960145329f993504ca7d64d4132dbccb504cb5e32d41329f987504ca7d61d4132ded42504cabf6454132af191504caf76154132bd185504cb7950141329f990504ca7d64141329f984504ca7d61141329f98f540cb5e63d50329f98b540cb6e62d50329f987540ca7d61d50329f983540ca7d60d50329f596540cb3f54950329f986540ca7d61950329f982540ca7d6095032cfd91540ca7f61550329f185540ca7f60550329f181540cb3d5415032bd984540caf56115032be980540caf960150329f990540cb3e64150329f98c540cb5e63150329f988540cb6e62150329f984540cb7661150329d984540ca7d6115032dd584540ca7561150329f980540cb7a60150329e980540ca7d6015032de580540ca7960150329f992530ca7d6494c329f597430ca7f6590c329f596430cb3e5490c32cf552430caee6290c32bb58a430ca7f6550c329fd94430ca7d6510c32cf950430cb3d5410c32bb988430caed6210c329f992520ca7d64948329f597420ca7f65908329f596420cb3e5490832cf5524
  | 50 => 0x94142b758e5050b7b5094142de5405050a7e63141429f58c5050b3e42141429f9845050a7d6114142d7d4e5310a7e6194c429f5865310a7e6094c429f5825310a7f6154c429f1855310a7f6054c429f1815310b5d5314c42bd9845310af56114c42be9805310af96014c42d794f4310b5d53d0c42bb98b4310aed62d0c429f5964310a7f6550c42d794c4310b5d5310c42bb9884310aed6210c42af5874210abe60d0842af5924210b3e5490842bb5924210b6e5490842eb9524210a7f6550842afd954210b3f65508428fd954210abf6250842cf9494210abf6150842af1814210aef6550842dbd954210a6f6550842bbd914210baf6450842db9514210bae5450842ebd0d4210bad4350842ddd465110a7e63944429f58e5110a7e60944429f5825110b3e64544429fd8d5110a7c6354442cfd095110b3d42544429fd815110a7c6054442b798c5110add6314442dd5445110afa6014442be5805110b7b50940429f98e5010a7d63940429f9865010a7d61940429fd8d5010a7c6354042db9095010b6d42540429fd855010a7c6154042b798c5010add6314042bd9845010af56114042de5405010afa60d5332be58354ccb5e63d5332db58b54cca7e61d53329f58754cca7e60d5332de98354cca7a60d53329f58354ccb7960d53329e58354ccb3f54953329f98654cca7d61953329f98254cca7d6095332cfd9154cca7f61553329f18554cca7f60553329f18154ccb3d5415332cf99054ccb5e6315332db58854cca7e61153329f58454cca7e60153329f58054ccb3e5490f32cf55243ccaee6290f32bb58a43ccb3e5410f32cf55043ccb9d4310f32bb98843ccaed6210f32cf95342ccb3d54d0b32b798f42ccadd63d0b32cf95142ccb3d5450b32b7d8d42ccadc6350b32af99251ccabd6494732ddd4651cca7e6494732cf99251cca3e64947329f59251ccb3d64947328f59251cca7e60947329f58251cca7f64547329f19151cca7f60547329f18151ccabe6414732af59051ccb755114732be98051ccaf96014732af99350ccabd64d4332ded4250cca7e64943329f59250cca7e61943329f58650cca7f64543329f19150cca7f61543329f18550ccb795014332be983548caf960d5232d758f548cb6e62d52329f987548ca7d61d52329f983548cb7a60d52329e983548ca7d60d5232de583548ca7960d5232cfd52548ca7e61952329f586548ca7e60952329f582548cb3f64552329fd85548ca7c61552329fd81548ca7c6055232cf550548cb3e6415232d758c548cb6e62152329f984548ca7d61152329f980548ca7d6015232cf953438cb3d54d0e32bb98b438caed62d0e32cf951438cb3d5450e32bbd89438caec6250e32cf952428cb3d5490a32b798e428cadd6390a32cf950428cb3d5410a32b798c428cadd6310a32eb508428ca
  | 51 => 0x3cfd954310e3f6550c43afd8d4310f3e5350c43afd854310ebc6050c43b7d954310f5f6550c4397d954310edf6450c43e7d914310f5e5450c43e79514310f6f52948439f9865210e7d61948439f9825210e7d60948439fd855210e7c61548439fd815210e7c6054843db5485210ef66114843bd5845210efa6014843be5805210f7751944439f98a5110e7d62944439f9825110e7d6094443cf9915110f3f4354443cf50d5110e7f62544439f1895110e7f60544439f1815110eee6214443bb5885110f755114443be9805110ef96014443ded425010e7e62940439f58a5010e7e61940439f5865010f5e4354043d750d5010e7f62540439f1895010e7f61540439f1855010eee6214043bb5885010ef66114043bd5845010f795014043bd98753d0af561d4f42d7d4e53d0a7e6194f429f58653d0a7e6094f429f58253d0a7f6154f429f18553d0a7f6054f429f18153d0b5d5314f42d794f43d0b5d53d0f42bb98b43d0aed62d0f42d794c43d0b5d5310f42e750c43d0aee6210f42bb58843d0ade63d4742b758f51d0b7751947429f98e51d0a7d63947429f98251d0a7d6094742cf99151d0a7f63547429f18d51d0a7f60547429f18151d0b755114742ded4250d0a7e63943429f58e50d0a7e61943429f58650d0a7f63543429f18d50d0a7f61543429f18550d0ade6314342b758c50d0af66114342bd58450d0b795014342be9835390af960d4e42d7d4e5390a7e6194e429f5865390a7e6094e429f5825390a7f6154e429f1855390a7f6054e429f1815390b5d5314e42d794e4390b5d5390e42bb98a4390aed6290e42d794d4390b5d5350e42bbd894390aec6250e42af5974290b3d65d0a42af5874290abe60d0a42bb5974290b6d65d0a42bb5834290b7751946429f98e5190a7d63946429f9825190a7d6094642cf5915190a7f63546429f18d5190b3f42546429fd815190a7c6054642b798c5190add6314642dd5445190afa6014642be5805190ade63d4242b758f5090ade6394242b758e5090b7b50942429f98e5090b5e63942429798e5090a7d6394242d758e5090a5d63942429f9865090a7d61942429fd8d5090a7c63542429fd855090a7c6154242de5405090a7e61d4d429f5875350a7e60d4d429f5835350b5f5394d42be9825350af96094d42d754c5350a7e6114d429f5845350a7e6014d429f5805350a7e65d0d42d7d4e4350b5c5390d42bb98a4350aed6290d42d7d4d4350b5c5350d42bbd894350aec6250d429f9944350b9d4310d42bb5834250baf5290942af5864250b3f64d45429f98f5150a7d63d4542cf90b5150a7e60d45429f5835150b775194542b7d8d5150adc6354542bed815150af86054542dd5445150a7e63145429f58c5150a7e60145429f5805150a7e63d41429f58f5050a7e61d41429f5875050ade63
  | 52 => 0x50002000400000030000000000b000a0006000800080010000000c0040000000000140000001000a000400000050000000000000000004000000080000008001800080080000001c00900050018000000080010006000c0000000000600280020000000e0000001800b000000080000000000a00240020007000a00000000000000200080018000000e00040018000000000000010000000000180000000000000000000005000600180000000001200000008004000000040000000000800040010000000a001000000010000000000380010006002c0000003000400040000001000800040008001001800000000005000000200028000000200000008008000c000c00000040002000c00080000004000000000010002000400180000020001c0018000000000000020000000a00040000009000e001800080010002000000000030002000c003800000000002f661d4b43bd58752d0f6f5294b439f98652d0e7d6194b439f98252d0e7d6094b439fd8552d0e7c6154b439fd8152d0e7c6054b43db54852d0eee62d4743bb58b51d0f7751947439f98a51d0e7d62947439f98251d0e7d6094743cf99151d0e7f62547439f18951d0e7f60547439f18151d0f755114743ded4250d0e7e62943439f58a50d0e7e61943439f58650d0e7f62543439f18950d0e7f61543439f18550d0eee6214343bb58850d0ef66114343bd58450d0f795014343af5974390f3d65d0e43af5874390ebe60d0e43b75974390f5d65d0e43b75834390efa60d4a43be5835290f6f5294a439f9865290e7d6194a439f9825290e7d6094a439fd855290e7c6154a439fd815290e7c6054a43db5485290f7751946439f98a5190e7d62946439f9825190e7d6094643cf5915190f3f43546439fd895190e7c62546439fd815190e7c6054643bb9885190eed6214643dd5445190efa6014643be5805190eee62d4243bb58b5090eee6294243bb58a5090f7b50942439f98a5090f6e62942439b98a5090e7d6294243db58a5090e6d62942439f9865090e7d61942439fd895090e7c62542439fd855090e7c6154243de5405090edd60d0d43e7d4e4350ebd6190d439f9875250e7d61d49439f9835250e7d60d4943dbd4a5250efa6094943be5825250f6d52149439f9845250e7d61149439f9805250e7d6014943cfd935150f3e43d45439f98b5150e7d62d45439f9835150e7d60d4543ddd465150eef6254543bb1895150efb6054543be1815150f7551145439f9885150e7d62145439f9805150e7d60145439f98b5050e7d62d41439f9875050e7d61d4143bb98a5050eed6294143ded425050f795014143cf90c5050e7e62141439f5885050e7e61141439f5845050ebd61d0c43af9834310ebd6490c43cf9524310edd6490c43d79524310f9e5490c439fd954310ebf6550c4
  | 53 => 0x6000c0030000000000040020000000c002400000060000002c0060011000000040008002001600100028003000000200020001000400240028000001c000000100060010000c00080070000000000000040000000000300050006001c00500000004001c000000100020008000000000040008004000100280008005800000000040000800100040010003800000020008000801100020000006000200000004001000200020014001800100020000000000200040024000000100020000006800100000010002800500220004001000000000014001000b000200000048002001000240028002000000080000000000c000800280000004000c0000006000200000008000000200000008000000000440000002000000000008004000000040008000002600000000002001000000000000000200000010000000200000000019000c00000028000000000040038000000400140000001000a0000008800800080000000000400000000000000300000000002000300080000000000600000000001000300000018000000000000000001800600080000004800200040008004000f0006000000080000000006000000010000000400080140006001800080110002000c0010007000000000000003000000000000000000600140000009000400000008000000c00140000002000000080000006000000000000003000000000008004001800600000009001e00040008000000200000000001003000000008002000400000020000000000080050007000000080010004000000100000000000000000030001000000000000000000a002c0010001000200440000008001400140008009000400080020000000800000020001000800000008000000e000c003000a000a0004002800200000000001800e0004000800680050000000c00300050006000400080000000000400900020004000400000000000000c00000010002000c0008000004000000060004001400000010000000a00000020000000000240038006000600440000000000400000008000000400040000009000000040000001000200100018002000000200008000000c0000000000100000020000000000020060000000000020004002800f0002000000100040000001c00200010000000000180020000000000000000002001000000000026003c00200020018001400000020002000c00180000004008c00000290000001c00280000000000000000010000001000180030000001000300010000001400100010004000c001000200000000001000000060024001800000000008005800000020000000000100140000002800d000a0000001800000000000001000000000000000000000080000001000000040000001001a00000014000800000000040000000400040004001
  | 54 => 0x80020000000c0040000000000040038000000000040020000000a000c0010000000a00080068001001c001800000060004001c000000000040034000000100000004002800900040000001000000080014000000200120008000000600080008002800e000000040010003002400040020007000000000038003000000000040007000c000000000010000000c00180020000000000080000012001000300010006003c0000001000200180000004000400000008000001400000020000001c000000000020010001400100070004000c00080000004000800100030000000000000000000000000000100002002400300020008000c00000000004000000f80010000000000200040000000400200000000000000000050006000c0000006000000180000007000400080008000001e00200008003000600300110009000200000010000000c000c000000b000200040018000000000000008000000a004000300000002000000180000002001400080000002000000600000012000000000070000000c00380000002000c00100020004000c002000500020000000000700000004000000a00020004000800a0000003400000000000001c001800000000008002000f0004000000380010004002c0018003000200000058000000400000000002000000140010000000c000400080010010006000000020004000000200030016000000180050002000400280000004000c0000002000200040030000001600080030000000a00000020005000000000008005000a00000030001000000040038003000400f000000000002001000000060012000c00000000000002c0000004000200100000000000000000010002000200140000000000200040000009000000000000001000000000000000000000140040001001c0004000000000120004002000a00000000000000f000400200018000000000080018004000400180000009000a00180000001003c000000480070002000000000000000008c00200040002001400400010002000800000080002000000980010004000400080060008001000400080016000000380020014000400180060000000000600020000001800300000006000400100030002000c00100000002000c00000000004000000380010000001800000000000000000100030004001000500010010000000000030002000000500000002000000180010008002c0000005000a00000010013000200000008000000200200048010000000000008003000600000000000000a0004001000600000000001000100000000000801c000000000000005000000100008001000000140008012000000140040000000200000018000000800080008002000000000020002000000640000001000000040000001000a00040030000001
  | 55 => 0x800000000000000600a000000010000000c001000800040010002800400000004000800000020050000000400060018006800a000400080030002000e00580000006000c00040008000000000040008007000a00000000004000000000020000001800180018003000400000000001000000080000004000000240000001000000200010004000000380008004002000100048002000600140050008000000040000000000000100008001000000240040003000000000010000000400040020012000000040000000000000100020002000e000000100090000000000080000008000000000000004000400100000008000000600010000000000100000000003400080030006001000080000004000800080030030000000080030014000c002000f000e0008006000100000000000800b0004000400200010002004400000000004000400180080046000c00000010010001c00300010000000000100020000003800400080008001c00180020010000800000000000001400500000000000800600000000000000080000000003400400000002000000180040000000c000000a000200000000018001a000c00080000004002000380000004001000200020002000c0000001000a000000200000002000000200000000000000000000006000800080000008000800200010004000000180010000000000a000000080004000000a0000002800080000000000c0078001000a000400000030000001400080060000000c00280020000000c004000000000004002800d000000000038004001000380018009000a002800200010006000400000010000000c0000000000000040048000001200100008006000800180018002000a00040020000000000100008000000e000000200010000000000000040002000000000020000001400480060004000000080000002003000000000006000800100020000000000180030002001400a8009000e00000000000000c00000020000000000040018000005a0024004000c0000000400080010000004400180020000000c00000000004000000100000002000800300000006000000800040006000400400000002000000000000032000c0000001000200000040001000200000020001000000040008001000000300000000001200080008000000000140008000001c00140000001000000000000000000200040000003000a00080010001000a00040000000000200000038000000000040008004000a00040040000000600140000000000000000008016000000040000001000c000c00080000002001800180010008000400000000002000400180020002002c0028003000600040000000000e000000080000006001c001800e0000001800000140000000800080000000001c00280030004000800
  | 56 => 0x8001200080018005001a00040000007000e000800000040000000000000000000001000200030000000000000000002001000180040002000000580000000000400000000006000000380000000000000300010002000800000080000000400780080004001c0000004000c000000280000000001000200000006000000000000000000000680000002000000180000004000400000070024001400180000014000000200000000001000680000004000400180030000001c00000040008000000000010004000000b800c0004000c00200030000000c002800200060008000000000000000000000000000000001800000060004000800000160024000800300040008000000000000010000800200040008001000300060000000800600120004000000e000000040068002000200140010000000a003400280080008001c0018000000200080020000000000180000002000000180010000001200200000000000c0008000000b000000000000001000400100008000000600000008000000c000400000020004001400000000004000000500000006000c002000100120008009000500000000001000200040000000000300000004000000f0000000400000020002000c00000010000001000e0004000200040000001001c00000058002000000080048006000800100000000000a000c0018000001c001000280000000000c0020000005800000000002000000000010001000000000078004000000100098000000c000400000000004000c0020003000000000010000000000000000000001a0000002800b0000000000080010004000400000000000000000080000000000000000000002000400400010002000400080040000000400280040004001000780050000002c0048003000600000000002000000200000001000c0000001000f000a000000180000004002c00600000000002400000010016001800080000002003000280010000001400e800b000000000020001001c001000100010002001000100040000000800300010004000800180000022002c00000050000000400000010000002400000000000002000100100000000400000010004000800500000002000c000000000040004000800000080004001800200400004000800b000000040038001000000200000000000800280010007000000000008004000000000058000000200000000000000c000000000020004000800100000000002c0020002000400080008000000e0004000000000040010003000500000000001000a001e000000900000002000c0018005000a00000088000000c000000100000002000c000000500000000002800300000008001000000000000000800000040000000000000020024001000000000040002000100040004000800900
  | 57 => 0x5c00000030016001800000000008000000380000034001000180000004000c0020003001800000018001000000000000006000000040000003000000400030000000000d000380010002000800100000006000800800010008002000000000002000800280150002000000280010000000800180040004000000180020000002c00100070000000000080010002000400080030002003400000000000000400000000000000400000010012001000000170034000400700010004000400000030000000c00380020002000000280020000000000180070000001c0070000000000040008009003c00080000002000200100008002000000000018005000000080020001000600280000000000000000040000000000000008018000c000c0028000000200140000000000000080008001001e00180000007000400180008004001c0000000800c0000001400800050000001800600020000000800100000000000000080000004000800080070010000000800010008000000180010000000c00580050000001000080000000000c000000000000000004800000040000002000600060000000800f0000002400000060006001000000000002008400400070008000c0008000000000040000003000200040000000000e000400000020000000400600030000000000080070002002c00080000004000000780010014001400600050000000400000000000000c002800000020004001000000020008000000000000000000000300080008002000000040040001800000060048001800a000000040000000001000040028000000600000020000000e000c0010001000000000000006001a0028000000d0006000000000000008005000580000000000400080030004000400a80020006000000900000000001800180000002000000280020004000000100030002000800780000002000800000070000002800000020006000c0010001000e00040010000000000040000006000a0008003000000000040007800600000004002000300000008000000a000400080008000000000000028002000c0008000000900020018001800200000004000801c00000008000000600000004005800b000000000008004000400440008003000000300020002000a00080000000001400100080001000400040018001000c00140008006000000200010004001400000000000000e00040038001001400000028002000400100008009000a0014000000000060018003800000120008000000000000000011000100000004000800b00200030002800000000010005000e0008000c000800600080000002000b0000000000600020008001800080000002000800600010006000000280040012001800100010002000000000030006000800000030002001c0
  | 58 => 0x480020000000800680000000000000100070000001400080050002000800780000004000400080020002004800180010000000c00000010000003c0030000000400000038001001000000000009000000000068000000a0000000800a000a000800080010000000800080000004000000000000002003c00000030002002c00080000008001000000010014000800780010006000000480060006000400200040028000000000060000006800180010000000400000060000000000000030008000000100010002001400380000012001c00280020000002400380030006000001c0002000e006c0000008000a003400100000002000c000000d000e00200000004000000000008004000a0004000000000060000006800200000000000000200000000000000000160000000800100000000003800d000a002c00380030002000000100080000000000180000006000000d8001000000500000006000200000030003000000000018001000200040008004000800040000001000a0004000800b0000000c00480010000000000e00000000001800000070000005400280030010000000000030008001800000040000000400180010000001000000000000001000a00020006000c00000040006000400100010002000400180000012000c0030000000000000048000000200040020002000e002c0088005000000080000007000e00000018003000800100000002000000000010009000200140000004000a002800000010008000c0030002000c0004002000b000400200018010000000040000004000600080018000000600000008000000a000400000000000001400a80000004002c0008009000400140048002000000000018000000000240008000001e0020001801000000000004800000060000000000100040020002001400000004000000500000008008000000000004001800100000018003801a000400180028000000200040010000000200040020000000600100008000003e00040018004000e00180008001000200000040000000000000018003000400100000006000a00080000029000e003800000050000000400280050002000800400010000000800c8002000000000018004000e00040038009000a003c00000010012000c00c00040000000400180010000005c00000000004001000080020000001000000000004001000200030000000400680040002000000300190000001c00280010012000000000000002002c0010001000200000008000000a003000100010004000400000000000006400080070000000000180000002000000000000004000c0030001000c00140008000000200000020006001800000020001000e001c0000001000a00140018002001a000400000040002002c00180000004000800600080
  | 59 => 0x7e4800000000030000000011c8000000000004aea4c70000000046ac00000001c630000000000000000000150852e0000146a2b780001890000057d8da88ac40f680001115253b4954174026518b721ae9a1cb5280000000aa1096a1fa835d64ff0000082025ec00001008ca148360000d1d000000000000a4827780000000000010950cb60000000000000002b180000000000000005a2054c325280b910d142500000000abfa756285e000075198a3580400012b4800000000c7c0001bcb170cadc4000000000002a150c784e50000854c2fb183f000052381ce93bb19744fc11ef800000008801046000005884740000266300001ad11c2800048f889fced2800000008d2800012fb00008790000280f5412a800000202d00000000000000000000000000000000004f55544000044c265b4000000001502dc481b0000043800000000000000000000000be650a00000000000000000000d79871d0000000022780000000a27837ea49f213a00000f5000000000000f6e00005272aeec00024e4576eab2d207995b3f0488a40d40b4300007df8000000000070000002400080020004000000000010004000400000010016002400000000000000000500020018001000e00010002000000200000024000c00080030002005c00080000000000000280000000000800a80050000000400000000002000c00100050006001400000030000000400080010000000000600000004002000080000002004c0000000000200040020002001200040000013000a0000002800000060018000800000020000002000d0000000000000030002005000280080000002400000000008000400000000000000c0010001000a0004000000b000200000000000001c000000580000002001c0028000000000000000000000400000000001000c0014001000400000000000000000040000001800000060014000000000020000003000a000000040030003000000040000002000600080000001001000080000003000000140030001001a00000000000000e00080000002000e0004004800400000000002800300060008001000300000000001001e0030002000000000000001000080030000000000000050030000000100000002000800200010000000c00000040002002c00280020006001000000010020000c0000001001200040010007000000000000003000200080000004000000080008000000e001c0000005000e000400000000002000400000000010000000180040002005c000000f0000000000c8005000800040040000001a005c0000018001200040000001001e000c000000000000000000000d000400000038000000000000010002000e003000000000008000400000050006000000000090006000c000000400060010007000000000004
  | 60 => 0xa92b251ca4d401b145e000063e40001ea300003d1c0000000000000000002671000000000001ed702da00006fb8c53000081dc00000000000a768000000000001e18000000031a83c1c74fa48c39fe19d41c4196700000000a39a5154200abdd2a2a17500000000000181a00000000b642b1000003ddc00000001184771c8c90000066e00007359b23143c4c6d26f8fd75890458d3f80000000083900000000000000010578000141c9ffc000000043a26fc8d20898d1274ad04b0e0cd10000000000016c624ea5a9000000004706a1f4b461a96000000000001a6d0000000000012e2000000003540000255619694cb9e132126327d24a2a931ffa000000007d0138c000042400002f6a85384739f45548c1144cf58acf55e684791e11f933fae03c40000785000058b817898bd1d64000000000000000b0a89851dd3386c5c80000000000000000dbe187c4e4414f8bca800b082279711671ac20d4a35d457200004a72478c0001a54000080fc24a0a382278810417b80003eb40000000000022ae000000002f8404e0000000000000006b84000056255c2440c00000001e841d594e82b3800c000005c4800000005408000000000000000a6793f1000000000001e3f0f48000101d99d54d9e3b503de81e63bf62f30be924b057c6524cc07a21e0dd41bed1a82b003dd8683c40b92833b5859d0000220545ee81e4000000040043b8400000d720ea2af047f89860000748441f87b6000000011ff1f6458ae00004d70f934894000000020a50bc482b80002652000000000001af839f6000000028a70000a7d8c8c000000000000fc580000000675930b000000000000a00800000005f18000086f1572795041a000007ea000000021b5105e000015198aa354e000000008370436000092f99f61a26921800000000000af6452c804b4f1c0000000000000000108e8c9ccd00000000b070000000000009290000000000dc0000000000000000000000000000004f38000285c30e40001b990000000000000001ba4000000021682b8e0000000000000004ea8c241f3940182bcc85b24021bce43d40002025209c000000011d946809e20000059f1f408730000150c00000000be415b2265427c913d1acb06c241e43288000197c000032c1b98000025289e800003912a75824406144b5eaf38000000011fa2bc4b06171840540000412056f562e40ac676816f031e2efd51ea3af3ad66c0456506d04e3ca60c79f909b4dde565499989dd4800978950e80000000000000000000000000000010c500002db400000000932a698000000043da8624df6196a1ce84498ab8189843fc09100000000585e81e00000000000000011ae8000000060bc0000000000000000001c963d6e000000000000d2c00000001817004a00000000758081057e039e00000000
  | 61 => 0x6400c71a80000000021803f88eb3e0c6d7800016e2016000011d5a6683566a0ac3b1a39d55ec06b0449934a00000000d5c0000000048089ce2ad656f061fcbe81d77394e6eccdd3913b3ebe016d5d191560a3c029c000140500007628b138000506a232c564283d00000000edf029b293e72686020fd15812748c00a0000457414950f50c7218888b2d60b895539d82bc91868c74108c28e8b0c8000270a47f800005df492aa0493fd01a71c84add91cc858f514c92a4000208b10a20000000054948a800000000c0800005d940000000000000000000b66364000007ef000000008de00000baa2d10000000000001fbe0000000133f0000000000000000000a7b400023c00000000066780001c40000117d0df80000008400001b4222a000046780005666363948a2978166e0001050a1f138001bd04a7889a00008f940001384515eacd0b7b0000000040cc00000000000161c0001d6717360000274000006cc2c7d4ef8b39271e93f50ffa627000062c082c09a7249e90bd5fb1ebc23d60000afb80000000000005b00000000000000000000000a45955700000000768c25da144095e33e400000000000000023a2b8b34e64e3017990ba15c285ec2a300000146ad4896b00001eb07895508000000009e6c63a9e58525a9eccd8d80004a668e980aa06b500004a9c000074923b0691cd010000218c0000000045c4e6e44a44940a004f0e00000001ee304c03024ad3a9280000551400000001b94760c0000000000000000001cde391a4b9400007ad2c00683440e0c2100004a588491367066869840000ce0529a0000244800000000000000000000001a0d143042e2b465eec0000000233c51a000000000c7a6da0ae5a8ad000087e960400003bec53193d4875a0000a5e400020fd0000000014220a32e287d89027193f52926910e69a0d323e6000000000004284000000000002f189f112fd00002854683886d845e00003cd40000000000085e466d97e3450800003e38c8b2916a600b4709c340c6000000028b8276492fd22b00003fa40000000085a2958000000018e9338a9398000000000003fa82de0000329690540000000000045480000000549c00000000000013a5efcf208dea55868f592e912ca00000000000000049f00000d8625cc4588000000022e10000664400000003c0600009b500000000a9cc00000003cc000000000d11000096cc000000000001b54a8b80003e7c0000bf487c00000408434c92034ea6165d0ec894837c88048a6a8f9d50a45f0400000004d5a2c3c0000000096a4b6904f15fc30680f7044180003bce0000c351d9427be22549020288163600012d891cd00007d84f15a90653ae58b47111c4704aeaa8c5492b4d073c893545b0000000072107e6800000001eecac38bfb3da4a80cdc590dc0000000074b
  | 62 => 0x380000000a165368000037b466080001c4c360a8fc505c816000007b843221598348c396c000188e000094fd2818521191e32e03768000000072f00f58c5f502c8f0c000116f0000000039b8000000032dcca40000000031cd09f00000000793872b0000036640c49fc91b313ac00000001b0e05c00000e622bc353f42a3810f1f4740982608474a0ac457c7f6cc5c8000421c6f54a60000000007868ea71aef0000000123e9e9855369f91537800000004a99241ac0f000000e541700003fe60000000000001720d50ba6000245e49af000029dd000000009bd00003d3e00000000000275e07942b993d7000000000002bf9000073e4f889eca4d243b7948f0f5600001f8cdb900000318a858d2faa48145e25709bf8a2c2d2230cc867051f416c95f80000000000020e44478bdf0f9c2a9c71316fe0aba000000000000530000000005b20d8424d00001277000005dc000000000000b4868a89602d5491c0683000001a852fc68a03241a727e29562000020944b1021f800000008f700001e7a000021c48830000258a9ee08f81a2600001d0c000000051940f550cb00000000000000007f550760000000000000000fc4c210000000052910912b0a1ba600005a38bfd1a40b1551681e3b29be7fe93baa99200249bd40001efa000000000000000000066e0cba8ccd1f2e5650a33800000000000755008700009020b6380480000003800002001cf83295386a9c10c8e29b034f000004264b54000168a000077bd5ff0000000000002bf86860f183204000095b161200000001927541c00000000a9536cc0000a3780002f5600000002190189c3ab0000122f0000000000012f50a6a0001422800031ca080933000000000745546cabf242ba4ef099b21e54bc648385578b7b2514727d2cd956f0f2e5ecc1be160f567e31f4ac8276900000000000110006c045f8f47000046c84240000000049e20001210a4f206200000000237300000000db580002fd0000000000000000000000014fa00003a44be7a70200000000a5e800024265634611227d160a5a2ca2c86b826e003940cea9213914000100e1db7380a3c2860f87e1059e247d48ea13a33d45784aa1a39b4ad09b34166932349a26c49487077d0a8a5cc0b7d046805002b7010f8ed720769d6898481f52cdc322442489db539c878890da7e53d5867b8b38a60551fc458848384e348906f495352a4b55e862b4f5f84ce33ca07b8b571b4d28fc058cfb5850e1f5636615cb16cc00002a0016121630000000034900001d388b780001d2800000000000000000000000000100500f0000054e86f21d086e980d5a8bf117a5714000032531fe5a98e901c3a54149a8800009150b5e0000000064d000031d90a380000000a218000163430f00000f9a26c204b89f2cf940daa53d23de40000000257
  | 63 => 0xac6406e93db0000495c1a280000f406211548a0a6144e9c9c72687ea000049d8ac786ec13bc7e58c060959000000013f88c8c11aa6dec54c1d3d0bfc2f2c8de000053ea45c8f9808300000845d160290b47d211d460f0fba377cadd41fe2a5b4f285da959727922ae87d2d1c588f000004954000000000000ea48181e95159a42c45748b8a5780a25485000001606181560aa507000067e00000d1a000003e40688bc721c647d8f6c00002746360c3688f8e12ea4898caa800000007f68000055257c400003a000003e528f34e1516d4296494d49540000112e00006b500000000000000013f70000933c000000006660000000000000000000aa4022139c8602ca2a0f9b37e887713149de40ad626f034812604b3ca5ecd9f8aa5279a0c143811f331082000032e19a30c123364b109a34000000000000580000040100002406000000005db970a398c0ae552b13ad398aa6dc3a3800000001d7c00000000000a490000288d000000006c280000000a2506b2161f2bae0000000137500000f64000000000009870df0000000005a40ecc2bb537525c20b9e98af000000000000000000000003a4000040d60000000139a0000187141a148a0000000076380002a465ba4000000000005b6000026a0102600007f4800007d25b954550f720000000000002bc00000001484153321cc20540001bed00000000e2005221bd600015451d3600006a683248000503a00012ca0000414400009a586d200009e180000cc4456c2d242fb80000000000000016bd0d421bdce240000000035dc000000041e60e9c00026142e58b118f241fb802d6000000023e4000000011a71911000096b0f6a100c09a67a401b4a7043a2e5d902bb80001208124818b80004bde4870c7783ec213c6ec1398000052e079688dfaa971c0c0000dca2633000000000001b384a985e0802f017306366f94ccca54e1c70000118d21cb0000547800023b90000000120880000000000000000000000706c00011b7050e749483f08ce4bec74c115d8c11214432550db8000473c75040001209000038b14b980793466194d5d804014b380000000000000000000fba8eb64418ad3800006870180000000000001f14a2840000a093b6226c8a50099100000000dab8f3b00000000acd80002f6c98c0000051c00003e1c00000003b2272ac56d81f0532213f0000044600000000aa203d20a464a8c0001fe326be0000a2981a200000001130000029ce00b886a21af35ce72a84c80e1b14e477a4f78a2a729d02ed4ad30000154c0b440000000000054c54ada7ae000096a93e80000360682a00000bf626ba32390db1fea000003d80002268000000015b698820000000000026d4000094c8c360a2e2da4562c00027002ab85ee923b921d3d2c2eac00000002b349a1800000d31640000155
  | 64 => 0xf6000000007cf43bd800054ee0000000003216f4000000024970b6287acce710e11be48acc68b08e81a0e00000002034186e75bc000231c3b764694b9d274449f41c355f70b6b2c7220f082124030c50957d59e83d8052e000000006b70b9219e4000256e390e3d39140074400006ae8f192b583e6e395097b8000202069903781cd044ee6e4547420e8262c5cd800000b2173258dcc6d8391000000000001b732f2898a90c1805100000000000091900003560b1f0000379209211b8000012a8621ca6b0abb353224511451fa23ede58b0b618e6f2de409c4000000000000000000140800006968000000014d600013f50000113c96d0760800007c8286025511e641dc86c47a500001a7e80601481c5244b81ccc0000000000058a8c8382ed1bd2ad440001f1d2cea7fb11d4a58651d89a0400000003f0c29b82ea221c3ca0117c9c8000047f20000000000000000000ecf000000005cb8000000700000000000000007240738acc95aa3e788038000000029e2090cfac0000000000000002089181600010a1800017d2000000025a63ed800016129cf30fa22e00000000000000e5c0001a07337287d4a7f139e1b8a648433f000009e631b400001ff574c0bbc5f9800036728f3060b8b24333e14c0f488000335200012558d76000016940000f6000000000000228906b200008258d26000034dcda01b4149d071a45fe266b000019c40000000371200000000000288c000073f07f432bc8b200000000000000000000ada0000388c000000000005a6115c8278417e6b4468b8cf420bc3a60000145f56885e9d1c8155210083ad03b48fe2288844f892c000035126c84a4d80003c685891183912f529400015d100003a580000000000032c81e1c793000036dca6d4c60803a0fca93ccee586b248c4441c000000005dc0000d1500001c80a568b03800055924a1c64100004002327561a9ffc074c000001f101c4410000000028e24dbe4900e7a8cbb225817ad3efab0c00000000d7018c811160000000113f3206000000020c60000000000000b73a0e580c00017571d96237474d00000d5c00004628000337e52480000000000000000000000000045b80001952422835ad40d8085015e85141bc00000000163555c0e59000000000001f952d5200003d50b1e138485f0fc78ae8096c984800000001eae5c78000005a36c400000000000390457e4d191fd600007074b7a0c9757ba2874c5a8ed134525e7c851a23f588aabe40000fc2000044c800000000e64750cd8c0bb135640000b8e1dd548fe00015298d92467a67640000000223a0000000000000000000ac9189c02047a9c000065d00000fe4ad08c4728fe1cb1465a2e81d841584007a4ac2d4600000000000000038d80000df90484000035c9ef314843bb88f4906a4f1e0000000000000
  | 65 => 0x3c000001a98f4c225c0acd1552311000053807298e4607020000ac32988000041d931f0dff2c0c0a940000000000072bc59888d3186276540000d861882883489b09e538b85e8c0000464423453280002abd00002820000005f100c6cc4cd815ba31aa0000f8f9d01000056f820ea6a91f3867a40001b9c000000000000e0b00000000db3ab6e0000000000004ed000000009b2ac1e000000004732015284815e0a0da2032b3a17195588b0656d4ab3d0428000039e0001047887c0580000161128bc0ea60001077800033680000000000000008be0d4e1a0c57b65c7482e24ec4dbc00001b9253c00009a94e38807a21b081451b1951000006810000000000001e44000000000002bfcda90ebe1b08164891f8d7a4ee60000000000000003f28595227e00008f5088715210cf4913cd9687af204012110c100001f10662000000001e6492b5151800026764c2c487000000002d54000045b00009f7401881d50000a21c000000002d467f4703800014a4000000024d60000afc049ca93b46ee4a194169c5000000000000190b4d1c4424d6617414d3a82e8109000053b600000001de300007e4400019230000000000000003ae65c7cfcf0de21c06502487f8000148a6ec8a7f8000000000008a40a5300004a040001eb52950869800013972ef61dd4b9f87880000a5b496b80004cb00e50000000050ca88c40001fc1000000000000000464e0000000000042560000f08269c00001448b288000000000000000000083091a800008f91bda3e952669f2c0000000000022d70000000129b800020fa2f64f2ca1bb0b4e00009751b5f000000000001078222438000000000282a1b600000e5f57bc7198e2211d60000980458680000000acd53cc1185000017c426d8000057487e400000000000000000000002a60000000006f921389f6000324d500000001096800000005f292fc280e255a00005d61620446600015c50b3f0000a81400000002e1202e8a058ba4207200001a1000046a80000159000000003f2c3150c5e335c0000ed588794a9ea090000000000000000b0b1e2825005da0a0985fd2cca19b9523ab594534049894e8000300c000000015b43d540000ec3868b122c709c00028690a520000000000002be57f4a4f1d26461000000002b4619500000000000000005b68000266d2e8c000000000002c2463d000000003dd26c515010932376e7850e6b847e17288b4c0001810380200008d000000000000000000001b5e1fb4000000000000000ab89c45046e000000015262c2e811d0030633166a0de8000000000009f0c43400000000000000003ca511000014459abc31b400007721a945368310cbed14aa19a67c24c1224b542486a6cbd30c2b00000000000000000a07e6d5492a3800002404d22ac3b00000000f9080000fe600007
  | 66 => 0x18da69b58b05ff8756800000000001349a87803b023f0f7a80000000000000007e600000a3c5f695840000000000008b70000710400000001cc8000150780000bd2a3dd3aa800000000000000238d40e863c40000000000000011b78b291e78474400000000d2881f4d2d8bf53bea88b467b07190000744080497b1045225008ae94190000000110c88381b8ca18cb0aa0091af20aa0a071c4b219209b89da9e6157622ddcd4c11143c7888f0942800021be0000044109a0000679820713791a8631600000d270a082cd0bf789851a70a7c10d800001f0255f45f60cb10000053000000002b6641100000cb500000000000000017ae39a40000d4e1bbe793c0000e3935140000000000000000000000152e00000000000000000002db8000284e418200004bd00002af20000000000000005c58000000000000000000068c0000000000000003dfa09dc66b11d217dc243463100002f4a73f487b039a00000000000000000006524000081156942ebcc39033854e897dc4bc2956280846700002c1d2462a1d0632824b07800d3c0000000185e00002cd8000114eb04c00000000000000130b8843000074c5226858c229470b8b758eb03cbc9b6051a0f6b2e7257a523ca2a01c345c30df100a41cf26c7158aa81c2b220000bd78000240058e03af1eb80df4aa1c4428000360870112d222550b3200000000000561eaba957d80002d440000fad800044c4000080980003902005935b0000575418848d8951d311e9c586029e333a24000000001b50fc83c68bb10000105606a8000099e4de200000000bb2209820ec0001eed00000000d160c382c565cc535b80000d9e959000007ef00005bbc000163b361e0000fd01c220000364c6b10d960c3e00000380d5e11926eb122328790000ad500001d62000073982a6963d00009880f36875254aa3e8c00028582b58acecc3a0000300257700000000311086e40002ad248fc0000000000000000000080a4bb000000007f58000317400004e6800035e0000138780001c3e000000013dd13a20000000265500008311551000000003b880000000000023b0aa6000000003f18363197100000000c0ea70352900000b91a56a0000487d5b41e00000000005029e734120000000000004dca00000002c010000000000004fa14483be800002b4542200006db2ba00000682cd33912d000013f46e100004f2600013b022903086b0b4689010c3e840000203046b3cc400002ad0ff151300000000000000006314e85800031ba16810e9a5d834789b3049083e5000070312058930370843bc000000000000001183088c01a00000000205401f000000001e4927a41010000000000000001511800033f200000001d5500000000c3e800009bc00000000654000019400000c694b180000f571bfb52ae28a400000005
  | 67 => 0x547979224dc00004fc80003d4c00006b1800000009f01538a6da00000000fd71edb0000000000014f30000a654000266c0000000072b8f7e033e13915988a4439e09920ff5946d4a9201dc8cd88a500e47aac0001035068e000000000000000a2f89180000000036251bd28d612ca00000982842284c00000001829000000007af24760000b04000016830000000151680004b8600012f30000272200000000000509246d4000000057d622e8d218000336c1e6000028f500003080de2000000000000a71800000003af400000000000000000004612386af84b6f88a8481408e00000a47000013254020c91000000006069f5600000ddc0000405000000004661869000046b95e2800039489260c541f441afe0000000047101241b586e6000000000000665a2f400001a8cc1728d427b00000dda0e0100000000e140be20000000047900000000000000028ef000067240000000000078d800000000000000034400000000000083d000014be00000000000000000000000000000000000001c434f504d04871000000000000000000000000000000000000000a988b9800000000000c2c122d00007b3c00005813cdc00015f020cb38c83650ec611c7403e00004d680000000000013f16ec35186f7d0b20000520e8a7c4118ef112ba00000000000000000000000000325e0000000197a15821b7c1b6800029b40a2c00015623f2400013d88000000000000001dae16f20000ce918cf2f5853740002974016a1670000260347022ab40b207ee14c8ab7539880003652000079b0000160200000001e170000546c0000000000066491c206f8067600006d8000000000000000063b00004a6d4868000145a00015c7a07f000060dc000085d000030d44e227be4c0c00000002be53b0c97288ff8105046c743c000015e268000000002776000000000000c640996614c0000d9c3eae885834d243831523c0400013e0000012581de80000000000000012c135440ed43ed8000180000010b100000e1400004f30000215a000061187713c7400008bc0da100005e2c00000005206000089a9631314c9374000000030a05d01618a9d1122454f0b6c8a7f4020000080f02d31016a4f880a26dc0000000086825521eba7770a6c11374c4a75e91331bf5000014c8ab59fcf199ca67400000000000752c0e6000026ec7b203c08f7a09586248c3d80002ef0000100023fb1e1a30b80000000461c00012f41e7d22a6183d16b2c16368400004a080000000787414984c2000000011370d8f3a000000bbd0f37249609a51bf25ae1c22a58893a160b15f6b0f4000000000004db855f057e51b46f0d1c380000caea11000002fa15ea000000000005436000000024c60000b0486a02404518a000074c80004f3a006000009e31e3655d921a28d836769b2d
  | 68 => 0x4adc00021f2000000005fc817556304ae0dfd0d455778039d34b8000000a00000000000057685480000000000043f800000000000000000021bc4dd6000102900000000265c1d9955d3c8c8a4c000000000005c3c0000000000000000002a81187c3b9454126ae295635a400027cc0000000029e89d01a169838a300aee45ec62590409b33446a16740000b0e000000011ea80000d949b18ede06e71766005427925984c742d6cf0c9b9e0e9a514521c87650be400000000931265c37f09990000000067a000000001414a6f00000000000093280000f210000a2ec00001842b864fe00000194309a7e0cd6a259009f634a40001752468c687800001b838ee7f7881400000642a7889c38000000046d94d20ea21cc4873843b055e3d6c54f54d62aee0000a9f81e78000279c0000ae097774222000091223f80000a308000000000000000000000027e84c993d580000000a538316ab293ca200000000a4300002c4c0001fb4006040bc0000b5a2be84b084830000419a1ba042f9be8000044e5237a5780000000019e06ad000001bcd8a95563ee232fc33f92ae443e46386c38000500a9c28d41086300000000aad198a219e000061825960000a8c48bb9b4918fc590c03a0000172a17cc033000056229860000125416c89f9caff213f4a242b49213150b4e741424d439469507c28c0ac103cc16c23ca4fb425d4055240690cd00001f5c8c9800025fc0000919c0000dc0000091692141bfd0d129e8000020ca000081cc03b186e3f8e7e010dc00000000341520b957c169aa50c00000000000acf15ca8ed01c820a70a321cee43ce5234000071117749ed82e023a53aec22d53dda7321f302dcd0a59af124940001520095f338833f0e9ba2b22674042d1e092a40000000000000003bd800003ed0d55127c2064efc8f190412121820f0a78000093d0d5d897903a00c30dac80000000000000018490000601155b118d00009ae1320800000000000000000000005e4c00000004e18371c000122e000074bc8868000048232b8000201d55983fed2d4869f0000a7b8000000000000000a1aa51b00000000000000045523e64000037f2ff00f38047a0860f86815d479a24c1be018450cb929200000000fbc22b008180000a07852b4750000000c90b5013e9210e71000000003e44e2a951c000000000ec980807fc465521f80000000000000000000998444c000000048f40000c3aa0760000785400000003ee40c18ade00000000a6cc000000000000000eb9000000000000a43ab97263c0e38ba4800031343c9c41b0c884d501690310000049ec767509a28b100001ce55bd27a2263054250df27fd330a43c455625df21ee22802e1a5b84a0856e41f30b4544d23dbc000039000008e3000020750000000000000001de46b014ec8000
  | 69 => 0x600000000961800031180000df1800000000001383800026425f74dae99f4455c5b58f2d9fb94a4006148e0000000006cf4d29800000000000000000000003aed392000013500000000000044f8b0640dc8000000000000000000000065f40000ec4290200000e52743000000003a7000024fe0000b34800000006e90a659e1100004c443d3234712fc664d23919c7000000005312bef35908d354b41b6d3d369cec0962a3442cca0a48c400001c7600009298723000006703d98d2243281ff4b26a8e700008c643b728ae3fd22654000000020a8a50846ca50e00007f98f03800007888364a0faa8349b0000013e8000489270fc0002aeb00008fcc0000000000092f44470000000000002ff9cfa2b76a33867214381caa000000000004ac025ccce40000000000000000a31188a0b6940b8da80000000000000005674000082e80000000184c36d80001ee80000000180e1b3e998539581740bde9100d698000082a5200f6b0000393096387619748581847b9533096a412894b80000cc3556a4ac40001e390000a6802ae239c0000894800021ae40ac30052ad80000f420001144000004606bb4a7521f4302a00000002b0e4152000129780003e46899471ea2e9000098900000000000000004b18000000000004598000128c0cc0fc080002d7677e80000000229c833095924730000a8e47b6800013a4416c000128f2522491c3350000000000000000000363c8e613110000235e0d78000098100000000000000000000000d4f80000000465000023b2028892b91d08000000000000001a8122d6600924c941809b4145c000205318aa000046d800006247ddcf4e98fd000000000001e934cbe19ad33a941e0c080438bf58c7c50e2a5e86df16ea2cda000000014f412de00000002bc90000000054384350000000000027f3157e0000ea9255752aa0f140001aac000000000000000000077ad51b9d7d0a0600000000000375c00000000c1d541a51a8000272c142a000000000000d600d380000000000000000000862291e3cbd38ca4f01fc600012e38fdd2f500000c61000000009ec8f1f0000000000008fc85de2394ad941a18000000000003f12a2500003c5c47d880c33f820b09df800035aca9713cf800000000000000155f12762b4c0000cf70000000028400000000a3980000000540210985a6189500007a890da0000427a0000000108544ea915c064194a328c00000000000000046d00000000000000000000000269ca5b81271402236030540000000000000006a2219223c8af709cea6320000a47158e86763f1812b53dc919d29d212c506790ea000022f8000000007c6714c78112fe393c000115312fa180c39fcd91150041f813b82fa0000494c0bc000014d40000394000011ad50ce09600000000289c000119280000608000
  | 70 => 0x111d80eb700005264000273f331a00000001a6810940c088ee158a2f203750b6d80000772000050217b8167004780000ff006ca4594f220b8349de000057289da01c0712809b2a2212d2000000000002c3400013be0828000000006f4079549380000f33a94614c60000000212709269718d5a800000008f40d5f8000000000015a799bc5492000025991423a9403040002a9f26d06f60b9e0000000046e0e65800002f222502c2077051c61cd4a311c7a37f075e4222975d01b8000129c00001c92000000000004cd473ac00000000000249c7050f491bea450ccfa871046540954000000041ea4b6c00006310000657c16b0f7031e468b40612a3b00007374de30a402b9c170400000000000000000000203056794ce6c02b83d760f352578b74108400012b8800000008519172147420020000b448000000007686c080000eee1f28301805c00341e3800027011214000000021250c843fd080f800030c63c79363934604346dd07859a1c55004738ddc2b0827da81014e317d500000000a43000053f02898b11800030c8510cbdca1fb000000000001233209e68ec35f8000000062c8000000000000000000000022d21480000000048aa000000000000000000000000000000770412b167a00007bf82dd8d50355000006379439000040640002923000014b0f202a6401340ac0b9326952a34356430585e719d237c43aa8d6d46d037380e6a04d08a018601df1cc00000045c820810d000000000000192434a65988b8800000001e8c000000000005d5884125ff000000002118000011c000122220912976704d3b790a723520e3d4e38000000032882fc80004d32000000015c21cd00000000186d477aae10975800041841c8929280003656000000000000000000000000003a28330837700de43a00f88c8aaa902998af18ead0000513610f00000000000000008f380000000000138729d20000aab54410000000000000000fcc00003d1400001b2544200007fc800047b6000016707454b7896009f7103c49400000f3c9dc24a1276e0188ab53101453dc0001e571112751095b09c74a1087b0829a62f3d62afd026e89b626843ba40000000070c994541c0d2400006aa94ff16f84dd4240126d00003f8a5ef895a86694608527151603ee1c1236b550581fa000090b9589800000007b8946e0000480e00000bd28963bbe000131427f201d02d88c52800042ca6310000000047f8082800012f900005a840000000000068bc0001d3b0000567c0002747000000000000ca340c817b8eaf8c0e347267fc3ea0ad00000584cc7227280000000079c0c3c0d888c2d3da800007b400000001b440000848c000204f5650af480110000462600000002b9a58600000b6b9d61000029588b500000000ad580000a65000000000000d0a0000a7d03899da
  | 71 => 0xa44ace0000000000057b4a178f34000000001f209f0800000004ea40a68000579e0000000000031a0a32113c978100000000a92a2ef2fc4000123202cb3976000000000000000490400009420d58a428d6321d8546a8fac27a830e00000000e869a564af6000107b14c2000000015c080000000adad4be92a200004ecc30aa15e30baa79c0000ecd000085b04cca5590778000000000000000000036c89082f5a0000a188000466228812868bf04b4e4ed8c87060012e0ac6c00000000000ad1ce8ea84d1998000000000003ce20000f780814000021c000000001a7a6f08f80a5e73af869c0c4f000031ae00008d52b980000ae0c6231d0500001c7d5900dfa2150675d49e12e6000000000e3172f0598798c00006c0000000013d18d6716d285241fb0ba30000685100f039f0000000000011410a9630080000000490e0000cee8000000000000002a1a00000000000132f00006cbcacb2a7d3bc40000000295f0aa268b800000004902932070ca64b372e35350c51ca00000116451e9706449600006b021f30c5e00005552c4e06ba13ac0000000547e0000efe286230129f70fe49b4b00001a04e8f80003c9a35b064188ab0dcc02cc00019df4714ae4918818114fd69fb86be8d3532ee64780000000407800002e10e8d317e000000000000000000000007b100008474f420283000000003e3239331ac00010cf84f032ca077882f8f463a0400000000a253a3804b80000aa33e5615c460e0df317e210c8a16aa9e35820cf8ee61828506259a050ba8e91ae2111c35322221f6e0950f8d8000031c7718e28964a0000521513a0dee1db60000a8b00004460000015709bb1622000000002683f7a4fe8000000000009ccd097a78212e4031c0000000104a766c09180002b88000000009cc3a7c7a01202819010ca5ca8eed22ed4efc000000000000fb000013899beb000068c400000005738432091a80004bc8362928d10123a9869bd345882e173e0000000000019f6972cca0a9b046067ce8136180a08404140000214f3c1800000000000535c131122900000ae049f10a4091119647f7c000035042e22f441e5800040d023d4805000000000000000239700000000000000000000000d180000242460792bc8393142686b0338292c0000647c000000043aa000129380001a1a00013cf0e314b903430a7225282a52824868c0b5c43ac19f0eb6000026bc35243240000000000006c800000000000000000004c80000000000004dec7d5083b8ff2119a99640000000000037d8755946e41e48b0c00005c4000011890960b840ce43570b85a19b000000000002170138a00000000000000037bc3c793d3027e000000020482fd8000156f29e548481e58000115545b08768e480af90000a668bb9800000000000739a8e0192c33f4f17ac32303674
  | 72 => 0x4a801e91402efa673412902e12ee4834934499ac0000000002a80000000453cb008000000000002c59bff0f88631c0001cad242e73d05660000000000001dba3ea000000000001b1f00002df80000000000000013f4800000000000de08000000000000001d960000209c7c8000000005c0ce1c0cb0343ea5955fe800000006600000062c0000000000000001418000000004a84528055c0002bd100ca7d81552845d2d6e005d37e084e2724075d1ab800000001d813ff22fb2dfe00004ff87fb16ea27b40000000000035689e1a25009c25b34214a90231b2464c129a0d11b9e32646d62720329c6ebc55a1aaf0d2a164d44f80002d5a0000006a28355d0000004ca84841ca9bdc00007bf0000713c00000000000af9ca8500003b40a3e80000000000000000000000022c9b6456b800034b80000000042d000000000002a30000000005a80f0e10dc000000007cb00007bfc0be91c60000000112d00e91bfa03250fb853457640000a938000147600000002a7800000001187814900002e4076f80000594000077026d600001ee000000000000a2654e000000000282c0000000008e25c42530000000041a020d00000e627490f4d0000000045d0855047625a68b3c66a1fab3df80000000039b00006280f4a169724f600010f421ab000000000d880001d8a9d482df94821e1e0000dfe00004dda00000000000000032b00cb0000000000000000000000000000000000000049bc00027de00000000908ac472a261e9c0c10c2c030c08745ea22594b2e000000023bb2daa00010470a930000000097c00003b2006e958b0dda0000a1a8000269648d000006250000274e07a0149140d1d420000b7e89964b82873d146000015b048a000008800a72988c00020f800002a240000000000092290b921580e543a205a892be2fbe899c3ff96cb142858740b70779084ea1bd0efa0e1554c2e14e0c003f2df63de14bb1e8653462f3536a9c9d00006cd04e99a4c01125dc15d60ed8240c00000de80000000878c0000f00314e52d40001b9f00547d8c0001d8128ba3a5915c26e73fa81200eb72a32031600000001f6a00009a291ad929c4f2e481c87a000000000000000156e3074b09800000000000680c8398e3c0000735400007830000a9e86d70c0f0ea27b3400008e5071a5508000011a09ce3910000214d00000000d7a00000ab61e7c000288e1c4291413f4236900004524f441df00000000000000004c2a23d95040000000000014361fb500000001044000044f6348c0001e4700008af000022c11b9a2b088c39ada48e27a3c00000002cc200000001f3841b03d6c712012b0000000000000000000000037980001b7a293cec10d5203367c98292000016d09dd0000000036a60000000138e000068f800011dd1d9e6fb84a21ec752b00000c3999
  | 73 => 0x2df00005a10000000000006ed40000300546c00010368c5a00000000a690d1b12f6071410382c942605c884e78000000000001bd8c2d00000001544800041d284980002049000000001dd80003d520000000198f000000007c58790444c9ded4b50c54174c67c05508626000000006b0a31d00008f440000000000080f40000000565e405956380003df65840789800000003c180001ee804b40b70c6680000000751c0000000000051040000000445ea93000013ef00008168d961657000093a400000000000a24cfbc8000000085f400000003e5a7f3400000000000326c9de8df4563e000000021c13232000000001fb05c8000000023ba000053b02c48000453c00000000cfe000033cd4c596920a544664f84000058a64698194138a0a4ea47d35a80000000a0e844900000000a8f8f8b98d129a084100d09b6537deae64bc38697370639c0fec2891435a61510ee82511e962dbca091b4f3ce433d4b741aad25be32680002ab71ebe8f8d18615070000a3b400000003362000000000001852589800019634c16a20c00013d6000035c947c05ad1d4a641009127f72c6a1430000191200005f4cb651e313c42144d42b9e2e16ac72a4c0b16e0580c6e088611e184b22000000013864f8a4abcd80177e5564adec000000000000000baf9e1b1c040000000285d33763c40b8aa12812ac00014080329000000009a212d900000000da2800000007ae4000000057d20000000233914a80000a4496284c6c343800219b300001c1c00000003136466800000004ae800014fda9ba15dea6a8e8880001a940001071000047ea1f785c9000041f200000000000000000000000b8c3562403400009f7133a0f500000000367c0001528a429000000013c69d482fcc46840000000000000014501d5c2180973d60a1b80000005f000000004d28707000027e327440000000000016240000c1a80000000a24800000000000000000011ef00008a1c000000000000000000000000003834af300001baa00008a8800034d204f933288570000000000009a012b01d882f2800036b80000000000000002d740002b120000000141800004eba301c00000000e7e00010fe2a65223e9d70000000000009f58a50a9120000000000011fd000000014f5228512205f0d3b51b8650eea4c894faae424681f08950a6e2518c00000002ada2c80000009a8000389a5940000000057a05724f5a00004216264c981167e54dc060054a014150a6000031b10eb33bc48149138b1d45ca434d526800000003bfc23c0000458c0000000054835467955296003842ae6650cea207c38fc8ca0c710000000000014f18fff0f5000011c8a2b106d000000001b931792b0cc157846032a613fc2ac829f263e1e7120c80001f54646946921070c7045d81eb1eaf559477f93d518a22a304
  | 74 => 0x4accc958000000000000002a760000000000000000000000000000003a1000001101452000000007aa0463259200007cf0cec000029f0e5f8000000000014b780000000104cc7dac34438609400fb8f2e01b27fec80309a918ce42cc000258940d471182e6ac243de471505019f0427940d24fc827e207400000000032235ec00000000000000038bcfe5000000001914163800000004bb40000000000005c80001d8f000000000000000117603980230e1e3d9c00000000000000000000000000000012b800000000000000000000a20000891912180003e345c915e3936000009c7c38b1c39000066254cb040233e60000000004f000000000000000000062ec5ef00001b6ea63d470a36d0d5425255b303aa0842000082d13d9000000011c3047a3d02069000000001bb6939c0001e821454000150610fc0000000025f80000be0337ca9c09b73dee000000000000000000149280000000000031f018303f24dccc2da8c14e3610cd37e986501205f60554000000000000c708b873cd20000ff8800005407ecd075800000000000000000033a25fcc0002bb328b006dc0000000464200000001d853cde0d600001b261120000126195f100004c7557621bf0000103cfdf8a580cbc12351b70736472a876c000000000001100f068d08094e000000000000000000000000004b9a5c0928780004eee000001481cb1d700000bd110c7000063dce7528a40a1400000000a9e350a173c0db1885000065094862c380178541127296b40af60bac382164e4af896656158e370dd2304c000137c4b8072f80001ee657fe83a8526000006c4146145c96b600002c31034800036122b0cf52000000000000c6c0000000027d805c089d10249f08e83144f03cea9b14791e923944a44504d21e0538400001e4255d00000000000000000000000d810b82000010dd5d68d5300008d9c000000000002d4c46e16ac442e000000000001bf63fa00000000000000000000000000000000000a36232ca5ad14c05b02d0e363410b8000000000012260000000029f527d80000000000000000002330000090b1b7705d80000000000017d45b3c000000049d49c501d28fb2198a5c85218817f00002f0d4e480000000000000009d4000000014179bc71226743800000000000a74c83713e2184c0b206c61cd900009d50b72000000000e84d0c8000000000000000000254a0000a6f09291cca23ccdaa1b3a57a633bcf3f2b8c51e0019c00018b83f28000042b05b729786bb0e179f051850000000013341cf400009159bb900003778ede800000000000c2b08b11fb87df0000000000002f6d04b8000091c8bccc84000030e0347d0eb8000169c00013251faa500447f0000000000003cc00a296fc0122000000014a2000000001dd0d6807f4372c0002
  | 75 => 0x30a2f6812e80000000000002943ba14e20000ac0ce14ac4247d00001117125b0000693400000002f648194a32833d266a000113900003344b0e800015c8485a6a390c38b020fee232078292e00a349b0d00daa984c8600004e480000390b14541e0543000067704518000373400014e20000034a0000fe3065f38c47794d8b000021101048a41903d000000002128bf848da00000001ad90000024c0000000579400000002820394221d418c1af2212ca200a729a23176c0000000092211323eec00000000000255d11002c11e06000000015d24df000008c8000000000000436000057f8243000000003e040000f3b80000000000000014c300000000f5e80001df845780000000555841c40000000171a5f5c8f89e2c2ac25b8d4af00000000000000000001a1241581628ab3366e3c8c00019db3f604bf435b00000000aef4ef416330000a5c83271bf758ac0001019800046be1b74fa70d1e00000000443980000008e507cb179c0000ac9901d1bcf03c471f0000274b06b8ab0800019363eb216a80000000148c0000000172500002b9c000027f0000812c00024c94d3e000000000001a5492cc135a7c14e5e00000001102061600000001861000012ac000049f00002fa12ca85e60000000018a9ca804bc00012ee00000000a98131880000000a11903300001eb4000000006e125a40000000017100002cb0a3620c521880000306a98c36de2ccc21a0000000000000000000000064dc000298240bc00010f708ad005a5230000052800001a88ccba2ea0adc000023f9c1900000000000000000000000000000000000000000031d459818a400015752d4e000031a1a8b0000a3b800023ce000011ed3a800002f8e2cf500a00000000000000f8000537a00000000ab518300000181932900003f9d2980000000000000001d38559025d95711ade0904a754cce00001d720000000000000002eed28c800006de00000001471211600000000ba8000026684a6a04243f04ed00000000000075a91f082f917b80000000074b20ae6fd928b1406496889b000008e152eeac2c8c89e5d451e00001dc00003fc800006eb1c6f27cc0000d4f06f10000a89c0000000000000000000000000079a90f4a0592fa8662ca569e30439a930147d83b407e08d154059dfd048076a0058a0df0a5a2150000000000000001435a8d035920c8c53d8001037e567010a26044834adfc0000000401a43b025b800000000000000084553e40ba8f02866c20a265692b19325000087c099ca49d13662770000000023e832d8363806428064994000061d4a5a0c700001a93574a81bca77270540a03c54beb0a8c4c0e83b40000000000058943a828060ba40000318028136fe05c00000000506c000000000004442000000000000000338cdf980000000000000000000000
  | 76 => 0xe000000000000000a498000000000000000382804d381039386680d1015f8669440b000034d854b4915000000000000b82169300000000000000020f60000000000042b64630ea8083e000088445aa000000000000dba801100000000000000000003f5800015a5000062f00001826227a3ae8000000016ae13a925d0000564e3a48c9f13e800000000c16000000006094000145a545615e8000066255be75ed2c40e153f102848000000018ae96a000001e3558c010438c19e000003318c44820600000000aff981f297c8a04557077e1638655d2e20fe116080000000000000000138a9515060dca54ac000000000000000b3399c208f2000094a0000278a23e8e0815b605c43dd917e000050ac23bcbf51da256fab13c0000000024800001a580000000488400000004f000000000035700007db8b4083e1000000001ef00003efa00003da8da44c5c0ba0e51880700002e88c2780ea214a00012ea80001042b0807f31eda1614000142aabc10000000000006851d187958113924444ba73303c51b8d1af04610ba229673a9e000113518441f6862ac0000cf807d40000000095a0ef0830c7c2a2b755f8000132f08d20000000009c8000000049909860dec4064000000007d700005e453078000536c6378c458a8400000000f8a9742000000000001dc530c459d952197f500001fc53c2913100008274000000000005fec0000000193c0000e6900000000000144e84c62e205fe4f219d2e05d2000061b000000000000f1000000920ac908b0ab6100000000131800000000000cf2000000003bbc17b000000003a1800010b814ae00000000000362600002d41168000008a0f328000000000011bea1c70000000000000003ab63d64000000000007dd8a7c000025d800000000000000027d400005e84e42afc495a000000005d7943300003fec83014ef1a17000072480000000382e000131c000032e6000162c800000000000000000000008c8cb60951114ee68a105d99564f9c00013651c1e00003df4aa8000000000000000000000000000000000000001c6c9350000060234bc4df00004adaabb5400a26300009dac0000000000000001d180000000000000000000000a4000001d931f88a1f8c6194fb00003c500002b2c327a0858000266e000000000001bce0000000000017383bb691e011ea8891d3c39d8d5c90cb260a0f7c6b306af07d082f527b800011be00015ab8000000040f80000000000063a8000000000000001111a52438da000000004f9000000003ad8000058c00004ecaa6908561b0400000004d580000c781f40250402ecb4a20de0000000049195240000393d1738dd73078a3a8be4800018e2000000009f346d49950680096435560000000231400008cd01b180004df25acc5c8800029f20000000000000000000000
  | 77 => 0xc8e3a42620b94000000000002c8800004c00000000000025ba25e40000000163a366c79304080f0800007f100002551000000013ce0e4c0e0292d8000000053080000bb610ab0000000122280000000000123199f200000cb8000000000000000000087e00000000aec820d41382588d6d87c13bb27ffcfa91cf82cf048d80001fb6000034ac0000cc02d1e00000000000000000012e487d5455a69fc7b31f3f000032004420000519265c136d8cd21db80000a1000004746b0fc161800037c29a1547a085e226000000001396274a0000000160d00007d9c000023f3f4a0000000188a0000000000007bc00008ed40000000000083e80000000000000004a900000000000000000003c388eb51ec0e2542c0aefc5008a102102000000000000000000104c80000c780000e2e80000000892400000000000ad2400000000000000139300000c340000087a3531df698f4000088d1d5273d800028d5009851980000a88127a6c340000000427200004000000496e000090f000038b6708d52c125600000000000000008160000034895e01541e2c00000001f12ac7800028d1270064f027f00000000acac888000024e200009160000444a4d30886034654c600007fd1fba352000000001a570884207c0001f18451c844cac280002266000000022db0000000000029ca46cc5c055ae192a2b6e9f48000246952200000c101c670bb64fc907b800000007f8400021f6000000000000be500001a390af8000000000000000000000000012be800000000000921800000006c9c0002489000091b8000000033b0a6a000006660000000000023185800000000017580000a12800015bf2cbe3ff94548000000000000001f320000327004e2c1a5296979400023c500009c2d29517d9422c06283c985c533203770e2b82e710f61d5d23d892f050a53c800000000828000129f29b900000000b9a8000205c0000d5480000f4a00011968000000000012ec8000000000000000000000000000000000044c00000000e170000000000000001cdc0000bcc98d21a8c48940001c15000000000000000137012a400022b400004830000003c4c9c0000945800000000000657a098000086c925c96f70000000116d00000000000000000002f3600000001664000000000001307048a6af914b92f400000ec096599af000050283c2188110d40000931a6902a32929c46b890326e20000000083500000360000000054660000c4f860719fea181566800000000000000044c0000000000000004648699872c070b43526874966008200004b38fdf000001580000f6300000000000000004d7304422e020680004ac40000000000000000000000000000000000eb883e70000000045813950000000002b800000002df000000000f8a0000000000000002df54aea425206
  | 78 => 0x2e00007900000000017b00001b9b430c0000d2e80001c8ea5100000000421e0a549ea00000294000000000002ea803cc00000cd3cf04fa88e5a14c10e622981551a77393676d83cd25d03d6000000002a7c3bf00000000000000002f8c9f38d7b13be000000014470000738c84322a40a0c8df0f758b3e000092408f080001310b1307b3a74c0000000016f2b88202e3a00000000042127ba8fa501f4573a84d9196238f044815a4a1b83731c8a6f280000140000020612fe9ee0280e5e611bf980512701da824784f609de77d0b9ba90416c0242400000001aca00014190000412648200002950000036ec0000000277c000140d2b362e3415b4b31955b523640fcaaa800034fc49080c0a4271ab6000049515d4316c3d8c00000004d0876b40000ff34384afa9406800000008430d3b05910000081000019440000000135e99320968591804d80001fb6477913587ba00007bbc0000b780000000000005662fdc74d40000cda000000001d625b54fde000000002250000000000018ac00000000000299b000000007a80c7f06740001333000005cc68ac0000000421000000000000164a4db02ed190526e85544423925e10b629c437b24fe00008ca400000000000000022a00000000000000019764b8ab03862423cf00000000000120b02ce55e82d1a8514cde7cc477c918b51a660483f9206e36900000a0b871a05fa97a50fe95682ece0000d61901d1aac2b98053286d0000000096f083a1d6a130400000d2000000008f6000056be0eb50900000502600012162a610000000000024e3000000013a4800022f200015f60000115200010bba99e00000000000000006ac0001270839c1314069910e800023c0000109a837100000000000000000007c70ff41833209a63b00001db041928f81145829d165a34cc4650000000039a8000152f000082540000000000058c935580003e4877a800004b84fa6000000000000000000000027c800009f440000eae00006a0000000002e9c701c0a5962251fe48a4854a56130280ebc390a576010602b468781d40000a7202a80bbc54b225a0a3a80004488000099824a84f2aa0dd49794f02e8600010362a4f00000c250b980000f5c0160935974b475c25ac000258306ec672c000000014da00000001fd50000000000003440b2a1b700001db222ea000000000000862000000000003e0e9d340000ce6434400008ef997c171c8aa0e528000156c8098468800000000000000220b00004328747800000000000000191750e00000dd0a42b4402096400021ef19aa87508d420610bae30580eb015b12cc0000563abf7371c0000ae612bf15a8a0991de0000000029d02be00000000097ca110fc8555263b49b188330000476956a0000244070b499393143de88d80000072e327498fcabb80000000155d30
  | 79 => 0xe51f653eba0a782a0000000000000000000000002888ce0800000004d64000212a00000000000000000009be8000000023000000c1b000000000000000000016be6d54a3b08e20000000021c000000003bb52c5000041a0259c3061ede2e9a84c845c800000000000000000000000bc80000000000090cc00000004340000005000002fc834a12429a4a0000283cbf2800031683654143096e39065948dbc2748108846b072e8000047c8208000000042940000000000055e47acc0001dd039ca46280000000000045f000000000000272c0001e24093aa4c400014610bba1ec065a236b518000000002540054866611fb80000000932c9be81e91da42728da50000000000015210000000073c800027a53b1671fd01a800007fea30c05f0b41383e0000ad20000000023b911d800002d0608d52813da4e101ce0933800000000a6886880001104a0453d79c4200000000496a1994178add039e8a5e000085fc26c8000296048ed19826e653d000000000000000000008ada64d1ae60000000000058924590ce5108a289a9759206a278000061440771a8f00000000000000000000000e4783ef3ccc1a90eb4800000003710000047747a40000000263c2edc5f38000050500006328e59025d00006eac111a67d3c149489055925d1230749c00000003b9aa8bce61990d31800d2800011a318f40000e0180003b7400003278000439461041968a1b0e1089141d9003b494883fd371ac23557e9dc842813cc17e435740a8110a28526ab8e120000177c0000105800035ee411c00000004a567744fb305b35398186d00b800000000000908180728f40000f5d29ec1d162a407bf9cb40e5a0001241217e0ecc00000001745000008640001d972520af308d381f63aea000148a800000006a90000156900004b742ca28270d3a27a86318aba0000a5840000a321e585828fe621a10000000000001e400000000d41800000000000fe00000000083994ce281513f000000002854000075d00000000542a89c4539a3fd06e03f152829cb3357a5c340ae05413448ab4d360a8a51b4666d547206cb5134ae791b60000000071b14d7a5544602000000025173f4e33a8000000000006b28000000000007c89350ac444c6a50d125c013800005908f7c8d311824554c00000fe56fc54b0241a302558a91991c9274219ae52bcbbe0000000000015ad80003d16000057b1b4e025a0040000049b0380abbc33e835100002205605000000000000000000000000000000033106fa1eb0b600e5e1dba00013cb14700000b014e9e00001b400001128a9bb000000000000afd000032980000717000000000df0000000000000000000000000011a88f53040a11b4c2a8000462c0001071a58542700d002fd000047da000092d144c2968000000000001dac3620000000026
  | 80 => 0x49441448935000000000000f9a000024fc636000000005b74aa0a52139320000c9a8fda08de71f53080e3f000057441e09775000057a928818f500000000000027a40e20001288ab82000000009c680004e6c000000004d02130000065004a1000000007d80000000099883661840000055cc0001a71000000004c602ff01c8a2e840180002b9e509ca0629a12a8c0001090a2563d9800007c1a02c00000000000217440340000000125c00006b90dc500003f7618880000af721c8855400000001e480210000000058222688eb800001c6840a950e0e2a46985de4111114b489c778532800ae3daa28710e92839000026ac0000000363a401cac49cc7487c2834a42088a2cfa96ad55016413a667c94139805900004cb43c00272094656b4b9485ce2bba4a4d24d0000000074e869d0cbc000000012769daf00009e9000000000000b1293d692ff0000a4d903828412ecc037c1fe967b3fe0a500eae80000000000000006100000137c7c20000014227b85f585112e4e00000001b242740a43c33a10b219f48cd4fcb9cca138277b53a514d31a84a13caa01f10177a0c98c188e28000000011a49a7200005e800002960375a6b98372175340ce238c00000005830068c2ac000034022b7c31c800013060000880800045c40001308a396000050c80000cb332d800006da258b446c8950000064043cc5b104d51b4c5608000000025ce0000324c00010be000000010ce9e703b24439c2cf0000000083c000000001a587d040000000344a000000000000000000082c80000000000084a29bf322600012588000113e616455c07e80000a6e11f3000040aa4a210ce00003b5488ac0001be61a389b44000224a2a9670580001df20640954107d8000000065c800017fc18b800004f600005556b07c9c400000000858407f97175638804400000000000ae4d5a62b090000000000000001f7e00000001536266e14c4d25a98514f41785163800000005964e5723a246caa4e13a71dbf2d7200014f5949844be2ec159280003e6a967c00000001ba02f9c86d000023563ea47388f1d000018fc00015e22554412000004d8078422580000000000000009ff0ae2085e80e000000004ed000000000000045475b526f20ec2bb00000d8500000000000021ca44b194e0000000259a147c01f8119000000007a64000000010b000000001e833a5a55eca66987e2bde00010ef014f259e3028d4ba2ac2b8c033848e2a8600001620e3506be544c03d155500db3664a1f0000000000001c9460d0000000042fcced261e000000006ee9b9d2ce6a650aaf0a91000000013fc800041e82ea4000000021ba00009f49e970d9a6b5c0000a5b000079fcdbc921538b2254c74e8000000064893fa00001e3859b0923000040060000a1f0c1400000001094811b1914abd4a
  | 81 => 0x199e418e00008c3000010103bc106b96142490365c000015300000000000241412860000000000036d40cd44cf8000000002f47b9898b13d600000000000420400000001c7500005dd800015050000000000000001864712400020e70000000112700ca324a6ed800000003e4e684c2451ad00000041803992621c1e9d8cf4514000000111083605a60e840000000000046b22c54f3a22e008b069202eb0c775482a6608fd14a305b6000000000000000000155f000000005fc0000000039f8000000000000000000000000003b920000000000038601d512440000533e58102618c8d0000000051e0fce4664650c000015d379800003d12a2a0ef8000044413a8539ea61ca70a3f435be000105f00000000000000000002ab00001359233b00004f94326084d0c6e143d466a74f0e184cf111416703710000000008c7500e9a9ca6880000000000000012f1133611a8a75800000004458000000016422f2800000000000ac3400000003654908c000176d00005b24b3900000cc0aa6935c9ba2000080dc0000d0341c0000057a0cee04e00000a53a5b635fc6f746302af800a400007f2a110140c000100ca61d55f4ac1400000000000000000000001e125f8114e966b0000000000003990e242f580002c3c1c4e0de40000d740d1e3e50000000000009edc0000000156e5be4faa9c5a000049f80000000000000011e509e0000068155b10000000007840000000319c0000d52806c42143f5014b000000000000a9400e200000000cdf05190000000000026b40000000000000000bc6000000000004f8e00015391c4e146e91955d390f01e824fd800015014926acc0bfa07672856214d52525f533ee08d000018e30fa60000339842c000000014f0833f00006ec4a9d853c28fa6ba800000004e8c516c0000be00000a968bfb80000000000000000000000558c00019b700000000000227337245600da180004640668145a000047c4a7f50b500000000000111c99fb52a603e958a2338405212805a100004c18312d2fa2808063c01ec04f26393828a2ad10d8000248a00013c5000040167f9c583800002100000000000058503af00000000000094280000000411a00000000000147eae3400000003678000051180001fa015809e7919f38c03d9000000000000803d531040a00003cf4bf8a5b93030a544189800037a2808952f2a17000063f873b930618ba717800018ee465c892139a09fc58a08d0c0bc280a492400005d007b201ee39486af90e0125c700800022cd0000aba40001ec200000000000068200001d709680000000000000000000000000006278000000000014c7000000000000000245d000026d48bd24db2f06402d3d600001c5c000110c000022169b74146800037e242dc0821a78000000001fa00000000000000000000
  | 82 => 0x11da986c13c932827b80000f8b00000eba0000cae00004dc06114a280000124a13d02252b910000000152a11a40000050cdbd05684ff00000000000000000000000008101560000cae817b00006ef400000562a687344c9caa5d2e5a0a0889a02b6581665e4fcc141c1f7a20a94198cc7000022852528f0446b41cbc402ab734d3c18b92b9158e30429308000011f1d50040083785f839103744faf000057d04d841c280005642000066c00003b52669c20c800000000c9d3b6832c000010e800000003f86000000000000000781800000000000000000013a6000097cc000050104de97a8d2100000000000122180000000000000004e600009e452a32422000068680e9186000000000000000027e69b4d5b90a97520a0000f771a6b0000000000000000000000000024420000000000005b93ee6000027100002388a12c68e8ec942d2105d5a19d2b12f8080cf118d194dd860647e0800057280000036873a481c044949501524fd8000123a000004781c3d1048d320786033c00000f51b869b8400013eb239800001a9000000004dad437081d2572735000017893a6800000000000000000009c080000a1a36cc000255c0000000000012d8334c000000000002ba000000000b9e2512000000000000522000020fa03e000000001eea4c74f780000000000053b80000fde0ace2e76059457510d5086c00015ea000009a40000ca8807100000000d9800000ad8457120e265c00009b2453b00000000425c0000ef5239052e43a08d51000000000000f61000000000000000000066acc700dc80fd66f78b2b010900009a68000000041aa9dfc0000bc62a7c091c832007d351a947800027ba031a27392d08ff63fda44880001af905182eb4852000007040000f8980004a3e9608ce300002cf895cc000115f452c287c3329b08220a0000d7194c855180000000000023f65ca0000045a00009e0400000003a8c994c8b81a0900000000000000000000000000000000007018000000000007160d1c000010c801510c00000192800003f6000000003378bc4000000001b7876ca62100007b100001c7800008d10b3b8d47305a00000000f711f5a4b1cd0b22d1000005a4b4011e51c18a7fd10992e72ac800013eaa15437a01f7000000004d5e000091e800033c6000000000004106000000015d557000000f0f8000503c863000000000c8c0000d6700001e7472f479a1c2100000000000216726e400000002b2a0918000000000003c6a73a00000000000000010500000000000003401a500000a3315f68000000000000000f310000660c0000000000000004d201590000245d447a28220fe2b00c882570000000000000b28000000000002a144c4c38c8fee8000000000000000e5142de9a3c00010911f7092c93e6820f378a00000000000000049c0
  | 83 => 0xcef99e644f921aac75f9189292a51ec4d30f392d7e7308879135b33e2125d03d8d571f3e38145a020da33983e18000081a174a1c1894f0c7b274814e07a6a48f000000000e4a0800f3a0568f2100000000000000000000000612c988190612e856810d40515046a5b14a7313ff22b01cecc97243d1c2800000001027371e00000001308476e9695420114d0e5200011139ab72a2465a000017ff3c04a4f45761b70158a3a246b826490c94122c00028b010b838f8000027b282278055d789331c947cec53a9afc097aaa64a8404732d1a33885451352574221e000000004de4000000010ac000050ccc4b9774587c53f49b7830f0000000138a800041a88290795000000006b60c799c34328a5f4400014c50d0800001c2000000000000e4328e52eaa71b8000000009d2000021523c8000000001af8000528aa42463c2ab413b00f40ca380000ff0000143d000023ea9178d66826d00000000000000031006944b54149a446400000002b5a00004934879a3e708440844bed800022ce6534678a70900000000000032a0000000000017de0000000118a8000338652940000a390000000000008310000000132780000000a8f0000000055e08909039000000000000000000000f817280000c592fda9d90cc200000000a6348728a2b25807760000000034e80a380000dc108a6775c23e0155205894500178b9c466e00001a6000008900000000209f42ec772024f113a1c66000000000000000adc0f8c800054be34105b38bc10000916cab31022112200000000000000022d0c4e8b9310ce74fd298808000000000cd90596349e37801c480000000aa58000000000000000ea1000000000000000288a087c46090f089ac000000000000fef00000000119a4d052260000000000041621b500001e76492295dd04b2c5a29f800015039d6642022a580001f9c452a000000015fa123a0000989278c0fd2948d13b0024177056c46dc008b2d7807cd5c80455070e4148000000000000000000190c0aacad80000219e3b1064988119f43000031b89a48c2700000000000027431622bc073da7da2cde000070ea13c00004cc4fb483984fb62c5800000000000000000000000c4e7aa000016990000767026e0000000061d800014773bcc00012a112613ea25fd8833000000068b280000a6750547b440002969000036ac77b800007f600015830cdd131e3b9ce130000000074a895d00000c826c4160e0000149c0000000000000000000c4c89980000a25c000298a56c80000000000000005e7800000b454ce22fd5990000000083c51578b17203600000000000089c0000526aaa10000000095020442ea200000000000000090c91aaaba801de0000974993b00000000000000047b468fd11e800026cc598149f95f53f320000000267f45c64c540000536
  | 84 => 0x64f2000000000000156400008190fb320e80fc8000255503a280c079586250000808000011f2483a00000000000000035bc00000000d523bf5209a814387a04a0926000002144cb00001c0f0000000000001980000000091100003f3400002ec80001a6ca8a400025da000064280000a4b000033947180000110c00001c018f600000000a441ae23c1000000000000000000000000000000081e8000000000000000000000000008610d052864195215508a8000000000000000180d028e0e283191496019800009f19f142772b148000142800006d400000b2e000003c800000000000a95c763267a3e5479ad220802c2a44510938e0000000002fc000000000009b11374889b30ee69ec0000a6a00000000000000000009de8000169525de00000000000553a0000753871505b200010231a8433a08e9088b997f5516553421d897f0706390c000000000007c355098000504426947c6933d00000e2d09d935c000000011f78ad5471268402a2094c1a42ae1517f064b419030ece1922a506dc49e00001dca000090ecb5028f6551c000146fa4d257c817ec59900003f420000000000000000000e6e00000b5c000118f00000000406000000000000366512da2dd483029c059300004f3212c02e998cb353a000091199604c589af93a8987100007fd0aab8000503e769c0001e2a21d000007c780000418854400000000000000000015a2011803846c8800000004a5c9bd8424000082e09e080000000000000002d45712000000026b30000000000000003b8600000002bd749820000a4e8db916301f7c000000011ac50502dc0000000067bcbb59b69000000004be800034a455b0000053b586c5b780b3198626b448348e7800058082f3c580276522fa04945958a500000000000000002ed2619800008f400005bc4452118f0ba24f24a1b02d7028c6d800000000000079f00001c7b32020000674000000002340000254300001124a201db300000000d4880000000000000018ae0000a2cc0001ddd38d05b9c7e1800035ca0000000000000000000aa500000000000000028751884000000000c452fe947400024be000000004c727f626fc00005b189fa221eae1c00000000000000000000003e1c0000cb4800000002924000000003e48cbca59a2570e4872445038000446e0000d6e1383000000000000000362e14580000000190c88100000000000000000000b6500000a5000024cc15ac052000024580000000062697dc00006684330a333415aa08d2a6a2f1434e2d3c33426b137a62f6811d04a457e6a530cc3800010803cb400026d200000000000000000000001396870950587f2d30d259222c018646c10000277465f80002b5037ac00009a7ab6f4792a28953406eb0750666c9e218030978ad2c34c1ce00beab0a4bd08000560259f
  | 85 => 0x14a1fa0580000000157180003fe400000001ef837d27b74b77266441ba75e0e1d836c187a2eb8000000050bea8b8c87800000006f2000000001240a1cc0001c74278c7cd87f21d9f26080000000000053568710d3e8000000074c800000004a26a87cb78000000006960000222c48d66df5262a5bf4e6a33ac0000000000000004010000000000012150590000080bc0000000377ea86119f18d300009e993cd0a7900000000e7f127300000000eea00002dcc6be80000a9a51d60000000126c0000000000000000000000108a9a7c164e0000f1c1c9400007898000000000007500715a7d9540800001b509b928e400000000000000000006f203a4000047b4e5d220f396e0000000000000009974c630a6821060000e159b6100000000ff29d3955b67e7ccde8000001437840000fb100000000000186b4b4400012b58e4832d60000108101100000000000153f4c1aa7c5316a234551e49b40000e604c68ad74e4600003962a49d3550ea600000d6c00029860000984c9719b35000000004eb9d8d000000000000000012c00008c1800046a40000000000042660000d67800037ce545400023c44f16241400026020222a9107c10bc200001cac000000000002c640000eca03fa52440000000167400009a380000000000057025b7000000000000bf70000000000006c804ca000000003d33a267b4c000000000003be00000ec800001ea40001d5900009634184000049f2175400000004b268d8854f80001f4e2148f7204d619560000575800000000000cd400004e780000000017e000000000628000476800003f3a031000000000d7128c00003bf80000000048c0bf07ba822f47ae76380000000570c2490b8000000000000000006da526e69008a2090f0000817d538023952e25630b61000038160000edca0b0000000009c589d534f2882800004a50000af590a0233f25c22fbc00000000000000048d8000243200000001b460000ae7c4c913382478000000000002c8e1d90874a04a33d800000000f1f00001d30e4000002d5ea4cc6330000124c9a3000011d44366aee9490169c0d9c00009c1000000005b4120f9f5010e400006a780000000000077313572d5606440002ac0000000012858dbf00007a94c489bcd307600000002758434666380001a2200006a180000000000000013be80001e4a4ec0037114c35680ead20814c92b26000015a9f0f2bac34f800019d30d38578cff105bd4cb49b380000a6952c800000000f2817ba000087c27bd26a60000000232235240078000000000000770ddd25180000000080100001ed059787d603bf0000547c000000000001f5800006ff0000000151200000000ab40ded8000000000000000000000000000cf0000000000000d00c6b56bc5ccc07e80000000000117300002a2816e9434267
  | 86 => 0xcee02340001c7019728a88153800000000000ef8800015489c946248000078e00007a88000000000000000000000010580001a750000847000000000e280b60000195851580001195a2d215365b85478822c19820b40743a83f0000000000000000000000000000000dc000004d7968603120000f6ca71700000000000000000a658bd439169f000075fc8130000105a000023480000000b1354d681c203789c44000000000000001610883d000000000000c3f000000000000000000097b4b411b9500007db404b8000279600004fa0000000000000000000482c00007369a950ec200000001ff800001f8030b130f00009d0070214dc0228000097400000000004d022978600000d040000f12442aaf54000065625dc000000013a11b74747800000002c3c202400013fd0000000129a2bf50066385800026912e0e2d18a3c9713261a70280000e944cf0000000000000000000000008ac3b32058537d80000000aabc8e9a89c00002dc95609cb6000014fd02d8467323a55a93770a664b1e95e89689d1b03be72e4dac000058820000d442b3900005c44791000000000000000000000000000fa681af00006c4400019784584536ce6f8533224a1dbc0001934453251e10a8000046f65e0032c88da2ec2893c43b8000000000000000000000000000000000000000000000f113c7a0000541800046960000000000000000000000163c3540203d3b8828a49160000d8596b82b6a8cd8ade8000023a2a3438702dd4762000000003321ff0954c00012f307ee00005d080005188209935f99814d48000000000000000000000015390c86324800000001eaa0000000000057723ef098092791b780000232a8b500003fb4000294f0000a58c000000049ea3a290539362000000000041ae800000000fe8229b000000015a423790d403d4957e8c1955b20001228abf84008000013e13770000000000000000000000000000000000935c77b0000000052e800000004ff897c40f780005572000000000004f94aa0800000000d36784800000000ff86818000230047bc81752672809552aa2a00002767241e69e927fa59d3d3c0000b7a800000003d891ba00000a4ca030dab0000510294000000fb900001804461a91800000000000272900000000000000045aa00014971154000069b8a6c8000000039f54428000288a000017f0c3a3b9c9504000065202761aece8185cb000000000000fa2230200000000000342a724d43f81290000000000000da00001da00cc9f700000421c000153a000010f4000296c00003f80a4a193000003b5400019e1284600000002b223cbe0000bc50b300000448c451163f28760000d7f800000008c14a0d0b2f0b044ac009929cd50ec42f401a87b736d88ffcacba56c183600000000abd000021a44c008b221f475
  | 87 => 0x127103100002db802a545e800000000000cb78000000046e888f1734000019b400004700c0401a8000000034c40184c7300c6000010a07ae1d1654f61af0b1b094e0000000067382641e180000000000006720c68fe89080000000012ad000000000000000233c00000000000106538e42cec692939f0000399c0002c3900007e900000000078c78384a3890b000000000001c651a900000000112415380000a1810d2000000008508000000013e14fca9590000928c2049bf900008690ffb962928749a60aaa291a30ce855959b80003f0800002bb2647179c0d68000000005c653bc0000000000000008bd860600007b051eca5061a5a000157f9c6b00009f9886195a90000a7980000000000000000000000049200008de858a00002650a9a800000003fd5270098935a4010d2932672299c52d80000000000000000000000576c00000002202000090253a280000000378d08c00004690582009025a0000000000000a1917f44264f3603ae000000000001559000043ec00025e1471097b8000000000000000bad965805326bb800000000000000125080000000a760e3b03192da238385cb84c7294c4f44e1f000046844940e09069352cc4e4c6ec000009e215d06d2a8000ac692f0baca3ac04ea99f14df1bd44dfc3b8ccba11c2201c4cac00016ed275600000000a6100008e80000288400002b2cd832a060000000000000002168000000000000000624c00005e0126c00008dd85c700000000eb0000000000000000000050b600009e400000000017446a03eb000060a848f0c6a451a9598be01d0a47ec00012102947079263700001d804d7400000001d530000ad0895e000000000000c8b112b35ea8bb8d139b472c0a14e80130c871b3675f87fb8000534e000000004570f283320b012b6c00008bac0000000438a00000001da400000000000013c00d6007000000000000076c00000000000000000015e53d4026c018b254800000000000000000000000d53000000000000a6b9ecb23c49f50000000000004b70df800001dd4aa500000000000000015ec00000a6e59747ea850b00008f740000000578800000ca87f621dc000022182150dea8efc099800005ea00000000aa223d0667498c85653a9a8ef800009c857706880d1b1c370d921590b8d886d4ce0540d3eb8fcf09028634d1ea19557525cac33188c110fe96b4d63a292072a897852406b308387f4c3bb271221b249c83c6801d199466551648db14ebc4de0d0c27f538ac9778f72836420ce1cd05cb0f43020e6dd85ac0000000056a10e0272a48ea03b51d398be4c1016a4e100000116c00000000000103632a92f6024a32c4000000000001ccc743000000000000adf0e60874620d68e7c12da65712d832600000e135858410c000000000001fe800000
  | 88 => 0x3500eda1f64c09830d4de894705858fb5568a40b4740800028903d012e120b22640362c09b8000325051580000bd000003c580001d57545000001558000217285055bb9fa9307c7038b4f188300001dac8ed84ec17720d350bc210337460000000000032623bd0000106d00000000000000000000110406a00a0000000103017470000000000000000000505810c000026ac22f14ea000004cc000022900000c104a68000000034c00000af724121e6682a8eaf25470e94468800000001edc0000000000052a40000fe1000006561ae8000108e41fc0000000000024fa718482aa5db0ae40000000299000000000116a4ee0efe2f0019788ae19c200012c08ad145b2409043e8ca41d265988a2ba447335a000149a0c25437400004c3800000004fb09dc267b0000af2c00016660000000126e000000000000ca0209b00004188c740000000000002df00000f120000f850000000094d8a76a5560000000000000000000617800029990000000000000000000000000000003fea3ba0a57012a000077000000aa900005cf800000000000000000000000334000047b800000000000000058344e099e4c3429fc3b68382000000002492000000000000000000132287f0089a009c00000000b6a646d0b680003588788912025b04e3a8e015df273d137a1f2546380000000146cab90a4113380460b42800000000000000054a000012e4000000000000838078176f00000000000000000007cbc0000000000000000000000000000008b60000000000010c98000000000008479ea10000a7905588d9a0000000044c22d432407de800000002ea000000002738325a97e4000000000006234f6f920144da17612c38d7c00004e6102e1d49000000009870b482c6020384dd090240462c200000961000015d48cb838c000073dc4f418465030000122f867b23f0846c000046620e0ade4000077a34920000000000000ea0000371a6b02626000117fa23e0b3400007b52bfa2e24486149d292200005a590b5a1c8512000000002544505000000000000000018d5280956715025ac408982b72bd0000046016110000a4a510a0000000000000002a190000000000023c633544c0c000156546741bbc1338951000097c924b000056042e9c000087a2052000000008fe3bc046f82a72be63f580000ec494b745f25d80c811e7b1d361400000211900003184c19000000007dd0000238e2f540000bde22642e6497f932b00000ffc0000000016c00000000000019352f8a604b5a97850d14352d3b0a15938342f48fd19a5514663abc156a6773f3a75913aba3d32bf621ac62b05982f4870d4e1e068d538aaaa0236178d227037953c19a3555602a8000007f931489774eda90bc038622a8ad5977f550a9de4aed91282f7aab701b58e5a000000002afa54a00360
  | 89 => 0x574c2d09ce10000000147e1d582010499934406124b7c000050d106100002684b29a191438c11b800000001afc8660000000000001f485ac800000000000000000000000000000000000001990aa492cd39929e9c0000000000040e8000207e000000005140000000026c45cc0000000000013f691471920891c00000000d8a8dd800000000000000063c80000000000148ca1374aca0124d8ca46c13fa2e04ee20da610b23a8009ea2bf1e7c525cbb8a25337ae1c0047c169d178800006ec800000000000000000034224828abc271846148af4e06a84c399052a4000000025c80000cc62c271ed80000000035500007af8000054f27125f34bd480003fdc4a540000000000090d800000003f648f2cdc089e14e82297428109772f0804d00002c4301f67dfc0000000020600009fa800038f277fc57d0a7e2234207839f07032590a72ca60978f33c4141c1ba26f0565a368888c1a1250c21a451ac13643e9038480000d9e28580000000000051b66dc499f0000298e000000009370000611c00019380896593c000000041b65d700000000000048e117812f00000ac8cac1abc25440213c00000001d2000000000000118c00005c5abc82b9aa3f465e800054f2000012698574b466c95021a9b1000095fc000000058360000eab0e1c1fa67238000000000003b3824c0000000000000000000508e00003940000370eae389d8a45c0000000000000003bee0000a108000000000000000000410e39e0f4480000c3c0000a5893c200000000be589ef5260914c17a13244d760000f90000000001e6ceb286bd3238717d1489a4e00000000000092b4f680000c84a64c47040001240000000d032107d0800046ea43e4775964c3e3ca62520080000000000000018cc503259e400020d6000000000002c0300007ff90bd2af13d0e7f6448d1ad509a86ca0b67020800000000000000036fc159c95480001a0499d000023ec01d8000069d96451c209ba00000000378002602c28cf01a8226fcbcea2dc17aa00000002683000000000000000000000000000000022a000000000000000000153f917f41665ac800011ea2eb40000e4a9719419c38b48888cc917907c00000000000006cb8c260d0132dc0000000000000000001103000007c00001346a23800000000000000000007ab40000000420a00013e7a7fb2068000000000000114000129d1e8c4bd60000d2f00620806437915a8f9500006c68000276c56d207f8c960000000000000000000000006200001a213d8a0000000000026348c7c000000028aaa5040d80000000000000000000000011f40dd882200003a0c00000000000000000006e200003090a2580000000000000021aa1f8000007fe084c2d7c000000000004c6e000057180000000000000000000000ae90bdb84c509ee8fe90099
  | 90 => 0x57e783d31580000f32446400000002fc2aa355da00002f344d0c00000002da64518bd8194c11d4199c000265b338089bd21d000000005074000128d3fc07b0c000164b4c84000110900001cc600009d7287b2b6062cc9e38b8f13f68d70af026000f246bf46381237358a6ef0000000000000cd80000000000078591a79f4900000000000164401d65480e6d80000afa3da449629a5319200010121933289256b9042243c113813806081dcf2bbc2b740000fb6000031454f7800003dab01d51d04070000000000000003aa2000150f00000000000009380000000aeac00015f046e22bf83dc800000009a082a38197214c3ebc00000003c5200014d4800055ce0001401862b000070253b725e0000008ec6ce8000000047dc00000001a9800000000000000000000000de617687a1400000003e8c8568ffc8000083600000bb000031be24f074102fb2e941770d74944a43106eec0000945000000000000000000000011761f530f9ea2300000000215e0000000134d18809c4000000000ed848e87c9071e000000000001d63000000000000ed3306000005ec072052fc9bfc38e1e4a0fba792c0002207332c00008ea886056ce808415626444e7c2bb44a5800055aa000071480000000000000000004f420000000108d24d24d20000183903880000000000055c0392c0002bdf1b6a586062da4a255668dc8a1e9d0930deaaf0000165c00000000fd324350000791400018fa000000005b60eb11d4874886291ca61a600560ca788c40000288535300000a28053836b936930f268dc18a1c334e5c2790736002b00000000000275b0000596800000000000000000021850000000147c8bc520927d70000000055b04bf00001b8500006170000153200007610f590b6a0b56000111d00000000300c00000000762625126ca8a300000000df525bb55ae4f7800015f30000000000020b500000000000260a000031311849c25000000000000cf20000733858d12594392000138300004ebe60f4c73800000000000000000051ae9b20c7c229c000072b0b04910402c47358a868cdc372c7e1cf469560416e63ace738fd20000b034000024c238a05088dc921a4cd20000d5b249b207072c0242935800000000000000000008d792e9800013e0155426aa8b70000a9b5567000048b2a7cc4008bd3247277b8000139b00003dec0000121372000005288000000020c80000000000075a000000000d4eb15000008de1ef8442000018383938553cccd000000000000000271a5364154c52d00000186927878c1354000000006c00000260014bc00000000000000133f248e0000999ce8c0000088234b870c28de58805954a6227bf0e4e121c2d6026200002c8c00000000000614915581fc173a22bd30f80004dae000000000d50000000018380002392
  | 91 => 0x4000046c00000000883800000000000449cdff0e754e72000159f19fa257aa64ccbda5290000000024a82a201c6000000027c64ab0000000006fe000000000000000390a5768e160855589607c4e7487594d000000000000026440000c2f8000462492345af2b0700000000000000027800000fa60000000004c55728e5c072c000000000000000000000000004ba27b4055800000b0c000031d000041683acc000202b14941f347c6256f52a849a00000000374a42313799900339e518d01b17c54420553800016f308e4567800028431b528418000000047e45700000104032a839c830b83ed07e67c2c15f058e0e6000013d8000022cc2aac0001fb74eb21790fe4040022da000000000000000000000000002f1c70c413b169b0000000000000004bf63f64fbda9c30b6855b400004b234b206a4470000021fa8a84b2a08f100806ac00f6000028200000000000055a21bf02972a9c000000000002b9b00002e205b80000360e0001206065549d644854d1195000c617f016fa4d300000000e949d9a000000000000000548a456400009e2000000000000000000000000000000475400000000b7f1e90000000000000000427c0000000000000000001e3700000000a5c146b00000000000108917e80000e0880000000000000010721bfc00000000000000026d000004300000686c000000037b800012f8114556c64d543a790d62ff400005ff800000000000000000000000000f0f239a000000000fc0b761cc2104004a99ba33ce4d4400023f026da00000000000000000000001ec0000000001fc0f802a1ea168000011000000000000000000000000000000000000000000000000007758d32837e2732000000000001f50000002280004abc0000be6000000000001339a3c71f8e41a40000000000000010450000000086f536280000000000123080004ec4a1708580fbe3a348c5d08917052f5c71cc1eb8af8045636c8e7787263dec26111121537000077480000623000000000000000000035b84259c97190a51701589faf038e000074a800000007eb4ffe8000208c00000d680000000061c00000000000000000024fc000000000002c2e0000032cd0000000000805865687ab0f04000000000000462000006b0b4a000098ec00000004f120000000000013fc00000000000000000000000a8642dc96101a4000046820000000000012a0975cbe2181c22404938af68156000004640001fb1202a48c82bc93e42b706ea036985b645fa0000000000000000000000000000001ef8000024f3916000000013b71e882700fc28000272853d81171cb8396a1dc8af597962a1c00a0b581f122532000000000000000000000010c115b25ff4000004a0000943000023b8401029542b524c43e1828445a905100a3a133c56496495574a404000
  | 92 => 0x1bd917349dc000003a20d861838ff7882917c2aeb84f8800000007e3800000003d9257b14fb800015324568f020fd81e9e5f095fd8000000000000000491140400010c704be3142000093d000018684fec0000fa400000000312000000006564c13800023825d8c0000d5400008014000000036c8070488d8eec25581158f3a83d105423fb8779867800005c38ba78e8e2b10a45d3f080003740000146799fe1eca43300002ae60000b0dc766000000000000000000055760000000241e0000000000000234d4604bc000169a0000000059e000000000000000000031f80000000211f000000009d605a220c013213049025000003f053784d100005604f04984e3e5c9b0000000002c902c514109e5239da000000015df0d6256bc000215c20c60000c2d05ed13d20000000000000000f6d3c22b40000000000001ee716203a14d7d8da755fc000129e8b3600000000c8a1a08258c80a00001e0b0000000158d02612cd400001b382bd2d7400000000000000096c85a59cf100001dcc0000000000000009420000542490c0dad22f50000000080026e436c6126800015f204d4000000024d40000000069a000000000000bf3800000007e34abf20071b927e240002a751f4ca9480000000000017300ee8000253000000000000000000000000034247c93883e6000000007c0c000000018a0475c08e0bfe000065844308000208a8ecc00010cd10cc80e5535a3ee00000000d3190ae3aa86ea8760087405aa952c50b0c2a28f8000000000000000000106e000022386d6d4ae188606ea0780251079e201e7d3cc3d00004a04074c0a89cda425c789c0001e9c0000000000000000000000083e0eda0b900ed95e68000399e0000a1e00005548000000028b200009f80bf904cd00000000000000037189d980000000268a0000a7a8d3c3bbc0001323243721080000d50a2c5236443b400010bb00006490634165b00007f700000a6035ba8960000000000000000c251e2d3f9c00003052825421a579d1db09a301280000af2000000000000000154743022a2c00000003b42ad5400000004e460000000000033da586cbcb8c0c24282f9000023614316a5d42f528dd000069a92de866f000000000048000448200012300000000000004b68000027
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x862f645493004316322a4980210f9d2650c01087ae9328600846e729943004236b94ca180210f9d0650c01087ae8328600846e721943004236b90ca180218d552610c010ccaa5308600863554584300432b29ac21802199549610c0108bce7b2c400845d73d96200422ebacc710021879526388010c3aa931c400845f7558e200430f2a2c7100218755163880108beed29c400845d7694e200422fbb2a710021175d95388010c9cc7294400864d6394a200432731aa5100219358d5288010c6aa930c4008635545862004332a92c3100219658e508801087ced2a2400843c76951200421f3b2a8900210f1d95448010c3ec929a400861c6494d200430fb22a690021871915348010c5ec9292400862c649492004317b22a4900218b191524801087ce9328400843d74994200422f39cca10021175ce650801087ce8328400843d74194200422f398ca10021175cc6508010c6aa9308400865553984200431aaa2c2100219554d6108010ccca4b08400843d76953100421fbb2a9880218799253c4010c3ac929e200861e6454f100430eb22a7880218b99252c4010c5ac9296200862e6454b1004316b22a588021c594d41c4010e2aa6a0e2008726525071004392a9283880218d59664c4010c6acab26200847576d53100429bbb2a9880214d5d954c4010e2aa929e20087155454f1004392aa4a588021c955152c4010e8aa6a96200847576946100431cb2ca9080218e59554840108f2eda9c200856972d4e100432cb2ca708021965955384010e34a8a9c20087195454e100423cbb6a508021565cf5284010cd2cb29420087495394a1004334b2aa508021ca9515284010e52a8a94200874a5354a10043a4a9aa5080211e5da5184010a72eba0c200863965d06100438ca9e8308021ca54b4184010a76eaa0c200863965506100438ca9a8308021ca5494184010a6ae2aa2200853575d05100431bb2e82880218dd954144010e2ca6a0a20087155350510043932928288021c954941440108ecedaa2200853575951100431bb2ca8880218dd955444010caecb29a20087155494d100432bb2aa688021c55515344010ccecb2922008725549491004333b2aa488021c95515244010e8aa6a92200863554d81100431db2ca8880218ed9554440108f4eda9a200856972d4d10042acbaca68802196d965344010cb6caa9a200871a5454d100438caa2a6880211e9db5244010ab2e7a922008569759491004335b2ca488021d254e5244010cd6caa92200872a545491004394aa2a488021d294d5244010e92a6a92200865953d851004334a96c288021d454f6144010ec2a5b0a200847a769451004398aa4a2880214e5d74144010c76cba0a200871953d051004394a9682880214edd54144010c76caa0a2008719535051004394a928288021cc9454144010
  | 1 => 0x210421ebacc9108210fdd5648841087eed2a4420843d76952210421fbb2a9108210f5d95488410c3cc929c420861d6494e210430f322a710821875915388410c5cc9294420862d6494a2104317322a5108218b5915288410cb2a7304420866952982210423dbaac1108219654d6088410cd2a4b04420861e54d8d210430eaa6c690821879506348410c3aa831a420845e7694d210422e3b4a690821179d953484108b8eca9a420864f63949210432631ca49082193d8d5248410c98c6a92420843e74d94210421eba6ca10821179cf65084108bae7b28420847970594210421ebacc8108210fdd5640841087eed2a0420843d76950210421fbb2a8108210f5d954084108baeb318420861e5498c210430eaa4c61082117dd56308410c3ca8b18420861d5458c210422fbb4a610821175da5308410c3cc9298420861d6494c210422fbb2a610821175d95308410c3cc8a98420861d6454c2104317324a4108218b5925208410c9cc7290420864d639482104317322a4108218b5915208410c9cc6a90420864d63548210431d2a4c0108218e5526008410cb4a73004208659539802104334a94c0108218e9516008410c72a8b00420865a53580210432ca9ac0108219a9496008410cd2a4b00420843f7458e500421e3a2c7280210fdd16294010878e8b14a00863554986400423bbaac3200218d55161900108bce7b28800845d73d944004237396ca200211b5cb65100108bce7328800845d739944004237394ca200211b5ca65100108eae2b28800845e73194400422eb98ca200211b9c865100108dae4328800845d7598c400430f2a4c6200218755263100108beeab18800861e5458c400430eaa2c62002117dda53100108baed298800845f7654c400422ebb2a6200211b5d66210010c5ca9310800862d54988400432729cc4200219354e62100108deeab10800862e545884004316aa2c4200219394d6210010c9aa6b10800846f769484004236bb4a4200219398e5210010c9ac7290800846f765484004236bb2a4200219398d5210010c9ac6a90800863554984400432b29cc2200219554e6110010ccca5308800866552984400431b2a2c2200218d5516110010caca6b088008655535844004333292c220021995496110010c72caa008008719535004004394a9280200211b9cb658c0108dae5b2c600846d7598a30043172a4c5180218b552628c010c9ca7314600864d5398a3004237baac5180218b951628c010c5aa8b14600864e5358a3004326a9ac5180211bdda528c0108daed294600846f7654a3004236bb2a5180218d552618c010c6aa8b0c6008655535863004334b14a1180210f9da544c010878ed2a2600843e76551300421e3b2a89802187d92534c010c38c929a600861f6454d300430e322a6980218bd92524c010c58c929260
  | 2 => 0xa9a0821475cc54d0410a5ce42a6820852d72153410421ebb6a7a08214b9cb53d0410a5ae5a9e820861d6594f410430eb2aa7a08210f5d853d0410a5ce429e820852d7214f410429d380a7a08210f5db52d0410a3ce7a96820851d73d4b4104316b2ca5a0821c394e52d0410e1aa7296820862d6554b410438729aa5a0821c354d52d041087aec296820851e7314b410428eb98a5a08214e9c052d0410cb2a7304820866952982410431caa2c1208219654d6090410cd2a4b04820851e73d51410428eb9ea8a08214b9cb5450410a5ae5aa2820853671d51410421f3b0a8a0821479cc5450410a3ae62a2820852e721514104296b90a8a08214d9c45450410a6ce928a820853771d95410421f3b6a6a08214b9cb5350410a5ae5a9a820853671d4d410428ebaca6a082187d965350410c3ecaa9a820843e7614d410428f398a6a08214b9c85350410a5ae429a82085367114d410429d380a6a08210f9db5250410a3ce7a92820851d73d49410429b38ea4a08214b5d65250410c5ecb292820870e539494104386a9ca4a08218bd955250410e1ca6a92820870d53549410421f3b0a4a0821479cc5250410a3ae6292820852e72149410429b388a4a08214e9c05250410e2ca7b0a820871553d854104393296c2a0821c954b6150410a6ced28a820843f76550410430f324a620821879915310410c5cc9290820862e64548410432ca9cc0208219a54a6010410c74a8b008208659535804104334a92c0208210f9d3658c41087ae9b2c620843d75992310421fbaac9188210fdda548c41087aed2a4620843f76552310421ebb2a91882187992538c410c3ac929c620861e6454e310430eb22a7188218b992528c410c5ac9294620862e6454a3104316b22a5188219654e608c410cd2a5304620847b75582310432ca9ac1188219a549608c410c5ca9b12620862d54d89310432729ec4988219354f624c410c5ca8312620862d541893104327298c4988219354c624c4108dced292620846c7694931042373b2a4988211b1d9524c41087ce9b28620843d74d943104237396ca188211b5cb650c4108f2e0b28620843d75990310421fbaac8188210fdda540c41087aed2a0620843f76550310421ebb2a81882187992530c410c3ac9298620861e6454c310430eb22a6188211b5d6620c410c5ca9310620862d54988310432729cc4188219354e620c4108deeab10620862e545883104316aa2c4188219394d620c410c9aa6b10620846f769483104236bb4a4188218b992520c410c5ac9290620846f765483104236bb2a4188218b991520c410c5ac8a90620863a54980310431caa4c0188219654e600c410cd4a5300620866952980310431d2a2c0188218e551600c410cb4a6b006208659535803104335292c0188219a549600c41087ce9b2c420843d74d96
  | 3 => 0xd35394810a5ae9a9ca40870e5494e5204386aa4a729021c39515394810e1aa8a9ca40852e7414e5204296ba0a7290219358c6394810a5ce930ca40852d7498652042973a0c3290214b5d06194810a9ce630ca40854d7318652042a739cc129021535ce6094810a5ce9b12a40852d74d8952042a739ec4a9021535cf62548108bee6b0aa40845c73585520421fba2c0a90210f1d160548108dcedaa2a40854e73d5152042a6b9ea8a90211b9d85454810a9ce62a2a40854d7315152042373b6a6a90214b9d35354810a5ae9a9aa40870e5494d5204386aa4a6a9021c39515354810e1aa8a9aa40846e7614d52042973a0a6a90214b5d05354810ad0e0b22a4085647158d5204326b18c6a90215adc14354810ad0e0a1aa40852e749855204296ba4c2a90214b9d06154810a5ae830aa40854e7318552042a6b98c2a9021539ce6054810a9ae7302a40852e740415204296ba020a9021539cc1054810a9ae6082a40843d76950520421fbb2a829021879526314810c3aa9318a40861e5458c520430eaa2c629021175da5314810c3cc9298a40861d6494c520422fbb2a629021879915314810c3ac8a98a40862e549885204316aa4c4290219394e6214810c9aa7310a40846f765485204317322a4290218b5915214810c9cc6a90a40864d63548520430f324c629021875926314810c3cc8b18a40861d6458c5204317324c4290218b5926214810c9cc7310a40864d63988520421f3a4c2290210f5d26114810c6ac9308a40865563984520431d324c0290218e5926014810cb4c7300a40865963980520422f39ccba1021175ce65d08108bce632e840845d73197420423b388cba1021179ce65908108bae732c840845e73196420422eb98cb210211e9c065908108bce732a840845d73995420422f398caa1021175cc6550810c72a9b02840865953d814204334a96c0a10211e5d46050810cb2a6302840866952181420422f39cca21021175ce65108108bce6328840845d73194420423b388ca210211e9c0651081087ce932e640843d74997320421f3a0cb990210f5d065cc8108f4e032e640843e74996320421eba4cb190210f9d0658c81087ae832c640847a70196320421f3a4ca990210f5d2654c81087ce832a640843d74195320423d380ca99021531c9534c810a98e6a92640863554d85320432aa9ec2990219954b614c8108eaea30a640863554185320421f3a4ca190210f5d2650c81087ce8328640843d74194320423b388ca190211e9c0650c810a9ae5298640854d7394832042a7baa6419021535d5320c810c9eca990640864d654c832043872a26419021c3551320c810b88e29906408636719925104237b92c7288211b1c963944108bee6b14a20845c7358a510428f39ea9a0821475cf54d0410a5ce5aa6820852d72d53410428f398
  | 4 => 0x5ae5aa4a80851e73182540428eb98c12a0214b9c86095010a5ae4304a80851e73d91540428eb9ec8aa0214b9cb6455010a5ae5b22a8085387058d540429c382c4aa021479cc6055010a3ae6302a80852e721815404296b90c0aa0210fdd95415010c3aa9318a80861d5458c5404316aa4c42a0218b5516215010c3cc9318a80861e6458c5404317324c42a0219398e6215010c9ac7310a80862e64588540432731ac42a0219358d6215010cacc7308a808655639845404333314c22a0219958a6115010cb2c7300a8086696298054043172a4c5a98218b55262d4c10c5ca8b16a60862d5458b5304317324c5a98218b59262d4c10c5cc8b16a60862d6458b530421f3a4c3a98210f5d261d4c10c6ac930ea60866962983530428f3a6a729821475d35394c10a9ce5a9ca60854d72d4e53042a7396a929821535cb5494c10a9ce42a4a60854d721525304326b10c529821479d26194c10a3ae930ca60851e74186530428eba0c329821539c86194c10a9ae430ca60854e7298253042a6b94c129821479d36354c10a3ae9b1aa60854e72d8d53042a6b96c6a98211bdc96154c108d8e4b0aa60843f74581530421e3a2c0a9821179db5454c10a9ce5aa2a60854d72d51530422f3b0a8a9821539c85454c10a9ae42a2a6085587059153042aa38ac4a9821935886254c10a3ce930aa60851d74985530428f3a0c2a9821475d06154c10a9ce430aa60854d7218553042a7394c0a9821535ca6054c10a3ce8082a60851d74041530421ebb4a8298210fdd95414c10c3ca9318a60861d5498c530422fbb2a629821879915314c10c3ac8a98a60862e549885304316aa4c4298219354e6214c10c5ca8b10a60862d545885304326a9ac429821879926314c10c3ac9318a60862e649885304316b24c4298219398e6214c10c5cc8b10a60862d64588530432731ac4298210f9d26114c1087ae9308a608635649845304332b14c2298218e9926014c10c72c9300a60866a629805304334b14c0298211b9ca65d0c108dae532e860846e721974304236b90cba18211d9c465d0c108dce532c860846d729964304237390cb218211b5c86590c108f4e032c860846e729954304236b94caa18211b9c86550c108dae432a860863954d81430432ca9ec0a18211e5d46050c10cb2a6302860846e729944304236b94ca218211b9c86510c108dae4328860847671194430423d380ca218218795263d4810c3aa931ea40861e5458f520430eaa2c7a90218799253d4810c3ac929ea40861e6454f520430eb22a7a90218799263d4810c3ac931ea40861e6458f520430eb22c7a90210f9d261d481087ae930ea40863564987520432cb1cc1a90214b9d35294810a5ae9a94a40854e73d4a52042a6b9ea529021539cf5494810a9ae7aa4a40854e7315252042a6b98a9290214b9
  | 5 => 0x869663504404434ab1a8220221a99894110110d4ac4a0880884b574987304431b32a8318221a9989418c110d4ac4a0c60886a962d063044370b148318221aa589418c110d64c2a0c60886e1625063044359bb28318221ac1d9418c110d64caa0c60887326550630443c9b9a8318221e41cd418c110f44c4a0c60886b16250630443d0b128318221a8589418c11087ee8b2a608843c745953044237b92ca982211b1c9654c11096ae2322608861c64d4d304430e320a6982212d5d0614c11096ceca0a60884b476505304431c32ec8982218e194644c110b62e232260885ca72d8d304423d3b0a698221561d5434c110ab4eb1926088658658c9304432c3286498221745c4324c1109d2e430a60885b174185304425d3b682982218e197414c110b62e920a60884b876505304431c32a8298221e490d414c110f2286a0a60886b37650530442d93b282982216c1d9414c110d60eca0a60886b06550530443c939a8298221e45cd414c110f26c6a0a60887935350530443c829a8298221acd89414c110f2464a0a608879032505304432c32e6298221e4507314c110cb0ca98a60885c8724c530443c8a0a62982218d995410c110d62833006088791414c0304425aba4c3902218d9954188110d2cc6a0c408869563506204434cb1e8310221b458e4188110d32c6a0c40886b2615062044368b1a8310221acdd94188110d60eca0c40886b265506204439932a8310221acd8d4188110f24c6a0c40886b16350620443c8b1a8310221a458d4188110f46e4a0c40887a072506204421fba2ca902210f1d165481108bee6b2a408845c73595204425ab88c8902218b1935248110c58c829240884b574185204425b3b282902212d1d94148110c70cbb2240886386519120442d8b88c8902211e1d56348110b94e7b12408847a7614920442b43aa84902213a9db3248110ad4eb992408866865cc920443343286490221b258c3248110bc2e219240884d97318520442d8ba0c2902212e9db4148110c70cba0a40885b174905204425c3b282902218e1954148110f4484a0a40887a1425052044359bb282902216c9d94148110b60eca0a40886b076505204435832a8290221acd8d4148110d62c6a0a40887a27250520443d0b928290221e8d894148110f46a4a0a40887a05250520443d19928290221e80c94148110cd0cb90a40887a141c85204433432a4290221721cd2148110f428290a408863665504204426cb9cc010221ac5066008110f428290040884eb7258f104426db9ac5882216cdd941c4110d66eca0e20886b3635071044358b1a8388221acd8941c4110d62c4a0e20885e1728c210442e8b9c41082219398e62d5010c9ac7316a80864e6358b5404326b1ac5aa0219658e60d5010cd2c5306a80851e73d52540428eb9ea92a0214b9cb5495010a
  | 6 => 0x144296b90cba0a210fdd953d0510878eca9e828852f7254f4144296392a7a0a210fdd952d0510878eca96828851f7354b414428e39aa5a0a218e19560d05109b2e630282884e972181414428fb9acaa0a21471cd6550510a5ee4b2a828852c72595414429bb8acaa0a210fdd95350510878eca9a828852f7254d4144296392a6a0a210fdd95250510878eca92828851f73549414428e39aa4a0a214d9d76150510c68cbb0a82886396518141442ccb98c0a0a216a5c860505108ecec2a282886346590d41442d938486a0a216c5c24350510c68ca21a82885b27010d41442d8b8086a0a218d1964250510b64e121282885b170909414431a32884a0a216c9c04250510b62e021282885d17318141442f0b90c0a0a216c5c36550510a6ae1b2a828873170d95414429b3acc6a0a214d5d66350510c68cb31a82885b27098d41442d8b84c6a0a214ddd56350510a68eab1a82885a77258d41442d2392c6a0a216cdc16350510b60e0b1a82886346518d41442d9380c6a0a216c5c06350510b4ee4a9a82885a47254d414438aa98a6a0a214d9d66250510a6aeb31282886346598941442d9384c4a0a216c5c26250510a6eeab1282885347558941442cbb9ac4a0a21651cd6250510b66e0b1282885b070589414431a328c4a0a216c9c06250510b62e031282885977354941442ca39aa4a0a21c95485250510b64e199282885b170cc941442d938464a0a216c5c23250510a6eea9928288534754c9414429b3a864a0a214d5d43250510f0a6419282885b2700c941442d8b8064a0a218d1976050510d60cbb0282885b173d8141442d8b96c0a0a214d9d66050510b64e130282886b36098141442cbb9ac0a0a21651cd6050510b4ee4b0282885a472581414429b3a8c0a0a21659cc6050510b2ae630282885a67218141442d2b90c0a0a216c9d86050510d64ec30282885b27518141443993a8c0a0a21e49cc6050510b62e630282887917318141442c8b98c0a0a21e89c86050510b62e430282887a17218141442d0b90c0a0a218d99541cc5109d2e530662886b1419833144358a0ac198a2193d4c624c510c98a6312628863465505314438a29a8298a21a9d89414c510d48c4a0a62886b141d8131443533128218a21a9589410c510d6283300628863665507214426cb9cc190a21ac50660c8510d6282b06428864c63d492144326318a490a218d1954148510d2ec6a0a42886946350521443922928290a21ac5076048510d2cc6a084288695635042144358a0cc010a214d1d541d0110a38e6aa4808852c72552404431b32a832022117dcd65501108b8e6b2a808846f725954044236392caa02210f9d85450110a68eaa0a808863765505404429cb84a8202210fdd95410110a38e6aa0808852c72550404431b2a2c2202218d5516110110c6ccaa08808
  | 7 => 0x6984211e9d8534c2109b4ec29a61085587550d30842ad3ac64984213a5c8614c210974eda0a61084b87650530842e4392629842117dd9530c210da2c2980610854e73d4b208432731ca5104219398d5288210cb2cb31c41086596558e2084368b1ac310421a658f4188210d32c6a0c410854e73d4920842373b0a4904218ed9464482109e0e2b1a41085ca73d8920842e539ea490421785c752482108f4ec29241084ea7614920842b43aa84904215a9d73248210d92c619241084d973185208425d3b682904212e1d94148210b90e690a410846f765482084370b0a40104218d59664c4210c6acab26210863965993108431cb2ac9884213adc963c42109b6e6b16210861f6418d5444327b1ec4aa2219318f6255110c5ec8312a88864f631895444326318c4aa2219618f6055110cd0c5b02a88843f76550544428e39aa82a2214b1c954151108bce6300a88845d731805444237390c02a2211b5c8601511087ee8b04a68843c74582534430e326c6a9a218bd936254d10c58c9b12a68862f641895344316320c4a9a2193d8c6254d10cc8c5b0aa68863864d81534422fbb2a629a21471d15314d10a98e4a98a68843e74984534421eba4c229a210f9d06114d1087ae8308a68846e721845344236b90c229a211b9ca6014d108dae5300a68846e72d974344236b96cba1a211d1d561d0d108dce5b2c868846d72d964344274b94c121a211e1d56090d108dee4b2a868846c72595434423db82caa1a211bdc96510d108d8e4b28868846e721944344236b90ca21a211d1d56110d10ca8a6b08868847875580434431c2a2c021a210fdd16094910878e8b04a48861f64d8d524430e326c6a922187d906354910c38c831aa48862c64d89524432631ec4a92219518f6154910c70c9b02a48846f7654852442963a2a429221531cd521491087ce9308a48843d74984524421f3a0c2292210f5d061149108bce6308a48845d73184524422f39cc029221175ce60149108bce7b2e848845d73d97424423a3aac3a1221179cf65909108bae7b2c84884d973982424423c3aac12122117dcd65509108b8e6b2a848847b70595424422fb9aca21221171cd65109108bce6328848845d73194424423a3aac2212219914961109108f0eab00848863854580424421f3a6cb992210f5d365cc9108f0eab06648843e74d96324421eba6cb192211e1d5608c91087ee8b2a648843c74595324423bb8aca992210fdd1650c910878e8b28648843e74194324421eba0ca19221535c8530c910a9ae6290648854e754c832442a63aa64192212d5d2610c9108e8eab0864886c532584324423c3aac0192219614d600c910cd0a4b00648863854583414429ab8ecba0a2147dcd65d0510a38e6b2e828852f725974144296392cba0a21479cc65d0510a3ae632e828852e721974
  | 8 => 0x26008710c72a9300438863a5458021c431caa2c010e219a9496008710cd2a4b0043886b14158021c431b2a2c3a06218d5536150310b60e0a0a818861e5498c40c430eaa4c620621879516310310c3aa8b18818862e5498840c4316aa4c4206218b9516210310c5aa8b1081886355498440c431b2a2c2206218d5516110310d2cc6a0881886956350440c43533128220621a95894110310d62c2a00818854c7254f30c425aba4c3986218b952628c310c5aa9314618862e5458a30c4316aa2c518621a9989418c310d4ac4a0c618843d75d9130c421eba8c8986212d5c4644c31087ced2a2618843c7655130c42a6392a6986212d5d0614c31096ceca0a61884b47650530c42a639aa5906212d5d261c8310c3ca931c418861d5498e20c430f2a2c710621875516388310d2cc6a0c41886956350620c421ebaec8906210f5d4644831096ae2322418843e7695120c421e3b2a890621531cd524831096ae830a41884b67650520c425a3b282906210fdd95415210c9cc7310a90864d63988548432731ac42a4219358d6215210cacc6b08a908655635845484333312c22a421995896115210a9ce5a9ca70861d7319153842a7396c6a9c2117dd95314e108dce432e870846d721974384237396cb21c211b5cb6590e108dce532c870846d72996438428eb98a921c21471d15390e109d2e5304870846e729954384236b94caa1c211b9c86510e108dae432887086385458043842a739ea5294218b5c86454a10a9ce7b12a50846f76548528422f398cba1421175cc65d0a108bce7b2c850845d73d96428422f39ccb21421175ce6590a10a5ae42a4850852c7454a428426cb9cc121421179ce6550a108bae732a850845e73194428422eb98ca214218e1516010a1087ce9b2e650843d74d973284334a94c1994210f9d3658ca1087ae9b2c650865953982328421fba2ca994210f1d1654ca109e2e030a650843f74594328421e3a2ca194210f9d0650ca1087ae8328650854d7294c32842a6b9ca41942153dd5320ca10a9aea99065085c4714c83284297396a7a0c214b5cb53d061087eeca9e830851e73d4b418428eb9ea5a0c210fdd952d0610c72a830283084d9731814184274b90c0a0c21479cc6550610a3ae632a830852e721954184296b90caa0c214b9cb5350610a5ae5a9a830843c7654d418428f39ea4a0c21475cf5250610878eca9283085997318141842d4b90c0a0c213a5ca60cc610c9ca6312630864d53189318426cb9cc190c219318e5248610c98c6a92430843e76151408421fbb2a8204218d9516110210c6aa8b08810854e72d4f308432729cc5184219354e628c210cd2cb31461086696558a3084370b12c318421aa58b418c210d52c4a0c610854e72d4d308422f3b0a6984218ed94644c210b94e5b1a61085ca72d4d30842e8b8ea
  | 9 => 0xae4298658846d76d4832c42a6b98a419621539d5320cb10a98ea990658864f654c832c4326b2a6419621c3951320cb10e1aa899065884b57498432c431aaa4c2196218d551610cb10d8a64b08658843d76d4f41c4297b92a7a0e214b1c953d071087aec29e838852e7214f41c4296b90a7a0e210f5db52d0710a3ee6a96838851c7354b41c421ebb0a5a0e21479cc52d0710a3ae629683886395498241c421f3b0a8a0e210f9db5350710a5ee4a9a838852c7254d41c421f3b0a6a0e214b9c85350710a5ae429a838843e76d4941c428fb9aa4a0e21471cd525071087cec292838851e7314941c428eb98a4a0e216c5c35450710c6ecaaa283884767615141c425b3b0a8a0e214d5d64350710a6eeaa1a83885b37050d41c429abac84a0e214ddd54250710b66e0a1283885357598d41c429bbaac6a0e2169dc96350710b48e4b1a83885b37058d41c42d8382c6a0e212d9db5350710b4ee4a9a83885a47254d41c425b3b0a6a0e21c554c5350710b4ce429a83885a57214d41c429abacc4a0e214ddd56250710b2ee6b1283885947358941c42d9b82c4a0e216c1c1625071096ceda9283885977354941c42ca39aa4a0e212d9d85250710b2ce629283885957314941c4392a90a4a0e214ddd53250710a68ea9928388536750c941c429aba864a0e21e14c83250710c6ecbb0283886376558141c42cbb9ac0a0e21651cd6050710b4ee4b0283885a47258141c42cb398c0a0e21655cc6050710b4ce430283885a57218141c4358b00c0a0e210fdd95410710c74a930083886b14158041c42a6b90a798e210f5d6648c71087eeab24638843d7695231c421fbb2a918e21531c9538c710d6282b04638845e7614d31c42a6b90a698e218b953624c710c5aa9b12638862e5418931c4316aa0c498e2193d4c624c710c98a631263887145350531c4353b128298e21a9189414c71087aeb320638843f7559031c421ebb4a818e210fdd9540c7108beeca98638854c7254c31c43172a4c418e218b552620c710c5ca8b10638862d5458831c432729ac418e219354d620c710e2aa6a0863886a66250431c4352b128218e218e952600c710c72a9300638863a5458031c431caa2c018e219694d600c710cb2a6b0063886b14158031c42a6b98a590e210f5d6648871087eeab24438843d7695221c421fbb2a910e21531cd5288710d6282b04438861e54d8d21c430eaa6c690e21879506348710c3aa831a438864c63d4921c42373b0a490e21535cc5248710c98c629243886976350521c434a31a8290e21c9149414871087aeb320438843f7559021c421ebb4a810e210fdd95408710c3ca9318438861d5498c21c430f2a2c610e21875516308710c9ac7290438846f7654821c42a639aa410e219358d5208710d2cc6a0843886956350421c4392a928210e218e95
  | 10 => 0x54e72d4d30082ad386a698041179d8534c020a3ae829a60105557114d300821f3a0ca180410f5d0650c0208beeca98601046f755883008296ba0a790041595c453c8020e4aa2a0e401046d7694a200832731ca5100411e5da5288020e62a2a0c401062f65d912008317b28c8900411b9db54480208dcec29a401052d7414d20082b2b88a6900418bd974148020958eca0a401062f655052008392a8a8290041539ce5048020ad2ea20240107295410120082e4b988090041785c44048020ad2eb18240105a8744c120083a429a60900418ed976448020c76ca32240105c973d8920082b4bae84900415add53248020c76cba0a40104b876505200831db2a8290041cc5454148020ec2a390a40105cb734852008297396c72a6214b5cb6395310a6ce3b1ca9885367118e54c428f39ec52a621475cf6295310a6ce3b14a9885367118a54c428f398c32a621475cc6195310a5ce430ca98852d7218654c4297b92c6aa6214b1c96355310a76e0b1aa98851f7358954c428e39ac4aa6214edc16255310a3ce730aa98851d7398554c4297394c2aa6214b5ca6155310a3ee6b02a98851c7358154c4297b92c0aa6214b1c9605531087eecaa0a98862e54d8953c4316aa6c4a9e218b9506254f10c5aa8312a78864f6318953c421ebb4a829e210fdd95414f108beeca98a78854c7254c53c43172a4c429e218b5526214f10c5ca8b10a78862d5458853c4326a9ac429e218b9926214f10c5ac9310a78862e6458853c4316b22c429e219398d6214f10c74c8b00a7886396458053c4335312c029e219a5896014f108dce5b2e878846d72d9743c431b2a2c3a1e211b9c86590f108dae432c878846f7259543c4236392caa1e218e5506050f108dce4328878846d7219443c431b2a2c221e21879536354b10c3aa9b1aa58861e5418d52c430eaa0c6a9621935c86354b10c98c7b12a58843d7695052c421fbb2a829621879526314b10c3aa9318a58861e5458c52c430eaa2c6296211bdd95214b10a98e6a90a58864d6354852c430f324c629621875926314b10c3cc8b18a58861d6458c52c4326392c6296219358e6214b10c74c8b00a5886396458052c432d31ac0296219658d6014b108bce7b2e858845d73d9742c431b2a2c3a1621179cc6590b108bae632c858845f7359542c422e39acaa16218e5506050b108bce6328858845d7319442c431b2a2c2216210f9d265ccb1087ae932e658843e7419732c421eba0cb99621531c953ccb10a9ae6296658843e7499632c421eba4cb196210f9d0658cb1087ae832c658854d7214e32c42a639aa5196210f9d2654cb1087ae932a658843e7419532c421eba0ca99621179da534cb10a98e4a9a658846e7694932c42a639aa4996210f9d2650cb1087ae9328658843e7419432c421eba0ca19621175db530cb10a9
  | 11 => 0x4822f39cc1aa041175ce60d502087eecaa0a81061d5458c540831aaa2c22a041879916315020c9cc7310a81064d63988540832b31cc22a0419558e6115020cccc5308a81063664584540832b31ac22a0419558d6115020cccc4b08a81063674584540832cb1cc02a0419c586601502087ce930ea61043d74987530821f3a4c3298410f5d26194c2087ce830aa61043d74185530822fbb2a629841875915314c20caaa6b08a61043d71990530821fb8ac829841875926314c20c5ac9310a61043e74984530821eba4c2298418d9926114c20c6ac9308a61063674984530831aba4c2298418d9916114c20c6ac8b08a610656635845308333312c2298418d9d16114c20c6ae8b08a610639649805308338b0cc0298411b9c865d0c208ece232e8610475711974308237394cb218411d9c46590c208eae232c861046d7598a4308237baac5218411e5d66090c208dce532a861047a70995430823b388caa18411d5c46550c208dce4328861047671194430823ab88ca218411e9c06510c208bce7b2c841045d73d96420831caa4c1210410f9d3658c82087ae9b2c64106595398232082a6b92a619041535ce520c820a9eea990641063671992510821f3a0c6a88410f5d063544208eeeca88a21063564544510832ab1aa228841479cc54d0420a3ae62a6821052e72153410829ab8ecba0841479cc65d0420a3ae632e8210535711974108297396a7a08410f9d853d042087aec29e82105367114f410829ab88a7a084117dcd65504208b8e6b2a821045e73195410822eb98caa08414d9c75450420a3ce62a2821051d731514108297390a8a08414d9c454504208daebb12821053674945410831caa0c0a08414d5c66550420a3ee6b2a821051c73595410829bb8acaa0841479cc6550420a3ae632a821052e721954108297396a6a08414d9c75350420a6ae3a9a821043e7614d410821ebb0a6a08414d9c45350420a6ae229a821052d75d89410829abaec2a08414d9da5150420c6ced28a821053676545410829a3b2a2a0841c9d895150420e48c4a8a821073151d81410829cba8c0a08418e5946050420d50c4302821073151181410821f3a6cb188410f5d3658c420c6ac928c621063564546310821f3a0ca988410f5d0654c420c9ca6312621064d531893108274b80c4988419918a514c42087ce9b28621043d74d94310832631ca4908418d5925108420caac7288421063564544210832ab1aa2108419c5466008420c3cc7a0ca01061d63d06500830f31a83280418758d41940208bce7b2c801045d73d964008237baac520041179cf65100208bae7b28801045e73194400822eb98ca20041879516310020c3aa8b18801062d54988400831b2a2c2200418d5516110020a9ce5a9e601051d7414f30082aab88a7980419394e628c020c9aa73146010
  | 12 => 0x18a410f5db548c52087eec2a4629043d76152314829ab88a918a41b20c9608c52087ce9b2a629043d74d95314829ab88a898a41179da534c520aa8e2a9a629062f54d8931483162a6c498a413a9c3624c520c5ea8312629062c541893148327298c498a419354c624c52099ced992629064c65cc9314821fba2ca18a410f1d1650c52087ce8328629043d74194314821f3acc818a410f1d5640c52087eedaa0629043d76d50314821fbb0a818a410f5d8540c5208baeda98629062f5498831483162a4c418a418bd51620c520c58a8b10629064f53588314832629ac418a4193594320c520ccac5a88629074432144314831daa4c018a418e152600c520c76a8b00629063854580314832da9ac018a419614d600c520d9064b00629067351580314822f39ccb90a41175ce65c8520a6ae22a642904ce7399721482a6b9ccb90a411b9d764c85209d0e0b26429062e6515321482d2b88a990a413a9c263c85208daeda9e429046f7654f214832631aa790a41591c553c8520a9ae628e429052e75d0721482963aa8390a41339ce60c8520ad4ea306429043e75992214821e3aac910a410f5db548852087aec2a4429061f54d8d214830e2a6c690a4187d506348520c38a831a429065463d45214832a318a290a418e1536048520c70a830242904cc735912148274382c890a41339ce63485209d4e131a429064e7518d2148326ba8c690a41a3d506348520d18a831a429046e76d4d214832631ea690a419318d5348520ac8e2a9a42906c463d4521482a6b98a290a419318c5148520e4ea828a42906c46314521482973ae8290a41a318f4148520a58eaa0a429068c63505214839228a8290a41b218f6048520d96c6302429043f76d50214821ebb6a810a410fdd8540852087aec2a0429053571150214830faa4c610a41871526308520c3ea8b18429061c5458c214831daa4c010a418e1526008520c58a9316809062e6590a4048317aa0c4a024187d526310120c38a9318809061f5458c404830e2a2c6202418bd526210120c58a9310809062f5458840483162a2c4202418b9964210120c6ea9308809063454984404831baa2c2202418d1516110120d4c84b0880905387550040482d43928020241ac5854010120c58a9316609062c5458b304832629ac5982418bd52628c120c58a9314609062f5458a30483162a2c5182410f9d3654c12087ae9b2a609043f74595304821e3a2ca982410f9d7644c12087cea322609043e76d51304821e3b6a8982410f9d8544c120878ec2a2609064d650c9304838c2a260182414e1d541c8120dc2c390e40905c873487204830faa4c710241871526388120c3ea8b1c409061c5458e204826739ec910241a3d526388120d18a931c409068e63d0620482963aa8310241a398d4188120d4ac2a0c40906ca63d4220
  | 13 => 0x64509208dcec2a284906ab6418142482753a8c0a12419a9d46050920d56a830284906a8541814248274b88c0a12418b1526210920c70a930664906385458332482373aec9992413a9c364cc920ac8e2a9e64904ea7598332483353acc199241aad5260cc920d50a930664904e97198332482aa38aa719241179d8534c920a9ae5298649045f7654c32482aa38aa619241c3d51320c920e18a8990649046e75d903248274382c8192418b994540c920b92e1298649046f7654c32482b238aa61924133dd9530c920e1ea8a98649070c5454c32482e238aa61924172dc1530c920a9eeca98649064f7654c3248387ba2a619241c31d1530c920e8ee2a98649054c7154c32483a238aa619241511c5530c920a9ee0a98649074b7054c3248326a9ac2192414d5c764d4520a6ae2326a29043e7498f514821eba4c7a8a410fdd163d4520878e8b1ea29043e76d51514821f3b0a8a8a4187d536354520c38a9b1aa29061f5418d514830e2a0c6a8a414d5c75414520a6ae22a0a29061f5498c514830e2a4c628a4187d516314520c38a8b18a2904777654451482aa39aa228a41879926314520c3ac9318a29061e6458c514830eb22c628a4193dc96314520c98e4b18a2906547158c5148236bb66428a419358f3214520c9ac6190a29063a64580514831cb22c028a419698d6014520cb2c6b00a29062c5498b41483162a2c5a0a413a1c162d0520a58eaa1682905a87050b414828f39ecba0a41475cf65d0520a6ae3b2e8290535711974148316b90cba0a418d5c465d052087ced29e829043d7694f414821fbb2a7a0a410f1d953d0520a6ee2a9e82905347154f414831632cc5a0a418b19562d0520b50e0b16829052e75ccb414831732e65a0a416a9c332d0520c5cca196829070d530cb414828f398a3a0a41475cc51d05208bce632c829045d731964148317aa4c520a418ed52609052087ced2a2829062c6590941482963aa84a0a418b1954250520b50e0a12829043e75995414829ab8ccaa0a418d5c66550520a3ee6b2a829051c73595414829bb8acaa0a414edc16550520c5ae432a829043e7694d414821ebb4a6a0a410fdd95350520878eca9a82905377154d414829a38aa6a0a414d9c45350520a6ae229a829052e75989414831632cc4a0a41695c66250520a58eab12829062c6558941482c639ac4a0a4169dc56250520b50e0b12829052e75cc9414831632e64a0a416a9c33250520c58ca192829070d530c941482d2b8864a0a41479cc5150520a3ae628a829045e73194414822eb98ca20a410f9d6641052087aedaa0829062c54988414831c2a4c020a410fdd165cc520878e8b2e62905547154f31482aab98a398a41d1cc851cc52087ee8b2c629043c74596314821f3a0cb18a410f5d0658c52087ceb324629043c75592314821fbb6a9
  | 14 => 0xe9b2c631061e6494e318830eb24a718c4187991538c620c3ac8a9c631065953982318832ca9ac118c419394f624c620c9ca6312631064d53189318821f3a6ca18c410f5d3650c620c3cc9298631061d6494c318830f322a618c4187591530c620c9ca7310631064d53988318832729ac418c419354d620c620cb2a7300631065a53580318832ca9ac018c41879925388620c3ac929c431061e6454e218830eb22a710c418d5925188620c6ac8a8c431065953982218832ca9ac110c41175d763486208baea31a431045e7694d218822e3b2a690c41175da5308620c3cc9298431061d6494c218822fbb2a610c41879915308620c3ac8a98431065a53580218832ca9ac010c419394e6290220c9ca6b14811045d7598c408822fbaac620441175da53102208beeca98811064e539884088326a9cc4204418b5516210220c9ca6b10811064d53588408832b29cc2204419554e6110220c6ca8b08811063554584408832b29ac2204419554d6110220e32a6a0081106b161500408832729cc5184419354e628c220c9ca6b14611061f6494d308830e324a69844187d91534c220c38c8a9a611064e53988308832729ac418441539cf54c8220c9acb29e411064d6554f208838729e8390441c394d41c8220e4aa2a0e41106596594f208832cb2aa790441639cf62d5120a5ae5b1ea89053970d8f544828f39ec5aa241475cf62d5120a3ce630ea89051d731875448296b90c3aa2414e5c061d5120a3ce7b06a89051d73d83544821fbb2a82a2414b5cb6315120a5ae4318a8905367118c544829ab88c62a2414e5c06315120a3ce7b10a89051d73d88544829b38ec42a2414d5c76215120a5ae5b08a89062d62d845448316b12c22a241479cc6115120a3ae6308a89052d72184544829cb80c22a2410f9d261d4d2087ae930ea69043d71992534821fb8ac929a418b9916294d2087ce930ca69043d74986534831d322c129a410f9db5454d2087cec2a2a69063754d85534831a2a6c2a9a418dd506154d20c68a830aa69043d71d91534821eb88c8a9a418dd936154d20c68c9b0aa69063774d85534831a3a6c2a9a410f9d06154d2087ae830aa69063764185534831a320c2a9a4195d8c6154d20ccec430aa69063674185534831aba0c2a9a41995c86154d20ce2e030aa69045f7654c53482aa38aa629a410f9d26114d2087ae9308a69047671d97434823ab8ecba1a418b15262d0d208d8eab1686904e87058b4348236b96cb21a411e5c36590d208eee2b2a86904747159543482373aec4a1a418bd506250d208f4ebb02869063b54181434823b388ca21a411d5c46510d20c58a9310869046c7558843483162a2c421a418e1526010d208f0eab00869063854580434831c2a4c1a12418b99754909209d4e131c84904ce73982424831daa0c0a12418b197
  | 15 => 0x6e76d4d21c832631ea690e411b1d95348720c98c6a9a439064c6394521c834631e8290e41a318d4148720ce2a2b00439051e73d5240c821f3b4a8a06410f5db5410320a3ce7aa081906375458440c831a2a2c220641a99096110320c38c929a619061c6454d30c8326a98c4986419398d62d5220cb2c7306a91066962983548821fbb2a82a4418d5516115220c9cc6b10a91064d63588548832b31cc22a4419558e6115220ccac5308a91063664584548832b31ac22a4419558d6115220ccac4b08a91063674584548821f3a4c3a9c410f5d261d4e2087ce930ca71043d7498653882ab388a929c41555c45494e20a9ae5b24a71055a70192538828f3a6c529c41475d36294e20a3ce930ca71051d7498653882a7b92c329c41479d06194e20a3ae830ca71054d7218653882ad380c329c41479d06094e20a3ae8304a7105567118253882aab88c129c410f9d06154e2087ae830aa71045e76d51538822f3b0a8a9c41559c45454e20aaae22a2a71055870591538828fba2c4a9c41471d16254e20aaee2b12a71055471589538828f3a4c2a9c41475d26154e20ab4e130aa71054f72585538828f3a0c2a9c41475d06154e20a9ae430aa71055a70185538822fbb2a629c410f9d26114e2087ae9308a71066962980538823b388cba1c411d5c465d0e20c9ca7314871064e5358a438832ca9ec0a1c419654c6050e208ece2328871047571194438832d29ac021c414d5c45490a2087ced2a2851065953d81428832ca98c0a14410f5db5410a20a6ae22a0851065a53583328832ca9ec099441879925394620c3ac929ca31061e6454e518830eb22a728c418d9c66494620c74c9304a31063964982518822ebb4a628c41879925314620c3ac9298a31045f7654c518830f322a628c418759153146208eeeca88a31063564544518822f39ccba0c41175ce65d0620a3ce7aa6831051d73d53418828f398a9a0c41475cc54d0620a6ae3b2e831051e73997418828eb9ccba0c41479cc65d0620a3ae632e831053571197418822f39ccb20c41175ce6590620cb2a7304831065953582418822f398caa0c41175cc6550620a3ce7aa2831051d73d51418829b38ea8a0c41479cc5450620a3ae62a2831053671151418832729ec4a0c419394c6250620a6ce928a831051e73995418828eb9ccaa0c414d5c66550620a6ee2b2a831051e73195418828eb98caa0c414d9c75350620a6ae3a9a83105367114d418829ab88a6a0c41c394f6250620e1ca6312831053575d85418838b29ec2a0c41c554f6150620e2ca728a831071553945418829b3b4a2a0c418d9da5150620e64e128a831071653545418838aa9aa2a0c414d9d95150620a68eca8a8310727625454188392312a2a0c41179ce65106208bae7328831065953980418832ca9ac020c410f9d3658c62087a
  | 16 => 0xc28f398caa08614b9c86550430a5ae432a821851d75d8d410c29abaec2a08614d9da5150430c6ced28a821853676545410c29a3b2a2a0861c5d8d5150430e28c6a8a821873151d81410c29cba8c0a08618e5946050430d30c6302821873151181410c327298c4988618d592510c430ccac5288621863564544310c332b12a2188619c546600c43087ce9b2c421843d74d96210c31ab24a3108618d591518843087ce832a421843d74195210c26cb80c6908619318e5248430c98c6a92421865463945210c21f3a6ca108610f5d365084308beeab1c801861d5498c400c3172a2c4200618b5516210030c6ca8b08801863554584400c38aa8a8398061175da538c0308f2ed29c601873151506300c30fb2ec89806187d94644c0308bcedaa2601861f65d05300c24e3b2829806187d95414c030e2aa2a0a601855975101300c38caa08098061725c8404c030ba2e2202601863b65d91300c31db28c898061725cb634c030ab2eba1a601855b754c9300c31db2e82980612e1d9414c030c76caa0a601873151505300c3a8a8e629806172dc9314c030c9ac7316a99065a6358354c8335312c1aa641479cf5495320a3ce7b22a99043f7655054c821eb8cc9a9e410fdc564d4f2087ce930ea79043d7498753c831d322c1a9e41479d35394f2087ce930ca79043d7498653c828f3a6c6a9e410f9d06154f2087ae830aa79045f7654c53c821f3a4c229e410f5d26114f20cd4c4b00a79047671d9743c823ab8ecba1e419354e62d0f209d2e530487904767119443c823ab88ca21e41339ce6090b208dcec2a2859063a5458042c8275386c9996419694d600cb208deeca98659054f7654c32c8327bb2a619641531c5530cb20c9aa6b08659046d760ca51c821f3a6c6a8e410f5d363547208eeeca88a39045e73d9741c822eb9ecba0e41179ce65d07208bae732e839051e73d5341c828eb9ea9a0e41479cf65d0720a3ae7b2e839053571d9741c828f39ccba0e41475ce65d0720a6ae232e839043e76d4f41c821ebb6a7a0e41c354c32d0720a3ce7aa2839051d73d5141c831daa0c0a0e413a5c86050720d5484302839051e7399541c828eb9ccaa0e414d5c66550720a6ee2b2a839043e76d4d41c821ebb6a6a0e414ddc55350720a68e2a9a83905367114d41c829ab88a6a0e41695c66250720b18e6b1283905a77158941c82d4382c4a0e41c354c3250720b4ae2192839063a6518141c82d4b90c0a0e41aa988605072087ce932e639043d7499731c821f3a6cb18e410f5d3658c720c9eca194639064e5318931c8326a98c498e41339db324c72087ce9b28639043d74d9431c8326b286418e41b20c9600c7208deeca9e439064c6354f21c826739cc190e41331cd64487209d0e0b22439064f6518d21c8326ba8c690e41b29c06348720d92e031a43904
  | 17 => 0x8a61c5d50514c530d88c428a629851e75d05314c3463168298a61471d5414c530d18c4a0a629871451505314c364316c098a61b2d88604c53087eedaa0629843d76d50314c21fbb0a818a610f5d8540c530a6ae22a0629862f54988314c3162a4c418a618bd51620c530c58a8b10629863b54980314c31c2a4c018a610fdd165c8530878e8b2e42984da70d8f214c2b2b90a390a61d18c851c853087ee8b2c429843c74596214c21f3a0cb10a610f5d0658853087ceb324429843c75592214c21fbb6a910a610f5db548853087eec2a4429843d76152214c29ab88a910a61b20c9608853087ce9b2a429843d74d95214c29ab88a890a6187d536348530c38a9b1a42984da70d8d214c30faa0c690a6187150634853099ced192429864c658c9214c21fba2ca10a610f1d1650853087ce8328429843d74194214c21f3acc810a610f1d5640853087eedaa0429843d76d50214c21fbb0a810a610f5d85408530c3ea9318429861c5498c214c30faa2c610a61871516308530c9ac7a90429864d63148214c266bb06410a61935943208530caac7a88429874432144214c31daa4c010a618e1526008530c76a8b00429863854580214c335a92c010a619a1496008530d9064b00429867351580214c30e2a4c7a0261879964390130c3ea831a809861f5498c404c30e2a4c62026187d516310130c38a8b18809861e6590c404c317aa4c4202618b1526210130c5ea8b10809862c54588404c31baa4c2202618d1526110130c6ea8b08809863454584404c34b21ac2202614e1d54010130b30e6a0080986b161500404c29c3aa8398261b458731cc130b90e498e609862f5498a304c3162a4c5182618bd51628c130c58a8b1460984ce72d92304c347aa4c518261a3152628c130d1cc5a0c609851c75506304c3473128318261a5585418c130d94c5a84609843f76550540c316aa2c42a0618d5516115030c9cc7310a81862e64588540c32731ac42a0619598e6115030cccc5308a81866562984540c31b322c22a0619598d6115030cccc4b08a81866562584540c31b3a2c22a0619a58a6015030ce2c3300a81863954982430c21f3a4c3290610f5d2619483087ce830aa41843d74185520c237bb2a4290618b5915214830ccaa4b08a41845f7558e420c23b388caa10611d5c46550830a9eea990641863671992510c21f3a0c4a88610f5d062544308eeeca88a21863564544510c332b12a228861479cc54d0430a5ce42a6821852d72153410c29ab8ecba08614b9c865d0430a5ae432e821853571197410c237b92caa08611b1c965504308dce432a821846d72195410c29b38ea8a0861479cc5450430a5ce42a2821852d72151410c29b388a8a0861175d76350430a6ce928a821863954181410c29ab8ccaa08614bdc96550430a58e4b2a821853771595410
  | 18 => 0x45493087cec2a2a49863754d85524c31a2a6c2a92618dd506154930c68a830aa49846f76548524c2b238aa4292610f9d2611493087ae9308a49861c5498f424c26c382c7a126187d506350930c76a8302849847671194424c23ab88ca21261871526310930c38a8b18849863854980424c31c2a2c0212618e152608c930c70a8b0464984da70d92324c26d3acc119261969d6608c930d36a9304649869854982324c26cb8cc119261c3d51320c930e18a8990649845e75d90324c26c382c81926187994540c930b92e129064984cf76548324c387aa2a419261c3151520c930b88e2a9064985cb70548324c29ab8ec9a8a614d5c464d453087ce9316a29843d7498b514c21fba2c5a8a610f1d162d453087cedaa2a29843e76151514c317aa6c4a8a618b1536254530c5ea8312a29862c54189514c29ab8ea828a614d5c45414530c5ea9310a29862c54988514c317aa2c428a618b15162145308eeeca88a29856472544514c317324c428a618b5926214530c5cc8b10a29862d64588514c327b9ac428a61931cd62145308baed190a29864d628c8514c326b106428a618e9916014530c72c8b00a29866a62580514c334b12c028a618715263d0530c38a8b1e82984d87058f414c28e3aa87a0a61661c143d0530a5ce5b2e829852d72d97414c29ab8ecba0a614d5c465d0530c3ae632e829863571197414c30e32cc7a0a618719563d0530b30e0b1e829861e658cb414c2cd38465a0a618799432d0530a5ce428e829852d72147414c237390cb20a611b5c86590530c3ea931c829863b54982414c21f3b4a8a0a61871964350530a38eaa1a829861c6550d414c2cc38286a0a610f9d66550530a6ae332a829863571995414c297b92caa0a614b1c96550530a6ee2b2a829853b70595414c30eb98caa0a61479d66350530c38cb31a82985957198d414c28e3aac6a0a61871956350530b18e4b1a82985977158d414c2cc382c6a0a614d9c45250530a6ae2292829861c658c9414c2cd38464a0a61871943250530b2ae2192829852e72145414c296b90a2a0a611b9c865105308dae4328829843e75990414c21ebb6a820a61871526310530c70a9300829846e72997314c236b94cb98a614d5c454cc53099ce532e629854d72997314c22f3aec998a61361c164cc530c3cca2a6629859571153314c26d384c598a61535c851cc530a3ceba0e629851c75507314c267394c198a61569d460cc53087ceb324629843c75592314c21ebb6a918a610f5d8548c530c5ea9b12629862c54d89314c317aa0c498a618b150624c530cc8c5a8a629866462145314c31c2a6c098a618e150604c530998e4b2262984d870591314c3273a8c498a61935d4624c530d1ea8312629868c54189314c22f3b6a498a619318b524c530d88c5a8a629854d72145314c326310a29
  | 19 => 0x8a88a31846e72997418c236b94cba0c614b9cb54d0630a5ae5aa6831852e72153418c296b90a9a0c614d5c765d0630a5ce532e831852d72997418c297390cba0c614b5c865d0630a6ae232e831846e72996418c236b94cb20c619a54a6090630cd2a4b04831846e72195418c236b90caa0c614b9cb5450630a5ae5aa2831853671d51418c297390a8a0c614b5c85450630a6ce22a2831864f63949418c32631ca4a0c614d9d25150630a5ce532a831852d72995418c29ab8ccaa0c614ddc56550630a5ce432a831852d72195418c387b1ca4a0c61c318e5250630a6aebb0a831872652d85418c392a96c2a0c61c994a5150630e4aa528a831853676945418c31b3b4a2a0c61cc9c25150630e4ca4a8a831872552545418c29b3b2a2a0c614d1d95150630e2ec6a8a831871463545418c237394ca20c611b5ca6510630cd2a5300831866952580418c317324a518c618b592528c630c5cc8a94631862d6454a318c31ab24a318c618d591518c630cd2a5304631866952582318c236baec498c611b5d4624c6308dced292631846c76549318c317324a418c618b592520c630c5cc8a90631862d64548318c335292c018c619a549600c63087ce9b2c431843d74d96218c317324a510c618b5925288630c5cc8a94431862d6454a218c334a94c110c619a5496088630c9ec7292431864c63949218c32631aa490c610f9d3650863087ae9b28431862e64948218c316b24a410c619398e5208630c9ac7290431862e64548218c316b22a410c619398d5208630c9ac6a90431866952980218c335292c010c619a5496008630c9cc7294811864d6394a408c30eaa2c6204611b5d662102308deeab10811846d76948408c32731ca4204619358e52102308deeca90811864e63548408c326b1aa4204619994a6110230ccaa5308811863654584408c31aaa2c220461999496110230ccaa4b08811872952500408c358b0a8020461539cb54cc230c9acb296611864d6554b308c3872968398461c394941cc230e2aa2a0e61186696594b308c334b2aa598461639cb63d5130a5ce5b1ea89852d72d8f544c28eb9ec5aa2614e5c362d5130a3ae630ea89852e72187544c296b90c3aa2614e5c061d5130a5ce5b06a89852d72d83544c21fbb2a82a2614b9cb6315130a5ae5b18a89853671d8c544c29ab8ec62a261475cf6215130a3ae6310a89853671188544c29ab88c42a2614e5c06215130a3ae7b08a89861d63d84544c30eb1ac22a261475cc6115130a5ce4308a89852d72184544c29cb80c22a2618e15260d0d30c3ccbaa486984da7098a434c267394c121a618ed506050d30c38cbb22869845e76151434c34db20c0a1a61369d46050d30cb4ea302869869b54181434c34c2a0c0a1a61365c46050d30c38a9318869843e74987524c21eba4c3a92610f9db5
  | 20 => 0xa5458043cc2973a6a5296610f9d26194b3087ae930ca59843e7418552cc21eba0c2a96611bdd95214b308ece3b2e859847571d9742cc32731aa5a1661365ce6090b309b4e1b24659854f7654832cc327bb2a419661531c5520cb30c9aa4b08659845d760ca51cc21f3a6c4a8e610f5d362547308eeeca88a39846e72d9741cc236b96cba0e611b9ca65d07308dae532e839852e72d5341cc296b96a9a0e614b9cb65d0730a5ae5b2e839853571d9741cc297394cba0e614b5ca65d0730a6ae232e839870d520cb41cc297396a8a0e614b5cb5450730c76a830283984d97318141cc34d218c0a0e614b9ca6550730a5ae532a83985357199541cc29bb8acaa0e61655c66350730b18e4b1a83985977158d41cc2cc382c6a0e614ddc55250730a68e2a92839870d520c941cc2cab8864a0e618e9946050730b32e6302839869a6318141cc22fbb2a598e61339ca60cc730998e4b2263984d87059131cc327b28c498e61935d4624c730d94e031263986c97018931cc326312a498e619318a514c730d18c5a0a639868c6250531cc338a8ac018e610f9d265c873087ae932e439864c6354b21cc21f3a6cb10e610f5d36588730c9eca194439864c6394921cc32631aa490e61339da324873087ce9b28439843d74d9421cc326b286410e61b20c96008730a5ce5aa4819843e7695140cc21ebb6a8206614b9cb5410330c6ea8b0881986345458440cc34b21ac2206619358e62d5230cb2c7306a91866962983548c21fbb2a82a4618d5516115230c9ac7310a91864d63588548c32ab1cc22a4619998a6115230ccac5308a91863664584548c32ab1ac22a461999896115230ccac4b08a91863674584548c29ab88a921c610f9da5450e3087aedaa0871853571150438c21f3a4c3294610f5d26194a30acce22a4a51856571152528c2a6b9ec9294615a9c06494a30a5ce9b1ca51852d74d8e528c2973a4c3294614b5d26194a30a9ee6b0ca51852e74186528c296ba0c329461535cc6194a30ad4e030ca51852e74182528c296ba0c129461599c46094a30acae2304a51843e74185528c21eba0c2a94611b9db5454a308dcec2a2a51856671151528c2b2b88a8a94615a1c16454a30a5ee8b1aa51852c7458d528c2b3b8ac6a9461591c56354a30ad6e0a1aa5185687050d528c2973a4c2a94614b5d26154a30ad4e130aa51854f73585528c2973a0c2a94614b5d06154a30a9ae630aa51856a70185528c237bb2a4294619398e5290a30c9ac7294851866952d81428c334a90c0a14619a9496010a30cd4a4b04651866952d81328c317324a528c618b5925294630c5cc8a94a31862d6454a518c31b38cc928c618e9926094630c72c9304a31846d76948518c317324a428c618b59252146308deeca90a31862e64548518c316b22a428c611ddd95114630c6ac
  | 21 => 0x30f322a61888187591530c4408daeb310622064e539883110326a9cc4188811bdd5620c440c9ca6b10622064d535883110237bb4a4188811b5da520c440c5cc9290622062d649483110237bb2a4188811b5d9520c440c5cc8a90622062d64548311031ab24a2188819998a510c440ccac5288622063664544311031ab22a21888199989510c440ccac4a886220659539803110335294c0188819a54a600c440ce2a3300622065a53580311032ca9ac0188819a949600c440cd2a4b006220672515803110338a8ac018881179ce65c84408bae732e42204b9701932110317b22a5908818d19151c84408bce732c422045d73996211025cb84c910881879925388440c3ac929c422061e6454e211030eb22a7108818b9925288440c5ac9294422062e6454a2110316b22a5108818d5925188440c6cc8a8c422063564546211022fb9aca90881171cd65484408bce632a422045d73195211022ebaec690881175d463484408bced29a422045c7694d211022f3b2a690881171d95348440c9ec7292422064c639492110317b22a49088193d8d5248440c98c6a92422065763945211032a31ca2908818dd915148440c68c8a8a422065763545211032a31aa2908819a54b6048440ce2a3b02422045e73d94211022eb9eca10881179ce65084408bae7328422045d7598c211022fbaac61088117dda53084408baed298422061e6494c211030eb24a61088117dd953084408baeca98422061e6454c211030eb22a6108818b9925208440c5ac9290422064e639482110326b1ca4108818b9915208440c5ac8a90422064e635482110326b1aa4108818d5925108440cacc7288422065563944211031b322a2108818d5915108440cacc6a88422065563544211032d29cc0108819654e6008440cd2a5300422067151980211032d29ac0108819654d6008440cd4a4b00422066952580211033928ac0108819c5456008440e1aa6a96802063561547401038b29aa3a0081c554d51d0040e4ca4a8e802072552547401031b31aa3a00818d98951d004087aed2a480204797695240103a4a9aa520081d454d5190040ec2a4a8c802043d71d95401030fb2ca6a008187d955350040c5ecb292802062f655494010386a9aa4a00818dd96515004087ceca8a802063761545401031bb2aa2a0081c594d5150040e2aa6a8a8020726525454010392a92a2a00818d9d95150040c68c6a8a8020634625454010398382a2a008196d965350040cb6caa9a80204ba76d0d4010335b2ca4a00819ad955250040e92a6a9280204ba76d094010339b2ca2a00819cd955150040e64a8a8a80207515354540103b0a92a2a00814e5d64150040974ec20a802064e6358b54cc32d31ac1aa6619a98960d5330a5ce5aa4a99852e72d9154cc21fbb2a82a661339ca6090f308bcec2a2879863
  | 22 => 0x8814c5c04354440a6ce9b12a2205347458951102abb9ac4a8881551cd6254440ae0e0b12a2205367418951102ab398c4a8881555cc6254440ae4e0312a22053576909511029b39c84a88814d5c24254440ae4e0212a22057170109511029bbb084a88814d5d84254440a6ce6212a22072672109511039938084a88814d5c04254440e62e0212a22053170109511029b3a664a88814d5d33254440ae4e1992a22057170cc9511029b3a464a88814d5d23254440ae4e1192a220571708c9511029bba264a88814d1d13254440a6ee8192a220534740c951103a299064a8881559cc6054440aaae6302a2205667218151102b2b90c0a8881559cc4054440aaae6202a2205667210151102b2b9080a8881175da53144408beeca98a22064e539885110326a9cc4288819394d6214440c9aa6b10a22046d76948511032731ca4288819358e52144408deeca90a22064e635485110326b1aa4288819594e6114440caaa7308a220666529845110332a94c2288811ddd95114440cacc6a88a220655635445110333312a228881995895114440ce2a2b06822061e6354f411030fbb2a7a0881c394e52d0440e1aa7296822062e6254b411038729aa5a0881c354d52d0440c5eeca96822071653547411038aa9aa3a0881c994951d0440e4aa4a8e822063663547411031b312a3a0881cc54660d0440c6aa2b06822073151583411025dbaac1a08818edd560d0440d34a6b068220699535834110355292c1a0881aa54960d0440d64a2b068220639515834110358a8ac1a08818c54560d0440972e031a822061c7654d411025cb80c4a0881c394e5250440e1aa7292822070e535494110386a9aa4a08818b1d95250440e2ca7b0a822071553d854110393296c2a0881c954b6150440e2ca728a8220715539454110393294a2a0881c954a5150440c6ecaa8a822071653545411038aa9aa2a0881c99495150440e4aa4a8a8220659539804110334a94c0208819654d6010440cd2a4b008220672515804110237394cb988811b5ca65cc440972e0326622061f6454f311031a322a3988811b9ca658c4408dae532c62204b970992311030f324a71888187592538c440c3cc8a9c622061d6454e3110317324a5188818b592528c440c5cc8a94622062d6454a311031ab24a3188818d991518c440c6ac8a8c622046f725953110236392ca988811b9c8654c4408dae432a622061f6454d3110236baec4988819394f624c440c9aa7b12622046d751893110327298c4988819354c624c4408dced292622046c7694931102373b2a4988811b1d9524c440ccec528a622066462945311031bb22a2988818d191514c440ccec4a8a622066462545311032ca9ec0988819c547604c4408dce5b28622046d72d943110237394ca188811b5ca650c440c3cc9298622061d6494c3110
  | 23 => 0xcc840c3ac929e642062e6454b3210316b22a5990819a54a60cc840cb4a6b06642066952583321023b38ccb190811d5c6658c840c3cc8a9c642061d6454e3210316b24a5190819654e608c840cb2a6b04642066a52582321023b388ca990811d5c4654c840972e0322642061f6454d32102a6392a6990818bd91524c840a98e6a92642047671994321023ab8cca190810f5d7640c84096ae232064204b97019032102a6b94a619081535ce520c840a9eea990642054d754c83210327b2a641908193595320c840c9ca7316a22064d5398b511032729ac5a88819354d62d4440c9cc7296a22064d6394b511032731aa5a88819358d52d4440aace7a8ca22055573d4651102b3396a328881595cb51944408dee4b1ca22046c7258e511022fb9ac528881171cd6294440acce5a9ca22056572d4e511038b324a728881c51d15394440e2cc8a9ca2205667214e51102b2b90a728881c554e4394440b62e021ca22055673d4a51102aab9ea528881d194e5294440e8aa7294a2207266494a51103a329aa528881d154d5294440e48e8a94a2207266454a51102ab398a528881555cc5294440e4aa5214a2205b17010a511029b3a6c72888159dc96394440ac8e4b1ca2205367418e51102b3390c728881595c86394440ae4e031ca22053674d8a51102abb9ac528881551cd6294440a6ce8314a2205567318a51102aab98c5288815c9c06294440e8a64194a2205567318251102aab98c128881599c86094440acae4304a22046e7218d5110236b90c6a88814d5c64354440a6ae221aa2205397010d511022f398c4a8881175cc6254440a6ae3212a22053571109511029cb8084a88811d9db5354440acce5a9aa22056572d4d511038a3a4a6a8881c59925354440e28e8a9aa2207166454d511023b3b0a6a8881599c85354440acae429aa2205357590d511038b29c86a8881c554e4354440e2ca621aa2207155310d51102d8b8086a88811d9db5254440aace7a92a22055573d4951103a329ca4a8881d154e5254440e48e9292a22072664949511039321ca4a8881c910e5254440e8ca6a92a2207455354951103923a2a4a8881c99915254440e4c86a92a22072443549511023b3b0a4a8881559cc5254440aaae6292a22053575909511038b29c84a8881c554e4254440e4ca5212a22072552909511038b29884a8881c554c4254440e4ca4212a2207255210951102d8b8084a88814d9ce6454440a6ce5322a22073170991511029b3a6c6a88814d1d16354440acee4b1aa2205647258d51102b8382c6a88814d9d06354440acce431aa2205657218d51102b9380c6a88814d5da4354440a6ce521aa2205357090d51102b938086a88815c5c04354440a6eec21aa2205357610d511038b39886a88814d9c84354440e64e021aa2205357010d5110398b8086a8
  | 24 => 0x32862a061d64d4c3150327a9ac418a819314d620c540cb6a6b0062a065853580315022fb9acb10a81171cd6588540970e0b2442a062d6414a215022f39cca90a81175ce65485408bce632842a045d731942150316b26a410a819358f5208540c9ac629042a066b525802150334292c010a818d5875190140a9ce5a9ca62054d72d4e53102ab38ea729881555c75394c408dee4b0ca62046c72586531028f3a6c529881569c36294c40c9ac4314a62051e7498653102a7b92c329881531c96194c40a3ce830ca62054e7218653102a6b90c329881569c06194c40a9ce5304a62054d729825310237390c2a98811b5c86154c40a3ce9312a62055a70989531028e3a2c4a9881935886254c40a3ce930aa62051c7458553102a7b92c2a9881531c96154c40ab0e0b0aa62051e7418553102a7390c2a9881535c86154c40ab4e030aa62054e7298153102a6b94c0a988117dd95314c40c9aa7310a62064d53588531032aa9cc2298819554d6114c40cb2a6b06862061d6594e431025cb84c5218818754d6190c40976e0b0c862065a53580431034d31ac0218812edd56010c40c76eab00862069a53580431034ca9ac0218819594e61d4840caaa730ea42065653587521032aa9ac3a9081539cf5294840a9ae7a94a42056671d4a52102b2b8ea52908117dcd61948408b8e6b0ca42056671d4e52102b2b8ea729081c31d15394840acce229ca4205657114e5210386a9c87290816a5c04394840a5ce9b1ca42056a70d8e5210326b18c7290814b9d26194840a9ee6b0ca42054c7358652102973a0c329081539cc6194840a9ae630ca42056a7018652102a739cc129081535ce60948408bce630aa42045d7318552102373b6a6a9081599c75354840acae3a9aa42070c6494d52103863a2a6a9081c319153548408dcec29aa4205667114d52102b2b88a6a90814b5d64354840e1aa721aa42070d5310d52102d4b8086a90814b9d26354840ad4e131aa42052c7458d5210326b18c6a90815a9c04354840ad2e021aa42052e7498552102963a2c2a908153dcd6154840a98e6b0aa4205687058552102973a0c2a9081539cc6154840a9ae630aa42056a7018552102a739cc0a9081535ce6054840a9ce6202a42054d73101521022ebb4a62908117dd95314840c9ca7310a42064d539885210237bb2a4290819398d5214840c9ac6a90a42065653984521032aa9cc2290819954a6114840caca6b08a420655535845210332a92c2290819a54960d0840972e131c842061d6554e4210316b2ca521081c394d5290840e1aa6a94842062d52586421025db82c3210819654e6010840cb2a6b00842066a525804210386a9aa421081aa9896010840976eab00842063b75580421034d29ac021081a654d6010840d54a4b0084206a952580421023b38ccb990811d5c665
  | 25 => 0x748c5500869cba462a80435a9ca3154021ad2e518aa010f48328c550086b5b9262a80435a1c93154021e966498aa010c7a760c5500869d3a062a80434e5d03154021ad4e418aa010d69720c550087a419062a8043cc5043154021ad4e790aa010d6873c855008795a0e42a8043ca5072154021a74e910aa010d39748855008798a0c42a804356dcd2154021ab0e690aa010f314148550087a5b9a42a80435a9cd2154021ad0e690aa010f487348550086a439a42a8043d8dc52154021e568290aa010f62414855008794a0a42a8043d85052154021e428290aa010d3a74085500869cba042a8043569cc2154021ab2e610aa010c3d76950500861fbb2a828043879526314021c3aa9318a010e1e5458c500870eaa2c628043175da5314021c3cc9298a010e1d6494c500862fbb2a628043879915314021c3ac8a98a010e3a54980500871caa4c0280439694e6014021cb2a7300a010c7b76540500871d322a0280438e5915014021cb4c6a80a010e5963540500862fbb2a629e811bdd95214b408eeeca88a3a07315198341d0398a8ac1a0e814d5c65350740a6ee2a9a83a05357194941d029bb8aa4a0e816c5c3515074096cec28a83a06b14158041d0237b92ca98e811b1c9654c7408dce5b2863a046d72d9431d022fb9aca90e81171cd65487408bce7b2843a045d73d9421d02a7396a729c811b9c86154e408dae430aa72045f7654c53902a739ea529481179cc6154a408bae630aa52046f76548529023bb8aca994811d1c5654ca4096ae232065204b97019032902a6b94a619481535ce520ca40a9eea990652054d754c8329025c3a2c0194811bdc963946408d8e4b1ca32045f7358a519022e39ac528c81471cd6454640a58e4b22a3205357110d519029ab8884a8c811ddd95114640a6ced28a8320636769454190398a8ec0a0c81cc54460506408dce532e632046d729973190237b92ca98c811b1c9654c640c9ca6312632064d531893190237396ca18c811b5cb650c6408bce732e432045d73997219022fb9aca90c81171cd6548640c98c7292432064c63549219022f39eca10c81175cf6508640c6ac2a8e812064f5358a535022fbb2a629a811bdc96114d408d8e4b08a6a064d63d4a5250237bb2a42928117dcd61149408b8e6b08a4a054e72d4d32502a739ea4992811d9c4650c9408eae232864a043e75990325032732a641928193195320c9408dce531ea2a046d7298f515022f39cc5a8a81175ce62d45408eeeca88a2a073351d814150399a88c0a0a812e9d46050540c74ea30282a069a73181415034cb98c0a0a818e14c6050540d54e430282a06a972181415031c290c0a0a818ed446050540c6ccaa0882a046f725963150236392cb18a812e1c1648c540c3ac829c62a046e729953150236b94ca98a811b9c8650c5408dae4
  | 26 => 0x8aaa2a690843695d36248421d88c7b124210f4553949210870f2a4c7a80438755263d4021c3ca8b1ea010e1d5458f500870f324a7a80438759253d4021c3cc8a9ea010e1d6454f500869d3a6a1280434e5d35094021ab4e7a84a010d5973d42500861fba2c7280430f1d16394021ab4e7aa4a010d5973d5250086ad398a928043565cc5494021a74e9a9ca010d3974d4e500878d2a4a728043c65525394021e34a8a9ca010f195454e50087a4392a7280434e9d05394021a72e829ca010d6975cca50087a4a9e6528043d254c3294021a72eba0ca010f1a53d06500878ca9e83280434edd54194021e34a6a0ca010f195350650087a4a9e43280435add52194021b90e690ca010f495348650087d0a0a43280435cdd52194021ab4e6324a010d597319250086b5390c9280435c9c46494021ad4e5b1ca010d3b7458e500869c3a2c728043d24c83294021a74e830ca010d397418650086ad398c328043565cc6194021e66e2a0ca010d3a748c6500869cba463280435adc93194021ad0e498ca010c79760c6500869d3a063280434e5d03194021ad4e418ca010d69720c6500869d3a443280434e5d22194021ab6e690ca010d5873486500862f398c8a8043175cc6454021a98e690aa010f2541485500863d3b6a8a8043569cf5454021ab2e7aa2a010c7a7615150086ad398a8a8043565cc54540218f4eda9aa010d3a74d4d500869cba6a6a8043c69525354021e32a929aa010f487294d500878d2a2a6a8043c65515354021e90e4a9aa010c7a7614d500869d3a0a6a80434e5d05354021ad2eb992a010f2a54cc95008794aa664a8043d294f3254021e92a7992a010f2a540c95008794aa064a8043d294c3254021e92a6192a010d3975d05500878d29e82a8043c654f4154021a76eaa0aa010f1a53505500878ca9a82a8043ca9532154021e52a990aa010f4a53c8550087a4a9e42a8043cc5522154021ea2a710aa010d6b7548550087952a242a8043ca5512154021b90e690aa010f4a5348550087a4a9a42a8043e85052154021ae6ea90aa010f315448550087a8a9a42a80435a1c96454021ab4e6322a010d597319150086b5390c8a80435c9c46454021ad4e5b1aa010d3b7458d500869c3a2c6a80435a1c96354021ae0e2b1aa010d6a72d0d50086b4b9686a80435c9c74354021ae2e3a1aa010d6b7250d50086b439286a80435c9c44254021ae2e2212a010d6971cc950087a499064a80435c9c43254021ae2e2192a010f4a730c950087a531864a8043d258c3254021ec4e2192a010d69710c950087b0b8864a80434e9d26154021a72e930aa010f2b32d05500879419682a80435a9ca4154021ad2e520aa010f2b32505500879419282a8043ccdc54154021e64c2a0aa010d6a7210550086b4b9082a8043d2ccb3154021e628398aa010d3a
  | 27 => 0x430f5d3658c42187aeb3246210c3f75592310861fbb4a9188430f5da548c42187eecaa46210c3d76552310870f324a71884387592538c421c3cc8a9c6210e1d6454e3108726a9cc5188431bdd5628c421c9aa6b146210d4d750ca3108727b2865188438b953624c421c5aa9b126210e4e53d893108726a9ec4988438b950624c421c5aa83126210e4e531893108726a98c498843339db324c421a9aeb9926210e4f65cc9310861f3a6ca188430f5d3650c42187ce93286210c3d74994310861f3a0ca188430f5d0650c42187aeb3206210c3f75590310861fbb4a8188430f5da540c42187eecaa06210c3d76550310870f324a61884387592530c421c3cc8a986210e1d6454c31087172a4c4188438b552620c421c9aa73106210e2e545883108716aa2c4188439394d620c421c9aa6b106210d4d750c83108726b286418843715c4320c421c6acaa086210f15535043108752b128218843e10c9410c4218f2eb3006210e3a54980310871caa4c0188439694e600c421cb2a73006210c7b75580310871d2a2c0188438e551600c421cb4a6b006210e59535803108764192c018843ac505600c421ad2e1a9e4210c6f7654f210872731aa790843c395153c8421e1aa8a9e4210e4f7654f21087263b2a7908434b5d741c8421e1aa7a0e4210d2f755072108786a9a83908430f5da548842187eecaa44210e1e6494e210870eb24a710843879915388421c3ac8a9c4210c6d7694a210878aa9a8310843c555153884218eaed2944210e1e54d8d210870eaa6c690843879506348421c3aa831a4210c5e7694d210862e3b4a690843179d953484218b8eca9a4210e3765d05210871bb2a8290843a518d4148421e2aa6a0a4210e4f73d95210872639eca908438bd965448421c5ecaaa24210e4f65d8d2108636bacc690843339ce6348421c9eca31a4210e4d7518d21087472a0c690843a355063484218dceda9a4210e4c63d4d21086b4b86a690843331da5348421a9aeb29a4210e4f6594d21086363b2a6908439318d5348421998eca9a4210e4f6554d21087872a2a690843c35515348421c9eeca9a4210d4e7654d21086a63b2a690843931d95348421898eca9a4210e4d53d85210872631ca2908434b5d74148421c5ecba0a4210e8c63d052108786a9e8290843695d24148421d88c720a4210f45539052108697baa82908438bd954148421d18c6a0a4210f0d53505210876231a8290843d154d4148421b4eeaa0a4210f27755052108753b2a8290843c9d954148421f0ec6a0a4210ea663505210875231a8290843e118d4148421d08c6a0a4210f275350521087c329a8290843c954d4148421f0aa6a0a4210f0553505210872bb9eca90843951cf6548421c6ecb2a24210e3765551210872bb2ec69084395d946348421caecb29a4210e576554d21087
  | 28 => 0x4c21c3aa9318a610c5f7654c530870f322a629843875915314c21c74a9300a610e3954980530872ca9cc0298438e9516014c21c72a8b00a610e5953580530870f324c629843875926314c21c5cc9310a610e2d64988530861f3a4c2298430f5d26114c21c6ac9308a610e3a64980530871cb24c0298439698e6014c21cd4c5300a610e3a64580530871cb22c0298439698d6014c21cd4c4b00a610e7261580530863d384cba18431e5c265d0c218f4e032e8610c79701974308636bacc5a18439354e62d0c21c5ca8b168610e4d5358b430863abacc3a18439554e61d0c21c6ca8b0e8610e5553587430863d384cb218431e5c26590c218dce432c8610c7a70196430863cb80cb218431e9c26550c218f2e132a8610c7a70195430863cb80caa18438b5536250c21c9aa7b128610c6d751894308726a98c4a18431e9c26510c218f2e13288610c6e72194430863b388ca218431e9c06510c218f2e03288610e3554586420872aa9cc2210438d9516110821caaa6b088410e4e735973208716b2ca9990438b59554cc821ad2e1a9e6410e4d6594f32087872a2a799043c355153cc821c9aa6b0e6410e55535863208727b2a641904393595320c821e1ca89906410f0d544c8320871aaa4c2190438d551610c821caca6b086410d4d7598c3208726b2cc6190435a5c3530c821a9aeb2986410c6f7654c320872731aa619043c3951530c821e1aa8a986410d4f7654c3208727bb2a61904353dc1530c8218deeab086410e4d53584320876331ac2190431b5d83294421a3ce7aa68210d1d73d53410869d386a9a08434e5c354d0421a3ce62a68210d1d73153410869d380a9a08434e5c054d042187aeda9e8210d3a70d4f410869cb86a7a08438759653d0421c3acaa9e8210f0c7254f410861ebb0a7a08434b9c853d0421a74e029e8210d397014f4108696bae65a08438b59732d0421e1aa79968210d2d750cb4108716b2865a0843c354c32d0421c9aa73148210e2d5458a4108726a9ac520843479cf5450421a3ae7aa28210d3a70d51410869cb86a8a08430f9d85450421a3ce62a28210d1d73151410869d380a8a08434e5c0545042187ceda9a8210d3a70d4d410869cb86a6a0843475d65350421c3ecb29a8210e1f6554d4108786392a6a0843c51c5535042187cec29a8210d1e7314d4108697390a6a08434d9c45350421a74e029a8210d397014d4108696bae64a08438bd973250421e1aa79928210d2d750c94108717b2864a0843c354c3250421b4ae21928210f1653d85410878aa9ec2a0843179ce65104218bae73288210c5e73194410862eb98ca208430fdd95410421c3cc92988210e1e6454c4108726a9cc4208438b9516210421c9aa6b108210d4d75ccb3108726b2e65988438d59541cc421e2aa6a0e6210f8732507310861f3a6cb188
  | 29 => 0x966290e1e64d4e314870eb26a718a4387990538c521c3ac829c6290d4e758ca314872732c6518a438d995418c521e28a6a0c6290f8632506314872629ec498a4393d4c624c521c98a63126290d4c754c9314872632a6498a43711c5324c521c68caa0a6290f145350531487523128298a43e14c9414c521c3cc9a986290e1d64d4c314870f320a618a4387590530c521c9ea73106290e4c539883148727a9ac418a439314d620c52199aed1906290d4e758c8314872732c6418a4396d4e600c521cb0a73006290e5b53580314872c29ac018a43b28c9600c521e28a6a0e4290e1e64d4e214870eb26a710a43879905388521c3ac829c4290e4d6314e21487273b0a710a43935d85388521e1cc829c4290f0d6414e214878629e8310a43c314d4188521c98a6b044290c5e73993504862eb9cc9a8243179db5354121c3ec9a9aa090e1c64d4d504862f3b0a6a824387d905354121c38c829aa090c7b76540504869c3a2a0282439358e62d5021cb4c7306a810e5963983540872d31ac1aa0439658d60d5021cd4c4b06a810d1e73d52540868eb9ea92a0434e9c35495021a72e1aa4a810d2e72d8e540869b38ec72a043479cc6095021a3ae6304a810d2e72182540869b388c12a043479cf6455021a3ae7b22a810d3a70d91540869cb86c8aa043179cc60550218bae6302a810d2c7258d5408696392c0aa043479cc6055021a3ae6302a810d2e72181540869b388c0aa0430fdd95415021c3aa9318a810e1d5458c540871caa4c02a0438e5516015021c3cc9318a810e1e6458c5408726b1cc42a0439558e6115021c74c9300a810e5a63980540872cb1cc02a0438e9916015021cb4c6b00a810e59635805408735312c02a0439c9856015021c74a9306a610e3954983530871d2a2c1a98438e55160d4c2187ce930ea610c3d74987530871d324c1a98438e59260d4c21c74c8b06a610e39645835308735312c1a9843479d35394c21a3ae9a9ca610d5a70d4e53086acb86a7298430fdd16094c21878e8b04a610d5a70d5253086acb86a929843569c05494c21ab2e02a4a610d1e74986530868eba4c329843479d06194c21a3ae830ca610d5a7018653086acb80c329843539ca6094c21a3ee8b04a610d1c74582530868f3a6c6a9843475d36354c21ab4e1b1aa610d5970d8d530862f3b6a8a9843569c35454c21ab2e1aa2a610c5e7615153086ad380a8a9843565c05454c21e1ca8312a610f0d5418953086a7394c8a9843559c66454c21a98e4b22a610d1e74985530868eba4c2a98439318a6154c21a3ce830aa610d1d741855308726310c2a9843569c06154c21ab2e030aa610d1e74085530868eba042a98439318b6054c21a9ce5302a610d1f74581530868e3a2c0a9843531c96054c21aa8e2b02a610c3d76950530861fbb2a82984387952631
  | 30 => 0x4580318871caa2c018c439694d600c621cb2a6b006310ec832580318866639acb90c4353dcd65c8621c5acb2a64310e2d65553218872631ea790c431bdd953c8621c9cc6a9e4310e3565953218871ab2aa990c430fdd16394221878e8b1ca110e4f630c9508861ebb4a8284430fdd95414221c3ca9318a110e1d5498c508870f2a2c6284438755163142218f6eca80a110e5963540508862f39cc1aa243175ce60d5121c9cc6b14a890e5663586544872631ec4aa24396d8f6055121cb0c7b02a890e3b64181544872db18c0aa2439618c6055121cd6c4302a890e6972181544861fbb2a82a2434e1c15415121ab6e0aa6a690d5870553534868f3a6c5a9a43475d362d4d21a3ce9b06a690d1d74d83534872db04c1a9a43535c860d4d218beeca98a690c3f74580534861e3a2c029a43175da5414d218beecaa0a690d5b7055053486ac382a829a43535cb6414d21a9ae4320a690d557119053486ad380c829a43565c06414d21a3ce9b10a690d1d74d8853486ad386c429a43565c36214d21a9ee0b10a690e4d62d845348726b12c229a43535cb6014d21a9ae5300a690d1f74580534868e3a2c029a43479d06014d21a3ae8300a690d4d7218053486aab88c029a43965806014d218dae5b2e8690c7571d97434863d386cb21a431e5c36590d21c98a73148690c6c7558a434872629ac521a431bdc96550d218f6e0b2a8690c7870595434863d380ca21a431e5c06510d21c98a73108690c6c75588434872629ac421a439514e6110d218e8eab088690e5453584434872a29cc3a12439514d61d0921a70e0aa48490c3e76151424861fbb2a8212434e1c15410921ca8a730e6490e4f73996324872732ea7192439314e618c921c98a6b046490e575318532486a73aec69924393197634c921a9ce729a6490c6e7614d32486a73b0a699243939d8534c921c98a630a6490ce9701853248763b18c2992439314f604c921c98a73106490d4c754c8324872629cc5a0a439314d62d0521a3ce7b2e8290d1d73d97414869ab8ecba0a4347dcd65d0521a38e6b2e8290d3b70597414869c382cba0a434bdc953d0521e1ae429e8290f0c5398b414878629ac5a0a434b9d632d0521e18a71968290d2c754cb414878629a65a0a43179cf65505218bae7b2a8290c5f73595414862e39acaa0a439314f6250521c98a63128290d1e73d95414868eb9ecaa0a4347dcd6550521a38e6b2a8290d3771595414868f39ca6a0a434bdc95350521a6ee2a9a8290d1e7514d4148786b90a6a0a43c55c45350521e18a7b128290f0c5318941486973ac64a0a43c314e3250521a58ea9928290f0c534c941486d238a64a0a434d9d76150521c68cbb0a8290f1753d85414878a29ec2a0a43699cb6150521c3cc9a988290e1e6414c414872629cc598a439314d62cc521a98ea9
  | 31 => 0xfbb2a619643b14c9610cb21e18a69968390f0c534c941c86d238a64a0e43e14c941cc7218bced29a6390e4e5318931c8726a98c498e43175db530c721c9ea6b106390ccd768c831c878ba9a8218e43a9589410c721f0c64a086390e5b5358031c872c29ac018e43b28c9600c721d6282b006390e1e63d0650c870eb1e83286438798d4194321c3ac6a0ca190d357119150c8717390c8a86438b5c86454321c6ce2322a190e357119150c861f3b682a86430f1d941543218f6eca80a190d2d72d8e548869b388c72a443479cf6295221a3ae7b14a910d1e73186548868eb98c32a4434e9c06195221a72e030ca910d1e73182548868eb98c12a4434b5c86095221a6ce2304a910e3960182548862f398c0aa443175cc6055221a5ee4b1aa910d3b7058d548869c382c6aa44347dcd6255221a38e6b12a910d3b70589548869c382c4aa443479ce6155221a3ae730aa910d3a70985548869cb84c2aa44347dcd6055221a38e6b02a910d2f72581548868f398c0aa443475cc6055221a5ae4302a910d3671181548871cb00c0aa4430fdd95415221ccac5308a910e3564987538861fba2c129c430f1d16094e2187aed2a0a710c3f76550538862fbb2a629c438e9526014e21c72a9300a710e3a54580538871caa2c029c439654d6014e21c5cc8b10a710e2d64588538871d324c029c438e5926014e21cd2c5300a710e3a64580538871cb22c029c439698d6014e21cd2c4b00a710e2e5498b438863d380cb21c431e5c06590e218f6e0b2a8710c78705954388716aa0c4a1c431e9c06510e218f2e03288710e3654584438871b2a2c3a14438d5536150a21ab2e029c6510c5e7694d328871aaa6c2994438d550614ca218baeda986510d597014c32887872a26419443c3551320ca21c5acb2a06510e2d655503288636bb6a619443335db530ca21e1ca9a986510f0d54d4c32886e338ea619443535db530ca21c9aeda986510f0e74d4c3288786ba6a619443d19c7530ca21a9ae1a986510dc67114c32886e4b80a61944393d4d610ca2187aeda9e8310c3d7614f418869d380a7a0c434e5c053d0621e1ea61968310e2d5498a418861f3b0a8a0c430f9db535062187cec29a8310d3a7014d418869cb80a6a0c43c3d4c3250621b4ae21928310c3f7655041887172a4c420c43565c053cc62187aeb3246310c3f75592318861ebb4a918c430fdd9548c621f0864a0c6310c5e7614d31886acb80a698c438b953624c621c5aa9b126310e2e541893188716aa0c498c439314c624c62199ced9926310f145350531887523128298c43e1cc9414c62187aeb3206310c3f75590318861ebb4a818c430fdd9540c6218beeca986310e2e549883188716aa4c418c438b951620c621c5aa8b106310e4e535883188726a9ac418c438e952600c621c72a93006310e3a5
  | 32 => 0x3ccdc54194031a74e918ca018d39748c6500c6b5b9263280635a1c931940318dce4322a018c6d72191500c6a639262a8063c550531540318f4edaa2a018d6a72d51500c6b4b96a8a80631e9d85454031ad4e42a2a018d6972151500c63d3b6a4a80634e9d35254031a72e9a92a018f2a54949500c794aa4a4a8063d21ce5254031e54a8a92a018f2954549500c7a439aa4a80631e9d85254031a74e8292a018d3974149500c6acbac64a8063c69523254031e32a9192a018f4a528c9500c7a4a9464a8063c69503254031e32a8192a018f4a520c9500c7a4a9064a80634e5d74154031e54a5a0aa018f2952d05500c69dbaa82a8063ca9494154031e52a4a0aa018f1a54cc5500c78caa662a8063d294b3154031e92a598aa018f31548c5500c7b0a9462a806356dd53154031e34a898aa018f19544c5500c6e439262a8063d29493154031e92a498aa018f91414c5500c6b9baa62a8063cc5513154031ec2a498aa018d5873591500c6ad398c8a80635a9c86454031ad2e4322a018d7271191500c6b938886a80635c5c44354031ab4e7b12a018d3b74589500c69c3a2c4a8063561cd6254031ae0e2b12a018d5a73d09500c6acb9e84a80635c9c74254031ae2e3a12a018d5b73509500c6ac39a84a8063565c63254031e9264192a018d72710c9500c6b8b8864a8063d29c83254031e94c4192a018f49620c9500c7a938864a8063565c43254031ea2e2192a018d3a74985500c69cba4c2a8063c68cb4154031e3065a0aa018d5a73905500c6acb9c82a8063c68c94154031e3064a0aa018f3371505500c79930a82a8063569cc4154031ab2e620aa018d5a72cc5500c78da0e62a8063c65073154031a74e918aa018d39748c5500c798a0c62a80635adc93154031ad0e498aa018f31414c5500c7a5b9262a8063561c93154031e90e498aa018d48724c5500c7a9b8a62a8063c6d053154031ea48298aa018f19414c5500c7a8a0a62a8063c45053154031a74e818aa018d39740c5500c6b539062a80635a5c8315403187aed2a0a018c3f76550500c7172a4c4280638b5526214031c5ca8b10a018e2d54588500c636bb4a4280638b9925214031c5ac9290a018c6f76548500c717322a4280638b5915214031c74a9300a018e3954980500c735294c0280639a54a60140318f6eca80a018e3a64540500c71cb22a0280639a9895014031cd2c4a80a018c5e7398354c862eb9cc1aa6430fdd95415321cccc4b08a990c5f7654c53c861fba2c029e430f1d16014f218f4e1b2c8790c7970d9643c863d384caa1e431e5c26550f218f4e03288790c797019443c861f3b0a8a16430fdd95410b218bcec29a6590dc571d4d32c86373b0a699643339d8534cb21a9cec29a6590e4e7614d32c87a2b88a6996439314c614cb219d2e030a6590e4c53d8132c862
  | 33 => 0x431e1aa41968218e1d5458e410c72731aa5208639358d5290431a5ce5aa28218d2d72d51410c69d386a8a08634e5c3545043187cec2a28218d2e72151410c696b90a8a08634e9c05450431a72e02a28218e2f65949410c717b2aa4a0863c91c55250431a3aeb1928218e1f658c9410c786a9464a086387d943250431e1aa41928218d95710c9410c793296c2a0863c954b615043187eecaa08218e1e5458c410c72731aa4208639358d52104318beeca966218e4e6254b310c7872a2a598863c355152cc431c9eeca966218d1d75d07310c786a96839886347dd541cc431e1aa4a0e6218c3d76952310c61fbb2a918863175da538c431c5cc92946218e2d6494a310c717322a5188638b591528c431e4aa4a0c6218c757694e310c792aa2a5188638b953624c431c5aa9b126218e2e54189310c716aa0c4988631b1da524c4318dceca926218e3765d05310c71bb2a8298863a9189414c431e4aa4a0a6218e4f72d95310c726396ca9886387d96544c431c3ecaaa26218e4f65d89310c727b28c498863935d4624c431d1ca83126218e8d54189310c6663b4a49886393d96524c431c98c4a926218ccc76549310c727b2aa498863c3951524c431e1aa8a926218d4e76549310c6a63b2a498863931d9524c431a3aeba0a6218e1f65d05310c7463168298863c354b414c431b2ae920a6218ec462905310c7a2a94829886347dd5414c431c3ecaa0a6218e8c62505310c786a928298863b1189414c431e8aa4a0a6218d9775505310c78bbaa8298863a5d95414c431e2ecaa0a6218f8762505310c74a3128298863e1189414c431d08c4a0a6218f8652505310c78aa928298863e1549414c431e0aa4a0a6218e6772d95310c732396ca988638dd96544c431c6ecaaa26218d9574d8d310c733b2ec49886399d94624c431d8ec63126218e6765949310c733b2aa498863c9551524c431e8ca6a926218e2e5498b500c716aa4c5a80638b95162d4031c5aa8b16a018e2e6494b500c716b24a5a80638b99152d4031c5ac8a96a018d3a74d42500c69cba6a1280635a9cb5094031ad2e5a84a018c3f7458a500c61e3a2c5280635a9cb5494031ad2e5aa4a018d6a72152500c6b4b90a9280634e9d35294031a72e9a94a018f2a5494a500c794aa4a528063ca9515294031e52a8a94a018f487354a500c69d3a0a5280634e5d05294031ab2eb194a018f49528ca500c7a4a9065280634e5d74194031e54a5a0ca018f2952d06500c69dbaa8328063ca9494194031e52a4a0ca018f4952cc6500c6adbaa6328063721c93194031e92a498ca018f91414c6500c6b9baa6328063569cc6494031ad4e4324a018d6972192500c6b9388c928063569cf6294031a76e8b14a018d387458a500c7a499065280634e9d06194031a72e830ca018d6a72186500c6b4b90c32806
  | 34 => 0x2a098e2c64d49504c6373b0a4a82638bd905254131c58c8292a098c7b76540504c69c3a2a0282639398d62d5031cd4c5306a818e6962983540c72d31ac1aa0639a98960d5031cd2c4b06a818d2e72d52540c696b96a92a0634e9c35495031a72e1aa4a818d1e73d8a540c69b38ec52a063479cc6095031a5ce4304a818d2d72182540c69b388c12a0634b9cb6455031a5ae5b22a818d3a70d91540c69cb86c8aa0631b9c860550318dae4302a818d1c73589540c68e39ac0aa063479cc6055031a5ce4302a818d2d72181540c69b388c0aa0630fdd95415031c5aa9310a818e2d54588540c71caa4c02a0638e5516015031c5cc9310a818e2e64588540c72731ac42a0639958a6115031c74c9300a818e6a62980540c734b14c02a0638e9916015031cb4c6b00a818e6a62580540c734b12c02a0639c9856015031c6aa8b0c8618e3654584430c71d2a4c1a90638e55260d4831c74a8b06a418e3954583520c6973a6a5290634b5d35294831ad4e1a94a418d6970d4a520c61fba2c1290630f1d16094831ad4e1aa4a418d6970d52520c6b5380a9290635a5c05494831a5ce930ca418d2d74986520c6973a0c3290634b5d06194831ad4e030ca418d6970186520c6a739cc1290634bdd16094831a58e8b04a418c6e76d51520c6b5386a8a90635a5c354548318dcec2a2a418d6a70151520c6b4b80a8a9063c39506354831e1aa831aa418d4e73991520c6b338cc8a9063531cd6454831acce221aa418d657110d520c6973a4c2a90634b5d26154831a5ce830aa418d2d74185520c6b5380c2a90635a5c06154831a5ce818aa418d2d740c5520c6a739cc0a90634bdd16054831a58e8b02a418d4c73581520c6b238ac0a90630f5da541483187eecaa0a418e2e54988520c716aa4c4290631bdd95214831c5cc8a90a418e2d64548520c71d2a4c0290638e5526014831cd2a5300a418e3a54580520c71caa2c0290639a54960148318f4e132e8418c7970997420c70f2a2c7a10639398d52d0831c9ac6a968418e6552987420c71b2a2c3a10639954961d08318f4e132c8418c7970996420c63d380caa10631e5c06550831c3aa9b1a8418e4f63549420c72631aa4a10631e9c265108318f2e13288418e6552587320c727392cb1906387596548c831c3acaaa46418e4d6594a320c7872a2a519063c3551528c831c9aa4b0c6418f0e544c8320c786aa264190638d552610c831c6aa8b086418e6652584320c6a6bacc419063c3951520c831e1aa8a906418d4f76548320c727bb2a41906353dc1520c831d8cc4b086418c5d760ca510c697396a9a08634b5cb54d0431a74e1aa68218d3970d53410c697390a9a08634b5c854d0431a74e02a68218d3970153410c716b2ca5a08638b59552d0431a3aeb1968218e1d658cb410c786a9465a08638759432d0
  | 35 => 0x548528c71d2a4c0294638e5526014a31c74a8b00a518e3954580528c734a92c0294638795263d0a318f6e0b2a8518c7870595428c70eaa0c6a14638d9516110a31c6aa9b0a6518e3554185328c7872a26419463c3551320ca31c3acb2a06518e1d65550328c666bb6a419463c3953520ca31e1aa9a906518dc671d48328c6e3388a419463725c0520ca31c3aa931c8318c3e76151418c6cab8864a0c630fdd95410631c3ca93188318ccc72597318c6a7b92cb98c638759654cc631c3acaaa66318e4e6254b318c71ab2ca998c638d59554cc63187ee8b14a118c3c7458a508c727b1064a84630f5da541423187eecaa0a118e2e54988508c716aa4c4284638b9516214231c5aa8b10a118c7b76540508c734b12a0284631b9ca60d51318dae5306a898e4d6398a544c733312c32a26393d8c6255131cd6c5b02a898e6862d81544c71db20c0aa26396d8c6055131cd6c4302a898e6862181544c72cb98c0aa2630fdd95415131a70e0aa0a898d3870552434c61f3b0a8a1a630fdd95410d31a70e0aa08698d6b70553524c6b4382a9a92634b9d363d4931a5ae9b1ea498d2e74d83524c696ba6c1a92639ad8260d4931a9ae6306a498c6f76548524c61fba2c0292630f1d160149318daed2a0a498c6f76550524c6b5b82a8292635a1c15414931a9ae7b20a498d4d73190524c6b2b88c8292635a9c06414931ad2e0320a498d2e74d8c524c696ba6c6292635a9c36314931ad2e1b18a498d6671d0c524c6b2b8e8629263535cf6014931a9ae7300a498d2f74580524c6963a2c0292634b9d06014931a5ae8300a498d4d73180524c6b2b88c0292639a5806014931c9cc62948498e4d6314a424c63d380ca212631e5c06510931c9cc62908498e4d63148424c732294c221263991496110931c9ee532e6498e4e65d4b324c726294c3992639314960cc931cc8a530c6498e6752185324c6a73aec499263539d8524c931c9cec2926498cd970185324c763b10c2992639314b604c931c9cc62968298e4d6314b414c697396cba0a634b5cb65d0531a6ae3b2e8298d2f72597414c696392cba0a634edc165d0531a70e0b2e8298f0e6314b414c786b18a5a0a63479d732d0531e18a59968298f0c524cb414c727b18a4a0a639318c5250531a5ce5b2a8298d2d72d95414c697b92caa0a634b1c96550531a6ee2b2a8298f0f63149414c786318a4a0a63c95c45250531a3ceb9928298f0c52cc9414c78629264a0a63651c53250531a6cebb0a8298e3465d85414c6cb39ec2a0a63c9d4b6150531e48a5b0a8298f2452507314c717326a518a638b593528c531c5cc82946298e2d6414a314c726b10a518a63935d8528c531e1cc82946298f0d6414a314c7862968318a63c3149418c531c98a4b046298c6e72993504c636b94c9a82631b9db5254131c5ec9a9
  | 36 => 0x382a5a8a832ddd932d4541968ec996a2a0cb6760cb515065abb065a8a83e14c832d4541b2ce6306a2a0d957318351506d3390c1a8a83695c860d454195ee4b1ea0a0cac7258f505064fb9ac5a8283271cd62d4141b62e1a8ea0a0e8f63d89505074631ec4a8283a3d8c6254141d18c6312a0a0e9763d85505074a31ec2a8283a9d8b6154141d48c5b0aa0a0e9763d45505074a31ea2a8283a9d8b5154141d48c5a8aa0a0e9863d415050754316a0a82838718e5054141c58c5282a0a0e987058c505070eb1ca6282834e5c05314141d1cc7310a0a0e8d63988505074731ac428283a358d6214141d50e0b10a0a0e2d62948505069cb80a428283a598d6114141d2ac6b08a0a0ea6625845050752b12c2282838798f5114141c3ac7a88a0a0e2e62d445050716b16a2282834e5c35114141d2cc7a88a0a0e9563d445050753316a228283a958b5114141b62e1a88a0a0c3f76540505068e39aa0282834b1c95014141976eca80a0a0d987354050506d4392a0282834edd95014141c76eca80a0a0f1b73540505069c39aa028283c61cd5014141a30e6a80a0a0f1a63540505078cb1aa028283cadc95014141a70e4a80a0a0f28725405050694392a028283ca9895014141e52c4a80a0a0f33715405050798b0aa0282831b9ca6094c418dae5304a620c5f7654c5310726a9ac4298839654d6014c418bce7304a420c5d739825210637bb2a4290839358d5214841cd2a4b00a420c7a70195321063cb80ca99083531c9534c841a98e6a926420e4f654c83210726b2a6419083c3951320c84187aed2a48220c7576952411063dbb2a0280839658d5014041cd2c4a80a020c6e7298354cc636b94c1aa6630fdd95415331cacc6b08a998c3e7615143cc61fbb2a821e631bdd95214b318f4e1b2c8598c7970d9642cc6e2b8ea499663339d8524cb319b2e030a6598ec53258432cc6ca38a64a0e638b98b4194331c5ac5a0ca198e2e6250650cc716b1283286634d5c46454331c3ce6322a198e1d7319150cc71b388c8a86638d5c4645433187ceda0aa198c3c7650550cc63dbb2a0286634b9cb6395231a5ae5b1ca918d1d73d8a548c69b388c52a4634b9c86195231a5ae430ca918d3a70186548c69cb80c32a463475cc6095231a5ce4304a918d2d72182548c69b388c12a4638e58060952318dce4302a918c6d72181548c697b92c6aa4634b1c96355231a76e0b1aa918d387058d548c68fb9ac4aa4634edc16255231a70e0b12a918d2e72985548c696b94c2aa4634e9c26155231a72e130aa918d1f73581548c697b92c0aa4634b1c96055231a3ae6302a918d2e72181548c696b90c0aa4634d9c46055231c72c0302a918c3f76550548c72ab1cc22a4638d95161d0e31c6aa9b0a8718c3f74582528c61e3a2c1294630f5da5414a3187eecaa0a518c6f76
  | 37 => 0x1b1c963d41418bee6b16a0a0c5c7358b505063dbb2a028283561cd5014141ad0e4a80a0a0e1f7458c505070e3a2c6282838758e4314141a72e0218a0a0e4e639885050726b1cc4282839398d6214141c9ac6b10a0a0e2f7458850507163a2c4282838b58a4214141a72e0210a0a0cb57198b535065ab8cc1a9a83a5d4d6194d4196ee0b0ca6a0cae729825350656b94c129a83a3d4c6254d41d4ec5b0aa6a0ea462d85535074ba9ec2a9a832d5c36154d41d56c5b02a6a0ea862d815350759b0ec0a9a83acdc76054d41d56c4302a6a0ea8621815350759b08c0a9a83a6d4c6054d41c74a6302a6a0eb17118153506cab8ca629a830fdd95314d41a70e0a98a6a0c9f7654c53506c6392a629a8365dc55314d41b30e0a98a6a0cb771588535065ab8cc029a832d5c663d494196ae3306a4a0ea752586525065bb82c329283279ce609494193ae7304a4a0e8c63d49525074bb1ec2a9283a518f6154941d4ea5b0aa4a0cb570d85525074db1ec0a9283a618f6054941d66c3b02a4a0eb371d81525074db18c0a9283a618c6054941d66c2302a4a0eab52181525071d290c0a9283ac5c4605494196ee2b18a4a0da571948525061fbb2a4292834e1c1521494195eeca90a4a0d8c7354852506d3b8aa4292836a1c1521494196ae3300a4a0cb571d97325065d386cb992832e5c365cc94196ee2b2e64a0cb671983325065ab8cc1992832d5c7658c941974e1b2c64a0cb970d96325065bb8acb192832d9c6608c94196ae330464a0cb571d95325065bb8aca992832edc1654c941970e0b2a64a0cb675d85325065ab86c2992832e9c0614c941972e030a64a0db170185325065b3a8c2992838d9d4614c941d4e6430a64a0e96321853250759380c2992832d5c0614c941d62e030a64a0cb170185325065b388c0992832d5c4604c94196ae3b2864a0cb771594325065db82ca192832e1c1650c941974e032864a0cb970194325070eb28a619283635c8530c941c5aca29064a0d8d7314832506c6b9c641928327dd9320c941b28e299064a0caf764c832506d238a641928363dd9320c941d1eec99064a0d8e754c832506c63aa6419283e1dc5320c941b18e299064a0f84714c832506c238a641928363dc1320c941f0a6530864a0cb675984325071b3acc2192832d5c2610c941d1a64b0864a0f8532584325065a3aac219283a5d4d610c941d28a6b0864a0ea7525843250752292c219283a5cc9610c941d4c64b0864a0e95325843250752992c219283a14c9610c94196ee0b0864a0cb671980325065ab8cc0192830fdd5600c941878eab0064a0da672d8f51506d2b96c7a8a83a5d8e63d4541b4ee4a9ea2a0da47254f51506d9b82a7a8a836c1c153d4541b2ce7b16a2a0d9573d8b5150753b14c5a8a8365dcd52d4541b28e6a96a2a0db37054b51506d8
  | 38 => 0x418f4e1b2e65a0c7970d9732d065d386c9996832e5c364ccb41c5cc8a9665a0c7a70d9632d063cb86cb196832e9c3648cb41972e1b2465a0e1e6454e32d065d380c8196832e5c0640cb41a9ae529865a0d4d7394832d06a7baa6419683535d5320cb418dce5b1aa1a0c6d72d8d50d062f39ec4a8683175cf62543418f6eca80a1a0ea66258753d0752b12c3a9e83639cb5394f41b2ae3a9ca7a0cae7298253d0656b94c129e83639cb5354f41b2ae3a9aa7a0c3f7654c53d064fbb2a629e83a594d6114f41d2aa6b08a7a0e966358752d074ab1ac3a9683639cf5294b41b4ae3a94a5a0c9e7398252d064eb9cc129683639cf5254b41b4ae3a92a5a0c3f7654852d0657bb2a429683a99496114b41d4aa4b08a5a0cba70d9732d065cb86cb996832d5c665ccb4196ae232e65a0e2e6554b32d065d386cb196832e5c3658cb4196ae332c65a0cb57119632d070f32aa7196832d5c6654cb4196ae232a65a0cba7018532d065cb80c2996832d5c6650cb4196ae232865a0cba7019432d065cb80ca19683635ca530cb41b1ae729065a0c9f764c832d0657bb2641968363dd9320cb41d1eec99065a0d8f754c832d06c6baa6419683631c5320cb41b1ee099065a0e8d3258432d061fbaac0196830f1d5600cb4195ce5b1aa1a0cad72d8d50d064f39ec4a8683275cf6254341c3ac7298a1a0d397014c50d074731cc428683a358e6214341d1cc6b10a1a0e8d6358850d0716b14a4286834e5c05214341d2cc6b08a1a0e956358450d0753312c228683a9589611434187eeca80a1a0cbb7654050d069dbb2a0286838edd95014341e34c6a80a1a0f196354050d0795312a028683ca5895014341e62c2a80a1a0c6e729825390636b94c129c8317dd95314e41c9aa6b10a720e5953580539062f39cc129483175ce6094a418deeca90a520e4d635485290734a92c0294831e9c0654ca418f2e032a6520d4c7254d32906a639aa4994833c5c0614ca41c9eca9906520e4d654c832906e238a6419483b14c9610ca418f6eca80a120e59635405090734b12a02848317dd95314d41a98e4a98a6a0d587054c535065b38cc1a1a832b9ca6090d4195ae530486a0cb671982435065b388c0a1a832d9c66010d418deeca90a4a0d4c7354852506b4382a4292832d9c660d094193ce730484a0c9d73982425065b38cc1212832d9c4605094196ce330084a0cba70d93325065cb86c9992832e9c3648c941972e1b2464a0cb671991325065a38ac8992832d9d0614c9419e2e030a64a0c7b70594325063c382ca192831e9c0650c9418f2e032864a0cb671d90325065b388c8192832e9c0640c941972e032064a0e1d6414c32506a6b90a6192838b590520c941a9ae629064a0d4e754c832506a63aa6419283711c5320c94196ce930864a0ec5325843250637b92c7a8283
  | 39 => 0xa11943e74986508ca1eba4c3284650f9d0615423287ae830aa11947b76540508cb1baa2c32a2659558e6195132ccac530ca89963674586544ca1fbb2a82a2654d5c6641513287ee8b06a29943c74583514cb1ab26a328a651ddd95114532c6ce3320a29956571cc8514caaab8c6428a658e9926014532c72c9300a29963a64580514cb1cb22c028a659acc96014532cb464b00a29947671993504ca3ab8cc9a82650f9d261d413287ae930ea09947b76540504ca1f3a4c2282650f5d261141328ece2302a81947571181540ca1fbb2a82a0658d5516115032c72a8b00a81963664584540cb2b31ac22a065999896115032c6ce8b08a81967261980540cb38b0cc02a0658e9916015032cb4c6b00a81966a62580540cb3930ac02a0659c5856015032c5aa9314861961d5498e420ca2ebb4a7190651b5da538c8329b2e030a64194e970185320cb26baeca99065339c7654c83299ae1b2a641964e76d95320caa6b8eca99065535d6644c832b8ce332264195c571991320caa7baac899065339db544c83299cec2a2641970d54151320cae3388a899065715c4544c832b94e02a264195c970151320caa6bacc299065639d2614c832b1ae930a641954f75585320cac73a0c299065635d0614c832b94e030a64195c970185320cb26ba8c299065a39d0614c832d1ae830a64196ca70185320ca66b80c299065b25c0614c832992e030a64194ce71d81320caa6bacc09906553dd5604c832b1ee8b02641958c74581320cae3b8ac099065711c5604c83299eec996a2194cc764ca510cb473226528865a35913294432b88e2994a21963671992510ca663b264a8865711c53254432aace3992a219566718c9510caaa38a64a8865591c53254432c9eec992a21954c764c9510cb263b264a8865d1dc53254432a98e2992a219744714c9510caa238a64a886553dc1325443287ce8302a21943d74181510ca67bb26428865a39913214432d1ac8990a21947776544510cb1ab22a228865b24ca6014432d9264b00a21967151580510ca67bb265a806533dd93294032b96e0994a01943e74986500ca1eba4c3280652d5c4645403299eec992a01968f644c9500cb4632264a806572dc1325403287ae3b22a01947671191500ca3ab88c8a80654d5c46454032c3ce6322a01961d73191500cb17390c8a80658b5c86454032c6ce2322a01943d71191500cb1ab88c8a80650d5c46454032c72e0322a01943e74185500ca1eba0c2a806533dd93214032d1cc8990a01968d644c8500cb62994c228065b14c961140328f6eca80a01963964540500cba4992a0280659c5855014032a9ce5a9ca7a0c6e7298253d0636b94c129e8317dd95314f4195ce530487a0cad7298243d06a739ea529683179ce6094b418bae7304a5a0c6f7654852d064f39cc121683275ce6090b
  | 40 => 0x40000008011002000300000090000000001c002000000d00080050038001001c00200100020034002000000a0004006000c0000004001000000c00040010008002000000000100000018000000400200040000018006000400c000800f00000050000000001c001002c013002000000a0002001c001000000100040070058001000800000180070004001000400100040000004001002000100000020000000000400300740000008006000eb338ea5296871bdd95214b43acce5a8ca3a1c6e7218151d0e36b90c0a8e871ddd951147438f6eca80a1a1d6a70d4a5290e3d380c2a94871e5c06154a438deeca90a521d38705915190e9ab8e86a8c871ddd95114643ad4e5a84a121e2f7458a5090f163a2c5284871b9c861542438dae430aa121c7b765405090f35a92c1292871bdd95214943a6ae321ea2a1c7a7098b5150e3cb84c5a8a871b9ca60d45438dae5306a2a1c77765445150f34b16a1282871edd9501414387aed2a48621c5d769524310e1eb8ecaa18871e9c061548438f2e030aa421c6f765485210f32a92c2290879a5496014843a6ae3a1aa221c3f7650d5110e9bb8a86a88871e9c062544438f2e0312a221c6e721815110e36b90c0a88871ddd95114443ccac4a88a221e71515805110e37390c2a80871b5c861540438f6eca80a021e69625405010f38b0aa028087559c75394f428beeca98a7a155673d4651d0a2f398c0a8e85175cc60547428eeeca88a3a147b7654050d0aad386a729c851e9c06154e428f2e030aa72145f7654c5390a9c382c8a8c854d5c742546428eeeca88a32155a73d425090b0fba2c728485871d163942428bce630aa12145d731855090a3dbb2a02848596d4d6094d428beeca98a6a147a7098f5150a3cb84c7a8a854d5c642d45428bce7306a2a145d739835150a3bbb2a228a859658f50941428f6eca80a0a147a701855310a3cb80c2a988517dd95314c42caaa6b08a621659535805310a1ebb4a9210851b5da549084287ae3b2a842147a7018d5110a3cb80c6a88854d5c7425444287eeca12a221537715095110a2f398c0a8885175cc60544428eeeca88a221655635445110b38a8ac028885179cc61540428bae630aa02147b765405010b2cb1aa0280859c5855014042c9cc6b16a9996696298354ccb34b94c1aa6659698d60d5332a74e1aa4a99953a70d9154cca1fbb2a82a6659398d6215332c5ca8b10879943e74d8151cca1eba6c0a8e651ddd95114732a74e9a84a19943e7498650cca1eba4c3286650f9d0615433287ae830aa19947b7654050ccb26b1cc5aa4659658e60d5232cb2e7306a91966a62583548ca9d386a92a4654e9c3645523287eecaa0a91964d63988548cb0f2a2c621465595c73294632aace3992a31943e74d81518ca1eba6c0a8c651ddd95114632a74e9a84
  | 41 => 0x400480020004000001c008000c002001800000240000000000000c005000000000100000000002006400200040000004000000400200040010004001000000500000060018000003402a00000000028000000c00000200120028000000400500000010000001000000400040020008004000c01d00040040014000001800000000070000005003c001003c00b000800a00000050000009000800200000010004000000000500000010014000000c00b000c001000c001003c0060020000000c0100000013000c0030004000005000100080060010007000000000240010014004000800100740080000001000000e0030005002c005000400f00040050018006000400000040010004001000000000000000000004001400100240010000002001c004005000100200020004000001c00100000010048001001c000000c0020040002001000100300000004001000000000100000004008001000000000000004002003800000500000000002000000e006c00100080010000003001400100100030000000000c00600080030004009000400e0004005001c000001800200040050008004002400000080040070005000400000000010004000000000600100020008002002c000000c0000050000000000000340020000009000c01a0004003003800100000000008006001000000580050020004000001a0010004000c000000000b000c000000800000000030000002001c002000000000080060010002001400000040100000015000c0070000011001800f00000010024001003c000002c008000401600000000008003001c002000400b002c00000000030000014003800c000400000000000008000000400000080000000001001c005003c0030000002000c00b000c00b0024001001400300000000020007000c00100000040004000006800200000100000005002000100000010004003001c001001c001000c002000000000000010010002000000000000000018016004c0000040002000000000140060044005002800000100050018007000400a0000002001c0180008000000c0010010005001800d000400000280070004002000800000000050004005000c00000180000004008000400000040020014003003400300040040008004000000100000040004000000c004001c004002801e001800100d00000010000000400d001000d00040000054002002800500000020008000000000100040020008000000c0010000004000400500200030004000000000000000000020001001400000000000024000000000000000090020000001400100100020000009002400a000001700200100028001004001200140050014001000000500000130014000000000b0020004000c00100000020004000000000700000050008001000c
  | 42 => 0x2000c001001800000080010000003000c003000400100000050000000000000400600000024000000c000001800800080070000004002401e0004000001400d000c00000140220000004002800000000020018000000400400180000008000000000100000050004006000c00000040000000000000c002000400200080000008001001400600100260000005000000000040020004000000400000040040008009000000000180030000006000800800000000010000001000200200040000005005c0030000006001c008002c00400000070008004000400400100010008000000400300100000030005000c00300580030000003002800000180030024004000c000000000d00040070014008000000000080010000000001c0020028004001c008000c003000401b000800100000000010007000000800280020000003000000a00080040060001000001d0000003000c000000c00000000000000001000c0040014001000800000b000000000020054002000000000100000034000001c02100380010044000000400900000000050003003c00600080010004006001401300180070000006000800c0000001000000000140000000005000000500040000004004000801500000000004006002c0010000002000400400200040004000001000000240000000006002800c0018001000400100140070000002000002000080040010006009c0040004000000c00200140150014009001400200000040000000001c002004800300140010000000000400700080000000010000c0010000000000c000001000200040050004001001000d000000d0004005000c001000800700180190008004002c00200080020000005000800500040090008004000c0050018000000400e000400b002400100140090048000000400e00140010014000002000500000020004000000c0000004002002000700000030000000001000300000000010008001c00500000190000002001001d001c00800080030010002003401100000000018001007c0000010000000c001001400600080060058002000800000040040008003002400a001800e00000070030000000c00d000000300000010000000000000000840000000000000c009001c00000080050000003000000600140000000001000000000080550000003000000000080010008003001c002000000400200000000008003000500080000040003000c0000008005001000000ac0050008000000400000040060000001000c00100000000008013000800300000020004001001c00100180060008002001c0030078002000000000000080000000000000e0008000000001a000c002001400e000400100040030000002000000200000000074000001400b002c0090000009003c00400100000000008
  | 43 => 0x9000000000040000018000000400500080020000001000002300000000000001000c0100000001000400000080010010001000c003000000100000000020000000400000280130010000000c0010000000000400700140000054001004800300000080030000000400000080000000001000000c0004000000400200080020008004000000200140170018000000000a00040010004000001000400100000014008008c000008c0010000005000000b00040070018000002c0000000000001c0010020001003c0000054004000000200000000004005001800200200020018004001400000140000048003000000400000000000000000c00d0010009000c00b00040010008001000c00000040020004002000000900000010000001002400100100020000001000000000140000024000007c000002000000080030000004001400000180060010007000801f00500020018002003c0020000009001000e002000000380000008001000c00000000000000007005801400000000000009000000300100010014005000400700180040010000001c00000040020000002000800100040080000006002000e0004008000c0170020003000c002000000000000060034005002000c000401f000001500040070038000000000d0000000001400500000050004001003c0030038003000c0050048000000800000000020000009003c005001c0000000000001400d000000900000010000008000800a002000000340000014002002c026000000a0004002000000200140000008001000800100000000010001000800400000040000002000000100040030000000000c0000054006000000b0000006000c00000040000000000003000200100010014002005c0000010000002800400080000000000001001b0034001002400f0008000000c000000401100100060000007000400200700020000000001000000100060000001002401c00000020000000000000a005c001000000000b000a000400c0008016000001400080000004006003800200000050048003007c0030024002001c002001c03100040000000009000c004001c000000000000080030000000002c000000000c00080020000002000800b001c0030008001000c000007c001001400200000000004000000c00000040000014008000000200200000000000000000300340020004001000800400080010008000000400200080030008017000000000140010034000000400d000000100040000000001000c0010000000000000b000000200040030008007000400000000030024003000000d0000002001400000400020010020002800200000000000004000400200000000010004000800b0000000000c001002001200000000010000000000600000000014009000000c0010004001
  | 44 => 0xb318c000000000020081460000b5b9a8ecc1a5500002cc8000000000014b00000000c358e56a371bb427e24763ea9e8000000f2943000000005e4bef80000003130b4b9532289a7f6ca7b366bc98c46528024a00004b046aaf7c96b31c45222de0b2c8000a93b18221c252e0e2032cb45a85a000147c08b8000ac00000000131ea4e0b868169636025815a885108c3a70000c61000000000000002fbc4080000af480007472a1c0000536000000009e2bb61e006865c68c7c0000000211a268000197600000000000000000000000000000000000027871200000001ca2f8ea6c9c9c0001224a83800000000000000000000000000021de000000000003100002fcc5d880008bc803a00018806890000353000000000000dc0000000000000000000010000000000000000070000000002c00b00040020000002000800500000010040005000000000000020000000000400300040000014002005c00b001400000000090000001000000b0000001000000000000000010004000c0000004003000400000200000000003000800000080010000001000000200380050000003001c001000c001000c001000400400000060004013000c00100040030014005000800000100020004002000800c00000000000000000800400100020074004001c002004000b00000000010010000c02c00140020008002000c0080000015000c0040004000001c00100140010000002005c000000000700280020004000001400000040050000000000000300000000018000001000000080000010009003c000000400200340020000001001c000003c0000004007000000100000010004009000400f000800400200000010008009c00700040030008001001c004000000e00000050014011000000000040000028001000c00000000000000017000c0040000039001400f000000300000000018000000c000000400200080000004000000c0000010002000c005000c00600240000000000000c00100080000014004000800e000c000000801200080020000001001000300000020000003007000400400010008001000800000000110000005001000f000c000000000300000010000000000c0060004001000000400000030000006002800b000000300100010010006003001d00000050004001001000300000010000000001c003002400000040020010001001c005003000a00000100000000000400d007c0020018003001800200140000034000000800000300000008000000000400000050018000000c0090000002004000100080000004002002000400000130000000002000200000010038009000c000000400d00180140028001000801100180100000006000000300040020004015002400a000800a00040060008000001000b0004006000c002000000
  | 45 => 0x6ece12a166d19b1c58eae7a00022583d2af562f7198a88a1c983cf81d8000000031112260470ff845500fa7ec00000000cf0885a3f80dca5083f8986a0002faa0001ef8b128000b15a41ccb809b216b8000ca00978048b442b72174a832179c0ad9cec2450682a128d28931800067124828358af6000152600020187d500000001e9a92f00004f000000001bfe00000000df0a721258000852800010e10b48fc343854aab7a0002802afd8bdead208c40000930000000086700000002ff40001e28b941d768b897de8b718e2926123e817954e64f0000814a40e6d880006cb862a539800048e00006b5800051ca99869300c20000000000014e90190380821c5c40b831210b212a1f7aec600030ba0001fde0000000529344cad500000e2800200000003fd1eee99f84e2446900c8251c7444323bc00016f431b80000000df44b015689fe8eec0910ce096a04900000e1a656877e2070000d2d0a5c00034ec1aa8b8011a90887780dbe00018a0d1e000053521d00002180000052e000000000000000001768000298427295bc5571f3a01e00000000000000178a9538000ae894e882801ea49701304eeb1420000df00e81a38746115e0000db2000000096931be999a352012a040ad3281e370aed254727de7d880000b399dc00012089ae1450000000000011e8d33aaa84dd192a43609c0000146c4688d46000000000000000000000d3f0ffc60027a6c5580ae04180000000000a1122f000028403e6800002300000000000603800039a00000000000572227e2e42786000000000012c47b7129c00017d4be29a726b2a192530350066f199c5a6800075618e0402000000000002b083206cd09e20001dd41832b3054795b8000261eaa2b0089b70eb600029fa4fb2c5202e000042d91f0a7d080287d11da7f015822e390e29ee2190be7800000034ac00023d844199a6a520000d12800034280002bb0000573006697d00005671b0000000000002a52bd9ad080a885285cb19b403b8000000000000000006ab8000000277620e0000260185c77caa9a00000008cd286a85ba8cc409a61686c00007af9366a9cac7ecf095fa23e88107420790bb81e1a0cd0ce20003550000000000000005baa7e29a500004710000000094a2eb000000004acd0e840ece4813c3baad1c1caaa220000eb8938125e7138e74bc7000000000000000eaa05b0000000000000026260000210aafab9600000000000f3a90796b0acea176000000000000000000000040154c000160c0002e5818e97be92100000002d1ab2a9460444841a7c730c41da0fbc5c795860002e9a00020f600015ba7f9000000025d63ed9e26229acfea5f2348d320000000320c08e87b20000fcc78b800091a2a76b37a2940000c2c2150d3200000008d10000752346cad41998afc87ee2668000b1
  | 46 => 0x2aa071c9cf814a80002421d5a62090aa5c810ea66bb00e2c98220000204613a80009e1000069780000000000668800000022ee000170665f2cf85e78142c7787346d1019e08c034620d173ec3e8000856305a30eacc6024996eb788caa9ccb2a662c13f47e9000000022c20b686e600030c2d33070264b80000a09bda71e8000000044e66416d04fa8000c2500000002d24a18041e00032d46a19ca0c060000000339e000010c86f0abe00011a000027c6000272238f00000002252bc5a896117800019eb216cb09bb859d800026a0000b8100001c6a94c066991c9702d06879ac229a3255c5e921dc05e2fc40dea7ecce32b904cc26387f700ca43d26f2a33874644e81cc6fa975e427089870d800087a8638000169600010ac000000095a000028ca76e0010000210167200013f65bbb5346fe8000579000000023ac56aaa7a2b79a309e9000072e000000010860d792d6881800069f9b5e4359218d0086ae9bd08f0c6217da9cf06d4a140aa07eb2516cdd0cca000000093f800000009061a40d98000000000000003b296be01e9dca81595280b9b2fa0000e2c00031ee1500cac000157a6baa788bc000000000000b7180008b6b5229788000c5d000000003ecc9200000001ea6b5b000003b33bc014b38656b00ba84523e000031540001bb60000aae000000000000000002bce045000000000000000000000000000000005f39a9a5450ba6bc4b25051b9f56093817c8c42a0250185063739fc6c4993420e72f30000070a4c3800016891263cb98fe3e3000000000000f721ec0000000d2a8000c2c800085e1748000075c000178880987781de96bc1492c1271f000032880002581a228b39068ada0ec0bff9c90b74b45800000000000000000046e40780006d0800000010ce0001d1493380000001ec0729086ad3aac4e1991a54ada80005d5301a7fda9ec6eb2742b0b8da455f117ab778d6ad4f0ae65aba31c27f0ca616eb1286d821a827baa2800031f2b2a2ac895b9dbc26e0226d01958806da6e242c1c3a7cb0f2c1952f18a921eb4abbb3206740000d238e481a5b51859c30762bf06ce34c0c728a1b2f044008729c8170c000000000019fe2e8800000019501a5259c7e380000000aca00000000000000c170000000000000000000b300000002a4ad40ac945b5af889d680000c3943a0000000000208c8e024d8000219400000a0000000000000000000000a85000091e9abc9a0a9c81b793909ba248aa688eb29d594424afaf485a41d9ca3a2dfe0d88000520098a00015b200010dec4c800019a000065c937e1db22e6081035a00028840002cc40000000485029a41200001bc04728e480004ef8000a63a174000167c37ea2b800026180002e78b399d4a7e7333c452337e41100000002fba8712e944da800084f868c2dc18fa3810a
  | 47 => 0x3e43671ed69a425ae19200002f88000c572e848d2800000003fa89d20a4590004408b0bc407285c88be99f859e0edab2f33b4c7c000000002a60002774a8308ba8520c88000003cc9d00004939c9676e896a73f0000abe0000c512780735800050e06ec23527ba455800000000000000da600027f4899a08851d1bca3af8ba065a1bee236800005c00000a2800000013d21239276220a1d600005ce0001b4e6dd2f1a66a80000000000add800085f81c00979c50000000020980007820000000021c0000000000186e000011ac500c0e000006e00015f07ab0f9c00008680002a62000000011d84208ea326a980800051e00005b6849839aa2e8139800066f9d4000000006901f86379249a57998eea580000d08b0b600003f200000009e880000001c0a4ca00007700ac40130000a0887a609317d6000000030c0000746ac0ea481da29f6a07c7e4103a20e80009518d860000da20003232585000000021429110e84acc800071900002498dd228f8a8c00010e87c100000000fb458200000001dae00007d400000000000000000000000000000002c9aadb000032c09ce341352cbb29f94191000000000003500000981800076903a8148a1c0c2f21343fb16440002cf20001b8226f11ce0001a8262c9ade80a9816aa6271c02fab9ac9b0000cbb8a86925800035780e8b5a06c84dc0136ac22d4e000187e5270000b8400007c980004f18d36ad919d64d5862895ea4aa469000000000000000000bfcaefe33f85264312744bfb33700b497c4000312aa6988085119d10c792af25960de80000000b509c069a38000940a6780108000c8eb1c2adf1806bb92d3c9299bf6392922ac5ca51a6250000136800000000000000192bc280000000000b9a33f813186c60350b8c8a62f04000313658600009159b5690f2700aaf1bd816691f8812327cbad000000016cca5f96b63aa1b665031960718000069b8000b8aa24000000003eb800000000007810000aa184f20531c8860280000000000000217a000105290c0bb211e0d74d1c8b9484ca8b00000da053d246c6b8139c75725b413000005382ff8b7511cc13f934e17b03a454d12068c50bee7da80000000000d0296fea1080000001df809f2854c40b3729aba028b3e8bd0cc8a69a000000000000000000000000000000009e66e780000e000000721cc0ced9b5a000178c163800053380003bb800000000000000758b63050eaa88084000221ea7a8000b0d00008c1a70600000000000a42000011e55c81a651db18e19080003f7b02c25b0f340001c78000000000000000000000c972038916233c000154437aacd8b5533ac576327aa5d0b6a96f80000000000a9b0000285208ab008000305800000016108599574000113800000fc1c4000035a00004482a964492b8824034faacdaf2c3840b920
  | 48 => 0x1a927d600c4a6aa5d21960cdc000193e7ea8134d318a6a9448726a4410f89c58f1e1ab29b000495f424380007840000000000001624620000bf80001b0eba7aeaa24d0000c15980ca200b304aaa78a145838e9ef00d233a945c5ed26308668000a4380009698000b8300004ad1668b08262a2200358bcd01800000000d47911e3a600007228000b02800043407080000396000000076a8be80f8000065700000000000000131a4f321680000f0600024c82db914243ca3247d0916652532667a08000be08daa4eb0d4452b1fca1782cc00002f3831a000021989360000000cae90120002f420000000c22a83c8989f4e9de0422c8b2e2e8cc000021e3244550179a521972ac6600000372bfe0000dc45c29b50801a9080000000612956000028489b3800062305bc0000000c7ab04ad0900002be000064d1eb6a4a00007b298129532762a1cb2e8000000000006da13528ca0000000000000000000004b9ad5206e9104c02800000011c22ed9d901ce800006b33c00000ef43b094e499d316244a91f49dc0bfc4a0932e00024b0a132d9425321305f2800037680008299c1c000133c0000a747a92ba89eb8000a3e80005509cf400015d233f321a000296652b86d879f0000b5fb3643d380009948ad80001c44000000005a0000bb6116c0000000c520000a6408ee000056a0c018e400b8000000117ca89b46ab579a2e6518f3645e18f027eb4b8944221a000029e541a53e77d8000000280ec602b8e00000005121d8879695a84b9000012a0000000000053e0c84c6429e42c297a22308000000000000000005090c668f5a0c20831c420ab12d4c41953e97c95a230d126a0558000000320000000000000000c8200000001c8e0078000000344e36f33a09b818767338008c8133dc0000000000000000000000002da45de946a75d13fa12d079e2a52ad400012723a42a2045a89a4990969e345000000025e8000015412700003b3000000002fc8fa0fc2000190c9609fa89248000000311670f335a2cd23dc44285201a69622b119516738110e8932ec0700814831c0efa5c8aac69842ffc73095d4235953c0000000000000000029c23570000b63aeda42b9aa600000000001f5c0000000000226c09fac8c713127e000000000000000001b86000193a000000000000004bf0000a38000025cae1461c116828a000075880000002d7a000293c3c92466000000000025d470a026a000000066c2e080ba2c3c7a7800000000000000000c1782c4ae5000066da2486b493202e22dc200000002cf34f0000000026f862012080ea000000000017363a0958052a800000000002ba00000ca000066780000002332ceb9ffa8632f20ccd0000a6a0bca4f71d428e0b0f0cc7002a5b80000a290f0048e80003980000228089a3750000000000017caa100000
  | 49 => 0x141c0000000b261b14d492cd003310360001de4000000052f25648e91d4c3e0073870420ec00008c00518e387dc0000000207680d03f85fc8cd62c4b1e800000002771a6c58b00000000f3c9f914ccbdd8bbeb39000032c8d801c580101572a5c000000000000008fd80001b90ebabfe8b5e23180000001ce40002d72a3b000065f93d0d45000000000009bb800000018dc00000000001f8033e80006c9af6ccaf0df290580000002f1067c000000007f05248000000000000001b400014a8556800014c00003dc85c00000450b8eb078000190899028907d780000000000c331298000000087084ca55ab4c281a9cb400000000002368a741d04000185000026ac00000003872fd200000000001cf000000002ea01126150c78000000041600000001e6ed3129680000000000000000000005d11c1831e800000021d43988000c66a6b2c0000000000000a5000000960000000000000004843f200003a31c38000348a00005b6416a408000182e0000000c8e238ec89b1da000067400000000003234848b4a44a3845200000000068f5e00025380001444000000041f2f0600034820ed034a3d20000000188aa2d81a2ce591d26a81b207d29a68ac428ba49500000000000000211623b1de6a34310aa1e861c83c349e75180000002b0200008d800000006041ec4352acb0998b32400014ba6132f58cfa850838213961f108ac8e8000018480000dd07ae7d400003ca80005d39d000002b34000083096c311a60821500001774b4d2e443d6a4e400002c82e90000b29a25c00000000c2a76a8ab00000000000902aaec000292eb2d9b846f9ac3a0000000a8f2e5ea4782b004b1e22ade05b41f3310c0002106a39800000000008410000c3014402859f6e3fc800067893c40000000792800000000000000ef2c5b80000002e1a000312e0d90000000106c5d70000b8900000000000247100ebfa9c6c8df176e000248600000001220000c090cec00000000001fa654900001770d3a000092a00000000002c600002796bb5a0421d4a31a000000000000000002ac44df0000cd42bdc3e787b892d80005ba000050085867b92d981f9a9cc4059a8ab588918876059861886803c2a73836b800000015b400028120299a6610ea44a00000009e68000c4d0000b7700005098000000245200000001760d24563800e0001b30d079f5267212927230e8e8f5069c00000008a90000000336c00000006f5b1040000000000000085680002d932eaab72754000101a17c3074c8f92780001758d149c1a4721f44c3da24a33900007db2bf411929a025c0a60d3a2dbe7fb800057780000001ba82ca2060a22ab627aca22c000212800000004aa3030be42d040001fe2bb70d08aac80002fea1da000144a0c68a30000000000000000001a109068000626000016803bc
  | 50 => 0xc50034300da0f12043adb4c1a9ee25c70000372ac725e580000001e761d0000025d06d61020a8a0e480002490000bbd0304bfa08ea7c08a88000000002380000000000000048a0000be4934b16604e22561a102c0b8d025226085708db948236209a683824b48431dfc486ada600024d442f82549122ec84ff85fa2b3351650d87984e1a1e200008c800000000000e64167316a18407184a285a63bf00000000000c0480000000000a2800007541944a6187c2cc20000000000000000008ce800000000000390000000000054d8000000000004080009cb9362a9b8db0b85b5122a092c8000000000000221752ab80982c2a00001b000000002b02472300b484891a0142388deea0a214c833afee02c85964bb1ec6bba1198c34b25ed3c86b800023546f8a7107a60000d19afdc00016e234015be00000002c210f0000003800000000002bca000118e000000000000004f5000000000000000000bd91314000203094ea5667dcaf523deaae458932860000000aac23865f0aea61019b4878492ce1998cd24bd98903db800076c3420000001c50c8ed800003b60002e40450294e9d92c9293c0000000158a000253c000276c000000000000000000000c0981e80000000c3280001d200008fa8000000000008480002792278134865c43e8b441f21a0ac958000692339c0000a1864982bc0000e1443518140748a48728a0e2928a7fc39f95a03a2a6b6239ac50000124c9c980001392a90a9980008b931b2591b31acb20c7688d2570928229692e189cc1530ce2fc247c15c9262110b1fc18380006b0843c7e080004c9836c86eaa2e2f482ee5370352bbb80008059798000000000000000000000000000073200008460000cd331a00000ea688019f600000006df9ffc36b06260151d0ab8c317aa56000060d8a2c6359cc4000000000028746b98d3453180a2ab4a0da7eba03ccd0934c39732c49792f600002bae0000000ce880006328000d0f87ce0001b287093446000099800022a69c1000000014d035eabe0ac3249c0003086cf80786000000082faee20002d280000d067211824000339800000006da8fa80001a5c07100000000000000166a5dc80005f9a23017d936806200006b60000000000000000004cd00000002d56d0100000000000000000000000001450f8a88ba0623d1889450697ccb730b1400000000000000000000030f01da2fc80009710000a2fa224000000092eb17c80325048e7800000001189eda542bfc2b22000000000000000000000251af1400004d80000000425a964092000098397dc00000000001c4043b0000000000060222c000015ecc161f604318376ccb80000a1000003600006ef81960000e9e0000000bee000005d0000b0700000000f26000000000000000000322000000000021cc07f8bea0000000000
  | 51 => 0x3acec0bd22b400019d20e19ff2d0b00000000000b19b30c8d9054aa762186ad3b1d013e8b02c6b1bc0367872c80b1e8a276961c698a2700f425545fda4ca5a02cf6a7985ca000076ea3d07502290600ca434484142c08335107a9c60b4e979a0bcc3929c628dad0a80b8b1c355166000004f84cd906e0001d9800000001f4000023d0000a030b6c00000000000000c8400008610d6219180000f633ce000000000000000001fd46298000350800027d1da8000000000034d00000000c9a26c000000000ac800064b00000000000000090a5df00009b680003b52156000000000027a0cf620e486925c85ec255a72bb37c25900323148000327a6467608c608662f026e893a0a2b800073a0a0a0001f7c8578000000173289386a8324973000001ee8311b0a144b34446da67c77484ba40d000007e0000b5d0ea47a19a2c000012e1ad0cc48b192220940000bc21ad40000e94b5a80000002fde262137a9a191ea6e2330a970912e87b9c54000000007d0000608a8521fa1984326000082180000000e280000000c18aa6a40b1e3000029826b72b46ae7130600007447590592432053e02a2c7c564ae6201c30fe00000003859092ca300009d71eced2a2d3e5188602000266490480000a403c60000000000324a0000fd62381f4029a11de085085ecf680009f48a1e000000000000001988000000337800027e60001b0200000000000000a7280000001de85be80000000b1e13d0400461847a0001d9eab4252417a97bc06a9a427de80002f62e920001f4cb46127a00030a02c6000079b098e19fa478beca21200000009010b3a01800007a580001122c3800000009d798c838829f00000000b762442644054c3a800000000000000104045600000001d840000d0c0000aa800023da8f08c5a1c82876b839d1eaba80000000000000061a0000f383fc042a00018be0000ed6000000000011e6d0a899c0000efe4602c481e3000000000000001dc6000000000000007b20000000116000029e00001f667ee32607cd88ae0001d6aa9a1be800034b62228000c85114c07426e44792a509d20000a468000000190ab21897c8268f1c70fa36000026000001ef0000069209ba29a000320e2ee2d5c8d59e0ab16a9be93d8000000023c00011ae41c1b8a22c800000000000002c8071630d820ca20a0000000156a422000000023784240001e32000000035f80006b886721442d26ab68eac48293b8037a18a14ea9b8ca21c0e00030442048b105369ae80000000000157600000000002288000000000030920002712a49000000000005cd18f8af4145290eac8882eab147a728865e507005198e249528a4a1ee86141dd1a2ac1ba14056da2baa32328ab84a8a60738c10ccc8cb8d41b51c75ba6565e100005c601d6000000049f068ab328d1ebb521ca7ed0d8
  | 52 => 0x649df8a9ec9900e2a7fa0b4cea1fa200000006e68a9c256000000012d80000000b1c2f84abe973800000006491ac081c17ee371b17e0002fe23082830c8711502541c7e0629bd49f432a2c84a04a88c93b697c0e2a0000000a950cf60d72cc20bc0a708f31d720000000ae02e880002ecc3c6991416fa7301821a6a00008049f60ccc00013a64f3a8822bc8dd600000001b800000002036517882a01701441ff2b2c79e855014701bc9a6188e87c33d200000007b980000000000000203a5011fec8f4a6f000026146a78000345ab8c356088c72aafb44d20000c96301eb56b302d188f2094a2a38b8800000002c6a2f99a8c25b91f24ba8fdc0002c1e5a30b4057a2bb41788ee20001b32d0705dea62135aa3003f04bfaf6e7632b5e000000097f1eaa0a31548456a108080a12c09730c60ce043268a0d7663db5286b92536d3622800000000d0a12f2c721270a4c80004ac80001f6a0d000000006198000937800024a00007cc06b27c1aaae4fc000000000000000c54ac390780000b2400000001bf8678a9090a6a4031b475c0f8600024be6b417f80002644ac6b1a2865b0887862d7c7372deeb6e800002b1a1401cb20200000007bd80009780000000081ebb9a56281b91940002e3e0a587709d803c400002980000de20e9a66ec87a394cd480000000e1e07980000000e960002ed00c5b47e00009d67250000665a63a00007f43e4000000000000001e8800030320002044000000000000003be033a11f2db0000000000013e6000090c2332530bdd000038330b803680000001a0600000007891520326aa1a15d00000002ac226800000000a78019152e470034c0d3abcc27db4de98892881312fb0a2e077200015ce0002f680000000b610000000000041c939200017020001240000000018b80003df9db8c1995fe00019580000b6610594086cf0ae06530000683000054b0000c0f00000001434000000053a80000000000000000000027e89300000855000037d80005aa9f5a29980000001418527878a4b89f844090000af681fc8d1b0820fa30ea24fabec1932fc2b990f60c6795e000022d800000003f380006138fe664118c0000193200000009a231dc1ea05c243d9ab400000000000f66c9fa85619400004282ebe0000a4000019c65ab0ab000033882c80000313800083500004a82cdc000000000000000000000000000000007d2a748b2200009120002414a0b10bca0109c20001ac4ca0b3b804fa9f8000142e55fa474b971cd0a678f1613701649ffb30e8e1000012491d80000000be4965a0002de400000000000000d508000c8ab380540022a592b08401f0000000000002d2182564000000000000002d80000325a00028980001c4a79125ea000178086b0000594ab04be80000753a9ae0002b24000296e400a3a6af101de3e
  | 53 => 0x8dd0886d1012505fa33be0e6923c378163800009320000cde000309a96f00003e4863c133293e8baaf40d23289e00000008bd000000000c60000ef00000218b0a16ecb8b0000c2925226ff2b207ac2746000018c0000b0c8ce238cacb8bbab9f28b44421e4820880001010a569d633d000030fc0000000be5afe44b6b43c0000c086798000000000074d80004028104d1ba36a3ef80008b800000001454cc10000000000000020dc000000000000000000fb800034a60000000000000000027aa99c800057aa586d20000002700000000000c13000000000000e100005378000ccc0a340000000ca93246c8bb43686e286c99b28d600014fe23499a8c2b2efa0000000000000032700005c492fa4eb804eb2e81fa0000c14135ace042c800056b8e361e58a46beda926d3720f84e283aca34a0fa7dfaa5a091826c1550000000235cc88800023399626158858b2080000001bf28de9062cb196f27950aaa785b252bf9b19c65b23502ad80003a008747770b3800016ba00000008be33b07908c6a57110061e380004089e4600019802688c5e0000000ad1009a3ec1ba600004f682e0fa42558000376187c0b812c262e17ac3300000a8b245a0000000000000000000000bd89f0548800000003da682000025790285c10000000000000000000001416b518000000000094ab5300c606f8c2c000000000000000000164003000000000000000a0c9dcc2f300008dfadf40002cac696926eb6280000cf000031f80006de886c20f8816cab91368a324c2096a8da00034e032f8c0a250a72aa5e89400eb9a989b30e50c0524cc868a4205a914a639eaf440bb1134be9aba6bb085d25b506a66f70a922fd28eac5d90904d5244600000000000000819a4e222780002da11b000013c86948e6e4f89fb21e88000981074c000220c240b49a0000000000000000025eca55800000000006e9324c0002b840bc800081eb0e06010000215922e1fab338559000099300004608fca79caaaaa890428000135200019b20000b7a98f00000000000c758e7887fa260ac980009450000c00800000022a2737af5000029c0000354000000003231502000000058c80003dd800057c83c23a2000026e8000bab80004399d20000000000000005a129ba000185824422ca248948a00000009832d4c6911b3e7c691ec7c00080000000000000006648bc000000009de800000023ee0000000948000000000008e68f4003d80f021b805a04980000001594abf80002cf8000000230e0000e6c00032de0e880000000000d4217ea90d07766838706b3883f400022d60d58000000018291c000000000000000000000262c0001cfec23a4603f400000000000c379e8e7088bc2000000052689ec28404ce0001bc84c08000000000000000009b480002390a963a89b
  | 54 => 0x11238eb5320001a76c0733fa64da43619b9664000200aa9028200d805d61e49bdea52967407c96d841732708c899b884d9cd293680241d89e3800005523071766000000000003e2aff0c3e8ad93c29928000000000000029500001d060000a580000000000000000000000000000000000000017e43339382b93a8ee00000005ac800000000007979a02b11006ab9c8000000000095604120001a643d32df23da0000000000063785da83aab524858a2000000002af235e000079abd38f020e400004de17148eb8aa6197a218aec20b0ae28000534994854630a66899f16ae4873e5fd332872099eacb69efc4328000aa7000012d960ab1ea48c6ab0c8a9b1aa949130dde3bda576161274a96114222f691ee099a5b608d898428e90427580ffa02f109a321a1b616b2eb665098743f92d9e48a27e000000000002afcbab000000027ca075000090b1f2a2ed211ab6a80000000000411abe600019fc2d8195e00031f89040000c74aa0400003d400031b000000008f90736787aae8000253446d1d02ae900000000000a3c0d6605700000001fc8000295e00008640000000000000000006060002e60821119e0000b5491000004199d92c718000000056200031a400002d0b9bb03e000101c00000000001a040003494b48129aa1f306c1d9b296cea8e4ecb3872210d816696a96c42cb9c8008199a429428b2a4c014a453b35821800000cb9f3400000002ab148c1e08f825d9112c0000000000112800006ccd51000000000000000000655800000020c00002ad83b928383b78000c10a51e000287012808e85ad0bd463a8000000215c0001d7a00001c6c98800000003b000000000002d7813b800068d93a87b69e203d90f889279318b0b0bb03de009000000005dfb54e2750000346800032380007fa00000000000000190000025b2a3880008b5000032d00000001fe00001776ba8974cd3e1d2cc701b8c000000000000004eaaf7215b1e065a28000c8a352672c800050f8800af22a64815270e00011bc00000006bb950a0000000437060a23402fe000000038005585b98ffe81d116e0002f1e80fa33e4840ec697f800000021f60208076c320000000000097695d00000000c728c04373303a000222a82600000001f080000828000000000006a26cb281a2bf86c0c2597a885c049a0c700008d9932c09c98d00000000748aa1890e296a823997042e04e0000000000000003839a569bd800000000f824ea1a05ff1698000225e3a68b5a283265a43900000002cd40000a6c00000005f815700002a3600000000000000b1014907552e0081a02be0118000b70091e0000000000000000020de0000000a232dac89500000a80000000000000000009a121e000000000000398000000000018c40001b5258f14686d328661f71ff439620f45329ab00
  | 55 => 0xc1c01847f61398b24270a5c382b480902242bc27c8c90061887198424881d8041800347a892de7b82c24899164c00000005c59728232b16c0000000c90800000021a600022b25a18db45c20ece32926be000142c000000035e00000000000d038fa0954857e84780003c20a064d795783fa8954494983412f22d24d19cbebbaa590b8ca3f238ba7d40000000000218e83a2f3e00000000000c74000087a00000006ea80008910000d18345a7558000cf3000000011140000000000000000008060000848000000000009b00002c623df00fe12180003d080004640000bd28000917007e2baa9703ac000052f93640002cbe8f02798b0d8000bdf8000a9f84e8000000000014b653b0000000337697e9e340001332d4300000000d6c7c323200000c1210bb31e000000030c800056c16040002b425b197502148344196accc000288e06715f6000085c724800000000001fe19940000000aa00e703d8968ec54040287a087ecad800095817a0000000094c80007ef8e5a97780003db267a0000000000298cac7b29a01b35522722728c0e108aaf098ce76180000002a0a000247e000283a0000000ad7000000007fa4920000000307ab6584a600003820000b82000346800023f4b818b460e533e6d141242cb6299c6b38000795a3ecba70b989baad008839fcec7d21646ef298008287b479d28c215584a4b9f87c0bca1c046f4b4bc054aa3069291b2000237098d86d0b3a240c254b0e2951015014c984692b80009ec2c9667bae0a6e39000641a4260001786445abe20000000c7d84ae2d715fc5bd93b273b902a50500007de0000bf4000013091ca3ad23a24812d2c000208014f08be09c0000ba0800000000007b08c1a0001d3ebe50000000000008f9bb068c80000cc800000013bc2a0000044f0000825b3d4000000059b00000001164141000000000000000000286b07cb73962833432b833e0eae7bf8d642458d2e23f22d069184d041294964ae895cbbc880a0d01530c6501ae97b961690aa7c28c616de7080110d4aa2aa0001dc800002ea9740904cf130ec650108e8048784317000000000006f80cd8000150e0002ae000015ca0001e605a2127400000000000000d5205f84f833e4726875eb861bc4265292a2f1a2fc99832920002d30a9185f4c4627dcb5dad607d206f2000179279623ceb66832408a31a642a34e2aa9a160d17983e0000de614b0000000057a1e9000658d2316cb880009df00001e2000000030163a4b4ae0001188aab33d686a80000000000159800000031d40c18cb60002bd4000000006ca52c00000000002cf43129db22e708f64409074a31ad1eb019a9c33225a21050286bf2021e53b8ff6cb9270c00002a40000c6200024000001b98a4500000001e147198000000223800028de61b26fc87380000000e762b52
  | 56 => 0x80002a6aef01d6b1aa00030f81ef3382000242e0001afc0001982cb4800000002d46aa0000c890ab44f7921c6dda308343b3e800000000000cf4000000084400001c7000000000009c7913200013760001a7430a1aa28f780000000a64a271584b9aa4f26bf8b065e3acce3fb9ee81691e92cbdae28160a8f677d1db63cc80003da99ceb7680000000c82652866c941ae363849912b9c2f324382f0e2d5b0ee780800093f00005879a5856916c8a4d9cd45038ec84800e7c9f38aa41651df0009911836403b27f3300446a2df8b35b2846220688576870c4fa13b00001fea7430000843800078318d47991bf01d39dda11018aa9ea1b4013b016a67601ecaada48817187946db2ca23559d1212c82de3b70fb28c2996a2b4954a5ceb3a65a8871e55593a2b22adbc20d88f8c260ad032517d0b51062c346000aa93160e211201c0d2223e65e000025a01dc06800000001752000119600001f6aef0c0cc100ca800000000001c560b92d902138f0e8749ed07ca3100677907e0219ff0c53244e66185ee127aba05898000c5a000076d347caeb23789aab32c5b480cec37280a00002ae0000f500000000000000069c000028bb32a1f2ac64420311ed02000000019a05d6a0aa00000000b1802897726b0d2c92840fa919c95203088361d3071181601938000c53818e000181883f8000000000008cb2984e90000caa8a8e0000580965a3585d8048c35f2a004208e4c00000006180fc08ff0000194800034f00480000000a0d217c5e9ab820002612af78000cda80004bbab3c000311479aaa5e0000000274119204c92d2d51983ab0613840001202765b124000207ec48000033a2ece8519778d41231eafc33a497e2454015b33e171167e78b2bc0bf5b1aecdb844a71204945b013fcbe91fd0769ae96a7880009a80da8000279ed5306c2aa9313e4d42c783d1017e5a08000cb993d65ec913e686b20a89f0db8571800000024500d08016808a82a37418ba5701cac7548b7e6dba4e8b5c0ee6c2fb4a0739a0788c02f5c6fe313c528964258a81e2a568ae40002e1e0002e74cacb4ca78f03148f1a2229f5aa584cea1f80001ea09629cb63998000be72cf04519a346a58000308a3986259a88246a5b886f8000b0518c2ac59f8c4c40190a658dc840c24325f000008c3246495c8a229a90000a54800000000000002e4616a8426baf077c34e256a69ead50c11a6ca0000f0ca84904c765251891b80001c507324d7000063cae909b5000000025f600000009310d82000334a8ee269c7a4209e06e20fc0002f24000282660c3368cd0000029e840c4b1800093d0014cac063611800000000e52989000052e0000278118cadfa888a05000021d800086d259aa2a1264c56b434a1880000000000b648000a6d18d200002626e81d2446f800078aa79482b8fba
  | 57 => 0xea0227c00000000000133e436b3de000000045c800045d02569fe0000cfb8000986800000000000000d4e18c9bc200032c012a8000b0fa6fe000000024b80000838000662162e000046800016a84e38f528942d2228f226a1d592a4a66adfc62b81160001d8a0000b625698c56cbca208344b0365f6000071ba9c4b50149861c889c6c6800059211bad2600004c49344000000077080000002e9800012b86acb1129b62be4c398ee03488000000000000014120001e3e00012cc530800008d323672a0a2a16e1b5c8e585d03e8929e24f0036c2a06e873a859ebf1afa21eb0bfe38cb2f885aadb218d245eb920b4200000000001840ba82c32000232e0001fd2b958000000000078d8d2c5a72f7aa6b00000001f2e0f480000000000a1a22be000291810f882e6e406b66c8828e4a403fe000000071697ae0000000c861aa492009cc0002fa80002d4a00312ac9638000070805e000335e2f580000002d9ca4d0000000164ea7732ca00013243f4a5786ae83baadc80006070c4c626aad60250000339ab5860997f05f8887c8289430a3f2fd889ba1e469e1c2aa82313aab89656beb2b12cc4130a659867665e9bec994092c3498e30aa1333a8012b40cbf32a0b1607b64b2a9bc15f19f44912a74c488b2c000348815b9d682d4800026b0000000000066e836a77f92a241aa9fcd041394000268a4a3000000031640000000d4e000000000002b214b4c51800000000000000000c9534b07a500001811f7400000000140ac600031e08c980000002f0c45134f6000000000002a823724eeb89800041924fa13783e6c528000192a7f086bae1c0001c7600000000000000000000062d16a04db068e0002f98000000055ba6327ab800000028d400000c0d1da2260000000beba8d800018ac7ae800079e123600019ca0002b28614a0b641d86f400026b400000000002020849a7ea00005e68041d7c00010c0267936e4470000b1d00004060000c0d0128c580018000290c71aae3c7330000466b50a00011c600000002978dc0b3480000002540000000000000000cd800049b342610d2f2ebae1e702b8b0da4928e068ec80e6d2580008492a6003592a6c278fc4ab39920d2704c886782fa29d894887f0992c4b0a4c0c7a658515953a4830000b68000000026a2000130470c01f0000155eb44ac9e0323050185a1f2000000008e236c4a00000b171c32831a2029e4097a06527341c92ef60001fe600019ec92901722ef0c6c0000754000185a26d8f142c01e4e4999bf4b06aca42be94d844c0c9616a16fc1522944c7f9a1c7988b0400031e631915ee90620ca8a4a78272c16ce85c98da9c682c28138ca0d28a9725ae290aa570000705198e6b2246a5468000c659f1200026f8b909710d4f8e42bb780007a12df661e944e763aaba749ab9eb44293a8e2
  | 58 => 0x1deebf6ab7079fa892000000064a076a00026d0000282e00027520000000c289b1200015383f532d60000000187830c62a29160b29d0ec1902641ac1fd638d01240002baab03000075e1a180000d2000027687b60baaae61f686df32fe14693720001a204e217fa87224a8c7b00008f2972e1bab35ccfb279c7e20a9033180000000000a0d994e2f200a46c59d2a00026c4000000000030287ae23be000000000027082c68000bd1800004a800000034441bb80000001b6847f028000000006941cf6666800042610fe2760b9a69f34863cc13e4000000000011103541286000000066b34d6766adea0000000a7cb4baa3fa574854867ca1b8000cc52b5a4f28b8484f2d6688eaa34c6a30d0b108814b60b41a0000000000000000000000000564000000000020b21ae800043f00004e000000ea80000002f6a41500000000000474000000000000000000000318a0480a7c16311fa88d96f83e111a680c8000839923027f95981151af200000007b31fb62ae2806ba299525f1800004e950853eb47a203280040fb3626ae2a1e00006fa120000020692128880b506318000d369d2813c2592280122c12e34be27188fe51c0000000000000008849cb1e50adb80007aa1c9e00019f25540000ce5093838f8000ce690cc0002e6cccd83ee000165c000211c00000002d300009cf9eeabcf0000d1900000420000483ab1c000291283480008d0800021693ee19a884c3dd0a440002ea8a9580008a1000000018fc53f27404ed144c6c2232c3d725800cc00008c099c0ab7a35a0000b2ac1c9692c01824292b26eccab0000d3d18782dca77267305760001f9e4d032d0405263477b2f360000000000265e74d1e520002bbe3f6a9066291032bf29ffeb712b0a5d58000000095ac2d1cfa7eeaaf600005460c0aeb0000208263a25ce3ba21383b4027460a15f800000000000000b61a2cc2ebb15e47500002ae8e460001a1e0001b2a8240000732800035815e20ff000000034d4000000000019d40002f78000206c9c526a600000000000670142abd858489440000000000183800027c40000000ce40dec1d091ac000039e00032be00000004b800000000ec464c000000030e8000000085b0000008000000000000000470b040e40380816e4be250e2a105b2721add030786981cc328e487ae869b99bcc0000000aee00000000c403f60df8b4a800034ab1ba0002a8e3122a3a491a05818f9dd00562a7c58180000001ef29358f100f5af54086a3fe0000000000000074c800022400007901ed223c901000000003af2144ce3ac84617a40260b342e00023769ef9d38a5b000090a3510000000000001be0001e6600010ee00026c201d234e5800000253800000000003098a1c352261c00014f2c730000000000000011b8848000000000000000000a7522d
  | 59 => 0x109e22d8c060001f9600008a849680005c0000000025c667800003408000d3484440000000a2897c80000cc2580ac3071c1d16000000000026fa65d2be8a2a9f7600000000001cf20002f4caad00002140000a3923fa0002dae74f0000b2800005dc10c200024ec0000af413f054400009d20000000000097e00014844e783deaec86406193416a4b20506ce032602c000000000000ee000045c00000efa25a1f896503160ace1cb80d05773158d3014283f180006289f384488000c4406300a2000000000000000d10d468fe00000f560001d668bb326e461266a50a8000abc00001199a3ea47142002a85605358e5e17a17ba2f82eeca070000000026845f9bcec2ab3f237732769b200000002f80c5c000037f80001bd80000001c00c6480008af00006d2800000022c800034e48ed8000022800000007e49a58000b3a97401ec28162e582b88e728c427a9b1ec9e1d5e8402490ae190569e3050016c0534115b3e2a509bb2b17832ab930000643a648223800074e9c1e6eb94588dc9dde58c12b081c8000c2306bc3240000cbd0c3800010847d1a5000188000621b470d048000000350e000000000000000001c620000000acf8198afb98b63dc1f9a99db2201b485786e59af436eaa78000000049580004c88000caa0176c938000417880e00000000a481a8c2b800000032dc000000000014e200000000001ac6000204c00000000000000000000000031384c58000000158c2588000000257c551b34eac1b4ee99c337a9092da263d00000000000000345c0000a540000d70957a9da0000842a7b8000a7a19541d28d8a0000000612000089e98440000a246a10000cfc000000000002a61e5c824800000000006f18000454a2ae9d40000b8894645550a385599cc605880001a8307e840a62e0000000b4c80000000000680000000033ca4ba00007f08000b1b92340000cda7c505427e80d84ba922042cda000a138f186cd8000000000000012f400029b62cc9f186e4856895f8e22bb11902d249c5ed4da12e30d89f2c54a7f23109dfaad82f2234fa2a02249f325239a9451ea4dcbbf33fe595259eab3213ac041552bd886fcadd00006ee80006bc3318298a588277b02a1f620ee4ada304cbb227286229de2fb0a526b6a0643ca036e0d983788b125cc606903c11d0350afe16207c284302848d52000000000000002ac9b24aca8000000054e5440db6b7e9258890af3a000000000000009e48facba38764b2384469d9aeb29a024eabae846c8cd915c8a71e3a6768000b09800000008a2000000060cacb4d4e87f2c7381a45c91dc402da85e504069e3d500009aa200e27a00000000000b7a2da8c78b10e000000072f229e0000e86000306000000004ca800000006600000000a09000000006dc00012f070980000000000a3c930000
  | 60 => 0xfe80000d941b128ac000000000000000000d72000000000030f200000009c900000003432000238879a00005b71f923e6182a0000000a26a2fe54480006ad8bf68a2800025d800000000005da8b4a452973c0001ff8639991633c82d8afeafce000274ebfd8c5083c800080780009ae8000be6b23000030487ef00003c12c4c20902000000000ad9800010404a262f0920b368cbca1fa90400005feb5219e4d3fa10a6aab3c801a00885a502227bd13da7b515c2ce2b11cb012d886b30ed24b731d822c18d8bdc19c22d210045d0a3aa68490a4783a8180be309c20b29ce6afa7b211f82760a51e4ca172bc6000309000000000001f2257580003950c24000269e7c3b1b83472b56c819b9c7e29d2eb1500000000000556000098f80000f2829c6c62db86a00d8e000256c000228ea55000000000009680888320009868e802c00000000000000a65000086c8b58b4e82dc00000007388000000000047800007d9347439c9af685396666e007600001a3c000273a82b33fc000150cc03143c00000005078aee00005fc173000020606be00000008d8837e92c80001c39afa925000000000000000000000082061a163e7738000000000000000000000dfc0003052bd6800000017d26008e26458a8f800000000792162000340c70b00005d180004af00009af0cae0002ef8800800000024d0ab9a9f6a5d99fa8ca841c75f9c169fbb0804d29ede8ed12945b92db60900a4e6e50b0ea75800000003cc49817b8ca514f6b3f23903e589c45e400009661e1c532000000000000000000000038c00000005588b740000a0475b04189470000aa30000d15299272eb29c714a594a5188bc000147e939827a6630000775810acd1940a0000b78434931c4fcb068751255676822a820f050200014f00000000116a3c800000000002b3800010ba64e0e189f31b708c4800000000002a897821a923b0aa0add6b59250a1cf00006f92cb80f00000b9da98ac350000c6180005411964923b4e626400005169a4e05026de47580000000000000000000016f04c328106981b540002a324d61b728d02bba8842fd47c923e6b99b3000001aec0002fc089d8000000000000023c442500005311de200017fe11300007c8290200007a00003520000296226b800000000000100996627b3120000000000000000014b20d52e540002290a2f0a0277a800098a00000002a92566ad0e6c31ca6a1609660000000000167a646084a0000000b9487aa1f833f67048e0aa81aac046280006c10000000000000027b41b8904e3e50000000260a00000001ff80006de27360001c340003490000129614e2f860002de600033b21889dd89630588000136000029a40cfad3600000005ea8000ba3000011888626330a086f404be00000000001c6888f188400007d6000000000000
  | 61 => 0x23d00002cee000065635bab4a63b00e000000006c4000000009aa60f1cdab92a8460aa88aacd582bac138000000352eb0003f60000d9a00022820000000b8e015e0000b9e49a000048c8b1600000001fb1c0caa7b1787f10e44000166e33ba78e00008b4000000094980000001f100000000d529892a8f8000be30000a250c1800026545868ada0000896c6d9a9000033ba5a98000aa20000a1e34009eb00000000186000000000000000002922af58000147b2cc9970000000000000000007c780005b28b8a598a5cabca81e0b7c2c76d060bce98819e8597acae35691dcc089b582b707be7bb156cb431ebc0000c2e2dd9efa8331f984e3000093e06243c88d964c230f447da05c00003c8cc5a21c8eeb2727cfac9c4e6803e08593f8b728c2a648b3c60002692000017a76f8d920002c16117000070b8000162b3600001a1629f800000025d800000000002aca2b58000bd780000003348b4509b4000000028392ae03d000029689860002d58a5e0000cd50000a91191e702266876b0000a0f959e42880004b400000001b3a1c100003e9800000000000001e8c0002a2acad16c247f88b88f880000001fda0001e000001726ac60000000232800031fa00017b60002af4bf8264e0000000102800080680000001cd80000000000000000000000002beac6f33261f1a2f6b1a079c2df2e5a0002d3800000000000f580000000cfd07f6000000014302d6c0b86ca0000cba8d300006c18000d0500009c082e226300009b5a43eb8095967cf1338b7b1af80002608000117696e8000b40a74cba0191aa9c000000021fa00000001160c0000000000000000478b02000000000000000000181e0000000d1580000000000000000082a0000000323c000000000028640f3976cc4213d8000000015797ec8ac0000000000082700000
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x5530c920d06841c5530c920d05841c5530c920d41801c5530c920a448154d610c920a15811516314520a258119662d0520a0f8654c32d0520b048154c32d0520c28651c14250520c0c651cd6250520c28651c16250520c28659c332505209a1819c33250520a0c8654c3250520b048154c3250520d05535c4325052094587cc851cc520a2581150624c520a448154c624c520c26655c454c8520c44631c553c8520c44631c5534852084d8718c5148520e075418c5148520c0e7518f4148520c0c7518d4148520b05831454148520e04631454148520a15811516308520ca0725854010120c0c7598d4188120c24755854188120a18835946050420e20625446050420c24765454148020d09545cc4048020d21545c44048020b098414d3048020b418114d3048020c3076545414802084c87595320cb10a44854c9610cb10e05544c9610cb10b048254c5350710d05535c85350710b04835485250710d05735485250710b04854c83250710d05754c83250710a90835806050710aa0825806050710b058214d414c710e0453189414c710b048254d410c710e0553589410c710a488254d600c710e1153505600c71084d8718c5248710b05831494148710e0463149414871084c8758d5208710b04835494108710e05635494108710a48835496008710e215250560087109c1801c5320ca10ac08158c3248210a44854c9610c910a18835946050510a288259460505109a1829c24350510c30655c04350510991839c24250510c30655c042505109a1829c26350510c30655c06350510b048254c5350510991839c26250510c30655c06250510b04835485250510834865d43250510b04854c832505109a3825cf6050510993835cb6050510d81739c86050510d82735c86050510d81735c86050510ca17250660cc510e0453189414c510c917350660c8510e04631494148510a31809516110110a14835516110110a24825516110110aa1821d9418c110a1581190534c110c30655c4644c110a92869cd414c110a90865cd414c110c90765cd414c110b10855cd414c110b80825cd414c110c9076d8d414c110b8282d8d414c110c48651c9314c110a9086505314c110e1065505314c110d8072505314c110a91831d94188110a25811905248110c30655c46448110a488558c3248110cc1635c432481108b08758d4148110a308558d4148110aa2869c94148110aa0865c94148110ca0765c94148110b20855c94148110b80835c94148110ca076d894148110b8283d894148110aa286cc94148110e81630c94148110c48651cd2148110aa0865052148110e20655052148110d80735052148110c91735066008110aa38258d41c4110a938358941c4110a44815886254c10a448158c6354810945851c5320c810c45651c5320c810d05541c5320c810
  | 1 => 0x1c48635c35348421c0c769515348421c0c76551534842184e869d95348421c0d7518f4148421a0c8654f4148421a448654e4148421c0f7518d4148421a0c8654d4148421a448654d4148421a868398d4148421e058518d4148421c877518d4148421e077518d4148421e0463d4d4148421b2180d4d4148421a848694d4148421b058594d4148421a248654d4148421a848654d4148421e078654d4148421b068654d4148421b048654d4148421e048654d4148421a048654d4148421c857418f62484219488754d2194021d80735052194021f01535052194021d04735052154021d0a541cd2154021d09541cd21540219488794d21540219488754d2154021d23755052154021d80735052154021f02535052154021f01535052154021b408158c3254021d42735c43254021b21810c94154021f0332507315402194a87cc93154021b41810c83154021d21725043154021f00325043154021d10735052154021d0873d052154021d40739052154021d08735052154021d40735052154021f03735052154021d22735052154021d20735052154021f00735052154021d00735052154021944815d5320ca40a4581195320c940c89735c86050540d09535c04354840e09535496010840d12535c04354440d11535c04354440b218010e5254440b218010d5254440d12535c04254440d11535c04254440d22525c04254440d21525c04254440933805da4354440931809ca4354440d12735c04354440933805da4254440931809ce4254440d22725c04254440931801d13254440931801d03254440e095354960d0440e125354560d0440e115354560d0440e225254560d0440e215254560d0440a318019151cc440a3180991518c440a318019151c8440a31809915188440b11831c15150040b21821c15150040a4481549610cb30a2a82d506050730b04815483250730d05525c43250730a2a829946050730a2682d516110330e215258540102308d1811c1640c930d07541c5520c930d04541c5520c930a25811516214530a158119663d0530c18651c14350530c0c651c96350530c18651c16350530c18659c23250530991819c23250530c16655c454cc530e0754188514c530c0e7518b414c530c0c75189414c530b0582145414c530e0462145414c530a2581151620c530945878c851c8530a15811506348530c90735854010130c0c75989418c130c1475585418c130a28825946050430e10635446050430c1476545414c030d09545c8404c030d11545c4404c030c3076545414c030a448154d610cb20a1a83d506050720b048154c3250720d05535c43250720a1a839946050720a1683d516110320e11535854010220c31745c06154d208e1811c1640c920d07541c5530c920d04541c5530c920d07741c5530c920d04741c5530c920c45861c
  | 2 => 0xc5320c941981801c5320c941984874ca610c941a84814c9610c941984874c9610c941a858214d610c941a8583149610c941c87874c9610c941a84874c9610c941c84874c9610c941a86854c9610c941a84854c9610c941a87804c9610c941a8682d8e63d4541a8683d8a62d4541a87864c832d4541a91811c16314141aa1811c162141419188798d50141419188758d5014141d0873dc95014141d0b731c95014141d08731c95014141d0a631c95014141d09631c95014141928879895014141d08739895014141928875895014141d08735895014141e09635895014141c33765855014141d10735855014141e11635855014141d20725855014141e21625855014141991801c53250731c16735c46454331a28825806055231d05549c7520ca31925811d16014931c29745806014931c61715806014931a4685d88614c931991801c53250531d067314b6150531a4585989610c831b21801c55250431c0c76951524c431c0c76551524c431c0d7518b414c431c0f75189414c431e0585189414c431c8775189414c431e0775189414c431a8486949414c431e0462549414c431a8486549414c431b0686549414c431b0486549414c431e0486549414c431a8584d8c624c431948875493194031d80725053194031f01525053194031d04725053154031d0a541c93154031d09541c93154031948879493154031948875493154031d13755053154031d80725053154031f02525053154031f01525053154031b40815883254031d42725c43254031b11810c94154031d20725053154031d0872d053154031d40729053154031d08725053154031d40725053154031f03725053154031d10725053154031f00725053154031d00725053154031c46765c4534cb21c48535c0614cb21d04531c532507219a1801c53250721e0753589410c721a85868c9410c721e1353505600c721e8232505600c721c26725c46454321a18835806055221d05549c7530ca21c45769c7530ca21d05749c7530ca21a0d86d4c32d0621a0e86d4c3250621d07535c43250621a498014c624c621b118014d414c621e0453189414c621a8686cc9414c621915811d16014d21c19745806014d21c51715806014d21c48535c0614c921a4685d8c614c921d05725c45350521d04531c532505219a1801c53250521d04539cb6150521b06858c9418c521e06658c9418c5219c1801c5324c521e0453189414c521b04854c9414c521e04654c9414c521a4a858c9600c521c48625c06154c21a458598d610c821d04721c55350421b11801c55350421d05535c43250421b0585cc941cc421e0565cc941cc42184f87d97324c421c45655c4320c421e0553589410c421b05850c9410c421e05650c9410c421ac1810c9600c421e1153505600c421e8032505600c421a148654d414842
  | 3 => 0x180025a6502839a805a800090a838b7269a88d4062d527c369dc4c31c000140026400250288d6ac3240003681954c3b089b9c00d09ec12ce2698abbb809b1747fa7ee7ab8250de90294dc000e203cd9a520033c7d0006b96290a048787478048ab21a1020cdd1a4be2981b31000000003322318c0037a4aa9e9c8006e9660c28a8a3008eba2a1056e59ca039da758be3096c4f87ce4a12e1a96a0b900016e228860002697ba47794c069cc7ca4820858001e63b852180b8360003400000046002b6000000000000000da89c00132bc800000000000064000000f44686a0022ca40004b80000000b50000026862000001f6aaa62003188ca8c3380000356859c4001e2002d8020003924655800de176239141ea10ad0801900c0000000230df2e6ac800b2b4c8602e5011638136000006d800d69f01a340128f0000000003a001604b0c663b62282142f000003363e000c9800cc3943238c47244d48703aa34422084310e49800483482b85c52168742c4a9a2400256718c4019968828e6f142cba9c3ea0013a4e9538ae68e8bf2e82e8090040500c041d40a0000200001004020280d00800028200140003802000000200100000054000800902801010000340309c0e000000bc0110c0001c18018000a402008160940f01c000100800004008060040500c0b00000000050080e00026008050040004000014010000000c08064060000200c00000010000100000024080040a01401078180080000000020080300a0100202400018090600208c0001027000280381b020040e8180002402c00008000240800806004000380500c040280dd05545c4544c832d09545c0544c832c0d759d0614c832c0d755d0614c832c49759c0614c832c49755c0614c832c8a745c0614c832c89745c0614c8328c9801d93294432c85641c532944329c1801c532944329c1801c53254432951801c53254432961801c53254432949801c53254432b05841c53254432b41801c53254432946861c53254432c46861c53254432d06841c53254432d05841c53254432d42801c53254432945801c53254432d41801c53254432941801c53254432a85811913254032c16735c46454032c15735c46454032c26725c46454032c25725c46454032c31715c06454032e09644c95014032e41325855014032989801c5320cb41a84814c9610cb41e09635895014341e12635855014341e11635855014341e22625855014341e21625855014341c45651c5320ca419c1801c5320ca419c1801c5320c941a44854c9610c941ca3325c0614c941c92325c0614c941a1880594530c941a2880594520c941991801c5320c9419a1801c5320c941989801c5320c941b81801c5320c941c85861c5320c941986851c5320c941d06851c5320c941d82801c5320c941985801c5320c941d81801
  | 4 => 0xc692800000e3a745780001000b1922002aeb02ecdb904a68005f0000013c001442d8002aad0001b0001028f892d2a8616af0a8a6096000d80b2b8384132ea8f002661b48095229b2c5f80a00098b726a7222a750f63b3026a1e46e09082ba07e81661800003988d980a4a382d316b693a92842cd0ca062be97088c7b64c5346b8850c499aa8044351349c2fe7b8000cacc56b4e53b82ce2760705e682c2c28b0bea7a449d2d636cd7222dd82ac18d29e2d2c8af60791e5e9d8b7812440c00006ed10f20024c872e4081004e1fc001aac32a8d7a2e151461cb680f8005c3423f2f473b287a03856172ca800000787b010528a40b39c211a259266b20007aaa4678ac00000c8106610dc491f8648cc3f8966087edf9c26f99c89b3a199ac5733e5e150af076b590a6caba08800839
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x305d900547801c000802f34000000034000002400b000000300ac3852a7440c4c91134009c9ae00000250000c91424072c080100062c091f66a4500288c0282cb409b0c0078000000020002001860818102120c08500041e20591801c53294432c814230038a64a886590184600714c9510ca5032040a64b0865a0e10595801c5320ca41c40c350038a641928388186600714c8325063032043a6530864a0ca0640814c9610c941a044bac6b12a0282838088758d62540505068212eb1ac2a80a0a0f0058c725855014141a104bac4b0aa028283c00735896154050506a012ea928298ca018d4025e525053154031a804baa4a0a62a806390053600714c941c8680d2da9ae21928310d8064053189414c621c8029b0038a64a0a43900726007154d41087400c6c06a6a0a4210c81a5a8654d4148421a804baa6a0a43280435009794d4148550086a012ea9a8290aa010e04195819c23250530c02c330838aa619241841866007154c3248320308c00e2a986490608195819c33250520a024b2a6b8864a0a412059818c515052148220930baa64192838858024953505600c710902cc0c62928290e212049858d5250421c42c0126a9282b0043886041d8855cd414c110c403b104b9a829822188076a0b63505304431010c3928298a608870019472505314c110a204aac6b886490221820762157250520443100ec41ae4a0a40886201da83d894148110a404bac619282902216009558c32505204431010c39a8290a4088700194735052148110
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 42
  | 6 => 1947
  | 5 => 11355
  | 4 => 6826
  | 3 => 467
  | 2 => 53
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
  | 7 => packedAt gbK7 (756+((h/14+packedAt gbK7 (672+(h % 14)*6) 6) % 56)*7) 7
  | 6 => packedAt gbK6 (60357+((h/649+packedAt gbK6 (52569+(h % 649)*12) 12) % 2570)*12) 12
  | 5 => packedAt gbK5 (488265+((h/3785+packedAt gbK5 (431490+(h % 3785)*15) 15) % 18135)*15) 15
  | 4 => packedAt gbK4 (366324+((h/2275+packedAt gbK4 (334474+(h % 2275)*14) 14) % 9912)*14) 14
  | 3 => packedAt gbK3 (29570+((h/155+packedAt gbK3 (28020+(h % 155)*10) 10) % 561)*10) 10
  | 2 => packedAt gbK2 (3882+((h/17+packedAt gbK2 (3763+(h % 17)*7) 7) % 84)*7) 7
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xff87fffc0ff1f1c3e38fc7fff1f8383c19f793
  | 1 => 0x7f83e3ff1fffffc03f1f8e07e3ffffc6648ff
  | 2 => 0x7ffc03ffe01fe3ffc01ff007fc03fc3878f1c
  | 3 => 0xf800003ffffe003ffffe00007fffc003f80fe0
  | 4 => 0xffffffc00000003fffffffff80000003fff000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x10908c04602222006082412330488898089391
  | 1 => 0x41020048808080080110884402121220224026
  | 2 => 0xb231149124654055a401520954812589858d18
  | 3 => 0x2065a922494064a6caa4001269258112d80ec0
  | 4 => 0xc44630038d89893b1349a49c00060623776000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 31 gbPos gbNeg, 0xfeeaecc8feeaecc8feeaecc8feeaecc8feeaecc8feeaecc8feeaecc8feeaecc8feeaecc8feeaecc8feeaecc8feeaecc8feeaecc8feeaecc8feeaecc8feeaecc8, gbN, gbR, (fun _ _ => 0), gbI⟩
end PEqualNP.Outside.L_meta_12917
namespace PEqualNP.Outside.L_meta_12917
open PEqualNP.Outside.L_meta_12917.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 53 := block_range (n:=53) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 53 := bgb_2_0
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
theorem bgb_3_384 : Interval gbAtlas 3 384 83 := block_range (n:=83) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 467 := (concat (concat bgb_3_0 bgb_3_96) (concat bgb_3_192 (concat bgb_3_288 bgb_3_384)))
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
theorem bgb_4_6816 : Interval gbAtlas 4 6816 10 := block_range (n:=10) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 6826 := (concat (concat (concat (concat (concat (concat bgb_4_0 bgb_4_96) (concat bgb_4_192 bgb_4_288)) (concat (concat bgb_4_384 bgb_4_480) (concat bgb_4_576 (concat bgb_4_672 bgb_4_768)))) (concat (concat (concat bgb_4_864 bgb_4_960) (concat bgb_4_1056 bgb_4_1152)) (concat (concat bgb_4_1248 bgb_4_1344) (concat bgb_4_1440 (concat bgb_4_1536 bgb_4_1632))))) (concat (concat (concat (concat bgb_4_1728 bgb_4_1824) (concat bgb_4_1920 bgb_4_2016)) (concat (concat bgb_4_2112 bgb_4_2208) (concat bgb_4_2304 (concat bgb_4_2400 bgb_4_2496)))) (concat (concat (concat bgb_4_2592 bgb_4_2688) (concat bgb_4_2784 bgb_4_2880)) (concat (concat bgb_4_2976 bgb_4_3072) (concat bgb_4_3168 (concat bgb_4_3264 bgb_4_3360)))))) (concat (concat (concat (concat (concat bgb_4_3456 bgb_4_3552) (concat bgb_4_3648 bgb_4_3744)) (concat (concat bgb_4_3840 bgb_4_3936) (concat bgb_4_4032 (concat bgb_4_4128 bgb_4_4224)))) (concat (concat (concat bgb_4_4320 bgb_4_4416) (concat bgb_4_4512 bgb_4_4608)) (concat (concat bgb_4_4704 bgb_4_4800) (concat bgb_4_4896 (concat bgb_4_4992 bgb_4_5088))))) (concat (concat (concat (concat bgb_4_5184 bgb_4_5280) (concat bgb_4_5376 bgb_4_5472)) (concat (concat bgb_4_5568 bgb_4_5664) (concat bgb_4_5760 (concat bgb_4_5856 bgb_4_5952)))) (concat (concat (concat bgb_4_6048 bgb_4_6144) (concat bgb_4_6240 bgb_4_6336)) (concat (concat bgb_4_6432 bgb_4_6528) (concat bgb_4_6624 (concat bgb_4_6720 bgb_4_6816)))))))
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
theorem bgb_5_11040 : Interval gbAtlas 5 11040 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_11136 : Interval gbAtlas 5 11136 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_11232 : Interval gbAtlas 5 11232 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_11328 : Interval gbAtlas 5 11328 27 := block_range (n:=27) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 11355 := (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_96 bgb_5_192)) (concat (concat bgb_5_288 bgb_5_384) (concat bgb_5_480 bgb_5_576))) (concat (concat bgb_5_672 (concat bgb_5_768 bgb_5_864)) (concat (concat bgb_5_960 bgb_5_1056) (concat bgb_5_1152 bgb_5_1248)))) (concat (concat (concat bgb_5_1344 (concat bgb_5_1440 bgb_5_1536)) (concat (concat bgb_5_1632 bgb_5_1728) (concat bgb_5_1824 bgb_5_1920))) (concat (concat (concat bgb_5_2016 bgb_5_2112) (concat bgb_5_2208 bgb_5_2304)) (concat (concat bgb_5_2400 bgb_5_2496) (concat bgb_5_2592 bgb_5_2688))))) (concat (concat (concat (concat bgb_5_2784 (concat bgb_5_2880 bgb_5_2976)) (concat (concat bgb_5_3072 bgb_5_3168) (concat bgb_5_3264 bgb_5_3360))) (concat (concat (concat bgb_5_3456 bgb_5_3552) (concat bgb_5_3648 bgb_5_3744)) (concat (concat bgb_5_3840 bgb_5_3936) (concat bgb_5_4032 bgb_5_4128)))) (concat (concat (concat bgb_5_4224 (concat bgb_5_4320 bgb_5_4416)) (concat (concat bgb_5_4512 bgb_5_4608) (concat bgb_5_4704 bgb_5_4800))) (concat (concat (concat bgb_5_4896 bgb_5_4992) (concat bgb_5_5088 bgb_5_5184)) (concat (concat bgb_5_5280 bgb_5_5376) (concat bgb_5_5472 bgb_5_5568)))))) (concat (concat (concat (concat (concat bgb_5_5664 (concat bgb_5_5760 bgb_5_5856)) (concat (concat bgb_5_5952 bgb_5_6048) (concat bgb_5_6144 bgb_5_6240))) (concat (concat (concat bgb_5_6336 bgb_5_6432) (concat bgb_5_6528 bgb_5_6624)) (concat (concat bgb_5_6720 bgb_5_6816) (concat bgb_5_6912 bgb_5_7008)))) (concat (concat (concat bgb_5_7104 (concat bgb_5_7200 bgb_5_7296)) (concat (concat bgb_5_7392 bgb_5_7488) (concat bgb_5_7584 bgb_5_7680))) (concat (concat (concat bgb_5_7776 bgb_5_7872) (concat bgb_5_7968 bgb_5_8064)) (concat (concat bgb_5_8160 bgb_5_8256) (concat bgb_5_8352 bgb_5_8448))))) (concat (concat (concat (concat bgb_5_8544 (concat bgb_5_8640 bgb_5_8736)) (concat (concat bgb_5_8832 bgb_5_8928) (concat bgb_5_9024 bgb_5_9120))) (concat (concat (concat bgb_5_9216 bgb_5_9312) (concat bgb_5_9408 bgb_5_9504)) (concat (concat bgb_5_9600 bgb_5_9696) (concat bgb_5_9792 bgb_5_9888)))) (concat (concat (concat bgb_5_9984 (concat bgb_5_10080 bgb_5_10176)) (concat (concat bgb_5_10272 bgb_5_10368) (concat bgb_5_10464 bgb_5_10560))) (concat (concat (concat bgb_5_10656 bgb_5_10752) (concat bgb_5_10848 bgb_5_10944)) (concat (concat bgb_5_11040 bgb_5_11136) (concat bgb_5_11232 bgb_5_11328)))))))
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
theorem bgb_6_1824 : Interval gbAtlas 6 1824 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_1920 : Interval gbAtlas 6 1920 27 := block_range (n:=27) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1947 := (concat (concat (concat (concat bgb_6_0 bgb_6_96) (concat bgb_6_192 (concat bgb_6_288 bgb_6_384))) (concat (concat bgb_6_480 bgb_6_576) (concat bgb_6_672 (concat bgb_6_768 bgb_6_864)))) (concat (concat (concat bgb_6_960 bgb_6_1056) (concat bgb_6_1152 (concat bgb_6_1248 bgb_6_1344))) (concat (concat bgb_6_1440 (concat bgb_6_1536 bgb_6_1632)) (concat bgb_6_1728 (concat bgb_6_1824 bgb_6_1920)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 42 := block_range (n:=42) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 42 := bgb_7_0
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 5 zero,inputs.getD 4 zero]
def fullWord : Sig := 0xfeeafeeafeeaecc8feeafeeafeeaecc8feeafeeafeeaecc8feeafeeafeeaecc8feeafeeafeeaecc8feeafeeafeeaecc8feeafeeafeeaecc8feeafeeafeeaecc8
theorem fullBound (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have low := boundgb certgb
  have lift := lift_ok (u:=true) (ms:=fixRows 32 0) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 5 zero,1,33)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 5 zero,1,33)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4276813546 * 2 ^ 32 + 4276808904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_12917.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,2]⟩,⟨.or,[3,6]⟩,⟨.or,[4,5]⟩,⟨.and,[0,8]⟩,⟨.or,[0,8]⟩,⟨.and,[3,10]⟩,⟨.and,[2,11]⟩,⟨.or,[1,9]⟩,⟨.or,[9,13]⟩,⟨.or,[12,14]⟩,⟨.and,[7,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813546 * 2 ^ 32 + 4276808904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813546 * 2 ^ 32 + 4276808904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_12917

open PEqualNP.Outside.L_meta_12917 in
theorem PEqualNP.Outside.L_meta_12917 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813546 * 2 ^ 32 + 4276808904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813546 * 2 ^ 32 + 4276808904) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound allgb)
