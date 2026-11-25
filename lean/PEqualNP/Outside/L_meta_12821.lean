import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_12821.Model
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


end PEqualNP.Outside.L_meta_12821.Model

namespace PEqualNP.Outside.L_meta_12821
open PEqualNP.Outside.L_meta_12821.Model
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

def mirrorSteps : List Move := [swapRows 50]

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

end PEqualNP.Outside.L_meta_12821

namespace PEqualNP.Outside.L_meta_12821
open PEqualNP.Outside.L_meta_12821.Model
def gbK8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x600039c29fb80000a9d02c89b0337a4a00404c2f08d4b2b750313e620b25483461a64c58800e080041040210223ff42fe42fd42fc42fe32fd32fc32ff41fe41fd41fc41ff21fe21fd21fc21ff40fe40fd40fc40ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x241fc32483fea2905fd4520fba8a417751483fca2907f54520fe28a417c51483e8a2905d14520ffa0a41fe41483fa82907f10520ff98a41fe31483fa62907f0c520ff90a41ef21483fc42907f48520f690a41fc21483fe80907f90120fea0241fc40483fe60907f8c120fe98241ff20483f640907f88120f710241ff54082fea8107f95020bf2a041fd54082faa8107f15020be2a041ff53082fea6107f94c20bf29841fd53082faa6107f14c20be29841ff43083fc86107f50c20fe218417e52083fe84107bd0820ff21041fd42083f884107b10820ff99041ef32083fc64107f4c820fe19041ec32083fea2107f94420bf28841fd51082faa2107f14420ffa0841fe41083fa82107f10420ff98841fe31083fa62107f0c420ff90841fe21083dc42107f48420fe10841ec21082fca0107fd0020ff20041fd40083f880107fcc020ff18041fd30083f860107fc8020f790041fe20083f440107f48020f690041f920083fea9885fd5310ff2a6217e54c43faa9885f55310fe2a6217c54c43fea5885fd4b10ff296217e52c43faa5885f54b10fe296217c52c43fe85887f90b10fea1621fc42c43fc65887f4cb10fe19621ff41c43fc83887f50710fe20e21ff21c43fc43887f48710fe10e21ff40c43fc81887f50310fe20621ff20c43fc41887f48310fe10621ff54842fea9087f95210bf2a421fd54842faa9087f15210be2a421ff52842fea5087f94a10bf29421fd52842faa5087f14a10be29421ff42843fc85087f50a10fe21421fe32843fa65087f0ca10bea8c21ff41843ee83087f90610fea0c21fc41843e883087fc8610fb90c21fe21843fa43087f08610fa10c217e50843fe81087f90210fea0421fc40843fe41087f88210fe90421fc20843fe21087dc4210fd88421ff54442fea8886fd51109faa221fe54442fca8887f55110beaa221fc54442f8a8886f151109e2a221ff52442fea4887bd4910b7a9221fe52442fca4887f54910bea9221fc52442f8a4887b14910b629221ff42443fc84887f50910fe21221fe32443fa64887f0c910ffa0a21fe41443fa82887f10510ff90a21fe21443fa42887f08510ffa0221fe40443fa80887f10110ff90221fe20443fa40887f08110ff88221fb10443fc20887d84110ffaa0217f54043fca8085f95010df2a0213e54043faa8085f55010deaa0213d54043f8a8085f15010ffa90217f52043fca4085f94810f7290216e52043faa4085f54810f6a90216d52043f8a4085f14810ffa1021fe42043fa84087f10810ff19021fd32043f864085f94410ffa0821f741043fc82087f50410fe20821f441043fe42087dc8410ff10821fd21043f842087d08410bf28021ff40043fc80087f50010fe20021ff20043fc40087f48010fe10021ff10043ee20087f84010fd08021fd10043ea20087e44010
  | 1 => 0xd21087da4210fd48421ffa8043fe50086fca010ff54021bea8043fc50087fea5a07f94b40bf29681fd52d02faa5a07f14b40ffa1681fe42d03fa85a07f10b40ff19681fd32d03f865a07fd4740ff28e817e51d03faa3a05f54740fe28e81ff41d037e83a07f90740fea0e81bd41d03f883a07fc8740ff10e81fd21d03f843a05f55240ffa9481fe52902fca5207f54a40bea9481fc52903fe85207f90a40df21481fd42903f885206f10a40ff19481fd32903f865207fd4640ff28c817e51903faa3205f54640fe28c81ff41903fc83206f90640fea0c81fc419037883207fc8640ff10c81fd21903f843205f94240ffa0481bf40903f681207fd4940bfa9281ef52502dea4a07f94940fea9281fc52502f8a4a07b14940b629281ff42503fc84a07f50940fe21281fe32503fa64a07f0c940ffa8a817f51503eea2a05dd4540ff28a81fd51503f8a2a05f14540fa28a817451503fe82a06fd0540ff20a81fd415037a82a07f10540ff90a81fe21503fa42a07f08540ffa0281fb40503fc80a06f90140bf2a081ff52103fca4205f94840fea90817d52103f8a4207fd0840ff21081be42103fa84207f10840de21081fe32103fa64207f0c840ffa8881fe51102fca2207f54440bea8881fc51103fe82207f90440df20881fd41103f882206f10440ff90881fe21103fa42207f08440bf28081ff401037e80207f90040fd20081fd401037a80207e50040ffaa6417f54c83fca9905f95320feaa6417d54c83f8a9905f15320ffa9e41fe53c82fca7907f54f20bea9e41fc53c82f8a7907fd0f20ff21e41fd43c83f887907fd0b20ff21641fd42c83f885907fccb20ff19641fd32c83f865907fd4720ff28e417e51c83faa3905f54720fe28e41ff41c83fc83907f50720fe20e41ff31c83fc63907f4c720fe18e41ff21c83de43907f88720fe90e41ed21c83f843907fd0320ff20641fd40c83f881907fcc320ffaa4417f54883fca9105f95220feaa4417d54883f8a9105f15220ffa9c417f53883fca7105f94e20fea9c417d53883f8a7107fd0e20ff21c41fd43883f887105f54a20ffa1441ef42883fc85107f50a20fe21441ec42883fe65107bcca20ff19441fd32883f865107b0ca20ffa8c41fe51882fca3107f54620bea8c41fc51883fe83107f90620fea0c41fc41883fe63107f8c620fe98c41fc31883fe43107f88620f710c41fd21883f843107b08620bf28441ff40883fc81107f50220fe20441ff30883fc61107fc8220f790441fb20883fea8905fd5120dfaa2413f54483fca8905f95120feaa2417d54483f8a8905f15120de2a2413c54483fea6905fd4d20efa9a415f53483fca6905f94d20fea9a417d53483f8a6905f14d20ee29a415c53483fe86907f90d20fea1a41fc43483fe84907f90920fea1241fc42483fe64907f8c920fe99
  | 2 => 0xcbdc64197f4c832f699065cd320cbfea2197f94432bf28865fd510cafaa2197f14432ffa8065fe500cafca0197f54032bea8065fc500cbfea5a0ff94b41bf29683fd52d06faa5a0ff14b41ffa1683fe42d077c85a0ff50b41fe21683bc42d07fc65a0ff4cb41fe19683ff50d07fca1a0df94341fea86837d50d07f8a1a0df55241ffa9483fe52906fca520fb94a41b729483fd52906faa520fb54a41b6a9483fc52907fe8520ff90a41fea1483fc42907fc6520ff4ca41fe194837e51907fe8320efd0641fba0c83ff50907fca120df94241fea84837d50907f8a120ffd4941bfa9283fe52507faa4a0ff14941be29283ff42507fc84a0ef90941fea1283fc425077884a0ff8c941fe99283fc32507fe82a0fdd0541ff20a83be41507fea0a0dfd4141ff28283fd50507f8a0a0df14141bf2a083ff52107fca420df94841fea90837d52107f8a420ffd0841ff21083fd42107f88420ff8c841fe99083fc32106fca220ffd0441dfa0883fe41107ec8220ff50441dea0883f541107fea020ff94041bf28083fd50106faa020ff14041ffaa6437f54c87fca990df95321feaa6437d54c87f8a990df15321ffa9e43fe53c86fca790ff54f21bea9e43fc53c86f8a790ffd0f21ff21e43fd43c87f88790ffd0b21f7a1643fe42c87fa8590ff10b21f621643ff32c87de6590ff8cb21fe99643fc32c87d86590ffd0721ff20e43fd41c87f88390ffcc721ffa8643fe50c86fca190ff54321bea8643fc50c87fea910dfd5221ff2a4437e548877ca910cf95221feaa4437d548877aa910cf55221fe2a4437c54887fea710dfd4e21ff29c437e53887bca710d794e21fea9c437d53887baa710d754e21fe29c43ff43887fc8710ff50e21fe21c437d52887fe8510ff90a21fea1443fc42887fe6510ff8ca21fe99443fc32886fca310ffd0621ff20c43fd41887f88310ffcc621ff18c43ff21887de4310fdc8621ffa8443fe50886fca110ff54221bea8443fc50887fea890dfd5121ff2a2437e54487faa890df55121fe2a2437c54487fea690dfd4d21ff29a437e53487faa690df54d21fe29a437c53487fe8690ff90d21fea1a43fc43487fe8490fbd0921ff21243fd42487f88490fb10921ff99243ef32487fc6490ff4c921fe19243ec32487fe8290ff90521fea0a43fc41487fe6290ff8c521fe98a43ff21487ee4290ff88521f710a43ff50486fea090ff94121fea8243fc50486f8a090ffd5021bfaa043fe54086fca810ff55021beaa043fc54086f8a810ffd4c21bfa9843fe53086fca610ff54c21bea9843fc53086f8a610ffd0c21ff21843fd43087f88610df94821ffa1043fe42087fa8410ff10821ff99043fe32087fa6410ff0c821bf28843ff41087fc8210ff50421fe20843ff31087fc6210ff4c421fe18843ff21087de4210ff88421fb10843f
  | 3 => 0x800000000800400000c02c00000000000000000004400000000403002400800c00400400400000001800c00002c00001400800400400401000c02400000401001000c00402400000000001800000000000801c00004003000000000000400400001000400c04000000000802c01000801402c01000000401400400400800401400401000000402000000800003400800801400000000000000000000801800000400400000c01000000400001000001c00400c01c00c01400000000802801800000400000400001800000400400002000c01001000402800c00000000804000803800800000801401400401401c01400400000002401802001001802801001000000000000400001800400800000002002400401800800000400800000000800003401000801800400002400001c00001c02800800800000801400001000807800402401004800800400000401400c00800403c01000000c00001c00800401400c00400400c00000000001000400c02000800800000000c000004000000008000020008013fea7a17f94f42bf29e85fd53d0afaa7a17f14f42ffa1e85ff51d0bfca3a15f94742fea8e857d51d0bf8a3a17fd4342ff286857e50d0bfaa1a15f54342fe286857d5490bfea7217f94e42bf29c85fd5390afaa7217f14e42ffa1c85fe4390b7c87215f94a42ffa1485bf4290bde85217fd4642ff28c857e5190bfaa3215f54642fe28c85ff5090bfca1215f94242fea84857d5090bf8a1217fd4d42bfa9a85df5350abea6a17f94d42fea9a85fc5350af8a6a17714d42ae29a85ff4350bfc86a17f50d42ffa1285ef4250bfc84a16f90942ffa8a857f5150bfca2a17f54542fe28a857c5150bfea0a15fd4142ff28285fd5050bf8a0a15f14142bf2a085ff5310bfca6215f94c42fea98857d5310bf8a6217fd0c42ff21885be4310bfa86217f10c42de218857e5210bfe84216fd0842ff21085ee4210bfa84216f50842f6a1085ad4210bfea2217f94442bf28885fd5110afaa2217f14442ffa8085fe5010afca0217f54042bea8085fc5010bfea9195fd5232ff2a4657e548cbfaa9195f55232fe2a4657c548cafaa7197fd0e32efa1c65fe438cbfa87197f10e32ee21c657e528cbfe85197f90a32fea1465fc428cbfe65197bcca32ffa8c65fe518cafca3197f54632bea8c65fc518cbfea1197f94232bf28465fd508cafaa1197f14232ffaa2657f544cb7ea8994fd5132ff2a2657e544cbfaa8995f55132fe2a2657c544cb78a8994f15132ffa1265fe424cbfa84997f10932ff19265de324cbfea2995fd4532ff28a65fd514cbf8a2995f14532ffa82657f504cbfca0997f54132fe282657c504cbfea8195fd5032ff2a0657e540cbfaa8195f55032fe2a0657c540cafca4197fd0832f7a1065fe420cbfa84197f10832f621065fe320
  | 4 => 0x1640000760000c100000000000005b4338001669d012212f0b88244000001a800000021280000000000014e5f413a9c6d47a248a111dc001be17b5238000890001db00021e0000b31a10348730258001d7d918970000a60000000001fe8000001f380000002781904e8001a300007e8000000468000941a00765b402943800000003600009e80021b8000115fe2168900001a64c42130000000000b28001624054000000948000000000000bb8a50001b90000000c280000691780000016440000000015c0388bda100b3d1900000006a84200011b48f8250090b98000135af97012a51bc000104001fb4991b3521800000000000000039de44001275b1000000128da18ca47c00009a80011000000000000000009804ad390be00000000012a0001a4d0b892032016d618000aa8000000000000000000000000000000a080020100011d00000022200006e80000003a80000012650cdcf1eb40000000003b88805392c9488638749838bc1df9348000931e007d0001dd0cf42c449d325db8000000001bb4000000000000d14cc80008e50e0000000000668254000000f600000000000011102f59889980004a00000000019f94900013d800000115c0020f80000018295f0c300000000000000014c8000028110000000000000c08001b9d4f8000000000001a440003b04096aa0e82f9ed0801ed80016d8440f14cec000000000000000f80000000000001bcc000000000000000000ca9d38b910d80300000017c80000000000c9cc80017380000019800018983fc4100000014816f1270000000001868000a916980000440013f9e10efc978000a300000002ac00000212000000000129000021d0e8000000001c7c17c4055600013bc000000b70000e60530dd886823136000000000000000000120045800000000400400401400800000800800000401000c02000401000400002802c00001401c00002c00003000401001000000400000001001000801400000c00400000000000000800000001c01800401000000800c01c00001800400000800000000c04801401000c00000001000400c00400800400000802403c01400001401801401400400000401402c01000c04c00000000002400001400001000003400004800000401c00c00804800c00400001000000000000400000000800400000001400400400000001400401800000c00002c00000000000800800400001800000400801400000000000800400002000401000400405000800000400000800400000c07400000400001000000c00803400001400000c00400001001c01002000000400400006000c00401002400803400402800003c00000001c00000c01c00000801000400000000000c01400000809c00400c00000800800000000000c00000000401800000000800400800401
  | 5 => 0x15992c08082e80000006ec0000018448c8000000002051a61de1ce8001b29f89a080002cd635468f08b35f117f4000958000000210001c88000000001074002160159e51fd9120c20000000001b3c000021028000000601f09cb8001ff9d99e68000000000d500000009da08c000001ca800000195119c0019900000002081c8969551a5dfd07993c9410b20beca007800002b80000000000000010580019a8000002058081bd4c043dc59c7a000187154542000109c000001add834000000bac3c8129b24000002179f680008f04f8000000ee80008207100010861b1c10089c610800003f9ce0000e203e61e8126079a2d0b14c4e18545fc8671e598d1e20429e18d057107cc001f49140002210000001a70a495a618815c0010f99385ad4295b196c5b9aec400001cb0001be40016f8000000000001880000001b0c0014b9574001e38430301dc0bf5a144fc139045070d90714bf9bac4540011c80000000018c80000017dcab000080c000000690000000661d607400000021a0000000ac97e800047d5c8618000a980000013180000001d09c0f8c001d7a1a84c000107c000888af0001c09ea8ce106dd58001b94be940cd280000003f00008a0000000001054000001780001310000f0da3c0000018a88c0da16c80013501e0d196080000000000009b1c8c000000000695378b94688000000000728685ec00012f8084758b68001728001ec8b81bd0c780021d00005bd2e8070000000e6d6e0001955bec0014dc1e80001784d21d8000001a881a9a280000000a0e10a89d68000700000000f24000000000000e1576408c169ca53000000d0000000000b600021380004a80000000014b43f544000056018868c0004e0811fa875c000000000000001dc80000a86f80020ca1080000019640019d800078814cbc80000002ca0940d9ba8000000f54ad8bb10680fda5090c001e895351cc001b1c0007a8ff07042400000000001b0768bd000000000000000000144800000154c0009a09f0000000000000000000508000495f01fc0001aa11e1b00b40a554fc000000d200000000000000012100180000022184793280980008853e8678fb07be0d125dea0501ef8d000005b13340009100000000000000080015d95680007d559000046c0020800013540000000003ae0a800077c8780000000000018e00001487903110780000000000000003c000000000000000000000117c0000000000017c11d8010e48c457f03e953d1395d1750ac0fc00000006121c800000045d600aa185000030c7f80021c0001b8d8f0e9000000209132c0000000000000000019f00000014f1769280f521988980015880016b809db491647c58853b8c688712e12860b0001791ee95a98d8238cddee1611d6c000000000000000001900000000000000000000ab90c8
  | 6 => 0x1f802bc0000000009386e61497ec630f1d6b400166d7d8828c8dc19c95d282144d8c38d4da59b212300000002edd885a1b81064e41ae00007e0000001d5d09010c0000000000000011498e80000000000000380000000001ba140e6995c9c4f040002a0000fd00000014d8a40cfced0001d108500000001f0001c85ff00005680010f11b00956580000000000014599a0f485c048c0006285cdf61e31eb0ba508d4b1a91eb85044f0d385ed26c11cfe16a5fb9e2891594c0015e80004186a0000000001c5d6d0000d8da240010e529c00000217c84d048da4a3803c5f0000da91991691d54a9128000d79e914700000000005d80000006e0000d64001189509c4000000000000000000129927c288e59fa11596e83a1a49830001afc521528000001730001a0c000fb86d86a51a4511691fc4001ba54e8000d08000000000000000000ff9e8000089cec0000718001008ec8000f193414ad840398acd65c88c000f407784b5c79c92240000000ba15580017700000000020894cc8d0000b1c0022380000000016a0d95bbd05dd51c98000164a80001089171019958c70518f29ab8ea1c68000000c58579908001d180006fd8900000006d0ae95104a4000dc0000000000000001c3889400071caf8001fac000c900005d40000000009755b80000014a583c000000000558000198d319100008b00005e80000002d1229f79d40000f3c0c0000b59b180014d42a55716b1a20a78000001a40906158dd1d76018eb88415e1c9de61f906f4000201b30000000554d557bdae91180000012d00010a0e31ef1ad0590000001240001151020001288c8824d2a80000000006087545a8000d480019d013c2dc8317594e02b40e09b4049bc40005891f86f0bfdd64819928001ac8000000000001ee4fa09cd3e00005c4000000204cf80006200000018b0000001b605e498c001345000000041f3218000050c0000000019e0f2e068a64d40f9c000001f58000000175b70b44ee2231c594f4002191208000f34ad0001f28002071038e38cf0b517b2228a285d0000000000001010fa9b50d69e98000db80019e993059905129400198ce89ad83151c0b11031a04d808aa0c0738000000001a79d900020994007747b0d580000009bc001461d483680000000000000000007c80000000010608e0b09b140011743d8680e7cf00ac4002208000499740dc869a200c617d4b48001d710a4001538001630340000ba8ab5c80000658000000000f206c1a550d48d9450ef00000002fd85998481c0010c1ca07b83e17ad098000918000351041a69e70d71c7149918c581ac09899480004920a1c200000000013080002d98f80000000000019c869c268b019608b970800000000097d5489e0328abd1a9ab1940000000000000000000002110750b8c00000182d2b05e00000
  | 7 => 0x1cf829c000001fb0f3a0d8000249bdc0008ac471810000001dd81517f853da1c000001bb006007934c451a987f1e7d1607092ad3380518191316c1b390dde95b2cb78000000000000001b080005514a01c0000001cc00014bc000000001e9df980015817b8001d080000000000000017200003a45708fc001aa8001e4133012058cbf1bf15a00018b8001a35969380000f792b9acd9960e0651e79681b680b0058ca0f1091c00000000000000139870cf4c000c500e9c004609ba118001778b19648001370000f840000018a13d0000000001af4000000640cd8378548001f20f30a701549f8488858001638c01bc80a40b8001195b595b4e991a0000000f980008e91846b0b160402a8e50c9c8f4cd1af067dd31541408fc8000000130001248001e08a05034d100009c8000000000000000ce4d610a80ac000000000001418000486031c30e656ac1010d02e53881f97147d86753642711e8cb116c30800044800011a0f0eb00021500000000000000f94300000000003d000153020ce79a39bf99b1860f90000f44df8000e297d133cea8e08848000cc11ac001da000000054cef51e4001b7a02163c000c74000001d540011b98c0a21260001c74000000000000000001c497a804d1f17480000000000012780020380014d00019b8de8c18000001920f58001259798ed93ac0000019440002280000001700013680016501a01097a0e7021812d3c5c2a0600005c8001f503700020ba1700000018004b137c0001600000000000000017c4d9d7613fcad5c5000197de86029b99978ce9fbc181820f95180a195793a1bb8b380016285f8001de9df17e1d20e80001b88304a682205a44641455f9519998c49269d81ea5501ae4514000000000001cadcd9e48390280d0c358528fd80016209080018480015200000011080000000002e0b2db041d83ec5413b600143c261672048e743310948a4ef80f05957ccb4ca594c19719744b8481688000001ad4fe8df0000475654770000e01789809da93596608ec0002f00000000000000000007208618b5f193b21f8000000001439ba02d439400095000000025e1f104c000d9800162cc95e8cdb1bd86b8298140ae1be98886c8de1250b24000c8000187831800000092a008f689d00019c02b0f70838439bc0001320c98de42904c8b84648960f8800000136c0000000000000005dd03dcd0cb800169c0016793f12d93c00002c1f70001718000d8800000
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x2210433e5488410cf55221042de6388410b758e210435e5388410d754e210436e5288410db54a21042f66188410be98221042f960884109fd95210433e5448410cf551210435e5348410d754d210436e5248410db549210427f65084109f594210433e5408410cf550210435e5308410d754c210436e5208410db54821043e52108410be98021042f96008410dd59421042756508410bd99021042f46408410ed95021043b55408410bd98c21042f46308410f594c21043d55308410bd98821043e66208410ddd4821043e65208410dd54821043e55208410fc98021042f56008410fc580210427e64940109f592500427e62940109f58a500427d6194010ddd0650043744194010ddc86500437421940109f597400433e54d0010cf553400436e52d0010db54b40043b741d00109fd96400427d6590010cf952400433d5490010db94a400436d5290010bd98640042f56190010ed106400427f6550010cf951400433d5450010bbd8940042ec6250010db949400436d5250010bdd8540042f46150010edd05400427f65100109f994400427d65100109f194400433e5410010cf550400436e5210010db54840042f66110010bd58440043b441100109f597200433e54c8010cf553200435e53c8010d754f200436e52c8010db54b20043e721c80109fd96200427d6588010cf952200433d5488010d794e200435d5388010db94a200436d5288010bd98620042f56188010f9086200427f6548010afd9120042bc6448010cf951200433d5448010b7d8d20042dc6348010d794d200435d5348010db949200436d5248010bdd8520042f46148010f9c85200427f65080109f994200427d65080109f194200433e5408010cf550200435e5308010d754c200436e5208010db54820042f66108010bd58420043e42108010cf953100433d54c4010db94b100436d52c4010dd59710042f664c4010bd19310043b654c4010ed55310042f662c4010bd18b10043e652c4010f954b100433e5484010cf552100436e5284010db54a10042f56184010dd94610042f96584010de59610042796584010ee95210043b95484010fa94a10043e95284010be586100437a5184010fc94610043f34184010fc10610043f32184010fc086100427f6544010afd9110042bc6444010cf951100433d5444010bbd8910042ec6244010db949100436d5244010bdd95100437765440109dd9510043b76444010bd99110042f46444010ed19110042b46444010ed95110043b55444010f9d8910042f66244010bd18910043e46244010b918910043e65244010f954910042f76044010dd94110042fb6544010ded95100427b6544010eed9110043b86444010ee95110043b95444010fad8910043e86244010fa94910043e95244010bed8510043f36144010de94510043f25144010
  | 1 => 0x436e6354810db58d520436c6354810db985520436c6154810d9185520436e6054810db181520436c1054810af99052042bd6414810cf950520433d5414810b798c52042dd6314810d794c520435d5314810bb988520436d52148109f990520433e64148108f990520427d6414810cf590520423d64148109f98c520435e63148109798c520427d6314810d758c520425d63148109f988520436e62148109b988520427e6114810dd984520427e6014810de980520427f65d08109f997420427d65d08109f197420433e54d0810cf553420435e53d0810d754f420436e52d0810db54b42042f661d0810bd587420427f65908109f996420427d65908109f196420433e5490810cf552420435e5390810d754e420436e5290810db54a42042f66190810bd586420427f65508109f995420427d65508109f195420433e5450810cf55142042df6350810b718d420435e5350810d754d420436e5250810db54942042f76150810bd18542042fb6050810be181420427f65108109f994420427d65108109f194420433e5410810cf550420435e5310810d754c420436e5210810db54842043ad42108109fd96320427e658c8109f596320427c658c810cf952320433d548c810d794e320435d538c810db94a320436d528c810bd98632042f5618c8109fd95320427e654c8109f595320427c654c810afd9132042bc644c810cf951320433d544c810db949320436d524c810bdd8532042f4614c810bed8132042f8604c8109fd94320427e650c8109f594320427c650c810cf950320433d540c810db948320436d520c810f34c8320427e64944109f592510427e62944109f58a510427d65d0410cf953410433d54d0410db94b410436d52d0410bd597410437565d0410ddd5341043b654d0410dd55341043b554d0410cd55341042f662d0410f994b41043e552d0410ed90b41043b442d0410bd583410427f65904109f596410433e5490410cf55241042ee6290410bb58a410436e5290410db54a41042f66190410be98241042f960904109fd95410433e5450410cf551410436e5250410db549410427f65104109f594410433e5410410cf550410436e5210410db54841043b54110410be98041042f96010410dd59441042756510410bd99041043b66410410ddd5041043b65410410dd55041043b55410410bd98841043e65210410f954841043f26010410bd58041043f160104109f597210433e54c8410cf553210435e53c8410d754f210436e52c8410db54b21042f565c8410dd59721042f664c8410bd19321043b654c8410ed55321042f663c8410bd18f21043d653c8410f554f210437752c8410f994b210437552c8410f954b210436552c8410f9d0b21043e442c8410f9ccb21043e432c8410bd583210427f65884109f59621042be6488410af59
  | 2 => 0x52101109f997204433f54c8110cf153204435f53c8110d714f204436f52c8110db14b20442f661c8110bd587204427e6588110cfd52204433c5488110d7d4e204435c5388110dbd4a204436c52881109fd95204427d65481109f19520442bf6448110af191204433f5448110cf15120442df6348110b718d204435f5348110d714d204436f5248110db14920442f76148110bd185204427e6508110cfd50204433c5408110d7d4c204435c5308110dbd48204436c5208110cfd53104433c54c4110dbd4b104436c52c4110eed5310443b854c4110fad4b10443e852c4110cfd52104433c5484110dbd4a104436c5284110edd5210443765484110dd15210443b45484110cd15210443e75284110dd94a10443745284110f914a10443645284110fcd4210442ee62d5010bb58b540427e62d5010db98b540426e62d50109f58b540436d62d50109b58b540427e61d5010dd987540427e60d5010de983540427d6595010cfd52540427e62950109f58a540423d6595010ed186540433f6295010cf98a540433d6295010cf18a540433e6195010cf186540433e6095010cf182540433f64550109fd89540427c62550109fd85540427d6155010dd185540427f60550109f581540433f6555010ed185540433f6255010cf989540433d6255010cf189540433e6155010cf18554043346155010cf981540433c6055010cf04154042be6415010cf55054042ee6215010bb588540427e6415010cf990540423e64150109f988540436e62150109b988540427d6215010db588540426d62150109f984540437661150109f980540437a6015010af99352042bd64d4810cf953520433d54d4810b798f52042dd63d48109f993520433e64d48108f993520427d64d4810cf593520423d64d48109f98f520435e63d48109798f520427d63d4810d758f520425d63d48109f987520437661d48109f983520437a60d48109f596520433e5494810cf552520436f52948109f992520427d64948109f98e520427d63948109b596520436f5494810db95252043ae5494810cb952520436d5494810eb552520432d5494810db152520436f5394810db94e52043ce5394810d394e52043e46194810dbd92520436e6494810db592520436c6494810dbd8e520436e6394810db58e520436c6394810db986520436c6194810db982520436c6094810cf951520433d5454810d794d520427f64548109f191520427f63548109f18d520436f62548109fd85520427d6154810dd185520427f60548109f581520436f6554810dbd51520436e5454810eb951520432e5454810db55152043ad5454810cb551520436c5454810dbd4d520436e5354810f394d520434e5354810db54d52043cd5354810d354d52043e46154810dbd91520436e6454810db591520436c6454810dbd8d520
  | 3 => 0x910ddd85524427761549109fd81524437b60549109f994524433f5414910cf150524435f5314910db548524427e64149109f590524427e63149109f58c524436e62149109f984524427c61149109f980524427c6014910bb994524436e65149109b994524436f5414910ebd50524432f5414910db950524436d5414910db15052443ac5414910cb150524436f5314910f3d4c524434f5314910db94c524436d5314910db14c52443cc5314910d314c524436f6414910db990524436d6414910db190524436f6314910db98c524436d6314910db18c524436f6114910db584524436f6014910db580524436d10149109fd97424427e65d09109f597424427c65d0910cfd53424433c54d0910d7d4f424435c53d0910dbd4b424436c52d09109fd96424427e65909109f596424427c6590910cfd52424433c5490910d7d4e424435c5390910dbd4a424436c52909109fd95424427e65509109f595424427c6550910cfd51424433c5450910b7d8d42442dc6350910d7d4d424435c5350910dbd49424436c52509109fd94424427e65109109f594424427c6510910cfd50424433c5410910d7d4c424435c5310910dbd48424436c5210910eb50842442f66110910bd584424427f658c9109f996324427d658c9109f196324433f548c910cf152324435f538c910d714e324436f528c910db14a324427f654c9109f995324427d654c9109f19532442bf644c910af191324433f544c910cf151324436f524c910db149324427f650c9109f994324427d650c9109f194324433f540c910cf150324436f520c910db14832443cd320c910bd98432442f5610c9109f997414433f54d0510cf153414436f52d0510db14b41442fa60d0510be583414427e6590510cfd52414433c5490510bb98a41442ed6290510dbd4a414436c52905109f195414433f5450510cf151414436f5250510db14941442fb6050510be181414427e6510510cfd50414433c5410510dbd48414436c52105109f997214433f54c8510cf153214435f53c8510d714f214436f52c8510db14b21442fa60c8510be583214427e6588510af99221442bd6488510cfd52214433c5488510b798e21442dd6388510d7d4e214435c5388510dbd4a214436c52885109f195214433f5448510cf151214435f5348510d714d214436f5248510db14921442fb6048510be181214427e6508510cfd50214433c5408510d7d4c214435c5308510dbd48214436c52085109f997404433f54d0110cf153404436f52d0110db14b40442f661d0110bd587404427e6590110cfd52404433c5490110dbd4a404436c52901109fd95404427d65501109f195404433f5450110cf15140442ef6250110bb189404436f5250110db14940442f76150110bd185404427e6510110cfd50404433c5410110dbd48404436c
  | 4 => 0x9ccb21843e432c8610fc98321842f560c8610fc58321842be6488610af59221842de6388610b758e218436f5288610db14a218436e5248610db54921842fb6048610be181218436f5208610db14821843e52108610bd59421843756508610bd99021842f46408610bd98c21842f46308610f998821843775208610f9d4821843755208610f914821842f56008610cfd53408433c54d0210edd07408433e5490210cf55240842f66190210bd58640843b44190210cfd51408433c5450210bbd8940842ec6250210bdd8540842f46150210edd05408433e5410210cf55040842f66110210bd58440843b44110210dbd4b208436c52c8210f9c87208436e5288210db54a20842f66188210bd58620843e42188210afd9120842bc6448210b7d8d20842dc6348210dbd49208436c5248210bdd8520842f46148210f9c85208436e5208210db54820842f66108210bd58420843e42108210bd597108437565c4210bd99310842f464c4210bd98b10842f462c4210be597108437965c42109f98b544427d62d5110cfd8b544433e62d5110cf58b544433c62d5110cfd87544433d61d5110cfd83544433d60d5110cfd5254442ee6295110bb58a544427e64951108f992544427e6295110db98a544426e62951109f58a544436d62951109b58a544427d6195110dd586544427d6095110de58254442ef6255110bb189544433f64551109fd89544436f62551109bd89544427c6255110db189544426c62551109fd85544437761551109dd85544427f6055110ded81544427e6515110cf550544433e64151109f988544427d62151109f984544427c61151109f980544427c6015110af994544433e65151108f994544433f6215110cf988544433d6215110cf188544433f6115110cf584544433f6015110cf580544433d1015110cfd53524433c54d49109f993524427d64d49109f98f524427d63d4910dbd5352443af54d4910cbd53524436e54d4910db553524436c54d4910eb153524432c54d4910dbd4f52443cf53d4910d3d4f524436f64d4910db993524436d64d4910db193524436f63d4910db98f524436d63d4910db18f524436f61d4910db587524436f60d4910db58352442be6494910af592524433f5494910cf15252442de6394910b758e524435f5394910dbd4a524427e6494910cf992524423e64949109f592524433d64949108f592524427e6394910d798e524425e63949109f58e524435d63949109758e524427e62949109b98a524427d6194910dd586524427d6094910de58252442bf6454910af191524433f5454910cf15152442df6354910b718d524435f53549109fd91524433f64549108fd91524427c6454910cf191524423c64549109fd8d524435f635491097d8d524427c6354910d718d524425c6354910dbd89524427f6154
  | 5 => 0x41c433d5410710be98041c42f96010710dbd4b21c436c52c8710af99221c42bd6488710b798e21c42dd6388710db94a21c436d5288710be98221c42f96088710dbd4921c436c5248710db94821c436d5208710be98021c42f96008710cf95340c433d54d0310bd98740c42f561d0310cfd5240c433c5490310cf95140c433d5450310bbd8940c42ec6250310bdd8540c42f46150310cfd5040c433c5410310db94b20c436d52c8310bd98720c42f561c8310dbd4a20c436c5288310afd9120c42bc6448310b7d8d20c42dc6348310db94920c436d5248310bdd8520c42f46148310dbd4820c436c52083109f98b548427d62d5210dd587548437a60d5210cfd52548427e62952109f58a54842ef6255210bb189548433f64552109fd89548436f62552109bd89548427c6255210db189548426c6255210ddd85548433d5415210cf990548427e62152109f58854843756115210de980548427e64d4a109f593528427e63d4a109f58f528437561d4a10de983528436f5294a109f992528427d6494a109f98e528427d6394a10afd9152842bc6454a10b7d8d52842dc6354a109fd91528433f6454a108fd91528427c6454a10cf191528423c6454a109fd8d528435f6354a1097d8d528427c6354a10d718d528425c6354a10dbd8952843776154a10db548528427e6414a109f590528427e6314a109f58c528436e6214a10dd584528437a6014a109fd97428427e65d0a109f597428427c65d0a10dbd4b428436c52d0a10bd98742842f561d0a109fd96428427e6590a109f596428427c6590a10cfd52428433c5490a10bd98642842f56190a109fd95428427e6550a109f595428427c6550a10b7d8d42842dc6350a10bdd8542842f46150a109fd94428427e6510a109f594428427c6510a10cfd50428433c5410a10dbd48428436c5210a10eb508428427f658ca109f996328427d658ca109f196328435f538ca10d714e32842f6618ca10bd586328427f654ca109f995328427d654ca109f19532842bf644ca10af19132842f7614ca10bd185328427f650ca109f994328427d650ca109f194328436f520ca10db14832843cd320ca10cf953418433d54d0610be98341842f960d0610dd597418437754d0610ed953418437554d0610ed55341842f662d0610ed90b41843b442d0610fc98341842f560d0610fc583418433f5490610cf15241842ee6290610bb58a418433e5450610cf55141842fb6050610be181418433f5410610cf15041843b54110610bd59441843756510610ed99041843775410610edd5041843755410610ed15041842f66210610bd580418436e52c8610db54b21842fa60c8610be583218437565c8610bd99321842f464c8610bd98f21842f463c8610ddd4b21843e652c8610dd54b21843e552c8610f9d0b21843e442c8610f
  | 6 => 0x2df6350020b718d40082ef6250020bb18940082f76150020bd185400827f65100209f994400827d65100209f194400833e5410020cf55040082ee6210020bb58840083ac42100209f597300827f658c0209f596300835e538c020d754e30082ee628c020bb58a30083cc328c0209fd9530082bf644c020af19130082ef624c020bb18930082f7614c020bd185300827e650c0209f594300827c650c020bb98830082ed620c020f30c830082ee64c8020bb19320082ee63c8020bb18f20082ee61c8020db54720082ed6288020db94a20082f96288020de94a20083ea5288020fad0a20083e84288020facca20083e83288020fa88620083e821880209fd9520082bf6448020af19120082df6348020b718d20082f76148020bd18520082ef6548020dbd95200826f6548020ebd9120082ee6448020bb19120083ac6448020ab19120083cf6348020bb98d20082ec6348020f318d20082cc6348020f9d8520082ec6148020f918520082e46148020db54520082ef6048020db94120082fb6548020ded95200827b6548020eed9120083b86448020f6d8d20083d86348020bed8920083eb6248020de94920083ea5248020fcd8520083f06148020bb98b54c42ed62d53109f98b54c436e62d53109b98b54c427d62d5310db58b54c426d62d5310dd98754c437960d5310cfd5254c427e62953109f58a54c433f64553109fd8954c427c6255310cf55054c433e64153109f98854c427d6215310dd98454c43796015310af99352c42bd64d4b10b798f52c42dd63d4b109f99352c433e64d4b108f99352c427d64d4b10cf59352c423d64d4b109f98f52c435e63d4b109798f52c427d63d4b10d758f52c425d63d4b10dd98752c437960d4b10dbd4a52c427e6494b109f59252c427e6394b109f58e52c427f6454b109f19152c427f6354b109f18d52c436f6254b10db54852c427e6414b109f59052c427e6314b109f58c52c436e6214b10dd98452c43796014b109fd9742c427e65d0b109f59742c427c65d0b10db94b42c436d52d0b109fd9642c427e6590b109f59642c427c6590b10cf95242c433d5490b109fd9542c427e6550b109f59542c427c6550b10b7d8d42c42dc6350b10bed8142c42f86050b109fd9442c427e6510b109f59442c427c6510b10cf95042c433d5410b10db94842c436d5210b10eb50842c42f66110b10bd58442c427f658cb109f99632c427d658cb109f19632c435e538cb10d754e32c427f654cb109f99532c427d654cb109f19532c42bf644cb10af19132c42fb604cb10be18132c427f650cb109f99432c427d650cb109f19432c436e520cb10db54832c43cd320cb10bd98432c42f5610cb10cfd5341c433c54d0710cf95241c433d5490710bb98a41c42ed6290710be98241c42f96090710cfd5141c433c5450710cf950
  | 7 => 0x410820cf55042083ad4210820be98042082f96010820db594420826d6510820bb99042083ae6410820dbd5042083ae5410820db55042083ad5410820cb55042082ee6310820db94c420836c5310820eb90c42083ac4310820bb98442083ea6010820bb58042083e960108209f59732082ed65cc820db59732082ee64cc820bb193320836e54cc820db153320836f53cc820db54f32082ee61cc820bb583320827f658c8209f596320835e538c820d754e32082ee628c820be98232082f9608c8209fd9532082bf644c820af191320827f650c8209f594320835e530c820d754c32083cd320c820be98032082f9600c820db594320826d650c820bb99032082ec640c820db950320836c540c820bb98c32083ce630c820dbd4c32083ce530c820db54c32083cd530c820d354c32083cf430c820f310c32082ee610c820fa98032082ed600c820fa580320837751944209f992510827d64944209f98e510827d63944209fd91510827c64544209fd8d510827c6354420dbd09510836c4254420dbcc9510836c3254420af99051082bd6414420b798c51082dd6314420dd544510827f65d04209f997410827d65d0420cf953410833d54d0420bb98b41082ed62d0420eb10b410827f65904209f996410827d6590420b798e41082dd6390420bb98a41082ed6290420dd946410837551904209fd95410827d65504209f195410833e5450420cf55141082ef6250420bb18941083ac4250420dd94541083755150420bed8141082f860504209fd94410827e65104209f594410827f65cc4209f997310827d65cc420d794f310835d53cc420bb98b31082ed62cc420f30cb310827f658c4209f996310827d658c420af99231082bd648c420bb98a31082ed628c420dd9463108375518c4209fd95310827d654c4209f195310835e534c420d754d31082ef624c420bb18931083cc324c420dd9453108375514c420bed8131082f8604c4209fd94310827e650c4209f594310836e52c8420dd947210837551c8420be98321082f960c84209f59621082be6488420af59221082de6388420b758e21082ed6588420db596210826d6588420bb99221083ae6488420ab99221083ad6488420bb19221082ee6388420f398e21082ce6388420f358e21082ec6388420bb986210836d5188420bb582210827f6548420db94921083765108420dd54421083e52108420be98021082f96008420bb99021082ec6408420bb98c21082ec6308420bb98421083e66108420f9944210836d5108420f954421083ea6008420bb58021083e960084209f992500827d64940209f98e500827d6394020dbd0a500836c4294020dbcca500836c3294020db886500836c21940209f597400827f65900209f596400833e5490020cf55240082ee6290020bb58a40083ac42900209fd954008
  | 8 => 0x20d714f30482ee62cc120bb58b304837751cc120dd147304833f548c120cf152304835f538c120d714e3048377518c120dd146304827d654c1209f195304833f544c120cf15130482ef624c120bb1893048377514c120dd145304833f54c8120cf153204835f53c8120d714f204837751c8120dd14720483bb54c8120ee15320483db53c8120f614f20483f351c8120fc14720483eb21c8120fa487204833f5488120cf152204835f5388120d714e20483775188120dd14620483af5488120db952204836c5488120eb152204832c5488120f3d4e204836e5388120db14e20483cc5388120d314e20482ed6188120f9d46204836c5188120f914620483645188120fad42204827e63d50209f58f540827e62d5020db98b540827e61d50209f587540827e60d5020de983540827d6595020cfd52540827e63950209f58e540827e61950209f58654082df6355020b718d540833f64550209fd8d540835f635502097d8d540827c6355020d718d540825c63550209fd89540827d6255020db189540827f61550209f185540833d5415020b798c54082dd6315020bd98454082f561150209f990540833e64150209f98c540835e63150209798c540827d6315020d758c540825d63150209f988540836e62150209f984540837661150209d984540827d6115020dd584540827561150209f980540837a60150209f993530827d64d4c20db98b530827e61d4c209f587530837a60d4c209f596530835f5394c209f992530827d6494c209f986530827d6194c20afd9153082bc6454c209fd91530833f6454c208fd91530827c6454c20cf191530823c6454c20d7d8d530827f6254c209f589530836c6254c209fd85530827c6154c20af99053082bd6414c20d754c53082f66114c20bd584530827e6414c20cf990530823e6414c209f590530833d6414c208f590530827e6214c20db988530827e6114c20dd98453082766114c209f58453083756114c209d584530827e6014c20de980530827f65d0c209f997430827d65d0c209f197430833e54d0c20cf553430835f53d0c20bb98b43082ed62d0c209fd96430827e6590c209f596430827c6590c20cfd52430833c5490c20d794e430835d5390c20bb98a43082ed6290c209fd95430827e6550c209f595430827c6550c20cf951430833d5450c20d794d430835d5350c20bbd8943082ec6250c209fd94430827e6510c209f594430827c6510c20cfd50430833c5410c20d7d4c430839d4310c209f992520827d64948209f58e520827d65d0820bb597420836d65d0820dbd53420836d54d0820bb98f420836e53d0820db14f42082ee61d0820bb583420827f65908209f596420833e5490820cf55242082ee6290820be98242082f960908209fd9542082df6350820b718d420827f65108209f594420833e5
  | 9 => 0xd8c51483766314520dd58c51483746314520ddd0c51483764314520dd50c51483744314520ddd8851483774214520dd90851483754214520dd10851483773214520dd8c851483753214520dd0c851483776014520dd580514837520145209f997414827d65d05209f197414833f54d0520cf153414835f53d0520d714f414837751d0520dd147414827e65905209f596414827c6590520cfd52414833c5490520b798e41482dd6390520d7d4e414835c5390520bb98a41482ed6290520ddd46414837451905209fd95414827e65505209f195414833f5450520cf151414835f5350520d714d41483775150520dd145414827e65105209f594414827c6510520cfd50414833c5410520d7d4c414835c5310520bb98841482ed6210520ddd44414837451105209f997314827d65cc5209f197314833f54cc520cf153314835f53cc520d714f314837751cc520dd147314827e658c5209f596314827c658c520af99231482bd648c520cfd52314833c548c520d7d4e314835c538c520bb98a31482ed628c520ddd463148374518c5209fd95314827e654c5209f195314833f544c520cf151314835f534c520d714d3148377514c520dd145314827e650c5209f594314827c650c520cfd50314833c540c520d7d4c314835c530c520bb98831482ed620c520ddd443148374510c5209f997214833f54c8520cf153214835f53c8520d714f214837451c8520bb997214836e65c85209b99721483af54c8520db953214836c54c8520eb153214832c54c8520f3d4f214836e53c8520db14f21483cc53c8520d314f21483e751c8520db14721483e451c8520d914721482ee60c8520af99221482bd6488520cfd52214833c5488520b798e21482dd6388520d7d4e214835c5388520bb58a21483775188520dd14621482fa6088520be582214833f5448520cf151214835f5348520d714d21483775148520dd14521482fb6048520be18121483af5448520db951214836c5448520eb151214832c5448520f3d4d214836e5348520db14d21483cc5348520d314d21483e76148520f9d45214836c5148520f914521483645148520fad8121482ec6048520fa181214827e6508520cfd50214833c5408520d7d4c214835c5308520bb988214837751085209f997404833f54d0120cf153404835f53d0120d714f40482ee62d0120bb58b404837751d0120dd147404827e6590120cfd52404833c5490120d7d4e404835c5390120ddd46404837451901209fd95404827d65501209f195404833f5450120cf15140482df6350120b718d404835f5350120d714d40482ef6250120bb18940482f76150120bd18540483775150120dd145404827e6510120cfd50404833c5410120d7d4c404835c5310120ddd44404837451101209f997304833f54cc120cf153304835f53cc1
  | 10 => 0x34835d5314d209f990534827d6414d20d798c534827c6214d209f984534827d6114d20b7994534835e6514d2097994534835f5414d20e7d50534831f5414d20d7950534835d5414d20d7150534839c5414d20c7150534835f6414d20d7990534835d6414d20d7190534835f6214d20d7d84534835e6114d20d7584534835c6114d20d7d80534835d6014d20d7480534827f65d0d209f997434827d65d0d209f197434833f54d0d20cf153434835f53d0d20d714f434827f6590d209f996434827d6590d209f196434833f5490d20cf152434835f5390d20d714e434827f6550d209f995434827d6550d209f195434833f5450d20cf151434835f5350d20d714d43482ef6250d20bb189434827f6510d209f994434827d6510d209f194434833f5410d20cf150434835f5310d20d714c434839d4310d20bb98843482ed6210d209f997424833f54d0920cf153424835f53d0920d714f42482fa60d0920be583424827e6590920cfd52424833c5490920d7d4e424835c53909209f195424833f5450920cf15142482df6350920b718d424835f5350920d714d42482fb6050920be181424827e6510920cfd50424833c5410920d7d4c424835c5310920eb508424833f54cc920cf153324835f53cc920d714f32482fa60cc920be583324827e658c920cfd52324833c548c920d7d4e324835c538c920afd9132482bc644c920cfd51324833c544c920d7d4d324835c534c920bed8132482f8604c9209f994324833f540c920cf150324835f530c920f34c8324833f54d4520cf153514835f53d4520d714f514827e64d45209f593514827e63d45209f58f514837754d4520edd53514833754d4520dd953514837554d4520dd15351483b454d4520cd153514837753d4520f5d4f514835753d4520dd94f514837553d4520dd14f51483d453d4520d514f51483e762d4520ddd93514837664d4520dd593514837464d4520ddd8f514837663d4520dd58f514837463d4520ddd0f514837643d4520dd50f514837443d4520ddd8b514837742d4520dd90b514837542d4520dd10b514837732d4520dd8cb514837532d4520dd0cb514837760d4520dd58351482be6494520af592514833f5494520cf15251482de6394520b758e514835f5394520d714e51483775194520afd9151482bc6454520cfd51514833c5454520b7d8d51482dc6354520d7d4d514835c5354520cfd50514833c5414520d7d4c514835c5314520dd544514827e64145209f590514827e63145209f58c51482f66514520dd99451483775414520edd5051483375414520dd95051483755414520dd15051483b45414520cd15051483775314520f5d4c51483575314520dd94c51483755314520dd14c51483d45314520d514c51483e56214520ddd9051483766414520dd59051483746414520dd
  | 11 => 0xae6488620eb59221882ec6488620bb98e21883ce6388620b398e21883cd6388620bb18e21883e65188620db54621883e55188620fa98221882ed6088620fa58221883765148620dd54521882fb6048620be18121883e52108620bb594218836d6508620bb99021882ec6408620bb98c21882ec6308620f998421883e75108620db54421883e45108620bb580218833e5490220cf55240882ee6290220bb58a40883ac4290220b7d8d40882dc6350220bbd8940882ec6250220bdd8540882f46150220cf950408833d5410220bb98840882ed6210220eb10840882ee628c220bb58a30883cc328c220bb597208836d65c8220bb99320882ec64c8220bb98f20882ec63c8220bb987208836d51c8220be597208837965c82209f98f544827d63d51209f987544827d61d5120cfd8f544833e63d5120cf58f544833c63d5120cfd8b544833d62d5120cfd87544833e61d5120cf587544833c61d5120cfd83544833d60d5120cfd5254482de6395120b758e54482f66195120bd586544827e64951208f992544827e6395120d798e544825e63951209f58e544835d63951209758e544827d6295120db58a544827e6195120dd986544827661951209f586544837561951209d586544827d6095120de58254482df6355120b718d54482f76155120bd185544833f64551209fd8d544835f635512097d8d544827c6355120d718d544825c63551209fd89544836f62551209bd89544827f6155120ddd85544827761551209f185544837461551209d185544827f6055120ded81544827e6515120cf550544833e64151209f98c544827d63151209f988544827c62151209f984544827d6115120af994544833e65151208f994544833f6315120cf98c544833d6315120cf18c544833f6215120cf588544833f6115120cf984544833d6115120cf184544833f6015120cf580544833d2015120cfd53534833c54d4d209f993534827d64d4d209f987534827d61d4d20d7d53534839f54d4d20c7d53534835e54d4d20d7553534835c54d4d20e7153534831c54d4d20d7d93534835e64d4d20d7593534835c64d4d20d7d8b534835d62d4d20d7d87534835e61d4d20d7587534835c61d4d20d7d83534835d60d4d20af99253482bd6494d20cfd52534833c5494d20d7d4e53482f66194d20bd586534827e6494d20cf992534823e6494d209f592534833d6494d208f592534836d6294d209f98653483766194d209d986534827d6194d20dd58653482756194d20de58253482bf6454d20af191534833f5454d20cf15153482f76154d20bd185534827f6454d20cfd91534823f6454d209f191534833c6454d208f191534836f6254d209fd8553483776154d209dd85534827c6154d20dd18553482746154d209fd81534837b6054d209f994534833f5414d20cf1505
  | 12 => 0x152209f58c548836d62152209f984548827d6115220de98054882be64d4e20af593538827e64d4e20cf993538823e64d4e209f593538833d64d4e208f593538827e61d4e209f587538837a60d4e20d7d4e538827e6494e209f592538827e6194e209f586538827f6454e209f191538835f6354e209fd85538827c6154e20d754c538827f65d0e209f997438827d65d0e209f197438835e53d0e20d754f43882ee62d0e20bb58b438827f6590e209f996438827d6590e20cf952438833d5490e20bb98a43882ed6290e209fd95438827e6550e209f595438827c6550e20bbd8943882ec6250e209fd94438827e6510e209f594438833e5410e20cf550438835e5310e20d754c438839d4310e20cf953428833d54d0a20be98342882f960d0a20db597428836f54d0a20eb953428836d54d0a20eb55342882ee63d0a20db94f42882ee61d0a20fa98342882ed60d0a20fa583428833f5490a20cf152428833e5450a20cf55142882df6350a20b718d42882fb6050a20be181428833f5410a20cf15042883ad4210a20bb594428836d6510a20eb990428836f5410a20ebd50428832f5410a20db55042883ac5410a20bb98c428836e5310a20eb90c42883ac4310a20bb98442882ed6010a20d794f328835d53cca20be98332882f960cca20bb99332882ec64cca20db953328836c54cca20f394f328836d53cca20f354f32882ee61cca20fa98332882ed60cca20fa583328835f538ca20afd9132882bc644ca20d794d328835d534ca20bed8132882f8604ca20f34c832882ed650ca20db59432882ee640ca20bb190328836e540ca20db15032883ce630ca20dbd4c32883cf530ca20d3d4c328836d530ca20f314c32883cf430ca20f310c32882ee610ca20bb580328837751946209f992518827d64946209f98e518827d63946209fd91518827c64546209fd8d518827c6354620dbd09518836c4254620dbcc9518836c3254620af99051882bd6414620b798c51882dd6314620dd544518827f65d06209f997418827d65d0620cf953418833d54d0620bb98b41882ed62d0620eb10b418827f65906209f996418827d6590620b798e41882dd6390620bb98a41882ed62906209fd95418827d65506209f195418833e5450620cf55141882ef6250620bb18941883ac42506209fd94418827e65106209f594418827f65cc6209f997318827d65cc620d794f318835d53cc620bb98b31882ed62cc620f30cb318827f658c6209f996318827d658c620af99231882bd648c620bb98a31882ed628c6209fd95318827d654c6209f195318835e534c620d754d31882ef624c620bb18931883cc324c6209fd94318827e650c6209f59431882be6488620af59221882de6388620b758e21883765188620dd54621882fa6088620be58221882ee6488620eb99221882
  | 13 => 0x9f99053c827d6414f20db98853c827e6114f209f58453c83796014f209fd9743c827e65d0f209f59743c835e53d0f20d754f43c827f6590f209f99643c827d6590f209f19643c833e5490f20cf55243c827f6550f209f59543c827c6550f20bbd8943c82ec6250f209fd9443c827e6510f209f59443c827c6510f20cf95043c833d5410f20d794c43c835d5310f20e750c43c82ee6210f20bb58843c833e5490b20cf55242c82fa6090b20be58242c82df6350b20b718d42c833e5410b20cf55042c83ad4210b20be98042c82f96010b20d794e32c835d538cb20be98232c82f9608cb20afd9132c82bc644cb20d794c32c835d530cb20f34c832c82fa600cb20be58032c82be64d4720af59351c82de63d4720b758f51c82be6494720af59251c82de6394720b758e51c837751947209f99251c833e64947208f99251c827d6494720cf59251c823d64947209f98e51c835e63947209798e51c827d6394720d758e51c825d63947209fd9151c827c64547209fd8d51c827c6354720dd54451c827f65d07209f99741c827d65d0720cfd5341c833c54d0720dd94741c837551d07209fd9641c827e65907209f59641c833e5490720cf55241c82de6390720b758e41c82ee6290720bb58a41c827f65507209f59541c827c6550720cfd5141c833c5450720bed8141c82f860507209fd9441c827e65107209f59441c833e5410720cf55041c82ee6210720bb58841c83765110720dd54441c827f65cc7209f99731c827d65cc720dd94731c837551cc7209fd9631c827e658c7209f59631c82be648c720af59231c835e538c720d754e31c82ee628c720bb58a31c827f654c7209f59531c827c654c720bed8131c82f8604c7209fd9431c827e650c7209f59431c835e530c720d754c31c82ee620c720bb58831c8376510c720dd54431c837651c8720dd54721c82fa60c8720be58321c836e54c8720db15321c836e53c8720db14f21c836e51c8720f994721c83e551c8720bb98321c83ea60c8720fa58321c82be6488720af59221c82de6388720b758e21c82ef6548720dbd9521c836e5448720db15121c836e5348720db14d21c83e76148720db94521c82ec6048720dd94421c83755108720be98021c82f96008720cf95340c833d54d0320bb98b40c82ed62d0320cfd5240c833c5490320cf95140c833d5450320b7d8d40c82dc6350320bbd8940c82ec6250320bdd8540c82f46150320cfd5040c833c5410320bb98b30c82ed62cc320b798f54882dd63d52209f98f548835e63d52209798f548827d63d5220d758f548825d63d5220db58b548827e61d52209f587548837a60d5220cfd52548827e63952209f58e548827e61952209f586548833f64552209fd8d548827c6355220dbd89548827f61552209f185548833d5415220cf990548827e63
  | 14 => 0x9542102df6350840b718d421036e5210840db54842103ad4210840be98042102f96010840af98c421033e5310840af98842103ae6210840eb948421033d5210840eb548421032d5210840af98442103ba6010840af58042103b960108409fd96321027e658c8409f59632102be648c840af592321039c438c840db94a321036d528c8409fd95321027d654c8409f19532102bf644c840af191321036e524c840db549321027f650c8409f994321027d650c840afd9032102bc640c840eb10832103cd320c840ddd46511027e62944409f58a511027f62544409f189511033e4254440cf10951102ee6214440bb58851103755114440cf953411037651d0440dd54741102fa60d0440be583411027d6590440bb98a41102ed6290440af596411033d65904408f59641102be6290440eb98a41102ae6290440eb58a41102be6190440cf54641102bd60904409fd95411033e5450440dd94441103755110440ed50441102fa6010440be58041102be6210440af98441103b66110440ed944411033d5110440ed54441103ba6010440af58041103b960104409fd97211027e65c84409f59721102be64c8440af593211036e52c8440db54b21103ac42c84409fd96211027e65884409f59621102be6488440af59221102de6388440b758e21103765188440dd546211027f65484409f595211027c6548440afd9121102bc6448440db949211036d5248440eb10921103765148440dd54521102fb6048440be181211027f65084409f994211027d6508440afd9021102bc6408440cf90a501033c4294040cf906501033c4194040af98b40102be61d0040cf54740102bd6490040cf95240102f96490040de95240103ba5490040ee90a40103b84290040ee90640103b841900409fd9540102ef6250040bb18940102f76150040bd18540102bf6550040cfd95401023f6550040ebd8940102bc6250040eb18940102ac6250040edd8540102bc6150040ed18540102b46150040cf54540102bf6050040cf94140102fb6550040ded95401027b6550040bed9140103bb6450040de95140103ba5450040fad8940103e86250040fcd8540103f06150040b798f54c82dd63d5320bd98754c82f561d53209f98f54c835e63d53209798f54c827d63d5320d758f54c825d63d5320db98b54c827e61d5320dd98754c827661d53209f58754c837561d53209d58754c837960d5320cfd5254c827e63953209f58e54c827e61953209f58654c833f64553209fd8d54c827c63553209fd8554c827c6155320cf55054c833e64153209f98c54c827d6315320db98854c827e61153209f58454c83796015320af99353c82bd64d4f20bd98753c82f561d4f20d7d4e53c827e6494f209f59253c827e6194f209f58653c827f6454f209f19153c827f6154f209f18553c835d5314f2
  | 15 => 0x503cd320c940dbd4b515036c52d45409f98b515027d62d4540edd93515037752d4540f9d4b515036752d4540dd94b515037552d4540dd14b51503e452d4540d914b515037764d4540ddd8b515037662d4540dd58b515037462d4540ddd0b515037642d4540dd50b515037442d4540dd8cb515037532d4540dd0cb515037760d4540dd58351502ee6294540bb58a515036f5294540db14a51503775194540bbd8951502ec6254540dbd49515036c5254540dbd48515036c5214540dd544515027e62145409f58851502f66514540dd99451503b56414540ddd4851503e75214540d9d4851503765214540dd54851503745214540f914851503645214540ddd9051503776214540dd98851503756214540dd18851503774214540dd90851503754214540dd10851503763214540dd4c851503743214540ddd8051503756014540dd500515027e65d0540dbd4b415036c52d0540dd14741502be65d0540cf997415023e65d0540ebd4b415033c52d0540eb14b415032c52d0540edd47415033c51d0540ed147415033451d0540af98341502bd6490540bb98a41502ed6290540dbd4a415036c5290540ddd4641503745190540be98241502f96090540dbd49415036c5250540ddd4541503745150540bed8141502f86050540ebd49415033c5250540eb149415032c5250540edd8541503b75150540cf14541503b45150540cd14541503bb6050540af18141503b860505409f99441502be6410540dbd48415036c5210540ddd44415027e65c85409f597215027c65c8540d7d4f215035c53c8540dbd4b215036c52c8540ddd47215037451c85409f996215027d65885409f19621502be6488540af59221502de6388540b758e215035f5388540d714e215036f5288540db14a21503775188540dd146215027f65485409f995215027c6548540d7d4d215035c5348540dbd49215036c5248540ddd45215037451485409f994215027d65085409f19421502be6408540af590215035f5308540d714c215036f5208540db14821503775108540dd144215036f52d0140db14b405037751d0140dd14740503eb52d0140fa14b40503f351d0140fc14740503bb41d0140ee507405036f5290140db14a40503775190140dd14640503af5290140cf14a40503ac5290140cb14a40502bd6190140edd46405033c5190140ed14640503345190140eed42405036f52948409f98e521027d63948409f986521027d6194840b7d8d52102dc63548409fd8d521035f635484097d8d521027c6354840d718d521025c63548409fd85521027c6154840b798c52102dd6314840db54852102f66114840bd584521036e52d0840db54b42102fa60d0840be583421027d6590840af596421033d6590840af98e421033e5390840af98a421033d5290840af98642102bd60908409fd
  | 16 => 0xd6090a40ee58242902df6350a40b718d429036e5250a40db54942902fb6050a40be18142903ad4210a40af594429033d6510a40af98c429033e5310a40eb98842903af5210a40cf54842903ac5210a40af98442902bd6010a409fd96329027e658ca409f59632902be648ca40af592329035e538ca40d754e329039c438ca409fd95329027d654ca409f19532902bf644ca40af191329027f650ca409f994329027d650ca40afd9032902bc640ca40db948329036d520ca40eb10832903cd320ca40ddd46519027e62946409f58a519027f62546409f189519033e4254640cf10951902ee6214640bb58851903755114640bb98a41902ed6290640dd94641903755190640be98241902f96090640af98a41903ae6290640ab98a41903ad6290640ed946419033d5190640ed54641903ba6090640af58241903b96090640dd94541903755150640bed8141902f86050640ed50441902bd6510640cf59441902be6210640ed98441903b75110640cf54441903b45110640af580419027f65c86409f997219027d65c8640af99321902bd64c8640db94b219036d52c8640eb10b219027f65886409f996219027d6588640af99221902bd6488640b798e21902dd63886409fd95219027d65486409f19521902bf6448640af191219036e5248640db54921903ac42486409fd94219027e65086409f59421902bf6408640af19021902bd65d0240cf59740902be62d0240af987409033d51d0240be597409037965d02409f98f525027d63d49409f987525027d61d4940dbd4f52503cf53d4940d3d4f525036f64d4940dbd8f525036e63d4940db58f525036c63d4940dbd87525036e61d4940db587525036c61d4940dbd83525036d60d4940b798e52502dd6394940d7d4e525036f5294940bd98652502f56194940b7d8d52502dc6354940d7d4d52502f76154940bd185525035f5314940db548525027e63149409f58c525027e61149409f58452502ee6514940db994525036f5314940f3d4c525034f5314940db94c525036d5314940db14c52503cc5314940d314c525036f6414940dbd8c525036e6314940db58c525036c6314940dbd84525036e6114940db584525036c6114940dbd80525036d6014940db500525027e65d0940d7d4f425035c53d0940db14b425035f5390940d714e425036f5290940db14a42502fa6090940be58242502df6350940b718d425035f5350940d714d425036f5250940db14942502fb6050940be181425027e6510940d7d4c425035c5310940dbd4842503ad42109409f996325027d658c9409f196325035f538c940d714e325036f528c940db14a325027f654c9409f995325027c654c940afd9132502bc644c940dbd49325036c524c9409f994325027d650c9409f19432502be640c940af590325036f520c940db14832
  | 17 => 0xc421d754e31086ee628c421bb58a310867f654c421d7d4d310867e650c4219f594310867c650c421bb98831086ed620c421db953210876c54c8421db94f210876c53c8421bb98321086be6488421af59221086de6388421b758e21086ed6288421db94a21087b66488421ed59221087d66388421f558e21086f56288421dd94a21087e65288421bd982210867f6548421bbd95210876f65484219bd95210876e5448421db151210876e5348421db14d21086ef6148421db94521087e64148421f950521087e63148421f94c521086ec6048421bdd95210877765484219dd9521086f76248421f9d8921087765248421f994921087e64248421f950921087e63248421f94c921086f46048421ded42500867e64940219f592500867e63940219f58e50086bf6454021af19150086df6354021b718d500867f6454021cfd91500863f64540219f191500873c64540218f191500867f6354021d7d8d500865f63540219f18d500875c63540219718d500876f2154021db48550086be6414021af59050086de6314021b758c50087795014021b798f52d02dd63d4b40bd98752d02f561d4b40dbd4a52d027e6394b409f58e52d027e6194b409f58652d027f6354b409f18d52d027f6154b409f18552d036d5214b40db94b42d036d52d0b40be98342d02f960d0b40b7d8d42d02dc6350b40db94842d036d5210b40eb50842d02fa6010b40be58042d027f658cb409f99632d027d658cb40d794e32d035d538cb409fd9532d027d654cb409f19532d02bf644cb40af19132d027f650cb409f99432d027d650cb40af99032d02bd640cb40db94832d036d520cb40f34c832d02ee62d4740bb58b51d02ee6294740bb58a51d037751947409f98a51d036e62947409b98a51d027d6294740db58a51d026d62947409fd8951d027c6254740dd54451d037651d0740dd54741d02fa60d0740be58341d033e52d0740cf94741d03b651d0740ed54741d02be60d0740ee98341d03b960d0740bb98a41d02ed6290740afd9541d033f6550740cf94941d03b76150740cf94541d02bc6050740dd94441d03755110740be98041d02f960107409fd9721d027e65c87409f59721d037651c8740dd54721d027f65887409f99621d027d6588740af99221d02bd6488740b798e21d02dd6388740db94a21d036d52887409fd9521d027d65487409f19521d02fb6048740be18121d027f65087409f99421d027d6508740af99021d02bd6408740db94821d036d5208740dd94421d03755108740b798f52902dd63d4a40dbd4a529027e6394a409f58e529027e6194a409f586529027f6354a409f18d529027f6154a409f185529036d5214a40db94a429036d5290a40be98242902f96090a40af98e429033e5390a40eb94a429033d5290a40eb54a42902be6190a40ee98242902b
  | 18 => 0xaf59221486de6388521b758e21486ee6488521eb99221486ae6488521eb59221486ec6488521bb98e21487ce6388521b398e21487cd6388521f9d4621486ed60885219f993504867d64d41219f98f504867d63d4121ded4250486bf6454121af19150486df6354121b718d504877950141219f990504867d64141219f98c504867d6314121dbd08504876c4214121dbcc8504876c3214121ddc84504876e2114121b798f54086dd63d50219f98f540875e63d50219798f540867d63d5021d758f540865d63d50219f98b540876e62d50219b98b540867e61d5021dd987540867e60d50219f583540867d6595021cfd52540867e63950219f58e540867e60950219f582540873f64550219fd8d540867c63550219fd81540867c6055021cf550540867e6415021cf990540867e63150219f58c540867e6215021db988540867e6115021dd984540867e60150219f58054086be64d4c21af593530867e64d4c21cf993530863e64d4c219f593530873d64d4c218f593530876e62d4c21dd987530867e60d4c219f583530867d6594c21d7d4e530867e6494c219f592530867e6094c219f582530867f6454c219f191530875f6354c219fd81530867c6054c21d754c530867e6414c219f590530867e6214c21db988530867e6114c21dd984530867e6014c219f580530867f65d0c219f997430867d65d0c219f197430875e53d0c21d754f430867f6590c219f996430867d6590c219f196430873e5490c21cf552430867f6550c219f995430867d6550c219f19543086ef6250c21bb189430867f6510c219f994430867d6510c219f194430873e5410c21cf550430875e5310c21d754c430879d4310c21bb98843086ed6210c21bd98443086f56110c219f992520867d64948219f58e520867d65d0821db94b420867f65908219f596420873e5490821cf55242086f66190821bd586420867f6550821b7d8d42086dc63508219fd94420867d6510821cf950420873d5410821db94842087ad4210821bd98442086f561108219f597320876e52cc8219fd96320867d658c821d794e320875d538c821bd98632086f5618c8219fd9532086bf644c821af191320867f650c8219f594320875e530c821d754c320876e520c821f34c832086f6610c821bd584320867e6494421cf992510863e64944219f592510873d64944218f592510867e6394421d798e510865e63944219f58e510875d63944219758e510867d65d0421cfd53410873c54d04219fd96410867d6590421cf952410873d5490421b798e41086dd6390421bb98a41086ed62904219fd95410873f5450421cf151410867f65104219f994410867d65104219f194410873e5410421cf55041086ee6210421bb588410867d65cc421d7d4f310867f658c4219f59631086be648c421af592310875e538
  | 19 => 0x544867e63151219f58c544867e60151219f580544867e64d4d219f593534876d62d4d219f983534867d60d4d21d7d4e534867e6494d219f592534876d6294d21dd586534867e6094d219f58253486bf6454d21af19153486fb6054d21be181534867f6454d21cfd91534863f6454d219f191534873c6454d218f191534876f6254d219fd8553487776154d219fd81534877b6054d219ed81534867c6054d21de18153486786054d219f994534875d5314d219f990534867d6414d21d798c534867e6014d219f580534867f65d0d219f997434867d65d0d219f197434875f53d0d21d714f43486ee62d0d21bb58b43486f661d0d21bd587434867f6590d219f996434867d6590d219f196434873f5490d21cf15243486ee6290d21bb58a43486f66190d21bd586434867f6550d219f995434867d6550d219f19543486ef6250d21bb189434867f6510d219f994434867d6510d219f194434873f5410d21cf150434875f5310d21d714c434879d4310d219f997424873f54d0921cf15342486f661d0921bd587424876e65d09219b997424876f54d0921ebd53424876d54d0921eb15342486ee63d0921db94f424876c53d0921bb98742487e661d0921b998742487e561d0921bb583424867e6590921cf952424873d5490921bb98a424867c6550921cfd51424873c5450921b7d8d42486dc6350921bdd8542486f461509219f994424873e5410921cf55042487ad4210921bb994424876e6510921bb99042487ae6410921dbd5042487ae5410921db55042487ad5410921cb55042486ee6310921db94c424876c5310921eb90c42487ac4310921bb98442486ed6010921d7d4f324875c53cc921bd98732486f561cc921db99732486ee64cc921bb193324876e54cc921db153324876f53cc921f3d4f32487cc53cc921bb98732487e661cc921b998732487e561cc921bb583324867e658c921d794e324875d538c921bb98a32486bf644c921af191324875f534c921d714d32486f7614c921bd185324867e650c921d794c32487cd320c921bb994324876e650c921bb99032486ec640c921db950324876c540c921bb98c32487ce630c921dbd4c32487ce530c921db54c32487cd530c921d354c32487cf430c921f310c32486ee610c921bb580324867e65d0521cfd53414873c54d0521bb98b41486ed62d0521eb10b414867e6590521b798e41486dd6390521bb98a41486ed62905219fd95414867d65505219f195414873f5450521cf15141486ef6250521bb18941487ac42505219f99441487b541105219f997314875f53cc521d714f31486ee62cc521bb58b31487cc32cc521af99231486bd648c521bb98a31486ed628c5219f595314867c654c521bbd8931486ec624c521f30c931487e742c8521f910b21487e732c8521f90cb21486be6488521
  | 20 => 0x86bd6414e21cf950538873d5414e21d754c538867f65d0e219f997438867d65d0e219f197438873e54d0e21cf553438875e53d0e21d754f43886f661d0e21bd587438867f6590e219f996438867d6590e21cf952438873d5490e21d794e438875d5390e21bd98643886f56190e219fd95438867e6550e219f595438867c6550e21cf951438873d5450e21d794d438875d5350e21bbd8943886ec6250e219fd94438867e6510e219f594438873e5410e21cf550438875e5310e21d754c438879d4310e21bb98843886ed6210e21cf953428873d54d0a21d794f428875d53d0a21bd98742886f561d0a21cf952428873d5490a21d794e428875d5390a21cf951428873d5450a21b7d8d42886dc6350a21d794d428875d5350a21bdd8542886f46150a21cf950428873d5410a21d794c428875d5310a21eb508428873e54cca21cf553328875e53cca21d754f32886f661cca21bd587328873e548ca21cf552328875e538ca21afd9132886bc644ca21cf951328873d544ca21d794d328875d534ca21bdd8532886f4614ca21cf950328873d540ca21d794c328875d530ca21f34c8328873e54d0621cf553418875e53d0621d754f418873e5490621cf55241886de6390621b758e418875e5390621d754e41886ee6290621bb58a418873e5450621cf551418875e5350621d754d418873e5410621cf550418875e5310621d754c41886ee6210621bb58841887b54110621cf953318873d54cc621d794f318875d53cc621cf952318873d548c621bb98a31886ed628c621cf953218873d54c8621d794f218875d53c8621bb597218876d65c8621db95321887ae54c8621cb95321887ad54c8621db153218876e53c8621f394f218874e53c8621f354f21886ee60c8621bd597218877565c8621ed95321887b554c8621f594f21887d553c8621af99350886bd64d4221cf953508873d54d4221b798f50886dd63d4221d794f508875d53d4221cf952508873d5494221d794e508875d5394221ded42508867e64942219f592508867e63942219f58e50887772194221cf951508873d5454221d794d508875d53542219fd91508867c64542219fd8d508867c6354221dbc8550886be6414221af590508873e5414221cf55050886de6314221b758c508875e5314221d754c508877950142219f98f544867d63d5121db58b544867e60d51219f583544873f54951219f992544867e63951219f58e544867d6295121db58a544867d6195121dd586544867e60951219f58254486df6355121b718d54486fb6055121be181544873f64551219fd8d544875f635512197d8d544867c6355121d718d544865c63551219fd89544876f62551219fd85544877761551219fd81544877b60551219ed81544867c6055121de181544867860551219f994544873d5415121cf99
  | 21 => 0x6110b21db59442c87ae6410b21dbd5042c87ae5410b21db55042c87ad5410b21cb55042c86ee6310b21db94c42c876c5310b21eb90c42c87ac4310b21bb98442c87e66110b21f958442c86ed6010b21bb59732c876d65ccb21bb99332c86ec64ccb21db95332c876c54ccb21db54f32c86ee61ccb21bb58332c875e538cb21d754e32c86f6618cb21bd58632c86bf644cb21af19132c875e530cb21d754c32c87cd320cb21bd98432c86f5610cb21bb99032c86ec640cb21db95032c876c540cb21f398c32c87ce530cb21db54c32c87cd530cb21d354c32c87cf430cb21f310c32c86ee610cb21f998432c87e5610cb21bb58032c873e54d0721cf55341c86ee62d0721bb58b41c87ac42d0721b798e41c86dd6390721bb98a41c86ed6290721cf95141c873d5450721bbd8941c86ec6250721eb10941c86ee62cc721bb58b31c87cc32cc721af99350c86bd64d4321b798f50c86dd63d4321ded4250c867e64943219f59250c867e63943219f58e50c876f4294321db10a50c876f3294321db0ca50c867f64543219f19150c867f63543219f18d50c87795014321b798f54886dd63d52219f98f548875e63d52219798f548867d63d5221d758f548865d63d5221db58b548877661d52219f983548867d60d5221cfd52548867e63952219f58e548867e60952219f582548873f6395221cf98e548873d6395221cf18e548873f6295221cf58a548873e6195221cf186548873f6095221cf982548873d6095221cf182548873f64552219fd8d548867c63552219fd81548867c6055221cfd95548873f6355221cf98d548873d6355221cf18d548873f6255221cf589548873e6155221cf185548873f6055221cf981548873d6055221cf181548873d5415221b798c54886dd6315221cf990548867e6315221d798c548865e63152219f58c548875d63152219758c548876d6215221dd984548867e60152219f58054886be64d4e21af593538873e54d4e21cf553538867e64d4e21cf993538863e64d4e219f593538873d64d4e218f593538877661d4e219f983538867d60d4e21cf952538873d5494e21d7d4e538867e6494e219f592538867e6094e219f582538875f5494e21d7952538879e5494e21c7952538875d5494e21e7552538871d5494e21d7152538875f6494e21d7992538875d6494e21d7192538875f6294e21d758a538875e6194e21d7186538875f6094e21d7982538875d6094e21d7182538873e5454e21cf551538867f6454e219f191538875f6354e219fd81538867c6054e21d7d95538875f5454e21d7951538879e5454e21c7951538875d5454e21e7551538871d5454e21d7151538875f6454e21d7991538875d6454e21d7191538875d6254e21d7985538875c6154e21d7d81538875e6054e21d7581538875c6054e21af990538
  | 22 => 0x141cf90450506de63d4841b758f521076f52948419f98e521067d63948419f982521067d60948419fd8d521067c63548419fd81521067c6054841db548521076e52d0841db54b42106f661d0841bd587421067d6590841cf952421067f6550841b7d8d42106dc6350841cf950421076e5210841db54842107ad4210841bd98442106f561108419fd96321067e658c8419f596321075e538c841d754e321067f654c8419f595321067c654c841afd9132106bc644c8419fd94321067e650c8419f59432106be640c841af590321076e520c841db54832107cd320c841bd98432106f5610c841db98a511076d6294441cf94b41106be60d0441af592411073e5490441bb98a41106ed6290441bd59241107765490441ed95241107e66290441f958a41106f660904419fd9541106bf6550441cfd95411063f6550441cf94941106bf6150441cf94541106bc6050441bdd95411077765504419dd9541106f76450441edd9141107765450441ed95141107b74250441ed50941106f46050441ded42501067e62940419f58a50106ef6254041bb189501067f6254041dbd89501066f62540419f189501076c62540419b189501073f4154041cf50550106ee6214041bb588501077950140419f98f54c867d63d5321db98b54c877561d53219f98354c867d60d5321cfd5254c867e63953219f58e54c867e60953219f58254c86df6355321b718d54c873f64553219fd8d54c875f635532197d8d54c867c6355321d718d54c865c6355321db18954c867f60553219f18154c873d5415321b798c54c86dd6315321cf99054c867e6315321d798c54c865e63153219f58c54c875d63153219758c54c876e6215321dd58454c867e60153219f58054c875f5394f219f99253c867d6494f219f98253c867d6094f21afd9153c86bc6454f219fd9153c873f6454f218fd9153c867c6454f21cf19153c863c6454f219fd8153c867c6054f21af99053c86bd6414f21d754c53c867e6414f21cf99053c863e6414f219f59053c873d6414f218f59053c876e6214f21dd58453c867e6014f219f58053c867f65d0f219f99743c867d65d0f21cf95343c873d54d0f21bb98b43c86ed62d0f219fd9643c867e6590f219f59643c867c6590f21cfd5243c873c5490f21d794e43c875d5390f21bb98a43c86ed6290f219fd9543c867d6550f219f19543c873e5450f21cf55143c875e5350f21d754d43c86ef6250f21bb18943c867f6510f219f99443c867d6510f219f19443c873f5410f21cf15043c879d4310f21bd98443c86f56110f21bb59742c876d65d0b21dbd5342c876d54d0b21bb98f42c876e53d0b21db14f42c86ee61d0b21bb58342c873e5490b21cf55242c86f66190b21bd58642c86df6350b21b718d42c873e5410b21cf55042c87ad4210b21bd98442c86f5
  | 23 => 0xbd4e529076e5394a41f394e529074e5394a41dbd92529076f6394a41db98e529076d6394a41db18e529076e6194a41db186529076f6094a41db982529076d6094a41db182529075e5354a419fd8d529067c6354a419fd81529067c6054a41dbd95529076f5354a41db94d52907ce5354a41d394d529076d5354a41f354d529074d5354a41db591529076f6354a41db98d529076d6354a41db18d529076e6154a41db185529076f6054a41db981529076d6054a41db18152906de6314a41b758c529075e5314a41d754c529076d5214a41d794f429075d53d0a41db94b429075e5390a41d754e429076e5290a41db54a42906f66190a41bd58642906df6350a41b718d429075e5350a41d754d429076e5250a41db54942906f76150a41bd185429075e5310a41d754c429076d5210a41eb508429067f658ca419f996329067d658ca41d794e329075d538ca41db94a329076d528ca41bd98632906f5618ca419fd95329067d654ca419f19532906bf644ca41af191329076e524ca41db549329067f650ca419f994329067d650ca41af99032906bd640ca41db948329076d520ca41f34c8329076e52d0641db54b41906bd65d0641cf597419073e52d0641eb94b419072e52d0641eb54b41906be60d0641bd597419077565d0641f994b41907e552d0641bb98b50906ed62d4241db94b509076d52d4241db94a509076d5294241ded42509067e62942419f58a50907774194241db949509076d52542419fd89509067c6254241cfd0550906ee6214241bb588509076e5214241db548509077950142419f98f525067d63d49419f983525067d60d4941dbd4a52506df6354941b718d52506fb6054941be181525076d52149419f98c525067d63149419f980525067d60149419f997425076f5290941db14a42506f66190941bd58642506be6390941cf14e42506be6290941cfd4a42507af5290941eb14a42506be6190941ed98642506b66190941ed58642506bd6090941b7d8d42506dc6350941dbd49425076c5250941bdd8542506f461509419f99442507ad4210941af994425073e6510941af98c425073c5310941af98842507ae6210941cfd4842507ae5210941eb54842506be6110941af580425067e658c9419f596325067c658c941af99232506bd648c941d7d4e325075c538c941e710e32506f6618c941bd586325067f654c9419f995325067c654c941afd9132506bc644c9419f994325067d650c9419f19432506bf640c941af190325076f520c941db14832507ac420c941f34c832507b642d0541ed10b41506ee6290541bb58a41506be6290541eb98a41506ae6290541eb58a41507b75190541af582415067e62d41419f58b505077b5094141bbd8950506ec6254141de540505067e62141419f588505073e4214141cf10850507774114
  | 24 => 0x420cb6d5410832eb550420cb2d5410832f398c420caed6310832f358c420cacd6310832db94c420cbcf4310832eb90c420cbac4310832f310c420cb8c4310832bb584420caee6010832bb992320caec648c832bb58e320cacd638c832db94e320cbce538c832f3d0e320cbcc438c832bb586320caee608c8329fd95320cabf644c832af191320caef654c832dbd95320ca6f654c832ebd91320caee644c832bb191320cbac644c832ab191320caef634c832db94d320cbce534c832f3d0d320cbce434c832f350d320cbcc434c832bbd85320caec604c832f3d95320cacf654c832d3d95320cbcf644c832e3d91320cbce644c832b3991320cbcd644c832f3191320cacc644c832e3191320ca8c644c832f3d51320cbce544c832f3551320cbcc544c832f3d85320cacf614c832f3985320cbcd614c832f3185320cbcf604c832f3981320cbcd604c832f3181320cacc604c832af993510cabd64d4432f34cb510cabe6494432af592510cbcd3294432ddd46510ca7e6494432cf992510ca3e64944329f592510cb3d64944328f592510ca7e60944329f582510cbcd32544329fd91510ca7c6454432dbd09510cb6c42544329fd81510ca7c6054432f34c8510cb755114432f34cb500cbcd3294032ded42500ca7e64940329f592500cb6f4294032db10a500ca7e61940329f586500cabf6454032af191500cbcd3254032bdd85500caf461540329fd91500cb3f64540328fd91500ca7c6454032cf191500ca3c64540329fd85500cb7761540329dd85500ca7c6154032dd185500ca746154032af990500cabd6414032f34c8500caf66114032bd584500cb795014032dbd4a52d067e6394b419f58e52d067e6094b419f58252d06df6354b41b718d52d067f6354b41d7d8d52d065f6354b419f18d52d075c6354b419718d52d067f6054b419f18152d06de6314b41b758c52d076d5214b41db94b42d076d52d0b41bd98742d06f561d0b41af59642d073d6590b41af98e42d073e5390b41cf54a42d06be6190b41af58242d06df6350b41b718d42d076e5210b41db54842d07ad4210b41bd98442d06f56110b41af98c42d073e5310b41eb98842d07ae5210b41cf54842d07ad5210b41cb54842d06be6110b41ed98442d07b56110b41af58042d067f658cb419f99632d067d658cb41af99232d06bd648cb41e710e32d076e528cb41db54a32d067f654cb419f59532d067c654cb41afd9132d06bc644cb41db94932d076d524cb419fd9432d067e650cb419f59432d06bf640cb41af19032d07ac420cb41f34c832d06f6610cb41bd58432d06ee62d4341bb58b50d077b50943419f98a50d067d6294341cf90a50d073c42943419fd8950d067c6254341de54050d06de63d4a41b758f529076f5294a419f98e529067d6394a419f982529067d6094a41d
  | 25 => 0xaf661d4232bd587508cb7b50942329f992508ca7d6494232d7d0e508cb5c4394232dbcca508ca7e61942329f586508ca7f64542329f191508ca7f61542329f185508cb7950142329f987544ca7d61d51329f983544ca7d60d5132cfd8b544cb3d62d5132cfd87544cb3e61d5132cf587544cb3c61d5132cfd83544cb3e60d5132cf583544cb3c60d5132cfd52544ca7e64951328f992544ca7d6295132db58a544ca7e61951329f586544ca7e60951329f582544cb3f64551329fd89544cb6f62551329bd89544ca7f61551329f185544ca7f60551329f181544ca7e6515132cf550544cb3e64151329f984544ca7d61151329f980544ca7d6015132af994544cb3e65151328f994544cb3f6215132cf588544cb3d3215132cfd84544cb3e6115132cf584544cb3c6115132cfd80544cb3e6015132cf580544cb3c60151329f997424cb3f54d0932cf153424cade63d0932b758f424ca7e6590932cfd52424cb3c54909329fd95424ca7d65509329f195424cb3f5450932cf151424cadf6350932b718d424ca7e6510932cfd50424cb3c5410932eb508424cb3f548c932cf152324cb9f548c932d7952324cb5c548c932e7152324cb1c548c932f3d4a324cb3f54d4532cf153514ca7e64d45329f593514cb5e32d45329f983514ca7d60d4532af992514cabd6494532cfd52514cb3c5494532ddd46514cabf6454532af191514cb3f5454532cf151514cafb6054532be181514cb3f5414532cf150514cb7551145329f990514ca7d64145329f980514ca7d6014532cfd53504cb3c54d41329f993504ca7d64d41329f987504ca7d61d4132af992504cabd6494132cfd52504cb3c5494132ded42504cabf6454132af191504cb3f5454132cf151504caf76154132bd185504cb3f5414132cf150504cb7950141329f990504ca7d6414132d78c8504ca7e61141329f584504caf661d5032bd587540ca7e62d5032db98b540ca7e61d5032dd987540ca7661d50329f587540cb7561d50329d587540ca7e60d50329f583540ca7d6595032cfd52540ca7e61950329f586540ca7e60950329f582540cb3f6455032db189540ca7f61550329f185540ca7f60550329f181540cb3d54150329f990540cb3e64150329f988540cb6e62150329f984540ca7d61150329f980540ca7d60150329f992520ca7d64948329f597420caed65d0832db597420cb6f54d0832db553420cbcf63d0832bb58f420cbcc63d0832db94f420cbcf43d0832bb587420caee60d08329fd96420ca7d6590832cf952420cb3d5490832b798e420cadd6390832bb98a420ca7f6550832b7d8d420ca7f65108329f994420ca7d65108329f194420cb3e5410832cf550420cade6310832b758c420cbad4210832bb594420cb6d65108329b594420caee6410832eb990420cb6f5410832eb950
  | 26 => 0x390842eb90e4210bac4390842bb5864210aee60908429fd954210adf6350842b718d4210abf6550842cfd954210a3f6550842e7d8d4210abc6350842e718d4210a9c6350842afd894210b3e5250842afd854210abc6050842bbd954210b6f65508429bd954210aef6450842ebd914210b6e5450842eb9514210bcf6350842bb18d4210bcc6350842b318d4210baf4350842eb90d4210bad4350842eb10d4210aef6150842bb1814210baf6550842abd954210b2f6550842ebd8d4210b8f6350842eb98d4210bad6350842eb18d4210aac6350842e318d4210a8c6350842ebd4d4210bae5350842eb54d4210bac5350842ebd854210aaf6150842eb9854210bad6150842eb1854210baf6050842eb9814210bad6050842eb1814210aac6050842b798f5110add63d4442eb50b5110ade6394442b758e5110bad4294442ddd465110a7e6394442d798e5110a5e63944429f58e5110b5d63944429758e5110a7e60944429f5825110bad42544429fd8d5110a7c6354442cf90d5110b3c43544429fd815110a7c6054442eb5085110b755114442eb50b5010bad4294042ded425010a7e63940429f58e5010b3e4394042cf10e5010a7e61940429f5865010adf6354042b718d5010bad4254042bdd855010af461540429fd8d5010b5f635404297d8d5010a7c6354042d718d5010a5c63540429fd855010b7761540429dd855010a7c6154042dd1855010a746154042b798c5010add6314042eb5085010af66114042bd5845010b795014042d758f548cb6e62d52329f987548ca7d61d52329f983548ca7d60d5232cfd52548ca7e61952329f586548ca7e60952329f582548cb3f6455232d7d8d548ca7f61552329f185548ca7f60552329f181548cb3d5415232bd984548caf56115232cf990548cb5d6315232db988548ca7e6115232dd984548ca7661152329f584548cb7561152329d584548ca7e60152329f580548cb3e54d0e32cf553438caee62d0e32bb58b438cb5d65d0e32d7d53438cb9e54d0e32d7553438cb9d54d0e32f398b438cadd62d0e32f358b438cadd61d0e32b7983438cb3f5490e32cf152438cb3e5450e32cf551438caef6250e32bb189438cb3f5410e32cf150438cb9d4310e32b7594438cb5d6510e32e7990438cb5f5410e32e7d50438cb1f5410e32d7550438cb9c5410e32b7588438cadd6110e32b7980438cb3e5490a32cf552428cade6390a32b758e428cb9c4390a32b7d8d428cadc6350a32cf950428cb3d5410a32b798c428cadd6310a32e710c428cbad4210a32bb597328cb6d65cca32db953328cb6c54cca32ddd46518ca7e64946329f592518ca7e60946329f582518ca7f64546329f191518cb5f4354632d710d518cb6f32546329fd81518ca7c6054632af990518cabd6414632dd544518cabe64d4232af593508c
  | 27 => 0x429f58e50d0a7e61943429f58650d0a7f63543429f18d50d0a7f61543429f18550d0b795014342d7d4e5390a7e6194e429f5865390a7e6094e429f5825390a7f6154e429f1855390a7f6054e429f1815390b5d5314e42bd9845390af56114e42bb98a4390aed6290e42eb98a4390abd6290e42eb58a4390abd65d0a42cf5974290abe63d0a42af5874290abe60d0a42bb5974290b6d65d0a42db94f4290b7751946429f98e5190a7d63946429f9825190a7d60946429fd8d5190a7c6354642cf90d5190b6f42546429fd815190a7c6054642b798c5190add6314642dd5445190ade63d4242b758f5090af661d4242bd5875090b7b50942429f98e5090a7d6394242cf90e5090b6f42942429f9865090a7d61942429fd8d5090a7c63542429fd855090a7c6154242de5405090a7e61d4d429f5875350a7e60d4d429f5835350b5f64d4d42d7d8b5350b5d62d4d42d7d875350b5e61d4d42d75875350b5c61d4d42d7d835350b5e60d4d42d75835350b5c60d4d42d7d4e5350b5d5314d429f9845350a7d6114d429f9805350a7d6014d42b79945350b5e6514d42d7d905350b5f6214d42d75085350b5f6114d42d79845350b5d6114d42d71845350b5f6014d42d79805350b5d6014d42d71805350b5c53d0d42d7d4e4350b5c5390d42bb98a4350aed6290d42bbd894350aec6250d42d7d4f4250b5c53d0942f3d4f4250b6c53d0942f314f4250b4c53d0942d7d4e4250b5c5390942e7d4e4250b3c5390942e714e4250b1c5390942ebd4a4250b5f53d4542d714f5150a7e63d45429f58f5150b6f42d4542cf90b5150a7e60d45429f5835150ade6394542b758e5150b5f5394542d714e5150b775194542b7d8d5150adc6354542d7d4d5150b5c5354542bed815150af86054542d7d4c5150b5c5314542dd5445150a7e63145429f58c5150a7e60145429f5805150b5f53d4142d714f5050a7e63d41429f58f5050a7e61d41429f5875050ade6394142b758e5050b5f5394142d714e5050b7b5094142b7d8d5050adc6354142d7d4d5050b5c5354142bdd855050af46154142d7d4c5050b5c5314142de5405050a7e63141429f58c5050b6f4214142cf9085050a7e61141429f5845050af661d4c42bd5875310b5f5394c429f9865310a7d6194c429f9825310a7d6094c42db1895310a7f6154c429f1855310a7f6054c429f1815310b5d5314c42d794f4310b5d53d0c42bb98b4310aed62d0c429f5964310abd6590c42cf5964310abe6390c42cf54e4310baf6290c42af58a4310bac6290c42af5864310abe6090c429fd954310aef6250c42bb9884310aed6210c42eb9884310abd6210c42eb5884310aad6210c42cf90e5210b3c4394842af98f4210abd61d0842af9834210abd6490842cf9524210aed6490842ab5924210b6e5490842eb9524210aee6
  | 28 => 0x100010013000001b0004001002802c0018003003800300000000000010000c01f0000030007c001001c000000c00600100000028000000400700040060004002000c00400100010000000003000f000403900040010030004000c000010801000100040000015000800e00780010008000000800600180030008006004000000200040024000001800700580010010003000c0010008000000000a000003f000400100ac001001400d004c00200200010050001000802c000400000240140008002000802d0020004001000f00140010000000000000100000010010005000401600200000048005000000200000030008008000000500140040034018000000500000010004007001400300080080000006002000900000000040002000000100000010008004001c01800700050068000001800200000180008012000400200000050008000001c00b0000001008000200040140038002000400b006c00100080200038001000000000100000004040000000300180030008001005c0030024004001400400040000024004000800700000040038016002400100840030094000006c004000000000040000020000000c00000140060008008000400100440010008001000003d00040080000004000800600180000000000001c01d000000100000000004003000000e000000000000000004000000c00200100080010003000000200440000000001001c000000c0070008000000000500840010008000015c003008400500040050010000000800000a40030000002000c001008c004000401300080020058001000800000000010014000001800900000040010005002400900000000000006002400a000000000040000048007002c0030020000002c00000000000008000000c000000c00d005000600040010038005000400f0028007000c00000080020048000000801b00080000060034004400c00000000030002000400300180000000001000400f000c001001800100080070000001000400000040040000000000002f000000000400000008001000000f00000000018005002400300c40020008000000000000200020040000002800000000140020004000c001000000800280070074001003c00000240000070001000001b0004009005c0170000000000400d012c006000000100000050000000000400c0000000000400400040030010002d7d4e53d0a7e6194f429f58653d0a7e6094f429f58253d0a7f6154f429f18553d0a7f6054f429f18153d0b5d5314f42bd98453d0af56114f42bb98b43d0aed62d0f42ddd4651d0a7e63947429f58e51d0a7e60947429f58251d0a7f63547429f18d51d0a7f60547429f18151d0ade6314742b758c51d0b755114742b798f50d0add63d4342bd98750d0af561d4342ded4250d0a7e63943
  | 29 => 0x80000000004001801a00b000400140080000000004c00000040090078000000000300e800b016c00100240000000020000000600080080000001000000c0030005005c00200140000000000000c006001000100000050008000000400c0058007001c0010000001000000000080000000010001c000000000e0004001001800e000c007001000400000000008000001400200040020008000001c004002c0000030008001800900080040008000001402d0000000000800500180000000002000c00b0000000001800000400000018014000400b00240040024000000000b0004000005c00100140030000000000000000040010018003000401500200000004015003000000040030000003001c00200040000000004004c002001c000000000700780000064018000400600000000004002005800200200060004000000400000180000000005000800b0058028000000300040000074000000000700000080004005000400700000000094000002401700040000004000001800100040000004000003c00e0018001000000100000040040001000801400040050000029000800100000110000000002800c002000100100000000002000400b00980140028006001800000000000000010000800f0010000001800000140130000016001000d00300080000028000000b001c00300540020008000004000a000000a000c0020028000000000400100510004000000c04000040020028002000c009000c0020044008003800c000c0000000008003001200140080000004002800100100000044000000000300200020054002001c002000001700000070000003000800000600010018018000000000200030008002001000100040000034001004801c0008007000400700140040024006000000e000c0060000007007800000080060060001001800000080140004012000000400000310000000000000000200000000000001000100000000008019000000d000401a0000001005c0030018008002400200080000000001001c0030050000001000d00540000000007000c0030014021000000000080070004007000800000040000024000000000c000800e0044000000400200000000030001003000b001c0110000001000400d0014002000800f0008000000800000000010000006001c00a003c00600140010004003000c0080004004001401000080000014000000c00200380030028000003c006001c0050000000000001b000c00000000010008005002800000200020018001001001500280130018000002800b00040010034000000400800000000008000000801700940000014005000000c000000400cc0020054000000c0000008000000c013009c0060000005002c014001c000000c000003800d0004001000801100000090000
  | 30 => 0x80030004001000400c0000003000c01f0000000000401c001c000002800c001800000000050004000000800400280020014000000c0020010018001401c000000d004c00000a8000002000100040000008003006c001000000100000000000001001400000ac00100140030028003006c013000800400080080004003000000200140000018025000801400000000018000002800100840000020002000c0010018000003800f00000030000001000400600140000014019000000a0008000002c00300040030000000002400000240010010003001000100140040000000000001400200010000020000c00f006c006001c01900a800100100000020004000400b0014003001800000040090024000000001100380000010001006c00200380090000005000400000680000058000001800800580080000014001c00000280020010000000800e00040090074003000c002000c0000000007000001f0014003000000400000150000001007c00d000c00e0038010000400d002c00d000000200240030050002000001a00080020074002000000000000000024007000401a002c0100000003000000200040020010001000000f000c000005c0070004005000000f001c0010000000000802c003c0020008005001000000000000014001000400a000400000480020008004000c02a001c00a000000100180000008005000001b0000000008c00a000c00000080020000007001000a0004003009400000000000004000001c02f00240000004015000c007002000e0048003000002f00800130020000000400000240060068000000c00d005000200080060004004000c00200040160020009001c0020064002000800000380010004001002401c002400000000010010006001000300140010024008001400b000800000180000008000001400000180050000000001800600300010008002000000300a402300040060018003001400000000000000029000c012005000c0074027000c0020020000000400c00000000004015000000d001800b00b400600000000000059003c0000000005000000000340020008001001000000100020020000000800000740040004005000000d001c00e0044000002800000000020004009001c02d000400200d800200040000000007000000c000000f0098000005c000000c00000000000028000000000100040000088000002400200000020010002003c01300000000000000001801b000400300680100000002000000e000000000400000000002000002f00240080004001000c0010000021000c00200040070000012000c009000c0190000011002c0010008000016c001000c00100000010074004000801b0000003000800500540130000004001800c005800400080000034005001c008008803d0048005
  | 31 => 0x2006400b000000a0000003000400100000000010021004c01f001000300000080010000001c012002400500080140000000000000100000010000004000c00000000000020003000000000140010000002000000900040000064000000000e000000000000000010005000000000580110040001007800100080070004005000800b00100020010000003c005001000e00200000004007001c0010084000004400e0000000001000b00040010014000000000c00000250008006000c00000000090000003000001b000c00000180000000002003c007000c01100000040000012000401600140030014005000400100000000030003003000c0000008001c000000000d000c0040004006000402100300010004000002c00200000040010006001000500080010004007000001a001c003000c00200040030080008000000d0000000000c0040004000004000000000010000037000000500000070004012000c00000140000050002004c006002c02f000003f0048006000c0020084003000000500480080004003001c001000c00800040020008001000002500400040008000007c000000400000040000000001000c00000000160000002002800e0038018000c003001000a0008000000000f000000900c00050010001003c00300780020014008003000c001c004001800000000000024002000400800000000024001000801d003c002000c002002c004002000100000010000000000800900000040014001000400e0004000000c000002c00800100230018006001c003000402e000c0030024005000800100080040034002000c004000000f000400a000400500240030028006000001d000400800000050000001001c00f00000000008003002000300100000014000003800400580020028001000800100400080020015000400900000040018012003000000dc002003c001000000f0004000000c0090098003002c0060004000000800200000270004000001c00c000800100200020000000000800c001c0000000017001c006005800200000010000001000000e00140020024009000c01500040150000002002402f00a00010004000000000500100000000001000800b001c000001400d0024007000800000400060008015000000200240050008007002400b001c00400240040028015004800700300000028001000000d00000030004000003800d0008020000801b001000300100020018001008c005000c00100b800d00040000040004000c001002c00600840000024007003800500ac006002400200540000000005000401000280060050000001000c001c003003800600440030008002004c0260000000001c005001c0050014011000001000140010010000003c00600b000000040000000004000800000900090004008000
  | 32 => 0x808921b9224a699000018380000001a28a28a5c600008700000ba00002b907f0873800000006f48e860b2a22e7b2aaca469982a6b2035a9cdab484d3a3f00000000000000094dde54000000069caf2269140005300d9763f925600000009018000a204000a098000a2200000002c5a7340a810002dfe868000030b8193715e0e02e9dcff744854e45807ee8e9ab24ba5016097aa0fc1625fba1fc1ed566880004f5e458754a0982241d8c95b098e557a7fe00019958c64a9a695c00023e000034a2d1a2018d34449a4421970c38000086e00013fe7310c6f435850c4b48c4d18989a63eb020eb1c9bd80001672469e24487518de6c840000000f3c488800031fc000000000014b816a00000000000000000000081505d616e0f2c0aa9d4818f601c07540000000000148400099d96d9535caf741004b112e4c2cb9c96ba00007445b9286aae814a429b54b818a1eec750488073b00007c2eee685c223e70ec14913c07be9a183a10001c4c5a7af607038000923176b4ef2824a5400005cd849ea3467b94b280008c094927ba1e354ba203c02c400030754ea00000002e01ccc3a60000743270bba2029d000075c8d200008a406ad8940be016480001bf033c137263cb68c000000151c0002462a199982a9c23328240ba124f08323462cd92ec88260d1817f07cd05a7d08f509825fe6346439c71ca8dc29191c133788562961452182dad00000a40ac60468a8e5f220001ef200008cca2d18c254003fa0002b7b0000009005400000000020000002004800100000180000014004400100040050004000000400100480010008011000800d0000025000c0100010001004c00000140000004009000001a00140000074016000c00d00200020000000000000200140010028002001c000001c000000000b002800c0000000000800400000000020001000c00300140040034003003000000d800400340210000000000800000000020000006000c0010018001002000c0034009000800000000030100011000400000240330000002002000200080050028006000c01a0008017000000b00140010000008000c002001000000040000000005001401700080000000005003c00000000040024027000001200080010084010002400600740020054007000000100040010004019001c000000400f0080000001c000000c00100080100008005000c001000c0000018003004c005001000300000050018000009c000000000200000020074017000402400080000004004002400900000040048002000800c0004016000000d0000005004800000040010004008000000000000020008003000800000300000020027000000d000000000140000000007000000f000400500b0007000000800100010004001000c0030004000004800b002c000007c019000000
  | 33 => 0xb6d80000002e9600246b3860906e74d034d15340002ea8630250aa212ad000006c1fee24a65bc0000000815e527b6ce99e46614f24bb60c810e8c56ac8e3d067d249e208a40a000000096788363c680000c42ba20001c7010f8cd00eb80000002a4a80b23e81c4800010d00121608858000000000023822021bf127c00000000000a418000000108c6c60000bd88212a46aafc2caac20575805e2c90304000000031b090e4e4878d111400029e000001980003742db8318a1644ce13be036d2350001ea88d72efa00000002dc821d49d103caba20410000000000154a0001852709a37200028174fbc000147a7300c68000069519e00023a106998a83662b665ba66961740ad23db2cb622ba02303e8e56500967f58c400089d53567c2895c7a58746933ab9e519469c000026a000000000019e900022b48e026200000d8a1e7000032905b249e800000026d624a82a10001b68000000000000000a000000e4c000b18e6210001af40dda9a69d92bdc3790eba914986ca75800038ea1187fe18065432c3489d116c25aa062540e5b04aa02600a3a3c43af0d1e81797f03a2088c060c0007231f583d1a6cc000214d1ac236e2b883b0000000014480007f10000000000058922c7000233c757800034299e8710ab5a00004e60f0901a56a8a379fa946c3a686d8777a6aabc60a907ff0acea9cad8db6329e4abb81d241bee5957b89501a5813aa97956c106866e5cf85dcb0d4b91326af4c04b953499e0b542e1c4fa6fe1216bc1220277e2aa399227402222786765a055b312a667b79ff687200003700216ae000009bd9b90a8480008b9a8429a9ac9843e0fcabcd24a216ad7683d3c0009dfd236365a44e0000000b5300006c398460000000a0e87704e39ad70000662000092861dd37240782dd6d40e169c696900000000aa4836c59404690000f19520800045710ee0000000000257e58f0000000159c60eee4e135114c57780006218000000282a000122c0000000a5e00008c20000000272851543642c49bcb0001729b0a98580e09e3a8c791560001074157e96a81d16cd14000000000ab01f250ac4978340b7c066638a178456ae5520000c24a612d24424a795363ebe4000000000000007a15fe86a2c00035a000071600000000342079092700029d755d80000001ae80ab87061d4d4e00079c22a258000000000000016d83260000195a3f8a39a05f970aeac0000000000000000000005a9128e13640004368000a28c6361a75aaa17b0000000000048a1c065d0892e56a2d765f300000002d9e00000009b76804a4503c388425e2000206b2421d3e0000000000000094080002664eaa85f2bc0b0795b605e96e12bd1cf29c1a1a89df660794a182605784ea00011344a88000078e7e2956199e3788000000244800006e815e80005a95e08b5
  | 34 => 0x264500004480000efe000110c0000c9002e8c91677000014eea324b9800034540000478ab2586e7f6786012ca6a0d1470d05b455405e01bd9fac868a7581739d9e000020003a26bc3d2142a49213a00d80f5470e58a40002e9800027b721027870b9ac4700007f81ea15245d880000bf0da6bc3a3cc36c687f9ad11b82f79a463f50f0a58989c464812e07d812f05d3aa8067d9b34000000000016b4316cee862b140e93703585620fda314075186e85c03b780fe95be18a07b165a758a83d3af83d461d06a45e300bf0a68ef226a1e0c23dc70019910f2b19a7a0391c0006d380008250d33000264c23711b268aded00a1053842f881b49aa14871c487c81c0f5106408f0287aca6b329e22a7b5b1070b4cbc34c800018ea47a9f125968361d466fc0a02123614e483ae44af8a4adbb384c45cc80001034000000000041040008b2a0175ee1e701d32936323943c7b98d2c0001582847a460000060c808467a0002883a63100c25882bc9ebc00097c84cc05c99f04ca00002c1400040b000000000009619b4c044504ab5519e27782f5a8d089725dd9b4b934a8f40002028814167e00018ffac720149f84a5246cc9121fc91e684d90c06a2667b000000000010adbae167c7bb8abe000234e0000c5a486854c1920000855400000000000002974b2a0000348cd22791882411685877b00c8700010b26cfd8726ff2aa4000059b79e4b8c5b38b1a000231c5e16f3604680003d91714550250476c1f4a4298624b08917270aa1ae2988bba8f2aa2081d65da0df612178fc000949a9a251627ac9f014c4b2d2e2c000000000021880000ac4049998e338800000006f0331c0000002b708528e3e09594ae5c280006090000b134000b47876cb859a5206200000702b3ea569be19e9ae1003299a01ce84201f7a5361598000a3a400058700001018000417242a699ab3f8ef00000001e620002ed667a800061280009be000000006aa8302de26fa000028f000087e82b63898000000278b5590230052aa640f82107ac501358aaa137102a139000000058b87e45dec00000002d400006371eaa93c02bc3c85ea22a0164208877f279f4828dec3281d060001d108e18000a1526e300018b83ed000082840008f3ad56000132a57e9dc09ef603973f1c64664dd451e4a02e42f2f5810892ec6478000b84a20c34b42b5a2981568819a554eb8dda5331ab800001820002d38000000093a917469e81e70000000a854000000000000000008d01b2300000000000e547de1c84b0dc000000000084c4018bbf8000b7e10080001cc8a85e79c67626d19c4ac51000202a00020ce17cea980b5a6140e1592faf1937c8c49ce81e8180a90ea36a588c7d1000000000019648e90c06a238000128000026218d600000001b5800052801152b315b253c643c029000053780
  | 35 => 0x42400006570194e6c3acaef242080004e8800017a122eadb1e2c399000086a99e435b546797e00006182b0a90ca3b00fba27a1f52c19527de9c03ac0000000000000000000003d700026e5b8c8000a812c1f9226577037daf301a8312000000091c82ed5000b745dc00007a6000000015389c1e3aa9d5227600022ea0002be809a400013a0a5c00000000000000b22800043700008ad9b41058442845a000036f4b2c00000008428000a7141ad35f800000000000001a262bc4b850001da694f997a2a0a5cc51840000001d842a783a0000233879681865021d4a8b1881809b9694003ec8e00020296370bfc012ef160760509000000000021925ac1a4300018ca089a18c0002c9ab950730a5f0000154a0e27a95476000071a00006c663314e416a59c47a98df602b2a1d4f8800091a13829f6a466232000000000002bc000036bde8a9326b377d222886dade4f34e13d66c5948f0f967ca4a5ab462c5086a9440000a0d0000b1b0c1489c4b3061dae649a02c1800002dfb7298368ac27383c429c3a71e168a31998a000112e9fd00004239a4eabfab52043a30b9e00000000000062d00008cc000054a5f4eac4c0000002a2cb03a9b631312b697d80000001fb61b31c360000cc8964a0776e8839a3eb8000000066c7e4933a95649e6000000056e9dd2000244c627a55b2c180000001c828b504aaa2300547838d7d46001c882ec01aa9b9d5a5605f5c4e18000b281db600008b0000055a4240000812000000000007224000acf000000000007e88396a814e7a5439954bd0108000000004d49dc45b58000bcf1a8322b4000121a0760001808b2187155131e4d1652660b762c7a0002c3b32a00001cf000040800002e50cea0001aa9bccaa88000000025b0c6042600003ab823c45d9616878208600015f402045e2000000000000007900000b64c000b9997d200003c042d26cbb53800000000000001be087183e6000251c3cc277b8031caa36e436a64d27e07792b72000271c9f9097409f9fd28e7124c55d2c5482080004e60eca71112900000d070000000b0f800042e0b5eb638000000000082a15221ab800070344e2000155a0001ee7a7300002c3c510ade00000e00000995def0b8a800030400009c0990e7a9c0009e583204de2d9492bc00018b800017680004f680009fb078c5884c76ba729b29a280460d50000a6500008659c9880e800000000000c9800000000000000000000000000016422938d9c83e12b70002bb89b14000038c5206f22b875db94200001aeaa268000000255074100005aa93643dfa1410d3ae9d4f3000000016192c300002c99b8716286e092658540000574a94c00001600001289e744c500007978000220800000000003120000ab906a800025160001e6700000000002564140c000000000000013c021500000
  | 36 => 0x7890000410c0006c4878b00019880001aae02128e23f30c20b0b9a100a708ca0e1c1b42990d4e1f706e21e127a8987adb405a5a4c6121d572d5a784b9718003681d8a70a559844780c72ff8b933939b825b2d7c042a1abc29a0743b9e9d4da01a7ab5191f060846d4005423f49c95c3a6dc04769d729d10a88000bc789f85eb0b3200b946a9ee1c9c8d78d5800000009b700000e98bd64ab000098c16560000ec2000110e03e2329202a07a60ca8e08481a409b657886a8550545ea34500025ca550800000027c64518de0000000011c80000e9010c4c3208c00000004fcacaa30d153c02aa3600001e1e0001124b73abac566c00000009e31eb4000b57000080340000fe2bca75e800008a000059806de64a80009051c47000292847d924540d40005368000b4320a74fba726ac12f5094c2e845b1c776406139a2c25ef900011e72c7120cb0e4274480c0000f311f43f1923a00010767ceebfabc70f7c0000000a501f5a0002c1a88e000040ba0cc9fc587c41300483209278000000c00009b69841f24b711cdc667ed9d000000077c800052d042e00009c60002e8a000145c2ef5a657a0c000304a0a683701258af8000000038d4522dea43a2a196fa8ee00000255afda7890001b5a07324be0000424169a734000000012462ac9badd4e77ba13e0000b0204a8fe6ad60720822a53893e800037640002a38000000229e599800000010c20000a180001ee2067425a4aa9cae85118e2269cf68318dba036b4d744a1986e000000018480000000000a3a8000000265b4c000000ddc0000001b8000020837a44e1e92a9f3eb68a20829f95868eb188890080000001d3d5d94154000037b2aa00003b98638000209600b01cb3e400009bc18f006d8a808acd6de4f518a60c6105e1038a5300006a200026a0147400000000004378000b69d02a6f91a3a0000f1cac394fe63b22a60ae6dda19f65a275d5e3e561d32e1be24267a918948c52d46bd1aa8e9cb035666b550b54b1966526c7b459badc0234c86c48724c7aea800006c838e3880e1c0822d3c0b6a19350713944e14000addca3e00000007e9903e4c600000fd8000ac0a8c80002cde86f8000b7c8000966107e6ab430b98911a029fc4eb1944000381000000022a100029fe6a721fe0001144a25000094d27be00000008c7d2cc3a580008950152000000000029f97f2867c00000000002709714aa480ce0d5e000230e4f26a3a20ea4ec75d2c300f196f8a18179e2fd8844b5e2e50aa2a94e789a57676001f2276100a00000000002dbeaa700007a68000857a2de09d931692e1bbe7f320876d4800000000003f400003ff80003f70000a1f8aae00029c20aa0dee4d801a029d9b7800025320000ff8b66d75eaaa2e1c00000000bb80006cd913c000265e65d000055210f412558a044e98f30001
  | 37 => 0x291809102f19f42d621a221355e613b0bbe5d6e93e29f39a69ac568085246199dbc7cea84081ed68692b89b05c19f2c70102e25b5eba40ee868aaad254200025b40001e8c0002ea6a8f800000012f60000ed60000000000157a000254e0002d958e3854887b0c8a93500005a040000000000000000000000000002b8e6b36af203f4000b4618ae49f8db400029fc2e41a987008ac20000aa6b9f06e1af32334301164e00022f6110ab201af17044ea2e78af51976a0f0b8d6b4c61c981074a4d50283ab3acee27810000001f7eb7b00005bd094e0000000ad41c186eccd106c300001a318be8c600005dd13e8523aa83000289e0001532849cd780001426adf02420472ddc00a8790a410a3889980005af80001c4000034480821a4c84e7ac9fea6249f3d19fc00076200007560b9e00000000002ec67bfa0b02121470780a4cf20a8dfe22ac4e45e816924340c5eb5d4384123a4e895215bc16a9584bb21da040d80001726640a8b62bd000168ea818473a64191895580009c2239e35425c8aca800091c115ea40a3e61888fb63e494d251bdb0a4f9c67e0001698516858d000000000007890000d000000c4471180001f3876227d034ca9269fa2268000a72600800207821ca093482b0ae684940006be800000004ba00000003c784b20001f040cd2bf05949c012aaa6129ad8b9805a19e127420aa00000005791332b3e220e13b80003ad01d31ad1abe7136aec6cbd720722132c0000000292800000000000000000a3c8909000108a8b56bd600000003c026707ce1f6a289eb3b000000039105070000000000000000000004780000000000000003d100015beaab149a5b50000005800000017104b780006ce000069a84970149689a6b0f320001f9823c851fb898000a5797481162a9ab8d247852e8af2b8182722cf2dd4816a12c58501ea0ad21120001ea9011417682a482800019aa36b0bf07e320e43c305765bb0e786b78a8c7aa91baac6c8ce9af90932b2914029ad2199df10f655883be8872572566a500aae067b112a130990c57887c27de43f1e4e0138ef4afb4722bcb1ca80d107f451eac137d901f04b0245a7acd51bb008baca5c9e1a92480001e9c492356851a187d89683401f80601cad79c407268900008aec0000002a070000f4e000000068a9e5d819c078ab6073f2912d2000001b850b262c37c800058a2982339000000000003dc80bc000000034e481a0000000631400053e8fd661cc6dc1c4eef7336991000000000002efb0b4215a1a9aa860000b7eb4c0678506874108f91ff36880ea5f5165c15b1cb6000076576b80006080000067085e0318000851c0002b42b94af6000000000ef0002e02728023a00008e49ab9a290000000792800020b0000857216c7df6bbc6adecc078e015f8b329a0000000003c29e83d9980e
  | 38 => 0x3c19b9a4c79e5b8f780000000797ba000000000bd2b14800000000002758000000000000000003202e769f989367da0518487834a5408c705d68f2768b84d89218d3a973920233027184a200006a14d2a47c09ab70b05045a28000000000075080009519ed40000000000000060f279b2cd97549eb82d13dd1f62a062efcabe8a5d00000001ae800049a00005a65add0001b72893804254da02728c02e000001b5608cbce6cc40000dfc39e4629ee9907972f000259069fd51a27685feabd21c05f2985183591c327ba5aa23540004f9530eb40044e57e05f04408f7a408a324baa14ef1e2a0c40002da020b8f44b25237033d844c8d618792f20000016985600002042a90580516c7949a3c74811ea96069c2152000124e9a4097e780079e295c00058893440002659677d67600000001bc81641ed80007a52dde25a193082684e989c820a66b2eae6d1a4b696704360002b2d729274cb56801000000000001ec11434a845caea437ae18e981f95f6926800019de0b813c4b6433bcb959d3d2c81bb8b5829b28e48da0e9e1ce4dae38b1b5ca77aa094b41ed77cf2cbc34091705a68f459336ef60915ac200000003588cb8960172c7829a8000000005d2a5d6910000068dd7e8000041cb0ac00015a555200900000002a65a8c0000a2800008d4c368171a78a3f4a298645a732452aa84b6f0000175de44000000053599909c1213400000575fb9a905a727562a280000000cc68811f0fb6c11305cb8dbea14848943f8000bb02e4071812302e728ec47e22ee02cac1618fad040002d2aa7c8bea5be80004599b887b140cc0340b1ea7d800086d14302e98bebb07523cb181078895813eb44016d5e680000391ebc3a9874e6408a3a14be80d2c0611500000008ed0c1670c95f2000000000000001e3ae6216e54b00001c1a7a80000b6e4df451c40002bcce724035bfe00000000001e68ad50000000000000007450002c3a0002aa50c58de5b124b86b5e94dd0de4bb4000000000000007bda720b01042c7c4a4444250000ad0c9785c2134a0002c50766ac709c3800037e0f8e0001a1e00011360000c4a994a90e52723549b52c566ec822c69b11c0a4c24ca8ec9d20679931010a88fa959a58e2ae25aebb923b666700002319ab50000070325006269080005a3c000000000000000000000000068800000018e4000000046dc00000022140001e9e0441aa2b686f4d00000000000000000146800011908ce93f6542000052a2c8400026685b800008a8800006b2ed76982da80000000b8f8000000000058b000000000000000000b07000011ac0000000daa3f8163200021140000f9e3a0a7914c700006ab1dc87c79cb05ef16eaa36af0045f2ce0a7dcd43b42037c745e4547cdad701822b822f617ae6fd15f05ca28d400029b88088d379d6ad0e1b4
  | 39 => 0x335800000005320001f231cec37a196000074caaf000000009e7856a6444b4816f0f4200000007fb00000f6abd28c2a4ab00002414b900000001d5500006c2828ce92acbd5c02f980000000b180c7c00023d00005d327b223a82b336c0bec58800000002e04af4000029f0cfc906208f60780000000000364065244a28b0b930000bae87ab393e3315ffc0005c7892f58000000001f560000adc5d70b6c00000000001fc09a31e6f093211a000000000019e014f299c4d70bc72f094f086e04d287882921ac5fd8398a4a630724129bb990c6a19d6f5241cdeb649a7e3d0cd721fd800069d000086981fe000022250490648098e2a000236218d23a03cfa3d22ba879813f8e686468c7c183d57e9762e46670a7480270000747c00005200000002a740002ccc7981100ab30a2536f15c864f80000001ba66b24000000201822b0f2300028505042a0054284c21df9ecc85e69760a9149868e1b425ce25390000000b6a80006041594aafa25a2278522ac98f9671212d6661048232d13de2459968135c5266d15bd6a2e9a34000000000005ea2a6c0004708000719ad42b322966000095e302006433a002d14a0ce6afa9ccaacd00d90000f203c9422e5cea5ee000285c000221e0000ba800004c700000006758000000000000000001f3000000000000000000000224614a815a1b7c3d60001010815a23a0000000000048b000000000000007e100004da80004e9800036322ba068e98000021d000000000002d6800000000002d770001d222d30cb209a240034149561a08e900000db300026ec0002de65c68ad48791a27b7414f483d281a6360650697188772c8876666ace263aa1e68c59956231064613ddad2b642856000081900015fe38261c70001a628f007880f3e4da836a68873080000000fb84b100776d5937e167064b1d980001d1de8f11a8000218000000024d604619600001fb2034826401f1108b1a22183891bee0000ca6000000000005730002812000037498e206aad0a6017b809c84c92d6674a1b6e000000017300000001ab2461000000013c2890000029c80009b840000002e8c45fa644000052c3b8a67d9740c22000000084a0000000043c000000072b21580000000000009216d80007c714bca7ba6fc00011ab34fac2595e948188d893f1a3800000000005146be000000d600000007bf4ff202d00005f200002789a77216ad6a8cfd4055b066c02548000b30e3fe0000000a59ec7e1a5e0970000ac0a73d3ea11f13408279c41053025eb1388a69c30000ae202610000a0cb35294c9db15588bf80000000000869022433b867601580504d98def0052e005118a50310242e0bb19fc7f90000a212e3800019b5b8f1ed88410ec69b3d7582a1c059270aa628348a48000000000000000000b8800000001826547000000
  | 40 => 0xa3a1e8d25349161f000295415c6a4ca1ac0000000000000294a205a4567501e326d1cb0ebb11a360000000b4500006e52cfe000000000014af8c105ca0000000b470b625ff12e223618c426c868466ae08e10780447059dea6288000212a6b0926234a0cca8868a49b96000093e71718c15769a7b52c933cb920467000131a23f40006b3c000351000000004649dd0000000156e76700000002b40000128b000000098300000000000000188c0000000b09c00015911d41802553b8dad3400f80006bc0d4800000008c81ad1000076e9a0eb419be9d668d5800068940000ed16300002c9c00019321e5a0e87154e8411593886819bc414d8f3400016e8a8ba5147abc000bca800000000006e1876a42581b902e08b874b00000d706353aa2dcc999400000000003ea800000001dc000000036d970c0cfc0000000023000265a9da91a831743144c8000001a00e60375312000145402b8b4ea00093912100007639c1e2380470b4dc0006ec000041080006db2ad20002c926ad23ba71f000082ae7820002a6a0001d6d1bc41624f400325cc4000000000097f1b26266800033628be5bb80000001c8e000000000012fe06ad6ae000214600019d000018845a823f22651f324ce426c0e184e002f40006588cf07bf1186328a6180a61e474b090243a525a69e507a909e2a4b4a72dfc0001aefb34030c4cf98535f080007732ad0000246c1422ebb85413ac1d581a81b1240c80783529a5de723b10bf868150022528c26000000063da0045db5d9000000000002e9eb4e61268ee163e9bd00007ada222690594c95708f37e91e421de8000b1d13c4baf8198ade65ff0000000ae601e00002d8200018e879b593875f800000019fe9380e020f8c22b07dc778a9a000013840000001c20bd505f4676e2a4b8c0000000272200025b6000077599998980000000b67df96243010a20800001e940005b259f3948a4dd5e400009c0242c31500007d309320cf90d42258234983af06a11226c1560000ac783d8a560000a91870400000001d91c3e0001cd698b8000710e9e63f881f500018e100017e09bc800074900002e7c0000000ec853ac0000000d36000255423002661a6c000852c0004988000000000600019c781086900001f8270324d00000000000000087a000047300000bcc0000cb9b9800026560490000000000000000000000eac00000006911b087bd09a1145806cb8900000000254ab58e2e23a229ab3d2c881a7c00000000001ffa9165d4e73e219800049f0000000070e33c40003c919b26f6acf098286794952b06939a12200016dca0d8f803a00cb775e24902ab1eb08131c10a432ca22818904ba4104e5689a8f93128d60e5140c5869a5e95c1cbc5de0462476800000000004d182c2bd4800087712ba9fa1a9e74b80007abab5c0001d0000
  | 41 => 0x8f9bae77092842b61d1db1617b26768ece00028bc35a9f7c000000000000007e2261900001d70630bb6a9012f860e00001d8d9c05fb00264f22a42000219ab61000072591ce000000036a0000a9e000047a17699fbebb0000000000007b567486fe71e80004a0157cb099eba279000093ba63783b800073a40000de16f6ab095c4b2086867c021ee5ef9b3037f000071b800000000005e8813d34392327ff8000000000000000c4518a5b869a0000190c00000009240002d9823d40000000f9a4569b7e8d980003e09b9e0f4eb6e241a67c00000000002d9c06edb84a5ba450768905085e03ec03b800061c2bfe000077c126aa353d00c513d7000006780000000000b3f00007eb89ca2190000821033b536c00030319d5427800b8fe87a64dea63e4772db70000cb082497026a9d188a079c3031a87187be2a825530ee443802eb683ca264fc0dce0b18e462e6a27757185981e0233e11705ba3971f1052585300316d914ee8a7a5628452a402b170a80dd88e68bb022ca1da52d80001ee1c5600006607c20000431a162829066a0000000a22c3481b998624c2aeb4528977207e8572570ae5a303800084e9c6f6d9800065c8000a649aec4e794993dd80000000000083091a00028100000f0b0510d036f28000000091b84c9dfe9b0ac804321c4e4198e6a631949e3802106b52983479fa6df53f5d149ac81345089f02000000018ee29f000152e9ef2c3d1ef23767a129203f90000604a56d1abd95ca83800000023d8000055d0000f59a1a1390ac46ad466d000000000005c90000998879329c1b6a4992dc279416c600000000001d3f17e0d0f6e29f6c7ab00002784000183522000000004fb1cf400000000000000000000054a15a100008a000000000e2800002442abb1327fd00000007028886283800099180000001f74bcba23023b2e5b0000a2a00000d800015154711f66512000000000009038000a1f1c7800019267b1894c74c18900e320652ca0b5a26d179c81498df025a4765598b9700000000002714baf26db615dd645de812853640000001ba400000de5c3981c00023e0404a388af118226bf947b096000000005d477c000000008beba3ad3275f29700294f1202800001d840009e38e290419eea296902f7fc038bbbd27249394000afb1516000065ebd900b66d9d95e75a8ddb9e64e252f248f62f10d9214d0418b2c85fc12adba8b9499c6aabc40c87e116474ec87e8cb955c3e30b16a2351fa28218210b64b2005c0c71936c3b88729e561ddcc3a507a5e440c26d894e800091ba8165108ecc000000048f8aec0dc907a8e301665b1525a2ce19ec0001644735061713d619400003005340e3000018782641727930a32675b292280190b6b12e35a00009006fb000008700009e3c3050ade6151cf686968807ae55a936e67787
  | 42 => 0xa0182159c837e89de000000000004321f184fc3ec01ee8c00d55000121591f80000002a7e3c9a1c24f9952095a8000000234600000000002200a478000000278101da28e9d39c4a69b80006ca90046bb800016a1bb657a2adc214a5a40e7e41c6e059283920480925ae92b6e9f0e0000000a0888b600000000001bdc000000087f2654119860600e97186acc1aa6fca04e71a09adbc8251805b80003d6c000927000000015149581c50bb4a3109e74f032979b0400000002f8ae58000184ea21c90f000000000006720000a390002a1ea249b9c000265072e1b930be9362347ec900000c6400026e8bcc18636a900009fc056200002ef12b989c2a252ea000000000016e20000000151ac7893f03474181cea422191b1c200008328c5c93d2710b3d85e416156b65901a0c0001e8800000000000ade7ab40006b1c0005aa16d265280006b6a97e000008c00010590002a96a86800049b23f600000000001e7a1868ccc1da22288559d5090912660000cce50f9dfb00009a0b0cc00060c611c0ae8000803ebfc88823ea7249a00bba1d470000000242901b000000034f557881b944daa98080a710737a4aab9a00014f9078a26e35f27fcabd9f764246a5d6c0c7c55d5e4bb2c123929de8da427a27dc0000868363a54300000000000dcd6c4c0000000a8f000000028b121454760c60408000533a520403d9a813389b50002dfa0000000672800086f01e87af9463a91000000bc00000000003cda9d421ca99600014730dd458e22e8000bb4204066fde900001c53a961b7102140008d9151eac311aa2b82ac415088d62c20902a2564b28ac88b45ac971c0df800d012475404f04102b92cf23d5a94f89ce7a30000000000000004fc69eb8883e461a800094907b300024cc9b425e0a1b9914a6e80006d22edc0000000993c00083ec0000001b245f925810001f8a1f481897b70fe8000000089a268260610b04019b1a1749427121eca411d4b3a044df34712c42721305be0000000aeba9be269133b000192c4b62e0a92f4000aca400000018bc17c48305ff8ef6446099c00009a30002d2868580005fa8c3e00013d90001d070000000000028853dc4de000049c5b4098a00000000000000000080c687004021d16e65a985060000aba0f2c0000000000152ceb89aa29f400011108400000169d67a00007e20001c3820500000001d98839573c4fe14567ef09863c09e528f5a2649edacdc00022af000098c74e90ba00014aaa7c070a000236c6f18eeaaceaae20502768612d591729891d000023da6180005460e6e000000082440000eda16aa809ae5381c0006c886ea000277800015930000000000025cac65ce2137e72e0002e70a284000000041600005f2000000000000003ee8000013000000020fe814c1d08f8a9d500017e671144a8a1f40006
  | 43 => 0xba911c6bd700000000b7aaf6800013b18d083d900e7406b2ead5c00000ac0002730bd908a9d1e7e6892c0000350b7808bd000178a0000000314968075c0bee6d91d820a7ea384a088a87512b7a3e811124c21fd44052ee093c1a8ca9692116154e525b68c6e6c56c3c8f7267249ba9eaaefab15ba08be12e29cb4b101ffa1bb00000000e7029522d669e58f4000290ab878000b3b0f2e80901818271b76000196e000000008fdaaf15ba089000000000000002c35b601fe8da71f9a90886199c137cdf166d0265c18b2788a2a9c001a24f5e490850a90a0afa16b82e43501fd62009ce6a0701c62e762823a39f189822b3800010a085ea29609f0e089dd872c62c12a643988412e667b4794e80b4a74b5c8f9061d392868b7070067686284d47aa1a16699526ac76c5c32b9d0e60e9e104936f0c46919b3b560cb385d08a4b0c8d80a3b8bcc60bae14539945e5c4831b36fca699e40a1432ea962574271eb4baba604cd5963f3800073da3097ad5936ab6905677e84746c000005978000548c00065e0c6647f2f120002a2a71b00005cd0000bc5273c69218d29ec4d60000026b5960000a1b1d36ab21c2f5370fbe1711af804e191c01ba80e35728d068692122edea4e88c8b221a3430a57b25120b4ac0c0cb0b7ba2c8d462499240835107cb95a5c49b5d1a57e7115078819960bd000000000007761ea39751e8b0901f8e51017b49b80dcab122813607c00046fda58a470a9c46680000000946863a28140dc7b08039ae95fd00009ce95108b21cd390d9bc23712d2c1a528709c46a5b3b40bca0ec846d93617f6952abce11b850e0739cf02f18d545ec147429588380001f2e5f18be4764af0882b80005bc95ac00000a200028900000c8493866136bad700b7d800030f0bb831cc8bc4af0fc21f2ed3e58e85d874a8abc00013b800a18cf85ba4e425680004e100005ca8000000198624803361084000584a22c000206f00000009d187166bf1a9702a4e3202a1766a0fd9a40001e667cbc0000000bdc44aa4a70001a2ca2000000000000000232aa736eb20381b449f34570a10624c43316fe4d08a368d300009799f1a83e857c3faa0be00014e700003024be800047580005625a35466e3068a51da4365166a000245e409880e68f0e8c2c2e62877b04bb3c50ba402c1d86086c6104a818e36448be935644b3a2b030815513501ad84980001ed64d606b80bd86394fe8c6da981bbc2888c3635ba79a2cfa7d406444f20000000b23222a54a829489ec0000000000000022051e0c77ac483091f419d749429645c890320001be69d40a4c00026ed91d000000000000001fa8625c5a4520244a000113e8aa2a5c795c4783472019b0195d263ae6eab27918eb020370146c7363e72c44b3a21d80000000a89192200019ba4ed9d7281c925259d04143889
  | 44 => 0x289c0e8c0000002cd6573000016dc2dc000059d0001b5e5559b0299f987e2f8c0000002a140002cc65840090384868f0f1193c93c80006395404111c49bbb0800000006be22a8ea20002952000211600000004bc80d4247007400022c0b2b948879e2c460000000000244648900be0002328000000000020b5a85800082883fe341a770aac13d26ce800025026742981904000181d77d18d454480006b28000718a8a403b00000000d849b25de66b2c0000000e340000ae8986a7faad280008e50000519a4b068ca102ad789ec86704460000000383098096a04b695d2540736800000004be7c5db1c3e8800055c00000000000ab7807f000284a0002bf81542e6113d8000bcea4160a94bd459292daa94a1721165942522978640d09f64804cecb1a80000000cc20f543730002b6400023430000f283328000000135b00021b20a78ed248d00000001e921ff00006520fecbc416ca8e121800001f945a5800000026a20000000022000035167a17b3aa9e00002cf000000000000000f420164b380000002d4453209f200000000000632092264d0000791987279251f91d01dc94ee5df2b21030233600000006418000000000000024c30000000514e59403880000fd1f2600000009b88000000255e000128a000045e6b30a95ba184d09011cfa0ac260006f97fd27007e8781101c0000000000000099080000000000a030000226208000000006c780000794bf40be682c3ef00003e115fcb75800000029c887ca9dc6b8c0002752a8c189d0526ac00001b5000080fa5ec0bca7600002602a44017c837aae65139bd47718a6e64b84ac8b8019a8ab800000011e2ae8d3025410000877a0464bf1764b65e9e05876b32a1693ca2e8ddda1bbc00076d000000d1334161237484f24f6824c3fc66f2c0a00028020d887020002b3096f8000709195244121ac345d36c4841a0308602f8aacac4a6de8d160b311feb42812789f099b4a32b2238693e400005c7b9a0ef878b8ea426880009818000095c0008fba0bc5e08000008a1ea2581f136cb0000000000000000002644000b391a827e1a6a40f2600036e22f052997da5404210a8fc0001f691927ad1b8e5bc24f90ab212ebbf55e0ae2504749624a819d19d46a040001b01c121d4ac6e70a19fa4121ae62772f3800013dcae28bda0f150683c12eff934657c62085c282d29329eaa70a0000000000114234c000087a69e200022c5000000098882020638d42b189b325649d4b1c7800000000006a984313bb188e31e000094b848f00f0000acb0000000083c00000007a880000002d992eade3c0001664a841ec4123277e2d01f14000075e51c9a0e8111fdc065228a97c261153f26c673f585d4dc007a12c1ae473497d093166bf9172d0612e1244aaa8ea09f58f786f3a50c00025e80c3ae20446a544
  | 45 => 0x673f9a7d68c196a0001db881a07a200006910000588b458b6a5af033000018c8000000099601856421d089d0871c185a98a16c1bde1d7cfee4651db2458a64a367abb4b8301caa639fc8157293438296c03e86410b5417ce62a5e6c82d9629b6281a40002c3f000000000000005dfaa2500000001d41da819113b2a9b22e44f19d3839d2c8d8b49380a519cc63b500000752663560292421700008d112be930000000000000001daa16686490000b8200000006b84000a18af4400000000000000b59000033f8000b9b2bb20001dac5b10000792c000000000000000000002da55e00000000065900d8d52000000000002c45c9888d45b80009b0400056804498a019ce89c0c7d000000000002d70001af60001efb0000000000295c000208b0000e360001368000000060a0000000000020480008ccc00000002620000000020e2b9000145084914d400020c2048000090e000065c166c0000cf9bc91aa02ef0f2f6a54afe9d989acbac000040a2df40000000000050503d28b80002dee61780004c10cf8000168c0000000441808e17785e6810da9f1f106dabd98000819800042108d0a0666ca000800063344d60000000a13a12900000005f70000561605c5729fb8281069a000000000000000000dea79f17a4327800077880000001434bd21ab9b1f10f06b60000140a7cb00000009b68000000195000000002d08000a4e943263826c4a88e69400000005a21326afca4a07960ba2000053d0000000a1e190037a109ba94231d00005ac111164b0000d8800011be00000000000000a178000a52207c0948f5a7f8aeb6263ea270000000000111c000188aa2ba5a02a15c5e7970000b868ec046c05ee6ada3c267e20956da400000023969d280304c88000a3c01f60001b543f11fab26497969d34d1a65f1901000000000000005cc255a000160c91f0c1a630c00000000001dd2a0b2560000b3a8000b1099999478c8866c05f74cd8b6e19a2cba6d8a9d0a3a24883a260ad70507a4806c45b7499b6f1c36a315f78d7a2c0c00000000004550000000000000009ea3758eb62211e4528b8b922b59a5b9d12874000057e95e14ca6f320101a0e0ea6a58eb0ac690ae110c4c646c45a236081954e328647bbca10b61a224b8a0bf2ae102c11d6078f6bb40000002e088749d3c000000000008500001e860002a343d2ab083558236ba88000331000000027620000f3800000002bad9800000000000180200018c000021409b3af2810bc0000000e5e000000049c00000000a920000000000000000003a800007e033711ac0002d48000181a03f061100000007f80000000004708c8000000000064c4000000127300023d444b2015843000020700009e302701928000000183000027ee0a0a2cf0000000000052d31ec0002f0688200006b20000bc0000
  | 46 => 0xe83aa028edae72e8c00619243056996af2189adc8bf028c0279e6a3960c9c48189445251a0861a15dc28919cc5d82eec3e1a29c94ec89c489946e579a2bc80767d284e12f4af7960a46f18040002abc097c0049208f4c673c00051ac62a3980b502c1d05400015061881c5a63b5ad609e80000001e76aba83e89bf80006d60000ab807263351ae2a26000017d8bfa926deda9ca950d80800000000c7200000000bf91e400013060e0d1a200025497d02b39000000084a8e062a518f287304cb9fe280a0eb090598d994db0da78556d44ca8f6803820785560e484001cc9c90328c00000005fd77a24e20c0db206562e7e580821a27f096e897ab9cac01229bb2a8d83028b005fca83e603000089702de6b6c00011b210e7d78000000000000000003e220ba6a2966b25900004779c3f94b000000002b22d100000001e163941f2ab05037100022e280c80000c79d568efac2f44821665a467ba00027fb34309481a159be5d1816c0ae1b6dae30c59033a5dc3f7906a563864e740935a168115875327a26b7d5b89b20938882800081f6e2e4452195193c56800021d6993937405f87994349cc000023fc3c583ce80480000001cf8530800009180007d4275e0f3669278c1f2b491aaba26f20a58bca51a300688a1faa63a000000089f8d116f4d21739daa1cb4d9b2e8206d9680ec000b0004383fda3503b6a0b20002d26000018440e09ce075800063e14e80b380005ee80000002ee220d1cbe07a4a2066b9f54472011744e0d132660000000099d54c29b48b70d2e12f04b420f80000000c3096b07cab044000bd78b842df22c49f8d39c0b612ae75a02968b3861413d18b6bb691f243e833d6df260b5d11c6d00029b0000000000000000000000b0b56061020000405a4226a9400000028b3816154400000007d65b2800000001bea2788de02c80002a6747b1e2aa30199479eda0d00000000000000acd40c200024200000000124053a69580007c44d4c000000032fa6e40002b053c20000750c000a130000083d81600007d8352800004880000ba0000000228c00000000000eb500014ac000000000007ba8ba0000b690000aeda87600021493e910ca0000d866cf2e742eb9f9e2efe9aa0000214000000083980001d800002ef800085f90588e28d0d3219e3455d5fda000000078480000000000a5580000000dd20539fa0077a2f8afded7e2fa1dce92380000001c9a7ed005c93d4000a8a28de18968f6ab02830a2f4caa8868e42000000000000009990dcc0268c7e00017fa0f1c4f8313ad52610909a78a230d3842c101d6aed48b61bb81950a1665695d438e18daacdaf0a21a650e342042302521b6120c000000000004103888a18596131400069f099f13009b800008c287da588a4980dc86402a300000002460000ad880003c3a58a795484
  | 47 => 0xbc2042b56000000094d400000015ce0000cf30001ad45b080000000a5500000009899438ad65794000000000000000001a9a3dc22b8156c00000000008e8c000aad83062bf04da2de1a8d0001f903e280000000000290ac96a4fa8fc2d18e4034740003380000aa81a0ab839636b2b0450850800053e0a0a000015cb014000bba80000c1e9d300025fa6f3421e1274000000051c000168d00024e789214444a480000001a8400000005e3e3a881822266aada917b492399292b7e379aa0c96687d39778460af98a001c907aca332bee92ea03873844a99a101586b0cb963ff1bfab62260d0fa8ac80734dc88f1943a50d88fc781a7e9b48a4fe777064281e1c76691cc5849286d98bb070c1a1ca96009ca125464ada3249cce80c0ffa6660c93664929e062a66e92a400028a0311a5e8efa145253c000008a44c99446c5c9707a1c0008c6934c807d3ce6951fce7ef9ace4bb9d946110000696a7a429a90705426a54090c586236af4e844c00066e40000001814b982ef07200000051800063f091eb69999728d0f3a00000001a640000002a711a60f07238806065f98bf595201a3f01bc0941908630a15ae88f000053d9bba0002f3e37520590000c2a8c891aea704000633800046d0000ae19f61000114e000060200005600001a5945e000050a254c045194000021540001dd61100dba00027cc0c7299aa8beb2825e8eee0d143de0000000438a83b8e88d26890800007d2c5ea0818ee7d180000000000b1908b90001d54b1d8e677bd4000bb60fa62bb929a6f406703a28b341cb800058cc000000000000014e25bad18c00000000000000418aecc0000a742dc1e64000000000001ba00015463a2cf2a1151e3d000185a8660e9c21eaa1800016c881b1c2e7d48000a3e246a41180000000000a719c2b74597c49ec000000011ca2609c085ae000000000000000000000000021f47b200014060001740a9da002a1620f012500009eb400023480ed2be47c200397f807101744b19d5c60bedb2a0a000034265c08fb2d5e541c00092f1df600000009b497aa079804a58ae60f03eca1a6200df062e9c7baee81329ae2e9aa5b2aa2000000000000000001b0172280009c580000000000058c00000028d29a71fc60002bf4000106c8b08e7c5a7c0000a042c07870f606810000b2c0fe948156385931560420e53d040086b5050231653a1c4428a7520002e5d0f880007f42bc80000000b360000b97c0006490ff060f89ae5bf093a861176c093aea07f78c7459a0dc90a1a7233b62f4273813f400004851098e665ccd3b401e560e86c041d79304120001b754a509d200012d45bbc0001500147103c000000000000014d800011d2244000002ac2380000000b5f204a98a80000001376a91c0006a4c00042aa56eb5b1f2000000009428000000267a61
  | 48 => 0x9ce2609378366000000003205d931e824a906ac2873baf4ab748cacbc98e1832c6e1832592b2a86eb100002bc2b0e058c38f1f0c0082d120002772958d0440c8acbe87391d8a8229da00280003d8833a0000000921da758e60c8c710035e24503285182b4c97f967042916a253ec000b6b15900002b7460b2cda6aa0000063c0000000116000000000000000002c2900012b076e80002d99ec3baa81928e34ddc2658d3c4e28f6a92c59b70000108bc69ac073603f2b3081ae16957929b7a4c8b7a21084f80af82a61a5055ca69e47b88783dbab608b42252bb78290b722ba15128de77460fc88515be20e068116631c74523161e17beb4e8e4079a3c16968396862ba2d82a6a021bac8df2c12753d84014fa8fa0002de45679c8675d96824ea9f28b92a1f4125984c48a90e40a29dd463986d215868ce23506f40262a3658d2634482151f0000c32a2a18394ae0549a7396460dba5615b300000000fd81900fa80002aae0000cf57a01c3c9f380008848000a6b80000001684987d3a40000000465800000018faa662464ad100001cf9662a448000bc080001fb0f98000000034d5dd08532d801a80b8fbd3ddca00000f61d014162998d0478d89be920237e99aa37a54f8b520c906c826aacce000283926e89256f149075920804000292c0000edca328000000032a0000e14a76189a74b4000109400000012dc95a14860000000000072a26780000000000182a9db963200a0002d9a23b84c96cf89fa974ad749ab00000f71ec20ef2a941321e07ae4800035c000000015b000002ea33ca6168be9dbe2c29c5443392c50095357a4e2b68261228443118e74609e149e600001b3a52a1d0990a7252cb8ada8f0d1f1eac622380008b468c20001238a0522daa7bdefa563054a2c402f004dadb57429af537794c641c8e0e2228cd22a22a56b8e897c0e412a43fd1ac434fdbf631180007fd00003c6153a0fc000001fa9d226de569a8f064c7580488000096649c97a692b27c87fc80006ea800050b925c5c5a84618780007ec0ac60000000b4e8c8d57a80000000000000064d692859e4e59678454a2f412900006b81bb4370ad6e792103a498148475440005e3800067ec8428eb87344a6036f2eed9b800007c06ae919c4811b8c28c9a1299b0000a6f2b963e500000000de19212167000175600000002cbaa0a6a39c4924c18654272494a3f8000a9e90d800000005d4019600000000000000000022d00003a20002b766e48000b6a60ec6d299cd7cc28856b19c9e96c9e6e0001554b03da142dd87c881b65ba000000000027f29e5dd396a529f86a215e2a76585c029c0a6163e6ba55388a253b000000007d6000000000002bb00000008d4a4340002944000000000000000000000000159f00013d8bd59ec831a000090fa9c017eac24000219e09401
  | 49 => 0x162a3d49f703079ee43d62a90b9b81fc43a88fe1011604b5c97d633eaa7c7db8e7e69da25888d18aa1f0e0a064e9a2255a1ef736c93ed45aaaf884406800e6011207085f57d127d84cc0391942261779aeeee00012b405095a4958a5f480d0cb649d9ce47288dd33744d6c0af9b14a4b996c3bf04a6a72cb686dd248a50616a1a729cd134829ec71f88e69020130679da92107c3ca05e194b26a422f52fa632153e8c49b980866bc80009318d6600000002a1800003c694267b800025d8d6400019b6000000000026c30001200a5944991810ae99f09f72bbe19f9300aa2203c8fb269e29a439321601e1ad022ada4c1a1c9e9548604300000b601c50a7335ec00000000002000de95d49f7a8f2016b651a5823c26dc700000000002b2b56d048a310aa2646d83e70769b0627f976a5f6000081904f311f80000072cd271a800084cc0000002e5e44280000002a45a545d1a96105443bc269883c9d1c1a059f243b0c53b9a947c5a5e9888c300003718d91000175500008bb36680004d786920000583157800018b4f22000221600022625f8ac2ca0caba83060000000056b2a8800033de0360000bd05ab00005edab167ea98b224885c8b718a1c2d280002a80618586000000a5ad961400da2bd9e82a0b88de4d208944489fa70000cf40000093b3e93fc9a394e900000009db8000000000050282065820000196800089a800000006ca000095400006ac6686ce6ac964b400026e935d800044580000001e8ea121a677e027bf576050f0002176000040200000000000000b908b8e000232c00007c10f4863c000000000000000002838a
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x846c765494004327b1aa4a00219318d5250010c6ca9b0a800863554d854004333296c2a00219954b6150010c6ca830a8008635541854004333290c2a002199548615001096ceda0a800863765d05400435231682a00211b9ca65100108dae5328800846e721944004236b90ca200219954a6110010c6ca8b08800866552584400429aba882200216c5c04110010ccacb90e40086655258620042b2ba843100211ddc7654801087ced2a2400843c76951200421f3b2a8900210f1d95448010c3ca9b1a400861d54d8d200430f2a0c6900218755063480108bced29a400845c7694d200430fb24a6900218719253480108bceca9a400845c7654d200430fb22a690021871915348010c5ec9292400862c649492004327b1ca4900219318e5248010c5ec8a92400862c645492004327b1aa4900219318d5248010c6ca9b0a400863554d85200432b29ec2900219554f6148010ccca5b0a400866552d85200431b2a0c2900218d5506148010caca630a4008655531852004333290c2900219954861480109cced90a400866765c8520043523264290021b118f214801087ce9328400843d74994200422f39cca10021175ce650801087ce8328400843d74194200422f398ca10021175cc6508010c6aa9308400865553984200431aaa2c2100219554d6108010ccca4b0840085657508420042f0b8042100211d5d464c40108eaea31620087255454b10043a2a9aa5880211d5da5184010c72cb2a42008639655521004334b2ca5080219a59552840108f2ed28c200843e76951100421e3b4a8880210f9d95444010878ecaa2200862e54d891004316aa6c4880218b9506244010c5aa8312200846e7694910042363b4a4880218bd925244010c58c9292200864f63949100432631ca4880211b9d952440108d8eca92200862f645491004316322a48802193d8d5244010c98c6a92200863774d95100431a3a6ca8802199dcb6544010cc8e5b2a200863765d91100423abacc8880212d9d264440109cce5322200863765191100425a3b4a8880218dd965444010968ecaa22008637655511004333b2ec488021a919362440108eaeb31220084b674989100426b39cc488021399ca6244010cceca31220086a7641891004352320c488021b1d8c6244010d88c631220086a6541891004352aa0c488021391da5244010ccecb29220086a464949100436231ca488021391d95244010ccecaa9220086a4645491004392aa2a488021b118d5244010e8aa6a922008634649411004332314a0880218edd36544010c70e9b2a200866b72d951004334396ca880218ed976444010c76ca322200863b65951100431db2aa8880219ad976244010cd6ca31220086a8641891004364318c4880219ad965244010cd6caa9220086b064d851004370316c2880211e9da5144010
  | 1 => 0x42042d438284210210f9d2658c81087ae932c640843e74196320421eba0cb190211d5d6618c810c6aa930c640865553986320431aaa2c3190219554d618c810ccca4b0c640843e74995320421eba4ca990210fdd1654c810878e8b2a640843e74195320421eba0ca990210f5d7644c81087aea322640843e76951320421e3b4a8990210f9d9544c810878ecaa2640862f649493204316324a4990218bd91524c810c58c8a92640854c735493204332a96c2990211d5d4614c810cd2a5b02640847975181320421f3a4ca190210f5d2650c81087ce8328640843d74194320423b388ca19021535ce520c810a9eea990640854d754c83204327b2a641902193595320c810b18e8990640870e544c83204386aa2641902171dc5320c810b90e09906408635659534104392aa4a5a08219959552d0410e4aa8a9682087455354b410429aba885a08211b9cb65904108dae5b2c820846d7598a41043172a4c5208218b55262904108deeab14820862e5458a4104316aa2c5208211bdda52904108daed294820864e6394a4104326b1ca5208211bdd952904108daeca94820864e6354a4104326b1aa5208218e5516090410c6acaa08820872552504410431d2a2c0208218d59664104108eeecaa08208636645504104392aa2a420821d154d52104108eeeab0082084e4725804104359322c0208211d5d464c84109ace6326420863565553210423aba8c7908212d9d063c8410caacaa9e42087155454f2104332b2ca590821c995152c8410e4aa8a9642087465354b21043a2a9aa590821595d442c8410acaea196420843e74d96210421eba6cb10821179cf65884108bae7b2c420843d75992210421fbaac9108210fdda548841087aed2a4420843f76552210421ebb2a910821175d66388410c3ca931c420861d5498e210422fbaac710821879516388410c3aa8b1c420845f7694e210422ebb4a710821879925388410c3ac929c420845f7654e210422ebb2a710821879915388410c3ac8a9c420862e6494a2104316b24a5108219398e5288410c9ac7294420862e6454a2104316b22a5108219398d5288410c9ac6a944208669525822104332b2a4210821c95512108410e8aa6908420866a52580210423aba8c8108211d5d46308410e2aa8a98420866565988210423bbb2a410821999895208410e4aa8a90420874553548210423bbaac0108212d1d160084109a8e6b0042086e2625802104237b92c9280211b1c9649401087ee8b14a00843c7458a500422fb9ac528021171cd629401087ee8b0ca00843c745865004237b92c3280211b1c96194010c6acba0e800863554586400429aba883200211ddc76550010c5ca9b12800862d54d8940043172a0c4a00218b55062500108dced292800846c769494004327b1ca4a00219318e52500108dceca9280
  | 2 => 0xa529021539cf5294810a9ae7a94a40845f73592520422e39ac9290210fdd16394810878e8b1ca40854e73d5252042a6b9ea929021c91c55494810a9ce62a4a40854d7315252042973a6a7290214b5d35394810e1ca929ca40870d5494e52042b338ec92902153dcd6494810a98e6b24a40862d6419252042b338ec7290214bdd16394810a58e8b1ca40864d6318e52042973a4c3290214b5d26194810a9ce730ca40854d7398652042973a6c4a90214b5d36254810a9ce7b12a40854d73d89520421fba2c0a90210f1d160548108bee6b02a40845c7358152042373b6a8a9021539cf5454810a9ae7aa2a4087247155152042373b0a8a9021539cc5454810a9ae62a2a40852e74d4d5204296ba6a6a9021c39525354810e1aa929aa40870e5454d5204386aa2a6a9021c99506154810e4aa830aa4087465318552043a2a98c2a9021599c66454810a9ee6b22a40854c7359152042b238ac8a90215a1c16454810c5ac8322a4085667198d5204297ba2c6a90214b1d16354810ac8e2b1aa4085687058d5204326b18c6a90214b9d26154810a5ae930aa40854e7398552042a6b9cc2a9021991866054810cc8c2302a40852e740415204296ba020a9021535cc105481087aed2a0a40843f76550520430f2a4c629021875526314810c3ca8b18a40861d5458c520422ebb4a629021879925314810c3ac9298a40845f7654c520430f322a629021875915314810c5ca9310a40862d54988520432729cc4290219354e62148108deeca90a40862e645485204316b22a4290219398d5214810c9ac6a90a40861e6498c520430eb24c629021879916314810c3ac8b18a40862e649885204316b24c4290219398e6214810c9ac7310a40863564984520432ab1cc229021179ce65d08108bae732e840845e73197420422eb98cba10211d5d661d0810caaa730e840866552987420431b2a2c3a10219554d61d0810ccaa4b0e840845e73996420422eb9ccb21021179cc65908108bae632c840847575986420431aaa4c3210219554e6190810c6aa8b0c8408655535864204333292c321021179ce65508108bae732a840845f73595420422e39acaa1021179cc65508108bae632a840852c72551420422ebaec6a1021879536350810c3aa9b1a840845d7518d420430f2a0c6a10218755063508108bced29a840845c7694d420422f3b2a6a1021171d95350810c9ec7292840864c6394942042963a2a4a102193d8d5250810c98c6a92840863554d854204332a96c2a10211d5d46150810c72a9b02840866952d81420423cba8c0a1021179ce65108108bae7328840845e73194420422eb98ca210211d9c46510810a5ae52a0840852d749484204297baa84210214b5d54210810c5ecaa10840862d6550842042c639a8421021c394d4210810e1aa6a1084085a771508
  | 3 => 0x4a60c851087eedaa4428843d76d52214421fbb0a910a210f5d85488510c3ea931c428861c5498e214430faa2c710a218715163885108beeda9c428845d76d4e214430f326a710a218759353885108beec29c428845d7614e214430f320a710a21875905388510c5cc9a94428862d64d4a214432731ea510a219358f5288510c5cc8294428862d6414a2144327318a510a219358c5288510c70a9b02428865853d81214431c2a0c090a219614c6048510cd6a43024288634549874044332294c3a02218d15161d0110cc8a4b0e808846e72d954044236b96caa02211bdc965501108d8e4b2a808846e75d894044317aa6c4a02218b15362501108dcea312808862f5418940443162a0c4a02211b9db52501108d8eda92808864f63d49404432631ea4a02211b9d852501108d8ec292808864f631494044326318a4a02218d1536150110ccea5b0a808866452d85404431baa0c2a02218d1506150110ccea430a808866452185404431a2a4c3902219514e61c8110cc8a530e408863454587204432a29ac3902219914961c811087ce9b2a408843d74d95204422f39eca90221175cf654811087ee8b2a408843c74595204422fb9aca90221171cd654811087cebb22408843e75191204421f3b6a8902210f1db544811087cec2a2408843c76151204422f3aec69022187d536348110c38a9b1a408845e7518d204430faa0c6902218715063481108bceda9a408845c76d4d204430fb26a6902218719353481108bcec29a408845c7614d204430fb20a690221871905348110c5ec9a92408862c64d492044327b1ea4902219318f5248110c5ec8292408862c641492044327b18a4902219318c5248110c6ea9b0a408863454d85204432ba9ec2902219514f6148110cc8a5b0a408863754185204431a2a0c29022195d4c6148110ca8a630a4088667521852044332290c290221ca15052c4110e90a629620885667295210443922a6a5082214d9d25284110aace729420887275414a10443922a0a508221d1d4c5284110e88a6294208864e6398b540432731ac5aa0219358d62d5010a5ce5aa4a80852d72d52540422fb9ac52a021171cd6295010a6ce3b14a80851f7358a540428e39ac52a0218b5886295010a5ce530ca80852d729865404297396c8aa0214b5cb64550108dee4b02a80846c72581540429b38cc4aa02147dcd6255010a38e6b12a80853471589540429c382c4aa0218b5886255010a5ce530aa80852d72985540431a30cc0aa0218d184605501087eecaa0a80862d549885404316aa2c42a0218b9926215010c9cc7310a80862e64588540432731ac42a0219358d6215010ccac5308a80861e5498f520430eaa4c7a90218795163d4810c3aa8b1ea40861e6498f520430eb24c7a90218799163d4810c3ac8b1ea40852e74d4a5204296ba6
  | 4 => 0xdeeca90a48852f7454852442963a2a42922153dcd5214910a98e6a90a48845f73590524422e39ac8292210fdd16314910878e8b18a48852e749885244296ba4c429221539ce6214910a9ae7310a48843e74984524421eba4c229221179ce61149108bae7308a48862e65d505244236bb4a829221539ce5414910a9ae72a0a48846f7655052442a7b9aa829221531cd5414910c5cca2a0a48864e65d4c5244387aa6a629221c315353149108daed298a48852e7494c5244296ba4a6292211bdd95314910a5ee8a98a48852c7454c5244387aa0a629221c31505314910a9ee6b20a48854c735905244316b20c829221595c46414910a5ee8b18a48852c7458c5244326b18c629221595c46314910a5ee8b00a48852c7458052442a7b9ac029221531cd6014910a5ee8880a48852c7444052442a7b9a2029221531cd10149108bce7b2e848845d73d97424423ab8ecba122117dcd65d09108b8e6b2e848845e73d96424422eb9ecb212211d5c765909108bee6b2c848845c73596424422f39ecaa1221175cf65509108bce732a848845d73995424422fb9acaa1221171cd65509108eee2b2a848847b705954244297396a8a1221179d76350910c3ea9b1a848861c54d8d424422f3a8c6a122187d506350910c38a831a848845e76d4d424422e3b6a6a1221179d853509108b8ec29a848852e74d494244327b1ea4a12219318f5250910c9ec6292848864c63149424422f39eca21221175cf65109108bee6b28848845c73594424423bb8aca212214b5c85410910a5ae8290848852e7550842442963aa84212218b9954210910c58caa10848858c735084244387a9a8421221c314d42109108eceb308848863454984424432a29cc2212219914a61109108e8eab08848863454584424432a29ac22122199149611091087ce9b2c648843d74d96324423ab8ecb192210fdd1658c910878e8b2c648843e74d95324421eba6ca992210f9d2654c91087ae932a648843f74595324421e3a2ca992211ddc5654c9108f6e0b2a648843e75d91324421f3a8c8992210f9db544c910878edaa2648843e76151324421e3b0a8992218bd93524c910c58c9a92648854e73d493244317b20a4992218b190524c91087ce9b28648843d74d94324421fba2ca192210f1d1650c9108eee2b28648854d7314832442a73aa6419221531d5320c910c9cca990648864c654c832442c63a26419221c3d51320c910e18a8990648847675984324431a2a4c2192219914a610c9108e8eab086488634545843244332292c2192218e15260d0510c5ea9314828862c5498a4144317aa2c520a218b15162905108deeda94828846d76d4a414432731ea520a219358f52905108deec294828846d7614a4144327318a520a219358c5290510cd0a5b02828863b541814144334290c0a0a219a1
  | 5 => 0x852c7550842842c639a842142169dc54210a1087ce9b2c650843d74d96328432ba9cc3194210f9d2654ca1087ae932a650843f74595328421e3a2ca994210fdd1650ca10878e8b28650843e74194328421eba0ca19421535cc520ca10a9cea990650854c754c832842c63a2641942171dc5320ca10a58e4aa683085a4725534184317aa4c520c218b152629061087ced2a2830852c72551418421ebb6a820c21391c965106108eaedaa083084b576d5041842d9386a820c216c9c054106109c8e4b00830852c7454b21842a639aa590c21359cc64c861096ce831e43085a47454b21842e239aa590c218b9935288610c9cc7a94430862e6414a2184327318a510c211b9da5248610a58e8a92430854c735492184236bb6a410c212d1d165086109a8e6b28430847576d482184272bb6a410c21789c35208610bc4e029043084b474580218426a39ac010c214b1c9549021087cec2a2810862f5418940843162a0c4a04218d150615021096ceda0a81086a462d05408421fbb2a8204214b1c95410210a58e8a94410854c7354a2084316326a4904219318f52482108dcec292410862c641492084326318a4904219914861482109cced90a41086a464c85208436231e42904211bdd95208210a58e8a90410854c73548208425a3a2cb88421391c965c4210a3ce7b16a88851d73d8b5444317b14c5aa2214b9cb60d5110a5ae5b06a88862f5498a5444317aa2c52a2219398e6295110c9cc6b14a88864d6358a5444333312c32a2218bd936255110c9ec7b12a88862f641895444327b18c4aa2219318c6255110ccec5b0aa88866462d855444334316c0aa2210fdd95415110a5ee4aa0a88852c725505444297394c82a2214b5ca64151108bee6b10a88845c735885444237394c22a2211b5ca6115110a3ee6b10a88851c735885444316b10c42a2214d5c46215110a5ee4b00a88852c7258054442a739ca9a9221535ce54d4910a9ee6aa6a48854c735535244387aa6a7a9221c315353d4910a9ce7b26a48854d73d935244317b24c9a92214b9d363d4910a5ae9b1ea48864f6398f52442973a6c1a92214b5d360d4910a9ce7b06a48854d73d83524430faa4c729221871526394910c3ea8b1ca48861c5458e524430f326a729221875935394910c5cc9a94a48862d64d4a524432731ea5292219358f5294910c3cc931ca48861d6498e524430f322c729221875916394910c6cc8b0ca48865663586524421f3b6a8a92210f9d85454910c3ea9b1aa48861c54d8d524430faa0c6a9221871506354910c3ec9a9aa48861c64d4d524430fb26c6a9221871936354910c3ec831aa48861c6418d5244317b26c4a92218b1936254910c9ec7b12a48864c63d89524431bb26c2a92218d1936154910caec7b0aa48865463d85524431c326c0a92219618f60549108
  | 6 => 0x8347b20c690041a31906348020ccecbb0a40106a464d85200836231ec29004199d946148020d4ec830a40106a4641852008363b18c290041b118c6148020ccaea30a401062c64545200832631aa290041991855148020c58c9282401064c63941200831db2ec8900418ed946448020cb6cbb1a401065b6518d2008354326c490041b218f6248020ce6cbb0a4010673651852008358320c290041b418c6148020dc6c430a401064e6398b54c432731ac5aa6219358d62d5310cccc530ea9886656298754c4297396a92a62117dcd62953108b8e6b14a98852e72d9154c421fbb2a82a6218799263d4b10c3ac931ea58861e6458f52c430eb22c7a96218d99261d4b10c6ac930ea5886566398752c432ab1cc3a96214b9d35294b10a9ce7a94a58845f7359252c422e39ac9296210fdd16394b10878e8b1ca58852e74d8952c42a739ec4a96211bdd95214b108bce632e858845d7319742c422f398cb21621175cc6590b108bce732a858845d7399542c422fb9acaa1621171cd6550b108bce7b28858845d73d9442c422f39cca21621175ce6510b10a5ae52a0858852d7494842c4297baa84216214b5d54210b10b18e6a1085885a87050842c421f3a0cb196210f5d0658cb1087ce932a658843d7499532c421fba2ca996210f1d1654cb1087ce9b28658843d74d9432c421f3a4ca196210f5d2650cb10a9ae7290658854f754c832c42a6baa6419621631d1320cb10b90e0990658852e72d5341c43172a4c520e218b5526290710a5ce5aa2838843e7615141c421fbb2a820e214b9d352c8710a9ce7a96438862e6494a21c432731ca510e218b9915288710c9cc6a94438852e74d4921c42a739ea490e211b9d852487108deeca90438852e72d5240c421f3b4a8a06218b9506250310c5aa831281886365418540c431aaa0c2a06210f5db5410310a5ce5aa0818852e74d4a20c42a739ea5106211b9da5248310c58c9292418864c6394920c4316322a4906219318d5248310ccca430a41886655218520c4236bb6a4106214b9d35208310a9ce7a90418864f63d895484317b20c4aa42193d8c6255210c98c6312a90866762d855484332316c2aa4210fdd95415210a58e4aa0a90845f73588548422e39ac42a42187d936354a10c38c9b1aa50861f6418d528430e320c6a94218b1936254a10c98c7b12a50863764d85528431a326c2a942195d8f6154a10ca8c7b0aa50846f7654852842963a2a429421531cd5214a108bee6b20a50845c73590528421fba2c6294210f1d16314a108bce7b2e850845d73d974284333a94c3a1421179cf6590a108bae7b2c850863754986428422f39ccaa1421175ce6550a108bee6b2a850845c73595428422fb9aca21421171cd6510a108bce6328850845d731944284296b90a8214214b5d05210a10a5ceaa10850
  | 7 => 0x8210414b5d654108208deecaa0841054c7355042082c639aa8210414bdd95410820c5eecaa0841070f73550420829639aa821041c31cd5410820a18e6aa0841052f715504208236bb0a6210414b5d05310820acae2298841052f7590c420838729c86210414b5d44310820e18a6218841046d75984420826739cc2210411bdd56010820998e6b0084104e4715804208236ba8c999041399c464cc8208daec2a6641054d7315332082b2b88a9990414b1d153cc82087ce9b2c641043d74d96320828e3a2a719041471d1530c820a9ae4a98641058c744c83208236ba8c8190411b5d8540c820a9ae62a064105657115032082a6bacc619041535d6530c8208deeca98641052c7454c32082c63a2a61904153dd9530c820c9eeca98641070f7454c32082a63a2a619041c31d1530c820a18e8a98641054f7154c32082a7bae8619041c3953430c820a9aea218641070c5410c3208236bacc2190412b9d2610c8208deeab0064104ac74580320827238ac019041599c74254420acce2212a21056671cc951082b338864a88411ddd95114420c6ac8a88a21065563544510828e39aa9a0841331cd62d0420a5aea216821062d6510b410822f39ecb20841175cf6590420caac728c8210655635464108333312a32084117dcd65504208b8e6b2a821045e73195410822eb98caa0841471cd5450420c5aa8312821052d751094108316b2884a0841c91095150420d5084302821051c7454f31082563a2c598841535d432cc420c9aca196621043e74d96310821eba6cb188418d592518c420c6ac8a8c621066662546310821fba2ca988410f1d1654c42087ce832a621043d74195310828e3a2a6988419354c624c420a9aea192621064d650c931083a2192a298841b20c8604c420c5acb324421062d655922108236ba8c910841339cc6488420c9acb31c421068e6498e2108346b24c710841935956388420d1cc8b1c421046d7518e21082573a0c7108418b9915188420c9cc6a8c42104ae74984210826739cc2108412b1d16008420998e6b00421052e7488650082a739c43280411b5d821940208bce7b2c801045d73d96400828e39aa9200418b5526290020a5aea214801062f6510a400822f398ca20041175cc6510020a38e6aa080104cc735884008296ba884200418b594421002087ce9b2c601043d74d96300828e3a2a7180419354e628c020c9eca194601043e74194300821eba0ca180412b1d1620c020c9aca19060104ae74987200826739cc3900411bdd951c8020cccc2a8e401046d7694a200823cbb4a5100416a9d22188020b94e710c401062f65d912008236bacc8900412b9d2644802099ce732240104e6719912008317b28c89004193d976348020d18c9b1a401046d7598d20082573a4c690041339ce63480209cce331a401064f6518d2
  | 8 => 0xf65501208bee6b2a809045e75d8d404830faa6c6a02418715363501208bcea31a809061f5418d404830e2a0c6a0241179db53501208b8eda9a809045e7614d40483162a6c4a024193d4f6250120c98a7b12809062f5418940483162a0c4a024193d4c6250120c98a6312809047675d85404831baa6c2a02418d1536150120caea7b0a809065453d85404823b3a8c2a02418dd506150120c68a830a809065753185404832a298c2a02411d9db5150120caec7a8a809065463d454048333b16a2a02419918b51501208ecec28a809065763145404832a318a2a024199d885150120cc8c428a809062c5498b304832629cc5982418b15162cc120c98a6b166090666621473048332b10a3982410fdd1654c120878e8b2a609043e76d51304821e3b6a8982410f9d8544c120878ec2a2609062f54d8930483162a6c4982418bd50624c120c58a8312609064f531893048326298c4982411d9db514c120c6ec9a8a609063464d453048333b16a2982419918b514c1208ecec28a609063764145304831a320a29824199d88514c120cc8c428a60907305414720483a8298a390241539ce5488120acce32a4409070c54d4e20482973a4a710241599c65388120e1ea829c409070c5414e20483162a2c3102419314d6188120e48a9a8c409074453d462048332b08a310241c9d505188120e48a828c40907475314620483a2298a310241995d851881208bce730ca81045d73986540830fb20c6aa041171cd6255020c9ec6312a81064c63189540821fbb2a82a041471cd5415020c3aa8b18a81063554584540830f322c62a041931c96315020c9ac7310a81065663984540832ab1cc22a0418d9916115020cacc6b08a810655635845408333312c22a0410f9d26194c2087ae930ca61061d73191530830e326c6a98410fdd16254c20878e8b12a61062f641895308316320c4a984117dd95314c20a38e8a98a61061d6454c530832aa9ac2298418b1c96414c20c5ac9310a61063664984530831ab24c2298418d9916114c20c6ac8b08a61066662584530823b388cba18411d5c465d0c20a38e6aa6861046d7598b430823b388cb218411d5c46590c20a3ae62a4861053571152430828e3a2a7218410fdd16550c208bee6b2a861046f72595430823b388caa18411d5c46550c2087ced2a2861051c73551430828e3a2a6a18411b5d46250c20c5ca8312861062d541894308327298c4a18419354c6250c208ece2328861047571194430821ebb6a8218410f5d85410c20a3ae62a0861053571150430822ebb6a621841479d54310c20a38eaa18861061f6550c430830eb2a8621841631c94310c20a98e6aa6841046d7614f4208296ba0a7a1041595c453d08208bce7b2c841045d73d96420828e39aa921041471cd5410820a5ae4aa0841058c735084208296bacc
  | 9 => 0xce632c829045d73196414822f3acc720a4187d526390520c38a931c829045c7558e414830faa2c720a418715163905208beeda9c829045d76d4e414822fbb0a720a41175d85390520c5ea9314829062c5498a4148327a9cc520a419314e6290520c58a8b14829064f5358a414832629ac520a419598f5190520caac7a8c829066662d464148332b16a320a419598c5190520caac628c8290666621464148332b10a320a41179cf65505208bae7b2a829045f73594414822e39aca20a411b9d66210520c58a9310829064c5398841483162a2c420a419314d6210520cccc4288829066562144414821fba2cb98a410f1d165cc52087ee8b2c629043c74596314821f3a0cb18a410f5d0658c52087ceb324629043c75592314821fbb6a918a410f5db548c52087eec2a4629043d76152314830f326a718a4187593538c520c3cc829c629061d6414e3148317aa4c518a418b152628c520c9ea7314629064c5398a3148317aa2c518a418b151628c520c98a6b14629063664d46314831ab26a318a419998b518c520ccac5a8c629063664146314831ab20a318a4199988518c520ccac428c629043e74d95314821eba6ca98a410fdd1650c520878e8b28629046e7598831483162a4c418a419314e620c520c58a8b10629064c535883148333310a218a4199588510c520ccee332e429062e65d532148236bb4a990a41539ce54c8520acce32a6429062e65153214832732ea790a41c315353c85208daed29e429052e7494f21482b338ca790a419399453c8520e1ea829e429070c5414f214833332ea390a41c915351c8520e88a7a8e42907275414721483922a0a390a41d1d4c51c8520e88a628e429062c54983214832629cc190a419914660c852087ceb324429043c75592214821ebb6a910a410f5d854885208bceb31c429061f5498e214830e2a4c710a41171d56388520c3ea8b1c429061c5458e214822ebb6a710a41879935388520c3ac9a9c429045d7614e214830f320a710a41875905388520c6cc9a8c429063564d46214832b31ea310a419558f5188520c6cc828c429063564146214832b318a310a419558c5188520ce0a3304429063854d81214832c29ec090a418e1506048520cb0a630242906735118121482973a4a890a41539ce5448520acce32a2429070c54d4d21482973a4a690a41599c65348520e1ea829a429070c5414d21482b33aec290a41c91536148520e88a7b0a429072454d4521483a229ea290a41c9d505148520e48a828a42907475314521483a2298a290a41599d85148520cccec28a429072854d8121483a429ec090a418b1506048520c98a630242907285418121483a4298c090a41b8d846048520c58a9310429062c5498b404832629cc5a02418b15162d0120c98a6b168090666621474048332b10a3a0241175c
  | 10 => 0x51e7550c434828e3aa8621a41879954310d20c38caa18869058c7250c43482373acc421a418b1526210d20c98a7310869062c54588434832629ac421a418e15260d09208bcebb1a849061f54d8d424830e2a6c6a1241179d46350920c3ea831a849061c5418d424822f3b6a6a1241171db53509208bcec29a849063b5418142482963aa8421241631cd4210920e1ea6a10849070c53508424832c29cc1992410f9d7644c92087cea322649043e76d51324821f3b0a89924187d93534c920c38c9a9a649061f6414d324830e320a69924196d4c604c920b18e8990649070f544c832483862a2641924117dcd64d45208b8e6b26a29043f7458f514821e3a2c7a8a41559ce54d4520aaae72a6a2905577355351482aa39aa9a8a41c5d5353d4520e28a9a9ea2905367494f514829aba4a7a8a414ddd153d4520a68e8a9ea2907175414f514838a2a0a7a8a41c915362d4520e88a7b16a2905577359351482aa39ac9a8a4159dc964d4520a6ee8b1ea2905347458f51482b3b92c7a8a4159dc943d4520ac8e4a1ea2907154310f51482abb9a85a8a41551cd42d4520e4a84216a290537744cb514829a3a265a8a41d14c832d4520a6ce9b06a29053574d8351482ab39ec1a8a41555cf60d4520c3ea931ca29061c5498e514830faa2c728a41871516394520c3cc9a9ca29061d64d4e514830f320a728a41875905394520c6cc9a8ca29063564d46514832b31ea328a419558f519452087cedaa2a29043e76151514830faa6c6a8a41871536354520c3ea831aa29061c5418d514822f3b6a6a8a4187d935354520c38c9a9aa29045e7614d514830fb20a6a8a418719053545208eeeca88a29053774544514829a3a2a228a4155dcd5114520aa8e6a88a29063665d50514823abb4a828a41559ce5414520aaae72a0a2904777655051482abb9aa828a41551cd5414520c6cca2a0a29065665d4c514838baa6a628a41c515353145208eaed298a2905367494c514829aba4a628a411ddd95314520a6ee8a98a2905347454c514832b328a628a41c5d505314520e28a8298a2907275458851483922a2c428a41d1d4d6214520e88a6b10a29055673d9051482aab9ec828a41595cb6414520acae4320a29053674d8c514829aba6c628a41595cb6314520acae4318a2905677250c51482b23928628a41c550c4314520acce4218a2905657210c514829b3a6c428a414d5d36214520aace7b10a29055573d8851482abb9a8428a41551cd4214520ae6e0a10a290570705085148392a108428a414ddd13214520a68e8990a290573704c851482b83826428a41d14c83214520a6ee8b00a2905347458051482abb9ac028a41551cd6014520a6ee8900a2905347448051482abb9a4028a41551cd20145208bee6b2e829045c73597414822fb9acb20a41171cd65905208b
  | 11 => 0x882573a4c390441339ce61c8220cccc2a8e411052d72d8f544830fb1cc7aa241479cf62d5120a3ae7b16a89051e73187544828eb98c3aa2414b5c861d5120a3ce7b06a89051d73d83544829b38ec1aa2414d5c760d5120c3ea931ca89061f5458e544831baa4c32a2418dd516195120c9cc6b14a89065663986544832ab1cc32a2419958a6195120ccae530ca89065663586544832ab1ac32a24187d936355120c3ec831aa89064f63d89544832631ec4aa2418dd936155120caec7b0aa89065463d855448333b16c2aa2418dd906155120caec630aa890654631855448333b10c2aa2419c187605512087eecaa0a89051f73550544828e39aa82a2414ddc55415120a68e2aa0a89051e73990544828eb9cc82a2414d9c66415120a6ae3320a89045e73984544822eb9cc22a2414bdc96315120c3ac6318a89052d7218c544828fb9ac42a241471cd6215120a3ce7308a89051d739845448296b94c22a2414b5c86115120a3ee6b00a89051c73580544829bb8ac02a2414d1c56015120aace32a6a6905557195353482abb8aa9a9a41551c554d4d20a9ae5b26a69061f64993534828f3a6c5a9a41475d362d4d20a3ce830ea69051d7418753482a6b90c3a9a41479d360d4d20a3ae9b06a69055671d8353482aab8ec1a9a41879935394d20c3ac9a9ca69063754986534831a2a4c329a4195d4e6194d20c6ea8b0ca69063454586534832ba9ac329a418b9916294d20c6cc930ca690635649865348332b14c329a41995ca6194d20c6cc8b0ca69063564586534821f3b6a8a9a410f9d85454d20c6ea9b0aa69063454d85534831baa0c2a9a418d1506154d20c5ec9b12a69062c64d89534831bb26c2a9a418d1936154d20ccec5b0aa69063764185534831a320c2a9a4199d886154d20ce0c3b02a69045f7654c534828fba2a629a41471d15314d20aaee2a98a6905547154c534828f3a4c629a41475d26314d20aace3318a6905557198c534821f3a4c229a410f5d26114d20c3ccbaa0a69045d7695053482ab38ca829a41555c65414d208beecaa0a6905577155053482aa38aa829a41879945414d20a9ee4b20a69061d6419053482a6b90c829a41479d26114d20a3ae9308a69054d7298453482a6b90c229a4147dd16014d20a38e8b00a6905577158053482aa38ac029a4147dd12014d20a38e8900a69047671d97434823ab8ecba1a411ddc565d0d208e8e2b2e869047671d96434823ab8ecb21a411ddc56590d208e8e2b2c869047671d95434823ab8ecaa1a411ddc56550d208e8e2b2a869051e73d51434828f3a6a6a1a418bd536250d20c58a9b12869064f53d89434832629ec4a1a418bd506250d20c58a8312869064f531894348326298c4a1a411d9c76510d208eae3b28869047771594434823a38aca21a41475cc5410d20a3ae82988690
  | 12 => 0xa0e414d5d251d07208bce7b2c839045d73d9641c830f2a4c720e41875526390720c5ca9314839062d5498a41c828f39ea8a0e414d9c7545072087cec2a2839045e73d9441c822eb9eca20e41179ce65107208bae7328839043f7655041c82aab9ca398e410f9d3658c72087ae9b2c639061e6494e31c830f322a718e419394e628c720c9aa7314639043e74d9431c821eba6ca18e410f9d2650c72087ae9328639052e7494721c82a739ca390e41599c654487208dcec2a243905667194d21c82373b0a690e414b9d25148720a9ce728a439051e73d5240c829b38ea9206410f9da5450320c3ca831a819061d5418d40c83172a0c4a06418b5506250320c6ca830a81906355418540c821ebb6a820641479cf5410320a6ce3aa0819064e6358b548828f39ea92a441179ce61952208bae730ca91051e73d91548821fbb2a82a441531cd6215220a3ce9a9ca71043e74986538821eba4c329c41479d36354e208beeca98a71047671d97438823ab8ecba1c411d9c76590e208eae3b2c871051d73950438828eba4a621c4147dd54310e20a3aeaa18871058c7250c43882a739ea9a14411b5d661d0a20a3ce7aa4851043e76951428830f2a0c6a1441875506350a2087aedaa0851051e73d5042882c639a84214411b5db5410a20a9ce7aa085104ad76d5042882c739ea8214416a9c35410a20a5aedaa0851062d76d50428829739ea821441c39cf5410a20a1ce7aa0851070d73d504288296b8ea821441ca9c35410a20b54e02a0851052d7494c42882973a88621441c394c4310a2099ce730885104cc73580428827238ac021441399c464cca208daeb30e651051e74d4e328830e324a69944187191534ca20b18e8990651054d739503288236bb0a8194411b5db530ca20a5ce9a9865104cd76d4c32882c73a6a619441729c3530ca20a9aeda98651064d76d4c32882a73a6a619441c39d3530ca20a1ce9a98651070d74d4c32882a6b8ea619441d29c3530ca20b94e0298651054c75d0c32882a73a88619441c3950430ca2095ce930865104ac74580328827238ac019441179cf64546208bae7b22a31043e74d8d518821eba6c6a8c418bd904254620c9ec6192a31047776544518822f39ecba0c41175cf65d06208bce732e831045d7399741883172a2c5a0c41331cd62d0620c5cca216831045e73d96418822eb9ecb20c414d1c5545062087ce9b2e631043d74d97318821f3a4cb98c410f5d265cc620958e8b16631064e5358b31883273286598c410f9d3658c62087ae9b2c63105547154d3188267398c910c41a39926388620d1ac931c431068e6458e21882573a0c710c418b9915188620c9cc6a8c43106aa64982218836531cc110c41395db5108620bc4e1a8843105e27014421882563a2c010c41331cd6008620c5ca8b1081104cc7358840
  | 13 => 0x5188540c6cc828c42a063564146215032b318a310a819558c51885408bce7b2a42a045d73d95215022fb9aca10a81171cd650854087ceb32042a061e6414c215030eb20a610a818b9905208540c5ac829042a063664144215031ab20a210a81d814851d0140e1ea629480a070c5314a4050316292c320281c914b5190140c6ac228c80a0727521464050392290a3202818d5d851901408bce730ca42045d739865210237bb2a429081531cd5214840c9ac6a90a4206655258452102a639aa5a1081471cd5290840a98e6a90842058c735084210296bacc421081471cd5210840b18e6a90842052f765484210317bb2a421081c3dcd5210840a58e6a90842070c73548421028639aa4210814bdc5521084087aeb308842049e73984421024e39ac0210812d1c56010840c3eca21c642070c4394a32102a639aa5190811d9c4654c8408eae232a642062c649493210316322a499081531cd524c84087aebb2064204b671d903210316b288419081531d5320c840c9eca990642064d654c832102c63a264190814d9c64254440a6ce2212a220477765445110332b12a2288818b5966290440d1cc7314822062d6558a411034731ac5208818b9895190440958e4b00822049c7359321102a639aa5908818b59442c84408bce7b2c422045d73d96211032ab1ca3108818d9915188440caac6a8c422045f73595211022e39aca90881179cc65484408bae632a422062c6454921102a639aa4908818b5944248440e4884a8a42206a842181211021ebaec810881279cf640844095ce5b20422052e72906501021ebb083280812b9ca61d004087eeca8e802063661547401021ebb4a9200811e5da5490040b54e520c802062f65d894010317b28c4a0081a3d8c6250040d18c6312802063765d854010352316c2a00818dd946150040d4ec430a80206a462185401031aba8c2a00818b1895150040c68c2a8a802066b65d894010335b28c4a0081aad906250040ce6cbb0a8020673651854010359b20c2a0081b81886150040c9cc7316a99064d6398b54c832b31cc3aa6419558e61d5320cccc530ea9906566358754c832ab1ac3aa6419998961d5320a3ce7aa4a99053671d5254c828f39ec8aa6414d9c7645532087eecaa0a99045e7398454c822eb9cc22a641479d35394f20aace3a9ca79045f7654c53c821f3a4c229e410f5d26114f208ece232c87904757119643c823b38eca21e411d5c76510f208ece332887904757199443c828eb9ca821e41475d25310f20a3eeaa18879051d7550c43c82c63928621e41631cd4210b20b18e8990659053674d4651c82ab39ea328e418d1c56494720c3cc931ca39061d6498e51c830f322c728e418759163947208bce7b22a39045d73d9151c821f3a6c6a8e410f5d363547208eeeca88a39051e73d5341c829b38ea9
  | 14 => 0xebb1a84a045e7518d425022f3b6a6a1281179d85350940c9ec7a9284a064c63d494250327b18a4a12819318c5250940cd6a430284a058c735084250387a9a8421281c314d42109408eee2b2c64a047471596325023b38eca992811d5c7654c940c5ec9a9264a062c64d4932502a739ea4992818bd90524c940c58c829264a047771594325023a38aca192810f9d6640c940c5cc829064a062d6414832502a6b98a419281539d5320c940a98ea99064a064e654c8325032632a6419281631d1320c9408bee6b16a2a045c7358b51503a3a9ea5a8a81559ce52d4540aaae7296a2a05577354b51502aa39aa5a8a81d1d4c52d4540e88a6296a2a07276414b515029bba2c5a8a8155dcd62d4540aa8e6b16a2a05577350b51502aa39a85a8a81c950842d4540a6ee8996a2a0534744cb51503a299065a8a81599cb60d4540acae5b06a2a064e63d4a5150326b1ea528a819398c5294540c9ac6294a2a066662d465150332b16a328a811b9db5254540c9ec7a92a2a064c63d4951502373b0a4a8a8193d8c5254540c98c6292a2a04777654451502b3b92a228a81591c95114540ccccba90a2a074753d485150392b26a428a811d5da5214540aace7290a2a055573948515023bbb2a428a8155dcd5214540aa8e6a90a2a06666514851503a3a98a428a81d114c5214540e4ac8290a2a056672d9051502b2b96c828a814d5d36214540aace7b10a2a055573d88515029aba0c428a8155dcd4214540aa8e6a10a2a05737050851502b83828428a81c95084214540a6ee8990a2a0534744c8515029b3a06428a814d5d03214540e8a64190a2a05677258051502b2392c028a8159dc94014540ac8e4a00a2a063771997415031732ea5a0a818b99452d0540e1ea629682a070c5314b415031b32ea3a0a81c914b51d0540e4ea428e82a0724521474150316294c1a0a818d14660d05408dceb31482a046c7558a4150236bb6a520a819398f5290540c9ac7a9482a046d7614a4150327318a520a819358c5290540cccc5a8c82a066562d464150333310a320a81995885190540ce0a330482a066852d814150334290c0a0a819cd446050540e1ea629282a070c53149415029b3aec2a0a81c914b6150540e48a5a8a82a0727521454150392290a2a0a814d9d85150540c6cec28a82a072852d814150316290c0a0a81ca1486050540d66c230282a045f73597215022e39acb90a8117dcd65885408b8e6b2c42a045e73196215022eb98cb10a81179d663885408b8eab1c42a045f76d4e215022ebb6a710a81879935388540c3ac9a9c42a045f7614e215022ebb0a710a81879905388540c3ac829c42a062e64d4a215032731ea510a819358f5288540c5cc829442a062d6414a2150327318a510a819358c5288540c6cc9a8c42a063564d46215032b31ea310a819558f
  | 15 => 0x6f755883108636bb4a5108438b9925288421c9cc72944210e956458e210863abb4a5108431b9d854484218dcec29a4210d2e7494521086a739ca290843595d64148421b8ae720a4210f245450521086b2bac6290843695d23148421e88a698a4210da574d8921086e2b9ec49084359dd54248421b8ee6a124210d67754c921086d3ba2649084317dcd64940218b8e6b24a010c3f7458e500861e3a2c72804387d936354021c38c9b1aa010e1f6418d500870e320c6a80438b1932154021c98c790aa010d6a70c85500871632242a80439318d2154021ad0e090aa010c7b7654050086a739ea529681599c75294b408deeca90a5a058c7350842d023b38eca196811d5c7650cb408ece332865a04757199432d02a6b9ca41968153dd5320cb40a9aea99065a058c744c832d02b3396a328e819398e6294740c9cc6b14a3a064d6358a51d022f39ec4a8e81175cf62547408eeeca88a3a052e7294741d029b38ca4a0e814b9ca5150740acae528e43a045e73d9621d022eb9ecb10e818b9925288740c9cc729443a062e6454a21d032731aa510e81179cf65087408bae7b2843a045e7399421d022eb9cca10e81539cf5294a408bce730ca52045d739865290237bb2a4294810f5d66190a40c98c7292852064c6354942902c639a84214814b5ca5310a4095aeda90852058e73d4842902d5386a4214816a9c05210a4093ce7308852049c73580429025a38ac0214811d9c7658ca408eae3b2c65204b671d9032902a6b9ca4194818b994420ca40e1ca6210652054f754c832902a6baa6419481631d1320ca408bce7b12a32045d73d895190317b1084a8c811ddd95114640d1cc7314832068e6358a4190317312a320c81aa98a609064096aeda8883205b270d4441902d9380a220c812b1c960106408bce7b2e432045d73d97219022f39ccb90c81175ce65c8640938e6b26432062d6494b21903173288590c81179cf65886408bae7b2c432056471549219024f39ec810c812b9ca61d0240c6cc2a8e812054e73d9352502a6b9ec9a92814b5d363d4940c9ec731ea4a052d7418752502a7398c3a9281535cc61d4940a9ce7b06a4a054d73d8352502b338ec1a9281595c760d4940c9cc7a94a4a064d63d4a525032ba9cc32928199d4a6194940caea6b0ca4a066752586525032ba9ec2a928195d4c61549408deeca90a4a054f7354852502a639aa42928159dc55214940ac8e2a90a4a045e73984525022eb9cc2292819399753149408daed298a4a05667194c52502b2b8ca6292811bdd95314940acee2a98a4a05647154c5250297ba2c6292814b5d06314940c9ac6318a4a052d7498452502a739cc229281535ce6114940a5ae8308a4a054f7358052502a639ac02928159dc56014940ac8e2b00a4a054f7350052502a639a80292819a14a60909408bc
  | 16 => 0x8793b8aa821243cadc15410921a58e0aa08490f28705504248694382a821243399c663109218daed2988490d2d7414c4248697bac8621243695c64310921a5aea2188490f0c5310c424866739cc221243331cd60109219c8e2b008490ce6711933248636bb4a999243399d661cc921ccceb30e6490c6c75583324868e3a2a719243561c1538c921c38c9a9a6490c5e7614d324870e320a699243631d1320c9219cce33206490c6e751903248636bb4a819243535cc540c921b8ae32986490c6f7654c32486963a2a6192435a1c1530c92199eeca986490d8c7454c32486e3b8aa619243721c1530c921a9eeca986490e4f7654c3248787ba2a619243531d1530c921e18e8a986490d0c7454c32486a7b8aa619243d1dc5530c921e96e0a986490d4c7054c32487a4382a619243521c1530c921a9eeba186490dc571d0c32486a6ba88619243c3150430c92195ce93086490cac74580324867238ac0192438b15162d0521998e6b168290c5f735954148716b2884a0a432b1d162cc521c98a6b166290c3f74595314861e3a2ca98a4393594324c52199ce63244290e8e6498e2148746b24c710a43a39916388521d4cc9a8c4290ec663d46214863dbb2a0282434e1d15014121ab0e6a80a090c5f73590504862e39ac8282430fdd16314121878e8b18a090d6671d085048716b208428243599c73214121c9ac6190a090d2e7488450486a739c42282435a5c22114121c9cc7316a810e4d6398b540872ab1cc3aa043479cf54950218d8e4b1ca810d1e73d91540861fbb2a82a043175ce61150218bee6b00a810c5c735805408717324c5a98438b59262d4c21c6ac930ea610d1e74d4e530868f3a6c6a984317dd95314c2187ce9308a610c3d74984530861fba2c0298430f1d16014c218ece232c8610c6d751894308672b88c4a18431b9ca6510c218f4e03288610c7970194430868eb9ca821843475d25310c21a3eeaa188610d1d7550c43086c639286218431bdd56210c218eaeb3088610c5f73592520862e39ac9290430fdd16394821878e8b1ca410e3554986420862f39eca21043175cf6510821a5ae92908410d2f7550842086c639a84210439554e618c82187ce9b286410c3d74d9432086a6b9ca41904353dd5320c821b18e89906410e1e6498e510870eb24c728843879916394421c3ac8b1ca210d1e73d534108697396a9a0843179cf65904218bae7b2c8210e1e5498e410870eaa4c7208438b9526290421c5aa93148210d1e73d514108697396a8a08434d9c7545042187cec2a28210c5e73d94410862eb9eca20843179ce65104218bae73288210c3f765504108637baac420843479d353cc42187ce9b2c6210c3d74d96310870f324a71884387991538c421c9ca73146210e4d5398a310868f3a6a6988430f9d2650c42187ae93286210c
  | 17 => 0x1443175d46350a21c3ca831a8510e1d5418d428862f3b4a6a1443171d95350a21c6aa9b0a8510d8c73508428878729a8421443c354d4210a21c6aa930e6510e3554587328872b29ac3994430f5d7644ca2187aea3226510c3e76951328861e3b2a89944387d92534ca21c38c929a6510e1f6454d328870e322a6994439554f614ca21b18e89906510f0e544c83288786aa26419443175d66390621c3ca931c8310e1d5498e418862fbaac720c43879516390621c3aa8b1c8310c5d7694e418862fbb2a720c438b9526290621c5aa93148310e4e5398a4188726a9cc520c438b9516290621c9ca6b148310e4d5358a41887172a4c420c439394e6210621c5ca8b108310e4e53588418878aa9a8220c430f5da548c62187eecaa46310e2e5498a3188716aa4c518c439394e628c621c5ca8b146310e2d5458a318872729ac518c438b59654c8621c5acaaa64310d4e731532188726b2ca790c43c395253c8621e1aa929e4310e4d6554f21887872a2a790c438b95260c8621c9ca73064310e3565953218871ab2aa990c439559653c8621caacaa9e4310f155454f218870f2a4c7a84438755263d4221c3ca8b1ea110e1d5458f508870f324a7a84438759253d4221c3cc8a9ea110e1d6454f508862fb9ac928443171cd649422187ee8b1ca110c3c7458e50886b538642a84430f5da541422187eecaa0a110e1e5498c508870eaa4c628443879516314221c3aa8b18a110c5d7694c508870f324a6284438759253142218beeca98a110e1e6454c508870eb22a6284431edd95014221a98e6b14a890e1f6418d544872631ec4aa24396d8f6055121cb0c7b02a890e3b64181544872db18c0aa2439618c6055121cd6c4302a890e7361181544861fbb2a82a243471cd5415121a70e0aa0a890c5f73580544862e39ac02a2434b1d16294d21c58c9b12a690e3b64d81534871c326c0a9a438ed906054d21c70c8302a690e6b621815348739b08c0a9a4317dd95314d21a38e8a98a690d587054c534861fba2c029a430f1d16014d218f4e1b2e8690c7970d97434863d386cb21a431e5c36590d218e8eab0c8690c7b70595434863c382caa1a43399c76250d218eae3b288690c7b70594434863c382ca21a43475cc5410d21a3ae82988690d1e7550c434868e3aa8621a43631c94310d21a98e6aa68490d687055342486733acc3a1243999d661d09218d8eab068490d1c73552424869c382a9212430f9d85450921c3ea831a8490e1c5418d4248696b94a8212430fdd95410921a38e6aa08490d387055042486c639a8421243695c654109218deecaa08490d4c7355042486b4382a8212432bdd95410921b18e6aa08490da77155042486d4382a8212434bdd95410921c5eecaa08490f0f73550424869639aa821243c31cd5410921a18e6aa08490d2f71550424
  | 18 => 0x410b21b18e6aa08590d2f7655042c8717bb2a821643c3dcd5410b21a58e6aa08590f0c7355042c868639aa8216434b1c15410b21a5ae82988590d2f7590c42c878729c86216434b5d44310b21e18a62188590da57110c42c866739cc2216431bdd56010b21998e6b008590ce47158042c8673388c9996431b5d854ccb21a9ae62a66590d2c7454f32c868e3a2a719643471d1530cb21b18e89906590e565358432c86a6b98a8196434b1d1530cb21b18e8a986590d4f7654c32c8727bb2a619643c3dd1530cb21a98e8a986590f0c7454c32c86863a2a619643531c1530cb21a9eeba186590f0e54d0c32c86a6ba88619643c3150430cb21b8ae22186590cae7498432c8637baac0196432b1d1600cb219c8e2b006590d1c7355341c866639ac5a0e43471cd5450721c5aa83128390cac7458b31c863dbb2a0286439398d62d5221c9ac6b16a910d1e73d52548868eb9ea92a44317dcd60952218b8e6b04a910d3671d8e5488697b92c72a4438758c6395221a5ae431ca910d1f7358a548868e39ac52a443479ce6195221a3ae730ca910d2d72d82548868fb9ac12a443471cd6095221a5ee4b04a910d3471582548869b388c12a443479cf6455221a3ae7b22a910d367198d5488697b92c6aa4438758c6355221a3ee6b12a910d1c73589548869db82c4aa4434e1c16255221a3ce730aa910d1d73985548868fb9ac0aa443471cd6055221a5ee4b02a910d3471581548861fbb2a82a443875526315221c3aa8b18a910e1e6498c548870f322c62a4439398d6215221caac7308a910e6562984548868f3a6a729c43475d35394e2187ee8b04a710c3c7458253886ab38ec929c4353dc96494e21c3ac8324a710d4d72192538868fba2c529c43471d16294e21a3ce930ca710d1d7498653886a6b96c129c4347dd16094e21a38e8b04a710d4f7258253886aa38ac129c43559c46094e21a3ce9b1aa710d1d74d8d538862f3b6a8a9c43179d85454e21aace3322a710d4f72591538870eb20c8a9c4347dd16254e21a38e8b12a710d5b7058953886ac382c4a9c43479d26154e21a3ae930aa710d1f74581538868e3a2c0a9c4353dc96054e21aa8e2b02a710c3d76950538861fbb2a829c4317dd95314e21c3cc8a98a710e1d6454c538872aa9cc3a1c438d95161d0e21caaa6b0e8710e3554986438871aaa2c321c439594d6190e21a38e6aa28710d1c7454d43887172a6c4a1c438b5536250e21c9ca7b128710e4d53d8943887172a0c4a1c438b5506250e21c9ca63128710e4d53189438868eb9ca821c43475d25310e21a3eeaa188710d1d7550c438870fb2a8621c43875954310e21b18e4a188710e2e54988438872729cc421c438b9516210e21c9ca6b108710e5553987428871b2a2c3a14439554d61d0a218baebb1a8510e1e54d8d428870eaa6c6a
  | 19 => 0xca9a8520e4f63949429072631ca4a148393d8d5250a41c98c6a928520e6552d8542906c639a8421483c394d4210a41e1aa6a108520e5553986329072aa9ac31948399949618ca41c5ec92926520e2c649493290717b22a4994838b191524ca41a98e6a926520e2e649483290716b24a419483535ce520ca41a9eea9906520d4d754c83290727b2a641948393595320ca41b18e89906520e2d6594b419078729ca5a0c838b59552d0641e1ca6a968320e2e529834190732b2ca5a0c839959552d0641e8aa6a968320e4e6394b5090726b1ca5a84839398d52d4241c9ac6a96a120c5f7358a509062e39ac5284834e9c341542418daed290a120e4e639485090726b1ca4284831bdd95214241c9cc6a90a120e4d63548509063dbb2a0284831bdd95214941a98e6a90a4a0d6870548525062fb9ac029283171cd601494196ceb30c84a0e3675986425061e3aac1212839318f5250941c98c629284a0d8c73508425065b38cc6212834b5c85310941b4ae329084a0caf7654842506c639aa42128369dc55210941b50e0a9084a0c9e73984425064e39ac0212832d1c56010941d2886b0c64a0cb671d91325063db82ca192831e1c1650c94196ce3b2064a0c3e7519032506a6b98a4192838b594420c941e18a621064a0d4e754c832506a63aa6419283631d1320c941d1cc731482a0e8e6358a4150753316a320a831edd95014141ad0e4a80a0a0c5f73588505062e39ac4282834d9c64214141c5ac4210a0a0d2e72904505069cb848228283539cf52948418deeca90a420d2f7550842106c639a84210832d5c4644c84187eeab206420d4d7394832106a7baa6419083535d5320c841b18e89906420e4e6398a511072731ac5288839358d629444187aed2a48220c75769524110762b1ac520883695cb6450441a6eeaa128220d9773509411062fb9ac528083171cd6294041c9ec7b12a020e4f631895010726318c4a80838b18b4154041a74e1a0aa020e2c62505501069c38282a80831edd950140418bee6b04a990c5c7358254c870fb20c6aa64393d8c6255321c98c6312a990c3f7655054c868e39aa82a643875516315321c3cc8b18a990e4c7258c54c8726b1cc42a6439598d6115321cccc4b08a990c3f7458253c861e3a2c129e43875cc6454f218beeca98a790d1c7454c53c870eb22a629e438b1c96414f21c5ac9310a790e366458453c868e39aa9a1e43475cc5490f21a38e8a9c8790c3e7695143c868e39aa8a1e43471d15350f21c5ca83128790e2d5418943c8727298c4a1e439354c6250f2187aedaa08790d1d7315043c868e3aa8621e4387d954310f21c3acaa188790d8c7250c43c8672b94c221e43531cd54d0b218daec29e8590d2d7414f42c868e39aa921643471cd5410b21b18e6a108590e365458442c8637bb2a821643531cd5
  | 20 => 0xc64951320ca67bb2a899065331d9544c832d18c8aa264194ce76151320cb46320a899065c3550544c832d1ec9b0a641968c64d85320ca673a6c299065339c3614c832a9aeb30a641958e74985320cac6ba4c299065a3192614c832a9eeab0a641958f74585320cac63a2c299065a3d91614c832d18c8b0a64195cb70585320cae4382c299065a3190614c832d18c9b02641954d75981320cac73a4c099065635d2604c832d1ec9302641968c64981320caa7baac09906563dd1604c832b18e8b02641968c64581320cae3b8ac099065711c5604c832d1ec8302641968c64181320ca673a0c099065335c4604c83299eec996a21958c744cb510cb4732265a8865a359132d443299eec994a21958c744ca510cb473226528865a35913294432b8ee2994a21953674d46510cb1a38ac92886533dd93254432b18e8992a2195c7714c9510cb8621884a88650f9d0605443287ae8302a2194cf764c8510cac63a264288651ddd95114432e8a64a88a2194cf764cb500cac63a265a8065331d93294032b18e8994a0195c8704ca500ca3bb8ac9280651d1c56494032e1886214a01943f74586500ca1e3a2c328065331d93254032b18e8992a01968f644c9500cb4632264a8065721c13254032d8a65b0aa0196c532185500cb1bb26c2a80658d1936154032c6ec830aa01963464185500cb33390c2a8065995c8615403299eec990a01958c744c8500cb473226428065a35913214032d8a65308a0196c532584500ca3dbb2a02806517dcd6094b418b8e6b04a5a0c6f7654852d06a639aa4296839358d5214b41a98e6a9685a0d1c7354a42d06a639aa421683631cd4210b41a38e6a9085a0d8c7354842d0697bb2a4216838bdd95210b41e1ee6a9085a0d2c7354842d078639aa421683431cd5210b41a58e0a9085a0c9e7398442d061fbaac021683271cd6010b41968e2b0085a0e1f6510e32d078621ca519683531cd528cb41c58c929265a0e2c6454932d06a639aa4996832d9c7640cb41c5aca21065a0d4c754c832d0727b2a641968393595320cb41b18e899065a0cb57498432d0752212c2196831edd95014341a9ce7a94a520d4d73d4a529062fb9ac129483171cd6094a41acce3b1ca520d2f7458e5290696ba0c7294839358c6394a41a9ce730ca520d4d739865290696ba6c1294834bdd16094a41a9ee6b04a520d4c7358252906b238ac129483599c46094a41a9ee6b22a520d4c7359152906b5b82c8a94835a1c16454a41acce331aa520d2f7458d5290726b18c6a9483539ce6154a41a9ae730aa520d2f7458152906a7b9ac0a9483531cd6054a41ac8e2b02a520c5d7694c529062fbb2a6294831bdd95214a41c9cc6a90a520e4d63548529072aa9cc3214839554d6190a41ccca4b0c8520c5d75d8d429062eba8c6a1483179da5350a418b8e
  | 21 => 0xb87396a821c65475c75410e32a3ce1aa0871958e72150438cacab88a821c65879516310a32b1ae4218851958c73508428cab2b88a9994650fdd16094632878e8b04a31961f6410d518ca3bbb2a228c658d5915114632c3ac821ca11943e74185508ca1eba0c2a84651edd95014232c6ec330ea89952d72187544ca96b96c1aa2654d9c760d5132a6ae3b06a89943f76550544ca3bb8ac02a2651d1c56015132a6ce3b10a89953571d88544ca96b96c22a2654b5ca6115132c6ac2308a89952f72580544ca9bb8ac02a2654d1c56015132a5ae4300a89953671180544ca9ab88c02a2658715263d0932c38a8b1e849961c54d8d424cb0faa0c6a1265871506350932a58eaa10849958c73508424ca1f3a4c1a8a650f5d260d453287cedaa2a29943e76151514cb1daa6c0a8a658e1536054532c76a8302a29963854181514ca3bbb2a228a655c1c1511453287ee8b00a29943c74580514ca1f3a4c3a82650f5d261d413287cedaa2a09943e76151504cb1baa6c2a82658d1536154132c6ea830aa09963454185504ca3dbb2a0282655c1c5501413287ee8b08a09943c74584504cb33312c3aa0654d9c75495032a6ce3b22a81964c63189540ca1fbb2a82a0651ddc560150328e8e2b00a81956571d53420caa6baec7a1065715c463d083299ee6b0e84194cd73983420cb0eaa4c7210654b5d66410832acae3aa0841952d75950420ca37bb2a8210654bdd95410832c5eecaa0841970c73550420ca97b8aa8210654b1c154108328deeab1884194cf7558c420cb27baac62106533dc56310832998e0b18841964d65d0c420cb86aa686210654bdd64310832c5acb218841958e7390c420cb46b1c86210654b5d44310832c5aca218841964d6510c420cb873288621065a35944310832e1aca218841960d6510c420cb4621ac221065a310e60108329cae2324641946d7694e320cb473268719065a3190438c832c5ecbb22641946d75991320ca573a4c8990658bd94644c832d1ee6322641968d73191320cb16324a699065a3192534c832d18c9a1a64194ce7690d320cb463248699065331d9434c832d18c8a1a641968c6410d320cb26baeca99065339d3654c83299ae3b2a64194ce70d95320cb273b6ca99065a3d97644c832e1ecbb22641954d75991320cac73a4c899065335d6644c832c9aeb32264194ce74991320ca473a4c899065335c6644c83299ce1322641954f75591320cb46b20c899065a39d0644c83299ae232264194ce70191320cac73b0c899065a39d8644c832d1eca322641970f65191320cb47ba8c899065a35d4644c832d1ee2322641968e71191320cb46b88c899065a31c4644c832d1ee0322641968e70191320cb46b80c899065a31c0644c83299cedaa2641968c64d51320cae338ea899065715c7544c832998ed2a2641968
  | 22 => 0x285559c75394c428beeca98a62152d75d8a4310ad2b88c5218852bdc96190c4295ae530486214af755884310b17baac4218852bdc56210c42958e0b10862143d769524210a36bb4a921085a398e4390842c3ecbb1a842161f6518d4210b47b90c6a1085a35c86350842c9ecbb1a842164f6518d4210b47b20c6a1085a3dd06350842d1ca831a84214ae76d0d4210b4631e86a1085a318e4350842d18c6a1a842162d75d954210a5739ecaa10852b5c7655084295ce1b2a842162e76d954210b47b2ec6a1085c3d976350842a5aeb31a842158e7398d4210a97baac6a1085a358c635084295ae231a84214ae7018d4210ac73b0c6a1085a39d86350842d1eca31a842170f6518d4210b47ba8c6a1085a35d46350842d1ee231a842168e7118d4210b46b88c6a1085a31c46350842d1ee031a842168e7018d4210b46b80c6a1085a31c0635084295ceda9a842168c63d4d4210ad338ea6a1085695c75350842958ed29a842168c6394d4210a563b2a6a1085a318d535084295cec29a842168c6314d4210b86a98a6a1085a3d8f6150842d18c7b0a84214ae73d854210a57386c2a10854b5d66150842b1ce730a842158d739854210b4631cc2a10854bdd56150842b1ee6b0a842158c735854210b47b1ac2a1085a318d6150842b56e0b0a84215a8705854210b46318c2a1085a318f6050842a5aeb302842158e739814210ac6b9cc0a1085a3d8e6050842d18c7302842152f755814210ac7b9ac0a1085631cd6050842d18c6b0284215a7715814210ad238ac0a1085a3d8c6050842d18c630284214ae731814210a56b88c0a10852bdd942d4442b18e6a16a22168e6350b5110b46b1a85a88852bdd94294442b18e6a14a22168e6350a5110b46b1a852888569dc54294442aace7a8ca2214af765095110ac639a84a888569dc542544428bce6302a22145d731815110a57bb28428885631cd42144428eeeca88a221725425445110a57bb285a8085631cd42d4042958eca14a02158c7350a5010ad438285280851ddc563940428e8e2b1ca02145f735865010a2e39ac3280852b1d94254042b18e6a12a02168f635095010b4631a84a80856a1c14254042d4a85b0aa0216a5421855010b2bb1ec2a80859518f6154042caec630aa021654631855010b1b3a0c2a80858d5d06154042ccce430aa021665721855010a57bb28428085631cd4214042d1cc6a10a02168d635085010b52a14c228085a950961140428f6eca80a02164d6398b548ca3bb8ac12a4651d1c5609523287eecaa0a91963554584548cb26b1cc42a4659558e6115232caae7308a91963664584548cb33312c22a4654d5c45490e3287ced2a2871962e54189438cb16aa0c4a1c650f5db5410e32a6ae22a0871945d76d50438ca4ebb6a821c65639cb5410e32a3aedaa0871961d76d50438c
  | 23 => 0x400000000060010008000010001000006c0020000008004012000000804000000d000000403e0010000004000006001002c0100100000024002012002000c0040010128058002000000801000000000b800800a001000000800200000080240040020088020000013000000c0080010010024002000002000000000e006800801c000000001800200000200340180000018008000000001000400200300101580060050000008000000002802000000e0000084002002000000c00600f007000803403500080040080070048000002005008802c00000000d0000012000001000000a000002001000600300e8000008000003800c01c000001000c08e00000d0014000000003000000000000b80040200010018008000003001002801601b007000001000a00a801c01800c000000000a00700480080000000000010010000001000c002001000000c0040070000030006015000000c01c00000180080060000018000014000009803001e010001000000000c013800800602000080000240040030004000000000800400a00200c0000040019003000000000100000000040010000028000001004803003200b00000000000040010004008004002000400400000080000020010188004006004003800001a04200000340140140020038002001000000000c00100000280000020000000002003002000002e002000000003e000005800c0260050000060000011000000c000007002802400001200280000000010000034004000004000401400100480080080038eee2b04a7a14747158253d0a2fbb2a629e859554d6114f428bee6b04a3a145c7358251d0a3bbb2a228e859558d51147428bce630aa1a145d7318550d0a3dbb2a0286851ddc56094e428e8e2b04a72145f7654c5390b2aa9ac229c8517dcd60946428b8e6b04a321477765445190b2ab1aa228c85179cc61542428bae630aa12147b765405090b2bb0cc3a9a85475d061d4d42a9ae430ea6a151d74d835350aa6b96c1a9a85559c760d4d42aaae3b06a6a145f7654c5350a3bb8ac029a851d1c56014d42aace3b20a6a155571d905350aab38ec429a85555c76214d42a3ae9b08a6a154d72d845350a8eba4c229a85535ca6114d42caac2308a6a151f745805350aa7b92c029a8555dc56014d42aa8e2b00a6a151d741805350aa6b90c029a85559c46014d42aaae2300a6a164c5398a4350b27a98c4a1a85179ce60d45428bae7306a2a145e76d4d5150a2f3b0a6a8a8596d4f6054542cb0a7b02a2a165b531815150b2c298c0a8a851ddd95114542ae0e0a88a2a145f735805150a2e39ac028a85179ce61d41428bae730ea0a145e76d4d5050a2f3b0a6a828595d4f6154142ca8a7b0aa0a1657531855050b2a298c2a82851edd95014142ae0e2a80a0a145f735845050a2e39ac228
  | 24 => 0x3200500a800000000000000a801800100000000020020060040000000014801c000002000000000a00600000000100030030000000000000801800c025002802000a01900f005c004003016000800400100500240200010078000022001000001800207300100140020060010018000008004001002e0030000004024011007800000200900c8000000000000800800a000002003c02200200400100000010000000034005001800000400c0000018040000002000800c004002000400000000f8054002000000800800a00500e802800c000000800800800600100240000000040000010000003800400000000580a800000301780100000000000060000000000000000400c0028004004000000002800600600000280140020010020000003000801c01e00300c000c002009004000000000000280180280150008034000008000001c008016006006400e0060060004006004002007800200200780000100220028018000001005000c000002000001400e000000800002e00001d800400001b00000080040010128000024029001004800400a0048000000002001000002a003001801000400200580080040070000018000002002800000e0020000000000002002802c024002000000800000500580040000000010008010012006803000a002000000400000000000100000000010028008003005004000000200000500040010000000002001000801c0060010018000000000001002403a000003801404000100c801001200000b800400e001000001000200100100000020000028000074006000001801a00d000000c010001002800400c00100200100060020078044020000000000000801200f003800e002000800000400101a800000a0000018000006032002000c00a001000802400a0030068000012007000801400c001008000c004001005800007600c003800800200600000140040000020000002003004001400800400000a40060020010050022004000001000001e0000040006007000800400000a0010000002001000000c00201b000001001e00000680080000020000028004018000800400e003004000c01a003000006000000e004003000e003001801c036002000002400400001000000000040010004014000000001c000007001000000400000100040000000028000004000000001c00001400080000000100000000012006005002000001c0060010054006000000400600000600200020070000000006000000801c0000010010014004011006001800800600100000000000018010032007002808800600a00b800405200600b8000000000000800001000800280080160030008000000002000801800201d000800000200a000001000c0070000010012003000800000c04d000000c022000003800403200
  | 25 => 0xb124aa8000000000310a37193e73a5ee87bdcd66690524001a020003d98e2b1747d14200e046e8f370472231e3a6cb2b677354360006290000000c72ea228ccf9e00000037486f72be6df06158bc00020ba2ddb540000001ba037e6646f6c00a008002000000001b001000c02400a0018000012009000802402a0000000000006000004002c016004000800c00c000000000c0180010000008002000018800000e0050000004004009005802800c00200000040160010018008006007000001801c001002802000e0000000030002000001007c03a0030050018000003009001c00000a000000c000001000007c00e00800580040320000050000004000002800c000009005001000600800100080180000000024008001002800004000100000280bc0030058100002001008004c016000002800800200100600180040040000038006000000006800000c001801400000d00000000040080000014000000001001000200d000000800c009000000401600a008801000400100000040480020048028006001001000001200c00100040020080090000014003004803800a0100000018006000003803c008004002000000200400080000040000008018010002000000c01200000100140120300040014004004000801000a016005003001200800000000080120030018034001001802000a005002000000600102f000400200c005000c002003000801c02400000000000000030000000002004001001c002003002006c00000200a8004006002000800800000000a0000010000000001000002200400000220050018008002003003000400201100100040200040008014036007002000c010010002000c014000000801000000200480240020060000000006001002804800c002006000c002004000001800a009000002401e01700000280000010008014000000001000404a0040000020000008004003c00000000a0024004008008004802c00a007001c01401e0018024006003000003000600800b001400000100080000060110000004000007001000800000000700bc0040020090040022000002801800001300080000240000000004004001014000000c00e00e002c0060060000030008001001002402a000000001c0080000050000000000003004c000013003800000e008001001c010006001001800000b003800400200300580000000080060000004002000007000200200100000020000000004002000001000802600c002800400000200100040080010000010006005000000c00e000002000800000c003800800a0040018000000005004000400001e00400300000010008018014000000000000400e000800800a0050020048008001000000000c001000000000c00a001800400c00b0030008006006005001400200b00080
  | 26 => 0xafb960312e366438aedbfd3663b382596d60004ce037c8480371d8fb6d3d0e605aa70681da9265832ed166c2fa3b69dcad46f2c2fb398569acf619da1dc0000001f400011b6765729afb10ec00000030e0eba07b0001382ff600000030b9510b5821c400079800011a4a8893cc7a6f2d764d3a1e50000c50a8a0006390f5bc102c502600007a450c6f9234c000caf057a8708aa000000041a0000554abca283bc0000000000ce600079b2ee0392960547811000014e32d15b93520002893c7cd4800069fba3406ce8b34d19f55ebe744e300014468a30003a404348a11c38bb8c2258e4768001df09a30002df18a8000109cb8caf2b306bc00000800001a5800000074e4ee0000000000474eb70aa30001c42fc0a7f6dc698ae89676c63737a3699b02826991a586a6a0eda740000005470000000aee00038a22c4000b5b00000013583ac09ac0c473edc63e19bd4ef0a151bc7a7c000a4977d2d49cb5d654e4970494e03fcc420f01c46012c3b2a1148d056b2c0000e80004bc82578564910002f2e9f4d510001918000233000000000000002f00017c014733f2840000000000005ee4c77e39e00000d6eb26948001d865000f4a7940004870000499e82e379c0400155282844d00016071a71c75ec40000007499940ef626b71e1758f01a5459faa15dcc07d33fa6ada746a94a365edccd49f36928a4850bdb4062e9a2b48b03423301014b425dc92d46d217213541b00000000b1125800000054880000000005750000000cfe13b35c94aec1700029be620db000036d9bd256007ea2bd8d400009ba571b0ce10751337db18f4b1588454e0e46a1fd9f2593a5fa1bbd814ebc73758c23b9a1ac574d2b08480e11da738594318c1543a8a8e4264772b817d054fbf5262cf975424aa581793ce943a33ce0804a14a3000002d15828c75072c3e0798e54d6b2ccd3239354c34d443a2abcedc0eb5e831d205205d7583623052eedc6a8b7a6781e40641e128207bbcf2000197a1a94620000000d580000bc0001bc48e50004c6753dd06498000216118d01a5e7909c83af4700037b0a64473eab0f940004f771c9fbdbde8fa4bd5b20194ce7766243000097852680014340005b018c0600907645000717a67210a88249dc06ad55a1413161f3000000000025f63415c89fc2e2000011700b89d0338284d6c7ec6c40b295e44580000000dd44d274f248dc020000002c68de60001a7974cd0a2ade3bb35206a5e121a00000009150000000000d986eb0eedbb612211c2518000000775d42d7af00048e0000000000166a1647af05b59e800165e0000002af000054000000000007021dc3855302003714800000005c0000000000735cf130416bc2a1a1b8000d3edc100002b20000ebebe23f51d249b1708fa85830d305cc271a087000f8941c5201a54c512ee0
  | 27 => 0x86075c0fa14045b202a40b2e84b9808100000018793452a991bd543a07017bc8043c4846fdc1299584fc00000000000000000e40000b5f6bb80011c1bd8000000093a51852200007925488002cc4b26c0c3b98001608b690001b0457a516697a220000333b27400127688e0003c1853aad50001739b1a322049400075eeab6951fdcf54b4607cae9847c44b2219af5a106160a78000c7024f1e18752422d2313d90c4000dd5000035c00029f6dd1b41afc33036e80000000001a2031008174dbf328859a82b36b53079682c8872c9b8938a47062b1f05de22002f6bb8cd28a9355fe9b4f22b7e79f0634f2014a68b3b65546094000321512c6a13f5826d9628e758d8000c82c22152d67d5b9d5b2adc00000068700010dfb068e42dc9dc591ce03d29b7fdbca77c3978d054fe3a11fc86c170a7dc20d9e849002c4ad2b9cb51a0004378000000d5d4f21252000e5c00021457f4c12000192c00056ba41b4ed6a80d92547ce05d03b4b6c00504fa0de80029dfc6ed55000257e000000196486c000412b6a963132e0006e3b4e5c04adef000000a7895580340003520000001f86bf0c0000000000001ff8f6019169c000000087e000255bbd1c617a033f638df7d9e90003ca9fb469a309045392770c9b880000000005e0ccf0723caa87e4229cb05a6810665366ce26061e198308151e7a3f8b4ffbd9423800341600022c13b986414faad00f07b46bc76b04bbbb15f0e522b60d5c8b4cdc31cabb95ea0005052a4e000eb500021740000000001d5c291a772dc0d81d5c000000000141a00037f3afc0000005df88115160000e9c000b2c2f1000308000082268c22353085900001954b22bf62dcc000a5c11a1e7b23b1db0000000cc2e5a72b5872858158324d0903ac00098f1c5a89c000b50637379d104993dc406b8d1c8270e385a9d961318000cb403565700037de00000000000000003cb48db258000a8bc4e0001877be65e70e99654de63c70000000a4700024482c63ad758800104c00e00022fe10c60413d183cf325760de3999538a7d22483c0958000000037400054300002be000000111a57c0000000000c085241db050cc2da36000409ce4e0002cc18f00001850003b19b68874ac449506a99d6cf91ba8b201fcc07252b3b0c4e5aa94d2e25b624464beec2a51ace3055546fd9eb083d230bc96403e8c431803f6994819e4186fe3d08a61f200dc1cee425478e2e0fc64d0045288c7f051104658e65d21cc91979211888bc07d1d0537621080b7388ec7094174ea1df06ea1accc26098c32143e60e9144628189e20ef66b71eed9870c556ca0855b0e4a000162d8100000000860000000000000144c10e0000f9c00019c48846f4b86112ba00b24708024122006c66c04551f37798ca50336510fd96cf1e34d80013e4eba1f60001a850001
  | 28 => 0x14e49160000000e247a92d00000a8d2581610c326eb547a5500007f45686c207b39f9c6073b135e138508e2e11205e540067500009d371400000031118500000000000444f4941c8001e8800018e00001160c34beb3349054084d71f8d97244c77e157d9e3e0d80025773709ff6519d240005ec03e1ed8000683256a8d8b7c5464d79d11b24b172fe00000002c233ca261c7e00009c8001b12167000074859c8f908390eab0800061fc000f7a8ab63d8001cdc00000027f82360201488e607e0890607243848d00065c27987acd066fc63d50bb710141adb4000000000387c000d00f6880000003916420aa27655f335780008543944b6800001461c4b24864000b294fd0001c84454563b3a00002588000fc93aeb048002c840009531e28000000a9c9bd0000bd4a5b04f8001de800063a0c5d534c4a0003be400034318f800007093000019bde0100049e9104000e5dea1ba306baaa0d4ec000000ca24cdb7cdddd973496aad19d20000f6400064000048caa5600000000000000000910000a15c980c7f4a252e0000007132c04000d59637c0000009ba4d329a6000ca0157ba3d40ae252fea038000000516b0fc0000ff0000b018f7ea530c17fd350b3952089d00000000002e75b2cdad0d2f6f400000016e0674000ae696210080c13120000291d6600000016a9d8ad940bd0000a2a1824680000dfa7e85ba00017061dc5d72d880005169c696f1a120004151e7c00040b717800000045f6b6b1383365814c8b7c471b11c11685604299b54c6a264a5619e72d1d3fd5844f12722f20002d5eb4a9a8000e450001e303f0c764cc80000a7e2d000000032400000024400000005cb2d916e47f3318b9e11dd00037fae4d9c7bc8000000000f62000037ec9a14a461f40000009376089225562e9c000000027400050b898a0003f5709800000000037b0000a2b90169cee480001b836d8001d7818e1d8b03d544a590000fcc0000004d0a541c81bde5421c881e864b80038cc258116121afc508c00249f8354de8c9c00033e09de73782580013b0000000320843800044300011665d16fe2d98000c0a1ca99889a025c00004be51d0000000000c3a054157146b8cc9925cf33f461a000000000129100000000000000003b114f5b668970002fdf5863e65eabcb44dd0000000000f7000000000000006476a73a8d86abb00000001a040001b38c44e34e6a3ee80014e9da2231933400000000020f40000004b4c5d89862fb0948aa8eb040d3ba169800000000000000000003a280000000e901e31e000001bd9c4b44000ae053232b800000000000003e4445115211000066e38414759920ee61d2f100000000000000000114d241a602ea9ee27da73a00000070a199dcf67644d8b61d9b43d719e1d1cb3ae6513482f5090dc40d0800035b0002e2b5f4
  | 29 => 0x8da8b0f721915c000011e2580de542c3c73985b51be0004b3245c00002366b1c0ca125a109b19600000348000410000b565ecc000000a3578f7114cd0000662b295e2a15f19eb33c8b817b57f2d1c55375b59e03980009dd32498500006862f220fc64fde2b3020dd62800000037e00002ac2cc00013239822c4a59e0003724c947dc04943854b14cc00000005c39a64767f80001bf1540d824b0aab6aaa6de1f8a7b0383e6c528bc682216ae2fc98d00e6b8b6c22821cfe47920e2f902de3215a04c9079ab6c6b4249d1f00003e11110000b992af2c4e0ea0001e82a32372cff5aaa409e668132c794b71e083137606dd39cae74b1c0000000005d1e4287970000002c310464b4e2f800000081793a80000000000fb33041924334878058e68daf0000000e2400000000000000002f00e180000000002d94626bb55d28001e640005f795205ae015a5c2cac6a277d784bb7408900000003fb6940001458758000335c089c3e7c00a02ae30b4224bc1000150a2ae0007582ac8a6c00070e82336a2c065722a40484deb70da74c8e2aeb1b6280c4b35990001ab0215d0b1690000b3600018cadd8a835b45bea3990c4caa0000000cd400053aced04e6987caa013c536d246fe6521d5400064d40000003310000000f3aa9f2d0304cbfc00009a7175a07abf3aa93940b946b0002997e9063f0ae8000b10d4d000123833d000000000102a65f0002b864688242328a98a5224a720c33c000ea821717994b0bd10e232497f867b0d20e153f200000012f91c400055e80000007ad00000003646710000001c4000000009b80000005378000a92dfdf721948000cedf702be60000000000000000b2553db96c0000003c01e942a8e115b415f1af4a7e59a11b9aa49f556987adb7e436309236fbed00061da339bc4aba0000230f967690a810ad554dbc0000edc1b325126da0c81b6bba270acdd2a50855008b980002255f29ef06ed00076084953942ab4d51ae80f48a940a7918410da351600015245d4000000101a9a03a1072a3c045b1504f014f075106300000001735030000472499193858106a49c0002318d54a3d429000111bb780001a450a645100000000000006dcb9a0c80abe4c4c0005483b60000001882a1416780000006a044080855be90e80024580000b4aeb8001614000000000000052b9c000001124e4000000000098be6429cfa6e60b4c3b5d9c1e8471ac0340b5886d1ae3070e14e2b7a28000d6aef2000153d432bb10000001e5400006000004cc00062c800000000000033ba78458a368800000000000004cc0001841bcf8250b4844d5ab6e06b2e118938000072b61183119caf6a5216a0001ac8c732aa32ed3aa7a02088e5c8bc3e466a84ac9202799471aecc469f30f3898000072a3ac80000000000003684c6c17f000358d780068
  | 30 => 0x4acb3e800000000000002281c65121a210c26df26400011b2d200e78a9393cc020001e1989d00074e99b0d180000000001e4cbfe8001464b5c810eefea9730b07f78681f874a0b5e6270042328940b4b5251ee04247036d401ae4100402613b5000000180c54e00000024e00000000001c33ca8000370ac81c0acf28000000000a822c2898c9f08f380000018017be3eca480000d8e1fd0e9c00038e5e9c0003c400066eabd8000ce04aa42a40000000000001bec4560000dc4824f255968000c840000003b3973ec97053b9880003254d240000000006a1c000606bd9059378da221780001bc97961e98003d09d081c9df1a078ff4000000041979aec829f22b2000000000000116900025a084a0009003bb8a764147286cf92ac6da00009f39751644f90000000690c9c8002b587ab1ea0002e9dcbc20219ca7a8296bbc756b77ce228835ac86444f7a0b14ff540e42b773241f15c2c121425bc6000000000000521b04cb05f3cfdc7a8f26d58001e044f12b79aa021aac645f51b072c0007630000000000136169dd708910002a240000003dc8000000000000201800000058b0000fb639a1a300003990000001f847a60000001fa8000aae5888c8ab3498515c89ea732ce44df9eb027ea3c3b0000035800015925b106c282c001a48b6277cdd497d42140006129bbd0feafacedadc48a00175aeab8ee0a2264a1b17e8449322872485e0220b000132576b00000009f673117700037ce794e64f938e5e0009c8000002d28b96a0000a644ac00078d8000000000000000194996e782ac88a220000001d5885584231580001c2990482b7015730006c5afe1b4c0004388ed44c80003f380006698fe2ebc000000c3e00000016fec6903b8000000e800002f8518400050bc000000d970112ba547108069e13a0cf83f43b5252c03d78435c8756459088000134e0000005bc8ca199640f8002d1599854cbb611840006ce0002d3c00000072400000007e98003a20fd275012a0001986000795b4b417e0000ad800116d98e10bd77517cb320000e28270a7fba9a4d840d5888000bb4000e4e1ee1cc12baa8180006818640004129af00001fa0001b3007481a5f927b4b4633a7610254fe87254346ce096681c196247998837d0003ce997b84956e8000000d2747974b1dacd1d67a23137d0b8d23432fde4256d19c14c517864e39f80000000006a591b4000000000235c31e8f400000000009c22beab968069930db223c8fa76f9f79a255bc994530aeb762000057169f04eb96421cbc3117e00064621b194e93e16d229910a1e36ee1a05592dd013c63adc46008f9480000003b275b9e20000e190002e01a901df0001c552f49980003064f2e4da2db0729c9ade400030dcf1e92b672898e000958052c001dfe0001b5190ce6a0005668534000000000384
  | 31 => 0x18e088730a004c0b4500071d3cf0d5abe907c38ede101d36ba21c85d8c6757c9443dd2ee50ac83ecc18a730a42bffd484006ec14344cd2f53c19dc0a89e0af382548940c9b01800010bcaf746a36a1bd50005431b646849f872f800035aa419ea16bc0070003246ff9bb40000002abaae219a6f3c0014120003580000000000678a3318a095183000018ea9fb5788272000bfb2e7a0a502854b0000dbc00072005803a88f66615418c981c667a3e025066236c354a800066e4d14e38000aa00004a2a24c00000016b000015d41427a00005deed70000000fc8997ef2424800000000014800000005cd023c5300002e400017c483b00019140009e128e24688406f80003504000a393b3068d0ae0d12432320ac56900ed20490ac0b53e200d105ae3429c1ed4fe00415218299ba2b265190a70d6ec4f00001b46f09f40002c246667ae0000bdd38600060488162200000fc8830e9e00000000019a0cb55b983b069ced00000b6d382e8e0003a2400069c2e53818ccc00034598ec6e063e45b24cd0c0a1e306bb500185350003d18d4e95e800333859611180000016dce05a70c000000ea669f2d69d88bf300038c4000220000000100a26537492842260002c91c70c6a0003628adc000b350ddb5cd1c33d90000001ac0cd900014991bd2366c00000000cb700000015a270900002c4b56f0180028ea000d91054c3a00004f50000ca5af600000000012c623c000344c0000004d156fc07b85680017bc0004936b100000003a926c875ddb041f25d83c45ca00f5d1b41da8eaec5782ec9b40b9b128048de1eab8b26b45d95a8f619f219c9c012d3c6814a43e5b005722d5c7de9716058089c4dd346510d5a1c6320a9811b0c62dd021b400668a4c73bb1602a4c75d0c0c4a9143da464b5bc9b838c5359de445540c6fb85f0a74e641290aa09cd90467a83900fd913ce89041468a803c0a6f9c0e00065d2a5c8fc26f6fab604a5ab02117a9e420382f0b5904c000a652b98f1800000000038c96e0e4b47192097bea9d1df19b47f830f6851c2e0003bc49e032016c471800000136700000018f450083a0000000262f0474080bf4407486e785b92eea994b397ddb38547be7382815b8331432c78560000599ad4f93d384800308c00005326d720400084d24d12549d6c01aca840d5f60006ceb464c5f1906ac07b83eab2306588d4cb265b2d90000cd60001bd4478b8cef058584da000000258c000f6e51a0671efc5d2ab6672c73fbc70001a01e1cc3e00000007fddc22613cb0604ff2d5445971f581ab3f92e9ce634c0004e6035896b5b76d4a1f09bc0003869ff905610ecfb8fdd3d6e0d478a941a3819456a02adc671ce69e800027a74d0000001a68ec9000206a98471ca374000490520a6b80000000005212cb1baebfd2b35f31559000081170800000
  | 32 => 0xc33a08c0aa42bf000060d5da5780380b192bc6827142304f24a5f1a53cd4fc0f433bee619e5cdf90791575c77b1c566213c4eff280001958a817a3000247425025b138c0b537602b6959b59450c936cd21719d707820c8ee409049428a437858200000000019c28d8000265ba8abea5d5c96456c45229525f00007eb8001248000a135078000000940d230000d8c0000000000f74f1c079af48b7a2f84d11374000000000080c00038bcf78001b209cf00032a40000002ad0000000a3b2a20000000942ef7008ec54000084c0000ae2fc00000012060000a2042e0005864453782c4c0765c729a400054a00009f1c08c147339ed00000000e6020c00017d4421128fea0001c2c001a9400000000000001710002f1d1b98895e601335d03818000ddc0000006b3800000000000000000a05c4000177048223763c8001a5c0006d633b2000000552ab8400040500000017204e65578001ac20000001545368000000000144a18b00000013b20005c0b4687dc0000f6fb9c23e45d3ed1be838284c53425aa00000071f08925bef3b06680013664480001ce5e9800073687552b4c48279000000000061800013608d55c62349292d6c4570000d700ad76f1a88000c62364b0594e417e000000019827e000309800000032a2d0c704d458550c0462700055e6691388bd310a2f29cc564460e80820002a96581cf4c0c6b21ce33095a0d030000000000db7271bc4cee74b12a08720e8600d8439db86a897f00033c3124dc8279c000bd600071a7448b440005e11a01648e4700000000000000af02dc98000043280000000055868ad40000000002c144a90000002b9800000036382e80000002918000000a400002989ccf3878b4109872bdfa45694c00b001c61a17c40004d6705800159e0000001a94aea0003a600000005c000000016807a60fe1aacbd00040002c753bc00028f800085e87a75f028cbd2c8389717555ae4df0b22ed92f34535598275632cea668a9d5518ac01d52674000bacca6daf988c88b26a255908644260f800169000040e7bf96f4afb982a8e1411049023a78ca503fd2078d4989fefb4a743bf6b8aa8488c8e8c8f56b1e8a74941944e6fa400185404654a07a3de951470cdca48c0e497318000fc40000003c3849241a0f209a600020b80028b9af20136e4a1a000000007003709744c5105713442e8d63120067d94225c0e9725d42215bca1094ee42f024b8000350ec7097ba80c4400038c8ef40002d53a0a086d143c70000ae800093a77b84ed431d1400808480008ac0cb2d4d1688b839890573d28c400000013114590e3c7ae83000028400000007d84cf8f20cec01d0000e4697501200032f1a4c0000000000000000000263e000e50010c000000cfc33293a53bf0005fbb1845d48f378a00010d600004129581e38340ce48
  | 33 => 0x383000000000000002e800034f198ce212f300014ec53c10c000242000042c3eab124e1601ca7f748865631a64302e2ca233542513605864b60000000000b75000043c03283e0000001ce20002f700000a28b9aa9c00072d5645d6ae10bb0c470000000000c6c00000004db0000000001372ca10420000c3c0001cf00015b429476ab1bc397000279bb3400000076988a64aa00036216e8ec2cf22c008b887c37c00019790824401d10efc00000065b7169c580002d98000c10bc64b92e5cda6dc366b84013c0cde6f092f5e9c64c7489d486dc4b05ca00004fee212fdacf85e88ef63e09a88f800077e80008cce694e69ce00b2000613a8fd154cbe933f3db136ced5581c58ff80e729100015c6028e8808a1e6887957e33b9623ad27750000c2080143c00007b00650003709afece654500007aa0000003cc4000df42a70001df76e6113a0b887a000000018400047a4ba255c000000172202443dcb425fb2419a40005270d5433e94d2f836918064c70000234525de98002ffe000d5a49ab95c7bcba000002520000000000098000754269aa9d8e0a87000000032e50200a84812223ff00007994dc94e1503bf22ccdcb5d79c04ed08dd800363d1400002c040951447de14b1354d2621600000000000004b8afe4bc697620b34c06544c60000b9c988000000000000037b6ef4c962820006ca800134e97e899000000058300026258e2e60ad438120009bd137d1d14744750a12b20f6400074d9824000dca0000b78bbfc8900000000000000003b7c00081f23c0f04000004db38001d7a697629a3002683731c87530ac406f2daa2794f123100025304b400055305580007e500009b4ab658d07b5f35408cbe247868b6de30800000000000002ac158444d95882ef1015b6da55fb6c1c7fc00000002760000002ed51340006cf73a9e1555850600000000009988002b88326b3a27ec00050261b2bd26eeb5a628501132950b0092aa40017546e039dd93d1f60000001fc8000000677885a7480418002ae0e9d8306b58cb875d1cd38aed1007a4ce04f3388864cc71e2009db3ccfea3aeecd196d1f78efcf400000023b00000009da0a18001b0ab058000001d0ad933e30c286f24ec041c6badce8dd08ac0b004500000032f5454e180ec80008120000000000000a81372a0ebb98ca9800243612fa2b5e289784208ff4a0b40609af4d00018000000005ee1234e6c8742d3dffc000099bbb30d82aa8c7800000132b0010f425c1c0d4a2551400000032ba82aea1244000161c001e5e4b967d9bc1c170da1a62155318afa2f28000e3a20f00000010a88ea48990b53f90000002a382160001936c9d230ca44d94e746080001298000bce4149569ea000000038f8000000429000000079c066000000143a0004dbfa65964b8d8000001da43
  | 34 => 0xa4567ef79a952221b171740374ca60003aec0000002440000000ac50ea306dd3409680000013f863300000f8fa01448000001a2abed099c51980ad0280007c14b42fe3c99a980000000000000fa698ef8b25ef928b6a1a48b6003b2aaeb246c5dd00398c3b36d161bc326602e4f14cf3a147c6405c8666288545aea6b16af18f057897e3b658680300000003245e6000004814b1ae200064c80000000000000001bc03ab00029c0ce006a1ad9cb9e167f64a880005d6aef3769b900005973d802a035e0002ca2b29848c8339900018b50002e5800000000000033dc00000000000012dec559ad0000000000000031dcf800000027500000000000c8e7d60001b2800000074b0003901006000000299da3500068f0ae07a50000001caa452bb71bf0000d1ef0a0e0338b25054d197d4d052edc51217a601826ee092067e00081b7a52601306abb5eac000706000484a9b00000000003c00000b4c000109e00025731ba0b15f1a71000000000056300006602374af00007403b0e3800008f40000004fe9a5400000000002f695cd46e863a280008bd9d73a084f2a2247e00009d4c4300000017fedfe23900004b07ee0003c1c000000400c0a14f4000777af9d7d6cc667371901a402987a8000000a80e5dc8c87241d08b621c1c545561f180014b8cf3133a4340008952ad5929070401106a5972d63e10000eb2ace00664c3bffb4eae5000206175d000636824c0e21b30000000132eb40000001bd40000001ad0000a4a00006d58b647f492103800032de2614ef268a8de3cc0001663db2edaca000050282d00000000000000e26000c5c0001b3400000017f9609abe2070000fb40000000000914ffad4000000000009395805d19dc407200024c539600064686548e600075b2ef95059b20a48000dae9293c11402e4e00075789e1830000000000000080256100000000000000a212944a842d8f8963e36b466a080b4355946784728c84f05970601ca28044dba87c14ab87086d43c000b098000838000b570001e9c000f39000000000087d00000004e2336be504145ec332c4003bcbb4000100f57000060e7256d25748eed00022ec8c46eb27f813741b94044f8000f3404381db8787baddd7892fb93e2c6ecef56ed1501110a2ba49d4e70f55b8ec129ea5e407b888000b9832e0001de675a07296714e843c0e5892d32a71b4a106ac62ac3d149a6593a0ea90ff23787f09650cc8708000eda775967901039b4fb2d2c00092542f813868e5c763f1ebde480bcef0c3dc48e000731e4b80000000848001acc1d134690844e50004a3c0000006fb02fa56dc4ee86508a9745c039c800155dc88cab4cd39c800028c7770ecd1867d715855a400000025bc0010f60003c58000ca6000134000050ea6b994470da6c000485a9cb0dcf116d9105546e9b61448
  | 35 => 0x298cae8968f4ab665d720004de1690acc10873b144dd0e3233d130e4ad01be4e03b00afcd8a18c2eac8467063cc36ec00092f56705718aa5d20da14910077a929674cd5fab951bb15fc6c61dd74b2e3dc1c016c0c8001bfa000000323c00000020314fdb68c2c3e9177d14e0a09b08714a2000000037c311709a0001298a4200052783b200000022398a40005a680000001f45f200000005e4000781bc880009754a8654eebe0000000000eea00010260632c4000000000000000000000000000000c52e08cf013c6148fd89ecaa400000001a894748a445d3be5e21390c597ac4a3581800149600000014bd2d24c10001b0123e0005ed04a9cfa53eb8600015e670e70e000153c06300028fee3c88709ab010a2e3df4f3aae48764b70e95c9090a5cd1528e3cdee1ea81c40a53acf17000354cfa854c77c40cd86dc40ef680fddeaa663eb3b70000a9b00013b4498000000014800000000000000000000001dbcc0e00000000000005653bf82ec00000017c80012d02050039cf9e46bf427e803aa3679e2a13738c5a069605ae44c748b96a321a53e07c730a8000000f4f25e098844200011f9ccc5fa6bf72b0000000960a46346745e7230000d9000035002b0460c2e1012ef093461cdf1ea1000000000050600000000000003890000000194c000000f404014000456b1353000014ec4043718000ad43a06f95894000dae2ae71ad00f0003d596a5bb2c801c358bc000d38470aef5a1ed2158a80000000000002bfc00000056580017a88d10000000a4e0000d1334d7ae11d12028936c6c311990ea0f3625d938107916328f67800000000001b41204000d280002a7f6f600000000000006770002c013b98076b8277714ae3694a9495c34de8316202c63600037c800000078964ab80c0004691f48ee9a4ae1764585c1aae
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xf524c940c0e651d1320c940c0c651d1320c940b048350842d4540b04844c832d4540b04835084214540b04844c83214540a3285d846050540e2052d846050540a44835496114840c0c641cd524c840945811d5320c84084c87595320c840c0f651d1320c840c0c641cd5248440a0c835944248440a0e83d904254620a0e84d8c3254620c0e541cd62d0620a0e8399442d0620c0c7494d62cc620a0e8499432cc620c0e541cd6210220a0e83d506250d20a0e84d4c6250d20c0e651c94310d20c0c651c94310d2090e851cd421092090e87d4d421092090e851d1320c92090e87d51320c920b048250c43d4520b048350842d4520b04844c832d4520b048250c4314520b04835084214520b04844c83214520a6285d846048520e2054d846048520e4053d846048520a14835516115020a0c825cc6454c20a148454d6114c20c0c731c96414c20a0c835506250c20a0c8454c6250c20915811d54310c2081c875954310c20c0f651c94310c2090c835c95410820a0d8614c4310820b058114c431082090c845c9530c82090d87150430c820a0d86150430c820b0581150430c820a0c835506250420a0c835944250420a0c8454c624c420a0c84594324c420a0c835526290020a0e83d944290020a0c8454e628c020a0e84d94328c02090c835ca5410b1090c835d25210b1090c835d54210b1090c845ce520cb1090c845d5320cb1090c835c85410a1090c835d05210a1090e839d54210a1090c845cc520ca1090e849d5320ca10a0e83d8a62d5110a0c835886215110a0e83d9264d4910a0e84d8e63d4910a0c835906414910a0c8458c6314910a0e82d506350910c0e7418f525091090c835c8541091090c835d0521091090e839d5421091090e851cd4210910c0e651cd4210910c0c651cd421091090e87d4d421091090c8714d4210910c0c649cf524c91090c845cc520c91090e849d5320c91090e851d1320c910c0e651d1320c910c0c651d1320c91090e87d51320c91090c87151320c910a0c835886295010a0c835886255010a28805886255010a0c835906494810a0c8458c6394810a0c835906454810a28805906454810a0c8458c6354810a488058c6354810a0c825506350810c0c7418d525081090c835ca541081090c835d2521081090c835d5421081090d851cd4210810c0f651cd4210810c0d651cd421081090c8794d421081090c8754d4210810c2565dc54210810929851c14210810c0c641cd524c81090c845ce520c81090c845d5320c81090d851d1320c810c0f651d1320c810c0d651d1320c81090c87951320c81090c87551320c810c4565dc5320c810949851c1320c8109a0825c041100109a0845c021080109c0835c02108010a24865515244010c24765515244010e055418d5244010c447654d5244010e046454d5244010
  | 1 => 0x2c84639c75350842c84635c753508428a5811da535084288e839c36150842c0d7518e615084288e87d8d6150842c8863dc16150842c8b631c16150842c88631c1615084288e8718d6050842c0f7518d6050842c8463dc56050842c84631c5605084288c835c4605084288c8798d42d444288c8758d42d444288d861cd429444288c8798d429444288c8758d4294442b0483509511444288e861cd425404288e87d8d425404288c8718d4254042a848350b6154042a84835086154042aa080508615404288c8798d421404288c8758d4214042a848350a6114042a84835096114042b05819944310832a8581190438c832a8681dcc644c832a8581dcc644c83288c845c7654c83288e849c3654c832a8681dd4644c832a8581dd4644c832a0d85dc4644c832a0d859c4644c832c85711c4644c832a0f855c0644c832a87815c0644c832a84815c0644c832a0d851c0644c832a86811c0644c832a85811c0644c832c84649c7544c832c84645c7544c8328c5811da544c832a0c86550544c83288e849c3614c832c0d75192614c83288e87d91614c832c8864dc1614c832c8b641c1614c832c88641c1614c83288e87191604c832c0f75191604c832c8464dc5604c832c84641c5604c83288c845c4604c83288c8799132d443288c8759132d443288d861d1329443288c87991329443288c875913294432b04844c9511443288e861d1325403288e87d91325403288c871913254032a84844cb6154032a84844c86154032ac0804c8615403288c87991321403288c875913214032a84844ca6114032a84844c96114032c0c641cd524cb4184c87595320cb41c0f651d1320cb4190d851cd4210a4190c8754d4210a41c0c641cd524ca41c0f651d1320ca41c0d651d1320ca41a2880594420c941a0c835884214141985811d1320c841c28621c14154041a0c825cc6454f21c0c731c96414f21a0c835506250f21a0c8454c6250f2181c875954310f21c0f651c94310f21a0c835506250721a0c835506250e21a0c8454c6250e21c0f651c94310e21c0d651c94310e2190d851cd4210a2190c8754d4210a2190d851d1320ca2190c87551320ca21d0873dc15410921c2b761c15410921d0b731c15410921d08731c15410921d23711c1541092192a80dd64310921928805d44310921d0874dc1530c921c4b761c1530c921d0b741c1530c921d08741c1530c921d43711c1530c92194a80dd7430c921948805d4430c921c0c541cd62d0521c0c7414d62cc521a0c84594324c521a0c835904214121a0c8458c321412190c825ce5410c2190d851c94310c21985811c94310c2190c835d2521082190c845ce520c821c28641c12154021c48631c12154021a0e83d884254640a0c8359252c8640a0e8399442c864090e851cd421094090e87d4d4210940c0c649c
  | 2 => 0xcb304000640c25c002dc00414262c6df1911d000001c2e831c363bcf93203a07ce91f10400022094001985c94cc614516158808c04c2ec633d4600d12012cadac4a90dc541410713d1e1e447290843c85921c57800001bc7142c00160a200000154e12849d3d80639890c847f058b79c8003e8528f480388d83489527c4ba51034305c0b8fc2b50a218490c85d3dcc41d91a1ec1429409020fd340ab418454350f2527d012b21ac182e0772408b0000026cf0000001c06539c0000c002f491258004448f1b8cd300433b82d00000000461a8f1c704e1b4000005215c00000000011f08c1b0000021519080002a08244c0004000000e53d0280009c2b8780001d0f8000a90e24a0029805000f1220000000f350de0a4002f02133000314db370010ac982fc6700a1316c5a2b00e0004823469000310fc00045141c60000800000af934568005e09cfb2284400000000be0011002d081f80700000034c2006cf0bc919d473100ff2688916e042baba8288e2bcd63906c0b0c30f0ec380aa00061248b934c7a001124550235c9914ea72c01e0011b338410e4d920c74188813be6ea30152e89345c9e40118108ca3c238344b32d400000ed2ce683ccd50ec938d41a048c9374a00cce30000017ceb01eb6425012d0ea2d217162fe000f8368240700028c4a0040e030000c100a040140808440000c0d0588002000189002090a0082004000380000020b40a0205044000201048040c000082c0e008140408000181a010281000020c82802000801004010004402080100400111081c1409000940a0100018000009880b600078000407018240601000342e03138000600a8681dc86350842a8581dc86350842a8681dd06350842a8581dd0635084288c835c7655084288e839c36550842a8681dd46350842a8581dd46350842a0d85dc46350842a0d859c46350842c85711c46350842a0f855c06350842a87815c06350842a84815c06350842a0d851c06350842a86811c06350842a85811c0635084
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 27
  | 6 => 1098
  | 5 => 6068
  | 4 => 3920
  | 3 => 290
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
  | 7 => packedAt gbK7 (510+((h/13+packedAt gbK7 (432+(h % 13)*6) 6) % 49)*6) 6
  | 6 => packedAt gbK6 (35670+((h/502+packedAt gbK6 (29646+(h % 502)*12) 12) % 2404)*12) 12
  | 5 => packedAt gbK5 (265976+((h/2528+packedAt gbK5 (230584+(h % 2528)*14) 14) % 10013)*14) 14
  | 4 => packedAt gbK4 (212230+((h/1550+packedAt gbK4 (192080+(h % 1550)*13) 13) % 6141)*13) 13
  | 3 => packedAt gbK3 (18363+((h/107+packedAt gbK3 (17400+(h % 107)*9) 9) % 387)*10) 10
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xfffffffffffffffe07fffffffffffffe1fffff
  | 1 => 0x3f81fff81fffffff81f07c1ff83ffffe88e3f
  | 2 => 0x3ffe03ffe03f81fffe007fe0ffc1f01f0f3cc
  | 3 => 0xfc00003ffffc001ffffff8000fffe001ff03f0
  | 4 => 0xffffffc00000001ffffffffff0000001fffc00
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x80882809048900001650942128421540334d5
  | 1 => 0x515245190c91268e580a4291a5235aa8e88a2a
  | 2 => 0xaa6149aa243a42b6aaa084f489e91c0d70d34c
  | 3 => 0x33459634492074db34d3d0210e738831bd03b0
  | 4 => 0xc386183871c3871dc71ce739c04210c1deec00
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 31 gbPos gbNeg, 0xeaa8a888eaa8a888eaa8a888eaa8a888eaa8a888eaa8a888eaa8a888eaa8a888eaa8a888eaa8a888eaa8a888eaa8a888eaa8a888eaa8a888eaa8a888eaa8a888, gbN, gbR, (fun _ _ => 0), gbI⟩
end PEqualNP.Outside.L_meta_12821
namespace PEqualNP.Outside.L_meta_12821
open PEqualNP.Outside.L_meta_12821.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bgb_3_192 : Interval gbAtlas 3 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_224 : Interval gbAtlas 3 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_256 : Interval gbAtlas 3 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_288 : Interval gbAtlas 3 288 2 := block_range (n:=2) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 290 := (concat (concat (concat bgb_3_0 bgb_3_32) (concat bgb_3_64 (concat bgb_3_96 bgb_3_128))) (concat (concat bgb_3_160 bgb_3_192) (concat bgb_3_224 (concat bgb_3_256 bgb_3_288))))
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
theorem bgb_4_1824 : Interval gbAtlas 4 1824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1856 : Interval gbAtlas 4 1856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1888 : Interval gbAtlas 4 1888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1920 : Interval gbAtlas 4 1920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1952 : Interval gbAtlas 4 1952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_1984 : Interval gbAtlas 4 1984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2016 : Interval gbAtlas 4 2016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2048 : Interval gbAtlas 4 2048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2080 : Interval gbAtlas 4 2080 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2112 : Interval gbAtlas 4 2112 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2144 : Interval gbAtlas 4 2144 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2176 : Interval gbAtlas 4 2176 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2208 : Interval gbAtlas 4 2208 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2240 : Interval gbAtlas 4 2240 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2272 : Interval gbAtlas 4 2272 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2304 : Interval gbAtlas 4 2304 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2336 : Interval gbAtlas 4 2336 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2368 : Interval gbAtlas 4 2368 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2400 : Interval gbAtlas 4 2400 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2432 : Interval gbAtlas 4 2432 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2464 : Interval gbAtlas 4 2464 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2496 : Interval gbAtlas 4 2496 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2528 : Interval gbAtlas 4 2528 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2560 : Interval gbAtlas 4 2560 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2592 : Interval gbAtlas 4 2592 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2624 : Interval gbAtlas 4 2624 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2656 : Interval gbAtlas 4 2656 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2688 : Interval gbAtlas 4 2688 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2720 : Interval gbAtlas 4 2720 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2752 : Interval gbAtlas 4 2752 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2784 : Interval gbAtlas 4 2784 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2816 : Interval gbAtlas 4 2816 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2848 : Interval gbAtlas 4 2848 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2880 : Interval gbAtlas 4 2880 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2912 : Interval gbAtlas 4 2912 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2944 : Interval gbAtlas 4 2944 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_2976 : Interval gbAtlas 4 2976 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3008 : Interval gbAtlas 4 3008 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3040 : Interval gbAtlas 4 3040 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3072 : Interval gbAtlas 4 3072 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3104 : Interval gbAtlas 4 3104 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3136 : Interval gbAtlas 4 3136 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3168 : Interval gbAtlas 4 3168 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3200 : Interval gbAtlas 4 3200 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3232 : Interval gbAtlas 4 3232 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3264 : Interval gbAtlas 4 3264 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3296 : Interval gbAtlas 4 3296 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3328 : Interval gbAtlas 4 3328 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3360 : Interval gbAtlas 4 3360 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3392 : Interval gbAtlas 4 3392 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3424 : Interval gbAtlas 4 3424 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3456 : Interval gbAtlas 4 3456 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3488 : Interval gbAtlas 4 3488 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3520 : Interval gbAtlas 4 3520 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3552 : Interval gbAtlas 4 3552 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3584 : Interval gbAtlas 4 3584 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3616 : Interval gbAtlas 4 3616 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3648 : Interval gbAtlas 4 3648 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3680 : Interval gbAtlas 4 3680 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3712 : Interval gbAtlas 4 3712 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3744 : Interval gbAtlas 4 3744 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3776 : Interval gbAtlas 4 3776 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3808 : Interval gbAtlas 4 3808 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3840 : Interval gbAtlas 4 3840 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3872 : Interval gbAtlas 4 3872 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_3904 : Interval gbAtlas 4 3904 16 := block_range (n:=16) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 3920 := (concat (concat (concat (concat (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat (concat bgb_4_96 bgb_4_128) (concat bgb_4_160 bgb_4_192))) (concat (concat (concat bgb_4_224 bgb_4_256) (concat bgb_4_288 bgb_4_320)) (concat (concat bgb_4_352 bgb_4_384) (concat bgb_4_416 bgb_4_448)))) (concat (concat (concat bgb_4_480 (concat bgb_4_512 bgb_4_544)) (concat (concat bgb_4_576 bgb_4_608) (concat bgb_4_640 bgb_4_672))) (concat (concat (concat bgb_4_704 bgb_4_736) (concat bgb_4_768 bgb_4_800)) (concat (concat bgb_4_832 bgb_4_864) (concat bgb_4_896 bgb_4_928))))) (concat (concat (concat (concat bgb_4_960 (concat bgb_4_992 bgb_4_1024)) (concat (concat bgb_4_1056 bgb_4_1088) (concat bgb_4_1120 bgb_4_1152))) (concat (concat (concat bgb_4_1184 bgb_4_1216) (concat bgb_4_1248 bgb_4_1280)) (concat (concat bgb_4_1312 bgb_4_1344) (concat bgb_4_1376 bgb_4_1408)))) (concat (concat (concat (concat bgb_4_1440 bgb_4_1472) (concat bgb_4_1504 bgb_4_1536)) (concat (concat bgb_4_1568 bgb_4_1600) (concat bgb_4_1632 bgb_4_1664))) (concat (concat (concat bgb_4_1696 bgb_4_1728) (concat bgb_4_1760 bgb_4_1792)) (concat (concat bgb_4_1824 bgb_4_1856) (concat bgb_4_1888 bgb_4_1920)))))) (concat (concat (concat (concat (concat bgb_4_1952 (concat bgb_4_1984 bgb_4_2016)) (concat (concat bgb_4_2048 bgb_4_2080) (concat bgb_4_2112 bgb_4_2144))) (concat (concat (concat bgb_4_2176 bgb_4_2208) (concat bgb_4_2240 bgb_4_2272)) (concat (concat bgb_4_2304 bgb_4_2336) (concat bgb_4_2368 bgb_4_2400)))) (concat (concat (concat (concat bgb_4_2432 bgb_4_2464) (concat bgb_4_2496 bgb_4_2528)) (concat (concat bgb_4_2560 bgb_4_2592) (concat bgb_4_2624 bgb_4_2656))) (concat (concat (concat bgb_4_2688 bgb_4_2720) (concat bgb_4_2752 bgb_4_2784)) (concat (concat bgb_4_2816 bgb_4_2848) (concat bgb_4_2880 bgb_4_2912))))) (concat (concat (concat (concat bgb_4_2944 (concat bgb_4_2976 bgb_4_3008)) (concat (concat bgb_4_3040 bgb_4_3072) (concat bgb_4_3104 bgb_4_3136))) (concat (concat (concat bgb_4_3168 bgb_4_3200) (concat bgb_4_3232 bgb_4_3264)) (concat (concat bgb_4_3296 bgb_4_3328) (concat bgb_4_3360 bgb_4_3392)))) (concat (concat (concat (concat bgb_4_3424 bgb_4_3456) (concat bgb_4_3488 bgb_4_3520)) (concat (concat bgb_4_3552 bgb_4_3584) (concat bgb_4_3616 bgb_4_3648))) (concat (concat (concat bgb_4_3680 bgb_4_3712) (concat bgb_4_3744 bgb_4_3776)) (concat (concat bgb_4_3808 bgb_4_3840) (concat bgb_4_3872 bgb_4_3904)))))))
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
theorem bgb_5_5088 : Interval gbAtlas 5 5088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5120 : Interval gbAtlas 5 5120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5152 : Interval gbAtlas 5 5152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5184 : Interval gbAtlas 5 5184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5216 : Interval gbAtlas 5 5216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5248 : Interval gbAtlas 5 5248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5280 : Interval gbAtlas 5 5280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5312 : Interval gbAtlas 5 5312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5344 : Interval gbAtlas 5 5344 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5376 : Interval gbAtlas 5 5376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5408 : Interval gbAtlas 5 5408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5440 : Interval gbAtlas 5 5440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5472 : Interval gbAtlas 5 5472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5504 : Interval gbAtlas 5 5504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5536 : Interval gbAtlas 5 5536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5568 : Interval gbAtlas 5 5568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5600 : Interval gbAtlas 5 5600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5632 : Interval gbAtlas 5 5632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5664 : Interval gbAtlas 5 5664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5696 : Interval gbAtlas 5 5696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5728 : Interval gbAtlas 5 5728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5760 : Interval gbAtlas 5 5760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5792 : Interval gbAtlas 5 5792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5824 : Interval gbAtlas 5 5824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5856 : Interval gbAtlas 5 5856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5888 : Interval gbAtlas 5 5888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5920 : Interval gbAtlas 5 5920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5952 : Interval gbAtlas 5 5952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_5984 : Interval gbAtlas 5 5984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6016 : Interval gbAtlas 5 6016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_5_6048 : Interval gbAtlas 5 6048 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 6068 := (concat (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 (concat bgb_5_96 bgb_5_128))) (concat (concat bgb_5_160 (concat bgb_5_192 bgb_5_224)) (concat bgb_5_256 (concat bgb_5_288 bgb_5_320)))) (concat (concat (concat bgb_5_352 (concat bgb_5_384 bgb_5_416)) (concat bgb_5_448 (concat bgb_5_480 bgb_5_512))) (concat (concat bgb_5_544 (concat bgb_5_576 bgb_5_608)) (concat bgb_5_640 (concat bgb_5_672 bgb_5_704))))) (concat (concat (concat (concat bgb_5_736 (concat bgb_5_768 bgb_5_800)) (concat bgb_5_832 (concat bgb_5_864 bgb_5_896))) (concat (concat bgb_5_928 (concat bgb_5_960 bgb_5_992)) (concat bgb_5_1024 (concat bgb_5_1056 bgb_5_1088)))) (concat (concat (concat bgb_5_1120 (concat bgb_5_1152 bgb_5_1184)) (concat bgb_5_1216 (concat bgb_5_1248 bgb_5_1280))) (concat (concat bgb_5_1312 (concat bgb_5_1344 bgb_5_1376)) (concat bgb_5_1408 (concat bgb_5_1440 bgb_5_1472)))))) (concat (concat (concat (concat (concat bgb_5_1504 (concat bgb_5_1536 bgb_5_1568)) (concat bgb_5_1600 (concat bgb_5_1632 bgb_5_1664))) (concat (concat bgb_5_1696 (concat bgb_5_1728 bgb_5_1760)) (concat bgb_5_1792 (concat bgb_5_1824 bgb_5_1856)))) (concat (concat (concat bgb_5_1888 (concat bgb_5_1920 bgb_5_1952)) (concat bgb_5_1984 (concat bgb_5_2016 bgb_5_2048))) (concat (concat bgb_5_2080 (concat bgb_5_2112 bgb_5_2144)) (concat bgb_5_2176 (concat bgb_5_2208 bgb_5_2240))))) (concat (concat (concat (concat bgb_5_2272 (concat bgb_5_2304 bgb_5_2336)) (concat bgb_5_2368 (concat bgb_5_2400 bgb_5_2432))) (concat (concat bgb_5_2464 (concat bgb_5_2496 bgb_5_2528)) (concat bgb_5_2560 (concat bgb_5_2592 bgb_5_2624)))) (concat (concat (concat bgb_5_2656 (concat bgb_5_2688 bgb_5_2720)) (concat bgb_5_2752 (concat bgb_5_2784 bgb_5_2816))) (concat (concat bgb_5_2848 (concat bgb_5_2880 bgb_5_2912)) (concat bgb_5_2944 (concat bgb_5_2976 bgb_5_3008))))))) (concat (concat (concat (concat (concat (concat bgb_5_3040 bgb_5_3072) (concat bgb_5_3104 (concat bgb_5_3136 bgb_5_3168))) (concat (concat bgb_5_3200 (concat bgb_5_3232 bgb_5_3264)) (concat bgb_5_3296 (concat bgb_5_3328 bgb_5_3360)))) (concat (concat (concat bgb_5_3392 (concat bgb_5_3424 bgb_5_3456)) (concat bgb_5_3488 (concat bgb_5_3520 bgb_5_3552))) (concat (concat bgb_5_3584 (concat bgb_5_3616 bgb_5_3648)) (concat bgb_5_3680 (concat bgb_5_3712 bgb_5_3744))))) (concat (concat (concat (concat bgb_5_3776 (concat bgb_5_3808 bgb_5_3840)) (concat bgb_5_3872 (concat bgb_5_3904 bgb_5_3936))) (concat (concat bgb_5_3968 (concat bgb_5_4000 bgb_5_4032)) (concat bgb_5_4064 (concat bgb_5_4096 bgb_5_4128)))) (concat (concat (concat bgb_5_4160 (concat bgb_5_4192 bgb_5_4224)) (concat bgb_5_4256 (concat bgb_5_4288 bgb_5_4320))) (concat (concat bgb_5_4352 (concat bgb_5_4384 bgb_5_4416)) (concat bgb_5_4448 (concat bgb_5_4480 bgb_5_4512)))))) (concat (concat (concat (concat (concat bgb_5_4544 (concat bgb_5_4576 bgb_5_4608)) (concat bgb_5_4640 (concat bgb_5_4672 bgb_5_4704))) (concat (concat bgb_5_4736 (concat bgb_5_4768 bgb_5_4800)) (concat bgb_5_4832 (concat bgb_5_4864 bgb_5_4896)))) (concat (concat (concat bgb_5_4928 (concat bgb_5_4960 bgb_5_4992)) (concat bgb_5_5024 (concat bgb_5_5056 bgb_5_5088))) (concat (concat bgb_5_5120 (concat bgb_5_5152 bgb_5_5184)) (concat bgb_5_5216 (concat bgb_5_5248 bgb_5_5280))))) (concat (concat (concat (concat bgb_5_5312 (concat bgb_5_5344 bgb_5_5376)) (concat bgb_5_5408 (concat bgb_5_5440 bgb_5_5472))) (concat (concat bgb_5_5504 (concat bgb_5_5536 bgb_5_5568)) (concat bgb_5_5600 (concat bgb_5_5632 bgb_5_5664)))) (concat (concat (concat bgb_5_5696 (concat bgb_5_5728 bgb_5_5760)) (concat bgb_5_5792 (concat bgb_5_5824 bgb_5_5856))) (concat (concat bgb_5_5888 (concat bgb_5_5920 bgb_5_5952)) (concat bgb_5_5984 (concat bgb_5_6016 bgb_5_6048))))))))
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
theorem bgb_6_1088 : Interval gbAtlas 6 1088 10 := block_range (n:=10) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1098 := (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 bgb_6_96)) (concat (concat bgb_6_128 bgb_6_160) (concat bgb_6_192 bgb_6_224))) (concat (concat (concat bgb_6_256 bgb_6_288) (concat bgb_6_320 bgb_6_352)) (concat (concat bgb_6_384 bgb_6_416) (concat bgb_6_448 (concat bgb_6_480 bgb_6_512))))) (concat (concat (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640)) (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 (concat bgb_6_768 bgb_6_800)))) (concat (concat (concat bgb_6_832 bgb_6_864) (concat bgb_6_896 bgb_6_928)) (concat (concat bgb_6_960 bgb_6_992) (concat bgb_6_1024 (concat bgb_6_1056 bgb_6_1088))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 27 := block_range (n:=27) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 27 := bgb_7_0
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 9, 13),(inputs.getD 3 zero, 5, 13),(inputs.getD 4 zero, 5, 21)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 5 zero,inputs.getD 4 zero]
def fullWord : Sig := 0xeaa8a888a888a888eaa8a888a888a888eaa8a888a888a888eaa8a888a888a888eaa8a888a888a888eaa8a888a888a888eaa8a888a888a888eaa8a888a888a888
theorem fullBound (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have low := boundgb certgb
  have lift := lift_ok (u:=true) (ms:=fixRows 0 32) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 5 zero,21,53)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 5 zero,21,53)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (3936921736 * 2 ^ 32 + 2827528328) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_12821.Model.Repr at out
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

def mono : List Gate := [⟨.and,[4,5]⟩,⟨.and,[3,6]⟩,⟨.or,[3,6]⟩,⟨.or,[2,7]⟩,⟨.and,[2,4]⟩,⟨.and,[0,8]⟩,⟨.and,[9,11]⟩,⟨.and,[7,10]⟩,⟨.or,[0,13]⟩,⟨.and,[1,14]⟩,⟨.or,[12,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3936921736 * 2 ^ 32 + 2827528328) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3936921736 * 2 ^ 32 + 2827528328) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_12821

open PEqualNP.Outside.L_meta_12821 in
theorem PEqualNP.Outside.L_meta_12821 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3936921736 * 2 ^ 32 + 2827528328) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3936921736 * 2 ^ 32 + 2827528328) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound allgb)
