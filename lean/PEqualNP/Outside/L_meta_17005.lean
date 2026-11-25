import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_17005.Model
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


end PEqualNP.Outside.L_meta_17005.Model

namespace PEqualNP.Outside.L_meta_17005
open PEqualNP.Outside.L_meta_17005.Model
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

def SBf (j : Nat) : Nat := [8, 5, 6, 7, 7, 7].getD j 0

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

end PEqualNP.Outside.L_meta_17005

namespace PEqualNP.Outside.L_meta_17005
open PEqualNP.Outside.L_meta_17005.Model
def s0K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K6 : Nat → Nat
  | 0 => 0x53ebd118243c2270000d80000128032800ad4ca482c3400991108ce030cb8f0a16a0b8e4200a2b4800eaa04003801a30b092a00134008b000100047040100ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41bf41fe41fd41bd41fc41ff31df31fe31fd31dd31fc31ff21fe21fd21fc21ff40fe40be40fd40fc40bc40ff30fe30de30fd30fc30dc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x617e510c2faa2186fd0430dea0861df310c3bc6218774c430ee188617e500c37c80186f10030ef98061fa300c3ba60187e4c030efaa061de540c3baa8187715030efa9061de520c3baa4187714830efa1061de420c3ba84187710830efa8861de510c3baa2185754430ee28861df410c33e82187790430eea08619d410c3b8821877c8430ef10861dd210c3b842187794030af28061da500c3be80187790030cf20061dd400c3b880186710030bfaa6417e54c837ca9904f95320beaa641bd54c827aa9905f15320bfa9e417e53c83bca7905794f20bea9e41dd53c82baa7905f14f20bf28e417d51c837e83906f50720ef98e41dd31c83de43907b48720df20641bc40c83bc6190770c320bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3106fd0620dea0c41df31883ba63107b88620f610c417e508837c81106f10220ef18441dc30883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20bfa8a41f751482eea2905f14520fa28a4174514837e82906f50520ef98a41dd31483de42907b48520df20241bc40483bc6090770c120fd90241ee20482fea8105f95020beaa0417c54082fea6105f94c20bea98417c53082fca4105f94420bea8841bf410837a821077cc420ee98841ee21083d842105f94020df20041bc40083bc6010770c020f790041fa20083da40107e48020bfaa6217e54c437ca9884f95310beaa621bd54c427aa9885f15310bfa9e217e53c43bca7885794f10bea9e21dd53c42baa7885f14f10bfa96217e52c42faa5885f14b10dfa0e21bd41c43be6388774c710df20621bc40c43bc6188770c310bfaa421bf548427ea9085f95210beaa4217c5484378a9084f15210bfa9c21df53842bea7085f94e10bea9c217c53843b8a7085714e10bfa94217e52842faa5085f14a10bea8c21bf418437a830877cc610ee98c21f721843e843085f94210df20421bc40843bc6108770c210fd10421f920843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910dfa0a21bd41443be6288774c510df20221bc40443bc6088770c110fd10221f920443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf28821bf410437a820877cc410ee98821f721043e842085f94010df20021bc40043bc6008770c010fb88021fa10043ea20087e44010
  | 1 => 0x721886fca110df54221bfaa2437e54486faa890df15121bfa9a437e53486faa690df14d21dfa0a43bd41487be6290f74c521fb90a43ee21486fea090df14121bfaa0437e540877ca810cf95021beaa043bd540867aa810df15021bfa98437e53087bca610d794c21bea9843dd53086baa610df14c21bf290437e510877e8210ef50421ef98843dd31087de4210fd88421f690843f521086fca010fe94021bd280437d50087f2a010de54021bf29e81de53d02bca7a05f54f40eea9e815d53d02fca5a05f54b40bf28e817d51d037e83a06f50740ef98e81dd31d02faa9205f94e40bea9c81bf439037c87206f50e40de21c817e52902faa5206fd0a40df21481bd429037885205f94640bea8c81bf419037c83206f50640de20c81df31903ba63205f94240dfa0481fb409037ea7206f94e40dea9c81bc539037ea5206f94a40dea9481bc529037e65206f8ca40de99481bc329037ea3206f94640dea8c813d5190378a3206fcc640cf98c81be319037a6320674c640de18c81bf219037c43206f48640de10c813e50902fea6a077d4d40afa9a817c53503b8a6a05714d40bfa92817c52502fea2a05f14540dfa0a81bd41503be62a0774c540fda0281be40502fca8205f94c40bea9881bf431037c86206f50c40de218817e52102faa4206fd0840df21081bd421037884205f94440bea8881bf411037c82206f50440de20881df31103ba62205f94040dfa0081fa401037a80207e50040dfa9881be531037aa6206f14c40dfa9081be521037aa4206f14840df99081be321037a64206f0c840dfa8881be511037aa2204f54440de28881bf311033e62206f8c440de988819d311037862206fc8440df10881bd211037842206f940409f28081ba50102fea9985f95330df2a6613e54cc2faa9986f553309eaa6617c54cc2fca5985f54b30bf28e617d51cc37e83986f50730ef98e61dd31cc37c81986f10330bfaa4617e548c2faa9185f15230bea9c61df438c3bc87187750e30ee21c617e528c2faa51877cca30ef19461dd328c3b865185f94630bea8c61bf418c37a831877cc630ef18c61dd318c3b863185f94230df20461bc408c3be61187ecc230efaa461de548c3baa9187715230efa9461de528c3baa5187714a30efa1461de428c3ba85187710a30efa8c61de518c3baa3185754630ee28c61df418c33e83187790630eea0c619d418c3b8831877c8630ef10c61dd218c3b843185794230efa0461de408c33c81187750230ee204619c408c2fea8986fd51309faa2617e544c2faa8985f15130de2a2613c544c2fea4985f14930bfa8a617c514c37e82986f50530ef98a61dd314c37c80986f10130fd98261de304c2fea8185f95030beaa0617c540c2fca61877d0c30ef21861dd430c3b886185f94830bea9061df320c3bc6418774c830ee19
  | 2 => 0xcbbe65197bcca32bf28c657d518cafca1195f54232bfaa265bf544ca7ea8995f95132beaa2657c544cb78a8994f15132ef21a65dd434cbde6499778c932bfa8a657c514cafea0995f14132bfaa0657e540cb7ca8194f95032beaa065bd540ca7aa8195f15032bf29865df430cbb886195f94832ef99065ee320cbba64197b4c832bf288657d510cafca0195f54032bf29e837d53d077e87a0ef90f41dea1e83bc43d06fca5a0df54b41dfa1683be42d077a85a0ef10b41bf286837d50d077ea7a0ef94f41dea9e83bc53d077ea5a0ef94b41dea9683bc52d077e65a0ef8cb41de99683bc32d077ea1a0ef943419f28683bd50d0778a1a0df552419eaa4837e53907bca720d794e41bea9c83dd53906baa720df94a41bea94837e519077e8320fdd0641bf284837d50906fea6a0df14d41dfa1a83be435077a86a0ef10d41bfa92837c525077e84a0ef90941dea1283bc42507ee82a0ef90541bfa82837c505077ea6a0ef94d41dea9a83bc535077ea4a0ef94941dea9283bc525077e64a0ef8c941de99283bc325077ea2a0edd4541dfa8283be505077aa0a0ef141419e282837e541067ca820df94c41ef298835e53106faa620f754c41aea98837e52106faa420df94441dfa0883f6411077a8220fd50441bf280837d50106fea998df95331beaa6637c54cc7be8798f790f31eea1e63dc43cc6fca598df54b31ef99663de32cc7ba6598f70cb31dfa0e63bd41cc6fca198df54331efaa663de54cc7baa998f715331efa9663de52cc7baa598f714b31efa1663de42cc7ba8598f710b31efa0e639f41cc7bc8398f750731cea0e63dc41cc7bea198f794331af28663dd50cc7b8a198dfd5231bf2a463be548c67ca918df55231deaa4633d548c6f8a918df54e31aea9c637e528c6faa518df94631dfa0c63bd418c7be6318fdcc631bf284637d508c6fea898df95131beaa2637c544c7be8698f790d31eea1a63dc434c6fea498df14931ef99263de324c7ba6498f70c931dfa0a63bd414c7ee6298f78c531bfa82637c504c7bea898f795131eeaa263dc544c7bea498f794931eea9263dc524c7be8498f790931eea1263dc424c7bea298f5d4531efa0a639f414c7bc8298f750531cea0a63dc414c7bea098f794131eea8263dc504c6b8a098dfd5031bf2a063be540c67ca818df55031deaa0633d540c6f8a818df94c31af298637e520c6faa418df94431dfa0863bd410c7be6218fd8c431ee98863f5310c6fca018df54031bfaa6437e54c86faa990df15321bfa9e437e53c86faa790df14f21dfa0e43bd41c87be6390f74c721bf286437d50c86fea910df95221df2a4433e54886faa910ef552219eaa4437c54886fea710df94e21ef29c435e53886faa710f754e21aea9c437c53886faa510df94621dfa0c43bd41887be6310f74c621f790c43f
  | 3 => 0xc42f2415320000012d5500018d9ae000e10438cd54cbf0000d71ac1340021f6f4595280000006d8000ac0007d40000071c2791f029366ad9429d80f033c0023c142bb80033f0000000000000010c0030c0009b80028c034004a200000064400000000609e1a816e87f8e580426825c0000000000011155000235d58005600000000000092ced80000c79512bbe63a08c30800210841a5b16000049a117a55e8202d9bf7628480039633a001e20005221b42f9a870e79c9f3890000013f000770984000000000020100300000200c0000001a0000200300202000000006038018040000000c80100400001800000004058000040240080c0160000080000000800000002010020060000a8000000160040300001400000001000004008010000000180700202c048000000080500500205c0180100000c000050040140000100a0300500400400400016002004000000060000180f00000809001002010020040000441580200a02c000050000000b80500e000000040000180080002402c0a0010000040000100000001000002040000000060100000000005c1180801000c0000000406408007000008028060120000000000002400801002000010000080000080000800c0000700202000002008008010000080000600002a0080200000a0000300201c01005800004000008010000080000300c02c0080000e0100780300400c000020000080280000c00c0000d006000000070060100000800200800006000020010070000000180a004018008010000200100500200400000000008000000020000280200c024008000460000580000402c0300300402805800000000018010080040181300c0100100101200c000000000140180100e0000600101001802014008000008020040040180f00800400800006000015f94b43bea96877e51d0efaa3a1df94343bea86877d5490efca721efd0e43efa1c877e5290efaa521df94643bea8c877e5090efaa121f7d0d43df21a877f5250ef8a4a1dfd4543be28a877f5050ef8a0a1df95043bf29887bf4310fbc8621ef50c43eea18879d4310efca421df54843bf288877d5110efca021df54043bf29e857d53d0b7e87a16f50f42bf28e857d51d0afca1a15f54342beaa4857e5390afaa7216f90e42de21c857e5290b7e85217bd0a42bf28c857d5190afca1215f54242bfa9a85df5350abea6a15f14d42ee29a855c5350b7e86a16f50d42f7a1285be4250afea2a15f14542bfa82857c5050afca8215f94c42ef298855e5310afaa6217754c42aea9885be4310b7886215f94842dfa1085ee4210b7a84217b50842bf288857d5110afca0215f54042bfaa6657e54ccafaa9995f15332ef21e65dd43ccafca3995f54732bf286657d50ccafea9195f95232beaa4657c548cafaa71977d0e32ee21c657e528
  | 4 => 0x2772f8ec9afb6f62a7ac410830009b5698000000000005d01aa88003d85da60c000d82e200153800000001212f3000001a2000164d04c33e63849a82994f0fea59110884f4d3000000000b08002c668a3b16f0e637699cee0f3000001d1800000dd51fa2b7b405c00130000001b721a0000015f2aa6e60007f80566800000000000001ce2870c46d400000012001bfb08000001c31701be0009439500093000000098038ae0f542648434a116b87b1891227106ac58016414edd01ac056400113800000878000006f69eca000064c215758007a69918d3c91d60017d800278000000000000011989f0000009daca2929cc1ca985260012f8562640007d093000000000004ec000001b7000fb00c0bd148954bb808236001b90000002a5cdaf621600064ac7000118001b065e0640000012a190c0bad7c0560e6000000084000322d8720fbb2d16200162800000000000000005ede7800000431809ea000600003646947a527a6002266c63b1e0001d00eb8578cea006113506995d30d341630d65a1b45400000000054000003e20000010200000054d88000000998002ac000724b582d4f2000000005f20000038c21ce61030000000000000000000000000744a1923905000650768ce0663c0e511e5d0d6d568815880018c00067858c658003345795c9a50000000020f0000008ea8d18c000140d4714001d9800000498280c25869f435b566ba43da994d4301f8000000002701dbee000bfcf81e815ecac4da002ea148cf138000e75472a45a27d0ca98e7a8114fe0d05e8da0158a3000000d91d6616f35e8b541d0ce8ef3ef00088c7e000438b2400000660dc0a103407e7488a16400065c001161f6001938b820c58559800000000249694e473c0028a6124acd33b039a001e2ba7000a094e00002629d2216d000001e0359774d494a9c65760c5928385ce53924007000384aa3c1048cc8002db330880608157244cc48000000000e204830ed44a62e92f2a812b9ee7e43a5fb1df4ac000000921a43d0003d744c0016faae7a40016780000000082382000e790b35e03c000002904e20001b8007da0011a800516000bb0000003e400000312db0963472ae700c686c000001dc86a000000001930000000003d49200150b990ca5cc5baec00042400360000885cf800000e943c9e0100a69f48ab6ce000e38c84b2ed8052a3524001310000ec8d80033708e000001fa7bc000002e23740002a240000ddc001f25cab541f08a2a278c1b3f4000e5c003480fa630000005909705b000000000000002328ed148b4200001eda3d7ac39de38573baea40000034889155bf026c000000002b69f00000066c1c4301f85f40011a34e05e0010a2c159ae2c00000000a24ea08b166ac531b8f7a0799df8420ee3dc8106625490de40dd404ea8511aa5a44
  | 5 => 0x27aadc3aaf80000000030261c5bca436265ce84a280012807ced3431c659d3600017c000d100053c000003650000000036d00009c00217308a6db1a584d2444dc0da000f70928005b02a194800000c88f7800000001f08006500809c800230d34afa9d6e24bc550bb2dc000003a05b429400010340fac002f543240c001b46fc4a41d000632210df20700446904800000000003e7000000cb000000354d63145fc8e16e00040a001889e1000000001f357e0000006e796f38d8999626001d2338000001be0fd2c0000000000580008b9d10b81f02c985000a944e8e44b4eb13a8bc0c63e09f91f43ace4173833a0b74b1143096ae93a34f666001908007caced1880017e001f8959194af06cbb4734428003ae49a06c220cc598da812800000a5d2e8000005e11724a7c61ccf684e6488e4d082611ebdcf132a6fa000000003b2c807b000658144003df01648d9aa5200000062b8d0000000005500067000000000001700004e07fcc505a000640d798f000b380000028c0713c07a172c000028f7e60000000015ad8400000000000a9000000000b30ea00043400357132000b51150003c8000ef2d0b65443e448a480000002b475c00003000000fdb694640003d800000738beae16b00014a0006b496d91bcc500310700fe0008e92f25378438935835000230dc9f600013dfbb045c6224571357d47051b80012203d342b50009396b9f1094e049393a00074d5c03c45e0000000025cc3c00000180c15ee800000000001413520004d2b44fe52c0030d42a491230006aa0000019f75ec5df41370b040400000000000bf0ba12cdadec97260c3b86f0dc4585fcfe9d56a0d195e8001e27e4e18005fa000f230a5e0de1fabb50007140003079428154ad410c575c839400000000000778001de80035a440000005de83118379000b9978800000529c8800662b904730700068c0000028e00068a517f02980000053ec0c000000286f56b000000f55790000828a00000067ab4000000000e017522d63810000000000000002542a09bcc5b762ac41d06a840e0001008b57260008e3660006484c000000000001881b6000d38000e41a08900067ceeda00e50ce6f00000041c000ba3490dec7c0000000
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0xc40842b56110210c7d52308431c548c210b5586308431f540c210c715030842d5610c210f808620842f06148210f8c85208423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f994544423e60151108f180544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d1097994534431f5414d10c7150534425e6014d1097180534432f54d4910cb153524434f53d4910d314f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109dd85524426e6514910cbd50524432c5414910d3d4c524434c5314910da580524423e65d0510c7d4f414431c53d0510cbd4b414432c52d0510ae983414423c6550510c7d4d414431c5350510cbd49414432c5250510ae181414425e65cc510c7d53314431c54cc510d3d4b314434c52cc510b6983314425c654c510c7d51314431c544c510d3d49314434c524c510e550531442d8604c5108f996404431f5390110c714e404432f5290110cb14a404423e6510110c7d4c404431c5310110cbd48404432c521011097996304431f548c110c7152304434f528c110d314a304425e650c110c7d50304431c540c110d3d48304434c520c110da14a20442786548110d914a104425e63d50109758f540426e62d50109b58b540423d65950108fd85540423d61550108f990540425e63150109758c540426e62150109b588540423e64d4c108f593530426e62d4c109b58b530425d6594c10c7952530431d5494c10c7951530431d5454c1097d85530425d6154c108f990530423d6414c109798c530426e6214c109b588530423e64d48108f593520425e63d48109758f520426d6594810cb952520432d5494810d394e520434d5394810cb951520432d5454810d394d520434d5354810d9185520423e64148108f590520425e63148109758c520426e62148109e980520423e64944108f592510425e63944109758e510423d65d0410c794f410431d53d0410cb94b410432d52d04108fd95410431e5350410c754d410432e5250410cb549410425d65cc410c7953310431d54cc410d394b310434d52cc41097d95310431e544c410c7551310434e524c410d3549310436552c84109d594210423f65900108f596400431e5390010c754e400432e5290010cb54a40042b561900108fd94400423d6510010c794c400431d5310010cb948400432d5210010ad584400425f658c01097596300431e548c010c7552300434e528c010d354a30042d5618c01097d94300425d650c010c7950300431d540c010d3948300434d520c010b55843004398400c0109e596100436952840109dd9510042e462440109ed9510043695244010
  | 1 => 0x8398400c2208f587544823e64951209798e544825d63951209d9865448275619512097d8d544825c63551209dd85544827461551208f994544823d6115120c7d53534831c54d4d2097587534823e6494d208f592534825e6394d209d98653482756194d208fd91534823c6454d209dd8553482746154d2097994534831f5414d20c7150534825d6114d20cdd53514833454d4520d5d4f514835453d4520cdd93514833464d4520d5d8f514835463d45208f990514823d64145209798c514825d6314520cdd5051483345414520d5d4c51483545314520cd99051483356414520d598c51483556314520dc580514823e65d05208f197414831f53d0520c714f414833751d0520cd147414823e65505208f195414831f5350520c714d41483375150520cd145414825e65cc52097197314831f54cc520c7153314835751cc520d5147314825e654c52097195314831f544c520c71513148357514c520d5145314826e65c8520d9147214836451485208f996404831f5390120c714e40483375190120cd146404823e6510120c7d4c404831c5310120cdd444048334511012097996304831f548c120c71523048357518c120d5146304825e650c120c7d50304831c540c120d5d443048354510c120e61003048364518812097d8d540825c63550209798c540825d63150209d984540827561150208fd91530823c6454c208f990530823d6414c209d98453082756114c208f992520823d64948209798e520825d63948208f992510823d64944209798e510825d6394420cd94541083355150420ae1814108356514c420d554531082d8604c4209b59621082e960084209bd9520082e46148020ea10120083c830480209ed95200825e63d53109758f54c425e63153109758c54c423e64d4f108f59353c431e5494f10c755253c431e5454f10c755153c423e6414f108f59053c423e64d4b108f59352c425e63d4b109758f52c423e6414b108f59052c425e6314b109758c52c431e53d0710c754f41c431e5350710c754d41c431e54cc710c755331c431e544c710c755131c4395414c710c794e40c431d5390310c794c40c431d5310310c795230c431d548c310c795030c431d540c310e610030c433561d5210ce983548425e63952109758e548425f63552109718d54843356115210ce980548431f54d4e10c7153538435561d4e10d6983538423e6494e108f592538423f6454e108f191538431f5414e10c715053843556114e10d6980538423e6494a108f592528425e6394a109758e528423f6454a108f191528425f6354a109718d528431f53d0610c714f41842ba60d0610c7d4d418431c5350610ae181418431f54cc610c715331842da60cc610c7d51318431c544c610b618131842f16008610c7d4e408431c5390210ad586408431f5310210c714
  | 2 => 0x605063097994418c25d651063097996218c25d6588630a7992218c29d648863097994218c25d6508630a7990218c29d6408630b6980218c2d96008630a7586408c31d5190230a7584408c31d5110230e6980408c23d61d51308f992544c25d639513097d8d544c23e65151308f584544c23e64145308f590514c23e65d05308f197414c23e65505308f195414c25e65cc530c7d53314c31c54cc530c7d51314c31c544c530d5d45314c23e65901308f994404c31f548c130c7152304c26e62150309b588540c27661150309d584540c23e6494c308f592530c25d6590c30c7151430c25d6510c30c7550430c23f64548308f191520c29f644c830a7191320c29e640c830a7590320c34d520c8308f992510c23d6494430cd945410c3355150430ae181410c35551cc43097596310c29e648c430a7592310c29e640c430a7590310c29e64cc030a7593300c25f654c030a7d91300c29c644c0309ed95300c2da60d5030c7550540c2ce6215030b3588540c2d66115030b5584540c2da6015030b6983520c29f6454830a7191520c29e6414830a7590520c34d5214830b5984520c2d56114830b6980520c2da6090830b6582420c25f655083097195420c25e651083097594420c2da60d4430a7992510c29d6494430a7990510c29d6414430b3988510c2cd6214430b6980510c31d51d0430a7983410c25e659043097596410c29d6490430d5546410c3555150430b6d81410c2d86050430e5d85410c3965150430c7545410c3955150430c5545410c39b6050430a7181410c3986050430a6181410c25e651043097594410c29e641043097996210c25d6588430a7992210c29d6488430d5546210c3555148430b6d81210c2d8604843097994210c25d6508430a7990210c29d6408430b6980210c2d96008430c7d06500c31d4194030d6982500c39b4194030e6506500c25d65d0030a7586400c31d5190030a7982400c31e5090030e6942400c25f6550030a7584400c31d5110030a7980400c39a6010030c7940400c39a50100309798f54c825d63d53208f58654c823f61553209798c54c825d63153208f99353c823d64d4f20c795253c831d5494f209758653c831e5454f20c755153c825f6154f208f99053c823d6414f208f99251c823d64947209798e51c825d63947208fd9741c823d65d0720c794f41c831d53d07208fd9541c823d6550720c794d41c831d5350720ae18141c825f65cc7209759731c831e54cc720c755331c825f654c7209759531c831e544c720c755131c82d8604c720c794e40c831d5390320c794c40c831d5310320c795230c831d548c320c795030c831d540c3209798f548825d63d52209798e548825d63952208f993538823d64d4e208f992538823d6494e208f992518823d64946209798e518825d6394620ba580218
  | 3 => 0xe40c7d4e53902ba6014e40a798f529029d63d4a40ae983529029e6394a40a758e529032f5294a40ae980529023f654ca408f195329023e650ca408f59432902ba60d4640a798e519029d6394640a798c519029d6314640ab98851902ad6214640ae980519031d51cc640a7983319023e658c6408f5963190397614c640c7545319029c604c6408f994319023d650c6408f996219023d6588640a798e219029d63886408f994219023d6508640a798c219029d6308640ae98021902b9600864097587535025d6114d409798c515025d63145408f997415031f53d0540c714f415031f5350540c714d4150337515054097997315025c65cc54097995315025c654c540c7d4e405031c5390140c754c431025f63548409718d521029f6350840a718d421029e6310840a758c421032d52108409798e511025d6394440cd547411023d6590440a798e411029d6390440a798c411029d6310440d59453110355514c440b6181311029e63d0040a758f401023f6550040a7d8d401029c63500409ed9540102ba60d4c40c754c53102ae6214c40ab58853102b66114c40ad58453102ba6014c40ae983521029f6354840a718d521029e6314840a758c521032d5214840ad98452102b56114840ae98052102ba608c840ae582321023f654c8408f195321023e650c8408f59432102ba60d4440a798e511029d6394440a798c511029d6314440ab98851102ad6214440ae980511031d51cc440a7983311023e658c4408f596311029d638c440cd5463110335514c440aed8131102b8604c440e5d853110396514c440c75453110395514c440c5545311039b604c440a71813110398604c440a6181311023e650c4408f594311029e630c4408f996211023d6588440a798e211029d6388440cd54621103355148440aed8121102b860484408f994211023d6508440a798c211029d6308440ae98021102b96008440c7cc6501031d3194040ce982501039b3194040e64c6501023d61953308fd8554cc23e64947308f59251cc23f65d07308f59741cc23f65507308f59541cc2b86050730c795331cc31d54cc730d554731cc31e544c730c755131cc26e62d52309b58b548c31e5450e30c7d50438c23e6494a308f592528c29f644ca30a7191328c34e524ca30a7990328c29d640ca308f992518c23d6494630a7992318c29d648c630d5545318c29e640c630a7590318c29e64cc230a7593308c2ce62d5230b358b548c2da60d5230c7d52548c2da6015230a7993528c29d64d4a30b6983528c29e6494a30a7592528c34f5294a30b6980528c25f6550a3097195428c25e6510a3097594428c2da60d4630a7992518c29d6494630a7990518c29d6414630b3988518c2cd6214630b6980518c31d51d0630a7983418c25e659063097596418c3976150630c7545418c29c
  | 4 => 0x7590524c74d5214931b5987424c6d561d093197d95424c65c655093197994424c65d6510931e5d47414c69e60d053197996414c69d6490531e5d85414c7975150531a7181414c65e6510531a7990414c69e64d4131a7593504c69f6454131a7191504c6cf6254131b3189504c71f4114131c7504504c65e63d50318f596540c63e60950318f181540c63e64150319798c540c63e64944318f592510c63d65d0431c794f410c63f6550431c794d410c71e54cc431c7553310c65f654c431c7951310c71d544c4319dd95310c756534c4318fd91500c63c645403197d8d54c865c63553219798c54c865d63153218fd9153c863c6454f218f99053c863d6414f21e550531c863f64543218f19150c865f63543219718d50c865e63d52219758f548863e60952218f181548865e63152219758c548863e64d4e218f593538871e5494e21c7552538865e6094e21c7951538871d5454e2197181538863e6414e218f590538871e53d0621c754f418871e5350621c754d418871e54cc621c7553318871e544c621c7551318863f64542218f191508865f63542219718d508865f63551219718d544867b60551219e181544865e63151219758c544863f6454d218f191534867b6054d219e181534863e6414d218f590534863e64d41218f593504865e63d41219758f504865e63d50219758f540867a60d50219e583540863d65950218f982540863c60550218f990540865e63150219758c540867a60150219e580540863e64d4c218f593530867a60d4c219e583530865d6594c21c7952530871d5494c2197982530871e5454c21c7551530865c6054c218f990530863d6414c219798c530867a6014c219e580530863e64944218f592510865e63944219758e510863d65d0421c794f410871d53d04218fd95410871e5350421c754d410865d65cc421c7953310871d54cc42197d95310871e544c421c75513108795414c4219bd9521087a54148421f14c521086776548421ce95250087395494021d694e50087595394021ced9250087386494021d6d8e50087586394021ced0650087394194021d6cc6500875931940218fd91500863c645402197d8d500865c6354021ce95150087395454021d694d50087595354021ced9150087386454021d6d8d50087586354021ced0550087394154021d6cc550087593154021dac85500876921540219758653d025f6154f409798e51d025d6394740c794f41d031d53d0740cd54741d031e5350740c754d41d025f65cc7409759731d025f654c7409759531d02d8604c740c794d439025e6394a409758e529029f6350a40a718d429032e5250a40a798c429029d6310a409798e519025d6394640a798e419029d6390640cd545419029e6310640a758c419029e63d0240a758f40902ae62d4e40ab58b53902ba60d4
  | 5 => 0x51cca3f64543328f19150cca7a60d52329e583548cb1f5410e328f992518ca3d64946328fd91508ca3c64542328f587544ca3e60d51328f992544ca5f63551328f994544cb1d63151328f584544ca3e601513297996434cb1c5490d3297195434cb1c5450d32c7152324ca3e64145328f590514ca3e64d41328f593504ca3d65950328f586540ca3e6095032c718d540ca3f61550328f181540ca3e64150329798c540ca5d65d0c32c7553430ca5d6510c32c7550430cb1d54cc83297d95320ca9c644c832c7551320ca6f654c8328f992510ca3d64944328fd91500ca3c6454032c754c43d065f6354b419718d52d069f6350b41a718d42d069e6310b41a758c42d072d5210b4197d8d50d065c6354341ad58753d071d5314f41ab98853d06ad6214f41ad58453d06b561d4b41a7d8d52d069c6354b41a798c52d069d6314b41cb54852d06b56114b418fd9532d063c654cb418f99432d063d650cb41a798f50d069d63d4341ab98b50d06ad62d4341a7d8d50d069c635434197982539065c6054e41c794f419071d53d064197d8d509065c6354241c714d435065e63149419758c525069f6350941a718d425072c5250941a798c425069d6310941a798e415069d63905419798f505065d63d4141ad58653506af6254d41ab18953506b76154d41aed8153506b86054d41c754c53506b56194941a7d8d525069c6354941add8552506bb6054941ae181525069e6314941a758c525072d5214941ad98732506b561cc9418fd95325063c654c9418f994325063d650c941a798f505069d63d4141a7d8d505069c6354141abd8950506ac625414197982531065c6054c41c794f411071d53d04418fd95411071e5350441c754d41106776550441cd951411065f63540419718d501066e62153319b58854cc71c5450f31c755043cc63f6454b318f19152cc69f644cb31a719132cc69e640cb31a759032cc74d520cb318fd9150cc63c6454331b558754cc71d5415331b398854cc6cd6215331b558454cc6d561d4b31a7d9152cc69c6454b31a799052cc69d6414b31d354852cc6d56114b3197d9542cc65c6550b319799442cc65d6510b31a798341cc7976150731a718141cc69e64d4331a759350cc6ce62d4331b358b50cc71f4194331c750650cc69f6454331a719150cc63e60952318f181548c71e54cc631c7553318c63f64542318f191508c66f62551319b189544c67b60551319e181544c65e65d0d3197195434c71c5450d31c7550434c63e64149318f590524c69f644c931a7191324c74c524c931a7990324c69d640c931a7992314c69d648c5318f993504c63d64d4131b5586544c6cf6255131b3189544c6d76155131b6d81544c6d86055131c7550544c6d56194931a7d91524c69c6454931b5d85524c6db6054931b6181524c69e6414931a
  | 6 => 0xf8800000264858a6c84ca7906c11f8002238b2a8f8a315988480005c11801ea8414116198e26592c14500020ea9895c0000000db0002839358d41f29a90000598a70000000628fc24e17d800000288a921150002189cc03f8b6a910000ee00880000004580012300018e85d9539c180006f8000970000bd9950f19d90568f00668811e41c31d209788a1088cd8ce9b893b9370178dfa8922308e24121c20a06913e19e8020000260680080b02a040000020000040000e00003403800000004010160000080000100a008000000000200a00900c0140d801000034070020000000300901a0000081001800404807004020000060000000500b0180000d00002c0280000a000024030640000000000000c00c0080400a00000000000060010010000c40c0000000040000700200c09000000060010000080080180100800001004012004008030000000a8080100440c83b00a028000010020000200800600c01801000010138050100040600401e0040000500c068028060040080100400004c0101b000000030070260000280600202800003022004018000040040100502e06c008000140000300a00a010000070180480380d00c000028000000000200c00a088000060080080000001a00c0300c00e0000100000e01005809014008028000100100080501e044048030000040100801c000020030080000a00001c0080c80600a0200180200e09400001008000000090040300000000e0040e008024020008000060180000a0320300100500e000098240000040401700800800017002000008110040000180600001401801008004100060000080080c0060200b8070060100100000200c010000000080000b01e00000001004004010000000100000000e00c0000700e0040400000c008018000080100580c00204c068390000300100801c000020000080040100100600403005000018000080040801e80200c054178010040480580301c00001001006008050020000500000600001c00000004020000000060101501200207c09000068004000010060300100500802c0200001a0040202c03c000000000000029d6490c438fd954310e5f6550c43a7d954310f1f6550c43a71894310e9f6150c43a71814310f1d4354843c750d5110f1d43940439798e51d0a5d639474297d8d50d0a5c63543429798e5190a5d639464297d8d5090a5c6354242975875350a5e60d4d42975845350a5e6014d428f9974350b1c53d0d42c714d4350b1c53909429798c5150a5d63145429798f5050a5d63d4142975865310a5e6094c4297d855310a5c6054c428f5964310b1d5390c42c754c4310b1d53d08428fd954210a9c6350842c754d4210a6f65508429798e5110a5d639444297d8d5010a5c63540429d98454cca756115332c715143cca3e64947328f592
  | 7 => 0x983027120c93f80011d1b4035259a1a95f0f39902321a4a6309a9470531319a500028e1c72260c22508000639bd00027c0002530c51aaa11a6514e01698b22a96c05380024ca0b8fb9069e69f610f85b83a0000000128e61290b02899c58001ec80026104d9ba0001eb8000001338000000001679ea00022f29c91400400c0f923695d23c00000019c0d928027e00691c8578ae0f1205a9d1c384903702f10b82b84500000000000000c8000001210000000000a50bd06080006180000011381ca470000000000b58001b58000bea3d24c25c2308fd8a1a859060000001f423a1d99561d60ea1621948ac07b00007a8002609f114b9b1a5b80a80002e9828f40000000c78cc94e9c097899aa8b22d07280007a2149af8000000000000000aa00000f80000010288d0710f811aa6c19c9c695a05028aa2e2430001d38d898d90a80008400022c8000000000001fd2462242980001e580028300e2109c90000000a2800124810000074830a9180027e8fe92786123f8001a7800000279a0e0e007d8e381b1d6a6208189d8920000d200002a20387c8eba0516e8ae8781d7a498b48001c81d40482190df08b95e262a9c0d11d0a6601ba5b2378001be8ba85b1ad82303380014c8001f2240a000fb0672450940000000002548000000002110000000000d29608000000d50000000002338000000001038000bb9590000000000001e02680a000007200000000000025a0000078001be00022b1c21080ce2088519d29099e89e325f14f83681589d19208985e0cc00081da878e100000b8a09258b20000a4a2529a9879531cc8cf9548c10880809ee00000000028e80000000009380000023e80000014a8002329ad00028c92702921f8000000839499159af00000000000001389f00029f8e91311d01c00e0a7812f0da95a92387ea4011c00000018f90c2559988b0a8201f847023a278061d187997198c27d8870050709e7114892a0607b8e31870900f78002269732221dda6916422027f8000a900024f16294407c0221421120de9908469218731330a6a282619ab9f8992a1400f0ef9938ff03d8581701ce1e49f98a59a182292e91b245a3e0261199f3a3495701d20694d9fe8b721d89693d88013494393091608e92d0a38db80000018a8001521e09cd1090000000000f502180000020d0d78fa94f01aa5ea57a6f9749b518a0e1a699569981221798ee878a0116987195b0421b31e9a0191a1601bf25e17917c03d0140640000b904e8d5a550461818099d729600009c0b98cd0eb1a6a0499314086e18385084a2440681e90002318058002811cf2180e980026ba938bb0401b6a43800000042800000185a5d0f30998c5a501cd8002031df80013a29280000000000027a80016b82b0000f49ba99780000013280000013f00018800000009315da8d0
  | 8 => 0x15502e11f0379fa8001281fa17400001c003a1ba529bb8000002818b617ca6d8960b400008c8000a20000000888ad23c8000298ac8001820028000630001c791190e05a03e0ec2538a8800138090a8815284a98100019e1b4a1a1a200000022c04300025d93c00024180025c8170001bc81185d02518f02788218687f80015111d96880000000003111b8dd8268280000001de9b38382730ba0e4a3899594585480000027d1019850e581120b25408f1ef9e826a0e81a2a1691316f8001f491889c8000000000fd1e394600000017e00018d1d58988b18081d48af067a0705f9db80017580023f28d8af8000002998000001f1a0a8000409eb00025100000000014309e0000200000f08000000000150001588b38000000570002950272a00002588000000d800700b00008597f8000000000001848bc9fd9720cf1a015e8bc000263a4490327480012c80000027714d00000004d2391f903ba3980000000014a000025a009d50a817106a00000000026f2101a106593a8001d11ff800290a8f1b29cb8dd136222a20a170189b90241c103b01094c0001768c724b29692f958082a8286e824a1d0c315789b1990d083301907687f03f24910028727b8eaa8c0c496104f9da0560f223301f2569e210400020f0000002159389b7a5a8001e600e9e28c08868b50fe10d91e0b8a8a0ab0001750448bf10480017600000012b92680000023d80000d03ca7b148280a9e8ab80216e1c9a8b8000000f9a9a27a00006b21e88b03985217f09e83a966a7ca47a5602887928481a00017a0002291190000980000cb0002979890d30660da1cf84b80d87d1a0924101231094800077a729ef19a10b08c0b10001a380003600022712b164a679ed8be0e700027406c9f09509998001341f31008000510d9800000163000000000070139800297095800000202a6017a891800000165000000000235a760000000f2a2980000001480000000009ba302700000489aa0fc80000023aa090001ea8000000000f68d182a80000000014000023b0d000019b8000000eda0f97780002f8001b01a88001110aa8001b1000032000212a718000000319488890001e10c294b00023600000000018896d92d9919bfa4d8910540dc16a0001e18000000761051ca9368000d49351bd80024a8e20a601829f0600000160ec82083ea211941970c692005e8000001840a10b30000000e413d117a4e8878000e51801d80000b80758001f02079fb1419c613790a2751f797726729319f0a7a2b9d30ad91715000a1c49f597e9b608321e1808750211aea4a0e7a73a581898cb9479a61830c39ff2570000f583c2352519c51b08000000000000001e780000024f8002709968000e29670018de0c61d89a41109070000bfa6e1ac0000411f816f07e208149268a9da94a7f25f8d61a317d04
  | 9 => 0x5c84c09506da76a9e1020ff9dc8698ca1ab0000b799d8000001ce8000990ed0c892298b80000000016c8620000002958e8916a4224d22d80029b00025204195c80010580009a00029b93c8000000001f500017b0001fb996047a2ea6a99115413906b8011dc0e683588f98616607401e12096d04f0f70c920222f82c00000021222a2130001a58558000851b99f71b821600025905a97080000005506502d0001518000002941de00903423b92e00026b1a70000000000000000002150d710e800052a6680000016901300010d17b88d99b2219261b220d91e90c84b0001ca0c189f8a42991c88ca8d69449e50000c4012000004834a4295fa138002860000000001bc1ed129a868592259ae142a6ea199129f6a380199300c01b724886d24b9df1fc0649eea179738c99659db2640c80fa125246a721078001288d380004e0a99780000862371fe20404421c9ec06f20c29007727880002c9c29c4172955a0996a91005f2759bb12a073a6d16b1680001639a983912a8002850000439ac80013b0001a802da2890f0dca34000068a1b19d0328f61321fc80000006a80008a80000000015ba4818c8ef00013e800277a2480019fa1f1468388001da8000031dd1cb
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0xca00bec25ad89c003e42a800003a0000007486c48c5496cc00dac000000e0000de2ad2188414d6d410201e282cac9800b00056ce12003002ae0ac8ba3cb280886048aa445c8ed07a9ab638b49070042e62001c00c60c5e00bc246adc00004a9200a400468200b87c943458a09e78081aa64c1664367626004e228a686c7e0672526e4032a26650000b000101030101020008050a0402170501140101007e04021a0718000c0e0c08010e0602a2ee2a1aa221d187050e5010e8ab88a8a1e65469c35410e32838ecaa2641960d6354842d0706a9ac429e838358d5214b41c18c629284a0d0c7254c535068c382a629a83255c66314941a18e6a90a4a0d2870548525061c382ca19283435c85450f31c1ac8a906598e0d5458854cc706b22a429663431c95410d31a30e0aa08698e0c64149324c686392a82a263461c1541513192ae3320a498d0c74548524c6a4382a429263161c16510931a30e0a08a098f11414c55008790a0a42a8043d04c52154021a2ae329a83a060c639494290287396a729c81439cf5294a40c1ac6a908420651511813110306a9ac4298818554d6114c40934e1b1aa42060d635485210312a92c2290810d5c4654c840930e0b1ca220631511813110388a8ec09888185544604c440e22a2302622069251181311030ca88c098881a4544604c440c22a230262204987058e211030ab1aa310881455c6544c730a1ce5aa0871860c64949328c287396a92a461439d35294a30a1ae42a2861851571151430c306b22a4190618c5446050430c1aa8b10a81861554584540c24d386c8a9061835915214830c8aa4b08a41845571195420c24c382c928861945446050430e22a3b02821861551181410c388a88c0a0861a49446050430c32a2302821869151181410c308a88c0a0861261c16488430c2ac8a8c421861561544400c28ab8ca6a0e418694c6050720a2ae32a2639061a5418131c83882888018241a81844048020d80c2182401061853181418430c2a0c098c2185d4d6110210c2ea8b0861084e276c85208430c298c0a0a218a1486050510a28eaa0a62886146550531443822928298a21641c1414c510c30a83026288648521813144348a08c098a218554d6110010c4aa4b088008615545843004322a92c218021465d4400c010c32ca20060087095210030042c8b888018021a4584400c010
  | _ => 0
def s0K2 : Nat → Nat
  | 0 => 0xe000c000140030004124281c00a108058d5188440a10805915188430a118194c6050720a1181950604c720d00521c1414c510e0052504604c510c11655c4400c010d01525c4400c010c1175584400c010e0152584400c010
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 48
  | 5 => 1017
  | 4 => 1345
  | 3 => 112
  | 2 => 10
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s0K7 (i*5) 5
  | 6 => packedAt s0K6 (i*16) 16
  | 5 => packedAt s0K5 (i*27) 27
  | 4 => packedAt s0K4 (i*38) 38
  | 3 => packedAt s0K3 (i*49) 49
  | 2 => packedAt s0K2 (i*60) 60
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s0K7 (6+((h/1+packedAt s0K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s0K6 (864+((h/16+packedAt s0K6 (768+(h % 16)*6) 6) % 58)*7) 7
  | 5 => packedAt s0K5 (31188+((h/339+packedAt s0K5 (27459+(h % 339)*11) 11) % 1477)*11) 11
  | 4 => packedAt s0K4 (56038+((h/448+packedAt s0K4 (51110+(h % 448)*11) 11) % 1776)*12) 12
  | 3 => packedAt s0K3 (5784+((h/37+packedAt s0K3 (5488+(h % 37)*8) 8) % 135)*8) 8
  | 2 => packedAt s0K2 (615+((h/3+packedAt s0K2 (600+(h % 3)*5) 5) % 18)*5) 5
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffff81ffff83f07ffff83ffc1ffc0fcf9f3f3
  | 2 => 0xf07fffe0fffffff81f07fc3ffe1fffff463c7f
  | 3 => 0xff81ffff03ffc3ffe007ffc3ffe1ff0387cf9c
  | 4 => 0x1fffffc0003fffff80003fffe0003f80fe0
  | 5 => 0xfffe0000000003fffffffffc00000003fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x210c08c42890400165098044c022425818d1b1
  | 2 => 0x44109102412221280a422429121494a1422446
  | 3 => 0xa22522481a440652a084ca8265412a0a854a98
  | 4 => 0xcb59c4929076ab9cd3d06223b9980c33e80f60
  | 5 => 0xc61871ce38733e71ce77330311030c3f7b000
  | _ => 0
def s0Atlas : Atlas := ⟨7,rawDecor 62 s0Pos s0Neg, 0xfcccfcc0fcc0f0c0fcccfcc0fcc0f0c0fcccfcc0fcc0f0c0fcccfcc0fcc0f0c0fcccfcc0fcc0f0c0fcccfcc0fcc0f0c0fcccfcc0fcc0f0c0fcccfcc0fcc0f0c0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_17005
namespace PEqualNP.Outside.L_meta_17005
open PEqualNP.Outside.L_meta_17005.Model
def s1K4 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K3 : Nat → Nat
  | 0 => 0x9d43
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s1K4 (i*5) 5
  | 3 => packedAt s1K3 (i*16) 16
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s1K4 (6+((h/1+packedAt s1K4 (5+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt s1K3 (17+((h/1+packedAt s1K3 (16+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x7ffff83ffff83f07fff07fff83fffc0f39f3f3
  | 2 => 0x87c1ffc3e0fffff8707f8783fc3c1fffd64c9f
  | 3 => 0xf801fffc00ffc3ff807ff803ffc01ff0e78f1c
  | 4 => 0x1ffffff0003ffff800003ffffe000f80fe0
  | 5 => 0xfffe0000000003fffffffffc00000000fff000
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0x800880400040008090088880444422009131
  | 2 => 0x2112910909522128342485112428894c524486
  | 3 => 0x12a52290d2a406538859502aca8152a2a58b18
  | 4 => 0x5539c42a9836ab9d5d0c4443733380c4f80ec0
  | 5 => 0x663187331cc733e66e6e667062220308ff6000
  | _ => 0
def s1Atlas : Atlas := ⟨4,rawDecor 61 s1Pos s1Neg, 0xfaaafaaafaaaf0a0faaafaaafaaaf0a0faaafaaafaaaf0a0faaafaaafaaaf0a0faaafaaafaaaf0a0faaafaaafaaaf0a0faaafaaafaaaf0a0faaafaaafaaaf0a0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_17005
namespace PEqualNP.Outside.L_meta_17005
open PEqualNP.Outside.L_meta_17005.Model
def s2K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x46002008a10ee21ec21ef20ed20f710f510
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x202d2a010f848110
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 6
  | 3 => 2
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
  | 4 => packedAt s2K4 (104+((h/2+packedAt s2K4 (96+(h % 2)*4) 4) % 9)*4) 4
  | 3 => packedAt s2K3 (56+((h/1+packedAt s2K3 (54+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x81fffff81ffffc0ff0ff83ffffc1fffd18fe3f
  | 1 => 0xfe07e0ffe07e0ff0ff0ffc1e07fe0f02ef33cc
  | 3 => 0xfff800ffff800fff000fffe007fff0030fc3f0
  | 4 => 0xfffffffffffff0000007fffffff003ff
  | 5 => 0xffffff0000000ffffffffffff8000003fffc00
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x8c104408c1044401101190aa30c85518085615
  | 1 => 0x14b18511472854b07106948c534a46286b32cc
  | 3 => 0x2862d6a28a1d6d57088b5ac8a5ad64530dc370
  | 4 => 0x714518c414510a6aaaa04201063188e3b001aa
  | 5 => 0x4186108718618b8ccccc6311c0210083d6a800
  | _ => 0
def s2Atlas : Atlas := ⟨5,rawDecor 59 s2Pos s2Neg, 0xeeeeeeaaeeaa0000eeeeeeaaeeaa0000eeeeeeaaeeaa0000eeeeeeaaeeaa0000eeeeeeaaeeaa0000eeeeeeaaeeaa0000eeeeeeaaeeaa0000eeeeeeaaeeaa0000, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_17005
namespace PEqualNP.Outside.L_meta_17005
open PEqualNP.Outside.L_meta_17005.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x6548894eac01a1800000004c0000861500005c41f02000005000e804438da540980003c016a358840001ea49241a143823850c802c1800b202808280000000100343830008282ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32df32fe32fd32dd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10f710fe10fd10f510fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x14640662003c5a43077236235c005e675773417153423a654d63254b0066690024000000332b5f00000029001a030068002200510000004f5b4a08276f1c1b443000001f45000059287400000000005200000e5d004c2e31000000206046003d0000260d6c3b6b00004e0b1d0954003402213f002f5055323713004700116a356e2a1e00001538000f000a0c2c6149012d704800580016046d3e0039194000121000001756000018050000000007030002000091000300000180828000000101810000818000808101000a8180808380006750c43b7290876d5210e7aa9215794e42aea9c85775150ae8a2a16bd4942dba8a85b45150a7ca8215794c42aea98859f42ccb3a85994f952329eaa4655d538cb5a85196b50932bba8a6574514cb9ea49967d0932e7212659d424cb9a84996350932eba8a65d4514ca7ca8194f55032af298655e53d06baa7a0db94b41b6a96833e54cc67aa998db94b31b6a96633e54c867aa990d794f21aea9e43ad428879a6510cf950219eaa0435e53086baa610eb50821e6990437a50086f2a010dd94640baa8c815f53502b8a6a05794c40aea98816e52102daa4205d94440baa888176518c2eaa3184fd51309e2a2613e540c27aa8185b94830b6a906176510c2eaa2184f953209eaa6415e53c82baa7906b50b20e6996417651882eaa3106b50920e6992413e540827aa8105794c20aea98417651082eaa2106dd0b10daa1621d732c43aa65885d546109faa2213c54442bea6885714d10b7a92216c524436ea8886d15110eba9a21d453443cea4887914910dba1221b542443ae6488754c910f9a8221f220443e240885d94410
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x20049c280000000000818b8698008002202800402c31440000e580000a9a90001e0800c00000c0c350d5210f254214532a3592424cac46150932e1d85424cb846150932e150b514cb854214532c354d420870d544c821ca5095008749325402193588535022d6215130c354d42c830d544cb20e150932c43245414910d114c52442346550910951953244385424c910e850920443c13248110
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x500180a0cebb0a84994877650b514ca823aa849922181195424c910
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 117
  | 3 => 24
  | 2 => 4
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s3K6 (i*5) 5
  | 5 => packedAt s3K5 (i*16) 16
  | 4 => packedAt s3K4 (i*27) 27
  | 3 => packedAt s3K3 (i*38) 38
  | 2 => packedAt s3K2 (i*49) 49
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s3K6 (6+((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s3K5 (841+((h/15+packedAt s3K5 (736+(h % 15)*7) 7) % 67)*7) 7
  | 4 => packedAt s3K4 (3471+((h/39+packedAt s3K4 (3159+(h % 39)*8) 8) % 170)*8) 8
  | 3 => packedAt s3K3 (960+((h/8+packedAt s3K3 (912+(h % 8)*6) 6) % 44)*6) 6
  | 2 => packedAt s3K2 (199+((h/1+packedAt s3K2 (196+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x83ffff07fffe1f07f0fe1fffc3fff81e89f3f3
  | 1 => 0xfc1e1ff83c3fe1f8ff0fe1c1fc383fe176cd9c
  | 2 => 0xffe01fffc03fffff000ffe01ffc03fff870e1f
  | 4 => 0x1fffffc001fffff00001ffffc001f80fe0
  | 5 => 0xffffe000000001fffffffffe00000001fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x884001108000200010120244404888440050b1
  | 1 => 0x19442231905402287106208cc41192c432c594
  | 2 => 0x208954420aa91153088954112a822519850a0a
  | 4 => 0x729598852a0d559daaa11021b3270189d80f40
  | 5 => 0x431910e6333199e6cccd993822040611efa000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeeeeeaeaeaeae0e0eeeeeaeaeaeae0e0eeeeeaeaeaeae0e0eeeeeaeaeaeae0e0eeeeeaeaeaeae0e0eeeeeaeaeaeae0e0eeeeeaeaeaeae0e0eeeeeaeaeaeae0e0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_17005
namespace PEqualNP.Outside.L_meta_17005
open PEqualNP.Outside.L_meta_17005.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x321052a36040004220ea80000000007c82d163129a003c02b001549800453141c012160e0011e00343124001180005c9833825380000002c44540c1800a101801200001120c080ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30df30fe30fd30dd30fc30ff20fe20fd20fc20ff10f710fe10fd10f510fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x300f7052275e432512175b150d6042050a00341a144a656c000c014e4b63002d530000571c00002c5f240000734823310b28002972541f46020013006a21373610223341666d5559686e003d002f2b5d08005171000050323c3f695a07033e6b3a0e044c1d1849116f624558404f741e162606200900003b2e19392a645c004d001b006756470000004435386107859001800a810a88800000010100810500000000000101009187070d8100008c028003830c005d94643baa8c877a5090ef2a121cf55242afa9a855c5350aeea2a15d14542bda8285785050b3ea6a16714d42d7a9285b75150b68a2a16ed4142dc282853e5410a7ca9194f55232bba8a6574514ca7ca8194f55032bb2886575510caf4a0195e54032af29c835d53906f4a120de54241ea988637a500c6f2a018cf953219eaa6435f53486b8a690cf950219eaa0435e53086baa610de94021bca80435e53902baa7205d94640baa8c815e53102baa6205b94840b6a90817651102eaa22067d0b30cea16615d538c2eca3185d546309faa2613c544c33ea8986715130cfa12619d424c3b6a09876d0130ec202615e530c2eca2185d544309f2a6413d54c835a85905794e20aea9c417651882eaa310764c220d6a1241d9304827ca8104f55020af298415d53082eca2105d54420dba1621b542c43ae6188754c310af29c215d53842eaa308764c2109faa2213c54443b260886dd5110da2a221b7424436a84887cd4110f9a0221f040443ae60887c8c110ea98221f130443a260887c88110f8902215e53042baa6085d94410
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0xc280aae09602c000014920412a2260838070679a126242400ac89c614c5050b3051141429c580514cb51315403196580534861c6550930b2588404c2d16110130d45453088389424c120c615130442346550910b458c40442e16210110b458e30442b0644c110e4d913044390644c110e4d513044390544c110e4d093044391424c110b458e20443a14248110
  | _ => 0
def s4K2 : Nat → Nat
  | 0 => 0x1a0010a24ebb22608849276d5130442483b28498221441d5424c110
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 117
  | 3 => 24
  | 2 => 4
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
  | 5 => packedAt s4K5 (841+((h/15+packedAt s4K5 (736+(h % 15)*7) 7) % 67)*7) 7
  | 4 => packedAt s4K4 (3471+((h/39+packedAt s4K4 (3159+(h % 39)*8) 8) % 141)*8) 8
  | 3 => packedAt s4K3 (952+((h/8+packedAt s4K3 (912+(h % 8)*5) 5) % 29)*6) 6
  | 2 => packedAt s4K2 (199+((h/1+packedAt s4K2 (196+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xf87fffe07c3e1f0e3e1fc7fff8783c1e467e93
  | 1 => 0xff83e1ff803fe1f03fe1f8f03f803fe079b31c
  | 2 => 0xfffc01ffffffffffc001ff003fffffff81c3ff
  | 3 => 0x1ffffc001fffffe00003fffc001fe03e0
  | 5 => 0xfffffe00000001ffffffffffc0000001fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x491850230944a902068a41519c48a44c421691
  | 1 => 0x5328924519988b301aa8c862acc129c458b314
  | 2 => 0x2001048820200044400112040112121081402a
  | 3 => 0x4652d912510ccd9aaccc00493665a0896e03c0
  | 5 => 0x8463001c623110ed3111a48e00060311b5e800
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xfeeafeeaf0e0f0e0feeafeeaf0e0f0e0feeafeeaf0e0f0e0feeafeeaf0e0f0e0feeafeeaf0e0f0e0feeafeeaf0e0f0e0feeafeeaf0e0f0e0feeafeeaf0e0f0e0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_17005
namespace PEqualNP.Outside.L_meta_17005
open PEqualNP.Outside.L_meta_17005.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x1e32295a136000014a21680000142c00a8d2618005800000029309138f2814b0e004c0071a7c106008cba020000113800003124800000100222a74100810420005020c3031408002ff43fe43fd43fc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30df30fe30fd30dd30fc30ff20fe20fd20fc20ff10f710fe10fd10f510fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x5f426510365c1e1d146208004600271807564e716c676b3e09193700164429280f0000481b256917000000006633232253114f437068602000036d0c742f24000a50000e3c345a056f016e4d3530581a2a38005e1f5b045132470b0000632b3d726a002d733100000059154506210d3b2e26003a5d004b00001300000000553f57404c00390012000000005441494a61001c2c00000000025200640203830000010580000080000900038480000000000e8580020501030b000106868004808000805d94643baa8c877a5090ef2a121cf55242afa9a855c5350aeea2a15d14542bda8285785050b3ea6a16714d42d7a9285b75150b68a2a16ed4142dc282853e5410a7ca9194f55232bba8a6574514ca7ca8194f55032bb2886575510caf4a0195e54032af29c835d53906f4a120de54241ea988637a500c6f2a018cf953219eaa6435f53486b8a690cf950219eaa0435e53086baa610de94021bca80435e53902baa7205d94640baa8c815e53102baa6205b94840b6a90817651102eaa22067d0b30cea16615d538c2eca3185d546309faa2613c544c33ea8986715130cfa12619d424c3b6a09876d0130ec202615e530c2eca2185d544309f2a6413d54c835a85905794e20aea9c417651882eaa310764c220d6a1241d9304827ca8104f55020af298415d53082eca2105d54420dba1621b542c43ae6188754c310af29c215d53842eaa308764c2109faa2213c54443b260886dd5110da2a221b7424436a84887cd4110f9a0221f040443ae60887c8c110ea98221f130443a260887c88110f8902215e53042baa6085d94410
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x92e78818000000069c00e000026580a8049002c00002208000a100000628520000300008341000001c614c5050b3051141429c580514cb51315403196580534861c6550930b2588404c2d16110130d45453088389424c120c615130442346550910b458c40442e16210110b458e30442b0644c110e4d913044390644c110e4d513044390544c110e4d093044391424c110b458e20443a14248110
  | _ => 0
def s5K2 : Nat → Nat
  | 0 => 0x184010a24ebb22608849276d5130442483b28498221441d5424c110
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 46
  | 4 => 117
  | 3 => 24
  | 2 => 4
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
  | 5 => packedAt s5K5 (841+((h/15+packedAt s5K5 (736+(h % 15)*7) 7) % 67)*7) 7
  | 4 => packedAt s5K4 (3471+((h/39+packedAt s5K4 (3159+(h % 39)*8) 8) % 155)*8) 8
  | 3 => packedAt s5K3 (960+((h/8+packedAt s5K3 (912+(h % 8)*6) 6) % 48)*6) 6
  | 2 => packedAt s5K2 (199+((h/1+packedAt s5K2 (196+(h % 1)*3) 3) % 8)*3) 3
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xf87fffe07c3e1f0e3e1fc7fff8783c1e467e93
  | 1 => 0xff83e1ff803fe1f03fe1f8f03f803fe079b31c
  | 2 => 0xfffc01ffffffffffc001ff003fffffff81c3ff
  | 3 => 0x1ffffc001fffffe00003fffc001fe03e0
  | 4 => 0xfffffe00000001ffffffffffc0000001fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x491850230944a902068a41519c48a44c421691
  | 1 => 0x5328924519988b301aa8c862acc129c458b314
  | 2 => 0x2001048820200044400112040112121081402a
  | 3 => 0x4652d912510ccd9aaccc00493665a0896e03c0
  | 4 => 0x8463001c623110ed3111a48e00060311b5e800
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xfeeaf0e0feeaf0e0feeaf0e0feeaf0e0feeaf0e0feeaf0e0feeaf0e0feeaf0e0feeaf0e0feeaf0e0feeaf0e0feeaf0e0feeaf0e0feeaf0e0feeaf0e0feeaf0e0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_17005
namespace PEqualNP.Outside.L_meta_17005
open PEqualNP.Outside.L_meta_17005.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0x120520000a841c1c980000000009879f20931700160f81039411859b16800e800310800294800688900000158f0d06179b89191d198b0180150e1f800b9d9280080082189a0a0c07049a8da10ca1939e1e91128c0610c080c0000d161858200046230220003027fd5007fe54007f55007fc54027fd4c05fe53007f54c05fc5301ffd0c05fe43007f50c05fc43027fd48017f52007f94801fd52005f54809fc5201ffd0801bf42007f90801fd42006f50807fc42017fcc801fe32007f4c805fc32027fd4401fe51007f54409fc5101ffd0401fe41007f50407fc41017fcc401fe31007f4c405fc31007fc8401fe21007f48401fc2100ffd4003fe5000ff54003fc5000ffd0003fe4000ff50003fc4000ffcc003df3000ff8c003fd3000f74c003fc3000ffc8003fe2000ff48003fc2000ffc4003f71000ff84003fd1000fd44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2a420fff19521025f8ca90803ff64484017fb22420eff9912101dfcc890803fd64484017eb22420eff1912101df8c89083fff544841dff2a24200ff55121077f8a890803ff63484017fb1a4200f7d8d21005bec690837fe63484057f31a4200ff58d21005fac690837fc63484057e31a4200f718d21015b8c69083fff534841bff29a4200ff54d2106ff8a69083bff434841bff21a4200ff50d2106ff8869083fff5248401bfa924207ff94921007faa4908037d524840ffe292420effd09210077e849081ffe4248401fea124200ef5092103ff88490837ff324840fff1924200ff4c92103ff8649083fff5148401ff28a4200ff5452107ff8a29083bff4148401ff20a4200ff50521077f88290837ff3148401ff18a4200fd8c521007fa6290803f5314841bfe18a4207ffc852103fee4290803fe2148401f710a420cffd8121065fec090833fe60484037f302420cff58121065fac090833fc60484037e302420cffd4121067fca090833fd5048419fe282420cffd0121067fc8090833fd4048419fe202420cffcc121067be6090833fe3048419fe982420cf74c121067f8609081fff2048419ff102420cff4812103ff84090833ff1048419fb882420cff84121067fa2090833f51048419fe0824205ffd942103dfeca1081ffe65084097f3284207df99421024fcca1081ffd65084017eb284207df59421004faca10817fc650840f7e3284205ffd902103dfec81081ffe64084077f3204207ef9902101d7cc81081ffd64084017eb204207ef590210057ac810817fc640840f7e320420affd502104ffca810803fd5408413fe2a04205ffd8c2103dfec61081ffe63084057f3184207f798c21015bcc61081ffd63084017eb184207f758c21005bac610817fc630840f7e318420affd4c21047fca610803fd5308411fe2984209ffd0c21047fc8610803fd4308411fe2184207bf9882103ffea41081f7f520840fff2904207ff5482103efaa41081ffc520840fffa104207efd082103ffc841081ffd420840fdea104207ff1082103ffe641081ffe320840ffe9904207ff0c82105dfcc21082bff510840bff2884200ff5442102ff8a210827ff410840bff2084200ff5042102ff88210823ff310840bff1884200ff4c42102ff8621081fff210840ff79084205ff8842103fec421081ffd2108401f69084207fd4842102ffec01081eff600840fff3004201bf9802103ff4c010806fa600840ffeb004206bf5802103ff2c010802f9600840bfe3004201bf18021037fea01081bfe500840dfea804206ff14021037fe801081bfe400840dfea004206ff10021037fe601081bdf300840dff1804206ff4c021037ba601081bfc300840fff9004207ff8802103ffa401081ffc200840bff8804206fdc4021037fc201081bfd100840dfa8804205ff04021
  | 1 => 0xffe204c42ffe9026217ff081310bffe209885ff7104c42fff0826217ff441310bfea209885ffc104c40fffb2e4207bfd972103ffccb90812fe65c840fbf32e42049f9972103ffacb90802fd65c840fbeb2e42009f5972103ff8cb9081efc65c840fffb264207bfd932103ffcc99080efe64c840fdf3264203af9932103ffac990802fd64c840fdeb264200af5932103ff8c99081efc64c842dffaa64215ff95321007faa990857fc54c840fffb1e4207bfd8f2103ffcc79080afe63c840ffeb1e4200bf58f2103ff8c79081efc63c842dffa9e4214ff94f21007faa790853fc53c842bffa1e4214ff90f21007fa8790853fc43c840fffa964207dfd4b2103ffca59081ffd52c840fbea964207ff14b2103ffe859081fbf42c840fff2164207ff50b2103f7a859081ffc42c840fff9964207ff8cb2103ffa659081ffc32c842dffa8e4200ff94721007faa39085bfc51c842bffa0e4200ff90721007fa8390857fc41c8429ff98e4200ff8c721007fa6390853fc31c840fffb064207bfd832103ffcc190806fe60c840ffeb064213bf5832103ff8c190806fc60c8427ffa864213ff9432109ffaa19084ffc50c8427ffa064213ff9032109ffa819084ffc40c8427ff9864213f7cc32109ffc619084ffd30c8427ee9864213ff0c32103ffe419081ffe20c840ffe9064207ff0832109ffe219084ff710c8427ff0864213ff4432109fea219084ffc10c840bffb2c4200bfd9621097fccb10812fe6588401feb2c4200bf5962102ff8cb10812fc658840bffb244200bfd922108ffcc91080efe6488401feb244200bf5922102ff8c91080efc6488425ffaa44211ff95221007faa910847fc548840bffb1c4200bfd8e21087fcc71080afe6388401feb1c4200bf58e2102ff8c71080afc6388425ffa9c4210ff94e21007faa710843fc5388423ffa1c4210ff90e21007fa8710843fc43884197eb144212ffd4a21006fea51081ffe5288401fea944200df54a2103ff8a510847ff4288401dfa144207ff90a21007fa8510803bd428840ffe2144210ffcca2103ffc6510803fd328840ffe1944207bf98621097fea310817fe5188401fea8c4205ff1462108ffe8310817fe4188401fea0c4205ff10621087fe6310817fe3188401fb18c4200ff4c621007ea6310817fc318840fff90c4200fbc862103fee4310817ff60884177fb04420bff9822100dfcc11082ffd60884177eb044205ff1822100df8c11082fff5088417ff284420bff5422105ff8a11082fff4088417ff204420bff5022105ff8811082fff3088417ef984420bff8c22105ffa611082fdd3088417fe1844207ffc822105ffc411082ffd208840ffe1044205ffc422105fee211082ffe1088417fe884420bfd4422102ff82110803ff65484017fb2a420fff99521025fcca90803fd65484017eb
  | 2 => 0x4100dfcc0a0877fd605043b7eb02821dff1814100df8c0a0877ff505043bff282821dff541410eff8a0a080fff4050407ff2028203ff5014101ff880a0877ff305043bef982821dff8c1410effa60a0877dd305043bfe182821dffc81410effc40a0877fd205043bfe102821dffc41410efee20a0877fe105043bfe882821dfd441410eff820a0817ff658c4017fb2c621cff99631025fccb18803fd658c4017eb2c6205ff19631025f8cb18817ff648c4017fb24621bff9923101dfcc918803fd648c4017eb246205ff1923101df8c918873ff548c437ff2a46200ff552310dff8a91880afd638c405ffa9c6202ff94e31017faa71880bfc538c405ffa1c6202ff90e31017fa871880bfc438c40bffb146200ff98a3103dfcc518803fd628c4017eb146205ff18a310e7fea5188037f528c401ff2946200ff54a31006faa518873fc528c437ffa146200efd0a31007fc8518803fd428c401dea14621bff10a31017fe651880bfe328c401ef1946202ff4ca31017f8651880bdc328c4057f30c621cffd463102ffca318803fd518c40bfe28c621bffd063102ffc8318803fd418c40bfe20c6202ffcc631017be631880bf7318c40bfe18c6202fd0c63102ffec11886aff608c435ff3046201bf982310d7fac11886afd608c40bfe3046201bf182310d7fea11886bfe508c435fea84621aff142310d7fe811886bfe408c435fea04621aff10231017fe611880bdf308c405ff1846202ff4c2310d7ba611880bfc308c435ff904621aff882310d7fa411886bfc208c40bff884621afdc42310d7fc211886bfd108c435fa8846205ff04231007feca98802ff654c433ff32a6204bf99531007faca98802fd654c433fe32a6204bf19531007fec898802ff644c431ff3226203bf99131007fac898802fd644c431fe3226203bf191310cffea898863fe544c401feaa26218ff15131015fec69880bff534c405ff29a6202ff54d31017f8a69880bff434c405ff21a6202ff50d31017f88698803ff624c4017fb126200ff98931007fac498803fc624c40f7e3126219ffd4931006fea498803fe524c401fea926200df549310cff8a498863ff424c401dfa126200ff90931007fa8498803bd424c431fe2126202ffcc931017be649880bfe324c405fe9926200f74c931017f8649880aff614c433ffa8a6200ff94531007faa298867fc514c431ffa0a6200ff90531007fa8298863fc414c405ff98a6202fdcc531017fc6298803de314c405fe18a6202f70c531017e8629880bd4314c42fffb026217bfd81310bffcc098806fe604c42ffeb026217bf581310bff8c098806fc604c42fffa826217ff941310bffaa09885ffc504c42fffa026217ff901310bffa809885ffc404c405ff9826202f7cc131017fc609880bfd304c42fee9826202ff0c1310bffe409885
  | 3 => 0xea92a200df54951027f8a4a8897ff4254401dfa12a200ff90951007fa84a8803bd425444bfe212a224ffcc951007fc64a8803fd3254449fe192a204bfd8551027fea2a8813f75154409ff28aa200df94551027f8a2a88137c5154409fa28aa225ffd055112ff882a8893ff3154449fe18aa223ffd815111dfec0a888ffe60544037f302a223ff5815111dfac0a888ffc60544037e302a204ffd4151027fca0a8813fd5054409fe282a223ffd015111ffc80a888ffd4054447fe202a223ffcc15111fbe60a888ffe3054447fe982a223f74c15111ff860a888fff2054447ff102a223ff4815111ff840a888fff1054447fb882a223ff8415111ffa20a888ff51054447fe082a205ffd9641005fecb2088bfe65904097f32c8200ff59641005facb20817fc65904097e32c8203bf5924101ffea92080ffe5490407df2a48203ff552410077aa92080ffc549040bffb1c8221ff98e41015fcc720803fd63904017eb1c8205ff18e41015f8c72088bff5390443ff29c8200ff54e4110ff8a72080fff4390407ff21c8203ff50e4101ff88720817ff6290401ff3148207bf98a41007fac520802fd629040bfe3148222ffd4a41006fea520803fe5290401fea948200df54a41117f8a52080fff4290407dfa148203ff90a4101ffa8520803bd4290407fe2148221ffcca41007fc6520803fd3290443fe1948203bf98641117fea320817fe5190401fea8c8205ff1464101ffe832080fbf4190407fba0c8205ff1064101fe88320887ff319040bfe18c8205ffd8241105fec120883fe60904037f3048220ff58241105fac120817fc60904037e3048220ffd4241107fca120883fd5090441fe2848203ffd024101ffc8120883be4090407fea048203ff1024101f788120883ff3090441ef9848220ff8c241107fa6120883dd3090441fe1848220ffc8241107fc4120883fd2090441fe1048205ffc4241107ee2120883fe1090441fe8848220fd4424102ff82120803ff65504017fb2a821fff99541025fccaa0803fd65504017eb2a821fff19541025f8caa080eff6450407ffaa28203ff9514101ffaa8a080ffc5450401ffb1a8200bfd8d410f7fcc6a080afe6350401feb1a821eff18d41015f8c6a087fff535043dff29a8200ff54d410f7f8a6a080fff4350407ff21a8203ff50d4101ff886a0803ff62504017fb128200ff98941007fac4a0803fc625040f7e312821fffd4941006fea4a0803fe5250401fea928200df549410fff8a4a080fff4250407dfa128203ff9094101ffa84a0803bd4250407fe212821effcc941007fc64a0803fd325043dfe1928203bfd85410fffea2a0803fe5150401fea8a821fff1454101ffe82a080ff74150407ff20a8200ef9054101ff882a080fbc4150407fa20a821effcc5410f7f862a0877ff605043b7fb02821dff981
  | 4 => 0x3fd654c8017eb2a642bff19532025f8ca99003ff644c8017fb22642aff9913201dfcc899003fd644c8017eb22642aff1913201df8c8990afff544c855ff2a26400ff55132157f8a89901eff634c805ffa9a6402ff94d32017faa69900bfc534c805ffa1a6402ff90d32017fa869900bfc434c8057fb12642bffd4932006fea49901ffe524c801fea926400df5493203ff8a4990abff424c801dfa126407ff90932007fa8499003bd424c80ffe2126402ffcc932017de649901ffe324c80fef1926407ff0c93203fb8649900bec324c801ffb0a6400bfd8532007fcc299003fd614c801fe30a6400bf1853215ffea2990affc514c855ffa0a642aff10532017fe629900bdf314c805fe18a6429ffd813214dfec0990a7fe604c8037f3026429ff5813214dfac0990a7fc604c8037e3026429ffd413214ffca0990a7fd504c853fe2826429ffd013214ffc80990a7fd404c853fe2026402ffcc132017be609900bfe304c805fe9826429f74c132017f8609901fff204c853ff1026429ff4813203ff840990a7ff104c853fb8826429ff8413214ffa20990a7f5104c853fe0826404bf5965102ffec9288a3fe64944077f324a200ff59251005fac928817fc64944077e324a204ffd5251026fea928813fe5494409feaa4a200df55251027f8a928817ff639444fff31ca202bf98e51007fac728802fd639440bfe31ca202bf18e51027fea728813fe5394409fea9ca204ff14e51147fe872889ffe4394401fea1ca227ff10e5102ffec528803fe629440f7f314a200ff58a51005fac528817fc6294409ffa94a204dfd4a51027fca528813fd5294401bea94a204ff14a51147fe8528803bf4294401ff214a200ff50a510077a85288a3fc429444fff994a200ff8ca51007fa652889ffc32944097f30ca204ffd4651026fea328813f7519440bfe28ca204fd14651147fe8328817fc419444fff98ca205ff0c65102ffec12889aff609444dff304a201bf98251137fac12889afd609440bfe304a201bf18251027fea128813fe509444dbf284a204ff54251027f8a1288137c509444dffa04a226ff90251137fa812889bfc409444dff984a226f7cc251137fc612889bfd309444dee984a226ff0c251137fe412889bfe209444dfe904a226ff0825102ffe212889bf7109444dff084a226ff44251137ea2128817fc10944097fb2aa200ffd9151005fec8a8897fe64544077f322a200ff5915112ff8c8a880efc6454409ffaa2a204ff95151027faa8a8813fc5454401ffb1aa200bfd8d51127fcc6a880afe6354401feb1aa224ff18d51015f8c6a8813ff5354409ff29aa204ff54d51027f8a6a8897ff4354449ff21aa200ff50d51127f886a8803ff62544017fb12a200ff98951007fac4a8803fc625440f7e312a204ffd4951026fea4a8813fe5254409f
  | 5 => 0x94201fde84a101ffe425080fdf2128407ff1094203f7884a100fec4250861ff9928407ff0c942007fec2a1002ff6150801ff30a8400ff58542007f8c2a1002fc6150863ffa8a8431ff1454201ffe82a100fbf4150807fe20a8403ef10542187fe62a10c3fc315085fffb02842fbfd814217ffcc0a1006fe605085ffeb02842fbf5814217ff8c0a1006fc605085fffa82842fff9414217ffaa0a10bffc5050807ffa028403efd014201ffc80a10bfbe4050807fea02842fef5014201ff880a100fbc405085fff982842ff7cc14217ffc60a10bffd305085fee982842fff0c14203ffe40a10bfef205085fff102842fff4814217fda40a101ffc205085fff882842ffdc414217ffc20a10bffd105085ffa882842fff041420077ecaa10c7be6550801deb2a8431ef195420077ec6a10c3be6350801deb1a8430ef18d4218f7ea6a10c3be5350801dea9a8430ef14d4201f7ec4a100ebf6250807d7b128431efd49420067ea4a101fbe5250801dea928400cf5494203f78a4a10c3bf325080fde1928400efd85420077cc2a1003bd6150801de30a8431efd454218f78a2a10c3bf3150861de18a842fefd814217f7cc0a10bfbd605085fde302842fefd414217f7ca0a10bfbd505085fde282842fefcc14217f3e60a10bfbe305085fde982842fe74c14217f7860a101fbf205085fd7902842fef8814217f7a40a10bfad205080fde102842fefc414217f6e20a10bfbe105085fde882842fed4414217f7820a101fff658c80f7fb2c6407ff99632025fccb1901f7e658c8093f32c6407ff59632005facb1901f7d658c8013eb2c6407ff1963203df8cb1901fff648c80f7fb246407ff9923201dfcc91901fbe648c8075f3246407ff59232005fac91901fbd648c8015eb246407ff1923203df8c9190bbff548c85bff2a46400ff5523216ff8a91900afd638c805ffa9c6402ff94e32017faa71900bfc538c805ffa1c6402ff90e32017fa871900bfc438c80f7f3146407ffd4a3203efea51901ffe528c80ffea946407df54a3203ff8a51901fff428c80fdfa146407ff90a3203ffa851901fbd428c80ffe2146407ffcca3203fbe651900bef328c80ffe1946407fb0ca3203ffec31901ffe618c8017f30c6407ff58632005fac31901ffc618c85dffa8c642eff1463216ffe83190b7fc418c805ff98c6402ff0c632017b8631901fff608c80f7fb046407ff9823200dfcc11901ffd608c8597eb046407ff1823200df8c1190b3ff508c859ff284642cff54232167f8a1190b3ff408c859ff204642cff50232167f8811900bff308c805ef9846402ff8c232017fa61190b3dd308c805fe1846407ffc823203ffc411901ffd208c80ffe104642cffc4232167ee21190b3fe108c859fe884642cfd44232167f82119003ff654c8017fb2a642bff99532025fcca99
  | 6 => 0x1bf30aa400df58552006f8c2a90eb7f4154875be20aa439dfcc5521cef862a90e37f6054871bf302a438df581521c6f8c0a90e37f4054871bf202a438df501521c6f880a90e37f3054871af982a438df8c1521c6fa60a90e35d3054871be182a407dfc81521c6de40a90e37e2054871be902a438db4815203ef840a90e37f1054871bb882a438df841521c6fa20a90e3751054871be082a403efd974201f7ccba100fbd65d0807de32e8403efd8f4201f7cc7a100fbd63d0807de31e8437efd4f421b77ca7a1003bd53d086dde29e8437efd4b420067ea5a101fbe52d0801dea968400cf54b4203f78a5a10dbbf32d080fde1968403efd874201f7cc3a100fbd61d0807de30e8437efd47421bf78a3a10dbbf31d086dde18e8403efd834201f7cc1a100fbd60d0807de3068435efd43421af7ca1a10d7bd50d086bde2868435efcc3421af3e61a10d7be30d086bde9868435e74c3421af7861a101fbf20d086bdf1068435ef4834203f7841a10d7bf10d086bdb8868435ef843421af7a21a10d7b510d086bde0868407ffd964203dfecb2101ffe65908097f32c8407df99642024fccb2101ffd65908017eb2c8407df59642004facb2101ffc659080f7e32c8403bf5924217d7ac92100fff5490807ff2a48403ff5524201ff8a92101fff639080fff31c8402bf98e4203ffac721002fd639080ffe31c8407bf18e421a7fea7210cffe5390801fea9c8433ff14e4201ffe872100ffe4390807fea1c8403ff10e4203dfcc52101fff529080fbfa948407ff94a4203ffaa52101f7d529080ffe2948407ffd0a4203f7e852100fef429080ffe2148407fb10a4203ffe652101ffc329080fffb0c8407ff98642005fcc32101ffd61908017eb0c8407ff186421a7fea3210d3fc5190807ffa0c8403ff1064219ffe63210cffc319080fffb048407bfd824203ffcc121006fe609080ffeb048432bf5824203ff8c121006fc6090865ffa848432ff94242197faa1210cbfc5090807ffa048403ff9024201ffa812100ffc4090865ff9848432f7cc242197fc61210cbfd3090865ee9848432ff0c24203ffe412101fef209080fff1048407ff48242197da412101ffc2090865ff8848432fdc4242197fc21210cbfd1090865fa8848432ff04242007fecaa1002ff6550863ff32a8404bf99542007facaa1002fd6550863fe32a8404bf1954203dfec8a100fff5450863dfaa28403ff9514201f7ca8a100ffd5450801deaa28403ff1514201f78a8a1003ff63508017fb1a8430ff98d42015fcc6a1003fd6350861fe31a8402bf18d4218ffea6a10c3fe5350801fea9a8430ff14d4201ffe86a100fbf4350807ff21a8430ef90d4201ffa86a1003bd4350807fe21a8403ef10d4201dfec4a10c7ff5250801bfa928407ff94942007faa4a10037d525080ffe2928403ffd
  | 7 => 0xa90fb7e30d487dbe986a43ed74c3521f6f861a901f7f20d487dbf106a43edf4835203ef841a90fb7f10d487dbb886a43edf843521f6fa21a90fb7510d487dbe086a404bf596521c4facb2901fff649480fff324a403bf9925203f7cc92900ebe649480ffeb24a400bf5925203f7ac929002bd649480ffe324a407bf19252027fea929013fe5494809feaa4a404ff1525203ffec72901ffe63948057f31ca407ff58e52005fac72901ffc639480f7e31ca404ffd4e52027fca729013fd5394809fe29ca43dffd0e521e7fc8729003fd4394879fe21ca407bf98a5203ffea52901f7f5294809f7a94a407ff14a5203fd8a52901fff429480ffe214a407ffcca5203ff8652901fff619480fff30ca400bf9865203ffac329002fd619480ffe30ca404ffd4652027f8a3290f7ff419487bfe20ca43cffcc6521e7f8632901fff609480f7fb04a407ff9825200dfcc12901ffd60948777eb04a407ff1825200df8c129013ff5094809ff284a404ff54252027f8a1290efff4094877ff204a43bff502521dff881290efff3094877ef984a43bff8c2521dffa61290efdd3094877fe184a407ffc825203fde412901ffe209480ffe904a43bfb4825203ff841290efff1094877fb884a43bff842521dffa21290eff51094877fe084a407bfd9552007fec8a9002ff6454875ff322a403bf99152007fac8a90ebfc64548077e322a404ffd5152026fea8a9013fe5454875bf2a2a404ff55152006faa8a9013fc5454809be2a2a400ffd8d52005fec6a90e7fe63548057f31aa400ff58d521cff8c6a900afc6354809ffa9aa404dfd4d52027fca6a90e77e5354809fea9aa400df54d52027f8a6a90137c5354875ffa1aa439ff90d52007fa86a90e7fc43548097fb12a404ffd4952027dea4a901ffe525480fbf292a407ff1495203ef8a4a9013ec5254875ffa12a407ff109521cffe64a901ffc3254801ffb0aa400bfd8552007fcc2a9003fd6154801fe30aa400bf18552027fea2a90137f5154809fe28aa404df145521d7fe82a90ebfc4154873ff98aa439ff0c5521c7fec0a90e2ff6054871ff302a401bf981521c7fac0a90e2fd6054871fe302a401bf18152027fea0a90137f5054809ff282a438df94152027faa0a90e37d5054809fe282a404df141521c7fe80a90e3fe4054871fea02a438ff101521c7fe60a90e3df3054871ff182a438ff4c1521c7ba60a90e3fc305480fff902a438fbc81521c7fc40a90e3fd2054871f6902a407ff081521c7fe20a90e3f71054871ff082a438ff441521c7ea20a90e3fc1054801bfb22a43adf99152006fac8a90eb7c6454801bfb1aa439df98d52006fac6a90e77c6354875bfa1aa439df90d52006fa86a90e77c4354809bfb12a4049fd8952026dec4a90eb7f425480fbe212a439dfcc95203ef864a90037f615480
  | 8 => 0xfd015401f7e80aa00ffe4055007fea02a845ef5015401ff880aa117ff305508bef982a845ff8c15422ffa60aa117dd305508bfe182a845ffc815422ffc40aa117fd205508bfe102a845ffc415422fee20aa117fe105508bfe882a845fd4415422ff820aa00aff6554c01ffb22a600bfd9153227fcc8a980efe6454c01feb22a644ff1915301df8c8a9813ff5454c09bfaa2a604ff95153027faa8a98037d5454c09fe2a2a602bfd8d53017fea6a9813df5354c05ff29aa602df94d53017f8a6a980b7c5354c05ee29aa602ffd0d53017fc86a980bfc4354c01ffb12a600bfd8953007fcc4a9803fd6254c01fe312a607bf18953027fea4a98137f5254c09fe292a644ffd0953227f884a980bff3254c05fe192a600ffd8553005fec2a9803fe6154c01feb0aa600ff18553005f8c2a9813ff5154c09fe28aa644ffd0553227f882a980bff3154c05fe18aa643ffd815321dfec0a990ffe6054c037f302a643ff5815321dfac0a990ffc6054c037e302a604ffd4153027fca0a9813fd5054c09fe282a643ffd015321ffc80a990ffd4054c87fe202a602ffcc153017be60a980bfe3054c05fe982a643f74c153017f860a990fff2054c87ff102a643ff4815321ff840a990fff1054c87fb882a643ff8415321ffa20a990ff51054c87fe082a600ffd9543005fecaa190bfe6550c097f32a8600ff59543005facaa190bfc6550c097e32a8602bfd914301ffea8a180ffe5450c07df2a28603ff551430077aa8a180ffc5450c057fb1a8602ffd4d43017fca6a180bfd5350c05fe29a8602ffd0d4301fbe86a180bfe4350c05df21a8602ff10d430177886a180bdc4350c01ffb128600bfd8943007fcc4a1803fd6250c01fe3128607bf18943217fea4a190bfc5250c07ffa128603efd094301ff884a180bff3250c05fe1928600ffd8543005fec2a1803fe6150c01feb0a8600ff18543005f8c2a190bff5150c85fe28a8603ffd054301ff882a180bff3150c05fe18a8641ffd814320dfec0a1907fe6050c037f3028641ff5814320dfac0a1907fc6050c037e3028641ffd414320ffca0a1907fd5050c83fe2828603ffd014301ffc80a180ffd4050c07fe2028602ffcc143017be60a180bfe3050c05fe9828641f74c143017f860a1907ff2050c83ff1028641ff4814320ff840a1907ff1050c83fb8828641ff8414320ffa20a1907f51050c83fe0828604dfd9352026fcc9a90137d64d4809be326a404dfd8f52026fcc7a90137d63d4809be31ea440dfd0f521fefc87a90037d43d487fbe21ea440dfd0b5203ef885a90ff7f32d480fbe196a404dfd8752026fcc3a90137d61d4809be30ea440dfd0752206f883a90ff7f31d487fbe18ea404dfd8352026fcc1a90137d60d4809be306a43edfd03521f6fc81a90fb7d40d487dbe206a43edfcc3521f6be61
  | 9 => 0x500100700100200300000100300100000400000000000200100400900200300001800000000000200300000200000200f00400000000200100000000200500400000b00000000a00600100200600000000000100000300000200100300000100200200800201100200e00100700000000000000100000300100200000300000000100000000500000000100800700500200900000900100001700600100f00200900200000000000000000200100801f00100100000500400600600000100300000000100500000600a00300100000000500200200000000200001000000000100500d00400200000000c00000600100000400500000a00f00000100200b00a01500000200100100300800000f00000000000000800300100000700100000000000a00300200000300500000400100700400700000000300000600400300100500400100000000100000200000100000600000300400200100100000200000500c00600300000300200200000000200200000800000000100600100000000100000000100200000000200400600000500100000000300000300500100000100100700001d00f00000600000200700000400200600200000200f02200000400400b00000100000000300100000100100000300000000301000600400300000100000300000900200300600200400000000100000000000c01000000000200400100500100200900000100300000100400200000000601000100300200000700200100100100100300800000300f00100000100200900101501a01900300300200d00100200100d00000100200100100400600100300000f00800100700000000400400000600000400100100400300000100300000500000500000000b00100400000000a00500001000000a00700100300000000200400000d00300600400400300f00200100200402800200300000100200000000400000000000400000000000000100100001dfecaaa00eff6455007ffaa2a804efd515401ffca8aa00f7e5455007fe2a2a803df1515401f78a8aa00f3c5455001ffb1aa800bfd8d54237fcc6aa00afe6355001feb1aa846ff18d54015f8c6aa013ff5355009bfa9aa804ff94d54027f8a6aa00fff4355007dfa1aa803ff90d5401ff886aa003ff62550017fb12a800ff98954007fac4aa003fc625500f7e312a804ffd4954026fea4aa013fc5255007ffa12a803efd095401ff884aa11bff325508dfe192a800ffd8554005fec2aa003fe6155001feb0aa800ff18554005f8c2aa013ff5155009fe28aa804df1455401ffe82aa00ffc4155007de20aa846ffcc554237f862aa117ff605508b7fb02a845ff9815400dfcc0aa117fd605508b7eb02a845ff1815400df8c0aa013ff5055009bfa82a804ff94154027faa0aa1177d5055009fe282a803f
  | 10 => 0x1dc98b4de00000f2914c9840000719974a9a0003ce10600003ef16e80000004612e7000000046c2aa8dc477618e000001100280a13b8000bb80002c08cd8a560d82290000b220002ae05980000003f6942c0006540001edc0000fe33799d8a0a5143bf098c9d43e43390ef4a0e08005d8c04c6070f343949cdce1ea05b800000043f000000000000000003980000d900000000000000000a00000396000000054e18f2dd84389546650cc955c53600014300002843b319d059ccdc23b0000a9800038100000000ca00000015ec36c21f20d040401007f03d0830a5455f0e998603ec000338849462000012f0000000153000000077c4e912a00000000001fa826024e00009110e836040000000000007bb21a8b0cea232f00000000000000000c740000000000d2c00048000c00000000000000000e16000000000032c11d29c17f48f20001c30000eca00010f014c88e0332ca0864b322ec1750270cd825b1018558e8c4c33be8ffc8fc2ef2709d4c4e237e1fd06246343980d892783740e027911b808e0003ee963c00044c20a80000000002be9bd800008a0000aac0000001c61b640005b3144000000023500011bc00008d000000000069632f9fb000047638e1a5c6d871d20911e8e5862634c823c6784bc38f84a028c5180b61a7c0000d1260832456e61008480f83bc2d722516ace880000bb9720ed25d700000000000000000aa400000000000009f600000000000000001149e880006f700015383e82b92cd00000000001160f10b1c0321cf90287100421b903c43ce0722068e9477880029608b81181aa1180e2c8e600025898487b6000000000025a0952079f6c4d20003c280002f665a0001fa8a841f500000000dc00006580000007b30f59114b6c2bd0000000c567f200015b000000000000000000003108000bd65163c993b40005081f002381060002cf80000004833a1800099a4ac25b89c029c1ab02b000045600600100000100700000000300300000200000100100000900200000400100300100401f00900000000000200100000300200000000400000000000700000500600200200100000d00300500100600400500100700100000300e00900e00100000400200100100100300200100300000000300400100000500000000000000301300600000000000000300400200300300d00100000700000000200100900700000000400000400001800a00000000400200101e00200000200c00000000000100400100800500000d00200600300200000000700000300000100900000300100000201000800400000300000100300000200000400000000600d00a00000000000000300500000200400300400301000202b00100400400301d00000100500000400000000100000000300500100200a00000200000000000100100c
  | 11 => 0xec37a1ca000000000036a1298000e1a00006e1a140000000f000002da00007611d400000000000005bc5aa000176c8680001840b28000681000000071a0000d78000b72000352815d01016100000e80000000000758e12000000050c00000d36880006b616f0ff8000ecc5671ab8b5400078609b128000053d1b70868f021023e01db0a5e1e438800000c82110000268e4c6881f080000003fb0000118d0014415e1f709c00000b703bc0002f719012245186cb18b03840704db00004a40000002de169c00028f00000009387eb00000000000004018000c263113cf8d986821f70591410d7c0000f31cdc0007e51488b400000002b517c40006270df950c00064f3579bfc000000000166c97a10a3240000c5e0000ca1fd47421ce3c40f700004ab3298f4800011600000008420000001cf0000000000000000000000007cc00000000017782681e300002200000000000f0c49e08914f01c0ca21d2147022c00000001286a000000024d8e6c6d000000010c0cce1a23b7000028e2450000e8073232100014a468a00000006542900000000000000000000000000011a00016d00000000000f58bec6f300001680000000001d640006d30d180005207920000a14000000000194000022700000004d62280d49e340006bf3a508a896a45e0a785d40004081749258a5a51320494c01ce16a193151c2aa36320592440000000000840c6200019b82442e800000000000000003c399304b4000000000000000000001800000003c613c00000000001ac0e023783a8158000044d0001174d2a71b0990000dc83ab3649c3000045630a831ca0c80936206280124cc22c0ebc8260002ad1ccccac4dc000110834c27a2850000fdc0000001d00b8e0001c900000003b200000000000000000c300000001f700006de5e42789ef0c585a207580000000000318000000647371800000000036f0198a6405d0000000000614000000040e000000000000000016492549600262928d8000000014e0000d4673a0d38dcc2f000c0ab9ad000056540286ec75a00000000007b260a189000009833d09d996c2c854900003403b0000000191822000023413d88a00002f69efcbb400000c800030800000000000002922389fd8f540af2358ed40a80001f4800000013c00000002486433291e2c2ec02d1d20ec0e7a20435b0834df867e2368304af25820000bac53e2ee2508b2c0de0390001bb813e16500000006800001ec09a0ed400000000000001be0000ca00000000001110a444772cb17c060a00000007f85ac0000000000000000321000023600000009301ba00000000006280000001b5400000000000008d405933e10b4f4a000000000000067d0000c784c80000001b5c07a0000000000caa0000eb8300eb83760879fe4a5c4401c0047c1fe000000185ceda00
  | 12 => 0x9e12900006ce64e00010cc0d607c34810746ba0131a4086065c3d11e017c838c58009f035ce2c5191b29f48c0e0002fd1c1c7f21c837f029428a00000018340000213e41f643160003119eacc50000000082440c2e72e11ca491c2ff2ac0000db832b0000a2802a3220000a2c00051e030982c70600a3a90a34d9867416d07500000003b900000000b833316149be0bc10d884cd8e4f83ba9b149b400000009d0e3239c380000038a4bb3e59ef4d262373cc8ff00006b211f9c28f5074c3bb9b000006f40000c6c00032d0a882cc000000185061830400000000000000002e2912c00000003b9904a2e09709a9f7cce60000000000000000000000038e4111b5874095e4be07418d46941bc12a9e244be3932fe124086c1132d20d880002fb39b03b820c01d1641ebc87663911a1dd0224150000033829214b000000000000000001204a04fd1870000ac20bd31e8ddc42c6402db9e7400075d00019e8fac0002c181a80004310000da41be0002b486900ce12a2bf116475c0a00001124ffc3cd000183cb623021f39a80eec42b0001dac05c0000000000e8a2df000000076200029d1388000000000000000000002e040c0000003cc03180005202fb8000c6e00000018180007d804380000000304058000dbe2080000000b380000001ae402e00013004cc34a6a10610ea4d1253621e1c4422e15b0000ea800000000000000007d11d600002bc8040000de40007ce1090b3c00019807800bcc5c19a0b018ec4167ae13780000000002de81600001d900009b41a8000000000000000015680806f622617180000000000000000fb400000000000000001329ea49183f720398102460003061740a780ae2b58ed00000001628fa09ca00030f04548821c90000000000000298876c39600035b9f84bac5a30cd8000a3e0001f51e00ef40000ae9c5400068e3c10000a4800000000009e83d72ca8768608000000000000000000000000000002c500000004cb1c891980000002e0919c168329000000000000000011a427a000000092ccf60000000c600002c400000009d677800000008580000af95982a860e39880000000001a300000000002548000d5600004c80000006ec37697e0dde42500000000007831dc1d800004f70000000baa5e53249f540000000000000e7e38e35d974c00001c2a200004a2005187800006c000000000000000001580000000000058ee83400002190000f7061a01a8000cea4de30e01a41505e0141000056a00023f98fcfbc30315f9ef8fae0001050d2416c37c0fc1de420031300014ec3c41cf1c10b6c0003ed29a1dfcbf6000325186400000000012b80b60001199d240000000268edc0000002d680000000000001344794139000000035c1a12739fdc0000003550a04d701b739807844f80001211cf86681d51f101
  | 13 => 0x121301961088c0000000000904000000000069c0000001910a8000023e00007a02d41df88e80003511109dc00446000000000ee20850000000b300001cd18e000040205f1520ee60000000d4cac849400f8530b260003f203a40000000000e406b200000000001c848731e00004ce000210161c06e3392a88a5058267900000000005ec2c3110c00000000000000005e70001ce000000000002840000001c480000005af0000de80004d22b10c1c15855b11215746a048b00013185c06331308e74a063e62a998d05fa2e6202800000000002f1e28c6c000000180800028918310f400031c000073420a0000000000000000349129000035223d8b1807855424780001600ca33f94d4a960003959cb4d5868a07b9c48e6444822b83d0a506a71a39694e3004f13909700584161240c8cf9a4c93f38f74c7474b0be97e47a65260000000a9401b16c96e0ba86f82df14f8db00003fc13f86700003ad17441f25c4000162479c00000000002706dd0000814b640002b7955800007d2d009649742e81560000e9a5720fd1b04fa00960001f100000000f4916867600022a8000000000000056449a0fb00000002b40cc00010b8ae804e0ae000000030b0148fc80005e110096a40000f600009e40000000000000000000000000032052325400000007a7000000000023137000005646b116381b000000000008700006ca000000000031700000004703de39a01d40004921fe925cf1e00026a0c24e345712569d04d28000000000000000004080001880f800003b4f8e0000248d78fc60073d0800000004400012341280003f980004001910311718c103a80000000000568000113ce047ba0e61ae80000000000078000629243000041e6583599ce4ae6678000000097e2a51aa1548d483e313b00000000000000000f2c000053977c000000003088000063e00080000002b40001c9ca2a5d908a1e54d1e000000000000000020080009fe35f1f60000f682f500001e0cd60ba0000000f721b930480000004d30fd87c493000000000000000000000d7000000000000005f20001ac06b00000001ca07e40003b60001f800000001e489f40000002cb8000a98241000000000012e00019c0054000000000000000020f1310162130381809c0007b200006e08ca00000000003660000859eb04ae62028100004cc0683b400000001973cd105c03466929f927402200021c0000f9e2a23f806b4000000000029879e00000a00000000b519985e80000000e895fc1ac0000c60fd00004513ff81e4dd60fa3e2800000001600004349ae000000000000024e000017cf920000001e50ece0000000000ec42e400005acb5c42f000000000000010b9f3020e10c0001390eae62a3678000aec4b400012200008072ba99880008020000ac041c240000070c6847
  | 14 => 0x38a1ca8e906631399440bb02e132f00000002dc11b0fc000055000000000000001690a5c0004b930f800000000036400000000000e017009a003b00000005b02ae2ee8f940006c60ce9e6c94e0000001c4c404000000000074614d000000000000015d1a2c00070e3430a642385883f31ab8a382fc000000000050d3420000000000000000000000000000000000002d809fc2e06ad00016fc00077c00001f8fa60aa2dd05a008250f1f58000ede00004e93980000842be0000f6000000000000005e83d180000000a90000bb40002be00006483d00f20001990a007e91ef83cc74c3f600000005e218700012881ea1830000b4c4ba0000000fc40000000001b68506000029108c4722f33d31d78da4742384000019a0bf10e85a42fc2440b10cc8d304601ca9c78adc56d0399c844464263ac02487fc57020c8b3483e24301a18c8d361ee15003f03260002021e38526000000026c0007a00000000cda3c70001c8c0000000219a740000000001ff40000000001724b427563670bc0dcc0001c7927c4d80003bd80000000002fa032015a6a213115140000c533b858cb9658c0000000b6a43e1b69fec10c00026000009b00000000a908c66f90c418449aa79026412640000000000bc80000023d20e1479600034d1c800000000000b943be0000cf195c00000000000005700b93350000b9a000000146c0001f000011386fa0003da80000006e90558e5c0000000000000e08000011969800024a0698560784414274089473c4220000ca80000000001be8e2e42a3911a709dc6910000000a224060000634c36000000000055e4b332c90e40000000cf80000500003d680000000002380e10b940000da00004ac0002e19090000000000091c00043728e99a0000000000000000000037d800000000009b8a8c00042800000005660000001a0c0003a22798aec00048a000000007e00013d94480004ca1c3800000011929b800000017909780007e6000000000000038a000000068829609880000000002b18bf8b5076309600001bc000000000000037f1ba80008b610800000009c600023a000100c4b22fa8000c2c68226e96340000000000000bd400000781440000000081cb800000011900006c86d40bf80484fc3c10001678e6a00000007b0dac000000173c9de33e1a18bd0dc24c53e10c9c5427c3354000053075b1ea80007f00000001f180000000000000be65ee069000000062409592e0db60000820000000300000000000000000017480005e600000000005213f7800056c140392187453469e0001468c8a45f0000b006aa00004100000000003f107040004f9000070800000006d1f281b659d0e200009b250109f8f302e64a622a0000b9872f3549c18aee2b100000004d40000000cd44f018106784980006a603b1b940002f80750
  | 15 => 0x6000137077400000026790303de00013a80006c200008c1d1c000000000000000000000006c80622cc2a799340000001ba030c0004843db150400045c000000000047d17b0000000000000024c000478000118800022d0000cc094a3561110000cc05e92c58f200002fa0000e9c0000000001ca080640e0000000f08045025000000011e0000c34f222152861c142746e237a920400033f000000078a76137406d4af02d10a9000093468c0ee17bc64a4b63aa09240806cd1ea1d7c00066100000000004fc2ac8000a66539214800078c590000000000073b3ea0a1000000035a8090fd0000263981499c0000000f6800000000000000000a200000000000000001d3c00000036180000000000000000c9665c1ad00002e47640f907f000024600000009f400008881d09ea0003110c906620000000b380005ac21380008c85e33788480000797025824000018500002900000000f680000000000000000000141000000050e6f2000000000009e00000009462c21b808f053a0001540c640000003fa1d541466bc00000000e200024983548365923a71ba80006c2000000000000012c000090a00e072800000062527605f00000000000000fe200000000005c400014a81b445e00018a800063e23e2f10d340a032c0000000a8c0000fe80001fa4101a60aa82e27c13fe0000a127b137e91c83381802af0d3cc026d026b17f847a50e10a17fc0aa0003fd10701c40000a51a340000002bd1c94d7a
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x52158c2102edc2158c21006df7058c21004df7058c21006de7058c21006dd7058c21004dd7058c21006dc7058c21006df5058c21006de5058c21006dd5058c21006dc5058c21006df4058c21006de4058c21006dd4058c21006dc4058c2103edf2058c2103ede2058c2103edd2058c2103edc2058c2102edf1058c21006d71058c21006de1058c21006dd1058c21006d51058c2102edc1058c21004ff7654c2102cfe7654c21004fd7654c2102cfc7654c210267e6554c210067d6554c21226be6454c21006bd6454c21016de6354c21006dd6354c21005f77154c2102df47154c2121efa6054c21004ff7650c2102cfe7650c21004fd7650c2102cfc7650c212167e6550c210067d6550c2101ebe6450c21006bd6450c21016de6350c21006dd6350c21005f77150c2102df47150c2120efa6050c21094ff76544210267e65544210067d655442112ebe6454421006bd6454421126de6354421006dd635442111efa605442108cff76504210fe7e65504210067d655042101ebe6450421006bd64504210f6de6350421006dd63504210eefa6050421084ff764c4210ce7e654c4210067d654c4210c6be644c421006bd644c421016de634c421006dd634c421086f6614c42102fd4314c4210befa604c42102def7648421006ef7648421004ef764842102f6e654842102f6d654842102fae644842102fad6448421007cf7348421007cc734842102fce634842102fcd634842102def714842103fe7714842102eee614842102fe6614842102fe65148421007e5514842102fe64148421007e5414842102fea604842102fe9604842123fcf304842123fcd3048421006fb7558021006fa7558021006f97558021006f87558021006fb7458021006fa7458021006f97458021006f87458021006fb5458021006fa5458021006f95458021006f85458021006fb7358021006fa7358021006da7358021006f97358021006d97358021006f87358021006fb5358021006fa5358021006f95358021006f85358021006fb4358021006fa4358021006f94358021006f8435802103efb725802103efa725802103ef9725802103ef8725802103efb525802103e7b525802103efa525802103ef9525802103e79525802103ef8525802103efb425802103ebb425802103efa425802103ef9425802103eb9425802103ef8425802103efb325802103efa325802103ef9325802103ef83258021036fb715802102efa7158021006f27158021036f97158021036f1715802102ef87158021006fb515802102efa5158021006f9515802102ef85158021006fb415802102efa4158021006f9415802102ef84158021006fb315802102efa3158021006f9315802102ef8315802103efb215802102efa215802103ef2215802103ef9215802103ef1215802102ef82158021
  | 1 => 0x9021004fd705902100cfc705902104ebf4059021006be4059021006bd405902104ebc4059021006df3059021006dd3059021006f71059021006f51059021006bf7559021006be7559021006bd7559021006bc7559021006bf7359021006be7359021006bd7359021006bc7359021006bf5359021006be5359021006bc535902103ebf725902103cbf725902103ebe725902103ebd725902103cbd725902103ebc725902103ebf525902103e3f525902103ebe525902103ebd525902103e3d525902103ebc525902103ebf325902103ebe325902103ebd325902103ebc325902104ebf715902102ebe715902102ebc7159021006bf515902102ebe515902102ebc5159021006bf315902102ebe315902102ebc315902103ebf215902102ebe215902103ebd215902102ebc2159021006bf7059021006be7059021006bd7059021006bc7059021006bf5059021006be5059021006bd5059021006bc5059021006bf30590210069f3059021006be3059021006bd30590210069d3059021006bc305902103ebf205902103ebe205902103ebd205902103ebc205902102ebf1059021006b71059021006be1059021006bd1059021006b5105902102ebc1059021004ff765502102cfe7655021004fd765502102cfc76550210267e65550210067d655502101ebe6455021006bd645502104f3c5455021236de6355021005f7715502102df4715502122efa6055021004ff7558c21024fe7558c21024fc7558c21004ff7458c2101cfe7458c2101cfc7458c2102cff7358c2102edf7358c21006df5358c21046de5358c21046dc5358c21006df4358c21046de4358c21046dc4358c2103cff7258c2103cfe7258c2103cfd7258c2103cfc7258c2103e7f5258c2103e7d5258c2103ebf4258c2103ebd4258c2103ede3258c2103edc3258c21014ff7158c2102cfe7158c21014fd7158c2102cfc7158c2102ede3158c2102edc3158c2103ef62158c2103ef52158c21004ff7058c2100cfe7058c21004fd7058c2100cfc7058c21046df3058c21006de3058c21006dd3058c21046dc3058c21006f71058c21006f51058c21006df7558c21006de7558c21006dd7558c21006dc7558c21006df7458c21006de7458c21006dd7458c21006dc7458c21006df5458c21006de5458c21006dd5458c21006dc5458c2103edf7258c2103ede7258c2103edd7258c2103edc7258c2103edf5258c2103e5f5258c2103ede5258c2103edd5258c2103e5d5258c2103edc5258c2103edf4258c2103e9f4258c2103ede4258c2103edd4258c2103e9d4258c2103edc4258c21046df7158c2102ede7158c2102edc7158c21006df5158c2102ede5158c2102edc5158c21006df4158c2102ede4158c2102edc4158c2103edf2158c2102ede2158c2103ed62158c2103edd2158c2103ed
  | 2 => 0x3df6724c52103df4724c521007e4724c52100777524c52100775524c521007b7424c521007b5424c52106fd7324c521007d5324c521255f7704c521255f5704c52124ef7604c52124ef5604c52106fd7304c52124fd5304c521006df6388521086dc63885210076f52885210076d5288521007af4288521007ad428852103df6718852103ef7618852103dee768852102eee768852100cee7688521007cf6388521007cc638852102dee718852102eef618852103fe7618852102fe63188521007e53188521247cf3088521247cd308852102fe71088521247e5108852102cff755942102e7f7559421004ff745942101cfe745942101cfc74594210567f54594210067e54594210567c5459421004ff7359421014fe7359421014fc73594210567f53594210067e53594210567c535942103cff725942103cfe725942103cfd725942103cfc725942103e7e525942103e7c525942103ebf425942103ebd4259421024ff715942102cfe7159421024fd715942102cfc715942102e7e515942102e7c5159421004ff705942100cfe7059421004fd705942100cfc70594210567f50594210067e50594210067d50594210567c5059421006df3059421006dd3059421006f71059421006f510594210067f74594210067e74594210067d74594210067c74594210067f73594210067e73594210067d73594210067c73594210067f43594210067e43594210067c435942103e7f725942103c7f725942103e7e725942103e7d725942103c7d725942103e7c725942103e7f425942103e3f425942103e7e425942103e7d425942103e3d425942103e7c425942103e7f325942103e7e325942103e7d325942103e7c32594210567f715942102e7e715942102e7c71594210067f415942102e7e415942102e7c41594210067f315942102e7e315942102e7c315942103e7f215942102e7e215942103e7d215942102e7c21594210067f70594210067e70594210067d70594210067c70594210067f40594210067e40594210067d40594210067c40594210067f30594210065f30594210067e30594210067d30594210065d30594210067c305942103e7f205942103e7e205942103e7d205942103e7c205942102e7f10594210067710594210067e10594210067d105942100675105942102e7c1059421004ff7559021024fe7559021024fc755902102cff745902102ebf7459021006bf545902104ebe545902104ebc5459021004ff7359021014fe7359021014fc735902104ebf4359021006be435902104ebc435902103cff725902103cfe725902103cfd725902103cfc725902103e7f525902103e7d525902103ebe425902103ebc425902101cff715902102cfe715902101cfd715902102cfc715902102ebe415902102ebc4159021004ff705902100cfe705
  | 3 => 0xf30549212875d305492103f6f20549212876d205492128777105492128775105492101ebf76d0921076be76d0921076bd76d092101ebc76d0921006bf65d09211bebe65d0921006bd65d09211bebc65d0921006bf63d09210079f63d09210069f63d09211b6be63d0921006bd63d09211b6bc63d09210079c63d09211b69c63d092103dbd72d092103ebf62d092103f3f52d092103f3d52d0921077b671d0921077b571d092103ebf61d092103fb721d092103fac21d092103fb421d092127ebf60d09211aebe60d092127ebd60d09211aebc60d092127f9f30d092127f9d30d092127fb710d092127fb510d092101cfc7650921006bf645092101ebc6450921006df6350921186dc63509210076d5250921005f77150921005f4715092103fe4215092101ebf7650921006be7650921006bd765092101ebc7650921006bf655092118ebe6550921006bd655092118ebc6550921006bf63509210079f63509210069f6350921186be6350921006bd6350921186bc63509210079c63509211869c635092103dbf7250921077af725092103ebf625092103f3f525092103fae525092103f3d5250921007ad52509210072d525092103fae3250921007b77150921007b4715092103ebf615092103fb7215092103fac215092103fb4215092103fa42150921276bf605092117ebe6050921276bd605092117ebc60509212779f30509212779d305092103faf2050921277ad2050921277b71050921277b51050921014fc764c921006df634c921016dc634c9210076d524c921007ad424c921005f7714c921005f4714c9210b4fe76945210267e65945210067d6594521006df639452113edc6394521024ff765452107cfd765452103cfc76545210067f65545210267c6554521006df6354521126dc6354521005ef725452103dec72545210acfe769052101ebe6490521006bd6490521006df639052110edc639052101cff7650521074fd765052103cfc7650521006bf645052101ebc6450521006df63505210f6dc6350521005ef725052103dec72505210a4fe768c521006df638c521016dc638c521005f6768c5210a6f6768c52106df5738c521007d7638c521016f6638c521016f4638c52106fd4638c521016d4638c52103df6728c52103df4728c52102ef7628c52100777528c52100775528c521007b7428c521007b5428c52126fd6328c52126fd4328c521265f7708c521265f5708c52125ef7608c52125ef5608c52106fd7308c52125fd5308c521014ff764c52106cfd764c52103cfc764c521006df634c521016dc634c521005ef724c52103dec724c52106fd4314c52103df4764c521016f4764c52103cf4764c52106df7734c521007d7734c521007d7634c521016f6634c521016f4634c52106fd4634c521016d4634c521007e7724c521
  | 4 => 0x8d21006df52d8d2126ede52d8d2126edc52d8d21006df42d8d2126ede42d8d2126edc42d8d2126edf71d8d2106ede71d8d21006dd71d8d21006df51d8d21006dc51d8d21006df41d8d21006dc41d8d2126edf21d8d2126edc21d8d21006df70d8d21004df70d8d21006de70d8d21006dd70d8d21004dd70d8d21006dc70d8d21006df50d8d21006de50d8d21006dd50d8d21006dc50d8d21006df40d8d21006de40d8d21006dd40d8d21006dc40d8d2126edf20d8d21006de20d8d21006dd20d8d2126edc20d8d21006df10d8d21006d710d8d21006de10d8d21006dd10d8d21006d510d8d21006dc10d8d2106edc6358d21004ff7558d21024fe7558d21024fc7558d21004ff7458d2101cfe7458d2101cfc7458d2106cff7358d21006df7358d21084ff7258d21006ef7258d210a4ff7158d21006f77158d21004ff7058d2100cfe7058d21004fd7058d2100cfc7058d2106edf3058d21006dd3058d21006f71058d21006f51058d21005de7618d2106ede7618d21004de7618d21006df6518d21006de6518d21006dd6518d21006dc6518d21006df6418d21006de6418d21006dd6418d21006dc6418d2106fd57118d21296df6118d21297d72118d21297d42118d2106ddf7018d2106fda7018d21005dd7018d2106fd97018d21005d97018d21006df6018d21006de6018d21006dd6018d21006dc6018d21007d71018d21007d51018d21004ff7654d21004fe7654d21004fd7654d21004fc7654d21006df6354d21016dc6354d21004ff7650d21004fe7650d21004fd7650d21004fc7650d21006df6350d21016dc6350d210267f76d492107e7e76d492107e7d76d49210267c76d49210067f64d49212067e64d49210067d64d49212067c64d49210067f63d49210075f63d49210065f63d49211fe7e63d49210067d63d49211fe7c63d49210075c63d49211fe5c63d492103d7d72d492103e7f62d492107f7671d492107f7571d492103e7f61d492103f7721d492103f6c21d492103f7421d492128e7f60d49211f67e60d492128e7d60d49211f67c60d492128f5f30d492128f5d30d492128f7710d492128f7510d4921024fc76549210067f65549210267c6554921006df63549211cedc6354921005f77154921005f4715492103fe421549210267f76549210067e76549210067d76549210267c76549210067f64549211d67e64549210067d64549211d67c64549210067f63549210075f63549210065f63549211ce7e63549210067d63549211ce7c63549210075c63549211ce5c635492103d7f725492107f6f725492103e7f625492103f6e425492103f6e325492100777715492100774715492103e7f615492103f77215492103f6c215492103f74215492103f6421549212867f60549211c67e60549212867d60549211c67c60549212875
  | 5 => 0xcfe70d9521004fd70d952100cfc70d95210067e50d952107e7c50d9521006df30d9521006dd30d9521006f710d9521006f510d952107e7c6559521005df735952106ddc735952107cff75595210067f7559521004ff745952101cfe745952101cfc7459521004ff7359521006df7359521004df7359521014fe7359521014fc7359521006dc7359521014dc7359521094ff7259521006ef72595210b4ff7159521006f7715952107e7c5159521004ff705952100cfe7059521004fd705952100cfc7059521006df3059521006dd3059521006f71059521006f5105952101cfe76d9121076be64d9121024fe75d9121004fd75d9121024fc75d9121076be54d9121014fe73d9121004fd73d9121014fc73d912103cfe72d9121074fd72d912103cfc72d9121076bf42d912102cfe71d912103cfd71d912102cfc71d9121076bf41d9121004ff70d912100cfe70d9121004fd70d912100cfc70d9121006be40d9121076bc40d9121006df30d9121006dd30d9121006f710d9121006f510d9121076bc6459121005df735912106ddc7359121004ff7559121024fe7559121024fc7559121074ff7459121006bf7459121004ff7359121006df7359121004df7359121014fe7359121014fc7359121006dc7359121014dc735912108cff7259121006ef72591210acff7159121006f77159121076bc4159121004ff705912100cfe7059121004fd705912100cfc7059121006df3059121006dd3059121006f71059121006f51059121004ff7655121004fe7655121004fd7655121004fc76551210067f65551210267c6555121006bf645512101ebc64551210773c5455121236dc6355121014fe76d8d2106ede63d8d21024fe75d8d21004fd75d8d21024fc75d8d2101cfe74d8d21004fd74d8d2101cfc74d8d21006df53d8d2106ede53d8d2106edc53d8d21006df43d8d2106ede43d8d2106edc43d8d2103cfe72d8d2106cfd72d8d2103cfc72d8d2106edf32d8d2102cfe71d8d2103cfd71d8d2102cfc71d8d2106edf31d8d21004ff70d8d2100cfe70d8d21004fd70d8d2100cfc70d8d2106edf30d8d21006de30d8d21006dd30d8d2106edc30d8d21006f710d8d21006f510d8d2106dde76d8d21014de76d8d21006df65d8d21006de65d8d21006dd65d8d21006dc65d8d21006df64d8d21006de64d8d21006dd64d8d21006dc64d8d2126fd771d8d2126fd721d8d2126fd421d8d21005df70d8d21005dd70d8d21006df60d8d21006de60d8d21006dd60d8d21006dc60d8d21007d710d8d21007d510d8d21006df75d8d21006de75d8d21006dd75d8d21006dc75d8d21006df74d8d21006de74d8d21006dd74d8d21006dc74d8d21006df54d8d21006de54d8d21006dd54d8d21006dc54d8d21006df72d8d2126ede72d8d21006dd72d8d2126edc72d
  | 6 => 0xc6354a210976f7254a212e76f3254a2103f6c3254a21007777154a21007747154a2103e7e6154a2103f6f2154a2103f772154a2103f742154a212de7f6054a211c67e6054a212de7d6054a211c67c6054a212df5f3054a212df5d3054a2103f6f2054a212df6d2054a212df771054a212df751054a2108ebe76d0a2108ebd76d0a21006bf65d0a211bebe65d0a21006bd65d0a211bebc65d0a21006bf63d0a211b6be63d0a21006bd63d0a211b6bc63d0a2103f3f52d0a2103f3d52d0a2108fb671d0a2108fb571d0a2103ebe61d0a2103faf21d0a2103fb721d0a2103fb421d0a212d6bf60d0a211aebe60d0a212d6bd60d0a211aebc60d0a212d79f30d0a212d79d30d0a212d7b710d0a212d7b510d0a2101cff7650a2102cfc7650a2101ebe6450a21006bd6450a21005f77150a2102df47150a2101ebf7650a2101ebc7650a21006bf6550a2118ebe6550a21006bd6550a2118ebc6550a21006bf6350a21186be6350a21006bd6350a21186bc6350a2108faf7250a2103f3f5250a2103f3d5250a212cfaf3250a2103fac3250a21007b77150a21007b47150a2103ebe6150a2103faf2150a2103fb72150a2103fb42150a212c6bf6050a2117ebe6050a212c6bd6050a2117ebc6050a212c79f3050a212c79d3050a2103faf2050a212c7ad2050a212c7b71050a212c7b51050a21014ff764ca2102cfc764ca21016de634ca21006dd634ca21005f7714ca2102df4714ca21054ff765462102e7f655462102e7c655462104cff765062102ebf645062102ebc645062102df5768c62102ef5768c62103cf5768c621016f6638c62102fd6638c62102fd5638c62102ef4638c62103df6728c62102fe6728c62102fe5728c62102df4728c62100777528c62100775528c621007b7428c621007b5428c62126fd6328c62126fd4328c62102df7708c6212bdf5708c62102ef7608c6212b6f5608c621087d7308c6212b7d5308c621044ff764c62102edf634c62102edc634c62102fd4314c621005f7764c621046f7764c62102fd7734c62102fd7634c621016f6634c621016f4634c62102fd4634c621016d4634c62103df6724c62103df4724c62100777524c62100775524c621007b7424c621007b5424c621087d7324c621007d5324c6212adf7704c6212adf5704c6212a6f7604c6212a6f5604c621087d7304c6212a7d5304c62102ded76c862103eed76c862103f6e75c862103f6d75c862103fae74c862103fad74c862102fe661c862129fcf30c862129fcd30c8621024fe76d952107e7e65d952101cfe74d9521004fd74d952101cfc74d952107e7f54d9521014fe73d9521004fd73d9521014fc73d952103cfe72d952107cfd72d952103cfc72d952107e7f52d952102cfe71d952103cfd71d952102cfc71d952107e7f51d9521004ff70d9521
  | 7 => 0x962102cff70d962100cfe70d9621004fd70d962100cfc70d96210067e50d96210967c50d9621006df30d9621006dd30d962102ef710d9621006f510d9621024ff765962102e7c655962102e7f7559621004ff745962101cfe745962101cfc7459621004ff7359621014fe7359621014fc73596210967f525962102cfc715962102e7e515962102e7c5159621004ff705962100cfe7059621004fd705962100cfc7059621006df3059621006dd3059621006f71059621006f51059621024fe75d9221004fd75d922102cfc75d922108cfd74d922108ebe54d9221014fe73d9221004fd73d922102cfc73d922102eed72d922102ef671d922102ebf41d922102cff70d922100cfe70d9221004fd70d922100cfc70d9221006be40d922108ebc40d9221006df30d9221006dd30d922102ef710d9221006f510d922101cff765922102ebc6459221004ff7559221024fe7559221024fc755922102ebf7459221004ff7359221014fe7359221014fc735922108ebf425922102cfc715922102ebe415922102ebc4159221004ff705922100cfe7059221004fd705922100cfc7059221006df3059221006dd3059221006f71059221006f51059221004ff765522102cfe7655221004fd765522102cfc76552210067f65552210267c6555221006bf645522101ebc645522108f3c5455221024fe75d8e21004fd75d8e2102cfc75d8e2101cfe74d8e21004fd74d8e2102cfc74d8e21084fd73d8e2102eed72d8e2126ede32d8e2126edc32d8e2102ef671d8e2102edf31d8e2102cff70d8e2100cfe70d8e21004fd70d8e2100cfc70d8e21086df30d8e21006dd30d8e2102ef710d8e21006f510d8e21014ff7658e2102edc6358e21004ff7558e21024fe7558e21024fc7558e21004ff7458e2101cfe7458e2101cfc7458e2102edf7358e21086df3258e2102cfc7158e2102ede3158e2102edc3158e21004ff7058e2100cfe7058e21004fd7058e2100cfc7058e21086df3058e21006dd3058e21006f71058e21006f51058e21004ff7654e2102cfe7654e21004fd7654e2102cfc7654e21004ff7650e2102cfe7650e21004fd7650e2102cfc7650e210967e76d4a210967d76d4a210067f64d4a212067e64d4a210067d64d4a212067c64d4a210067f63d4a211fe7e63d4a210067d63d4a211fe7c63d4a210977671d4a210977571d4a2103e7e61d4a2103f6f21d4a2103f7721d4a2103f7421d4a212ee7f60d4a211f67e60d4a212ee7d60d4a211f67c60d4a212ef5f30d4a212ef5d30d4a212ef7710d4a212ef7510d4a21024ff7654a2102cfc7654a210267e6554a210067d6554a21005f77154a2102df47154a210267f7654a210267c7654a210067f6454a211d67e6454a210067d6454a211d67c6454a210067f6354a211ce7e6354a210067d6354a211ce7
  | 8 => 0x6bf7559321006be7559321006bd7559321006bc7559321006bf7359321006be7359321006bd7359321006bc7359321006bf5359321006be5359321006bc535932103ebf725932103ebe725932103ebd725932103ebc725932103ebf525932103e3f525932103ebe525932103ebd525932103e3d525932103ebc525932103ebf325932103ebe325932103ebd325932103ebc3259321006bf7159321006bd71593210aebc7159321006bf5159321006bc5159321006bf3159321006bc315932103ebf215932103ebe215932103ebd215932103ebc2159321006bf7059321006be7059321006bd7059321006bc7059321006bf5059321006be5059321006bd5059321006bc5059321006bf30593210069f3059321006be3059321006bd30593210069d3059321006bc305932103ebf205932103ebe205932103ebd205932103ebc2059321006bf1059321006b71059321006be1059321006bd1059321006b51059321006bc1059321004ff765532103cfe7655321004fd765532103cfc76553210267e65553210067d655532101ebe6455321006bd64553210af3c5455321005f77155321005f47155321004ff7558f21024fe7558f21024fc7558f21004ff7458f2101cfe7458f2101cfc7458f2103edf7358f2103cfc7258f2103e7f5258f2103e7d5258f2103ebf4258f2103ebd4258f2103ede3258f2103edc3258f210a6df3158f2103ef62158f2103ef52158f21004ff7058f2100cfe7058f21004fd7058f2100cfc7058f210a6df3058f21006dd3058f21006f71058f21006f51058f21004ff7654f2103cfe7654f21004fd7654f2103cfc7654f210267e6554f210067d6554f21226be6454f21006bd6454f21005f77154f21005f47154f21004ff7650f2103cfe7650f21004fd7650f2103cfc7650f212167e6550f210067d6550f2101ebe6450f21006bd6450f21005f77150f21005f47150f2107cfd76947210267e65947210067d6594721146be6494721006bd6494721024ff765472103cfc76547210267e65547210067d655472112ebe6454721006bd6454721005ef725472103dec7254721074fd76907211167e65907210067d659072101ebe6490721006bd649072101cff765072103cfc76507210fe7e65507210067d655072101ebe6450721006bd6450721005ef725072103dec725072106cfd768c7210e67e658c7210067d658c7210debe648c721006bd648c72126edf638c721016dc638c721014ff764c72103cfc764c7210ce7e654c7210067d654c7210c6be644c721006bd644c721016de634c721006dd634c721005ef724c72103dec724c7210a7d4314c721094fd75d962101cfe74d9621004fd74d962102cfc74d96210967f54d9621014fe73d9621004fd73d962102cfc73d962102eed72d962102ef671d962102e7f51d
  | 9 => 0x4714c931016df614c931017d7614c93131ddf704c93131ddd704c931316df604c931316dd604c931317d7104c931317d5104c93130cfe76945310cf77519453102fd43194531024ff7654531014fe7654531124fd7654531014fc76545310067f65545310267c6554531005df7354531015dc7354531127d43154531304fe769053102fd4319053101cff7650531014fe76505310f4fd7650531014fc7650531006bf645053101ebc6450531005df7350531015dc73505310f7d43150531005dd728c53126edc628c5310075f528c5310075d528c5310079f428c5310079d428c53102dde718c53102fd6718c531015d6718c53102edf618c531017d7618c53102ddf708c5312fddd708c5312f6df608c5312f6dd608c53102fd7108c5312f7d5108c53103e7f7559721004ff745972101cfe745972101cfc74597210b67f54597210067e54597210b67c5459721004ff7359721014fe7359721014fc73597210b67f53597210067e53597210b67c535972103cfc725972103e7e525972103e7c525972103ebf425972103ebd42597210b67f5159721004ff705972100cfe7059721004fd705972100cfc70597210b67f50597210067e50597210067d50597210b67c5059721006df3059721006dd3059721006f71059721006f510597210067f74597210067e74597210067d74597210067c74597210067f73597210067e73597210067d73597210067c73597210067f43597210067e43597210067c435972103e7f725972103e7e725972103e7d725972103e7c725972103e7f425972103e3f425972103e7e425972103e7d425972103e3d425972103e7c425972103e7f325972103e7e325972103e7d325972103e7c32597210067f71597210067d71597210b67c71597210067f41597210067c41597210067f31597210067c315972103e7f215972103e7e215972103e7d215972103e7c21597210067f70597210067e70597210067d70597210067c70597210067f40597210067e40597210067d40597210067c40597210067f30597210065f30597210067e30597210067d30597210065d30597210067c305972103e7f205972103e7e205972103e7d205972103e7c20597210067f10597210067710597210067e10597210067d10597210067510597210067c1059721004ff7559321024fe7559321024fc755932103ebf7459321006bf54593210aebe54593210aebc5459321004ff7359321014fe7359321014fc73593210aebf4359321006be43593210aebc435932103cfc725932103e7f525932103e7d525932103ebe425932103ebc42593210aebf4159321004ff705932100cfe7059321004fd705932100cfc70593210aebf4059321006be4059321006bd40593210aebc4059321006df3059321006dd3059321006f71059321006f51059321
  | 10 => 0x49311ff7731d49311ff5c31d49311ff7431d49311ff5431d493133e7f60d49311f67e60d493133e7d60d49311f67c60d49311ff5f30d493133f5d30d493133f7710d493133f7510d4931004fe7694931004fd769493103cfc76949311cd7d75949310c5be7494931005bd7494931015de7394931005dd7394931006ef629493103eec6294931005f67194931005f571949311e7d43194931004ff7654931004fe7654931004fc76549310067f65549310267e65549310067d65549310267c6554931006ef625493103eec62549311cfd431549310067f76549310067e76549310067d76549310067c76549310067f64549311d67e64549310067d64549311d67c64549311ce7f63549311fd7f72549310cf6f72549310067f62549310076f62549310066f625493103e7e625493103e7c62549310076c625493103e6c62549311cf5f32549311ce7f61549311cf7731549311cf5c31549311cf7431549311cf5431549313367f60549311c67e60549313367d60549311c67c60549311cf5f30549313375d30549313376f20549313376d205493133777105493133775105493101ebf76d09310c6be76d09310c6bd76d093101ebc76d0931006bf65d09311bebe65d0931006bd65d09311bebc65d09311b6bf63d0931006bf62d093103ebe62d093103ebc62d09310073f52d09310073d52d09311b79f32d09311b6bf61d09311b7b731d09311b79c31d09311b7b431d09311b79431d093132ebf60d09311aebe60d093132ebd60d09311aebc60d09311b79f30d093132f9d30d093132fb710d093132fb510d0931004fe7690931004fd769093103cfc76909310cd7e75909310057d7590931185bd7490931015de7390931005dd7390931006ef629093103eec6290931005f67190931005f5719093119fd43190931004ff7650931004fe7650931004fc7650931006bf645093101ebe6450931006bd645093101ebc6450931006ef625093103eec6250931187d43150931006bf7650931006be7650931006bd7650931006bc7650931006bf655093118ebe6550931006bd655093118ebc6550931186bf63509311b5bf72509310c7af7250931006bf6250931007af6250931006af625093103ebe625093103ebc6250931007ac625093103eac62509310073f52509310073d52509311879f3250931186bf6150931187b731509311879c3150931187b43150931187943150931326bf605093117ebe6050931326bd605093117ebc60509311879f30509313279d3050931327af2050931327ad2050931327b71050931327b5105093103cdc764c931015df724c931017cf724c931007cf624c93103ede624c93103edc624c931007cc624c9310075f524c9310075d524c9310079f424c9310079d424c931007d7714c93102ddc714c931007d4714c931005d
  | 11 => 0x34cff7654631127d73154631344ff7650631024fe76d95310ce7e65d953113fd431d953101cfe74d9531004fd74d953101cfc74d95310ce7f54d953102cff73d9531014fe73d953113cfd73d9531014fc73d953113e7f53d953113e7d53d953103cfe72d9531004fd72d95310ce7f52d9531014fd71d95310ce7f51d9531004ff70d953100cfe70d9531004fd70d953100cfc70d95310067e50d95310ce7c50d953113edf30d9531006dd30d9531006f710d9531006f510d95310ce7c655953134df77159531127d4315953113cff75595310067f7559531004ff745953101cfe745953101cfc7459531124ff7359531006df7359531004ff725953103cfc72595310ce7f525953134cff7159531006f77159531004ff705953100cfe7059531004fd705953100cfc7059531126df3059531006dd3059531006f71059531006f5105953101cfe76d91310c6be64d913110fd431d9131024fe75d9131004fd75d9131024fc75d91310c6be54d913102cff73d9131014fe73d913110cfd73d9131014fc73d913110ebf43d913110ebd43d913103cfe72d9131004fd72d91310c6bf42d9131014fd71d91310c6bf41d9131004ff70d913100cfe70d9131004fd70d913100cfc70d9131006be40d91310c6bc40d913110edf30d9131006dd30d9131006f710d9131006f510d91310c6bc6459131345f771591310f7d43159131004ff7559131024fe7559131024fc755913110cff7459131006bf74591310f4ff7359131006df7359131004ff725913103cfc72591310c6bf4259131344ff7159131006f77159131004ff705913100cfe7059131004fd705913100cfc70591310f6df3059131006dd3059131006f71059131006f51059131004ff7655131004fe7655131004fd7655131004fc76551310067f65551310267c6555131006bf645513101ebc64551310c73c5455131005df7355131015dc7355131005f77155131005f47155131237d43155131087d431d8931024fe75d8931004fd75d8931024fc75d893101cfe74d8931004fd74d893101cfc74d8931086ee32d8931086ed32d893102cfe71d8931004ff70d893100cfe70d8931004fd70d893100cfc70d8931086df30d8931006dd30d8931006ee20d8931006ec20d8931006f710d8931006f510d89310cd7e75989310057d75989310c5be7498931005bd7498931006ef629893106df571989310a7d431989310a5f7715893106fd431589310cd7e75189310057d75189310c5be7418931005bd741893103eee6218931006ed6218931047d431189310bdfa7018931005f970189310267f76d49310ce7e76d49310ce7d76d49310267c76d49310067f64d49312067e64d49310067d64d49312067c64d49311fe7f63d49310067f62d493103e7e62d493103e7c62d49311ff5f32d49311fe7f61d
  | 12 => 0x51058a310267f76d4a310e67e76d4a310e67d76d4a310267c76d4a310067f64d4a312067e64d4a310067d64d4a312067c64d4a311ff5e73d4a310e75d73d4a3103e7e62d4a310067d62d4a3103e7c62d4a3126f5c32d4a311fe7e61d4a311ff5f31d4a311ff7731d4a311ff7431d4a3137e7f60d4a311f67e60d4a3137e7d60d4a311f67c60d4a311ff5f30d4a3137f5d30d4a3137f7710d4a3137f7510d4a3103cff7694a3102cfe7694a31004fd7694a310ddbe7494a31005bd7494a3102df67194a31005f57194a31004ff7654a31004fd7654a3102cfc7654a310067f6554a310267e6554a310067d6554a310267c6554a31005df7354a31015dc7354a310067f7654a310067e7654a310067d7654a310067c7654a310067f6454a311d67e6454a310067d6454a311d67c6454a310075f7354a311cf5c7354a310e76f7254a3103e7e6254a310067d6254a3103e7c6254a3126f5c3254a311ce7e6154a311cf5f3154a311cf773154a311cf743154a313767f6054a311c67e6054a313767d6054a311c67c6054a311cf5f3054a313775d3054a313776f2054a313776d2054a31377771054a31377751054a3101ebf76d0a310debe76d0a310debd76d0a3101ebc76d0a31006bf65d0a311bebe65d0a31006bd65d0a311bebc65d0a311b79e73d0a310df9d73d0a3103ebe62d0a31006bd62d0a3103ebc62d0a310073f52d0a310073d52d0a3126f9c32d0a311b6be61d0a311b79f31d0a311b7b731d0a311b7b431d0a3136ebf60d0a311aebe60d0a3136ebd60d0a311aebc60d0a311b79f30d0a3136f9d30d0a3136fb710d0a3136fb510d0a3103cff7690a3102cfe7690a31004fd7690a310e57e7590a310057d7590a3102df67190a31005f57190a31004ff7650a31004fd7650a3102cfc7650a31006bf6450a3101ebe6450a31006bd6450a3101ebc6450a31005df7350a31015dc7350a31006bf7650a31006be7650a31006bd7650a31006bc7650a31006bf6550a3118ebe6550a31006bd6550a3118ebc6550a310079f7350a311879c7350a310dfaf7250a3103ebe6250a31006bd6250a3103ebc6250a310073f5250a310073d5250a3126f9c3250a31186be6150a311879f3150a31187b73150a31187b43150a31366bf6050a3117ebe6050a31366bd6050a3117ebc6050a311879f3050a313679d3050a31367af2050a31367ad2050a31367b71050a31367b51050a3126f5e758ca3126f5d758ca3126f9e748ca3126f9d748ca31015de728ca31017ce728ca3126fce628ca3126edd628ca31007cd628ca3126f5f528ca3126f5d528ca3126f9f428ca3126f9d428ca3126fd6718ca31005dd718ca3126fd5718ca31016de618ca31017d6618ca3126ddf708ca3135ddd708ca31356df608ca31356dd608ca31357d7108ca31357d5108ca31
  | 13 => 0x9413979d3050941397af2050941397ad2050941397b71050941397b51050941004fe768c941004fd768c94103cfc768c9410fd7e758c9410057d758c94101dbe748c941005bd748c941006df638c941016dc638c941004ff764c941004fe764c941004fc764c94138cfe76945410267e65945410067d65945410ff77519454102fb44194541024ff765454101cfe765454112cfd765454101cfc76545410067f65545410267c6554541005bf745454101dbc745454112fb44154541006bf6590541006bd6590541005bd7290541006bf62905410073f52905410073d529054102dbe719054102fb6719054102ebf619054101fb76190541106be6090541106bc60905413879f30905413879d309054102fb71090541387b51090541124fd75d963101cfe74d9631004fd74d963102cfc74d96310e67f54d963102edd73d963103cfe72d9631004fd72d96310e67f52d963102cfe71d963102ef671d963102cff70d963100cfe70d9631004fd70d963100cfc70d963113edf30d9631006dd30d963102ef710d9631006f510d9631024ff765963102e7c655963102e7f7559631004ff745963101cfe745963101cfc74596311267f53596311267d5359631004ff725963103cfc72596310e67f525963102cfe715963102cfc715963102e7e515963102e7c5159631004ff705963100cfe7059631004fd705963100cfc7059631126df3059631006dd3059631006f71059631006f51059631024fe75d9231004fd75d923102cfc75d92310f4fd74d92310debe54d923102edd73d923103cfe72d9231004fd72d92310debf42d923102cfe71d923102ef671d923102cff70d923100cfe70d9231004fd70d923100cfc70d923110edf30d9231006dd30d923102ef710d9231006f510d923101cff765923102ebc6459231004ff7559231024fe7559231024fc755923102ebf74592310f6bf43592310f6bd4359231004ff725923103cfc72592310debf425923102cfe715923102cfc715923102ebe415923102ebc4159231004ff705923100cfe7059231004fd705923100cfc70592310f6df3059231006dd3059231006f71059231006f51059231004ff765523102cfe7655231004fd765523102cfc76552310067f65552310267c6555231006bf645523101ebc64552310df3c5455231005f7715523102df471552310e57e7598a310057d7598a310ddbe7498a31005bd7498a3102eef6298a3102eec6298a3102eec6258a31004ff7558a31024fe7558a31024fc7558a31004ff7458a3101cfe7458a3101cfc7458a3106eee3258a3106eed3258a3126edc3258a3103cff7158a3102cfc7158a3106edf3158a3102eee2158a3102eec2158a31004ff7058a3100cfe7058a31004fd7058a3100cfc7058a3106edf3058a31006dd3058a31006f71058a31006f
  | 14 => 0x67f755954112cff7459541006bf7459541004ff7359541014fe7359541014fc7359541004ff725954103cfc72595410fe7f525954112ebf42595413b4ff7159541006f771595410fe7c515954112ebc4159541004ff705954100cfe7059541004fd705954100cfc7059541006df3059541006dd3059541006f71059541006f51059541014fe76d8d410f6de63d8d41024fe75d8d41004fd75d8d41024fc75d8d41014fc74d8d410f6de43d8d410dedd43d8d4103cfe72d8d41004fd72d8d410debf42d8d410f6dc32d8d4101cfd71d8d410f6df31d8d41004ff70d8d4100cfe70d8d41004fd70d8d4100cfc70d8d410f6df30d8d41006dd30d8d41006f710d8d41006f510d8d410f6dc6358d413adf77158d41004ff7654d41004fe7654d41004fc7654d41024fe75d8941004fd75d8941024fc75d8941006bf74d8941014fe73d8941004fd73d8941014fc73d894108eee42d894108eed42d894108ebc41d8941004ff70d894100cfe70d8941004fd70d894100cfc70d8941006df30d8941006dd30d8941006f710d8941006f510d89410fd7e75989410057d7598941006ef6298941075f57198941005df73589410f5dc73589410adf771589410fd7e75189410057d751894103eee6218941006ed62189410267f76d49410fe7e76d49410fe7d76d49410267c76d49412067f64d49410067f63d49411fe7e63d49411fe7c63d49410067f62d494103e7e62d494103e7c62d49412073f42d49412067f61d49412077741d49412073c41d49412077441d49413a67f60d49411f67e60d49413a67d60d49411f67c60d49413a75f30d49413a75d30d49413a77710d49413a77510d4941004fe7694941004fd769494103cfc76949411d57d759494101dbe7494941005bd7494941004ff7654941004fe7654941004fc76549410067f65549410267e65549410067d65549410267c65549410067f76549410067e76549410067d76549410067c76549411d67f64549410067f63549411ce7e63549411ce7c63549412057f72549410ff6f72549410067f625494103e7e625494103e7c62549411d73f42549411d67f61549411d77741549411d73c41549411d774415494139e7f60549411c67e605494139e7d60549411c67c605494139f5f305494139f5d305494139f6f205494139f6d205494139f77105494139f75105494103cbc7650941006bf655094118ebe6550941006bd655094118ebc6550941006bf6350941186be6350941186bc635094101dbf725094101faf7250941006bf6250941007af6250941006af625094103ebe625094103ebc6250941007ac62509410073f52509410073d5250941007b7715094102dbc7150941007b4715094101ebf615094101fb76150941396bf605094117ebe6050941396bd605094117ebc60509413979f305
  | 15 => 0xe4258a41076ed4258a4102cfc7158a41076bf4158a4102eee2158a4102eec2158a41004ff7058a4100cfe7058a41004fd7058a4100cfc7058a41006be4058a41076bc4058a41006df3058a41006dd3058a41006f71058a41006f51058a410267f76d4a411167e76d4a411167d76d4a410267c76d4a412073e74d4a411173d74d4a411fe7e63d4a410067d63d4a411fe7c63d4a4103e7e62d4a410067d62d4a4103e7c62d4a412073f42d4a412067e61d4a412073f41d4a412077741d4a412077441d4a413ce7f60d4a411f67e60d4a413ce7d60d4a411f67c60d4a413cf3e40d4a412073c40d4a413cf5f30d4a413cf5d30d4a413cf7710d4a413cf7510d4a4103cff7694a4102cfe7694a41004fd7694a4101dbe7494a41005bd7494a41004ff7654a41004fd7654a4102cfc7654a410067f6554a410267e6554a410067d6554a410267c6554a4101dbe7454a411d73e5454a410073d5454a410067f7654a410067e7654a410067d7654a410067c7654a411d73e7454a410073d7454a411ce7e6354a410067d6354a411ce7c6354a411176f7254a4103e7e6254a410067d6254a4103e7c6254a411d73f4254a411d67e6154a411d73f4154a411d7774154a411d7744154a413c67f6054a411c67e6054a413c67d6054a411c67c6054a413c73e4054a411d73c4054a413c75f3054a413c75d3054a413c76f2054a413c76d2054a413c7771054a413c7751054a4103cbf7650a41005bf7550a41005bd7550a41006bf6550a4118ebe6550a41006bd6550a4118ebc6550a41186be6350a41006bd6350a41186bc6350a4101dbf7250a4101faf7250a4103ebe6250a41007ae6250a41006bd6250a41007ad6250a41006ad6250a4103ebc6250a410073f5250a410073d5250a41005bf7150a41007b77150a41007b47150a4101ebe6150a4101fb66150a41105be7050a41105bc7050a413bebf6050a4117ebe6050a413bebd6050a4117ebc6050a413bf9f3050a413bf9d3050a413bfaf2050a413bfad2050a413bfb71050a413bfb51050a4103cff768ca4102cfe768ca41004fd768ca411157e758ca410057d758ca4101dbe748ca41005bd748ca41004ff764ca41004fd764ca4102cfc764ca41016de634ca41006dd634ca413b4ff765464101dbe745464112fb74154641024fe76d95410fe7e65d954102cff74d954101cfe74d9541144fd74d954101cfc74d95411467f54d95411467d54d9541014fe73d9541004fd73d9541014fc73d954103cfe72d9541004fd72d95410fe7f52d9541146bf42d954101cfd71d95410fe7f51d9541146bc41d9541004ff70d954100cfe70d9541004fd70d954100cfc70d95410067e50d95410fe7c50d9541006df30d9541006dd30d9541006f710d9541006f510d95410fe7c65595413b5f77159541144ff7559541
  | 16 => 0x95103ebc625095118f3f52509510073d525095118ebf615095118fb7515095118f3c515095118fb451509513eebf605095117ebe60509513eebd605095117ebc60509513ef9f30509513ef9d30509513efaf20509513efad20509513efb710509513efb51050951004fe768c951004fd768c95103cfc768c9510257e758c9510057d758c95112dbe748c951005bd748c951006df638c951016dc638c951004ff764c951004fe764c951004fc764c9510067f64945510057d72945510067f62945510073f42945510073d429455102d7e719455102f76719455102e7f61945510277761945511367e60945511367c60945513e75f30945513e75d309455102f7710945513e775109455112cfd75d964102ebd74d9641014fe73d964102ede73d9641014de73d9641004fd73d964102edd73d9641004dd73d964102cfc73d964103cfe72d9641004fd72d96411167f52d9641146bf42d964102cfe71d964102ef671d964102cff70d964100cfe70d964102efa70d964100cfa70d9641004fd70d964102ef970d9641004f970d964100cfc70d9641006df30d9641006dd30d964102ef710d9641006f510d9641024ff765964102e7c655964102e7f755964112e7f545964112e7d5459641004ff7359641014fe7359641014fc7359641004ff725964103cfc72596411167f525964112ebf425964102cfe715964102cfc715964102e7e515964102e7c5159641004ff705964100cfe7059641004fd705964100cfc7059641006df3059641006dd3059641006f71059641006f51059641115bf7655241026bf7655241024bf765524101dbf755524101f3f7555241026be65552411173e65552410263e65552410073d6555241026bc65552411173f5355241005bf72552411173f5255241005bf7155241007b77155241007b4715524101ebe615524101fb661552413df3e51552413df3c5155241105be7055241105bc70552413d6bf60552413d6bd60552411173f50552413d73d50552413d79f30552413d79d30552413d7b710552413d7b51055241014ff7658e4102edc6358e41004ff7558e41024fe7558e41024fc7558e410c6be5458e41006bd5458e41006df5358e4110edc5358e4110ede4358e410c6dd4358e41004ff7258e4103cfc7258e410c6bf4258e4110edf3258e4102cfe7158e4102cfc7158e4102ede3158e4102edc3158e41004ff7058e4100cfe7058e41004fd7058e4100cfc7058e4110edf3058e41006dd3058e41006f71058e41006f51058e41004ff7654e41004fd7654e4102cfc7654e410073d5454e411157e7598a410057d7598a4102eef6298a4102eec6298a4102eec6258a41004ff7558a41024fe7558a41024fc7558a41006bd7458a41076be5458a41006bd5458a41004ff7358a41014fe7358a41014fc7358a41076e
  | 17 => 0x257e758ca510057d758ca51145be748ca51005bd748ca51004ff764ca51004fd764ca5102cfc764ca51016de634ca51006dd634ca5101cfe76d915112ebe64d915101cfc75d915112ebe54d9151116bd54d9151014fe73d9151004fd73d9151014fc73d915103cfe72d9151004fd72d91511167f52d915112ebf42d9151024fd71d91511167c51d915112ebf41d9151004ff70d915100cfe70d9151004fd70d915100cfc70d9151006be40d915112ebc40d9151006df30d9151006dd30d9151006f710d9151006f510d915112ebc645915140df77159151014fe76d8d51126de63d8d51014fc75d8d5101cfe74d8d51004fd74d8d5101cfc74d8d51126de53d8d510e6dd53d8d5103cfe72d8d51004fd72d8d510e67f52d8d51126dc32d8d51024fd71d8d51126df31d8d51004ff70d8d5100cfe70d8d51004fd70d8d5100cfc70d8d51126df30d8d51006dd30d8d51006f710d8d51006f510d8d51126dc6358d51405f77158d51004ff7650d51004fe7650d51004fc7650d510067f75d895101cfe74d8951004fd74d895101cfc74d8951014fe73d8951004fd73d8951014fc73d8951096ee52d8951096ed52d89510967c51d8951004ff70d895100cfe70d8951004fd70d895100cfc70d8951006df30d8951006dd30d8951006f710d8951006f510d895112dbe7498951005bd7498951006ef629895107df57198951005df7358951125dc73589510b5f7715895112dbe7418951005bd741895103eee6218951006ed621895103c7c76549510067f64549511d67e64549511d67c64549510067f63549511ce7e63549511ce7c63549510257f72549510276f72549510067f62549510076f62549510066f625495103e7e625495103e7c62549510076c625495100777715495102d7c71549510077471549510267f61549510277761549513fe7f60549511c67e60549513fe7d60549511c67c60549513ff5f30549513ff5d30549513ff6f20549513ff6d20549513ff7710549513ff75105495101ebf76d095112ebe76d095112ebd76d095101ebc76d0951146bf65d0951006bf63d09511b6be63d09511b6bc63d0951006bf62d095103ebe62d095103ebc62d09511bf3f52d09510073d52d09513b6bf61d09511bfb751d09511bf3c51d09511bfb451d09513f6bf60d09511aebe60d09513f6bd60d09511aebc60d09513f79f30d09513f79d30d09513f7b710d09513f7b510d0951004fe7690951004fd769095103cfc76909510257e75909510057d759095118dbd7490951004ff7650951004fe7650951004fc7650951006bf645095101ebe645095101ebc6450951006bf7650951006be7650951006bd7650951006bc765095118ebf6550951006bf6350951186be6350951186bc635095112dbf725095112faf7250951006bf625095103ebe625
  | 18 => 0xf7658e5102edc6358e51004ff7458e5101cfe7458e5101cfc7458e510ce7f5458e510067d5458e5113ede5358e510cedd5358e51006df4358e5113edc4358e51004ff7258e5103cfc7258e510ce7f5258e5113edf3258e5102cfe7158e5102cfc7158e5102ede3158e5102edc3158e51004ff7058e5100cfe7058e51004fd7058e5100cfc7058e5113edf3058e51006dd3058e51006f71058e51006f51058e51004ff7650e51004fd7650e5102cfc7650e510073d5450e51145be7498a51005bd7498a5102eef6298a5102eec6298a5102eec6258a510067d7558a51004ff7458a5101cfe7458a5101cfc7458a5107e7f5458a510067d5458a51004ff7358a51014fe7358a51014fc7358a5107eee5258a5107eed5258a5102cfc7158a5107e7f5158a5102eee2158a5102eec2158a51004ff7058a5100cfe7058a51004fd7058a5100cfc7058a510067e5058a5107e7c5058a51006df3058a51006dd3058a51006f71058a51006f51058a5103c7f7654a510057f7454a511d67e6454a510067d6454a511d67c6454a511ce7e6354a510067d6354a511ce7c6354a510257f7254a510276f7254a5103e7e6254a510076e6254a510067d6254a510076d6254a510066d6254a5103e7c6254a510057f7154a51007777154a51007747154a510267e6154a51027766154a511357e7054a511357c7054a514267f6054a511c67e6054a514267d6054a511c67c6054a514275f3054a514275d3054a514276f2054a514276d2054a51427771054a51427751054a5101ebf76d0a51146be76d0a51146bd76d0a5101ebc76d0a511473e75d0a511473d75d0a511b6be63d0a51006bd63d0a511b6bc63d0a5103ebe62d0a51006bd62d0a5103ebc62d0a511bf3f52d0a510073d52d0a5138ebe61d0a511bf3f51d0a511bfb751d0a511bfb451d0a5141ebf60d0a511aebe60d0a5141ebd60d0a511aebc60d0a5141f3e50d0a511bf3c50d0a5141f9f30d0a5141f9d30d0a5141fb710d0a5141fb510d0a5103cff7690a5102cfe7690a51004fd7690a510257e7590a510057d7590a51004ff7650a51004fd7650a5102cfc7650a510257e7550a510057d7550a5101ebe6450a51006bd6450a5101ebc6450a5118f3f5450a510073d5450a51006bf7650a51006be7650a51006bd7650a51006bc7650a5118f3e7550a510073d7550a51186be6350a51006bd6350a51186bc6350a51147af7250a5103ebe6250a51006bd6250a5103ebc6250a5118f3f5250a510073d5250a5118ebe6150a5118f3f5150a5118fb75150a5118fb45150a51416bf6050a5117ebe6050a51416bd6050a5117ebc6050a514173e5050a5118f3c5050a514179f3050a514179d3050a51417af2050a51417ad2050a51417b71050a51417b51050a5103cff768ca5102cfe768ca51004fd768ca51
  | 19 => 0x93203ebf62d093203f3f52d093203f3d52d09321b7af32d093203f9e32d093203f9c32d093203fac32d09321b79f31d093243ebf60d09321aebe60d093243ebd60d09321aebc60d09321b79f30d093243f9d30d093243fb710d093243fb510d093201cff7650932014fe7650932184fd7650932014fc7650932006bf645093201ebc6450932005df7350932015dc735093203fcc325093201ebf7650932186be7650932186bd765093201ebc7650932006bf655093218ebe6550932006bd655093218ebc65509320079f73509321879c735093203ebf635093203dbf7250932157af725093203ebf625093203f3f525093203f3d5250932187af325093203f9e325093203f9c325093203fac325093203f8c32509321879f315093203faf2150932436bf605093217ebe6050932436bd605093217ebc60509321879f30509324379d305093203faf2050932437ad2050932437b71050932437b51050932024fe75d8532004fd75d8532024fc75d853201cfe74d8532004fd74d853201cfc74d853203cfd73d85320067f52d85320067d52d8532006bf42d8532006bd42d8532006f751d8532006f451d8532006f741d8532006f441d85320a6f631d8532004ff70d853200cfe70d8532004fd70d853200cfc70d85320a6df30d8532006dd30d8532006f710d8532006f510d8532006f76198532006f5611853214dfa7018532005f97018532024fe7518532004fd751853202cfc751853201cfe7418532004fd741853202cfc741853203cfd73185320067f52185320067d5218532006bf4218532006bd4218532296de3218532296dc3218532006f7511853202ef45118532006f7411853202ef4411853202edf311853202ef63118532046f5311853202cff701853200cfe701853202efa701853200cfa7018532004fd701853202ef97018532004f9701853200cfc7018532046df3018532006dd301853202ef71018532006f5101853201cff765925102ebc6459251146be54592510febd5459251004ff7359251014fe7359251014fc7359251004ff725925103cfc72592510fe7f5259251146bf425925102cfe715925102cfc715925102ebe415925102ebc4159251004ff705925100cfe7059251004fd705925100cfc7059251006df3059251006dd3059251006f71059251006f510592511457f765525101e7f765525101c7f76552510257f74552510273f745525101e7e64552511473e645525101e3e64552510073d645525101e7c64552511473f43552510057f72552511473f42552510057f71552510077771552510077471552510267e61552510277661552513df3c41552511357e70552511357c705525142e7f605525142e7d60552511473f405525142f3d405525142f5f305525142f5d305525142f77105525142f751055251014f
  | 20 => 0x6dd30d9532006f710d9532006f510d953215e7c65595321fdef7259532005f77159532005f471595321e4ff75595320067f7559532004ff745953201cfe745953201cfc745953215e7f54595321ccff7359532006df73595321ce7e53595321ce7c53595321fcff7259532006ef7259532004ff7159532006f77159532004f7715953202cfc7159532006f47159532004f47159532004ff705953200cfe7059532004fd705953200cfc70595321cedf3059532006dd3059532006f71059532006f5105953201cfe76d9132156be64d9132024fe75d9132004fd75d9132024fc75d913203cff73d913203cfd73d913219ebf43d913219ebd43d9132014fd72d9132156bf42d913202cfe71d9132004fd71d9132004ff70d913200cfe70d9132004fd70d913200cfc70d913219edf30d9132006dd30d9132006f710d9132006f510d9132156bc64591321b5ef7259132005f77159132005f47159132004ff7559132024fe7559132024fc755913219cff7459132006bf7459132156be5459132184ff7359132006df7359132186be4359132186bc43591321b4ff7259132006ef7259132004ff7159132006f77159132004f7715913202cfc7159132006f47159132004f47159132004ff705913200cfe7059132004fd705913200cfc7059132186df3059132006dd3059132006f71059132006f51059132004ff7655132004fe7655132004fd7655132004fc76551320267e65551320067d655513201ebe6455132006bd64551321573c54551320267f76d49321fe7e76d493215e7d76d49320267c76d49320067f64d49322067e64d49320067d64d49322067c64d49321ff5e73d493215f5d73d493203e7f63d493203d7d72d493203e7f62d49321ff6f32d493203f5e32d493203f5c32d493203f6c32d49321ff5f31d493244e7f60d49321f67e60d493244e7d60d49321f67c60d49321ff5f30d493244f5d30d493244f7710d493244f7510d4932024ff7654932014fe76549321ccfd7654932014fc76549320067f65549320267c6554932005df7354932015dc735493203fcc32549320267f76549321ce7e76549321ce7d76549320267c76549320067f64549321d67e64549320067d64549321d67c64549320075f73549321cf5c735493203e7f635493203d7f725493215f6f725493203e7f62549321cf6f325493203f5e325493203f5c325493203f6c325493203f4c32549321cf5f315493203f6f21549324467f60549321c67e60549324467d60549321c67c60549321cf5f30549324475d305493203f6f20549324476d205493244777105493244775105493201ebf76d09321b6be76d0932156bd76d093201ebc76d0932006bf65d09321bebe65d0932006bd65d09321bebc65d09321b79e73d09321579d73d093203ebf63d093203dbd72d
  | 21 => 0xf545923216ebe545923216ebc5459232186bf4359232186bd435923203cfe725923203cfc725923203e7f525923203e7d525923203ebe425923203ebc4259232004ff715923202cfc715923216ebf415923216ebc4159232004ff705923200cfe7059232004fd705923200cfc705923216ebf4059232006be4059232006bd405923216ebc4059232186df3059232006dd3059232006f71059232006f51059232006bf7559232006be7559232006bd7559232006bc7559232186bf7359232186be7359232186bd7359232186bc7359232186bf5359232186be5359232186bd5359232186bc535923203ebf725923203ebe725923203ebd725923203ebc725923203ebf525923203e3f525923203ebe525923203ebd525923203e3d525923203ebc525923203ebf325923203ebe325923203ebd325923203ebc3259232006bf7159232006be7159232006bd7159232006bc7159232006bf5159232006bc5159232186bf3159232186be3159232186bd3159232186bc315923203ebf215923203ebe215923203ebd215923203ebc2159232006bf7059232006be7059232006bd7059232006bc7059232006bf5059232006be5059232006bd5059232006bc5059232186bf30592321869f3059232186be3059232186bd30592320069d3059232186bc305923203ebf205923203ebe205923203ebd205923203ebc2059232006bf1059232006b71059232006be1059232006bd1059232006b51059232006bc1059232004ff765523203cfe7655232004fd765523203cfc76552320267e65552320067d655523201ebe6455232006bd645523216f3c5455232005df7355232015dc7355232024fe7598632004fd759863202cfc759863201cfe7498632004fd749863202cfc749863203cfe729863202cfc729863203e7f529863203e7d529863203ebf429863203ebd429863202ef6719863202ef63198632086f5319863203ef7219863202ef4219863202cff709863200cfe7098632004fd709863200cfc7098632086df3098632006dd309863202ef71098632006f51098632004ff7558632024fe7558632024fc7558632004ff745863201cfe745863201cfc745863203cfc725863203e7f525863203e7d525863203ebf425863203ebd425863203edf325863203edd325863203ef7715863206ef6315863206edc315863203ef7215863203ef42158632004ff705863200cfe7058632004fd705863200cfc705863206edf3058632006dd3058632006f71058632006f51058632024fe76d953215e7e65d953201cfe74d9532004fd74d953201cfc74d953203cff73d953203cfd73d95321e67f53d95321e67d53d9532014fd72d953215e7f52d953202cfe71d9532004fd71d9532004ff70d953200cfe70d9532004fd70d953200cfc70d95321e6df30d9532
  | 22 => 0x8542005bf709854217dbe7098542005bd709854217dbc7098542006be6098542006bc60985420079f30985420079d3098542007af2098542007ad2098542007b71098542007b51098542005bf755854218dbe755854218dbc7558542005bf73585420079f73585420059f7358542185be7358542185bc73585420079c73585421859c7358542007af7258542077af62585420073f52585420073d5258542007b76158542006be6158542005bf705854217dbe7058542005bd705854217dbc70585420079f30585420079d3058542007af2058542007ad2058542007b71058542007b51058542005be761854218dbe7518542005bd751854218dbc7518542006bf6518542006bd6518542185be7318542005bd7318542185bc731854204ebf621854204faf62185420073f52185420073d5218542006bf6118542007b66118542006bd6118542007b56118542007b75118542007b45118542007b73118542007b43118542005bf701854217dbe7018542005bd701854217dbc7018542006be6018542006bc60185420079f30185420079d3018542007af2018542007ad2018542007b71018542007b5101854203e7f7559632004ff745963201cfe745963201cfc74596321767f54596320067e54596321767c54596321ce7f53596321ce7d535963203cfe725963203cfc725963203e7e525963203e7c525963203ebf425963203ebd4259632004ff715963202cfc71596321767f51596321767c5159632004ff705963200cfe7059632004fd705963200cfc70596321767f50596320067e50596320067d50596321767c50596321cedf3059632006dd3059632006f71059632006f510596320067f74596320067e74596320067d74596320067c74596321ce7f73596321ce7e73596321ce7d73596321ce7c73596321ce7f43596321ce7e43596321ce7d43596321ce7c435963203e7f725963203e7e725963203e7d725963203e7c725963203e7f425963203e3f425963203e7e425963203e7d425963203e3d425963203e7c425963203e7f325963203e7e325963203e7d325963203e7c32596320067f71596320067e71596320067d71596320067c71596320067f41596320067c41596321ce7f31596321ce7e31596321ce7d31596321ce7c315963203e7f215963203e7e215963203e7d215963203e7c21596320067f70596320067e70596320067d70596320067c70596320067f40596320067e40596320067d40596320067c40596321ce7f30596321ce5f30596321ce7e30596321ce7d30596320065d30596321ce7c305963203e7f205963203e7e205963203e7d205963203e7c20596320067f10596320067710596320067e10596320067d10596320067510596320067c1059632004ff7559232024fe7559232024fc755923203ebf7459232006b
  | 23 => 0x3f3f21d494203f3c21d494218f3f70d494218f3e70d494218f3d70d494218f3c70d494246f3f60d494246f3e60d494246f3d60d494246f3c60d494246f3f30d494246f1f30d494246f3e30d494246f3d30d494246f1d30d494246f3c30d494203f3f20d494203f2f20d494203f3e20d494203f3d20d494246f2d20d494203f3c20d494246f3f10d494246f3710d494246f3e10d494246f3d10d494246f3510d494246f3c10d494218dbf765494201dbe765494218dbd765494201dbc765494203dbf75549420073f655494218f3c6554942005bf7354942185be7354942185bc735494218f3f53549424673e53549420073d535494218f3c535494203dbf725494203ebf62549421d7af625494218faf525494203f3e525494203f3c525494203fac5254942467af325494203fac3254942005bf7154942005bc715494218f3f515494218f3c515494203faf215494245dbf705494217dbe705494245dbd705494217dbc705494218f3f50549424573e50549424573d505494218f3c50549424579f30549424579d305494203faf2054942457ad2054942457b71054942457b5105494218f3f76549421d73e76549420073d76549420073c76549420073f73549424673e73549420073d73549424673c73549420073f63549424673e63549420073d63549424673c635494203f3f725494203d3f725494218f2f725494203f3f625494203e3f62549421d72f625494203f3f32549424672f325494203f3e325494203f3c325494203f2c32549420073f71549420073e71549420073d71549420073c71549424673f31549424673c315494203f3f215494203f2f215494203f3c215494245f3f70549424573e705494245f3d70549424573c70549424573f60549424573e60549424573d60549424573c60549424573f30549424571f30549424573e30549424573d30549424571d30549424573c305494203f3f205494203f2f205494203f3e205494203f3d20549424572d205494203f3c20549424573f10549424573710549424573e10549424573d10549424573510549424573c105494218dbe75d85420073e75d854218d3e75d8542005bd75d85420073d75d85420053d75d854218dbc75d8542185be73d8542005bd73d8542185bc73d85420aebf62d85420afaf62d85420073f52d85420073d52d8542007b751d8542007b451d8542007b731d8542007b431d8542005bf70d854217dbe70d8542005bd70d854217dbc70d85420079f30d85420079d30d8542007af20d8542007ad20d8542007b710d8542007b510d854218dbe7598542005bd759854218dbc7598542006bf6598542006bd6598542185be7398542005bd7398542185bc7398542007ad729854208faf62985420073f52985420073d5298542005be7198542006bf6198542007b7619
  | 24 => 0xd71d9542005bf70d954217dbe70d9542005bd70d954217dbc70d9542006bf60d9542006bd60d95420079f30d95420079d30d9542007af20d9542007ad20d9542007b710d9542007b510d954218dbf75595420073f655954218ebe655954218ebc655954218f3c655954218e3c6559542005bf73595420079f73595420059f7359542185be7359542185bc73595420079c73595421859c735954218f3f5359542005bf7259542007af7259542005af72595421d6bf62595421d7af6259542005bf7159542007b77159542005b77159542005bc7159542007b47159542005b4715954218f3c5159542005bf7059542007bb7059542005bb705954217dbe7059542005bd705954217dbc7059542007b8705954217db87059542006bf6059542006bd605954218f3f50595420073d50595420079f30595420079d3059542007af2059542007ad2059542007b71059542007b51059542185be76d8d4218dbe75d8d42005bd75d8d4218dbc75d8d42006bf65d8d42006bd65d8d42186be63d8d421879e63d8d42186bc63d8d420079f53d8d421879c53d8d4203dbe72d8d4201dbd72d8d4216ebf62d8d4216faf62d8d421879f32d8d42005be71d8d42005bd71d8d421879c31d8d42005bf70d8d4217dbe70d8d42005bd70d8d4217dbc70d8d421879f30d8d420079d30d8d42007af20d8d42007ad20d8d42007b710d8d42007b510d8d42005bf7558d4218dbe7558d4218dbc7558d42006bf6558d42006bd6558d42185bf7358d420079f6358d42186be6358d42186bc6358d421879c6358d42005bf7258d42007af7258d42005af7258d42157af6258d42005bf7158d42007b77158d42005b77158d42005bc7158d42007b47158d42005b47158d42005bf7058d4217dbe7058d42005bd7058d4217dbc7058d421879f3058d420079d3058d42007af2058d42007ad2058d42007b71058d42007b51058d42005bf7654d42005be7654d42005bd7654d42005bc7654d42185bf7554d4218f3e6554d420073d6554d42185bf7354d4218f9f5354d421873e5354d421873c5354d421879c5354d42005bf7254d4203dbe7254d4203dbc7254d421b6bf6254d42227af6254d4218f3f5254d42005bf7154d42005bc7154d42485bf7054d4217dbe7054d42485bd7054d4217dbc7054d421879f3054d4247f9d3054d4247faf2054d4247fad2054d4247fb71054d4247fb51054d4218f3f76d494218f3e76d494218f3d76d49422073c76d494218f3f73d494218f3e73d494218f3d73d494218f3c73d49420073f63d49424773e63d49420073d63d49424773c63d494203d3d72d494203f3f62d494203e3f62d49422072f62d494203f3f32d494203f3e32d494203f3c32d494218f3f71d494218f3e71d494218f3d71d494218f3c71d49424773f31d49424773c31d4942
  | 25 => 0xd4248f9d3050d4248faf2050d4248fad2050d4248fb71050d4248fb51050d420267f76d49422067e76d494218e7d76d49420267c76d49422073e74d494218f3d74d494203e7f64d49420067f63d49421fe7e63d49421fe7c63d49422073f43d49424773e43d49420073d43d49422073c43d494203d7d72d494203e7f62d49422076f42d494203f3e42d494203f3c42d494203f6c42d49422073f41d49422073c41d494246e7f60d49421f67e60d494246e7d60d49421f67c60d49422073f40d494246f3e40d494246f3d40d49422073c40d494246f5f30d494246f5d30d494203f6f20d494246f6d20d494246f7710d494246f7510d4942024ff765494201cfe76549421d4fd765494201cfc76549420067f65549420267c6554942005bf745494201dbc745494218f3f54549421d73e54549420073d54549421d73c545494203fac42549420267f76549421d67e76549421d67d76549420267c76549420073f74549421d73c745494203e7f64549420067f63549421ce7e63549421ce7c63549421d73f43549424673e43549420073d43549421d73c435494203d7f725494218f6f725494203e7f62549421d76f425494203f3e425494203f3c425494203f6c425494203f2c42549424676f325494203f6c32549421d73f41549421d73c415494203f6f21549424567f60549421c67e60549424567d60549421c67c60549421d73f40549424573e40549424573d40549421d73c40549424575f30549424575d305494203f6f20549424576d205494245777105494245775105494218d7e75d85420057d75d8542024fe75d85420067e75d85420247e75d8542004fd75d85420067d75d85420047d75d8542024fc75d854203cfd74d8542014fe73d8542004fd73d8542014fc73d85420067f52d85420067d52d8542006f751d8542006f451d85420aef641d85420aebc41d8542006f731d8542006f431d8542004ff70d854200cfe70d8542004fd70d854200cfc70d8542006df30d8542006dd30d8542006f710d8542006f510d8542006f76198542005df7358542185dc7358542006f56118542024fe7518542004fd751854202cfc751854203cfd741854204ebe5418542006bd5418542014fe7318542004fd731854202cfc73185420067f52185420067d5218542006f7511854202ef4511854202ebf411854202ef6411854204ef54118542006f7311854202ef4311854202cff701854200cfe7018542004fd701854200cfc7018542006be401854204ebc4018542006df3018542006dd301854202ef71018542006f5101854218dbe76d954218ebe65d954218f3e65d954218e3e65d954218ebc65d9542185be73d9542005bd73d9542185bc73d954203dbe72d954201dbd72d95421eebf62d95421efaf62d954218f3f52d9542005be71d9542005b
  | 26 => 0x6dd30d9542006ef20d9542006ed20d9542006f710d9542006f510d954218e7c65595421d73e54595421d73c5459542005df7359542185dc7359542205ef7259542005f77159542005f47159542005fb705954217df870595421ecff75595420067f75595421d4ff7459542006bf745954218ebf54595421d67e54595421d67c54595421d6bc54595421d63c5459542004ff7359542006df7359542004df7359542014fe7359542014fc7359542006dc7359542014dc735954218e7f53595421d6bf4359542204ff7259542006ef7259542004ff7159542006f77159542004f7715954202cfc7159542006f47159542004f4715954218e7c51595421d6bc4159542004ff7059542006fb7059542004fb705954200cfe7059542004fd705954200cfc7059542006f8705954200cf8705954218e7f50595420067d50595421d6bf4059542006bd4059542006df3059542006dd3059542006ef2059542006ed2059542006f71059542006f5105954203dbc7655142026bc765514203cbc765514201dbf755514201f3f75551420073f6555142026be6555142026bc655514218f3c65551420263c6555142005bf7355142185be7355142185bc735514218f3f5355142007af725514203dbe725514203dbc7255142007ac725514201ebf625514201faf625514218f3f5255142005bf7155142005bc715514218f3c51551424adbf705514217dbe70551424adbd705514217dbc70551424a6bf60551424a6bd605514218f3f50551424a73d50551424a79f30551424a79d30551424a7af20551424a7ad20551424a7b710551424a7b51055142014fe76d8d4201dbe74d8d42186de63d8d421879e43d8d42024fe75d8d42004fd75d8d42024fc75d8d4203cfd74d8d4203cbd74d8d4216ebe54d8d42006bd54d8d42006df53d8d42186dc53d8d42186be43d8d42186de43d8d4216edd43d8d42186bc43d8d4201cfd72d8d42186df32d8d4202cfe71d8d42004fd71d8d42186dc31d8d42004ff70d8d4200cfe70d8d42004fd70d8d4200cfc70d8d42186df30d8d42006dd30d8d42006f710d8d42006f510d8d42186dc6358d4249def7258d42005f77158d42005f47158d42004ff7654d42004fe7654d42004fc7654d420267e6554d420067d6554d42005bf7454d4201dbe7454d4201dbc7454d4218f3f5454d420073d5454d4203dbc7650d42016bc7650d4203cbc7650d42005bf7550d4218dbe7550d42005bd7550d4218dbc7550d42006bf6550d42006bd6550d4201dbf7350d4201f9f7350d420079f6350d42016be6350d42016bc6350d421879c6350d42007af7250d4203dbe7250d4203dbc7250d42007ac7250d4201ebf6250d4201faf6250d42005bf7150d42005bc7150d42495bf7050d4217dbe7050d42495bd7050d4217dbc7050d421879f305
  | 27 => 0xf73596420067e73596420067d73596420067c73596421d67f43596421d67e43596421d67d43596421d67c435964203e7f725964203e7e725964203e7d725964203e7c725964203e7f425964203e3f425964203e7e425964203e7d425964203e3d425964203e7c425964203e7f325964203e7e325964203e7d325964203e7c32596420067f71596420067e71596420067d71596420067c71596421d67f41596421d67e41596421d67d41596421d67c41596420067f31596420067c315964203e7f215964203e7e215964203e7d215964203e7c21596420067f70596420067e70596420067d70596420067c70596421d67f40596421d67e40596421d67d40596421d67c40596420067f30596420065f30596420067e30596420067d30596420065d30596420067c305964203e7f205964203e6f205964203e7e205964203e7d20596420066d205964203e7c20596420067f10596420067710596420067e10596420067d10596420067510596420067c1059642004ff7558e42024fe7558e42024fc7558e4203edf7358e4219ede4358e42156dd4358e4203cfe7258e4203cfc7258e4203e7f5258e4203e7d5258e4203ebf4258e4203ebd4258e4203ede3258e4203edc3258e42004ff7158e4202cfc7158e4219edf3158e42004ff7058e4200cfe7058e42004fd7058e4200cfc7058e4219edf3058e42006dd3058e42006f71058e42006f51058e42004ff7654e42004fd7654e4203cfc7654e420267e6554e420067d6554e42186bd6454e42024fe7598642004fd759864202cfc7598642014fe7398642004fd739864202cfc739864203cfe729864202cfc729864203e7f529864203e7d529864203ebf429864203ebd429864202ef6719864202ef6419864208ef5419864203ef7219864202ef4219864202cff709864200cfe7098642004fd709864200cfc7098642006df3098642006dd309864202ef71098642006f51098642004ff7558642024fe7558642024fc7558642004ff7358642014fe7358642014fc735864203cfc725864203e7f525864203e7d525864203ebf425864203ebd425864203ef77158642076f6415864203ef7215864203ef42158642004ff705864200cfe7058642004fd705864200cfc7058642006df3058642006dd3058642006f71058642006f51058642024fe76d954218e7e65d954201dbe74d954203dbd74d954218f3f54d954203cff74d954203cfd74d954218ebd74d954203cbd74d95421ee7f54d954218ebf54d954218e3f54d95421ee7d54d95421eebc54d9542014fe73d9542004fd73d9542014fc73d95421eebf43d954201cfd72d954218e7f52d954202cfe71d9542004fd71d95421eebc41d9542004ff70d954200cfe70d9542004fd70d954200cfc70d95421eebf40d9542006bd40d9542006df30d9542
  | 28 => 0x4b422073d63d4b422073c63d4b4203f3f32d4b4203f3e32d4b4203f3c32d4b421bf3f71d4b421bf3e71d4b421bf3d71d4b421bf3c71d4b422073f61d4b422073e61d4b422073d61d4b422073c61d4b424d73f31d4b424d73c31d4b4203f3f21d4b4203f3c21d4b421bf3f70d4b421bf3e70d4b421bf3d70d4b421bf3c70d4b422073f60d4b422073e60d4b422073d60d4b422073c60d4b424cf3f30d4b424cf1f30d4b424cf3e30d4b424cf3d30d4b424cf1d30d4b424cf3c30d4b4203f3f20d4b4203f3e20d4b4203f3d20d4b4203f3c20d4b424cf3f10d4b424cf3710d4b424cf3e10d4b424cf3d10d4b424cf3510d4b424cf3c10d4b421d5bf7654b4201dbe7654b4201dbc7654b4203dbf7554b421d73e6554b421d73d6554b42005bf7354b421b5be7354b421b5bc7354b421bf3f5354b424c73e5354b420073d5354b421bf3c5354b4203dbf7254b4203ebd6254b421bfaf5254b4203f3e5254b4203f3c5254b4203fac5254b42005bf7154b42005bc7154b421bf3f5154b421bf3c5154b424bdbf7054b421adbe7054b424bdbd7054b421adbc7054b421bf3f5054b424b73e5054b424b73d5054b421bf3c5054b424b79f3054b424b79d3054b4203faf2054b424b7ad2054b424b7b71054b424b7b51054b421d73f7654b421d73e7654b421d73d7654b421d73c7654b420073f7354b424c73e7354b420073d7354b424c73c7354b421d73f6354b421d73e6354b421d73d6354b421d73c6354b4203f3f7254b421bf2f7254b4203f3f3254b4203f3e3254b4203f3c3254b420073f7154b420073e7154b420073d7154b420073c7154b421d73f6154b421d73e6154b421d73d6154b421d73c6154b424c73f3154b424c73c3154b4203f3f2154b4203f3c2154b424bf3f7054b424b73e7054b424bf3d7054b424b73c7054b421d73f6054b421d73e6054b421d73d6054b421d73c6054b424b73f3054b424b71f3054b424b73e3054b424b73d3054b424b71d3054b424b73c3054b4203f3f2054b4203f2f2054b4203f3e2054b4203f3d2054b424b72d2054b4203f3c2054b424b73f1054b424b7371054b424b73e1054b424b73d1054b424b7351054b424b73c1054b4203e7f75596421d67f54596421d67d5459642004ff7359642014fe7359642014fc73596421a67f53596420067e53596421a67c535964203cfe725964203cfc725964203e7e525964203e7c525964203ebf425964203ebd4259642004ff715964202cfc71596421a67f51596421a67c5159642004ff705964200cfe7059642004fd705964200cfc70596421a67f50596420067e50596420067d50596421a67c5059642006df3059642006dd305964203eef2059642006ed2059642006f71059642006f510596421d67f74596421d67e74596421d67d74596421d67c74596420067
  | 29 => 0x57c7650d521cd7f7450d521d73e6450d520073d6450d521cd7f7350d521d75f4350d521cf3e4350d521cf3c4350d521cf5c4350d520057f7250d5203d7e7250d5203d7c7250d521fe7f6250d522176f6250d521d73f4250d520057f7150d520057c7150d524f57f7050d521c57e7050d524f57d7050d521c57c7050d521cf5f3050d524ef5d3050d524ef6f2050d524ef6d2050d524ef771050d524ef751050d521d57e74d85520073e74d85521d53e74d85520057d74d85520073d74d85520053d74d85521d57c74d85521cd7e73d85520057d73d85521cd7c73d85520b67f62d85520b76f62d85520077741d85520077441d85520077731d85520077431d85520057f70d85521c57e70d85520057d70d85521c57c70d85520075f30d85520075d30d85520076f20d85520076d20d85520077710d85520077510d85521d57e74985520057d74985521d57c74985520067f64985520067d64985521cd7e73985520057d73985521cd7c73985520076d72985520976f62985520057e71985520067f61985520077761985520057f70985521c57e70985520057d70985521c57c70985520067e60985520067c60985520075f30985520075d30985520076f20985520076d20985520077710985520077510985520057f74585521d57e74585521d57c74585520057f73585520075f73585520055f73585521cd7e73585521cd7c73585520075c73585521cd5c73585520076f725855207f6f62585520077761585520067e61585520057f70585521c57e70585520057d70585521c57c70585520075f30585520075d30585520076f20585520076d20585520077710585520077510585520057e76185521d57e74185520057d74185521d57c74185520067f64185520067d64185521cd7e73185520057d73185521cd7c73185520567f62185520576f62185520067f61185520077661185520067d61185520077561185520077741185520077441185520077731185520077431185520057f70185521c57e70185520057d70185521c57c70185520067e60185520067c60185520075f30185520075d30185520076f20185520076d2018552007771018552007751018552225bf7654f4201dbe7654f42225bd7654f4201dbc7654f421b5bf7554f422273e6554f422273d6554f421b5bf7354f421b79e6354f422279d6354f421bf9f5354f421b73e5354f421b73c5354f421b79c5354f42005bf7254f4203dbe7254f4203dbc7254f421bf3f5254f42005bf7154f42005bc7154f424e5bf7054f421adbe7054f424e5bd7054f421adbc7054f421b79f3054f424df9d3054f424dfb71054f424dfb51054f422073f76d4b422073e76d4b422073d76d4b422073c76d4b421bf3f73d4b421bf3e73d4b421bf3d73d4b421bf3c73d4b422073f63d4b422073e63d
  | 30 => 0xf70d855200cfe70d8552004fd70d855200cfc70d8552006df30d8552006dd30d8552006f710d8552006f510d8552006f76198552005df73585521cddc7358552006f5611855203cfd751855201cfe7418552004fd741855202cfc74185520567f54185520067d5418552014fe7318552004fd731855202cfc731855202e7f511855202ef65118552056f55118552006f7411855202ef44118552006f7311855202ef4311855202cff701855200cfe7018552004fd701855200cfc70185520067e50185520567c5018552006df3018552006dd301855202ef71018552006f510185521d57e76d91521d67e64d91521d73e64d91521d63e64d91521d67c64d91521cd7e73d91520057d73d91521cd7c73d915203d7e72d91520257d72d91521a67f62d91521a76f62d91521d73f42d91520057e71d91520057d71d91520057f70d91521c57e70d91520057d70d91521c57c70d91520067f60d91520067d60d91520075f30d91520075d30d91520076f20d91520076d20d91520077710d91520077510d91521d57f74591520073f64591521d67e64591521d67c64591521d73c64591521d63c64591520057f73591520075f73591520055f73591521cd7e73591521cd7c73591520075c73591521cd5c73591521d73f43591520057f72591520076f72591520056f725915218f6f62591520057f71591520077771591520057771591520057c71591520077471591520057471591521d73c41591520057f70591520077b70591520057b70591521c57e70591520057d70591521c57c70591520077870591521c57870591520067f60591520067d60591521d73f40591520073d40591520075f30591520075d30591520076f20591520076d20591520077710591520077510591521cd7e76d8d521d57e74d8d520057d74d8d521d57c74d8d520067f64d8d520067d64d8d521ce7e63d8d521cf5e63d8d521ce5e63d8d521ce7c63d8d520075f43d8d521cf5c43d8d5203d7e72d8d520257d72d8d521767f62d8d521776f62d8d521cf5f32d8d520057e71d8d520057d71d8d521cf5c31d8d520057f70d8d521c57e70d8d520057d70d8d521c57c70d8d521cf5f30d8d520075d30d8d520076f20d8d520076d20d8d520077710d8d520077510d8d520057f7458d521d57e7458d521d57c7458d520067f6458d520067d6458d521cd7f7358d520075f6358d521ce7e6358d521ce7c6358d521cf5c6358d520057f7258d520076f7258d520056f7258d5215f6f6258d520057f7158d52007777158d52005777158d520057c7158d52007747158d52005747158d520057f7058d521c57e7058d520057d7058d521c57c7058d521cf5f3058d520075d3058d520076f2058d520076d2058d52007771058d52007751058d520057f7650d520057e7650d520057d7650d52
  | 31 => 0x915203c7d75d91521d67e54d91521d6be54d91521d63e54d91521a6bd54d91521d67c54d9152014fe73d9152004fd73d9152014fc73d91521a67f53d9152024fd72d91521d6bf42d915202cfe71d9152004fd71d91521a67c51d9152004ff70d915200cfe70d9152004fd70d915200cfc70d91521a67f50d91520067d50d9152006df30d9152006dd30d9152006ef20d9152006ed20d9152006f710d9152006f510d91521d6bc645915218f3f54591521d73c5459152005df73591521cddc73591521bdef7259152005f77159152005f47159152005fb70591521c5f8705915203d7c765515201e7c765515203c7c76551520257f74551520273f74551520073f645515201e7e645515201e7c64551521d73c645515201e3c64551520057f73551521cd7e73551521cd7c73551521d73f43551520076f725515203d7e725515203d7c72551520076c72551520267f62551520276f62551521d73f42551520057f71551520057c71551521d73c415515251d7f70551521c57e705515251d7d70551521c57c70551525167f60551525167d60551521d73f40551525173d40551525175f30551525175d30551525176f20551525176d2055152517771055152517751055152014fe76d8d520257e75d8d521cede63d8d521cf5e53d8d5203cfd75d8d5203c7d75d8d5201cfe74d8d52004fd74d8d5201cfc74d8d521767f54d8d520067d54d8d521ce7e53d8d521cede53d8d521ce5e53d8d52176dd53d8d521ce7c53d8d52006df43d8d521cedc43d8d52024fd72d8d521cedf32d8d5202cfe71d8d52004fd71d8d521cedc31d8d52004ff70d8d5200cfe70d8d52004fd70d8d5200cfc70d8d521cedf30d8d52006dd30d8d52006f710d8d52006f510d8d521cedc6358d5250def7258d52005f77158d52005f47158d5203d7c7654d520167c7654d5203c7c7654d520057f7454d521d57e7454d521d57c7454d520067f6454d520257f7354d520275f7354d520075f6354d520167e6354d520167c6354d521cf5c6354d520076f7254d5203d7e7254d5203d7c7254d520076c7254d520267f6254d520276f6254d520057f7154d520057c7154d525057f7054d521c57e7054d525057d7054d521c57c7054d521cf5f3054d524ff5d3054d524ff6f2054d524ff6d2054d524ff771054d524ff751054d52004ff7650d52004fe7650d52004fc7650d520057f7550d520257e7550d520057d7550d520257c7550d5201ebe6450d521d73e5450d520073d5450d521d5be74d8552005bd74d855203cfd75d855201cfe74d8552006be74d855201cbe74d8552004fd74d8552006bd74d8552004bd74d855201cfc74d8552014fe73d8552004fd73d8552014fc73d85520b6f651d85520b67c51d8552006f741d8552006f441d8552006f731d8552006f431d8552004f
  | 32 => 0x3cfc725925203e7f525925203e7d525925203ebe425925203ebc4259252004ff715925202cfc71592521eebf41592521eebc4159252004ff705925200cfe7059252004fd705925200cfc70592521eebf4059252006be4059252006bd40592521eebc4059252006df3059252006dd305925203eef2059252006ed2059252006f71059252006f5105925218ebe755925218ebd75592521eebc7559252006bf7359252006be7359252006bd7359252006bc735925218ebf535925218ebe535925218ebd535925218ebc535925203ebf725925203ebe725925203ebc725925203ebf525925203e3f525925203ebe525925203ebd525925203e3d525925203ebc525925203ebf325925203ebe325925203ebd325925203ebc3259252006bf7159252006be7159252006bd7159252006bc715925218ebf515925218ebe515925218ebd515925218ebc5159252006bf3159252006bc315925203ebf215925203ebe215925203ebd215925203ebc2159252006bf7059252006be7059252006bd7059252006bc705925218ebf505925218ebe505925218ebd505925218ebc5059252006bf30592520069f3059252006be3059252006bd30592520069d3059252006bc305925203ebf205925203eaf205925203ebe205925203ebd2059252006ad205925203ebc2059252006bf1059252006b71059252006be1059252006bd1059252006b51059252006bc1059252004ff7458e5201cfe7458e5201cfc7458e5203edf7358e521e6de5358e5215edd5358e5203cfe7258e5203cfc7258e5203e7f5258e5203e7d5258e5203ebf4258e5203ebd4258e5203ede3258e5203edc3258e52004ff7158e5202cfc7158e521e6df3158e52004ff7058e5200cfe7058e52004fd7058e5200cfc7058e521e6df3058e52006dd3058e52006f71058e52006f51058e52004ff7650e52004fd7650e5203cfc7650e521ce7d6550e5201ebe6450e52006bd6450e5201cfe7498652004fd749865202cfc7498652014fe7398652004fd739865202cfc739865203cfe729865202cfc729865203e7f529865203e7d529865203ebf429865203ebd429865202ef6719865202ef65198652096f5519865203ef7219865202ef4219865202cff709865200cfe7098652004fd709865200cfc7098652006df3098652006dd309865202ef71098652006f51098652004ff745865201cfe745865201cfc7458652004ff7358652014fe7358652014fc735865203cfc725865203e7f525865203e7d525865203ebf425865203ebd425865203ef7715865207ef6515865203ef7215865203ef42158652004ff705865200cfe7058652004fd705865200cfc7058652006df3058652006dd3058652006f71058652006f5105865201cfe76d91520257e75d91521d6be64d91521d73e54d915203cfd75d
  | 33 => 0xc50d954354edf30d9543006dd30d9543006f710d9543006f510d9543024ff76595432167c6559543545bf7459543555df735954354cff75595430067f7559543544ff7459543006bf7459543234ff7359543006df7359543004ff725954303cfc72595432167f5259543226bf4259543004ff715954302cfc7159543004ff705954300cfe7059543004fd705954300cfc7059543236df3059543006dd3059543006f71059543006f51059543015bc7655143026bc7655143014bc765514301dbf755514301f3f75551430073f6555143026be6555143026bc65551432173c65551430263c65551430079f7355143015be7355143015bc73551432379c735514301ebf635514301f9f63551432373f53551432373d5355143005bf72551432173f52551432173c515514353ebf605514353ebd60551432173f505514353f3d50551432379f305514353f9d305514353fb7105514353fb5105514303cfe76d8943024fe75d8943004fd75d8943024fc75d89431b6bf74d8943014fd74d894349ebe54d8943006bd54d894301cfd73d89431b6be43d89431b6bc43d89431b6bf42d894349eee42d89431b6ee32d894302cfe71d8943004fd71d8943004ff70d894300cfe70d8943004fd70d894300cfc70d89431b6df30d8943006dd30d8943006f710d8943006f510d89432157e75989430057d7598943006ef6298943005f77158943005f471589432157e75189430057d751894303eee6218943006ed6218943024fe75d8543004fd75d8543024fc75d8543014fd74d854301cfd73d854303cfe72d8543004fd72d85433aebf42d85433aef641d8543346f631d8543004ff70d854300cfe70d8543004fd70d854300cfc70d8543346df30d8543006dd30d8543006f710d8543006f510d8543006f76198543006f56118543024fe7518543004fd751854302cfc7518543014fd7418543536be5418543006bd541854301cfd731854303cfe7218543004fd7218543536bf421854302ef64118543536f5411854302ef63118543306f5311854302cff701854300cfe7018543004fd701854300cfc7018543306df3018543006dd301854302ef71018543006f510185432157f7650f520257e7650f522157d7650f520257c7650f521fd7f7450f522073e6450f522173d6450f521fd7f7350f521ff5e6350f522175d6350f522075f4350f521ff3e4350f521ff3c4350f521ff5c4350f520057f7250f5203d7e7250f5203d7c7250f522073f4250f520057f7150f520057c7150f5252d7f7050f521f57e7050f5252d7d7050f521f57c7050f521ff5f3050f525275d3050f52527771050f52527751050f5203ebf74592521eebe545925218ebd5459252004ff7359252014fe7359252014fc73592521eebf4359252006be43592521eebc435925203cfe7259252
  | 34 => 0x8554024fd7418554014fe7318554004fd731855402cfc731855403cfe7218554004fd72185545867f521855438ebf421855402ef65118554586f5511855402ef6411855438ef5411855402cff701855400cfe7018554004fd701855400cfc7018554006df3018554006dd301855402ef71018554006f5101855401cfe76d9153226be64d9153014fd75d9153226be54d915357ebd54d9153024fd73d9153546bf43d915303cfe72d9153004fd72d915357e7f52d9153226bf42d915302cfe71d9153004fd71d9153004ff70d915300cfe70d9153004fd70d915300cfc70d9153006be40d9153226bc40d9153546df30d9153006dd30d9153006f710d9153006f510d9153226bc6459153575df73591530157c765515301e7c76551530147c76551530257f74551530273f74551530073f645515301e7e645515301e7c64551532273c645515301e3c64551530075f73551530157e73551530157c73551532375c73551530267f63551530275f63551532373f43551530057f72551532273f42551532273c415515356e7f605515356e7d60551532273f405515356f3d40551532375f305515356f5d305515356f77105515356f75105515303cfe76d89531fe7f75d8953014fd75d895301cfe74d8953004fd74d895301cfc74d895350e7f54d89530067d54d8953024fd73d89531fe7e53d89531fe7c53d89531fe7f52d895350eee52d89531feee32d895302cfe71d8953004fd71d8953004ff70d895300cfe70d8953004fd70d895300cfc70d89531fedf30d8953006dd30d8953006f710d8953006f510d8953225be7498953005bd7498953006ef6298953005f77158953005f47158953225be7418953005bd741895303eee6218953006ed6218953014fd75d855301cfe74d8553004fd74d855301cfc74d8553024fd73d855303cfe72d8553004fd72d85534067f52d8553406f651d855334ef631d8553004ff70d855300cfe70d8553004fd70d855300cfc70d855334edf30d8553006dd30d8553006f710d8553006f510d8553006f76198553006f56118553014fd751855301cfe7418553004fd741855302cfc74185535667f54185530067d5418553024fd731855303cfe7218553004fd72185535667f521855302ef65118553566f5511855302ef6311855330ef5311855302cff701855300cfe7018553004fd701855300cfc701855330edf3018553006dd301855302ef71018553006f51018553024fe76d95432167e65d9543234fd75d9543014ff74d9543014fd74d954355e7f54d954355e7d54d954301cff73d954301cfd73d954354e7f53d954354e7d53d954303cfe72d9543004fd72d95432167f52d954355ebf42d954302cfe71d9543004fd71d9543004ff70d954300cfe70d9543004fd70d954300cfc70d95430067e50d95432167
  | 35 => 0x1000000000c0020000000012001004804800000500d801c000019000001001a00f013004400200c00b00200680010000028004004000000000000e0200030008002005004401600000000040000010000004000008027000800400100980040060110000080002002000002c01c005002801800600000d000c000000002801c000000041802c00002a006802000000000080000040010008000012003001004800e00100000140160050000000034010000002401601900100000000010038000004002000806000201d00e807400c000003800400a04600b000000600401600e0002003002800c004000004807c03e057003800c000018004000000000200a000000200f001006c00600300e000c0000040030008002001006801800400000f000c0080010030000000004005000c0040010068014006000004800801a00d001006802e000000800001e000000800001000c000800001800400180280100020070034000001001000400001100480100000010038008010001011801000401e014fe76d8d545573c54d8d54236de63d8d5401cfd75d8d54024fd74d8d54236de53d8d54236de43d8d5403cfe72d8d54004fd72d8d545767f52d8d54556bf42d8d54236dc32d8d5402cfe71d8d54004fd71d8d54236df31d8d54004ff70d8d5400cfe70d8d54004fd70d8d5400cfc70d8d54236df30d8d54006dd30d8d54006f710d8d54006f510d8d542273c5458d54236dc6358d5403cfe76d89542073c54d89542067f75d895401cfd75d89541bebf74d8954024fd74d89541bebf54d89542067e54d89542067c54d8954206bc54d89542063c54d8954014fe73d8954004fd73d8954014fc73d89541be7f53d8954206bf43d89542067f52d89541beee52d8954206bf42d8954206ee42d895402cfe71d8954004fd71d89541be7c51d8954206bc41d8954004ff70d895400cfe70d8954004fd70d895400cfc70d89541be7f50d89540067d50d8954206bf40d8954006bd40d8954006df30d8954006dd30d8954006f710d8954006f510d89541ef3c5498954006ef62989541d73c5458954005df7358954235dc7358954005f77158954005f47158954005fb705895422df8705895458f3c541895403eee6218954006ed62189543b73c54d855401cfd75d85543b67d75d8554024fd74d855440ebd74d8554014fe73d8554004fd73d8554014fc73d855403cfe72d8554004fd72d855440e7f52d85543b6bf42d855440ef651d855440e7c51d85543b6f641d85543b6bc41d8554004ff70d855400cfe70d8554004fd70d855400cfc70d8554006df30d8554006dd30d8554006f710d8554006f510d85541473c5498554235de7398554005dd7398554006f7619855422dfa7098554005f9709855412f3c545855438f3c5418554006f5611855401cfd751
  | 36 => 0x4003000c00e0030000000000007003801000401b0038028030002000005001600100900000580020030034006001006000000000d007800000400500f8040000001000005801800100d0018022009003800000a0000030078004004011801c00e00200380280000050050050024004002803800600700000000140010000008000003006800000a0020000030000004001002c02a04c00a8060066002002002c016001003000c0540040028008000000002801800000200300040020000008000002003001002c022006001000800e01f00a8050004002000800000e001007800001a000002800000200800080080000000098018002022003802c0000030000004000000000000002c000000009002a000002800c00a002001001003e007008000c010000003000400e006003004000c009006802400400e0000008008011004800000a007000003000801b0000000000023007001c00000b0058000020001000001004e01a000001400001100401a002800100000080060350000010004005002000000001901d000c00200c001000c01c001004803c000003001000400c0070008044010001007800c01a02c000000800600000500080060030080024000009001005c03c00100000280040040030004000001000006402c004005000800400000080280040010030004004005002800000e00001c00100160170018000004042004800000600000f80000020010000030002008001800000a00000c80c0000003000800400a00000180340000050020020094008000001c0060000040024038001000003800e0000090010008001002800c01c004011800802200100600040240000038010008003000803c032003006800000000f009002801e00400580440060110018008004000000800c030001001803402a0090000068000000000005400a077005800000600500280100200040050018000006000000c01400e003003800600e00000080040180070074008001000003c01c01d000809400400a000000000c00100180180000000008000000043001005803c0010018010006004000000803200000000100e000e002003c01800100000400080030038010014011004801c002000000800003e0220038048002001002800802a0020010098006008000800c05e00601600000000010130000006000000000400401d0048050004001000805400e00d00000880020000030004002006004800002600e00d804400e00c004801800600e002801c028001004802802a00100b801c002002006000002200100780100080060010008006001000000801a002014800c00e0110008054002013003809000a021004002006000d01c8010008002000000000200000080a0006000012800400600300000000500000008000000001008000c00000
  | 37 => 0x100180040600100078000002002000000000200300280000080010060098002000000801c006001000800002e00b000801400a009000001400000400080000040000008000000000004800000e00200e8044000003006002800201801400000020080040028004005000005c004000000001c00000e001800401000400f8030004001000001c00800800100d400001c01580440020040030014000002009002c012004000002c02c0020010000030000000002400400f01100100000020080038000010000800002e00d002003c022000000801c07e000003000c0000010008010002022004800000c022004011804200600180d000000000900000440010050074058000000000003a00000180a801c004004000c01c01b0100004000027004802400a017000001000000000100100000000118020010011005013000e0000048028008005011802800400000a800003600b006000000c000002000c00200100180140000010038028000004001000001a00000c800c02400100b000c00800500080380380030000004000015002000005200500080000000020030004018016001000400e00100100040140070070010000002009805001e005000001c0000060018010010004005019c064000000805000600b004003400a000000001c01000b001801c0100040008014004008002801000400a000002c0080000070000006012007800003a001000800000200b004000000c0020070010006011004800000a012000800800005200d80840060160000004002012000000800200c0008000014002000801000201a00780780040130010000010018003000001000b000800800400300880040020130020000042004005000805600100200040000030040018006007000005000000a000001403e019003000c01200f00980cc09c00000a801c0020000040000002000006800c00000e00a003c048000003800c00001200b008400603000080440180020000010000000000000001e00700002040040030280018000002013802000600000a800c0020000000004000001012801002e00f00680000000010070028000019006800001c0000008014022002003002000a004001805c00e018005000001a003006000c00200600280b8004000001004c00200400380ec0440000010000040002000802801400a000801800e0050038024020002000000c000002005000c002009002806400200000d80100140050018000012000001800800000600500180060000078008006010001000c00e00a00080080020000000000000004001000000405702d00180120090030004002023000001800802d001000c01a0030000008014003005009c01a007001000000e00600380180000000010000000003000801000200b000000c03000e001803c00201600380
  | 38 => 0x2223c000054c851491d9a16000000000029006de0b4400028146fe189c000127815822e648184641fb89ac0000000922986081e859e73c0c1241baa7c8e980007d8a2a456c9ef4b2b0d6a54186643db8a6a00021c45e20a5c0dd073600006aeac080003b100000772f306c7a480a5da99855e992c9fa96404f5a5b65a88b76874087e3250e2011126d051b998e7229b823c30000a9e14ac7cb934a5c60dd0a6510dc715800c000000001c00000a007800400e000003004001400c0000014000000007805802401900b000400200000380000ba01f000805c002002008006000204c000800c06200200380000200010078000012001000000402000b000806c008000001000401000000100b0002004001006400200d0010054008000000800000e002001800000400001e000c000001004001800601f0020008008000002001000401e002001c00e006010004403c002000003c010001001000001c01000000280020030020004020004001004406a010000000001e00000000380b000600d8024006002000003800e0030020058026001015004c000000000001802000000000000000010048010004000000002802400000b0034000000000000000a007001018000600300b800800200500a000c00200f000003800200800080300260000030008000004007000c00200400f800000400000000340060010040070004002000000400000400000040020000000020044001003800402a000000000c00006d001800c0000030000024008008000000400000201600000060010010018014003001008801000e00700100060140018000012003000001c00401e00500000000010010000000001009803801c00600080600000120010004024008000000400a00000280a403e011001007000e002000005c02400800380840000090010000000003007006000c00000400040020030030004000009000800401c0030028034018000000800c000027006800807e0030008038078041002001803a00000000c4014004009008800200001600000060280030000000004001000000601d000001c0020030040020000001000800800e00400e00040060070000034000020002001400603b0070214000008002801400a018003003000000001d800002c022000008000c00b00f800400e002000804800a001009000400e001003000c000008000002001001300200a8000000000801002800000000040020000000004002007006000000200000100740080000010000034004005800000601000200440060000010010026013005000c03602300e000000602e000003000400d0020020044000019804000000800100080180240000008000001000000c0020000000024000003000002801e006004000c0000360048000020006019000000401000000140300
  | 39 => 0xbd80009a0a302000000000029d2835ac1600000002de91500412be02e62d420001e6e8f01a3ebaea4dc99daebc00008589bf8ae24a5000000023429f595ca786800020080b0000141800f2b420001d7c9aa1a3a993a35265c9aacb421db21881912000166626e101c7790596b1aad4ebcd1dd47059c624eda57275fac223bc8a52367845cb1e19625808000000179c852a73a9210ae6a0c800016f800094080002fe27a816aa6148cf986a675aafcba914665d922107928000476858c4f8a1349be800026c0000af08000b0d8000312961c27c2b2200000000000000104a6c63398792685153a01580000001bf42608000000276caabad1246b8000b9d80004ad80006060ebe7970000000000033697c0795143660c8c24b242d6a8571e842c30a626881196181960a00015743a8a1e29bd00d616694845c5000016510ea22711f2502adeea09a70e413a3b0b401ecaaf40bb64618f7c39b869eba315feb632ef047e0e2c69186fe276a768b4e000018d93d000021d21948bfc21400006bc1f66631920c90c0fdc49f9c7c35296cc87007da174000019c2cda574a26c7f092a256499162212dd43fa0000697a5acb2c191eaa920b42c8022438fa3c27e8171031da8be4fb886c5d18d84a5c904c0160168b48283069d921e8899bae5831ab25b08558b7395aa85880006ffa8c82ae2ba4a8b890665180d22e29b3e3c0ac0ea9a9100000263e00010c03ac0f584dba0e6150a2fe0002740327a35eb63a7de0000000000000000000007dc214c0bb9a36943a9d4254a33a1fc8aa602a834837992121c3a3b825228ca00019ac00000003032bc855faf2000000009bd9a1841d00000001a72000000000003ae0cc111c38a151642091267f392d46b609b49b588d445108e413501283ba83987a4000017aa69c3dc25d88d923a8643800093224ce6600000775a7e21ef264a85e9ad00001f3c1699672310a014537000038910cc6e28f4881c000000991149a8026460596047b80d1e00004c0a822c460002bc60638fcc67225f4000007200aa80c63d1fa21a0a554000000089100001b5000000000001261ad68e30c140000d5e99815365338000000025a9d91002a130c20485000009f9dc0582009891112565ef1570759af5078180000000000804000066a800051f800000000000521daa00018e8bd197345c32a9866c21feb9f1eba9368e1cb0f051813180000000f0abb699da0001eaa76914064e7a5a418c94584a3023eb0823069c296d225e80007e40d0485b0c5038d8e184c6800000013a652f8d966c581ae29180002ee00001eb000061600009930000a5b0dda4e0ad28b9010be7e11200915a8581ff0e646d90934b4720f42dc0b1e5f800000dc2c34370a82c9b8062c1e511d800000006fea2a8b5c800072ba3d400000000001fe46ee85840ca92
  | 40 => 0x2b62d90c600d587446df20aa3451b444e181eeb38118a00780000001ae84d52a3a3b008a008718fc216800000000006a402f426f096a000117a412806462b21140000a440000a026498c2c8c7a84606a817885a9f341c19ece5d715d6099892a00011d62a10cfe57700fa68a28163071b142b295e46ab8000b699da84a980008a8a44800028780002ad0927aa026a486d2b8f9faa8f715040001db462097b854a8ad4b85210620a84106d08082a561c444a219c682a03f644816fe5be27b43378b429998856b279d3634c9016051a30a3d8ac6cbb5abb68aca8c200005ee0000ff489300004c087b60000000a9d970015228f003da7ee60801e400020ea876a9f0af6800012a00002a900003788faa4bc00003d12de20001d6c0000000000299204622ccb700d2e7138000bdc9152000000000000000000a4e000185408ba28a203803e003ab5c7322b32000000000018c86f0a70cbd208c200000001108000af583345ec80006e6800033aaf1c12900000d080008be80008c9a39c91e9f0043e20b64740d86b909c4a00000004530000b598000672a31251500000ff2e666378000abc97747a680001448f4a5c20ede8e8030e71320740e91ce23b226446098000000114094d8000b6700003c58000770a2820002e38a108f7a06f2d963c989740001b6800000007e7a2e85fa04de000111a11023acb1813aa81f8c863b514b8bd89ec6bcf9e96ad01d8c00015e63fa8b7c37308ce8fc26ce9a89dae35a210400012da1e19c804508e1687b866a000000048a105a99224f42d996ec05894c826b9a2c97402d02d41b1086a05887ae0fca8be1ede00015c872980009092d5c33424ec3671bac8cb0ab44648b305f311d2000132a5578000000000093a00d0076a48c000000030d87b076f17e64f4861c0000000223974254022761309c7647224d40001ee6000111e6c8000073caf5a1c90000ae4829225b9da66b680006ea92c00001620b4901b0000103aae22af8b22800005398ce41cac0a6a92b8c51e88d01341a0e3208a7c0002a366ca90966fa08667fc24c206b1f4600004260001642404aedc62824b2ac4a74c78f1c10af484a0a1b29168b7ad92a2a926a000197e0001894ac31fe6785a638bad0578b1120b824780628c507fe7d0112c65e93449df000099e000000006a2000202c6a780001aa87ca7f82b1ca1b9bbe21c1f8047f03385070942b8428c00c11cb8a6ba34e39698529518be4880a67c7ad287a00000005dc000045917280002c52719876600010b63f7a6460c180000000a06272981a612a818000036c9dd192a45f25cc9a429480001e92000000088289c0ab281a28b3839297a906c0001098b1295a467a80009f98be600011360000000000087822e80002e799d200019a68ac00002800bca3c3a01c795aa847c800006
  | 41 => 0x7620024732a8f624f10648422b9a9fe1c9a7cc97fe36e11fa00000d46f5a99645b959a27d8e3a3f51e5a486aef82029f1a5292dbe1cb261e22e2e2ebd998c0411158a68028382fd80007fe80005e11b7e3d099f479d80004360e387c4952627912d28d8ab2c1e0023095b11a069b012eba21d762a22e8a99c082633e9aaa4d903bc198ac400f48000b5ba1ae2f6800054311f4222010200028520640a4c2f38b9022d20dc9e007fa56f2dd808aa3009be0a92192006e0a402085f380008019f0e733164a00014ba27e29e08989d4e000084e5d88af6000000068e1de265e233c95c21e0a9321986d411167f52c9c4ff9464a3a0710b5da1f2a33a236079876c15d173aaa792f441627c45bc05bc04201bea082da8000000044f845e4438b4c973800014309b6a93903000008823bb000000000000001498a16991c1f220c40000000080abaa3b58a780000b5200005a8556ae241942e747e2004831207a07e62c043abab1616480000811460920983c03d0000aff9c2c81681c04ff10de8a7985e95f803088880000002d74000000000000007a0adec52c96d000001d60000af2bd0834a26794003e483b20001a861be8f3a3ef153844e80009d985ae96404228f580005aa295ab0a80008102b4c4f3000000017be34d81862eaac4c80011eea2ca28600000ea000075a7c98a049ed80003fe800026c800050208d882ca5de1b82b8aa18970e0d983e40210b603432bac000116a39a9aa874e8fd88b6aa5a8480f200000634a3d04b40000520b5f1f500001c8221a997c96aaf2a0002b906fc00006a8000022c20ae6f1aabab2b8d568d295c400029f69331f024a4ac109fb00000000ff6bda87c0abb80000499ea6bca2e68acea964aec2a5e54c000096313e6b3200009422d1e15a0bfaae12a8e1f9a696ae02ea26121cb487f1cba6ff058200019549c8a6f06e8943ea2e0bae1d4254e1d0ab0635093c411fa7083e0195c53d8b0a4e20dde94e1124178ac667f30e8a31fa53e3ed223025693f4120abe4b07948e31c145c1fc1c98777a40c16e8c749b2acdc00087ba00029500c4a1deb7ca85c8758000a8c800066729300a527be0001a48a5983da388957c5d7aef6b7f283e7be942c4952b082519148000181003291e0bce09e691800000000bec3849a9ca07800000019745a588088432b7a2c0935859c0f4604d1a560000000000073a0f409f20002436b981eec5c9916c615a6b018f00b61d49d12a239a820c5236620ca8fc2d8825827f1eda0002c32a61800000000001a61fec4c4a2f04d02de8410000000000000000000063262a848923a506a3687f799181d38000539902a14886f45b001d80001244b280000246898c1b925d625e0000717a6b2000225644c284a07da0c695e00002d29bd800000001dd19f08e7800000020220cea2120000
  | 42 => 0x8000000253293f0ccc345a9b075c821a1d319a893f987200028f85da97de0b500001cf85e6000000000000008b585c25622d6880f000000015f6a0d9a6e000292495a05ca00001fa27b22660000000749aef4000000000006927171caca5d1a8e24017f0000000059d80000000eaa00014449700e7475413263b82c74a110034b3e000000029ca13aa3e825d984e39394ea11d241835817a8118136060dae0c64926aa1f881ea3dd96d429a2ab458e96c89da82be566149437916bc4be80420000f8417c08940002c560000d9200022780001d088862bf22d206fcbde1e6a0002e5a5c49300000195665b8000b30a32e59a05622b782284d6843c7bd8000b5c2b52854aa96abd80005db0000921a5cab348000000000000011d41be00007bc0ad81831842540883825c01963d81b52aa72afeb500c3c0000cd46849e4283f2868a6f2b9660914da02c85283a7900a9161cd87532c6e456991060c12108c80ff090b891429f8bf28af9e6c69c218e328987012f1d86b43902236698061c290560001eea3598ba64220e725561a2e3561a326220cfc794a06651a037825f1cfe3a60424128894a6e612ba6c2855caf50a206c31a96a5794d44b422901691e68062a0f672129b878a8c1a225aee43f80bde9c401925789028204231ab519fc68c3985c64100de42a0dd230204ac9a526000cb9e8c3df8a1665781d0827175455d83ea13c10142bf177a5509bc080a105231caa8a8e0a910a6997b01d21a5a84609864c5800039f0e2637d80064a68000550235c2712634000077a00023500001ac06358c787290aee79c80005f1a4d08951e9400009f4429800000000000000000b41279226480007160b5aa5b89a43ac895e00006c220d05ec000078468883ce00000386e800006a2aaa8335ae8e0bb0ce873a24ca1952e3c892ad1664829a80b38f564bb1ff81cc8000000034600000003da804c000260a5e992420002e32b768000aba81ca82e99023ed9d58b2e9fae46f0a9c75100009500af88f40000ba49abc7ee9df85d6080c4f7ab7614aa4e20cd80000000916319152017f8000bdd8924a9b9ef22261432a22143860fa52aafa13662b717d83ada86440e00baa7f1b6e92e1cb2a010f5c14129b63e917dab9325da00007e061baf7e1f51ea21e5a0a2afb8aa88ab800012e982c00000008a38000173265e103800083eadaca7e80903309422817998a4420ece000198698dacb849b2b723b6a9c6587924aa071d64724a49441d800000000005981a04b9f929c6d3a2a6830800049210348dd8000afb00008208000000159e0001456466a21e9a900004b594c69d4a960b4ca0fe0bf8000555a0984ac1b940002f6e2581db0534000043989fe3bf0740b14084aa3b825e06e1c0e100aa7a39d9f8c168000057e14280da979aa921c889ae0f0858b8696
  | 43 => 0x2a300006398000b20800000024001ef909a797acb611893749cb0f1a48611e400000000002cd899aa4689080000220000007c000064f8e92a290000ad800007f1255000014509aba090b0b1d70a4f00000002dfaa382a72625800044c849ab98989236d034053b0efe875290a1cd2e4613e8000743a8ac19800b843484ceb13a20894d2cea3549c9c000036800009e20000000b260000bc699e223e04d89719ab05caa0180000d8e0002bd812990a4000000032aa2ba63ba4eaa0aae86bc5895802525d4000000048803ba000000053c940457195226b796920002e1220919602049a108b488b200022f498f05e07ef80688df9d544b8a36a62d9f084a087028c8a498b3b138cb008354b6b98ec9660f3e30f812c8db149e5eb9f488220b2213b13720002eca2a5883e35680928a522605d6aa0a67b287c1e4101861e0ce21f3a01e4410fee2db0728000076a76e8b127a60edc0000eee9e8866e0000ca810d80000ab10d4a1f93b07f480000002e9e0000214142a1e454680006088d822190b38864800073b875e000000077801b65ea80000000000a46844aa7727d48971c9050f145e00008040fc00000000000b318e9ca1590605d8069c000061011c00000002c700000000542a9e82ce890867900000002b54af2800000022c60002e2c93b800000022065de0ee422f1bdc00000009680f1c57ca52e3b88df877303286ba80008870b18bab91748c3064c30a80000002c860a702223cf2cb269f2e5051023ee82b2e7800000000001bc8af88000865187e94f0a3058982d6b7a8d7c0f51202000100898c88c665982d2a8906ca827af32a34008e45284762bfa71ea910534a2686f678a00000f8a88aa671bde00000009c580009ef2f243db00002e59f82acc08a80a02180059000089399cc10f881a0362ab811213ec0558f8671f89de7e29f3e9f80d300571c1479300000001ef850c0d3448c9bb2910ae8200005de20f0e0a237000032fa3c43200e583348da20002d5600003b67e180005b28300308abfc5a80000aa30e907a2275c9e99f6c1f601885a6911013309669c480008eca27e656803a2cf1ffe4080f2c09386d81c724d20000eb406800f89e080000002daa0be8b8065a0000a50a89c0001600768000057e85ce0d822585b187a64d300006c180526d0109424f9f4250b81ec121000045714884cf0c7a00000007d315a00000b102348000430980e09c9122b8386de88a973680c10b220600004a5adb857319381418c6c9312c42000267231687dea9c1eb25a6000069d07c22570dc099b250a64516a42f487b80aa1006136a5e67ec27568fc9a78bab12de0000b4e000000075e1a3c5582c7649f2e1e9869c20ae18a1e8d02b500d6079a00026ac00029e460281388c61e741ea8000a608be8000000000026fc5fa
  | 44 => 0xa758000138842ab178c4e0001f4a82f180800000004ef8000bc982e06998a1c3a1800000000007490254ab5800044600000931e4400018ba50a8248177000093da0a00001f5462baea812da90857b087a2f1ace82cc82deb258000afe1c063510da4a4aa626b568a4a11a289280e94c291d2cce18aaf687862730344829697480005e185fc00010bc498000090999f223fa5662969fbc000109e504200435c94de96e99e60bca18449e9e2e518af4e8d3058627203a68b00e6ca6801c21c99694a13874a3b326864012124000104672aaf361791adc9e51a604a7825c80d88440002ac68d81ab605f0a942ec27b096c8b8e3e701ba3f98aaa86799dea232a0ebb7a5623be00223a69050716a10e9a696466c02d885af839a535a43c397917e328000000009c296b9682b7827861cb81e2b9628706cd996c92d0000000148caca86f22f52f7a6489f9a6afa83a6a3233446217ca139861865aa66430e2944205895487e07f83f22f12b730eac9c9000020dae1615b80007d7152ca81a3b4559a3c80a80f4e3e0976675aacd46ee22880c786000000b7e03f1750acd22ec783915860785b0458908e000000000020b00001dce862a3f400012dc0d8ad3ca99af2e00b87e83058aa2b09065898c1304056a7843909acc0d3a90651d8d489d3a62230eadb23d7817ea87ae2697d9f22a310c402e81ace6f3285e6bb99425a00602a101e6605b8ee826281f200d9208905ac62b86138e5bd9b848858d80bc50a180608a544e720449b78a1068d1b223a588d60001f6a2cf80000001b1c9b20c620650284bb207589a32c282821c465cb98bcaef973e6fc9f7e5cf204c1061dc8b5913a4a439ce0a720ac2a8d2002b031b967349e620002d542d5058aa731d96735a55e6f982eaa1aaee060e14f83c009d80330a3680c816068c000000008540000668b4308fa71aaaa67b127a0b808f50460800026986b204f1d2000010780000a0c1eb80002dba9540b69dc45ae99c400025a21dc800000000000000000000297c91992eaa2413c68d597a0837ab3c0000000aaf80000001480268000077e864e00000002a680006ed102cbdd0286348226a1c780000000000000063e053014247d978a8fa88e281a13c00000782bba2788b88055a997061665480000002e54552117264f00003a91b4c71c00000000c981219514a218cb40000262833800090d02f84b98f7800000000000d3c00002060001d626328da800021e60000a22a47994e00000000001bbc6a628481a68000b8004dc17a2d2c0001d3c000000056993b8422986869a9dbe8af216000029a4175115485e1b6a6bf1d2a00000004ab16e43360d6ea20ab6c5f480006a8a3c6000000016d80000002a5240c819a733a0be33c00008b2800039c00001aa0c6e79e9df290480000000000ad920203f0000
  | 45 => 0x624ae174068903087ff2880b26800085796e65bc80006dd0d2a71400006b08fa27aa0000a85000090a80003fe27aa508136a0002a681dd82b0017a64200000000000530503925821a043010580005ee80008ab02a43da00000002bae0140ac06dd83f858c985043cac808ffa3e46bc8ace324800000029aa95d03de3b2ab5a25b057618c1fa64c32a3e1d59f746ae06947572528ae89cdcab4ad304d4143a73d05980ec0f540e7814a861882eb990c189b10bcc71bac30b5e023a1e92594b79133eb6c139a1a3a2e0752292c140acb48c598a69628122bd823fa0001b701f926e2a461d80000241e46c0000071ab9c2ba079ea7b00000002d3400019061501d144580000072070092680001fd86cc66fa7960d701662e8988cb6796360002d2641c27501119fc87238770027aa546400dd85651c020001bd200012f811b296a0f103aa1e304e86faa462381000046323962c109e0a882e840069cde9d1a3beaf12f0c5a41cd436b91cea288d7e3902f5863606ce9ca1828a5e02882e7222069f85faab603b83e800006d5af3a7bf89c6783020e8c71d3eb2a2a9aba40000319999a0000000b5280165fd87c6bbf1e26000153eabe950e8969cf65f120840002cc4849868a9240e5661f0d9000004d25a31322bb8982e8e60000191833228a9572299a1ba14716787da186200010b0082951e74627d2147a9da000000012bae2219c8fb2ade000046f85d839fa35485c800000000006422146000125228f000073e8cc675480008558000ab01e128ad0000142144e000278c3bd8e085d214023e6a9c200027ce00011c4a00838a57c1c2e3d99c7800006c088f829a7d586dcb3daa562cd000074b80004ee9eee64c08ca739a3f6b1f01d224b0000505a37c2b31aa642b25240002606adf1a4c6f2993a000172235e850e52f08ec85b9a4495f18fe9ad107c00028c6b9e8000000008c1c8800062c2a04088013e00019881551dac47b03ac000082c5fe98c42d700001139f100001c947b01036a39800000019fe00005c80000e4a22bae0a00000000000000a2d00008f2a43a7311bee20182c635d80002dca0d09a11aecaa4a06c910000000018f21258a90261034400003c20578000746800062f8ebc69295e00002b94b1c979e5ab9dfe9902a6c6ed941293800001ae00000001f64aad94e032416880002bc07a1800000000004e02da000000000001ddaa471e7c5ab117649b980489d041a7458f124788000069958c90080002b12e0878e800000025300000f2863e80000002f700e8ae3a7bf1ae43620d0e1e29092443190c00012d88a72dc81969fe86cf144870a9474146800089b9ae062100005e480005ae18e4656049c1ad00000000000b6d800000008b6bb126e68152c1c315119eb4280005672552b871f2aa3786120b12a4a1ae9f14a2da7ca00
  | 46 => 0x1e22007f8a920bd1196470a2ccc93c141e2c0215a14c870843ba47890b1ab43e78892b419dea170289e4c72ec27f686140180fa60540be0aba18da4241dd8a372f5e5e40d284cb8e46000124c9070aba00019a484a800008d99bc9c82b9e1ad800000006a6ac12d2e0000c9a6071c648ca9fd61d1906884f00000fb8f9486e151066b97042b80a64113121cb6d024031a22f24e6120ab250c46b5f98f60168000a36000015b0faeb398e827281f940fc846e19d8a1a0030c8430b82ae4d083cc2ed2acc9270b8c995225e61198f0b86a87202d2f0e5c181e0045000033e00005302aaa43400002081e145fe094e4b1823255b80a000000000a3124685c05260e5239010209122c92810b58253a0138cc8152ad864fc90f0268852e80d1f52463a4c64ab9134bc88716b4fa83418983c092dabb25a102f019f22fc958298e8a109d08f48d4ebaa8e0006715bea8a1f0692f88867569738bbb244e5420ff286825a874888fc21814fa46e9b9c58e2bf661114269a49a0c702acd6ab792248f993300aa86c435b2650307802807e16e04d89bd0044159632ca5ec58b2b74b9c95b8adfa02e7d398aab9a923440418d43f181244dea54c52407d24e5970a7fb8b9a00b2eea4778f105979b8c2eca7f6af7aa2646a987a7558822b560a4010e20126d797a46528fb89ffae56a35006a7f2a66224e2c081c527daa6c8cc004e80be57a14a2b5b0a72b5eac2e70922926662a9456e8406bd01acaa8b1d6851a8b2ea872ca28b40df44901156911aa9086b24085ed2e9c09410b8baf9f8e5e09482512a23263a8ceead1a1cc901178c9fcaad49830d08174a268592166e2be89a87ad8000b57956c2b480007c72e2813b8a282ca13b224087a8047965c32c271a9cb9b660000e50922218252c281a5fb888c73000006521f7c00027fa6b180003b60cc4a8609960df8efab298e48693826858d1e3271c8e94b3896c45838dee0c602cc7980382a7883dc8322b005e5831c4709950000066601c00004448af02620000873a40a60d000074e200a2399724633064abae15ceba50d40948090cac7a4646f517b6987000072312fc2e098a89e7980c7de225094707043a019c2a4325e470f0a2672f00f04fa154ca5c174c9890cdc85f94fe836a6204cb2aec1d91a1e2c1891c3cd00003832a88135800083511ac00016ee6b49d90a7a8c28a7422041ce24f88442d90b60a97a115297e09288c40001b866fd96e8066052400020600e19ff49e6a1289a2826a8140000371a4ba0101df6000152e3408000094815200015443f4233600012e49562dd003680003f09d941b5a4f25db8a3484c8000000223800013320e10000387a29897a142400010b41518e322a600009af219a0001af400006ee6a002d83ff90e23f9026e8c417d68348000619a9ee00000004f388a285da9
  | 47 => 0x49240781fea391c12ac3800085384e4000166cb70a988469092e027055e7678e8822f871237e80c099d08282f4048c05d800080e2174ac419b66d60d8c0000b789591606358816c7b8a506a8c17024f28000a4c9d7a9dc9042000007a0aca3a28200ab629b26d841a8d8a0b202c0000000096d00008f6acfe3d024c00dd9348acfa39284c293e14e25ee4d38d9489f1e30b948ac61901a2aa5a0000abc05b8552862200018d26190fd21ba9284000167c0001ad47e59d10000051646ca90299f800043f00008f800000a98d5419e123c0001b6c6008b14000271cacd946c048032002593f66e203103cd8a0ea4880764689d4a883087c00c89d4854290453f0d269b0919c7b913f891692b278b14a6a549fc09c08de825c87dcb1f96b24c1a3f8000269800019d40000690869a4e65b8838e18a259e6292e9895590a07a02450aab28a68e910aa67802464af835215a84665c6a3d87ca01061249ae2576842e56095b616d13da4e89264a98a0a42c5aab0a8415287dba75aaa8a2dc23a1e64708a3e272884142a294868ce28b0a6b10483171f1eab12a4043b211a766a05880aa2eeb9c0a744bd90d62078f2e8158080971258e1f5808aa2e88f6323010058aaf0a5b3af563c88604819053cb719dd0266aa420399f184dda7c67e71d2c8300c5e34695d0793a5c89df80006428cbc0c6800000027702c9a7900001370789086e95d8472952010e000209200000000001e02b6000005a2ab1843825dc61d8daa8641dca7062a5c0c88000945800000007a20001be48a584f6a0bad1a4d70dc80002778000000000028ae5cc80007a3824448d80004ce8000af999ba9ae834c7882cd0b9783a88510390ad8a47e4941f5e34180e2085a09400025440000000a70204a0001b4a000260492ba40e79c0f98970a9d837c9f3656392e87519ce403fa1405940326273a7cc2462ae0095a73e35d0b1a138183a00000000001d92a2820ca34625f8b2aa1a29b328842381c1e986030c406845600013dc28ea7dc859a68e3770a58000000082280004db2c8800002c21cc0c062e51e34b24855257b80000f181740000d462da26ee76726be4170c308d600c66658000028828a0f5977600002981a924debdf2f4a6d22e6eab20f047100ee683c1c3047985f62321e100dc84c46d511ca1c6860a9fd1e0400000008b629f23e2945221328fa00014f0ae98940912800033d0bea1e6086200009fa5470000207099c8e12ea0153ab6621d23de73400ce477113c5588e345a717e29359a1a8cc80c2248ae4e00000545492b4871a000000000001328fd64df8000000000000001f4b7c1d84bc1848891c29c456ba43ebd4a0f204c897e57d0dca25a28e244b8ea8aeeae4801d132459613922f012c87921ed40f827c01600e782c71e787b09e1c48c14e218baa223838ea61
  | 48 => 0x44a076075081d48f32f1e6fb00002589aba6c127e478e0cca19d10e4aee2052123800071b06e6155aec69fa0db2762ab985611e9e0000000836250058484be0601f3a0002a2a595941432d80008891fb88e02688000012a91ba67a7d628760e580004df070c2d781cc6c9adc40ed049049d86885268d3a67d9274084894c265155221c9b9e4faaae6957154e6ea08a40000f2a00021b6a348f903ec046a7d68ef0b2f9cea1bb17d000019b21011d8e4cd0d5c0001fd0ad600009eb00007098000b2305f200000002149e4009e12662d5a00c4ad21480000000069294c92a12bcbb00000000000049c1568000178ea358bc40b99f044b1280e00025e200009cc0000000a1984b80a3912a9dd8bba9cd09aa0000a7a5a3aba867b8bbe0e00e1a3472c68b8c26e4983961000010ceb8d82dc02ba17c0000000000000000028cc08b00001e727d8b0685641200ab23002592b3918c202f23309152df81b413e0000000000000006e915de664022600010f4a6f88ee0002e4a000238e84e00000001c60a251390b5491c07012e068171216000130eb3c2898511a18829827d036d961814f90ca403977c029923e99622722fd037a0fe800a3850004ac9af5c1a319326cc04b26c3801ca02815448e1a0a757aabc5b7a2e4660949613f0b2a9672b4a0500f64870a19637c238a62019840002b6e127a2804e2aa58742a7f000000007c9110a3a3acfc000108c00012f291a80003ee9f160000f8c5ff166492900006d711a835e2d8481200004ef10da0001b900002a801af8936859218c1a11652323984c0df166a6218e02826ab445a19b2e1878c0a9809c368eb8a70b09a72a0000144bb3a41477f2a3cb589ed22dd0fc4a4d8c4c586a52c8b8a59a9e282ca144000023c99ce81a8ebaab8ac48b23ad1803b9afe8eda374000130aa9900000000000000000086c988e0002b820000fce4aaac6424c80000002a82000163e00002760e3181452a800034f8000000000000009e857a945a0dbaf006f683a000009dc2441ac497ca19c1971b8e36f15469609674000263a0002a1608329289e3a83c52b80e00001a9a7408bee0000dec0000000a7d00008258000000000000000000002706b17048a83b81e870710c600009808a30000295a0cc7ab1a940c909981db90241e2030296c2a125cc27320860000000198c7a8098e4e82c84a019f765a99936000000077d03e642180004202dd222681c42da8000a53ac5872d90620002386b6f119400015d4591282830d0f3272c22ea2cb00001d89e085968c96bc400001b697720a884207800c881cf0f5a9c10000bbca5fea4d172c779a9e646e1a06680a13621080009e6042c88a000000028606700000000299e000207801988f400016fa5b6a1e87af8ec2000000000000003541054000236eb7f8b8621194e80001
  | 49 => 0x8e6612507f424eaceeb440086acb8db08b21db61759cf85a7845800015181028000000282200005f43338f303ea1ca881d8bbc560000020c14785dfaf0400015646d8222e0112b200b91cec38aac54a6325e08428bd86b9805cba01d1c85624bc74c11b470eaa38498a47200000000000bc2464192eb0e266ebb30000000224240f0f146261a58844949c2511b24afc00007ba000003908aa75b9be00efa07299a00000001d7447a96d600000002f70dba77721dcb0026522558c3200002824ca0388000000047a00000001fa479400004a808de5c822c466e1ec84b38e4c284800061d15c06d88c44adc0000593ab6aaa19a5200023ce466129057f03505c78dd60562c3a8ee8af400200002642850000115ebc6274a303804643e99a25d59b0200019d05109c0898b0000bb9a01aad39c7a845a4b013f94f49ec9e8a322abce00491c618e83f42749180555241063e2cbc1eca1be5618088813905e7ed222cba98c105329f444d78a48ac681b225420e4ab3a522012817067a1f2c5d1007840f8ec6628a5267fd9e7e6c619dc8ef0bac5c71dc639501848aa81361b8847a9a9a3469b01352a451320706900c6c693fa93913d890a1cc215f01de70e15b4899117885a00c4b6525a60af02e89eb9fea57080182d1907a89e9ac800019764ed0000431066c77c0b36000287497c2a1a6dc989e0000000000128e9659c480002adc1148c560000000a9f80000000cf682386bc0000000b4e80007de9752bb62eb686f17a20c29a6200017f2baca98400005da7318cba9088000000206ea66800000000000000e7a0291b08000220e0000000000244c000163ca6e9812bb400007ab8f8e3b48aa000025429172742aca2dd60002f54bc20000000000080f86c69968b84a049b7a496a7b88e680008401c3251f213aa4e800040005a26342ab2b3d279ca3b2a6029413385da000098a1d60576234892b18e2787a2b6534ade678f93148218544b77938451307b458908140678400107167a51ca0a6a7781fc2240000000000096f00009e90d380000a142af00001c6000037105b27431d829cf09d6a570000000000000003c865c0000bac000000027264da09ee84fa616944010c7960ab0000124e4eba7ba0001c74000000062400003e59c5289021025282bea301257a62d2a0000005f8453a39469ea1f60001f0c24980006229da2b668000026a69e0002f6494520e266505c415988ac43a0f189ce12c24a29c0c0000000676292e69a122c2e4a6124f08c6a5fd1ba6b4a989a230040c000000058500009a00fda4a6185a6e01fac2429170391206252d854c7400d70461052c23a81125f7065e0c594d8ace15ac52295b05390dbe7368f7437522c2943200809e99b4a7f8cf2327139446dac7a88f1d1e0b8a4968ff07cc03b2824a2593d48b500002aba6d4
  | 50 => 0xc59fa98a037036467e93f0741128687c006c86904508a8114638ba3706649ed692380007748a3e6ce1b9200000009ba87544f914b45f92a502d00000000000026f85c69c512043390e8c032033e0082dba2a0aa74000000000029a267e00008de83fe0000f1e9f200001fb12721a1a76200010ae19f964c21212ca4c60e609298000000053a000000083e0000000162200029389958aaca0000000002248a641bce31f090437f8d2c2a39ea40002ddc0002d8a28b0000042a4a00000000ad580000002980595050000010f60000a806cc800081096162bb0428a73aed4914ae044270dfc1959a502f88dac610134602a0a3235300000000e060000ba811f000000029260000572ab90000000246c4838e6800000007e498dc0002ca49c61d980ae202458c125c316075ca52896447f9db8000077e98b9b3400000001c80000000291200000001da1cbea3f9a640001d405f500000000000721800080980000000c5223682b4afead141322efab3e9f3874a1cfc13d21b43949084568a21a87b0bc820e93a8b378eb84b82b68116ac3eb060e5c84b16fc3bd0000bbb800029d99a09179e222b9060815f9b4635909eab4080000001afa4bb8ba43d4800000012fe0001940373ac5ab660ed0961a25295290a23ff2304a022748432026cb54122636625be54d0a9e28e1f721639a4008789286be1a8805c8000409ae5c9ff25181911eb008423443a112cc1a8077c2a18260906a1425fb26080d7a8ea9b7270001f99349b6800070f8000000238800516b004580006908130ac909ba1078000544a956000000000026ec090a4069ada23a96e182a97f16b41ac0680190aac23c18ac816b1c425aaaf3c5988000329a8f25ada7c238400008d6a4d847c00006820fe20f2a51287a8d246a12ba015c000000000005b7000088d1fd860004f291f011c8de0abe1bc2f4c4de2da41de057a00000007b421fa0000a0a05aaaf415400009db885c0000b08b328e3c00017941b2153c55a91a60000000960000000000003381b5a0000fec000059c00021ca5f0835a2ba893000020e09b480009622e34000255a3401e0a13e00004aa23ec29b800053ba1c697e8000a83000001f2dcaa7e17160001ecc2000ada1f4102e14da77a0cf251e5f2140ca51974e18e2d489d518b81ca925e4c42da2b01aa469d80ad68850d106cb2aa04731dee369a372ba584b083b07c4a5001ce94129b410e88cc7ec9c9e3dc92a408e2df47ed888a2f589203c9011a6ca1470bcb14a856a24a27fcae9a05ea6e890e2c14b489ebc309a04678dad447f703d88038a5e86c126803c8bfe38c0dea2439c001faaf6c0bf11068ea8b589bc885e0fb2d367b71e46b91122eb7d994c8ca256e10ca0e845a1c545540e622279a1c189023c0bdad4c8059f30a368ad05b622463e20d2200400005ba
  | 51 => 0x58a1308183979810d04aa77a0caeaf70de00cb28bc2891c96ad7aed20002e2a9d60a2e3682efebc098e00002adaaf30cb8000000021002ba81f10fe08d186c09c21c88c917ac6f1211c0001be221dabf4667a12e89c1102b0480e8ac29944a2a1d3256400000fa21540e722f664a19fc6ec00004cd827c229829e1ab14cc2e2078e9cda1aaaef13ac000230833b1ed870d0f38b3c9dec1ba174a00000001640ca48a6a584000061a4a00000000256a00002000001fa87419e9c00024aa2c38ea0000000000000003d3000000024920001b3a3eb11380001a5c87621f43efa75e0001a260002cc09d1000062c81b42908d0a74d251a7d824327c28bf0ac5157832b143448a916606a2b8e0001a5409d261000016f400000005e0131e4f20c0202b22b85312bb419e907ea151b1242e8000646955c419a08c93e9356847ae6
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xcd570c4163084111bd0f082c6108023761e1058c215b56ac0c20b184200a5f8544163084014b90a882c610802a7e111058c210054e42220b184200e57854416308401ca90a882c610803a5e111058c210074a42220b1842b6ad782441630856d5ab04882c610adb95d491058c215b72aa9220b1842b6e9742441630856dd2a84882c610816b5e011058c2102f69c0220b184200cd7704416308401da4e0882c610803355c11058c2100768b8220b1842b6ed220441630856dda240882c6108161f2177654c2102c7a40aeca98420587c87595530840b1b90eb1aa610817351c56354c210063ab2ee2a984200cd563dc5530840b17909bb286108163720f7650c2102c7a40aeca1842058bc87591430840b1b90eb1a8610817351c56350c210065ab26e2a184200cd563dc5430840bca862b2a6210817a50c5644c42102d6a40ac69884200ccf83dd9210840199907bb2421080333cc3764842100666986ec9084200ccf76dcd210840199eec39a4210802f260073484210056d41eeab004200ad983dd5600840b5e503baac01081abc60775580210055d420eab004200ab9841d560084015b5063aac010802b660c755802103d75410eab004206ae9821d5600840b5e5023aac01081abc60475580210056d41ee8b004200ad983dd1600840b5e503ba2c01081abc60774580210053d428e8b004200a79851d160084015b5063a2c010802b660c745802103d75410e8b004206ae9821d1600840b5e5023a2c01081abc60474580210071daa4a8b004200af381551600840b5e102aa2c0108038e550545802102d7940ee6b004206af181dcd60084019e2e3b9ac010ad2b661e735802159f2da94e6b0042b3e59529cd6008567d368539ac010acfa650a735802100768b8ce6b0042b3ed2219cd6008567da24339ac010ad6bae09735802103d74412e6b004200cf1715cd60084019b70eb9ac010803b2e0973580215a764412e6b0042b4cdb725cd60085699b2e4b9ac010ad396d4973580215a72ca92e6b0042b4e9b425cd6008569d3284b9ac01080336dc573580210066cb8ae6b004200ed1715cd60084019a2e2b9ac010ad3b488573580215a76890ae6b0042b3ada831cd600840b5e50239ac01081abc604735802103d75416a6b004200ae982d4d6008401cb6a729ac010802bce05535802102d7840aa6b004200aba8414d60084015730829ac01081ebaa0b435802100574c1686b004200af38150d600840b5e102a1ac0108029ea1443580210053cc2886b004206af1879c5600840b9e30f38ac010803b49ce715802100768b9ce2b0042b2af1829c5600840bdc30538ac010acb9cd4a715802159738a94e2b0042b2eb3429c56008565d628538ac010802aea1351580210055cc26a2b004200a7a85d0560084014f30ba0ac010817b40c53158021
  | 1 => 0xee4982c8108bf275c930590215a70fa9260b2042b4e1d524c16408401d3700982c810ad3a688130590215a74c90260b2042b3a9e830c1640840b56d02182c810802ad60430590211ae5bb9620b20422fcb572c416408565c6ea5882c810acb8d54b10590210074b98620b204200e9530c41640840153d07082c810802a760e10590215b55ac0c20b204200e9930841640840117f0e882c8108262f21d10590210051fc2a20b204200a3c854416408401d3260882c8108032de1d10590210065a43a20b204200e37854416408401c690a882c8108d72ddc9105902117e5ab9220b2042b6e3752441640856dc6aa4882c810816ade01105902102f59c0220b204200e97304416408401d6460882c810803a54c110590210075898220b204200e9130441640856dd6440882c810adbac48110590210061e2a6ecaa04200c3c545d9540840b1e902bb2a8108161f21d655502101d1e422caaa042058bc8759154084094790ab22a8108031d59771550210065ab26e2aa042058de87d4d63084018beeba9ac61081eb3a0b5358c2102c6f43e86b184207ace82d0d63084031b907b82c61081e3b2097058c210066d982e0b1842058de878c1630840b5ad03182c6108063721d3058c210066db8260b184201cf2704416308401da460882c610803b44c11058c210062fbaceab184207ace829d5630840159b053aac610816b52057558c210054f420eab184200a9d841d5630840f59d053a2c610802b360a7458c2102d6a40ae8b184200a5e851d163084014bb0a3a2c61080387d525458c210056bc0aa8b184205ad4815516308401c3aa82a2c610802a7a135158c210054ec26a2b184200a5e85d0563084014bb0ba0ac610acf17d4b7058c2159e2ea96e0b1842b3c9f42dc1630856793a85b82c610acf358877058c2159e6a90ee0b1842b48dd879c1630840b5ad03382c610802b56067058c2100567c12e0b184207acc825c1630840199f04b82c610ad3332097058c215a62fa92e0b1842b4c5d525c1630856993e84b82c610ad3275097058c215a66b10ae0b1842b4cd5215c163084019b700b82c610ace37a1c7058c2102d6b408e0b184208ad5811c163084011bd0f282c6108023761e5058c2102d6b40ca0b184200ad58194163084011bd0e282c6108023761c5058c210054f420a0b184200a9d84141630840f59d04282c610802b36085058c2102d6b408a0b184200ad58114163084011bd0f202c6108023761e4058c2102d6b40c80b184200ad58190163084011bd0e202c6108023761c4058c210052f42880b184200a5d85101630840f59d04202c610802b36084058c2102d6b40880b184200ad581101630840b5af05882c610acab560b1058c215972ba9620b1842b2e5552c416308565d2e85882c610acba550b1058c210066bb8620b184200
  | 2 => 0x2745942102d3a40ae8b284200c3d741d165084018bee739aca108169d20573594210051f420e6b284200a3d841cd650840f4dd05a1aca108029b60b43594210043f43886b28420087d8710d65084150fd0fa0aca108021f61f41594210052f41ce0b284200a5d839c1650840b4ed03382ca108029d60670594210051f420e0b284200a3d841c165084014bd06382ca108029760c705942103d37410e0b28420aa6d821c1650840b4ed02382ca1082a9d60470594210052f41c80b284200a5d83901650840b4ed03202ca108029d60640594210043f43880b28420087d8710165084014bd06202ca108029760c405942103d3741080b284200a6d82101650840b4ed02202ca108029d60440594211f62fb9660b284238c5d72cc16508567c3e85982ca10acf8750b30594215a52ec1c60b284205a76818c165084014eb03182ca108fb17dc930594211c62eb9260b2842b4e1f424c16508569c3a84982ca1080396e0130594215a72d10260b2842b4e59204c165085674bd06182ca108169da0430594210053ac0860b28423ec7772c4165084718eae5882ca10acb8dd0b10594215971aa1620b284200e5730c416508401caa61882ca1080297a0e10594210052ec1c20b2842b6a75818416508401cb261082ca108021fe1d10594210543e43a20b284200a3f84441650840147908882ca10803964c110594210063bc3a20b284200c74874416508401c6f08882ca108038d21110594211f63bb9220b284238c7572441650856dc6e84882ca10adb8d509105942102d3bc0220b284205e73804416508401cae60882ca108039c8c110594210072a98220b284200e71304416508401ca260882ca10adb9c88110594215b73890220b2842058be87d51640840187eebaa2c8108162fa1e435902102c5f43c80b204200a9e83901640840153b07202c810816ada06405902100c5e43a80b204200ed130441640840187eeb3aac810816ad20575590210061eba8eab204205ab4815cd640840147d0a39ac8108028f614735902103d57416a6b204200aad82d4d6408401c3ea729ac8108022fa1c53590210045ec38a6b2042098be87d45640840117b0fa8ac810802a7a0e70590210054ec1ce0b204205ab6819c1640840156b03382c8108028fa1470590210051ec28e0b204200a9e831c1640840153b06382c81081eaba08705902104d56c10e0b204205ab6811c1640841356b02382c810802a7a0e50590210054ec1ca0b204205ab681941640840156b03282c8108022fa1c50590210045ec38a0b204200a9e83141640840153b06282c81081eaba08505902100556c10a0b204205ab681141640840156b02282c8108d727dcb305902117e4eb9660b2042b3e1f52cc16408567c3aa5982c810ad2a760e305902102d5b40c60b204200ab5818c1640846b93
  | 3 => 0x6a924200e5510d8d52484b94df04b1aa49093697a186354921297a2108c6a924200b598018d5248401ca8c7b8aa4908039518c71549210054fc1acba124236a9c8359742484a553d0db1e849093787d4b63d092126f0ea96c7a124200a9f80d8f424840153b01b1e8490803a5c4363d09210074a886c7a124200b998018f42484758d8eca9284908eb8b19152509214672631aa4a124200cd463dc542484019a8c638a849080359548715092107556c14eca124200a9f835d9424846153906bb28490846abe0976509210054fc1acaa124230a9c8359542484a553d0db1a8490937e1087635092126e4fb96c6a124200e8f72d8d424849bc3ea5b1a84909378754b63509210054fc06c6a124200a9d80d8d424849bd1e41b1a8490803a348363509210074b886c6a124200e9510d8d42484b355f04b1a8490936a7a186350921297c2108c6a124200b998018d42484635590ca928490a33a318d5250921005d240aa4a124231e2f865494248463c590ca9284908eb8bdd952509211d7163b2a4a124200f0f635494248519c5cc6a928490a338b18d52509210078631aa4a12428ce0c635494248401e4f02a928490803c9205525092103f17b0aa4a124207f2761549424856fc5ec0a928490adf8b58152509215bf87982a4a1242b7f0d30549424856fe4e20a928490adfc944152509210074a31ee2a124200f2552dc54248401d28c638a8490803c954871509211ce363b2a49924239e4c635493248461958eca1264908c3a318d424c9210066bb18e29924200d65521c53248401b4a8438a64908027c600714c92103c3fc3acb28a42078bf8759241484055ad0db1c6290803359db638c5211ff2a31ea518a4239e546354a314840fac8e4a946290937d18c9528c5211b74a31e8518a4230e946350a314840fb48e4a146290803c9549428c52126fc31928518a424dccc72d8d314840b5ad03b1a62908063ba1b724c5210a56b436e698a4202cd476dcd31484055ad0db1a6290937351db634c52126ee3b98e498a4207c7476d49314847fca8c7a92629081f1d1d9524c5211cf2a31aa498a4207d6472549314840f968eda1262908dba518f424c52103e5a3b28498a4230e9463509314840fb48e4a126290803c9549424c52103cea43a6498a4202ad4864c9314840f9a8ec992629081f711c9324c521007a2a926498a4200f85424c9314840f8dceda94429081f1b9d952885212e72631aa510a4207d667154a214840f95ceda14429081f2b9d942885212cf4631a8510a4207da67150a214849b99cedb1c429080b339d86388521005e4c00c710a420587e87951650840187ee92a2ca108161fa1e53594210062fb9ca6b28420587e8794165084014bd07282ca108029760e505942102d3b40ca0b28420187c875416508401da260882ca108030fdd
  | 4 => 0x34849b59d04286c690802b360850d8d210056b408a1b1a4200ad58114363484011bd0f206c6908023761e40d8d210056b40c81b1a4200ad58190363484011bd0e206c6908023761c40d8d210052f42881b1a4200a5d85103634849b59d04206c690802b360840d8d210056b40881b1a4200ad58110363484011bd0f106c6908023761e20d8d210056b40c41b1a4200ad58188363484019b6e1106c69080336dc120d8d210066bb8621b1a4200cd570c43634849b1bd0f086c6908023761e10d8d210066db8421b1a4200a5f8544363484014b90a886c690802a7e1110d8d210054e42221b1a4200cdb704436348401caf0a886c6908039521510d8d210074bc2221b1a4200e94844436348401da700886c69080335dc110d8d2100769b8221b1a4200cd37044363484019aae0886c690803b41c110d8d210076910221b1a4200ed12044363484011bd0e086c6908363761c10d8d210076888021b1a42018f481dc163484010ff0ab82c6908121f2157058d210045fc22e0b1a42038bc845c163484011bf06b82c6908023be097058d2100c6e43a60b1a4200cdb704c163484031e90e882c6908033cdc11058d210076898220b1a42008dd809d863484011bb0f328c690802a7a126518d210054ec24ca31a4200acd8299463484011bf0eb28c6908023761e6418d210052f42cc831a4200a5d85990634840159b05320c69080237e1d6418d210066d432e031a4200cd8865c063484019b6cab80c690803369957018d210066cb2ae031a4200cd8655c063484019b6c8b80c690803369917018d210066cb22e031a4200cd8645c063484219b6c4b80c69080374a057018d21006e8c0ae031a4214cdb615c06348401ba642b80c690803740857018d210046fc3ec031a4200cd970d8063484011bb0f300c690802b56066018d210066cb84c031a42008df8758063484014bf0ab00c690802972156018d210054fc22c031a4200a9c84580634840159f04b00c690803365c16018d210146f438c031a42008dd8718063485715ad02300c690803365c06018d210066b3b62031a4200dd170c4063484a55a90c880c690803359d91018d21006e8b822031a4200ed36044063484011bf06bb2a6908023de057654d210246f43ec6a9a42008df835d943484011ef02bb2869080e37a1f6350d210052fc1ac9a92423fa5c8359352484a54bd0db1ea49080297e0363d49210052ec06c7a924200e5710d8f5248401caa21b1ea490802d660063d49210066a31ee2a924200cd4631c5524841f4db053b2a49080297e0d76549211cd2e41aeca924212a6f825d952484014bf06b22a4908e69720d64549212952f436c6a92424df4421d8d524849b8bee5b1aa49080393dcb63549210052fc06c6a924200a5d80d8d524849bc9e41b1aa4908039348363549210072b886c
  | 5 => 0x803365c130d8e2102e79b8221b1c4200ed13044363884010ff0ab82c7108121f2157058e210045fc22e0b1c42038bc845c163884031b90e982c71080336dc13058e2100679b8220b1c4200ed130441638849bc9865b1aa510aeb93cc96354a2126f46196c6a144205cd47158d328840f8eaeda94631081f1d5d9528c62126fa2192a518c4207cb576d0a318840f96aeca146310937e10c9428c6211ff2a31ea498c4239e5463549318840fac8e4a926310973d1cc9524c6211b74a31e8498c4230e9463509318840fb48e4a126310967e1cc9424c62102cea43a6498c4205ad4864c931884039b4e0986ca90803365c130d95210076898221b2a42028de87dcd65484018bea5b9aca908023760373595210066a39ee2b2a420087f855c1654840117f08b82ca9080e2f21170595210046fc1ae0b2a42028dc835c165484011bd0f982ca9080a3721f30595210046f43a60b2a42008dc874c165484019aee7882ca90ae3351cf105952100c7a43a20b2a4200cd77344165485739a8e6882ca908033cdc110595210076898220b2a4201cda704c364484019b2e0986c890803b44c110d91210146f43ee6b224200c9f42dcd64484011bb01b9ac890803351cf71591210043fc2ae0b22420487c855c1644840117f08b82c89080237e0d70591210146e41ae0b2242008de87cc164484051b90f982c89080237a1d30591210046e43a60b224200cd773c4164485719a8e7882c8908063d21d10591210066bb9a20b2242b9cd47344164484019e6e0882c890803b44c110591210146f41eecaa242008dd83dd954484011bf06bb2a89080a3720d76551210047bc0aecaa242008fb805d954484031f100bb2a89080e1fa1f655512101d1f426caaa242048be87d91544840947d0bb22a890803175d753d8d210056ac0c61b1a42018df874c363484039b4e0986c690803365c130d8d2100679b8221b1a4200ed2304436348401da260886c690802a7a1265d8d210054ec24cbb1a4200a5e8599363484014bb0b326c690803365c360d8d210066db84c1b1a4200a5f8558363484014b90ab06c690802a7e1160d8d210054e422c1b1a4200cdb70583634841b1bb0e306c690803365c060d8d2126d6a43221b1a42b9cd6764436348401ba6e0886c690803b4d8110d8d210076830221b1a4200a9e849d7634840153b093aec690803175d475d8d210052f42ce9b1a4200a5d859d36348401c3ea92a6c6908038755054d8d210054f426a3b1a4200a9d84d4763484014bd0ba0ec6908029761741d8d2106d6b40ce1b1a4200ad5819c363484019b6e1386c69080336e0170d8d210056b408e1b1a424dad5811c363484011bd0f286c6908023761e50d8d210056b40ca1b1a4200ad58194363484011bd0e286c6908023761c50d8d210054f420a1b1a4200a9d841436
  | 6 => 0x51f428e6b264200a3d851cd64c8401c3ea729ac9908022fa1c53593210045ec38a6b264200a3e85dc564c840147b0bb8ac990802a7e0d71593210054e41ae2b2642008be87d4564c840117b0fa8ac990802aea0031593210055cc0062b264200a9e839c164c840153b07382c990802ada0670593210055ac0ce0b264200a3e851c164c840147b0a382c990802a7a0c70593210054ec18e0b264207aae821c164c842b55b04382c990856ada0470593210055ac08e0b264200a9e8394164c840153b07282c990802ada0650593210055ac0ca0b2642008be8714164c840117b0e282c990802a7a0c50593210054ec18a0b264207aae8214164c840155b04282c990802ada0450593210055ac08a0b2642b3e1f52cc164c8567c3aa5982c990ad2a760e30593210055b40c60b264200ab5818c164c8569c3ea4982c990ad38754930593210074dc0260b2642b4e9a204c164c8569d3240982c990acea7a0c30593210055b40860b264200ab5810c164c8565c6ea5882c990acb8d54b10593210074b98620b264200e9530c4164c840153d07082c990802a760e105932103d5741420b264200aad8284164c856d56b03082c990803a64c210593211045fc3a20b2642bb8bc8744164c840147f0a882c9908028f21510593210074c98220b264220cb78744164c85779690e882c9908038de1510593210071a42a20b2642b6e375244164c856dc6aa4882c990803ace0110593210074b98220b264200eb23044164c8401d2a60882c990803ac4c110593210074898220b2642b6eb22044164c856dd6240882c990802a7a0c10593210054ec1820b2642b2ab68104164c8401878a9bb2a9908030f15176553210046fc1aecaa642028dc835d954c84011f700bb2a9908063e201765532103c3e43acaaa64203a3c8459554c840f1790eb22a9908128f21564553210063ab28e2aa64200cb5641c554c84031b90e982c79080336dc13058f2100e7938220b1e4200cf17044163c8401da260882c79081e1f2177654f2103c3e43acaa9e4200c75651c553c840f17909bb2879081e2f21d6450f210065ab20e2a1e4200c6d65dc951c840195ac9b92839081f1b1c9654c7210072a18aca98e4207cac7259131c8401d2862b2263908031b597724c72100656b26e498e4205cf3105c365884039b4e0986cb10803365c130d96210076898221b2c420087f855c1658840117f08b82cb1080e2f211705962100679b8220b2c4200ed130441658840b9e620b86c910807369c130d92210066cb8261b244200ed13044364884010ff0ab82c9108121f21570592210045fc22e0b244200cf3704416488401da260882c91080e1fa1f655522101d1f426caaa442048be87d91548840947d0bb22a9108063d60570d8e2102e79882e1b1c42018df874c363884039b4e0986c71
  | 7 => 0xd6861c5324c401aaea438a649880355548714c931006cba10e29926200d95421c5324c40b3af0038a649881774a00714c931004eac00e29926205dd1801c5324c4013a30038a649880335d80714c9310066ab00e29926200c5f65dcd514c4051b90cb94629893733189728c53102ee310ae518a623fd5671d4a314c49bc98c4a9462988e7559c5528c5311b6cb38e8518a624de8c6250a314c461b2ce2a14629881e1fa1e54597210061fba4a8b2e420787e8794d65c84018bee729acb9081e1fa1e50597210052f41ca0b2e4200a5d8394165c84014eb03282cb908061f21d50597210076898220b2e4200c3f749d165c84014bf06ba2cb908029720d74597210053bc0ae8b2e4200a7b805d165c84014f100ba2cb908030f5d074597210062fb9ce6b2e4200a77815cd65c840147d0839acb908028f61073597210043f43886b2e420087d8710d65c840147d09b8acb908028f61371597210052fc1ae2b2e4200a5c835c565c84010fd0fa0acb908021f61f41597210053d40062b2e4200a79800c565c84014bd07382cb908029760e70597210053b40ce0b2e4200a75819c165c840147d08382cb908028f61070597210052f418e0b2e4200a5d831c165c840f4dd04382cb9085a9b60870597210b53b408e0b2e4200a75811c165c84014bd07202cb908029760e40597210053b40c80b2e4200a758190165c84010fd0e202cb908021f61c40597210052f41880b2e4200a5d8310165c840f4dd04202cb908029b60840597210053b40880b2e4200a758110165c8567c3e85982cb90acf8750b30597215a52ec1c60b2e4200a76818c165c84014eb03182cb90ad387d0930597215a70ea1260b2e4200e5b804c165c8569cb440982cb90ad396481305972159d2f41860b2e4200a76810c165c84014eb02182cb90acb8dd0b10597215971aa1620b2e4200e5730c4165c8401caa61882cb9080297a0e10597210052ec1c20b2e4207a6e8284165c84014db05082cb90ada9d60610597210072c98420b2e422687f8744165c85790f90e882cb908028fe1110597210051e42220b2e4200e593044165c844d8ef0e882cb90af31d21d10597210071bc2220b2e4200e348444165c856dc6e84882cb90adb8d509105972100739c0220b2e4200e573044165c8401ce460882cb90803954c110597210073898220b2e4200e513044165c856dce440882cb90adb9c48110597210052f41820b2e4200a5d8304165c85654ed02082cb9081e2fa1f54593210061fbaea8b2642078be8790d64c840f17d0f202c990802a7a0e40593210054ec1c80b264200ab58190164c84031790ea02c990803b44c110593210061fbaceab264200a9f835d564c840153906baac990802ade0575593210055dc02eab264200ab8805d564c840187aea3aac990802ade0573593210
  | 8 => 0xab82c8988121f21570591310045fc22e0b2262008ef825c1644c40f1d904b82c8988063721d30591310066db8260b2262018f487441644c4019e6e0882c898803b44c1105913103c77416ecaa262008ed82dd9544c4031f5013b2a8988023e602765513101c3f43ecaaa26203a3e84d95544c40917d0fb22a8988128fa17645513102c6f436e6aa26200c5f65dcd544c40b3ad03b9aa89880a3da1b7155131014eb41ee2aa262059d4831c5544c4010ff0ab86c4988121f21570d89310045fc22e1b1262038bc845c3624c4019b6e0986c498803b24c220d893100536c2841b126200aad84083624c40159b06106c498802b960420d893100679b8221b126200ed130443624c401dc440886c49881f1b1897598931006aa18aeb3126207cac625d2624c401b2862ba4c4988031b5d7629893100656ba6c53126200d54315d4624c401b2862ba0c4988023be1d621893126e6db1ae03126200dd0315c0624c40f1d904bb4a49881f2b1897494931006ca18ae929262059d4815ce524c40195ae9b14a4988167520e719493103c7a432e329262029d4835c6524c40717d09bb2a4988022f61376549310066a18eeca926200cd4311d9524c40f0f90eb2aa49881e9b20965549310247743ec4a92623aa3e84dd9524c40147b09bb2a498803950c7765493100536c14eca926200a6f825d9524c4014ef02bb2a498803950c4765493100537c12c8a926207a6c82591524c40f4dd0db12a498aebd10c762549310253743ec4a926204a6c87d89524c4014df01b12a4988029b60362549315d727986c4a926200e4d30d89524c401cce21b12a4988039944362549315ffa2188c4a926200b6980189524c535e2863a9684988038bd8952d093103f16312a5a126298f143154b424c40f1d904bb4849881f1b1897590931006aa18aeb21262059d4815ce424c4018daebb1484988167520e719093103c7a432e321262029d4835c6424c4090fd0bbb284988021f61776509310066a18eeca126200cd4311d9424c40f1790eb22849881eab209645093101c7743ec4a126231a3e85dd9424c40147b0bbb28498803a50c7765093100556c14eca126200aaf825d9424c40156f02bb28498803a50c4765093100557c12caa126207aac82595424c40f55d0db128498afbe10c7625093101d5743ec4a126203aac87d89424c40155f01b128498802ab60362509315f747986c4a126200e8d30d89424c401d4e21b128498803a944362509315efc2188c4a126200ba980189424c401c5ec5a92849881f8b18b52509314778a18ea4a126200e2f62549424c40fc58c4a928498a33c3cc952509314678a18aa4a126207c5c76d49324c40f8b8eca92649881f93189524c93103e4e3b6849926207c9c76509324c40fd18c4a126498802f4600714c931084eb430e29926205c
  | 9 => 0x7454a413c59c402e8a948200a6f8258d529040f4d904b1aa5208c70f9957550a41104dc402eaa1482078be87d95429046153d07b2a8520802a760f6550a4100556c16caa14822faba80d95429040157301b2a8520802abe016250a4100556c02c4a148200e8f305894290401d1a60b128520803a9c416250a4100752882c4a148207c3f76d494290401c5ac5a92852081f0fdd95250a4103f17312a4a148200e2d62549429041d17b0db8a85208024f6177150a4100752b16e2a148200ea5621c54290401da260886caa08021fe1570595410045fc22e0b2a8200cdb704c165504039b0e0982caa08063d21d105954100679b8220b2a8201cf0704416550401da260882caa080637e1d30d8d410066cb8261b1a8200cf3704436350401da260886c6a08021fe1570d89410243e42ae1b1282078bc845c362504019e6e0886c4a0803b44c110d894100477c3ac43128207a3c84d8b525040f179093b4a4a081e1f21d65549410051ec26eca928200a6d829d952504014bf06bb2a4a08e69720d765494100537c12eca928200a77815d952504014f700bb2a4a08e29e201765494103d1e426c4a9282078bc87595425040155f04b2a84a081eab21f625094100557c06c4a128200aad80d894250401d1e61b1284a0803a34c3625094100753886c4a128200ea510d89425040f878eda9284a08038bd8b525094103e1e3b2a4a128200e2f62549425040fc58c4a9284a0803a9d8b715094100753b10e2a1282078bc849da3250461938c6ba464a080e1fe1d65945410061fb2ee8a8a82048bf87596415040195ae5b1482a08173cc4170d963100c6fc3a61b2c6201cda704c3658c4019b2e0986cb18803b44c110d963100679b8220b2c6200ed130441658c40b9e620b86c91880637e1d30d923100e6d38261b246200cd9704c3648c401da260886c9188033cdc110592310076898220b2462058f4815d9548c4070fd0fb2aa91880e8fa1365552310245f43ec8aa46204a3e85d91548c4039b4e0982c518803365c13058a3100679b8220b146200ed130441628c40717d09bb2a5188022f6137654a3103c3f43ecaa946200c5d65dcd528c47547d09bb2a5188028f6137654a3100536c14eca946200a76819d9528c4014df04bb2a518803175db7354a3126f27192c4a94620487e85dd9428c4010fb0bbb2851881e2fa1f6450a3118d1f42eeca146200a3d85dd9428c40155b053b28518802ada067650a3100557c12eca146207e2e62549428c401c5ac4a928518937c30c95250a312946fc32e31946200a5d83943654c401da260886ca988021fe1570595310045fc22e0b2a62038bc845c1654c4011df04b82ca9881e3b209705953100c6e43a60b2a6200cdb704c1654c4031e90e882ca988033cdc110595310076898220b2a6200ed130443644c4010ff
  | 10 => 0xb1ca200a5d85d0d6394401c3aa9a1ac7288063721d3058e510052fc2a60b1ca200cdb704c16394401da260882c7288030fdd95450e512043fc3aa8b14a203c3e7455162944010fb0f282c528807369c13058a510066cb8260b14a200ed13044162944014df00b12a5288029b6016254a5100727982c4a94a200e4d305895294401cce20b12a528803994416254a5107c3ec36e2a94a20093d84dc55294401ccac5b8aa528803995887154a5103d1fc32a5a14a200e2d6254b429447587cc8baa852889a5e2017550a5101d1fc32a8a14a200c3f76551429446153d073b28528802a760e7650a510055b40ceca14a22faba809d94294401573013b28528802abe097650a510061fbb2eaa14a200b2f825d5429450567100baa8528802abe096350a5103d56412c6a14a207a3f86549429440fc5cc4a9285288038b5895250a510076898221b22a2018df874c363544019b2e0986c6a88033cdc110d8d510076898221b1aa20787c855c3625440117f08b86c4a880e2f21170d895100679b8221b12a200ed13044362544011df0eb10c4a881e9b21f625495100537c06c4a92a200a6d80d895254401c9e61b12a4a8803934c3625495100733886c4a92a200e6510d895254401ccec5b8aa4a880399d88715495103d1e432a5a12a200e2f6254b425440f0f90b3b484a88028f617765095100556c14eca12a200a9f835d9425446153906bb284a8802ade0576509510055dc02eca12a22fab8805d9425440f4790bb1284a881e8f219525095100717b12a4a12a20787c859da32544738b8c6bac64a8803175d7638c95100636b96c528aa200c5f525cf659040193e84b9ecb2080237e0173d964102e6b882e7b2c8205cf3105c365904019b506b86cb208033660d70d96410063da92e1b2c8200cbb425c3659040b9e502b86cb2080a37e1f30d96410046ec3e61b2c8201cda70cc365904019b2e1986cb2080237e1d30d96410046ec3a61b2c8201cda704c365904019b2e0986cb20ae7359cd10d96410066ab9a21b2c8201cf27044365904019e2e0886cb20803b44c110d96410076898220b2c8204a3f86595549046f87ccbb92a9208962f61b715524101c9ec2ee2aa4827bd3651dc5549040987ceaaa2c72080317dd75358e410054ec26a6b1c8200e1d54d4d63904031b90e982c72080336dc13058e410076898220b1c8200c3f76551539046f17f0eaa2c5208130f9d55458a410045ec3c80b148201cda704c162904019b2e0982c520803b44c11058a4103c3f43ecaa948239a5e83d9552904014bb07b2aa5208e29ea036554a410053cc06caa948204a3f86551529040187eecaa2a5208e697a0e7654a410052ec1ceca948200a6d829d952904014ed033b2a5208e29ea027654a410053cc04eca948200a6f825d9529040187eecba2a520802cbe09
  | 11 => 0x8c8010ff0ab82c3190121f21570586320045fc22e0b0c64038bc845c1618c8039b4e0982c319003365c1305863200c7a43a20b0c6400cf370441618c801da260882c3190073c9c110d953200678b8221b2a6400ed130443654c8018eea5b8aca990023d60371595320066b986e2b2a6400cd7731c5654c8018eea838aca990031dd4871595320047ac00e2b2a6400cd7301c5654c80117f08b82ca9900e2f21170595320047bc0ae0b2a64058f4815c1654c8031b90e982ca9900335dc530595320066a38a60b2a6400cdb704c1654c8011ed0f882ca990163d21f10595320047b43a20b2a64008f487441654c801da260882ca990073c9c110d913200678b8221b226400ed130443644c80196e85b8ac8990023d60371591320066b986e2b226400cd7731c5644c80196ca838ac8990032dd0871591320047ac00e2b226400cd7301c5644c8010ff0ab82c8990121f21570591320047bc0ae0b2264058f4815c1644c8031b90e982c89900335dc530591320066a38a60b226400cdb704c1644c8011ed0f882c8990163d21f10591320047b43a20b2264008f487441644c801da260882c89900237e0d76551320047bc0aecaa264058f4815d9544c8011f700bb2a8990063e201765513201c3e43acaaa26403a3c84595544c8014e902b2aa8990122f21d64551320251e42ac8aa26400ab481591544c8014ef02b26a4990029d20564d49321cd36c16caa926400c5f65dcd524c8014ef02b22a4990029d20564549321ce2f3b6e6a926407b4e82dcd524c80156f02b2e8499002ad20565d093218556c16c8a126400ab781595424c80156902b2a849901ee3a0b73509320055b426a3b0a6400a7685d07614c8090fd0bb86c2990021f61770d853201c5f426e1b0a64008bd84dc3614c8019b6e0986c2990063de1d10d85320053a42a21b0a6400ab484443614c8039e4e0886c2990033c5c110d85320076898221b0a64008f787584614c80b9e4c2b80c2990033c58570185321f63d386a430a6452e4c32548614c8718f4e0a90c2990d72e9c34218532297461928430a642fcba70508614c80156d09a88c2990029da1741185320066d982e030a6405cf3105c0614c8019b506b80c2990033660d70185320063da92e030a6400c79525c0614c80197684b80c2990032e50970185320066d192e030a6400cd8325c0614c80b9e502b80c2990033cd45701853202e7828ae030a6400cf3415c0614c80b9e082b80c29901736cc5701853202e7918ae030a6405cd9315c0614c8019e262b80c2990173c885701853200e6d3826030a6400cd9704c0614c8014e90a880c299002ad211101853200e793822030a6400cf170440614c801da260880c299003b44c1105925101d1fc32c8aa4a240c3e64dc9549443f0fb0db8aa9288124f613715525101e1f3a2a8
  | 12 => 0xe796e0130596325a72d10260b2c64b4e59204c1658c965c6e85882cb192cb8d50b105963261f2b98620b2c6400e5530c41658c8734bd07082cb190029760e10596325b53ac0c20b2c6400e5930841658c8010ff0e882cb190021f21d10596320051fc2220b2c6400a3c84441658c801cb260882cb190031de1d10596320063a43a20b2c6400e3784441658c801c6908882cb192db8dd0910596325b71aa1220b2c6400e7380441658c985cae60882cb1930b9c8c110596320072a98220b2c64c2e7130441658c801ca260882cb192db9c88110596325b73890220b2c6439a5e83041658c8014bb06082cb192ca9da04105963203c5f43ea8b246400c3f75d51648c8090fd0bb8ac9190021f617715923203c5f43c80b246400a9d83901648c80156d03202c919002ad606405923200c5e43a80b246400ed130441648c80187eeb3aac919002a7e0d75592320055bc0aeab246400ab4815d5648c80157700baac919002ae20175592320061eba8eab246400a3e85dc5648c80147b0bb8ac919002a7e0d71592320045f43ea2b2464008bd87d45648c80f55d0428ac919002ab60851592321854f41ce0b246400a9d839c1648c80156d03382c919002ad60670592320051f428e0b246400a3d851c1648c86153d06382c919002a760c705923203d57410e0b24642daad821c1648c80156d02382c919002ad60470592321854f41ca0b246400a9d83941648c80156d03282c919002ad60650592320045f438a0b2464008bd87141648c86153d06282c919002a760c505923203d57410a0b246400aad82141648c80156d02282c919002ad60450592325a70fa9260b2464b4e1d524c1648c96753f00982c9190c3a6e0130592325a74d10260b2464b4e99204c1648c965c6ea5882c9192cb8d54b105923260f4b98620b246400e9530c41648c86153d07082c919002a760e10592325b55ac0c20b246400e9930841648c80117f0e882c9190022f21d10592320051fc2a20b246400a3c85441648c801d3260882c9190032de1d10592320065a43a20b246400e3785441648c801c690a882c9192db8dd4910592325b71aa9220b246400eb380441648c981d2e60882c919303ac8c110592320074a98220b2464c0eb130441648c801d2260882c9192dbac88110592325b75890220b246430a9e83041648c80153b06082c9192caada0410592320061e2a6ecaa46400c3c545d9548c8011ef02bb2a9190163d20576552320047dc02ecaa464018f8805d9548c80f0f90eb2aa91900e8f21165552321ce2e39acaaa464078bc87591548c8094790ab22a9190c3271cd64552320062eb2ee6aa4640087f855c2618c8090f90ab84c3190022fe11709863201c5e422e130c6405cf3105c2618c8039b4e0984c319003365c1309863202e79b822130c6400ed13044261
  | 13 => 0x4d6c16e130a8400a3d85182615080156b02304c2a10bf669c13098542006ccb826130a84009ad87c82615085f35f0e904c2a1046ab219209854217ed53824130a8400da9704826150801f1260904c2a10be6d61f1098542006d8b862130a8400ab4864426150801f2260884c2a1003e84811098542006c7b16e6b0a840099d80dcd6150801b1ee7b92c2a1003631cf72585420068fb9ea4b0a848ed1c73d496150801a3ee6a92c2a1233471cd5258542006ca39ec2b0a84079ac82dc1615080117f0cb82c2a10024fe15705854218c9e42ae0b0a840099f835c1615086133906b82c2a10026be097058542004cf43e60b0a843099c87cc1615080133d0e982c2a10026721d3058542004d743e40b0a8400d8f73c81615098bb18e7902c2a10be6b21d2058542006c7b9a40b0a84c4d8c734816150801b56e0902c2a10bf6a1c12058542007c498240b0a8400d9773c416150983b28e7882c2a10be6d21d10585420055a43220b0a8400d97734416150981b28e6882c2a10036cdc11058542007c898220b0a8400fa120441615086327d0b3b0c2a10c62f61f651854218e1f3aeca30a8431c3c75594615080156f02b28c2a1002ae201651854249cd7c12e630a8400a3d85d84615080117f0eb08c2a10026de1d6118542005ca41ac230a8400ab586d44615080156b0c288c2a10038d5945118542005d2c10a230a8400d95730c4615080174b04188c2a1002ec60031185420055ac0cc030a84008bd87180615080147b0a300c2a10bf669c13018542006ccb826030a8409aac86480615085fb54e0900c2a10036a5c12018542007c49824030a842f9b587c40615080156b0d880c2a10036c5c310185420055bc322030a8400b34854406150801f2260880c2a1003e8481101854203c3f43ca8b2c6400c3f74951658c80717d09b8acb190022f613715963203c3f43ca0b2c6400a5d83941658c8014ed03282cb190029d606505963200c3e43aa0b2c6400ed130441658c80187ee93a2cb1900297e0d74596320053bc0ae8b2c6400a74815d1658c8014f700ba2cb190029e20174596320061eba0e8b2c6400a3e84dc5658c80147b09b8acb1900297e0d71596320043f43e82b2c640087d87d05658c80f4dd0420acb190029b60841596321cd2f41ce0b2c6400a5d839c1658c8014ed03382cb190029d60670596320051f420e0b2c6400a3d841c1658c8734bd06382cb190029760c705963203d37410e0b2c642ea6d821c1658c8014ed02382cb190029d60470596321cd2f41c80b2c6400a5d83901658c8014ed03202cb190029d60640596320043f43880b2c640087d87101658c8734bd06202cb190029760c405963203d3741080b2c6400a6d82101658c8014ed02202cb190029d60440596325a70fa1260b2c64b4e1d424c1658c9674bf00982cb19
  | 14 => 0x1304436350801f4240886c6a10c22f21d6558d4218e1e3aacab1a8400d8f63dc96350999b18c7b92c6a10026b6037258d42666c7986e4b1a8400da772dc56350801b4ec5b8ac6a10026d6037158d42006cb986e2b1a8400da7721c5635080196eca38ac6a10032d5947158d42006cbb18e2b1a8400d94631c56350801b4ec438ac6a10026d6007158d42006cb980e2b1a840093f855c163508632790ab82c6a10026be097058d42004dbc0ae0b1a84009b4815c1635085f3390e982c6a1002a72193058d42006c7b9260b1a8400d97714c16350801b28e2982c6a100366dc13058d42004d743e40b1a8400da771c816350801b48e3902c6a10026ba1d2058d4217cd643a40b1a8400da7714816350801b48e2902c6a10036adc12058d4217ed438240b1a8400f8930481635080136d0f882c6a10026d21f1058d42006d3b9620b1a84009b68744163508013690e882c6a100369dc91058d42007c898220b1a8400fa120441635080135b05bb2a6a100267e0d7654d42004d7c12eca9a84009b7815d9535080136902bb2a6a10026ee017654d4217cdc402eca9a843093c875955350801878ecb2aa6a1002cbe096554d4203cd7410e2a9a84009ad821c5535080165f04b1ea4a1002cde0563d49420059a40ac7a928431c3f76d95525087565b05b2aa4a101e4f61773549424668f29ee6a9284319ad82dcd525080f2790ea9aa4a101ecb209535494204c5f436e2a928400b1f835d9525091963906bb2a4a1002cbe0976549420059bc0aeca928400b34815d9525080167700bb2a4a122ace20176549421d61ebb0eca92843ab2f821d95250881a5ee43b2a4a10eb8bd8876549424668f39ee6a928431b2d82dcd5250919e1e65b9aa4a1002cbe0973549420059bc0ae6a928400b34815cd525080f65d05b1aa4a10eacb60b635494246787996c6a928400b2f8258d525080166f02b1aa4a1002cd20563549420051f436e2a928431a3d86dc5525080163f06b8aa4a1232c720d715494200596c14ebb0a844093f825d7615080187ec4baec2a10034bd8975d85420069bc0aebb0a844093f87d4b615080127b0fa96c2a10024fe1d52d85421d49ec3aa5b0a8400ab586d476150801a6aea28ec2a1002e960851d8542005d2c1063b0a8400bb1800c7615086327d0bb86c2a10024f61770d854265e8f3ae61b0a8400d1d75cc36150995a3cea986c2a1003475d530d854264e973ae41b0a8400d2d75c836150991a5cea906c2a10034b5d520d8542006d5b8241b0a842fda8704836150801f1260906c2a131f4d9d710d85420069abae21b0a842f9b78744361508016690a886c2a131b4d9d510d85420069abaa21b0a8400db1704436150801f2260886c2a1003e848110d854218c5fc3acb30a8431c3e75596615080157100b2cc2a10028f617619854200
  | 15 => 0x5b9acaa100363d8b73595420068fa96e6b2a840099d80dcd6550801c38ca39acaa10df0f197725954266f1632ee4b2a8400d8f73dc96550801b18e7b92caa11034be1772595422069642ee4b2a8400d2f65dc9655099ba58cbb92caa13374bd4f725954266e9628ee4b2a84009ad80dc9655099ba5ea1b92caa10038d1977159542006cbb9ee2b2a8400d9473dc56550801b4ee5b8acaa10032d61b71595420069b42ee2b2a8400cb762dc56550801b4ec5b8acaa10034dd4b7159542004dac06e2b2a8400e34651c56550801b2ee638acaa1003651cc7159542006d3b90e2b2a8400cb7621c56550801b4ec438acaa10034dd487159542004dac00e2b2a842f9ba87dc16550801c70cbb82caa100366dcf7059542006cc39ee0b2a8400dab72dc16550801b66e3b82caa10036c1c77059542006cdc1ee0b2a8400d9883dc16550801b5705b82caa10032ed8b7059542006d5b16e0b2a8400d3b52dc16550801b6703b82caa10036c2077059542004cfc1ae0b2a843099c835c1655080135f04b82caa10026de057059542004da40ae0b2a84009ba871c16550801c70ca382caa100366dcc7059542006cc398e0b2a8400dab721c16550801b66e2382caa10036c1c4705954218d1e42ec0b2a842fcb870d816550801c76a1b02caa10be2f21d605954218d1e42ac0b2a842f93c8754165508014790ca82caa10034bdc9505954217e9c382a0b2a840099e87cc165508613390f982caa132f871973059542006c7b9660b2a8400d9771cc16550801b28e3982caa100366dc3305954217ecc38660b2a840099e874c165508013390e982caa132b871953059542006c7b9260b2a8400d97714c16550801b28e2982caa100366dc1305954217ecc38260b2a84009ae87c816550993c58cb902caa100363dcf205954262ec639e40b2a8400da771c816550801b48e3902caa10036adc3205954217ed438640b2a84009ae87481655085f3590e902caa13238b1952059542006c7b9a40b2a84c4d8c734816550801b4ee2902caa1003691c52059542006d5b8240b2a842fda8704816550801d56c0902caa1003e24c12059542004db43e20b2a84009b487c41655098fc68cb882caa100365dcf105954260eca39e20b2a8400da772c416550801b66e1882caa10bf6c1c31059542004db43a20b2a84009b487441655098dc68ca882caa100365dcd1059542606ca39a20b2a8400da7724416550801b66e0882caa10bf6c1c11059542007c898220b2a8400fa120441655086117b0fb2ec6a10c70f9d765d8d4218e1e3aacbb1a8430a9c83597635080153b0da9ec6a1003475d753d8d420070eb2ea7b1a8400b8d82d4f635080f35d0538ec6a103a6b60a71d8d4217ccfc3a61b1a8400d99704c36350801b56e0906c6a10bf6a1c120d8d42007c498241b1a8400f9
  | 16 => 0x5954200678388e0b2a840187c87541655087547908a82caa10071e1c1505954200c5e43a80b2a8431a3c8550165508011bd0f982caa100a3721f30595426c70e2a660b2a8400cd771cc165508019a8e3982caa100336dc3305954200e6c38660b2a84008de874c165508011b90e982caa135f8715130595420066bb8a60b2a8400cd4714c165508019b6e0982caa1007361c130595426b7162a640b2a8401ce870c8165508031d90e902caa13578b15120595420076498240b2a84008f687c41655080b1e90f882caa13538d15310595420066bb9e20b2a84b8cd473c4165508019e6e1882caa10073c1c310595420047b43a20b2a84008f48744165509a7c68a8882caa100335dcd10595425ce6a39a20b2a8400cf37044165508039e0e0882caa1003b44c110595420077090220b2a8404a3e86d955450881a5eebb92a8a11026ba1c72551420261e3aaa9b1a8430a9c8355363508018baeba9ec6a1002a761353d8d420070eaa6a7b1a8400acd82d4f63508031bf0e986c6a12d3275d130d8d420066cb8261b1a8400ed13044363508019a8c638ac6a100a1f21d6554d421d61e3a2caa9a840393c875515350801878ecaa2a6a101e2f2197550d420145e43acaa1a8431c3c75595435092735d0e39286a101e8f61363d494203d1e43287a928407a3d84d9552508754db05b2aa4a101e4f61774549420061fb2ee8a92843a9ad82dd1525080f2790eaa2a4a101e8f219545494201e1e3b2a8a928407b2c82551525087587cedba2a4a101ecba0b74549421d596c16e8a928407a3d84d8d52508754db05b1aa4a134b93ccb635494203d1e43286a928407b2c8250d52508090ff0ebaec2a10031de0575d85420061e20aebb0a840487f87d4b61508010fb0fa96c2a102a1fe1d52d85421d43ec3aa5b0a8400ab584d4761508018eaea28ec2a1002bc60031d85420243f42ee1b0a840087d85dc361509a38bceb986c2a1003175d730d85426862f3aa61b0a8400c5d754c3615099f8eceb886c2a10031d5d710d854200c7bc3a21b0a8400a7485443615099d8ecea886c2a10031d5d510d854200678b8221b0a8400ed13044361508011ef0eb08c2a1002b520d61185420261e3aaa830a8400ab78155061508f7c68a2aa0c2a1017350c573185420055ac26a230a84038bc845c0615080b9e620b80c2a1002ad606401854200e6d3826030a8400cd9704c061508014e90a880c2a1002ade111018542007689822030a84939af825cf655080f35904b9ecaa101e6ba0a71d9542074d6c14e3b2a842f8bd87d83655086347d0bb06caa132f8799730d95426570f32a61b2a8400eab604836550801f1260906caa131f8d99710d95426371b32a21b2a8400f91304436550801f4240886caa10c68fa1b6559542184cf43ee6b2a8400e1c65dcd655080193ec
  | 17 => 0x2c84b4e1f424c16590969c3a84982cb2100396e0130596425a72790260b2c84b4e5a204c16590969cb240982cb212ce97a0c305964203d3741060b2c8400a6d820c165908014ed02182cb210029d604305964203d37c0240b2c8407e6b804816590801c9e60902cb210039a8c120596420072698240b2c8400e69304816590801c9260902cb212cb8dd0b10596425971aa1620b2c8400e5730c416590801caa61882cb212cb99c8310596420073290620b2c8400a5e8384165908014bb07082cb2101e9ba0a105964200536c1420b2c84b6a75818416590801cb261082cb210039a48210596420043fc3a20b2c840087c87441659080147f08882cb210ea8f21110596420072c98220b2c8400e692044165908018ef0e882cb210031d21d10596420071bc2220b2c84d3e3484441659096dc6e84882cb212db8d509105964200739c0220b2c8400e57304416590801ce460882cb21003954c110596420073898220b2c8400e5130441659096dcce40882cb212db9c88110596420073290220b2c84b6e71204416590801cc240882cb2100297a0c10596420052ec1820b2c8407a6e8204165908014db04082cb212ca9da04105964200c6e43a60b1c8400cdb704c163908039e4e0882c7210033c5c11058e420076898220b1c840787c8759553908010ff0ab84c3210121f215709864202e79882e130c8401cda704c261908019b2e0984c321002ade11109864202e79b822130c8400ed13044261908010ff0ab82c3210121f215705864200e6d38260b0c8400cd9704c161908031e90e882c3210033cdc110586420076898220b0c84038bc845c7655080f17b09b86caa12cf275d330d954265f0faa661b2a84b4c9d744c36550995c3ea8986caa101f2b5d320d954264f17aa641b2a8407cad744836550991c5ea8906caa1003b24c120d95425965aba621b2a84c7e3754c43655096d96ae8886caa131b8dd5110d95420076898221b2a8400ee120443655087547d0bba2caa100a37a1f73595420070e2a6e6b2a8400c5f52dcd65508018baa5b9acaa10023760373595420070e2a0e6b2a84d9e2c54dc96550801c68a9b8acaa100335dcf71595420066a39ee2b2a8400c7685dc5655080196d09b8acaa10032d61371595420063ba96e2b2a84008f580dc56550801c68a838acaa100335dcc71595420066a398e2b2a8400c77521c565508011eb0038acaa10063ea1f70595420071c2a6e0b2a8400cdb73dc165508019b0e7b82caa10033cdc770595420067838ee0b2a8400cdb83dc165508019b107b82caa10031ed4b70595420063ca96e0b2a8400cf381dc165508019e103b82caa100237e0d70595420146e41ae0b2a84008f7815c1655080b1e902b82caa10023ea1c70595420071c2a0e0b2a8400cdb731c165508019b0e6382caa10033cdc47
  | 18 => 0x480147b09b0cc2a90025b60b70985520051ec20c130aa400a75811826154871ab4e0984c2a9003565c13098552004b6c3e4130aa43896f8748261548254d90c904c2a90e35a9c12098552006b4b824130aa400f493048261548712eb0f884c2a90029da1b1098552006b8b862130aa400a74864426154801ea260884c2a9003d84811098552006a7b16e6b0aa40095d80dcd6154801a9ee7b92c2a9003531cf7258552006aa39ec2b0aa40796c82dc161548010ff0cb82c2a90024fe1170585521d49e422e0b0aa40095f835c161548732b906b82c2a90025be097058552004af43e60b0aa43995c87cc161548012bd0e982c2a90025721d3058552004b743e40b0aa400d4f73c8161549b7a98e7902c2a90e25b21d2058552006a7b9a40b0aa4dad4c734816154801ad6e0902c2a90e35a1c12058552007a498240b0aa400d5773c416154987aa8e7882c2a90e25d21d1058552006abb9a20b0aa4c2d54734416154801ae6e0882c2a9003d44c11058552007b090220b0aa43a93e849d861548750fb0fb20c2a90eb0f9d364185521d61e3a2c830aa400a778159061548014f100b20c2a92865be0973185520051ec26c230aa40087f8758461548012ef0eb08c2a9002d520d61185520053ac368230aa400e356410461548016cb04208c2a9003555cc3118552005b2c106230aa400b71800c461548014eb03300c2a90021f61c60185520051ec20c030aa400c79701806154871ab4e0980c2a9003565c13018552055364324030aa438d6a704806154801ad2e0900c2a9003d24c120185521c4bac3e2030aa400d7170c4061548014ef0c880c2a9002cd2111018552007a89822030aa400f6120440615480f27b0bb9aa5a12634794f7354b4203c9e43aa6a9684038be86dc552d080117b0db8aa5a1263479cf7354b4200597c12e6a968400b37815cd52d080166902b9aa5a10ea8fa1b7154b420051ec36e2a968400b1f835c552d093163906b8aa5a100317dce535964203c3f43ca0b2c8400a5e8394165908014bb07282cb2101e9ba0a50596420053b40ca0b2c8400a758194165908030f90ea82cb21003b24c120596420076898220b2c8400ee12044165908018bee739acb210ea8fa1073596420051ec20e6b2c843aa3e84dc5659080147b09b8acb2101e9ba08315964200536c1062b2c8400a7a800c565908014f30018acb2100297a0e70596420052ec1ce0b2c8407a6e829c165908014db05382cb210029da0670596420053ac0ce0b2c843aa3e841c1659080147b08382cb2100297a0c70596420052ec18e0b2c8407a6e821c165908694db04382cb210029da0470596420053ac08e0b2c84b3e1f42cc16590967c3a85982cb212cf93c8330596425a52ec1c60b2c8407a6e828c165908014db05182cb210029da0630596420053ac0c60b
  | 19 => 0x6b531cd2059152006b3b8a40b22a400d64714816454801ad6e0902c8a90e35a1c1205915200735b0240b22a400f493048164548012ed0f882c8a90025d21f10591526a71a32620b22a400d5773c416454987aa8e7882c8a900359dcb1059152006b9b8620b22a438d7070c4164548012ed0e882c8a90025d21d105915269f1a32220b22a400d57734416454985aa8e6882c8a900359dc91059152006b9b8220b22a438d70704416454801ea260882c8a9003d848110591521cc3ec3ec9b1aa43ac3e74d9363548734bd07b26c6a90eb0f1d164d8d521cd2e41ac9b1aa400a5d86d0f6354801c3ac9a1ec6a9002d360b43d8d5203cb7414e3b1aa40f96d829c763548712bf0e986c6a900297e1930d8d52006acb8261b1aa400d6b704836354871ad0e0906c6a9003d24c120d8d5261f2b31e21b1aa4c2e56634436354801ea260886c6a9003d848110d8d521cc3e43ac8b1aa43ac3c745916354801a9ec7b92c6a93735318f7258d52004b6c06e4b1aa4dcd4f30dc96354801acee5b8ac6a900359d8b7158d52004bac06e2b1aa400d5730dc56354801acee438ac6a90031dd907158d520063ab20e2b1aa400d57631c56354801aa8c638ac6a900359d887158d52004bac00e2b1aa400d57301c5635480127f08b82c6a90ea4f2117058d52004b7c12e0b1aa400977815c163548012e902b82c6a90e25721d3058d520052e43260b1aa400d4f724c16354801aaee2982c6a9003551c53058d52006adb8260b1aa40096e87c816354801acee3902c6a9003591c72058d52004b743a40b1aa43896c874816354801acee2902c6a9003591c52058d52006b5b8240b1aa438d68704816354801e9260902c6a90025da1f1058d52004ba43e20b1aa400d6772c4163548012ed0e882c6a90025d21d1058d52006b3b9220b1aa400f51304416354801ec240882c6a90025b60b7650d52004b7c12eca1aa400977815d943548012e902bb286a90025ee017650d521c4bc402eca1aa43993c875914354801878ecb2286a9002cbe096450d5203cb7410e2a1aa40096d821c5435480165b053a6c2a90de4fe0974d85520061fb12e9b0aa400d2f625d36154801a6f02ba6c2a90029d61b41d85520069aba083b0aa400b658210761548014eb0d98ec2a9002d960831d8552005b8c0063b0aa43a93e84dc3615480127b09b86c2a9363479d330d85520068eba661b0aa4d7d1e744c36154801a3ae8986c2a935b4b9d320d855200696ba641b0aa4d5d2e744836154801a5ae8906c2a90035adc120d85521c6b438241b0aa400f493048361549a9a6ce9886c2a90034d5d310d85521c4bbc3a21b0aa400a7786443615480166908886c2a934f4d9d110d85520069aba221b0aa400d71704436154801ea260886c2a9003d848110d85521d61f3a2c930aa400a7880592615
  | 20 => 0x4eba661b0aa4dfc9e744c3615480193ae8986c2a937b2d9d310d85520065aba621b0aa4018f78744361548014ef0a886c2a9002ad21110d85526ee5b3a221b0aa400cb57444361548019e2e0886c2a9003b44c110d85520047bc3ac230aa400ad4835846154807878e8aa0c2a90029de0554185523df1a20aa830aa405cd4315cc61548014eb0ba08c2a90121f21570185520063c282e030aa405cf3105c061548014eb03280c2a9007369c130185520066cb826030aa400a7785440615480156908880c2a9003b44c1101855250cb7c12e7b22a40796c825cf645480f2dd0538ec8a903e5b60a71d91521c43ec3ec1b22a43aa3e84d8364549b1c3cc9986c8a935f8799130d915200735b0241b22a400f493048364549a9c6cc9886c8a934f8d99110d9152007a898221b22a400f6120443645487547d0db22c8a90e657a1f73591520070e326e6b22a400d4f62dcd6454801a3e85b9ac8a90025760373591520070e320e6b22a440c3c64dc964549b3c58c9b92c8a900353dcf7259152006a639ee4b22a437d2f84dc9645486fa5909b92c8a90034bd9372591526ce96326e4b22a4d9d2f43dc964549b3a5883b92c8a90025b60372591526ce97a06e4b22a400e3464dc56454801aaee7b8ac8a9003551cf7159152006b3b96e2b22a400c7586dc56454801a6d09b8ac8a900359d8b71591520069ba16e2b22a40097580dc56454801c68c838ac8a900355dcc7159152006aa398e2b22a400d67721c56454801acec438ac8a90034dd087159152004bac00e2b22a43897a87dc16454801c70c9b82c8a900356dcf7059152006ac39ee0b22a400d6b72dc16454801ae6e3b82c8a90035c1c77059152006adc1ee0b22a400d5883dc16454801ad705b82c8a90035ad8b70591520069da16e0b22a400d7381dc16454801ae103b82c8a900257e0d70591521ccae41ae0b22a40096f825c164548012ef02b82c8a90025d20570591520071c320e0b22a400d5b731c16454801ab0e6382c8a90035adc87059152006b9b88e0b22a400d70711c1645487547909b02c8a90e31e1c360591520071da06c0b22a43887c87581645487547908b02c8a90e31e1c160591521c49e43a80b22a400a3c865016454801a5ee4a02c8a900257a1f30591521ccae43e60b22a4d8e1c64cc16454801a9ee5982c8a900355dc73059152006aa38e60b22a400d5b70cc16454871ab0e1982c8a900257a1d3059152004ae43a60b22a4d7e1c644c16454801a9ee4982c8a900355dc53059152006aa38a60b22a400d5b704c16454871ab0e0982c8a90025ba1f20591526b71632640b22a400d4f73c8164549b7a98e7902c8a900359dc72059152006b238e40b22a400d6b70c816454871ad0e1902c8a90025ba1d20591521c4b643a40b22a4d5e2c644816454801a9ee6902c8a93
  | 21 => 0x820c564948015750018ac929002ae60031592520054f41ce0b24a400a9d839c1649480f55d05382c929002ab60a70592520055b40ce0b24a400ab5819c1649487b47d0a382c9290028f61470592520054f418e0b24a400a9d831c1649480f55d04382c9290f6ab60870592520055b408e0b24a400ab5811c16494967c3ea5982c9292cf8754b305925259f4790660b24a407aae828c1649480155b05182c929002ada0630592520055ac0c60b24a4b4e1f524c16494969c3aa4982c929003a6e0130592525a74790260b24a4b4e9a204c16494969d3240982c92901eaba08305925200556c1060b24a400ab6810c1649480156b02182c92901faae0120592520074798240b24a400eaa304816494801d1a60902c929003aa4c120592520074498240b24a4b2e3752c416494965c6aa5882c929003a5cc310592520074a98620b24a4b2ea720c416494801d4a41882c929002a7a0e10592520054ec1c20b24a407aae82841649480155b05082c929003a64c210592520075490420b24a4008bf8744164948011790e882c9290028fe15105925218d1e42a20b24a400e99304416494801d5240882c9290032de1d10592520065a43a20b24a400e3785441649498dc690a882c9292db8dd4910592525b71aa9220b24a400eb3804416494801d2e60882c929003ac8c110592520074a98220b24a400eb1304416494801d2260882c9292dba9c8110592525b75910220b24a400ea520441649496dd6240882c929003a848110592520054f41820b24a400a9d83041649480f55d04082c929002ab608105925200c6e43a60b1ca400cdb704c163948039e4e0882c7290033c5c11058e520076898220b1ca4078bc87591439480117f08b84c32900e2f211709865202e79882e130ca401cda704c261948019b2e0984c3290029de15109865202e79b822130ca400ed130442619480117f08b82c32900e2f211705865200e6d38260b0ca400cd9704c161948031e90e882c3290033cdc110586520076898220b0ca40387c855c764549b1c3ca9986c8a935f8795130d91526b7172a641b22a407c6d7548364549abc5ca8906c8a9003b24c120d91526a71b2a621b22a4d3e36544436454801da260886c8a9003b848110d915201d1f436c8aa2a437d2f74dc9545486f2dd0e392a8a900f0f1d154d8d521cd2e41aa9b1aa400a5d85d0f6354801c3aa9a1ec6a900637e1d30d8d520052fc2a61b1aa4b4c5d754c363548019b2e0986c6a930f9594f10d8d526172b29a21b1aa400ed13044363548019a8c638ac6a92865ba1c7254d5203c3e432eaa1aa40493c875514354801878ecaa286a900e2fe1d74d85520061e28ae9b0aa400a7585d07615480196ae820ec2a90029d61731d855200578c0063b0aa4038be84dc3615480117b09b86c2a9383279d330d8552006
  | 22 => 0x8006002000000000000300c6fc3a61b1aa800cd9704c363550019e6e0886c6aa0073c1c110d8d540076898221b1aa83e87c87543625508147908a86c4aa0d62f21d40d89541bd1e42a81b12a8e6e1c54cc362551cbc38a8986c4aa00336dc130d895400e6c38261b12a8e4e3454c4362551c7c68a8886c4aa0033cdc110d895400e7838221b12a800ed13044362551b38daebb14c4aa3372b5d362989540068e2a6e6b12a800d3454dc56255001a68a838ac4aa0034e153705895400477c3ac4312a80387d85dc3615500917b09b86c2aa383175d730d855468e4eba661b0aa8dfc5d754c361551a193ae8986c2aa00336dc130d855400e6c38261b0aa8dec7575c43615519f96ae9886c2aa0063de1d10d85546ee3abaa21b0aa8cecb57444361550019e2e0886c2aa003b44c110d85540068e2a2e730aa805cd4615ce61550019aae7b0cc2aa0034e151709855400679b0ae130aa805cf0615c261550011ef0eb08c2aa00237e0d72185540146e41ae430aa805ce4215c8615500b9e620b80c2aa007369c130185540066cb826030aa800a7785440615500156f08880c2aa0173cdc11018554007689822030aa800ed1304436454c0747d0db22a8a99030f19372551531fc3e43aa9b12a603c3c745536254c0117f08b86c4a980e2f21170d89530066db8261b12a600ed1304436254db98daebb14c4a98023be1d62189530143ec2ee1b0aa6038be84dc36154c0117b09b86c2a980336dc130d855300c7bc3a21b0aa600cf1704436154c01da260886c2a98023de1d611855301e1e3a2a830aa6008bf845c06154c0717908b80c2a98173cc41701855300e6d3826030aa600cd9704c06154c014ef0a880c2a9803b44c110185530052ec1ca1b2a8600c79709436550c01da260886caa1b8b0fdd7745954370e2fbaee6b2a860087f855c16550c0117f08b82caa18063721d30595430066db8260b2a8601cd8704c16550c019e6e0882caa18073c1c110595430076898220b2a8604a3e86d955450c6f878cbb92a8a18da2f21d54d89430261e3aaa9b12860087f855c36250c090f90ab86c4a180336dc130d89430076898221b1286cccad74d8a6250c011df0eb10c4a18121fa1770d85430043ec2ee1b0a86028bd84dc36150c019b6e0986c2a18063de1d10d854300678b8221b0a8600ed1304436150c011ef0eb08c2a18130f1d554185430043fc2ae030a860487c855c06150c0b9e620b80c2a1807369c130185430066cb826030a8600ab7844406150c01da260880c2a1802a7a0e40592520054ec1c80b24a407aae82901649480156d03202c929002ad606405925200c5e43a80b24a400ec9304816494801da260882c929003b848110592521ed1f428e6b24a400a3d851cd649487b47d0bb8ac9290028f617715925203d5741062b24a400aad
  | 23 => 0x200040000060038000004000000000400600200a801000000100000000000000000004002000000002000600900b800401800000080340000020008004000000000000000200100000840080000000000002003000000800000200280200120010028004000001004000001a0070010094000004000000c000012001000800400b00080300060040000018004000000001c0000000008004002000002001c002001004000c006000007800000000000180100040070000000010006001000400600300000000020010000000000001002801402400000080100120030000000000000000000c00a0000008004002000000000c0000030010004000002001002400200100080040020020000004002000000004000e003001000800e00000b00000040000010024002000000001c002006004002000a000000800000a01100000000040000000070004000001000000a001000000800600f000000000600800080040000040000000000000005000c000000000800400c001000000c004003000000800000500000040020000020004000000001000c0000030020020006004000000000800000c8018000007003800000e000002802400200400480200040000008010006000004000000a0000020030002000000000000800700000080000030060000000002001800000000100000240220000008004002001000800001c000001000000000000000040060010000000002002000003800e0070078004004009000000800000200080080000120000024002001000801c000000000001400c000001800400000800380040040050000018002001000800000a00400180000000000000000000004000800c0020130020010008003000800000c00500b8000004001000000401800000000040000090028044000002001000000801600300080020030000004000010000802c002001000000000a0050080008002001006802c00001900000040000010000010000000001802400801b0008000004001002000c006000000000800000300000000000060010010000004000001000600100180040040030018000000001000001000800a00100000080060010004010001000000000200100000840020010008000000000000801000a004000802400000600000000040000010004000000000003000600100000180040080008010008004002800000000d001000001a0030010020004000000000c0220020040008002001000800001400900000040020000008018000000001800801200b000803400000a0028008004001000001c000009008800000c001006002000800300100080060020000020000006000800000800e0038014002000000001800000a002000c002000000000000400200080080260080008008000001000000400a0000010
  | 24 => 0x3f50c20f36000056a6e40009502cd000189070d6122af400000026588f8a9c37625702946d05f407c8264e2e0f1266800000000000020483fe00037a800017a3b2000000000089700000000007ca5209f30000538063000000055636d1c54c242c242aa56ceda9d63fda624c065a029e0000d8232221e8dac63ca9100016318625d55ca80010be1fb00000014167ae359800000000000000000000000002c3c00000055d16ad23875d000119c5da30d0000f8000000000009f93f20000002310088047000183800000041300000001a9398ac340000002a7a81c0000002231d90c8a75137c000135693e00000000002772519e940007f10bd0000000000000260c54073d1aa201400019a00017c8daeb130002428000000000092c00000000005b80005c65658ea53100004ea800116e0000001b84000136000000049210346125300000000d18000848000000000000000000000000010040000002007000002c00800700a80140080010010018002006001800001e001006800c0080010020000006000005000000a00700000000040060000000000000001006c0080010000010000001001800c000002002804000400300200040000140018000004006005800400600300080080060010008000008003000000001e001008800000401a0000004006002001800c000006001801c008001000000800a001006000400200a000001c00200300200140080000000004000004000000400a004000000400200200180040000030040008004000000001000800100580040040020000028000003000000801200000000000020050018004004008000800000200200200000100000008010002008000000400c0050028008008000000002c002005003000000000000080140000000120000002010000003c000002004801c004002000000c000007001000001000000080000000040060000008000002000800800200580080060000010010000001000801000400300100000000040040000000000001000c00200700080040020000008000004000000800c00c000004000800800200d800001a00000000000040020008000008000001800c000009001000000e007002000000400000200000040000018000002001000000000000200580000100020028008006003001000000000000000500000060008000000000004000000e0090000004002001000000000000a00100000060000028000002000000800000200600080040040050018004008004000000c00400300b0010008006002800c000000002000c002003000801c00800500d800800400a00400000180000000014002003000801400e00400300100060010000000002008000800000000e0010000000000001800400a006000001001a018000002800200700080100020070000018000
  | 25 => 0xe70bb6000000000006047a00000000003ba0d540000000000000000960531000074002f00000002da00000026600000005648a180007dd232000000000014b800000000048993f14d839b5418ae0000c1c02105451766af18c8ac095a4c94181e2000000000023f85249482981ff892400000025716841815f606744a600045080009146ea33e0001266a5a4aa9adc62a000206184d508adb0d680000368b45cc269564c000462a76000058d31900980000842fb156482e475302a78400000034489302d612e0000b58f1e1382db9ded41c0000000aa800000025c229400013a000020137491d3991920c4296f0001de43860000aaa0f8000000000000000000000029452288cf00000018420592a684e528e907000187947c9bb461a43c59679711c879c000000619000000000062e00005b25c535c27b0ca200040a00000000006062ba10207220088000e105e453a0000000a810bda8908ec5ce5fc0000d52b1d0000000c74000087a82400000001a02497340e259d000000037a5338f040001924fb28647d0b60000000000050704b800000055e09304d12ec9b20000000000000000185c0000005ad15800000f34530add1bc00057f8000000365000000010a00000000000000000002708138a701ed897040e28e16000006ae0000000000b7008100000018de00000000007e62be06a85c429aae70000000a7c55200014c4000685000313d54a00061a27e8fb20000002cb11529935468000000000000000036673a000000113a0000002104000b1e5aa19349e4c400002ef400000045898f03106461ca2f18af46115c48000000b3d00000000deb9e3a0000121c50c36d800091200023e24d0494afe0000000000b77000000000094b1d18cfd17a0834ab80000002dd13a1a451f60000000000d201e611d8820d1c73c19082b874c000400800000038d000000000007f000000000000000002e800000000006ed2ee9a22c3009cad20000001b9112a0000000e200000000000af188400062280001ce00003a2fa000011c000267115c00c3ed000000027a133800000000000021e92800000001070000746000021c80819304b08400003354a6ae4c3906ac3d0800051a00019206186bc7332929d80cac94f47099480002ae5e2000138a0003df000000052a00000000009060002f980006a700000ec0000004c72560000000083065c7c6000273800183441e000000026688d2e4800000000000000000004b200027f482c0004bc00000fc8824ea000030a000000000173232d13c00000000000000000000000000000000000035a9b2c0000002ca80000c21291bf0000000c4c0000000ed2a10000000000000000000000002710000000db06582308be8bd49dc000000000095401f00000004bd0a300000000000518000f0e4ef33e80001fc78e
  | 26 => 0xf4e60000f4c4120002da8fca7aa00006412002471b68000000a88000000000043612a000098e00022b800000072700000000000000000000000b882ba02ec000000000000000044a000000000090100014880000ac00005d4000a794ab02790fc82d26100000000005b813f80000000000000d3262806484397faa361938d844448181d08d8c0ec6b60002d498d81ab59226b8b36c3c53f800000000700024ac4028d83e483c94ec00000000000006c5404000139649611280000006a23459b4446c54c31380008d00b2625800022a5510000c280000e6000000000000000000000009031ed12347207e640d82a09a821a2dd1174e263f509200005ea0680002ee800022e1929c78000a0129eaf0cc9e6780002c20a3aab40862d7857607b128aed061e8490000630a0ab17000000000019e293134cf5e9b058d8f08522000122088c00000028821800007bd0e28000292000000000000000000021b000016757c0000b460000002f2800013e59280000000002fc16c000048e0002f9501a000000000037e8ce5f9828800000030200000000003130000136c1300000000000000002ff17ee000000000000000028680011eabb70001d6000000000000014c0000000114800097d00018ac0000000002bc56e80d30002d180008485d60fe97624c02399408c128e50000d2902ca6d28900000005d42cb2b6800068c5bb16601908dc000000000093c39180008360003889c140000000002ffcf8400023c23456386f30e900000005d7000157c0009125ca2ce45588d3000069144c0000001cb80000000770bf000000051a80004c60001c0135c0004e900003ac000000316800000000000000010ae00025b9eb0e5876f30c8eac530ac7596833c0000003590a0801e96a1fe00000060000000ca8000000000000046e00041604747a800000007c00000000688a4c0000000002e991de7300fb96a0000abc3bb000042431200014d143c0004e41e1110c4bf000239c0005fa0002910000000000070000026b0b9ab80000aaf000289cd54766000162557c28900008254f01a04b2889960a4c830c0974da649756a000077000031180010da42e2d1149d8a03c60918000d2e33900030d868457c00003a80501f40e38d3429050800030580001ee2df8a99156bd235287bcd405c4400306c87c4e811c0aad8dabd358b00001ea0a700000000001e32d900000002170000000ff0a5556f80000000000a28eec5326255cd81dd43eac22e1000181a98a0000000ba04ac369196400000000006243a041a3f58d000000002162e3c6fa92a0001cf8f8c2941990b8851e00024f80009dc7d10002da131a33b61827d50ee2d83c3000153e0cc2d49968f1456d26509ec0006405ed051000077f00000000000000002e5c000bd40000000faa00044491e4000000000000
  | 27 => 0x34e4742a0000131e00029d0000ad84800000000814817000250c78800000000015380000001c94000b000bc8bec00006d000174d1245640858694fac00036e80000002650002b0c82a000000000050a0004d30000f7e12500000000000000000a749520000000000000b7900025ac00000000000017080001b3ae747ca5e700030bc0008230000000b1e51e43e800000000000026f80003b91340ba0000000220082cae68654df8114fbe1160002a384904082558eb16cac5210d8001022bcc51617dd5760000c199c16c65d23c08914ef825a172a74072e049190000067400047b00000003020000000000063000000170200055ba2b4b9e8220000c5c000008000210c3325de17f8edcbd8000270aebc5ae9c60bf8fbc0e0c470c50d1400097f5ff02cc0004ec0002fec188000000000000000006080000002164e90fa849a0004ba270000036c0000b5003a000434917881c4fd28a803933e00047e9a74cae0000001bb047e44534529ec5d60000ed80c498c66d2520000c2807c0d90000000c010002d2036e0000000078048bf900014a103c00000007a0000afd00027a07e8af600010c000000014410c80666bc02e9daccdc4854398308962000257abb00009e40002fb50ac0000001f3d3b283c05228593deb870002b600005f30001e8ce38401000000043000000015844be000539a42cbf895900001f4f60adc00000000000000000000000a870bbae8cb2017d4770ac87980dc4058a40d008440b21cd11960004bd80015644f00281c11718b3842e9d8c78eb4f25d853d3c62de00023a98ce169000000000081c0000000a060000002b148ac00031a00012c44ce59a2aa84588a4000000104e0000000000d468150000000000c0f00014b562200016d0000000874373049cd9c66f000100800c00000020cc000a34590abdc0006c901e800145ead91f7000032a1960000f4c45095144faf0816261a1c700018d40000001f2c00045b2149f6c63e7c54b68000a460000000001008000055183c4540ca000000000000019580000000001b7941071221d37291652baa3b1ae2b40ffe7d201700006860005fd06c00f400062680000008f75d100006a446d60ea4fd872bd121100018b47484b895ed58c8d2588032cbc6ac000000b54ba0f70ba074400000023d2a1856c00000000000005ef0000ea95706d0000000000023c1a62eb8d022af521317c0004835ba81297160002bf000000069a61a80000005290000170b1655d3011e546184375298e3c730a591da94ec00061526b2fac0009f0000000128a000035800134e6e818e8ea0de00f60000000eac000000036859200000000000900000000000e5a38a00009b149e56300010ccc101c22488be4ee600024c800156c1ed521822506200051e80000000205010000000000000283400084
  | 28 => 0x8bd82075a00013400000004d600010cc0ed2a820d94140000002488b7aa4c00000005ce00000000004de00000014dc18a000000024c00056220998bcfc0000000000119200000000009c803f00009a42d80001af9bdd66452c05f0830b14c23371a7cc8629f10ed262c84675039780000006de4a219ed6d82524dea5d40004fb3da80000000002a380002503cf5a59268fec88c09a8000f7065c1c8800066ca9b000279cf56b5b00020fc000000000000000000000000000003bd1ef8b7132e9e52db1c090c466a31700010a0a1800021b820084c000000000083a0000e780007c300000005180000000c5800000000d000000000007d9460000bdf00000000000001350c600005000002d540002ec2622da4afe00000028949ec8b016fabd403200012a9e9cf0675f000000160e00010180000001aa3cb0eb91da0000efa03182e23a28c800000000046ca0e400000060012a8650bbb00006a000000000024b031aa7d02d98800000005d800016780000a9847c0000000000000000000559a100f268613bd00000004501778e7cdce0001c5990cca87b72fd8000d8c00000028755e400028480017e20000002c3800000000001a80000000000f786605ca2f800000004000002f2cf748cd00030fc0009a302f800000000038780009b00000001ec40007280000db815e0000002d1c98641f22491044f235b5b6a3b0f6699d4d08000000880000000103a5d641203847ce01300011fc0003231df873c00000000000000000a626c80012e00004cd800000000000025991320e900007642c60000000000a826f200007806b2000000000175a0000f993d4d08aac16a846044e7681180000edc00031f80000000bf00002e020a5eb380a6b580600000005d80009ed08ca4900000f046b0d2c692c5600022780008fc36f95bcd2c8be289a3e141816a000000000046218d8001212aed0310000df8000108a86c0009b459b0000000bcd000000048c2195b88f406386a417e923cfbc7fa000201c000000000159ceca8530000000aa80000000a0458e6c300013fc9a22c40001570c2c00017ba23d1e02310000f597e8052000000000074919c00000007ad00000000000000000b3d66200042c261086a7e40fa9c754ae0000ca144532a23d32f9d34d9050100000012bc0004c2a7b94dc7f351024807e01fc000000040a6e9000000000000013b1ab526a9c9000198904058e000000000008c16289fc5e2bc73410fac0007d70000000c9889c0000000d724703543044dde00000000012c219c0003190000b830000000928000000000000000000016f922a8545c69a855d26440a6015c0003560000fe55aa9a0000010026e00000000009720005379b3570c399000000000030449e9ed00005f91828e4802099a00031c841a02c5a481d575260643780
  | 29 => 0x581ab5800486a4b712788beb221e186b1514bc0585a9140005ac303800000000000026e0ce6000346800000065b00000005cc0005ee000118e2d25d5b080000025000051ca9000039f95c47921d64cca7dc3f44cf00031184800000000000000a490000000b860002c9800000011200025680001540000000000000000000066684552b17a40006be57298917dcbf012c00008a2000390836400000002984343d89425b7800000000028e0000000a370000dec5360866129c1d4d293011a87acf00a721ce98d47fe00013e8aa40003b000019746069b11bba00d53a00055428e810416102c1f380000003c5ac496e656b2d38ad123c0551f30000000000632800000038400021a0000000026800165200048130ac00000020780000001e45c90af48dc09800e0000000c091880000b3a00000000000b467a414138c000000000000000037245d00000000004e08001324bea23e96a80000000000000bb652e00004a8e1200036aaa000009041fe80a80000003c6977c0006b10002938fa65ad333182c97c00050a14e406aa715340000000000000142849c69f3c900007d274200000011cc62906802ac84200000017440000006090000000afb066802c00068600003d154e00053b96c4c20c4e00001c9272000000000171c000520116059079815398dd83031116d89c923078910f2c111a80b50001e645448fa40300000000005a81f201528830b912a11b49fc0002ab936c00000000000000b736e0f287a42e319893a968665300000000d87bc000036c000c6348f964404692900010b40002f43fb8c04000000000000000088133b000000014e0000000f2800000017997ae0000000000236000620800000000000000009440000001a0c0000004829e9110eb3e41e800151200039495d820801554b80000002d030515080003e220194bc00004c000152c00093a315000122000010f8000000b615ce28acb067701cb00000002b9023030118ca650000000000117000000000049d5a2283cfb800000018e423457d17980000001ca3f7298c1fe1b82151ff4c9c7522ffa0396f067459d94fc1d046559aacbcaa69da0e628c89c077824380248780fa5660378ce4000500039000046f04a800000000000000000000a00c7000000027c0000cf10f83d8000000111079c00010e06889862409784718c3d00000006588b51ba80000004f443c80006b00005a29f411e44e25a626301be7473620e0870ea460c59c48c7649b0000001816c4a00000016ba7e254c8001410000000199c00000000000d93f614b4ff8000000aa60002a4c000000417000000032e1701468b5e8b359599a4da897954d10502948b25f23011618c57000000000006e3181c7d660549000225105646b2f40ae9218000000000000048b0001d0400000002f1d703ba0
  | 30 => 0xa225650c98000018601083917eb190000000000000000071800000033f0034fd24a12bb800058600037c943c27600049896b800000038a1c980000005cfa2f05d20005df8000000000000115496a8525690b902280000000000000c7561b800000076c000118ce48aeb0000e681a80543f621e00005920ff00004c086436121180007a855f9c0c00075533baf6000000000026bd7c28e05dc237519464b624af74c18b4122720bce162a53a2ac08c821d71eaa538aea9080991f3530e43901d1a603c274b107a92d5820324452468f6c16608996d17643785309d6400000000019849b475e5acb01400061d49700000008343a7800122c0000348000c580123901e7c0008510ec000080a0000a0abf15c6ab52c1121063473b27b80015461f800000000004b022e31cc0007820002a7800000027caaa42040c75090000368000000000048625b1ec8000000371127800000000024a9cd400077d28b800094c00000000000004a700005580521d500031c4e1800000028a40007c426905a0e54a4850288286fe3dc4758c4cdfa1c144b0d3c3963000000cf53d26e03b924b49bc4d5000246cb964bc3582a4907696c5482d4c00000046f80000004dd00004f40e2a4d51c000174ec760000000bca0000000b05832c6900000011584cc54a2ea08d44532b52dc8d987370000e9d8445144711a20000a282b900000000004539f600000e52089aacb7884d1fd82e576a0000000734c7c8db13200009040005ab800000000000000000000000000c2d6beadd5150f346e8000353000000000052f2fa46c81d344700000000000000000000000000000000000015f80000000000000000dac58700006f80007570f90000e6c00000000005349de0330000000a392ac273c5f0000000000000000000004b4c36a1a613aa90b8243f0dd01040005850000a55348a0461f00000000ef0002d440008f11c2ad994a826e00021682421fd1f9315000000045c8f5d64e00000008a40003071ad064552a000183137000000021d0a907dac260a114585ec0906039c6039c000000066d2f492f24816e4cd6a3159f800104a000000000183e000000000000000011029400000002e3a8cc00069c00000014d61602c418f55567f500021c465200046b8ef136a7bb33a895c0000000002494cd8000000000000000000000002b6ad701588915f4c600000d7400008a00000000000001e00000c928590002e44000000577038c77c0011e70010eeebbe2f6a6f0000287000146d5d4078000000000017e4010a2c35e0bc29b0a780003ba2a5224cbea6c700000003ca0004cb071000000048680000960001be1594000bc900014ac0003b3000000165cc080000000000b2a3f3a5f81d80000de13140008703e38da46f2c5b47180000004540001134000b4e367800172003723f0
  | 31 => 0x1d1000000015d00008848ee0000000000000bf600024d982a5b35088000c662003b12961438444000212d80c74461d04242b000000b007cae044f00003583001d435730b13c40002a1800000013f1012c600000002d29b640705dd0002ea800000000000000600000000f8400000000021080001e25919fc000029c00ba734b3e00000000882780000000000000bf50b10000f3c2560000d88dda0003a617b800083800022110645cc0001c291800000000d1d8e8ad3000137c542a7500007e53f0809594297162a7391b329998ccaf90b780008129a816500012d2000494000046800051f800000000021d80000005c02c21bd82447fc5351e44bfa74a00000000001a6000022d6f40003112b846a2a964d9aa080000000690000000000000000020e0000000000000b1a000000142a81f10a000000000000000005a23415f380000001bd30f80008d200005a2d5800000049d800153096401c82855cc60d33891c538e01400016645a652100025c8b760004d502d94940000000220a402965ec81382e054600027ac0001b500008b40001305bda650d2a08e08091802b8ba5000230412841d62c89cc8305d96298ed8aaa49807e159813e40d45b1a78ff21573958274bb87e354580003b87ed3a70ec4d80000000000000000000018c45e00004eda7d15c442f109800000077e07013e10ce6e20af800147800012c800171400000019a13fc89a1a710d0bfc6500001678000005000156d7aa15a34795a17de23300000007ec8e94a300005c200037f80000000210002a880000b04c10000000b8500000000ca000607000000000000030a179c8a313081cc0006fa4b9800000000022d15e40002622130000000350000297d48e00000008180785a40d080000c80dd00021ed39c0004a490640002cc03c80000008a2558a35400088b00030e00000000f51c18896b0a000275c000ba048ca02880e000448203cf72b825a680000003c81fc0000c3840b617111d054425579a069140c7718a226d6669f22ad2b3c0003e423322e000087f000000067c4eb0c21c40000b960000000c8e0001c30000caac3b34daf8ca3e448634000055a8c8000000000071b2138000000aa155c8000362b7f00009b459aad15e0a88400000034980000008a800011ec8984ba000218d40c0000002a3000028433c960000000059003e18d60003b500000009320001bd00009e64a0a5298540004b40000000000000019d2ce28a2788a8c33e33435d00000000000000000cc01204be22456f84a502b07c44a0000096000151e000000000059c00000028c0000000000317566e5c84e18000000000000000000000000030a46900003cd0e700003530002d90000000177042000009100000002565240002c04000c33000258c0004ed572254c7060000001bf823c
  | 32 => 0x28b8562000187000000000063700000a267f1e88ff96b87433ce85492be26634903617b6911000000000009a46829e8bb43ad00017c472646c2cba7442208f90001ea50b64fa0c78000000c553f080000005330002ee44848470978000000000000087001419800000014b64101e593980000000000bc8fe4b7e3fa00000000005d99d858a2270509af140005574799ec90ecb093870cbcde250b58a18e188800032f068960c00040c8000ee2be019b80013522c600021c8f4000063812cc0000000002a800001433d10e9000083500000001ae7165b10ed00003f13baa45c72aba138015b80000000000dc1388c1e0888e94cc83ec1c080014c8000000000000000029a83f40000002f0226000075b37d800011e0000000000c6cba41b997889684433e02df48563dd47f97614f80000f480000009dd26099952424860ef124c08600000000016943c5000000000050656200018bc0000002bd02bc0000000000000000000000000000000023300007852bc20a4a1c85c3a98724b9a6871418608a8a9d30000da82b29230002d00000a852440000000bd612087d80004b611900000000002102d60000000000000000000014f80000000005b71fa000000000018042ca00038d0000d7e28000000000000005f100000000000003028b4c48c0000000f829273ea00000001b900011090eaacd631198cb420005de06b90d64724c02b787eea7e35a0000d94a520db2bc0d7a17c62c2d9d36eb8056409d4f207544108000000c4312f00000007190002640fde0000000ad400085e000000009e9df4f010189ca9915e78c2585a938321136c30e0ce32500017bc0000000000000bf200000011c8000098a04c00084a0002f404560002c0a60485078c154127133c60034a000000084e2500000a6400000005415609ca1598d1924c00000000000000000000234000c6100000000006eb58f8bf93d46ee457a8b49e62ea00005e0000aef56700012a40002dab05075e10a000000106e76710a80000003600000000000a170000501446a0300000004086bb0000000000000061951179000000000000000005b5a2a8000885556a4dcb388e82ca
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x4014d29788110d8d2100634a1d1004363485714d2912197018d2100526a52655c06348401499949957018d210053264a655c0634840145a959917018d2100516656645c063484014c9929917018d2100534259815c063484018d2866057018d2100570249815c063484011d1980857018d2100534a58215c063484018d1815c26018d2100616e15705806348401858855c16018d2100626e11705806348401898845c16018d2100632e097058063485718d2815c06018d21006342197044063484014d397d811018d2100694e0110d8f52484014d19018f715492100534640631c55248401a4b80483635492100694e0110d8d5248401e412044363549212e692d898018d5248401b402160063549210059464063dc552484016519018c7154921006a4e0110d8f42484014d19018f715092100534640631c54248401c44635487150921006a2e0120d8d4248401a93804436350921007a048110d8d42484b3a8b626006350921006e00858018d4248401a8463205525092129583a5b6354942484017099018d525092100549a5f815494248401e0463e0552509210078118c8154942484016919018f7150921004c9e6152dc54248401e046354b7150921005a4640631c54248401e0463548715092100634d8d801c5324840196152600714c92100668509801c53248519e0463549428c52103f091d9525093148519e0463549424c52103e5121d524c93148473a4486549324c52103f111d9524c9314840f98487509324c521186a1219424c9314840fc8476509324c521016329d98018e214840103f985d074594210048b648844416508401834872111059421005896488444165085d1651938c1105942100714e1d304416508401c50874c1105942100784e11304416508401e10844c110594211f714dc9304416508471c51724c1105942173f84d093044165085cfe11424c110594210040fe61751d5640840122d9221510590210060d21c854416408401625922151059021745a464e304416408401c93874c110590210072421d304416408401e13854c110590210078421530441640846bc93724c1105902117f245c93044164085cfe13524c1105902173f8454930441640840103e9815376550210040fa60545d9540840121f985505458c210049364885441630840128d922111058c2100591648854416308401a14852111058c21005a16488444163084016c3925c11058c210053264083dd921084018cb7660073484210048ee61541516008401c53955c5735802100714255715cd6008401c93945c5735802100724251715cd60085cf4d3925c5735802173d34649715cd6008401cc3825c5735802174730209715cd60085d1c53525c5735802174714549715cd60085d1c93425c5735802174724509715cd60085cf8d1875ce7158021
  | 1 => 0x273ea460530841648c80122d9221510592320060d21c85441648c80162592215105923200724e1d30441648c801c90874c1105923200784e1530441648c801e10854c1105923273f84d4930441648c9cfe11524c110592320040fa6054dd9548c80141d9315376552320040fa60545d9548c8014d1901c5305953200634a1d30441654c8014d1901c5305913200634a1d30441644c8014d191a0d701853200532249835c0614c8014d1918c9701853200436660325c0614c801c49520c9701853200722508325c0614c8014d1910c970185320052ca53515c0614c80147295d0570185320049964885440614c8012a59221110185320061c21570440614c8018b0845c1101853200692601305895294401e41304416254a5100698e0110d895254401e4130443625495100534e5d3044365904014d1974c110d9641006a2601305894290401e81304416250a4100e3421d304416550401aa3804436250941007a04c110d894250401551900c5759893100564640315d2624c401545920c5751893100554640315d4624c401585920c5741893100564640315d0624c4011d1980c5701893100561648315d2524c401591900c574949310053464031dd9524c4014c5920c4765493100534640311d9524c401645920c776549310059464031dd9524c401645920c4765493100594640311d9524c401a4b804c3625493100698e0110d89524c401e4130443625493126e92d8d80189524c401b4031600625493100551648315d6424c401551900c575909310053464031dd9424c4014c5920c4765093100534640311d9424c401685920c77650931005a464031dd9424c401685920c47650931005a4640311d9424c401a8b804c36250931006a8e0110d89424c401e8130443625093126ea2d8d80189424c401b8031600625093100634a59801c5324c40195352600714c93100654549801c5324c40199342600714c93100664509801c5324c4018d180d80714c93100634601601c5324c40103f985d07459721006926093084165c85d1651938c1105972113714e1d3044165c8579c50874c1105972100784e113044165c8401e10844c1105972173f84d093044165c85cfe11424c110597210040fe61751d564c8401a89824c21059321745a464e3044164c8441c93874c110593215df2421d3044164c8401e13854c11059321007842153044164c85cfe13524c1105932173f845493044164c840103e9815376553210050b64854dd954c840103e981517655321005946403159531c8401691900c5644c72100d34645704c363884014d2974c1105952100534a5d3044164484010db985c060d8d2100487e615415363484018d181dc270d8d2100634607708836348401c5385dc110d8d2100714217704436348401c9384dc110d8d2100724213704436348
  | 2 => 0x9d7e13544c110d95425b7285d12044365509d5e235448110d954200507a5c54dcd655080141e9715073595420050da5c54dc565508014369715071595420050ea5c54dc165508018d383e0770595420050ea5c541c16550801c18541cc70595420070c150711c1655080181c5421d305954200534640714c165508038c8874c12059542787821513048165508018345421d105954200534a5d3044165508014d0974c1105954200634a1d3044165508018d0874c1105954277f841513044165508034e097481105954277788151204416550801a0d5460b53d8d421d40f66365dd152509dbc52754c110d8542007145d530443615080126592215101854275f8499530443655080141e97197735954200507a5c651cd65508014369719771595420054964a85dc565508014369719471595420050ea5c65dc1655080198b83e0b705954200664e0f81dc165508019a382e0770595420050ea5c651c16550801c18651cc70595420070c194711c1655080181c6521d305954200564640714c165508015a1901c5205954217e2a21f60481655080158a974c120595420056225d30481655080198a874c1205954217e6221d3048165509d9e08654c1205954200760dc5304816550801d80714c120595420060d194874416550801592974c110595420056425d304416550801992874c110595420066421d3044165509d7e10654c1105954200760dc93044165508015a297481105954217d6825d2044165508019a28748110595420066821d2044165509d5e2065481105954200760dcd2044165509d3d807348110595420068359582d4f6350801894861c53058d4200564640714c163508015a1901c52058d4217d6225d30481635080198a874c12058d42005a2259304816350801d83714c12058d42007601c5304816350801992874c11058d4200760dc93044163508019a2874811058d420066821d20441635088182c76e0976549421d48b64a86dc5525087512d92e1d52d8542767429d5304836150801d09754c120d8542004c96488544361509d7d12754c110d8542007445d53044361509d5d227548110d8542007485d520443615085f98b874c1209854200562a5d304816150801588974c12058542006251cc864416150801592974c1105854217e6821d204416150801aa086481105854200760dcd2044161509d3d807348110585420058c241651446150801a25656085118542006615cd820c4615080199173600311854217d686457048061508013259221510185420040fe61741d1658c9cfa51814c210596320048b64884441658c8018348721110596320058964884441658c801c53874c110596320071421d30441658c801e13844c110596320078421130441658c9cfe13424c1105963273f8450930441658c80103f985d4755923
  | 3 => 0x5273fa0c81304416494801c93874c110592520072421d304416494801e13854c1105925275f842153044164949cfe13524c1105925273f84549304416494801e83304811059252007a04c1204416494801ca38748110592520072821d204416494801e23854811059252757882152044164949e1e0a544c120d915277f849513044364549dde225448110d9152797249d1304436154801c91744c110d85520050e650505c061548012a592211101855277f8499130443645480141e97193735915200507a5c641cd64548014369719371591520054964a84dc564548014369719071591520050ea5c64dc1645480194b83e0b705915200654e0f81dc1645480196382e0770591520050ea5c641c16454801c18641cc70591520070c190711c1645480181c6421d305915200554640714c16454801561901c520591521c61a21f60481645480154a974c120591520055225d30481645480194a874c120591521c65221d3048164549e1e08644c1205915200750dc5304816454801d40714c120591520060d190874416454801552974c110591520055425d304416454801952874c110591520065421d3044164549dfe10644c1105915200750dc93044164548015629748110591521c55825d2044164548019628748110591520065821d2044164549dde2064481105915200750dcd2044164549e3d4073481105915200615218714c16354801551901c53058d5200558640714816354871548974c12058d5200652a1d304816354801648964c12058d5200750dc5304816354801d40714c12058d5200654a1d304416354801d43724c11058d5200658a1d204416354801960874811058d52787429d1304836154801d09744c120d8552004c96488444361549dfd12744c110d8552007445d13044361549ddd227448110d8552007485d120443615487194b874c1209855200552a5d304816154801548974c1205855200554a5d30441615487196087481105855200750dcd2044161549e3d407348110585520058c241641046154801a25646084118552006515cd820c461548019517360031185520060e611701806154801868865c120185521c5586457048061548013259221110185525a59264e304816590801661918c12059642007904c120c416590801a49824c210596420069260d20841659096da618148210596420060d2108744165909d1651938c110596420059864a3044165909cfe43204c1105964200714e1d304416590801c50874c1105964200784e113044165909dfe10844c1105964273f84d093044165909cfe11424c1105964200790cc1204416590801e4130481105964200718e1d204416590801c6087481105964200788e112044165909dde208448110596425a7225d13048365509d9e0b544c120d954273f245d130443655
  | 4 => 0x4f000000369d00020334000003d16283a6ccd96a86000ca040b9b0400000d29d800298878a612000513ba3a0000000000000000000001a000004e80000000423b4000002e80000000000000000000000003a2841fe003240035c8238c4b07a00230000000010c00000153c402936da18a29142a2afa0000400182e4000001e047140a49bc6c956de34624aaea51247083a000006ab9c002b07d800020ece2000001dc00186000000014c000000000000000000000000000000542380023a0000093800b280000000001f20000016b000036c4695298ba4658b209acc391e8c70bc8097c000000000000000d600007aaa1da12ecb06898d02b26042814001163f03e2f80067a7a000000000064316003601b800bb888739c04c8a8002e80302a6d2c62dad46898e00060692be68342e6b4001b2a74b121c2247f24ac7b84a1204af00000000ec2f81e00081b2e0004e0d1d400000000000008e5537a5200028800df074b91e20031af1800230005d0002b80000086000d20014a9600027000759de0014e0000000000600f09c18897000002e2aa1f00700000000000000000064b202590400000c41f4889107980000000db97a1a00000000002ac992b2000000023c00000cf0e20023200398d5000002680b056e824600000002441a80271800199ec060000c994002760000010a2a0000000130000005680033a78000000029a00000d430c20b4ce2ac8000000005c00000003a6b4800bc800ce000000000000026000000005a2f600146d9000b6800000000000066000000000000037000000b0000e60000000000630001926e9a92a00000003b83eb5e0000000000000009cafe48000000000000000000000000024000000000006b3628d3a8000909499a00102a882e0000000000bb0008da14ad0c6efab6e385eb583cd68f6cc8000013e1cb66003c086bacc8a5000003028040300001c0203000008050000002403004020000000000008010040101c0300007004010240d0040600c0700400000010380001c0200c010000200c03004010040004803004030100900c0000000020000080002002008010000000400000070000200002014030180300800004000000c0000700000054010000001404000000000000000010000000600807000030000200c0000000000060040101c0b02c00004010000c000000600100405014010000301003000020000c00c000040100000000000000079f8415130443625500141e9615373589540050da5854dc562550014369615071589540050ea5854dc162551e5c51754c110d855476f245d130443615500141e9615173985540050ea58545c261550034d0974c11059543005a8646304816494801e81304831059252006a2609308416494801a898348210592520060d2148744164948016a1928c110592
  | 5 => 0x132546d8000033000000000c4001b8002165e0aa7b9c800000000b80e0000020a00000002e018b020000000000ea800d3800002ea0021c0000000000000f81489a000e06ba007e1660016e0029e3780e32800000003580000000000001617200000e4bbc831ba9f00041b1400000003520038636a4899800000008a00000000d20000033aa5b56210c2a80105f8002d382eda8e000000025e478006a1cc6c06c002a4bf00000000000000000000000c28003ab764bace769123c8205900000396cfad85b022df9ea462d00c0000000014372a4344118005622c3f976a3000282f000000dd1d030394e0282a18eedc2f48b800b73260019c4500058000003aec6100b0800000000a00000000002c004800003c200000000d4001229590e7900000308a982400000a2000930001f000969ca9f934a01700015eae184cb00069b0edaa20aeac422816710d84e0948fb9e27800128001112800000a70006f87e570000000000000b7800000007e800498cc0000000000908c800000
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x75491003c128002928e1a0c000000002730ac000400001300640043e91510008859634780002ac8e2f1200d97000428042503ae0098908180033100c16ac000118001004008a00440802000883000000038108521d304416494801418d00c843a20b22a400d04190974c11059152007020c843a60882c8a900305086640714c16354801510502c8c108230aa400e04210874c11059642005063402a10e882caa10034105425d304416550801c082a10e98220b2a8400a0c6806521d1059542006820ca4ba60882caa10038106521d3044165508018484332038a60b1a8400a2468073219105854200544140b2b04288c2a10030248764884441658c801c084390898220b2c6400b80688844c110596320060490ec910a882c9190038108721530441648c801700d110a98220b246400c12661520c9701853200611330a1064b80c29900344152644325c0614c801a40a1322192e030a6400a18688855c1101853200514344422e0880c299002341a90c580189524c4011c0d4862c00c4a1262008d06a42160063549210058834031aa438a8490802381a90858018d4248401540d00c640aa4a124200d01a5c63e055250921005c034031f02a928490802e01a018c815494248401903cc0c6a96e2a124200b806806354b7150921005c034031aa438a849080302487648844416508401c084390898220b284200b80688844c110594210060490ec910a882c81080381087215304416408401700d110a98220b204200a81688852111058c210064090ac9108882c610802c41a2255715cd6008401a084a928b8ae6b004200b20688945c57358021
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x80280013a30018008000680087688844c1105963200680087688854c110592320064029768063e055250921006203986806354b715092100680087688844c1105942100680087688854c11059021005401b2254945c5735802100640095688945c57358021
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x4
  | 3 => 0x5
  | 4 => 0x6
  | 5 => 0x2
  | 6 => 0x209
  | 7 => 0x3
  | 8 => 0x20c
  | 9 => 0x20d
  | 10 => 0x20e
  | 11 => 0x1409
  | 12 => 0xb09
  | 13 => 0xb0c
  | 14 => 0xb0d
  | 15 => 0xb0e
  | 16 => 0x140c
  | 17 => 0x140d
  | 18 => 0x140e
  | 19 => 0x1549
  | 20 => 0x154c
  | 21 => 0x154d
  | 22 => 0x154e
  | 23 => 0xb49
  | 24 => 0xb4d
  | 25 => 0xb4e
  | 26 => 0x1449
  | 27 => 0x144d
  | 28 => 0x144e
  | 29 => 0xb89
  | 30 => 0xb8c
  | 31 => 0xb8e
  | 32 => 0x1489
  | 33 => 0x148c
  | 34 => 0x148e
  | 35 => 0xbc9
  | 36 => 0xbcc
  | 37 => 0xbcd
  | 38 => 0x14c9
  | 39 => 0x14cc
  | 40 => 0x14cd
  | 41 => 0xcc9
  | 42 => 0xccd
  | 43 => 0xcce
  | 44 => 0x15c9
  | 45 => 0x15cd
  | 46 => 0x15ce
  | 47 => 0xd09
  | 48 => 0xd0c
  | 49 => 0xd0e
  | 50 => 0x1609
  | 51 => 0x160c
  | 52 => 0x160e
  | 53 => 0x1889
  | 54 => 0x188c
  | 55 => 0x188e
  | 56 => 0xd49
  | 57 => 0xd4c
  | 58 => 0xd4d
  | 59 => 0x1649
  | 60 => 0x164c
  | 61 => 0x164d
  | 62 => 0x1a09
  | 63 => 0x1a0c
  | 64 => 0x1a0d
  | 65 => 0xe89
  | 66 => 0xe8e
  | 67 => 0xec9
  | 68 => 0xecd
  | 69 => 0x1049
  | 70 => 0x104c
  | 71 => 0xb0211
  | 72 => 0x140b11
  | 73 => 0xb4b11
  | 74 => 0xb0b51
  | 75 => 0x144b11
  | 76 => 0xb1451
  | 77 => 0x144b
  | 78 => 0xd0b11
  | 79 => 0x188b11
  | 80 => 0xd4b11
  | 81 => 0x1a0b11
  | 82 => 0x24b
  | 83 => 0x155411
  | 84 => 0xb5411
  | 85 => 0x140b51
  | 86 => 0x145411
  | 87 => 0x141451
  | 88 => 0xd1411
  | 89 => 0xd1414
  | 90 => 0x189411
  | 91 => 0xd5411
  | 92 => 0xd5414
  | 93 => 0x1a1411
  | 94 => 0x144b51
  | 95 => 0xb5451
  | 96 => 0x28c
  | 97 => 0x2cc
  | 98 => 0xccb51
  | 99 => 0xb4cd1
  | 100 => 0xd0b51
  | 101 => 0x188b51
  | 102 => 0xd4b51
  | 103 => 0x1a0b51
  | 104 => 0x184c
  | 105 => 0x19cc
  | 106 => 0x15d451
  | 107 => 0x1455d1
  | 108 => 0xd1451
  | 109 => 0x189451
  | 110 => 0xd5451
  | 111 => 0x1a1451
  | 112 => 0x148b91
  | 113 => 0x2cd
  | 114 => 0xd0b91
  | 115 => 0xd4b91
  | 116 => 0x1a0b91
  | 117 => 0x16cd
  | 118 => 0x19cd
  | 119 => 0xd1491
  | 120 => 0xd5491
  | 121 => 0x1a1491
  | 122 => 0x105491
  | 123 => 0x104a
  | 124 => 0x14cbd1
  | 125 => 0xd0bd1
  | 126 => 0x188bd1
  | 127 => 0xd4bd1
  | 128 => 0x16ce
  | 129 => 0x184e
  | 130 => 0xd14d1
  | 131 => 0x1894d1
  | 132 => 0xd54d1
  | 133 => 0x1054d1
  | 134 => 0xd0cd1
  | 135 => 0x188cd1
  | 136 => 0xd4cd1
  | 137 => 0x1a0cd1
  | 138 => 0xd4d11
  | 139 => 0xd0d51
  | 140 => 0xd4d14
  | 141 => 0x1a0d11
  | 142 => 0x1a0d14
  | 143 => 0xecd11
  | 144 => 0xd0ed1
  | 145 => 0xe8d11
  | 146 => 0xd0e91
  | 147 => 0x170d
  | 148 => 0x104d11
  | 149 => 0xd1051
  | 150 => 0xd5891
  | 151 => 0x188d51
  | 152 => 0xd5894
  | 153 => 0x1a1891
  | 154 => 0x1a1894
  | 155 => 0xed891
  | 156 => 0x188ed1
  | 157 => 0xe8d51
  | 158 => 0xd4e91
  | 159 => 0xecd51
  | 160 => 0xd4ed1
  | 161 => 0x170e
  | 162 => 0x104d51
  | 163 => 0xd5051
  | 164 => 0xe9a11
  | 165 => 0x1a0e91
  | 166 => 0x24d
  | 167 => 0x104e91
  | 168 => 0x1a8c
  | 169 => 0x194c
  | 170 => 0x1a4d
  | 171 => 0x17cd
  | 172 => 0x24e
  | 173 => 0x104ed1
  | 174 => 0x18ce
  | 175 => 0x178e
  | 176 => 0x28e
  | 177 => 0x44d
  | 178 => 0x138b
  | 179 => 0x168b
  | 180 => 0x9cb
  | 181 => 0x21711
  | 182 => 0x94b
  | 183 => 0xd4d0b19
  | 184 => 0x138c
  | 185 => 0x94c
  | 186 => 0x140d54
  | 187 => 0x289
  | 188 => 0x2c9
  | 189 => 0x20d14
  | 190 => 0x140d14
  | 191 => 0x20d54
  | 192 => 0x94d14
  | 193 => 0x138d14
  | 194 => 0x94d54
  | 195 => 0x138d54
  | 196 => 0x98d14
  | 197 => 0x150d14
  | 198 => 0x94d16
  | 199 => 0x138d16
  | 200 => 0x98d16
  | 201 => 0x150d16
  | 202 => 0x9cd16
  | 203 => 0x168d16
  | 204 => 0x188d14
  | 205 => 0x188d16
  | 206 => 0x94e
  | 207 => 0x138e
  | 208 => 0x9ce
  | 209 => 0x168e
  | 210 => 0xd0d54
  | 211 => 0x94d55
  | 212 => 0x138d55
  | 213 => 0x98d55
  | 214 => 0x150d55
  | 215 => 0x9cd55
  | 216 => 0x168d55
  | 217 => 0x1a0d55
  | 218 => 0x98d54
  | 219 => 0x150d54
  | 220 => 0x1a0d54
  | 221 => 0x94d
  | 222 => 0x138d
  | 223 => 0x9cd
  | 224 => 0x168d
  | 225 => 0x1a57d5
  | 226 => 0x1a9954
  | 227 => 0x95a15
  | 228 => 0x139a15
  | 229 => 0x9da15
  | 230 => 0x169a15
  | 231 => 0x9c953
  | 232 => 0x949d3
  | 233 => 0x9894d1c
  | 234 => 0x9894d1e
  | 235 => 0x9c94d1e
  | 236 => 0x9c98d1e
  | 237 => 0x9c956
  | 238 => 0x9894d5d
  | 239 => 0x9c94d5d
  | 240 => 0x9c98d5d
  | 241 => 0x9894d5c
  | 242 => 0x9c955
  | 243 => 0x9c95a1d
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 68
  | 7 => 2060
  | 6 => 6080
  | 5 => 3192
  | 4 => 484
  | 3 => 51
  | 2 => 8
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
  | 2 => packedAt gbK2 (i*92) 83
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
  | 2 => gbHint (packedAt gbK2 (i*92+83) 9)
  | _ => 0
def gbI (k h : Nat) : Nat :=
  match k with
  | 9 => packedAt gbK9 (16+((h/1+packedAt gbK9 (15+(h % 1)*1) 1) % 2)*1) 1
  | 8 => packedAt gbK8 (1922+((h/22+packedAt gbK8 (1768+(h % 22)*7) 7) % 82)*8) 8
  | 7 => packedAt gbK7 (84452+((h/686+packedAt gbK7 (76220+(h % 686)*12) 12) % 3291)*13) 13
  | 6 => packedAt gbK6 (318178+((h/2026+packedAt gbK6 (291840+(h % 2026)*13) 13) % 7297)*14) 14
  | 5 => packedAt gbK5 (202160+((h/1064+packedAt gbK5 (188328+(h % 1064)*13) 13) % 5098)*13) 13
  | 4 => packedAt gbK4 (35490+((h/161+packedAt gbK4 (33880+(h % 161)*10) 10) % 849)*10) 10
  | 3 => packedAt gbK3 (4250+((h/17+packedAt gbK3 (4131+(h % 17)*7) 7) % 74)*7) 7
  | 2 => packedAt gbK2 (746+((h/2+packedAt gbK2 (736+(h % 2)*5) 5) % 17)*4) 4
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x1fffe1c1f07f87fffe1e03c07c51233e467e93
  | 1 => 0xe1e03e01ff83f8780fe003ff80ae3cd879b31c
  | 2 => 0xfe003ffe0003ff800fffffffff30c0e181c3ff
  | 3 => 0x3ffffffc00000ffffc0003c0ff01fe03e0
  | 4 => 0x3ffffffffffff000000003ff0001fffc00
  | 5 => 0xffffc000000000000000000003fffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x2a1a040321480a867120a411800210a421691
  | 1 => 0x20c2a600d2918830ab30129708062c5858b314
  | 2 => 0x54040892000255010044a128613040a081402a
  | 3 => 0x8933656b5800224d995a0212c0b7016e03c0
  | 4 => 0x10101db98c6366478000600c23fb0001b5e800
  | 5 => 0x991e0030084044040001803043fddaf4000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeefeeafeeaf0e0feeefeeafeeaf0e0feeefeeafeeaf0e0feeefeeafeeaf0e0feeefeeafeeaf0e0feeefeeafeeaf0e0feeefeeafeeaf0e0feeefeeafeeaf0e0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_17005
namespace PEqualNP.Outside.L_meta_17005
open PEqualNP.Outside.L_meta_17005.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_2_0 : Interval s0Atlas 2 0 10 := block_range (n:=10) (by decide +kernel)
theorem alls0_2 : Interval s0Atlas 2 0 10 := bs0_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_32 : Interval s0Atlas 3 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_64 : Interval s0Atlas 3 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_96 : Interval s0Atlas 3 96 16 := block_range (n:=16) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 112 := (concat (concat bs0_3_0 bs0_3_32) (concat bs0_3_64 bs0_3_96))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_0 : Interval s0Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_32 : Interval s0Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_64 : Interval s0Atlas 4 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_96 : Interval s0Atlas 4 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_128 : Interval s0Atlas 4 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_160 : Interval s0Atlas 4 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_192 : Interval s0Atlas 4 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_224 : Interval s0Atlas 4 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_256 : Interval s0Atlas 4 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_288 : Interval s0Atlas 4 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_320 : Interval s0Atlas 4 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_352 : Interval s0Atlas 4 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_384 : Interval s0Atlas 4 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_416 : Interval s0Atlas 4 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_448 : Interval s0Atlas 4 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_480 : Interval s0Atlas 4 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_512 : Interval s0Atlas 4 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_544 : Interval s0Atlas 4 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_576 : Interval s0Atlas 4 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_608 : Interval s0Atlas 4 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_640 : Interval s0Atlas 4 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_672 : Interval s0Atlas 4 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_704 : Interval s0Atlas 4 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_736 : Interval s0Atlas 4 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_768 : Interval s0Atlas 4 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_800 : Interval s0Atlas 4 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_832 : Interval s0Atlas 4 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_864 : Interval s0Atlas 4 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_896 : Interval s0Atlas 4 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_928 : Interval s0Atlas 4 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_960 : Interval s0Atlas 4 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_992 : Interval s0Atlas 4 992 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1024 : Interval s0Atlas 4 1024 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1056 : Interval s0Atlas 4 1056 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1088 : Interval s0Atlas 4 1088 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1120 : Interval s0Atlas 4 1120 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1152 : Interval s0Atlas 4 1152 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1184 : Interval s0Atlas 4 1184 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1216 : Interval s0Atlas 4 1216 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1248 : Interval s0Atlas 4 1248 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1280 : Interval s0Atlas 4 1280 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1312 : Interval s0Atlas 4 1312 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_4_1344 : Interval s0Atlas 4 1344 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 1345 := (concat (concat (concat (concat (concat bs0_4_0 bs0_4_32) (concat bs0_4_64 (concat bs0_4_96 bs0_4_128))) (concat (concat bs0_4_160 bs0_4_192) (concat bs0_4_224 (concat bs0_4_256 bs0_4_288)))) (concat (concat (concat bs0_4_320 bs0_4_352) (concat bs0_4_384 (concat bs0_4_416 bs0_4_448))) (concat (concat bs0_4_480 (concat bs0_4_512 bs0_4_544)) (concat bs0_4_576 (concat bs0_4_608 bs0_4_640))))) (concat (concat (concat (concat bs0_4_672 bs0_4_704) (concat bs0_4_736 (concat bs0_4_768 bs0_4_800))) (concat (concat bs0_4_832 (concat bs0_4_864 bs0_4_896)) (concat bs0_4_928 (concat bs0_4_960 bs0_4_992)))) (concat (concat (concat bs0_4_1024 bs0_4_1056) (concat bs0_4_1088 (concat bs0_4_1120 bs0_4_1152))) (concat (concat bs0_4_1184 (concat bs0_4_1216 bs0_4_1248)) (concat bs0_4_1280 (concat bs0_4_1312 bs0_4_1344))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_0 : Interval s0Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_32 : Interval s0Atlas 5 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_64 : Interval s0Atlas 5 64 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_96 : Interval s0Atlas 5 96 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_128 : Interval s0Atlas 5 128 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_160 : Interval s0Atlas 5 160 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_192 : Interval s0Atlas 5 192 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_224 : Interval s0Atlas 5 224 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_256 : Interval s0Atlas 5 256 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_288 : Interval s0Atlas 5 288 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_320 : Interval s0Atlas 5 320 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_352 : Interval s0Atlas 5 352 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_384 : Interval s0Atlas 5 384 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_416 : Interval s0Atlas 5 416 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_448 : Interval s0Atlas 5 448 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_480 : Interval s0Atlas 5 480 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_512 : Interval s0Atlas 5 512 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_544 : Interval s0Atlas 5 544 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_576 : Interval s0Atlas 5 576 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_608 : Interval s0Atlas 5 608 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_640 : Interval s0Atlas 5 640 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_672 : Interval s0Atlas 5 672 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_704 : Interval s0Atlas 5 704 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_736 : Interval s0Atlas 5 736 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_768 : Interval s0Atlas 5 768 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_800 : Interval s0Atlas 5 800 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_832 : Interval s0Atlas 5 832 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_864 : Interval s0Atlas 5 864 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_896 : Interval s0Atlas 5 896 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_928 : Interval s0Atlas 5 928 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_960 : Interval s0Atlas 5 960 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_5_992 : Interval s0Atlas 5 992 25 := block_range (n:=25) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 1017 := (concat (concat (concat (concat (concat bs0_5_0 bs0_5_32) (concat bs0_5_64 bs0_5_96)) (concat (concat bs0_5_128 bs0_5_160) (concat bs0_5_192 bs0_5_224))) (concat (concat (concat bs0_5_256 bs0_5_288) (concat bs0_5_320 bs0_5_352)) (concat (concat bs0_5_384 bs0_5_416) (concat bs0_5_448 bs0_5_480)))) (concat (concat (concat (concat bs0_5_512 bs0_5_544) (concat bs0_5_576 bs0_5_608)) (concat (concat bs0_5_640 bs0_5_672) (concat bs0_5_704 bs0_5_736))) (concat (concat (concat bs0_5_768 bs0_5_800) (concat bs0_5_832 bs0_5_864)) (concat (concat bs0_5_896 bs0_5_928) (concat bs0_5_960 bs0_5_992)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_0 : Interval s0Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_32 : Interval s0Atlas 6 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls0_6 : Interval s0Atlas 6 0 48 := (concat bs0_6_0 bs0_6_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_7_0 : Interval s0Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_7 : Interval s0Atlas 7 0 1 := bs0_7_0
theorem alls0 : ∀ k ≤ 7, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_2 i (by omega) hi
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
  · exact alls0_6 i (by omega) hi
  · exact alls0_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_3_0 : Interval s1Atlas 3 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_3 : Interval s1Atlas 3 0 1 := bs1_3_0
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
  · exact alls1_3 i (by omega) hi
  · exact alls1_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 2 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 6 := bs2_4_0
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
theorem bs3_3_0 : Interval s3Atlas 3 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 24 := bs3_3_0
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
theorem bs3_4_96 : Interval s3Atlas 4 96 21 := block_range (n:=21) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 117 := (concat (concat bs3_4_0 bs3_4_32) (concat bs3_4_64 bs3_4_96))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 14 := block_range (n:=14) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 46 := (concat bs3_5_0 bs3_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 1 := bs3_6_0
theorem alls3 : ∀ k ≤ 6, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_2 i (by omega) hi
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
  · exact alls3_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_2_0 : Interval s4Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls4_2 : Interval s4Atlas 2 0 4 := bs4_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 24 := bs4_3_0
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
theorem bs4_4_96 : Interval s4Atlas 4 96 21 := block_range (n:=21) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 117 := (concat (concat bs4_4_0 bs4_4_32) (concat bs4_4_64 bs4_4_96))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 14 := block_range (n:=14) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 46 := (concat bs4_5_0 bs4_5_32)
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
theorem bs5_2_0 : Interval s5Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls5_2 : Interval s5Atlas 2 0 4 := bs5_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 24 := block_range (n:=24) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 24 := bs5_3_0
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
theorem bs5_4_96 : Interval s5Atlas 4 96 21 := block_range (n:=21) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 117 := (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 bs5_4_96))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 14 := block_range (n:=14) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 46 := (concat bs5_5_0 bs5_5_32)
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
theorem bgb_2_0 : Interval gbAtlas 2 0 8 := block_range (n:=8) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 8 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_32 : Interval gbAtlas 3 32 19 := block_range (n:=19) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 51 := (concat bgb_3_0 bgb_3_32)
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
theorem bgb_4_480 : Interval gbAtlas 4 480 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 484 := (concat (concat (concat (concat bgb_4_0 bgb_4_32) (concat bgb_4_64 bgb_4_96)) (concat (concat bgb_4_128 bgb_4_160) (concat bgb_4_192 bgb_4_224))) (concat (concat (concat bgb_4_256 bgb_4_288) (concat bgb_4_320 bgb_4_352)) (concat (concat bgb_4_384 bgb_4_416) (concat bgb_4_448 bgb_4_480))))
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
theorem bgb_5_3168 : Interval gbAtlas 5 3168 24 := block_range (n:=24) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 3192 := (concat (concat (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat bgb_5_288 (concat bgb_5_320 bgb_5_352)))) (concat (concat (concat bgb_5_384 (concat bgb_5_416 bgb_5_448)) (concat bgb_5_480 (concat bgb_5_512 bgb_5_544))) (concat (concat bgb_5_576 (concat bgb_5_608 bgb_5_640)) (concat (concat bgb_5_672 bgb_5_704) (concat bgb_5_736 bgb_5_768))))) (concat (concat (concat (concat bgb_5_800 (concat bgb_5_832 bgb_5_864)) (concat bgb_5_896 (concat bgb_5_928 bgb_5_960))) (concat (concat bgb_5_992 (concat bgb_5_1024 bgb_5_1056)) (concat bgb_5_1088 (concat bgb_5_1120 bgb_5_1152)))) (concat (concat (concat bgb_5_1184 (concat bgb_5_1216 bgb_5_1248)) (concat bgb_5_1280 (concat bgb_5_1312 bgb_5_1344))) (concat (concat bgb_5_1376 (concat bgb_5_1408 bgb_5_1440)) (concat (concat bgb_5_1472 bgb_5_1504) (concat bgb_5_1536 bgb_5_1568)))))) (concat (concat (concat (concat (concat bgb_5_1600 (concat bgb_5_1632 bgb_5_1664)) (concat bgb_5_1696 (concat bgb_5_1728 bgb_5_1760))) (concat (concat bgb_5_1792 (concat bgb_5_1824 bgb_5_1856)) (concat bgb_5_1888 (concat bgb_5_1920 bgb_5_1952)))) (concat (concat (concat bgb_5_1984 (concat bgb_5_2016 bgb_5_2048)) (concat bgb_5_2080 (concat bgb_5_2112 bgb_5_2144))) (concat (concat bgb_5_2176 (concat bgb_5_2208 bgb_5_2240)) (concat (concat bgb_5_2272 bgb_5_2304) (concat bgb_5_2336 bgb_5_2368))))) (concat (concat (concat (concat bgb_5_2400 (concat bgb_5_2432 bgb_5_2464)) (concat bgb_5_2496 (concat bgb_5_2528 bgb_5_2560))) (concat (concat bgb_5_2592 (concat bgb_5_2624 bgb_5_2656)) (concat bgb_5_2688 (concat bgb_5_2720 bgb_5_2752)))) (concat (concat (concat bgb_5_2784 (concat bgb_5_2816 bgb_5_2848)) (concat bgb_5_2880 (concat bgb_5_2912 bgb_5_2944))) (concat (concat bgb_5_2976 (concat bgb_5_3008 bgb_5_3040)) (concat (concat bgb_5_3072 bgb_5_3104) (concat bgb_5_3136 bgb_5_3168)))))))
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5376 : Interval gbAtlas 6 5376 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5408 : Interval gbAtlas 6 5408 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5440 : Interval gbAtlas 6 5440 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5472 : Interval gbAtlas 6 5472 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5504 : Interval gbAtlas 6 5504 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5536 : Interval gbAtlas 6 5536 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5568 : Interval gbAtlas 6 5568 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5600 : Interval gbAtlas 6 5600 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5632 : Interval gbAtlas 6 5632 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5664 : Interval gbAtlas 6 5664 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5696 : Interval gbAtlas 6 5696 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5728 : Interval gbAtlas 6 5728 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5760 : Interval gbAtlas 6 5760 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5792 : Interval gbAtlas 6 5792 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5824 : Interval gbAtlas 6 5824 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5856 : Interval gbAtlas 6 5856 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5888 : Interval gbAtlas 6 5888 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5920 : Interval gbAtlas 6 5920 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5952 : Interval gbAtlas 6 5952 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_5984 : Interval gbAtlas 6 5984 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6016 : Interval gbAtlas 6 6016 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_6_6048 : Interval gbAtlas 6 6048 32 := block_range (n:=32) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 6080 := (concat (concat (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 (concat bgb_6_192 bgb_6_224)) (concat bgb_6_256 (concat bgb_6_288 bgb_6_320)))) (concat (concat (concat bgb_6_352 (concat bgb_6_384 bgb_6_416)) (concat bgb_6_448 (concat bgb_6_480 bgb_6_512))) (concat (concat bgb_6_544 (concat bgb_6_576 bgb_6_608)) (concat bgb_6_640 (concat bgb_6_672 bgb_6_704))))) (concat (concat (concat (concat bgb_6_736 (concat bgb_6_768 bgb_6_800)) (concat bgb_6_832 (concat bgb_6_864 bgb_6_896))) (concat (concat bgb_6_928 (concat bgb_6_960 bgb_6_992)) (concat bgb_6_1024 (concat bgb_6_1056 bgb_6_1088)))) (concat (concat (concat bgb_6_1120 (concat bgb_6_1152 bgb_6_1184)) (concat bgb_6_1216 (concat bgb_6_1248 bgb_6_1280))) (concat (concat bgb_6_1312 (concat bgb_6_1344 bgb_6_1376)) (concat bgb_6_1408 (concat bgb_6_1440 bgb_6_1472)))))) (concat (concat (concat (concat (concat bgb_6_1504 (concat bgb_6_1536 bgb_6_1568)) (concat bgb_6_1600 (concat bgb_6_1632 bgb_6_1664))) (concat (concat bgb_6_1696 (concat bgb_6_1728 bgb_6_1760)) (concat bgb_6_1792 (concat bgb_6_1824 bgb_6_1856)))) (concat (concat (concat bgb_6_1888 (concat bgb_6_1920 bgb_6_1952)) (concat bgb_6_1984 (concat bgb_6_2016 bgb_6_2048))) (concat (concat bgb_6_2080 (concat bgb_6_2112 bgb_6_2144)) (concat bgb_6_2176 (concat bgb_6_2208 bgb_6_2240))))) (concat (concat (concat (concat bgb_6_2272 (concat bgb_6_2304 bgb_6_2336)) (concat bgb_6_2368 (concat bgb_6_2400 bgb_6_2432))) (concat (concat bgb_6_2464 (concat bgb_6_2496 bgb_6_2528)) (concat bgb_6_2560 (concat bgb_6_2592 bgb_6_2624)))) (concat (concat (concat bgb_6_2656 (concat bgb_6_2688 bgb_6_2720)) (concat bgb_6_2752 (concat bgb_6_2784 bgb_6_2816))) (concat (concat bgb_6_2848 (concat bgb_6_2880 bgb_6_2912)) (concat bgb_6_2944 (concat bgb_6_2976 bgb_6_3008))))))) (concat (concat (concat (concat (concat (concat bgb_6_3040 bgb_6_3072) (concat bgb_6_3104 (concat bgb_6_3136 bgb_6_3168))) (concat (concat bgb_6_3200 (concat bgb_6_3232 bgb_6_3264)) (concat bgb_6_3296 (concat bgb_6_3328 bgb_6_3360)))) (concat (concat (concat bgb_6_3392 (concat bgb_6_3424 bgb_6_3456)) (concat bgb_6_3488 (concat bgb_6_3520 bgb_6_3552))) (concat (concat bgb_6_3584 (concat bgb_6_3616 bgb_6_3648)) (concat bgb_6_3680 (concat bgb_6_3712 bgb_6_3744))))) (concat (concat (concat (concat bgb_6_3776 (concat bgb_6_3808 bgb_6_3840)) (concat bgb_6_3872 (concat bgb_6_3904 bgb_6_3936))) (concat (concat bgb_6_3968 (concat bgb_6_4000 bgb_6_4032)) (concat bgb_6_4064 (concat bgb_6_4096 bgb_6_4128)))) (concat (concat (concat bgb_6_4160 (concat bgb_6_4192 bgb_6_4224)) (concat bgb_6_4256 (concat bgb_6_4288 bgb_6_4320))) (concat (concat bgb_6_4352 (concat bgb_6_4384 bgb_6_4416)) (concat bgb_6_4448 (concat bgb_6_4480 bgb_6_4512)))))) (concat (concat (concat (concat (concat bgb_6_4544 (concat bgb_6_4576 bgb_6_4608)) (concat bgb_6_4640 (concat bgb_6_4672 bgb_6_4704))) (concat (concat bgb_6_4736 (concat bgb_6_4768 bgb_6_4800)) (concat bgb_6_4832 (concat bgb_6_4864 bgb_6_4896)))) (concat (concat (concat bgb_6_4928 (concat bgb_6_4960 bgb_6_4992)) (concat bgb_6_5024 (concat bgb_6_5056 bgb_6_5088))) (concat (concat bgb_6_5120 (concat bgb_6_5152 bgb_6_5184)) (concat bgb_6_5216 (concat bgb_6_5248 bgb_6_5280))))) (concat (concat (concat (concat bgb_6_5312 (concat bgb_6_5344 bgb_6_5376)) (concat bgb_6_5408 (concat bgb_6_5440 bgb_6_5472))) (concat (concat bgb_6_5504 (concat bgb_6_5536 bgb_6_5568)) (concat bgb_6_5600 (concat bgb_6_5632 bgb_6_5664)))) (concat (concat (concat bgb_6_5696 (concat bgb_6_5728 bgb_6_5760)) (concat bgb_6_5792 (concat bgb_6_5824 bgb_6_5856))) (concat (concat bgb_6_5888 (concat bgb_6_5920 bgb_6_5952)) (concat bgb_6_5984 (concat bgb_6_6016 bgb_6_6048))))))))
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
theorem bgb_7_2048 : Interval gbAtlas 7 2048 12 := block_range (n:=12) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2060 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 bgb_7_224))) (concat (concat (concat bgb_7_256 bgb_7_288) (concat bgb_7_320 bgb_7_352)) (concat (concat bgb_7_384 bgb_7_416) (concat bgb_7_448 bgb_7_480)))) (concat (concat (concat (concat bgb_7_512 bgb_7_544) (concat bgb_7_576 bgb_7_608)) (concat (concat bgb_7_640 bgb_7_672) (concat bgb_7_704 bgb_7_736))) (concat (concat (concat bgb_7_768 bgb_7_800) (concat bgb_7_832 bgb_7_864)) (concat (concat bgb_7_896 bgb_7_928) (concat bgb_7_960 bgb_7_992))))) (concat (concat (concat (concat (concat bgb_7_1024 bgb_7_1056) (concat bgb_7_1088 bgb_7_1120)) (concat (concat bgb_7_1152 bgb_7_1184) (concat bgb_7_1216 bgb_7_1248))) (concat (concat (concat bgb_7_1280 bgb_7_1312) (concat bgb_7_1344 bgb_7_1376)) (concat (concat bgb_7_1408 bgb_7_1440) (concat bgb_7_1472 bgb_7_1504)))) (concat (concat (concat (concat bgb_7_1536 bgb_7_1568) (concat bgb_7_1600 bgb_7_1632)) (concat (concat bgb_7_1664 bgb_7_1696) (concat bgb_7_1728 bgb_7_1760))) (concat (concat (concat bgb_7_1792 bgb_7_1824) (concat bgb_7_1856 bgb_7_1888)) (concat (concat bgb_7_1920 bgb_7_1952) (concat bgb_7_1984 (concat bgb_7_2016 bgb_7_2048)))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_0 : Interval gbAtlas 8 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_32 : Interval gbAtlas 8 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_8_64 : Interval gbAtlas 8 64 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_8 : Interval gbAtlas 8 0 68 := (concat bgb_8_0 (concat bgb_8_32 bgb_8_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_9_0 : Interval gbAtlas 9 0 1 := block_range (n:=1) (by decide +kernel)
theorem allgb_9 : Interval gbAtlas 9 0 1 := bgb_9_0
theorem allgb : ∀ k ≤ 9, ∀ i < count gbAtlas k, checkRow gbAtlas k i = true := by
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 8 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 10, 42)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 5 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 6 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 1 zero, 24, 26),(inputs.getD 3 zero, 18, 26),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 4, 12),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 1, 33)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefeeafeeaf0e0feeefeeafeeaf0e0feeefeeafeeaf0e0feeefeeafeeaf0e0feeefeeafeeaf0e0feeefeeafeeaf0e0feeefeeafeeaf0e0feeefeeafeeaf0e0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277075690 * 2 ^ 32 + 4276809952) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_17005.Model.Repr at out
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

def mono : List Gate := [⟨.or,[2,4]⟩,⟨.and,[4,5]⟩,⟨.and,[2,3]⟩,⟨.or,[2,3]⟩,⟨.and,[1,9]⟩,⟨.or,[5,6]⟩,⟨.and,[1,7]⟩,⟨.or,[0,12]⟩,⟨.or,[10,13]⟩,⟨.and,[11,14]⟩,⟨.or,[8,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4276809952) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4276809952) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_17005

open PEqualNP.Outside.L_meta_17005 in
theorem PEqualNP.Outside.L_meta_17005 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4276809952) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4276809952) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
