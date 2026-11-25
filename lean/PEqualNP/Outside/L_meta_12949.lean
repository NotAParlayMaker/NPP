import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_12949.Model
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


end PEqualNP.Outside.L_meta_12949.Model

namespace PEqualNP.Outside.L_meta_12949
open PEqualNP.Outside.L_meta_12949.Model
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

end PEqualNP.Outside.L_meta_12949

namespace PEqualNP.Outside.L_meta_12949
open PEqualNP.Outside.L_meta_12949.Model
def gbK8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x300003920a5d0000000e960078c95009899a3800602429008a1a88fa7009459b082440e308c811281878800e080041040210223ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x8417d51083f8a2107fd0420ff20841fd41083f882107fcc420ff18841fd31083f862107fc8420ff10841ee21083fa42107f08420f6108417e50083fe80107f90020fea0041fc40083fe60107f8c020fe98041fc30083fe40107bc8020ff10041fa20083fa40107b48020fc90041ff54c42fea9887f95310bf2a621fd54c42faa9887f15310be2a621ff53c42fea7887f94f10bf29e21fd53c42faa7887f14f10be29e21ff43c43fc87887f50f10fe21e21ff52c42fea5887f94b10bf29621fd52c42faa5887f14b10be29621ff42c43fc85887f50b10fe21621ff32c43fc65887f4cb10fe19621ff41c43fc83887f50710fe20e21ff31c43fc63887f4c710fe18e21ff21c43fc43887f48710fe10e21ff40c43fc81887f50310fe20621ff30c43fc61887f4c310fe18621ff20c43fc41887f48310fe10621ff54842fea9087f95210bf2a421fd54842faa9087f15210be2a421ff53842fea7087f94e10bf29c21fd53842faa7087f14e10be29c21ff43843fc87087f50e10fe21c21ff52842fea5087f94a10bf29421fd52842faa5087f14a10be29421ff42843fc85087f50a10fe21421ff32843fc65087f4ca10fe194217d51843fe83087f90610fea0c21fc41843fe63087f8c610fe98c21fc31843fe43087f88610fe90c21fc21842fca1087fd0210ff20421fd40843f881087fcc210ff18421fd30843f861087fc8210ff10421fd20843f841087fc4210fb88421fb10843fea8885fd5110dfaa2213f54443fca8885f95110feaa2217d54443f8a8885f15110de2a2213c54443fea6885fd4d10efa9a215f53443fca6885f94d10fea9a217d53443f8a6885f14d10ee29a215c53443fe86887f90d10fea1a21fc43443fea4885fd4910f7a92216f52443fca4885f94910fea92217d52443f8a4885f14910f6292216c52443fe84887f90910fea1221fc42443fe64887f8c910fe99221fc32443fe82887f90510fea0a21fc41443fe62887f8c510fe98a21fc31443fe42887f88510fe90a21fc21443fe80887f90110fea0221fc40443fe60887f8c110fe98221fc30443fe40887f88110fe90221fc20443fe20887ec4110ff08221f610443fea8085fd5010ff2a0217e54043faa8085f55010fe2a0217c54043fea6085fd4c10ff298217e53043faa6085f54c10fe298217c53043fe86087f90c10fea1821fc43043fea4085fd4810ff290217e52043faa4085f54810fe290217c52043fe84087f90810fea1021fc42043fe64087f8c810fe99021fc32042fca2087fd0410ff20821fd41043f882087fcc410ff18821fd31043f862087fc8410ff10821fd21043f842085f94010ffa0021fe40043fa80087f10010ff98021fe30043fa60087f0c010ff90021fe20043fa40087f08010ff88021f710043fc20087e84010fe88021f510043f220087c44010
  | 1 => 0xf524c3fca4987f54930fe292617c524c3fe84987f90930fea1261fc424c3fe64987f8c930fe99261fc324c3fea2985fd4530ff28a61fd514c3f8a2985f14530ffa0a61fe414c3fa82987f10530ff98a61fe314c3fa62987f0c530ff90a61fe214c3fa42987f08530ffa0261fe404c3fa80987f10130ff98261fb304c3fc6098778c130ffaa0617f540c3fca8185f95030feaa0617d540c3f8a8185f15030bf29861ff430c3fc86187f50c30fe21861ff520c3fca4185f94830fea90617d520c3f8a4187fd0830ff21061fd420c3f884187fcc830ff19061fd320c3f864187fd4430ff288617e510c3faa2185f54430fe28861ff410c3fc82187f50430fe20861ff310c3fc6218778c430fe98861fc310c3b862187fc8430ff10861fd210c3f842185f94030ffa0061fe400c3fa80187f10030ff98061df300c3fc60187e8c030fe98061dd300c3f260187fd5320bfaa641fe54c82fca9907f55320beaa641fc54c82f8a9907fd4f20bfa9e41fe53c82fca7907f54f20bea9e41fc53c82f8a7907fd0f20ff21e41fd43c83f887907fd0b20ff21641fd42c83f885907fccb20ff19641fd32c83f865907fd4720ff28e417e51c83faa3905f54720fe28e41ff41c83fc83907f50720fe20e41ff31c83fc63907f4c720fe18e41ff21c83fc43907f48720fe10e41ff40c83fc81907f50320fe20641ff30c83fc61907f4c320fe18641ff54882fea9107f95220bf2a441fd54882faa9107f15220be2a441ff53882fea7107f94e20bf29c41fd53882faa7107f14e20be29c41ff43883fc87107f50e20fe21c417d52883fe85107f90a20fea1441fc42883fe65107f8ca20fe99441fc32883fea3107f94620bf28c41fd51882faa3107f14620ffa0c41fe41883fa83107f10620ff98c41fe31883fa63107f0c620ff90c41fe21883dc43107f48620fe10c41ec21882fca1107fd0220ff20441fd40883f881107fcc220ff18441fd30883f861107fc8220f790441fb20883fea8905fd5120ff2a2417e54483faa8905f55120fe2a2417c54483fea6905fd4d20ff29a417e53483faa6905f54d20fe29a417c53483fe86907f90d20fea1a41fc43483fe84907f90920fea1241fc42483fe64907f8c920fe99241fc32483fea2905fd4520ff28a41fd51483f8a2905f14520ffa0a41fe41483fa82907f10520ff98a41fe31483fa62907f0c520ff90a41fe21483fa42907f08520ffa0241fe40483fa80907f10120ff98241fe30483fa60907f0c120ff90241fb20483fc40907b88120ffaa0417f54083fca8105f95020feaa0417d54083f8a8105f15020ffa98417f53083fca6105f94c20fea98417d53083f8a6105f14c20ffa1841fe43083fa86107f10c20bf29041ff42083fc84107f50820fe21041ff32083fc64107f4c820fe19041ff51083fca2105f94420fea8
  | 2 => 0x3faa7a05f54f40fe29e81ff43d03fc87a07f50f40fe21e81ff52d03fca5a05f94b40fea96817d52d03f8a5a07fd0b40ff21681fd42d03f885a07fccb40ff19681fd32d03f865a07fd4740ff28e817e51d03faa3a05f54740fe28e81ff41d03fc83a07f50740fe20e81ff31d03fc63a07f4c740fe18e81ff21d03fc43a07f48740fe10e817d54903fea7207f94e40bf29c81fd53902faa7207f14e40ffa1c81fe43903fa87207f10e40ffa9481fe52902fca5207f54a40bea9481fc52903fe85207f90a40fea1481fc42903fe65207f8ca40fe99481fc32903fea3207f94640bf28c81fd51902faa3207f14640ffa0c81fe419037c83207f50640fe20c81bc41903fe63207f8c640fe98c81fc31903fe43207f88640fe90c81fc21902fca1207fd0240dfa0481fb40903fea6a05fd4d40ff29a81fd53503f8a6a05f14d40ffa1a81fe43503fa86a07f10d40ffa92817f52503fca4a07f54940fe292817c52503fe84a07f90940fea1281fc42503fe64a07f8c940fe99281fc32503fea2a05fd4540ff28a81fd51503f8a2a05f14540ffa0a81fe41503fa82a07f10540ff98a81fe31503fa62a07f0c540ff90a81fe21503fa42a07f08540ffa0281fb40503fc80a06f90140bf2a081ff53103fca6205f94c40fea98817d53103f8a6207fd0c40ff21881fd43103f886207fd4840ff290817e52103faa4205f54840fe29081ff42103fc84207f50840fe21081ff32103fc64207f4c840fe19081ff51103fca2205f94440fea88817d51103f8a2207fd0440ff20881be41103fa82207f10440de20881ff31103fc62207f4c440fe18881ff21103fc42207f48440fe108817e50103fe80206fd0040ff20081fa40103fa80206f50040fca0081ff54cc2fea9987f95330bf2a661fd54cc2faa9987f15330be2a661ff43cc3fc87987f50f30fe21e61ff52cc3fca5985f94b30fea96617d52cc3f8a5987fd0b30ff21661fd42cc3f885987fccb30ff19661fd32cc3f865987fd4730ff28e617e51cc3faa3985f54730fe28e61ff41cc3fc83987f50730fe20e61ff31cc3fc63987f4c730fe18e61ff21cc3fc43987f48730fe10e61ff40cc3fc81987f50330fe20661ff548c2fea9187f95230bf2a461fd548c2faa9187f15230be2a4617d538c3fe87187f90e30fea1c61fc438c3fea5187f94a30bf29461fd528c2faa5187f14a30ffa1461fe428c3fa85187f10a30ff99461fe328c3fa65187f0ca30ffa8c61fe518c2fca3187f54630bea8c61fc518c3fe83187f90630fea0c61fc418c3fe63187f8c630ef18c61fd318c3f86318770c630ff90c61fe218c3fa43187f08630bf28461ff408c3fc81187f50230fe20461ff308c3be61187ecc230ffaa2617f544c3fca8985f95130feaa2617d544c3f8a8985f15130ffa1a61fe434c3fa86987f10d30ffa92617
  | 3 => 0x8718ff10e31ffa9463fe528c6fca518ff54a31bea9463fc528c7fe8518ff90a31fea1463fc428c7fe6518ff8ca31fe99463fc328c6fca318ffd0631ff20c63fd418c7f88318ffcc631ef98c63f7318c7fea118ff94231bf28463fd508c6faa118ff14231ffaa2637f544c7fca898df95131feaa2637d544c7f8a898df15131ffa1a63fe434c7fa8698ff10d31ffa92637f524c7fca498ff54931fe292637c524c7fe8498ff90931fea1263fc424c7fe6498ff8c931fe99263fc324c7fe8298ff90531fea0a63fc414c7fe6298fdcc531ff18a63de314c7fea098dfd4131ff28263fd504c7f8a098df14131ffaa0637f540c7fca818df95031feaa0637d540c7f8a818df15031bf29863ff430c7fc8618ff50c31fe21863ff520c7fca418df94831fea90637d520c7f8a418ffd0831ff21063fd420c7f88418ffcc831ff19063fd320c7f86418df94431ffa0863fe410c7fa8218ff10431ff98863df310c7fc6218fd8c431fe98863dd310c7ea6218ffd4031ff280637e500c7faa018df54031fe28063ff54c86fea990ff95321bf2a643fd54c86faa990ff15321be2a643ff53c86fea790ff94f21bf29e43fd53c86faa790ff14f21be29e43ff43c87fc8790ff50f21fe21e43ff42c87fc8590ff50b21fe21643ff32c87fc6590ff4cb21fe19643ff41c87fc8390ff50721fe20e43ff31c87fc6390ff4c721fe18e43ff50c87fca190df94321fea86437d50c87f8a190ffd5221bfaa443fe54886fca910ff55221beaa443fc54886f8a910ffd4e21bfa9c43fe53886fca710ff54e21bea9c43fc53886f8a710ffd0e21ff21c43fd43887f88710df54a21ffa1443fe42887fa8510ff10a21ff99443fe32887fa6510ff0ca21bf28c43ff41887fc8310ff50621fe20c43ff31887fc6310ff4c621fe18c43ff21887de4310fdc8621ffa8443fe50886fca110ff54221bea8443fc50887fea890dfd5121ff2a2437e54487faa890df55121fe2a2437c54487fea690dfd4d21ff29a437e53487faa690df54d21fe29a437c53487fe8690ff90d21fea1a43fc43487fe8490ff90921fea1243fc42487fe6490ff8c921fe99243fc32487fe8290ff90521fea0a43fc41487fe6290ff8c521fe98a43fc31487fe4290fdc8521ff10a43ee21487fea090dfd4121ff28243fd50487f8a090df14121ffaa0437f54087fca810df95021feaa0437d54087f8a810df15021ffa98437f53087fca610df94c21fea98437d53087f8a610df14c21ffa1843fe43087fa8610ff10c21bf29043ff42087fc8410ff50821fe21043ff32087fc6410ff4c821fe190437e51087fe8210ff90421fea0843fc41087fe6210ff8c421fe98843fc31087fe4210fbc8421ff10843f621087fa4210fb48421fa90843ff50087fca010df94021fea80437d50087f8a010ffd4f40ff29e817e53d
  | 4 => 0x7f94332bf28665fd50ccafaa1997f14332ffaa4657f548cbfca9195f95232feaa4657d548cbf8a9195f15232bea9c65ff438cbfc87197f50e32fe21c657e528cbfe85197f90a32f721465fd428cbda85197f10a32ff99465df328cbde65197fd4632ff28c657e518cbfaa3195f54632fe28c65ff508cbfca1195f94232fea84657d508cbf8a1197fd5132bfaa265fe544cafca8997f55132beaa265fc544caf8a8997fd0d32ff21a65de434cbfa86997750d32fe21a65ff424cbfc84997b90932fea1265ed424cbf884997fcc932f799265fe324cbbc64997fd4532bfa8a65fe514cbfaa2997f14532be28a65ff504cafea0997f94132fea8265fc504caf8a0997fd5032bfaa065fe540cafca8196f950329f2a065fd540cafaa8196f550329eaa065fc540caf8a8195f94c32ffa1865fe430cbfa86197f10c32bf29065ff420cbfc84197f50832fe21065ff320cbbe64197f8c832f719065fd320cbba64197b4c832e699065ff510cbfca2195f94432fea88657d510cbf8a2197fd4032ff280657e500cbfaa0195f54032fe28065ff53d07fca7a0df94f41fea9e837d53d07f8a7a0ffd0f41ff21e83fd43d07f887a0ffd4b41ff296837e52d07faa5a0df54b41fe29683ff42d07fc85a0ff50b41fe21683ff32d07fc65a0ff4cb41fe19683ff50d07fca1a0df94341fea86837d50d07f8a1a0df55241ffa9c83fe53906fca720ff54e41bea9c83fc53907fe8720ff90e41fea1c83fc43907fea520ff94a41bf29483fd52906faa520ff14a41ffa1483fe42907fa8520ff10a41ff99483fe32907fa6520ff0ca41bf28c83ff419077e8320fdd0641ffa8483fe50906fca120ff54241bea8483fc50907fea6a0dfd4d41ff29a83fd53507f8a6a0df14d41ffa1a83fe43507fa86a0ff10d41ffa92837f52507fca4a0ff54941fe292837c52507fe84a0ff90941fea1283fc42507fe64a0ff8c941fe99283fc32507fe82a0fdd0541ff20a83be41507fea0a0dfd4141ff28283fd50507f8a0a0df14141bf2a083ff53107fca620df94c41fea98837d53107f8a620ffd0c41ff21883fd43107f88620ffd4841ff290837e52107faa420df54841fe29083ff42107fc8420ff50841fe21083ff32107fc6420ff4c841fe190837e51107fe8220efd0441ff20883f641107fa8220ef50441faa0883ff50107fca020df94041fea80837d50107f8a020ffd5331bfaa663fe54cc6fca998ff55331beaa663fc54cc6f8a998ffd0f31ff21e63fd43cc7f88798ffd4b31ff296637e52cc7faa598df54b31fe29663ff42cc7fc8598ff50b31fe21663ff32cc7fc6598ff4cb31fe19663ff41cc7fc8398ff50731fe20e63ff50cc7fca198df94331fea86637d50cc7f8a198ffd5231bfaa463fe548c6fca918ff55231beaa463fc548c6f8a918df54e31ffa1c63fe438c7fa
  | 5 => 0x300000200000700100000200800100400000a00100a00100b00000300200a00000200400000000b00100400100000000600100100700500700100a00000400000000100100301000200c01000100600200d00000200400200700000b00200000602502100000200000700300100d00001500002800a00300400300100101901000d00000000000600100100000800100000000100000300500700101000100300400a00800000100000100200900000100000c00200300000000000700d00600100000000200100b000001000007001001000003017004000003005020006008000003006ffa9687fe52d0efca5a1ff54b43bea9687fc52d0ffea3a1ff94743bf28e87fd51d0efaa3a1ff14743ffa8687fe50d0efca1a1ff54343bea8687fc50d0efaa921df94e43ffa1c87bf4390fbe8721ffd4a43ff294877e5290ffaa521df54a43fe29487ff5190ffca321df94643fea8c877d5190ff8a321ffd4243ff284877e5090ffaa121df54243fe28487ff4350fbe86a1ff90d43df21a87ff5250efea4a1ff94943fea9287fc5250ef8a4a1ffd4543bfa8a87fe5150ffaa2a1ff14543be28a87ff5050efea0a1ff94143fea8287fc5050ef8a0a1df95043bf29887ff4310f7e8621ff90c43ef21887fd4310f7a8621f750c43cea1887ff5210ffca421df94843f7290876e5210ffaa421df54843f6a90876d5210ff8a421ffd4443ff288877e5110ffaa221df54443fe28887ff5010ffca021df94043fea80877d5010ff8a021ffd4f42ff29e857e53d0bfaa7a15f54f42fe29e85ff43d0b7e87a17f90f42fea1e85bd43d0bf887a17fd4742ff28e857e51d0bfaa3a15f54742fe28e85ff50d0bfca1a15f94342fea86857d50d0bf8a1a15f55242ffa9c85fe5390afca7217f54e42bea9c85fc5390bfe87217f90e42fea1c85fc4390afca5217fd0a42dfa1485ef4290bfea3217f94642bf28c85fd5190afaa3217f14642ffa8485fe5090afca1217f54242bea8485fc5090bfea6a15fd4d42ff29a85fd5350bf8a6a15f14d42ffa1a85bf4350bfc86a17f50d42dea1a85fc4350bfe84a17bd0942ff21285be4250bfea2a15fd4542ff28a85fd5150bf8a2a15f14542ffa82857f5050bfca0a17f54142fe282857c5050afca8217fd4c42ff298857e5310bbca6215794c42fea98857d5310bbaa6215754c42fe29885ff4310bfc86217f50c42fe218857e5210bfe84216fd0842ff21085ee4210bfa84216f50842f6a1085ad4210bfea2217f94442bf28885fd5110afaa2217f14442ffa8085fe5010afca0217f54042bea8085fc5010bfea9995fd5332ff2a6657e54ccbfaa9995f55332fe2a6657c54ccbfe87997f90f32ef21e65fd43ccbba87997f10f32ffa1665fe42ccbfa85997f10b32ffa8e65fe51ccafca3997f54732bea8e65fc51ccbfea199
  | 6 => 0x102de89c886d060008b078a5766e079c908000000014bb22f4304d3800000000025409e000000878c7e000ad4da6000000000af0ac8000000000000000d42000668bfed1c0001e89760000000000000005a208659a00039e0000002e65ae5fac28ccc4a011239878400085c000d2a000adc3c24125e4000000ce8000000a64d5c50043a39ccd200000088eb303e840a0008247f200028e968bf222ac88d20874000a5e40ec4ec6aa3a89800000013816c2ee21a0004d41426e60e422c0000008ae1f6c12d7a1ba2bebb000096000002c81e0006b003a1dc9880000080002d0000000a880008f60000000003664840003268ca2caa98000000000d5475c8bc35a3de9320b054e000000000000bd8000000000aea1e625c00010264a92c11e29ec82b4a634572548b1c0000000000000007000000003b400000054cc0a000b2c0003d8000c0cd6e7048c4cd62740002fc00048a2328d200042c8ee46a77415045cc0656c000d8c00050e2a68a00b60008ce5ce4b6000c2616a79093e00b00200700200d00000000800000000100000400100000300000900000100a00000300200600300100000200100300a00c00500101b00000500200100101100000600400600300400800a00000000100400200500200500501400700500c00200100201100200700900600100101000500900101000300701300700201600200400a00000100900400000200000400000900000400200000000700100000200200000400000100500000000500000200100000900001100100e00000000400302300a00e00000100100300100400000100100300200800000100000800100001f00000000000000100800900100600000100000000000400701400300100000200000000000600000b00000000f00000800201000000c00200300000300100000001b00000500901700401000200100700000000100100300100300001300000200600100300600000300100800c00000900000000000f00000000000200300100100401300000000a00100400000200a00900100300000200000300000000300200000200200200600c00100100700200000100301e00000100000a02300300400501000300000600000000400001f00001200000200000300300f01000800a00200600200100f01f00000100000000300000700000100000300c00000100001900100100500100000e00000300000000300201500100300101300000b00000000a00000000200000900000000600700701400200200700000100300100100000100000100200800100600200000100500a00001500000a00200d00000300001900300000f00600200000000000700000200000e00401000000700000000100100a00000000000200c00200100600000900200100b000003008015005003005001000000
  | 7 => 0xe56893651017055053a33c2bcc504e0b2a3ac0004883601047ea0f8a467bad3c0000004e4000d224240b4000b0ebe00007022301daad043c896bce00092e000000000000870756000644a2ad686569943c48a2a5a3887d400035890a000b16000a9c00068caaa00013a84800094c5446fa000080b7ea8637682e7d6498206aee00000026e4a22c2858b0a83ed9e0000000003480000003e20003cc000000664000000000ae24207183f837a2645b62622827784440008b8a06068b5e4d6000abac3455ccfab3a9b4a02128cfc44e07abd02a401a5aa95276e30a8340005025327a05de7b86c808a0e63d45b2000006c5a3a47f6be6d4a38600012e06e000b1e45872e986574836b6c2ac000aa82340000001200008e20000009fa00099641810c7d83b0178000afe7b0ac6c3c1be0000000000000600000000000000700004280006c00007da1b81d600000057cc720000002e400000032e1981bc23e000000000324bdc30c0009e0000a348a61a6cd03545660000000000006bc000cc2c1eb800003289e2b54950cde0000000009b2000d2800000018e0000005d0028226bf8590000d72000000000cf40004c047c55460086cc8402eb48154bd495e38e1466904aa9aa0ecbc00a8af8a2cb6a0000009720000000002b00ca000000a4aa60560c66000000cb80000fc000ab6d4e0004f282a000000d5a2fa806000000000000214000602436b5c1fcb9c0d61d46cc966bb4b56c6ec4a7440000000000007327acd9c84ac9636c60e0009f60346288ac3e6000cd434633261a32a71e8c21a43f01a80000006de0000000000006d0000bac0000002520003943d0000c64c2240697a000cae242152000876d562a200085222000044854200000081a00000086a00000000020c000000000000000000678000000000160218934000a48d4c80e954aa0ab2108000090bb8cb4c54cfe000000a6c01c00000000005c0006140008624947425be00069800000000000000000c7720004682122040c0d306dc9706269a6a26780d60a1cc14054a400007aa1684d0794a503e47c2928a1876a9f258036404c28a75067ea1e6ee2502d656a3aa00092663eafabc4000a70000000912b0c3ceb580000002c81c646000019adaa2ba6c40006f40004220009b6446000294000180338758d08000000d12268118d52c6814a00000047020ac9e3c6000000662000000b8a652646b180007c40000000006b22162d40000000006fc0008e643e15652c000000d5e0200000004e27c6000000000270802000d0c5c6c8cd1a5167622c6828000c809c8a386103029a4630000a6273a284c4865ab22c36a7417cd7e66e96ac000e061eaae710ba285e55a21cca857e41a21e6a4746202c9a832a3c6d44c427abe8b8e78800eac0d14000b7813200095a24862ab401300f007ec56a
  | 8 => 0x92a2380000002d21f44b2522000c581ec51ab5226c000000850476042bcc6ae0000d21164f6c6089e384730124d9a5840a21c007c6ca1ce880000b6200023c0009060003a2000000000106000d82bd60000fa5a6000baa0029da00052672a41600034000063a000c447d03301580000000001760008e42a0000000000d40c080840002fe5c4c2a52eb500000000007d20004eeada6be49ad2cc04a783dac0e1a0ae600068e000000196000000000d32b3487a884ac48f208cbfa94097ccb03a8000c3889a5e0382ca64fe58a2ec7482b4032b4648c0003f2d982e241e1ea0d80004b01f262ca801cc0000008662565528160b80d06e2b700005d471c000a66cf2bba000a7ed905e881857022400084200033e000a4400018cd360000000006060000004a87a40001d8c7cb0891c1940000000000000003920000c80005f80006b40005200000007ec12200000000000000035600010e0000dc0007164025fc0005bcd0e3ec5380000005582920001e0000af691a830000c02000000c1cc6284078c0003000001a20f40002000003ca000798000000d1e00000035e0001825ca288000000cc688aa7cd168d6aa24420005087fa8de77067c7388c0134daecbc8141f89e6d50c861c4a926ec38008e44a00099e0007a20000000000002cc734990ca4ad8c5c7683680006ea50c0000007644dc000bbe51ea54000cca33600035080c1d000000083849c0002da00064e0009f87ae65c396b244807123420000000fe53c0ac0000004084a418847a57a47e66083a7e48fecb600091860ccc000037400027cc320c40004ba0a63f61740aa60444c8d00000007b6c3ea00c240001fe22ed345cc000a280008ec87c8cc37e1ac000000064910094352024d3a00000000034c000000000000000b0204ad8a0000001ae00014800034e00000000052a75e31868400077e000228a14000000ce62107be0000000004f879a00005851c8569a831ad940008b4546000ab05ec000000b3e00010a0000000000003728a4d2629a9eaaded86000ce2baed627a60000003dc96482c00094e7362f0bf6b3838c514c184964c69b000096e61c948c2e4d214e0008080000c234a17a0f23f4ae83120001b4000bda6d2c1a0001e42aa8f4aec00000024678ec5eda29ceb66a906a28f0096ba058627628c3ae0009c4ba86b870a4f0a088eaa20362320a0a692bf04e688cb2e0000005360003a0000854000a2e73e49e000000426000000b5a5c2a2211aa76000d0041403e20e90c6220000000005ea136b729a0000076000b9200038a6d87269e400000058200000043486024c2080001268d40000000000000000000000000005ac506b8c820a3e40437829cc205e2004000804000000000a56c780000001141660006503eea0450abe21ca1e2c528da4e8868cbe45e9d00e237c55
  | 9 => 0x407e80eac8eccebea12a0000000000001fa7de000290ac200036e8c8556cf8596000c420000000000000000000160008100000006c6618b8674e1b08e894a6ba2e0ba4000af4000ca036a018d240000920006ce00000063c0004f4bc686e8467ccbf418a67a31c2403b66166f20008640000000003e00002365a49a2098920000266d80000192000a9459c894a587ce68800023a000000a4292246c6e8000000cea00082230e000000914b0415a3161845ba000000930000a52000000000000000000d92a82000000000000b8400040012cc76000d7cc9c05264c8aada400000000001e0008c6000000d2e0003be3fcb26d46b7c49093c15c51874a5343d269407819ca8aa16bd239a3100da7660007c07827221c2c2c0885f63c840cabe00006c45662e0008be65e4820009384409d25c03346e49c00bcaa42b8714432000110c160aed022dc24427eb12c98b882b2720b642588f868a25a000000a9e000b006b60820004d82b600022200000000000000000085aa6e00000000058ca3056e0001869c60000de9dc00000000000077c6ac2960001c8000172a360005f20002985da0360006f09de0500004de000cda58e00000014c0f6bee58854ac406aa33a000d0abe4a4e1f0578000000cee000b3600048e5a80007eed780005b06320000000000009bc74c0000ba000048100000466ae07e0a68000b76000cba6965e60007fe8e011ca724a6000796d9653e98e9005242ce3141b23b27080627e2000a1a73c2f20729d42860000c600000000000042a6203ba0008ba000000000dac000c7a31e96c0009925f40000006d60000000000000000000009784aeabc452d6c1de98000024a00079e000cac000d6a4b40ce000000528af235c87e00a680cdc90496266a7f06a86c2000666000724d58b9660a1eecc4786bec454b069980009ca0009be8727fcbca5a0ca29844c2d4891ed10308c46000a0c4860005f00000eeab899cbb65626a0cc8d64a8ed76a5c5d8000d3ecf0a0e0b2000ba600041000000000002ac94000c10b427e60001b649294463680a4fcd1800098c0220448dc000cd80bec6c8b64ea7c83ea0000265d200000032246e0009d60000002c000000000065490283c4bc8820100007ca000ace000caa598000946000a968125dc72cad6aacda89fe0000003d613e32cb9ac7016e3062600007b417e2802f6d04a9a00039045aa324da00000016400090e1aacf64cc00099ab909cc00009a0000000003fe00025e776000b4e00081c000956000000000000000a8c09cbfc0000007f44fa7068fc05e4c842e000000000672000658000916d44000000000760b14674a8460876ca6a5d675404069c06a800056b202f80e8612b685c864200070e5b8000c900009d8000670ce0ab45920000005120009f0012b44000000afc4386f89ae278
  | 10 => 0x5b40003bc03884c0002a8cecbc8000a7aae4000d8800098293a0008d80009249ec000792000000b28844d70974a1267684e8fa6860007bc77a5ee0001629b88924629fc430000d660460007400007b2000530624b1a00075a1d28b28880d40003fa00071aacca24504bc2c8a95cd8e472000942648c92564594ce40000000006da0006fe3440a0d7400004e00024eb3c00063827298a000000000752b98c30c3a0002eab9e2ae0006403c00007280004beb10ad2aa6000b4c69a0000004ac00000000066c000b746f67f8890000b941900000cc0003a69c268200000026a066c4cbde46400000000037000000000047400041c9acb320300000000000000004ce00000059e000da000000000000000005a00000000000000000069eb6e00003c0000009f41445fe82600000070cacab828a84ca074b609ba95813c4ec97e0009ee3b8478cb27a8d844509e815ea4cb7a0002d80000007dc19e0a40000004b80001400002c4bbcc742e80006a65
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x32042bd640c810f34c8320427e64944109f592510427e63944109f58e510427e62944109f58a510427d65d04109fd96410427d6590410cf952410433d5490410be98241042f960904109fd95410427f65104109f594410433e5410410cf55041042fa6010410be580410427d65cc4109fd96310427d658c410d794e310435d538c410be98231042f9608c4109fd95310427f650c4109f594310435e530c410d754c31042fa600c410be580310427d65c84109fd96210427d6588410db94a210436d5288410be98221042f960884109fd95210427f65084109f594210436e5208410db54821042fa6008410be580210427e64940109f592500427e63940109f58e500427e62940109f58a500427d61940109f597400427f65900109f596400433e5490010cf55240042f66190010bd586400427f65500109fd94400427e65100109f594400427c6510010cf950400433d5410010bd98440042f561100109f597300427f658c0109f596300435e538c010d754e30042f6618c010bd586300427f654c0109fd94300427e650c0109f594300427c650c010d794c300435d530c010bd98430042f5610c0109f597200427f65880109f596200436e5288010db54a20042f66188010bd586200427f65480109fd94200427e65080109f594200427c6508010db948200436d5208010bd98420042f56108010dd59710042f56184010dd94610042f96584010de59610042796584010be58610042f16184010de94610043f251840109fd9510042bf6444010af19110042df6344010b718d10042ef6244010bb18910042f76544010ddd9510042776544010edd9110043b46444010f5d8d10043d46344010f9d8910043e46244010bdd8110043765044010fcd0110043f24044010fc50110043f04044010fccc110043f23044010fc4c110043f03044010fcc8110043f22044010fc48110043f02044010bed95100437b65440109ed9510043bb6444010ee19110043db6344010f618d10043eb6244010fa18910042fb6144010fcd85100437a5144010fc94510043f34144010fc90510043f14144010fc10510043f33144010fc8c510043f13144010fc0c510043f32144010fc88510043f12144010fc08510043f36544010bcd9510043736544010fcd9110043b36444010fc99110043f16444010fc19110043b06444010fcd5110043f25444010fc55110043f05444010fcd8d10043d36344010fc98d10043f16344010fc18d10043d06344010fcd4d10043f25344010fc54d10043f05344010fcd0d10043f24344010fc50d10043f04344010fcd8910043e36244010fc98910043f16244010fc18910043e06244010fcd4910043f25244010fc54910043f05244010fcd0910043f24244010fc50910043f04244010fccc910043f23244010fc4c910043f03244010
  | 1 => 0x427d6295010cfd91540427f63550109f18d540427f62550109f189540427f61550109f585540427f60550109f581540433d5415010b798c54042dd6315010bb98854042ed62150109f990540433e64150109f98c540435e63150109798c540427d6315010d758c540425d63150109f988540436e62150109b988540427d6215010db588540426d62150109f984540437661150109f980540437a60150109f993530427d64d4c109f98b530427d62d4c109f987530437661d4c109f983530437a60d4c109f596530435f5394c109f992530427d6494c109f98a530427d6294c109fd91530427c6454c10d7d8d530427f6254c109f189530427f6154c109f585530427f6054c109f58153042be6414c10af590530435d5314c10bb98853042ed6214c109f990530433e6414c108f990530427d6414c10cf590530423d6414c109f98c530435e6314c109f988530436e6214c109b988530427d6214c10db588530426d6214c109f98453043766114c109f980530437a6014c109fd97430427e65d0c109f597430427c65d0c10cf953430433d54d0c109fd96430427e6590c109f596430427c6590c10d794e430435d5390c109fd95430427e6550c109f595430427c6550c10cf951430433d5450c10d794d430435d5350c10bdd8543042f46150c10bed8143042f86050c109fd94430427e6510c109f594430427c6510c10e750c43042ee6210c10bb588430427e64d48109f593520427e63d48109f58f520427e61d4810dd987520427e60d4810de983520427d6594810dbd4a520427e64948109f592520427e63948109f58e520427f64548109f191520427f63548109f18d520436f62548109fd85520427d61548109fd81520427d6054810af99052042bd6414810b798c52042dd6314810db548520427e6414810cf990520423e64148109f590520433d64148108f590520427e6314810d798c520425e63148109f58c520435d63148109758c520427e6214810db988520427e6114810dd984520427e6014810de980520427f65d08109f997420427d65d08109f197420433e54d0810cf553420427f65908109f996420427d65908109f196420436e5290810db54a420427f65508109f995420427d65508109f195420433e5450810cf551420436e5250810db54942042f76150810bd18542042fb6050810be181420427f65108109f994420427d65108109f19442042de6310810b758c42043ad42108109fd97320427e65cc8109f597320427c65cc810d794f320435d53cc8109fd96320427e658c8109f596320427c658c810db94a320436d528c8109fd95320427e654c8109f595320427c654c810d794d320435d534c810db949320436d524c810bdd8532042f4614c810bed8132042f8604c8109fd94320427e650c8109f594320427c650c810af99
  | 2 => 0x5410510cf150414435f5310510d714c414436f5210510db14841443b541105109f997314433f54cc510cf153314435f53cc510d714f314436f52cc510db14b31442fa60cc510be583314427e658c510cfd52314433c548c510d7d4e314435c538c510dbd4a314436c528c5109f195314433f544c510cf151314435f534c510d714d314436f524c510db14931442fb604c510be181314427e650c510cfd50314433c540c510d7d4c314435c530c510dbd48314436c520c510f54c4314427e65c8510cfd53214433c54c8510d7d4f214435c53c8510dbd4b214436c52c8510be98321442f960c85109f996214433f5488510cf152214435f5388510d714e214436f5288510db14a214427c6548510cfd51214433c5448510d7d4d214435c5348510dbd49214436c5248510bed8121442f860485109f994214433f5408510cf150214435f5308510d714c214436f5208510db14821443e521085109f997404433f54d0110cf153404435f53d0110d714f404436f52d0110db14b40442f661d0110bd587404427e6590110cfd52404433c5490110d7d4e404435c5390110dbd4a404436c52901109fd95404427d65501109f195404433f5450110cf151404435f5350110d714d404436f5250110db14940442f76150110bd185404427e6510110cfd50404433c5410110d7d4c404435c5310110dbd48404436c5210110ee500404427e65cc110cfd53304433c54cc110d7d4f304435c53cc110dbd4b304436c52cc110bd98730442f561cc1109f996304433f548c110cf152304435f538c110d714e304436f528c110db14a304427f654c1109f595304427c654c110cfd51304433c544c110d7d4d304435c534c110dbd49304436c524c110bdd8530442f4614c1109f994304433f540c110cf150304435f530c110d714c304436f520c110db14830443d9300c1109f997204433f54c8110cf153204435f53c8110d714f204436f52c8110db14b20442f661c8110bd587204427e6588110cfd52204433c5488110d7d4e204435c5388110dbd4a204436c52881109fd95204427d65481109f195204433f5448110cf151204435f5348110d714d204436f5248110db14920442f76148110bd185204427e6508110cfd50204433c5408110d7d4c204435c5308110dbd48204436c5208110fa480204433f54c4110cf153104435f53c4110d714f104436f52c4110db14b10443bb54c4110ee15310443db53c4110f614f10443eb52c4110fa14b104433f5484110cf152104435f5384110d714e104436f5284110db14a10443b75484110ed15210443d75384110f514e10443e75284110f914a10443f350841109f98f540427d63d50109f98b540427d62d50109f987540437661d50109f983540437a60d50109f596540433f54950109f98e540427d63950109f98a540
  | 3 => 0x910dbd4a524427e6494910cf992524423e64949109f592524433d64949108f592524427e6394910d798e524425e63949109f58e524435d63949109758e524427e62949109b98a524427d6194910dd586524427d6094910de58252442bf6454910af191524433f5454910cf15152442df6354910b718d524435f5354910d714d524427f6454910cfd91524423f64549109f191524433c64549108f191524427f6354910d7d8d524425f63549109f18d524435c63549109718d524436f62549109fd85524437761549109fd81524437b60549109f994524433f5414910cf150524435f5314910d714c524436d52149109f990524427d64149109f98c524427d6314910db988524427e61149109f184524427e60149109f18052442ee6514910db994524426e6514910dbd5052443af5414910cbd50524436e5414910db550524436c5414910eb150524432c5414910dbd4c52443cf5314910d3d4c524436e5314910db54c524436c5314910f314c524434c5314910dbd90524436e6414910db590524436c6414910dbd8c524436e6314910db58c524436c6314910dbd0c524436e4314910db50c524436c4314910dbd84524436d6114910dbd80524436d6014910db440524427f65d09109f997424427d65d09109f197424433f54d0910cf153424435f53d0910d714f424436f52d0910db14b424427f65909109f996424427d65909109f196424433f5490910cf152424435f5390910d714e424436f5290910db14a424427f65509109f995424427d65509109f195424433f5450910cf151424435f5350910d714d424436f5250910db149424427f65109109f994424427d65109109f194424433f5410910cf15042442de6310910b758c424435f5310910d714c424436f5210910db14842443ad4210910bd98442442f56110910be98042442f960109109fd97324427e65cc9109f597324427c65cc910cfd53324433c54cc910d7d4f324435c53cc910dbd4b324436c52cc9109fd96324427e658c9109f596324427c658c910cfd52324433c548c910d7d4e324435c538c910dbd4a324436c528c9109fd95324427e654c9109f595324427c654c910cfd51324433c544c910d7d4d324435c534c910dbd49324436c524c9109fd94324427e650c9109f594324427c650c910af99032442bd640c910cfd50324433c540c910d7d4c324435c530c910dbd48324436c520c910f34c832442f6610c910bd58432442fa600c910be580324427e65d0510cfd53414433c54d0510d7d4f414435c53d0510dbd4b414436c52d0510be98341442f960d05109f996414433f5490510cf152414435f5390510d714e414436f5290510db14a414427c6550510cfd51414433c5450510d7d4d414435c5350510dbd49414436c5250510bed8141442f860505109f994414433f
  | 4 => 0xf980544427c6015110af994544433e65151108f994544433f6315110cf98c544433d6315110cf18c544433f6215110cf988544433d6215110cf188544433f6115110cf584544433f6015110cf580544433d1015110cfd53534433c54d4d109f993534427d64d4d109f98b534427d62d4d10d7d53534439f54d4d10c7d53534435e54d4d10d7553534435c54d4d10e7153534431c54d4d10d7d93534435e64d4d10d7593534435c64d4d10d7d8b534435e62d4d10d758b534435c62d4d10d7d87534435d61d4d10d7d83534435d60d4d10af99253442bd6494d10cfd52534433c5494d10d7d4e53442ee6294d10bb58a534427e6494d10cf992534423e6494d109f592534433d6494d108f592534427e6394d109798e534427e6294d10db98a534426e6294d109f58a534436d6294d109b58a534427d6194d10dd586534427d6094d10de58253442bf6454d10af191534433f5454d10cf15153442ef6254d10bb189534427f6454d10cfd91534423f6454d109f191534433c6454d108f191534435f6354d109fd89534436f6254d109bd89534427c6254d10db189534426c6254d109fd8553443776154d109fd81534437b6054d109f994534433f5414d10cf150534435d5314d109f990534427d6414d10d798c534427e6214d109f588534427e6114d109f184534427e6014d109f18053442de6514d10d7994534425e6514d10d7d50534439f5414d10c7d50534435e5414d10d7550534435c5414d10e7150534431c5414d10d7d90534435e6414d10d7590534435c6414d10d7d88534435e6214d10d7588534435c6214d10d7d84534435d6114d10d7d80534435d6014d10d7440534427f65d0d109f997434427d65d0d109f197434433f54d0d10cf153434435f53d0d10d714f434427f6590d109f996434427d6590d109f196434433f5490d10cf152434435f5390d10d714e434427f6550d109f995434427d6550d109f195434433f5450d10cf151434435f5350d10d714d434427f6510d109f994434427d6510d109f194434433f5410d10cf150434435f5310d10d714c434439d4310d10bb98843442ed6210d10bd98443442f56110d10be98043442f96010d10cfd53524433c54d4910d7d4f524435c53d49109f993524427d64d49109f98f524427d63d4910dbd5352443af54d4910cbd53524436e54d4910db553524436c54d4910eb153524432c54d4910dbd4f52443cf53d4910d3d4f524436e53d4910db54f524436c53d4910f314f524434c53d4910dbd93524436e64d4910db593524436c64d4910dbd8f524436e63d4910db58f524436c63d4910dbd0f524436e43d4910db50f524436c43d4910dbd87524436d61d4910dbd83524436d60d4910af99252442bd6494910cfd52524433c5494910b798e52442dd6394910d7d4e524435c5394
  | 5 => 0x438427f6510e109f994438427d6510e109f194438439d4310e10bb98843842ed6210e10be98043842f96010e109f993528427d64d4a109f98f528427d63d4a10dd587528437a60d4a10dbd4a528427e6494a109f592528427e6394a109f58e528427f6454a109f191528427f6354a109f18d528436f6254a10db548528427e6414a109f590528427e6314a109f58c528436e6214a10dd584528437a6014a109fd97428427e65d0a109f597428427c65d0a109fd96428427e6590a109f596428427c6590a109fd95428427e6550a109f595428427c6550a10bdd8542842f46150a109fd94428427e6510a109f594428427c6510a10b798c42842dd6310a10eb50842842fa6010a10be580428427f65cca109f997328427d65cca109f197328427f658ca109f996328427d658ca109f196328427f654ca109f995328427d654ca109f19532842f7614ca10bd185328427f650ca109f994328427d650ca109f19432842be640ca10af59032843cd320ca10be98032842f9600ca10cf953418433d54d0610be98341842f960d0610cfd52418433c5490610cf951418433d5450610bed8141842f86050610cfd50418433c5410610d794f318435d53cc610be98331842f960cc610d7d4e318435c538c610d794d318435d534c610bed8131842f8604c610d7d4c318435c530c610db94b218436d52c8610be98321842f960c8610dbd4a218436c5288610db949218436d5248610bed8121842f86048610dbd48218436c5208610cf952408433d5490210bd98640842f56190210cf950408433d5410210bd98440842f56110210ee500408435e538c210d754e30842f6618c210bd586308435e530c210d754c30842f6610c210bd58430843d9300c210db94a208436d5288210bd98620842f56188210db948208436d5208210bd98420842f56108210fa48020842f565c4210dd59710842f965c4210de597108427e63d51109f58f544427e62d51109f58b544433f63d5110cf98f544433d63d5110cf18f544433f62d5110cf98b544433d62d5110cf18b544433f61d5110cf587544433f60d5110cf583544433f5495110b798e54442dd6395110bb98a54442ed62951109f992544423e64951109f98e544435e63951109798e544427d6395110d758e544425d63951109f98a544436e62951109b98a544427d6295110db58a544426d62951109f586544437561951109f58254443796095110b7d8d54442dc6355110bbd8954442ec6255110cfd91544427f6355110d7d8d544425f63551109f18d544435c63551109718d544427f6255110dbd89544426f62551109f189544436c62551109b189544427f6155110ddd85544427f6055110ded81544427e6515110cf550544433e64151109f98c544427d63151109f988544427d62151109f984544427c61151109
  | 6 => 0x27d65d0f109f19743c427f6590f109f99643c427d6590f109f19643c427f6550f109f99543c427d6550f109f19543c42fb6050f10be18143c427f6510f109f99443c427d6510f109f19443c439d4310f10bb98843c42ed6210f10bd98443c42f56110f109f99352c427d64d4b109f98f52c427d63d4b10dd98752c437960d4b10dbd4a52c427e6494b109f59252c427e6394b109f58e52c427f6454b109f19152c427f6354b109f18d52c436f6254b10db54852c427e6414b109f59052c427e6314b109f58c52c436e6214b10dd98452c43796014b109fd9742c427e65d0b109f59742c427c65d0b109fd9642c427e6590b109f59642c427c6590b109fd9542c427e6550b109f59542c427c6550b10bed8142c42f86050b109fd9442c427e6510b109f59442c427c6510b10b798c42c42dd6310b10eb50842c42f66110b10bd58442c427f65ccb109f99732c427d65ccb109f19732c427f658cb109f99632c427d658cb109f19632c427f654cb109f99532c427d654cb109f19532c42fb604cb10be18132c427f650cb109f99432c427d650cb109f19432c42be640cb10af59032c43cd320cb10bd98432c42f5610cb10cf95241c433d5490710be98241c42f96090710cf95041c433d5410710ed50441c42fa6010710be58041c435e538c710d754e31c42fa608c710be58231c435e530c710d754c31c43d5310c710be98031c42f9600c710db94a21c436d5288710be98221c42f96088710db94821c436d5208710f948421c42fa6008710be58021c433e54d0310cf55340c42f661d0310bd58740c433f5490310cf15240c433e5450310cf55140c42f76150310bd18540c433f5410310cf15040c435e53cc310d754f30c42f661cc310bd58730c435f538c310d714e30c435e534c310d754d30c42f7614c310bd18530c435f530c310d714c30c436e52c8310db54b20c42f661c8310bd58720c436f5288310db14a20c436e5248310db54920c42f76148310bd18520c436f5208310db14820c427e63d52109f58f548427e62d52109f58b548437561d5210de983548433f54952109f98e548427d63952109f98a548427d6295210cfd91548427f63552109f18d548427f62552109f189548433d5415210cf990548427e63152109f58c548427e62152109f58854843756115210de980548427e64d4e109f593538427e62d4e109f58b538437561d4e10de983538435f5394e109f992538427d6494e109f98a538427d6294e109fd91538427c6454e10d7d8d538427f6254e109f189538435d5314e109f990538427d6414e10d798c538427e6214e109f58853843756114e10de980538427f65d0e109f997438427d65d0e109f197438427f6590e109f996438427d6590e109f196438427f6550e109f995438427d6550e109f19543842f76150e10bd185
  | 7 => 0x20c820be98032082f9600c820ddd46510827e64944209f592510827e63944209f58e510827f64544209f191510827f63544209f18d51082be6414420af59051082de6314420b758c510837551144209fd97410827e65d04209f597410833e54d0420cf55341082ee62d0420bb58b410827f65904209f996410827d6590420dd946410837551904209fd95410827d65504209f195410833e5450420cf55141082ef6250420bb18941083765150420dd54541082fb6050420be181410827f65104209f994410827d65104209fd97310827e65cc4209f597310835e53cc420d754f31082ee62cc420bb58b310827f658c4209f996310827d658c420dd9463108375518c4209fd95310827d654c4209f195310835e534c420d754d31082ef624c420bb1893108376514c420dd54531082fb604c420be181310827f650c4209f994310827d650c420dd947210837551c8420be98321082f960c84209f59621082ed6588420db59621082ee6188420db54621082ed60884209fd9521083765108420dd54421082fa6008420be58021082ee6108420f998421083e65108420db54421083e55108420d954421083ea6008420bb58021083e96008420ba580210827e64940209f592500827e63940209f58e500836e2194020db086500827d65d00209fd96400827d6590020cf952400833d5490020bb98a40082ed62900209fd95400827f65100209f994400827d65100209f194400833e5410020cf55040082ee6210020bb58840083b940100209f597300827f658c0209f596300835e538c020d754e30082ee628c020bb58a300827f654c0209fd94300827e650c0209f594300827c650c020d794c300835d530c020bb98830082ed620c020f64c030082ee61c8020bb58a200836e5288020be58a200837a5288020fa94a20083ea2188020fa086200827f6548020bbd95200836f65480209bd9520082ec6148020bbd81200836e5048020fad0120083e84048020facc120083e83048020bed95200837b65480209ed9520082fb6248020fad89200837a5248020fa94920083eb4248020fa10920083eb3248020fa0c920083eb2148020fa485200827e63d53109f58f54c427e62d53109f58b54c437661d5310de58354c433f54953109f98e54c427d63953109f98a54c427d6295310cfd9154c427f63553109f18d54c427f62553109f18954c433d5415310cf99054c427e63153109f58c54c427e62153109f58854c43766115310de58054c427e64d4f109f59353c427e62d4f109f58b53c437661d4f10de58353c435f5394f109f99253c427d6494f109f98a53c427d6294f109fd9153c427c6454f10d7d8d53c427f6254f109f18953c435d5314f109f99053c427d6414f10d798c53c427e6214f109f58853c43766114f10de58053c427f65d0f109f99743c4
  | 8 => 0x20dd147314827e658c5209f596314827c658c520d7d4e314835c538c5209fd95314827e654c5209f195314827e650c5209f594314827c650c520d7d4c314835c530c520bb98831482ed620c520ddd443148374510c520be98031482f9600c5209f99721483775188520dd14621482fa6088520be58221483775148520dd14521482fb6048520be181214827e6508520f9484214827e65d0120cfd53404833c54d0120bb98b40482ed62d01209f996404827f65501209f595404827c6550120cfd51404833c5450120bbd8940482ec62501209f994404827e65cc120d7d4f304835c53cc120bb98b30482ed62cc1209f996304827f654c1209f595304827c654c120d7d4d304835c534c120bbd8930482ec624c1209f994304836c5188120fad42204827e63d50209f58f540827e62d5020db98b540827e61d50209f587540827e60d5020de983540827d6595020cfd52540827e63950209f58e540827e61950209f586540833f64550209fd8d540827c63550209fd89540827d62550209fd85540827c6155020cf55054082de6315020b758c54082f66115020bd584540827e6415020cf990540827e6315020d798c540825e63150209f58c540835d63150209758c540827e6215020db988540827e6115020dd984540827661150209f584540837561150209d584540827e6015020de980540827e64d4c209f593530827e62d4c20db98b530827e61d4c209f587530827e60d4c20de983530827d6594c20d7d4e530827e6494c209f592530827e6194c209f586530827f6454c209f191530835f6354c209fd89530827d6254c209fd85530827c6154c20af99053082bd6414c20d754c53082f66114c20bd584530827e6414c20cf990530823e6414c209f590530833d6414c208f590530827e6314c20d798c530827e6214c20db988530827e6114c20dd98453082766114c209f58453083756114c209d584530827e6014c20de980530827f65d0c209f997430827d65d0c209f197430833e54d0c20cf553430827f6590c209f996430827d6590c209f196430835e5390c20d754e430827f6550c209f995430827d6550c209f195430833e5450c20cf551430835e5350c20d754d43082ef6250c20bb18943082fb6050c20be181430827f6510c209f994430827d6510c209f194430839d4310c20bb98843082ed6210c209f992520827d64948209f98e520827d63948209f597420827f65908209f596420833e5490820cf55242082fa6090820be582420827f65508209fd94420827d6510820cf950420833d5410820b798c42082dd6310820eb50842082fa6010820be580420827d65cc8209fd96320827d658c820d794e320835d538c820be98232082f9608c8209fd95320827f650c8209f59432082be640c820af590320835e530c820d754c32083cd3
  | 9 => 0x54521882fb6048620be18121882ed6508620db59421883e66108620db54421882ed6008620cf952408833d5490220bb98a40882ed6290220cf950408833d5410220bb98840882ed6210220d794e308835d538c220bb98a30882ed628c220d794c308835d530c220bb98830882ed620c220bb597208836d65c8220bb98720882f965c8220de597208827e63d51209f58f544827e61d51209f587544833f54951209f992544827e63951209f58e544827d6295120db58a544827e61951209f586544827d6095120de58254482df6355120b718d54482f76155120bd185544833f64551209fd8d544835f635512097d8d544827c6355120d718d544825c63551209fd89544836f62551209fd85544837761551209dd85544827c6155120dd185544827461551209fd81544837b60551209f994544833d5415120cf990544827e63151209f58c544827e62151209f188544827e61151209f584544827e64d4d209f593534827e61d4d209f587534835f5394d209f992534827d6494d209f98e534827d6294d20db58a534827e6194d209f586534827d6094d20de58253482bf6454d20af19153482f76154d20bd185534827f6454d20cfd91534823f6454d209f191534833c6454d208f191534835f6354d209fd89534836f6254d209fd8553483776154d209dd85534827c6154d20dd18553482746154d209fd81534837b6054d209f994534835d5314d209f990534827d6414d20d798c534827e6214d209f188534827e6114d209f584534827f65d0d209f997434827d65d0d209f197434835f53d0d20d714f434827f6590d209f996434827d6590d209f196434833f5490d20cf152434827f6550d209f995434827d6550d209f195434827f6510d209f994434827d6510d209f194434833f5410d20cf150434835f5310d20d714c434839d4310d20bb98843482ed6210d209f997424833f54d0920cf15342482fa60d0920be583424827e65909209f195424833f5450920cf15142482fb6050920be181424827e6510920b798c42482dd6310920eb508424827e65cc920d7d4f324835c53cc920be98332482f960cc9209f996324827c654c920d7d4d324835c534c920bed8132482f8604c9209f99432482be640c920af59032483cd320c9209f993514827d64d45209f98f514827d63d4520ddd4651482bf6454520af19151482df6354520b718d514837551145209f990514827d64145209f98c514827d63145209f997414827d65d05209f197414837751d0520dd147414827e65905209f596414827c6590520cfd52414833c54905209fd95414827e65505209f195414827e65105209f594414827c6510520cfd50414833c5410520bb98841482ed6210520ddd4441483745110520be98041482f960105209f997314827d65cc5209f197314837751cc5
  | 10 => 0x1c827f65d07209f99741c827d65d07209fd9641c827e65907209f59641c833e5490720cf55241c827f65507209f59541c827c6550720bed8141c82f860507209fd9441c827e65107209f59441c833e5410720cf55041c82ee6210720bb58841c827f65cc7209f99731c827d65cc7209fd9631c827e658c7209f59631c835e538c720d754e31c827f654c7209f59531c827c654c720bed8131c82f8604c7209fd9431c827e650c7209f59431c835e530c720d754c31c82ee620c720bb58831c837651c8720dd54721c82fa60c8720be58321c83765108720dd54421c83e52108720be98021c82f96008720cf95340c833d54d0320bb98b40c82ed62d0320cf95140c833d5450320bbd8940c82ec6250320ee50040c835e53cc320d754f30c82ee62cc320bb58b30c835e534c320d754d30c82ef624c320bb18930c83d9300c3209f98f548827d63d5220db58b548827e61d52209f587548837a60d5220cfd52548827e63952209f58e548827e61952209f586548833f64552209fd8d548827c63552209fd85548827c6155220cf550548833e64152209f98c548827d6315220db588548827e61152209f584548837a60152209f993538827d64d4e20db58b538827e61d4e209f587538837a60d4e20d7d4e538827e6494e209f592538827e6194e209f586538827f6454e209f191538835f6354e209fd85538827c6154e20d754c538827e6414e209f590538835e6314e20db588538827e6114e209f584538837a6014e209fd97438827e65d0e209f597438827c65d0e209fd96438827e6590e209f596438827c6590e209fd95438827e6550e209f595438827c6550e20bbd8943882ec6250e209fd94438827e6510e209f594438827c6510e20e750c43882ee6210e20bb588438833e54d0a20cf55342882fa60d0a20be583428833e5450a20cf55142882fb6050a20be18142882de6310a20b758c42883ad4210a20d794f328835d53cca20be98332882f960cca20d794d328835d534ca20bed8132882f8604ca20af99032882bd640ca20f34c8328837751946209f992518827d64946209f98e518827d63946209fd91518827c64546209fd8d518827c6354620dd544518827f65d06209f997418827d65d0620bb98b41882ed62d06209fd96418827e65906209f596418827f65506209f595418827c6550620bbd8941882ec62506209fd94418827e65106209f59441882fa6010620be580418827f65cc6209f997318827d65cc620bb98b31882ed62cc6209fd96318827e658c6209f596318827f654c6209f595318827c654c620bbd8931882ec624c6209fd94318827e650c6209f59431882fa600c620be58031883765188620dd54621882fa6088620be58221883e65188620db54621883e55188620fa98221882ed6088620fa58221883765148620dd
  | 11 => 0x76510c430dd544310c2fa600c430be580310c2de610c430f5984310c3d6510c430d7544310c3d5510c430d5544310c3da600c430b7580310c3d9600c430b6580310c27f65c84309f997210c27d65c8430b798f210c2dd63c8430db94b210c36d52c84309fd96210c27e65884309f596210c3765188430dd546210c27f65484309f595210c27c6548430b7d8d210c2dc6348430db949210c36d5248430dd945210c3755148430bed81210c2f860484309fd94210c27e65084309f594210c27e64940309f592500c35e3194030d70c6500c27d65d00309fd96400c27d6590030cf952400c33d5490030b798e400c2dd63900309fd95400c27f65100309f994400c27d65100309f194400c33e5410030cf550400c2de6310030b758c400c3b94010030b7987300c2dd638c030d794e300c2f9638c030de94e300c3da538c030f68c6300c3d8318c0309fd95300c2df654c030d7d95300c25f654c030b7185300c2df604c030d7941300c3db404c030f6101300c2fb654c030ded95300c27b654c030bed8d300c3db634c030de94d300c3da534c030f6d0d300c3d8434c030f68c9300c3d8324c030f6cc5300c3d9314c0309f98f54c827d63d5320db98b54c827e61d53209f58754c837960d5320cfd5254c827e63953209f58e54c827e61953209f58654c833f64553209fd8d54c827c63553209fd8554c827c6155320cf55054c82de6315320b758c54c833e64153209f98c54c835e63153209798c54c827d6315320d758c54c825d6315320db98854c827e61153209f58454c837960153209f99353c827d64d4f20db98b53c827e61d4f209f58753c837960d4f20d7d4e53c827e6494f209f59253c827e6194f209f58653c827f6454f209f19153c835f6354f209fd8553c827c6154f20af99053c82bd6414f20d754c53c827e6414f20cf99053c823e6414f209f59053c833d6414f208f59053c835e6314f20db98853c827e6114f209f58453c83796014f209fd9743c827e65d0f209f59743c827c65d0f20cf95343c833d54d0f209fd9643c827e6590f209f59643c827c6590f20d794e43c835d5390f209fd9543c827e6550f209f59543c827c6550f20cf95143c833d5450f20d794d43c835d5350f20bed8143c82f86050f209fd9443c827e6510f209f59443c827c6510f20e750c43c82ee6210f20bb58843c833e5490b20cf55242c82fa6090b20be58242c833e5410b20cf55042c82de6310b20b758c42c83ad4210b20be98042c82f96010b20d794e32c835d538cb20be98232c82f9608cb20af99032c82bd640cb20d794c32c835d530cb20f34c832c82fa600cb20be58032c82be64d4720af59351c82de63d4720b758f51c837751947209f99251c827d64947209f98e51c827d63947209fd9151c827c64547209fd8d51c827c6354720dd5445
  | 12 => 0x8c530be582314c377514c530dd145314c2fb604c530be181314c27e650c530f54c4314c27e65c85309f597214c27c65c8530ddd47214c37451c85309f996214c27d65885309f196214c36f5288530db14a214c27f65485309f995214c27c65485309f994214c27d65085309f194214c2de6308530b758c214c36f5208530db148214c3775108530dd144214c2fa6008530be580214c27e65d0130cfd53404c33c54d0130b798f404c2dd63d01309f996404c27f65501309f595404c27c6550130cfd51404c33c5450130b7d8d404c2dc63501309f994404c35c518c130f6d42304c27e63d5030d798f540c27e62d50309f58b540c27e61d50309f587540c27e60d5030de983540c27d6595030cfd52540c27e62950309f58a540c27e61950309f586540c33f64550309fd8d540c27d63550309fd89540c27c62550309fd85540c27c6155030cf550540c2ee6215030bb588540c2f66115030bd584540c27e6415030cf990540c27e6315030d798c540c27e6215030db988540c26e62150309f588540c36d62150309b588540c27e6115030dd984540c27661150309f584540c37561150309d584540c27e6015030de980540c27e6494c309f592530c27d65d0c309fd96430c27d6590c30cf952430c33d5490c30be982430c2f96090c309fd95430c27f6510c309f594430c33e5410c30cf550430c39d4310c30bb988430c2ed6210c30be980430c2f96010c30dbd4a520c27e64948309f592520c27e61948309f586520c27f64548309f191520c27f61548309f185520c2be6414830af590520c36d5214830bd984520c2f561148309fd97420c27e65d08309f597420c33e54d0830cf553420c27f65908309f996420c27d6590830db94a420c36d52908309fd95420c27d65508309f195420c33e5450830cf551420c2df6350830b718d420c36e5250830db549420c2fb6050830be181420c27f65108309f994420c27d6510830b798c420c2dd6310830eb508420c36e52cc830db54b320c2fa60cc830be583320c27d658c8309fd95320c2be640c830af590320c36e520c830db548320c3cd320c830be980320c2f9600c830ddd46510c27e64944309f592510c27e62944309f58a510c27f64544309f191510c27f62544309f189510c2be6414430af590510c2ee6214430bb588510c37551144309fd97410c27e65d04309f597410c33e54d0430cf553410c2de63d0430b758f410c27f65904309f996410c27d6590430dd946410c37551904309fd95410c27d65504309f195410c33e5450430cf551410c2df6350430b718d410c3765150430dd545410c2fb6050430be181410c27f65104309f994410c27d6510430dd947310c37551cc430be983310c2f960cc4309f596310c2dd658c430d7596310c2de618c430d7546310c2dd608c4309fd95310c3
  | 13 => 0xb798f418c2dd63d06309fd96418c27e65906309f596418c27f65506309f595418c27c6550630b7d8d418c2dc63506309fd94418c27e65106309f594418c2fa6010630be580418c376518c630dd546318c2fa608c630be582318c3d6518c630d7546318c3d5518c630f6982318c2dd608c630f6582318c376514c630dd545318c2fb604c630be181318c2dd650c630d7594318c3d6610c630d7544318c2dd600c6309fd97218c27e65c86309f597218c2de63c8630b758f218c27f65886309f996218c27d65886309fd95218c27d65486309f195218c2df6348630b718d218c27f65086309f994218c27d6508630be980218c2f96008630cf952408c33d5490230b798e408c2dd6390230cf950408c33d5410230b798c408c2dd6310230b7597308c35d65cc230b7987308c2f965cc230de597308c27e62d51309f58b544c27e61d51309f587544c33f54951309f992544c27d6395130d758e544c27e62951309f58a544c27e61951309f586544c27d6095130de582544c2ef6255130bb189544c2f76155130bd185544c33f64551309fd8d544c35f63551309fd89544c36f62551309bd89544c27c6255130db189544c26c62551309fd85544c37761551309dd85544c27c6155130dd185544c27461551309fd81544c37b60551309f994544c33d5415130cf990544c27e63151309f18c544c27e62151309f588544c27e61151309f584544c27e65d0d30cfd53434c33c54d0d30be983434c2f960d0d309f996434c27c6550d30cfd51434c33c5450d30bed81434c2f86050d309f994434c39d4310d30bb988434c2ed6210d309f993524c27d64d49309f987524c27d61d4930dbd4a524c2bf6454930af191524c2f76154930bd185524c36d52149309f990524c27d64149309f984524c27d61149309f997424c27d65d09309f197424c36f52d0930db14b424c27e65909309f596424c27c6590930cfd52424c33c54909309fd95424c27e65509309f195424c27e65109309f594424c27c6510930cfd50424c33c5410930b798c424c2dd6310930dbd48424c36c5210930eb508424c27e65cc930dbd4a324c36c528c930be982324c2f9608c930dbd49324c36c524c930bed81324c2f8604c9309f994324c2be640c930af590324c3cd320c9309f993514c27d64d45309f98b514c27d62d4530ddd46514c2bf6454530af191514c2ef6254530bb189514c37551145309f990514c27d64145309f988514c27d62145309f997414c27d65d05309f197414c37751d0530dd147414c27e65905309f596414c27c6590530cfd52414c33c54905309fd95414c27e65505309f195414c27e65105309f594414c27c6510530cfd50414c33c5410530b798c414c2dd6310530ddd44414c3745110530be980414c2f960105309f997314c377518c530dd146314c2fa60
  | 14 => 0x5243cc2fa6090f30be58243cc33e5410f30cf55043cc39d4310f30bb98843cc2ed6210f30be98043cc2f96010f30dbd4a52cc27e6494b309f59252cc27e6194b309f58652cc27f6454b309f19152cc27f6154b309f18552cc2be6414b30af59052cc36d5214b309fd9742cc27e65d0b309f59742cc33e54d0b30cf55342cc27f6590b309f99642cc27d6590b30db94a42cc36d5290b309fd9542cc27d6550b309f19542cc33e5450b30cf55142cc36e5250b30db54942cc2fb6050b30be18142cc27f6510b309f99442cc27d6510b30b798c42cc2dd6310b30eb50842cc36e52ccb30db54b32cc2fa60ccb30be58332cc2be640cb30af59032cc36e520cb30db54832cc3cd320cb30be98032cc2f9600cb30af99351cc2bd64d4730bb98b51cc2ed62d4730ddd4651cc27e64947309f59251cc27e62947309f58a51cc27f64547309f19151cc27f62547309f18951cc37551147309fd9741cc27e65d07309f59741cc27f65907309f99641cc27d6590730cf95241cc33d54907309fd9541cc27d65507309f19541cc2fb6050730be18141cc27f65107309f99441cc27d6510730cf95041cc33d5410730b798c41cc2dd6310730dd94731cc37551cc730be98331cc2f960cc730dd94431cc375510c730f54c431cc2fa600c730be58031cc27f65c87309f99721cc27d65c87309fd9621cc27e65887309f59621cc36e5288730db54a21cc27f65487309f59521cc27c6548730bed8121cc2f860487309fd9421cc27e65087309f59421cc2de6308730b758c21cc36e5208730db54821cc33e54d0330cf55340cc2de63d0330b758f40cc33e5450330cf55140cc2df6350330b718d40cc3b94010330d758f548c27e62d52309f58b548c27e61d52309f587548c37a60d5230cfd52548c27e62952309f58a548c27e61952309f586548c33f64552309fd89548c27c62552309fd85548c27c6155230cf550548c33e6415230d758c548c27e62152309f588548c27e61152309f584548c37a6015230cf953438c33d54d0e30be983438c2f960d0e30cf951438c33d5450e30bed81438c2f86050e30e750c438c2ee6210e30bb588438c36f5294a309f992528c27d6494a309f986528c27d6194a309fd91528c27c6454a309fd85528c27c6154a30db548528c27f65d0a309f997428c27d65d0a309fd96428c27e6590a309f596428c27f6550a309f595428c27c6550a30b7d8d428c2dc6350a309fd94428c27e6510a309f594428c2de6310a30b758c428c3ad4210a30db94a328c36d528ca30be982328c2f9608ca30db949328c36d524ca30bed81328c2f8604ca30af990328c2bd640ca30f34c8328c37751946309f992518c27d64946309f98a518c27d62946309fd91518c27c64546309fd89518c27c6254630dd544518c27f65d06309f997418c27d65d063
  | 15 => 0x1027d6590c409fd95431035e5310c40d754c431039d4310c40bb98843102ed6210c40be98043102f96010c40dbd4a521027e63948409f58e521027e61948409f586521027f63548409f18d521027f61548409f18552102de6314840b758c521036d5214840bd98452102f56114840db94b421036d52d0840be98342102f960d08409f596421027f6550840b798c42102dd6310840db948421036d5210840eb50842102fa6010840be580421027f65cc8409f997321027d65cc840d794f321035d53cc8409fd96321027e658c8409f596321036e528c840db54a321027f654c8409f595321027c654c840afd9132102bc644c840d794d321035d534c840db949321036d524c840bed8132102f8604c8409fd94321027e650c8409f59432102be640c840af59032103cd320c840ddd46511027e63944409f58e511027e62944409f58a511027f63544409f18d511027f62544409f18951102de6314440b758c51102ee6214440bb58851103755114440dd947411037551d0440be98341102f960d04409f59641102bd6590440cf59641102be6190440cf54641102bd60904409fd9541103765110440dd54441102fa6010440be58041102be6110440ed98441103b65110440cf54441103b55110440cd54441103ba6010440af58041103b96010440ae580411027f65cc4409f997311027d65cc440af99331102bd64cc440d794f311035d53cc4409fd96311027e658c4409f5963110376518c440dd546311027f654c4409f595311027c654c440afd9131102bc644c440d794d311035d534c440dd9453110375514c440bed8131102f8604c4409fd94311027e650c4409f594311027f65c84409f997211027d65c8440af99321102bd64c8440db94b211036d52c84409fd96211027e65884409f59621103765188440dd546211027f65484409f595211027c6548440afd9121102bc6448440db949211036d5248440dd94521103755148440bed8121102f860484409fd94211027e65084409f594211033e4194040cf10650102be61d0040af592401033e5490040be592401037a5490040ee95240103ba4190040ee106401027f6550040afd95401033f65500408fd9540102bc6150040afd81401033e5050040bed95401037b65500409ed9540102fb6450040eed91401037a5450040ee95140103ba4350040ee10d40103ba4250040ee10940103bb4150040ee505401035e63d53309f98b54cc27d62d53309f98754cc27d61d5330de58354cc33f54953309f98a54cc27d62953309f98654cc27d6195330cfd9154cc27f62553309f18954cc27f61553309f18554cc33d5415330bb98854cc2ed6215330cf99054cc35e63153309f98854cc36e62153309b98854cc27d6215330db58854cc26d62153309f98454cc27d6115330de58054cc33e5490f30cf5
  | 16 => 0xd6510640cf59441903b66110640cf54441902bd60106409fd97319027e65cc6409f59731902be64cc640af593319027f658c6409f996319027d658c6409fd95319027d654c6409f19531902bf644c640af191319027f650c6409f994319027d650c640be98031902f9600c6409fd97219027e65c86409f59721902be64c8640af593219027f65886409f996219027d65886409fd95219027d65486409f19521902bf6448640af191219027f65086409f994219027d6508640be98021902f96008640af597409033d65d0240af98740902f965d0240de597409027e62d4d409f58b535027e61d4d409f587535035f5394d40bbd8953502ec6254d40bdd8553502f46154d40d754c535027e6214d409f588535027e6114d409f584535027e65d0d40d7d4e435035c5390d40be98243502f96090d40d7d4d435035c5350d40bed8143502f86050d409f994435039d4310d40bb98843502ed6210d409f98f525027d63d49409f987525027d61d4940dbd4a52502df6354940b718d52502f76154940bd185525036d52149409f98c525027d63149409f984525027d61149409f997425036f5290940db14a42502fa6090940be582425036f5250940db14942502fb6050940be181425027e6510940b798c42502dd6310940eb508425027e65cc9409f597325027c65cc940dbd4b325036c52cc9409f996325027d658c9409f196325035f538c940d714e325027f654c9409f995325027c654c9409f994325027d650c9409f19432502be640c940af590325035f530c940d714c325036f520c940db14832503cd320c9409f98f515027d63d45409f98b515027d62d4540ddd4651502df6354540b718d51502ef6254540bb189515037551145409f98c515027d63145409f988515027d62145409f99741503775190540dd14641502fa6090540be58241503775150540dd14541502fb6050540be181415027e6510540ed504415027e65cc5409f597315027c65cc540ddd47315037451cc5409f996315027d658c5409f196315035f538c540d714e315027f654c5409f995315027c654c5409f994315027d650c5409f19431502be640c540af590315035f530c540d714c3150377510c540dd14431502fa600c540be580315027e65c85409f597215027c65c8540ddd47215037451c85409f996215027d65885409f196215036f5288540db14a215027f65485409f995215027c65485409f994215027d65085409f19421502be6408540af590215036f5208540db14821503775108540dd14421502fa6008540be580215033c5190140eed42405035f5394c409f98a531027d6294c409f986531027d6194c409fd89531027c6254c409fd85531027c6154c40d754c53102ee6214c40bb58853102f66114c40bd584531035e53d0c40d754f43102fa60d0c40be58343
  | 17 => 0x4f409f58a53d027e6194f409f58653d027f6254f409f18953d027f6154f409f18553d035d5314f40bb98853d02ed6214f40d794f43d035d53d0f40be98343d02f960d0f40d794c43d035d5310f40e750c43d02ee6210f40bb58843d02fa6010f40be58043d036f5294b409f98e52d027d6394b409f98652d027d6194b409fd8d52d027c6354b409fd8552d027c6154b40b798c52d02dd6314b40db54852d036e52d0b40db54b42d02fa60d0b40be58342d02de6310b40b758c42d036e5210b40db54842d03ad4210b40be98042d02f96010b409fd9732d027e65ccb409f59732d035e53ccb40d754f32d027f658cb409f99632d027d658cb40db94a32d036d528cb409fd9532d027d654cb409f19532d035e534cb40d754d32d036e524cb40db54932d02fb604cb40be18132d027f650cb409f99432d027d650cb40af99032d02bd640cb40f34c832d02de63d4740b758f51d02ee62d4740bb58b51d037751947409f98e51d027d63947409f98a51d027d62947409fd8d51d027c63547409fd8951d027c6254740dd54451d037651d0740dd54741d02fa60d0740be58341d03765110740dd54441d03b54110740be98041d02f960107409fd9731d027e65cc7409f59731d027f658c7409f99631d027d658c740d794e31d035d538c7409fd9531d027d654c7409f19531d02fb604c740be18131d027f650c7409f99431d027d650c740af99031d02bd640c740d794c31d035d530c7409fd9721d027e65c87409f59721d027f65887409f99621d027d6588740db94a21d036d52887409fd9521d027d65487409f19521d02fb6048740be18121d027f65087409f99421d027d6508740af99021d02bd6408740db94821d036d5208740d7d4e539027e6294e409f58a539027e6194e409f586539027f6254e409f189539027f6154e409f185539035d5314e40d794e439035d5390e40be98243902f96090e40d794d439035d5350e40bed8143902f86050e40e750c43902ee6210e40bb588439036f5294a409f98e529027d6394a409f986529027d6194a409fd8d529027c6354a409fd85529027c6154a40db548529036e5290a40db54a42902fa6090a40be582429036e5250a40db54942902fb6050a40be18142902de6310a40b758c42903ad4210a409fd97329027e65cca409f597329027f658ca409f996329027d658ca409fd95329027d654ca409f19532902bf644ca40af191329027f650ca409f994329027d650ca40af99032902bd640ca40f34c8329037751946409f98e519027d63946409f98a519027d62946409fd8d519027c63546409fd89519027c6254640dd54451903765190640dd54641902fa6090640be58241903b65190640cf54641903b55190640ee98241902bd6090640ee58241903765150640dd54541902fb6050640be18141902b
  | 18 => 0xcf55054086de6315021b758c54086fa6015021be580540867e6415021cf990540867e6315021d798c540865e63150219f58c540875d63150219758c540867e6215021db988540867e6115021dd984540867e6015021de980540867a60150219f580540877960150219e580540867e64d4c219f593530867e62d4c21db98b530867e61d4c21dd987530867e60d4c219f583530867d6594c21d7d4e530867e6494c219f592530867e6094c219f582530867f6454c219f191530875f6354c219fd81530867c6054c21af99053086bd6414c21d754c53086fa6014c21be580530867e6414c21cf990530863e6414c219f590530873d6414c218f590530867e6314c21d798c530867e6214c21db988530867e6114c21dd984530867e6014c21de980530867a6014c219f58053087796014c219e580530867f65d0c219f997430867d65d0c219f197430873e54d0c21cf553430867f6590c219f996430867d6590c219f196430875e5390c21d754e430867f6550c219f995430867d6550c219f195430873e5450c21cf551430875e5350c21d754d43086ef6250c21bb18943086f76150c21bd185430867f6510c219f994430867d6510c219f194430879d4310c21bb98843086ed6210c219f992520867d64948219f98e520867d63948219f597420867f65908219f596420873e5490821cf55242086f66190821bd586420867f65508219fd94420867d6510821cf950420873d5410821b798c42086dd6310821eb50842086f66110821bd584420867d65cc8219fd96320867d658c821d794e320875d538c821bd98632086f5618c8219fd95320867f650c8219f59432086be640c821af590320875e530c821d754c32087cd320c821bd98432086f5610c8219f992510867d64944219f98e510867d63944219f597410867f65904219f596410873e5490421cf55241086ee6290421bb58a410867f65504219fd94410867e65104219f594410867c6510421cf950410873d5410421bb98841086ed6210421ed504410867d65cc4219fd96310867d658c421d794e310875d538c421bb98a31086ed628c4219fd95310867f650c4219f994310867d650c4219f194310875e530c421d754c31086ee620c421bb58831087d5310c421bb98321086ed6288421db94a21086f56288421dd94a21087e652884219fd9521086ef6548421dbd95210866f6548421bbd85210876e5148421f9d0521087e44148421f9cc521087e43148421bb18121086f76548421ddd9521086776548421bdd8921087e76248421dd94921087e65248421f9d0921087e44248421f9cc921087e43248421ded42500867e64940219f592500867e63940219f58e500867f64540219f191500867f63540219f18d50086be6414021af59050086de6314021b758c50087795014021d7d4e53d027e629
  | 19 => 0x7218877565c8621ded42508867e64942219f592508867e63942219f58e508867f64542219f191508867f63542219f18d508877950142219f98f544867d63d51219f983544867d60d5121cfd52544867e64951219f98e544867d63951219f58a544876d62951219f586544877561951219f982544867d6095121b7d8d54486dc6355121bed8154486f86055121cfd91544867f6355121d7d8d544865f63551219f18d544875c63551219718d544867f6255121dbd89544867f6155121ddd85544867f6055121ded81544867b60551219f181544877860551219e181544867e6515121cf550544873e64151219f98c544867d63151219f980544867d60151219f993534867d64d4d219f983534867d60d4d21d7d4e534867e6494d219f592534867e6394d219f58a534876d6294d219f58653487756194d219f982534867d6094d21afd9153486bc6454d21bed8153486f86054d219fd91534873f6454d218fd91534867c6454d21cf191534863c6454d21d7d8d534867f6254d21dbd89534867f6154d21ddd85534867f6054d21ded81534867b6054d219f18153487786054d219e181534867e6514d21d754c534867e6414d219f590534875e6314d219f980534867d6014d219fd97434867e65d0d219f597434867c65d0d21d7d4f434875c53d0d219fd96434867e6590d219f596434867c6590d21cfd52434873c5490d219fd95434867e6550d219f595434867c6550d219fd94434867e6510d219f594434867c6510d21cfd50434873c5410d21d7d4c434875c5310d21e750c43486ee6210d21bb588434867e65d0921cfd53424873c54d0921bd98742486f561d09219f996424867c6550921cfd51424873c5450921bdd8542486f461509219f99442486de6310921b758c42487ad42109219f997324875f53cc921d714f32486f661cc921bd587324867e658c9219f195324875f534c921d714d32486f7614c921bd185324867e650c921af99032486bd640c921f34c8324867e65d0521cfd53414873c54d0521bb98b41486ed62d05219f996414867f65505219f595414867c6550521cfd51414873c5450521bbd8941486ec62505219f994414867e65cc521d7d4f314875c53cc521bb98b31486ed62cc5219f996314867f654c5219f595314867c654c521d7d4d314875c534c521bbd8931486ec624c5219f99431487e751885219f993504867d64d41219f98f504867d63d4121ded4250486bf6454121af19150486df6354121b718d504877950141219f990504867d64141219f98c504867d6314121db884504867e63d50219f58f540867e62d5021db98b540867e61d5021dd987540867e60d50219f583540867d6595021cfd52540867e63950219f58e540867e60950219f582540873f64550219fd8d540867c63550219fd81540867c6055021
  | 20 => 0x867d6494f219f98253c867d6094f219fd9153c867c6454f21d7d8d53c867f6054f219f18153c86be6414f21af59053c875d5314f219f99053c873e6414f218f99053c867d6414f21cf59053c863d6414f21d798c53c876e6214f21dd58453c867e6014f219f58053c867f65d0f219f99743c867d65d0f219f19743c873e54d0f21cf55343c867f6590f219f99643c867d6590f219f19643c875e5390f21d754e43c867f6550f219f99543c867d6550f219f19543c873e5450f21cf55143c875e5350f21d754d43c86f76150f21bd18543c867f6510f219f99443c867d6510f219f19443c879d4310f21bb98843c86ed6210f21cf95242c873d5490b21bd98642c86f56190b21cf95042c873d5410b21b798c42c86dd6310b21eb50842c86f66110b21bd58442c875e538cb21d754e32c86f6618cb21bd58632c86be640cb21af59032c875e530cb21d754c32c87cd320cb21bd98432c86f5610cb21cf95341c873d54d0721bb98b41c86ed62d0721cf95141c873d5450721bbd8941c86ec6250721ed50441c875e53cc721d754f31c86ee62cc721bb58b31c875e534c721d754d31c86ef624c721bb18931c87d5310c721af99350c86bd64d4321b798f50c86dd63d4321ded4250c867e64943219f59250c867e63943219f58e50c867f64543219f19150c867f63543219f18d50c877950143219f98f548867d63d5221db58b548877661d52219f983548867d60d5221cfd52548867e63952219f58e548867e60952219f582548873f64552219fd8d548867c63552219fd81548867c6055221cf550548873e64152219f98c548867d6315221db588548877661152219f980548867d60152219f993538867d64d4e21db58b538877661d4e219f983538867d60d4e21d7d4e538867e6494e219f592538867e6094e219f582538867f6454e219f191538875f6354e219fd81538867c6054e21d754c538867e6414e219f590538875e6314e21db58853887766114e219f980538867d6014e219fd97438867e65d0e219f597438867c65d0e219fd96438867e6590e219f596438867c6590e219fd95438867e6550e219f595438867c6550e21bbd8943886ec6250e219fd94438867e6510e219f594438867c6510e21e750c43886ee6210e21bb588438873e54d0a21cf55342886f661d0a21bd587428873e5450a21cf55142886f76150a21bd18542886de6310a21b758c42887ad4210a21d794f328875d53cca21bd98732886f561cca21d794d328875d534ca21bdd8532886f4614ca21af99032886bd640ca21f34c8328873e5490621cf55241886ee6290621bb58a418873e5410621cf55041886ee6210621bb588418875e538c621d754e31886ee628c621bb58a318875e530c621d754c31886ee620c621bb58831886ed65c8621db59721886ee60c8621bd59
  | 21 => 0x64141319f988504c67d6214131d78c4504c67e63d5031d798f540c67e62d50319f58b540c67e61d5031dd987540c67e60d50319f583540c67d6595031cfd52540c67e62950319f58a540c67e60950319f582540c73f64550319fd89540c67c62550319fd81540c67c6055031cf550540c6ee6215031bb588540c6fa6015031be580540c67e6415031cf990540c67e6315031d798c540c67e6215031db988540c66e62150319f588540c76d62150319b588540c67e6115031dd984540c67e6015031de980540c67a60150319f580540c77960150319e580540c67e6494c319f592530c67d65d0c319fd96430c67d6590c31cf952430c73d5490c31bd986430c6f56190c319fd95430c67f6510c319f594430c73e5410c31cf550430c79d4310c31bb988430c6ed6210c31bd984430c6f56110c31dbd4a520c67e64948319f592520c67e60948319f582520c67f64548319f191520c67f60548319f181520c6be6414831af590520c76d5214831be980520c6f960148319fd97420c67e65d08319f597420c73e54d0831cf553420c67f65908319f996420c67d6590831db94a420c76d52908319fd95420c67d65508319f195420c73e5450831cf551420c6df6350831b718d420c76e5250831db549420c6f76150831bd185420c67f65108319f994420c67d6510831b798c420c6dd6310831eb508420c76e52cc831db54b320c6f661cc831bd587320c67d658c8319fd95320c6be640c831af590320c76e520c831db548320c7cd320c831bd984320c6f5610c8319f992510c67d64944319f597410c67f65904319f596410c73e5490431cf552410c6de6390431b758e410c67f65504319fd94410c67e65104319f594410c67c6510431cf950410c73d5410431b798c410c6dd6310431ed504410c6de60cc431b758e310c75e538c431bd58e310c776538c431f594e310c67f654c431b7d95310c75f654c43197d95310c6df614c431d7945310c7d7414c431f5105310c6dc604c431bdd95310c777654c4319dd95310c6f7634c431f5d8d310c776534c431f594d310c7d7434c431f510d310c7d6324c431f50c9310c77b50940319f992500c67d64940319f98a500c67d62940319fd91500c67c64540319fd89500c67c6254031af990500c6bd6414031bb988500c6ed6214031de540500c67e63d53219f58f54c876e62d5321dd58754c867e60d53219f58354c873f54953219f98e54c867d63953219f98254c867d6095321cfd9154c867f63553219f18d54c867f60553219f18154c873d5415321b798c54c86dd6315321cf99054c867e6315321d798c54c865e63153219f58c54c875d63153219758c54c876e6215321dd58454c867e60153219f58054c867e64d4f219f59353c876e62d4f21dd58753c867e60d4f219f58353c875f5394f219f99253c
  | 22 => 0x2319fd81548c67c6055231cf550548c73e6415231d758c548c67e62152319f588548c77661152319f980548c67d6015231cf953438c73d54d0e31bd987438c6f561d0e31cf951438c73d5450e31bdd85438c6f46150e31e750c438c6ee6210e31bb588438c76f5294a319f992528c67d6494a319f982528c67d6094a319fd91528c67c6454a319fd81528c67c6054a31db548528c67f65d0a319f997428c67d65d0a319fd96428c67e6590a319f596428c67f6550a319f595428c67c6550a31b7d8d428c6dc6350a319fd94428c67e6510a319f594428c6de6310a31b758c428c7ad4210a31db94a328c76d528ca31bd986328c6f5618ca31db949328c76d524ca31bdd85328c6f4614ca31af990328c6bd640ca31f34c8328c73e5490631cf552418c6de6390631b758e418c73e5410631cf550418c6de6310631b758c418c6dd65cc631d7597318c6de60cc631bd597318c77565cc631ded42508c67e64942319f592508c67e62942319f58a508c67f64542319f191508c67f62542319f189508c77950142319f98b544c67d62d51319f983544c67d60d5131cfd52544c67e64951319f58e544c75d63951319f98a544c67d62951319f586544c77561951319f982544c67d6095131bbd89544c6ec6255131bed81544c6f86055131cfd91544c67f6355131d7d8d544c67f6255131dbd89544c66f62551319f189544c76c62551319b189544c67f6155131ddd85544c67f6055131ded81544c67b60551319f181544c77860551319e181544c67e6515131cf550544c73e64151319f988544c67d62151319f980544c67d60151319f997434c73f54d0d31cf153434c6f661d0d31bd587434c67e6590d319f195434c73f5450d31cf151434c6f76150d31bd185434c67e6510d31e750c434c6ee6210d31bb588434c67e64d49319f593524c67e60d49319f583524c76f5294931afd91524c6bc6454931bed81524c6f86054931db548524c67e64149319f590524c67e60149319f580524c67e65d09319f597424c67c65d0931dbd4b424c76c52d09319f996424c67d65909319f196424c73f5490931cf152424c67f65509319f995424c67c65509319f994424c67d65109319f194424c73f5410931cf150424c6de6310931b758c424c76f5210931db148424c7ad42109319f997324c76f528c931db14a324c6f6618c931bd586324c76f524c931db149324c6f7614c931bd185324c67e650c931af990324c6bd640c931f34c8324c67e65d0531cfd53414c73c54d0531b798f414c6dd63d05319f996414c67f65505319f595414c67c6550531cfd51414c73c5450531b7d8d414c6dc63505319f994414c7d7518c5319f993504c67d64d41319f98b504c67d62d4131ded42504c6bf6454131af191504c6ef6254131bb189504c77950141319f990504c67d
  | 23 => 0xf58e521067e60948419f582521067f63548419f18d521067f60548419f18152106de6314841b758c521076d5214841be98052106f96014841db94b421076d52d0841bd98742106f561d08419f596421067f6550841b798c42106dd6310841db948421076d5210841eb50842106f66110841bd584421067f65cc8419f997321067d65cc841d794f321075d53cc8419fd96321067e658c8419f596321076e528c841db54a321067f654c8419f595321067c654c841afd9132106bc644c841d794d321075d534c841db949321076d524c841bdd8532106f4614c8419fd94321067e650c8419f59432106be640c841af59032107cd320c841af98341106bd6490441cf95241106f56490441dd95241107b654904419fd9541106bf6550441cfd95411063f6550441afd85411073e5150441af18141106f76550441ddd9541106776550441bdd9141107b76450441dd95141107b65450441ed90d41107b44350441ed90941107b44250441ded42501067e63940419f58e501067e62940419f58a501067f63540419f18d501067f62540419f18950106de6314041b758c50106ee6214041bb58850107795014041d798f54cc67e62d53319f58b54cc77561d53319f98354cc67d60d5331cfd5254cc67e62953319f58a54cc67e60953319f58254cc73f64553319fd8954cc67c62553319fd8154cc67c6055331cf55054cc6ee6215331bb58854cc73e6415331d798c54cc67e6215331db98854cc66e62153319f58854cc76d62153319b58854cc77561153319f98054cc67d6015331cf95243cc73d5490f31bd98643cc6f56190f31cf95043cc73d5410f31e750c43cc6ee6210f31bb58843cc6f66110f31bd58443cc76f5294b319f99252cc67d6494b319f98252cc67d6094b319fd9152cc67c6454b319fd8152cc67c6054b31af99052cc6bd6414b31db54852cc67f65d0b319f99742cc67d65d0b31cf95342cc73d54d0b319fd9642cc67e6590b319f59642cc76e5290b31db54a42cc67f6550b319f59542cc67c6550b31cf95142cc73d5450b31db94942cc76d5250b31bdd8542cc6f46150b319fd9442cc67e6510b319f59442cc6de6310b31b758c42cc7ad4210b31db94b32cc76d52ccb31bd98732cc6f561ccb31af99032cc6bd640cb31db94832cc76d520cb31f34c832cc6f6610cb31bd58432cc73e54d0731cf55341cc6de63d0731b758f41cc73e5450731cf55141cc6df6350731b718d41cc7b54110731af99350cc6bd64d4331bb98b50cc6ed62d4331ded4250cc67e64943319f59250cc67e62943319f58a50cc67f64543319f19150cc67f62543319f18950cc7795014331d758f548c67e62d52319f58b548c77661d52319f983548c67d60d5231cfd52548c67e62952319f58a548c67e60952319f582548c73f64552319fd89548c67c6255
  | 24 => 0x32d067e650cb419f59432d06be640cb41af59032d07cd320cb41b798f50d06dd63d4341bb98b50d06ed62d4341ded4250d067e63943419f58e50d067e62943419f58a50d067f63543419f18d50d067f62543419f18950d07795014341d7d4e539067e6294e419f58a539067e6094e419f582539067f6254e419f189539067f6054e419f181539075d5314e41d794e439075d5390e41bd98643906f56190e41d794d439075d5350e41bdd8543906f46150e41e750c43906ee6210e41bb588439076f5294a419f98e529067d6394a419f982529067d6094a419fd8d529067c6354a419fd81529067c6054a41db548529076e5290a41db54a42906f66190a41bd586429076e5250a41db54942906f76150a41bd18542906de6310a41b758c42907ad4210a419fd97329067e65cca419f597329067f658ca419f996329067d658ca419fd95329067d654ca419f19532906bf644ca41af191329067f650ca419f994329067d650ca41af99032906bd640ca41f34c832906bd65d0641cf59741906be60d0641bd597419077565d0641ded42509067e63942419f58e509067e62942419f58a509067f63542419f18d509067f62542419f189509077950142419f98b535067d62d4d419f983535067d60d4d41d7d4e53506ef6254d41bb18953506fb6054d41be181535075d5314d419f988535067d6214d419f980535067d6014d419f997435075f5390d41d714e43506f66190d41bd586435075f5350d41d714d43506f76150d41bd185435067e6510d41e750c43506ee6210d41bb588435067e63d49419f58f525067e60d49419f583525076f5294941b7d8d52506dc6354941bed8152506f86054941db548525067e63149419f58c525067e60149419f580525067e65d0941dbd4a425076c5290941bd98642506f56190941dbd49425076c5250941bdd8542506f461509419f99442506de6310941b758c42507ad42109419f997325067d65cc9419f197325076f52cc941db14b325067e658c9419f596325067c658c941d7d4e325075c538c9419fd95325067e654c9419f195325067e650c9419f594325067c650c941af99032506bd640c941d7d4c325075c530c941dbd48325076c520c941f34c832507b751905419f98f505067d63d41419f98b505067d62d4141ded4250506df6354141b718d50506ef6254141bb189505077950141419f98c505067d63141419f988505067d6214141cf904505075f5394c419f98a531067d6294c419f982531067d6094c419fd89531067c6254c419fd81531067c6054c41d754c53106ee6214c41bb58853106fa6014c41be580531075e53d0c41d754f43106f661d0c41bd587431067d6590c419fd95431075e5310c41d754c431079d4310c41bb98843106ed6210c41bd98443106f56110c41dbd4a521067e63948419
  | 25 => 0xb3d5490832b798e420cadd6390832db94a420ca7f6550832cf951420cb3d5450832db949420ca7f65108329f994420ca7d65108329f194420cb3e5410832cf550420cade6310832b758c420cbad4210832cf953320cb3d54cc832d7d53320cb9e54cc832d7553320cb9d54cc832c7553320cb3e548c832cf552320cadd638c832d794e320cb6f548c832eb952320cb6d548c832eb552320cb2d548c832bb58e320cacd638c832db94e320cbce538c8329fd95320cb3e544c832cf551320cadf654c832d7d95320ca5f654c832d7d51320cb9e544c832d7551320cb9d544c832c7551320cadf624c832d7949320cbcf424c832f3909320cbcd424c832f3109320caef654c832dbd95320ca6f654c832dbd51320cbae544c832db551320cbad544c832cb551320caef634c832f3d8d320cb6e534c832f394d320cbcf434c832f390d320cbcd434c832f310d320cbcf654c832b3d95320cb4f654c832f3d91320cbce644c832f3591320cbcc644c832f3d51320cb4f544c832f3951320cb8e544c832f3551320cb4d544c832e3551320cb0d544c832f3151320cbcf614c832f3985320cbcd614c832f3185320cbcf604c832f3981320cbcd604c832f3181320cabe64d4432af593510cb3e54d4432cf553510cbcd32d4432cf952510cb3d5494432f34ca510cb7751944329f992510ca7d64944329f982510ca7d6094432cf951510cb3d5454432f34c9510ca7f64544329f191510ca7f60544329f181510cabe6414432af590510cb3e5414432cf550510cbcd3214432dd544510cafa6014432be580510cabe64d4032af593500cb3e54d4032cf553500cbcd32d4032cf952500cb3d5494032f34ca500cb7b50940329f992500ca7d64940329f986500ca7d6194032cf951500cb3d5454032f34c9500ca7f64540329f191500ca7f61540329f185500cabe6414032af590500cb3e5414032cf550500cbcd3214032bd984500caf56114032de540500cb5f5394f419f98a53d067d6294f419f98253d067d6094f419fd8953d067c6254f419fd8153d067c6054f41d754c53d06ee6214f41bb58853d075e53d0f41d754f43d06f661d0f41bd58743d075e5310f41d754c43d079d4310f41bb98843d06ed6210f41bd98443d06f56110f41dbd4a52d067e6394b419f58e52d067e6094b419f58252d067f6354b419f18d52d067f6054b419f18152d06de6314b41b758c52d076d5214b41db94b42d076d52d0b41bd98742d06f561d0b41b798c42d06dd6310b41db94842d076d5210b41eb50842d06f66110b41bd58442d067f65ccb419f99732d067d65ccb41d794f32d075d53ccb419fd9632d067e658cb419f59632d076e528cb41db54a32d067f654cb419f59532d067c654cb41d794d32d075d534cb41db94932d076d524cb41bdd8532d06f4614cb419fd94
  | 26 => 0x1151329f584544ca7e60151329f580544ca7e65d0d32cfd53434cb3c54d0d32bb98b434caed62d0d329f996434cade6590d32d7996434cadd6490d32d7952434cb5c5490d32f3d8a434cade6290d32f318a434ca7c6550d32cfd51434cb3c5450d32bbd89434caec6250d32d7195434ca5c6550d32e7d91434cb9f5450d32d7951434cb5c5450d32e7151434cb1c5450d32f3d89434cadc6250d32f3189434cacc6250d329f994434cade6310d32e750c434caee6210d329f997424cb3f54d0932cf153424cade63d0932b758f424cb9d43d09329f996424caee6590932db996424caed6490932db952424cb6c5490932f3d8e424caee6390932f318e424cbce4390932f350e424ca7f65509329f595424ca7c6550932cfd51424cb3c5450932b7d8d424cadc6350932e750d424caec6550932db195424ca6c6550932ebd91424cbaf5450932db951424cb6c5450932eb151424cb2c5450932f3d8d424caec6350932f318d424cacc6350932ebd0d424cbce4350932eb50d424cbcd4350932e350d424ca7e6510932b798c424cadd6310932bb988424cbad4210932bbd93324caed64cc932f390f324cbcd43cc932b7d92324cadd648c932f3d4a324cbce428c932f350a324ca7e64d45329f593514ca7e60d45329f583514cb775194532afd91514cabc6454532bed81514caf86054532dd544514ca7e64145329f590514ca7e60145329f580514ca7e64d41329f593504ca7e61d41329f587504cb7b5094132afd91504cabc6454132bdd85504caf46154132de540504ca7e64141329f590504ca7e61141329f584504ca7e63d5032d798f540ca7e62d5032db98b540ca7e61d50329f587540ca7e60d50329f583540ca7d6595032cfd52540ca7e61950329f586540ca7e60950329f582540ca3d6595032cf98e540cb3c6395032cf98a540cb3c6295032cfd86540cb3e6195032cf586540cb3c6195032cfd82540cb3e6095032cf582540cb3c6095032cfd91540ca7f61550329f185540ca7f60550329f181540cb3f6555032cf98d540cb3c6355032cf989540cb3c6255032cf0c9540cb3f6155032cf985540cb3d6155032cf185540cb3f6055032cf981540cb3d6055032cf181540cabe6415032cf550540ca7e6415032cf990540ca3e64150329f98c540cb5e63150329798c540ca7e6215032db988540ca6e62150329f984540ca7d61150329f980540ca7d60150329f992530ca7d6494c329f597430cb3e54d0c32cf553430ca7f6590c329f596430cb3e5490c32cf552430cb5e5390c32bb98a430caed6290c329fd95430cb3e5450c32cf551430cb5e5350c329fd94430ca7d6510c32cf950430cb3d5410c32e750c430caee6210c32bb588430ca7e64948329f592520ca7d65d0832cf953420cb3d54d08329fd96420ca7d6590832cf952420c
  | 27 => 0x329f58654cca7e60953329f58254ccb3f64553329fd8554cca7c61553329fd8154cca7c6055332cf55054ccb3e6415332d798c54ccb6d62153329f98454cca7d61153329f98054cca7d6015332cfd5343ccb3c54d0f32cf95243ccb3d5490f32bb98a43ccaed6290f32d759643ccb5e5490f32e795243ccb9d5490f32d715243ccade6290f32f398a43ccbcd6290f32cfd5143ccb3c5450f32b7d9543ccb5f6550f32e7d9143ccb9f5450f32d795143ccb5c5450f32e715143ccb1c5450f32b718943ccb3e5410f32cf55043ccb9d4310f32bb98843ccaed6210f32cf95342ccb3d54d0b32b798f42ccadd63d0b32e750f42ccb3e5450b32cf55142ccadf6350b32b718d42ccb9d4350b32b798c42ccadd6310b32eb50842ccb7751947329f99251cca7d64947329f98251cca7d60947329fd9151cca7c64547329fd8151cca7c6054732dd54451ccb7b50943329f99250cca7d64943329f98650cca7d61943329fd9150cca7c64543329fd8550cca7c6154332de54050ccb5d63d5232db98b548ca7e61d52329f587548ca7e60d52329f583548cb3f5495232db98a548ca7e61952329f586548ca7e60952329f582548cb3f64552329fd85548ca7c61552329fd81548ca7c6055232cf550548cb3e6415232d758c548cb6e62152329f984548ca7d61152329f980548ca7d6015232cf953438cb3d54d0e32bb98b438caed62d0e32cf951438cb3d5450e32bbd89438caec6250e32e750c438caed6210e32cfd53428cb3c54d0a32cf952428cb3d5490a32b798e428cadd6390a32bb596428cb6d6590a32db952428cbae5490a32eb552428cb6c5490a32bb98e428cbce6390a32f358e428cb3f5450a32cf151428caef6550a32dbd95428cbaf6450a32ebd51428cb6e5450a32db151428cbac5450a32cb151428caec6350a32ebd0d428cbad4350a32cf950428cb3d5410a32b798c428cadd6310a32eb508428cadd65cca32d7597328cb5f54cca32d7553328caed65cca32db597328caef64cca32bb593328cb7751946329f992518ca7d64946329f982518ca7d60946329fd91518ca7c64546329fd81518ca7c6054632dd544518cb7b50942329f992508ca7d64942329f986508ca7d61942329fd91508ca7c64542329fd85508ca7c6154232de540508ca7e61d51329f587544ca7e60d51329f583544cb3f54951329f992544ca7d6395132d758e544ca7d6295132db58a544ca7e61951329f586544ca7e60951329f582544caf76155132bd185544cafb6055132be181544cb3f64551329fd8d544cb5f63551329fd89544cb6f62551329fd85544cb7761551329dd85544ca7c6155132dd185544ca7461551329fd81544cb7b60551329ed81544ca7c6055132de181544ca7860551329f994544cb3d5415132cf990544cb5d6315132db588544ca7e6
  | 28 => 0x58f4250baf43d0942eb50f4250abd6390942ebd4a4250a7e63d45429f58f5150a7e60d45429f5835150b775194542b7d8d5150adc6354542bed815150af86054542dd5445150a7e63145429f58c5150a7e60145429f5805150a7e63d41429f58f5050a7e61d41429f5875050b7b5094142b7d8d5050adc6354142bdd855050af46154142de5405050a7e63141429f58c5050a7e61141429f5845050b5f5394c429f9865310a7d6194c429f9825310a7d6094c42d71925310b5e6294c42d718a5310b5f6194c42d79865310b5d6194c42d71865310b5f6094c42d79825310b5d6094c42d71825310a7f6154c429f1855310a7f6054c429f1815310b5f6554c42d79915310b5e6254c42d71895310b5c4254c42d7d855310b5e6154c42d75855310b5c6154c42d7d815310b5e6054c42d75815310b5c6054c42b798c5310b5d5314c42cf9534310b5e53d0c42d754f4310aee62d0c42bb58b4310a7d6590c42d754e4310a7f6550c42cf9514310b5e5350c42d794c4310b5d5310c42e750c4310aee6210c42bb5884310b5e53d0842d754f4210b9e53d0842cf54f4210b9d53d0842c754f4210abd6490842cf9524210b5e5390842d754e4210aed6490842ab5924210b6e5490842eb9524210bce5390842db54e4210bcd5390842d354e4210a7f6550842d794d4210b5d5350842afd954210b3f65508428fd954210b9e5350842cf54d4210b9d5350842c754d4210abf6250842cf9494210aef6550842dbd954210a6f6550842bbd914210baf6450842db9514210bae5450842f394d4210b6d5350842f354d4210b4d5350842ebd0d4210bae4350842eb50d4210bac4350842ebd954210aaf6550842cbd954210baf6350842eb98d4210bad6350842eb18d4210baf5350842eb94d4210b8e5350842eb54d4210b2d5350842e354d4210b0d5350842eb14d4210baf6150842eb9854210bad6150842eb1854210baf6050842eb9814210bad6050842eb1814210ade63d4442b758f5110b5e53d4442d754f5110bad42d4442d794e5110b5d5394442eb50a5110b7751944429f98e5110a7d63944429f9825110a7d6094442d794d5110b5d5354442eb5095110a7f63544429f18d5110a7f60544429f1815110ade6314442b758c5110b5e5314442d754c5110bad4214442dd5445110afa6014442be5805110ade63d4042b758f5010b5e53d4042d754f5010bad42d4042d794e5010b5d5394042eb50a5010b7b50940429f98e5010a7d63940429f9865010a7d6194042d794d5010b5d5354042eb5095010a7f63540429f18d5010a7f61540429f1855010ade6314042b758c5010b5e5314042d754c5010bad4214042bd9845010af56114042de5405010b5e63d5332db58b54cca7e61d53329f58754cca7e60d53329f58354ccb3f5495332d798e54cca7e61953
  | 29 => 0x210f6d4354843cb50d5210f4d4354843c350d5210f6c4354843dbd855210f6e6154843db5855210f6c6154843dbd815210f6e6054843db5815210f6c6054843e750c5210eee6214843db5485210f9d43d4443bb98b5110eed62d4443db94b5110f6d52d4443e750e5110f6e5294443db54a5110f7751944439f98a5110e7d62944439f9825110e7d6094443e750d5110f6e5254443db5495110e7f62544439f1895110e7f60544439f1815110f9d4314443bb9885110eed6214443db9485110f6d5214443dd5445110efa6014443be5805110f9d43d4043bb98b5010eed62d4043db94b5010f6d52d4043e750e5010f6e5294043db54a5010f7b50940439f98a5010e7d62940439f9865010e7d6194043e750d5010f6e5254043db5495010e7f62540439f1895010e7f61540439f1855010f9d4314043bb9885010eed6214043db9485010f6d5214043bd9845010ef56114043de5405010f5f5394f429f98653d0a7d6194f429f98253d0a7d6094f429fd8553d0a7c6154f429fd8153d0a7c6054f42d754c53d0b5e53d0f42d754f43d0aee62d0f42bb58b43d0b3e53d0f42e794f43d0b9d53d0f42af98b43d0bae62d0f42eb58b43d0abf6550f42cfd9543d0b9f6350f42e7d4d43d0b3e5350f42e714d43d0abc6250f42d794c43d0b5d5310f42e750c43d0aee6210f42bb58843d0b7751947429f98e51d0a7d63947429f98251d0a7d60947429fd8d51d0a7c63547429fd8151d0a7c6054742dd54451d0b7b50943429f98e50d0a7d63943429f98650d0a7d61943429fd8d50d0a7c63543429fd8550d0a7c6154342de54050d0b5f5394e42db98a5390a7e6194e429f5865390a7e6094e429f5825390a7f6154e429f1855390a7f6054e429f1815390b5d5314e42d794e4390b5d5390e42bb98a4390aed6290e42d794d4390b5d5350e42bbd894390aec6250e42e750c4390aed6210e42af5974290b3d65d0a42cf54f4290aed65d0a42db5974290aed63d0a42ddd465190a7e63946429f58e5190a7e60946429f5825190a7f63546429f18d5190a7f60546429f1815190b755114642ded425090a7e63942429f58e5090a7e61942429f5865090a7f63542429f18d5090a7f61542429f1855090b7950142429f9875350a7d61d4d429f9835350a7d60d4d42d7d4e5350af76154d42bd1855350afb6054d42be1815350b5d5314d42db5885350a7e6114d429f5845350a7e6014d429f5805350a7e65d0d42af9974350b3e65d0d42cf14f4350baf62d0d42af98b4350bac62d0d42af5924350b5f5390d42d714e4350aee6290d42bb58a4350b5f5350d42d714d4350aef6250d42bb1894350b9f6350d42e7d4d4350b3c5350d42e714d4350b1c5350d42ebd894350abc6250d42eb1894350aac6250d429f9944350abe6410d42e750c4350aee6210d42bb
  | 30 => 0x100000020000001000c0000004000000000000000000000001001000000000010000003000800600080040014000001400000080010000001001c003002800700000000004004001000c000800300000000000003000000000000040010001000c000000c00300000000010002000b6f5294b439f98652d0e7d6194b439f98252d0e7d6094b439fd8552d0e7c6154b439fd8152d0e7c6054b43db54852d0f7751947439f98a51d0e7d62947439f98251d0e7d60947439fd8951d0e7c62547439fd8151d0e7c6054743dd54451d0f7b50943439f98a50d0e7d62943439f98650d0e7d61943439fd8950d0e7c62543439fd8550d0e7c6154343de54050d0ebd65d0e43cf5974390edd65d0e43d75974390edd62d0e43dbd4a5290e7e6194a439f5865290e7e6094a439f5825290f3f4354a439fd855290e7c6154a439fd815290e7c6054a43db5485290f7751946439f98a5190e7d62946439f9825190e7d60946439fd895190e7c62546439fd815190e7c6054643dd5445190f7b50942439f98a5090e7d62942439f9865090e7d61942439fd895090e7c62542439fd855090e7c6154243de5405090edd62d0d43e7d4e4350ebd6290d439f9875250e7d61d49439f9835250e7d60d4943dbd4a5250ef76154943bd1855250efb6054943be1815250f6d52149439f9845250e7d61149439f9805250e7d60149439f98b5150e7d62d45439f9835150e7d60d4543ddd465150eef6254543bb1895150efb6054543be1815150f7551145439f9885150e7d62145439f9805150e7d60145439f98b5050e7d62d41439f9875050e7d61d4143ded425050eef6254143bb1895050ef76154143bd1855050f7950141439f9885050e7d62141439f9845050e7d6114143af5924310f3e5490c43b75924310e9d6490c43d79524310f9e5490c439fd954310ebf6550c43cfd954310e3f6550c43afd8d4310f3e5350c43b7d954310f5f6550c4397d954310edf6450c43e7d914310f5e5450c43e79514310f9f6550c43a7d954310f1f6550c43e7d894310f9e6250c43e75894310f9c6250c43e7d854310f9e6150c43e75854310f9c6150c43e7d814310f9e6050c43e75814310f9c6050c43e750f5210f9d4394843dbd4a5210e7e61948439f5865210e7e60948439f5825210faf4394843f390e5210fad4394843f350e5210f8d4394843db1925210f6c6394843dbd0e5210f6e4394843db50e5210f6f6194843db9865210f6d6194843db1865210f6f6094843db9825210f6d6094843db1825210f9d4354843cfd0d5210f5e4354843cf50d5210f5d4354843c750d5210e7f61548439f1855210e7f60548439f1815210f6f6554843ebd0d5210fce4354843eb50d5210fcd4354843e350d5210f6e6454843db98d5210f6f4354843cbd0d5210f6e4354843d390d5
  | 31 => 0x30000000003c003000000000000000004000000000000040000018000001400200040000000004002c004001000000040060038000000000100200000014008000000300080000058001000c0090000000000c0060008000000c006000c0000028004003000200000000000000000c0060008000000400300100010000000000000000400100008000000400300140070004000002000200040020008002000000800140000000007000000000040020000003000000f000c000000000100000020000000002c00000040000000001000400a0000005002c003001c0040068004001400e00000050004004000c0000014000001c00000000010000002001400200000000000000000000000080020004004000c0020004002000c0000004002000000b00000000000003000400100000010004007000000400080000008004000800000000060034007004c00000000090004000000000100200000000000000000200040020010000000c000005400100100030050000000c0080004010000c00500040000064000000400200000000000001000000100100030000000000c00600200080008000000000000240030000004000c00b0000001000400200000040008003000000700040000000008001c000000400100240030000000001400800000000000001000c00800000010004001000800100140000000003000000900080070004003000800500040000000004000000200140010008001001000000100020000002000c000000800100140060008002001800100000000000002000400000100000008000001c005000c003000000100040010000001000400b001c0010018000000000a000400b0018003000800000180000004003000400600040040004000000c00000040000004004000000d0014003000000100080000020000000c00d0000006000000500000020070003001c003000001600000000004000000c00000040010004002000000100000010000004000000100200010000004002000c00180000004002000000300000070010000000000d0008004000000000000000000004000000f0000002000800100080000008000000400100000010000000000000100040010014002002800100140000004000000800300000030000000000800000140000018007000400300000030004000001000100000000000000000000000000050008000001c00000000000000000000000400000000000000000000000040020000000000000000080010004003000000100000050008001000800500000060004000000400800000020004003000400100000010004000000400000000000010001001c0010000000000000000000010000002000000000040070000005000c00000100100004000000800300040000004000000c000
  | 32 => 0x100000050000001000000100080010004005000c0000004002000000000000000014000001c0020004001001400100100020004005000400100380000008006001c0080010001001c000000c0000000003000c00000000020000000000c00000200010000002000000000000010000008000c002001800200000000004001001800600080040008002000400000000070000001000000100000000044001000800900080010010003000000200180000004000000000100000000000001000c000000c0000000000000c0000014004000c0010004002000000c000400200000020004001001400200040030028004001000000100000004001000c000000000100000000000005000800000000010004001000800100000000004009000c00000000040000000000000300000000000000000400000080000000002000400000080030000001000000200040020000000000c00100000030000003000c014000000200080070004006000c00700000000008002000000700700000000001000000000140000018000000400000000050000002002000100100020000000000000000040000008001000000b00000000000007000c00a0004004000c00100080070014001001800400140010008002000400000180000000006000c000002000000000010008001001000a0024008000c00c001800000000040000001000c003000c001000000000000000010010000400000000000008006000400200000010008000001000000180000000000000400000000000000003002000100000050008008000400500140060000003000400c00180020004000000000300100000004002000000000080030000003000800500280000008001000000a000400000040000004001000000000140000008000000000000080000020001000000000000020028000001c00200340000008002001000000040010014002000000000000000000000001400000140000018000001800400000080000000000c0000000001000000300040000008002001000600140000000000000400700000000000002000c00100100020024001001000f000000000040000010000000c0000000000000400300040000000000000800300000000008000000000200000010004000000800200000000000001000c0000000000001c00300080000000000000000800080100010001001000d0000004009c005000000500080000008000001c007000000300000000004000000000b000000100480040000000000000000040060004014000000000040060000006001000000080020008003001800300100020000000005000d0004000000000200000000008002000000000000050000009000c0000008010000400200100000018004003c007001c004001c00200000030054001000
  | 33 => 0x30000000c0010000003001400000100040000002000000100000030000004000400000000000000000000800300080000004008002c003000c00000040000004007000000000040000000001000000100000010014000000c00700140030000001000400100000070050002000000100040000000001000c00000080010000000000000200140000000003000000500040030000000000000000000070018001002400300080010004000000000400040020000000002c0000004000000800e00000070020000000400000000000004001000c00500080000008007000c005000000000180000054000000c0020000002000000000240020000002000c000001000a000400000000040010001000000a000000000000000004000000000a0004000000000600100000010004000c0010000000000000200100000000008004c000000000000040000000002000000000080010014003000000300100020004001000c00000040000000000000000600000000010003000000200040000000000000001d0004008000c00000000020000002000c0050004000001800000580010000002000400a000400100140030010004000000000080000024000000000400080010004000001c00000080150004004000c00000080000000003000000100080020004005000400b0058008001000800100000000002000000000040030008003002400000000000014000000c00000000000004005000000000040000014001000400c00000020000006000400c0000002000c0000000002000000000000020010006000c0020004002000000100000090008000000400b00080020020001000000100140030014001000000b000400200000010000002000c000003400000000000010001000000000000030000001000000100200010000001000000000040000000002000c000002000300040000000005001800000140050014001000c0100004001000400200040060024003002800300100000004000000800000000040000002000800100000010000004000400b00000000000004000400a0008002000000200040030000007000000400280060000000000400000000030008001000c00100040010034003000000200000020000000000000000040000004005000000a0018002000400800100010000001000c0050000001000c0010018001001000000040020000000000400800000020028009000000100040000004002000400100040000004001000c000000c00000040010000004002401000080060000003000000000180000004004000c0000008001000800000000000000000000c002000c0070000002000800100080000000001000400100000010014001000000000040030014000003400100000010000002000000500040000000002002000
  | 34 => 0x4ca0c9b94000164832995a47030000000259651f00000000000000000028e8000000000000000006c400000000038995919e000100e52caddc2608000b9b000092b84c06be16641ef1a9200032e40000000000000061faf72462910e000000020580000000000a8700004611a4e3f780004bd9f3028298703fb0000bb6116a0002abc75c0d7409700009b90000a518cd22afae227f899c83000b267c52b7400018109ea0000270135051680007bd000000004401a820b0969b0ca02793225c80000284800000018e0b16000000025c6577800000000001f70c6a000000000000002d319fe00000000000f080000000192aac41e12562a7380005f981602c31b1c67013520001560a650000000000000000006c580000000f8400000005d00000000278400026babb88000000103ec61269e0001e806332e0c9b8800068a00000a01e04be98c2a00100000004000000000100000000008000000000000040010000002000400100000020000008000c00300080000000000000000100100000000002000000000040000010000000400100140000004000001000200600030000000002c00000000060004005000000c001400000000000020012000000d0000000001c00b000000100040000000000000c000000000600000000000003000c0020008000003800000000030004000002400400080000018000001000500040020010000000400000200000004000000c0010010001000400100380090004009000000e00140000000002000800300040020008003001000100040080024000000000600240020008003000400e0004000000400300040120004002000c00000000000008003001c001000000000000000008006000000e0008003004c0000004000000c0010008000000000200080030018007000000a0004000002c002000c0000004000000800100000020020001001c00800000000008000000000000000000000001000801500040010008005000800000000080028000000800000040080000000000000000000010010002000c000001000400200000000006000000100000020000006000400100040010000001000c000000000000100000004002000000200000010008004000400100000040000000000000100000010000006001401e0024006000400300080000000000000000500000080048000000000000000020000000001c000000000000040000008005000c00100080000000001000400000340020010000000c0040008000000000a0000000001000000000020000000001c00100000000000005001c001001c000001000200000000008002001800100040000008000002400000000020000001000400600000010000001001400000000030004001000000b00080010000006000400000080030000001000001600
  | 35 => 0x798b5c000062800008da33b000083700000000000cb1a91a00015bc21b831e3de80006251e12000000000000008f3827600025b273c9890aefa26c0000be000018380002718000000092285e000019f00001c0260e89300002fde1cc00000002a1237e811056c00000000000ca8000000680004e832520000000000000012f000000000001340000a579b6cbfd00008baafcc0000000c4b8000000123000000002ed835c0000000a34005a000000002b036e7daa8e4b879ee40002a868de800000000000928000ba49cc200003e40000d6482fa5181d727fc0000000000340400000000000000814ad9049b0b0a00000005c60000000000000027ae000000050dafc25b9a63a34204ec9bc0000000000000000005078000bbb066000011ee0002bd65ff80000001a0c000000000006dc25490ae0000b6c4808dd0ce41dd0cf080000000000000000000000007e3b24039104880001ba05c0000000011c400000000000000000000053f000000007120000fd6ae1105a7a4198e15b329263e0000000132e468080069b95584cda2a0b4f27ba7070000000000050c8000b5992d000000000002544000050080ab33400017d600033d600022f47861d5ab0700002c8800000000000000000000000000000009488000abf1274000270239d95944af054880f00004a7125636bb13a00007d468d0ca21d680002e600006d6000000000000000000000021c5f782d85e000000000000194a72273380f60000000000303c394000000026fa0001ec679e2812000000005f01c4000000000017bc0000f1a7a6982c00031cc00006fc98531066e18bee00000000dd00000fa000000000006e000000003136000289a0002d1a000012a60881268bd88967ee220603500000000000383235acbca198bbf87f4767af4c00000000000bd2000000000024ca5d1224421c12ca39c20b6b18000040e0000000118c00001c2289a4f600000008fcac700d680009af87e0399800000000000000e8a788000000000000000000780027a0002b1400028a20002fe65a8000000008ba0002ace0ca01b2000000000010a6406907c0000000444000000000003e800000001dec000000032b8000000278a8db8a060cb244871018be63406780ce95567fe15f8000310e000000000000000000000000000086e00000000dac140b18c00028640000c3a0650bbc0000d440000e4e0000000000000000000000000000cf2aa748d703e68ac800041f80000000000000000074e1612b6e06de05dab060b780004689a561560000916ab3ab0b2ea4150028caa7000000000004a4aa4c000151091f054c0000f98000292a000000000000001c7aa7215c33be000082c8318b3e7a7028ec33877a0000000ac81258000000041328f60000000a128df4862209a00016c2c3780006e927d039311
  | 36 => 0x8412bde00000009360d2410a00000000000000206e000090e1de174a0000be80000000424800000016307b98d300000000a570b60000000000000000000bfe0f100000002338000079c61280001da1a52000227c00000000000000c2c8b660000c8226780002e500b4bbb9c326bd0000000156e00000002208000c870000000000055080005b600009251f5814b000087080008171a460000000722800077185a49170e6cb3d000083b00007e08000000110aa7d83ea0000928626000057e94e4000000071f800090a00000000f520000000000000035cad6e0000000772ad48782320600002ae0e89996920a498000300200028cc2251d501d0a6c200000000000000af922308fe156a08216fa4dd0000b690000a9f00000000a64000000000000000001bee33f31940000000a030000000212e0002f54000000000000000000000b740000bad8a3ec31ad1043d00000001770a8c8b5800003c200000000eb0000cf0000029b257000000000000822448000000000001a5882a00000000001b300000aa60000e14bc4000000000000000ce099b064c0002f7a0de9eaa1b49cb8aed800031b00002a10000978261e00000000002c9e0d8800000000000001dd600027fe00000009b69f90c1193d213fb30895a00001fc8000a639f5600013b631a25ce54527380002ce8cd600008192d940000000c6d000000012dc0000fc000027ec5e700aaa45a32a84fb3e0000155c4ac82ee4d624a000000000000000398a0d80002ba00000000000000000023e66c8af404952fee59e0b867458000557aaee0000000c4e1cfe896800000000008eb8000000000000020940002dacc26296248d1fec00022c48a600009f70000000237200000000530b3800000005d42af28d194e000007e2000246200380000000000000281a86990b6be0a218000000046f000003b0dbe00032ca000000073e2a880000d1ac24b33abc8800000000000d900000b4800000032480ce0242000000000000001e68344c96b2a80001e7200000c449d8000bf2165c77d00000002f62757b3f0ced8000af11a50afb91e00001d7a000000016a80000000bf065280001cd00004fb000000000000001fee2e015e4000213400017a200018e2a2729708340138bca000017d11184e20000000000085f800000029e01b6aea26762344a5ba06058c819668fb1224eaadca0000000c8900006dc80000000000af6326e0000000000000000013c83b7a84c07f80009b10000000000061880000001b1804a00aeacc0e480000fd4928989eaad800c7bb00004ba80000000000459ad468f480249b1800000000000002138a8e0000240b3fa42280000000000bc223f0cc6224a0000e28598800070000000002aba2ee0000000060200033640000000afa29f8585a4b2ad8000000031fa00000008
  | 37 => 0x3be9e0202600000002bbc2751c460000b040002378000000000000003ae8000000000000004be000000000022d800000000000000ba685a620a29b45e6b1ac51524ac1ff9040000172e0000000b660000387a8884a8000024780004a38000704849a000000072b0000000000000000000000000000165e000000022aa8940000bc000030f21f20f320002f860000c565d9187c0000000000000000028ba6f6a91c000068c000000000011325d184201dd2b70000000000000004d3a3a407987d000022da0000000678000000020d2a16000000029600002abe00002a63b68000000336e8632c325e100000002414000000000000000000000000121c00000000000ebe8560000c532460000115aa17b3284f800001140810571000000028c80001d54000000000031a86810000bfd9f2c000000000000000000000000000000000000001de000005a07b800000001c200000000000000000026ce0001f4a017aa4294d80002d58000cdf89dc31f258047380c600021a8a1eb16a5e18000ad00000000000000000009cc0e4a00016c0b190aca00000000002caec510cc4000115c1eb22880000000a3680001789c0acab82780000000bf11b6ab6e8000afb016e02580000000000000000026290160c88000c42000063280003e9000000000000a880000001d7e9e0800026a80b0000209806180000001864000000000024c00002668000279a12a00000002f9890d0b3237e234e56a25ca00015200001f240000000000000011391920000d8c0000a72a7500000000000000030271d03a00001fc400017669d52ca8a8920de000000000000000002e266402b58609a42e69e903000027b29ac08886a7800000000001039c680000000b5800000000000000000032f00000001f5484c0000000000000000000891884431162e025000055a000000000000001eb87450000000000000022ac0f01eb4000027c0001704252176a454800000000009550000b5e800032100005522c9200019926f480005bf8000555204400014f00000000000091600000009b4800034700000000000000000000029520000000b5f1df000000003f300000001ab62e98eb46baa88c0000de60000000b3d800050e1d9853203cebcca904000075e3fb80005c980003d700000ff11de6030000c6c000050400460001af22d180000000000c1e800000030080001d6c8cb8000425000006e2ada00000005d08000bd68a909d60000abd2d6200003ccc01000090400003ee80005bb800000000000002dd400001562370000a1e1bd8bf4000086b00007ac89e08f20000b6f00000000000b94a0304c28b8e000000050b00003e681909b724680e92ae800000000000000000000001bb384723280e09d06e20ba0f5027118bc0001ed600021720002f0600019a0000025800025f82300
  | 38 => 0xa7a600005ee93f9c548e3072c5cc80000000000000129a00004ca24e800000018b00003074000115484e800051c24e42f101f2cc125ee00000000000ef846e9620bc2b1f40b100007d0ad321858000099870e667032618306e400019389fb800028c000091d0000a6c00001438c46cc380007ed00004041b845d2208c00000000792dd800000000001f1ab9d8000510000000000000000744b70a39277228009a99bcaad18000ca11b9ca592db4bb2163448a2e0e00024ba0000000706000097216f80000000000065c2e800006910000340822aae983084170e2c1f115747e30000b529e2800024eeb2380000000000000000018d800000032b4482a8b60002a4412128568f80000000000000000000000b340000000a6285da341ae9000023e43f80000000282c016072a000000000017b4c8f0000bae00005120e980bf21ea00000001cc8000000000000000008d0824000000000000000715829a173a39c79e8b8822800005e48998000000000000000000000000000044680003d10000498a860000102c000000000000006b722fe00013727772e82000023e0001b3400000000000000000000000032a63712fe2a88000042026ee0002d700000000000000028a00008c580007ea0ec004dafd6bb4a02200000000002e580000bca3da00003810000000065aa0d00004f600000000000c742b9c062128a46a800000000006e380004ef80005df1cd2000000098988de0001e14c9a8000000231200004820001a2e0e9800008d0000000000000018e40000000000000000000000001cd67428000993800033400000af8ef29158eaeafeaaf0ac2a5dec4b0000000000086d8232c3123d0aa313084b80d8e8a482ca00010980002078707800047da93800032860002c960001f6c00000000001c780000000000000000000000f1800000008f000000005e3000055f240c3dc2d1e9611f72acd9be421b2d1861ca072a7f2e1aa66922a36200007cd20689ca823abb2ac4600000000002c8651e9b3600000000000000007800000000000000000c3f80002a21fa042f10c21bc9ac20001640840800050491d00001e9e08e31ee00005420dc8b2eb7c00008c200005db0db03fa0000000000000000003fc800008280008060000395001c71c887698600000001de60d500003dab32ec0dafd465e9ed293824405b1adb660812d813800000001fa49aa8c1a37a0000bb58bb21120000908317a00000006bb1e5000030be000044c00002a400025920001e6a4e406c600020d60000000000000000000006ee800076200000002a56bb687cc5c0ad161e7805caae2d1225f00000001b7e0001ba2b49985ab7f800078a8000546800031400009b32cd21a4000013c80008ef02488b4278800013440000000000000000008a40002ed4000290a51d00000000000
  | 39 => 0xd4a0627d380006ef0000bad206600003f64d31b4455fb09400000006a70d48bd98410673906e70c216207e000098c276e000000000000002632a5e14a15ba32e085800022ec000279e00000006bc0a4200024040f40a5c35880000001bae00000000001b7600025481c4000036d8000000000000019720000000a5a800000000000778da0adb000028000000000000b370cb248883860001880428800005412160000000bd780005a50000000222a00008acbdd000000000007128000628272e4a000002e699b600000005f0800059800001918000c2a183000016dc00017080002076823a9be74a2aec000211676b0000000000000000008bb80000000000bab0000bec00bc68e8d0499c8000ca380a400000000000000bf9207c67d0f349bd800000000004f7000074793ac0000000000000000012c2c842bb200019429991f46000123eacf0a8e17b00000001cca5ba0000763852644e8000000000000008f618e0a403690000babab8c5dfadfc0001cf63e980007778000712334474088d00000000000216600031a0000304cafab03e0000000a05b22a0000e1a4651d8000000004c30000000027e0000000000000000000003c3a7749d0250423186b0000000059d8000000000000000000000000466073600002842f8800000000000000ab400000000002c8a0001060000000000021d089ca5503968000b4e0aac6fd800000009b8a36000066b00000001eea3c1239407a0000000022c0001bfc696258a00011d6bfe800000000000000000c6e2e5000000000000000c1b0000000000000000000000000000322883300000000000addaf3000000003f180000002ab25f013c000005d84e12fe869d0000855934a412a8b2000006a2abaea600006d451d91f8000000000033460001c04af080c099600000002048cbeb09c4c08000000021685ea674000000000000008131a7885b8000cc99d9ca6109d6beb9abe501800051780000000d32000223c6c78000000197e000000000007da0002f849678ee0000000017c000000000000000dc6a35b05e0ca8a9c00019ec22f927e8f72a5a23880007c890140000000989000000012c05e980008be000033a050c2a180005732e8e29832e88a6a7be503800068c9a62b850000884974e19080000000116b8d00000002ee474bac5ab3232689492f768ba1b08575015400019e415e00000001e6888ca77600030a05c700621239a0e1050452c4c000012000000002fec000036a0000556000302c7610000bf6000057d00008b480006b300004049db6a8f80be000000000000000000000a37800000000009268000000000000000000000000000000000000002ba8a20a8080006cc80009ab90d4000000056b80000000c38978800000000000000000000000000005dc00000000001b560002a82bc3
  | 40 => 0x90a96687152a000000000009d0000049600009b60000c6e000000000000006f000000000e36693237650a04a0c4303fe0000c7e4690000a63216432b000000000000002b90000000000000003c4800039a1c62107063c0003066a5086bccb82ca01f98000ce20000366000000031ce000000051f8f94befb3a42d2a0200000000000000000000007e6008c531000000000000002002570a8e010180008042ccacc180000000000000092406a2fca38f86867ec834800005340000000ae9283600000000000000000000061a01da4980cd45ab8000907158465c10f0795254c214000083c800003098140000000000000000026bc000069a8810f9e5420000cb20514000000000014221d89f32000282430b8854c1b80008c0a3aaa2b8000751a8208a58000000000066e0f181252a9a00032d200023fc0ed800017ca1ec0000d3c00000000000e940000000882000058a8000a12000000000000000000586000000000000fd000000000005a78384000000000012e60000c8e296041a00026760001328a4fadf60000000000145200002940000000000212c00000006b900000001ffa38f000000004a471b9652181899a69a196a00027160001ad60002d9e7e7246600010b21748808000260800000000001c863081ab42a29fa20000000224999a20609129b025d024d0000000165600000004d70f90b0f800000004d20000000c6900000d81b8a0be0000522b34200022ba73521a00000000b1f8ae2ce6b1f00001f861028ee400020a8233821400020e60a400085438000000000000024e20002e4ea8322cea70800000000004f6800000005de0000a5a000000000001d400000000001f7c1cb925c09180000000000bb984eead514b600000003ba800000013e6572274a853277a000000083a8ace1ee11a8b8e1e4619d2daa35480000cd8000c5c00009902db0091000073a0000899052400010960001bf8000267a0702f1e0001f02000000089e80000000000c75000006104a20002e7a000000016e00003b110040001fdeb4a0000925800000000000fe1b2600000000002e160001706397800000006d000007fa00012d600000000000000785800000000004c00000257000019780005470be400000000003242000000011a803a0000000000000000010f248484080001e3a0000000c382d3e382a2d4000000079b848642c0000b1409a60000000aad11807302b7cbd1000000000000000000000099000030f800002f00000000a73000026fa0060001c8e55c021081b0000c5d0000b2e85f80001cc800025be00031c622e10646fea9767f22696ceb2402618000000019f898029a0b3e800045b0000000103c000171e878aecc0000000000080e00014b400013203120aba90980000002d3a9a305fe40a2e4c00000008b586e8000000000030c
  | 41 => 0x69f1832659aae29948000c78ab5a00004a62bc094a00033b87dd800034417be00002e4561ab88000008a09a8c1ea9922360002a34716000095e8c321ca0000000000000023f400027244f2adb20000ff0000000000000000000000154152ecea992c6f50000000045838580000001b0c0002e5ebeb0000cbc0000000293c000040c00000003c0000000016ca91da6d4b648d3eccf800000000000000000000177866a917a0000000000000000000002310a808ad0ab8000033ccae977400000006d69b886950000000000000000000000000ccd8000000000000000006270a2e0001e40a9404c42842b440000000000000000000004ec0000000000000022e20de00000000b8400032220000000b0e0000000000095780000000bd8b0031c0acca2dc00000000000000000000000013b4000157827f810600020163198000a3089ce6c10cb400025a000003fa000015e92c000093480000001c36a2a0000c9627260000000a3a02da9733264000000000003ee0000000c3c0eca000229ec75b340000012400025ec782800000000000000000b1480009790000ab600000002ad43db8000000000000006ba4e58000000000000000000000000b2a8000000000000000006c396a4000000000000006f7800000000007cb963e0000000000000000000000000000000164a73900000000000c5c9cfa0000bba05080000001024cf4866c00000006a6810000019fc27a142662e09a20000000000000047994ce000185c6f080000000b6e239000091c800098404348240d2ccfd800000000009f7800000021903f40000523000051583348a080000000aa87ce0d687d88000b3e0000bc924b677e0000000000000015ee4a9800005688844e6026c00016288bc1a849d41a7612484560000ed218bb07200014aaca923c4684852ab34000000000002aa8000baf0000000000000000004ab80000001ae20001f70000000000000008f0938c0000ad800013a4a4804180001ec8ab98bf2c9407a035586aa28900000001598000000000000007ba0dc80001e600000000a82a0ca000000088b1a42c3431560b8000074000006aa0d3a00015ac9c181c600000009ba321600024120002ee0015800000000003b3a8847f8000002697961afa8ca7841fd28fda9d0cbf800000031fca660000000000000000009e42aa422182f4a5b20bc3b58000bd38000000000018fa4440002b48886b2820000b0e77516700002a1e5362e5a66f0cee046afb26d2287c000253e00006880002910aaa209c760a9de000000000000004a317fcb841d48b3a8624b91afb49320000a07335eabeae944df1288000307c000234c00000000000000000000094b80009adb3fc3f998482a800005f1312605cb352c3b28fe10c80006f11da6558a8f24021fd4b42314284f2cc248329e684
  | 42 => 0x1e1e99114f4000000000000d20000b1c000328c00001ce18023da00008b6013032400021001d400006220b5e8c695304db800089a9526000153600009380001c5acef2cbe000304a45b93ae2ea80003df1d6000020040000000000000000005c20000000000000000000001fb80009c0000000000004a90a66520800000014be2a7a92875600007e007c6000000092721703e00000ba82ca42b9a2e4000232c00022a83ec07a60000000c0800001d5000000002d4c0e80000003244375b0ee00000009482b0e72a889e000000011680000000000000000000000003bf0f1e34d0a74000000000000000000c94000000000000007ec000000000000c1941c6232a780000000000000000000005ab000000015fe0000000b3f8000000107000009c23ed31c44a180000000f8233580004c91f2600024e60001e76391acc60102cb2a4b8000cd20504000000089a00002cf00000000000759000017a00006d2800082100000000dfe7d8000000000009c68000761ac5e000294a67780000000000b36996078680000001b4e00015c0bd4098846d06c44b394960000000000000057d800000000003c9b21a6440da21538d4c12b2dea2c4111c7c780000d98000b84b132000195632f8000a050000b57ab4c4af869e0000ec600010c683828924b19182c2baff2000068e000033200000009b99c82000000000000fe00006827658e0075f0000000251a0000000000000000000000001ee20000bde7cea8769418000000000000000000000000721000000000000000000000089c130800000000009fa25aa3f12b50c0a0000000035676d283e000000000000000000944c1a00fa000077c375049800000006542d449dfa10800011c80002d5a80e11dcaf70000506105800000000000e0e0001f5e0000066641000019c1382250000029480006ac80003a19d320000000107937e198a0a2cae29f0aea09f689d8f3a0000000000000000000000000000000000064f0ff41420000a4e97a40000000890800000000007178000a2fa0f09c10000000000000000000000000ce000000000f880000000000000000024a84d0800001a2492000000080c80003609a300002a7a64800002de000000029f49b8000048205520000756234a6fc94a04ea54c95820000000b158000adea5a290e9c16c388ee804493044281392a92aff066a33226e42866c8e219c2580cfe22f29f267e8000a7a00000000000000000000000003d180000002c14b24000000000002b02c74000025ea510000000000062ea0da9818b2061480000002bc60000000000273a000226613f0584b1730244912d4c00000008ad800000004c65b100002fd00000001a26b8700000298392cb7000000000005c50000471800068e1baabf0050600016883ff80000000e72792800000018
  | 43 => 0x104881e9e7cb6288d8ab580000000000ca000000000000000000000000000000000000000000003da0d40000370800000033f86aa9c88cfaa3044f516b2137b4004aa95b80000000307000081a8d1498d8d9a39f186a0000000b0281808a01f3ca4900003949d04000000035000000e4034e49a8f7600000000002f4600000000000000c3d943e0002470ac48e9c3128000bd6004eb04a1fe0000000000000080397346742f9652b8000000059c10b089a000135e3f88000929a67c7640000000248c268000048f202e7a111be5af2fba91930580002d7e0ec800066200000c6a1807f3ac2a000322c00007b656829a46628dd80002bfe00005ac0000000000286e0000000497b04e11b800000000000002f920000000000038003aac4e7cf8622000000050100006eb0fca142940a00000001db000023506b68931b1200018fa06d0dbc6a08000000000053d80009f20f62c2c196c0002dde7280e92ae7954c76ab09a2ba20c26ee1654a6cae700bc80000000000010aa540000000000000000010a40000170000141400014ec000000000000001550000a9a0a46ce600000060a7e0000000217a40aa90220071433689001522642302a8d003180000000000033e00021600000000843087e00000000000ef6c0d1fae5a400007deabf00000000000059e000000000017f60000000647091c000000000003b0bcf8da61bd3044c6980000002a2a91a98a888380004e18000000326c13210be51c99ba33732d00000afa00027ce000331222baf425b880008e415721629ac806480000df9bf059388f28650000319063a00000002be000000000000000000000000000000003a79074000215000000220001148000094c000233ebfa8b027b79a180000f4e78c92acb438000000000416c261a000238456f8a380001dc200010ce0000d54000000000000000000000000247e00000000000668bc490526d18d84aa4b24645f80dc000257692230708828000b3c000000029c6a0780001b80a50000016ab98af64b4a9bce47f800000000003cc00000001ac47319978000000000018a6000000000000000002e28b0eab2a0002e4200023881c68ea68cd80007fd00001519c7c000000000023b400000000000000c50000000005823bd109c8b7ad14cc00000000000060901ec00000006c90840000000000000007c12aa66d88000000013c000000096d87be857228c0002c447a5000079380000000000000211c00a0000a5f00000002e8690622b89d20c3648b080a000221689c00001230000510b030cf2000000012d451a9d1816b819ab1e9fbec6680004fd16de000000000007f00000000000000000006489b60000000000000033a208c00008e080002c626de6d08dea0001046000000022400000001a5c000000000000000002a0e00010d20
  | 44 => 0x328000551331c00000001390000519ab62287acd49d5951800000000002b3e00000003f2000000000000000000b99006c00000000000c10ae89e7e4f926780001f5089811ec00004247d313fa1baabca2c200000000000a1f9c1012c2aac0002be20000000b1b0f7eb92800000000000000000cb00000554000000000000388a8c0000000448800013d8dcec36aaf6bf8053e6f7159e7a4814e5b300ee6661beab2313c2b5d9026362afd282825b445400007b418b64e00000b6b9a1674302ec0002540000101e88b85120000000000000004c3396cd6851e72f800003a0e8c4bf800049e800016d95f293e2f38000000031080006258c221a90cf43aa9b78ab00000682800000023a8000167e07b800000000005f200000001ef86578000209262000018f400000640002bf2230813a50ea36c0000000000000000016a20000de400000000003090a39800000018082b931d200000000001f002bb800000023aca14800000000006dd2556913327872e80006a9896a0000000a55800001100000000954000275c0000a1400000000002f60906990664c160027180001ab295000000005f6000092e0000b95800000000009e3953e000000096084cc0001f120ee80002d6982a825800000000005aa0000000195c00004dc0b322ae000179e332080c9440000b998000182a1d2a621f08000184e0000a6e71c22c800031c21ec80003cd8000000000010a800000000000000d6e00000000000000000222290c026859aa588668800000000000000000cc80d4e866ac7c6268000000000000021e8000000000008728b01a2400000000001d2656300000000000844944600023e2cc69364b201c2287c11305bc3086602800050220d434da4fa93f000000012fac673120692112800000000002126000000000000005a1a732000000066c25f6c5f00002b718540fc08e801e80000000000000000000000004230000000000023ea2ca5cc0000a430b3000009ba1860000451b3da39f94a26869ed8059965a64d80000000000000000000032743652a0421f06e63c1a2e01689fbc2a885200002c34c0521d400022c20000ba400000001d4a120000218283398e65ac0ab21fe200a754b2e2b682e1833a80000002300000000000000001622f8a000000000026a2a720b488ff800077000000000368000091000027986db9760b9503ae8048ba200000000000000000018e7b3a74200012460ee285a1848090b7330823ee2af84fc917234a97900000000000000010b80149471a60b9000000df2354b9fa25c000104226b323627b14ba8e78000280a764956b1522168c0a3e71ace64fae7cb7e8866586a3481fb012e01d800081600000000c9c00011e8a1c0000000000000000003e30000000000015880000000a5661e000000000000b3a31c000062cc7a0
  | 45 => 0x57c07ea0f4000219e2d8b36c0002dc00000000000000029a800079300000002b9a0000bb0000000000021c82faa07005612b86be896ecf131763e893687e98b8c00000007d028f00001fda000208a7710000a5f9c6656a80000001f2000000000000000000000084d883200019646fc800000002a000002bc40ca238b0980007c7243e8cf00000001e1c31c01a44658000a60b3820001a0000592100000000000000000000009f116c8ba00000000000044b8000a618000042b39e000000000012847b10000a2e000000021e0000000060a000000000000000000000000000000004410000000000005d000019f000000000000000000000074a00000000001626b288672cba935a0000c8a00000e4ac6030a000058c00000003cf80005220000a2f06b27a314ac12a9dfec5b00009ed00006dc000000000000001bb60000182916136c4a500007201c4c0001dee20f000013895b4ce71e2e03400000001fca000118600000000001b3a42d00000000000000323280d8000000000036d0000000000086b80000001e2418d000073400000001e709b2238e624878a984800000011fabc022b046b00000000000000114200001f43b61738000003e00014bc0000000000138e00000004a62900000000028c82960002a96000000063584f4aca2330aa821b20000000744036c6e4919010c000004380001b20a760001ffc0000b0600000009e81834273000000000009fd000067580007b514780001e8800023528c780002b123747372cd80000000a238000cce26946c188b470a0b160000000940aec40000814556acc0af980000520000a658000671ab1ac790000741946018c884643e25f2000000062d00006cf9672997308c1170da8568800072f0000a678000bed800094e99243d58000000314e7a8322e00000004dd800098f1ff256ca76c81d119c06a8f220000000000005285d18aa0000000000000000000000002d64414100200000000aeb3a68552f9a000000000012da40d0036ac9b28a000000000005c006b8000139a24e4498f389c70000b5d00009c30c62ad91a98a3e94ee37899e20808000000000000000000000000000214494200005c494980d7800000024da00021ceb1010780002f7e000000000014340ba80000002442af4942e8d883b40000bcc00024de0000000c42973ec35800000000740000000000000000004f80000000000000031632d86289c2a000000023980000000000000038200000001ec000093514fa28a80002ada33a0000000931820e0000000000311200000009a70000000000000000000002dc60002eba00008a6a8c22240000000cdd250a37b0000bc0965000018c80000000000000054a0000589210e000000084c80004ef00000000070adb8000000000039b968c2c6a8820002d6abea10ac6ce2dc8
  | 46 => 0x423945c00000000000000ab8038c0001492a18a07e223abc800005d0bbc80000002be00000000c0896ce49492687ab85cc0002e600000000000000000003120000000000000000023685478000000000000000003d930b400020820001330b012766665258c5ebb3ee00025c40ea800087900000d315e2897a1ca00019769d1029cbceb2601daaa80c76119a7330000000316800000006ff8d168bf1c4483e1d567241a705ec8000540a906000000000000000000a440000000ab49bf400000004b2002eb48801099c2fa057b294c00000000000c3e6808cce79d1ad8000286cb379b2e20d084a6e58316bb18b4278183d400000000001d4e000131c00000005b900cc93c00004371be2cde8af6ce302266969efe48688fe0f7b20ea8d8baca759ea2cc52eaacde131a51b22620001f28000319615e838ab2984e8675000000000000000000000015c00011d200000000001538000000044000000000ab000000000000b000000000000000093429ea0000000000000000000006ec0000000000082e0000000018c02e0000b1507b400021cc15da3cc2561f526a5289668195347f580009dc00005c3964c4900000218a9a67f080000cc1c9813eab6839e21d6acbb0ea0000282768000003c191e96f0efe0001a72449031c000000000000007afa698000236000000000479102492062a4a8800005e00002bb0e2ab1ba68e07aa1da000078c000000048926ac00000000002e3681410d6cd8800000031b60001db0719000000000003a80000000163875cacfc0001b9800006d800000000002f180000000000000000020e2000000000000000000000c0b8000000055e0002e020001ac00002408000000041a800057f316058f000089511da3d9a5d80002c06000000096e00000000e26cc4000000020c859f1fea0000000000000000000000000000000000000000004d88000000000095ba23e00000001c5b2ceadc8162000000086180004731c0e06f0000a7f900c6cf0438c9faa9e15f96d0000204a00000001c0800024f00007e4a14a71d80000000000000000036e94a0000020400000002d90000623800000028b000006200000000a47800000032c4000293600000009ac991239732bea9980000001068c59000098bb27c6451b7a06730e852a0000b8e94da0bd8000000000061b16aa0001a080000000bf709fa8e000006ec88600000000c07800000010760000ebc8edadbea74800000030380001dd8887a846000279c52183ca000102a0000000c5884227f626ec000000000000000000000cb6a0aa00000000000000cd70000a08a62c0e7000000002882d510ea3778e8841ea9e2447800020707143fe1116642874ccdd81a01f49b527a080000000000000097a27aa4ceaeb218e42e9c428d413b200029bc1b3
  | 47 => 0x8c912cc00000009a8242c00028f4a299dfa0000970885000044512e4000000000007925f680003d2311c4188000330a35eb1e024ebb080a21e09296000053a7312c840001d2acac218a82198eaae501148c8063000000000002ef800029800001666c4689a400000008ec2f8e73a8000000000000021bc06780003d680009f8ad84146a40ea6480000001c382d1029e91280000000af454000003360000000000000017689d8a51641b00000000000000289e9f3000000000000001e865740152000000000024540000bc600025a80000000c72810800018d8b8f9d3c11e00003d0800024812f288a196800000001e42cd6880800062c800043b2a484d02bd4cb9961e57a255c29397ba6878e408518580aac19dc6f981322d00718527a57c9828b960002b10ca633ae00021ee0000bfc00000000001e5a0000000000044600000000001cb26378000c34aed00831de855925660000538b572e985e290de47c15ca1112d725a725983e491683db00000142fb85ce87705e08000ba7871c00000000bf84d800000003092f6882932d4a1429540730000c2e89e43c82dec3679378596169a226051840894d0cdf2b529693214ac8975a00004ae7f1a25800030108af07ce0000000000133282c80000000000a3b80002a500003640000000000000000000c31f5c00000001911788b75800000023b22dc800087700000002f4ac102c180001e56c61a0e40000000c459a4a14400000000992000000003380000000000000294ec070a0890e00009f596ec54300001d380009f600000000e1816e80006881a2a00003d200000000000dfc00000000000000000000000033ec072153c98e00002518eb2000000052e2b780001efcb5a0000000178e51b81d24f30bec1d92e3c7139e5898a3262000211853f921e43f8f280e207deada872695fa49e13597b84b7894e7f913ce71802609290b283b5076e5db81acb1d9d224deacce01e1b5c25a0b6a384a5fa3a5a0282af209221e8000b780000ac5a650bc680000000000000010219400009ba80005fb82a800000007ac05a800000000000000000000000000005dd8000af400002dd1e5e344a1101b08a3404f87c0a7b201a00025f40001178b4d26900000f8600012207b2958e87c9206000201e0000000000000000030520000000aa880000000000c1581f00002fbccf98a0e3540fac2098704458190265b9ef67e6b13c88d079887f0000000000000029ca24600000000000ace0e2200015dac8800006208000002800077a8d2600000008418000159000026b80000001ecc72516fc8880d3883d80000000000a6880000001efac9c8000000000000000009311aee2a0800000030b60000666ab7000000000000f5b2ee776800000000007650b245b50fbec9780000002e6e000125000011a6000000
  | 48 => 0x246c00000000150000000000059d00a882000000000bb48ee27202f58a5412e94eabc5981c970034228f0000a6b00007cda5da565af88a2d000000000003bc00000000e844aa127800015406ed0000000000000028ce00007660000000871800000029ba00000000000f742f080005491c92ce287200e5887496b86fa71b0e386100fb25ec0e320000000ad58032a13a3ea7908ee2000000000000005a0800044f0000000000096180008e62d0c00000006ae80000000000000320400000009cf1b1ab4001640000000000000000029580001b5425c923a0b08304000000000028a000020ae3a88a22000000000000000000000a108ac26c00e2400008caabfaa905332e2a00000264f897f2cf706840002a6e0000134b20991a00000000000000000000050ab02600000002cb28380000000cc5b012419b1045ad17a800024460000000ac0800000000000000000b0f0000000060ec958000a229ad258d800029200009581dd2000000000030f475db1aa000000004800001c2ae8c000162c6f324f40a29de4000000073bb2cc0002e680002ac20001e380001b9e000000031786f000027803f080000002da837c11400000bdacbd00001d000000001c5c7a2abfc000318a8c2800069b08488761d68b2d1e4432423d8c2a80009452c4ac6b8e90cec869449998c421a800000000000000c128e800000001ab8000000000000006130000ba58eb80002e8a00000000002aaec8f80000000000000000000000000001a6a0002f70545a7f8606000000000008a51f1600003d803780002cd800070b8000bc51f0a0002526000070858e80006e0a4d600022100001138000000000000004ce27e0000000000000001d20000a7b93d090cb0c21a2a8ea0e380840003016000335000031de07d968e72589969bf8ca080330a20000000848800000000008702d823ed9afe64580009b400000000536a7eac1a00031900c4237e0942c622dd800000000000000000000144a4432cc4457800000003e200007e4ccc8000000182e00028040000bae00000008d2800077d8ad4c47988600005160000000000000020e8000000000094c80000000e2e228b18e6698000529af0c1e58a1ac2911d86ba28082dea03a000230e00000002e711f4b2200000001d6e652087800000001fa11c00000000542a0ba00011b2436256c63180000000dda000320c00013f62a624f2b50b1b2beab32c03d19ca352ac94276083e661ac2464b8000649ad242b7a2cca9da09e00019cc000024cd00976200000005fe97e4963925a000113e0001fba000000020180007caa9740000000000184200006a60000000000139ca91800036187581f6292c09697c62b3059a0000000909027020e0000000000032792b6000146200000007f406ae8c4166885b1d6a00004d49f9800000
  | 49 => 0x338600000000001c240000000000000000019e876e8530b3c800000001a600024bc000000000000007438000ad731500000000000069c000000000012b0000000000180005a6000000000000e780000000afe000000000000000000c96000000000000000000000000000000008440000ec2364a286ad38000805000000000000000000cda80e0000300009b800000000000002efa1f2804a0000000a5980001ae27c60000000000000000007a289d00000001e0eb04085606da786000205e00003be000000025d19ea72c000080023ca6b408ee29f2e74463abb4c450e6000027e400000000000000165811835e0000000301a3ff2de200016ba0000edc0001d366049b2c1719b2000006a8022000080b0000c212ee8c2b000034a2eb091b80007f32a70576000000000005810000a2920b4adf9f942720feac780d8030580000002f520000000000000000000007ea9d8aac791ea84500003331e5220780d646b88645059156000084e31507942d49c1a5d706ca0000000809901806e80000000122000102e00007ae8c3040232000000002c1e22a00004d590825b497f0cb780a0a98968060680000002a5cbde2ebe5f3800000019542e4000023e0ecc6640000000000089f80007c600000001e627aa314acc282c065f00003d307720e50000000000007611067148000000000000000002c780009a2800000000000000000000124200027cab020000000000000000000000000a1d00004d180000000fd857c00006748e80372a82e0000eac6519f8a00000000001f96690000000000001198868000000079700000000a620000000a11000000000008310dee00000007d20000000000000030c8653a8720002bda5f480007f02d8e0000000000000074e99c462ba01c000000000007f6c2397545292364000000091e853c6510000ad783bc5518000ba200000001480bc70000588a5e80002baa0000000cfc8000b48000061632b6000000090587a845d00000001abc00000000001a2caec05bc69f8000c2e19221470000a6b94c20000000000000000000000002dce92417a00000000a8628c049c1b9a000180632d9b66974a6a48ef8000b8b28105d6000034311f20000c260000000000000000000000002d36000000000000000002a3c5770000000243c72ba96829e00005cf00009d3000000000006ea0000000248e83f0000000299c068800000003980000ac800000000003226b410000be50000000000000010a800000606fb2898a4c80000000000384000000000120000000000000085da6600002cee0002f480002cbc71a9bbe200a6224a092f4a2b0b7e619816c3ea8d00856957ac4d2ec02412ade5f29a904c61f84136a85c4c4321807897246c2987a7500d4243a0936a4096f6b4b800000000000002a1632a18560002ce4be780
  | 50 => 0xc9a5c8a59a00024be47280008bc8000000000018420e877f0000acd00005f5000052c0f2a0000dc0a52000035985b499fa178b7100004f10c720000000000018a1c1a1686e3000042100000000314c92890024f800043d800000000007d980003248d9c00000000002b80417800036a817e000000019b800045131c800019800000000000000029332660000000000000011d0ddc2509164000120e000000048b800000018440000000000000096514de94e00008b18000000000000000000000000000198c08b89ee2bcb0500003060c462008000127c000000026c830eb39800000000000001056000309e000205a000139465009e209c80000000a4a000000023d014600000001898000000000000000005908000000070c000088cac0000084785be000000000f0000285800053880001b015c600033f4238000000020c00000f0290d8000000000000006ce000053200030760000000cab0000a9f80000000000c4a1928646152c752ab920000a2c00000000002a2e000159000008cc0000000000262a000000000026b4000000031380004e691581128000b4718c05bc80001fab302a8e94c01ea893211c800000000003fdb34a0000000b2709d200033ce8f587c20e69bd0c0c8358000047c8d5800020d9cb4256b2f6914000000000006ab11b8399109e9fd80008920000000000098380000001b640000000c190d0acc91b148feb15e0002fa402709760000000ca59ab0ae1912a000069800000000001ec200000000000000c01800000000000000000759800090880000000000000102000d014a33d80005852d50cbb15126bf323a3180000171000066ba2aa74722a4afd2d569078cc600033a0000000000000008a7000000000000002bba0000000000000000000000000000a3531483e597560000000c408000297a9b800000003a925ba000000076c941a00009641109eee9faa78c66f9a5e00000000000a185ada5fc81500009708000000224600017accf780007fd961c93b0000000000000000000002a0682b00000000000caf078e0000bc822cac68810195292d1d08a018000000000000000000000000b0b9bc60000e3000012e89df197428100000000000000274e00012d2000188a0000000c361cb60000000000000000000004ce80000000e743d600003170e6a17900007290ca47b000008ee94d60b400000000000300ac36c601db80000000000000000023c00000000a37000000000009b28000000000069980000002e06be000002b5800024500003c3132c44215e0000172a000061c887000063531dcb63194ca980000633b2f82ca8000000000038805865d300000000346c18800000000000000000aa282524f58000433000000000006371c9a190000000005c8000242a0000000000123800000004f1800058300000
  | 51 => 0x213067e7ff9bd6000283a5809aa200000003168000000172c0001f9e9c3800000018fe00013f843b9316000000067baa26afe000098cb146000000000027b8c552c280000000000000000000000000000998b32a4ea1ef00001f0659b13140002c4c00033a810d8f3c9ef000097aa9c40000212000228400019c21758140b5e26f8c5f800000026661820000000000000030542ea00004c1a8ec5c5a9dc736b33c01f00000002a2835c2d965f800007af00005fa204200032c29750d2ec35196200006769f51566000010478c1d9a4ca8000000000000000000000c401a480000000c3000000009ca0ad26d7b15a9e8ad300002fda27c25dca93800000004b4c7b00000002d06000000000000003ef0d7e248a73600000007c42e083e299f600033b40000caa4ff80000000000b8b9d920001dce0000000a1028f8000000037d80000002034000000000000007dd00000000000a1ab1ea24b15d2a0a000000030a623a89da93a00003301ef2b9e00001cf260c0000000901ac22b55000043400008e89dcc11f8dd2a4480008c500000000000000000037321483d5000048c80000000000c66324c2fe9ada3d00000c258cfa3bb2480000142027e00009562f2c6348000c6f0000000000061b80000000000cc3032ec5b8f0a5241a14000021e4ff15a6c7e154e70e80009f4800000009de00002d6c8202202fe000000028301be315c24a83e07f980007f700000001ba67c380000001b4c9432e0078f9836000000000000009c5000002000009a68000000000083e8000000000000025647dfaa0851905ca3c90c74aa502565dc80000000ce2000000000024860000000000000000000009d7800000000002a9046c000112c5fe0000000214e93a800000000008649846415014449296467a394241ce800000030fa5271e268a28000000097800000000000000000000089e05989799adebfe2290aeb909a8509f6ec9c3354000000000024527fa23ecbdb0002894800078f2bce00019348df1cde13c266e00002924991c0841cb3e225b000000000000001cd835d95d65fab3ba7fc26a8a02a646b76847063a00005bab34e746861a36e2df27da0cda3a686ee26525f031e05e614ba9e4ac32c302b42226be313baa0a8604432251e00000006a00000992a6820000000088a28e5ed944c783007e42400000000000000000000000006a91f0c00023a600001b000010e0a5ca9782598cca0000000000056e0000000cf3297a9c28200158000000026f2000095eb2e1e660000000000000000021c400000205a28cf064a9aa0000000073b000000000009c4b23498fb1f20000000000000000000000002f3400008c8000000041127f200022be00006809951e2c0000000000169200000004a40000a962d0276f224000019e600014583f3953a0ad00e60002
  | 52 => 0x28e2c1f8000a801a64000138a3809a229f0250eb6880002798000aa380008f52eb291e0cde00001d6c3300002600a7a4538254526800062b0000667b0e6000000045c000000000000000000643800000000003038b9ea6d8eb084286fe4220000b7d00003bba51203f223ac6f939e000130e261045e9b5800002080000002eeabd7002a00b0298000238a70fa7a41ee8592b2da81883f8000a64000056690e4cf19ca258200002148000b53800000000009fc180231e8e823eb81ca55b0000148800093095ea099000055482e20000afc339aef038d000000000000000000000000000000003d81c264bc1dae0000000000181ea5026040c818ec0001b2a00000004c9847a00002ac5fd000059e8a9275088300000d5eaf32b2400000000000000000101c0000000000000000007606610000220000000000008d6000000010ca00000000001d2000017cc60f239a0000ac600000000d00000bf380000002d522f42128000057404b00000000000815993a00019821d1800017f0000778a1a473d17365ae204600000003260000000000048000009f08000000000030d0000b2c066a96b1b409538000000000000c135400000001642d9a0000000bb7120455d9ca65c6800000000000781c144fa8bce26719a45a58f7250030fc5f8882e4ae903644d0000c9e983e356a8aa000000006f800053c9d78c4433e4895846233e01fc0dda1a246203dcc608092000000000014cac2033927589272c1732762f9b0e400027b674b00009a4aac624200000000788c76ada64219a8834896beae395e600025907888000bf1a9141f5922612c9a100002e84ab29d1295d0000000265e92109f4000092e00000002ce80004be0f2e000000000000000000000b97000038701d05a98c76000000035700009eb000095c900600031e6c0612c400023264bb00000000614326a76a53a000043e800000000000fb2de600018c237800009ec0000be7090c000000000000000002c48000214000000000000df2813800086a91fc05e93eeb1aa71e0001ea611db29e65690da0002b4a2f730883d797ec1e1a76894f000056480862d39b7c0b200ba00013b87a61d8c0001b029ea987611800f80000000a460000c4922fa0003360000264c00031a20000cbaae6042676a00006a32a6c000000095e3290000000000005d4000000027f000094b2bb800000008ca0e583f722e643f05eab8286b43b21d7494c0000000000000000008a889a801213a60362e30c1a8d6c20812fc66c94c60ac00005348000bc800000002500000048aa498000000000066d1506000263400018da5b80c86985ae200001cf05de800008180000000000000022873880003110f8e000000000000000001f7800004b6605ac029a006d651382b630b2b4264c8962493ab6600028808dc10006da0000
  | 53 => 0xafd80000000000000000061d00004d82152baa18f01960000000000000003a8b890a70032158800000000002d8628d80000dc08425600000c9500000002ef4a840568a76800041384640002c4274f9a363061acac8c0000c8024aa000000070b000000000005ca098e00000006b81eb6000337200000003232f36104800000000000000000bc100000000000000000000004900002a14000300a0f228c6c038db2cbf2196a1500000000000cdc259c000143c8c6170c000000000012ee0001e64b19b166be8a5b07a914dca348000cf600004931794133843a000000010591b600000004a7b1925d7800000000000000000000000000033d0000081a000266a2df2bc095a80003909fac00000000d2a1de00000001bb0000a242f26381800000002e6241a1f4523800000000000000000bdbadd276887fc000000000000008e18000cfa00007b70000541000000000000000000000000011a000070f00000000d5800000000000000000000000000000000000439a1be86e88d6000000039e80002542778cac8000c6780000000000950a3ee91793e86b980006ca1d249d1a6f426f0bd44da98a40000000000202400016d600033940000000a86800083b800000026880000d1845f0000000239685f25467d11ac600008ecaa607769c200009e51aae0b1966eaa10d20b7b800000000000000000bb7ab1c51127fa5140000738185e0000000478a80200023322b680009370bf651a000000000000000000000334c8832c16b9100000000fa80000000000088a00004b8127958a0001c9e395933c0000000bbd8000caa90c0000313e000255200027600000b120000000ce3ae0410f9ad4753000000013666a580000002642757000000000004b88f78603af560000000933000044498f633caf2e35e9eacb9caa2c94d1a8a63f1798cc7800065600002e284045f7000080f800071e80000000804cd98c3c4e8b29415ca12a9dc80003c70bbe0001ca80c01ce64708fe4b7a290e000329c5c42306bdf159c00000000002c2053e0c14ab307a4b502922cd5b188b6200007d90c5200018ee79b137008da648c2280000001236195858e000328829a00000002e9c000011cab40c0c8cd06a2bcf00000002b823518000c1e0000000000000000000ac9a860b70d6ab8c91e4bff00000000000a4c1df2be400000000000c1080003aa000000000003130a1c00000000000000000000022c000020483f2ac100002c517d055280f210f0cb02468700a0f18f2152921419926029c42ae405a2868086170a73f2c0eca8a3de000272ca6a023c0000000000000049b800000033fe27280da0430f141cfab080988d1e89b855a89416066d402aa9d68000b1cb3b060100000000000b792792bb399f2322114a84680b27271bc88f192b40000000a88877e00002fa000
  | 54 => 0x7ae8000000000000000000001494a6a800000014d40000000000000000025d611501983b40000c5e0ce43820000521329a78d0e3a0000000bda80003010000a098000000134887d990c159800015132d60000000000312a0000000000000000000000000000b5b000000000009a180000000000a700000000254a0000000000000056d80008a98fda17daa6a4fc2ce29a1290800000000002c983f4ad80c400000000000000015ce0002a52000021a43896442558000a3f31f6c829be0ae2b0dc676a5fe9f680004f78a9a7a5800085a9fb6000324e30a0d60582800000000003c59be80000000000061eab2300caaaad0a7e22796000288625f80008fa000000000000000000c169b600000000000000087e9a8e000000000011d40ae2d2c3020b920000000a5680b67b68000000000000006547690000c2f00000000000000000070d29d876f8d0eb67103a94a89f21271e36c80accc68f000000009b43a3a1f800007245b680008d994e6365b212bff80001000b680000000000218435f0ee619e800000007800000000000000000000009138c06000000000000005bd131216c8594000000000000003d2885c44d800000000000000000ae587220002cac0000000000000000000002d4117623f000015a8b70b3b07380002322cf5000000010aab9a9334402800046c27342e08000bbf000026180005ea9f5ac7faf2a45898509d482864cf800042e1d30b560a0c3c4090a00030480002c0c8222ce00000000c5600000000072829a61cc87ae48157140c86c09260001610500a15e0000f2c8da80000000ffa00009b00001752000000000000000000eb600029340770000c6ea73e00000000000ae0792064e00021b4583a6b8751000000012180000000996931e50c00007018000c972df8a312aea74d05fa5a11af6ccc00000238000acb00001bd80000000000000000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x8659539823104334a94c1108210fdd16194010878e8b0ca00845f73586500422e39ac3280211bdc961940108d8e4b0ca00863554986400422f398ca20021175cc65100108dce4328800846d72194400432aa9cc3180210f9d0650c01087ae8328600846e721943004236b90ca180219954a618801087ce8328400843d74194200422f398ca10021175cc65080108eaed28c200847976946100431bb2ec8880218dd946444010caecbb1a20086576518d100434a320c68802199d976244010cceca31220086a4641891004362318c4880218ed976444010c76ca322200865b65d8d100432db28c688021a61906344010cd6cbb12200866b651891004354320c488021b218c62440108f4ed28a200867175d9510042b93b6ca880219c9db6544010d66cbb22200873365d9110042b8bacc8880216c9d26444010ba4e732220085d17399110042f1394c888021785ca6444010ae6eab2220085d37359110042e839ac88802178dc96444010bc0e4b2220085b27619110043593b0c888021acd946444010e66ca32220084f276d5110042793b0a888021cc5505444010ba4e62a220085d17315110042f1390a888021785c85444010da6cbb1a200875365d8d10043c9b26c688021e41936344010ae2eb31a20085b27498d10042d8ba4c688021ac1926344010ba4e731a20085e27298d10042f0b94c6880215cdd56344010b66e8b1a20085b07458d10042f1b92c688021781c96344010d60c831a20085d27618d10043693b0c688021b4d946344010ea6ca31a20087936418d1004369320c688021b41906344010f20c831a20086906418d10042793b6a6880213c9d85344010b64e829a20085b17414d10043a8a98a688021789c85344010bc2e429a20084f37650d10042783b286880215c9d44344010ae2ea21a20087914310d10042f13908688021785c84344010dc6cbb12200876365d8910043d1b26c488021e81936244010f86c7b1220087c063d8910042b8bacc4880216c9d26244010b62e931220086b06498910042e939cc488021745ce6244010da0c731220085e27298910042b9baac4880216cdd16244010b60e8b1220085d37358910042e839ac488021ac1906244010da0c631220085e27618910043713b0c488021b8d946244010ec6ca31220087a3641891004371320c488021b81906244010f40c831220086a06418910043e1b18c488021b898c6244010dc0c631220087c0631891004360318c4880213c9db52440109e4ec29220085b27414910042d8ba0a488021749cc5244010ba2e62922008761521491004279bb284880213c1d94244010ae4ea21220085717510910042e93988488021745cc4244010f428421220084f3764c910042783b264880215c9d43244010ae2ea19220085b2740c910042d8ba06488021f04c83244010
  | 1 => 0x3044236392ca982218d153614c110cc8a5b0a608863454185304432ba98c29822199148614c110ab0ea9806088718544c030443a42926018221741c5300c110cc8a530e408843e74d95204421eba6ca90221179cf65481108bae7b2a408843f74595204421e3a2ca9022117dcd65481108b8e6b2a408863454d85204432a29ec2902218d1506148110ca8a630a40886675218520442b43aa4010221ca1512008110e90a690040885e071480204438c2a0a788221ca15052c4110e90a629620887145414e10443922a0a508221d114c52841108dce431aa80846d7218d540422f398c4aa021175cc625501087eecaa0a80861d5458c5404316aa2c42a021879916315010c9cc7310a80864d639885404317322c42a0219398d6215010c9ac6b10a808655639845404332b14c22a0219658e6015010cd2c5300a80846e721915304236b90c8a98210f9d06254c1087ae8312a60845f7654c530430eb22a6298219354d6214c10c3ac9318a60862e649885304316b24c4298218b9916214c10c5ac8b10a60864e63588530431ab24c2298219958a6114c10c72c9300a608669629805304237390cba18211b5c865d0c108dce432c860846d721964304237b92caa18211b1c96550c108dce432a860846d72195430428e39aa8a1821471d15350c108eaea30a860863554185430432aa98c2a18213c5c06150c108f2ea302860863954181430432ca98c0a18213c5c46050c108dce5b28860846d72d944304237390ca218211b5c86510c108ece2328860847a70194430430fb2a8621821875954310c10d1a86b10860845e73191520422eb98c8a90210f9d0635481087ae831aa40846f765485204316b22a4290219358d5214810c3cc9318a40861d6498c520430f322c629021875916314810c5ac9310a40864d63988520431ab24c2290219558e6114810c72c9300a40865963980520422f398cba1021175cc65d08108bce632c840845d73196420422fb9acaa1021171cd65508108bce632a840845d731954204296392a8a10214b1d152508108eaea30a8408635541854204332a90c2a10213c5c061508108f2ea3028408639541814204334a90c0a10213c5c460508108bce7b28840845d73d94420422f398ca21021175cc65108108ece2328840847a701944204317b2a84210218b5954210810d1ac6a10840843e74197320421eba0cb990210f9d0658c81087ae832c640843f74595320421e3a2ca990210f9d0654c81087ae832a640854c7254d32042a639aa4990211d5d4614c810caaa630a6408665521853204278b80c2990211e5d4604c810cb2a63026408669521813204278b88c0990210f9d3650c81087ae9b28640843e74194320421eba0ca190211d9c4650c8108f4e0328640864f654c83204326b2a6419021a3591320c810c72a930482
  | 2 => 0x8629221c350c4314910a5ee8880a48852c7444052442a7b9a2029221531cd10149108bce7b2e848845d73d97424422fb9acba1221171cd65d09108bce7b2c848845d73d96424422fb9acb21221171cd65909108bce7b2a848845d73d95424422fb9acaa1221171cd65509108eee2b2a848847b705954244297396a8a12214b9d352509108bce7b28848845d73d94424422fb9aca21221171cd65109108bce6328848845d731944244296b90a821221179d66310910c3ea9318848861c5498c424422e3aac62122187d516310910c38a8b18848845f76d4c424422ebb6a62122117dd853109108baec298848864e63d484244326b1ea4212214b5d05210910c9cc6290848864d6314842442973aa84212214b1d54210910c5ccaa10848862c655084244346b1a8421221c3d4d4210910e18a6a108488634549844244332294c2212211d1d561109109e0e0b088488638549804244334294c0212211e1d560109109e0e2b00848843e74d97324421eba6cb992210fdd165cc910878e8b2e648843e74d96324421eba6cb192210fdd1658c910878e8b2c648843e74d95324421eba6ca992210fdd1654c910878e8b2a648847771595324423db82ca99221539cb534c910a9ce7a92648843e74d94324421eba6ca192210fdd1650c910878e8b28648843e74194324421eba0ca192210f9d6640c910878eab20648843f76d50324421ebb6a8192210fdd8540c91087aec2a0648861e64d4c324430eb26a61922187990530c910c3ac8298648854d7214c3244317326a4192218b593520c910c5cc8290648862d6414832442a6b98a419221539d5320c910a98ea990648864e654c8324432632a6419221a3591320c910e1ea8990648870c544c8324432a29cc2192219914a610c9108e8eab0864884f070584324432c29cc0192219a14a600c9108f0eab0064884f071580324431c2a4c1a0a219614f6050510cd0a5b02828863b54181414432c298c0a0a219a1486050510a68eaa0882887145350441443922928220a216c1c14110510cb0a7306628863854d813144334296c098a218e150604c510cb6a630262886685218131442aa3aa6218a21c5151310c510e88a498862885d0704c43144334294c190a218e1536048510cb0a7b02428863854181214432c298c090a219ad486048510ac8ea90842887245448421443a229a4210a21781c12108510c68a930e808845e73d95404422eb9ecaa02211b9cb65501108dae5b2a808845f73595404422e39acaa02211bdc965501108d8e4b2a808865453d854044332296c2a02218dd506150110ca8a630a808866452185404429c3aa8020221c614d4010110e50a4a0080885b071500404432a29cc3982210f9d3654c11087ae9b2a608846e72d953044236b96ca982210fdd1654c110878e8b2a608846f72595
  | 3 => 0xc95414d10a98e4aa0a68861e65150534430eb20c829a21539c86414d10a9ae4320a6885557119053442acb80c829a21479d06214d10a3ae8310a68864d6218853442aab88c429a21565c06214d10a3ee8880a68851c744405344237396cba1a211b5cb65d0d108dee4b2e868846c725974344237396cb21a211b5cb6590d108dee4b2c868846c725964344237396caa1a211b5cb6550d108dee4b2a868846c72595434423bb8acaa1a211edc16550d10a3ce7aa2868851e74d4d4344237396ca21a211b5cb6510d108dee4b28868846c725944344237390ca21a211b5c86510d10a3ae62a0868851d7414c434428f3aa8621a21471d54310d10c3ccaa18868861c6550c43442373acc421a218bd526210d10c58a9310868864f53988434432629cc421a211b1d56210d10c5ea8b10868862c545884344327a9ac421a219314d6210d10d1a86b10868863454984434432a29cc221a211d1d56110d109e0e0b08868863854980434432c29cc021a211e1d56010d109e0e2b00868845e73993524422eb9cc9a92210f9d263d491087ae931ea48854e7395352442a6b9ca9a922153dcd54d4910a98e6aa6a48870f54d4f52443862a6a7a92214b9d253d4910a5ae929ea48852f7454f52442963a2a7a9221c3d5053d4910e18a829ea48862f6499352442a739cc9a9221535ce64d4910a5ce931ea48852d7498f5244327b1cc7a92211b9d843d49108daec21ea48870d4310f524430faa4c729221871526394910c3ea8b1ca48861c5458e524430f326a729221875935394910c3cc829ca48861d6414e5244317326a5292218b5935294910c9cc7a94a48864d63d4a524430f324c729221875926394910c3cc8b1ca48861d6458e524421f3b6a8a92210f9d85454910c3ea9b1aa48861c54d8d524430faa0c6a92218715063549108bceda9aa48861f64d4d524430e326a6a9221179d85354910c3ec829aa48861c6414d524430fb26c6a9221871936354910c3ec831aa48861c6418d5244317b26c4a92218b1936254910c9ec7b12a48864c63d89524431a326c2a92219518f6154910c70c9b02a48865863d815244237bb2a4292214bdd15214910a58e8a90a48854f7354852442a639aa4292214b9d26214910a5ae9310a48854e7398852442a6b9cc4292218b99754149108daed2a0a48854e7395052442a6b9ca8292211bdd95414910a9ee6aa0a48854c735505244317328a829221939975314910e1ea9a98a48870c54d4c5244236bb4a6292214b9d25314910a5ae9298a48846f7654c5244297ba2a6292214b1d15314910c9cca298a48870f5414c52443862a0a6292218b5906414910a9ce6320a48854d7319052442b2b88c8292215a5c06414910a5ce8318a48852d7418c5244326b18c629221595c46314910ad2e0318a48846e7610c5244236bb0
  | 4 => 0xbce7b28858845d73d9442c422f398ca21621175cc6510b10d1ac6a10858843e7499532c421eba4ca996210f9d3650cb1087ae9b28658843e7419432c421eba0ca19621a3591320cb10c74a8b00838865a5358031c4335292c010e210f9da545031087aedaa0818845e7694d30c422ebb6a6186211b9da52483108daeda90418867161983548421fbb2a82a4219c5866015210ce2c3306a70845f7654c5384338b0cc029c211b9ca6550e108dae532a870846e72d944384236b96ca21c211b9c86510e108dae4328870868d435884384338b0cc1a94211bdd95214a10ce2c3300a50845e73995428422eb9ccaa1421179cf6510a108bae7b28850845e73194428422eb98ca21421a358d4210a1087ce932a650843d74995328421f3a6ca194210f5d3650ca1087ce8328650843d741943284346b2264194210f9da545061087aedaa0830845e7694d318422ebb6a618c211b9da52486108daeda90430863654584408432b29ac2184219994961082108dce531ea88846d7298f544422f39cc5aa221175ce62d5110c3ec731ea88852e7298f5444296b94c7aa221479ce62d5110a3ae7316a88862f6298b544430faa4c72a22187d516395110c5ea9314a88862f5458a544432731cc52a2219358e6295110c9cc6b14a88864d6358a544430fb26c6aa22187d906355110c5ec9b12a88864f63d89544432631ec4aa2218bd906255110c9ec6312a88864c63189544432a31ec2aa2219918b6155110cb0c7b02a88866862d81544421fbb2a82a22147dcd5415110a38e6aa0a88852f725505444296392a82a221479ce6415110a3ae7320a88852e729905444296b94c82a2218758c6315110a5ce4318a88852d7218c544429ab88c62a2214e5c06315110a3ce6310a88851d731885444316b10c42a2214d5c46215110a72e0310a88846e729935344236b94c9a9a210f9d262d4d1087ae9316a68854e7295353442a6b94a9a9a2153dc954d4d10a98e4aa6a68861f6499353442a7394c9a9a21535ca64d4d10a3ce9316a68851d7498b5344327b14c5a9a21879935394d10c3ac9a9ca68862f5498a53443162a4c529a2193d4e6294d10c5ea8b14a68862c5458a5344327a9ac529a218b9926294d10c5ac9314a68862e6458a5344316b22c529a210f9db5454d1087cec2a2a68862f54d8953443162a6c4a9a218bd506254d10c58a8312a68861f64d8d534430e326c6a9a218bd936254d10c58c9b12a68864f63d895344317b20c4a9a218b1906254d10c9ec6312a68863464d855344332316c2a9a218e1936054d10cd0c5b02a68845f7654c534428fba2a629a21471d15314d10a9ee4a98a68854c7254c534428f3a4c629a21475d26314d10a9ce5318a68854d7298c534430f32ea829a21175da5414d10a9ce52a0a68854d72950534422fbb2a829a2153d
  | 5 => 0x5547154c534821f3a0c429a410f5d06214d208ece3b2e869047571d97434823b38ecb21a411d5c76590d208dee4b2a869047771595434823a38acaa1a411edc16550d208dae5b28869047771594434823a38aca21a411b9c86510d20a3ae62a0869051d7414c434828f3aa8621a41471d54310d208d8eab10869062f5458843483162a2c421a4193d4d6210d20c98a6b10869068d435884348274382c421a418e15160d0920d1ac6a108490658535833248346b2264192411ddd95114520a68e8a88a29055473544514822fb9aca20a41171cd65105208bce6328829045d7319441483162a2c420a418e1516010520ce0a2b00829043f74594314821e3a2ca18a410f9d0650c52087ae8328629064c53588314832c29ac018a419c145600c520c58a8b16809045f73595404822e39acaa02419314d62cc12087ee8b2a609043c74595304821fbb2a82a041875516315020c6aa8b08a81061e6458c5408326b1cc42a0419598e6115020caac7308a81063664584540832b31ac22a0419558d6115020cccc4b08a81067161980540822fbb2a629841875915314c20caaa6b08a61061d6498c5308316b24c4298418d9926114c20c6ac9308a61063664584530831ab22c2298419598d6114c20cccc4b08a61067161980530823b388cba18411d5c465d0c208ece232c861047571196430823bb8acaa18411d1c56550c208ece232a861047571195430828e39aa8a1841471d15350c208daea312861062d541894308326a98c4a18411e5d46050c20c72a83028610659531814308236b92ca218411b9c86510c208ece2328861047571194430830fb2a8621841875954310c208daeb31086104e9709884308346a1ac421841179cf65108208bae7b28841052d72550420830f2a2c621041875516310820d1ac6a10841043e74d94320821eba6ca1904187592530c820c3ac8a98641054d7254c3208346b2264190411ddd95114420c6ac8a88a210655635445108274b84c5a084117dcd65504208b8e6b2a821045e73195410822eb98caa08418b5506250420cc8c4a8a8210671511814108274b84c5988410fdd1654c420878e8b2a621043e74195310821eba0ca988419354c624c420cc8c4a8a62106715118131082b2bacc21084159dd95108420cceeca8842104eb755802108335baac0108418b55262900208bce6328801045d731944008326a9cc5180410f9d0650c02087ae8328601046d7694a200823cbb4a510041729cc4248020b54e819240104ea76c85200833930ac1aa6210fdd95415310ce4c2b00a9886726158353c422fbb2a629e219c9856014f108dce532a878846d7299543c4237396ca21e211b5cb6510f108dce4328878846d7219443c4346a1ac421e219c98560d4b108deeca90a5886726158052c422f39ccaa1621175ce6550b108
  | 6 => 0x24c2973aa84212614b1d54210930d1ac6a10849868d644c8324c23bbb2a228a614d1d15114530ac8e4a88a29846f72594414c236392ca20a611b9c865105308dae4328829861c5458c414c31c2a2c020a619c145601053087ee8b28429843c74594214c21f3a0ca10a610f5d06508530c9ac6290429866852580214c33828ac010a618715163d013087eecaa0a81862d54588540c31aaa2c22a0618b9916215030c9cc6b10a81866662984540c332b14c22a0618d9916115030cacc6b08a81866662584540c332b12c22a0619c5866015030a3ae6aa0861862e54588430c316aa2c421861a350d6210c308deeca90a41862d64548520c332a92c2290611ddc565508308e8e2b2a841847671195420c23ab88caa10614b1c95450830c3aa831a841852c74549420c32631aa4a10618e5506050830cd2a430284184d97098c420c317b2a84210618b5954210830d1ac6a10841862d64948320c316b22a419061a3591320c8308eeeca88a21863564544510c332b12a228861365c263d04308dee4b2a821846c72595410c237390caa08611b5c86550430c3aa831a821865463545410c338a88c0a0861555d6610c430aaeeca88621865776544310c26dbaac01886196dd5600c4309b2e131e421843f74595210c21e3a2ca908610f9d0654843087ae832a421864c63549210c32a31aa2908619c5446048430c3aa931c801845d7694e300c23cbb4a718061729c8434c030b34e819260184da76cc5300c335312c1aa6410fdd95415320c3aa8b18a99061e6458c54c8326b1cc42a6419a98960d4f208beeca98a79061d6454c53c830eb24c629e418b5926214f208ece332a87904757199543c828e39aa8a1e41471d15350f20c3ecaa18879061d6550c43c8346a1ac421e41879516310b20c3aa8b18859068d6350842c830eb24a61964187591530cb20d1ac899065904777654451c822f39ccb20e41175ce6590720a6ae32a0839043e7499631c821eba4cb18e41555c6530c720c5aa8312819064d5318930c8334b14c1aa4410fdd95415220cd2c5306a71045f7654c538823b38ccaa1c411d5c66550e208ece23288710475711944388346a1ac421c418e5506050a20d1ac6a108510659531813288346b2264194411ddd951146208bce7b2e831045d73d97418821f3a6cb98c410f5d365cc620c5ca8b10811064e53588308830fb20c6aa2419318f6255120caec7b0aa89065463d85544831bb20c2aa24195d8c6155120ca8c630aa89066762185544832c31ec0aa2419c187605512087eecaa0a89051c73550544829a38aa82a241179cc62151208bae6310a89061c64d8d5348316326c4a9a418dd936154d20c68c9b0aa69063764185534831a320c2a9a4195d8c6154d20ccec430aa69063864d81534833830ec0a9a4117dd95314d20a38e8a98a69
  | 7 => 0x629c81a350d6210e408deeca90a52068d635084290346b2264194811ddd951146408dce5b2e632046d72d97319022f39ecb90c81175cf65c86408beeca98a6a054c7254c53502aa38aa629a81a350d6210d408deeca90a4a054c7354852502b238aa429281a358d42109408eee2b2864a047471594325025c382c81928187593530c940c3ac829864a054d7214c3250316b26a4192818b590520c940a9ae629064a054e754c832502a63aa6419281a3591320c9408eeeca88a2a05547354451502b2392a228a811bdc9650c5408d8e4b2862a046e721943150236b90ca18a8187590530c540cb0a6b0062a067051580315022fb9aca10a81171cd65085408bce632842a045d731942150316b20a410a819a1496008540ce0a2b0042a045f7654c5310326a9ac4298819554d6114c40c9ca6b10862064d535884310346a1ac4218811bdd95214840c9ac6a90a420665525845210326b1ca4210819358d5210840d1ac6a10842047771595321023a38aca990811d9c4654c8408eae232a642061c6454d32102a6392a6990818b191524c840a98e6a926420659531813210334a90c0990812e5c2640c840c9eca990642064d654c83210346b2264190811ddd95114440caac6a88a22066562544511029abacc2208814ddd95110440c6eeca8882204bb75580411031dbaac0208812e5c264cc4408dee4b2a622046c725953110237390ca988811b5c8654c440c38c8a9a6220634645453110338a88c0988812e5c264c84408bee6b2a422045c73595211022f398ca90881175cc6548440c58c8a924220634645452110338a88c0908810f5da54900408f2ed2a480205aa7210d40102cd39884a00812e9db4150040cb4c6b06a99843f7655054cc316aa2c42a6618b9916215330c9cc6b10a99862e5458843cc316aa2c421e61a350d6210f308deeca90a59862d6454852cc296392a8a16614b1d15250b30c5ecaa10859862d6550842cc346b1a84216618b592520cb30c5ac8a90659868d644c832cc23bbb2a228e611b9ca65907308dae532c83985357195041cc21f3a4cb10e610f5d26588730acae3290439861d5418d40cc32cb1cc1aa4610fdd95415230c72a8302871868d43588438c237bb2a429461a358d4210a30d1ac8990651847776544518c237396cba0c611b5cb65d063087ce9b2e431843d74d97218c30f2a2c6204618bd906255130c9ec6312a89866762d85544c332316c2aa2618dd906155130caec630aa89866762185544c332310c2aa2619a18b6055130ce0c3b02a89843f76550544c296392a82a2614d1c55415130c70a8b06869868d43588434c237bb2a4292614b1d15214930ac8e2a90a49847771594424c23a38aca212614b5c85410930c3ea8b18849861c5458c424c26c382c6212619358f5210930a5ae8290849864d631484
  | 8 => 0x95314e218f4e132a8710c7970995438863d380ca21c431e5c06510e21d1a86b108710e35541854288746b1a84214439554c614ca21d1ac89906510e2e54588418872729ac418c431edd95014221c3ec831aa890e4c63d89544872a31ec2aa24396d8f6055121cb0c7b02a890e3b64181544872db18c0aa2439618c6055121cd6c4302a890e7361181544861fbb2a82a243471cd5415121a70e0aa0a890e1c64d8d5348716326c4a9a438d1936154d21c76c9b02a690e3864d81534871db20c0a9a438e1906054d21cb6c6302a690e6b621815348739b08c0a9a4317dd95314d21a38e8a98a690d587054c534863d386cba1a431e5c365d0d218f4e1b2c8690c7970d964348637b92caa1a431ddc56550d218f6e0b2a8690c78705954348636b96ca21a431edc16510d218f0e0b288690d1d73150434868eba0a621a43479d54310d21a38eaa188690c6c755884348717aa2c421a438b1516210d21c9ea6b108690e4c535884348746a1ac421a43391c56210d21c68a8b0e8490e8d63508424872a29ac399243a3591320c921c58a8b168290c5f73595414862e39acaa0a439314d62cc52187ee8b2a6290c3c74595314863dbb2a0282434e1d15014121ab0e6a80a090c3f76550540870eaa2c62a0438e5516015021c3cc8b18a810e4d63988540872d31cc02a0439658e6015021c74c8b00a810e5a63580540872cb1ac02a0439a9896015021ce4c2b00a810c5f7654c530870eb22a6298439654d6014c21c3ac9318a610e2d64988530871d324c0298438e5926014c21c74c8b00a610e3964580530872d31ac0298439a9896014c21ce4c2b00a610c7a70197430863cb80cba18431e9c06590c218f2e032c8610c7b70595430863c382caa18431e9c06550c218f2e032a8610d1c73551430868e3a2a6a18431b5d46250c21c5aa83128610e4d53189430863aba8c2a18438d5506150c21caaa630a8610c6e72194430863d380ca218431e5c06510c21c3ecaa188610e1d6550c4308636bacc421843395c66210c21d1a86b108610c5e73d94420862eb9eca21043879516310821c3aa8b188410e8d63508420861f3a6ca190430f5d3650c821c3ac92986410e1d6454c3208746b2264190438b55262904218bce63288210c5d731944108726a9cc5188430f9d0650c42187ae83286210c6d7694a210863abb4a510843719cc4248421b4ce81924210c7b76540500871cb22a0280439658d50140218beeca98a7a064d5358853d032729ac421e819354d6210f40d1a86b1087a046f7654852d0326b1aa4296819358e5210b40c9ac6a9085a068d6350842d02a6392a699681531cd524cb40c9eca99065a064d654c832d0346b2264196811ddd951147408dce532c63a046d7299631d02aab8ca618e81179ce65887408bae732c43a05657194821d022fbb2a
  | 9 => 0x2a6b00a620e4e535884310726a9ac421883a350d6210c418deeca90a420e4d635485210734a92c0290839358e5210841c9ac6a908420e8d63508421063db82ca990831e1c1654c8418f4e032a6420c7970195321070e322a699083531c9534c841c58c8a926420d4c73549321072aa98c29908399548614c84196ae33206420e4f654c83210726b2a6419083a3591320c84187aed2a48220c757695241106d339086a0883659cc42504418f6eca80a020e59635405010734b12a0280839598d61d533187eecaa0a998e2d5458854cc717322c42a6639398d6215331c5ca8b108798e2d5458843cc746a1ac421e631bdd95214b31c5ac8a90a598d2c7255142cc6963a2a4a16638bd954210b31c5acaa108598e8d6350842cc716b24a4196638b591520cb31d1ac89906598e1d5418d41cc63dbb2a0286639558e61d523187eecaa0a918e3554185438c746a1ac421c631bdd95214a31d1ac6a108518e8d644c8328c70f2a2c620c631edd95014231c5ec8312a898e4f63189544c732316c2aa2639ad8b6055131cd0c5b02a898e3b64181544c72db18c0aa2639ad886055131cd0c4302a898e7361181544c61fbb2a82a2634b1c95415131a70e0aa0a898e3454587434c746a1ac421a631bdd95214931a58e8a90a498d6870548524c63db82ca212631e1c16510931a5ae42a08498e1f5458c424c70e2a2c621263351c56310931c9ac7a908498d2d74148424c726b18a4212634b9d54210931a58eaa108498e8d63508424c746b2264192638715163d05318f6eca80a098d3874540504c6b4392a0282630fdd95415031c5aa8b10a818e3954580540c717322c42a0639398d6215031cd4c5300a818e6962980540c71d322c02a0639698d6015031cd4c4b00a818e6962580540c73930ac02a0638b9516210c31c5aa8b108618e8d43588430c637bb2a4290638b5915214831cd2a4b00a418c7b70595420c63c382caa10631e9c065508318f2e032a8418d2c72551420c70eaa0c6a10634b1d15250831c98c6a928418e3554185420c732a90c2a1063355c66310831c5ecaa108418e2d65508420c746b1a84210638b592520c831c5ac8a906418e8d644c8320c70eaa4c720863175da538c4318eaed29c6218dc67210d310c6cb3a064988631edd95014031c72c8a80a018e6962540500c733312c3aa6430fdd95415321c3aa8b18a990e1e6458c54c8726b1cc42a6439998961d4f218beeca98a790e1d6454c53c870eb24c629e438b5926214f218f4e132a8790c797099543c868e39aa8a1e43471d15350f21c3ecaa188790e1d6550c43c8746a1ac421e43879516310b21c3aa8b188590e8d6350842c870eb24a61964387591530cb21d1ac89906590e2d5418941c8726a98c498e431edd95014321ccac530ea910c3f765505488732b14c3a9c4317dd
  | 10 => 0x62f65551320cb8739aa899065c31cd544c832c5aa9b1a641970d54d8d320cb86aa4a699065535d7434c832e1aa9a1a641970d5490d320cb86aa28699065535d4434c832e1aa821a641964d75d95320cb273b6ca99065535d3654c832a9aeb322641954f75591320cae3b8ac899065711c5644c832b96e0b2264195c870591320cb46b20c899065339db544c832a9cedaa2641964e76d51320caa6baca899065635d6544c832a1aeb2a2641968f65951320cb87b2ca899065539d9544c832a98ecaa2641970f74551320cb87b22a899065c3191544c832e1eeaaa2641968f65551320cb87b2aa899065c3dd9544c832e1cecaa2641970d76551320cb863b2a899065c3dc5544c832e1ce2aa2641970d71551320cb8638aa899065c3dc1544c832e1ce0aa2641970d70551320cb86382a899065339d8544c832a9cea2a2641958e74151320cb86aa0a899065c3553614c832a9aeb30a641970d54985320caa7baac29906563dd1614c832b18e8b0a641970d54585320cae5b82c299065721c1614c832e1aa830a64196c561185320cb86aa6c099065535d6604c832e1aa9302641954f75581320cac7ba2c099065631d1604c832e1aa8b0264195c771581320cae238ac099065c3550604c832d92c030264194cf764cb510cb4732265a8865a359132d4432e1aa8996a21970d544ca510ca1fba2c1288650f1d16094432e1aa8992a21943d76950510ca1fbb2a82886533dd93214432d1cc8990a21968d644c8510cb86aa264288651ddd95114432c74a9300a21963954980510cb64994c0288658e9516014432c72a8b00a2196c932580510cb38a8ac02886533dd932d4032d1cc8996a01968d644cb500cb86aa265a8065c3551329403287ee8b0ca01943c74586500cb86aa264a80650f5da541403287eecaa0a0194cf764c8500cb473226428065a35913214032e1aa8990a01963654984500cb1aaa4c228065b14ca6114032c6ca8b08a01963554584500cb62992c2280651edd95014032ce2c2a80a01945f7654c53d0726a9ac429e839394d6210f41c9aa6b1087a0e8d4358843d0637bb2a4296839358d5214b41c9ac729085a0e4d6354842d0746b1a8421683531c9534cb41a98e6a9265a0e4f654c832d0726b2a6419683a3591320cb418f6eca80a1a0c5f7654c5390746a1ac421c831bdd95214a41d1ac6a108520e8d644c8329063dbb2a02848317dd95314d41a98e4a98a6a0d587054c5350746a1ac421a831bdd95214941a98e6a90a4a0d68705485250746b1a84212831edc1650c9418f0e0b2864a0cb471590325070eb26a61928387590530c941a9ae429864a0e2d64d483250716b20a419283535cc520c941a9cea99064a0d4c754c83250746b2264192831edd95014141ab0e6a80a0a0d6872540505062fbb2a6298839354d6214c41cb
  | 11 => 0x10b86a9a84280859594e6114042caaa7308a0216a5429845010b2b29ac2280859554d6114042d4a84b08a02147b765405010b38b0aa0280859398d62d533287eecaa0a99964e6358854cca1f3b0a8a1e65635cb5450f328bcec2a2879949e7615143cca8f3b0a8a1e65879d85450f32e1ae42a2879943f7655043ccb172a2c421e658b5516210f32d1a86b10879961d5418d42ccac639286a1665a358d4210b328eeeca88a39947b7654050ccb26b1cc5aa4650fdd95415232c9ac7310a91962d54189438cb46a1ac421c650f9d85450a32b1ae7aa2851946e76151428ca573b0a8a14654b9d85450a32c5cec2a2851970d73151428cb4631a86a14650fdd95410a32c3ca8b18851961d5458c428cb46b1a84214651ddd951146328f6eca80a11963764185544cb2bb18c2aa26599d886155132ce6c3b02a89967061d81544cb1db20c0aa26596d8c6055132cd6c4302a89967361181544cb38308c0aa2650fdd95415132a68e2aa0a89953870550544cb26b1ac42a2658b15162d0d32a9cea314869951e75d91434ca8f3a4a8a1a65179d85450d32a3cec2a2869961e76151434cb86b90a8a1a65339d46250d32c9cea312869961c5458f424ca8e3aa87a1265631c943d0932a9cea31c849954c7550e424cb862a28721265471d54350932c38caa1a849958c7250d424ca973aec8a12654b9d254509328dcec2a2849952e76151424cb173b0a8a1265c35cc545093299cea31a849964e7518d424cb1632e86a1265a318f4350932c98cb21a849958d7490d424cb862a486a12654b1d54350932c58caa1a849954c7550d424cb2632a86a1265c31d54350932a18eaa1a849970f6550d424cb4632a86a1265c31954350932c18caa1a849968d63508424cb46b248799265a3d9143cc932d1ac9214649968f6450a324ca3bbb2a228a654d1d15114532ae0e0a88a29943f74580514ca1e3a2c028a651edd95014132a70e8a80a09957071540504ca1fba2c2282650f1d16114132c6ac230ca81963960182540ca8e39ac2aa0654b1c96155032a76e0b0aa81953870585540cb1ab08c2aa065471cd6055032a58e4b02a81953771581540ca9a38ac0aa0658e580605503287eecaa0a81962d5498a430ca37baac5218658b5516290c32c3ecaa18861961d6550c430cb16aa4c4218658b9516210c32c5aa8b10861968d43588430cb0eaa4c72106517dd56390832c3aa8b1c841961d5498c420cb0f2a2c621065875516310832c5ecaa10841962d65508420cb46b1a8421065175da538c8328daed29c641945e76d51320ca8ebaca89906587d96544c832c3ecaaa2641970e72551320cb86392a89906587553624c832a9aeba12641970d54d09320cb86aa48499065c3551424c832a9aea212641970d54109320ca373b6a8990654b5d6544c832c5ecb2a26419
  | 12 => 0x280871bdd95214043e1a86a90a021e95439845010f33294c2280879954a6114043d2a86b08a021e66525845010f32a92c2280871edd95014043ce2c2a80a021c5f7654c53d0ac6b96a6a1e85279d85350f42c9aa6b1087a168d4358843d0a3bbb2a228e851edd950143428beeca98a72168d435884390a3bbb2a228c851edd950142428beeca98a6a15547154c5350aac382a629a854b9d462d0d42a3cebb1a86a151e7614d4350b0f3b0a6a1a85c35c85350d4295cea31286a162e751894350b46b1e87a12851ddd95114542aa8e6a88a2a1570705445150a2fb9ac028a85171cd60145428f6eca80a0a1558735405050ab838aa02828517dcd61141428b8e6b08a0a1655611865310b2cb00c129885471d16154c42a98e4b0aa62155b705855310aac382c2a9885955846154c42a38e8b02a62154c725815310aabb8ac0a9885551c56054c42cb2c0302a62145f7654c5310b26a9ac5a18859354e6210c42c9ca6b10862168d435884310a1ebb4a9210851b5da5490842c3ecb29a842161f6554d4210b87392a6a1085c31c95350842c9ecb29a842164f6554d4210b872a2a6a1085c39d15350842e1ec8a9a842170d53d0d4210a96bac86a1085c354e4350842e1aa621a842162d75d954210b173b6caa10854b5cf6550842a5aeb31a842152f7558d4210ad3b8ac6a1085691c56350842b56e0b1a84215a87058d4210b46b18c6a10852b9db5350842b1aeb29a842168f6594d4210b87b2ca6a10854b9d95350842a58eca9a842170f6354d4210b8631aa6a1085c3dd55350842d1ecaa9a842170f6554d4210b87bb2a6a1085c39d95350842e1aeca9a842170c7654d4210b87b8aa6a1085c39c55350842e1ae2a9a842170c7154d4210b87b82a6a1085c39c15350842e1ae0a9a842170c7054d4210a573b0a6a1085639cc5350842e1aa629a842170d53d854210a96bacc2a1085c354e6150842a5eeab0a842158f735854210ac639ac2a1085c354d6150842b56e0b0a84215a8705854210b86a98c2a1085a95846150842e1aa7b02842152d759814210b86a9cc0a10854bdd56050842b1ee6b02842158c735814210b86a9ac0a108569dc56050842b48e2b02842170d531814210b54b00c0a10852bdd942d4442d1cc6a16a22168d6350b5110b86a9a85a8885c354d42944428bee6b04a22145c735825110b86a9a84a8885175da53144428beeca98a2214af765085110b4731a8428885a358d4214442e1aa6a10a221477765445110b2d29cc0288859654e6014442d5285300a22165a535805110b2ca9ac028885aa5096014442ce2a2b00a2214af7650b5010b4731a85a8085a358d42d4042e1aa6a16a02170d5350a5010a2fb9ac328085171cd6194042e1aa6a12a02145d7694c5010a2fbb2a6280852bdd94214042d1cc6a10a02168d6350850
  | 13 => 0x100000180680000080000100080000000000080280200200000000080000100000100080101500100080180100380000080200180080000400080080100100000100000080000180480280080180000100180000200000000080600180000000100e80180100000000080000100000180000100180180000000480100280000480000380080280000200780000300000100600280180000000080080800100000600b00000100080000400b80080000000180000080080700480000000100080b000000000002001003801004c6f7654852d0e3bbb2a228e871edd950143438deeca90a521c77765445190e3dbb2a0284871bdd95214943ac8e2a90a4a1d68705485250e3bbb2a228a87591c95114543ae0e0a88a2a1c6f725805150e36392c028a871edd95014143ad0e4a80a0a1d70715405050e37b92c2282871b1c9611414387aed2a48621c5d769524310f0ebaecaa1887879db6550c43a3ae5b2a8621d1d759894310e8fbaac4a188765dc56250c43b28e2b128621d9b705894310ecc382c4a1887a35886250c43a3aeb30a8621d1f755854310ec7b92c2a1887631c96150c43b36e0b0a8621d98705854310f4ab08c2a1887475d66050c43a3eeab028621d8f725814310ec6392c0a188765dc56050c43b28e2b028621e99601814310e4fbb287a90874bdd54394843a9eeaa1ca421d8f7550e5210f87baa8729087995846194843cd2c0304a421e1f7650d5210f0e3b286a9087c3dc94354843e18e4a1aa421d2f7550d5210ea7baa86a908763dd54354843e1eeaa1aa421f0f6550d5210f87b9a86a9087c398d4354843e1ee8a1aa421f0e6450d5210f87bb286a9087c39d94354843e1aeca1aa421f0c7650d5210f87b8a86a9087c39c54354843e1ae2a1aa421f0c7150d5210f87b8286a9087c39c14354843e1ae0a1aa421f0c7050d5210f86a1886a9087c350f6154843e1a8730aa421d2c745855210ea639ac2a9087c350d6154843ad6e0b0aa421d68705855210f86a18c2a9087995846154843e1a87b02a421f0d439815210e963a2c0a9087531cd6054843e1a86b02a421d67715815210eb238ac0a9087c350c6054843cd2c0302a421c9f7650c5210f46a1cc4290871bdd95214843e1a86a90a421c9f7650f5110f46a1cc5a8887a350d62d4443e1a86a96a221f0d4354a5110e37b92c1288871b1c96094443e1a86a92a221c9f7650c5110f46a1cc428887a350d62144438daed290a221c6f765485110f86a1aa4288871ddd95114443d3287300a221e6a529805110f34a94c028887a650d6014443cd4a4b00a221e69525805110f38a8ac02888727dd943d4043d1a87316a021e8d4358b5010f86a1aa5a8087c350d52940438dee4b0ca021c6c725865010f86a1aa4a808727dd94314043d1a87310a021e8d435885010e36bb4a4
  | 14 => 0xd440da00013a80000002731fb9e98a280322ea1dc47243aa2b9978007c0760000000000000225892ca0a0530d392e10884cf3408d103f40001961760f946d03658ec40008280801f542ee43500080000200000000380380000000880180300800200080080300200d00800c80180500380180000500c80000580000200180000280000400000080680000080000000200200a00300000000880380380c80800200280000380000400100000400000080280400000000500400480100180000000380280080000000400380000200000180100380000000600080200180400180400300000000100300500180001380080400280500100080000180280000080100000000000000000080000580000000000200000000900100100100400100080000000200000100280000180080000080000000100280100180080000000180000380080000080000000100180000000580000100200400000180200080080000180000600000280500000080280100000080580000700180180000380000180600180000000000100200100a00000080280000300400180580100480000080400200100100600080080000000500080000000100080200000000300200000400000180500200700000100400000500000280000000000000000180180000080180180080180400380b80d80000580400000280200080080000280180580000180080100080000000000380180180200380000200000080080180080780080080000900000080000080a00080080200100000100000080000000600180700700080000200900180000000000800000000000a00000000080000080880300300280a00480000a00500f80200400200000400180180000080300080380500180380100180280300100080280000000100080000080400500000080400200300380080000000000080300c00100000000000000200000000500000000000100180000280280400480100200880080480100000400100180000680400000000300000200000000000200780480880600180000200080000480100480380b80200000300100100180100000780000000280100000000000000f00000300000080200080000180100500d00200000000300000580180180080000080b80000000280500080400180300180a80100100480000000280680200000000000980300100180780080380080080180680180000200200400000180580000280080000000480100680000080280100000000080000300180000100080500000000280400200080000000000480000000401001000100900180000080300080080080500080280180000280080080900200480100200200b80f00000100080480000c80300000180000100000000500400000100000000000000a001801800801000803802800
  | 15 => 0x2033a416c0fe019b17d1810a482c042494c000041500020b0cac00c2199b510601500000000d2c51801709185ac2420e70c4467c7460000238d600000001be8f2c8181b48b08e5a3af31b844cf065230000ca800066643696f4e625ba1298f007be2bb3010000ecc2eb0e785a009c13400009847b08bf00000000008e30000000000000000211cb3e00034e9814000526000000089c00000002148600000dd9c94ad23d00c780000001640831ad48a25dd0708828b4a61f1a1001c00077800006f80002de000000051877c09d955457276935b0d2c6500002f4a0e4fce4ab1f9807d14a19200006d0cd46233901ed800000038200005583de08200ec5a831a430a2e8e940000000b40c2e77d32fa248cf20000000488a546a012600000003e700017e91bc00000000001da0d03661118a5c00000006ac6e81902b719c01e08d931d000089000000000008400004298000ce456832302cc0006071a380003ee000000000031034a000130800083300000000000000000a689e67a40959d3005e2372a9203c7fe17800020bcd9a09c2ce000000074921c8000a060bb28580006465a130306580000002dc8428026000000000078e00042081c00006de0001ec4e3887303d23600000000d8000000021200023bc5e00ba09881680006a9409000009e00036e89ac8ce6770ff23509166641c002ac02a5632b79cdc59c5743f221805be378000129005248014e98d8ea848209b95e854c0000d088a830e65a479147400030e31c80008d47431f00348744000000198800027707100005b033800003f400060126b929903222105f07186ac0b200000010ce7340548da05e817f44c0940000000000000000073e03480000000001a28a640005cc4749e688fe05f20a1ea00000004760a0c5263e83ef8e981080a01e79acc00039611a8a4400043f45c230c0000000000e951a44f805c12d8e5c1663f50cc4e9a0001f51610a8c0000991dbc4266340059e201f4000428a2900ba0000928b849ca8502cda2c0d0000000c128400053f3ce96bc3b485e17b090400000000005c42100000000000f9a3080001c0489e74f17d8d845de57b1609620c7858202907a40000000e400001f800022618cd0de6e30e500000002310000000b1e00003a9658000000349193c0005c30000000a9a3a92af15f40000003ac9b901f67073c08a5885e59100010f40003332388000bc28b4000000083e3933700000f0a00000284c0d7e5b336a82bc1f01f90c722d82d222e1b29348e2a00024b196d03849d01c000069800028601ac56455023411100000004671374000000000053084c55400000010ee4f908c9324d587be139159cb7e6b4000047cc2c17010d9df81de12a34714f04f6236071903cbdc6862129b7014a4f22ca8f0c0005200031b4c5020002d90dac1bc6893730
  | 16 => 0x50d0d06141628924924000037122107c16f3ea0000000635000186c5f800033608b00000000fe959400000000005780003fe0d20000918722000183071600000011d872836224a9dd800075714200000004ef00017ac5e44640d9a13c62c36f1ea8708bbc78f2e31b183dc8460510aa07f8248013045016a8930002138b167ae0d10608baa0ac13718b4212217000000000077700022c40005f400000000000003228fe8e6a3822711b140000001d411a400034e000000000086e0000000000000280950833e899000000097a47400017946a001b16c89e488000000000000007e003b87340ca0000001d1041000000000004d00000002030e3e000000000101629b1d01390dfa8160e01e30f560004118000fae4900fa801006284337982300d84980e491785d0539000000101a0004408000000000143000036439f47100010982431ab9a8d0cc8e522091351401a800680000008b548123d897c00044f8d491dc00025384d88d65df0a08e8cd348850000eb42422c320ca03919a65015481211a651211205f51c23ec4010df4a5a4a9243142046468704095b07105b10a3052cb480d438c89982c64ba1908da80000000000000b680003d681d073c8d700010b000000042501c8d4232600020d83a200000005502ba00000003b07300001a00000a5664110580000000000000000000000000000071c661000008c4c66ba23c116c5744832640000676000000182917600000000000000000001238000000260800040829f19484780000004430c3c986000399000077a000388800114e00041a91885cc00000000000000002048e2800037a00000000008f400022c904065e0001fec63e5480000678ea23d2063a274a5e40217008800005ea00015f82047d62ec9af80000d51469bc46f211819000009465d61cd902c8aa51c2a590d00000003d019b40000000000000ed670542f800000078700000000000002c323f41ec5f100000005422c400023180005763d50ec00800001db9ca40002851d610c4db669b28c85b8ab66a7284904cdc42e300008ec6c05f30da80000002d700000000000000a78380aea02c02a80c00001284052228f6688d3442254dac20e2b800007b265113f8000f0432400e00008e00001fa9fe800004b25a9b0107a6f6102800043a7240f51e006a600003f00010786c900000000003cc28d20fc2e60000000000000000000000094000023194d509a558114a4000000001c80b54a3e66701f8f4c8fa0002d70e3400000000004702be3cb0000000b584293ae8064000000000162875c37001416d400000000000000a21dc165107031248d0340a4015a0000001044c6400000003fc72a3b900000002b2000000238062400006480000000003b0a08800000000022e515870e1f6822c4322ea086a39861864b28b877c2c2
  | 17 => 0x24f62dc03440003e630e8f6c0c24ec117960c60e5a335783f80000f1346000120272c32a9dd48425c700000000000001dd94d88701d200000006742102b2000072271600000011348fe0001d9000000002510dce968c84030af000000000004f0000000000000000002b11f80000000000000498e6600000000000000660001edc4bc0000bd81e47dc33d15110f0c400eb1cc983c00058c27686d8000000085800018c7583a9178c0728bc08880002667ef00005104ae41700019ad0768ae4551f0ce4c4470f91f4d0f641825b9cf00003b225983906b07ec32a0844b0e4e70001ba8cc689e0fe0af46b22520000c60b9c5bb1159c4c0003bc34c17109be81d3a9a18c0fe2972158e740005270000a9c2c0000000000000000000000000003da0001c843286a5000000063800016313281e62dc3b10000bc867f3708000ea049100000011be00032e061430012d3ba12240660002852370000644087a3400008040108cd41d40000001d54e702e927198848360e9460a1e40004070be0ab40001012e423e10ac0002e00e9094a4bc0001580ffe8c5209087c10000040480009966b801005245f22223621bf01464ac000000000000033e1c087900000de0a282ca26f2df1ae400000329e80006720000001e640000001c380008d800000018ec33400000780001827f711c02a10646d8402a390aba1c52281aa80000003e480785606f233f1400a1e1f60e195f019862410a99004300001ce06b88b28700000dc40000004449314bcc000267111400059300000000002c700011f81900004080000000191278944053000024b80001606752f6a2585ea0ce02da25c6c837e22b9bb811a6090000954bb65d321d80006042344769c3400000200000000000000000df000000000001e0000000000235900e7e233c234450488401b00006566910001168438363000126c37a0000001f4416800023986bd1aa0001198000cf40960000180b5a6d2000079893e0000651f851ee00000000380000003ae08f80783f047f9ed000006a3cd85080ac1930000eccc4a4bb22f80009a000018684fc0008900000000a9871219f800000000000000002a20003fa19d0d9e2b114f23010267ee3c7000008e791420232c76c6821f5a20115600000014e80002a50df8000f30000200800000014725901f40000003fe22dc00064a0001b04c7e2060001350bec7eb0ea80005e6176444066115a0950c322705008910000c0c4b600000000004be10312d00451d01f11ad0000bc427800005e8c2454933884f80000003218cbc0000000000000e540000a70000f841170000a800008751e50000d5000029a000078a00000007400002260001b7c0000003de953800034d097800000001734a80000006ef2899564f7066e47d00002fc00000017fc0000003e70000e10477353
  | 18 => 0x9800104818313000001e40001f894e00006d738d0000cae10e0001e9c00055c0001f948480004458398f8000000014c80003b439580002d6000356a23903c0004510a8c24028f125141c0860003e42188f645fc00005591f60e51fd8000000000000000000000047516ac44a7f1256800105c0bd3b68178f521d703d90b400011b00004e11b44de3d78000bf638f26c86e45d83cd1ee000000001a3180000c982b700000006f62bf3ce166000083839f86b43c800036c8e0c0008013419fc8a8236e000000000032232c18340000000000000ba0000376901800073d24c98540005371af96411040000002310000000000000000035437a80000000000169878000000176800069e87400000000004bf3849ee802c6b700020ac0005253c58000c5662200021fc5fe3053ed00006600000001c40f76557000172802053310618b834664e18e8674000000221a1f4000000329800000000000000000006310001af46b60002b5000079c28800020e90e28a30450c6468c0000000f910965aa00020dcf8e00022b00002f20000000000000000000065d1504230ec06306ce00047c88787a28e705718f803a7792a380005244cd45780004d869f00000010280001d5800000026743e07bd0c856d00021c80000901770b748742651ee80000008310001f8ca94315342000081a0003dc80000000000f993700ae4cc3760c780004a2334834c2d40451b91444b1253100017bc4b81a92ab1634f463091221b680c679200003589ea694185037001220130d10b89507db25805709b057723c88f0f888081af0704000829000215cdfc7e9000000078c05900000e80000000f40c4014e00000011b8f4200013d1194c223c20000e250060420000fa40005d106216009a229c0000000da211200000000000340001c18bb82713818000d2e00012a0bdc01400000010a8ff000000000000000003468268e5e71b0001e2826a1070000000d9c8a64291a90e9c0000000f8cc1074000016800000000a902903624750000000294349000000091e59e3b800000005da4139d9c6cc4e11380db40001ed2330000cca7a50001a78dfe00000000000240000001c50d1e20f14707651664d343d10d8af00000b6821c8f6000363a3c074e76a0ee8000a0c11000017dcf0c00026d1b94358629270000000037f0eb1f7800013a0000000a5022d00000000006683e800007182af00000010340003f300f4c260000000c6c4720000490c011b68bd30008688f450e0b905143400dd000124ca528250001ef05b60000970604de827c12b232910e02a000000040033207c871c0005940dc03010223d42c28b4c0000000000000ffa00000000007e40000000cb81d00000000000bea6ab12880000000000000000ae20002fe80000000000000e6809808f18b8e1800066f27e8588f1
  | 19 => 0x1444a32692288b06c82a89be0a8a000211100c9f80cf0000858f207950000000480487000020c0005400ba10307700cd40f9e4c8927b50000b4400000004c231cb6e27e2fc800000070b3d11decbe46590311ac8ad634828a9310c328f306f80003540000f080000b80bf1b99268d16000205179c6ec0000001fcc81c0244679898ec00003e60b200001e0000175ce1e0001a182791841551e2099000058100020b48083fd32e8b8820a1b70001d9400000000023d40002f813e93c0b2e0000000e8446055a3bfa1d829074508d16d800025814a1f18000000000172c11000041080005fc0000000000abe0000000acc9808a926312e49540000a00000d202763e580000001f00001210a2c00000000000003e23cb9af0000000000000049c00000018f48a889b4418750e004eb04890a0f5830b111a1ac39673a1039a4ce1815b27305d4d6275f39c87d0c846523bd0c04fa42091ae00001b086a0ff80880020bc2308ee8556381000022462812734e09347de00014a99200000730aba0d000000000000008ba4ee000048cb3a00025a04b000000000015100000000000000c540a60001bac0000001f0910800085a0dd15c8ee60670000ad40000003b198409f62742b322300000b700000000002b808b000000000033da23d0ba75b0000000df60003ab1aec0000c2475828456870a0000f5c000000094a1a46261cc0c501bc18a00000023c40000f513699cc00009d3138000fda00007a0b246ee3f81cb80000002aa0000000d9426900001105980000001748e3a00000016a105400036180000002cf3a3854c8de00000000006ea1950001d783ca0000c217c000009700000003c45c527a076d142000213800000000000021500004d61068000a445c90fd936d0b851b00000002d85cd46e8b909d484512c800000060e0001c5cf8a3840000000082000000000064a28b000089c00000006182d80000003ff15e4a7c7300001588fb849e182000000045c12e954c0002b639b0b68010494357210887c0001aa81180000823b921b00006763941f044c43413f40568dee76e3ee9fe41264ff2a18b34000400466078d0b65021fc82642484e83d807b0b520d90431e500283b51c282e49388c92fc1214c505041df14b00004520000000000000000205400060308e8000dce8be0000808a9e8942d39668e4641a12280dc45067d1fb1efc0001a63c6904000005002a0b4822a5210001e7904c6e9196809c0000000001478df20002e11b0800000003e00000000002390000000000000027c000000000000000071e1e480010b033c0770b2c3bc00000003dc00005800000d496264728684304745ec000118055c3c120f0db000079f11e800000035d000000000068500000000000003fa800031a19c0002000000000000000000004904d9980c305c10e
  | 20 => 0x1f80000c180005e827480000000003fb15fc00000043c16f00004fe42c80000004fa14490c909000015f16380007d92579a881b40003780664c5e76c0588c9cc1648117894ec7ca3f419b206c1b63d620b07101540002b08000b3241d26393dc27a6991351d6809a8fc03205348f871800000005ca0712e79870b4462c000000000013904a085102e5922571da10ca00000000001ce02506b80000004050001cec8100cb1438efce847840000a90000334000000048e000374000000000043f05605fa727000114c8da0000d28000c707d82ff0b9c0001673a0893c00000000000003168550001698c921e70000cdc0007cf26a87acd
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0x1544c832d09701c1544c83290e87551614c83290c87551614c832d0954dc1614c832d09541c1614c832a8484584614c832e0554584614c832ac080584614c83290e87551604c83290c87551604c832d0554dc5604c832d05541c5604c832a8884580604c832e0954580604c832ac081580604c832e09544ca6014432e09544c96014432e05544ca6114032e05544c96114032c0d645c8530c941c0d645cc520c941c0e75591320c941a0d821516310931c0d7458c5210931c0e7558d4210931a0d831516210d21a0d8414d6210d21a0e8550d6210d21a0c8550d6210d21c0d645c8530c940c0d645cc520c940c0e75591320c940a0d821516310930c0d7458c5210930c0e7558d4210930a0d831516210d20a0d8414d6210d20a0e8550d6210d20a0c8550d6210d20a0d825954310c20a0d825516310820c0d645c9530c820c0f635ca63d5110c0d73d8a62d5110c0d635c86315110c0d735886215110c0f645ca64d4d10c0d74d8a62d4d10c0d645c86414d10c0d745886214d1090d829cf5450d1090d829d35350d10a0d821954310d10a0d831516210d10a0d8414d6210d10a0e8550d6210d10a0c8550d6210d10c0c7550d6210d10c0f645ce64d4910c0d74d8e63d4910c0e7650c43d4910c0d645cc6414910c0d7458c6314910c0d7650c431491090d839cb545091090d839d35250910a0d821516310910c0d7458c5210910a0d831954210910a0c8558d4210910c0e7558d4210910c0c7558d4210910a0f86d4d4210910a0d8614d421091090d849cb534c91090d849cf524c910c0d645c8530c910c0d645cc520c910a0d84195320c910a0c85591320c910c0e75591320c910c0c75591320c910a0f86d51320c910a0d86151320c910d10531c14110510d20521c14110510d10541c1310c510d40521c1310c510d20541c12108510d40531c12108510d10531c54010110d20521c54010110d10541c5300c110d40521c5300c110d20541c52008110d40531c5200811090d821cd5450c1090d821d15350c10a0d82d954310c1090d831c9545081090d831d15250810a0d83d95421081090d841c9534c81090d841cd524c810a0d84d95320c810d11545cc5444010d21545c85444010ca0649ca6344010a92849906344010ac2829906344010d117454c5344010d41535c85344010a908650c4344010d117550c43440108e0865c84344010d81435c84344010e806418f6244010c90649ce6244010c927418e6244010aa2849906244010ac2839906244010e8064d8c6244010aa28498c6244010ac28398c6244010e836418c6244010e806418c6244010d21745485244010d417354852440108d0865cc4244010aa0865084244010d21755084244010d817350842440108b0865d03244010ac0864c83244010d41754c83244010d81744c83244010
  | 1 => 0x568003a470020cb6b7002f98a000d000e2863080000000000000003b001848c6611142b936000303e001bc000b211042c0000001ae006c80000555900000925aa205462049d0944e4c800700f00000002e00000a4000023db80000039a2001a88c28001680000005b028fa9d5e2cd5e9000229261f4117c3c341400000841e85d9c5e5da24fedb18920eacb4f00000a90010000000000020bf40000004300000007000000ca59000000000002940030010999e00000e4a0004fac40a1513800e4950000000001e26000003e31c00a20000000a600000000000001a84d0000000005001000120023864001b80000004a001365801800008d0000158001d8bc001c552700e5d3d95c000000000006a0000000780032400080caacda003c80000a8003619446000a4988b2292c9e210000182d20680002060000400018140a01000000000000100004000000802028040202000180c00008100200030100a010100002030100c1a020602402000381c0000000080e0f000400400010000203000080000040001803a84815886250c43a88805886250c43a84825846150c43a90805846150c43a88825806050c43a90815806050c43b07815d94354843b04815d94354843b0b805d94354843b08805d94354843a0f865c54354843a0c865c54354843b0b805c54354843b08805c54354843d05711c54354843a0f865c14354843a0c865c14354843b07815c14354843b04815c14354843d09701c1435484390c8750d6154843d0943dc16154843d09431c16154843e05435846154843a6080584615484390c8750d6054843d0543dc56054843d05431c56054843e09435806054843a60815806054843e094354a6014443e09435496014443e054354a6114043e05435496114043a50805846154c42a50815806054c42a848158c6350842a888058c6350842b07815d95350842b04815d95350842b0b805d95350842b08805d95350842a0c865c55350842b0b805c55350842b08805c55350842d05711c55350842a0c865c15350842b07815c15350842b04815c15350842d09701c1535084290e8754d615084290c8754d6150842d0953dc16150842d09531c16150842a84835846150842e05535846150842aa080584615084290e8754d605084290c8754d6050842d0553dc56050842d05531c56050842a88835806050842e09535806050842aa0815806050842e095350a6014442e09535096014442e055350a6114042e05535096114042c0e765c85450f32a30805846155032a30815806055032a8481590644c832a8880590644c832b07815d9544c832b04815d9544c832b0b805d9544c832b08805d9544c832c0d761d9544c832a0c865c5544c832b0b805c5544c832b08805c5544c832d05711c5544c832a0c865c1544c832b07815c1544c832b04815c
  | 2 => 0x12c3a03158000068000000000000006966800ee0000000a2bd1b1694e68600b122645a2b836c66230c443f0884c4a5335801340000000000000124b8003180148d5001f8007a519b8000058214ccc80000000000000000005c00000202a00002976980000006b2e8e6004383000600000000000000048810000000da000ccce2b
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x80002c7100d2600d1e300cf8b0a74a92126430f0200811286c5001011117001c00c1c010804420658e00400e20b404965c47150d5210ea0120b88e2a1aa421d02259701c14354843a8048ae038286a90872049850d611855210f40286402c230aa421c82261435806054843d00a1902b00c0a9087404965c47154d4210aa0120b88e2a9a8421502259701c15350842a8048ae0382a6a10852049854d611854210b402a6402c230a8421482261535806050842d00a9902b00c0a1085404915d876551320ca81120bb0ecaa26419501259711c5544c832a80482e238aa899065408965c070551320caa0122b80e0aa2641948126154584614c832d00aa100b08c2990652089855160181320cb402a840ac030264196042197550c4344010a404b286b9086880218808650d7210d100430410cbaa842122008520259735084244010c40432e6a108488021840865d5320c9100429012cba2641922008620219744c83244010
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 40
  | 6 => 1752
  | 5 => 6659
  | 4 => 2307
  | 3 => 221
  | 2 => 35
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
  | 6 => packedAt gbK6 (54312+((h/584+packedAt gbK6 (47304+(h % 584)*12) 12) % 2544)*12) 12
  | 5 => packedAt gbK5 (284108+((h/2219+packedAt gbK5 (253042+(h % 2219)*14) 14) % 11698)*14) 14
  | 4 => packedAt gbK4 (122271+((h/769+packedAt gbK4 (113043+(h % 769)*12) 12) % 3349)*13) 13
  | 3 => packedAt gbK3 (13917+((h/73+packedAt gbK3 (13260+(h % 73)*9) 9) % 388)*9) 9
  | 2 => packedAt gbK2 (2551+((h/11+packedAt gbK2 (2485+(h % 11)*6) 6) % 43)*7) 7
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xf80ffffe03fffff03ffc3ff0fff87fe8e3f1ff
  | 1 => 0xfff01ffffc07ffffc0ffc3ff0fff87f71c7e3f
  | 2 => 0xffffe03ffff80fffff0003fff1fff8f81f8fc7
  | 3 => 0x3ffffff01ffffffc0001ffff1fe00ff8
  | 4 => 0xffffffc00000001ffffffffffe00001ffff000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0xa614282389122400b2c04b01258092061b0db
  | 1 => 0x10a4c50448724482c054415104a882430c562d
  | 2 => 0xa14289a89120e9155502226aa1355098168b46
  | 3 => 0x858b1631224481d9a69aa80881c6641da00db0
  | 4 => 0xc60c1821c3870e1e38e3338cc804401edb6000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 31 gbPos gbNeg, 0xeee8e880eee8e880eee8e880eee8e880eee8e880eee8e880eee8e880eee8e880eee8e880eee8e880eee8e880eee8e880eee8e880eee8e880eee8e880eee8e880, gbN, gbR, (fun _ _ => 0), gbI⟩
end PEqualNP.Outside.L_meta_12949
namespace PEqualNP.Outside.L_meta_12949
open PEqualNP.Outside.L_meta_12949.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 35 := block_range (n:=35) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 35 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_96 : Interval gbAtlas 3 96 96 := block_range (n:=96) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_192 : Interval gbAtlas 3 192 29 := block_range (n:=29) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 221 := (concat bgb_3_0 (concat bgb_3_96 bgb_3_192))
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
theorem bgb_4_2304 : Interval gbAtlas 4 2304 3 := block_range (n:=3) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 2307 := (concat (concat (concat (concat bgb_4_0 (concat bgb_4_96 bgb_4_192)) (concat bgb_4_288 (concat bgb_4_384 bgb_4_480))) (concat (concat bgb_4_576 (concat bgb_4_672 bgb_4_768)) (concat bgb_4_864 (concat bgb_4_960 bgb_4_1056)))) (concat (concat (concat bgb_4_1152 (concat bgb_4_1248 bgb_4_1344)) (concat bgb_4_1440 (concat bgb_4_1536 bgb_4_1632))) (concat (concat bgb_4_1728 (concat bgb_4_1824 bgb_4_1920)) (concat (concat bgb_4_2016 bgb_4_2112) (concat bgb_4_2208 bgb_4_2304)))))
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
theorem bgb_5_6624 : Interval gbAtlas 5 6624 35 := block_range (n:=35) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 6659 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_96) (concat bgb_5_192 bgb_5_288)) (concat (concat bgb_5_384 bgb_5_480) (concat bgb_5_576 bgb_5_672))) (concat (concat (concat bgb_5_768 bgb_5_864) (concat bgb_5_960 bgb_5_1056)) (concat (concat bgb_5_1152 bgb_5_1248) (concat bgb_5_1344 (concat bgb_5_1440 bgb_5_1536))))) (concat (concat (concat (concat bgb_5_1632 bgb_5_1728) (concat bgb_5_1824 bgb_5_1920)) (concat (concat bgb_5_2016 bgb_5_2112) (concat bgb_5_2208 (concat bgb_5_2304 bgb_5_2400)))) (concat (concat (concat bgb_5_2496 bgb_5_2592) (concat bgb_5_2688 bgb_5_2784)) (concat (concat bgb_5_2880 bgb_5_2976) (concat bgb_5_3072 (concat bgb_5_3168 bgb_5_3264)))))) (concat (concat (concat (concat (concat bgb_5_3360 bgb_5_3456) (concat bgb_5_3552 bgb_5_3648)) (concat (concat bgb_5_3744 bgb_5_3840) (concat bgb_5_3936 bgb_5_4032))) (concat (concat (concat bgb_5_4128 bgb_5_4224) (concat bgb_5_4320 bgb_5_4416)) (concat (concat bgb_5_4512 bgb_5_4608) (concat bgb_5_4704 (concat bgb_5_4800 bgb_5_4896))))) (concat (concat (concat (concat bgb_5_4992 bgb_5_5088) (concat bgb_5_5184 bgb_5_5280)) (concat (concat bgb_5_5376 bgb_5_5472) (concat bgb_5_5568 (concat bgb_5_5664 bgb_5_5760)))) (concat (concat (concat bgb_5_5856 bgb_5_5952) (concat bgb_5_6048 bgb_5_6144)) (concat (concat bgb_5_6240 bgb_5_6336) (concat bgb_5_6432 (concat bgb_5_6528 bgb_5_6624)))))))
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
theorem bgb_6_1728 : Interval gbAtlas 6 1728 24 := block_range (n:=24) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1752 := (concat (concat (concat (concat bgb_6_0 bgb_6_96) (concat bgb_6_192 bgb_6_288)) (concat (concat bgb_6_384 bgb_6_480) (concat bgb_6_576 (concat bgb_6_672 bgb_6_768)))) (concat (concat (concat bgb_6_864 bgb_6_960) (concat bgb_6_1056 (concat bgb_6_1152 bgb_6_1248))) (concat (concat bgb_6_1344 bgb_6_1440) (concat bgb_6_1536 (concat bgb_6_1632 bgb_6_1728)))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 6, 7),(inputs.getD 1 zero, 5, 7),(inputs.getD 2 zero, 3, 7),(inputs.getD 3 zero, 3, 11),(inputs.getD 4 zero, 3, 19)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 5 zero,inputs.getD 4 zero]
def fullWord : Sig := 0xeee8e880e880e880eee8e880e880e880eee8e880e880e880eee8e880e880e880eee8e880e880e880eee8e880e880e880eee8e880e880e880eee8e880e880e880
theorem fullBound (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have low := boundgb certgb
  have lift := lift_ok (u:=true) (ms:=fixRows 0 32) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 5 zero,19,51)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 5 zero,19,51)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008241280 * 2 ^ 32 + 3900762240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_12949.Model.Repr at out
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

def mono : List Gate := [⟨.or,[0,1]⟩,⟨.or,[2,3]⟩,⟨.and,[4,5]⟩,⟨.and,[0,1]⟩,⟨.or,[8,9]⟩,⟨.and,[8,9]⟩,⟨.and,[2,3]⟩,⟨.or,[11,12]⟩,⟨.and,[7,10]⟩,⟨.or,[13,14]⟩,⟨.and,[6,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241280 * 2 ^ 32 + 3900762240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241280 * 2 ^ 32 + 3900762240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_12949

open PEqualNP.Outside.L_meta_12949 in
theorem PEqualNP.Outside.L_meta_12949 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241280 * 2 ^ 32 + 3900762240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241280 * 2 ^ 32 + 3900762240) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound allgb)
