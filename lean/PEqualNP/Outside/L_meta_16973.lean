import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_16973.Model
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


end PEqualNP.Outside.L_meta_16973.Model

namespace PEqualNP.Outside.L_meta_16973
open PEqualNP.Outside.L_meta_16973.Model
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

def SBf (j : Nat) : Nat := [8, 6, 7, 7, 6, 6].getD j 0

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

end PEqualNP.Outside.L_meta_16973

namespace PEqualNP.Outside.L_meta_16973
open PEqualNP.Outside.L_meta_16973.Model
def s0K7 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s0K6 : Nat → Nat
  | 0 => 0xa2e00026262100b080110746181210060a8e340009b000000000012802078f941e14e8324000000000c9100000244e34000002400018000160000e00020200002023400d0000101ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s0K5 : Nat → Nat
  | 0 => 0x4817e53903bca7205794e40bea9c81dd53902baa7206fd0e40dea1c817e52902faa5206f90a40de214817e51902faa3206f90640de20c817e509037e81207ed0240bfa9a817c535037c86a06f10d40bfa92817c525037e84a06f50940bfa8a817c515037e82a06f50540fda0281be40502fca8205f94c40bea9881bf431037a86205f94840bea9081be421037884205f94440bea8881be411037882205f94040dfa0081fa401037a80207e50040bfaa6617e54cc37ca9984f95330beaa661bd54cc27aa9985f15330efa1e61dc43cc2fca5985f54b30ef99661dd32cc2fca3985f54730ef98e61dd31cc2fea9185f95230df2a4613e548c2faa9186f552309eaa4617c548c2faa7187790e30eea1c617e528c2faa518778ca30ee194617e518c2faa318778c630ee18c617e508c3be61187ecc230bfaa2617e544c2faa8985f15130efa1a61dc434c2fea4985f14930ef99261dd324c2fea2985f14530ef98a61dd314c3f66098778c130bfaa0617e540c2faa8185f15030bf29861de430c3ba86185f94830bea9061de320c3b864185f94430bea8861de310c3b862185f94030ef98061fa300c3ba60187e4c030bfaa6417e54c82faa9905f15320bfa9e417e53c82faa7905f14f20bf28e417d51c83de43907b48720bfaa4417e54882faa9105f15220bfa9c417e53882faa7105f14e20bea94417e51882faa3107b88620f610c417e50883de41107ec8220bfaa241bf544827ea8905f95120beaa2417c5448378a8904f15120bfa9a41df53482bea6905f94d20bea9a417c53483b8a6905714d20bfa8a41f751482eea2905f14520fa28a417451483de42907b48520fd90241ee20482fea8105f95020df2a0413e54082faa8106f550209eaa0417c54082fea6105f94c20ef298415e53082faa6107754c20aea98417c53082fca4105f94420fb288417651082faa2107d54420baa8841ee21083d842105f94020f790041fa20083da40107e48020bfaa6217e54c42faa9885f15310bfa9e217e53c42faa7885f14f10bfa96217e52c42faa5885f14b10fb10e21f521c42fea9085f95210beaa4217c54842fea7085f94e10bea9c217c53842fea5085f94a10bea94217c52842faa3087dc8610fa10c217e50843ee21087ec4210bfaa221bf544427ea8885f95110beaa2217c5444378a8884f15110bfa9a21df53442bea6885f94d10bea9a217c53443b8a6885714d10bfa9221ef52442dea4885f94910bea92217c52443d8a4885b14910fb10a21f521443f620887d84110bfaa0217e540437ca8084f95010beaa021bd540427aa8085f15010bfa98217e53043bca6085794c10bea9821dd53042baa6085f14c10bfa90217e52043dca4085b94810bea9021ed52042daa4085f14810bf28821f721043e842085f94010fb88021fa10043ea20087e44010
  | 1 => 0xf5350af8a6a17714d42ae29a85bf4350b7a86a17bd0942df212857f5150af8a2a15fd4142be282857e5410afca6217794c42af298857d5310bbaa6215754c42df21885bc4310afca4216fd0842f721085bd4210bda84215f94442bea88857e5010afaa0215fd5332bf2a6657d54ccaf8a9997790f32eea1e657e51ccafaa3995f94332bea86657f548cafca9195f55232be2a4657d538cbbe87197710e32bf29465df328cbde65195f94632bea8c657e508cafaa1195fd5132dfaa2653f544cafca8995f55132be2a265bc544ca78a8997790d32eea1a65ef324cbbc64995fd4532be28a657f504caf8a0995fd5032bf2a065be540ca7ca8195f55032deaa0653d540caf8a8195f94c32efa1865dc430cafca41977cc832f719065dd320cbda64195f94432bea88657e500cafaa0195f94f41bea9e83bf43d077a87a0df94b41bea9683be42d077885a0df94341bea86837d54906fca720df54e41df21c83bc43906fca520df54a41dfa1483bd42906fca320efd0641fba0c837e50906faa120dfd4d41efa9a835f53506f8a6a0f714d41ae29a83bf435077a86a0dfd4941be29283be425077884a0fdd0541df20a837f50506f8a0a0df95041bf29883de53106bca620df54c41eea98835d531077c8620ef10c41bf290837d521077e8420ef50841bf28883bf41107ec8220ef50441faa08837e50106faa020dfd5331bf2a6637d54cc6f8a998f790f31eea1e637e52cc6faa598f78cb31ee196637e50cc6faa198dfd5231bf2a4637d548c6f8a918df54e31efa1c63dc438c6fca518df54a31ef99463dd328c6fca318f7cc631fb98c637e508c6faa118dfd5131dfaa2633f544c6fca898df55131be2a263bc544c678a898f790d31eea1a637f524c6f8a498f78c931ee19263f7314c7bc6298dfd4131be282637f540c6fca818ef950319f2a0637d540c77aa818cf55031be2a0637e530c7be8618f710c31bf290637d520c7be6418f74c831bf28863df310c7ec6218f74c431fa988637e500c6faa018dfd5321bf2a643be54c867ca990df55321deaa6433d54c86f8a990dfd4f21bf29e43de53c86bca790df54f21eea9e435d53c86f8a790df94321bea86437f54886fca910ef952219f2a4437d548877aa910cf55221be2a4437f53886fca710f794e21af29c437d53887baa710d754e21be29c437d52886fca310fbc8621fb90c437e50886faa110dfd5121bf2a2437d54486f8a890dfd4d21bf29a437d53486f8a690fdc8521f710a437f50486f8a090dfd5021bf2a0437d54086f8a810dfd4c21bf298437d53086f8a610df94821bf28843ef21087ec4210fb48421fa90843e521086fca010df54021bf29e81de53d02bca7a05f54f40eea9e815d53d037c87a06f10f40bf296817d52d037e85a06f50b40bf28e817d51d037e83a06f50740beaa
  | 2 => 0x881900006896c968570000002290d0006d4000000005bcf297235a7387f96414e0004705f3f07f02422b0800012495c5204f0cb11e37806ca22122fa55c2e9ac44c0846c8001e07b80003c00c38cd8252528860929290628e49a9064022a9409bb41a00035a983129d4000000f2998689f20008c0000000d800000000434000000004c00008414d2fc8645881518876c8526434a1d0c51bd4e459c0000023e0014013927a9e908a1c0009f8cd00024c8540026905a20000104442000000440e6000560000e02bc158001988a4cb83b3860509619b170a489c0e22961e04f24314a324e9127522124b08b30fa9a0fd02301c2a4aca372820013700035c79c4421d00e5e10d82c3023092394c50e390e10563a0094730d51ba9fd0797f34020d170220005a8001300ca00000000116789058004062d8499be00076078a2d1b07b1101e01385b5190001ec074002250008bd318c31ea5492c91a0b26911e1313da254429fe0a07984d1403b803c9b198094a28768580482d4c7a672ca56c47a1046c774439b81ce0703d2621ae4bc55a6f4aa8392409f00000042170344448c101340494c0596e3500d8ef1f504e560f20bd2266ac001fb000508000fd1a65d4521051be7ac48062000454838174f6314258cf50a0080000000057c00179428984e50001901f0001710000fc000432d0638728f40f6001050004509440010023aa188c8c04669742a89906e8e8aa07f4704907c8e102092c2e1324b06e87da5f3800f434008000010b4010141902c0a00c0001c08000050040001004028010700c0c800000000000702c1e0000006c0b0100300403028060a00401001008030000f00001000000743700c0300403024040081f130000100e08c0800c04044020180704401000020280301c00038010cc00080010080000801004040000101c0903001058040040002801000000040f0400109c1100c16000040000403807000030000600c000040500007040000100400c00014010040401c01000120381c0040e0200a0180300000030080080001828014020240000005000040240400c0201800044010141203809008070142100426018240000c02c2d0000102c00018010000703c0400812000030ac000000d02400008010340200001022fca5a1df54b43bf28e877d51d0efca1a1df54343beaa4877e5390f7e8721f7d0e43bf294877d5290efca321df54643bf284877d5090fbe86a1ef90d43bfa92877c5250efea2a1df14543bfa82877c5050efca821df94c43dfa1887de4310f7a8621f750c43cea18877e5210efaa421df94443bea88877e5010efaa021df94f42bea9e85bf43d0b7a87a15f94742bea8e857e50d0afaa1a15f55242bf29c857d5390b7c87216f10e42bf29485bf4290bde85215f94642bea8c857e5090afaa1215fd4d42efa9a855
  | 3 => 0x20927c6000284d1f06a50219f0b469ce30b72749b49428c19c5d03f1f40549390621e00600079864388461250de3242742a04139e11c0226c0ea5552f0cd4469ad0b8bc0e4a2d3816b0a44d0ff84c104598e418351a95cbd1b73321a4571601502c00017c3267641f1ef136000e48bb3c24408120811a2808581a0de4ad1a0ad12c18c000331024dc001f317e0612d23503e1b8742820006440419e1d83c93c04238aa0c9f9da2c6a3d0380d11843cfe8ca0a6614b4a5000044430819316348148a33281b51e83039616cfb9b63c66a8d88c65122e845000196284bb15d0003a4060000000007b8001a874d4a8fc49a890970dc400538e39f102c000000000742600000003c7d8c80003a22f8449510000000000044e654001bf4267a8389e94ec908809d61ac3b93b948238a4d22a444e8430908e01b461d4b02e0243a8a99030ee48c4a0004f8000338461de438dc8fe3be0285a0390bc0000015a0ec0bd032400408b0d929728c4cc848113f27a0492051a05dd389d734c674000003aa6cc0002600019800000182004530004449e40015653246cf8145000950ce0092926307d13b0002c800216254001440003a8458489b430c13c43000228620c6a5648c000a50002865cd150000c0000d0a3f06a70463a5c0000000000043e0002724f0000000026a000144000002bc0000023e0009053e80034651d1d9af0000e0e60b9508734000000009953997b1b66103514f498001470971444888b96c0003ac000000008c4900282a05
  | _ => 0
def s0K4 : Nat → Nat
  | 0 => 0x1518825f63546209718d518823e64951209798e544825d63951209d9865448275619512097d8d544825c63551209dd85544827461551208f994544831f54d4d20c7153534823e6494d208f592534825e6394d209d98653482756194d208fd91534823c6454d209dd8553482746154d2097994534831f5414d20c7150534833754d4520cd153514835753d4520d514f51483375414520cd15051483575314520d514c514826e65c8520d914721483645148520d9146204825e63d50209758f540827661d50209d587540823d65950208f990540825e63150209758c540827661150209d584540823e64d4c208f593530827661d4c209d587530825d6594c20c7952530831d5494c20c7951530831d5454c208f990530823d6414c209798c53082766114c209d58453083365494420cd55251083565394420d554e51083365454420cd55151083565354420d554d510826d6588420d954621083655108420d9547200826f6548020b9185200836551480209ed95200825f63553109718d54c425e63153109758c54c423f6454f108f19153c423e6414f108f59053c423e64d4b108f59352c425e63d4b109758f52c423e6494b108f59252c425e6394b109758e52c436452487109798f548425d63d52109798e548425d63952108f993538423d64d4e108f992538423d6494e108fd91528423c6454a1097d8d528425c6354a108f990528423d6414a109798c528425d6314a10d9d48218423e64951109798e544425d63951109b98a544426d629511097d8d544425c63551109bd89544426c62551108f994544431f54d4d10c7153534423e6494d108f592534425e6394d109b98a534426d6294d108fd91534423c6454d109bd89534426c6254d1097994534431f5414d10c7150534432f54d4910cb153524434f53d4910d314f524423e64949108f592524425e63949109758e524426e62949108fd91524423c645491097d8d524425c63549109dd85524426e6514910cbd50524432c5414910d3d4c524434c5314910d958452442766588510d914a21442746548510d9149214436452841109798f540425d63d50109b98b540426d62d50108f596540423e64150109798c540425d63150109b988540426d62150108f993530423d64d4c109b98b530426d62d4c1097596530431e5494c10c7552530431e5454c10c7551530423e6414c108f590530425e6314c109b988530426d6214c108f993520423d64d48109798f520425d63d48109b596520432e5494810cb552520434e5394810d354e520432e5454810cb551520434e5354810d354d520436461548108f990520423d64148109798c520425d63148109b988520427661148109d597210436552c84109d59421043655208410d954b100427965840109dd9510042e46244010d9549100427b6544010
  | 1 => 0xc71c5450d31c7152324c65e650c931a7590324c71c540c931c7152314c63d6595031c718d540c63e64150319798c540c65d65d0c31c7553430c65d6510c31c7550430c71d54cc83197d95320c69c644c831c7551320c71d54cc43197d95310c69c644c431c7551310c677654c4319798f54c865d63d53219798c54c865d63153218f99353c863d64d4f21c795253c871d5494f21c795153c871d5454f218f99053c863d6414f219798f548865d63d52219798c548865d63152218f993538863d64d4e21c7952538871d5494e21c7951538871d5454e218f990538863d6414e2197d8d544865c63551219ed81544867860551219798c544865d63151218fd91534863c6454d219ed8153486786054d218f990534863d6414d218f990504863d64141219798c504865d631412197d8d540865c63550219798c540865d63150219e980540867960150218fd91530863c6454c218f990530863d6414c219e98053086796014c218f992520863d64948219798e520865d63948218f992510863d64944219798e510865d6394421b958a210866f65484219dd9521086e76548421d9d9521086e460484218fd91500863c645402197d8d500865c6354021d9485500871d5390f40c754c43d031d53d0b40a718d42d031d5350b40c754f41d029c6350740c754d41d031e53d0e40c794d439031e5390a40a758c429031e5310a40c794e419029d6310640c794c419029d63d0240c794f409023e6510d409798c525025d63149408f997425029c63509409798c515025d63145408f997415029c6350540a798e405023f6550c4097d8d521025c63548408f596421029d631084097d8d511025c63544408f596411029d6310440a758f401023f65500409ed95401031c6355330c755343cc31d5410f30c755332cc29c644cb30c755132cc31d54cc730a719131cc31d544c730c758e548c31e5490e30c7951438c31e548ca30a7590328c31e540ca30c7952318c29d640c630c7950318c29d64cc230c7953308c25d63951309bd89544c26c62551309dd85544c274615513097997434c25e6510d30c7550434c23e64149308f590524c25e65cc930a7191324c23e64145308f590514c25e65cc530a7191314c29e648c1309798f540c26e62150309b588540c27661150309d584540c23e6494c308f592530c25d6590c3097d95430c31c5450c308fd91520c23c645483097596320c29d640c8308fd91510c23c645443097596310c29d640c4308f992500c23d6494030a7593300c25f654c0309ed95300c25f63553209718d54c825e63153209758c54c823f6454f208f19153c823e6414f208f59053c823e64947208f59251c825e63947209758e51c825e63d52209758f548825e63952209758e548823e64d4e208f593538823e6494e208f592538823f64546208f19
  | 2 => 0xc02ee0010f136000000000ba00055c000001e800000018000344000d900000000000000000000a000026c1f85b0fe000c00003540000000e000000b402c1ac0003c0e00000009d00036000000075000568000442e0238a0800000000000060621ac0004a3b2070898a53ce7480017c1782e4940413aa80c000132a0758001e60000007d1f301a320001b60441900002a0003f4000003220010d80000012c000003162109299b4084102c954420080ce1dc2fc548f18273e8084789de00037c4e8000247c0d78510e0000da000000000f40fc000044c293e0000000005e32000c0000005004030000300002014080100707400000270000002809014020280000005000160100300401000030000e00407000030100900005000300dc0a004130080500003004020040101400074000340000c0201400014080580000801020000c00010c000000001401008080180502401004080041d0200201800008060000102806000080000000800010070a401000010040400c00004000640100c000000101c0a00806000270080400003000040100100002004000540308804010020040000c150240100404014060080700003000000100200012014000080a00409000020029d6490c438fd954310e5f6550c43a7d954310f1f6550c43a71894310e9c6150c43a7d814310f1d4354843c750d5110f1d439404397d8d51d0a5c63547429798e50d0a5d63943429798e5190a5d639464297d8d5090a5c63542428f9974350b1c53d0d42c714d4350b1c53909428f5964310b1d5390c42c754c4310b1d53d08428fd954210a9c6350842c754d4210a6f65508429d98454cca756115332c715143cca3f64547328f19151cca3e64943328f59250cca7661d52329d587548cb1f5410e328f992518ca3d64946328fd91508ca3c64542328f992544ca5f63551328f994544cb1d631513297996434cb1c5490d3297195434cb1c5450d32c7152324ca3d6595032c718d540ca3e64150329798c540ca5d65d0c32c7553430ca5d6510c32c7550430cb1d54cc83297d95320ca9c644c832c7551320ca6f654c83297d8d52d065c6354b41a758c42d065e63943419758e50d065e6394a419758e529069c6350a4197d8d509065c63542418f997435071c53d0d41c714d435071c53909418f994425069d6310941c714c425071c53905418f596431071d5390c41c754c431071d53d08418fd95421069c6350841c754d421071d53d04418fd95411069c6350441c754d411067765504419b98854cc66d6215331c715143cc63f6454b318f19152cc69d640cb318f99250cc63d64943319b98b548c66d62d5231c7d50438c63e6494a318f592528c69c644ca318fd91508c63c64542318f992544c65f63551318f994544c71d631513197996434c71c5490d3197195434
  | 3 => 0x520298010002605b00000056d0406209e068858e32dc00c0007b3a6000e1800004184000da0000003e8360000006600038258c000002c863c5c0003a8864c99992764147405c1d24c0531453f023cac20a16a6581e9b72d83acf68d336a01c890103be7244112c27281cb39b11f02506487737427c8e9a50d40c8c18f938e6388e0833185880f88027a3901a1422a2000579183484fc059142120a00008a3f23880010f0b0000001001b884c000000003341c97844a1cc00000086774000000001689100504a408118bd1a825459a021ee8146e8000000000016632a4180006e448000d19ff0000000615f25c0000013543e688e01ae0aa0010581d01e0a4ce80035a00000000262000590b40a0000000a4240000001712d6610338f50785d8f50000a45bca1a060000008b80034276848a0c232898a480037c7c8aa92b35650044186156880681f11208882680000069ce1000188458580c50da000eba18000000a3000000000000000003b00008b39c0c004800000000dc9bb0007dc7500000000000000000000540000006c80a017236268002144222c40000a00039cc10972ca444f70600000009380033482486a152ac54cd48000000000007a41a000679f6388000be80039a6cd0b0002143c891800000000a210702c3cccb8bb2ba100f09eb15a000000863ca054e591f33c000de1260d22884f1bf15273c1599f1421589b9b839024c000ce2d20e0cc15e000378bc9344421a0000ae0ae000000000000000000037a304001e929c00084000000000330450007447f9ac22a7280004e000730c48001f636cca00042e000000000f2584240003f6000000000000008617512c570c08000f80001d0001184c80000810e0ec001732d4328bd8bf0be4a80000005e4e0948003147bc0000010200000000434000d30fe1da3bc1a9872025303881e07c3d85b8e509223463a1d29e634238333b040ced82614e7140002d000790120be31006c908041cc30c490c62c032c560762b2000690000001c8000000000006b9fc10a83c001fd00052c9e2230323c10714a0fc801090002da438f000006e000ba0000c6000e30000840002a0892664908d02e3ea2643600018451c978001aa5e800201340000770000007400005d350000378653d8000c9000000870230a30001300009c25a1d000110000000000e10000000011e3f4534001721b0000000003c42a8ff17f00
  | _ => 0
def s0K3 : Nat → Nat
  | 0 => 0x2670000a00400052860000608c5888927a00006a4390010002811431c94354843a28e2a1aa221d1b7050e5010e8ab88a8a1e65459c75410e32838ecaa2641950d7215143cc687396a821c63075d8540c931838ecaa26418c1c76551310c60e3b2a899661071d9544c73083aed2a0651841d76950318c20ebb4a998461431c95410d30a28e2aa0869850d72151430c28ab88a8a1861191d95244010
  | _ => 0
def s0N (k : Nat) : Nat :=
  match k with
  | 7 => 1
  | 6 => 40
  | 5 => 666
  | 4 => 551
  | 3 => 21
  | _ => 0
def s0R (k i : Nat) : Nat :=
  match k with
  | 7 => packedAt s0K7 (i*5) 5
  | 6 => packedAt s0K6 (i*16) 16
  | 5 => packedAt s0K5 (i*27) 27
  | 4 => packedAt s0K4 (i*38) 38
  | 3 => packedAt s0K3 (i*49) 49
  | _ => 0
def s0I (k h : Nat) : Nat :=
  match k with
  | 7 => packedAt s0K7 (6+((h/1+packedAt s0K7 (5+(h % 1)*1) 1) % 2)*1) 1
  | 6 => packedAt s0K6 (731+((h/13+packedAt s0K6 (640+(h % 13)*7) 7) % 69)*7) 7
  | 5 => packedAt s0K5 (20202+((h/222+packedAt s0K5 (17982+(h % 222)*10) 10) % 800)*11) 11
  | 4 => packedAt s0K4 (22768+((h/183+packedAt s0K4 (20938+(h % 183)*10) 10) % 800)*11) 11
  | 3 => packedAt s0K3 (1064+((h/7+packedAt s0K3 (1029+(h % 7)*5) 5) % 30)*6) 6
  | _ => 0
def s0Pos : Nat → Bits
  | 1 => 0xffffc1fffffff03ffff83ffc1fffffcf8f1ff
  | 2 => 0xf03fffe07ffc3ffc1f07fc3ffe1fc0ff473e73
  | 3 => 0xffc0ffff81ffc3ffe007ffc3ffe1ff0387cf9c
  | 4 => 0xfffffe0003fffff80003fffe0003f80fe0
  | 5 => 0xffff0000000003fffffffffc00000003fff000
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x8104044410480000a5090044802254501850a5
  | 2 => 0x248a48832490612c0a42a429521482a9432652
  | 3 => 0x429291090d2206554084ca8265412a0a858b18
  | 4 => 0x6b2ce252483aab9a73d06223b9980c33e80de0
  | 5 => 0x8c30c39c71c333e39ce77330311030c3f6f000
  | _ => 0
def s0Atlas : Atlas := ⟨7,rawDecor 62 s0Pos s0Neg, 0xfcccfcc0fcc0ccc0fcccfcc0fcc0ccc0fcccfcc0fcc0ccc0fcccfcc0fcc0ccc0fcccfcc0fcc0ccc0fcccfcc0fcc0ccc0fcccfcc0fcc0ccc0fcccfcc0fcc0ccc0, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_16973
namespace PEqualNP.Outside.L_meta_16973
open PEqualNP.Outside.L_meta_16973.Model
def s1K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s1K4 : Nat → Nat
  | 0 => 0x80bf43bd43
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 2
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (i*5) 5
  | 4 => packedAt s1K4 (i*16) 16
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s1K5 (6+((h/1+packedAt s1K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s1K4 (34+((h/1+packedAt s1K4 (32+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0x80ffffc0fffffe07ffffc0fffe07fffcf8fe3f
  | 2 => 0xff03ffff01fc0ff83e0fff07fff83e034f1fcc
  | 3 => 0xfffc0ffffe000fffc00ffff83fffc0038fe3f0
  | 4 => 0xffffffffffffff000003ffffffff003ff
  | 5 => 0xfffff00000000fffffffffffc0000003fffc00
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xa6082046244842014a12c42946214a98186e15
  | 2 => 0xa58c48a1c915658168555259aa92c294b16cc
  | 3 => 0x14316914483a6aaac109a6b12d3588528da370
  | 4 => 0x58a28e2091230d34a5a0308431c63163e001aa
  | 5 => 0x60c30c38e1c38dc739ce38c601842183f6d800
  | _ => 0
def s1Atlas : Atlas := ⟨5,rawDecor 61 s1Pos s1Neg, 0xfaaafaa0faaa0000faaafaa0faaa0000faaafaa0faaa0000faaafaa0faaa0000faaafaa0faaa0000faaafaa0faaa0000faaafaa0faaa0000faaafaa0faaa0000, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_16973
namespace PEqualNP.Outside.L_meta_16973
open PEqualNP.Outside.L_meta_16973.Model
def s2K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s2K5 : Nat → Nat
  | 0 => 0x90c00b800000296188c00f0040e803c00c00340101100002241a38a014c492a726090a2066ca993e2ce000e2050600e58000818419b000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s2K4 : Nat → Nat
  | 0 => 0x1d8000008a36a019b04afdbbe00c9380003c33914d802c00002ab3abc2003e04000182498b005c03d1a00f2e00e80000ea4a942cb4000420101a3000d8078018801c0ce2248a8834100891950e13000f02081010000088040418008002840604082bda8287785050edca421db54843bba8a85745150abca6215754c429faa2653c544caeea2995d14532bda826578504ca7ca8194f55032b7a92836c52506f4a020de540419f2a6633d54cc6dca598db54b319f2a4633d548c6f4a118de542319faa2433c544867ca810cf55021af298435d53086f4a010de54021afa9a815c53502eca2205d544409faa2613c544c27ca8184f55030b7290616d520c2eca2185d544309f2a6413d54c82bca7905754f209f2a4413d54882eca3105d546209faa2213c54442bea6885714d10b7a92216c524427ca8084f55010
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 40
  | 4 => 64
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s2K6 (i*5) 5
  | 5 => packedAt s2K5 (i*16) 16
  | 4 => packedAt s2K4 (i*27) 27
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s2K6 (6+((h/1+packedAt s2K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s2K5 (718+((h/13+packedAt s2K5 (640+(h % 13)*6) 6) % 53)*7) 7
  | 4 => packedAt s2K4 (1875+((h/21+packedAt s2K4 (1728+(h % 21)*7) 7) % 92)*7) 7
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0x7ff03fffff8307fe0ffc1ff0ffffe018e73fc
  | 1 => 0xf83ffc0fc1ffff83ff07fe0ff0f01ffef38ccf
  | 3 => 0xfffffff001fffffc0007ffffff001fff03ff0f
  | 4 => 0x3ffffffe003ffffff8000fffffe003fc0ff0
  | 5 => 0xffc0000000003ffffffffff000000003fff000
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0x309118a290425014a849d0930194d21886315c
  | 1 => 0x52922864129212816942528510a154a8b284c5
  | 3 => 0xa1245101a524252c1084a52aaa028953015b0a
  | 4 => 0xc52882492034a9ca5290210ccc4b0063580ea0
  | 5 => 0x630e38e39c73e739ce739c0888c1183efe000
  | _ => 0
def s2Atlas : Atlas := ⟨6,rawDecor 59 s2Pos s2Neg, 0xeeeeee00eeaacc00eeeeee00eeaacc00eeeeee00eeaacc00eeeeee00eeaacc00eeeeee00eeaacc00eeeeee00eeaacc00eeeeee00eeaacc00eeeeee00eeaacc00, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_16973
namespace PEqualNP.Outside.L_meta_16973
open PEqualNP.Outside.L_meta_16973.Model
def s3K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s3K5 : Nat → Nat
  | 0 => 0x40e225c59e004c00c30587840000005248ce9a2001300000000d00500a12a011250418d83321d200389c01f14804831541c8153003042000ff43fe43fd43fc43ff42fe42fd42fc42ff32fe32fd32fc32ff41fe41fd41fc41ff31fe31fd31fc31ff21fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s3K4 : Nat → Nat
  | 0 => 0x962e401616c02252089aad3a00a876c09e8d3085bac00bc000706c7ae00015994cc841e3e9c033180000000008a33419e3b144922a7e0da3e2680a28745d4801c1409c29221420000001033a84a805c002030608101bda8287785050edca421db54843bba8a85745150abca6215754c429faa2653c544caeea2995d14532bda826578504ca7ca8194f55032b7a92836c52506f4a020de540419f2a6633d54cc6dca598db54b319f2a4633d548c6f4a118de542319faa2433c544867ca810cf55021af298435d53086f4a010de54021afa9a815c53502eca2205d544409faa2613c544c27ca8184f55030b7290616d520c2eca2185d544309f2a6413d54c82bca7905754f209f2a4413d54882eca3105d546209faa2213c54442bea6885714d10b7a92216c524427ca8084f55010
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 40
  | 4 => 64
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s3K6 (i*5) 5
  | 5 => packedAt s3K5 (i*16) 16
  | 4 => packedAt s3K4 (i*27) 27
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s3K6 (6+((h/1+packedAt s3K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s3K5 (718+((h/13+packedAt s3K5 (640+(h % 13)*6) 6) % 53)*7) 7
  | 4 => packedAt s3K4 (1875+((h/21+packedAt s3K4 (1728+(h % 21)*7) 7) % 77)*7) 7
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0x7ff03fffff8307fe0ffc1ff0ffffe018e73fc
  | 1 => 0xf83ffc0fc1ffff83ff07fe0ff0f01ffef38ccf
  | 2 => 0xfffffff001fffffc0007ffffff001fff03ff0f
  | 4 => 0x3ffffffe003ffffff8000fffffe003fc0ff0
  | 5 => 0xffc0000000003ffffffffff000000003fff000
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0x309118a290425014a849d0930194d21886315c
  | 1 => 0x52922864129212816942528510a154a8b284c5
  | 2 => 0xa1245101a524252c1084a52aaa028953015b0a
  | 4 => 0xc52882492034a9ca5290210ccc4b0063580ea0
  | 5 => 0x630e38e39c73e739ce739c0888c1183efe000
  | _ => 0
def s3Atlas : Atlas := ⟨6,rawDecor 55 s3Pos s3Neg, 0xeeeee0e0eaeac0c0eeeee0e0eaeac0c0eeeee0e0eaeac0c0eeeee0e0eaeac0c0eeeee0e0eaeac0c0eeeee0e0eaeac0c0eeeee0e0eaeac0c0eeeee0e0eaeac0c0, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_16973
namespace PEqualNP.Outside.L_meta_16973
open PEqualNP.Outside.L_meta_16973.Model
def s4K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x92298007bf41bd41fb40f840fa10f910
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x202e2a2206c50510
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 6
  | 3 => 2
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (i*5) 5
  | 4 => packedAt s4K4 (i*16) 16
  | 3 => packedAt s4K3 (i*27) 27
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s4K5 (6+((h/1+packedAt s4K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s4K4 (102+((h/2+packedAt s4K4 (96+(h % 2)*3) 3) % 8)*4) 4
  | 3 => packedAt s4K3 (56+((h/1+packedAt s4K3 (54+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xfc0ffe03f07e0c3f0f87fe1ff0f81f02279ecc
  | 1 => 0x7ff03fffffffffc00ff83fe0fffffffc38e3ff
  | 2 => 0x7ffffffc007ffffff0003fffff001fffc0ff0f
  | 3 => 0x80003fffff800fffffffc000ffffe003ff03f0
  | 5 => 0xffffc00000000fffffffffff00000003fffc00
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x2561a238aa955c0b43c54f1578c8d91a238ecc
  | 1 => 0x824a4490821088004cc13301192524828a055
  | 2 => 0x30c208906348455550012446aa410cb2c0570a
  | 3 => 0x228b1122420c666669118004cc6588235503a0
  | 5 => 0x430c21c38c718bb88e663998008610c1bef800
  | _ => 0
def s4Atlas : Atlas := ⟨5,rawDecor 47 s4Pos s4Neg, 0xfee0fee0ccc0ccc0fee0fee0ccc0ccc0fee0fee0ccc0ccc0fee0fee0ccc0ccc0fee0fee0ccc0ccc0fee0fee0ccc0ccc0fee0fee0ccc0ccc0fee0fee0ccc0ccc0, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_16973
namespace PEqualNP.Outside.L_meta_16973
open PEqualNP.Outside.L_meta_16973.Model
def s5K5 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x8fb40f840
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 5 => 1
  | 4 => 2
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 5 => packedAt s5K5 (i*5) 5
  | 4 => packedAt s5K4 (i*16) 16
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 5 => packedAt s5K5 (6+((h/1+packedAt s5K5 (5+(h % 1)*1) 1) % 2)*1) 1
  | 4 => packedAt s5K4 (34+((h/1+packedAt s5K4 (32+(h % 1)*2) 2) % 3)*2) 2
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xe0ffffe03e1f087c3c7f8ffffc3c0f020cfecc
  | 1 => 0xff03e1ffffffff803f87f0e03ffffffc3333ff
  | 2 => 0xfffc01ffc01fffffc007ff003fc00fffc3c30f
  | 3 => 0x1ffffe00ffffff800003ffff003fc03f0
  | 4 => 0xfffffe0000000fffffffffffc0000003fffc00
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x2618d02384a2580d0c2985239e24691a0456cc
  | 1 => 0x42480244900801001482904484492248113055
  | 2 => 0x8c2154890cd44ab5402526092aa08cb2c2c30a
  | 3 => 0x18b2991228866cd9a93004123332c8236c03a0
  | 4 => 0x10c3001c311887623246489c000300c1bba800
  | _ => 0
def s5Atlas : Atlas := ⟨5,rawDecor 31 s5Pos s5Neg, 0xfeeaccc0feeaccc0feeaccc0feeaccc0feeaccc0feeaccc0feeaccc0feeaccc0feeaccc0feeaccc0feeaccc0feeaccc0feeaccc0feeaccc0feeaccc0feeaccc0, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_16973
namespace PEqualNP.Outside.L_meta_16973
open PEqualNP.Outside.L_meta_16973.Model
def gbK9 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK8 : Nat → Nat
  | 0 => 0xa401a00816803a0c712664410050dca001e0000800d921362b1a090a112ae008c0003600080000178b0cc800a7000b077279d9500d402220c132100a8c1c745c6273e34c8000000000000000560c381821404000040850002380850000001007fd5001fe54007f55001fc54007fd4c07fe53007f54c07fc53007fd0c07fe43007f50c07fc43007fd4805fe52007f54805fc52007fd0805fe42007f50805fc4201ffcc805fe32007f4c805fc32007fd4401fe51007f54401fc51007fd0401fe41007f50401fc4101ffcc401fe31007f4c407fc31017fc8401fe21007f48405fc2100ffd4003fe5000ff54003fc5000ffd0003fe4000ff50003fc4000ffcc003fe3000ff4c003fc3000ffc8003fe2000ff48003fc2000ffc4003fe1000ff44003fc10
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2620bbfd813105ffcc098806fe604c417feb02620bbf5813105ff8c098806fc604c417ffa82620bff9413105ffaa09882ffc504c417ffa02620bff9013105ffa809882ffc404c407ff9826203ff8c13101ffa609880ffc304c417ff902620bff8813105ffa409882ffc204c409ff882620bff8413105ffa2098813fc104c409ffb2c4204bfd9621027fccb10822fe6588409feb2c4200bf59621027f8cb10812fc6588409ffb244204bfd9221027fcc91081efe6488409feb244200bf59221027f8c910812fc6488401ffaa44200ff95221007faa910803fc5488409ffb1c4204bfd8e21027fcc71080efe6388409feb1c4200bf58e21027f8c710812fc6388401ffa9c420aff94e21007faa71082bfc5388401ffa1c420aff90e21007fa871082bfc43884057eb144202ffd4a21017fca51080bfd5288405fe2944202ffd0a21017fc851080bfd4288405fe2144202ffcca21017fc651080bfd3288405fe1944204bf98621027fea310813fe5188409fea8c4204ff14621027fe8310813fe4188409fea0c4204ff10621027fe6310813fe3188409fe98c4204ff0c621027fe4310813ef2188405fb90c4204ff08621027e84310813ff60884097fb044204ff9822100dfcc110813fd60884137eb044204ff1822100df8c110827ff5088413ff2844209ff5422104ff8a110827ff4088413ff2044209ff5022104ff88110827ff3088413ff1844209ff4c22104ff8611080bff2088405ff1044202ff48221017f84110813ff1088409ff0844204ff44221027f82110803ff65484017fb2a4200ff99521045fcca90803fd65484017eb2a4200ff19521045f8ca90803ff64484017fb224200ff9912103dfcc890803fd64484017eb224200ff1912103df8c890803ff5448401ff2a24200ff55121007f8a890803ff63484017fb1a4206ff98d2101dfcc690803fd63484017eb1a4206ff18d2101df8c690803ff534840dff29a4200ff54d21037f8a690803ff434840dff21a4200ff50d21037f88690812ff6248405ffa924202ff94921017faa49080bfc5248405ffa124202ff90921017fa849080bfc4248405ff9924202ff8c921017dc649080bfd3248401f69924202ff0c921015fec290803ff5148409ff28a4200ff54521027f8a290803ff4148409ff20a4200ff50521027f8829081bff3148409ff18a4200ff4c521027f8629080bff2148405fb90a4204ff88521027dc4290813fc2148409f610a4202fd0852102ffec090816ff604840bff3024201bf9812102ffac090816fd604840bfe3024201bf1812102ffea090817fe504840bfea824205ff1412102ffe8090817fe404840bfea024205ff1012102ffe6090817fe304840bfe9824205ff0c121017fe409080bfe2048405fe9024202ff08121027fe2090817fe104840bfe8824204ff04121
  | 1 => 0xafe6210409feb108200bf58841027f8c420812fc6210401ffa908210ff94841007faa420843fc521040fffa108207ff9084103ffa842081ffc4210423ff9908210ff8c841007fa6420843fc32104097f3088204ffd4441027fca220813fd5110409fe2888204ffd04410277e8220813fe4110409fb2088204ff504410277a822081ff54110409ff9888204ff0c441027fe4220813fc2110409ffb008204bfd8041027fcc020806fe6010409feb00820fbf58041027f8c020806fc601041fffa80820fff9404107ffaa02083ffc501040fffa008207ff9004103ffa802081ffc401041fff980820fff8c04107ffa602083ffc301041fff900820fff8804107ffa402083ffc2010409ff8808204ff84041027fa2020813fc1010409ffb2c6204bfd9631027fccb18822fe658c409feb2c6200bf59631027f8cb18812fc658c409ffb246204bfd9231027fcc91881efe648c409feb246200bf59231027f8c918812fc648c401ffaa46200ff95231007faa918803fc548c4077eb1c6203ffd4e3101ffca71880ffd538c407fe29c6203ffd0e3101ffc871880ffd438c407fe21c6204ffd8a31027fcc51880afe628c409feb146200bf58a31027f8c518812fc628c401ffa94620eff94a31007faa51883bfc528c401ffa14620eff90a31007fa851883bfc428c407ff9946203ff8ca3101ffa651880ffc328c4097f30c6204ffd4631027fca318813fd518c409fe28c6204ffd0631027fc8318813fd418c409fe20c6204ffcc631027be631880ff7318c409fe18c6204fd0c631027fe4318813fc218c409ffb046204bfd8231027fcc118806fe608c409feb04620dbf58231027f8c118806fc608c41bffa84620dff9423106ffaa118837fc508c41bffa04620dff9023106ffa8118837fc408c407ff9846203ff8c23101ffa611880ffc308c41bff904620dff8823106ffa4118837fc208c409ff8846204ff84231027fa2118813fc108c401ffb2a6200bfd9531007fcca98822fe654c401feb2a6200bf59531007f8ca98822fc654c401ffb226200bfd9131007fcc89881efe644c401feb226200bf59131007f8c89881efc644c401ffaa26200ff95131007faa898803fc544c4097fb1a6203ffd4d3101ffca69880ffd534c407fe29a6203ffd0d3101ffc869880ffd434c407fe21a6200ffd8931005fec498833fe624c4057f3126200ff58931067f8c49880afc624c401ffa92620cff94931007faa498833fc524c401ffa12620cff90931007fa8498833fc424c407ff9926203f7cc93101ffc649880ffd324c401ee9926203ff0c93101dfec298803ff514c409ff28a6200ff54531027f8a298803ff414c409ff20a6200ff50531027f8829880fff314c407fb98a6204ff8c531027bc6298813fc314c409ee18a6203fd0c531067fe4298813fc214c417ffb
  | 2 => 0x410c7fa21a0813fc10d0409ffb2c8204bfd9641027fccb20822fe6590409bf32c82009f99641027facb20802fd6590409beb2c82009f59641027f8cb20812fc65904257eb248200ffd524103ffca920803fd549040ffe2a48204ffd8e41027fcc72080efe6390409feb1c8200bf58e41027f8c720812fc6390401ffa9c8217ff94e41007faa72085ffc539040fffa1c8217ff90e41007fa872081ffc4390409ffb148204ff98a41015fcc520813fd62904017eb148204ff18a41025f8c520803ff529042dff2948200ff54a410b7f8a52081fff429042dff2148200ff50a4103ff8852085fff329042dff1948200ff4ca410b7f86520812fe6190409ffa8c8204ff94641027faa320813fc5190409ffa0c8204efd064103fee8320813ff3190409fe18c8204ffc8641027f84320813ff60904097fb048204ff9824100dfcc120813fa60904037d3048204ff582410adfac120813f960904017cb048204ff1824100df8c120857ff509042bff2848215ff542410aff8a12081fff409042bff2048215ff5024103ff88120857ff309042bff1848215ff4c2410aff86120857ff209042bff1048215ff482410aff84120813ff1090409fb8848204ff84241027fa2120857f51090409fe0848200ffd9541005fecaa0803fe65504117f32a8200ff59541005facaa0803fc65504117e32a8200ffd514103ffca8a0803fd545040ffe2a28200ffd8d41005fec6a0853fe63504077f31a8200ff58d410a7f8c6a080efc6350401ffa9a8214ff94d41007faa6a0853fc535040fffa1a8200efd0d410a7fc86a0803fd4350401dea1a8207ff10d41007fec4a0802ff6250427ff3128202bf98941007fac4a084ffc62504057e3128200ffd494109ffca4a0803fd5250427fe2928207ffd09410077e84a084ffe4250401fea128200ef5094103ff884a0853ff3250427ff1928200ff4c94109ff864a0803ff5150409ff28a8200ff54541027f8a2a081fff415040ffba0a8204ff905410277c82a0853ff3150409fe18a8213ffc8541027f842a084bff60504257fb028212ff9814100dfcc0a084bfd60504257eb028212ff1814100df8c0a084bff5050425ff2828212ff54141097f8a0a081fff4050425ff2028212ff5014103ff880a084bff3050425ff1828212ff4c141097f860a084bff2050425ff1028212ff48141097f840a0813ff1050425fb8828212ff84141097fa20a084bf51050409fe0828204ffd9441025feca20813fe65104117f3288204ff59441005faca20813fc65104097e3288207bf9904103ffea82081ffe541040ffeaa08207ff15041027fec620813fe63104077f3188204ff58c41005fac620813fc63104097e3188200ffd4c4108ffca620803fd5310423fe2988207ffd0c4103ffc862081ffd431040ffe2188204ffd8841027fcc42080
  | 3 => 0xf192a200ff4c9510fff864a8823ff5154411fba8aa204ff94551026fca2a8883ff3154409fe18aa21fffc8551027f842a887bff605443d7fb02a21eff9815100dfcc0a887bfd605443d7eb02a21eff1815100df8c0a8823ff505443dbfa82a21eff941510f7faa0a887b7d5054411fe282a21effd01510f7fc80a887bfd405443dfe202a21effcc1510f7fc60a887bfd305443dfe182a21effc81510f7fc40a887bfd205443dfe102a204ffc41510f7ee20a887bfe105443dfe882a21efd44151027f820a8822fe6514409ffb20a204ff9905103dfcc828813fd64144017eb20a204ff19051047fea8288237f5414411ff2a0a208ff55051006faa828823fc5414409ffb18a204ff98c5101dfcc628813fd63144017eb18a204ff18c51025f8c628823ff5314411ff298a208ff54c51047f8a628803ff431443bff218a200ff50c510eff88628813ff6214409ff310a202bf98851027fac428802fd6214409fe310a204bf18851047fea428823fe5214411fea90a208ff14851007fe8428873fe4214401fea10a21cff108510effe6428873fe3214401fe990a21cff0c851025fcc228813ff5114409bfa88a204ff94451027eca228813fd5114409bea88a208fd54451027fe6228813fc3114409ff908a204ff08451027fec028812ff6014409ff300a201bf98051027f4c028806fa6014409feb00a21bbf58051027f2c028802f96014409fe300a201bf18051047fea028823fe5014411fea80a208ff140510dffe802886ffe4014437fea00a21bff100510dffe602886ffe3014437fe980a21bff0c0510dffe402886ffe2014437fe900a21bff08051027fe2028813fe1014409fe880a204ff0405103ffecba081eff65d040fff32e8208bf9974103efccba08027e65d040ffeb2e8200bf5974103efacba08027d65d040ffe32e8207bf1974103ffea9a081ffe54d040ffeaa68207ff1534103ffec7a081ffe63d04077f31e8207ff58f41005fac7a081ffc63d04077e31e8200ffd4f410d7fca7a0803fd53d0435fe29e8207ffd0f4103f7e87a081ffe43d040ffea1e8200ef50f4103ff887a081fff62d040fff3168202bf98b4103ffac5a0802fd62d040ffe3168202bf18b41007fea5a0867fe52d0401fea968219ff14b4103ffe85a081fbf42d040fff2168207ff50b410077a85a081ffc42d0435ff9968219ff8cb41007fa65a0867fc32d0401ffa8e8204ff94741007faa3a0813fc51d0435ff98e8204ff0c7410cffe43a0813fc21d040fffb068207bfd834103ffcc1a0806fe60d040ffeb068218bf5834103ff8c1a0806fc60d0431ffa868218ff943410c7faa1a0863fc50d040fffa068207ff9034103ffa81a081ffc40d0431ff9868218ff8c3410c7fa61a0863fc30d0431ff9068218ff883410c7fa41a0863fc20d0409ff8868218ff843
  | 4 => 0xbfc204c84fff8826427ff8413213ffa209909ffc104c811ffb26a208ff9935103dfcc9a8823fd64d44017eb26a208ff19351047fea9a8823fe54d4401bf2a6a208ff55351047f8a9a88237c54d4411ffb1ea208ff98f5101dfcc7a8823fd63d44017eb1ea208ff18f5101df8c7a8823ff53d4411bfa9ea208ff94f51047faa7a88037d53d4411fe29ea200ffd0f51137fc87a8803fd43d444dfe21ea208ffd8b51047fcc5a880afe62d4411feb16a200bf58b51047f8c5a880afc62d4411ffa96a208dfd4b51047fca5a8823fd52d4401bea96a208ff14b51007fe85a8897fe42d4401fea16a225ff10b51137fe65a8897fe32d4401fe996a225ff0cb51137fe63a8813fc31d444bff90ea204ff08751047fec1a8822ff60d4411ff306a201bf98351047fac1a8892fd60d4411fe306a201bf18351047fea1a88237f50d4411ff286a208ff54351126faa1a8823fc50d4449ffa06a224ff90351127fa81a8893fc40d4449ff986a224ff8c351127fa61a8893fc30d4449ff906a224ff88351127fa41a8893fc20d4409ff886a224ff84351127fa21a8813fc10d443d7eb2ca204ffd9251027fcc92881efe6494409feb24a200bf59251027f8c928823ff5494401bfaa4a200ff95251007faa9288037d5494411fe2a4a204ffd8e51027fcc72880efe6394409feb1ca200bf58e51027f8c728812fc6394411ffa9ca223ff94e51007faa728823fc5394401ffa1ca223ff90e51007fa872888ffc4394409ffb14a204ff98a51015fcc528813fd62944017eb14a204ff18a51025f8c528823ff5294445ff294a200ff54a51047f8a528803ff4294445ff214a200ff50a51117f8852888fff3294445ff194a200ff4ca51117f86528812fe6194409ffa8ca204dfd4651047eea328813ff3194409fe18ca204ffc8651027f84328813ff60944097fb04a204ff9825100dfcc128813fd60944437eb04a204ff1825100df8c128823ff5094443ff284a221ff54251047f8a128887ff4094443ff204a221ff5025110ff88128887ff3094443ff184a221ff4c25110ff86128887ff2094443ff104a221ff4825110ff84128813ff1094409fb884a204ff84251027fa2128887f51094409fe084a200ffd9151005fec8a8803fe6454401feb22a200ff1915103df8c8a8823ff5454401ff2a2a200df95151007faa8a8823fc5454401be2a2a200ffd8d51005fec6a8883fe63544077f31aa200ff58d51107f8c6a880efc6354411ffa9aa200dfd4d51107fca6a8803fd5354401bea9aa208ff14d51007fe86a8883fe4354401fea1aa220ff10d51007fec4a8802ff625443fff312a202bf98951007fac4a887ffc62544057e312a208ffd4951006fea4a887ffe5254401fea92a200df54951047f8a4a8803ff425443fff212a200ff509510fff884a8883ff325443ff
  | 5 => 0xf42015fac5a100bff52d0805ff2968402ff54b42017f8a5a100bfe42d0805df2168402fb90b42017f885a100bbc42d0805ff9968402ff8cb42017f865a101fff61d080fff30e8404bf9874203ffac3a1002fd61d080ffe30e842bffcc74215ff863a100bff21d0805fe10e8407ffd834203dfec1a101ffe60d08037f3068407ff58342155fac1a101ffc60d08037e306842affd4342157fca1a10abfd50d0855fe2868407ffd034203ffc81a101ffd40d080ffe206842affcc342157fc61a10abfd30d0855fe1868402ffc8342017fc41a100bfd20d0805fe106842affc4342157fc21a10abfd10d0855fe0868400ffd9542005fecaa1003fe65508117f32a8400ff59542005facaa1003fc65508117e32a8402bfd9142007fea8a101ffe5450801df2a28400ff551420077aa8a101ffc5450801ffb1a8400bfd8d4214ffcc6a100efe6350801feb1a8429ff18d4201df8c6a1003ff5350853ff29a8400ff54d4214ff8a6a101fff4350853ff21a8400ff50d4203ff886a100aff6250805ffa928402ff94942017faa4a100bfc5250805ffa128407fbd0942017fc84a100bbe4250805fe2128402ef10942017d884a100bff3250805ff1928402ff0c942007fec2a1002ff6150801ff30a8400ff58542007f8c2a1012fc6150853ff98a8429ff0c542017fe42a100bfc2150851ffb028428bfd8142147fcc0a1006fe6050851feb028428bf58142147f8c0a1006fc6050851ffa828428ff94142147faa0a10a3fc505080fffa028428ff90142147fa80a101ffc4050851ff9828428ff8c142147fa60a10a3fc3050805ff9028402fbc8142017fc40a100bfd2050851f69028402ff08142147fe20a10a3fe1050851fe8828428ff04142007feca99002ff654c801ff32a6408bf99532007faca99002fd654c801fe32a6408bf19532007fec899002ff644c801ff3226407bf99132007fac899002fd644c801fe3226407bf19132007fea899003fe544c801feaa26400ff15132015fec69900fff534c807ff29a6403ff54d3201ff8a69900fff434c807ff21a6403ff50d3201ff8869900aff624c805ffa926402ff94932017faa49900bfc524c805ffa126402ff90932017fa849900bfc424c805ff9926403fbcc932017fc649900bde324c805fe1926402f70c932017d8649900bcc324c801ffb0a6400bfd8532007fcc299003fd614c801fe30a6404bf1853201ffe629900fdf314c807fe18a6402ffc8532017de429900bfc214c84fffb026427bfd813213ffcc099006fe604c84ffeb026427bf5813213ff8c099006fc604c84fffa826427ff9413213ffaa09909ffc504c84fffa026427ff9013213ffa809909ffc404c807ff9826403f7cc13201ffc609900ffd304c84fee9826403ff0c132017fe409900bef204c805ff1026402ff4813213fda4099
  | 6 => 0x1fe30a8604bf1854301ffe62a180ffc3150c63ff90a8631ff08543187fec0a18c2ff6050c61ff3028601bf98143187fac0a18c2fd6050c61fe3028601bf18143187fea0a18c3fe5050c61fea828630ff1414303ffe80a18c3fe4050c61fea028607ff1014301ffe60a180fdf3050c07ff1828603ff4c143187ba60a180ffc3050c61ff9028630ff88143187fa40a18c3fc2050c61ff8828630ff84143187fa20a18c3fc1050c057f32ea408ffd9352047fcc9a901efe64d4811feb26a400bf59352047f8c9a9023ff54d4811bfaa6a408ff95352047faa9a90037d54d4811fe2a6a408ffd8f52047fcc7a900efe63d4811feb1ea400bf58f52047f8c7a900efc63d4811ffa9ea408ff94f52047faa7a9023fc53d4801ffa1ea42fff90f52007fa87a90bffc43d48057eb16a402ff94b52016fca5a900bee52d4805fe296a402df14b52017fc85a900bfc42d4805ff996a402ff8cb52017f865a9023ff61d4811ff30ea404bf98752047fac3a9002fd61d4811fe30ea42fffcc75217ff863a900bff21d4805fe10ea408ffd8352045fec1a9023fe60d48037f306a408ff58352175fac1a9023fc60d48037e306a408ffd4352047fca1a9023fd50d4811fe286a42effd0352177fc81a90bbfd40d485dfe206a42effcc352177fc61a90bbfd30d485dfe186a402ffc8352017fc41a900bfd20d4805fe106a42effc4352177fc21a90bbfd10d485dfe086a402bfd9552007fec8a9002ff6454801ff322a400ff59152007f8c8a901efc6454811ffaa2a400dfd5152007fca8a9003fd5454801beaa2a408ff15152007fec6a9002ff635485bff31aa403bf98d52007fac6a90b7fc63548077e31aa408ffd4d5216ffca6a9003fd5354811fe29aa400ffd0d5216ffc86a9003fd435485bfe21aa402bfd8952017fea4a9023ef5254805ff292a402df94952017f8a4a900b7c5254805f6292a402ff90952017f884a900bff3254805ff192a402ff0c952007fec2a9002ff6154801ff30aa400ff58552007f8c2a9012fc615485bff98aa42dff0c552017fe42a900bfc2154859ffb02a42cbfd8152167fcc0a9006fe6054859feb02a42cbf58152167f8c0a9006fc6054811ffa82a42cff94152167faa0a9023fc5054859ffa02a42cff90152167fa80a90b3fc4054859ff982a42cff8c152167fa60a90b3fc3054805ff902a402ff88152017fa40a900bfc2054859ff882a42cff84152167fa20a90b3fc105480fffb2e8407bfd974203ffccba1022fe65d080ffeb2e8400bf5974203ff8cba101efc65d08057f3268407ffd534203ffca9a101fbe54d080ffeaa68400ef5534203ff8a9a101fff63d080fff31e8403bf98f4203ffac7a1002fd63d080ffe31e8403bf18f42007fea7a10affe53d0801fea9e842bff14f4203ffe87a101ffe43d080ffea1e8407ff1
  | 7 => 0xa9823fd60d4c6d7eb06a608ff1835300df8c1a9823ff50d4c11ff286a608ff54353047f8a1a98dbff40d4c6dff206a636ff503531b7f881a980fff30d4c07ff186a603ff4c35301ff861a98dbff20d4c6dff106a636ff483531b7f841a98dbff10d4c6dff086a636ff443531b7f821a980eff6554c01ffb22a600bfd9153007fcc8a9803fd6454c01fe322a607bf19153047fea8a98037f5454c01ff2a2a600ff55153006faa8a9823fc5454c077fb1aa603ffd4d53047bea6a980ffe5354c07bf29aa603ff14d5301ef8a6a980fdc5354c07ff21aa603ff10d53007fec4a9802ff6254c6bff312a602bf98953007fac4a98d7fc6254c057e312a635ff94953047f8a4a98d7fe4254c6bfe212a603ffcc95301ffc64a980ffc3254c01ffb0aa600bfd8553007fcc2a9803fd6154c01fe30aa604bf1855301ffe62a980ffc3154c6bff90aa635ff085531a7fec0a98d2ff6054c69ff302a601bf981531a7fac0a98d2fd6054c69fe302a601bf18153047fea0a98d3fe5054c69fea82a608ff141531a7fe80a98d3fe4054c69fea02a634ff1015301ffe60a980ffe3054c07fe982a603ff0c1531a7fe40a98d3fe2054c69fe902a634ff081531a7fe20a98d3fe1054c69fe882a634ff0415303ffecba181eff65d0c0fff32e8608bf9974303ffacba1802fd65d0c0ffe32e8607bf1974301dfcc9a181fff54d0c0fff2a68607ef9534303ffaa9a1803bd54d0c0ffe2a68603bf58f4301ffea7a180ffe53d0c07fea9e8603ff14f4301ffc87a180fbe43d0c07ef21e8603ff10f4301f7887a181fff62d0c0fff3168602bf98b4303ffac5a1802fd62d0c0ffe3168602bf18b4319ffca5a18cffc52d0c0fff2168607ff10b4301ffe65a180ffe32d0c07fe1968607ffd874303ffcc3a1812fe61d0c0ffeb0e8600bf5874303ff8c3a180fff31d0c07fe18e8633ffc874319ff843a181fff60d0c0f7fb068607ff9834300dfcc1a181ffd60d0c657eb068607ff1834300df8c1a18cbff50d0c65ff2868632ff54343197f8a1a181fff40d0c0fff2068607ff5034303ff881a180fff30d0c07ff1868603ff4c34301ff861a18cbff20d0c65ff1068632ff48343197f841a18cbff10d0c65ff0868632ff44343197f821a1803ff6550c017fb2a8600ff99543045fccaa1803fd6550c017eb2a8600ff19543045f8caa180eff6450c01ffaa28607ff951430077ca8a1803fd5450c01deaa28607ff1514301dfec6a180fff5350c07ff29a8603ff54d4301ff8a6a180fff4350c0fefa1a8603ff90d4301f7c86a180ffc4350c07de21a8603f710d43007fec4a1802ff6250c63ff3128602bf98943007fac4a18c7fc6250c057e3128631ff9494318ff8a4a18c7fe4250c0ffe2128603ffcc94301ffc64a180ffc3250c01ffb0a8600bfd8543007fcc2a1803fd6150c0
  | 8 => 0xfd825403ffcc12a006fe609500ffeb04a83ebf5825403ff8c12a006fc6095011ffa84a83eff942541f7faa12a023fc509500fffa04a807ff9025403ffa812a01ffc409507dff984a83eff8c2541f7fa612a0fbfc309507dff904a83eff882541f7fa412a0fbfc209507dff884a83eff842541f7fa212a0fbfc1095011ffaa2a808efd515403ffca8aa01f7e5455001ffb1aa800bfd8d541effcc6aa00efe6355001feb1aa83dff18d5401df8c6aa0f7fe5355011fe29aa83dff90d5403ff886aa003ff62550017fb12a83cff98954015fcc4aa003fd6255079fe312a802bf189541e7fca4aa023fc5255079ff212a807ff109541effe64aa0f3fe3255079fe192a800ffd8554005fec2aa003fe6155001feb0aa800ff18554025f8c2aa0f7ff315507bfe18aa83cffc85541e7f842aa0efff60550777fb02a800fed8154005f6c0aa0effe60550037f302a83bff581541ddfac0aa0effc60550037e302a83bfe1815400df0c0aa023ff5055077bfa82a83bff941541dffaa0aa0ef7d5055011fe282a807ffd01541dffc80aa0effd405500ffe202a83bffcc1541dffc60aa0effd3055077fe182a83bffc81541dffc40aa0effd2055077fe102a83bffc41541dffc20aa0effd1055077fe082a808bf9945403dfcc82a01fff541500fbfaa0a807ff9505403f7ca82a01ffd541500fbeaa0a808ef5505403ffec62a01ffe63150077f318a807ff58c54005fac62a01ffc63150077e318a808ff94c54047f8a62a01ffe431500ffe218a807ffd885403ffcc42a00afe621500ffeb10a800bf5885403ff8c42a00afc6215011ff290a808ff1485403ffc842a01ffc4215075ff990a839ff8c8541cff8642a01fff611500fff308a804bf9845403ffac22a002fd611500ffe308a83affcc4541d7f8622a0e7ff2115073fe108a807ffd805403dfec02a01ffe60150037f300a807ff580541c5fac02a01ffc60150037e300a808ffd4054047fca02a023fd5015011fe280a807ffd005403ffc802a01ffd401500ffe200a838ffcc0541c7fc602a0e3fd3015071fe180a838ffc80541c7fc402a0e3fd2015071fe100a838ffc40541c7fc202a0e3fd1015071fe080a803bf99753047fec9a9823fe64d4c0f7f326a608ff59353005fac9a9823fc64d4c11ffaa6a608dfd5353047fca9a9823fd54d4c01beaa6a608ff1535301dfac7a980ffe53d4c07bf29ea603f794f5301ebca7a980ffc53d4c07be29ea603ff90f5301ff887a9823ff62d4c11ff316a602bf98b53047fac5a9802fd62d4c11fe316a602bf18b53047fca5a9823fc52d4c6fff216a637ff10b5301ffe65a980ffe32d4c07fe196a608ffd8753047fcc3a9812fe61d4c11feb0ea600bf58753047f8c3a980fff31d4c07fe18ea637ffc87531bff843a9823ff60d4c117fb06a608ff9835300dfcc1
  | 9 => 0x200c00100100700002602600100300900001e00200001300100600700000900000000200100400301a00200100901401900103800100200000000100a00100701900000800700000000e00000103d00100100d00200c00000500100400000100a00700000100100300000000101800001000203300600601300100200f00201302e00f00400501800900200000201400700500300700000700200303400e01a00800000000001001900202500100600c00000300000600000102c00201300202300101000400000000200501502700100101502600200000a00200000000200800801000202806b00200800001300000000300701a00000401602800400002000200001800202f00500300000000000700103100200800600200000000201000200b00300001900000609400400600900800000000200d00b00000500000b02700000300700500700600901800a00b00c00600101200900100000401700400901001000000f00300000d00000900000600101601b00400b00300e00800002100300300100400100100500400400000500a00100000e00400100000700000702d00000100400901500700b00f00800400000000400000100000200b00c00700600600a00000600000000301500005e00000300000103a00000100400100100100500000201100000900100b00000000500001100400300600000100600800403b00100600001600602800200000e00e047fec7aa023fe63d50077f31ea808ff58f54005fac7aa023fc63d50077e31ea808ff94f54047f8a7aa10ffe43d500ffe21ea808ffd8b54047fcc5aa00afe62d5011feb16a800bf58b54047f8c5aa00afc62d5011ff296a808ff14b54217fc85aa01ffc42d5087ff996a842ff8cb54217f865aa023ff61d5011ff30ea804bf98754047fac3aa002fd61d5011fe30ea843ffcc75421ff863aa10bff21d5085fe10ea808ffd8354045fec1aa023fe60d50037f306a808ff5835420dfac1aa023fc60d50037e306a808ffd4354046fea1aa023fe50d5011fea86a841df54354047f8a1aa01fff40d5083ff206a841ff5035403ff881aa107ff30d5083ff186a841ff4c35420ff861aa107ff20d5083ff106a841ff4835420ff841aa107ff10d5083ff086a841ff4435420ff821aa0eefd659500f7f324a807ffd525403efea92a023bf54950019faa4a807ffd8e5403ffcc72a00efe639500ffeb1ca800bf58e5403ff8c72a00efc6395081ff29ca808ff14e5403ffc872a01ffc439500fffb14a807ff98a54015fcc52a01ffd62950017eb14a807ff18a54015f8c52a0fffe5295011fe294a807ff90a5403ff8852a103ff329507fff194a83fff0ca5403ffec32a01ffe61950097f30ca807ff58654005fac32a01ffc6195081ff98ca840ff0c6541fffe432a0fffc219500fffb04a807b
  | 10 => 0x147d4000154077419007a013c9bc2110000ea81587700cf0e2cba60002998a880002b001709809ae0000bc000015c0d1278848057c07c2dc8f6cb140000478d803064870000468b1c2df28795a45748222ca8000ada6ce1649bf8dba64b09b9ddc21420540b8aacb846fb2ee9544ac200002583787de00000000006a41a500009b000050200000009304290000be000044f1da1a30fe82bf03f00008984a71fa94f89a230b00004041723c432c9890b2475818b051864610e0a6800046e00038b96c408c53c26b00001dc0003479a580001c100000000004f800002940000000a98000fa64501c61c84fea43d29c9304ab68141711afcdd40be0f880007fc5300971448e001bd00015ac00029135a94d06007660319f60f206140a900004704012ea9c90e5669330b925cfd047318c930cae477c00b1fd88104511c40b78650808232952051028d1db0bbcc646990a71a102b8224060988c4c85f500d19cc62425a0899674d0a10c0030000ece23a0dd01000000000001ca049400000c13b0184069000074cd4254d3430efcef43c304f8f8c3866d720298747487d53d68b0400000024a9e04aba6870c9083c0006633b40410f1454a0048e3c17446c2f39228e0a5a334e2000bd245f36d1b84b9e4dc036199850c5363971b04d9a812238000000056a35400007da58620601e82d82bc225000066203101200200000400200602c00002f01500001200600100400000000002200a00800a00600800a00000100500003b00100f00a01400200200200200101200400300000100000600201e01701200100200200100300000000200001100100300700000500801100701000200000100100400f00500904b00000000300002500101500500000000600900002000d00602600301201d00000100700000200900100f00100101100000e00001200a00201601700000d00200000d01b00701401a02500e01200000303000001300800000801200000000500100000000100400001400302900400000a00400200000300b00300100101a00001300300300000700c00e00000601b00803000200a00001400b00000000a00800000100001301000600002b00200100200b00500301e00200900000001700300100400500202100000300200100400000300002e01700100300800700100000000200600c02b00001d00000c02000800300100600000100000001800b00a01a01400d00200c00200400301100100000300000a00000f00400200000400000f03400000000d00000201000100202200300000000b00004401800500001c00100300500000d00800301100d00400901d00300600400401d00100c00c01f00f00300000901c00000800100700101400000200d00300000000100000400101700900700901600300f00f00000000c0010040020030010
  | 11 => 0x53878059a3740338e5800016a3651214cc81a200704587c047714b0db8dfa00011f95101fa51c00007fc00e14c1a800006c44ae0bb95980d45103309400c6000012981c485400012f89a8ec210010e00000b20001eb8aa8b420004118000ae61cd00012b4b566be1e01db43de8030e400006426b4000062c82e000037038c7a67b7231160c0160c61e716901ca00016588785383660cd8bf073602137d08a0430320168950410206212396d49f86c72070b948e224b2718d6893205b0000ba4a1476340997ccd740551b613e42d00c90680ec4c2c01118e14680e862f0ca0a7cab057606e00b49d467d12c80000000002d411f000057b000137c0000000000238adc0003ae9f00eea4f600015e40001700910b7400000000000007d82ee23d00000003a61df0000000000312833400074b0001c507382d03c49d24b5c4272a006343a013a3d980ec0006131450b50d580000000f58000000000123505409a0000880000128000000038467c31d1d30fb84f40dc80000002a80cd19941a61621a08d704f06830009394a1871b34807f41da01c28a0000f0474f3b79a08e4a06403f89aca328202209f9044c5462bf85b853638e388920432e535127987c25636b236996c7567a005520747ce486216984475257e0e6124c4601c502902cc00434903286a0dfe2b634c03ec5a64bf3ef12006e459e1da90084cc3ae11187d8cc451529f98808b67e23fe98e47343640001c30bc81f44170c883924232a900c804c4a229d000c9ee63821b043418613416a857810e0920b20904bb20b10099878c1c0003c9967cdf0066018a0900000292ae08245b66b83cb01d876455535300000007e139682280002cf2050cecc203da0000c7838831422103100004160f3930800036800000009122362f10000b405bc1038e60db64c009382f09aa17b3f2986001a05025b11f8b603b81c891d8d6c4fd2ac85f8e7679913704441cc0af29b880c1e47a331b8e4883414924f02a00005bf00012841d238901101c09a63c11c283141aa2083fb9af42864d00708ca810634b229158cb6859b0f804505ae000000157c60c36900000008ae3f71a1177cf4a23b16d17c870e16511f0f5030808223390f90026e30df1bc4b546672dd10e4e944603fd0ef021e3a711c8ab4b383533678e7c0000cf3580bb42c200000020bc4aa75222b074867800026a1c604560d810990cc48a50334e80000007c83599f9c00011822e861c1be5310001da49f432b354800055e000000133001e000000107cffc4f208f1a4898876c1ab0000e9c7010390f1c000000183a09cf7474819f80784144eb3b98ea0a0c54f3a2811085800012110900008102db87f8d564ca3eb9a7c7e401d0519c9c4c41670e017f064c3832eb118c1008051e60a107e63f916016b0c865181241010e103c630501806
  | 12 => 0x9041262fa0e4054e81e0000e5cfa00000df840c570000000000000000021a83807146012b79b6103613d094890c37622a3a084c000003c1e883008fa2141338000b187512a49ebc1364f00f410c400000031a14c83a8000000000066c4e80fc0e184c62ca23d9e6c3f66410c98950bfc5de25b8b1435a25126399e0d840da3b898985c80003d806c8f4e5cc1741c68f285e60c41f48e0e2f038104b45d657808a8744cd03761401a8c00054b3be9494000706385181452e0003220decc6675432a94acc003cd0001e440000003349728cac49641403f004e0003e717bc1107cd03c90e0dd00081ab9fc026624c0000000058507000145c5302f627781ac00014b3d89aa8e6a7c106c85d47d42871c107a80003302cb00e4aea11929118ac0ba2bb000201011a0003dd800015a00004c0000000344263087c0005980ab847c36a4b91188d30c081f71719eacc9a5d72d291a056a4590002054b163f117c8000b7021612e8aa4e6801014c97009080000739390c4e77f1c002d000081f38714b82f404c14596b49380ca3f71900f9622e37709a40e620234a008cf8e32c09188a42727eb07c99b8c444e93aa8608d623c20760c38b2800000000007945b200000000003022770cc81087761708d500001d608111fc2421a109210188423ee38e1ab85464fb1a8814c30a11b0c61c64a02729214108000034f1139d1844281c3ca8934f0a25015985b4a705111ea9290ce80bf12e0fa062a6c340c0d6ca165bb06918a45ea6e7282180c4ca4743a18c3cfba14f00b8510b224a33de9d0031247809a933504a67f020988483867027313d424a42b196806cfb60e200000000000003c9056c000147000028000057d0000d6000000000000000000000000000ca26c900c876400050835d994800000000000001fc00036f9f28000000000000031e0002a6000034e80719c8cccc043af00012a0df816b3cd0e8c54a0002e800d46be1e1000000000021501d00000008330979d80da409400019d827e2d6287127c65e0991b81be40006ed22308687a40000838b64cde00a35680005641b300011a8000000000000101a6a200000001763dc1561ac800006d2ab016095e2ec30a93800000000000000b8a2251be972404077941094b00ee2730bf9e9097c2e000012200003b70f216f426c2b921109b467440b418163cbf02ae357800033001f1e403e81ea11c2d38d3437874d259800052474711108bc9fc1f53298cd4ebe09c13f00f400000028f1c4cf8a0000c0095878a0000000a24000612290886419813e09882dc43a55e3998000ea028e3f301280001f33d31094cbc45825e08c80486b720f1474f5c1cf0db1e5c10a5452978d382cc1ed00a07603564e22b601346e265f2b20b609fe39e0ce9d10ca866006b01200087fb0c88b2042e6b90c09768c8e7b40
  | 13 => 0x37b90443480002901fcc0000002769e3874400014f0000d4045c3660fd80003b917d90b8d2e5d407f9ef8bd81b03e78d78b081583ae0adc46a20638917345863012b80dbcb9073e2cb81e0a542b122288340000000001fe47581cb0000c34eca6e01dd8de40006a40001508ac045537a1f309a44da40b0df091810b39600a03ca2ea11e98c4c7860b18c1b1838c00030384e081278f3b59298bda2a60d194a0eb45ff00000000004b4000151c11225213b86b0aa645a2920000e7033722002c8bb07fc39c90dc00014514800dc0003de00a8258fa23e220c076839404e1ba9dec5022b41610fa4fd232500617e4c7a00012000000006e231704a8000000037945823a0001461d9006c53b1081e7091c00029490c072a1d73bf1f8c12a14a0b003bc88600033f18182aa4dd13c80005e265a0001f64ad081a0181824eb63452c29bd8c7c15a3b703a0c9c1a904891908d280621d8bc88265db00016a40000000001fb02f26c402d0000b122342e303dcb027d60ef8924b865b31691bbc3ba0003680000de67100670ce0ff045406b84c8c5a4e72df1fc86c26883d41050c1a3432561ee038e7ea24e87887c80f602b19ec63a45302e07a482066d11e0fd022e2bd3bc0d9472643a3241cc862614117997ecb3274218191c800002f25c01441e04b10001960e2c0001a300006d400025802c099e7c6162097800071d33606d00006713c00000b0e3fa34700000000003b500003cc4a5000123cb6c82b00018a00000000000b9cf1661a1500df90326082f411d4bc052d13d1e0cf3a24e25a8e808f260c0150d00916000167000000082933d000000000030d8000af408b0001a445fa72300007b02c6311000100000003800018b000000010089d88640970000f4000011028992ec2ba0003d080001ba44800000004de64a3c3202400073d0001d64e4c186000000041c6d31639cdc3707b2000000087e70f1e7800000009000019d4c320002018eccf3e6570d302ac60815124880002ac1b1000171c4e23554160000d345051e583a8f7849a3f888b4f6a4a901a0de832c4db0961c0cbd462a0129cd88d66d902f83e01261db2b289f101c3472f18d8c71a29a03d82182ec6792ad00cc69468d00000000002ff21a193caee680000000050418e1ec194000066a12d8a50cd617d3979034d021dc3dc904889a29d1521f80b883344188e640006dc1ae9e889545672ba09d06ce3053e197d86da5e518801f433880b2868000e440003601cc40001730798ffc00034805c00002b2000385800000020400000000000003df8000eac00014988b0be033d05e87e87e02a113f87f0a3633e2799ffc0001123628778f8853d0f70c68cee0e42c98b30906000000132400000000000009560001479af000000000000007085e125e9e3428463b3729178ea600013402a4
  | 14 => 0x48846f1730f24d3c10600019c80005cb3228000b4c03e06420b4c6c2580cc81781b609d02100000ae00038485c46520751ca0000f3042f2f71a2429038136f18700000a13d48000ee417c262964077a73f1fc1eb00247ef37484ec63e0002130c5cbf45803c40680196000000078cbe271e19200000003a100000000000000001bb07f668a372147c8c22dc0b900142a82000d7912cba20b640102d40d002b2658ff07ca32e25906a8b102121060be90224902fb8c2009280a1bc16bc3146351380dfc2d24d826c9280eae1eb1230420d967840d71a9c36e16f3d511b874a08c3cf1a6cd1671f2e0867c4660a61f31c340a83593b11688fda0d420e9424cb815013d9f24c7e37724d9e30a4e0473ed1c104ae65d00000008366490218f744e477409e031c8cc49400007e414437339e0c9c41654e36a111c99c4ba3901b4481e6420af948ce603ad2fe8f7c7fa03f37a80000006c81428000b1a09e000000000000030790f0d2a78716309841d600018480000000f100015c49901d50001770ba40003ef8000d4a2833af00010646d540600000000000000ec028064617a1bc00005543e120983e41ce2f58654b043d92930424b9c4153db111101e00003080000002951861930af872a0001588dd627539d1bc89242f738a901c5fc39d022912400059a000150c4361051f58000dac31b20c955cdcc00005200000000001f080002e800022713844fa000
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x77159121004ff7559121044fc7559121006bf7459121004ff735912101cfe735912101cfc735912109cff7259121006ef72591210ccff7159121006f77159121004ff705912100cfe7059121004fd705912100cfc70591210b4fe761912103ebe6419121006bd6419121044ff76d5121004fe76d5121004fd76d5121044fc76d51210067f65d51210467c65d512103cff7695121004fe7695121004fd769512103cfc76951210073f5495121004ff7655121004fe7655121004fd7655121004fc76551210067f65551210467c6555121005fb705512102df8705512103cff7615121004fe7615121004fd761512103cfc7615121015ee7215121005ed721512101cfe76d8d21036de63d8d21044fe75d8d21004fd75d8d2103cfe74d8d21004fd74d8d21036dc53d8d21036de43d8d21024ff72d8d21014fe72d8d21024fd72d8d21014fc72d8d21076df32d8d21076dd32d8d21024fe71d8d21014fd71d8d21024fc71d8d21036df31d8d21004ff70d8d2100cfe70d8d21004fd70d8d2100cfc70d8d21006de30d8d21036dc30d8d210057f7558d210057c7558d21036dc6358d2122df77158d21004ff7558d210067f7558d210047f7558d21044fc7558d210067c7558d210447c7558d21004ff7458d2103cfc7458d21074ff7358d21006df7358d21064ff7258d21006ef7258d2122cff7158d21006f77158d21004ff7058d2100cfe7058d21004fd7058d2100cfc7058d21044ff76d4d21004fe76d4d21004fd76d4d21044fc76d4d21006df63d4d2101edc63d4d210375e53d4d21004ff7654d21004fe7654d21004fd7654d21004fc7654d2103cff76d0d21004fe76d0d21004fd76d0d2103cfc76d0d21004ff7650d21004fe7650d21004fd7650d21004fc7650d21006df6350d2101edc6350d21025ec764c92101eec764c921024ec764c921015ef734c921017cf734c921007cf634c92101eee634c92101eec634c921037cc634c92101ecc634c921007e7714c921025ee714c921025ec714c921007e4714c921016ef614c921017e7614c921037cf314c921226ef604c921226ed604c921037cf304c921227cd304c921014fe76d4521014fc76d45210067f65d45210467c65d4521015ee72d4521005ed72d4521044ff7654521014fe76545210fcfd7654521014fc76545210067f65545210467c6554521005ef7254521015ec7254521014fe76d0521014fc76d05210057e75d05210057d75d0521006bf64d052103ebc64d0521015ee72d0521005ed72d052103cff7650521014fe765052109cfd7650521014fc7650521006bf645052103ebc6450521005ef7250521015ec7250521027e4215052101cff764c521014fe764c521064fd764c521014fc764c521006df634c52101edc634c521005ef724c521015ec724c521007cd324c521
  | 1 => 0x96210067d5059621004ff7559221044fc7559221026bf7459221004ff735922101cfe735922101cfc735922109ebf425922109ebd4259221024ff7159221024fe7159221024fd7159221024fc7159221026be4159221026bc4159221004ff705922100cfe7059221004fd705922100cfc7059221044ff76d5221024fe76d5221004fd76d5221024fc76d522123e7f65d52210467c65d522103cff7695221024fe7695221004fd7695221024fc76952210467e65952210067d65952210073f5495221004ff7655221024fe7655221004fd7655221024fc76552212367f65552210467c6555221005ef7255221015ec7255221005fb705522104df8705522103cff7615221024fe7615221004fd7615221024fc76152210467e65152210067d6515221004ff7558e21044fc7558e21004ff7458e2103cfc7458e21026df7358e21066df3258e21066dd3258e21024ff7158e21024fe7158e21024fd7158e21024fc7158e21026de3158e21026dc3158e21026ef2158e21026ed2158e21004ff7058e2100cfe7058e21004fd7058e2100cfc7058e21044ff76d4e21024fe76d4e21004fd76d4e21024fc76d4e210467e65d4e210067d65d4e210575e53d4e21004ff7654e21024fe7654e21004fd7654e21024fc7654e210467e6554e210067d6554e21005ef7254e21015ec7254e2103cff76d0e21024fe76d0e21004fd76d0e21024fc76d0e2103ebe64d0e21006bd64d0e21015ee72d0e21005ed72d0e21004ff7650e21024fe7650e21004fd7650e21024fc7650e2103ebe6450e21006bd6450e21044fe76d952103cfe74d9521004fd74d952101cfe73d9521004fd73d952101cfc73d95210067e53d95210067c53d9521024ff72d9521014fe72d9521024fd72d9521014fc72d95211167f52d95211167d52d9521024fe71d9521024fc71d9521004ff70d952100cfe70d9521004fd70d952100cfc70d95210067e50d95210067c50d95210067f65995210fdf57199521005df7359521035dc735952112df771595210067f7559521004ff745952103cfc7459521004ff7359521006df7359521004df735952101cfe735952101cfc7359521006dc735952101cdc73595210fcff7259521006ef725952112cff7159521006f77159521004ff705952100cfe7059521004fd705952100cfc7059521114fe76195210467e65195210067d651952103cfe76d9121044fe75d9121004fd75d912101cfe73d9121004fd73d912101cfc73d9121024ff72d9121014fe72d9121024fd72d9121014fc72d91210b6bf42d91210b6bd42d9121024fe71d9121024fc71d9121004ff70d912100cfe70d9121004fd70d912100cfc70d9121006be40d9121006bc40d91210057e75991210057d7599121006bf6499121035de7399121005dd739912109df571991210cdf
  | 2 => 0x4ff70d913100cfe70d9131004fd70d913100cfc70d9131006be40d9131006bc40d91310057e75991310057d7599131006bf6499131065ee7299131005ed72991310a5f571991310d5f77159131004ff7559131044fc7559131006bf74591310a4ff7359131006df7359131004ff7259131014fe7259131014fc72591310d4ff7159131006f77159131004ff705913100cfe7059131004fd705913100cfc70591310bcfe761913103ebe6419131006bd6419131044ff76d5131004fe76d5131004fd76d5131044fc76d51310067f65d51310467c65d513103cff7695131004fe7695131004fd769513103cfc76951310073f5495131004ff7655131004fe7655131004fd7655131004fc76551310067f65551310467c6555131005fb705513105df8705513103cff7615131004fe7615131004fd761513103cfc761513101dde7315131005dd7315131014fe76d8931066ee62d8931044fe75d8931004fd75d893103cfe74d8931004fd74d8931024fd73d8931014fc73d8931066ec52d8931066ee42d8931066ee32d8931056ed32d8931024fe71d893101cfd71d8931024fc71d8931066ef21d8931004ff70d893100cfe70d8931004fd70d893100cfc70d8931006ee20d8931066ec20d89310057f75589310057c7558931066ec625893124df77158931004fe76d4931004fd76d4931044fc76d4931006ef62d4931016ec62d4931004ff7654931004fe7654931004fc7654931004fe76d0931004fd76d093103cfc76d0931004ff7650931004fe7650931004fc7650931006ef6250931016ec6250931025dc764c931016dc764c931024dc764c93101ddf724c93101fcf724c931007cf624c931016de624c931016dc624c931067cc624c931016cc624c931007d7714c931025de714c931025dc714c931007d4714c931025d4714c93101edf614c93101fd7614c931067cf214c931246df604c931246dd604c931067cf204c931247cd204c93101cfe76d453101cfc76d45310067f65d45310467c65d453101dde73d4531005dd73d45310277651d4531044ff765453101cfe7654531104fd765453101cfc76545310067f65545310467c6554531005df735453101ddc7354531027d4315453101cfe76d053101cfc76d05310057e75d05310057d75d0531006bf64d053103ebc64d053101dde73d0531005dd73d053103cff765053101cfe76505310a4fd765053101cfc7650531006bf645053103ebc6450531005df735053101ddc7350531027d431505310267f7559621004ff745962103cfc7459621004ff735962101cfe735962101cfc73596210fe7f52596210fe7d5259621024ff7159621024fe7159621024fd7159621024fc71596210267e51596210267c5159621004ff705962100cfe7059621004fd705962100cfc70596210067f505
  | 3 => 0xe634c841006dd634c841016ee624c841006ed624c841087cc324c841005f7714c841025f4714c8410267f7559631004ff745963103cfc74596311067f53596311067d5359631004ff7259631014fe7259631014fc7259631024fe7159631024fc71596310267e51596310267c5159631004ff705963100cfe7059631004fd705963100cfc70596310067f50596310067d5059631004ff7559231044fc7559231026bf74592310a6bf43592310a6bd4359231004ff7259231014fe7259231014fc7259231024fe7159231024fc7159231026be4159231026bc4159231004ff705923100cfe7059231004fd705923100cfc7059231044ff76d5231024fe76d5231004fd76d5231024fc76d523123e7f65d52310467c65d523103cff7695231024fe7695231004fd7695231024fc76952310467e65952310067d65952310073f5495231004ff7655231024fe7655231004fd7655231024fc76552312367f65552310467c6555231005df735523101ddc7355231005fb705523106df8705523103cff7615231024fe7615231004fd7615231024fc76152310467e65152310067d6515231004ff7558a31044fc7558a31004ff7458a3103cfc7458a31026ef7258a31076ee3258a31036ed3258a31024ff7158a31024fe7158a31024fd7158a31024fc7158a31026df3158a31026dd3158a31026ee2158a31026ec2158a31004ff7058a3100cfe7058a31004fd7058a3100cfc7058a31044ff76d4a31024fe76d4a31004fd76d4a310467e65d4a310067d65d4a31004ff7654a31004fd7654a31024fc7654a310467e6554a310067d6554a31005df7354a3101ddc7354a3103cff76d0a31024fe76d0a31004fd76d0a3103ebe64d0a31006bd64d0a3101dde73d0a31005dd73d0a31004ff7650a31004fd7650a31024fc7650a3103ebe6450a31006bd6450a31044fe76d953103cfe74d9531004fd74d9531024ff73d953101cfe73d9531024fd73d953101cfc73d953111e7f53d953111e7d53d9531014fe72d9531004fd72d9531014fc72d95310067e52d95310067c52d9531004ff70d953100cfe70d9531004fd70d953100cfc70d95310067e50d95310067c50d95310067f6599531105f57199531005ef7259531065ec7259531135f771595310067f7559531004ff745953103cfc7459531104ff7359531006df7359531004ff7259531006ef7259531004ef7259531014fe7259531014fc7259531006ec7259531014ec7259531134ff7159531006f77159531004ff705953100cfe7059531004fd705953100cfc705953111cfe76195310467e65195310067d651953103cfe76d9131044fe75d9131004fd75d9131024ff73d913101cfe73d9131024fd73d913101cfc73d91310bebf43d91310bebd43d9131014fe72d9131004fd72d9131014fc72d9131
  | 4 => 0x4941044fc76d49410467e65d49410067d65d4941006ef62d4941016ec62d4941004ff7654941004fe7654941004fc76549410467e65549410067d6554941005be76d094103ebe76d0941006bf65d0941006bd65d0941005bd73d094109dbd72d0941016be62d0941016bc62d0941025be71d0941025bc71d094103ebf61d094103fb761d094125fb710d094125fb510d0941024fc7650941006ef6250941016ec6250941005f77150941025f47150941025bc7650941016bc7650941024bc7650941006bf6550941006bd6550941005bf735094103dbf725094103faf7250941007af6250941016be6250941016bc625094109fac6250941007b77150941025be7150941025bc7150941007b4715094103ebf615094103fb7615094109faf2050941257ad2050941257b71050941257b51050941004ff764c941004fe764c941004fc764c94103dbe744c941005bd744c94109fcc324c94103cfe76d454103cfc76d45410067f65d45410467c65d454103dbe74d4541005bd74d45410277651d4541044ff7654541004fd765454103cfc76545410067f65545410467c6554541005bf745454103dbc7454541027b44154541024ff75594410267f755944103cff745944103cfe745944103cfd745944103cfc745944103e7e545944103e7c5459441004ff735944101cfe735944101cfc7359441004ff7259441014fe7259441014fc7259441024fe7159441024fc71594410267e51594410267c5159441004ff705944100cfe7059441004fd705944100cfc70594410067f50594410067d5059441004ff7558c41044fc7558c4101cfd7458c41024ff7358c41026df7358c4108ede5358c4103edf4358c4103edc4358c41004ff7258c41014fe7258c41014fc7258c4108edf3258c41024fc7158c41026bf4158c41026bd4158c41026de3158c41026dc3158c41004ff7058c4100cfe7058c41004fd7058c4100cfc7058c4108edf3058c41006dd3058c41044ff76d4c41024fe76d4c41004fd76d4c410467e65d4c410067d65d4c4108f5e53d4c41004ff7654c41004fd7654c41024fc7654c410467e6554c410067d6554c4101ede6354c41006dd6354c41004ff7558841044fc7558841014fd7458841004ff735884101cfe735884101cfc7358841024ff7258841026ef7258841086ee525884103eef425884103eec4258841086ee3258841024fc7158841026bf4158841026bd4158841026ee2158841026ec2158841004ff705884100cfe7058841004fd705884100cfc7058841086ef2058841006ed2058841044ff76d4841024fe76d4841004fd76d48410467e65d48410067d65d4841004ff7654841004fd7654841024fc76548410467e65548410067d6554841016ee6254841006ed6254841004ff764c841004fd764c841024fc764c84101ed
  | 5 => 0x26fb2158241026fa2158241026f92158241026f82158241044fe76d954103cfe74d954103cfc74d954101cfe73d9541004fd73d954101cfc73d9541014fe72d9541004fd72d9541014fc72d9541004ff70d954100cfe70d9541004fd70d954100cfc70d9541006f710d9541006f510d95410067f6599541005df73595410a5dc7359541005ef725954109dec7259541005fb7059541095f870595410067f7559541004ff7459541006bf74595412767e54595412767c5459541004ff7359541006df7359541004df735954101cfe735954101cfc7359541006dc735954101cdc7359541004ff7259541006ef7259541004ef7259541014fe7259541014fc7259541006ec7259541014ec7259541004ff7159541006f771595412367e51595412367c5159541004ff7059541006fb7059541004fb705954100cfe7059541004fd705954100cfc7059541006f8705954100cf870595410067f50595410067d5059541006f71059541006f51059541004fe76195410467e65195410067d6519541024fe76d5141024fc76d51410067f65d51410467c65d514103f3e54d5141025f671d5141005f571d5141024fc76551410067f65551410467c6555141005f77155141025f4715514103fb44155141005fb7055141095f8705514101cfe76d8d410a6de63d8d41044fe75d8d41004fd75d8d41024fd74d8d4101cfc74d8d410a6dc53d8d410a6de43d8d41014fe72d8d41004fd72d8d41014fc72d8d4103cfd71d8d410a6df31d8d41004ff70d8d4100cfe70d8d41004fd70d8d4100cfc70d8d410a6dc6358d41004fe76d4d41004fd76d4d41044fc76d4d410467e65d4d410067d65d4d41006df63d4d4101edc63d4d410a75e53d4d41004ff7654d41004fe7654d41004fc7654d410467e6554d410067d6554d41005be76d0d4103ebe76d0d41006bf65d0d41006bd65d0d410a5bd73d0d4101ebe63d0d4101ebc63d0d41005bd72d0d41025be71d0d41025bc71d0d4103ebf61d0d4103fb761d0d4126fb710d0d4126fb510d0d41024fc7650d41006df6350d4101edc6350d41005f77150d41025f47150d41025bc7650d4101ebc7650d41024bc7650d41006bf6550d41006bd6550d4103dbf7350d4103f9f7350d410079f6350d4101ebe6350d4101ebc6350d410a79c6350d41005bf7250d41007b77150d41025be7150d41025bc7150d41007b47150d4103ebf6150d4103fb76150d410a79f3050d412679d3050d41267b71050d41267b51050d41014fe76d894109eee62d8941044fe75d8941004fd75d8941024fd74d8941014fc74d894101cfe73d8941004fd73d894101cfc73d894109eec52d894109eee42d894103cfd71d894109eef21d8941004ff70d894100cfe70d8941004fd70d894100cfc70d894109eec6258941004fe76d4941004fd76d
  | 6 => 0xf30596410067e30596410067d30596410067c30596410067f20596410067e20596410067d20596410067c20596410267f10596410267710596410267e10596410267d10596410067510596410267c10596410467e65d52410067d65d524103f3e54d5241025f671d5241005f571d524120efa60d5241044ff76552410467e65552410067d6555241005f77155241025f4715524103fb74155241005fb70552410adf870552411defa6055241004ff7558e41044fc7558e41026df7358e410bede4358e41004ff7258e41014fe7258e41014fc7258e410bedf3258e41024fc7158e41026bf4158e41026bd4158e41026de3158e41026dc3158e41004ff7058e4100cfe7058e41004fd7058e4100cfc7058e41044ff76d4e41024fe76d4e41004fd76d4e410467e65d4e410067d65d4e410bf5e53d4e411b6fa60d4e41004ff7654e41004fd7654e41024fc7654e410467e6554e410067d6554e411a6fa6054e4101cff7650e410067e6550e410067d6550e4101ede6350e41006dd6350e41005f77150e41025f47150e41186fa6050e41004ff7558a41044fc7558a41004ff7358a4101cfe7358a4101cfc7358a41026ef7258a410b6ee4258a410b6ee3258a41024fc7158a41026bf4158a41026bd4158a41026ee2158a41026ec2158a41004ff7058a4100cfe7058a41004fd7058a4100cfc7058a41044ff76d4a41024fe76d4a41004fd76d4a410467e65d4a410067d65d4a41176fa60d4a41004ff7654a41004fd7654a41024fc7654a410467e6554a410067d6554a41166fa6054a41014ff7650a410067e6550a410067d6550a41016ee6250a41006ed6250a41005f77150a41025f47150a41146fa6050a41004ff764ca41004fd764ca41024fc764ca410067e654ca410067d654ca4101ede634ca41006dd634ca41016ee624ca41006ed624ca410b7cc324ca4113efa604ca41006fb7558241006fa7558241006f97558241006f875582410aefb74582410aefa7458241006f974582410aef87458241006fb545824127efa5458241006f9545824127ef85458241006fb7358241006fa7358241006f97358241006f87358241006fb5358241006fa5358241006f95358241006f8535824127efb4358241006fa4358241006f9435824127ef84358241006fb7258241006fa7258241006f97258241006f87258241006fb5258241006fa5258241006f95258241006f8525824127efb4258241006fa4258241006f9425824127ef84258241006fb3258241006fa3258241006f93258241006f83258241026fb7158241026fa7158241026f97158241026f87158241026fb5158241026fa5158241026f95158241026f85158241026fb4158241026fa4158241026f94158241026f84158241026fb3158241026fa3158241026f93158241026f83158241
  | 7 => 0x4b4103cfe76d4b41004fd76d4b410467e65d4b410067d65d4b41004ff7654b41004fd7654b4103cfc7654b410467e6554b410067d6554b4103dbf7650b41086bf7650b4103ebf6550b4103f3e6550b41006bd6550b4103f3d6550b410063d6550b41005bf7350b4103faf7250b41016be6250b41016bc6250b41025be7150b41025bc7150b410cfaf2050b4128fad2050b41004ff764cb41004fd764cb4103cfc764cb410067e654cb410067d654cb4103dbe744cb41005bd744cb410cfcc324cb41005f7714cb41025f4714cb410467e65d47410067d65d474103dbe74d4741005bd74d4741044ff76547410467e65547410067d6554741005bf745474103dbc7454741027b641547410467f74996410467e74996410467d74996410467c74996410467f73996410467e73996410467d73996410467c73996412867f43996410067e43996412867c43996410467f72996410467e72996410467d72996410467c72996412867f42996410067e42996412867c42996410067f32996410067e32996410067c32996410267f71996410267e71996410267d71996410267c71996410267f41996410267e41996410267d41996410267c41996410267f31996410267e31996410267d31996410267c31996410267f21996410267e21996410267d21996410267c21996410467f70996410467e70996410467d70996410467c70996412867f40996410067e40996410067d40996412867c40996410067f30996410067e30996410067d30996410067c30996410067f20996410067e20996410067d20996410067c20996410267f10996410267e10996410267d10996410267c10996410267f7559641004ff735964101cfe735964101cfc73596410067e53596410067c5359641004ff7259641014fe7259641014fc72596410067e52596410067c5259641024fc71596410267e51596410267c5159641004ff705964100cfe7059641004fd705964100cfc70596410067f50596410067e50596410067d50596410067c5059641026f71059641006f510596410067f74596412767e74596410067d74596412767c74596410067f73596410067e73596410067d73596410067c73596412767f43596410067e43596412767c43596410067f72596410067e72596410067d72596410067c72596412767f42596410067e42596412767c42596410067f32596410067e32596410067c32596410267f71596410267e71596410267d71596410267c71596410267f41596410267e41596410267d41596410267c41596410267f31596410267e31596410267d31596410267c31596410267f21596410267e21596410267d21596410267c21596410067f70596410067e70596410067d70596410067c70596412767f40596410067e40596410067d40596412767c40596410067
  | 8 => 0x23e7e319974123e7c31997410067f219974123e7e219974123e7c21997410467f70997410467e70997410467d70997410467c709974103e7f409974103e7e409974103e7d409974103e7c40997410067f30997410067e30997410067d30997410067c30997410067f20997410067e20997410067d20997410067c209974123e7f10997410067e10997410067d109974123e7c109974103e7f7559741024fc745974103e7e545974103e7c5459741004ff735974101cfe735974101cfc73597410067e53597410067c535974103ebf4359741004ff7259741014fe7259741014fc72597410067e52597410067c525974103ebf4259741004ff705974100cfe7059741004fd705974100cfc70597410067f50597410067e50597410067d50597410067c505974103e7f745974103e7e745974103e7d745974103e7c74597410067f73597410067e73597410067d73597410067c735974103e7f435974103e3f435974103e7e435974103e7d435974103e7c43597410067f72597410067e72597410067d72597410067c725974103e7f425974103e3f425974103e7e425974103e7d425974103e7c42597410067f32597410067e32597410067c32597410067f71597412367e71597410067d71597412367c715974103e7f415974103e7e415974103e7d415974103e7c41597410067f31597412367e31597412367c31597410067f21597412367e21597412367c21597410067f70597410067e70597410067d70597410067c705974103e7f405974103e7e405974103e7d405974103e7c40597410067f30597410067e30597410067d30597410067c30597410067f20597410067e20597410067d20597410067c20597412367f10597410067e10597410067d10597412367c1059741004ff7558f41044fc7558f41024fc7458f4103edf7358f4103edf4358f4103edc4358f41004ff7258f41014fe7258f41014fc7258f41006de3258f410d6dc3258f410d6df3158f41004ff7058f4100cfe7058f41004fd7058f4100cfc7058f410d6df3058f41006dd3058f41044ff76d4f4103cfe76d4f41004fd76d4f410467e65d4f410067d65d4f410d75e53d4f41004ff7654f41004fd7654f4103cfc7654f410467e6554f410067d6554f4103dbf7650f4108ebf7650f4103ebf6550f4103f3e6550f41006bd6550f4103f3d6550f410063d6550f4103f9f7350f4101ebe6350f4101ebc6350f41005bf7250f41025be7150f41025bc7150f410d79f3050f412979d3050f41004ff7558b41044fc7558b41024fc7458b41004ff7358b4101cfe7358b4101cfc7358b4103eef7258b4103eef4258b4103eec4258b41006ef3258b410ceec3258b410ceef2158b41004ff7058b4100cfe7058b41004fd7058b4100cfc7058b410ceef2058b41006ed2058b41044ff76d
  | 9 => 0xc7058c5103cff76d0c51024fe76d0c51004fd76d0c510457e75d0c510057d75d0c5103ebe64d0c51006bd64d0c510073d54d0c51196fa60d0c51004ff7650c51004fd7650c51024fc7650c5103ebe6450c51006bd6450c510073d5450c5101ede6350c51006dd6350c51186fa6050c51014fd7558851004ff745885103cfc74588510467f54588510067d5458851004ff735885101cfe735885101cfc7358851024ff7258851026ef7258851046ef5258851046ec52588510e6ee42588510e6ee3258851024fc71588510267f51588510267d5158851026ee2158851026ec2158851004ff705885100cfe7058851004fd705885100cfc705885103cff76d0851024fe76d0851004fd76d08510457e75d08510057d75d085103ebe64d0851006bd64d08510073d54d0851156fa60d0851004ff7650851004fd7650851024fc765085103ebe6450851006bd64508510073d5450851016ee6250851006ed6250851146fa6050851004ff764c851004fd764c851024fc764c8510057f754c8510457c754c85101ede634c851006dd634c851016ee624c851006ed624c8510e7cc324c851005f7714c851025f4714c85113efa604c851046fb7558051046fa7558051046f97558051046f87558051006fb7458051006fa7458051006f97458051006f87458051046fb54580510467b5458051046fa5458051046f95458051006795458051046f85458051006fb7358051006fa7358051006f97358051006f87358051046fb5358051046fa5358051046f95358051046f85358051006fb4358051006fa4358051006f94358051006f84358051006fb7258051006fa7258051006f97258051006f87258051046fb5258051046fa5258051046f95258051046f85258051006fb4258051006fa4258051006f94258051006f84258051006fb3258051006fa3258051006f93258051006f83258051026fb7158051026fa7158051026f97158051026f87158051026fb51580510267b5158051026fa5158051026f25158051026f95158051026795158051046f15158051026f85158051026fb4158051026fa4158051026f94158051026f84158051026fb3158051026fa3158051026f93158051026f83158051026fb2158051026fa2158051026f92158051026f8215805103e7f749974103e7e749974103e7d749974103e7c74997410467f73997410467e73997410467d73997410467c739974103e7f439974103e7e439974103e7d439974103e7c43997410467f72997410467e72997410467d72997410467c729974103e7f429974103e7e429974103e7d429974103e7c42997410067f32997410067e32997410067c32997410467f71997410467e71997410467d71997410467c719974103e7f419974103e7e419974103e7d419974103e7c41997410067f3199741
  | 10 => 0x4d5101e7e6354d5101e7c6354d511075c6354d510057f7254d51007777154d510257e7154d510257c7154d51007747154d510467f6154d51047776154d512cd7f7054d512cd7d7054d512c7771054d512c7751054d51004fe76d0d51004fd76d0d5103cfc76d0d512757f75d0d510457c75d0d5103ebe64d0d512773e54d0d51006df63d0d5101edc63d0d51004ff7650d51004fe7650d51004fc7650d510057f7550d510457c7550d510073e5450d51014fe76d89510feee62d8951024fd75d8951014fc75d895103cfe74d8951004fd74d895101cfe73d8951004fd73d895101cfc73d89510feee52d89510feec42d8951006ef32d89510feec32d8951044fd71d89510feef21d8951004ff70d895100cfe70d8951004fd70d895100cfc70d89510feef20d8951006ed20d8951005df7358951105dc73589510feec62589510057e76d49510467e76d49512757e74d49510067f64d49510057d73d49510fd7d72d49510167e62d49510167c62d49510257e71d49510257c71d49510467f61d49510477761d49510457f70d49512bd7d70d49512b77710d49512b77510d4951024fc7654951006ef6254951016ec6254951005f77154951025f471549510257c76549510167c76549510247c76549512757c74549510067f64549510057f73549510457f72549510476f72549510076f62549510167e62549510167c62549510ff6c62549510077771549510257e71549510257c71549510077471549510467f61549510477761549512ad7f70549512ad7d70549512a77710549512a7751054951004fe76d0951004fd76d095103cfc76d09512757f75d09510457c75d095103ebe64d09512773e54d0951006ef62d0951016ec62d0951004ff7650951004fe7650951004fc76509510057f75509510457c75509510073e5450951004ff764c951004fe764c951004fc764c9510457e754c9510057d754c9510ffcc324c951026bf7459051046bf5459051046bc5459051004ff735905101cfe735905101cfc7359051004ff7259051014fe7259051014fc7259051026be4159051026bc4159051004ff705905100cfe7059051004fd705905100cfc70590510457f76550510067f76550510047f76550510457f74550510473f745505103e7e645505103e7c64550512357f71550512367e61550510477661550510077b705505129f7870550510467f60550510477a605505129e7d605505104779605505101cfd7558c51004ff7458c5103cfc7458c510467f5458c510067d5458c51024ff7358c51026df7358c51046df5358c51046dc5358c510eede4358c51004ff7258c51014fe7258c51014fc7258c510eedf3258c51024fc7158c510267f5158c510267d5158c51026de3158c51026dc3158c51004ff7058c5100cfe7058c51004fd7058c5100cf
  | 11 => 0x67f5458a510067d5458a51004ff7358a5101cfe7358a5101cfc7358a51026ef7258a51116ee5258a51116ee3258a51024fc7158a510267f5158a510267d5158a51026ee2158a51026ec2158a51004ff7058a5100cfe7058a51004fd7058a5100cfc7058a51014ff7654a51016ee6254a51006ed6254a51005f77154a51025f47154a5103cff76d0a51024fe76d0a51004fd76d0a510457e75d0a510057d75d0a5103ebe64d0a51006bd64d0a510073d54d0a51004ff7650a51004fd7650a51024fc7650a5103ebe6450a51006bd6450a510073d5450a51004ff764ca51004fd764ca51024fc764ca510057f754ca510457c754ca5101ede634ca51006dd634ca51016ee624ca51006ed624ca51117cc324ca5101cfe73d9151004fd73d915101cfc73d9151014fe72d9151004fd72d9151014fc72d915123e7e51d915123e7c51d9151004ff70d915100cfe70d9151004fd70d915100cfc70d91510067f50d91510067d50d9151006f710d9151006f510d9151006bf6499151005df7359151105dc7359151005ef72591510fdec7259151005fb70591510f5f8705915103ebe6419151006bd6419151024fe7695151006bf649515103ebc64951510473f5495151025f67195151005f571951510247e76951510457e74951512767f64951510073f64951510063f64951512773c64951510057d73951510057d72951510257e71951512777671951512777571951510257c71951510467f61951510477761951512757f70951512fd7d70951512f77710951512f7751095151024fc7655151006bf645515103ebc6455151005f77155151025f47155151005fb70551510f5f870551510057e76151510467e76151510047e76151512757e74151510473e74151512767f64151510057d73151510057d72151510257e71151510257c71151510467f61151510477761151510457f70151512ed7d70151512e77710151512e775101515101cfe76d8d51106de63d8d51024fd75d8d5101cfc75d8d5103cfe74d8d51004fd74d8d51106de53d8d51106dc43d8d51014fe72d8d51004fd72d8d51014fc72d8d51006de32d8d51106dc32d8d51044fd71d8d51106df31d8d51004ff70d8d5100cfe70d8d51004fd70d8d5100cfc70d8d51106df30d8d51006dd30d8d51106dc6358d51005ef7258d510fdec7258d510057e76d4d510467e76d4d512757e74d4d510067f64d4d511057d73d4d5101e7e63d4d5101e7c63d4d510057d72d4d510257e71d4d510257c71d4d510467f61d4d510477761d4d510457f70d4d512dd7d70d4d512d77710d4d512d77510d4d51024fc7654d51006df6354d5101edc6354d51005f77154d51025f47154d510257c7654d5101e7c7654d510247c7654d512757c7454d510067f6454d510457f7354d510475f7354d510075f635
  | 12 => 0xf7254f510257e7154f510257c7154f5131d7f7054f5131d7d7054f5103cff76d0f51044fe76d0f51004fd76d0f512857f75d0f510457c75d0f5103ebe64d0f51006bd64d0f512873e54d0f51004ff7650f51004fd7650f51044fc7650f510057f7550f510457c7550f5103ebe6450f51006bd6450f510073e5450f51024fc7558b51004ff7458b5103cfc7458b51004ff7358b5101cfe7358b5101cfc7358b51046ef7258b51046ef5258b51046ec5258b5112eef2158b51004ff7058b5100cfe7058b51004fd7058b5100cfc7058b510457f7654b510e67f7654b512857c7454b510067d6454b510057f7354b510476f7254b510167e6254b510167c6254b510257e7154b510257c7154b513157f7054b513157d7054b5103cff76d0b51044fe76d0b51004fd76d0b512857f75d0b510457c75d0b5103ebe64d0b51006bd64d0b512873e54d0b51004ff7650b51004fd7650b51044fc7650b510057f7550b510457c7550b5103ebe6450b51006bd6450b510073e5450b51004ff764cb51004fd764cb51044fc764cb510457e754cb510057d754cb5112fcc324cb51005f7714cb51025f4714cb51026bf7459251004ff735925101cfe735925101cfc7359251004ff7259251014fe7259251014fc7259251024fc7159251026be4159251026bc4159251004ff705925100cfe7059251004fd705925100cfc7059251006be4059251006bc4059251026f71059251006f5105925123d7d76d52510467d76d525103e7e64d525103e7c64d52510457f71d525123d7d71d52510477661d525123e7f60d525130e7d60d525123f7710d525130f7510d525103ebe6495251006bd64952510473f5495251025f67195251005f5719525103cff765525103ebe6455251006bd6455251005f77155251025f47155251047775155251005fb705525110df8705525103c7f76552510457f74552510473f745525103e7e64552512373e64552512373d645525103e7c64552512357f71552510077771552512377471552510467e61552510077b70552513077870552512367f60552513067d6055251237771055251307751055251004ff7458e5103cfc7458e510067f5458e510067d5458e51026df7358e5111ede5358e51004ff7258e51014fe7258e51014fc7258e5111edf3258e51024fc7158e510267f5158e510267d5158e51026de3158e51026dc3158e51004ff7058e5100cfe7058e51004fd7058e5100cfc7058e5101cff7654e5101ede6354e51006dd6354e51005f77154e51025f47154e51047775154e5103cff76d0e51024fe76d0e51004fd76d0e510457e75d0e510057d75d0e5103ebe64d0e51006bd64d0e510073d54d0e51004ff7650e51004fd7650e51024fc7650e5103ebe6450e51006bd6450e510073d5450e51004ff7458a5103cfc7458a51
  | 13 => 0x913215def725913218fcc3259132005f77159132005f47159132005fb705913213df87059132004ff75591320067f75591320047f7559132044fc75591320067c75591320447c7559132006bf745913219cff7359132006df735913218cff7259132006ef7259132004ff7159132006f77159132004f77159132024fc7159132006f47159132024f47159132004ff7059132006fb7059132004fb705913200cfe7059132004fd705913200cfc7059132006f8705913200cf8705913214edf3059132006dd305913218eef2059132006ed205913233cfe76191320057e75191320057d751913203ebe6419132006bd6419132337cc3219132044ff76d5132004fe76d5132004fd76d5132044fc76d51320467e65d51320067d65d5132217cc32d513203cff7695132004fe7695132004fd769513203cfc76951320067f65951320467c659513203ebe6495132006bd64951320073f54951321ffcc3295132004ff7655132004fe7655132004fd7655132004fc76551320467e65551320067d655513203ebe6455132006bd6455132005df735513201ddc7355132005ef7255132015ec72551321e7cc3255132005fb705513213df8705513203cff7615132004fe7615132004fd761513203cfc76151320067f65151320467c65151321cfcc3215132024fe76d853222fcc32d8532044fe75d8532004fd75d853203cfe74d8532004fd74d8532014fd73d853201cfd72d853224ef631d853222ef621d8532004ff70d853200cfe70d8532004fd70d853200cfc70d8532006f710d8532006f510d8532077cc3298532006f761985320057f75585320057c7558532067cc32585320057e75185320057d7518532005be7418532005bd741853232fcc3218532026f66118532006f5611853213dfa7018532005f97018532024fc75593510247c7559351046bf7459351046bf54593510467c5459351046bc5459351004ff735935101cfe735935101cfc73593510467f5359351004ff7259351014fe7259351014fc72593510467f52593512367e51593510467c5159351004ff7059351006fb7059351004fb705935100cfe7059351004fd705935100cfc7059351006f8705935100cf870593510467f50593510067d5059351006be4059351006bc40593510457d76953512867d76953510473e74953510467f64953512867d64953510057d73953510057d72953510257e71953510257c71953512857f70953513257d7095351024fc7558f51004ff7458f5103cfc7458f51046df7358f51046df5358f51046dc5358f51004ff7258f51014fe7258f51014fc7258f51136df3158f51004ff7058f5100cfe7058f51004fd7058f5100cfc7058f510457f7654f510ee7f7654f512857c7454f510067d6454f510475f7354f5101e7e6354f5101e7c6354f510057
  | 14 => 0x46bc7655142014bc765514203dbf755514203f3f75551420073f6555142046be6555142046bc65551420073c6555142007af7255142015be7255142015bc72551421e7ac725514203ebf625514203faf62551421e73f52551421e73d5255142005bf7155142007bb7055142367b870551423673f50551423673d50551421e7af2055142367ad205514201cfe76d8d4214ede63d8d42044fe75d8d42004fd75d8d42014fd74d8d42006be54d8d42006bd54d8d4214ede43d8d4203cfd72d8d4219edf32d8d42024fe71d8d42004fd71d8d42004ff70d8d4200cfe70d8d42004fd70d8d4200cfc70d8d4219eef20d8d42006ed20d8d420057f7558d420057c7558d4214edc6358d42005f77158d42005f47158d42005fb7058d42145f87058d42004fe76d4d42004fd76d4d42044fc76d4d4203dbe74d4d42005bd74d4d420073d54d4d4214f5e53d4d42015ee72d4d42005ed72d4d42004ff7654d42004fe7654d42004fc7654d420073d5454d42014fc7650d42006df6350d4201edc6350d42005ef7250d42015ec7250d42044fe75d8542004fd75d854201cfe73d8542004fd73d854201cfc73d854203cfd72d8542006f731d8542006f431d85420cef621d8542004ff70d854200cfe70d8542004fd70d854200cfc70d85420057e75985420057d7598542006f76198542145fa7098542005f97098542026f66118542006f56118542044fe76d9532357cc32d953203cfe74d9532004fd74d9532014ff73d9532014fd73d953235e7f53d953235e7d53d953201cff72d953201cfd72d95323567f52d95323567d52d9532024fe71d9532004fd71d9532004ff70d953200cfe70d9532004fd70d953200cfc70d95320067f50d95320067d50d95321acfd76995320067f65995321addd739953216ded72995321bfcc3299532044ff76595321bddf735953217def72595321afcc3259532005f77159532005f471595320067f7559532004ff745953203cfc74595321bcff7359532006df73595321acff7259532006ef7259532004ff7159532006f77159532004f77159532024fc7159532006f47159532024f47159532004ff705953200cfe7059532004fd705953200cfc7059532354fe76195320467e65195320067d6519532005be7419532005bd741953234fcc321953203cfe76d913233fcc32d9132044fe75d9132004fd75d9132014ff73d9132014fd73d9132346bf43d9132346bd43d913201cff72d913201cfd72d913233ebf42d913233ebd42d9132024fe71d9132004fd71d9132004ff70d913200cfe70d9132004fd70d913200cfc70d9132346df30d9132006dd30d913233eef20d9132006ed20d913218cfd7699132006bf649913218ddd739913214ded729913219fcc329913203cff76591320057f75591320057c755913219ddf735
  | 15 => 0x76198552005df735855216ddc7358552026f66118552006f56118552165fa7018552005f9701855203e7f7559742014fe7459742014fc745974203e7e545974203e7c5459742004ff735974201cfe735974201cfc73597421e67f52597421e67d5259742004ff7159742024fc7159742004ff705974200cfe7059742004fd705974200cfc70597420067f50597420067d505974203dbf7655342006bf765534203f3f755534203f3f6555342046be655534203ebc655534203f3c6555342015be7255342015bc72553421e73f52553421e73d5255342005bf7155342007bb7055342377b870553423773f50553423773d5055342004ff7558f42044fc7558f42014fe7458f42014fc7458f4203ebe5458f42006bd5458f4203edf7358f4215ede5358f4203edf4358f4203edc4358f4218edf3258f42004ff7158f42024fc7158f4203ebf4158f4215edc3158f42004ff7058f4200cfe7058f42004fd7058f4200cfc7058f4215edf3058f42006dd3058f42044ff76d4f4203cfe76d4f42004fd76d4f420467e65d4f420067d65d4f4203dbe74d4f42005bd74d4f420073d54d4f4215f5e53d4f42004ff7654f42004fd7654f4203cfc7654f420467e6554f420067d6554f420073d5454f4201ede6354f42006dd6354f42004ff7558742044fc7558742014fc7458742004ff735874201cfe735874201cfc735874203ef7715874203ef7415874203ef4415874209ef62158742004ff705874200cfe7058742004fd705874200cfc7058742006f71058742006f51058742044fe76d954201cfe73d9542004fd73d954201cfc73d95420067e53d95420067c53d954203cff72d954203cfd72d95421fe7f52d95421fe7d52d9542024fe71d9542004fd71d9542004ff70d954200cfe70d9542004fd70d954200cfc70d95420067e50d95420067c50d95420067f65995421e5bd7499542215bf7459542005fb7059542145f870595420067f7559542214ff7459542006bf7459542004ff735954201cfe735954201cfc73595421e4ff7259542006ef7259542004ff7159542024fc7159542004ff7059542006fb7059542004fb705954200cfe7059542004fd705954200cfc7059542006f8705954200cf870595421fcfe76195420467e65195420067d6519542014fe76d5142014fc76d51420067f65d51420467c65d514203f3e54d5142015ee72d5142005ed72d51421cdbe769514203ebe76951421e5bd7595142046be6595142046bc6595142015be7295142015bc729514203ebf629514203faf6295142005bd71951421ffaf209514236fad2095142044ff7655142014fe76551421e4fd7655142014fc76551420067f65551420467c655514203f3c5455142005ef7255142015ec725514203fac4255142005fb7055142145f87055142015bc7655142
  | 16 => 0x535238f7870553520467f605535238e7d6055352014fe7558f52014fc7558f52004ff7458f5203cfc7458f520467f5458f520067d5458f52046df7358f52046df5358f52046dc5358f5217ede4358f521aedf3258f52004ff7158f52024fc7158f520467f5158f52004ff7058f5200cfe7058f52004fd7058f5200cfc7058f5203cff76d0f52044fe76d0f52004fd76d0f520457e75d0f520057d75d0f5203ebe64d0f52006bd64d0f520073d54d0f52004ff7650f52004fd7650f52044fc7650f5203ebe6450f52006bd6450f520073d5450f5201ede6350f52006dd6350f52014fc7558752004ff745875203cfc7458752004ff735875201cfe735875201cfc7358752046f77158752046f75158752046f451587520fef62158752004ff705875200cfe7058752004fd705875200cfc7058752006f71058752006f5105875203cfe76d915201cfe73d9152004fd73d915201cfc73d9152044fd72d9152216bf42d9152024fe71d9152004fd71d9152004ff70d915200cfe70d9152004fd70d915200cfc70d9152006be40d9152006bc40d9152006bf6499152005fb7059152165f8705915203ebe6419152006bd64191521cd7e76d51520467e76d515203e7e64d515203e7c64d51520157e72d51520157c72d51520467f62d51520476f62d51520057d71d515223e7c61d51523867f60d51523867d60d5152014fe76951521e57d7595152006bf649515203ebc64951520473f5495152015ee7295152005ed7295152014fc7655152006bf645515203ebc64551520473c5455152005ef7255152015ec7255152005fb7055152165f870551520157c765515203e7c76551520147c76551520457f74551520473f74551520073f645515203e7e645515203e7c64551520073c64551520076f72551520157e72551520157c72551521e76c72551520467f62551520476f62551520057f71551522367c61551520077b705515237f78705515237e7f605515237e7d605515201cfe76d8d5216ede63d8d52014fd75d8d5203cfe74d8d52004fd74d8d520067f54d8d520067d54d8d5216ede53d8d52044fd72d8d521bedf32d8d52024fe71d8d52004fd71d8d5216edc31d8d52004ff70d8d5200cfe70d8d52004fd70d8d5200cfc70d8d5216edc6358d52005f77158d52005f47158d52014fc7654d52006df6354d5201edc6354d52005ef7254d52015ec7254d52004fe76d0d52004fd76d0d5203cfc76d0d520457e75d0d520057d75d0d520073d54d0d52015ee72d0d52005ed72d0d52004ff7650d52004fe7650d52004fc7650d520073d5450d5203cfe74d8552004fd74d855201cfe73d8552004fd73d855201cfc73d8552044fd72d8552006f731d8552006f431d855212ef621d8552004ff70d855200cfe70d8552004fd70d855200cfc70d8552006f
  | 17 => 0x6f51058743044fe76d954303cff73d954303cfd73d95432067f53d95432067d53d9543014fe72d9543004fd72d9543014fc72d95430067e52d95430067c52d9543024fe71d9543004fd71d9543004ff70d954300cfe70d9543004fd70d954300cfc70d95430067e50d95430067c50d95430067f65995431edbd749954321dbf7459543005fb7059543185f870595430067f755954321cff7459543006bf74595431ecff7359543006df7359543004ff7259543014fe7259543014fc7259543004ff7159543024fc7159543004ff7059543006fb7059543004fb705954300cfe7059543004fd705954300cfc7059543006f8705954300cf87059543204fe76195430467e65195430067d651954301cfe76d514301cfc76d51430067f65d51430467c65d514303f3e54d514301dde73d5143005dd73d51431d5be769514303ebe76951431edbd7595143046be6595143046bc659514301dbe739514301dbc739514303ebf639514303f9f6395143005bd71951432079f309514339f9d3095143044ff765514301cfe76551431ecfd765514301cfc76551430067f65551430467c655514303f3c5455143005df735514301ddc735514303f9c4355143005fb7055143185f8705514301dbc7655143046bc765514301cbc765514303dbf755514303f3f75551430073f6555143046be6555143046bc65551430073c65551430079f735514301dbe735514301dbc73551431ef9c735514303ebf635514303f9f63551431ef3f53551431ef3d5355143005bf7155143007bb7055143397b870551433973f50551433973d50551431ef9f30551433979d3055143014fe76d894318eee62d8943044fe75d8943004fd75d894301cfd74d8943006be54d8943006bd54d894303cfd73d894318eee42d894318eee32d8943024fe71d8943004fd71d8943004ff70d894300cfe70d8943004fd70d894300cfc70d894315edf30d8943006dd30d89430057f75589430057c755894318eec6258943005f77158943005f47158943005fb7058943185f87058943044fe75d8543004fd75d854303cfd73d8543014fe72d8543004fd72d8543014fc72d85430d6f631d8543006f721d8543006f421d8543004ff70d854300cfe70d8543004fd70d854300cfc70d85430057e75985430057d7598543006f76198543185fa7098543005f97098543026f66118543006f56118543014fc7559352046bf7459352046bf5459352046bc5459352004ff735935201cfe735935201cfc73593521e6bf4259352004ff7159352024fc7159352004ff705935200cfe7059352004fd705935200cfc70593520457f76553520067f76553520473f74553520473f645535203e7e645535203e7c64553520473c64553520157e72553520157c72553520057f71553522367e61553520077b705
  | 18 => 0xe71d9153004fd71d9153004ff70d915300cfe70d9153004fd70d915300cfc70d9153006be40d9153006bc40d9153006bf6499153005fb70591531a5f8705915303ebe6419153006bd64191531d57e76d51530467e76d515303e7e64d515303e7c64d515301d7e73d515301d7c73d51530467f63d51530475f63d51530057d71d515323e7c61d51533b67f60d51533b67d60d515301cfe76951531ed7d7595153006bf649515303ebc64951530473f549515301dde7395153005dd739515301cfc7655153006bf645515303ebc64551530473c5455153005df735515301ddc7355153005fb70551531a5f8705515301d7c765515303e7c765515301c7c76551530457f74551530473f74551530073f645515303e7e645515303e7c64551530073c64551530075f735515301d7e735515301d7c73551531ef5c73551530467f63551530475f63551530057f71551532367c61551530077b70551533af7870551533ae7f60551533ae7d6055153014fe76d89531aeee62d895301cfd75d895303cfe74d8953004fd74d89530067f54d89530067d54d8953044fd73d89531aeee52d89531aeee32d8953024fe71d8953004fd71d89531aeec21d8953004ff70d895300cfe70d8953004fd70d895300cfc70d89531aeec6258953005f77158953005f4715895303cfe74d8553004fd74d8553044fd73d8553014fe72d8553004fd72d8553014fc72d8553136f631d8553006f721d8553006f421d8553004ff70d855300cfe70d8553004fd70d855300cfc70d8553006f76198553005ef72585531adec7258553026f66118553006f561185531a5fa7018553005f9701855303e7f755974301cfe745974301cfc745974303e7e545974303e7c54597431ee7f53597431ee7d5359743004ff7259743014fe7259743014fc7259743004ff7159743024fc7159743004ff705974300cfe7059743004fd705974300cfc70597430067f50597430067d505974303dbf7655343006bf765534303f3f755534303f3f6555343046be655534303ebc655534303f3c655534301dbe735534301dbc73553431ef3f53553431ef3d5355343005bf7155343007bb70553433a7b870553433a73f50553433a73d5055343004ff7558b43044fc7558b4301cfe7458b4301cfc7458b4303ebe5458b43006bd5458b4303eef7258b4319eee5258b4303eef4258b4303eec4258b4319eee3258b43004ff7158b43024fc7158b4303ebf4158b4319eec2158b43004ff7058b4300cfe7058b43004fd7058b4300cfc7058b4319eef2058b43006ed2058b43004ff7558743044fc755874301cfc7458743004ff7258743014fe7258743014fc725874303ef7715874303ef7415874303ef441587430a6f63158743004ff705874300cfe7058743004fd705874300cfc7058743006f71058743
  | 19 => 0x8154006fa73d8154006f973d8154006f873d81543cefb53d8154006fa53d81543cef853d81543c6fb43d8154006fa43d81543c6f843d8154006fb72d8154006fa72d8154006f972d8154006f872d81543cefb52d8154006fa52d81543cef852d81543c6fb42d8154006fa42d81543c6f842d8154006fb32d8154006fa32d8154006f832d8154006fb71d8154006fa71d8154006f971d8154006f871d81543cefb51d81543cef851d81543c6fb41d81543c6f841d8154006fb31d8154006f831d8154006fb21d8154006f821d815403e7f5458c5403ebe5458c5403e7d5458c54046bd5458c5403cff7358c5403edf7358c54046df5358c54046dc5358c5403edf4358c5403edc4358c54004ff7258c54014fe7258c54014fc7258c54006de3258c541d6dc3258c54004ff7158c54024fc7158c540467f5158c541d6df3158c54004ff7058c5400cfe7058c54004fd7058c5400cfc7058c541d6df3058c54006dd3058c5403e7f545885403ebe545885403e7d5458854046bd5458854004ff735885401cfe735885401cfc735885403cff725885403eef7258854046ef5258854046ec525885403eef425885403eec4258854006ef32588541ceec3258854004ff7158854024fc71588540467f51588541ceef2158854004ff705885400cfe7058854004fd705885400cfc70588541ceef2058854006ed2058854004ff735845401cfe735845401cfc7358454004ff7258454014fe7258454014fc725845403ef77158454046f75158454046f4515845403ef7415845403ef44158454004ff705845400cfe7058454004fd705845400cfc7058454006f71058454006f5105845401cfc7559353046bf7459353046bf5459353046bc54593531eebf4359353004ff7259353014fe7259353014fc7259353004ff7159353024fc7159353004ff705935300cfe7059353004fd705935300cfc70593530457f76553530067f76553530473f74553530473f645535303e7e645535303e7c64553530473c645535301d7e735535301d7c73553530057f71553532367e61553530077b70553533bf7870553530467f60553533be7d605535301cfe7558b5301cfc7558b53004ff7458b5303cfc7458b530467f5458b530067d5458b53046ef7258b53046ef5258b53046ec5258b531beee4258b531beee3258b53004ff7158b53024fc7158b530467f5158b53004ff7058b5300cfe7058b53004fd7058b5300cfc7058b5301cfc7558753004ff745875303cfc7458753004ff7258753014fe7258753014fc7258753046f77158753046f75158753046f45158753106f63158753004ff705875300cfe7058753004fd705875300cfc7058753006f71058753006f5105875303cfe76d9153044fd73d915321ebf43d9153014fe72d9153004fd72d9153014fc72d9153024f
  | 20 => 0x3d73d30d52543d73c30d52543d73f20d52543d73e20d52543d73d20d52543d73c20d52543d73f10d52543d73e10d52543d73d10d52543d73c10d525403cfc7458e5403e7f5458e5403e7d5458e5403edf7358e54206de5358e5403edf4358e5403edc4358e54004ff7258e54014fe7258e54014fc7258e54004ff7158e54024fc7158e54004ff7058e5400cfe7058e54004fd7058e5400cfc7058e54206df3058e54006dd3058e5403cfc7458a5403e7f5458a5403e7d5458a54004ff7358a5401cfe7358a5401cfc7358a5403eef7258a541feee5258a5403eef4258a5403eec4258a54004ff7158a54024fc7158a54004ff7058a5400cfe7058a54004fd7058a5400cfc7058a541feef2058a54006ed2058a5403cfc7458654004ff735865401cfe735865401cfc735865403ebf4358654004ff7258654014fe7258654014fc725865403ebf425865403ef7715865403ef7415865403ef44158654004ff705865400cfe7058654004fd705865400cfc7058654006f71058654006f5105865401cfe76d8d541eede63d8d54006f860d8d5403cfd75d8d54044fd74d8d541eede53d8d541eede43d8d54014fe72d8d54004fd72d8d54014fc72d8d541eedf32d8d54024fe71d8d54004fd71d8d541eedc31d8d54004ff70d8d5400cfe70d8d54004fd70d8d5400cfc70d8d541eedc6358d54005fb7058d541ddf87058d54006f86058d54014fe76d89541e6ee62d8954006f860d895403cfd75d8954044fd74d895401cfe73d8954004fd73d895401cfc73d89541e6ee52d89541e6ee42d89541e6ee32d8954024fe71d8954004fd71d89541e6ec21d8954004ff70d895400cfe70d8954004fd70d895400cfc70d89541e6ec6258954005fb70589541ddf87058954006f86058954006f860d85542867e54d85542867c54d855401cfe73d8554004fd73d855401cfc73d8554014fe72d8554004fd72d8554014fc72d8554004ff70d855400cfe70d8554004fd70d855400cfc70d85540067f50d85540067d50d8554006f761985541ddfa7098554005f97098554006f86098554005df73585541eddc7358554005ef72585541e5ec7258554005fb70585541ddf87058554006f86058554026f66118554006f56118554006f860185541ddfa76d81541defa76d815400cfa76d81543c77b75d81541df7875d81543cfbb54d81543c77a54d81543c77854d81543cfb854d8154006fb63d8154006fa63d8154006f963d8154006f863d8154006fb62d8154006fa62d8154006f962d8154006f862d8154006fb61d8154006fa61d8154006f961d8154006f861d81543c6fb75d81541defa75d81541def975d81541def875d81543cefb74d81541defa74d81541def974d81541def874d81543cefb54d81543c6fa54d81541def954d81543c6f854d8154006fb73d
  | 21 => 0x10008000000002004800401c00000480000660300088004000001000000808e019003800c01003f002006c036008002807c00402200080280720110000068000006004000c010007000002400400800300000140160058014044004009800800600100d800000a00c003004000e001012800801e02200100100060010140044016009008801800000d00300240020160098014024000004003400a0080018040014003002800001c004003806804400100500000a203e00000240000000078018004017005801801200400f00100000020068044014008002800c00c0090020000000006001805c004000001801800800d01180000080780078068006000000009c00200e0078000054000006000000601f0010014002005004000000e012000001000001a00080040100010000010002004001800806a01a00b808800a00100100640000000000000004003001003800a01f00000100020030060010050000002000001800d00d80000000030010000004006000803801000000c001c01a00000f000000000000f0018000002001807001c003000800000c00000c80e4008021004802400000103cfc7558f54046be5458f54046bd5458f54046df7358f54046df5358f54046dc5358f5421ede4358f54004ff7258f54014fe7258f54014fc7258f54004ff7158f54024fc7158f54004ff7058f5400cfe7058f54004fd7058f5400cfc7058f5403cfc7558b54046be5458b54046bd5458b54004ff7358b5401cfe7358b5401cfc7358b54046ef7258b54046ef5258b54046ec5258b54216ee4258b54004ff7158b54024fc7158b54004ff7058b5400cfe7058b54004fd7058b5400cfc7058b5403cfc755875403c7c75587542767e54587540467c5458754004ff735875401cfe735875401cfc73587540467f5358754004ff7258754014fe7258754014fc72587540467f5258754046f77158754046f751587540467c5158754046f45158754004ff705875400cfe7058754004fd705875400cfc70587540467f50587540067d5058754006f71058754006f5105875403f3d76d525403d3d76d52540463d76d52540473f73d52540473e73d52540473d73d52540473c73d525403f3f63d525403f3e63d525403f3d63d525403f3c63d52540473f72d52540473e72d52540473d72d52540473c72d525403f3f62d525403f3e62d525403f3d62d525403f3c62d52543e73f32d52543df3e32d52543df3c32d52540473f71d52540473e71d52540473d71d52540473c71d525403f3f61d525403f3e61d525403f3d61d525403f3c61d52543e73f31d52543e73c31d52543df3f21d52543df3c21d52540473f70d52540473e70d52540473d70d52540473c70d525403f3f60d525403f3e60d525403f3d60d525403f3c60d52543d73f30d52543d73e30d5254
  | 22 => 0x800c004000004800003c0000008000004000002000000600501a804000202300a807801a006000006802800e0000018002004002007c004000001009802a02000080000040030008018000003001801000a0000020028004000001800802000000080bc00e00b0000018000003000801800001e0000020002000000001005e002000003c08002000f801000000100180240520030068004000008001000000c00d00080a001400000000ac02c05701100080040200038000000000006801c01e006001002802802d00980480c8002001801400a0000010050000000000000002c009000800c032002000001400e0020028000000005000000000001d002015c000000005001000e000000800000600800e001401c018005801800000100f00080200010038004000000005008803801c0000004010004000000c000001009000c00800c009000000200200b800000200000080280000020008040020003000801c00e0000030048022008000001803200700080180000020060168000006001000400a00e000800000a0000000000006000007009c0080040000000014008000800c06e01b002000000800500a003801c000003000c002006003001400200101e8010014002001000c002013000000800800503f001c0100010018058002012001000001800000d007001c000001801c00200700980240060000010004000002015801800000f015003800e0030038074000006019000402a00f000806001c0000000000000003001802401600700a8000000006003800000600000a004c0000030048038000002006805000600400400100260150008064004001000800800000200000340000000000054008001003801800c00f00600b405e00a001800800800700b8014010004001001802000b013800004e00c005802c006006003000402e0260020048000001000001800e000000000800000d00000000080080050000004012000000c000000001007c05e007000000000e004001001000000700f00700000000000000008014003800803c00600500900080020000028000000012800c00000e012000800201c0010000002006001001800e0040018034000048000006402c006003006402a00600100e800200a00000080080020010004016005005802c00a0110000018008001000001c00000301480080000020048054000001000800c02e00400200c0054000006800400200000080080500020038074000000000001c00e000007007410200001980d400002c0150004022001000004000800000c800c01600900980000200020030058004007001000800e00701e803400600d00e8018008003007803801c00100680a800000b000002400800000000000000070040010080000004000800c000000001c00c0010000004074003000007402a
  | 23 => 0x31a16f2870d59af00ed1b510801ca8375ec002cd46aed4108001bbc5eb0358b18aacd2156537a5114dea28b0b6953c4c012127c542049f5cf9131c2c4440ecb1f0be4d2f14da13cb4641f1c792c0152b1d66cadbc6eaaf8215a59010a8c23691a5018e39820c2e81a248621c398ed28a3334032c5154e6e615324e9c0c74120aa968c54e0d5c42c0cc88e2c1fea625338ada6c904f503a5ff0b9b92d6d222b0b4067c1489bd3372864e8e4311dc0a0528404466f2b5c2cea986b22df89c6c3139a22c410467906110e045800173080007820000d380010562d500015e44ce0006c48ab40000003f0abbca540000708000000000505b49558214b54324387840bd402a0394e20000a237480002630000c7400021a6f39eb12fe07f03915108025d43dd02946b2be02f08000cda5696118c24acc95b530b8202741e24f42f948fad913af30295604da0002d79bee6013b721200000ab0001ca8aae6912292bf0000d8c6300ff963c7be000186c000a1f6b326e12b46aa0000001a620003d199740000003cc8ea177432c0b705c96c21cd128ada8f6a6624090000e2c4224b990bc15a22726304441764be56fabf8b9a6ad372aef0030e145a70aa000092622da35c000a565f42145336db40000f293e6b5242229100000004e0800000000300040020140178018002000007800400000400280040120050010000000000001805400c000003000400c00a003804004e008005000c0080080058008038004000804000800301e801400a000003000c00201e012000407e047001801800a00000200340060020008004004005000800800405c0040004010000000800400000c000801c000015000001801600b005012404400000080000060000060058004005000802402c000003804800200a00100180020050040008000000005800000000400c0048002003002007c000000000800000000800000180320030118008000004012803404a00e0010078000003006003000000101100300000350060000002006000000000600c001802c0460010038000008005004802400600900280dc012000003800c00200100b006001a02d0008000006005001000000c00000000080340060068004054016003001401600700100080060030098000038009005801c0000060008034002001002006801a000000000c004000001803000e000000000c00000f00080140100060028004014000002802402600a00a0004006015002002400200b003803c00600000f800c0000050000000058006007800800200001d803c002000003800400000100a000004800f002002000c001008802000001600280b403e000005804800c0320000020000011000002400c0080000000014001003000000000200000e8008000000008c0000040028010038012003801c002000000
  | 24 => 0x906f00a891c20c3062ea06440050fc8a380ea78968f9cc9068c1437793909caaa55bf83f5620bc60139120b586340a91d1556237f4a8b2519c052b702846d36a2396cf000000033c56d9335452cc9000228881c54000031b0f82b3700000006d0b834c09a0d3c24b46f30000374e1f6799c75278cfa32f1de547420f1bc9af0cd62734d08000000a691b200000003ac14aac3c900c8e094a7dd9743b53d93880b6aa433b7a9f13ea89e1029bed9fa60e39a8c280000293e3065c2d621f00004ec00082836712fc0005876c0000159e5ae5122e38b262c969e9ea19f0d8342c00000008bd25c0ce47e2deb58aa2d49b8793546a3c0cd00630000acdae200018728a82924300000aec000000000163c00000000029ad0cc4b571e00009bcab603e2e25038d060000cc8000cbc4ba2d20ff461546320686d8c22158b6cc90abb650387f047cd8d00011a8000e0900009f86165cc6a0b2d14367a6386384888449b4f292412b87a72f8361499ccfc2510bb484c00021faab0c72b66512b2b4000ac500021d46cec2404725e4d3e3d7000247c000c710000000e1a2360001fac64ca3f02015f83de7974683865124cab2a583547e497536b1290a8c9ba0d412f00000001cb15858261f24798809b5e8f915c9475c2022164f00006ae96144c8b291c44af3a42ca120cdf4000008c00036629924297589bf0000098558c9c0eb800000076116c1e3c570ca671819f9832b80000000000041d00034740004fd00009e54fa63f4c42e340000004d2800026a88c0d20001a36d725b69464000000000000196ee2d0002f550ec11a14a01a4ad07da52fa6acdd4000000000000000000000010a007a00016dce7e0000002214000394248909455c0004aca1c00ec13c148b5fd2c692a31637e55ee2b66069ae0bc85aa3dda7911f8d732530ee40004ec5f78000d687066bea6dcd483e943e91040009d117db1b8000c8900017a512ad813ee850187e0951dd8c60530dfb2ff10716c6db51189cf0ffc11d00023a006e1d600028e01746460df10f59448300d327c19861a540dae3cef81b901007d8c34a4a609216537693b05031351e85d71369931a0604244d8874fbe8c73e5b1e4974ba3152978c986a933190eb88c288f23aa12811ebc7175b1307929f26d19a28ae043c0090e318f68682cf0d40e9c5fb363815c5ccde47171e7517c5941cf9770000dc12682b35abe8ba00c8cb996a978007a96c598beb01c22402fc9026688000bf200047331d0fb82dd0000330f180515ae80000008ff3f8b0d41e86971eca49000083e67a049000060826fa251bfa0006a72829860e3f3d01d7d39a73b0002bf582c35f0000000000000000000000000049780002ba0000002db0f0ee544b388494aa00038e1acc000a511c80ca4d7e33b0b28e0400085c6479c81c9a9cf2f1000
  | 25 => 0x182ee8b21989c280005db0003940e423ec0a89431ad65ec6ba9a34c04ae230832c546c62859c8e784788ed0001a615e8b0900016ec000ad53ac8000588000000241db2e54a29d8c3c000abe43a2b489a2000000000092405a50d01a9ba829a5e29cb1ad290c4992874ee286147a8ca836c11f119ac080126cb3589d595fe75800006fc31ea6f28d28a077e3727288591216d0b01a392546a8326ad084000028000037bdb32bdc404170d37c545000000092a4ab6d29a08000c0e5c0824936457c32b00007780336f7174d76024b0003208000cda4e5822000069e4188d080005922cea034336000000270c000835345aa087907ed0000000bdc24f00028607544460ae2b50cb0946431a88c076927000140994000068a800134c7e800011606429333a195f40000003b9199c00080762813ac79ed770082dd958e7c500000000001370ef8368000000539a1bcd9000000034a0000d535ab94f00000000002574000a3200027e4a62482130845859e3235f180017046ab2a18d6999e6c0455800000082730480005b8e2a6e102259cec3859c18e805c7402ac94e920691428a8361802304557ac1071c2961cdad6c0b06007292378568534014108c7a29ec0000a1d02c01a2d38e7532871f58728c0cae25200009a93aad3256c051d9da8554f68fb580a45c283864598cbc244584997cea7b293a03d8b66e019d2d0cc46e3917cb1f9cae36b3f337615c890d02e05a401498b4669db035c8e140f19ed7d47c86b508c01304712cb025dc563066310c4cf727ad42700000003b75df9f48c3c5ab59b0344f2c97a13b1aa434400061d103020894960aa28d04c01100034985de00000031580004a50001e0180c0003e38800402c1d0000af542828c368ac903fcd115a12680000b2000000000005a80002130a024fa00017a0a4acbf62c065400054d6019a4962cb700001fc84ae93832a08a0d4c3c70e584e05a058d3891f9cf623a50719ce56444f0148327400000026ab1bd4dc24626e819860a8572969c78264a0c2e41fd94ea8a6686a3c8ff6960132b6dc000ac210e2cd032c91e68825b000000002f000185acd862ab55021cc4e2c814d5c642626f0ae6ce7c51c1a7a440c0ec2a49583194680f3555aaa4ee0d446b12a2990085460e27145a2c8d3f82a9047e1b107fadc857ed1a022b8e02627075759f7915a8d1457a909a5a5d969cb7f176e48f32983acca45c72e836c4df07226bcb22090e27210402f19720002cc1a14000bcc5eb15418e0055374310c0ac2c11df02a859cc9f6963370cf4a9512db17840eabb13d05689fe6cd67126e5cc606c4a22b8dc8a04a1c51c5da9eb113c089bcb3e85e4328f612587377231b0d8ea5be1f30078384b404c2a7b85741420d4a9b12245526658d206201b36ea98b9c50a8f5511811cbe3406e71b88180a0
  | 26 => 0xdb00005506fa898000000156449800002d40000003843860c925f74f00fbc5f034408583c9b7c58a5020a74102a473f10bd1a3c7ab40503405d20a800027749f200000026c49346f108380017e85645ac800129ae5559ab76c0dc72500024b8000000000198da7659b5c626100000005be11e5480c470001044000cf500024897529d700015e116626c2932f88c9ee223a11b115163206949b1846e96804c8191b429cc0003248e063e246411f03e05133ffa210ed03ea6740b6559c757225a8acbda39702ca2ec4482a071782cc650b1c2b92658756dd737d0fa0c660d90000e9c0481e8672b2680000001410001cacd6514e236160e19244e84b4b6c18940c0718d4a20b701a600c30395000309c35ea88595075156ed4824234dc8a06ae425b19d9d25e50a50d1d110c075ea23ed96410a36d1bb92e21c93aab308b5aa3764b07a84068bf3582d9042a7b420b8c1c94ea705fbb6114fc3e1722245c7387af1f195a80006890f6a76047098755d19f1a1ec590e88e11086d571bb800099e9473bf10200006d523618dc3fa7d72790478660df15a9888893cb7955a03b00008f6284189107829e0da827829cabc40a274127234953fa16c0000001eaa1dc0008d97038095ba00005fb00008d62fe4b81f0055eb510002e5551808043906298420000000784e2a0000000000000b2f2a6074cabcadd0ce00000005c147236883588f70000b8c7baa8e28209b930c7d06d5165589e96a212040550245164da88117827f0002f3535a000310000126c3190000050dce00071d21ad9c619e0002691b58e5d000000000052c00000b000000000010a000000007f148da143c00001728dda0001fba6600000006f6b69c77400064c2e949cecca165a759b4cb875f8b22c9d0dfe4ec93bca50af934d9138f4a6776d4a6559ec5b44e3b63838800051c80005dc60d00018506988496a000001ba00069a0000440c66532834c1168876ac00016f694c597005c1186a80041de8baa2707272549b788cf7212e88cbe92527a0c48000000107159400000027da29d76484d1c33404c84dc34472208000447399a9d074c0005cb0bd40000001fc20918344c93a20a498ba6af2a7a608fa62d409b344d8eeb90000159c00000026585580005631f72fc916094018e173c00000000000004aa78e00005d918800000000000000003df8915a940001a1885c000468593154561a413294a1e01b84816920d895905b92fe0000f7a0005dd9018b622416771428ee8d9f45235588e818b2e48a2c000bc900021741a89bc0f89695a966260a6a6a0f9abcf01f00000008a14a5179895a61600011d800061f6900001642aa8360a374bd47493fa86ad786709617000024a0000003120000a3b0001ca0e04d0200000014c40003b38d4d240000026adc54dace136e800101200000031
  | 27 => 0x16d656c0002d305f498c4f48d600000003f20755ae00001de9ddc00000000007495ec31a21f1668eb8e2500000006c616c28a00007eac451ef8d700921e948d1a10ef02fd04502993de48a15931513f41f4631a6b80001ad00031a532699a0002b44c7000060b8f10f4444308a00018be1d813329600008fa6f61ce9138d430000e201cc3935748cf51260845428000ade0003f01a9c7c80006d4014008e00036e06d0a44000030324cb667f900035b46ec50b2e926a986e000313ac4c17ccaa59f35bd31a660000267c990000244aa980000002562f204a8c8a00033bd4c61787072a808242435c53000ea89ea0000ffd76a42e1eb345c00045f4d830e542c0005d3b758d986b25862d1516cb463c588d4c3876b7131b41bc47e926b9d98906b0a46b21487469de6d01c0585e02f45508bc2104e257289717da9b367ba834552a7806b310944291c0db955400067f01eac8d42ac206a8a89d38069c0bfa460c5e58327882711860cb54486144b4e5a5a08dc050cbe965291346b66350ab852111a1462c209f0f5c3c53209cbd60a1873cab351988c97337aa7d02ec9936a0001a7442c15831a93fe10c288ac49a1266916d886d8820222348ded75ea3d1b7194152ce2300237c09d401c3a6a1c4e3494300709202248891edb1cd4e404c24b83c00da5742c297144142094aa1d4814ea0e1ef0d543ca5d8222ad250f8000000208cc62ca800033ac7a8dca0329c9cb74e344efa5b89265f52e11a54e523b34be22055a6c2917e01880000000000000d7a9fd35b396c00e0006669ee000000c00b0c080f082900033410442995d990d028666c5760514e329a7297870164a65b0002ee12904e10e2839ca06d350001ba467e1e341c870575600017000000001a000003ec1e29a305b89ac0004c53629af8eec95000006ec06a7883461bc1ad8268321800803a170106a3e0864bca6dd800070abb964800008a68a96c32e142ea1ec23214011cecfb31e1284a2ec4a33804d16ee0005fe0000ba20000002b9ca1ed935ef94c190ab7a1200c7cb5281310998ac0fa4ed6128f0c56a0836999739af85f320f28707d67042398d1849438b07d12c80000006078c0449ac26000334c0001156a92aa80000000f3a3817e6cf907c92f46220002e200000007a15fd965c00013953000019ae9c90000000000aa100033a8090000507b960d1ee3b44ba4dda7c89a04f88443420c364607389a4b476c81f8d6ced8f1ed28996587733fc012c02adb244337652a65181389664d325af06f894039478446a98f92c42881d80b49716d760eda1ed7fe68600000000000000000000000e6029b83a01c4c1858cb0cc7a678a2b0057950ed9c0ba04349180001511d280008150578bfdb340000001ae8000000000000167ad460000769820d493bf9ae592a10250191b818a0
  | 28 => 0x3f90000000a5c0bf0001ff40007641b9b7cd7829775a20850adc0305faa78c4547bc50300018ec769000010c6962e25d8a7480000000c325f400075a00000000000004bdb36c00000036c800000007e6bf01c0000b313d20bd8c266f32329dedb6cbfe02e80015e447b721afb929c0b472c80000009b4149af2db100966861311b288ef448b49d7489c86e6b8f881e9356cda3a81ee12f11724f8f348d400037189ac43925b0f4080027d2891fb8e7ae245840fe82662c34fda1cc6f07fc1798000ae6a4616b30f17aecae1e70fc03328c941d00000000ae00023f4000000000154d0da00071e800000000049080000007910000001bd0a916b7000087436f6ee29200000006602c7c0002d767884896ea9760108001b7265c46d8000452d3c1fe0000636000000312c000000350000044abbd13c00013b600028f1d4091060b146800198e4d469f861105895e51116994921ee5e82558c80be62de0e89c424a9340b4210b40f55c3000131c35224e8f700001232249b6cc9086e68b0a11384d8b1be1f44fee63d4e2180cb7eb9a0e1a8b8ec4c6d53331493b85a21f2b030000000282b4d94bc0000000001674e17310800116800043d34a87f6ac000036b8000a94705a405524118000097871a3ad70989a40008e500000012da0000000000cea382000234907e000000264156a0000001c003180003d5238db880ef00010680006250003390dd8751000163157ab9e3e4834912c79805ca9e97246f9284aa7561669335bab25868e2959580001206610c7000067cde325720302b22a428338088c48ee5bc1ab0a8e3f4000331491a40258c05b52be62200022b845a58241b0c58242af35cc879926218323805f1bea3997000000000ae16b3aa0ce2664a3a62ae5170bd13cd800120849c2d01e351e270b2e013cdab60ca6fb24c150851f56b0000cb2c2b07c2b1854e46f577024c2c03384298001032e0f00034600007ea016a598000dcb456244d97c5420ca11008ce30c54ca9d8260b4b056000000000000020ec6fcacc00014349ea6f700013802400000000c5c000bb42ef956d08a6296dea97050a8690002cf146683865200004a60410001690000af5141922d2aab2d00000002b64045620000d2c04f0701cb87340002ad36fc7e6a2d11a263cfb6d234528000e301930000b1c1c800000032bcdfc0000002400000bf80002d7c00099e00028f905400038a00010400003d4800029e8ce00000003460002ae0000fb209a0000000d94094000358001a7ca0b180000003cb4608af04eebd910caeb522ac3b67818496a0dcc5ba31e0fe642d6a392c5b701f508ca42596696537f9bc8dc83a111193dda84af06b413054a674f0a80000476d38151af74c2e4540000000cec4565831dd40005ef651a20129616115f2474d3a67218f0000fb05771ae8
  | 29 => 0x37c9a60dc9066b7fd8926f45322e4c2d4cce487833d3220005e9a0b84e800016f211c0008cc00015e8a2091954b8b21246a01719a79c6da036000000175ccbb2b89a6902000025032112b00464f58f302e28da0000a2506661911e92ddc6c00000032a54aeae826c957c00079054d1034000409412b1fdb3a4190431b60e5696b0f2191d4a031446009395e23a9082ab980000004b9276986c4356358001b60d8a3f790dc0000002fc054d9aa9991260ba91d656d70e9f9443c00016117d80009d4526043dae8ac337094cdb7400055f80005c257f17892cdc3cca1488ad540ee4fe0000000ce23896660000a6c5b86ed1550fa87d55cc1f38e2200038d90283006c94ceb58c0005b00e3a90439e70e0748324488b5a65c1e0901617d6af146c0005211803584cc80001a8800170873012399d1bbea2f3512ccc25603c39b11984b28ec080200d9a4bc00c4118121044a52ca32d3e81555b42f792d2a674d137e086c19d01d19687cee0c17631916c04ee075391c00007b0590d0542e2e410330a183cd7b49680009b60002731e70f84ab849400003d64a36c38000bc000035a80005d05915ed06e129e3a0037b0c8bb403915521a8000e4c0003009536000000314505ec865351c3c2f600027e106d6b083d0001d6c9543b120a06a995893408b8d94000000203a009c900001af0001c142cd0002c699d8a3100032c011a22671ba4fd90e53d000000182200022bacec000ddd2698f49a56000640b8542b00005fd000000003f2b137156e600000026b1a8a9973e7897c2ccba60fdb55417000000000000004770002d94f249570001d743204b92c086698e40a14e32a01abaa5406ba8080d0d4c6d58151a1c7655270aad67ea790b11a38c9c67d4bf02c4dea45a718a64810ed984088310d1084029c80000003a463ea3a482c000322962420ce5e178307d9ace4a0ef1995172a1365b11fd0fcc3d648800042c000350adb8f3c30821db7e9a0a1e04321b7d8d0bec3399845a44b322fa21fc97688307e16205be7383d82ff53c4e35000380573a1f356c8de8e5aaa3369a5bc00080043c9d8c1903340e82b7030406716295ad30653e210b4008bc000629a3f90029ce46e28143f40003f60c340009f626c0c9c2585493b511c8dd6000371800194e3605cb800000002b00001840005c602d8000000bc40ee183c69c7850002f6d69e8b700004fcb3864d07709d57289fc71390cd4786c20018b94928a68593b94c0000006acb2f484ed4d42b0cbd55a6051699f589ec3800d90dd0ca2c443481b3c53e000214b0100005cb6c10000eda000000013800079400000000003f63e600003600000cc2118000acb3400ebc0003e0580902c0000530001264722c4018a8ec9a28541430219c4306de03a207c4640003be83042060ce3db2fc0e2012e61f2c004ba
  | 30 => 0x5a6806cc3ab6202f9618f3e80444f9575ba60005292f84bf4e6257d84f9a081f70000148cd400000fb1840004050eea72800063627494e05e4a450000001b80a120000000724783227b41d05a00062e118c0644865f2000000054e00000012360000002a70a90de50000001c36d1c000320d5d4324051a2a149a4c700033fc0008d36971ecdb4867822c804c238ba10000d29400c1b19b28200001bd12b000108400004e9aec00017a0003904b1698a00008e91be4cc0001490f0c32d56f0f350be47e29030251400004d78001b5aa5d018968451e0796e78960e620b65fc8000c967c35ab0da48da4f824b00013fc4ca0000018ccc3351da18285149050883398dae5bd0a633213a6d5c708ad513cc15f72e0ed878c576508b020b64cdf1959d80390cc163292a05eea1e68c97f4000000391b811ba2d7a4d4915425047a5980dc4c0c2970000000e4cb1b316995400045d48b02c064a000130175868a9297200b9d49ec2c3dba5048f00000000000706000000000000000063d00005800002610924212d960bc8000000d502bd98c00004105ae27e0000b9156810a8000000343aa404f6c0b00033c936cdc800024f40005dd4360001b8eb7d5a52be866ebd237e0000606a2c557000056e0f6570337469a5de15084a83f01cc038a3283fe2642ac17c4b000a270d049c6a8705201a9dcdfabbe727b1682267f4559b870b1c53f3e21d19082b172ba9c91738bce594b654136cfe2f385057548c504888106c27536f001cce96a4b37b0604000c570de
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x87c87541658c40f0f90abb6a9188121fe1d65952310051fc22cb2a4620787d85dd9548c4011df04bb2a91880a3b20976552310047dc02ecaa462018f8805d9548c48f0ff0eb28a9188021fe157058a310443e42ae0b1462008bf845c1628c40f17908b82c5188121f21d6554a310062eb2ee6a9462048bc87591428c4014bb07296ca988028f61052d95310063cb84a1b2a6200a7581143654c4051dd0fb92ca988031bdd4725953100667b98e4b2a6200ce472dc5654c4010ff0ab82ca988022fe11705953103c5e422e0b2a62008ef825c1654c4051d904b82ca988021fe1d651953100536412ca32a6200a9d83103644c40156b02206c8988021fe1570591310443e42ae0b2262008bf845c1644c4011df04b82c89880a3b20970591310045fc3ac8322620787c855db544c4011df04bb6a89880a3b20976d513100c7d404ecaa262008f9809d9544c4011bf06bb2a8988023be09765513101476412ecaa262008fb805d9544c4031f100bb2a89881e1fa1f65551310063c386caaa262048dc865cc544c4018d8c43aac49880ab3a1b624c931024eb43ee29926200c5f65dcd514c4030f90ea82cb1081e1f21576d52210243fc3acb2a44200a3f84596548840f0fb0bbb2a91080237e0d765522101c6e41aecaa442008fb805d954884031f100bb2a91091e1fe1d65152210043fc2ae0b1c420887c855c1638840117f08b82c71081e2f2117058e210243e43acaa9c42078ef865cb43884091790eb228710803175ce53d952100536c14a7b2a4200a3d8414f65484014eb02286ca9080e37a1f73595210062fba8e6b2a4200ccc73dc965484fb8eeebb8aca90803351cf71595210043fc2ae0b2a42008bf845c1654840f17908b82ca9080237e0d705952101c6e41ae0b2a420087f8759465484014b906b28ca90802ab60840d91210055ac0881b22420087f855c164484110f90ab82c8908022fe1170591210046fc1ae0b2242038dc835c1644840117f0eb20c89081e1f21576d51210046fc1aedaa242038dc835db54484031f5013b2a8908023e60276551210046fc1aecaa242038dc835d954484011df04bb2a8908023ee01765512100c7c402ecaa2420787e87d9554484018f0e1b2aa8908123b21972151210062e318eab1a420887e87dd563484018b8ebb9ac6908031b1d77258d210063a3aee2b1a420087f855c163484110f90ab82c6908022fe117058d2103c5e422e0b1a42008df835c163484011df04b82c6908029761763d4d210043fc2aeca9a42008df835d953484011df04bb2a6908023de057654d210043fc2aeca1a420887c855d943484011ef02bb286908023ee017650d2100c7c402eca1a42078de87d8d434840759d0db1a64908063ba1b724c521024e643a6498a4204acc864c93148405998ec9926290812f1205324c521
  | 1 => 0xd02382cb208029d60470596410253b40c80b2c8200a758190165904094ed03182cb208029d60630596410053741060b2c8200a6d820c165904094ed02182cb208029d60430596410253b40c40b2c8200a758188165904014bd06102cb208029760c20596410253b40840b2c8200a758108165904094ef00882cb208139ce0110596410073938220b2c8200e71704416590501ce680882cb20a039c10110596410073918220b2c8200e71304416590401ce440882cb208039c48110596410463b32ae3aa4824ed36545c754904018f0e0b2aa9208031d59771552410047cc36e0aa48279c7a65dc154904018f2cbb82a9208121f21d6554e410243e42eeca94820487c875955290401c986532a6520803930c9654ca410246e43ac69948202acc8258d32904091d90eb12652080eb320d624ca4127d5d424eab048200ab9849d560904095e5023aac120856bc60475582413fd79c0ae8b04824fe3a54d5160904095e503aa2c120802bc60754582413cc7dc3aa8b04827e8f887551609040157708b9ac12093eae211735824100575410e6b048200ae9821cd6090401cb6a729ac12093eaea1053582410055cc20a6b048200abb845c9609049f57108b92c120802b6a0c72582410056cc18e4b04824faba84149609040157308292c1208023ea1c32582410047cc3864b048200ec9320c9609040917b09b86caa08121f61774595412761f2a6e8b2a8200ccf73dc96550401998e7b92caa080333dcc725954100666398e4b2a820787d85dc565504019b6e7b82caa0803361cf705954100675b96e0b2a8200ce872dc165504011bf06b82caa080e3720d705954100477c12e0b2a82028ec825c165504019b6e6382caa0803361cc705954100675b90e0b2a8200ce8721c165504038f0e1a82caa08061f21d50595412751e422a0b2a8201c787054165504039e0e1882caa08063d21d105954100738a8220b2a820087f87594655049d0fb0fb2ea8a081e8f21365d514101c3f42ceda9a8203a5c8359753504014bb0bb1ea6a080e1f21d6554d4101d4e41acba1a82038bc8759543504050fd0b3b6a4a080a9b20965d49410143e43acaa928202a6c82595525040555904b2e84a080a2f21d65509410443f428ec992820087d851d932504091790cba264a091a1f61f65d454101c6e41aeca8a82028ec825d951504011f700bb2a2a08063e20176545410061fb2ee8a8a820187c8754165104010ff0ab82c6208221f2157058c4103c5e422e0b1882018dc874c163104090f90eb2aa6208021fe1570588410443e42ae0b1082078bc845c162104031d90e902c4208121f21d65548410043fc2aec990820887c855d932104091e902bb264208123721d634c84101566412c69908204cd47158d32104091d90eb12642080eb320d624c8410267238ac49908201
  | 2 => 0x32997410053cc006532e8200a6e820c265d04014db04184cba080297a0c20997410052ec184132e8207a3e8494d65d04018bee729acba081e8fa10535974103d1f424a4b2e8207a3e8414965d040917908b82cba081e1fa1e505974100c3e43aa0b2e8207a3c8454165d04038f0e0a82cba08029d604505974103d1f424e6b2e8200a3d849cd65d04018bee739acba08029ba0a735974100536c14e6b2e8200a7a809cd65d04014f30139acba081e8fa1073597410051ec20e6b2e8207a3e849c965d040147b09392cba080297a0e72597410052ec1ce4b2e8200a7a809c965d04014f301392cba081e8fa1072597410051ec20e4b2e8207a3e84cc965d040147b09992cba081e8fa1232597410051ec2464b2e8207a3e840c965d040147b08192cba08029ea0032597410053cc0064b2e8200a5f835c565d04014b906b8acba08029be09715974100536412e2b2e8200a7b805c565d04014f100b8acba081e8fa1331597410051ec2662b2e8207a3e84c8565d040147b0990acba08028fe11705974103d1e422e0b2e8246a76811c165d04014eb02382cba08031e5c0705974103d1f42660b2e8200a3d84cc165d040f47d08182cba08028f61030597410053741060b2e8200a6d820c165d040f47d09902cba08028f613205974103d1f42040b2e8200a3d8408165d04014bd06102cba08029760c20597410051fc2220b2e8207a3c8444165d04031b90e982c7a080e1f21d6554f4103e1fb9acaa1e8207e1f7359543d0401c3e60b2a87a0803874c16550f410061eb2ee4a1e82018ec8748162d040f0f90bbb2a5a080a1f21d6554b4103e1fb92caa168207e2f7259542d0401c5e40b2a85a08038b4816550b410061eb2ee6a1682048be84dd932d040199865bb265a0803330c9764cb4100726194ca9968247c747199532d040f87ce8b2a65a0803930c9654cb410061eb2ae899682049b4815d132d04018eccbb8a65a08230f99574d47410061eb2ee8a8e8200a7a800ca65904014f300194cb208028fe1130996412851e4226132c8200a6e820c265904014db04184cb208028fe1120996412851e4224132c8200a5e8308265904014bb06104cb2080317dce53596410051ec20a6b2c8200a3d8414965904090fd0f282cb208129da06505964100c3e43aa0b2c8204a768114165904039e4e0882cb208039c941105964100738a8220b2c8200a5f835d165904014b906ba2cb208029be09745964100536412e8b2c8200a7b805d165904014f100ba2cb2080317dce73596412751f420e6b2c8200a3d841cd659049d47d08392cb208028f61072596410253b40864b2c8200a75810c965904014f500192cb208029e60032596410052f41ce0b2c8200a5d839c165904014dd05382cb208029b60a70596410253b40ce0b2c8200a75819c165904094e
  | 3 => 0x8a96a20487c855db42d44090f90abb285a88023ee017650b5100c7c402eca16a2028bc8759142d44090fd0bbb265a88125d205754cb510051ec2880b24a200a9d83101649440155b04202c928812ada0440592510075820220b24a200cb87059154944f3ae6a3b82a9289e31eddb7055251006b9b8ee0aa4a2048bc87591439440f47f0caa287288122f21d6450a5103d1fc32a8a14a2048dc8758d32944018beeab1a652880ab3209634ca510247643ac4994a203acc83589329449d0fb0fa86c8a893a8fa1350d91510263abaa21b22a201cf2704436454401ce2a0886c8a88022fe1d64191512751ec3ec92a2a200c3d87d925454401c6e21b24a8a88038d44364951510463bb0cec2a2a247c77109d854544018ea213b0a8a88029761632d8d5100c6fc3a61b1aa24e87d87d93535449d87ce9b26a6a8802dc6007154d510243ec2ceda1aa2038be849db435449d87ca93b686a88029b61732d895100c77c3a41b12a208c77619db525449d0fb0fb26a4a893b0f9d364d4951005b8c00e2a92a20487d859db425440517d093b684a893b0f95276d095100666194ec992a2078be841d9325440117b083b264a8803330c8764c9510243e432ea992a204974815d5325441187ee9bb2a8288031e1c376550510063dc06ecaa0a200c7880dd954144018f6edb82a8288221f2157058c510045fc22e0b18a2078bc845c163144a10ff0cbae86289428fe1954d0c510245e43ac8a18a200a3f865514314401c3aa8b1a86288221f21570588510045fc22e0b10a2078bc845c162144a10ff0cbae84289428fe1954d08510245e43ac8a10a200a3f865514214401c5aa8b1284288123d205764c8510043ec36ea990a2048dc8758d321440559904b1a6428813351c5634c8510247643ac4990a203acc8358932144114f50b3a2c028a0e9e61674580510453d428e8b00a21ba79851d160144015b5063a2c028802b660c745805100575410e8b00a200ae9821d160144095e5023a2c02886ebc60474580510063dc3aa8b00a253c788755160144114f708aa2c0288238ee1154580510071dba2a8b00a200e3874551601448d4f702aa2c02891a9e60554580514153dc2ae6b00a208a78855cd601440157708b9ac028802ae211735805100575410e6b00a200ae9821cd60144114f50ba1ac0288029e61743580510071caa686b00a200e395450d60144114f50a21ac0288029e614435805140d3dc2ae4b00a208a78855c9601440157708b92c028802ae21172580510056d418e4b00a200ad9831c960144114f50ba12c0288029e61742580510071caa684b00a200e395450960144114f50a212c0288029e61442580510053dc2a64b00a208a78854c960144015e702992c028812bc20532580510047d43864b00a2008f9870c96014401d9264192c0288029ea0
  | 4 => 0x3d08070f90eb2aa7a101e3721d6354f420070eaa2c6a9e84018f48744161d08018bae729ecaa10028f61053d95420053ac08a1b2a847bc3f75dd165508031f50fb82caa10021fe1570595420045fc22e0b2a84008fa871c165508018f6ea382caa10032edd070595420043fc3aca32a8400a788059465508018f0e1b2aa8a11e72e1db70551420145ec26e1b1a84028bc865d3535080f1d90cb96a6a10034b55172d4d420055ac2063b0a8400ae5820c761508011ef0eb08c2a10061fe1d50d9532006e2196e2b2a6400dc4321c5654c9098beebb9aca990031ddd471595320066bb98e2b2a6400ce7721c5654c80117f08b82ca9901e2f21170595320047bc0ae0b2a64048f4815c1654c8010ff0eb28ca990029d2056519532006c6194e832a6408c3e655d0654c80187acaba0ca99003630c974195320043fc2ae3b22640887c855c7644c801d9260906c899003530cb7559132006a6190eab226400dc432dc5644c801b886438ac899003720cb70591320063bbaee2b226400c7475dc5644c8018eeea38ac8990031d1d4715913200c7d43ee0b226400c7b75dc1644c8018f0ebb82c8990033cdc770591320067838ee0b22640087f855c1644c8110f90ab82c8990023de0570591320247a40ae0b2264008fa871c1644c8018f6ea382c8990031e1d4705913200679b88e0b226400cf0711c1644c8031b90e982c8990063b21d20591320076498240b226400d4c329d4644c80f87cc8ba8c899003530c975191320045fc3ac83226400c3d75590644c80f0fd0b3b6a89911e9d20565d513203c5f424ed2a26400a3d84d96544c8114790ab24a8991efc30cb549513200c7d404ecaa264008f9809d9544c8010ff0abb2a8990023de0576551320247a40aecaa264008fb805d9544c8031f100bb2a89901e1f21d65551322353a40acaaa264088bc87591544c8051bd0db9aa89900a73a0b735513201c77436e4aa264039ce83dc9544c801b9065b82a899003330ca76151320443e42aec2a26400ccc325d8544c8011ef02bb0a8990123d20576151320043ec3eca2a2640087f855d3614c8110f90aba6c2990023ee0174d853200c7c402e9b0a64018f787443614c801a9865baac299003530c87558532006a6194ea30a6400d4c325d4614c801b18653a0c299003630c974185320047bc3ac230a6400a7485584614c801b9064b80c2990063ea1f70593513ce3c3aee0b26a279cb984dc164d44090f90ab82c9a89fb1e1d470593512843e43aa0b26a250a3c8454164d44038f0e0a82c9a88222fa1e40593510451f42880b26a200a9d8310164d440155b04202c9a8802ad60440593510065db8080b26a27ee3b5010164d44a10f90eb22a7a88121f21576d0f510243e42aeca1ea2008fb805d943d44031f100bb287a880e2f21d6450f512843e43ac
  | 5 => 0xa002b660e62d81540047dc3ac5b02a8008f98798760550011f70eb0ec0aa002b6e0d61d81540056c41ac3b02a800aeb8258760550015d104b0ec0aa002baa0a73d815400574c14e7b02a879a7a851cf60550f14f30a39ec0aa1e2aea1073d81543cd5cc20e7b02a879e5b5394f60550015b507396c0aa002b660e72d81543cd3d428e5b02a878a79851cb60550f157508396c0aa1e6ae61072d81540047d43865b02a8008f9870cb60550f34f50bb8ec0aa1e29e61771d81543c55d426e3b02a879ab984dc760550774f50b38ec0aa0029e61671d81540047d43863b02a8008f9870c760550f34f50a18ec0aa0029e61431d81543c55d42063b02a800ab9840c760550015d50418ec0aa002ba60831d81540047d43843b02a8008f98708760550f34f50a10ec0aa0029e61421d81543c55d42043b02a800ab98408760550015b50610ec0aa002b660c21d81540443e42ae0b18a8078bc845c163150031b90e982c62a01ea72113058c540443e42ae0b10a8078bc845c162150031d90e902c42a01eab211205885400c7a43a20b08a808c3f74dd954d4c018f0e1bb2a9a991a1f61b715535301c3e42ae0b16a6008bf845c162d4c0f17908b82c5a98063d21d10587530051ec2881b22a600a9d831036454c0117f0eb20c8a9802ae201641915323c3e432e3aa2a600cb870d915454cf18f0edb82a8a980e1f61770d895300672310e2b12a6008fb805d36154c031f100ba6c2a98029d61421d85530056ac1843b0aa6008f7875846154c015c904b08c2a98061f21d505974303e1fbaeecaa68600cb870dd954d0c010ff0ab82c5a18221f2157058b4301c5e422e0b1686018ec8748162d0c031e90e882c3a18031b5ca52d95430051ec20a5b2a8600a5d839436550c018f2e1286caa18029d60450d95433e61fbaee8b2a86018fa87dc16550c010ff0ab82caa18022fe1170595430047d438e0b2a8600c7b751c16550c01976e8382caa18021fe1d65195430053c402ca32a8600c7870d955450c018becbb9aa8a19e72e1db705514301c5ec26e1b128600ab5840876150c015ab0610ec2a18023de1d61185430461fba6ecaa6a400c7870dd954d488d0fb0db8aa9a911b1d98771553520143e42ae0b1ea4008bf845c163d480f17908b82c7a900e2f21d6450f520070eaa2c6a1ea4018f48744161d480147b0a206c8a9002ab60840d91520045fc3ac8322a400ab880590645488f0f90cb8ea8a90032e1c364551523c63c3b6e0aa2a40287d85dc363548019a8c638ac6a900a1f21975d0d5200696aa2e5a1aa4008fb805d361548031f100ba6c2a90029d61431d855200572c1063b0aa4008f78758461548015a906b08c2a90061f21d505974203e1fbaeecaa68400cb870dd954d08010ff0ab82c7a10221f2157058f420145e422e0b1e84018dc874c16
  | 6 => 0x930b4af600000094800000aec6db4e0808280008d16a4903180000000064800000000000000001495f94b000c2c002ad000640003590000000ca27000000a412e00000178b56000001890fa00076c0001d538000000000009ec19a8b000218000000004fc002aa1963298c8880003e0cf000000000068c11b200000247512001049b943ec080000058600000000000b759200034000095800000000730006129cc000005fc0000022e5f4000001540000010eb2955600000000000000a00002be000f90002ee6f4000003f8001ad9236582304a0001d80000000000002000000000509218000000000000000000093000000000a20006980017080066c1ac00000168000000000008ec002744c09d4000000000000000000023c00000000000c125a2780000000000000081800000a658e00003600000056000000000000001200032f0000400031124a000000005fa998632292a000000000000000bf8000000006a0000000000000000000000000000000000000005ac00000000994000000000012a800000990ac13a000000668004fe8185480049e000000006640000007300045c980380001289f0be518000568028010000000000200a00001000000004008000060040000000000401000004008000020020000000300a00402804002000008020080140100000000800801002004000020020080080000a004008020080000300000000000801000000030000000040000000200400003008004000000000000100000000400800004010038010000000100000201000800002000000000000000000001200c00003000000000000000100080200c0000000000200c0100200800800800000000008020020040000000000000000004000000010000000100000400400803000014030000000100200800201c008000020000000000600000806002004000000000000000000001403000000000000000100180200000600000001000000000000000100100100403003000004000018020000000000100000000000008000000000000000000100000401001000000008000000040000000000c0000000200000001004008000020000040080000200000801002014000000000180000000000000000000030000020000000000303c3e42ae0b0ea84787c8754161d50031e90e882c3aa0039c541105875400c6e43a60b1ca800a5f854c163950031d90e902c52a0029be152058a5403c5e422e0b0ca8018f487441619510b8f2ea306c2aa11a1f61f50d85542851e422a1b0aa801c787054361550031f50db82c2aa0ee3e21b70585540066db98c0b0aa800cd87318161550019d6e4302c2aa0033a1c860585540047bc3ac230aa8008f98798f60550015d50531ec0aa002ba60a63d81540047dc3ac7b02a8008f98798b60550015b507316c0a
  | 7 => 0x7800005129a000000000000000012d09800000000000768000002720000000000042159800000000000f96840005000058200000000000000000000005d0000000885e4000005be0000000000000000000000c8c97800000000e6800000000000000000011a06704e7fc000005b22bcb18000009a8000a51e82380000000000014a95000000002ce5400152bb48000000bc000000d680018e000000000a64da558520690ee7cc0008100000000000000000000005fe8140004d0007d8f7000000ba1722b54b6000590000002dd9d24b0000013900053c00000000120b340012100000000000000000000450000015280000029c001b00000002585a000000000000000012200000000000000000000000000000000007447418486a413cccc00305d0006a8000001ce000e98001d40003f987062c6823aba00000000000000000eb2f70006298d80000000000000000960770000000000000000000000000000900000005d200000000000000000000000000000000000000000332000210000000012500000041c000000000000000038a8b0000000000011c138000000d980000ec04a49ed4be0000017c692c54003173f4b45319140003f55c21c000000312dc0002b91f000000000000000009414a1cc000000000006a47c400000000000640000000000015d000a9d75800000000000d0000000000000000000030c3280000000009c000002d00f8ccc000000000011b0000000000026b440830118000000000000041ace0f5000000529630000003b40000001c0000004f0000015880000000060000000000000000fa0008e0a217a1a8000002ce00000281000000000395001e50900000000000210298000002d40b282c0030d1e00000018b3f0abc000000002f0002f4000000001ce60c001ac0003d085400000000000ae000000001a88000008c4001e900000169000388000da80047ac2838a45000000000000000006f800348000e1089466a84000000007f81500000000000000000000001321600f8489846680699b9b4000170000fc000000000001504c59700000000000000000000002c900044ccb800000000000004ce74800242000000003163426b072800000604002fb00002c00000000000000000002ad00800000208d423c00000000098000388b8191222000000000185a14c1963fa2780010e2020000000005a00000161000000000004902ec0002e000a1400000000000850215d8000000001ee694a70355f8a4001800000000f6000000ac97907e6562d92b0000000000a800000a4400000048a3c002da0007ac00000588000000000007750787a0007e4208002d8001aa1e10000000018f000d1400022000000001bb00005c0029b4c470000000000000ef8006260000031e44a0604980065a000000000000000000000
  | 8 => 0x114000610b917e0007b1bc0007900000024400000000000000000000000011ba26000000e320443200077a96000000001364309c0eb8000000000033b38200074000050c1000000000000000580000000011a4c20dc38253000000000002f60000008731a00000000000c94d71d50009785c00050c000a918c0ae6600019340600000000000000000004a46e000000000d54000000005c94533f4ee00493800524000ad80063a16c0000000000000000000000550ac5960d118000138b313d2ea0005b8b200009200000000000000af357000248000000002680200029ec40faa88000a1c000000004d4000000000001f8002e2001a000019c03cec1434560004d8d2000c60f28e300000000000076000002393c4000db8004b83740000028a84c00000000001a5353000b9400000000000000000000000000000000000110000000000462402cd7c8000a0c1c0000000000117a070005b4002240000013e2a83f600000000000000000001aa0000000031000000000000000000000006f800115000a69248000000015c8005ac264721e31061bd28951060000000000008a8000000009b1768003a8000000000000000000043400171800000000000e0000000000003b83109427e20a0000027d000b6cb300013a00000146000000b280068833c618002ec0004b80000065445800000000001020000000000021e86c0019f000000002e04440008f07600000000000000001470000006d8002f023a69d0f0004645bc000000000000002f28e000000000000000000058a00062800038001378004f0000000000000006f1a64ec000002690aab4d6c01e00070c708000000000000004000160000000000002f80001c800000678000088005446684a80023e00000000000000890000005f80005f282000a9800000688000000789380015a000000002b4014000000000005e83d800000af8000f357a000000000004cc33000000180e800000000000000000001140000006acd8b460006495e2845464b1370006108fd933310240015b00000028c0000068e0014b800390368000000005644f80000071cce800000000000000d079d828f245a0009e9192e6b20000000ca2c40000002c85c000001b061800327000b78001850001e00000000000177800000000788005523d40000000000042322696581940dc058458d1b00000000000001d6000000000000003700000084400000640000848000000000000066a0ac00000000ac0000005c4000002c2100000000000000000025d53e00000000000000002084b2000000006727d0001800000000000042c000748751fe6bc001d1000b9c00000000000d48000001900000046a0007d86c42828400000000cf400000000c5000000000000002230000019f0000000000024d000000001180004ec0030f
  | 9 => 0xf780058ea980020e000000d932100004c00000306ab000000000000000002c40000000051a72d3c95537e001a68000bc0f50135033855cfb83a000099520000001b40000061c418000000000000004300009400000000344ef0005268000000000000000000000000ec8d700000000000000000001345062588d9ca50442c6b1ad00000173000254b541b34148c00000000000000000000000000000000000000054000bd47f0850009c4dd00000000000000606bcc002b7064000000020a6000e7800000000638005ae6240017500000000000000401a78140009500000000000110b430000016797d0000006619b21834c00000000000002ca000ca85d009208a75771370000000001f2d40018f9c955c001341f0000000000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x3000000d48a8800583001f0848bab5254116024541332944a7380038e100051a4c3d02d0a50f180c8cea20001080166c00500000a78e0116030020040057064032dc5654c8015c1900c8715953200562640329d0654c80143491595741953200562640325d0654c801549900cb755913200552640321d5644c8015c1900cb715913200570640321c5644c8011ca980cb705913200552640329d4644c801549900c9751913200472a6032dc1544c8014c9900ca761513200532640325d8544c801549900cb755853200552640321d5614c801549900ca751853200551644325d4614c801549900c9751853200562640329d0614c801585910c9741853200562640325d0614c8011c9980c970185320058c654404416494401691931011059251005a86484044164944014c9900ca764c95100531644321d932544014c9900c8764c9510058664c745516014401629921d154580510063261d320c96014401871815c070597410053264032dd932d04014c9900c9764cb41005926403299532d0401649900c9654cb410059464e704416590401661929c1105964100592640329953290401645910c9654ca41005926403259532904018c9874c8325824100e1c21d504416550501630945411059541
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x1
  | 2 => 0x3
  | 3 => 0x4
  | 4 => 0x2
  | 5 => 0xb09
  | 6 => 0xb0c
  | 7 => 0x5
  | 8 => 0x6
  | 9 => 0x1409
  | 10 => 0x140c
  | 11 => 0xb49
  | 12 => 0xb4b
  | 13 => 0x1449
  | 14 => 0x144b
  | 15 => 0x289
  | 16 => 0x28b
  | 17 => 0x28c
  | 18 => 0xb89
  | 19 => 0xb8b
  | 20 => 0xb8c
  | 21 => 0x1489
  | 22 => 0x148b
  | 23 => 0x148c
  | 24 => 0x1849
  | 25 => 0x184b
  | 26 => 0x184c
  | 27 => 0x2c9
  | 28 => 0x2cb
  | 29 => 0x2cc
  | 30 => 0xbc9
  | 31 => 0xbcb
  | 32 => 0xbcc
  | 33 => 0x14c9
  | 34 => 0x14cb
  | 35 => 0x14cc
  | 36 => 0x19c9
  | 37 => 0x19cb
  | 38 => 0x19cc
  | 39 => 0xcc9
  | 40 => 0xd09
  | 41 => 0xd0c
  | 42 => 0x1889
  | 43 => 0x188c
  | 44 => 0xd49
  | 45 => 0xd4c
  | 46 => 0x1a09
  | 47 => 0x1a0c
  | 48 => 0xe89
  | 49 => 0xe8b
  | 50 => 0x18c9
  | 51 => 0x18cb
  | 52 => 0xec9
  | 53 => 0xecb
  | 54 => 0x1a49
  | 55 => 0x1a4b
  | 56 => 0x749
  | 57 => 0x74b
  | 58 => 0x74c
  | 59 => 0x1049
  | 60 => 0x104b
  | 61 => 0x104c
  | 62 => 0x1949
  | 63 => 0x194b
  | 64 => 0x194c
  | 65 => 0x1a89
  | 66 => 0x1a8b
  | 67 => 0x1a8c
  | 68 => 0xccb11
  | 69 => 0x16cb
  | 70 => 0x104a
  | 71 => 0x1a8a
  | 72 => 0xccb51
  | 73 => 0x154c
  | 74 => 0xd0b91
  | 75 => 0x188b91
  | 76 => 0xe8b91
  | 77 => 0x18cb91
  | 78 => 0xbcd
  | 79 => 0x94d
  | 80 => 0x19cd
  | 81 => 0xd1851
  | 82 => 0xe9851
  | 83 => 0x1042d1
  | 84 => 0xd4bd1
  | 85 => 0xbcd51
  | 86 => 0x1a0bd1
  | 87 => 0xbda11
  | 88 => 0xecbd1
  | 89 => 0xbced1
  | 90 => 0x1a4bd1
  | 91 => 0xbda51
  | 92 => 0x74bd1
  | 93 => 0xbc751
  | 94 => 0x194bd1
  | 95 => 0xbd951
  | 96 => 0x1054d1
  | 97 => 0x1a94d1
  | 98 => 0x19cd51
  | 99 => 0x19ced1
  | 100 => 0x19d951
  | 101 => 0x24b
  | 102 => 0x58b
  | 103 => 0x178b
  | 104 => 0x160c
  | 105 => 0x5cb
  | 106 => 0x17cb
  | 107 => 0x164c
  | 108 => 0x104d11
  | 109 => 0x194d11
  | 110 => 0x105891
  | 111 => 0x104d51
  | 112 => 0x1a8d51
  | 113 => 0x105a11
  | 114 => 0x104e91
  | 115 => 0x194e91
  | 116 => 0x1058d1
  | 117 => 0x104ed1
  | 118 => 0x1a8ed1
  | 119 => 0x105a51
  | 120 => 0x198d
  | 121 => 0x180e
  | 122 => 0x1a9951
  | 123 => 0x1a9953
  | 124 => 0x1a9954
  | 125 => 0x19d4d3
  | 126 => 0x10e
  | 127 => 0x149851
  | 128 => 0x94bd5
  | 129 => 0x2d651
  | 130 => 0x2d7d1
  | 131 => 0x2d051
  | 132 => 0x1a57d3
  | 133 => 0x14d
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 9 => 1
  | 8 => 60
  | 7 => 2100
  | 6 => 3684
  | 5 => 860
  | 4 => 46
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
  | 7 => packedAt gbK7 (86100+((h/700+packedAt gbK7 (77700+(h % 700)*12) 12) % 2521)*13) 13
  | 6 => packedAt gbK6 (192796+((h/1228+packedAt gbK6 (176832+(h % 1228)*13) 13) % 4421)*13) 13
  | 5 => packedAt gbK5 (53886+((h/286+packedAt gbK5 (50740+(h % 286)*11) 11) % 2009)*11) 11
  | 4 => packedAt gbK4 (3310+((h/15+packedAt gbK4 (3220+(h % 15)*6) 6) % 56)*7) 7
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x1fc3e0787fc3fffff0f807c0058e279e0cfecc
  | 1 => 0xe07c007f83fc1e00ffffffffcaf038e03333ff
  | 2 => 0xffffff8003ffe000ff0007fff303c0ffc3c30f
  | 3 => 0x7ffffffc000000fffff8003c03ff03fc03f0
  | 4 => 0x7fffffffffffff000000003ffc0003fffc00
  | 5 => 0xff80000000000000000000003ffffffc000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0xac0621814c0b28e78c836418086238e0456cc
  | 1 => 0x28080028814414121192949480b028a0113055
  | 2 => 0x5355aa8012aac024aa40432b1302c056c2c30a
  | 3 => 0x266d35558008048cc6562022c0355036c03a0
  | 4 => 0x103b1c66633309700001800c3f580001bba800
  | 5 => 0x9c00180440221180008604303fedbef8000000
  | _ => 0
def gbAtlas : Atlas := ⟨9,rawDecor 63 gbPos gbNeg, 0xfeeefee0feeaccc0feeefee0feeaccc0feeefee0feeaccc0feeefee0feeaccc0feeefee0feeaccc0feeefee0feeaccc0feeefee0feeaccc0feeefee0feeaccc0, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_16973
namespace PEqualNP.Outside.L_meta_16973
open PEqualNP.Outside.L_meta_16973.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_3_0 : Interval s0Atlas 3 0 21 := block_range (n:=21) (by decide +kernel)
theorem alls0_3 : Interval s0Atlas 3 0 21 := bs0_3_0
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
theorem bs0_4_544 : Interval s0Atlas 4 544 7 := block_range (n:=7) (by decide +kernel)
theorem alls0_4 : Interval s0Atlas 4 0 551 := (concat (concat (concat (concat bs0_4_0 bs0_4_32) (concat bs0_4_64 bs0_4_96)) (concat (concat bs0_4_128 bs0_4_160) (concat bs0_4_192 (concat bs0_4_224 bs0_4_256)))) (concat (concat (concat bs0_4_288 bs0_4_320) (concat bs0_4_352 bs0_4_384)) (concat (concat bs0_4_416 bs0_4_448) (concat bs0_4_480 (concat bs0_4_512 bs0_4_544)))))
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
theorem bs0_5_640 : Interval s0Atlas 5 640 26 := block_range (n:=26) (by decide +kernel)
theorem alls0_5 : Interval s0Atlas 5 0 666 := (concat (concat (concat (concat bs0_5_0 bs0_5_32) (concat bs0_5_64 (concat bs0_5_96 bs0_5_128))) (concat (concat bs0_5_160 bs0_5_192) (concat bs0_5_224 (concat bs0_5_256 bs0_5_288)))) (concat (concat (concat bs0_5_320 bs0_5_352) (concat bs0_5_384 (concat bs0_5_416 bs0_5_448))) (concat (concat bs0_5_480 (concat bs0_5_512 bs0_5_544)) (concat bs0_5_576 (concat bs0_5_608 bs0_5_640)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_0 : Interval s0Atlas 6 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_6_32 : Interval s0Atlas 6 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls0_6 : Interval s0Atlas 6 0 40 := (concat bs0_6_0 bs0_6_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs0_7_0 : Interval s0Atlas 7 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls0_7 : Interval s0Atlas 7 0 1 := bs0_7_0
theorem alls0 : ∀ k ≤ 7, ∀ i < count s0Atlas k, checkRow s0Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls0_3 i (by omega) hi
  · exact alls0_4 i (by omega) hi
  · exact alls0_5 i (by omega) hi
  · exact alls0_6 i (by omega) hi
  · exact alls0_7 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs1_4_0 : Interval s1Atlas 4 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls1_4 : Interval s1Atlas 4 0 2 := bs1_4_0
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_4 i (by omega) hi
  · exact alls1_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_32 : Interval s2Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 64 := (concat bs2_4_0 bs2_4_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_0 : Interval s2Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_5_32 : Interval s2Atlas 5 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls2_5 : Interval s2Atlas 5 0 40 := (concat bs2_5_0 bs2_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_6_0 : Interval s2Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_6 : Interval s2Atlas 6 0 1 := bs2_6_0
theorem alls2 : ∀ k ≤ 6, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_4 i (by omega) hi
  · exact alls2_5 i (by omega) hi
  · exact alls2_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_32 : Interval s3Atlas 4 32 32 := block_range (n:=32) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 64 := (concat bs3_4_0 bs3_4_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_0 : Interval s3Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_5_32 : Interval s3Atlas 5 32 8 := block_range (n:=8) (by decide +kernel)
theorem alls3_5 : Interval s3Atlas 5 0 40 := (concat bs3_5_0 bs3_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_6_0 : Interval s3Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_6 : Interval s3Atlas 6 0 1 := bs3_6_0
theorem alls3 : ∀ k ≤ 6, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_4 i (by omega) hi
  · exact alls3_5 i (by omega) hi
  · exact alls3_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 2 := bs4_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_4_0 : Interval s4Atlas 4 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 6 := bs4_4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 1 := bs4_5_0
theorem alls4 : ∀ k ≤ 5, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_4_0 : Interval s5Atlas 4 0 2 := block_range (n:=2) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 2 := bs5_4_0
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
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_0 : Interval gbAtlas 4 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_4_32 : Interval gbAtlas 4 32 14 := block_range (n:=14) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 46 := (concat bgb_4_0 bgb_4_32)
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
theorem bgb_5_832 : Interval gbAtlas 5 832 28 := block_range (n:=28) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 860 := (concat (concat (concat (concat bgb_5_0 (concat bgb_5_32 bgb_5_64)) (concat bgb_5_96 (concat bgb_5_128 bgb_5_160))) (concat (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)) (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 bgb_5_384)))) (concat (concat (concat bgb_5_416 (concat bgb_5_448 bgb_5_480)) (concat (concat bgb_5_512 bgb_5_544) (concat bgb_5_576 bgb_5_608))) (concat (concat bgb_5_640 (concat bgb_5_672 bgb_5_704)) (concat (concat bgb_5_736 bgb_5_768) (concat bgb_5_800 bgb_5_832)))))
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
theorem bgb_6_3680 : Interval gbAtlas 6 3680 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 3684 := (concat (concat (concat (concat (concat (concat bgb_6_0 (concat bgb_6_32 bgb_6_64)) (concat (concat bgb_6_96 bgb_6_128) (concat bgb_6_160 bgb_6_192))) (concat (concat bgb_6_224 (concat bgb_6_256 bgb_6_288)) (concat (concat bgb_6_320 bgb_6_352) (concat bgb_6_384 bgb_6_416)))) (concat (concat (concat bgb_6_448 (concat bgb_6_480 bgb_6_512)) (concat (concat bgb_6_544 bgb_6_576) (concat bgb_6_608 bgb_6_640))) (concat (concat (concat bgb_6_672 bgb_6_704) (concat bgb_6_736 bgb_6_768)) (concat (concat bgb_6_800 bgb_6_832) (concat bgb_6_864 bgb_6_896))))) (concat (concat (concat (concat bgb_6_928 (concat bgb_6_960 bgb_6_992)) (concat (concat bgb_6_1024 bgb_6_1056) (concat bgb_6_1088 bgb_6_1120))) (concat (concat bgb_6_1152 (concat bgb_6_1184 bgb_6_1216)) (concat (concat bgb_6_1248 bgb_6_1280) (concat bgb_6_1312 bgb_6_1344)))) (concat (concat (concat bgb_6_1376 (concat bgb_6_1408 bgb_6_1440)) (concat (concat bgb_6_1472 bgb_6_1504) (concat bgb_6_1536 bgb_6_1568))) (concat (concat (concat bgb_6_1600 bgb_6_1632) (concat bgb_6_1664 bgb_6_1696)) (concat (concat bgb_6_1728 bgb_6_1760) (concat bgb_6_1792 bgb_6_1824)))))) (concat (concat (concat (concat (concat bgb_6_1856 (concat bgb_6_1888 bgb_6_1920)) (concat (concat bgb_6_1952 bgb_6_1984) (concat bgb_6_2016 bgb_6_2048))) (concat (concat bgb_6_2080 (concat bgb_6_2112 bgb_6_2144)) (concat (concat bgb_6_2176 bgb_6_2208) (concat bgb_6_2240 bgb_6_2272)))) (concat (concat (concat bgb_6_2304 (concat bgb_6_2336 bgb_6_2368)) (concat (concat bgb_6_2400 bgb_6_2432) (concat bgb_6_2464 bgb_6_2496))) (concat (concat (concat bgb_6_2528 bgb_6_2560) (concat bgb_6_2592 bgb_6_2624)) (concat (concat bgb_6_2656 bgb_6_2688) (concat bgb_6_2720 bgb_6_2752))))) (concat (concat (concat (concat bgb_6_2784 (concat bgb_6_2816 bgb_6_2848)) (concat (concat bgb_6_2880 bgb_6_2912) (concat bgb_6_2944 bgb_6_2976))) (concat (concat bgb_6_3008 (concat bgb_6_3040 bgb_6_3072)) (concat (concat bgb_6_3104 bgb_6_3136) (concat bgb_6_3168 bgb_6_3200)))) (concat (concat (concat bgb_6_3232 (concat bgb_6_3264 bgb_6_3296)) (concat (concat bgb_6_3328 bgb_6_3360) (concat bgb_6_3392 bgb_6_3424))) (concat (concat (concat bgb_6_3456 bgb_6_3488) (concat bgb_6_3520 bgb_6_3552)) (concat (concat bgb_6_3584 bgb_6_3616) (concat bgb_6_3648 bgb_6_3680)))))))
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
theorem bgb_7_2048 : Interval gbAtlas 7 2048 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_2080 : Interval gbAtlas 7 2080 20 := block_range (n:=20) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 2100 := (concat (concat (concat (concat (concat (concat bgb_7_0 bgb_7_32) (concat bgb_7_64 bgb_7_96)) (concat (concat bgb_7_128 bgb_7_160) (concat bgb_7_192 bgb_7_224))) (concat (concat (concat bgb_7_256 bgb_7_288) (concat bgb_7_320 bgb_7_352)) (concat (concat bgb_7_384 bgb_7_416) (concat bgb_7_448 bgb_7_480)))) (concat (concat (concat (concat bgb_7_512 bgb_7_544) (concat bgb_7_576 bgb_7_608)) (concat (concat bgb_7_640 bgb_7_672) (concat bgb_7_704 bgb_7_736))) (concat (concat (concat bgb_7_768 bgb_7_800) (concat bgb_7_832 bgb_7_864)) (concat (concat bgb_7_896 bgb_7_928) (concat bgb_7_960 (concat bgb_7_992 bgb_7_1024)))))) (concat (concat (concat (concat (concat bgb_7_1056 bgb_7_1088) (concat bgb_7_1120 bgb_7_1152)) (concat (concat bgb_7_1184 bgb_7_1216) (concat bgb_7_1248 bgb_7_1280))) (concat (concat (concat bgb_7_1312 bgb_7_1344) (concat bgb_7_1376 bgb_7_1408)) (concat (concat bgb_7_1440 bgb_7_1472) (concat bgb_7_1504 bgb_7_1536)))) (concat (concat (concat (concat bgb_7_1568 bgb_7_1600) (concat bgb_7_1632 bgb_7_1664)) (concat (concat bgb_7_1696 bgb_7_1728) (concat bgb_7_1760 bgb_7_1792))) (concat (concat (concat bgb_7_1824 bgb_7_1856) (concat bgb_7_1888 bgb_7_1920)) (concat (concat bgb_7_1952 bgb_7_1984) (concat bgb_7_2016 (concat bgb_7_2048 bgb_7_2080)))))))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 8 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 12, 28),(inputs.getD 5 zero, 12, 44)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 6 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 2 zero, 24, 28),(inputs.getD 3 zero, 20, 28),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 7 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 1 zero, 8, 10),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 9, 41)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 7 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 6 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 36, 37),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 6 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 10 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 16, 17),(inputs.getD 1 zero, 4, 6),(inputs.getD 2 zero, 2, 6),(inputs.getD 3 zero, 2, 10),(inputs.getD 4 zero, 1, 17),(inputs.getD 5 zero, 5, 37)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xfeeefee0feeaccc0feeefee0feeaccc0feeefee0feeaccc0feeefee0feeaccc0feeefee0feeaccc0feeefee0feeaccc0feeefee0feeaccc0feeefee0feeaccc0
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4277075680 * 2 ^ 32 + 4276800704) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_16973.Model.Repr at out
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

def mono : List Gate := [⟨.and,[1,5]⟩,⟨.or,[0,2]⟩,⟨.or,[0,3]⟩,⟨.and,[7,8]⟩,⟨.or,[2,3]⟩,⟨.and,[5,9]⟩,⟨.or,[1,11]⟩,⟨.and,[10,12]⟩,⟨.or,[6,9]⟩,⟨.and,[4,14]⟩,⟨.or,[13,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075680 * 2 ^ 32 + 4276800704) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075680 * 2 ^ 32 + 4276800704) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_16973

open PEqualNP.Outside.L_meta_16973 in
theorem PEqualNP.Outside.L_meta_16973 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075680 * 2 ^ 32 + 4276800704) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075680 * 2 ^ 32 + 4276800704) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
