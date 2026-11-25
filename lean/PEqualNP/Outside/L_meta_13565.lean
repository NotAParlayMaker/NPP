import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_13565.Model
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


end PEqualNP.Outside.L_meta_13565.Model

namespace PEqualNP.Outside.L_meta_13565
open PEqualNP.Outside.L_meta_13565.Model
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

def SBf (j : Nat) : Nat := [5, 2, 5, 5, 7, 7].getD j 0

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

end PEqualNP.Outside.L_meta_13565

namespace PEqualNP.Outside.L_meta_13565
open PEqualNP.Outside.L_meta_13565.Model
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
  | 1 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0x7fff00ffffffffc03fff80fffffff807f8ffc7
  | 3 => 0xffffff00ff807fffffffff01fc03ffffff18ff
  | 4 => 0x83ffffff00007fffc03ffffe0003fff80fe0f8
  | 5 => 0x3ffffffffff8000003ffffffffc00000fff00
  | _ => 0
def s0Neg : Nat → Bits
  | 1 => 0x104b092124851444848a8b162d545b4a936b5b
  | 2 => 0xa095d84a4d4a28a3a915c0ab569aa8c5a8b5c5
  | 3 => 0x412652e88a534d293227558198c335974d18ae
  | 4 => 0x76389c8cec6c723223b9e6cd0313c6e18ee0f0
  | 5 => 0x7bc0e0f0f0707c3c3c3e78f1e3e207060fde00
  | _ => 0
def s0Atlas : Atlas := ⟨4,rawDecor 62 s0Pos s0Neg, 0xccc0c0c0cc00c000ccc0c0c0cc00c000ccc0c0c0cc00c000ccc0c0c0cc00c000ccc0c0c0cc00c000ccc0c0c0cc00c000ccc0c0c0cc00c000ccc0c0c0cc00c000, s0N, s0R, (fun _ _ => 0), s0I⟩
end PEqualNP.Outside.L_meta_13565
namespace PEqualNP.Outside.L_meta_13565
open PEqualNP.Outside.L_meta_13565.Model
def s1K1 : Nat → Nat
  | 0 => 0x7
  | _ => 0
def s1N (k : Nat) : Nat :=
  match k with
  | 1 => 1
  | _ => 0
def s1R (k i : Nat) : Nat :=
  match k with
  | 1 => packedAt s1K1 (i*3) 3
  | _ => 0
def s1I (k h : Nat) : Nat :=
  match k with
  | 1 => packedAt s1K1 (4+((h/1+packedAt s1K1 (3+(h % 1)*1) 1) % 2)*1) 1
  | _ => 0
def s1Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffffffff
  | 2 => 0xffffffffffffffffffffffffffffffffffde73
  | 3 => 0x6f9c
  | _ => 0
def s1Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffffffffffffff8205
  | 2 => 0x2552
  | 3 => 0x1958
  | _ => 0
def s1Atlas : Atlas := ⟨1,rawDecor 13 s1Pos s1Neg, 0xaaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0aaa0, s1N, s1R, (fun _ _ => 0), s1I⟩
end PEqualNP.Outside.L_meta_13565
namespace PEqualNP.Outside.L_meta_13565
open PEqualNP.Outside.L_meta_13565.Model
def s2K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s2K3 : Nat → Nat
  | 0 => 0x2802018900ef195c32bc6370c6f985d30
  | _ => 0
def s2K2 : Nat → Nat
  | 0 => 0x800c1096418ca390a318c424c2510530
  | _ => 0
def s2N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
  | _ => 0
def s2R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s2K4 (i*4) 4
  | 3 => packedAt s2K3 (i*15) 15
  | 2 => packedAt s2K2 (i*26) 26
  | _ => 0
def s2I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s2K4 (5+((h/1+packedAt s2K4 (4+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt s2K3 (98+((h/2+packedAt s2K3 (90+(h % 2)*4) 4) % 10)*4) 4
  | 2 => packedAt s2K2 (107+((h/1+packedAt s2K2 (104+(h % 1)*3) 3) % 7)*3) 3
  | _ => 0
def s2Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffdff3ffff1ffff1ff
  | 1 => 0xffffffffffffffffffffffedfc7f3fe3f0fe73
  | 3 => 0x76ff8fcffc7f0f9c
  | 4 => 0x78fff00fff800fe0
  | _ => 0
def s2Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa0180202049440a5
  | 1 => 0x122324452122a652
  | 3 => 0x9416819484a2b18
  | 4 => 0x78a4eae920ccde0
  | _ => 0
def s2Atlas : Atlas := ⟨4,rawDecor 27 s2Pos s2Neg, 0xee88aa88ee88aa88ee88aa88ee88aa88ee88aa88ee88aa88ee88aa88ee88aa88ee88aa88ee88aa88ee88aa88ee88aa88ee88aa88ee88aa88ee88aa88ee88aa88, s2N, s2R, (fun _ _ => 0), s2I⟩
end PEqualNP.Outside.L_meta_13565
namespace PEqualNP.Outside.L_meta_13565
open PEqualNP.Outside.L_meta_13565.Model
def s3K4 : Nat → Nat
  | 0 => 0xf
  | _ => 0
def s3K3 : Nat → Nat
  | 0 => 0x80a62004a2f195c32bc6370c6f985d30
  | _ => 0
def s3K2 : Nat → Nat
  | 0 => 0x132000096418ca390a318c424c2510530
  | _ => 0
def s3N (k : Nat) : Nat :=
  match k with
  | 4 => 1
  | 3 => 6
  | 2 => 4
  | _ => 0
def s3R (k i : Nat) : Nat :=
  match k with
  | 4 => packedAt s3K4 (i*4) 4
  | 3 => packedAt s3K3 (i*15) 15
  | 2 => packedAt s3K2 (i*26) 26
  | _ => 0
def s3I (k h : Nat) : Nat :=
  match k with
  | 4 => packedAt s3K4 (5+((h/1+packedAt s3K4 (4+(h % 1)*1) 1) % 2)*1) 1
  | 3 => packedAt s3K3 (96+((h/2+packedAt s3K3 (90+(h % 2)*3) 3) % 8)*4) 4
  | 2 => packedAt s3K2 (108+((h/1+packedAt s3K2 (104+(h % 1)*4) 4) % 10)*3) 3
  | _ => 0
def s3Pos : Nat → Bits
  | 0 => 0xffffffffffffffffffffffdff3ffff1ffff1ff
  | 1 => 0xffffffffffffffffffffffedfc7f3fe3f0fe73
  | 2 => 0x76ff8fcffc7f0f9c
  | 5 => 0x78fff00fff800fe0
  | _ => 0
def s3Neg : Nat → Bits
  | 0 => 0xffffffffffffffffffffffa0180202049440a5
  | 1 => 0x122324452122a652
  | 2 => 0x9416819484a2b18
  | 5 => 0x78a4eae920ccde0
  | _ => 0
def s3Atlas : Atlas := ⟨4,rawDecor 39 s3Pos s3Neg, 0xe8e8e8e8a8a8a8a8e8e8e8e8a8a8a8a8e8e8e8e8a8a8a8a8e8e8e8e8a8a8a8a8e8e8e8e8a8a8a8a8e8e8e8e8a8a8a8a8e8e8e8e8a8a8a8a8e8e8e8e8a8a8a8a8, s3N, s3R, (fun _ _ => 0), s3I⟩
end PEqualNP.Outside.L_meta_13565
namespace PEqualNP.Outside.L_meta_13565
open PEqualNP.Outside.L_meta_13565.Model
def s4K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s4K5 : Nat → Nat
  | 0 => 0x2c067922632a46152e8c02800240001a187af400000002b400036615824451516344471d009d090142d2880e7c21c260092e0a0001030883689407449c0105ff43bf43fe43fd43bd43fc43ff42fe42be42fd42fc42bc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s4K4 : Nat → Nat
  | 0 => 0x4c26800380000174881b1c000f05735000008336000b43537138c4000000046580000000003e09c026500060fc001804c00002a09800000000092001b0000000001ac1800000e8763424128000000000006d3a18000221593ce000000f408000005c2c4b1b8b872520000000084083800850f0000076000500000000001400000000010000f8ce0022868002c0018c00822b1e40000001e8000000000fe28001400000388000000001a4544200000000000000ea40191ec781523874d01114880820d059540a3f169bcb65328a003e84001cc866639000420212000001212990bc000000000003b80000000380000002f800b803179f462460000000000798432092c8006606000100000400400140000040400001c442c00100014042c000404100c340404040054000c0808040818040004027ca5a1cf947439ea86873d5490f3ea6a1cf149439e28a873f5050e7ca821cf54e429f294853e5190a7aa1215794c42aea98859e5310a7aa6216754c428ea98853e5210b5ca4214f944429ea80853e54cca7aa9996750f32bb28e657551cca7ea9194f152329faa2653c544cb3a86994f950329eaa0653d539067ca520cf946419ea84835e53106baa620e794c419ea98839d531063aa620cf948419f28883b6511067aa020cf953319eaa6639d43cc6dca598db54b319faa4633c548c67ea898cf15131cea1a633e540c67aa818cf953219eaa6435e53c86baa790cf952219eaa4435e53886baa710cfd51219e2a2433f5408678a810f948421af29e815d53d033ca7a04f54f40cea9e811d53d027ca5a04f947409eaa4813f5350278a4a04f14540dda82813e541027ca9984f553309f2a4613d548c33a87184f951309eaa2613e540c27aa8186750c30b7290616d520c2eca2185d544309faa6413c54c827ca9104f552209faa2413c54482bea6905714d20bba8a4174514827ca8104f55020af298415d53082eca2105d544209faa6213c54c427ca9084f552109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s4K3 : Nat → Nat
  | 0 => 0x30080194010008800018c80000b00680a0001e00e9a200a48ca96b800240047000040010130008758e5190a1f6354242c550d51cca3661d523287195434ca8c6250d328758e529061f6354241c350d52cc62e62d523187195434c6946150d318758c544861d63150218e580540861d63149408758c515021d63951308b189544c2346155130c350d520c31543544308758c54c821d63952208758c54c421d6395210
  | _ => 0
def s4N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 134
  | 3 => 26
  | _ => 0
def s4R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (i*5) 5
  | 5 => packedAt s4K5 (i*16) 16
  | 4 => packedAt s4K4 (i*27) 27
  | 3 => packedAt s4K3 (i*38) 38
  | _ => 0
def s4I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s4K6 (6+((h/1+packedAt s4K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s4K5 (864+((h/16+packedAt s4K5 (768+(h % 16)*6) 6) % 58)*7) 7
  | 4 => packedAt s4K4 (3970+((h/44+packedAt s4K4 (3618+(h % 44)*8) 8) % 234)*9) 9
  | 3 => packedAt s4K3 (1036+((h/8+packedAt s4K3 (988+(h % 8)*6) 6) % 45)*6) 6
  | _ => 0
def s4Pos : Nat → Bits
  | 0 => 0xffff0ffffffff81ffff07ff07fffffe78f1ff
  | 1 => 0xf07fff03f07e1ffe1e0ff87ff878383fa73e93
  | 2 => 0xff83fffc007fe1ffe00fff87ff803fc1c7cf1c
  | 3 => 0x3ffffff8001fffff00007ffffc001f80fe0
  | 5 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s4Neg : Nat → Bits
  | 0 => 0x800010208010000044120088008a0a10085025
  | 1 => 0x2519221924a430960a854853485090aca32692
  | 2 => 0x432a44486949032aa109950595012585458b18
  | 3 => 0x6a5388924c0d55cd33a0c446e6658109f00dc0
  | 5 => 0x8c630ee38e7199f1ddcee660c4460631fef000
  | _ => 0
def s4Atlas : Atlas := ⟨6,rawDecor 47 s4Pos s4Neg, 0xeae8eae8eaa8eaa8eae8eae8eaa8eaa8eae8eae8eaa8eaa8eae8eae8eaa8eaa8eae8eae8eaa8eaa8eae8eae8eaa8eaa8eae8eae8eaa8eaa8eae8eae8eaa8eaa8, s4N, s4R, (fun _ _ => 0), s4I⟩
end PEqualNP.Outside.L_meta_13565
namespace PEqualNP.Outside.L_meta_13565
open PEqualNP.Outside.L_meta_13565.Model
def s5K6 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def s5K5 : Nat → Nat
  | 0 => 0x43a2540d00991803850006007d00056054822eb489b007910c1c910992c3c00000bc5884e1d70a260161a4a14a9206a8c100014004400b58800200014c102ff43fe43be43fd43fc43bc43ff42bf42fe42fd42bd42fc42ff32fe32fd32fc32ff41fe41be41fd41fc41bc41ff31fe31fd31fc31ff21fe21fd21fc21ff40bf40fe40fd40bd40fc40ff30fe30fd30fc30ff20fe20fd20fc20ff10fe10fd10fc10
  | _ => 0
def s5K4 : Nat → Nat
  | 0 => 0x1c091040c2300000302e05cd07d001acf00d00140002c3c84c4a4137068b40522a04426f3f95cf628000e420530e19406180b164a45433a14140b4012402071d0f8e6690a16c627a2f838e24b0008c6a3c16990e836219b41e271a0747a1f158bc0c001709800113a808c6373e07894192a800fc0014800a20000054cc4e2686c7e470480000002780000122020cc40400180d432220200000199d8762a3600084562e8009070260000072001dc445800080c2842f0001408141c0000e800001c000018e0000000040020000480140018141c44783c98641004300800102c00541e7ca721cf54a439f28c873d5090edca421db548439f298879e5310f5ca421cf54843d6a90872d5210e7ca221cf540439f29e853e51d0a7aa1a14f552429e29a85af5250a78a2a14fd41429f2a0853f54cca78a9994f952329eaa465ad428caeca3195d546329faa2653c544cb5a84994f950329eaa0653e539067aa520cf946419ea84836e52106daa420cf94c41d7290833d521075aa420cb548419f28883b6511067aa020cf953319eaa6636e52cc6daa598cf952319eaa4636e528c6daa518cfd51319e2a2633f540c678a818f54c4319f2a6433d54c86bca790d754f21d6a16433f5488678a910cfd51219e2a243ad424867ca810cf55021b7296816d52d027ca7a06b94b409ea9681ad52d025aa5a04f947409eaa4813c535027ea4a04f14540dda82813e541027ea9984f153309f2a4613d548c27ea8984f15130b7a92616c524c2eea2985d145309f2a0613d540c2dca4185b54830bb2886175510c27ca9904f553209f2a4413d548835a85104f951209eaa2413e540827aa8105794c20aea9841ad42082eca2105d544209faa6213c54c427ca9084f552109faa2213c54442bea6885714d10b7a92216c524427ca8084f55010af298215d53042dca4085b54810
  | _ => 0
def s5K3 : Nat → Nat
  | 0 => 0x61a50042c01e232a00a8093011298281c28088002e0003960000063001070000462ca8b58a5190e2f62542438d98754ccb2542546328b195424ca8c63509328b58a539062f62542418b588544c62d62150318e580540c70d5350b218798f548862c6550921a9185424862d6214d408b588515022d62153308b58a548c22d62951208718d54482346155120c354d420832542544208b58854c422d6295210
  | _ => 0
def s5N (k : Nat) : Nat :=
  match k with
  | 6 => 1
  | 5 => 48
  | 4 => 134
  | 3 => 26
  | _ => 0
def s5R (k i : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (i*5) 5
  | 5 => packedAt s5K5 (i*16) 16
  | 4 => packedAt s5K4 (i*27) 27
  | 3 => packedAt s5K3 (i*38) 38
  | _ => 0
def s5I (k h : Nat) : Nat :=
  match k with
  | 6 => packedAt s5K6 (6+((h/1+packedAt s5K6 (5+(h % 1)*1) 1) % 2)*1) 1
  | 5 => packedAt s5K5 (864+((h/16+packedAt s5K5 (768+(h % 16)*6) 6) % 58)*7) 7
  | 4 => packedAt s5K4 (3970+((h/44+packedAt s5K4 (3618+(h % 44)*8) 8) % 161)*9) 9
  | 3 => packedAt s5K3 (1036+((h/8+packedAt s5K3 (988+(h % 8)*6) 6) % 38)*6) 6
  | _ => 0
def s5Pos : Nat → Bits
  | 0 => 0xfffff0ffffffff81fe0fffff07fffffe47f1ff
  | 1 => 0xf07fff03f0fc1ffe1ff0f07ff870783fb93e93
  | 2 => 0xff83fffc00ffe1ffe000ff87ff807fc1c1cf1c
  | 3 => 0x3ffffff0001ffffff0007ffff8001fe0fe0
  | 4 => 0xfffc0000000001fffffffff800000001fff000
  | _ => 0
def s5Neg : Nat → Bits
  | 0 => 0x10001020802000004401208800940a10025025
  | 1 => 0x25192219214930960a905453482150ac992692
  | 2 => 0x432b44486a9313aaa1889d45d5026585c18b18
  | 3 => 0xa528892481a454d332a0806a64b01096c0dc0
  | 4 => 0x8c630ee38ce399f1ddccee60c40c4631f7f000
  | _ => 0
def s5Atlas : Atlas := ⟨6,rawDecor 31 s5Pos s5Neg, 0xeea8eaa8eea8eaa8eea8eaa8eea8eaa8eea8eaa8eea8eaa8eea8eaa8eea8eaa8eea8eaa8eea8eaa8eea8eaa8eea8eaa8eea8eaa8eea8eaa8eea8eaa8eea8eaa8, s5N, s5R, (fun _ _ => 0), s5I⟩
end PEqualNP.Outside.L_meta_13565
namespace PEqualNP.Outside.L_meta_13565
open PEqualNP.Outside.L_meta_13565.Model
def gbK8 : Nat → Nat
  | 0 => 0x3f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x2d23324b3f3b44033c0e0c2b1a114543020009002c0000003400310d471237481410004000002e42172230000b00351e134100270a16211946283618293d1c3e3300051d060f494a2000383a0000010025262a082f0715041b241f3901002c09600c40020644007023c3090024288060c10d00ffd5003fe5400ff55003fc54017fd4c057f53017f94c05fd53005f54c05fc5300ffd0c03fe43006f90c03fd4300ff10c03bc43017fd4805fe52005f94805fd52017f148057c5200ffd0803bf4200ff90803fd42006f50803fc42007fcc801fe32007f4c801fc32017fd4405fe51005f94405fd51017f144057c5100ffd0403fe41006f90403fd4100ff10403bc41007fcc401fe31007f4c401fc31007fc8401fe21007f48401fc21017fd40057f50017f94005fd50005f54005fc5000ffd0003bf4000ff90003fd40006f50003fc40007fcc001fe30007f4c001fc30007fc8001fe20007f48001fc20007fc4001fe10007f44001fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x104007df9482003ef8a41001fbf420800fdea104000bf9842001fecc210002f661080017eb084003fd58420005eac2100037e510801fbe2884000ef90420077788210003ee210800ff61084003bf9802001efea01000f7d5008007dfa004003ef5002001fde401000ffa2008007f69004007fe4802006dfecb880037f65c40013fb2e2002bf9971006dfacb8800afc65c401bbe32e20029f19710035fec988003bf64c40015fb262001bf99310035fac988006fc64c400dde3262001af19310005fec788022fe63c40017eb1e2008bf18f1006efea7880037d53c4001df21e2006ef10f10005fec58801efe62c40017eb162007bf18b10006fca5880377c52c400ddfa162000ef50b10006fca3880377c51c4001df20e2006ef10710007ec6388003f531c4001fb10e2000fd4871006efea1880037d50c400ddfa062000ef5031001dfecb0800afe6584007bf32c20029f99610065facb0800f7d65840013eb2c2003bf1961001dfec908006fe6484007df3242001af9921005dfac90800fbd64840015eb242003bf1921001dfec708022fe63840017eb1c2003bf18e10066fea7080037d5384001df21c200bef10e1001dfec50801efe62840017eb142003bf18a10006fca5080337c5284017dfa142000ef50a1004dfac3080037e5184019be28c2000ef9061005f78830800efe6084007bfa842003df5421001f7e810800fbd4084007fb8842000fec4210055feca880037f65440013fb2a2002bf99510055faca8800afc6544015be32a20029f1951004dfec888003bf64440015fb222001bf9911004dfac888006fc6444013de3222001af19110005fec688003df63440016fb1a2008bf98d10005fac688022fc6344001ee31a2000b718d10056fea6880037d5344001df21a2009ef10d10005fec488003ef624400177b122007bf98910005fac48801efc6244001f63122000bb18910006fca48802b7c5244013dfa122000ef50910006fca28802b7c5144001df20a2009ef10510007ec6288003f53144001fb10a2000fd48510056fea0880037d5044013dfa022000ef50110007f6208800ff610440077fb282002bf9941001efcca0800a7e650400b7eb282003df59410004faca0800efc65040077fb202001bf9901001f7cc808006be64040097eb202003ef590100057ac80800efc64040077fb182008bf98c1001fbcc608002de63040017eb182003f758c10005bac60800efc630400bbfa982000df54c100077c8608013bc43040077fb102007bf9881001fdcc408002ee62040017eb102003fb58810005dac40800efc6204001bf2902005df148100277e8408003bd420400d7f3082000df9441002ef8a208003be4104009de2082003bf9801001efea00800f7d5004007dfa002003ef5001001fee200800ffa1004007fa8802000fe44010
  | 1 => 0x77c514c001df20a6018ef10530007be6298003dd314c033bfa826000df541300c77e8098003bd404c011fd9826003f78c13001dfeca1800afe650c007bf32860029f994300bdfaca1800f7d650c0013eb286003bf1943001dfec818006fe640c007df3206001af990300b5fac81800fbd640c0015eb206003bf19030045fcc6180237f530c011bea986008ef90c3004778861801efe620c007f73106000bb98830005fac41800fed620c00176b106000df948300bef8a41805bbf420c001dea106000bf9843001fecc218002f6610c0017eb086003fd58430005eac2180037e510c02fbe2886000ef904300b7788218003de310c011ee1886003bf9803001efea01800f7d500c007dfa006003ef5003001fbe601800ffa300c007ee9806008fe4c03003dfecb9001f7f65c800f3fb2e4002bf997200adfacb9001efc65c800fbe32e40079f1972003dfec990006fe64c800fdf3264001af993200a5fac99001fbd64c80015eb264007bf1932003dfec790022fe63c80017eb1e4007bf18f200aefea7900037d53c8001df21e4014ef10f2003efca59001f7c52c800fdfa164007ef50b2003fdc6590003ed32c80017f30e4000bf58720006fca3900577c51c8001df20e4014ef1072003fde4390003ed21c802bbfa864000df543200a77e8190003bd40c80077fb2c4002bf9962001efccb1000a7e65880277eb2c4003df59620004facb1000efc65880077fb244001bf9922001f7cc910006be64880257eb244003ef592200057ac91000efc64880077fb1c4008bf98e20005fac71000efc6388027bfa9c4000df54e200077c871004bbc43880217eb144007df94a2003ef8a51004bbf4288001dea144000bf98620005fac3100037e5188027be28c4000ef90620097788310003ee2188001f610c4003bf9822001efea11000f7d5088007dfa044003ef5022001fde411001ffb20880237fb2a4000dfd9520004feca9000afe65480237eb2a4002bf1952008ef8ca9000a7c65480217fb224001bf991200877cc890006be64480217eb224000ef591200057ac890006fc64480017fb1a4008bf98d20005fac690022fc6348023bfa9a4000df54d200077c8690043bc434800fbf2924007df149200877e8490003bd4248001f71924000fb4c920005fec290002fc6148001bf28a4011df145200077c8290043bc4148001f790a4000fb4852008efea0900037d5048021dfa024000ef5012003ff6409000fee20480077fb284002bf9942001efcca1000a7e650801f7eb284003df59420004faca1000efc65080077fb204001bf9902001f7cc810006be640801d7eb204003ef590200057ac81000efc64080077fb184008bf98c2001fbcc610002de63080017eb184003f758c20005bac61000efc630801fbfa984000df54c200077c861003bbc430800f7f3
  | 2 => 0x50006fac6a80037c635403fbfa1aa01fdf90d500067c86a807f7d435403fbe21aa01fcf10d50006fec4a80037e6254001beb12a000df1895003cf8c4a807f7f425403f9fa12a01fdf909500fefa84a80033d425403fbe212a000dfcc950006fc64a80037d3254001be192a000dfd8550006fcc2a80037d6154001be30aa0009f185500fefe82a807f7e41540019f20aa01fdf505500fef882a807f3c4154001bf98aa000df8c550006fa62a80037c3154001bf90aa000df88550006fa42a80037c2154005bfb02a0029fd8150016f6c0a807f7f405403f9fa02a003df901500fefa80a800f7c405403ddfb2a801eef995400f77acaa007bbc6550001dfb1a8000ef98d400077ac6a0003bc63500115e31a801eefd4d400f67ea6a007bbe535003ddea9a8000cf54d400f778a6a0003bf62500015fb128000ef989400077ac4a0003bc625003ddfa92801eef949400067ca4a007bbd525003dde292801ecf149400077e64a0003be3250001de9928000ef0c9400077ec2a0003be6150001deb0a8000ef1854000578c2a007bbf515003ddf28a8000cf945400f77aa2a007bbc515003d9e28a8000efcc5400077c62a0003bd3150001de18a8000efc85400077c42a0003bd2150001de10a8001efd814000d7ec0a0007bb605003ddfa82801ecfd414001f7ca0a007bbd50500019ea828003ef14140045fecb9800afe65cc011bf32e60029f997300edfacb980237d65cc0013eb2e6008bf19730045fec998023bf64cc0115fb266001bf993300e5fac998022fc64cc011de3266008af19330046fea7980237d53cc011df21e6008ef10f3003dfcc598002fd62cc001bf296601ddf14b300e77e8598003bd42cc011ef9966000f74cb30005fcc398002fd61cc001bf28e601ddf147300077c8398073bc41cc011ef98e6000f74c7300eefea1980037d50cc039dfa066000ef5033001dfecb1800afe658c007bf32c60029f996300ddfacb1800f7d658c0013eb2c6003bf1963001dfec918006fe648c007df3246001af992300d5fac91800fbd648c0015eb246003bf192300c5fac71806f7f538c001bea9c6008ef90e3004778871801efe628c0017eb146000df94a300def8a51806bbf428c001dea146000bf98630005fac3180037e518c037be28c6000ef906300d7788318003de318c001ee18c6003bf9823001efea11800f7d508c007dfa046003ef5023001fbe6118023fb308c0337fb2a6002bf995300cefcca9800a7e654c0337eb2a6000df59530004faca9800afc654c0317fb226000efd91300057ec898006fe644c0317eb226001bf191300c778c898006bc644c033bfa9a6000df54d300477c8698023bc434c0017fb126007bf18930006fca4980677c524c031dfa126000ef50930007be6498003dd324c0017fb0a6000bf18530006fca29806
  | 3 => 0xf20a622bef10531047ee6298803de314c4017fb026203bf18131166fea0988afbf404c4117fb286202bf99431046fcca1880a7e650c4537eb286208df59431004faca18822fc650c4117fb206208efd90310457ec818806fe640c4517eb206208bf1903104778c818822bc640c4117f3186208dfd4c31046faa618823be430c411de2186207bf98831005fac4188037e520c453be2906228efd08310077a8418823df320c401ee990622abf98431006fca2188a77c510c401df2086228ef10431047be6218823f6310c401ee9886208fd4c431007aa621880efe600c4017eb006229dfd40311477e801881eff65c84057f32e4207df99721014fccb9089efd65c840fbeb2e42009f5972103df8cb9081eff64c84037f3264207ef9932100d7cc99089afd64c840fdeb264200af5932103df8c99081eff63c84117f31e4207f798f21005bcc790802fd63c840feeb1e4200b758f2103df8c79089f7f53c8401bea9e4200ef90f2113778879081f7e52c840fbe2964207efd0b2103f7a85908037e51c844fbe28e4200ef9072113778839080efe60c84017eb064227dfd43211377e8190896ff65884057f32c4225df99621014fccb10896fd6588401beb2c42009f59621015f8cb1088aff6488401dfb244200afd922100dfcc91088afd64884037e3244222ef1922100d78c910802ff63884117f31c4200bf58e21045f8c7108977f5388401bea9c4200ef90e2111778871088efd628840fbf2944207df14a211177e8510803bd4288401f71944200fb4ca2103dfcc3108037e518844bbe28c4200ef90621117788310803ef218840ffb90c4203bf98221005fac1108977f5088445dfa044224bfd9521006feca908027f65484057f32a4224bf59521015f8ca908937c65484053e32a4223bfd91210077ec890802bf64484037f3224223bf5912100df8c89088fbc64484035e3224200bfd8d21045fcc690802fd63484117e31a4224dfd4d21006faa690803be4348447de21a4207df9492103ef8a49088fbf4248401dea124200df94521126f8a290803be4148447de20a4207fdc8521007dc4290802ff60484077e3024224dfd412111f7e809081eff650840fbfb2842079fd9421015fcca10886fd650840f7e3284207df1942103cf8ca1081eff64084037f3204207ef9902100d7cc810882fd640840fdeb204200af5902103df8c81081eff63084117f3184200bf58c2103df8c6108877f5308401bea984200ef90c2110778861081efe620840fbf2904207df1482103f7e841081fbd420840ff71904200fb4c821115fcc2108037e5108443be2884200ef9042110778821081fef210840ffb1084200fb4842103fea421080efe60084017eb004221dfd40211077e801087f7f645403fbf322a01fdf591500fef8c8a80037f63540013fb1aa000df98d
  | 4 => 0x23bc430c80f7f3106407df9483203ef8a41901fbf420c80fdea106407f7cc83203fdc641901fdd320c811f69906400bf98432005fac2190cf7c510c865de2086403bf98032005fac0190cf7f500c865dfa006431dfd925118efcc9288c77d6494463be324a200dfd8e51006fcc7288037d63944013eb1ca200df18e5118efe87288c77e43944019f21ca231df50e5118ef887288c73c4394401bfb14a200df98a5103cfcc5288037d6294401be314a231dfd0a5118e7e85288c77e4294463bea14a200cf50a5118ef885288037f3294401bf194a200df4ca51006f8652880b7e61944053f30ca202dd9865118efe83288c77e4194463bea0ca231df1065118e7883288037f6094401bf304a200df58251004fac1288037c6094463bfa04a231cfd025118efc81288c77d4094463be204a230efd96411877ccb208c3bd6590461de32c8200efd8e410077cc720822be6390401deb1c8200ef18e411877ea7208c33f5390461df29c8230ef54e410067aa7208c3bc5390401dfb148200ef98a410077ac520802bd6290401de3148230efd4a411877ca5208033e5290461dea948230ef14a4118678a520803bf3290401df1948200ef4ca41007786520807be61904035f30c8201ed986411877ea3208c3be51904019f28c8230ef5464118778a3208c33c5190401dfb048200ef982410077ac120802bd6090401de3048230efd42411867ea1208c3be5090461dea848230ef14241045fecb9880afe65cc411bf32e62029f9973117dfacb988237d65cc4013eb2e6208bf19731045fec998806fe64cc411df3266201af99331175fac998823bd64cc4015eb266208bf19331046fea7988237d53cc411df21e6208ef10f3103dfcc598823ee62cc401773166200bf58b31047dac598802ed62cc401bf296622fdf14b311777e8598803bd42cc401bf28e622fdf147310077c83988bbbc41cc4077f3066200bf5833117efea1988bbbf40cc45b7fb2c6200dfd9631004fecb1880afe658c45b7eb2c6202bf1963116ef8cb1880a7c658c4557fb246201bf992311577cc918806be648c4557eb246200ef592310057ac918806fc648c4577eb1c622ddfd4e31006faa718823be438c411de21c6207bf98a31005fac5188037e528c45bbe294622aefd0a310077a8518803df328c401ee9946208bf98631006fca3188b77c518c401df20c622aef10631007be6318823f7318c4077f3046200bf5823116efea1188abbf408c4597fb2a6200dfd9531004feca9880afe654c4597eb2a6202bf19531166f8ca9880a7c654c4577fb226200efd91310057ec898806fe644c4577eb226201bf1913115f78c898806bc644c459bfa9a6200df54d310477c8698823bc434c4017fb126207bf18931006fca4988b37c524c457dfa126200ef50931006fca2988b37c514c401d
  | 5 => 0x925203e7ac92901f7c649480fbfb1ca407df98e5203efac7290027d639480fbe31ca43bdfd0e521defc87290033e4394877bea1ca43bdf10e521de78872901f7e629480f3f314a407db98a5203efe852901f3f429480fbf214a407df50a5203ef8852901f7f619480fbf30ca4009f9865203efac32901f7c6194877bfa0ca43bdf906521defa83290ef7c41948779e20ca407dfd825203efcc12901f7d60948013eb04a407df182521defe81290ef3f4094877bf204a43bdf502521def881290ebbf65508019fb2a843aef995421d77acaa10ebbc65508759e32a8400efd8d420077cc6a1003bd6350801de31a8408af18d421d77ea6a10eb3f5350875df29a843aef54d420067aa6a10ebbc5350803dfb128401afd894200f5ec4a10ebbf525080fdf2928407cf949421d77aa4a101fbc525080f9e2928400efd85420077cc2a1003bd6150801de30a8400af185421d77ea2a10ebbe5150875dea8a843aef145421d678a2a1003bf60508015fb028400ef981420077ac0a1003bc6050875dfa82843acfd41421d77ca0a10ebbd5050875de2828408bfd9732015fccb990237e65cc8053f32e6439bf59732046facb990027d65cc8117e32e6408bfd93320477ec999022bf64cc8037f3266438bf59332045f8c999023bc64cc8115e3266408dfd4f32047bca7990237d53cc873eea9e6400d754f320477c8799023bc43cc80fbf2966407df14b321c77e8599003bd42cc8017f30e6400bf587321cef8a3990e3bc41cc8077f3066400bf583321cefea1990e3bf40cc80f7fb2c6407dfd963203cfecb1900afe658c86f7eb2c6407bf1963203ef8cb1901e7c658c80f7fb246401bf9923203f7cc919006be648c86d7eb246407ef592320057ac91901efc648c8697eb1c6437dfd4e32006faa719023be438c811de21c6407bf98a3203efca51901f7c528c80fdfa146407fb90a3203f7a85190dbed428c801d6a146407f7cca32047de6519002fe618c8017eb0c6437df146321b778831900efe608c8017eb046437dfd42321b77e81190d6ff654c801bfb2a64009fd9532015fcca990d6fd654c8057e32a6435df19532014f8ca990d2ff644c801dfb226400afd913200dfcc8990d2fd644c8037e3226434ef1913200d78c8990d77f534c86bef29a6400df54d321afbaa6990035d534c811df21a6408ef10d3203efca49901f7c524c869dfa126434fb909320077a84990d3ed424c801d6a126408fbcc93203fbc6499002ff614c8017e30a6435df145321a7788299002ff604c8077e3026435dfd41321a77e809901eff650c8057f3286407df99432014fcca190cefd650c80fbeb2864009f5943203df8ca1901eff640c8037f3206407ef9903200d7cc8190cafd640c80fdeb206400af5903203df8c819022fe630c811bfa986408df54c320477c8619
  | 6 => 0x100001c0400000e0040300100c05c0082300400c0800d00a024008000000040c80600401001000008014018000020000001801004c0b00201e0000000b000008018000000040380000202c0800c02e0000900100400c020080000000100d0020080681900000402806004000050020160000300002a0000100a0080c8068000100000100503200408004000000028060080180200500003004804002000018030100040f0000000000101b0060000000201800c0300000c0700380b0260040200004600c000020220000000000c000008030060101000b000018010010000000000300e0300500000c008050000100180200401003801802000038030000040000d00101e000020100000340080600001012803008000000040000080280000e0000082d0040680100500c030048000000080000b0060040000001c02018801006038000060000000080007e0000400300c004000040500080500b000010088050020a803007014000130000000040080000800000001000000068070020181b80900a000010000060100080100e02400822000004088040000140300804e010110000000042080a00200401000004000000020220200600e00206c028020000000080200602c0001a0000040300000c00801002014000008000000740380a02800c0200000600001000010000040000000040580001400c02004002014060010040140480300607006003008004020060100040180900400000001006008028130020000d00600401000001020054008030120000380101200000002002000068000020000d80900000809800002000000010183ddfd91530067ec8a98f77e6454c7bbeb22a63ddf191531ee78c8a980b7f6354c053fb1aa602d7d8d531eefe86a98237e4354c7bbea1aa608df10d530467886a98037f6254c01bf312a600df58953006f8c4a981e7c6254c7bbfa12a63dcfd09531eefc84a98f77d4254c7bbe212a600dfd8553006fcc2a98037d6154c01be30aa6009f185531eefe82a98f77e4154c7bbea0aa63ddf105531ee7882a98037f6054c013fb02a600df98153006fac0a98037c6054c7bbfa02a63dcfd01531eefc80a98f77d4054c7bbe202a608efd96430477ccb218233e6590c11deb2c8608cf5964304778cb21823be6390c115f31c8608e798e430477ea7218233f5390c11df29c8608ef54e430467aa721823bc5390c11dfb148608ef98a430477ac521802bd6290c11de314863cefd4a431e77ca5218f3bd5290c79de294863ccf14a430477ec321823be6190c015f30c8608ef5864304778c3218f3bf5190c79df28c863cef546431e778a3218f33c5190c11dfb048608ef982430477ac121802bd6090c11de304863cefd42431e67ea1218f3be5090c79dea84863cef1424303efec92901f7e649480f9f324a407df5
  | 7 => 0x60005f28f80f088a4b00c48d63ca7463124928d000085813890a9c696a4a80000007e840c6dc1a613a34ea9cad601e69e7945d4578acca164460864609fa47ea067aa0000e04100001c43b2ab68a811a8069f40009b200098249071688414e62460cab0b007043e49e87d824a0007c682e69c00000033c0000000004a0a0c9b43ba2d87e692a7f63540000004943f89987a884e5601f421c596af4a126282cc5e208486481c2b05349b06f809c2a400098a79239a3022aa2382840000002760009461ec00000044e3b643018e0006d09266b8a1aa8c2fe18c2b27b4742920000a5081200017e92c558a900004d2100a2a3ec8f40a66d80000001b28620000006447ea0000009a078e99a0003764c26867fa9c40003b443a00026814a7b297e0000008940000000000006805da0727820000000320b070e9009d001800000000000090c19400095e0c2344000000642000000000000576af667a37422478ca827785ce0000bea6000000000000000000000000000000098e0001ac5de27258800018078077257ea5a0000000000008e401600077033e0006fe8de27858a67ead000055a6546c894e88025e110256250006a7e39200001079e55ca4e000000a9a8ec0bc05671e67817823c84282c3a00006cca3c15639863696809a2603fea567621bc96220073e03a0526105924988883666082e80000008701f222e4dc05431a82a09411e5d25b4aae00059a3e004a89eb0a34a75663c1823386227ee6ce7749a24aa9ae00a84caee1465d87ca000000840a444e84fab02a9e6844668c00004124820002da000a8841e59461a39e7000000003629344bc89252635217a754172a269022c403c43e6e40000000008267dc92220c47429c5661500000001449766e825a81e90637a6de00000000093c0006b4a2400047c53c52ea10b1050e00002a06086e7140003c6ac06ea0a24c69d83502bca2825868c000004a0e4a49908e63ea7d621a5ee18481483e378174ae442a05e42e32e15e1e85b646c4b896c3c410eb0c11230e9123063e29ee80e99274a5a259860a28a8b634230c5c009246e40475c1d83b804c33a1245e43be5f030081a4229ca67019c1320669b86c68960f65a40000005e63c850470c0007a65cc89a000000000202000000000318154266310af265c00000000000076a38a4ec00045aa2e32c6b66309e2650918a1824c5f626e0641c838e5dca5c86c280502abaa3006c6984721ce2be9fc1202887fc69a4f20002c00006880a42168be52207079aa340cc0807d003693607685666e9946262f251a3b00000000d89a4000000000a2c0005484260004426a08f00b434800065a0821de2a800062000407c0280202401803002010004000220040b40000a00e0100300000c000090000000040000500c0000600000000c018090160000400
  | 8 => 0x9d2802294ae868200070a00021e00061e75200000088e5200002fc98064618843217c24038076e4be6e200000014c8bc00000000067c6b21023c285273456c000042afc000298a7c49a30a6e08d25c28904e213e7842260a02c25d66ae01c23600066845e832000ada58687271a0001863688e06d27f00300000000006047500fe93a96453ea6851c5563fa8c47c400036c3f030800075810a3c00fa4ea000a1c00c270aacac4ad800000000000057c000ac260e00048a0007083569aaa6a5320007244a29be8485002ee000000160000adc0000002a023a7f89ce7e42207985901188361f835a00059e4805be5e8488718040ae62b82d42040008464347cc1fe00044041473864e38c7ac4088d81680ca00036040e0d018a0007da0009de2fa8661040ee20600003ea3a56e0e69c00dc000a4a5720624160e292e31c0001be00000000047a4c40340001aa97c1480008d400081859c6be0aa26c0e80009f09e635e88c2b61082f88fc0009ec7d44d475e00022a9ba6f6ab20000009ac00045869650839c9d41344b62a200084a40012a00033400000000094c0000007be6900ac45290e00080c7c000000045c8ce2b45e05187129504da8aa0ae06800000016a0c68c291c07c4d00004205bca74000ac82ea43856400097a7c23e65b03ae5449280000000009e03d80000000000006345686028820008300000002f65826ba52a9a83280d4ab84fc8b09f26622ce0483320e45360001ca5301901c00000002dc95200085e70619e1d06f20000001584f66661969489840c80000005ec3a807a07824800000074c000a3e8ca0000002a64f81a03ac00000000000000000026400000028c6ac02e00000000000000035800091e7ba1e600000079605842c66000000023200008e000a0236e8b80a80001b0000a8a2de41c3d45ac68a75a1f69d600068e02c2181d66a45fe6bc3a60000009540006e691a2623a246a0000000003244280000002d656a0460000000007664d662a06a0f45ea176a6244c5282926da54054ea369dc542768a465a07b80008540449148ac21055019a71065eabc01a868512000000b160000001cc1c66c200027a06e0003ee87e00000074e09800005c27e16452c8f26a8b14000790a322e07304760d26ee7265c8aa664c0009b608a00063a3860000008449fe000000972252296000a804ba000a6e732000ace99634661429ea2037e1168348a61dc0248ba78a0003a4760000022a78000aec0ce12c1227208c8632ab42f40004f06ec45600096009e0009e4a960006ca0001d400057000000000000013c5a85d05f40000000000023cc0000000000004540008502122ca3307ae7e00002144ee3144cea760008ae7ce0006b01b60009440000000004247024cc80000000064800000000000000073a5b83821fc34c4f46727865a
  | 9 => 0xa00a141ea20e0000f2000b0800000000000000095a85c000a048c6aea66c000000910afe35c1e4506000000000a1e0000b60000000000002ba0000003aa0000000003f4a846181b81528a42280005c68cc0000000000963701620ba00000065283a0900003f6a400000000007a08e88da0006f463e6584702346a27bc39079c24e36a36420aa585ca6389a6000abe000a9400000011c67494200083824472e1e28242c88dc61c64054626aa7077c15a03888601247837277682298600816c00000e0d699c76400002854a83c000000aa894a8b20000001a800029a4c82e6aa477e7e20145ae76c6c4600ad20008783d600000000000041a1b40000004d89da3262545169249085ba0265620000000000008e2396940a080005740c00ec0000b2000000316000000a5e20800048e3d048612623e8744a69384845f832a0000000004184ac7de0003942421ee37cae067654c74487aaaa9cca86524128a4c00073c6aa90462e05058e0ea46895c1ba98c08c48c99e9c849c4967d20b8230aca6f043ca8e57a6d65103208288202220da2d06941704508a2af87f215c9f81407b043604e274584130ad4a3897485a96e4b207e8b41360000000001fa000000000a5200055e0001060004ae1420004ca2acac64e6462a667ec0005fc00000000000000040a00095612e808a7271c0009665aa9f6b06a7a804aa07c83fc27c1ae0de8fe5fa0005c45380003f27406160002903d29320000001a40000000006563400003220002f0000ae210c62c0009780008ee0004feade64a0008760000003848160000000000002464de000a5449e2e21f06c04e00009581da3bc388a0aa2277a9ea50cb0e7881983041a26fc0000000008100200000000000008f68a04064484b4a6428e9c26a60001147f4000988b187483ce00072ca927b6a481d20002d20000887a405a72a0002c680a000000612514000000a42a6c22c5b28981c2860afaaa200031e2864e446458044a6d47fe55400000000051e0000000fc25c0001662e44c00f86927a293e07400072816e000b048ea6068fa2823de0000003dc6fa00019200000000066433600087caf0000a980002ae58c9163e80001e0402000736b125522ec9bc3da72266a97093086a89c50a53a444
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0xc64945100065f63945100065c63945100066f62945100066c629451005cbe76905100063f65905101863c65905100069f63905100069c6390510006af6290510006ac6290510046d4638c51001cf4764c510046d4634c51003ee4628851001cf476485100147c76541100063f64541100fe3c64541100065f63541100065c63541100066f62541100066c625411000574715411001f70105411000cbc76501100063f65501100f63c65501100069f63501100069c6350110006af6250110006ac6250110005b4715011001cfa76c41100047f73594100063c435941003c7c72594100063f425941002c7c71594100063c415941001c7f705941001c7d705941001e3f405941001e3d4059410044bc73590100063f5359010004bf72590100063c5259010024bc71590100063c515901001cbf705901001cbd705901001e3f505901001e3d50590100465e7598c100465d7598c100469f7498c100469c7498c100065c5298c100069f4298c100065c5198c100069c4198c1001e5f5098c1001e5d5098c1001e9f4098c1001e9d4098c100147e7558c10004bf7458c1000cbc7458c100065f5358c100069c4358c100065e7558c100065d7558c100069f7458c100069c7458c100065c5258c100069f4258c100065c5158c100069c4158c1001e5f5058c1001e5d5058c1001e9f4058c1001e9d4058c1001ed71058c1001ed51058c100047f7654c100047d7654c101ee3e6454c100063d6454c100465e6354c100065d6354c10005747154c10044bf7690c10004bd7690c101e63e6590c100063d6590c100469e6390c100069d6390c1003e6f759881003e6c759881003eae749881003ead74988100066f53988100066d5398810006ae4398810006ac43988100066c5198810006ac419881001e6f509881001e6d509881001eaf409881001ead40988100047f75588100147c755881000cbe74588100066c5258810006af42588100066f75588100066c7558810006ae7458810006ad74588100066f53588100066d5358810006ae4358810006ac43588100066c5158810006ac415881001e6f505881001e6d505881001eaf405881001ead405881001ee7105881001ee5105881003c7f76948100047d76948101de3e64948100063d64948100065e63948100065d639481003e6e62948100066d6294810004bf7650810004bd76508101d63e65508100063d65508100069e63508100069d635081003eae6250810006ad6250810005b4715081006c7f76944100147d769441018e3e64944100063d64944100065e63944100065d63944100066e62944100066d6294410005797094410034bf769041000cbd76904101863e65904100063d65904100069e63904100069d6390410006ae6290410006ad6290410005b97090410004fb7644010007725144010
  | 1 => 0x4e10005747154e10044bf7690e10004bd7690e101e63e6590e100063d6590e100047f7558a100147c7558a1000cbe7458a1003c7f7694a100047d7694a101de3e6494a100063d6494a10004bf7650a10004bd7650a101d63e6550a100063d6550a10005b47150a100547d769461018e3e64946100063d649461004cbd76906101863e65906100063d65906100147e76d95100063c64d95100047d73d95100063c43d951003c7e72d95100063f42d95100147e71d95100147c71d95100063c41d95100547d70d95100063f40d951000cbe76d91100063f65d91100063c65d9110044be73d91100063f53d9110004bd72d91100063c52d911000cbe71d911000cbc71d91100063c51d911004cbd70d91100063f50d91100147c75d8d1000cbe74d8d10004bd74d8d100065f53d8d100069c43d8d10044de76d8d100065f65d8d100065c65d8d100069f64d8d100069c64d8d100065f75d8d100065c75d8d100069e74d8d100069d74d8d100065c52d8d100069f42d8d100065c51d8d100069c41d8d100065f50d8d100069f40d8d100047f7558d100147c7558d10004bf7458d1000cbc7458d10004ef7258d1003cec7258d10004de7618d100065f6518d100065c6518d100069f6418d100069c6418d100465e7518d100465d7518d100469f7418d100469c7418d100065c5218d100069f4218d10046d57118d100065c5118d100069c4118d100065f5018d100069f4018d100047e7654d100047c7654d100063f6454d101ee3c6454d100065f6354d100465c6354d10004be7690d10044bc7690d100063f6590d101e63c6590d100069f6390d100469c6390d10005b67190d100147e75d89100047d75d891000cbc74d89100066c52d8910006af42d891003cee76d89100066f65d89100066c65d8910006af64d8910006ac64d8910006cf63d8910006cc63d89100066e75d89100066d75d8910006af74d8910006ac74d89100066f53d89100066d53d8910006ae43d8910006ac43d89100066c51d8910006ac41d89100066f50d8910006af40d89100047f75589100147c7558910004bf745891000cbc7458910004df7358910044dc7358910004ee76189100066f65189100066c6518910006af6418910006ac6418910006cf6318910006cc631891003e6f751891003e6c751891003eae741891003ead74189100066f53189100066d5318910006ae4318910006ac431891003ee571189100066c5118910006ac41189100066f5018910006af40189100047e769491003c7c76949100063f64949101de3c64949100065f63949100065c63949100066f629491003e6c6294910005767194910004be7650910004bc76509100063f65509101d63c65509100069f63509100069c6350910006af625091003eac62509100647e76945100063f649451018e3
  | 2 => 0x1e5d5058c2001e9f4058c2001e9d4058c2001ecf2058c2001ecd2058c200047f7654c200047d7654c201ee3e6454c200063d6454c200465e6354c200065d6354c2003d6c7254c20044bf7690c20004bd7690c201e63e6590c200063d6590c200469e6390c200069d6390c200147c759842000cbc7498420006745198420006b44198420006777598420006747598420006b77498420006b47498420006775398420006755398420006b64398420006b4439842003e76529842003e74529842003eb7429842003eb5429842001e77509842001e75509842001eb7409842001eb540984200047f75584200147c7558420004bf745842000cbc7458420006745158420006b4415842003ee42158420006777558420006747558420006b77458420006b47458420006775358420006755358420006b64358420006b4435842003e76525842003e74525842003eb7425842003eb5425842001e77505842001e75505842001eb7405842001eb5405842001ee7205842001ee520584200047f76944200047d769442018e3e64944200063d64944200065e63944200065d6394420006766194420006756194420004bf7690420004bd76904201863e65904200063d65904200069e63904200069d6390420006b66190420006b56190420004ed7688420006cd6388420006e561884200063c64d97100047d73d97100063c43d971003c7e72d97100063f42d97100067671d97100063c41d97100067970d97100063f40d97100063f65d93100063c65d9310044be73d93100063f53d9310004bd72d93100063c52d9310006b671d93100063c51d9310006b970d93100063f50d93100147c75d8f1000cbe74d8f10004bd74d8f100047f7558f100147c7558f10004bf7458f1000cbc7458f100047e7654f100047c7654f100063f6454f101ee3c6454f10004be7690f10044bc7690f100063f6590f101e63c6590f10005b67190f100147e75d8b100047d75d8b1000cbc74d8b100047f7558b100147c7558b10004bf7458b1000cbc7458b100047e7694b1003c7c7694b100063f6494b101de3c6494b10005767194b10004be7650b10004bc7650b100063f6550b101d63c6550b100063f649471018e3c64947100057970947100063f65907101863c6590710005b9709071001cf5768c710046d4634c71001cf576887100147c76543100063f64543100fe3c645431000574715431000cbc76503100063f65503100f63c6550310005b471503100047f73596100063c435961003c7c72596100063f42596100063c415961001e3f405961001e3d4059610044bc73592100063f5359210004bf72592100063c52592100063c515921001e3f505921001e3d50592100147e7558e10004bf7458e1000cbc7458e100047f7654e100047d7654e101ee3e6454e100063d645
  | 3 => 0xd6454e2003d6c7254e20044bf7690e20004bd7690e201e63e6590e200063d6590e2000cbf7650a201d63e6550a200063d6550a2003f2c5250a20005bb7050a200147c759862000cbc74986200047f75586200147c7558620004bf745862000cbc7458620004df7358620044dc73586200047f76946200047d769462018e3e64946200063d6494620004bf7690620004bd76906201863e65906200063d65906200147e76d95200063e64d95200063e74d95200063d74d95200047d73d95200063c43d952003c7e72d952003c7c72d95200063f42d95200047e71d95200063c41d952003c7d70d95200063f40d95200063f65591200063c65591200059c7359120005b471591200063f75591200063c75591200069f7359120044bc73591200069c73591200449c73591200063f5359120094bf7259120006af72591201f63e52591201f63c5259120006b77159120004bc7159120006b47159120004b471591200063c51591200a4bf7059120006bb70591200063f50591200147c75d8d2000cbe74d8d20004bd74d8d200069c43d8d200047f7558d200147c7558d20004bf7458d2000cbc7458d20004f77158d20004f47158d200047e7654d200047c7654d201ee3e6454d200063d6454d20044bf7690d20004bd7690d200063f6590d201e63c6590d20005ad7290d200063f65509201d63c6550920005bb7050920006ad648c92001cec764c920006ad644c9200074d534c9200147e75d85200047d75d852000cbe74d8520004bd74d8520006b441d85200147c751852000cbe7418520004bd7418520006b441185200047e76945200047c769452018e3e64945200063d649452003d6e7294520004bd76905200063f65905201863c6590520005ad7290520004ee76c8520005cd73c852001cec764852003c7c76541200fe3e64541200063d645412003d6c725412001f68205412000cbf7650120084bd76501200063f65501200f63c6550120005af72501200047f73594200063c435942003c7e725942003c7c725942003e3f425942003e3d42594200047c71594200063c415942001e3f405942001e3d4059420044bc73590200063f535902003cbf725902003cbd725902003e3e525902003e3c5259020004bc71590200063c515902001e3f505902001e3d50590200465e7598c200465d7598c200469f7498c200469c7498c2003e5e5298c2003e5c5298c2003e9f4298c2003e9d4298c200065c5198c200069c4198c2001e5f5098c2001e5d5098c2001e9f4098c2001e9d4098c200147e7558c20004bf7458c2000cbc7458c200065f5358c200069c4358c200065e7558c200065d7558c200069f7458c200069c7458c2003e5e5258c2003e5c5258c2003e9f4258c2003e9d4258c200065c5158c200069c4158c2003ecc2158c2001e5f5058c20
  | 4 => 0x88300066c5258830006af42588300066f75588300066c7558830006ae7458830006ad74588300466f53588300466d5358830046ae4358830046ac43588300066c5158830006ac4158830046cc315883001e6f505883001e6d505883001eaf405883001ead405883001ecf305883001ecd305883003c7f76948300047d76948301de3e64948300063d649483003e6e62948300066d6294830004bf7650830004bd76508301d63e65508300063d65508300459c735083003eae6250830006ad62508300147c759843000cbc7498430006745198430006b44198430006777598430006747598430006b77498430006b47498430046775398430046755398430046b64398430046b44398430006765298430006745298430006b74298430006b5429843001e77509843001e75509843001eb7409843001eb540984300047f75584300147c7558430004bf745843000cbc7458430006745158430006b44158430046d43158430006777558430006747558430006b77458430006b47458430046775358430046755358430046b64358430046b44358430006765258430006745258430006b74258430006b5425843001e77505843001e75505843001eb7405843001eb5405843001ed7305843001ed530584300047f76944300047d769443018e3e64944300063d64944300066e62944300066d6294430006766194430006756194430004bf7690430004bd76904301863e65904300063d6590430006ae6290430006ad6290430006b66190430006b56190430004dd768c430006cd628c430006d5618c4300063f75593200063c7559320044bc73593200063f535932003e3e525932003e3c525932003eae3259320004bc71593200063c51593200063f50593200047f7558f200147c7558f20004bf7458f2000cbc7458f2003c7e7654f2003c7c7654f201ee3e6454f200063d6454f200465e6354f200065d6354f20044bf7690f20004bd7690f202063f6590f202063c6590f20005ad7290f20006ad644cb200074d534cb200147e75987200047d759872000cbc749872001cee72987200047f75587200147c7558720004bf745872000cbc745872003c7e769472018e3e64947200063d649472003d6e7294720004bf7690720004bd76907201fe3f65907201fe3c6590720005ad729072003c7c76543200fe3e64543200063d645432003d6c725432001f6a205432000cbf76503201f63f65503201f63c6550320005af72503200047f73596200063c43596200063f42596200047c71596200063c415962001e3f405962001e3d4059620044bc73592200063f53592201f63e52592201f63c5259220004bc71592200063c515922001e3f505922001e3d50592200147e7558e20004bf7458e2000cbc7458e200047f7654e200047d7654e201ee3e6454e200063
  | 5 => 0x20e3c435963003c7c72596300063f42596300047c71596300063c415963001e3f405963001e3d40596300063f5359230004bf72592300063c5259230004bc71592300063c515923001e3f505923001e3d50592300147f7654e301ee3e6454e300063d6454e300471c4354e300057b7054e300475b3054e300047f7558a300147c7558a3000cbe7458a3003c7f7694a300047d7694a301de3e6494a300063d6494a30004bf7650a30004bd7650a301d63e6550a300063d6550a300459c7350a300147c759863000cbc74986300047f75586300147c7558630004bf745863000cbc7458630004ef725863003cec72586300047f76946300047d769463018e3e64946300063d6494630004bf7690630004bd76906301863e65906300063d65906300063c64595300056c72595300057471595300063f74595300063c74595300dc7f73595300065f735953020e3e435953020e3c43595300066f725953003c7c72595300066c725953003c6c72595300063f42595300067771595300047c71595300067471595300047471595300063c41595300ec7f70595300067b70595300063f405953000cbe76d91300063e65d91300063d65d91300063e75d91300063d75d9130044be73d9130044bc73d91300063f53d9130004bd72d91300063c52d9130004be71d91300063c51d9130044bd70d91300063f50d91300063f6454d301ee3c6454d300057b7054d300147e75d89300047d75d893000cbc74d89300066c52d89300047d76949300063f64949301de3c64949300055d7394930004be7650930004bc76509301d63e65509300063d65509300065d65cc93001cdc764c9300065d654c9300078d424c9300147e75d85300047d75d853000cbe74d8530004bd74d85300067451d85300147e75185300047d751853000cbc74185300067451185300047d76945300063f649453018e3c64945300055d7394530004be7690530004bc76905301863e65905300063d65905300459e7390530004de76cc530005cd72cc53001cdc764c530006d4614c5300147f76541300cc7d76541300063f64541300fe3c64541300055f7354130044bc76501300f63e65501300063d65501300459c73501300447f73594300447d73594300463e43594300463c435943003c7c72594300063f42594300047c71594300063c415943001e3f405943001e3d4059430044be7359030044bc73590300463f53590300463d5359030004bf72590300063c5259030004bc71590300063c515903001e3f505903001e3d505903003e6f759883003e6c759883003eae749883003ead74988300466f53988300466d5398830046ae4398830046ac43988300066c5198830006ac419883001e6f509883001e6d509883001eaf409883001ead40988300047f75588300147c755883000cbe745
  | 6 => 0xc75589400059f73589400059c7358940005b77158940005b471589400a5bb7058940006ad62189401f63e76949401f63d76949400053d739494021e3c63949401f53e72949401f72e72949401f63f62949400053e71949400053d709494022e3f60949401df3b6094940044bc76cc9400f53e75cc9400053d75cc9400071d53cc940004be768c940004bd768c9401f53f758c9401f53c758c9400469c638c940004bf764c940004bc764c9400053f754c9400f53c754c9400071d534c940004be760c940004bd760c9400f53e750c9400053d750c9400469c630c9400f53e75d85400053d75d854004db970985400053f75585400f53c75585400059f73585400059c7358540005af7258540005ac7258540035bb7058540044be73185400063f53185400063d5318540004bd72185400063e52185400063c52185400063c51185400063f50185400053d73945402163c63945401f53e72945400063f62945402253e71945400f73671945400063c61945400053d709454018e3f609454018f3b6094540004be76cc540004bd76cc5400f53e75cc5400053d75cc540005ae72cc540005ad72cc540004be768c540004bd768c5400053f758c5400f53c758c5400469c638c540004bf764c540004bc764c5400053f754c5400f53c754c540044bc760c5400f53e750c5400053d750c5400469c630c54000795310c54001dba700c540005b9700c540004be76c8540004bd76c85400f53e75c85400053d75c85400059e73c85400059d73c8540006b461c8540004bc76885400f53e75885400053d7588540006af6288540004bf7648540004bc76485400053f75485400f53c7548540004be7608540004bd76085401f53f75085401f53c7508540006af6208540006b461085400053f735414020e3c63541401f53c72541400063f62541400053c71541400063c615414001d3f70541400f73b705414001e3f60541400ff3b60541400063f74597300063c74597300463e43597300463c435973003c7c72597300063f42597300465f32597300047c71597300063c41597300063f40597300047f7558b300147c7558b30004bf7458b3000cbc7458b3003c7f7694b300047d7694b3021e3f6494b3021e3c6494b300055d7394b30044bc7650b301d63e6550b300063d6550b3003eae6250b30006ad6250b300065d654cb300078d424cb300147c759873000cbe7498730004bd749873001cde73987300047f75587300147c7558730004bf745873000cbc74587300047f76947300047d76947302163f64947302163c64947300055d7394730044be76907301863e65907300063d65907300459e73907300147f765433020e3f645433020e3c64543300055f735433001f5a3054330044bc76503300f63e65503300063d65503300459c735033020e3e4359630
  | 7 => 0x8d500053f7458d500fd3c7458d500056f7258d500056c7258d50005777158d50005747158d500ed7b7058d5020e3e7690d5020e3d7690d5020d3e7390d5020f1e7390d5020e3f6390d500053d7290d502063c6290d500053e7190d500053d7090d502463f6090d501e73b6090d500fd3e74989500053d74989500066f629895008d7970989500ad7b70589500fd3e74189500053d74189500055e73189500055d731895003e6e62189500063f76509500063c765095020d3c73509500063f63509500fd3f72509500ff2f72509500072f625095003e3e625095003e3c62509500072c625095003e2c62509500053c71509500053f705095023e3f60509501d73b60509500047e76cc9500047d76cc95020d3f74cc95020d3c74cc95003e6c62cc95003c7c768c9500fd3e748c9500053d748c9500072d428c9500047f764c9500047c764c9500053f744c9500fd3c744c9500072d424c9500047e760c9500047d760c9500fd3e740c9500053d740c95003e6c620c9500fd3e74d85500053d74d85500067761985500557970985500053f74585500fd3c74585500055f73585500055c73585500056f72585500056c725855006d7b70585500047d73185500063e43185500063c431855003c7e72185500063f42185500063d42185500063c41185500063f401855020d3e73905500063f63905500053d72905501fe3c62905500fd3e71905500ff3671905500063c61905500053d709055023e3f60905501873b60905500047e76cc5500047d76cc5500fd3e74cc5500053d74cc5500056e72cc5500056d72cc5500067461cc5500047c768c5500fd3e748c5500053d748c5500065f638c5500047f764c5500047c764c5500053f744c5500fd3c744c5500047e760c5500047d760c55020d3f740c55020d3c740c5500065f630c55000674610c55000755310c5500047e76c85500047d76c85500fd3e74c85500053d74c85500055e73c85500055d73c85500047e76885500047d76885500053f74885500fd3c748855003e6c62885500047f76485500047c76485500053f74485500fd3c744855003c7c76085500fd3e74085500053d740855003e6c620855001d7a70085500057970085500f53e7598d400053d7598d400c5b97098d400e5bb7058d400f53e7518d400053d7518d400469e6318d40005ae7218d40005ad7218d400063f7654d400063c7654d402353f7354d400f71f7354d400071f6354d400463e6354d400463c6354d400071c6354d400461c6354d401f53c7254d400053c7154d400053f7054d401ee3f6054d401ef3b6054d400f53e75d89400053d75d89400063e75d89400063d75d8940044be73d89400063f53d89400063d53d89401f63c52d8940004be71d89400063c51d89400063f50d8940085b970989400053f75589400f53
  | 8 => 0x63c74596210047f73596210063c43596210063f425962103c7c71596210063c41596210047f70596210063f40596210063e65d92210063d65d92210059e73d92210063e75d92210063d75d9221044be73d92210069e73d92210449e73d92210069d73d92210063f53d9221006ad72d92211fe3e52d92211fe3c52d9221006b671d92210063c51d9221004bd70d92210063f50d92210147e75d8e210047d75d8e2100cbe74d8e21004bd74d8e210147e7558e21004bf7458e2100cbc7458e210069c4358e210047f7654e210047d7654e210063f6454e211ee3c6454e21005747154e21004be7690e21044bc7690e211e63e6590e210063d6590e21005ad7290e211d63e6550a210063d6550a21005b47150a21006af648ca21044ef764ca21006af644ca210074d534ca2103c7d76946210063f649462118e3c649462103d6e729462100cbe76906211863e65906210063d6590621005ad7290621005cd73c86210076651c86210147e7558221004bf745822100cbc74582210147e76d95210063c64d95210047d73d95210063c43d95210063f42d95210063c41d95210047d70d95210063f40d952100cbe76d91210063f65d91210063c65d9121044be73d91210063f53d912111cbd72d91211fe3e52d91211fe3c52d91210063c51d9121004bd70d91210063f50d91210147c75d8d2100cbe74d8d21004bd74d8d210047f7558d210147c7558d21004bf7458d2100cbc7458d21004fb7058d2101cf87058d210047e7654d210047c7654d210063f6454d211ee3c6454d2103d6c7254d21005747154d21004be7690d21044bc7690d210063f6590d211e63c6590d2100cbc76509210063f65509211d63c655092103f2c5250921005b4715092113c7e76945210063f649452118e3c6494521134be76905210063f65905211863c65905210147c75d812100cbc74d81210063f75590210063c7559021044bc73590210063f535902103e3e525902103e3c525902103eae3259021104bc71590210063c5159021004bf70590210063f50590210047f7558c210147c7558c21004bf7458c2100cbc7458c2103c7e7654c2103c7c7654c211ee3e6454c210063d6454c210465e6354c210065d6354c21044bf7690c21004bd7690c212063f6590c212063c6590c21005ad7290c21005b67190c21006ad644c8210074d534c82103c7e769442103c7c769442118e3e64944210063d649442103d6e7294421114bf769042100cbd76904211fe3f65904211fe3c6590421005ad7290421004ef764842100766514842124fa441484210047f75580210147c755802100cbe74580210fd3e74d8d500053d74d8d500063e74d8d500063d74d8d5020e3c43d8d5003c7e72d8d500063f42d8d500047e71d8d500063c41d8d500063f40d8d500065f6398d500cd79709
  | 9 => 0xd72d91310063c52d91310063c51d9131004bd70d91310063f50d91310147c7654d310063f6454d311ee3c6454d310471c4354d31005747154d31047543154d310147e75d89310047d75d893100cbc74d89310047e769493103c7c76949310063f64949311de3c6494931004be7650931004bc76509310063f65509311d63c65509310459c7350931005b4715093117c7e76945310063f649453118e3c6494531174be76905310063f65905311863c6590531045d6718c5310147c75d813100cbc74d81310063f74594310063c74594310463e43594310463c435943103c7c72594310063f42594310465f325943114c7c71594310063c41594310047f70594310063f40594310047f75588310147c7558831004bf745883100cbc745883103c7f76948310047d769483121e3f649483121e3c64948310055d7394831005767194831044bc76508311d63e65508310063d655083103eae6250831006ad62508310065d654c8310078d424c83116c7f76944310147d76944312163f64944312163c64944310055d7394431044be7690431044bc76904311863e65904310063d65904310459e7390431004df764c43100756514c43125f54514c43100796414c43125794414c431045d7764c431006d7764c43100757754c43125f54754c43104756654c43104755654c43100797744c43125794744c43104797644c43104794644c43100756524c43125f54524c43125797424c43100795424c43125f57504c43125797404c4310147e7558031004bf745803100cbc7458031006d531580310047f73597210063c435972103c7c725972103e3f425972103e3d42597210063c41597210047f70597210063f4059721044bc73593210063f535932103e3e525932103e3c52593210063c5159321004bf70593210063f50593210465e7598f210465d7598f210469f7498f210469c7498f2103e5e5298f2103e5c5298f2103e9f4298f2103e9d4298f210065c5198f210069c4198f210065f5098f210069f4098f210147e7558f21004bf7458f2100cbc7458f210065f5358f210069c4358f210065e7558f210065d7558f210069f7458f210069c7458f2103e5e5258f2103e5c5258f2103e9f4258f2103e9d4258f210065c5158f210069c4158f2103ecc2158f210065f5058f210069f4058f2103ecf2058f210047f7654f210047d7654f211ee3e6454f210063d6454f210465e6354f210065d6354f2103d6c7254f21044bf7690f21004bd7690f211e63e6590f210063d6590f210469e6390f210069d6390f21005b67190f211247d769472118e3e64947210063d64947210065e63947210065d639472111cbd76907211863e65907210063d65907210069e63907210069d63907210147e755832100cbe74583210147f76596210063c64596210063f7459621
  | 10 => 0x464118e3e619464118f3661946410053d7094641025b671d82411853e75982410053d7598241044bc73582410063f53582410063d5358241004bf72582410063e52582410063c52582410063e51582410063c51582410063f50582411853e75182410053d75182410059e73182410059d7318241005ae7218241005ad7218241035b671182410463e43597310463c435973103c7c72597310063f42597310063c41597310047f70597310063f4059731044bc73593310463f53593310463d5359331004bf72593310063c52593310063c5159331004bf70593310063f505933103e6f7598b3103e6c7598b3103eae7498b3103ead7498b310466f5398b310466d5398b31046ae4398b31046ac4398b310066c5198b31006ac4198b310066f5098b31006af4098b310047f7558b310147c7558b3100cbe7458b310066c5258b31006af4258b310066f7558b310066c7558b31006ae7458b31006ad7458b310466f5358b310466d5358b31046ae4358b31046ac4358b310066c5158b31006ac4158b31046cc3158b310066f5058b31006af4058b31046cf3058b3103c7f7694b310047d7694b311de3e6494b310063d6494b3103e6e6294b310066d6294b31005767194b31004bf7650b31004bd7650b311d63e6550b310063d6550b310459c7350b3103eae6250b31006ad6250b311647d769473118e3e64947310063d64947310066e62947310066d629473115cbd76907311863e65907310063d6590731006ae6290731006ad62907310147e755833100cbe74583310063e64d96310056e72d96310063e74d96310063d74d96310065d73d96312163e43d96312163c43d963103c7e72d96310066e72d963103c6e72d96310066d72d96310063f42d96310067671d96310063c41d96310047d70d96310063f40d963100cbf76592310063f65592310063c65592310063f75592310063c75592310063f5359231004bf72592310063c5259231044bc71592310063c5159231004bf70592310063f50592311ee3e6454e310063d6454e31005747154e31047573154e310047f7558a310147c7558a3100cbe7458a310066c5258a310047e7694a311de3e6494a310063d6494a310055d7394a31004bf7650a31004bd7650a310063f6550a311d63c6550a31005b47150a310065f65cca3103cdf764ca310065f654ca310078d424ca310147e769463118e3e64946310063d64946310055d7394631044bd76906310063f65906311863c65906310459e7390631005cd72cc6310075651cc6310047f75582310147c755823100cbe74582310147e76d95310063c64d95311647d73d95312163e43d95312163c43d953103c7e72d95310063f42d95310063c41d95310047d70d95310063f40d953100cbe76d91310063f65d91310063c65d91310063f53d9131004b
  | 11 => 0x4bf745843200cbc74584320147e755803200cbe745803218d3e74d8e510053d74d8e510056e72d8e510056d72d8e5114d7671d8e510053f7458e5118d3c7458e510063f7458e510063c7458e512163c4358e5103c7c7258e510063f4258e510063c4158e510047f7058e510063f4058e510065d6318e5116d767118e512163e7690e512163d7690e512153e7390e512171e7390e512163d6390e510053d7290e512063e6290e510053e7190e5126e3e6190e511e7366190e510053d7090e5110d7671d8a5118d3e7498a510053d7498a510055e7398a510055d7398a5118d3e7418a510053d7418a5103e6e6218a510066d6218a5112d767118a510063f7650a510063c7650a512153c7350a510063d6350a5118d3f7250a5118f2f7250a5103e3e6250a510072e6250a5103e2e6250a510072d6250a5103e3c6250a510053c7150a512263e6150a511d7366150a510053f7050a510047e76cca510047d76cca512153f74cca512153c74cca5103e6e62cca5103c7f768ca5118d3e748ca510053d748ca510072d428ca510047f764ca510047c764ca510053f744ca5118d3c744ca510072d424ca510047e760ca510047d760ca5118d3e740ca510053d740ca5103e6e620ca5102d7671d825118d3e74982510053d74982510047f73582510063e43582510063c435825103c7c72582510063f42582510063d42582510063c41582510063f405825118d3e74182510053d74182510055e73182510055d73182510056e72182510056d721825106d767118251145b671d8e411853e7598e410053d7598e41005ae7298e41005ad7298e411853e7518e410053d7518e410469e6318e41155b67118e410063f7654e410063c7654e412353f7354e411871f7354e410463e6354e410071e6354e410461e6354e410071d6354e410463c6354e411fd3c7254e410053c7154e411ee3e6154e411ef366154e410053f7054e411853e75d8a410053d75d8a410059e73d8a410059d73d8a41105b671d8a41006af6298a410053f7558a411853c7558a410063f7558a410063c7558a41044bc7358a410063f5358a410063d5358a411fe3c5258a410063c5158a41004bf7058a410063f5058a41115b67118a411fe3e7694a411fe3d7694a410053d7394a4121e3e6394a411fd3e7294a411ff2e7294a411fe3d6294a410053e7194a412663e6194a411df366194a410053d7094a41044bf76cca411853e75cca410053d75cca410071d53cca41004be768ca41004bd768ca411fd3f758ca411fd3c758ca410469e638ca41004bf764ca41004bc764ca410053f754ca411853c754ca410071d534ca41004be760ca41004bd760ca411853e750ca410053d750ca410469e630ca410053d73946412163e63946411fd3e72946410063d62946412253e719464118736719
  | 12 => 0x441987320047f75587320147c7558732004bf745873200cbc745873203cdc7358732006b44158732046d431587320147e7558332004bf745833200cbc74583320063f75592320063c75592320063f535923203e3e525923203e3c5259232004bc71592320063c5159232004bf70592320063f505923203c7c7654e321ee3e6454e320063d6454e321ae5d6354e3203d6c7254e320474f3254e3203daf7650a32196af7650a320072f7550a322872c7550a3203f2f6550a3203f2c6550a32045ae7350a32045ac7350a321a6ad6350a322872f5350a320072d5350a32005ac7150a322872c5150a32005af7050a322872f5050a320147e75986320047d759863200cbc74986320067451986320047f75586320147c7558632004bf745863200cbc745863203cec725863200674515863203ee421586320047f75582320147c755823200cbe74582320147e76d95320063c64d953203c7d73d953221e3e43d953221e3c43d95320063f42d95320047e71d95320063c41d95320047d70d95320063f40d953200cbe76d91320063f65d91320063c65d91320063f53d9132044bd72d91322063e52d91322063c52d9132004be71d91320063c51d9132004bd70d91320063f50d913203c7c7654d320063f6454d321ee3c6454d320471e4354d320471c4354d3203d6c7254d320474c3254d320165f7654d3203d5c7654d320165c7654d3203c5c7654d320071f7454d3227f1c7454d320071f6454d3227f1c6454d320074f7254d3203d5e7254d3203d5c7254d320074c7254d320465f6254d320474f6254d3227f1f4254d3227f4e4254d3227f4d4254d320055c7154d3227f1c4154d320055f7054d3227f1f4054d32044bc76509320063f65509321d63c65509320459c73509320071d535093203f2e525093203f2c525093200eaf7650932045ac765093200eac7650932044ac76509320072f75509322772c75509320072f65509322772c65509320078f7350932045ae7350932045ac73509320078c73509320458c735093203eaf635093203f8f63509322772f53509322778e53509320072d53509322778d53509320070d5350932005ac71509322772c5150932005af70509322772f50509320147e75d85320047d75d853200cbe74d8532004bd74d85320147c751853200cbc74185320147c75d813200cbc74d81320463e43594320463c435943203c7e725943203c7c725943203e3f425943203e3d425943203e5f325943203e5d32594320047c71594320063c41594320047f70594320063f4059432044be7359032044bc73590320463f53590320463d535903203e3e525903203e3c525903203eae3259032046ad3259032004bc71590320063c5159032004bf70590320063f50590320147c759843200cbc74984320047f75584320147c7558432
  | 13 => 0x8e5203e5c3258e520047c7158e520063c4158e520047f7058e520063f4058e522053f7690e522063e7690e522053d7690e5221e3d7690e520043d7690e5229d3e7390e5221f1e7390e522063f6390e5221e3d6390e522053f7290e522053d7290e522063e6290e522072e6290e520053e7190e520053d7090e520063f74986520063c74986520047d73986520063e43986520063c439865203c7e729865203e3f429865203e3d429865203e7671986520063c419865203e77219865203e7421986520047d70986520063f40986520063e74582520063d74582520047f73582520063e43582520063c435825203c7c725825203e3f425825203e3d42582520047c71582520063c415825203e7b70582520063f405825203e7b205825203e7820582522953e76d95421d63e76d95420053d73d954203d3e72d954203d3c72d95421de3f62d95421df2f62d95420053e71d95420053d70d95421d53c75d8d421d53e7598d420053d7598d420063f6598d420063c6598d421a5ad7298d42005b67198d42005b57198d420053f7558d421d53c7558d421c5af7258d421d53e7518d420053d7518d420063f6518d420063c6518d420469e6318d420063f7654d420053e7654d420053c7654d420063c7654d420043c7654d422353f7354d421d71f7354d420463e6354d420463c6354d4203d3e7254d4203d3c7254d421ee3f6254d421ef2f6254d420053c7154d420053f7054d421d53e75d85420053d75d85421d53e75985420053d75985420063f65985420063c65985420059e73985420059d739854211dad72985420053f75585421d53c7558542115af72585421d53c75185420063f65185420063c65185420063f75185420063c7518542044be73185420063f53185420063d53185422663e52185422663c52185420063c5118542004bd70185420063f50185421d53c75d81420063f65d81420063c65d81420063f75d81420063c75d8142044be73d81420063f53d81420063d53d814222e3e52d814222e3c52d8142004be71d81420063c51d81420063f50d81421d53e75981420053d7598142085ad72981420053f75581421d53c75581420063f65581420063c65581420059f73581420059c7358142095af7258142005b77158142005b471581421d53e75181420053d75181420063f74597320063c74597320463e43597320463c43597320063f42597320047c71597320063c41597320047f70597320063f40597320455f7654f3219e5f7654f320071f7454f3228f1c7454f320471f6454f320471c6454f3203d5e7254f3203d5c7254f3228f1f4254f320055c7154f3228f1c4154f320055f7054f3228f1f4054f32044bc7650b321d63e6550b320063d6550b320459c7350b320071d5350b320147c759873200cbe7498732004bd7498732006b
  | 14 => 0x500100100100801600300e00000000000100000200100d00e00100100000300202000700100200800000e00100a00700300000100f00200200000100000300000200400300a00000100000001700c00000000000500200000401000301000e00800400000200300000100000700600000100400000300100f00d00000500300100000100000400600700000000000700100200d00c00000000200000800000400c00000600200e01300000300000100a00201a00500202000000000600a00200300000200100000000200100300300500400100700000501f00000100000000300e00200400400600200700200301a00100000500000000000000300000300900600001100000700100801100000000200200a01000b0000000000000040020020010090021ed3e76d91531ee3e76d91530453e73d91530453c73d91531e63f63d91531e71f63d91530053d72d91530053e71d91530053d70d91531ed3c74d89531ed3e74989530053d74989530063f64989530063c64989531ad5d73989530057671989530057571989530053f74589531ed3c74589531bd5f73589531ed3e74189530053d74189530063f64189530063c641895303e6e62189531ed3e74d85530053d74d85531ed3e74985530053d74985530063f64985530063c64985531655d73985530056e72985530056d72985530053f74585531ed3c745855316d5f73585531ed3c74185530063f64185530063c64185530063f74185530063c741855326e3e431855326e3c431855303c7e72185530063f42185530063c41185530047d70185530063f40185531ed3c74d81530063f64d81530063c64d81530063f74d81530063c74d81532463e43d81532463c43d815303c7e72d81530063f42d81530047e71d81530063c41d81530063f40d81531ed3e74981530053d74981530cd5d73981530053f74581531ed3c74581530063f64581530063c64581530dd5f73581530056f72581530056c72581530057771581530057471581531ed3e74181530053d74181530063f7558a430063c7558a43044bc7358a430463f5358a430463d5358a43046af7258a432063c5258a43046af3258a43046ac3258a43004bc7158a430063c5158a43004bf7058a430063f5058a430063f75986430063c7598643044be73986430463f53986430463d5398643004bd72986430063c5298643046b671986430063c5198643046b73198643046b43198643004bd70986430063f50986430063e75582430063d7558243044bc73582430463f53582430463d5358243004bf72582430063c5258243004bc71582430063c5158243046bb70582430063f5058243046bb3058243046b830582430063f7458e520063c7458e5203e5f7358e5221e3c4358e5203c7c7258e5203e3f4258e5203e3d4258e5203e5e325
  | 15 => 0x306cc5b035836200007da8bd1979e380008092248000b0235700000000000003e8914c0002f842d17982d09a940f0f347928934430000d5200000019e406600000d00000100600000400500100500000300200800000001300000300200300000000000700000000000100500000400600500b00c00200800000000000000300000000200000001500b00200000400000000400000300500a00000101000600400a00000100700900a00200000000000000000200700000100100a02d00600201100300200d00800100400200c00900200000600300900700100c00100600000600000200102f00101400f00000200200100200400000000900000000100000400f00000900100200200100200000f01d00100700000000100100100e00100000000200400000f00300200000000100100300401400700800600101400400100000000000a00200700700a01e00000001400100000000000300700400000100000000101700600100000100000800300200e00300001500400000000100500e00300000700000100200400e00000b00000000f00000000000701800100600b00100e00000200000100300d00f00100100500000f00000400000100000600500100000000900a00700400000600100100000000400100000000000001000100a00100600600000500200000800200a00600000000b00000000200400600e00d00000003600500100000000500100100500900600000100800100000300000000100200000100800c00400600000400200700200101000001000500200700000102a00000200100100f00a00001000200000100100100600c00000301000300203800001800600000800000700000800300e00300000000100000200001100000000100000200000000001000000000200a00000100700000f00200300200200000200500000201f00e00700800000100000700200200000100000000000100100000100000000700100301c00500100100100200200400400000000b00300100600a00000300100000000000500000000c00700500100900000500001300200001300000700100000000400400200000000000500200400600100b00300d00b00100000300000600000101302000000200000a00000000100200401b00000201500200200000c00201400400500000100600400000100000400d00900500002f00900001000500200200400400100200400100800600000000001800100c00000900a00d00100c00900100000b00100100500500300900100400800000100000b00400100700300600000200600600002100500000001c00000000000800000c00400400200000100900500000702b00200300200200200200f00300100400400100201100700600000e00000600000000001101200703401000100000d000000
  | 16 => 0x982a2439272800096e12b01f929a05b1009da4d2e91b0001df4d1a3f6160215cc645a1006000000014a000000064000032600000000450fd00000005110b89c80f941cb44a000013434a3e080007d0468345800131466c0000000000748000258c8a064a1ba00013463644908000d04897000008522000000000005f431236c95d06a03cc04e9adc4185d61cd800000027f000000108800036399680009990000750e446d62cb80000004083470e9d29800033f9f20db624802ba680e422d400021949269be293913cafa3f23518dd43ec6cb0000ca92c80e320a234ca0200045180010f896c2a719746362701010c0c0002143b58cec23267a2e59e6055033935f19f4ea44f4262800025241500000000000000001c30df60b142880000008f12132438a8a1384cd9f903320cb14d9cfc8446d20e1a6c02f28c315b9c003c27310bc214c78e6a20b596540004fb1c089400006a849397ac00036547e0e3871a7b5000060400052614390940009560001870e6e4bb0000e60c0200041689e80000001b107dc00069b30f02940001fd11b0cb061429c0cb86900008640000000000000000000003800000001484640392cb0ef40007b92f409300002200001c6c5e00000c98000f6e00000022bca9215e0eb1484c8400001f8000952000000000000000000000000008b72e0a52520664d36c00000000003ee836c0000000001718be444715800108d400042f0000b347a500005307c211c43508289b63b3479828035002d1ed20e473283125816f400018232888f400000012a80000000000041bb92302812c318fc0a05a344aa650afe37b3b403dd26c98f0ce0ab535a0ad08704751d80f5347a6153741282bc994c0d68983ae035cb3689e33c02e80004a00a7800021200000003b40566953809e441520fe00016ec76c4be00019c468600000000004c84030000da8cfc96f00000012c0189379054400e0000a01ed863400000008c400050c3d9077c00000000000000000001be8000e585b70000a9cd0e8dd1bc93cc4b40002520f7466a93a13410ed10a9701af014c8ea3f100000000004c0000050cb922b600011189c03e622ea2380005cd35806f8c0e00023188ad20805c00000007de19a01394e06a816d07098ccd2c57a2721df90c00003c91b1800000000000011686060679058fbe6ba109142400a3281ae020cd9200038c87c52d60930001b3906440f0439de86cc0003e28390ec68b01f992d07729651081ead25e5b40000000fee2fe294800049a0000001c18b3c71300000000005460ea800000009b1fb92bc74a090295a3e00005714af8000a0a3c000000002966a711c99903ce00026ea220c2022900000000000000000cfc0006ca000000098610d18e05d80000ee0ab86c421e2c4366a4d000034609613c87fc20309e0000ade0000c
  | 17 => 0xff8ac8af8000000096400028d0471c500001f30232240000139333000035800034600010d6744000183449e32b17b00000000ea061a11d2da35124a02d478448e192086d08206d15a0ddcfa01413c21a50200123153132c7f600d16f000132c0e6000000000000019e800000000036ba6a849c000000001894200032f94fc14283a0539ae03ae5fe03100000003d60ed9c90d3c000000000000095e4099b7896c0004d900001804e34c70000f608e2499a4352e848234e0000000180000000032829633a1378000282000000121600022a94904a862d1a5a49455270d140196435a22200000000000004200e8d0160000000000dca0000001d0400003200002f138e3a218f8fe40005d400026b0000000000068c00055e4701d68d682e24690bc869245644d8fd000000001a96f04f20f43b69df000000023e000107a0000451f38000000000000000000038b00c46800004d59288d6225b4629b7cf4600000027313342bc3d723700489c309a20cc6f09531d791b442e2953c5a584f920003b984988b673d2609b000009a81481be40008c224c8f0400000011c1ea000082500000000006d400719d91ae081000000045c219097982c0004c800014411966e44919064f267aa000000000054c4349ec4b8a4d50001e340006c10000afc0003440001ce8a4446b000245c00029a00021b40005f72929f540007740000000ff8000000000000058a0000b24b5400000015008c443f0001170f025a21f393304be0b938725440004f01f22210eaa0000000ef924810434186e4f043dc2b100001aa8c700016acb5c95436e00012902233a99a74d7e42d000141c71462700011680809052fc263092c2d600000006d25e91cb11b08cc000000084c7502fd0dd8c000004eb454800000000000003440000dc051a710d5400033980004e60000b99fc49dc92a191180c00000000001f0000000000000087079f3cf0c58e521e3000000000003e0000000000000309853413881a000000000093d2b08000dd806021186c127c00000000600004d700022341b40000000c200000af3cd9f94a1a00000002180008a42bf0000000000000000017a3480001a00eec000000000077e00030ba3b51160ac3f4a0480de21f47b8f7c2cc0000001e00b5a84900020fc4a41033b280000000002570000f9865e00000005a661f0001e80c7c000226000000055f23e992400082020700e890800010e00003e80823308000e5693b3879d643ca0000880914f8465700000000f29c6368800000000004596bca6c3d00000000000000000045d2f03842ab9c4514a54709019800c60c10d0a43c85e7fb3229f48e121a92cf8da03a60000000000000000000162470e000433121c0000001dc1b800ee73c08518385ea9752df027c0d48fd0000000a464cd1788f5c12a34f0001c0cd
  | 18 => 0x1ca00000000007184a528f16c0d6400012382dc00000000000009f200000012a8a080002f880000000000001204f8613f0000b1920253a048a4240000001e423840000004018c5441a0001c2a1f80000004df80000887851209994a9400036d054c854000462055042293f0002258f582f300024208de0004800f891a880e000000000000039da2b0ba60b30001a280000002bd841c00000000000000002a0496a32426200005a000000064b0000ad40007be253000006800017a1bd536a0004c000000007b40000c940002c7000000000058300025f882e572000213424254f2241ce436c20b1d31220882097274059087a0002e60558000000421800064e0002b1800000000000000008ee5413b722240002933798050000622000000129e00000001b0d8491600000b8b3895512883fcc0a7a63e7807d23800041480005586372b380000a200013c0000000000000000000084a00000000005a826108382262ea4db90acd7a000209800082249124d0000bec8fa03a8ab856240629e800000000022c80006de1a5075a2691aa4c635b026476e58e000000000000000000001d20000000000f383cf3f9259c0008b92d38f14000987000133901e1f019195087784d90e516cca64470269834ca6a3a10341d8932e8173060cb42fe66d2e81dbc0601110460af91826f038b8984c3a6561af80000004b500023a80be6620421fbc9148ce38f0c4475a3d911290841ac1e41038744e5400006687000007c63a6a2010ba3714c988fc89a8f044c8000f4247f2711d8414c4340a21ba4aa80000ee9c08e2a2bb18217c032272540e090ca14919144a2c8ff28da2ef80011140000000000a165f400000003369620001660a3e09e1719690dba41e3ed970c00064716680003548542f297a928a0002e4000105e7e342f865400000022f0000000000000000028c0000ad9ef11ac12d00000006c24730b480000ba0003628bac5d04854170000c6a00016d8c087b000025d085800000046c99c92b44781c900004ae2df000000000000000015acd9e00000011848c82b903e96c4b2449e0da04f47bc576099998d2224e70001dd51027560001cd84ea54b1d9020079c3170a814b10b62ed00020345c80002748a0c000000000000053a0000e08ccc0008a24c30d090560002b983e497e7903d2072100e9074ac9728e8644031c943891200024f80007c62994e41aec0000000000a2c0008714d09d7493082c13b13fca2c0000a719bd25622100000000000000fd8c3d0ea8b8055800040a0f223011b939a0002b410c80000000000b74002623384174431a8b32a180740006e31f82548b1a00026b08ec0000002620aa8f744ab00021651d00004a59a450f625c13b800000000048999a40000000e9000000074a3f9800072274f07d8000f2a76632a8000f066251
  | 19 => 0x630a840048cd1370db4e46389393a4c0ab000013618240aa8f535a894c0009b900000012444713eb80980001850000000bb000000006c80000000001fd433a41a3219be8b8041c000000000094e3040ce12e65314631ebc5467eb3b884ad0c28522879d44acc0000000000dd411f4e58d380000001f517b0c609b639f0160f9a02f000245400069f1761d2d2b04f72eea1e012c0000000000a888e9000000000018a3a60000b2600024308dcfe04cf441800114e02a00016d487c00028c9a180000003df80000008f93c4120048028f472227cb886f641388a132a00000000000000000f6923cdd600015e9d18c500c838f92a0c520000000000b6c53e0000000d860002f78ea400007b2c001d8cea1c400000000000003ef00007860000000000d0299e00002c80006200000000d2000028003500001a000009600000000de1a94b9c30b0000d800008370f614f122416e2b5010425c5db24e87f86602841c81114ce092e0002724c804070000000d0a00000022ec00000000000000005880000d6c000000000037400096918c87e400026039a86400966ab0002030aac6540001b200005202f98000c56000000000000078f0000eaca2a0cc0001d7d2d081b3a0132521492922c02d87062b31a900007547301628cf915c40938388d07580000c396e901074220918852807054aea0109cc0000702044dfa9a21e2092833023c1e886f49e22b801c22e8af004a00005850545c703d0ee8000000000010c0005340000cc883a942000000000042843780451940000001de52040000000f4c1be3c64121348fa697c17c9034dde2cc0779fd00e08ab1f60cf036e000000000097000028d162c0980003090a1860c00043e926c000000000255c00036b0000e780000000001a200004f843618e804a000000000037e000000000000000000000000001080000c1ce080480ef19102c044e4c08a7c0001e93089554f8024b2dc0000eb000f0c700000000000001fe098e00049c978400087300000010a00a82bb88cd33800000000003c00743ea03e0c1e1cf00010b8c0478a0d3046c0505b942722311780001fe80012b838f000000136200008f00000000000e6000000011405d800000065219d00000007860cf8000000000000063119848d13e23d800047a00000013680000001a4809c000000218c1c40000000000a2e0d02a818f4a046ae4d220c0d342ce00022a000006417793700008d809b818400000021387e00008e30f7104000031342780004545e2000270466e0000000000a6000020080002542153e221545ca00000008786aa00013185f49ea91f3ab87704d20920000e4c6b23d4107800000048c0000000000000000000000000045080000003530000000dfc1491cb85c000000000f000000072e0388000fc000000007388965902b81574
  | 20 => 0x423000000082600000000001051579028f3a99129d9d9011e55245a849c00085c00017d400055b11aa540d4825d4be9cbc38a000000000030839d1bd0000306112000206400000000008b09a089c27f0a50e1400000000000000000000f540000000001a982480000002244da092c37a0e085b20000001ff8a507e62728c300001ff3a295a4000454011a0d8c3456e000078934e4200b913a8bf687739423fd0f20472ed04f82aa3010211d80c4800011f000103e000327800000093c00009d000000000012547f4998131000128600a00001ccaca06738c08681bc6f12348a942ba03d4e0045873438b34c80001ce1580001c98d784d14cf95207281ea13f00008be00007800011d600034982f81440d9000000002a30540a919d26e84c3bd9fe92345993f713b4b4a2ca20580000004fa437000128800013585dc0000f643a0000852000000144892400000004ec5b42982c117080000000d700000000360000308f5a00046fa0740005034c18000efe8e70b50a783d00fc1be262c4740003cc8fe00001da1120000fc27da0001e1c45e76c2329d24dda00031c07400ac3450d79c690760122289698000000116a6991f6452000127000000031780000449661770000cd4000483199d0ac13200000005a236e23c9abc5f82ab1ca8000f7a2cb00014e45227c719b000000000047a0798fd01363ec80000000f334c000009e4a70000000000474000000051861800020608f667c4bd14b4baa7a93ec0df8886433014a1893108c00000b9c0000000000c750fe05a00000000005fd00012e42fc63130a141937a8be1a09e24e70754000008001200000013f0b4000020d88606300b8197251c000000000087400000000000000008872f0000131200000000000005d22fc9ccc0000002c280000003f521e0734760594000202848c56c00000000000001700000f185ee26c1938ef08b60520ca4bf417400000000000002c20000bda892000071800084200000010b000018a000048400006480003ea0000000000e6800033d8dcc4cc4182000d680007cb41e14b80004da369942000000047900000002002120c3507c8d13af264096e4ca19885147a464825e0e7cfd800000001350d0000000000000006601d93bcac800000000002de94603c00001880003171dc80000001f493d8c363e5000000000097f0000360a303802ce800000076a3150d584923861619ffce160001e5112800037f00002c104458f0a925dc2ce2e600012c911e9413208000dc49263a700003e47101fe24810200003050e7083e0002950000000000000031c00017c25e8000ab82ff28e1bf00001251908fb800000016a9ba10ce5a93f504606983cb4778000f2863b03700000fe8b112f022400076700004087689710a419a080a7d648ea08c8ae9b308590d41101eb
  | 21 => 0x145000075b2b68000bb2363438000041299d08d068800080514b90e8000000000062000000000000011040000000000d72000000144d2f25dc410800002c90c00000000001c22fe2114c581650001e9d38456033b90c424410c0a10a211b613032d9ddd0ec0ae13ea528bce01a3a806784da5cf251857c590098009a73800055330b06ac0d200000000004d48a013d80001d800000003f43f852f4000000ffa00019316fd02c388000004010a00028e800000042c16b80003b072d08a89bc9d855900000000000003b80000000000000175d376000221000000000000000000000000d38000000000000000003200000000002c600000009c400065c24589109a893141c0000b180ca1da90309625b216e000000037600000005484e119a0000000000202186400023047300002b87a22998e902029763f1019400000032807bc95a03c4991fb502800028d8ec4c8c08d00003a0d406d517ba0a07c063c4ada0051a002c1609e6909031e04a227400618f2ff9fd880443715d1bfc3740c51b9005c316265373964532436c0b603391bc8a631a05e8f708c83a380dd35c71200011d800055a10419b80a80000b11b84cb083505f9e5c0002e10000d9c00014700024e000000000001c80bc5e40000000f769843730b3caea6364b9177938a000113000000000000021e800000b24b80000008e5000000000013a00d800000000000005d40008bf1a685ed35e28a4b51a8400030931300013781c716106d53707e7259800126a6ac1b800006ba00000000004e48ee3ee14dd3046f70000d1d1fc0003d99e587b61c92d61c741a468924186482b280221c84d50686f82f18bec00030e0000810e3800000000000004df149201800000024810c05a00000ad24a08e46151428000e6405923f07652f63a02220ba400084b27e99acd083ae10318000928cf2c38c405a44ac0831acc51c0aa356889d154551000000000000000022b40003eb48f03c5228000302065886c54d1dd83e80001b81338000000000000000134a98d000000
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0xa4d8314b624c00107b0fb24a4980020f21d655093003d16412caa126000a3481595424c00f49904b2e64980029520565cc93003c2e43aca9926000a5481595324c0015190ca12649800383595424c9300052ac18a230a6041c1e73596414c07f45904b2c82980028d205659053020e0e39acaa02603ea2c82595404c00146902b2a80980028760c525903000526c18eab106008a8c835d1620c011918e6b1284180029560c52984300052ac18a4b086008a9483509610c00107d0fa9ac9900020f21d6454f2003c2e43ac6a9e4008a8c8359132c8001c1ac8a9a659001f0b9c964947200444f41eed20e4007c2c7259150c800145b0421acb100021d2057654e200450e41ac8a9c400083d8710f654800145b0421eca900020f61f42d95200041f43ecab22400083e87195644800183eca39ac8900030719473591200061bb28e2b224000c34651c5644801113d0fb9ac89000307dd473591200060e3a8e6b22400083e87d4d6448011838e7a9ac890003251cf71591200061bba8e2b224000c34751c5644800192ee638ac890003251cc715912000653b90e2b224000c37851c564480018690a38ac8900030dd4c71591200061b290e2b224000c34521c5644809b838e628ac8900030d1c451591202460e39ea0b224000c3471d41644800151b0421ec6900020f21d6454d200450e41ac8a9a4000a3481591534800107b0fb2c869014a0fa1f65509200454641ac91924000aa48159232480111590eb226490022a320d644c9200055240ac89924000e0d6454d324808543906b24a2900fb0b9c964945200051a40ac928a4041a1c83591504807d858e4b22a0900028d205645412000516c1086b284007a4c825d5630800151b043a2c61001e1b2097654c2003e26392c6a984000aa58210e610800f4c904a9ac210002a9608435842000516c1087b2e2000a1d8314b64c400f0dd053b2a78802287a0f6454f100444f41ceca162007a2e82d9542c400145b0421acb080028760c525921003c36412eca9c2008a1c83591538401113906bb2850801e8b2096550a1000516c1087b2a2000a1d8314b644400151b0421ec688002a360a74d8d100042f438a5b1a200085d871486344011928c738c86880029360c52d891000526c1cebb1220008ae8710f624400154d03218c4880022b61c43189100062a31ce32922007c64629c652440018a8c638aa08800329188715011000516c1086b282000a1d8314964040010bb0e294c608002a36084358c100052a40aeab182000a8d821d163040010bb0e292c608002a66004158c100043ac30e2a982000c55631c5530400115b0e21cc4080029360c525881000526c18eab102000aa4815d162040014c902a9ac4080022b61c435881000534c00a2b1020008b5861c5420400192ac638a8408003295887150810
  | 1 => 0xacaa126418823079cd65904310062bbb4a29886200c5776dd5310c4012ad0f2926218822a5219424c43100516c1086b2e4207a4c825d563c840151b043a2c79081e1b2097654f2103e26392c6a9e4208c96639c643c840107d0e21acb108028b60843596210041f43e84b2c420083d87997648840107f0eb2ec9108030799673d92210060eb2ce7b244200c1e759cf648840183aeb39ec91082227e1d73d92210041ec3ea7b244208c1e73d4f648840192ae738ec910957295ca71d922126e0f398a3b244248c1e73d43648840151b0421ac7108020fa1f6454e210450f41ec8a9c4207875861c5538840107f0eb2c871094a0f21d6550a210454741ec919442088ae87d91328841151d07b22651080383d91534ca21005a240aa69944242a1e83d92518847f85ce5b24a3108028b60843d95210450f41ec8a9a424cd24521c5424840107d0fa9ac8108020f21d6454c2103c2e43ac6a9842088b5869c6430841151906b22641080383591534c82103e17392c92884200c6776945210840145b053a6c6a80020f61f42d8d5003e16312e9312a00083e87d8d4254083838e7b1a84a801e8ba1b625095000586c18c4a12a04cc2c621c5425408b858c5b8284a801f0b1d9428c95020c9643a84992a000c2c76509325408361906a1264a801f0b189740c9500060eb988630aa000a2d8210c615400146902a10c2a801e1b209760c5500052ac18c218aa000a54864c4315408323d07ba442a80ff0b18b748855003e16312e810aa007878865c02154011838c6bacc6a002287a1b6354d4000586c10c6a9a804dc1c631c55350091838c7b82a6a00028760e75d89400041ec3ea7b12800083f8754f625007d45904a9ec4a0002a920562189400460e3b2a7992803e91c8754d3250001838eca9a64a00230718d750c9400051a40aa630a8000a1d83148615000185ae4290c2a010b0718f758c5401f497416eb18a8008c1c635d431500111710cb8062a0003644c5700c5400444e41aec10a800083e87d0965cc0010790eb2a85980222b21d6250b3004546432849966000e0d6550932cc00f0dd05bb4a398023079cd65907300460e39acaa066000a1d83149648c00116902bb2851801e8b2096550a3000616320e4b2a6000c34641c5654c00185ee8392ca980030b1d072595300041f43e84b2a6007c2c72d09654c0018c8e5b8aca980030ddd071595300061a3a0e2b2a6000c57731c5654c0018cee438aca98003191c871595300061bc20e2b2a6000c34841c5654c00186c8638aca980030d10c71595300061ba10e2b2a604cc2c72105654c001868e220aca981170b1cb40595300061a38e80b2a600083d87997644c00107f0eb2ec8980028b20965d91300051a40acbb22600083d87d4f644c00107b0e296c8980028760c52d91302a41f43ec8a9a6000
  | 2 => 0xe43582520041ec3886b04a400c1f7310d609480145b0421ac1290030dd967198d420061a32ce331a8408c94635c6635087507b0fb28c6a10028760c6518d4229616b90ca31a840083e869d9535080107d023b2a6a10020f6007654d420060fb2ce730a8400c1c659ce615080146d03ba8c2a10028da0475185420041f43ea630a840083c8754c615081113906b80c2a10028da0750185420051cc06ebb028400a39801d7605080107d0fa9ec0a10020f21d53d81420444f41ce3b028400c1f651cd6050801838ca39ac0a10030dd9471581420061a328e2b02840083e87d0965cc8a50790eb2a85990024721d5350b320041f43ea6b24645483c87591538c8012590ea9a851913f8358d5350a321e60e3b6e8a9a6440c1c76d91534c80161b08392a699003431d07254d320048e43aa6a126407a1c8654d424c877858edbaa849910f0b1db655093221e8639ecaa12640898e87dcd424c80161b0a39a849900343dd47350932006863a8e6a12640092c8754d424c811858eca9a8499023431cd535093200687c3aa6a126400b0e8754d424c8016190ea9a84990034321d53509320048643aa6a126407b0e8654d424c80f6190ca9a8499023439d95350932046863b2a6a126400b0c8154d424c80161f00a9a84990034354c715093200686a9ee0a126400a2d821d1639440107d0fa12c72881f0b9897418a510041e43ac6a14a242c1c7358d429440161b07312852881e8be196250a5126617310e2a14a245c2e62dc1429440f85eeca14652890a4b21d424ca5100617bb284994a242b0c83509329440f85cc4ba0652880307dcc435825100516c1086b04a200a398010d609441183cc6ba8c720802c360a6354e410450fc32c6a9c824dc1e631c5539049183cc7b82a7208028760c7558a410041f43ea6b14820083c8754d629047f45904a9ac52082307dd953cca411fc8e43aa69948200c1f7654d329041183cc6ba865208028760c525824100617b90a4b048200a3980149609040143b06292c9988029360c7558b310454641ae8b166207c66629c652cc411918e6b1285988030b99272d9631006173a4e5b2c6200c2d749cb658c40107b0fa16cb1881f0b9cb42d96312b62ab9ce3b2c6200c65729c7658c49985ce420ecb189170b9cb40d96310041f43ecab246200a2e82d95648c40107d0e32ac9188020fa1f53592310041f438a4b246200a1d83149648c4a90790eb22a7188029360c5258a310041fc3ac9294620083e87d95428c40f45d05b2a851881e93a0b65cca3103c2f43eca9946200a8f86509328c401c1ecaa126518802e1205424ca312160f39ecb20c623fa2e82d96418c40143b06296c8989374510c7154d3103d17416caa12620083e87d09650c4012ab0738ca4188020f21d65508310445643ac4a106208a8c86509320c401c1
  | 3 => 0x1b64b03b17997118114b80030ce1000004640063c9039c870000040171634620cdcb000350c07100000414000c5255642a5395e6c12b324d22e8f500117540fd03c005ad920006359d5d4ed3246c0031d684f53e000000017011c6025cfc48c000f537001983e400699450007a2d8531bc000000000000000002ec0008800001bb000c55a9ae520002ad91424c4000e52c5902dcef380e40000024d545b5bc3609e321c6000b44807d00075275060f80000000344005899e15c28210036fc2b264005348057cd65d00b3e0bf3dc51085aa0015847800610b3000a72953f3b80042957628160012d000000019954d8b3b54a50400001292c073024d51f800650150286d2a92143cdd0a4cc468b95f800000000b4de3706b6b1955ec194bc08128da705b96190e048ca3ac5c3395b258761244e5dc000000000000000a10000000169458e64c4e8470000019f0008a6e17a0011f69d3c689ca5017f0b01300005001b161c8866dab290001684f00112690000bc985d44b0000000000568000e01f44c9b23c00218003c81471c000002e1b8006800000000000004d57d00110000ea434833fd0b1400000000191b364ce90940000032000895b9650301c1e533544c10000017c004a8486e800000bc001720007b3183a000a20004c6dc0000000308723b0002d4fa5bc000320200002000048000200809054000020d8000f0100480000812000000400009008040160081000000038000080a05006058121d0000087000016028000303a000021580c0101e0280a0204e01804000000000404002000000000205834028760201015804020000100c0081e00020000000000600000000100e8000400a000300080028802020000101c0280e0400000806020000080401846020060082c0600201824030000f00409002000000300a08800000000101c00800018120200e00c37649c66254c01868c938cc4a981f1918971989531ec1ec3ec8312a654c1d731906254c0185ec9394c2a98030b19272985530051b40ee830aa600a36811d06154c0107d0fa10c2a981e1b20970185530051b40e8030aa600a3980dd36054c01473003a6c0a98020fa1f42d815303c37414e3b02a600c2f641c96054c01858c8392c0a98030dd9071581530061a320e2b02a640a1d831d56290c0145d05bacc3219368da0775986432151b408eb30c860083e8714a6190c0143b06294c3218030b5c8529864320d1cc04eab048600a2c825d56090c9147700baac1218020f61c52582430050ec18a4b048600c2f721496090c8745b043a2c7290020f2057690e520041fc02ed21ca400a1e83dd2619489946d03ba4c3290fe8da0474986520041f43c8730ca40083e8710e619480183ae621cc3290028b60843986521f51cc04e8b04a400a1c835d1609488b47700ba2c1290020f61
  | 4 => 0x108002a468000d31581b600d41d1cc1f1ad23127164586f80d038a86d0785d93a0183c6c8e31fcbd659344743f35dc037dc3559a82986150964604660690719ccd13588251a5598174c1a3460b822d113882309d39214395e05b6753841043454a3530cb2381d098a01514772434000d900002234be1946c2b9080017c58400714fe0000010036001246f583738910910c040b20116c580520011468552554001c0000009a3d18940d9a3c15c341c850c9c254921a8ac524456a54f4a18e6149f3edc4204005cc771a4007085d52cc04040758d793d8cf079af000f30618240926670001540000000001b5111cd51800000af0dc20000412093600000000f10018c2b4000012200000000000000100000510db
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xc010000b1c187c126243818a3c400003684a13123c880349028000011a0449421d0e545862e34019100420026801000c82c2040180d835c852986430060360f721496090c0180d73608439865200603dcd8210d609480180d7260c6518d420040d245801d9535080110e97a1d535093220443a588754d424c8a710c9621d535093200443a448754d424c80110d9021d535093200443261531c5424c80110c9854f70509320060320f76509329440180f7360843582510060360f72149609040120e98d95424ca3103d03a5f65509328c40120c98595424c83100483a636454d328841140e97d91534ca21004832616454d320840180c831d9424c950006035cd8210c615400180d835c85218540004832616550932cc0014259210c71595300048326165509324c00f40c97595424c9300058124565509324c001816732056590530006051cc81595404c00120c98591534cb200050564c521c5644800120c98591534c9200450325d6454d324800160491591534c920006099c8815925148001824722056454120
  | _ => 0
def gbK2 : Nat → Nat
  | 0 => 0x3240016501000200ea6a448754d424c8010065332043aa6a1264008412859021d535093200500b4539902b2c8298002805a21cc81595404c001402d1ce440ac928a4000a0168c722056454120
  | _ => 0
def gbHint : Nat → Nat
  | 0 => 0x0
  | 1 => 0x5
  | 2 => 0x6
  | 3 => 0x1
  | 4 => 0x4d
  | 5 => 0x4e
  | 6 => 0x138d
  | 7 => 0x3
  | 8 => 0x4
  | 9 => 0x94d
  | 10 => 0x94e
  | 11 => 0x124d
  | 12 => 0x124e
  | 13 => 0x138e
  | 14 => 0x8d
  | 15 => 0x8e
  | 16 => 0x98d
  | 17 => 0x98e
  | 18 => 0x128d
  | 19 => 0x128e
  | 20 => 0x150d
  | 21 => 0x150e
  | 22 => 0xcd
  | 23 => 0xce
  | 24 => 0x9cd
  | 25 => 0x9ce
  | 26 => 0x12cd
  | 27 => 0x12ce
  | 28 => 0x168d
  | 29 => 0x168e
  | 30 => 0xa0e
  | 31 => 0xa4d
  | 32 => 0x20d
  | 33 => 0x20e
  | 34 => 0x140d
  | 35 => 0xb0d
  | 36 => 0xb0e
  | 37 => 0x140e
  | 38 => 0x154d
  | 39 => 0x154e
  | 40 => 0x24d
  | 41 => 0x24e
  | 42 => 0x144d
  | 43 => 0xb4d
  | 44 => 0xb4e
  | 45 => 0x144e
  | 46 => 0x16cd
  | 47 => 0x16ce
  | 48 => 0x148e
  | 49 => 0x14cd
  | 50 => 0x3cd
  | 51 => 0x3ce
  | 52 => 0xccd
  | 53 => 0xcce
  | 54 => 0x15cd
  | 55 => 0x15ce
  | 56 => 0x170d
  | 57 => 0x170e
  | 58 => 0xd0e
  | 59 => 0x164d
  | 60 => 0x178e
  | 61 => 0xecd
  | 62 => 0xa0b
  | 63 => 0x148b
  | 64 => 0x178b
  | 65 => 0xa4c
  | 66 => 0x14cc
  | 67 => 0x164c
  | 68 => 0x2cd
  | 69 => 0x180b
  | 70 => 0x1a4d
  | 71 => 0x198d
  | 72 => 0x198c
  | 73 => 0xb0215
  | 74 => 0xb4255
  | 75 => 0xb4256
  | 76 => 0x28b
  | 77 => 0x2cc
  | 78 => 0xd0cd6
  | 79 => 0xeccd5
  | 80 => 0xd15d6
  | 81 => 0xed715
  | 82 => 0x44d
  | 83 => 0x58b
  | 84 => 0x58e
  | 85 => 0x20b15
  | 86 => 0x24b56
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 76
  | 6 => 1421
  | 5 => 2511
  | 4 => 463
  | 3 => 39
  | 2 => 7
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
  | 7 => packedAt gbK7 (2151+((h/25+packedAt gbK7 (1976+(h % 25)*7) 7) % 92)*8) 8
  | 6 => packedAt gbK6 (57780+((h/473+packedAt gbK6 (52577+(h % 473)*11) 11) % 1876)*12) 12
  | 5 => packedAt gbK5 (130572+((h/837+packedAt gbK5 (120528+(h % 837)*12) 12) % 3646)*13) 13
  | 4 => packedAt gbK4 (28857+((h/154+packedAt gbK4 (27317+(h % 154)*10) 10) % 611)*10) 10
  | 3 => packedAt gbK3 (2808+((h/13+packedAt gbK3 (2730+(h % 13)*6) 6) % 47)*7) 7
  | 2 => packedAt gbK2 (575+((h/2+packedAt gbK2 (567+(h % 2)*4) 4) % 9)*4) 4
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0xff80ff807fffffe03ffffffff463cf1e47f1ff
  | 1 => 0x7fff07ff81e03fffc1e03c07fb9cf4e7b93e93
  | 2 => 0x81fff80001ffc0fffe003ff80c1f38f9c1cf1c
  | 3 => 0x1fffffffe0000ffffffc0000fe03f01fe0fe0
  | 4 => 0x1ffffffffffff00000000000fffc001fff000
  | 5 => 0xfe00000000000000000000000ffffffe000000
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0xa200110022485100022a05428021410a025025
  | 1 => 0x548b02b480a22a6a4140a815618c9464992692
  | 2 => 0x1d5a80c113688b6b40132b02c1628b1c18b18
  | 3 => 0x1166ccd9540400dd399580204ec03e016c0dc0
  | 4 => 0x61f8f76e79df3c06100620c18f7fc001f7f000
  | 5 => 0x7840807060183018211803060ffbffde000000
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 63 gbPos gbNeg, 0xeee8eae8eea8eaa8eee8eae8eea8eaa8eee8eae8eea8eaa8eee8eae8eea8eaa8eee8eae8eea8eaa8eee8eae8eea8eaa8eee8eae8eea8eaa8eee8eae8eea8eaa8, gbN, gbR, gbH, gbI⟩
end PEqualNP.Outside.L_meta_13565
namespace PEqualNP.Outside.L_meta_13565
open PEqualNP.Outside.L_meta_13565.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bs1_1_0 : Interval s1Atlas 1 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls1_1 : Interval s1Atlas 1 0 1 := bs1_1_0
theorem alls1 : ∀ k ≤ 1, ∀ i < count s1Atlas k, checkRow s1Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls1_1 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_2_0 : Interval s2Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls2_2 : Interval s2Atlas 2 0 4 := bs2_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_3_0 : Interval s2Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls2_3 : Interval s2Atlas 3 0 6 := bs2_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs2_4_0 : Interval s2Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls2_4 : Interval s2Atlas 4 0 1 := bs2_4_0
theorem alls2 : ∀ k ≤ 4, ∀ i < count s2Atlas k, checkRow s2Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls2_2 i (by omega) hi
  · exact alls2_3 i (by omega) hi
  · exact alls2_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_2_0 : Interval s3Atlas 2 0 4 := block_range (n:=4) (by decide +kernel)
theorem alls3_2 : Interval s3Atlas 2 0 4 := bs3_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_3_0 : Interval s3Atlas 3 0 6 := block_range (n:=6) (by decide +kernel)
theorem alls3_3 : Interval s3Atlas 3 0 6 := bs3_3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs3_4_0 : Interval s3Atlas 4 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls3_4 : Interval s3Atlas 4 0 1 := bs3_4_0
theorem alls3 : ∀ k ≤ 4, ∀ i < count s3Atlas k, checkRow s3Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls3_2 i (by omega) hi
  · exact alls3_3 i (by omega) hi
  · exact alls3_4 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_3_0 : Interval s4Atlas 3 0 26 := block_range (n:=26) (by decide +kernel)
theorem alls4_3 : Interval s4Atlas 3 0 26 := bs4_3_0
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
theorem bs4_4_128 : Interval s4Atlas 4 128 6 := block_range (n:=6) (by decide +kernel)
theorem alls4_4 : Interval s4Atlas 4 0 134 := (concat (concat bs4_4_0 bs4_4_32) (concat bs4_4_64 (concat bs4_4_96 bs4_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_0 : Interval s4Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_5_32 : Interval s4Atlas 5 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls4_5 : Interval s4Atlas 5 0 48 := (concat bs4_5_0 bs4_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs4_6_0 : Interval s4Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls4_6 : Interval s4Atlas 6 0 1 := bs4_6_0
theorem alls4 : ∀ k ≤ 6, ∀ i < count s4Atlas k, checkRow s4Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls4_3 i (by omega) hi
  · exact alls4_4 i (by omega) hi
  · exact alls4_5 i (by omega) hi
  · exact alls4_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_3_0 : Interval s5Atlas 3 0 26 := block_range (n:=26) (by decide +kernel)
theorem alls5_3 : Interval s5Atlas 3 0 26 := bs5_3_0
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
theorem bs5_4_128 : Interval s5Atlas 4 128 6 := block_range (n:=6) (by decide +kernel)
theorem alls5_4 : Interval s5Atlas 4 0 134 := (concat (concat bs5_4_0 bs5_4_32) (concat bs5_4_64 (concat bs5_4_96 bs5_4_128)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_0 : Interval s5Atlas 5 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_5_32 : Interval s5Atlas 5 32 16 := block_range (n:=16) (by decide +kernel)
theorem alls5_5 : Interval s5Atlas 5 0 48 := (concat bs5_5_0 bs5_5_32)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bs5_6_0 : Interval s5Atlas 6 0 1 := block_range (n:=1) (by decide +kernel)
theorem alls5_6 : Interval s5Atlas 6 0 1 := bs5_6_0
theorem alls5 : ∀ k ≤ 6, ∀ i < count s5Atlas k, checkRow s5Atlas k i = true := by
  intro k hk i hi
  interval_cases k
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact False.elim (Nat.not_lt_zero i hi)
  · exact alls5_3 i (by omega) hi
  · exact alls5_4 i (by omega) hi
  · exact alls5_5 i (by omega) hi
  · exact alls5_6 i (by omega) hi
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_2_0 : Interval gbAtlas 2 0 7 := block_range (n:=7) (by decide +kernel)
theorem allgb_2 : Interval gbAtlas 2 0 7 := bgb_2_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_0 : Interval gbAtlas 3 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_3_32 : Interval gbAtlas 3 32 7 := block_range (n:=7) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 39 := (concat bgb_3_0 bgb_3_32)
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
theorem bgb_4_448 : Interval gbAtlas 4 448 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 463 := (concat (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat (concat bgb_4_96 bgb_4_128) (concat bgb_4_160 bgb_4_192))) (concat (concat (concat bgb_4_224 bgb_4_256) (concat bgb_4_288 bgb_4_320)) (concat (concat bgb_4_352 bgb_4_384) (concat bgb_4_416 bgb_4_448))))
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
theorem bgb_5_2496 : Interval gbAtlas 5 2496 15 := block_range (n:=15) (by decide +kernel)
theorem allgb_5 : Interval gbAtlas 5 0 2511 := (concat (concat (concat (concat (concat (concat bgb_5_0 bgb_5_32) (concat bgb_5_64 bgb_5_96)) (concat (concat bgb_5_128 bgb_5_160) (concat bgb_5_192 (concat bgb_5_224 bgb_5_256)))) (concat (concat (concat bgb_5_288 bgb_5_320) (concat bgb_5_352 (concat bgb_5_384 bgb_5_416))) (concat (concat bgb_5_448 bgb_5_480) (concat bgb_5_512 (concat bgb_5_544 bgb_5_576))))) (concat (concat (concat (concat bgb_5_608 bgb_5_640) (concat bgb_5_672 (concat bgb_5_704 bgb_5_736))) (concat (concat bgb_5_768 bgb_5_800) (concat bgb_5_832 (concat bgb_5_864 bgb_5_896)))) (concat (concat (concat bgb_5_928 bgb_5_960) (concat bgb_5_992 (concat bgb_5_1024 bgb_5_1056))) (concat (concat bgb_5_1088 bgb_5_1120) (concat bgb_5_1152 (concat bgb_5_1184 bgb_5_1216)))))) (concat (concat (concat (concat (concat bgb_5_1248 bgb_5_1280) (concat bgb_5_1312 (concat bgb_5_1344 bgb_5_1376))) (concat (concat bgb_5_1408 bgb_5_1440) (concat bgb_5_1472 (concat bgb_5_1504 bgb_5_1536)))) (concat (concat (concat bgb_5_1568 bgb_5_1600) (concat bgb_5_1632 (concat bgb_5_1664 bgb_5_1696))) (concat (concat bgb_5_1728 bgb_5_1760) (concat bgb_5_1792 (concat bgb_5_1824 bgb_5_1856))))) (concat (concat (concat (concat bgb_5_1888 bgb_5_1920) (concat bgb_5_1952 (concat bgb_5_1984 bgb_5_2016))) (concat (concat bgb_5_2048 bgb_5_2080) (concat bgb_5_2112 (concat bgb_5_2144 bgb_5_2176)))) (concat (concat (concat bgb_5_2208 bgb_5_2240) (concat bgb_5_2272 (concat bgb_5_2304 bgb_5_2336))) (concat (concat bgb_5_2368 bgb_5_2400) (concat bgb_5_2432 (concat bgb_5_2464 bgb_5_2496)))))))
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
theorem bgb_6_1408 : Interval gbAtlas 6 1408 13 := block_range (n:=13) (by decide +kernel)
theorem allgb_6 : Interval gbAtlas 6 0 1421 := (concat (concat (concat (concat (concat bgb_6_0 bgb_6_32) (concat bgb_6_64 (concat bgb_6_96 bgb_6_128))) (concat (concat bgb_6_160 (concat bgb_6_192 bgb_6_224)) (concat bgb_6_256 (concat bgb_6_288 bgb_6_320)))) (concat (concat (concat bgb_6_352 bgb_6_384) (concat bgb_6_416 (concat bgb_6_448 bgb_6_480))) (concat (concat bgb_6_512 (concat bgb_6_544 bgb_6_576)) (concat bgb_6_608 (concat bgb_6_640 bgb_6_672))))) (concat (concat (concat (concat bgb_6_704 bgb_6_736) (concat bgb_6_768 (concat bgb_6_800 bgb_6_832))) (concat (concat bgb_6_864 (concat bgb_6_896 bgb_6_928)) (concat bgb_6_960 (concat bgb_6_992 bgb_6_1024)))) (concat (concat (concat bgb_6_1056 (concat bgb_6_1088 bgb_6_1120)) (concat bgb_6_1152 (concat bgb_6_1184 bgb_6_1216))) (concat (concat bgb_6_1248 (concat bgb_6_1280 bgb_6_1312)) (concat bgb_6_1344 (concat bgb_6_1376 bgb_6_1408))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_0 : Interval gbAtlas 7 0 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_32 : Interval gbAtlas 7 32 32 := block_range (n:=32) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bgb_7_64 : Interval gbAtlas 7 64 12 := block_range (n:=12) (by decide +kernel)
theorem allgb_7 : Interval gbAtlas 7 0 76 := (concat bgb_7_0 (concat bgb_7_32 bgb_7_64))
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

theorem bounds0 (cert : Complete s0Atlas) : Lower true (roots s0Atlas) (target s0Atlas) 5 := by
  have ready : Ready s0Atlas (asRow s0Pos) (asRow s0Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 1 zero, 12, 14),(inputs.getD 2 zero, 10, 14),(inputs.getD 3 zero, 6, 14),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds1 (cert : Complete s1Atlas) : Lower true (roots s1Atlas) (target s1Atlas) 2 := by
  have ready : Ready s1Atlas (asRow s1Pos) (asRow s1Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 4, 5),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds2 (cert : Complete s2Atlas) : Lower true (roots s2Atlas) (target s2Atlas) 5 := by
  have ready : Ready s2Atlas (asRow s2Pos) (asRow s2Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 10, 26)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds3 (cert : Complete s3Atlas) : Lower true (roots s3Atlas) (target s3Atlas) 5 := by
  have ready : Ready s3Atlas (asRow s3Pos) (asRow s3Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds4 (cert : Complete s4Atlas) : Lower true (roots s4Atlas) (target s4Atlas) 7 := by
  have ready : Ready s4Atlas (asRow s4Pos) (asRow s4Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem bounds5 (cert : Complete s5Atlas) : Lower true (roots s5Atlas) (target s5Atlas) 7 := by
  have ready : Ready s5Atlas (asRow s5Pos) (asRow s5Neg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ hn; exact False.elim (hn rfl)
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 10, 26)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
theorem boundgb (cert : Complete gbAtlas) (ss : ∀ v : Fin 6, Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD v.val zero)) (SBf v.val)) : Lower true (roots gbAtlas) (target gbAtlas) 9 := by
  have ready : Ready gbAtlas (asRow gbPos) (asRow gbNeg) := by
    refine ⟨?_,raw_faithful _ _ _,?_⟩
    · unfold properPairs; decide +kernel
    · intro k i _ _; exact ss ⟨min ((tip gbAtlas k i % 8)-1) 5,by omega⟩
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 2, 3),(inputs.getD 1 zero, 1, 3),(inputs.getD 2 zero, 1, 5),(inputs.getD 3 zero, 1, 9),(inputs.getD 4 zero, 10, 26),(inputs.getD 5 zero, 6, 38)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero,inputs.getD 5 zero]
def fullWord : Sig := 0xeee8eae8eea8eaa8eee8eae8eea8eaa8eee8eae8eea8eaa8eee8eae8eea8eaa8eee8eae8eea8eaa8eee8eae8eea8eaa8eee8eae8eea8eaa8eee8eae8eea8eaa8
theorem fullBound (certs0 : Complete s0Atlas) (certs1 : Complete s1Atlas) (certs2 : Complete s2Atlas) (certs3 : Complete s3Atlas) (certs4 : Complete s4Atlas) (certs5 : Complete s5Atlas) (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 9 := by
  have s0 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 0 zero)) (SBf 0) :=
    slice_correct (ms:=fixRows 1 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds0 certs0)
  have s1 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 1 zero)) (SBf 1) :=
    slice_correct (ms:=fixRows 50 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds1 certs1)
  have s2 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 2 zero)) (SBf 2) :=
    slice_correct (ms:=fixRows 36 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds2 certs2)
  have s3 : Slice true (roots gbAtlas) (target gbAtlas) (neg ((roots gbAtlas).getD 3 zero)) (SBf 3) :=
    slice_correct (ms:=fixRows 24 0) (by decide +kernel) (by decide +kernel) (proper_of _ (by decide +kernel)) (bounds3 certs3)
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
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (4008241896 * 2 ^ 32 + 4004047528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_13565.Model.Repr at out
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

def mono : List Gate := [⟨.or,[1,3]⟩,⟨.or,[2,4]⟩,⟨.and,[2,5]⟩,⟨.or,[2,6]⟩,⟨.and,[1,7]⟩,⟨.or,[0,3]⟩,⟨.and,[9,11]⟩,⟨.or,[8,12]⟩,⟨.or,[0,10]⟩,⟨.and,[13,14]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,15⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 9) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241896 * 2 ^ 32 + 4004047528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241896 * 2 ^ 32 + 4004047528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_13565

open PEqualNP.Outside.L_meta_13565 in
theorem PEqualNP.Outside.L_meta_13565 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241896 * 2 ^ 32 + 4004047528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241896 * 2 ^ 32 + 4004047528) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound alls0 alls1 alls2 alls3 alls4 alls5 allgb)
