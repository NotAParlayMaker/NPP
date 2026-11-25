import Mathlib
import PEqualNP.Defs

-- The signed live-wire search, its checker and the input-fixing lift are copied from the merged
-- L_meta_10856 (same repository, Apache-2.0), which follows L_meta_8453 and L_meta_1667.
-- New here: the search tables for this six-input function, the lift and the AND/OR circuit.

namespace PEqualNP.Outside.L_meta_12825.Model
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


end PEqualNP.Outside.L_meta_12825.Model

namespace PEqualNP.Outside.L_meta_12825
open PEqualNP.Outside.L_meta_12825.Model
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

def mirrorSteps : List Move := [swapRows 33]

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

end PEqualNP.Outside.L_meta_12825

namespace PEqualNP.Outside.L_meta_12825
open PEqualNP.Outside.L_meta_12825.Model
def gbK8 : Nat → Nat
  | 0 => 0x1f
  | _ => 0
def gbK7 : Nat → Nat
  | 0 => 0x60001dc0e49c0000862023a2003276a7c0404a6e08c4ab9740303ac04a2149ad61a78558800e080041040210223ff43fe43fd43fc43ff41fe41fd41fc41ff31fe31fd31fc31fe21fd21fc21ff40fe40fd40fc40ff30fe30fd30fc30ff10fe10fd10fc10
  | _ => 0
def gbK6 : Nat → Nat
  | 0 => 0x861ff410c3fc82187f50430fe20861ff310c3fc62187f4c430fe18861fe210c3fa42187f08430bf28061ff400c3f680187f90030fea0061fc400c3f080187fcc030ef98061fe300c3f460187f4c030ee98061f9300c3fea9885fd5310ff2a6217e54c43faa9885f55310fe2a6217c54c43fea7885fd4f10ff29e217e53c43faa7885f54f10fe29e217c53c43fe87887f90f10fea1e21fc43c43fea5887f94b10bf29621fd52c42faa5887f14b10be29621ff42c43fc85887f50b10fe21621ff32c43fc65887f4cb10fe19621ff41c43fc83887d90710fea0e21f541c43f883887fcc710fb98e21fe31c43fa63887f0c710fa18e21ff21c43ee43887f88710fe90e21fc21c43e843887fd0310fda0621fe40c43fa81887f10310fc20621ff30c43fc61887f4c310fe18621ff20c43fea9085fd5210ff2a4217e54843faa9085f55210fe2a4217c54843fea7085fd4e10ff29c217e53843bca7085794e10fea9c217d53843baa7085754e10fe29c217c53843fe87087f90e10fea1c21fc43843fea5085fd4a10ff294217e52843dca5085b94a10fea94217d52843daa5085b54a10fe29421ff42843fc85087f50a10fe21421ff32843fc65087f4ca10fe194217d51843fe83087dd0610ff20c21fd41843f883087d10610ff98c21fe31843fa63087f0c610ff90c21fe21843fa43087f08610bf28421ff40843fc81087f50210fe20421ff30843fc61087f4c210fe18421ff20843fc41087fc4210fb88421fb10843fea8885fd5110ff2a2217e54443faa8885f55110fe2a2217c54443fea6885fd4d10ff29a217e53443faa6885f54d10fe29a217c53443fe86887f90d10fea1a21fc43443fea4885fd4910ff292217e52443faa4885f54910fe292217c52443fe84887f90910fea1221fc42443fe64887f8c910fe99221fc32443fe82887f90510fb20a21fd41443ea82887f10510ff98a21f731443fc62887f4c510fe18a21f431443fe42887dc8510ff10a21fd21443f842887d08510ffa0221fe40443fa80887f10110ff98221fe30443fa60887f0c110ff90221fe20443fa40887fc4110fd88221fe10443ec20887fd5010bfaa021fe54042fca8087f55010beaa021fc54042f8a8087fd4c10bfa9821fe53042fca6087f54c10bea9821fc53042f8a6087fd0c10ff21821fd43043f886087fd4810bfa9021fe52042fca4087f54810bea9021fc52042f8a4087fd0810ff21021fd42043f884087fcc810ff19021fd32043f864085f94410ffa0821f741043fc82087f50410fe20821f441043fe62087f8c410fe98821fc31043fe42087f88410fe90821fc21042fca0087fd0010fda0021fe40043fa80087f10010fc20021ff30043fc60087f4c010fe18021ff20043fc40087f48010fe10021ff10043ee20087f84010fd08021fd10043ea20087e44010
  | 1 => 0xf31087ee6210ff8c421fe98843fc31087e86210ff88421fb10843fd21087ea4210f948421ffa8043fe50086fca010ff54021bea8043fc50087fea7a07f94f40bf29e81fd53d02faa7a07f14f40ffa1e81fe43d03fa87a07f10f40ffa8e81fe51d02fca3a07f54740bea8e81fc51d03fe83a07f90740fea0e81fc41d03fe63a07f8c740fe98e81fc31d03fc43a07f48740fe10e817d54903fea7207f94e40bf29c81fd53902faa7207f14e40ffa1c81fe43903fa87207f10e40ffa8c81fe51902fca3207f54640bea8c81fc51903fe83207f90640fea0c81fc41903fe63207f8c640fe98c81fc31903fc43207f48640fe10c817e50903fe81206fd0240fda0481ff53502fea6a077d4d40afa9a81fe53503faa6a07f14d40be29a81dc53502b8a6a07fd0d40ff21a81fd43503f886a07fd4540bfa8a81f751502eea2a07f94540fea8a81fc51502f8a2a07d14540ba28a81ff41503fc82a07f50540fe20a81ff31503fc62a07f4c540fe18a81fe21503fa42a07f08540ffa0281fb40503fc80a06f90140bf2a081ff53103fca6205f94c40ef298815e53103faa6205f54c40eea98815d53103f8a6207fd0c40ff21881fd43103f886207fd4440ff288817e51103eca2205d94440fea88817d51103eaa2205d54440fe28881ff41103fc82207f50440fe20881ff31103fc62207f4c440fe18881fe21103fa42207f08440bf28081ff401037e80207f90040fd20081fd401037a80207e50040ffaa6617f54cc3fca9985f95330feaa6617d54cc3f8a9985f15330ffa1e61fe43cc3bc87987f50f30eea1e61fc43cc3fea3987f94730bf28e61fd51cc2faa3987f14730ffa0e61fe41cc3fa83987f10730ff98e61fe31cc3bc63987f4c730fe18e61dc31cc3fc43987f48730fe10e61ff40cc3f681987f90330fea0661fc40cc3f081987fd5230bfaa461fe548c2fca9187f55230beaa461fc548c2f8a9185f54e30ffa1c61df438c3fc87187f50e30fe21c61dc438c3fea3187f94630bf28c61f6518c2eca3187f54630bea8c61f5518c2eaa3187f14630ffa0c61fe418c3fa83187f10630ff98c61fe318c3fa63187f0c630ff10c61fd218c3f843185f94230ffa0461fe408c3fa81187f10230ff98461df308c3f661187fd5130bfaa261fe544c2fca8987f55130beaa261fc544c2f8a8987fd0d30ff21a61de434c3fa86987750d30fe21a61ff514c2fea2987f94530fea8a61fc514c2f8a2987fd0530ff20a61fd414c3f882987fcc530ff18a61de314c3fa62987f0c530ee18a61fe214c3fa42987f08530ffa0261fe404c3fa80987f10130ff98261fb304c3fc6098778c130ffaa0617f540c3fca8185f95030feaa0617d540c3f8a8185f15030bf29861ff430c3be86187f90c30fea1861fc430c3b886187fd4430ff288617e510c3faa2185f54430fe28
  | 2 => 0x6fca220ffd0441dfa0883fe41107ec8220ff50441dea0883f541107fea020ff94041bf28083fd50106faa020ff14041ffaa6637f54cc7fca998df95331feaa6637d54cc7f8a998df15331ffa1e63fe43cc7fa8798ff10f31ffa9663fe52cc6fca598ff54b31bea9663fc52cc7fe8598ff90b31fea1663fc42cc7fe6598ffd0731fba0e63fe41cc7fa8398ff10731fa20e63ff50cc7fca198df94331fea86637d50cc7f8a198ffd5231bfaa463fe548c6fca918ff55231beaa463fc548c6f8a918df54e31ffa1c63df438c7fc8718ff50e31fe21c63dc438c7fea518ff94a31bf29463fd528c6faa518ff14a31ffa1463fe428c7fa8518ff10a31ff99463fe328c7bc6518df94631ffa0c63fe418c7fa8318ff10631ff98c63df318c7ee6318ffd4231ff284637e508c7faa118df54231fe28463ff544c6fea898ff95131bf2a263fd544c6faa898ff15131be2a263ff434c7fc8698ff50d31fe21a63ff524c6fea498fbd4931b7a9263fe524c7faa498ff14931be29263ec524c6d8a498ffd0931ff21263fd424c7f88498ffcc931ff19263fd324c7fe8298ff90531fea0a63fc414c7fe6298fdcc531ff18a63de314c7fea098dfd4131ff28263fd504c7f8a098df14131ffaa0637f540c7fca818df95031feaa0637d540c7f8a818df15031bf29863ff430c7be8618ff90c31fea1863fc430c7b88618ffd4831ff290637e520c7faa418df54831fe29063ff420c7fc8418ff50831fe21063ff320c7fc6418f78c831fe99063fc320c7b86418df94431ffa0863f7410c7fc8218ff50431fe20863f4410c7fe6218f7cc431ff18863f6310c7fa6218f74c431fa98863d5310c7fea018ff94031bf28063fd500c6faa018ff14031ffaa4437f54887fca910df95221feaa4437d54887f8a910df15221ffa9c437f53887fca710df94e21fea9c437d53887f8a710df14e21ffa1c43fe43887fa8710ff10e21bea9443ff42887de8510ff90a21fea1443fc42887d88510ffcca21f799443fe32887fa6510ff0ca21f6194437e51887fe8310ff90621fea0c43fc41887fe6310ff8c621fe98c43fc31887fe4310fdc8621ffa8443fe50886fca110ff54221bea8443fc50887fea890dfd5121ff2a2437e54487faa890df55121fe2a2437c54487fea690dfd4d21efa9a435f53487fca690df94d21fea9a437d53487f8a690df14d21ee29a435c53487fe8690ff90d21fea1a43fc43487fe8290ff90521fea0a43fc41487fe6290ff8c521fe98a43fc31487fc4290fb88521ffa82437f50487fca090ff54121fe282437c50487fea810dfd5021ff2a0437e54087faa810df55021fe2a0437c54087fea610dfd4c21ff298437e53087faa610df54c21fe298437c53087fe8610ff90c21fea1843fc43086fca210ffd0421fba0843fe41087fa8210ff10421fa20843f
  | 3 => 0x400c00001001800001801c00000000000000401000401800400400000000401000000001c01800401000002000000002c00000800000402800000000400400000400002000800400000001402800000000800800800400400000c00000000400000c00401801c00000800c00000000401800000c01402802000000800000000002c01400c01000400403801000802400000400400000000001000000001c01400c00803400001400000400801000000000000400802001000c01000400400400800001000c00400000000001800400000802001002000400c00800400400401400000000000400000401000801801001000000000800004000400400800400001000000400800801003800001000001000000001400001400800800c00000000000001400c01000400001000800000001000000403800000800800400c00000001000000401400400400800c00c00800c00401400000400000000800000000c00003400000000000000000000000400400801400800000001c02800c004000000004004003fea3a1ff94743bf28e87fd51d0efaa3a1ff14743ffa8687fe50d0efca1a1ff54343bea8687fc50d0efaa921df94e43ffa1c87bf4390fbe8721ffd4643ff28c877e5190ffaa321df54643fe28c87ff5090ffca121df94243fea84877d5090ff8a121ffd0d43efa1a87fe4350f7c86a1ffd4543bfa8a87f75150eeea2a1ff94543fea8a87fc5150ef8a2a1fd14543ba28a87ff5050efea0a1fed4143bda8287fe5050ffaa0a1ff14143be28287f85050ef0a0a1df95043bf29887ff4310f7e8621ff90c43ef21887fd4310f7a8621f750c43ffa8887fe5110efca221ff54443bea8887fc5110ffea021ff94043bf28087fd5010efaa021ff14043ffa9e83fe53d06fca7a0ff54f41bea9e83fc53d07fe87a0ff90f41fea1e83fc43d07fea5a0ff94b41bf29683fd52d06faa5a0ff14b41ffa1683ff50d07fca1a0df94341fea86837d50d07f8a1a0df55241ffa9c83fe53906fca720ff54e41bea9c83fc53907fe8720ff90e41fea1c83fc43907fea520ff94a41bf29483fd52906faa520ff14a41ffa1483fe42906fca320ffd0641dfa0c83f741907fea120ff94241bf28483fd50906faa120ff14241ffa9a837f53507bea6a0d7d4d41ff29a83fd53507f8a6a0df14d41ee29a835c53507fe86a0ff90d41fea1a83fc43507fea4a0dfd4941f7a92836f52507fca4a0ff54941fe292837c52507d8a4a0db14941ffa1283fe42507fa84a0ffd0541fba0a83fe415077c82a0ffd4141bfa8283fb50506f6a0a0ff94141fea8283fc50506f8a0a0fe14141bc282837e54107fea620ff94c41bf29883fd53106faa620ff14c41ffa1883fe43107fa8620ff10c41ffa9083fe52106fca420ff54841bea9083fc52107fe8420ff90841fea1083fc421
  | 4 => 0xadc000d442d903a0888154f8001fb8000000415da9125cd946976e1040000018340006d5c0895d20c008001b3a151ebc000445f08001740aa15c9df4000000864000ea21c86bd3e80000b9f04e6d1a9628d4c4400f8ece144671add2f0fa400072d6e8000bdc000991df21bd61cc91c589640000000001080001e1848ffce9d944d48000000350faa2080000012c8000001c88001e983d544c000001120550000960000000ff80c80004f1a8029c000000dc09e0000719eb87688980000000011b40021246a1a905a1a319c8284000000000000000c180011407880008a4f580016202e4000000000000ce00000004a40002a8000000000001f200019a80784e41c0900001c8c001d500007313500003d8a28001de0eb4558850ba8c50979ed9cd4ee84786900650047d4cd0f780003103800b4b70000ed80000a9e121d0000000000b30001fcc824000000000001229d9e239b21e609852600008f000023c0014286d80020a88280000000011e5e04001aa80000000000017116b1e58161b31d80a9c9804c0000001a75169c280012e4000000000000000001a21078031e00001a40d2e0d80014785f9ba438c0000000000000000020555c61087ac8419616c101cd3ca785894803e5bd0001b99f8159c000001bc40020b00012a00000009540007d18d4c45109a28ae8001b90001fe9080000418f382295b821857c4ec0000000007fa0e1bb8179150370be19d155a2319e83b0241025368bb000223458e1b8c100000000000bd4e83fa111d38279ca014ce90ad5f516c92007f1018bf12b8364b405d0001cb11d40000000e800000000015c378af8ef8001550000001cb90dc000000001330000704bbc000000a38000000000000001b68000000cf90200004008c1a2433175d0e00000014240011dc00000401c00401000000400000800400000000000400000800000000000000400002c00400000000001c00001c00001000001000000005802801c00001401400800800000001400000c01400000000000c00800801c00000800000800400000000400001400002800000000800000400401c00800000c00000800000800000000c01400000000c01400000000000000401c00000401401000000000000800802000400000001000c01002000800000000000401400000400002800800000000800000800002800400000000000000000001000002400800400000000400000400800400001001c00000c00001000000000000800800400000000001001800400000000000001402400800001000000400800c00000800403000005400800402c01c00000000001800400000000000400400000400800000c00402400401000801000c00800c00000000400000800c01400400001400c00c00000402c00c00000403400000800000000800003
  | 5 => 0xc00000056100800000015800071cfd6118c34d207e9f180007bc000a20a41c840000017a2148002244000000a084046e8e41fbc00094185800143c001d587cc5119317d1c783280000000010140002b8819804001011240000d68678d18239ff21a1ec0001d940000000015317754387c8d65c407585c0001ab00009380000000017f880913c000001e48a940000000022280004fe22c001d71f580002d4000374000000000aa4000251cdc000d74000000000bb92f40000000000015dc0000000000003859806dc0cd290c1c82d4719885a86a8000880870fb00010f10c112cd780000004d01480018221a4000af5e0c000000000001668000001ba8000051528000001100000001c20c4c0000000000001e80018a9b600000018f0002200000ce9e095b0e48bc5dd8430150000e780013199490ce1c46980000000000000000000000009180000007b8000e883ecca8000ca0908001738001c980009a01000000014e0a620440000006b1ca9658b280004c5dc80011597e1510001180001e30001248e543b98b1660040e18000002020b887c00005fdf108ba218000000cc0000001d9800008c000001878000000c60000615b5542c621ad000000000000000077a1c0ec4000de80001b4091758000c70f01748bf56f9b64001b1111c1d1c001fc001f68000eacd6020da5000027c001b50000000408000fadf91600001650002050000000000000000199cf800110c000d080000007b4080301ed0000001d60002179491a84001e880006f0000931b78000000000c39da1998001b583c1360001a942c00005d80000000000000000000000011b8000aa8e94acd1182f9bbde90a680000017d53012b21f1b28450000000000000000000000b38ab86e1aba0b8d1c00000000036cc14000b121e00015ec0013100011b000042818893ced01417c00009d9598be4dfa24d110000000508638ba0a740000000020e96892c499d068000661798ad03902100000019280006cc0000000000010e9028000000fd8000000001390584000cda0c80014b20c0000000500bec000000a18002070000000b215887b00000000003a88fa139624a90000da0000001ef4000001d49348000000be8e711341110a0000fe20f09b9610000d560080000001540013a1dc00000000009f93f9ad80001cd6800609c800029496c8a80000019780b0000000001430000f300003380000000000000000000004cc000e280000000000000000021417955a8c30000000001c50000fdcb90ac54400002e0001a2c000000649324001d117e5e500000018e80946c1561b4a0fc002121b000000000000007104be0980015d540c0000000014d80000021900015e46180008614a8521ce0001f31e70b80fe400000000000213c000001bc0000fd0d88085cc4002169850001af10e4000
  | 6 => 0x1890000000e382addf8000000000000b481c89b00000008e0bcc001a3c2f03dc56d869d900000018a1c1a1b12a92f8e5d1c80017b1718000231a8c001160ee4000001410000220bd15c00001800000010b0000f6a11d5ac00013c001188ec0000000848000000001c386800017280000000000000011480005c80011f0001d20000000000000518002011d68000000000270001104439e280018315a4e112ac0000000000000000008011fc000000291950000001871809a10000000ef00000000000000000440000004d4001209f7212800000000000000000000128097c000e8d7f0c880d8b9a04cc21288000000000001fb12bca713e1811919c7c001a692c00a4000208000000d58000000000651972080488001fd8000361bd9ec8db0aed97c7c4971250fb40008a00000000000000018e00d222400213046150a0594c92980009c04a9d89bac000000001c480007480000011c400191004c000000454000000000f2193ca840000012702010f4d24d8d7cd2d5791000c815cc000708001404000000000001ac0d14001a795906f4000000944000740b680019b0000000eb837c000d300000000000003c86280000000000005690fc8c8000e7c000948001ff800000131c000001a58000a480000000000000000004597a88740006e4f800000000000010f80000000003d0000b08000999e8188a028001570000001408e8606000133a0000000000012180982980f02b4000abc000d9a12c000dc80013140016d9581fc12e8000000280000398000e812200006a42580000009e800199000170a038cf1ae1058000000000000000001fd15482a4000c3c0000009100000000000000000013f001800141400000177c6f80000000000000018e40000000000000004b056400213578dbf90605f15f9ea8000890e2194d828c0800078219e1819f8001e40001860000000001618000000bc9c68000001b5df481d9a88000668000134498000000000728000470000d7c0019c0001f2855c000000f88fb9e6898d32c0000000000c0aac000001cf2068fc8ac8ec94d14a1304bc1800001459cc8000000000001388348000001b1812c6c49898bd445ef883a05d7f4715b89c81ae97650ed8b80000003e11780015f0000f94001ee8ab53c9eb0001d7a0a0c011e930d4f1dd0000000ea472019d3d817000160c128000000000000000ab16e0028001231768000dd00005e00000004d8001308e755bc0013b80000020f8f50358000000000000e010400000016940007e028d908000000000000e980019682cc0005480000000003080000000021600000000000000000000011bc000000600798000000000448088a50001f0c000001214000000000001654000000000b501210b91c00000001b000009e100000001435938001be9569c71f98f290
  | 7 => 0x3217e8000054001f61ef00004c8b19340ed4001f88640000929542078d509583a0ae2170000001400000000000000001114da8000000ebc000000000001604001c909696a8d854b8f603680006100001a0002030d0d2040004b80007a9170000000000a8d4c1128000001500f106892dca7d210934000574000000000000c2c000a991cc00203ddb20915458c96b8000bd8001a70e08000f70ae52e0000000000000000000000db99b8cc8d284681440000000000000007a4000000000000000000000002019f380000008e89d0de01a8dd9a60000f418d0001958c25778190571648000000000000070000000000000000000000288001448001e79c60b0079c8302c9a1d27921c0595a0001898000000000001fb5ea0659cd1460000000001be00017816d1328a58000000d5e18a0492fc4ac00081035c000000000001f011980000006d09740000017000000000010495f470d720000000000000000cb22498cc0015e800006c5413596146b87d941d640000000000f900003550d8000000665c11b811f40000000000000004a18dc1696099e1d31421e380004e0000fe9050001fc8002034000994001698001fa80000006740015e00000000019f10d0df0000bd61d8000e60c99538d700000000016a02c40000000006fc000001ba0a300000001180017b8f9cfecff0a115b4c04000000000000d380018f88b000210c2d03200001b80011917dc000000000e58000001070cb8951ce80000000019540000000000003421e9f797ec000000001c30c40ff52580011d11a0000001690af09f1a98000000000001fc4d807900018c18382e96380001300000000003b40011e1b70001db8001fa082000000024a1b50321159200017619a00005f40e08693d00020d00000000000022100017704e91ac4b55d0fcc529098000c58000001d19ee223c00000000000049cb783ea1581acedc000734001131e21efc5380007a1818000001a38074000000001d08000c488d1238000000000ad95d800000075000000000000005d6312ee1a84f8010000000000000001b40000000000a88000c0c000001a7d2d9b08f18eb1578000000410001bb00017311f95213805b0b60d350894880000000000a0000000000000000389bc80002ec0000000000000009a400094ca800006080003f12d00017c9af82600000000000005980000000000000005ea240d113c00018c40011ec0010921acfbc002220f497850c80000000000000000207700000007005940000006ed9d9ccc000000001f400000000000021f93b00000000006040000000015180016f0bf800000000081cfc4000001378000000858590e50164000000000000000c68000000000000000000000001dfc0000004816641bc00196cfc00010d4000000000d90000000000000318c2800000141800
  | 8 => 0x9a80021989205b8578a00001d4000060ce65aa06308d8761a34269ac8000000000001b6c001bf53991d8000000490000000000c78b58001751bb4e680001f16787380000001c407dd00ea9a48000049900581a002bc0000008882b0000ee0fa0835499fe0878000000069de80000000000000000018400000019400013a8002040039138531e180000000000012cc000001d290a9268421aadbf01f9a9c2a1a098d8001880f98d6cbfc000000000000274000494f080000000016700000000000017d9a18000000001cc00014500000006c9370000000ac0e30000000000d40139788d01
  | _ => 0
def gbK5 : Nat → Nat
  | 0 => 0x531042ef624c410bb189310427f650c4109f594310435e530c410d754c3104376510c410f54c431042fa600c410be580310427d65c8410dd947210427f65884109f596210436e5288410db54a21042fa6088410be582210427f6548410b7d8d21042dc63484109fd94210427d6508410db948210436d5208410dd94421043e52108410be98021042f960084109f992500427d64940109f98e500435e63940109798e500427d6394010d758e500425d63940109f98a500436e62940109b98a500427d6294010db58a500426d62940109f58650043774194010dd106500427d65d0010be597400437965d0010ded53400437954d0010de94f400437853d0010de94b400437852d0010fcd8740042f961d0010fc187400437a51d0010fcd0740043f041d00109fd96400427d6590010cf952400433d5490010bd98640042f56190010be982400427f6550010b7d8d40042dc6350010bbd8940042ec6250010bdd8540042f461500109fd94400427e65100109f594400427c6510010cf950400433d5410010b798c40042dd6310010bb98840042ed6210010bd98440042f56110010be594400437965100109e59440042fa6410010ee990400437b5410010ee95040043795410010ee55040043da6310010f658c400437a5310010de14c40043ea6210010fa588400437a5210010de14840043f26110010be58440043f16110010de94440043f34110010fc104400427d65cc010d7d4f300435c53cc0109fd96300427d658c010d794e300435d538c010bb98a30042ed628c010bd98630042f5618c0109fd95300435f534c010d714d300427f650c0109f994300427d650c0109f194300435e530c010d754c30042f6610c010bd584300427d65c8010dbd4b200427f65880109f59620042de6388010b758e200436e5288010db54a20042f66188010bd586200427f6548010dbd49200427e65080109f594200427c6508010bd98420042f56108010dd59710042f664c4010bd193100437754c4010dd553100437653c4010dd14f100437652c4010dd14b10043f340c4010fc10310042de6384010b758e10042ee6284010bb58a10042f56184010dd94610042f96584010de59610042796584010be99210042f86484010f698e10043d96384010fa98a10043e96284010be586100437a5184010fc94610043f34184010fc106100427f6544010bdd95100437765440109dd9510042f66444010bd19110043775444010dd55110043765344010dd14d10043765244010dd14910042f76044010dd94110043f34044010fc10110043f23044010fc4c110043f22044010fc48110042fb6544010ded95100427b6544010be99110042f86444010bed8510043f36144010de94510043f25144010fcd0510043f04144010fc8c510043f13144010fc88510043f12144010
  | 1 => 0x427e6294c109f58a530427f6454c109f191530435f6354c109fd89530427c6254c109fd85530427d6154c109fd81530427d6054c10d754c530427e6414c109f590530427e6314c10d798c530427e6214c109f588530427e6114c10dd984530427e6014c10de980530427f65d0c109f997430427d65d0c109f197430435f53d0c10d714f430427f6590c109f996430427d6590c109f196430435e5390c10d754e43042f66190c10bd58643042fa6090c10be582430427f6550c109f995430427d6550c109f195430435e5350c10d754d43042ef6250c10bb18943042f76150c10bd18543042fb6050c10be181430427f6510c109f994430427d6510c109f194430435f5310c10d714c43042de63d4810b758f520427e64d48109f593520427e63d4810d798f520425e63d48109f58f520435d63d48109758f520437661d4810de983520427d6594810dbd4a520427e64948109f592520427e63948109f58e520427f64548109f191520427f63548109f18d520436f62548109fd85520427d6154810db548520427e64148109f590520427e63148109f58c520427e6114810dd984520427e6014810de980520427f65d08109f997420427d65d08109f197420436f52d08109fd96420427e65908109f596420427c6590810db94a420436d5290810bd98642042f56190810be98242042f960908109fd95420427e65508109f595420427c6550810b7d8d42042dc6350810db949420436d5250810bdd8542042f46150810bed8142042f860508109fd94420427e65108109f594420427c6510810dbd48420427f65cc8109f997320427d65cc8109f197320436e52cc810db54b320427f658c8109f996320427d658c8109f196320435e538c810d754e320427f654c8109f995320427d654c8109f19532042f7614c810bd185320427f650c8109f994320427d650c8109f194320435e530c810d754c320436e520c810db54832043cd320c810bd98432042f5610c810be98032042f9600c8109f992510427d64944109f98e510427d63944109f58a510427d65d0410bd597410437565d04109d597410437754d0410dd553410437653d0410dd14f410437652d0410dd14b41043f360d0410bd58341043f060d04109fd96410427d6590410cf952410433d5490410bd98641043765190410be98241042f960904109fd9541042df6350410b718d41042ef6250410bb18941043765150410bed81410427f65104109f594410433e5410410cf55041042fa6010410be580410437565104109d59441042f66410410ed99041043775410410ed95041043755410410ed55041043765310410dd14c41043765210410dd14841043f26010410bd58041043f160104109f597310437651cc4109fd96310427d658c410d794e310435d538c410be98231042f9608c4109fd9
  | 2 => 0x64c8510bd593214437654c8510dd15321442f663c8510bd18f214437653c8510dd14f214437752c8510f9d4b21443e452c8510bd98321443f260c8510bc98321443f160c85109f996214436e5288510db54a21442f66188510b7d8d21442dc6348510dbd49214436c5248510bed8121442f860485109f994214436e5208510f948421442f66508510dd99421442f76408510bd59021443765408510dd15021442f66308510bd18c21443765308510dd14c21442f66208510f998821443775208510f994821443755208510f954821443655208510f9d0821443e44208510f9cc821443e43208510bd980214427e65d0110cfd53404433c54d0110bd98740442f561d01109f996404427f65501109f595404427c6550110cfd51404433c5450110b7d8d40442dc6350110bbd8940442ec6250110bdd8540442f461501109f99440442de6310110b758c40442ee6210110bb58840442f66110110bd584404427e65cc110d7d4f304435c53cc110bd98730442f561cc110f50c7304427e658c110bb98a30442ed628c110bd98630442f5618c1109fd95304427d654c1109f195304435f534c110d714d30442f7614c110bd18530443d4314c1109f99430443d9300c1109f997204436f52c8110db14b20442f661c8110bd58720443e421c8110b798e20442dd6388110bd98620442f561881109f595204427c6548110bdd8520442f46148110f9085204437a54c4110de15310443f241c4110fc50710443f331c4110fc0c710443f321c4110fc08710442de6384110b758e10442ee6284110bb58a10442f76484110bd59210443765484110dd15210442f66384110f598e10442d66384110f558e10442f46384110bd98a10443e66284110b998a10443e56284110fcd42104427e63d50109f58f540427e62d50109f58b540427e61d5010dd987540427e60d5010de983540427d6595010cfd52540427e63950109f58e540427e62950109f58a54042df6355010b718d54042ef6255010bb189540433f64550109fd8d540435f635501097d8d540427c6355010d718d540425c63550109fd89540436f62550109bd89540427c6255010db189540426c62550109fd85540427d6155010dd185540427f60550109f58154043786055010cf55054042de6315010b758c54042ee6215010bb588540427e6415010cf990540427e6315010d798c540425e63150109f58c540435d63150109758c540427e6215010db988540426e62150109f588540436d62150109b588540427e6115010dd984540427661150109f980540437a6015010bb98b53042ed62d4c109f993530427d64d4c109f98b530436e62d4c109b98b530427d62d4c10db58b530426d62d4c109f987530437661d4c109d987530427e60d4c10de983530427d6594c10d7d4e530427e6494c109f592530
  | 3 => 0x9109f58f524437561d4910dbd4a524427e64949109f592524427e63949109f58e52443756194910de58252442bf6454910af19152442df6354910b718d524427f6454910cfd91524423f64549109f191524433c64549108f191524427f6354910d7d8d524425f63549109f18d524435c63549109718d524437761549109fd81524437b60549109f994524436d52149109f990524427d64149109f98c524427d6314910db988524427c61149109fd97424427e65d09109f597424427c65d0910dbd4b424436c52d0910bd98742442f561d09109fd96424427e65909109f596424427c6590910cfd52424433c54909109fd95424427e65509109f595424427c6550910b7d8d42442dc6350910bdd8542442f46150910bed8142442f860509109fd94424427e65109109f594424427c6510910cfd50424433c5410910dbd48424436c5210910bd98442442f56110910be98042442f960109109fd97324427e65cc9109f597324427c65cc910dbd4b324436c52cc910bd98732442f561cc910be98332442f960cc9109fd96324427e658c9109f596324427c658c910d7d4e324435c538c910bd98632442f5618c910be98232442f9608c9109fd95324427e654c9109f595324427c654c910bdd8532442f4614c9109fd94324427e650c9109f594324427c650c910d7d4c324435c530c910dbd48324436c520c910f34c8324427e65d0510cfd53414433c54d0510be98341442f960d05109f99641442f66590510dd99641442766590510bd59241443765490510dd15241442f66390510bd98a41442f660905109f195414433f5450510cf15141442df6350510b718d41442ef6250510bb18941442fb6050510be181414437465505109d19541443b76450510edd5141443765450510dd15141443b45450510f5d8d41442f46350510f518d41442d46350510f9d8941442f46250510f918941442e46250510fcd8141442f46050510fc18141442f060505109f99441442f661105109f997314435f53cc510d714f31442fa60cc510be583314437665cc5109d99731442f764cc510bd593314437654cc510dd153314437753cc510f5d4f314437553cc510f514f31442f662cc510dd94b314437452cc510bd98331443f260cc510bc98331443f160cc5109f996314435e538c510d754e31442f6618c5109f195314435f534c510d714d31442ef624c510bb18931442fb604c510be181314427e650c510d794c314435d530c510f54c431442f6650c510dd99431442f7640c510bd5903144376540c510dd15031442f6630c510f598c3144377530c510f594c3144375530c510f554c3144355530c510f5d0c31443d4430c510bd9883144376520c510dd14831443d6320c510f50c831442f6600c510dbd4b214436c52c8510be98321442f960c8510dd99721442f7
  | 4 => 0xd58640842df6350210b718d408435e5350210d754d40842ef6250210bb189408436e5250210db54940842f76150210bd185408433e5410210cf55040842de6310210b758c408435e5310210d754c40842ee6210210bb588408436e5210210db54840842f66110210bd584408435e53cc210d754f308436e52cc210db54b308435e538c210d754e30842ee628c210bb58a308436e528c210db54a30842f6618c210bd586308435e534c210d754d308436e524c210db549308435e530c210d754c308436e520c210db54830842f6610c210bd58430843d9300c210d794f208435d53c8210db94b208436d52c8210d794e208435d5388210bd98620842f56188210d794f108435d53c4210db94b108436d52c4210bd597108437565c4210bd99310842f464c4210ddd53108437554c4210dd94f10843d653c4210d594f10843d553c4210dd14f108437652c4210f994b108436652c4210f954b10842f965c4210de597108437a54c4210de15310843da53c4210f654f10843ea52c4210fa54b108427e63d51109f58f544427e62d51109f58b544433f54951109f992544427e63951109f58e544427e62951109f58a544427d6195110dd586544427d6095110de58254442df6355110b718d54442ef6255110bb189544433f64551109fd8d544435f635511097d8d544427c6355110d718d544425c63551109fd89544436f62551109bd89544427c6255110db189544426c62551109fd85544437761551109dd85544427f6055110ded81544427b60551109f994544433d5415110cf990544427e63151109f58c544427e62151109f588544427e6115110dd584544427c61151109f980544427c60151109f993534427d64d4d109f98b534427d62d4d10dd587534435f5394d109f992534427d6494d109f98e534427e6294d109f58a534427d6194d10dd586534427d6094d10de58253442bf6454d10af19153442ef6254d10bb189534427f6454d10cfd91534423f6454d109f191534433c6454d108f191534435f6354d109fd89534436f6254d109bd89534427c6254d10db189534426c6254d109fd8553443776154d109fd81534437b6054d109f994534435d5314d109f990534427d6414d10d798c534427e6214d109f588534427e6114d109f184534427e6014d109f180534427f65d0d109f997434427d65d0d109f197434435f53d0d10d714f43442f661d0d10bd587434427f6590d109f996434427d6590d109f196434433f5490d10cf152434427f6550d109f995434427d6550d109f19543442ef6250d10bb18943442f76150d10bd18543442fb6050d10be181434427f6510d109f994434427d6510d109f194434433f5410d10cf150434435f5310d10d714c43442f66110d10bd58443442fa6010d10be580434427e64d49109f593524427e63d4
  | 5 => 0x528436f6454a10db991528436d6454a10db191528436f6354a10db98d528436d6354a10db18d528436f4354a10db90d528436d4354a10db10d528436d6154a10db981528436c6054a10b798c52842dd6314a10d794c528435d5314a10db548528427f65d0a109f997428427d65d0a109f197428435e53d0a10d754f428436e52d0a10db54b428427f6590a109f996428427d6590a10d794e428435d5390a10db94a428436d5290a10bd98642842f56190a109fd95428427e6550a109f595428427c6550a10b7d8d42842dc6350a10d794d428435d5350a10db949428436d5250a10bdd8542842f46150a10bed8142842f86050a109fd94428427e6510a109f594428435e5310a10d754c428436e5210a10db54842842fa6010a10be580428427f65cca109f997328427d65cca109f197328435e53cca10d754f328436e52cca10db54b32842fa60cca10be583328427f658ca109f996328427d658ca10d794e328435d538ca10db94a328436d528ca10be98232842f9608ca109fd95328427e654ca109f595328427c654ca10d794d328435d534ca10db949328436d524ca10bdd8532842f4614ca109fd94328427e650ca109f594328435e530ca10d754c328436e520ca10db54832843cd320ca10bd98432842f5610ca10cf953418433d54d0610d794f418435d53d0610db94b418436d52d0610be98341842f960d0610dd597418437754d0610ed953418437554d0610ed553418437653d0610f594f418435653d0610f554f418437453d0610dd94b41843e652d0610d994b41843e552d0610fc98341842f560d0610fc583418435e5390610d754e418436e5290610db54a418433e5450610cf55141842df6350610b718d418435e5350610d754d41842ef6250610bb189418436e5250610db54941842fb6050610be181418435e5310610d754c418436e5210610db54841842f56510610dd59441843b66410610ddd5041843755410610dd94c41843d65310610d594c41843d55310610dd14c41843765210610f994841843665210610f954841842f56010610d794f318435d53cc610db94b318436d52cc610be98331842f960cc610d794e318435d538c610db94a318436d528c610d794d318435d534c610bbd8931842ec624c610db949318436d524c610bed8131842f8604c610d794c318435d530c610db948318436d520c610f54c4318435e53c8610d754f218436e52c8610db54b21842fa60c8610be583218435e5388610d754e218436e5288610b7d8d21842dc6348610d794d218435d5348610db949218436d5248610bed8121842f86048610d794c218435d5308610db948218436d5208610f9484218435e53d0210d754f408436e52d0210db54b408433e5490210cf552408435e5390210d754e408436e5290210db54a40842f66190210b
  | 6 => 0x27e63d5210d798f548425e63d52109f58f548435d63d52109758f548427e62d5210db98b548426e62d52109f58b548436d62d52109b58b548437561d5210de983548433f54952109f98e548427d63952109f98a548427d6295210cfd91548427f63552109f18d548427f62552109f18954843776155210cf55054842de6315210b758c54842ee6215210bb588548433e64152109f98c548435e63152109798c548427d6315210d758c548425d63152109f988548436e62152109b988548427d6215210db588548426d6215210dd584548437a6015210bb98b53842ed62d4e109f993538427d64d4e109f98b538436e62d4e109b98b538427d62d4e10db58b538426d62d4e10dd587538437a60d4e10d7d4e538427e6494e109f592538427e6294e109f58a538435f5494e10d7952538435d5494e10d7152538435f6494e10d7992538435d6494e10d7192538435f6294e10d798a538435d6294e10d718a538435f6194e10d7586538435e6094e10d7182538427f6454e109f191538435f6354e109fd89538427c6254e10d7d95538435f5454e10d7951538435d5454e10d7151538435f6454e10d7991538435d6454e10d7191538435f6254e10d7989538435d6254e10d7189538435f6154e10d7585538435e6054e10d7181538435d5314e10bb98853842ed6214e109f990538427d6414e10d798c538427e6214e10db988538426e6214e109f588538436d6214e109b58853843756114e10de980538427f65d0e109f997438427d65d0e109f197438435e53d0e10d754f438427f6590e109f996438427d6590e109f196438435e5390e10d754e43842f66190e10bd586438427f6550e109f995438427d6550e109f195438435e5350e10d754d43842ef6250e10bb18943842f76150e10bd18543842fb6050e10be181438427f6510e109f994438427d6510e109f194438435e5310e10d754c43842fa6010e10be58043842de63d4a10b758f528435e53d4a10d754f528427e64d4a109f593528427e63d4a10d798f528425e63d4a109f58f528435d63d4a109758f528437a60d4a10d794e528435d5394a10dbd4a528427e6494a109f592528427e6394a109f58e528436f5494a10db952528436d5494a10db152528436f5394a10db94e52843ce5394a10d394e528436d5394a10f354e528434d5394a10db14e528436f6494a10db992528436d6494a10db192528436f6394a10db98e528436d6394a10db18e528436f4394a10db90e528436d4394a10db10e528436f6194a10db586528436e6094a10db182528435e5354a10d754d528427f6454a109f191528427f6354a109f18d528436f6254a10dbd95528436f5454a10db951528436d5454a10db151528436f5354a10db94d52843ce5354a10d394d528436d5354a10f354d528434d5354a10db14d
  | 7 => 0x50cb109f59432c427c650cb10d7d4c32c435c530cb10f34c832c42fa600cb10be58032c433e5490710cf55241c42fa6090710be58241c43756590710dd95241c43b65490710ed55241c43745490710bd98e41c42f66290710bd98241c43f26090710fc58241c42df6350710b718d41c42ef6250710bb18941c42f86050710bdd9541c43776550710edd9141c43765450710dd15141c43d76350710bd18d41c43d46350710b518d41c43e76250710bd18941c43e46250710b918941c43f36050710bd18141c43f06050710bc18141c433e5410710cf55041c42fa6010710be58041c42f565cc710dd59731c42f764cc710bd59331c437654cc710dd15331c437753cc710dd54f31c42f662cc710dd94b31c437452cc710bd98331c435e538c710d754e31c42fa608c710be58231c42ef624c710bb18931c435e530c710d754c31c43d5310c710be98031c42f9600c710dd59431c42f7640c710bd59031c4376540c710dd15031c43d6630c710ddd4c31c43d6530c710dd54c31c43d5530c710d554c31c43d7430c710f510c31c42f6620c710dd94831c4374520c710f58c831c43d4320c710bd98031c43f2600c710fc58031c42f565c8710dd59721c42f764c8710bd59321c437654c8710dd15321c42f663c8710bd18f21c437653c8710dd14f21c437552c8710bd98321c436e5288710db54a21c42fa6088710be58221c42df6348710b718d21c436e5208710db54821c43e52108710be98021c42f96008710bdd9021c42f56408710dd95021c43745408710bd98c21c42f46308710dd94c21c43745308710f998821c43e65208710dd54821c43e55208710d954821c43e74208710f910821c43e73208710f90c821c42f66008710fc98021c43f16008710cf95340c433d54d0310bd98740c42f561d0310be59740c437965d0310ded5340c43ba54d0310de55340c43b954d0310de94f40c437853d0310de94b40c437852d0310fc98740c42f961d0310fc58740c43f241d0310fc50740c43f331d0310fc0c740c43f321d0310fc08740c433e5450310cf55140c42df6350310b718d40c42ef6250310bb18940c42f76150310bd18540c42de6310310b758c40c42ee6210310bb58840c42f66110310bd58440c42f96510310de59440c43ba6410310ded5040c43795410310f698c40c43d96310310de94c40c43785310310fa98840c43e96210310de94840c43785210310fc98440c42f96110310fc58440c42f16110310fc90440c43f14110310fccc440c43f03110310fcc8440c43f02110310d794f30c435d53cc310bd98730c42f561cc310f50c730c42ee628c310bb58a30c42f6618c310bd58630c435e534c310d754d30c42f7614c310bd18530c43d4314c310bd98720c42f561c8310f908720c42de63d5210b758f54842ee62d5210bb58b5484
  | 8 => 0x3097d95300c2de644c030b7191300c35f544c030d7551300c35e514c030b7d81300c35e504c030f6d01300c3d8404c030bed95300c37b654c0309ed95300c2fa644c030be191300c2fb634c030f6d8d300c37a534c030f694d300c3db434c030f610d300c3db314c030f64c5300c2de63d5310b758f54c42ee62d5310bb58b54c427e63d5310d798f54c425e63d53109f58f54c435d63d53109758f54c427e62d5310db98b54c426e62d53109f58b54c436d62d53109b58b54c437661d5310de58354c433f54953109f98e54c427d63953109f98a54c427d6295310dd98654c433f64553109fd8d54c427c63553109fd8954c427c6255310ded8154c433d5415310cf99054c427e63153109f58c54c427e62153109f58854c43766115310de58054c427e64d4f109f59353c427e62d4f109f58b53c437661d4f10de58353c435f5394f109f99253c427d6494f109f98a53c427d6294f10bbd8953c42ec6254f109fd9153c427c6454f10d7d8d53c427f6254f10dbd8953c426f6254f109f18953c436c6254f109b18953c43746154f10d754c53c42ee6214f10bb58853c427e6414f109f59053c435e6314f109f98853c436e6214f109b98853c427d6214f10db58853c426d6214f10dd98453c43796014f109fd9743c427e65d0f109f59743c427c65d0f10d794f43c435d53d0f10bd98743c42f561d0f109fd9643c427e6590f109f59643c427c6590f10be98243c42f96090f109fd9543c427e6550f109f59543c427c6550f10bbd8943c42ec6250f10bdd8543c42f46150f10bed8143c42f86050f109fd9443c427e6510f109f59443c427c6510f10d794c43c435d5310f10bd98443c42f56110f10dbd4a52c427e6494b109f59252c427e6394b109f58e52c42df6354b10b718d52c427f6454b109f19152c427f6354b10d7d8d52c425f6354b109f18d52c435c6354b109718d52c42de6314b10b758c52c436d5214b109f99052c427d6414b109f98c52c435e6314b109798c52c427d6314b10d758c52c425d6314b10dd98452c43796014b109fd9742c427e65d0b109f59742c436e52d0b10db54b42c42f661d0b10bd58742c427f6590b109f99642c427d6590b109f19642c42fa6090b10be58242c427f6550b109f59542c427c6550b10b7d8d42c42dc6350b10bdd8542c42f46150b10bed8142c42f86050b109fd9442c427e6510b109f59442c427c6510b10db94842c436d5210b10bd98442c42f56110b109fd9732c427e65ccb109f59732c435e53ccb10d754f32c42f661ccb10bd58732c427f658cb109f99632c427d658cb109f19632c435f538cb10d714e32c436e528cb10db54a32c42f6618cb10bd58632c427f654cb109f59532c427c654cb10d794d32c435d534cb10db94932c436d524cb10bdd8532c42f4614cb109fd9432c427e6
  | 9 => 0x185540c2746155030de181540c33d5415030bd984540c2f561150309f990540c33e64150309f98c540c35e63150309798c540c27e6115030dd984540c27661150309f584540c37561150309d584540c27e6015030de980540c27e6494c309f592530c27d65d0c30b7597430c35d65d0c3097597430c35f54d0c30d7553430c3db60d0c30b7583430c3d860d0c309fd96430c27d6590c30cf952430c33d5490c30b798e430c35e5390c30be982430c2f96090c309fd95430c35e5350c30bdd85430c2f46150c30bed81430c27f6510c309f594430c33e5410c30cf550430c2fa6010c30be580430c35d6510c3097594430c2de6410c30e7990430c35f5410c30e7950430c35d5410c30e7550430c3da6010c30b7580430c3d96010c30bb98b510c2ed62d4430ddd46510c27e64944309f592510c35f4394430d710e510c27e62944309f58a510c27f64544309f191510c27f62544309f189510c37551144309fd97410c27e65d04309f597410c27f65904309f996410c27d6590430b798e410c2dd6390430dd946410c3755190430be982410c2f960904309fd95410c27d65504309f195410c2df6350430b718d410c2ef6250430bb189410c3765150430dd545410c2fb6050430be181410c27f65104309f994410c27d6510430dd947310c37551cc430be983310c2f960cc4309f596310c35e538c4309fd95310c2ef624c430bb189310c35e530c430dd944310c375510c430f54c4310c2fa600c430be580310c27f65884309f996210c27d6588430db94a210c36d52884309fd95210c27d65484309f195210c2df6348430b718d210c27f65084309f994210c27d6508430b798c210c2dd6308430dd944210c3755108430f9484210c2fa6008430be580210c27e64940309f592500c35f4394030d710e500c3766194030dd586500c27d65d0030be597400c37965d0030ded53400c37954d0030f6d8f400c2f963d0030f618f400c37a53d0030f6d0f400c3d843d0030de947400c27f65900309f596400c33e5490030cf552400c2de6390030b758e400c2fa60900309fd95400c2df6350030b718d400c2f76150030bd185400c27f65100309f994400c27d65100309f194400c33e5410030cf550400c2de6310030b758c400c2f66110030bd584400c2f96510030de594400c2796510030be990400c3ba6410030ded50400c3ba5410030de550400c3b95410030f698c400c2f96310030f658c400c37a5310030f6d0c400c3d84310030fc984400c3f16110030de944400c2de64cc030b7193300c35f54cc030d7553300c35e51cc030f6d03300c3d840cc030b758e300c35e538c030bd986300c2f5618c030be992300c2f8648c030be58e300c37a538c030f694e300c3db438c030f610e300c3f2618c030fc586300c27f654c030b7d95300c35f654c0
  | 10 => 0x44c33d5415130cf990544c27e6315130d758c544c27c63151309f984544c27d61151309f997434c33f54d0d30cf153434c2fa60d0d30be583434c27e6590d30b7996434c35e6590d3097996434c2dd6490d30d7952434c35c5490d30b7986434c2de6090d309f195434c33f5450d30cf151434c2f76150d30bd185434c2fb6050d30be181434c35c6550d3097195434c39f6450d30e7d51434c35e5450d30d7151434c39c5450d30f5d85434c2dc6150d30f5185434c2d46150d30f6d81434c2dc6050d30f6181434c2d86050d309f994434c2de6310d309f993514c27d64d45309f98b514c27d62d4530ddd46514c2bf6454530af191514c2ef6254530bb189514c37551145309f990514c27d64145309f988514c27d62145309f997414c27d65d05309f197414c2de63d0530b758f414c37751d0530dd147414c27e65905309f596414c27c6590530cfd52414c33c54905309fd95414c27e65505309f195414c2df6350530b718d414c2ef6250530bb189414c2fb6050530be181414c27e65105309f594414c27c6510530cfd50414c33c5410530b798c414c2dd6310530ddd44414c3745110530be980414c2f960105309f997314c377518c530dd146314c2fa608c530be582314c2df648c530b7592314c35e548c530d7152314c2de628c530d714a314c2de618c530d7d46314c3d7518c530f5146314c2de608c530f6982314c2da608c530f6582314c2ef624c530bb189314c377514c530dd145314c2fb604c530be181314c27e650c530f54c4314c2de650c530d7994314c2df640c530b7590314c35e540c530d7150314c2de620c530d7148314c2de610c530f5984314c35f510c530f5944314c3d5510c530f5d04314c3d4410c530b7980314c27e65885309f596214c27c6588530b798e214c2dd6388530dbd4a214c36c5288530f30ca214c2fa6088530be582214c27f65485309f995214c27c6548530b7d8d214c2dc63485309f994214c27d65085309f194214c2df6308530b718c214c3775108530dd144214c3d43108530f9484214c27e65d0130cfd53404c33c54d0130b798f404c2dd63d01309f996404c27f65501309f595404c27c6550130cfd51404c33c5450130b7d8d404c2dc6350130bdd85404c2f461501309f994404c2de6310130b758c404c2f66110130bd584404c37a54cc130de153304c3da43cc130f650f304c3da31cc130f60c7304c2f6618c130bd586304c2df648c130b7592304c35e548c130d7152304c2de618c130f5986304c2d6618c130f5586304c3db508c1309f98f540c35e63d50309f987540c27d61d50309f983540c37a60d50309f596540c33f54950309f986540c27d6195030bdd85540c2f46155030cfd91540c27f63550309f58d540c35c63550309fd85540c37761550309dd85540c27c6155030dd
  | 11 => 0x7d6294630ddd52518c3765494630dd552518c3745494630f5d0e518c3d44394630ddd4a518c3765294630f994a518c3665294630ddd92518c3766494630dd592518c3746494630ddd8e518c3774394630d5d0e518c3764394630dd50e518c3744394630d510e518c3776294630dd98a518c3756294630dd18a518c3766094630dd182518c36e52546309fd91518c27c64546309fd89518c27c6254630ddd95518c3775454630dd951518c3755454630dd151518c3d74354630f510d518c3775254630dd949518c3e65254630d9949518c3755254630f9549518c3655254630ddd91518c3766454630dd591518c3746454630dd58d518c3774354630dd90d518c3754354630dd10d518c3776254630dd989518c3756254630dd189518c3766054630dd181518c2ee6214630bb588518c36e5214630db548518c37551146309fd97418c27e65d06309f597418c36e52d0630db54b418c37651d0630dd547418c27f65906309f996418c27d6590630b798e418c2dd6390630db94a418c36d5290630dd946418c37551906309fd95418c27d65506309f195418c2df6350630b718d418c2ef6250630bb189418c36e5250630db549418c3765150630dd545418c2fb6050630be181418c27f65106309f994418c27d6510630db948418c36d5210630dd944418c3755110630be980418c2f96010630db94b318c36d52cc630dd947318c36e528c630db54a318c376518c630dd546318c2fa608c630be582318c2ef624c630bb189318c36e524c630db549318c376514c630dd545318c2fb604c630be181318c36e520c630db548318c375510c630f54c4318c27f65886309f996218c27d6588630db94a218c36d5288630dd946218c3755188630be982218c2f960886309fd95218c27d65486309f195218c2df6348630b718d218c3765148630dd545218c27f65086309f994218c27d6508630b798c218c2dd6308630dd944218c3755108630f9484218c37651d0230dd547408c33e5490230cf552408c2de6390230b758e408c3765190230dd546408c2df6350230b718d408c2f76150230bd185408c3765150230dd545408c33e5410230cf550408c2de6310230b758c408c2f66110230bd584408c3765110230dd544408c37651cc230dd547308c2dd65cc230d7597308c2de64cc230b7193308c35f54cc230d7553308c35e51cc230f5947308c35651cc230f5547308c2f965cc230de597308c37a54cc230de153308c3f251cc230fc547308c27e61d51309f587544c33f54951309f992544c27d6395130d758e544c27e61951309f586544c27d6095130de582544c2f76155130bd185544c33f64551309fd8d544c35f635513097d8d544c27f6155130ddd85544c27761551309f185544c37461551309d185544c27f6055130ded81544c27b60551309f9945
  | 12 => 0x10f30cf55043cc2fa6010f30be58043cc37751947309f99251cc27d64947309f98a51cc27d6294730bbd8951cc2ec62547309fd9151cc27c64547309fd8951cc36f62547309bd8951cc27c6254730db18951cc26c6254730bb98851cc2ed6214730dd54451cc27f65d07309f99741cc27d65d0730b798f41cc2dd63d0730dd94741cc37551d07309fd9641cc27e65907309f59641cc2fa6090730be58241cc27f65507309f59541cc27c6550730b7d8d41cc2dc6350730bbd8941cc2ec6250730bed8141cc2f860507309fd9441cc27e65107309f59441cc2de6310730b758c41cc3765110730dd54441cc37651cc730dd54731cc2fa60cc730be58331cc2dd658c730d759631cc2df648c730b759231cc35e548c730d715231cc2de628c730d794a31cc35d518c730b798231cc2ef624c730bb18931cc376510c730dd54431cc3d5310c730be98031cc2f9600c730b7d9031cc2dd640c730d795031cc35c540c730b798831cc35e520c730f598431cc3d6510c730d754431cc3d5510c730d554431cc3d7410c730f510431cc2de600c730f698031cc3d9600c7309fd9621cc27e65887309f59621cc2de6388730b758e21cc3cc3288730dd94621cc37551887309fd9521cc27d65487309f19521cc2df6348730b718d21cc3765148730dd54521cc27f65087309f99421cc27d6508730b7d8c21cc2dc6308730f50c421cc3e52108730be98021cc2f96008730cf95340cc33d54d0330b798f40cc2dd63d0330be59740cc37965d0330ded5340cc3ba54d0330de55340cc3b954d0330f698f40cc2f963d0330f658f40cc3da43d0330f650f40cc37a51d0330f68c740cc3d831d0330cf95140cc33d5450330b7d8d40cc2dc6350330bdd8540cc2f46150330b798c40cc2dd6310330bd98440cc2f56110330be59440cc3796510330ee99040cc37b5410330de55040cc3da6310330be58c40cc3d96310330b658c40cc3da4310330f650c40cc3f26110330fc58440cc37a5110330f68c440cc3d83110330bd987548c2f561d5230d758f548c27e61d5230dd987548c27661d52309f587548c37561d52309d587548c37a60d5230cfd52548c27e61952309f586548c33f6455230d7d8d548c27f61552309f185548c33d5415230bd984548c2f56115230cf990548c35d63152309f984548c37661152309d984548c27d6115230dd584548c2756115230de980548c33e54d0e30cf553438c2fa60d0e30be583438c35d65d0e30d7d53438c39e54d0e30d7553438c39d54d0e30f6983438c2dd60d0e30f6583438c33e5450e30cf551438c2f76150e30bd185438c2fb6050e30be181438c2dd6510e30d7594438c39e6410e30d7d50438c35d5410e30b7580438c2ee62d4630bb58b518c37751946309f992518c27d6494630d7d0e518c35c43946309f98a518c2
  | 13 => 0x9fd9541102df6350440b718d411035e5350440d754d41102ef6250440bb189411036e5250440db54941103765150440bed81411035e5310440d754c411036e5210440db54841103765110440dd54441102fa6010440be580411027f65cc4409f997311027d65cc440d794f311035d53cc440db94b311036d52cc440dd947311037551cc440be98331102f960cc4409fd96311027e658c4409f596311035e538c440d754e311036e528c440db54a3110376518c440dd54631102fa608c440be582311027f654c4409f595311027c654c440afd9131102bc644c440d794d311035d534c440bbd8931102ec624c440db949311036d524c440dd9453110375514c440bed8131102f8604c4409fd94311027e650c4409f594311035e530c440d754c311036e520c440db5483110376510c440dd54431103d5310c4409fd96211027e65884409f596211035e5388440d754e211036e5288440db54a21103765188440dd54621102fa6088440be582211027f65484409f595211027c6548440afd9121102bc6448440b7d8d21102dc6348440d794d211035d5348440dd94521103755148440bed8121102f860484409fd94211027e65084409f594211035e5308440d754c21103765108440dd54421103e52108440d794f401035d53d0040dd947401037551d0040e794f401039d53d0040ed94740103b551d0040af592401033e5490040d794e401035d5390040dd94640103755190040be592401037a5490040ee95240102fa6390040f694e40103d95390040be98640103f25190040fc546401027f6550040b7d8d40102dc6350040d794d401035d5350040bdd8540102f46150040dd94540103755150040afd95401033f65500408fd95401039f6350040e718d401039e5350040e754d40103b76150040ed18540103b65150040ed54540102bf6050040cf94140102fb6550040ded95401027b6550040bed9140103bb6450040de95140103ba5450040f6d8d40102f86350040f618d40102d86350040f694d40103d95350040fcd8540102f86150040fc18540102f06150040fc94540103f15150040bd98754cc2f561d5330d798f54cc27e61d5330dd98754cc27661d53309f58754cc37561d53309d58754cc37960d5330cfd5254cc35e63953309f98654cc27d6195330cfd9154cc27f61553309f18554cc37b6055330cf55054cc33e6415330d798c54cc27e61153309f58454cc3796015330cf95243cc33d5490f30be98243cc2f96090f30d759643cc35e5490f30e795243cc39d5490f30d715243cc2de6190f30b798243cc3da6090f30f658243cc2f76150f30bd18543cc2f86050f30b7d9543cc35f6550f30e7d9143cc35e5450f30d715143cc3d76150f30b718543cc3d46150f30b518543cc3db6050f30b718143cc3d86050f30b618143cc33e54
  | 14 => 0x453150374514c5409f994315027d650c5409f194315035f530c540d714c315036f520c540db1483150377510c540dd14431503d5310c540be98031502f9600c5409f996215027d65885409f196215035f5388540d714e215036f5288540db14a21503775188540dd146215027f65485409f995215027c6548540b7d8d21502dc6348540d7d4d215035c5348540ddd45215037451485409f994215027d65085409f194215035f5308540d714c21503775108540dd14421503e52108540be98021502f96008540d7d4f405035c53d0140ddd47405037451d0140f6d4f405037853d0140f614f405035853d0140fcd47405037851d0140fc147405037051d0140d7d4e405035c5390140ddd4640503745190140e7d4e405039c5390140edd4640503b45190140eed4240502f661d4c40bd587531035f5394c409f986531027d6194c40f6182531035c6494c40d7d86531035e6194c40d7586531035c6194c40d7982531035c6094c409fd85531027c6154c40de181531035f6554c40f6181531035e6454c40d7d85531035e6154c40d7585531035c6154c40d7981531035c6054c40d6181531035c4054c40b798c531035d5314c40bd98453102f56114c40d794f431035d53d0c40be98343102f960d0c409f596431035d5390c409fd95431035e5350c40bdd8543102f46150c40bed81431035e5310c40d754c43102fa6010c40be58043102de63d4440b758f511035e53d4440d754f51102ee62d4440bb58b511035e5394440d754e511037751944409f98e511027d63944409f98a511027d6294440ddd4e51103765394440f594e51103565394440dd54e51103d55394440d554e51103745394440ddd4a51103765294440f994a51103665294440fc18251103746494440ddd8e51103766394440dd58e51103746394440ddd0e51103764394440dd50e51103744394440ddd8a51103766294440dd58a51103746294440dd98251103746094440d794d511035d5354440db949511027f63544409f18d511027f62544409f18951103786054440ddd9551103775354440dd94d51103d65354440d594d51103755354440f554d51103555354440dd14d51103775254440dd94951103e65254440d994951103755254440f954951103655254440fc18151103766454440ddd8d51103766354440dd58d51103746354440ddd0d51103764354440dd50d51103744354440ddd8951103766254440dd58951103746254440dd98151103746054440dc18151103744054440b798c51102dd6314440d794c511035d5314440bb98851102ed6214440db948511036d5214440bd98451103755114440d794f411035d53d0440db94b411036d52d0440dd947411037551d0440be98341102f960d04409f596411035e5390440d754e411036e5290440db54a4110375519044
  | 15 => 0x9027f65886409f996219027d6588640db94a219036d52886409fd95219027d65486409f19521902bf6448640af19121902df6348640b718d219027f65086409f994219027d6508640dd94421903755108640f948421902fa6008640be58021902bd65d0240cf59740902f965d0240de597409037a53d0240de947409027e61d4d409f587535035f64d4d40d7d87535035e61d4d40d7587535035c61d4d40d7d83535035d60d4d40d7d4e53502f66194d40bd58653502f76154d40bd185535035d5314d409f984535027d6114d40b7994535035e6514d40d7d90535035f6114d40d7984535035d6114d40d7184535035f6014d40d7580535035d4014d409f997435035c53d0d40d7d4e435035c5390d40be98243502f96090d40d7d4d435035c5350d40bdd8543502f46150d40bed8143502f86050d409f994435035f5310d40d7d4f515035c53d45409f98f515027d63d45409f98b515027d62d4540ddd4f51503d753d4540d5d4f515037653d4540dd54f515037453d4540f514f515035453d4540ddd4b51503e752d4540d9d4b515037764d4540ddd8f515037663d4540dd58f515037463d4540ddd0f515037643d4540dd50f515037443d4540ddd8b515037662d4540dd58b515037462d4540ddd83515037560d4540b798e51502dd6394540d7d4e515035c5394540bb98a51502ed6294540dbd4a51503775194540b7d8d51502dc6354540d7d4d515035c5354540bbd8951502ec6254540dbd49515035f5314540d714c515036f5214540dd544515027e63145409f58c515027e62145409f58851502f66514540dd99451503775314540f5d4c51503575314540dd94c51503755314540dd14c51503d45314540d514c51503775214540f9d4851503675214540dd94851503755214540dd14851503e45214540d914851503776414540ddd8c51503766314540dd58c51503746314540ddd0c51503764314540dd50c51503744314540ddd8851503766214540dd58851503746214540ddd8051503756014540dd500515027e65d0540d7d4f415035c53d0540dbd4b415036c52d0540dd147415035f5390540d714e415036f5290540db14a41503775190540dd14641502fa6090540be58241502df6350540b718d415035f5350540d714d41502ef6250540bb189415036f5250540db14941503775150540dd14541502fb6050540be181415027e6510540d7d4c415035c5310540dbd48415036c5210540ddd44415027e65cc5409f597315027c65cc540d7d4f315035c53cc540dbd4b315036c52cc540ddd47315037451cc5409f996315027d658c5409f196315035f538c540d714e315036f528c540db14a3150377518c540dd146315027f654c5409f995315027c654c540d7d4d315035c534c540bbd8931502ec624c540dbd49315036c524c540ddd
  | 16 => 0x76348421f1d8d21087e66348421b998d21087e56348421f918d21086e46348421f118d21086c46348421f9d4d21087e65348421f954d21087e45348421f9d0d21087e64348421f950d21087e44348421f9d8121086e76048421f998121087e56048421f918121086de63d4021b758f50087e521d4021b798e50086dd6394021f9486500877b50940219f992500867d64940219f98e500875e63940219798e500867d6394021d758e500865d6394021ddd0650087744194021f9485500867f64540219f191500867f63540219f18d50087773154021dd0c550087e52114021de540500875f5394f409f98653d027d6194f40bdd8553d02f46154f409fd8553d03776154f409dd8553d027c6154f40dd18553d02746154f40ded8153d035d5314f40d794f43d035d53d0f40be98343d02f960d0f40bdd8543d02f46150f40be18143d035e5310f40d754c43d02fa6010f40be58043d037751947409f98e51d027d63947409f98a51d027d6294740b7d8d51d02dc6354740bbd8951d02ec62547409fd8d51d035f635474097d8d51d027c6354740d718d51d025c63547409fd8951d036f62547409bd8951d027c6254740db18951d026c6254740ded8151d03755114740dd94741d037551d0740be98341d02f960d0740b7d8d41d02dc6350740bbd8941d02ec6250740be18141d03765110740dd54441d02fa6010740be58041d027f65cc7409f99731d027d65cc740be98331d02f960cc7409fd9631d027e658c7409f59631d02fa608c740be58231d027f654c7409f59531d027c654c740bbd8931d02ec624c740bed8131d02f8604c7409fd9431d027e650c7409f59431d03d5310c7409fd9621d027e65887409f59621d02fa6088740be58221d027f65487409f59521d027c6548740b7d8d21d02dc6348740bed8121d02f860487409fd9421d027e65087409f59421d03e52108740bd98753902f561d4e40d7d4e539027e6194e409f586539027f6154e409f185539035d5314e40d794e439035d5390e40be98243902f96090e40d794d439035d5350e40bdd8543902f46150e40bed8143902f86050e40b798f51902dd63d4640bb98b51902ed62d4640ddd46519027e63946409f58e519027e62946409f58a519027f63546409f18d519027f62546409f18951903755114640dd94641903755190640be98241902f96090640b7d8d41902dc6350640bbd8941902ec6250640dd94541903755150640bed8141902f860506409fd97319027e65cc6409f597319037651cc640dd547319027f658c6409f996319027d658c640d794e319035d538c6409fd95319027d654c6409f19531902bf644c640af19131902ef624c640bb189319027f650c6409f994319027d650c640d794c319035d530c640dd9443190375510c640f54c431902fa600c640be58031
  | 17 => 0x4c21d754c530867e6414c219f590530867e6314c21d798c530867e6114c21dd984530867e6014c219f580530867f65d0c219f997430867d65d0c219f197430875f53d0c21d714f43086f661d0c21bd587430867f6590c219f996430867d6590c219f196430875e5390c21d754e43086f66190c21bd586430867f6550c219f995430867d6550c219f195430875e5350c21d754d43086f76150c21bd18543086fb6050c21be181430867f6510c219f994430867d6510c219f194430875f5310c21d714c430867e64944219f592510867e63944219f58e510867d65d0421bd597410877565d0421ddd53410877554d0421bd98f410877653d0421dd14f41087e762d0421bd58b41087e462d0421dd94b41087e742d0421bd583410867f65904219f596410873e5490421cf55241086ee6290421bb58a41086f661904219fd9541086df6350421b718d41086ef6250421bed8141086f860504219fd94410867e65104219f594410867c6510421cf950410873d5410421bb98841086ed6210421bd594410877565104219d59441086f66410421ed99041087775410421ed95041087755410421ed55041086f66310421dd94c41087745310421f998841086f56210421f958841086e56210421dd94841087e74210421f910841086f560104219f59731086f565cc421dd59731086f664cc421bd193310877654cc421dd153310877753cc421dd54f31087e762cc421bd58b31087e462cc421dd94b31087e742cc421f910b31087e732cc421bd583310867f658c4219f596310875e538c421d754e31086ee628c421bb58a31086f6618c4219fd9531086ef624c4219fd94310867e650c4219f594310867c650c421d794c310875d530c421bb98831086ed620c421f54c431086f5650c421dd5943108675650c421bd99031086f4640c421dd9503108774540c421bd98c31087d6630c421ddd4c31087d6530c421dd54c31087d5530c421d554c31087d7430c421f510c31087e6620c421bd58831087e5620c421b95883108776520c421f9d0831087e4420c421f9cc831087d6320c421f50c831087e4320c421f10c831086f5600c421bd99221086f46488421bd98e21086f46388421bd58a21086e56288421dd94a21087e65288421f9d0a21087e44288421f9cca21087e43288421bd582210867f6548421b7d8d21086dc6348421bdd95210877765484219dd9521086f66448421bd19121087d76348421bd98d21086f46348421f518d21086d46348421bdd8921087765248421f994921087e74248421f990921087e54248421f910921087e73248421f98c921087e53248421f90c921086f76048421f9d9521086e76548421d9d9521087e76448421f999121086e66448421f959121087e46448421b919121087e75448421f995121087e55448421f915121087e
  | 18 => 0xd7d8d534867f6154d21ddd8553486776154d219fd81534867c6054d219f994534875d5314d219f990534867d6414d21d798c534867e6014d219f58053486de6514d21d7994534865e6514d21d7d50534875e5414d21d7550534875c5414d21d7d90534875e6414d21d7590534875c6414d21d7d84534875d6114d21d7484534875f6014d21d7980534875d6014d21d7180534867f65d0d219f997434867d65d0d219f197434875f53d0d21d714f434867f6590d219f996434867d6590d219f196434875f5390d21d714e434867f6550d219f995434867d6550d219f195434875f5350d21d714d43486f76150d21bd18543486fb6050d21be181434867f6510d219f994434867d6510d219f194434875f5310d21d714c43486f66110d21bd584434867e65d0521cfd53414873c54d0521d7d4f414875c53d0521bb98b41486ed62d05219f996414875f5390521d714e414867f65505219f595414867c6550521cfd51414873c5450521b7d8d41486dc6350521d7d4d414875c5350521bbd8941486ec6250521bed8141486f860505219f994414875f5310521d714c414867e65cc521d7d4f314875c53cc521bb98b31486ed62cc5219f996314875f538c521d714e314867f654c5219f595314867c654c521d7d4d314875c534c521bbd8931486ec624c5219f994314875f530c521d714c31487d5310c521d7d4e214875c5388521db952214876c5488521f3d4e214876e5388521db14e21487cc5388521d314e21487e75188521d7d4f504875c53d41219f993504867d64d41219f98f504867d63d4121db88750486de6394121b758e504875f5394121d714e504877b5094121afd9150486bc6454121b7d8d50486dc6354121d7d4d504875c5354121d7d4c504875c5314121de540504867e64141219f590504867e63141219f58c504867e63d50219f58f540867e61d5021dd987540867e60d50219f583540867d6595021cfd52540867e63950219f58e540867e60950219f58254086df6355021b718d54086fb6055021be181540873f64550219fd8d540875f635502197d8d540867c6355021d718d540865c6355021dd185540867f6055021ded81540867b60550219f181540877860550219e181540873d5415021b798c54086dd6315021be98054086f960150219f990540873e64150219f98c540875e63150219798c540867d6315021d758c540865d63150219f984540877661150219f980540877a60150219e980540867d6015021de58054086796015021be98353086f960d4c219f993530867d64d4c219f987530877661d4c219f983530877a60d4c219e983530867d60d4c21de583530867960d4c219f596530875f5394c219f992530867d6494c219f982530867d6094c219fd91530867c6454c21d7d8d53087746154c219fd81530867c605
  | 19 => 0x5438867c6550e21bbd8943886ec6250e21bdd8543886f46150e21bed8143886f86050e219fd94438867e6510e219f594438867c6510e21d794c438875d5310e21bd98443886f56110e21cf953428873d54d0a21bd98742886f561d0a21db597428876f54d0a21eb953428876d54d0a21eb55342886ee63d0a21db94f428876c53d0a21f998742886ed61d0a21f958742886ed60d0a21cf951428873d5450a21b7d8d42886dc6350a21bdd8542886f46150a21bed8142886f86050a21bb594428876d6510a21eb990428876f5410a21db55042886ee6310a21db94c428876c5310a21bb58442886ed6010a21d794f328875d53cca21bd98732886f561cca21db59732886ee64cca21bb193328876e54cca21db153328876f53cca21f394f328876d53cca21f354f32887e661cca21bb58732887e561cca21bb583328875f538ca21d714e328875e534ca21d754d32886f7614ca21bd185328875f530ca21d714c32887cd320ca21bb594328876d650ca21bb99032886ec640ca21db950328876c540ca21f398c328876f530ca21f3d4c328874f530ca21db54c32887cc530ca21f3d0c32887cc430ca21bb58432886ed600ca21cf952418873d5490621bb98a41886ed6290621b7d8d41886dc6350621bbd8941886ec6250621bed8141886f86050621cf950418873d5410621bb98841886ed6210621d794e318875d538c621bb98a31886ed628c621f30ca31886ef624c621bb189318875e530c621d754c31886ee620c621bb58831887cc320c621f54c431886f565c8621dd597218877654c8621dd153218877653c8621dd14f218877b50942219f992508867d64942219f98e508867d6394221dbd0a508876c42942219fd91508867c64542219fd8d508867c6354221dbcc9508876c3254221ddc8550886de6314221b758c508877950142219f98f544867d63d51219f983544867d60d5121cfd5254486de6395121b758e544867e64951219f98e544875e63951219798e544867d6395121d758e544865d63951219f586544877561951219f982544867d6095121b7d8d54486dc6355121bed8154486f86055121cfd91544867f6355121d7d8d544865f63551219f18d544875c63551219718d544867f6155121ddd85544867761551219fd81544877b60551219ed81544867c6055121de181544867860551219f994544873d5415121cf990544867e63151219f58c544867e60151219f580544867e64d4d219f593534867e60d4d219f583534875f54d4d21d7953534875d54d4d21d7153534875f64d4d21d7993534875d64d4d21d7193534875f61d4d21d7587534875f60d4d21d7983534875d60d4d21d7183534875f5394d219f992534867d6494d219f98e534865e6394d219f58653487756194d219f982534867d6094d219fd91534867c6454d21
  | 20 => 0xc7765310431f5d0c410c7d44310431bd988410c7765210431f58c8410c7d43210431bd580410c6de64cc431b7193310c6de62cc431f5d07310c7d441cc431b7583310c6dd638c431d794e310c6f6648c431bd192310c6f5638c431b558e310c776538c431f594e310c7d7438c431f510e310c6f6628c431f58ca310c7d4328c431bd582310c67f654c431bbd89310c6ec624c431b7d95310c75f654c43197d95310c6de644c431b7191310c7cf624c431b7189310c7cc624c431b3189310c6df614c431d7945310c7d7414c431f5905310c7d5414c431f5105310c6df604c431bdd95310c777654c4319dd95310c6f6644c431bd191310c6f7634c431f5d8d310c776534c431f594d310c7d7434c431f590d310c7d5434c431f510d310c7e7624c431bd189310c7e4624c431b9189310c7d7324c431f58c9310c7d5324c431f50c9310c6f7604c431f5d95310c6d7654c431d5d95310c7d7644c431f5991310c6d6644c431f5591310c7d4644c431b5191310c7d7544c431f5951310c7d5544c431f5151310c7d7624c431f1d89310c7d6624c431f5589310c7d4624c431b5189310c7c4624c431b1189310c7d7524c431f5949310c7d5524c431f5149310c7d7424c431f5909310c7d5424c431f5109310c7d7604c431b5d81310c7d6604c431f5581310c7d4604c431bb98b500c6ed62d4031f54c7500c6ee6294031bb58a500c7d53194031ded42500c67e64940319f592500c75f4394031d710e500c67e6294031db98a500c66e62940319f58a500c76d62940319b58a500c7774194031dd106500c7d531540319fd91500c67c64540319fd89500c67c6254031d78c9500c75c3254031f54c4500c7795014031b798f54886dd63d5221be98354886f960d52219f98f548875e63d52219798f548867d63d5221d758f548865d63d5221db58b548877661d52219f983548877a60d52219e983548867d60d5221de583548867960d5221cfd52548867e63952219f58e548867e60952219f582548873f64552219fd8d548867c6355221dbd89548867f60552219f181548873d5415221cf990548867e63152219f58c548876d6215221dd984548867e60152219f580548867e64d4e219f593538876d62d4e21dd987538867e60d4e219f583538875f5394e219f992538867d6494e219f982538867d6094e219fd91538867c6454e21d7d8d538876f6254e219fd81538867c6054e21d754c53886fa6014e21be580538867e6414e219f590538875e6314e21db58853887766114e219f980538877a6014e219e980538867d6014e21de58053886796014e219fd97438867e65d0e219f597438867c65d0e21d794f438875d53d0e21bb98b43886ed62d0e219fd96438867e6590e219f596438867c6590e21bb98a43886ed6290e219fd95438867e6550e219f59
  | 21 => 0x6255031bb189540c6fb6055031be181540c73f6455031d718d540c67f6255031dbd89540c66f62550319f189540c76c62550319b189540c77461550319fd81540c77b60550319ed81540c67c6055031de181540c6786055031cf550540c6ee6215031bb588540c6fa6015031be580540c67e6415031cf990540c67e6315031d798c540c67e6215031db988540c66e62150319f588540c76d62150319b588540c67e6115031dd984540c67e6015031de980540c67a60150319f580540c77960150319e580540c67e6494c319f592530c67d65d0c31b7597430c75d65d0c31d7d53430c75d54d0c31b798b430c7d761d0c31b7587430c7d461d0c31b7583430c67f6590c319f596430c73e5490c31cf552430c6de6390c31bd986430c6f56190c319fd95430c6ef6250c31bb189430c6f76150c31bed81430c6f86050c319fd94430c67d6510c31cf950430c73d5410c31bd984430c6f56110c31d7594430c65d6510c31b7990430c79e6410c31d7d50430c79e5410c31d7550430c79d5410c31b7988430c7d66110c31b7584430c7d56110c31b5584430c6dd6010c31be983520c6f960d4831dbd4a520c67e64948319f592520c75f4394831d710e520c67e60948319f582520c67f64548319f191520c77461548319fd81520c67c6054831db548520c67f65d08319f997420c67d65d0831b798f420c6dd63d0831bd987420c6f561d08319fd96420c67e65908319f596420c6de6390831b758e420c76e5290831db54a420c6f66190831bd586420c67f65508319f595420c67c6550831b7d8d420c6dc6350831db949420c76d5250831bdd85420c6f46150831bed81420c6f860508319fd94420c67e65108319f594420c76e52cc831db54b320c6f661cc831bd587320c67d658c831b7596320c75d658c831b7992320c6dc648c831d7952320c75c548c831b798a320c75d528c831f5d86320c6dd618c831f5186320c6dd608c8319fd95320c6f7614c831bd984320c6f5610c831d7950320c75c540c831f5984320c6dd610c831f5584320c6d5610c8319f992510c67d6494431d7d0e510c75c4394431d78ca510c75c32944319f597410c6f565d0431dd597410c77754d0431dd553410c7d763d0431bd58f410c7d463d0431dd94f410c7d743d0431f510f410c6f662d0431dd94b410c7d632d0431f50cb410c6f560d04319fd96410c67d6590431cf952410c73d5490431b798e410c6dd6390431bd986410c67f6550431b7d8d410c6dc6350431bbd89410c6ec6250431bed81410c6f860504319fd94410c67e65104319f594410c67c6510431cf950410c73d5410431b798c410c6dd6310431bd594410c77565104319d594410c6f66410431ed990410c7775410431ed950410c7755410431ed550410c7d66310431bd58c410c7d56310431b558c410
  | 22 => 0x131bb189544c6fb6055131be181544c73f64551319fd8d544c75f635513197d8d544c67f6255131dbd89544c66f62551319f189544c76c62551319b189544c67f6155131ddd85544c67761551319fd81544c77b60551319ed81544c67c6055131de181544c67860551319f994544c73d5415131cf990544c67e62151319f588544c67e60151319f580544c67e65d0d31cfd53434c73c54d0d31bd987434c6f561d0d319f996434c67c6550d31cfd51434c73c5450d31bbd89434c6ec6250d31bdd85434c6f46150d31bed81434c6f86050d319f994434c67e64d49319f593524c67e60d49319f583524c76f54d4931db953524c76d54d4931db153524c76f64d4931db993524c76d64d4931db193524c76f63d4931dbd0f524c76e43d4931db50f524c76c43d4931dbd87524c76d61d4931dbd83524c76e60d4931db583524c76c60d4931dbd4a524c76d52149319f990524c67d64149319f980524c67d6014931bb994524c76e6514931dbd50524c76e5414931db550524c76c5414931dbd90524c76e6414931db590524c76c6414931dbd8c524c76f4314931db90c524c76d4314931db10c524c76f6114931db4c4524c76f6014931db980524c76d6014931db180524c67e65d09319f597424c67c65d0931dbd4b424c76c52d09319f996424c67d65909319f196424c76f5290931db14a424c67f65509319f995424c67c6550931b7d8d424c6dc6350931dbd49424c76c5250931bdd85424c6f46150931bed81424c6f860509319f994424c67d65109319f194424c6de6310931b758c424c76f5210931db148424c6f66110931bd584424c76c52cc931dbd4a324c76c528c931bd986324c6f5618c931bdd85324c6f4614c9319f997414c73f54d0531cf153414c6de63d0531b758f414c76f52d0531db14b414c67e6590531dbd4a414c76c52905319fd95414c67d65505319f195414c73f5450531cf151414c6df6350531b718d414c6ef6250531bb189414c76f5250531db149414c6fb6050531be181414c67e6510531dbd48414c76c5210531dbd4b314c76c52cc531dd953314c77454cc531f9d4b314c77452cc531f914b314c76452cc531dbd4a314c76c528c531d7952314c75c548c531f3d4a314c75c528c531f314a314c74c528c531f5d46314c76f52d4131db14b504c67e64d41319f593504c67e62d41319f58b504c77731d4131d78c7504c6ee6294131bb58a504c76f5294131db14a504c77b5094131afd91504c6bc6454131bbd89504c6ec6254131dbd49504c76c5254131dbd48504c76c5214131de540504c67e64141319f590504c67e62141319f588504c67e63d5031d798f540c67e62d50319f58b540c67e61d5031dd987540c67e60d50319f583540c67d6595031cfd52540c67e62950319f58a540c67e60950319f582540c6ef
  | 23 => 0xd55341cc7d663d0731bd58f41cc7d563d0731bd98b41cc77652d0731bd58341cc73e5450731cf55141cc6df6350731b718d41cc6ef6250731bb18941cc6fb6050731be18141cc6f56510731dd59441cc7b66410731ddd5041cc7755410731bd58c41cc6f66210731dd94841cc6f56010731ded4250cc67e64943319f59250cc67e62943319f58a50cc7774194331dd10650cc67f64543319f19150cc67f62543319f18950cc6ee6214331bb58850cc7795014331bb98b548c6ed62d5231be983548c6f960d5231d758f548c67e62d5231db98b548c66e62d52319f58b548c76d62d52319b58b548c77661d52319f983548c77a60d52319e983548c67d60d5231de583548c67960d5231cfd52548c67e62952319f58a548c67e60952319f582548c73f6455231d7d8d548c67f62552319f189548c67f60552319f181548c73d5415231cf990548c75d63152319f988548c67d6215231dd984548c67e60152319f580548c73e54d0e31cf553438c6f661d0e31bd587438c75d65d0e31d7d53438c79e54d0e31d7553438c79d54d0e31b798b438c7d661d0e31b7587438c7d561d0e31b7583438c73e5450e31cf551438c6ef6250e31bb189438c6f76150e31bd185438c6fb6050e31be181438c6dd6510e31d7594438c79e6410e31d7d50438c75d5410e31b7988438c6dd6110e31b7580438c76f5294a319f992528c67d6494a31d7d0e528c75c4394a319f982528c67d6094a319fd91528c67c6454a319fd81528c67c6054a31db548528c6fa6014a31be580528c67f65d0a319f997428c67d65d0a31b798f428c6dd63d0a31db94b428c76d52d0a319fd96428c67e6590a319f596428c6de6390a31b758e428c67f6550a319f595428c67c6550a31b7d8d428c6dc6350a31bdd85428c6f46150a31bed81428c6f86050a319fd94428c67e6510a319f594428c76e5210a31db548428c6f66110a31bd584428c6f6618ca31bd586328c75e548ca31d7152328c7d6618ca31b7586328c7d5618ca31cf952418c73d5490631b798e418c6dd6390631b7d8d418c6dc6350631bbd89418c6ec6250631bed81418c6f86050631cf950418c73d5410631b798c418c6dd6310631b7597318c75d65cc631b7993318c6dc64cc631b798b318c6dd60cc631bd597318c77565cc631dd953318c77454cc631dd94b318c77b50942319f992508c67d6494231d7d0e508c75c43942319f98a508c67d62942319fd91508c67c64542319fd89508c67c6254231d78c9508c7773154231bb988508c6ed6214231de540508c67e62d51319f58b544c67e60d51319f583544c73f5495131bb98a544c6ed62951319f992544c67d6395131d758e544c67e6295131db98a544c66e62951319f58a544c76d62951319b58a544c67d6195131dd586544c67e60951319f582544c6ef6255
  | 24 => 0x53106ee6214c41bb58853106fa6014c41be580531075e53d0c41d754f43106f661d0c41bd587431067d6590c419fd9543106ef6250c41bb18943106f76150c41bed8143106f86050c41d794c431075d5310c41bd98443106f56110c41dbd4a521067e63948419f58e521067e60948419f58252106df6354841b718d521067f6354841d7d8d521065f63548419f18d521075c63548419718d521077461548419fd81521067c6054841b798c52106dd6314841db54852106fa6014841be580521076e52d0841db54b42106f661d0841bd587421067d65908419fd9542106df6350841b718d42106f76150841bed8142106f86050841bd98442106f56110841af592411073e5490441bd59241107765490441ed95241106f66390441bd98a41106f660904419fd9541106df6350441b718d41106ef6250441bb18941106fb6050441be18141106bf6550441cfd95411063f6550441e7d8d411079c6350441ebd8941107ac6250441afd85411073e5150441eed8141107b86050441bdd95411077765504419dd9541106f76450441edd9141107765450441ed95141107d76350441bd18d41107d46350441b518d41107e76250441bd18941107e46250441b918941107f36050441bd18141107f06050441bc181411077b50940419f98e501067d63940419f98a501067d62940419fd8d501067c63540419fd89501067c6254041dd90550107754154041b798c50106dd6314041bb98850106ed6214041de54050106ee62d5331bb58b54cc6fa60d5331be58354cc75e63d53319f98b54cc76e62d53319b98b54cc67d62d5331db58b54cc66d62d5331dd58754cc67e60d5331de98354cc67a60d53319f58354cc77960d53319e58354cc73f54953319f98a54cc67d62953319f98254cc67d6095331cfd9154cc67f62553319f18954cc77761553319fd8154cc67c6055331cf55054cc73e6415331d798c54cc67e62153319f58854cc77561153319f98054cc67d6015331cf95243cc73d5490f31bd98643cc6f56190f31bbd8943cc6ec6250f31bd18543cc6fb6050f31be18143cc73e5410f31cf55043cc6f66110f31bd58443cc76f5294b319f99252cc67d6494b319f98252cc67d6094b319fd9152cc67c6454b319fd8152cc67c6054b31db54852cc6fa6014b31be58052cc67f65d0b319f99742cc67d65d0b31db94b42cc76d52d0b31bd98742cc6f561d0b319fd9642cc67e6590b319f59642cc6f66190b31bd58642cc67f6550b319f59542cc67c6550b31b7d8d42cc6dc6350b31bdd8542cc6f46150b31bed8142cc6f86050b319fd9442cc67e6510b319f59442cc6de6310b31b758c42cc76e5210b31db54842cc6f661ccb31bd58732cc73e54d0731cf55341cc6de63d0731b758f41cc6f565d0731dd59741cc77754d0731ed95341cc77554d0731e
  | 25 => 0x76f60d4941db983525076d60d4941db18352506de6394941b758e525075f5394941d714e525076f5294941be98252506f96094941b7d8d52506dc6354941d7d4d525075c5354941bed8152506f86054941d7d4c525075c5314941db548525067e63149419f58c525067e60149419f58052506ee6514941db994525076f5314941f3d4c525074f5314941db94c525076d5314941db14c52507cc5314941d314c525076f6414941dbd8c525076e6314941db58c525076c6314941dbd0c525076e4314941db50c525076c4314941dbd84525076d4114941dbd80525076e6014941db580525076c6014941d7d4f425075c53d0941db14b425075f5390941d714e425076f5290941db14a42506f66190941bd586425075f5350941d714d42506f76150941bd185425075f53d0541d714f415076f52d0541db14b41507d753d0541dd14f41507d453d0541d514f41507e752d0541dd14b41507e452d0541d914b41506f560d0541d7d4e415075c5390541dbd4a415076c5290541e7d4e415079c5390541ebd4a41507ac5290541edd46415075f53d4141d714f505076f52d4141db14b505067e63d41419f58f505067e62d41419f58b505077b53d4141f6d4f505075b53d4141de94f505077953d4141de14f50507d853d4141d614f505077b52d4141fad4b505076b52d4141de94b505077952d4141de14b50507e852d4141da14b50507f361d4141fcd0750507ba41d4141ded93505077b63d4141de98f505077963d4141de18f505077b43d4141de90f505077943d4141de10f505077b62d4141de98b505077962d4141de18b505077b42d4141de90b505077942d4141ded87505077b41d4141de90750506de6394141b758e505075f5394141d714e50506ee6294141bb58a505076f5294141db14a505077b5094141b7d8d50506dc6354141d7d4d505075c5354141bbd8950506ec6254141dbd49505076c5254141d7d4c505075c5314141dbd48505076c5214141de540505067e63141419f58c505067e62141419f58850507774114141be994505077a6514141ded4c50507db5314141d6d4c505077a5314141de54c50507785314141f614c50507585314141ded4850507eb5214141dad48505077a5214141de54850507785214141fa14850507685214141fc58450507f34114141ee904505077b6414141ded8c505077a6314141de58c50507786314141ded0c505077a4314141de50c50507784314141ded88505077a6214141de58850507786214141ded08505077a4214141de508505077b6114141ded0450507734114141de90450507794114141d7d4e531067e6294c419f58a531067e6094c419f58253106ef6254c41bb189531067f6254c41dbd89531066f6254c419f189531076c6254c419b18953107746154c419fd81531067c6054c41d754c
  | 26 => 0x114043de5405010eee62d4f41bb58b53d075f5394f419f98a53d067d6294f419f98253d067d6094f419fd8953d067c6254f41ddd8553d067f6054f419f18153d075d5314f41d794f43d075d53d0f41bd98743d06f561d0f41bbd8943d06ec6250f41bd18543d06fb6050f41be18143d075e5310f41d754c43d06f66110f41bd58443d06de63d4b41b758f52d076f5294b419f98e52d067d6394b419f98252d067d6094b419fd8d52d067c6354b419fd8152d067c6054b41db54852d06f661d0b41bd58742d077b50943419f98e50d067d63943419f98a50d067d62943419fd8d50d067c63543419fd8950d067c6254341b798c50d06dd6314341bb98850d06ed6214341de54050d06ee62d4e41bb58b53906fa60d4e41be583539075f5394e419f98a539067d6294e419f982539067d6094e419fd89539067c6254e419fd81539067c6054e41d754c539075e5390e41d754e43906f66190e41bd586439075e5350e41d754d43906ef6250e41bb18943906f76150e41bd18543906fb6050e41be18143906de63d4a41b758f52906fa60d4a41be583529076f5294a419f98e529067d6394a419f982529067d6094a419fd8d529067c6354a419fd81529067c6054a41db54852906f66190a41bd58642906bd65d0641cf59741906f565d0641dd597419077653d0641dd94b41906f560d0641b798f50906dd63d4241bb98b50906ed62d4241b798e50906dd6394241bb98a50906ed6294241ded42509067e6394241d798e509065e63942419f58e509075d63942419758e509067e6294241db98a509066e62942419f58a509076d62942419b58a509077741942419fd8d509067c63542419fd89509067c6254241de540509067e62d4d419f58b535067e60d4d419f583535075f64d4d41d7d8b535075e62d4d41d758b535075c62d4d41d7d87535075d61d4d41d7d83535075e60d4d41d7583535075c60d4d41d7d4e53506ee6294d41bb58a53506fa6094d41be58253506ef6254d41bb18953506fb6054d41be181535075d5314d419f988535067d6214d419f980535067d6014d41b7994535075e6514d41d7d90535075f6214d41d7988535075d6214d41d7188535075f6114d41d7584535075d4114d41d7d80535075e6014d41d7580535075c6014d419f997435075c53d0d41d7d4e435075c5390d41bd98643506f56190d41d7d4d435075c5350d41bbd8943506ec6250d41bdd8543506f46150d41bed8143506f86050d419f994435075f5310d41d7d4f525075c53d49419f98f525067d63d49419f983525067d60d4941dbd4f52507cf53d4941d3d4f525076e53d4941db54f525076c53d4941f314f525074c53d4941dbd93525076f63d4941db98f525076d63d4941db18f525076f43d4941db90f525076d43d4941db10f525076f61d4941db5875250
  | 27 => 0x439f58a5190e7e60946439f5825190e7f62546439f1895190e7f60546439f1815190f755114643bd9875090ef561d4243bd9865090ef56194243ded425090f5f43942439f9865090f7661942439d9865090e7d6194243dd5865090e7561942439fd855090e7c6154243de5405090edd60d0d43e7d4e4350e7e62d45439f58b5150e7e60d45439f5835150fd743d4543ed90f5150f7752d4543f9d4b5150f6752d4543ddd935150f7763d4543ddd0f5150f7643d4543ddd8b5150f7662d4543dd58b5150f7462d4543ddd835150f7660d4543dd5835150f7460d4543bb98a5150eed6294543dbd4a5150f775194543be9825150ef96094543bbd895150eec6254543dbd495150efb6054543be1815150f6f5214543dd5445150f5f43145439f9885150e7d62145439f9805150e7d6014543bd9945150f766514543f5d0c5150fb64314543ddd485150fe75214543d9d485150f765214543dd5485150f745214543f91485150f645214543ddd905150f776314543ddd0c5150f574314543dd90c5150f754314543ddd885150f766214543dd5885150f746214543ddd805150f766014543dd5805150f746014543ddd475050f7451d41439f9875050e7d61d4143f6d8f5050fdb43d4143ee90f5050f7b51d4143fcd475050f7351d4143de9475050f7951d4143de1475050ff051d4143dc1475050f7b64d4143ded8f5050f7b43d4143de90f5050f7b61d4143de9875050f7961d4143de1875050ef66194143bd5865050f775194143dd1465050f7b5094143bdd855050ef46154143ddd455050f745154143ddd445050f745114143de5405050f5f43141439f9845050e7d6114143be9945050f7a6514143f658c5050fdb4314143ee90c5050f7b5114143fcd445050f735114143de9445050f795114143de1445050ff05114143dc1445050f7b6414143ded8c5050f7b4314143d6d0c5050f7a4314143de50c5050f7b6114143de9845050f796114143de1845050ebd6490c43cf9524310edd6490c43d79524310f9e5490c43b79864310ede6090c439fd954310ef76150c43bd1854310efb6050c43be1814310ebf6550c43cfd954310e3f6550c43afd8d4310f3e5350c43edd854310fb46150c43eed814310fb86050c43b7d954310f5f6550c4397d954310edf6450c43e7d914310f5e5450c43e79514310fd76150c43b71854310fd46150c43b51854310fdb6050c43b71814310fd86050c43b61814310f7751944439f98a5110e7d62944439f9825110e7d6094443bbd895110eec62544439fd895110f6f62544439bd895110e7c6254443db1895110e6c62544439fd815110e7c6054443bb9885110eed6214443dd5445110efa6014443be5805110f7b50940439f9865010e7d6194043d790d5010f5d43540439fd855010e7c6154043bd9845010ef56
  | 28 => 0x15001c000000000100100010008001001000500040020000000000000a00040020008000001c027001c0010028004000001c000000000040000000003000c00900440100044000003400000040070004003001000300a8000006c0040000005000400c001400100000000000001004400100040000038016000000200000010030000002000000600040018001001000000040010000007000c001001c0120000009000c002001400d000000100bc000000c00a000400100300020014005003001a000c01100380040018003007400f000000000300080000002001c00b0000002003400100000000014002000c00200340100024006000800d0000004001000200140000004000003c0050000000007400400000120000000000802b000000e000c01f0008011009400e0030000003000400000060000009001c0070050000005c0130000002000001200000050060009002c0000004006002c0000000000000000300040050008007001000100640070008007000801200580000028033007000f0000000000400a00000000054000000000100a400900100010000001001c000000800d00140010004000008000000080000004006001000100000160000002000400200000060004002011c000002802f004801f000400f000c00f0020002001c011000c00d0000000001400200200040014004000401a005c01e00100050004000000000c000000000540030000008000000f0000000000400a000c001000000400080000034004003000e00180260010002000001b0008001000400100000230000002000c00c0000000000c038002000000000000004000001400d000c00300bc0110044002000000800200070004005000800000100000034005003000b00440010000000000400a0018001000400700740010004004001002400240050058009001800a00000010004013003c07900000000008001000400200180080000000000c006000000e00000040000000000800000000040018001000800000040010008001008800200000030004008000c001003c00b000800b0004000000000e000c005000800a0004005001c00200000000000000000c00b006800d0000000005400a0000002001800300080030000000000000900080020000000002000c000c0080000001000c0060028000000c00b000800400040050010009002c00000000010010005bb98b51d0eed62d4743ddd4651d0e7e62947439f58a51d0e7e60947439f58251d0e7f62547439f18951d0e7f60547439f18151d0f755114743ded4250d0e7e61943439f58650d0e7f61543439f18550d0ef66114343bd58450d0f795014343af5974390f3d65d0e43b75974390f5d65d0e43b75834390eee62d4643bb58b5190efa60d4643be5835190f775194643d7d0e5190e7e62946
  | 29 => 0x740050054003001000f00080050060000001000b000404b0004005000000e00180040004004001401d0004005006400000040040060005001c000000800100080010000003002000000000080008005000c016001000300180240010004000400e000000100040040000004003c003004000500080030014003001000700040010044001006800000000060000000003c0040008018000800a000000400100030004005004c0000008001001c000000c0040014005000400d0070008000800300180020068000000400a0024000000000000300060014001002800000200000020000000c00d000000000000070000000002c002007c0050000000006000300380000000000000800000000020000012013c0070040003000c02c003800c0000000001400e0028002000001a008800100080010014000006400000000070000008001000000640000014000000000200540030004005000c01300040000004004001400300000000000000001000b00000030000031007c000000000f000c0170004001003c009000000300640020014017000000600040040010002004000100000160010006000800402900010038006001000200080040000006004c006000000a0000000001000100340050040003001400b00000030004009000005d00a000000540090028001000000100600000034001000000a00800030010002003002d001c01e0008001002c004000000100080000004000000c000001000c00000020010000001000d0000001000000000000030004000000000a00500090004000002c021000400300a8009000000300000010000000003c000004c000003c002002c001007800000000270008000000000200100050090003005000000000000004003000400b000800d0010001001c002001c015000c0050010002001800900340100010000004400000000000000002000c0070034001001c0000044006000c000001800200000000000001000800f001c000000800b000801a002c009000000b000000500040070088000000000000180010000007001000000080070008005000c0060014013004800b0000005001400000dc030000c00300380020000010000000200300060040004000000d0000008001c007001400000180010004001000001e003000000000030000000000c000000000000040000024000000c01a000002200180050018003001000000c803300100000018001001801c002800c000800700000010004001000000300040090004004000002b00040010008007000c0030008005000c001000400c0044003004400600040200000004001c0090000002000000100400160000000002800000100050000009000400000080020020004000c008001c0000004002000c00c00000010018000000000100880000000
  | 30 => 0x4007004c000000c000000c000000400400b0016000001d006c0020028000000800c0028007000000700280110028000000c006002000400000050070002000000000080090100000000c0000020001001800b000000000080040040008000800e00240050028028001c00400040020000010001c00800100000010000000801c001401400540030010003000c005003c00100000240014000002c00200fc005001c000003c01400000140010001001c002000c001000c0000000008000c0070008008004800100180000000001000000a00200170000009003800300100090000003002000000140010000000000000100000050004001000c0400008013001800000000000018001000000d000400000000160000000000800e00000000000022000000000280030010005000000a000000600000000000000000800000140050000001001c006002c0000008000000c0020000001000c0030000000000800100000110034006000800a0018003000003c000000100c00010064005003800000080000040018003c005000800400380090020001002c003001800e001c00d0004022000c010001c0000000001000000100000000008000001c0000000001001000600100070088002000400000040010004019003c000000c0040000004000000d000000a00080040008018001000000800010018001001400200100280030008001c0000010001005c00a0000007001c00000880000044006002c00000400080034001002c00200140010000007000000e0004000005001200180000050002000000e002802b0000003000c00400040010008006001c00000180000070006001000200000040020014000000a0004006001c00000000060040003001c00100000000004000002800200100090000000000800100040040004000003400400000000008002000000100000050004000002c00000700020068001000000000000000014006001c0070010003001001400080020020016000000500080010010000001c00c0000000000000300000000000003006c0000024004000800b0008003000000f007000b00140040008002001000c00000000000003004401e0004001000800000140000008011000400200000000020000009400000000130038004000c0000000000000000500080070000001001800500380000000000000000b0054006000000000100010010015003c00200340070000008008c0020038000001001700000110008003000000d0030009001000000000020000004004800800d8000002000000240010014008003c001000400100100030008008000400100000010000001003c00800040000000003000800000000010000000001800000000000004001003000200580350028000001c002000c01e008800f0000004003c002
  | 31 => 0x30000001005c008001400700c4003000000400200070008005003800e000800000180110004006000000000280010004003000000100200010000004000c0020000000002800800100020000001001400d00000020010027000800200000000000000000000400000060018004000c0010058000000401f0020006000400a00080130018001000000801040050044004000c000005000100040000060000002000a003000c001000e00180050074009002401600280000028001004400000140250000001000c01d00000030000003001c00200000000014001000000000000000018014000c009000c00000000000074010001c00200100020004015001800200140080010005001c00e000c00b0054000000000f00080020004003000c001000c0010000003000000e0004001001400300080020008000005c0010030002000c005000400c00140020004000001800200500010030002003800400c0003000000200080000004002008c00200000000000005002c00100000050004008009000100140010004007001c0000014022002800f00240000000001002c0020000004000400500080020044000003400300180050010016000800100080000008007000000000040030044002003c00d00cc0040008013003c006000401100000260020001002001000140080004005001c001000401e001800b00780020000000000c00200000010070002000001b0010001000c003002000000100020070001000001d00040070004014001c000000c0020028006000800700000020004003003400d00040010070005004c00e0068007003001300000000018005000804d000400300340000004006000c00300000020000008004800800140000008001000800100080020004002004c00c0024000000800300140030024010000000700140040004003000400100080000008000001c00100a80020000001002000400100000004003004c0000014001000400e0034001000001e0020006000c000000800000040000000002001c018000400c003400200000100048003000000900080000000000005000300180030004000000000000000050004001000000500000060000004003c0070004000002000200000120010009002400000000040024006000000000040020008000000800200240090000007000400e002800e0020007000c00000240000000001003800b002400600000040014000000000000000030070000000800000180000034024006c0080018008003c003000c004004002b0000005000c011004400700f800a001000000200000000001000001c00100010010009004c00c001000000040140020007000000100000070000000000000f000801b0000001005800a003000a000000c0004002000c000000000100000150008001005
  | 32 => 0x5000079780007f19bb800000006159f8a30f18bd546800059c0000744c6f524e807c000191c371000000025924c82a3846521c6978424cb8e96b40000000272a6ba7d200000002aa20000000a80c0006c4061e8f74c0d02c139c6d48822aec00000000000098e63e3d708fe07d100a851e76ea5802670000000000228a98c8a96853ee174ea0c7eb3d84fe9a69dbe9160000ad3e8ac5112dfd5a984f8523d7386951eb63bd83d052649beb1ba26c746852c85f68fc4cd9b8e0701b1ca0690280000f9413a622a0000dd44101d7c04d928400027380002a9c76ca8cc23a05b65a4824a00000000001bf252800000002250b04a3e407b989d82e000018269fd2cb00001c11f2a000004eb51a6e47ef0d6f76d27240000def01a1bea5e28c4200000008a100009e9000084680002c3000035b0b9624d0106a0f11565ba86c08dc1f8869540000001af03fca6b400014e600021ab649211ea61aa847c9c010144d080190800031a80002b5d6b25ae15466c7ac685f163de31e4cfe305502c4540b8e96b928620584e00e6a42688413e86c51e466225e143812edd8f24366b2aa36c33283ca2c89efab240fd800018c300000002f1800000012e4588a4c90002c030d916ec484800000015ba000077808d9eda000142200000002b7a1862fdeedea6dd9cb05220020000000b7a67e869d001e00000000000000ab9962895680000002bac0000000ad38000000800300380020028000005c00a001400200040010000009007802300080110004000000001000000000000001000400a0000000002000400dc001001c00a0014000009c001001800a005c000002000000080010020000001c004000400900100030020001000000b001400400080000008000002c003001400000040170000000000000000180050028000000400900000140008002002400300000000000000000400100180070008000000000700040050000001002800000040040028000000000c00000000008000000800a0060000000000200000000008008000400100000000008007000400c001400000000080008006001c0080000001000c0000004000000000f002c0000028000007000301640010014020001c000001c006000000100200050004023007c0000008001002c000001800000000000000000001800200000000000007001c000001000200000030020002000000f001000600000020008005006800100140010000000001c00a0000015000000f000000500040000000000000801c0014003001c0000030013001c014000400000200030000000000c00000d4017000400d000c00000000020004002001400a0024000000400300000000000021001c00000740040000000000800b0000000002c00300140060004005001c0010008004000000d00440080038001001400
  | 33 => 0x195bc000000005210002021000000000000000a7800059d0b1e0001ae0000129393eac42000097485f881441a0d0560f9e564b21b9a65c40005fbd67d345af4aace00603f1895870a922070214b4220e206a799c84878a1095b30f7b9919a06bba6be668a2d208711d52a4e0a0472d094cab4057a4335c80301a9907ec0ccc4678b688fdef089750d89412997f3c91d507e4a0c5b6d1dd400009a30a28000113ac4c0f791ce3f798f72d200000001706a7b00000001808af8893204cd5fa5cded629fea27a036a1064e82e5ab6217367e00622a6e861727f9df938a92285c7a5f10bd2d92a8410ae7971f940000cdc000242d673277a79d0000ba48000b5b0000000085f00029c4846d33e562a48fb6513ca75ec0000001ed000008f000000000a9082f3c200000001239927000004b0000000000000000005e65abf6721d3473c98b564844b0503a1555f423a21588d3684341fc1f728589ed4d2ab9a8624926101450f1e40bd5a35e4f1959c7faa2a4000248209c80002e500000001b7d0000f7239ea8919d48618b8460f07b2261a8ef2164610488c35f6dc45045f2203ca18400005967d5458b78cac4e736a7820001e3a554e86492256c30000b1a000000026400005370000000018c00016de63397c0b09028c7b30972ac4000003388c60001a5a0002d7ea14ac467e11bfe87e146c50340000001647bc0dd6c00008d600000000000c2271200008c8105822980002f3a00a8b029441375f328d117620ee89186c5a4ec2b0800067f0da600000007c5143a72f090c0002d7a0001a5b2740d8e422acdf00000000001f896fa0c6eaf100007a21b340000dba5b40000057c000000058896712c20000b8a000000000025c29ad800092399fd4c353f69398a08903d0872ec00005db800021e000000004bcbcd80008d811c200000000002cfaa990fae00000008a0982c05080002e680de8208000000064b3ee8cbb6a4d2005a904ba11b918417d99f68888d1c0731d4f36ccf0057599fe31421be7cb10f4830154a7bb170c00021f6000000042e885200001880002cd700000004ccd2de5a50bc24bd15800d40000000000015a28dc000238350080008740000bbe800035b40000002c64000159049e1d6134300006e2800000000000001ccd0000c2a5de6e9a0c51df413c4000b7f126882c8000b98c164adf190e9a11c5834f100615112f5b7a9ea028493ce4001c36017800000002b279d8e02000000063a80005050000abb04909579fce70413546759a68afc00000c4995459080006579262bb497d951392e117080007504eb022660667ea8bf05918bfa15d19f31772d5a7999e0fb866ea6ba62cb4a5b0f577a3c742395aace7f799ae63ad9181bf89505d50c745f56d795278ea205d588aa7c0e9a7c90157b5085b4026e1324e899f077e8000ad
  | 34 => 0x102609d400026808ca94c848098d80008f107babc88fe99e800008c1000008091e64c38000000020a000174c94a17779860f68a1f8000594800079c0000ae39b3e1011f7f37f000085700006c02cb7b86901277ee2d037000002b7c000b0e80000000d94000290a0001905992acb242e2992000271400006db88b827c5fc5af6780a67c993206a000000038fc3f830b2ebe0b680e494200000000e2673c4fe43e19386863df47000097c000000000011660000056000000000010ed9ef800000000000000ebc00024122f79d635aa05aa46914aa59e0b023aaacb8093c90442c1d1100023e0000000011ca574011a3c2b4a18fe57128f88861575b4c86dc11182341a2893c0001f3e87c00a878e2ea8000000000000001d39db6126d8b192300000001bd89eb0000000034eb2c1f29148a0780000a473002e650001ea83670fce00024e8b5980000001935000196100000009728000b92db404f803ee3f32544191d77b3501c0cba9c0003d3400000028af000000083b0ace53c18bcb2e8000b8e00000000000295849400000000000000391a82e0000000ada08045f6d4041ffa01c0001aaabd0e6747c41fb69c12cf48eb22be5cfd22e000295228d15a891c9caa763c000569000068d80005e780000000fea13096902a98b929f49d940000f8e19499df5eac00093780001be80008e71dea00021ca1a304f63d000000002f451fa00008d1898000004ac000030f3d7a7ce40e2ec859245b05951d76ba0a8407680000000000092c0d797408000142013c00006f84c6c000727249400000007230000a91c000000000036c000099086d40002f600002ac00002aaa00000008b613ae000000058bc6645e31f1f1f5a13166a469671c1f312d58e44a59050d883000032d8f4343c000066a9fc21639e1078b0000631a2ac00020faa0615249075fdc4aadce071a2d580002b51000148e000000000012e20850000a0d00002a900009b89c7ea538b8418156ba305d0ce0000000000000060f44a412bd35d888000056980000002d510faaab600007ea2db0000aa787b075280005a62a920000a780000000000268e0000a9000001f08b1024200003f200029da2c22c708474e0a0a4221e249000032cd6c8000000028c80000e3a1fe8f2c4aa0001b8631b033e1cf19321f2a7500000000a630b3413b060c0000f2c1d910a697400004aaaa86b2f002e72880007cd116d31900009ddc6984d980001b15e2a0000ef46dd64310b916fe8e1e97e857ab596368910427aedf212a50a7da8a8a7b92d4b00000001341f9b8caeeda2bdaa8000026969d880007879f751dd94a8b4129aa2a61da1b26ab445328338a0493ddb920260a6fa15b69e8f440ef61724b98aea46c81e72c1adbc2688f8a93d28066d28000a5207588485bcc21d2a3ea9b000004488e635297
  | 35 => 0x6510000a11000001eacd89eec2fe123d88b000280e8de90b22bfa73b5231322a35aa2cad78000b66005a7221c820000cee4a300000002f04133c0007845a120000000531956e00025ce00012c97ff59520002bf4000169aa909a9153099765869850bab2e0c1e41618b47ac0119d9ddfb428c7c25e2976a2569ee5409902000279e8c90e649bd104e45d42d52650b1206d060707903a42f7000030e4a7c84d258a41898980002f060001162064cbfe3a1889a3949d8a7c0ad5e03ddd4e672800060703d2000176a000114e9cfa7f410c98990be93af025d3c80122c080000bc08109528000028500000000000000000000073417170001b062dbaab835ad84f5550f182f10968a17a88a0c391c176997cc00004f2000278c56aad00a020808195d9f875500007d0c374a57000000017e84ba19384d10000374c0000001c55819000600004e7000000000016310002acc00000006d8619c0000000071df4a6de97f46e42ea2000140f92ad1043a4000021921b43009f4600020924fc800017f959ab40800059687ac00000000002487060157a0001ff2aa316ce32728dd6e7a14ba5e9e54a911256769683000028006ea801428880000001260858000007a80004289cce6d19d0e0002e16b9b100e22c134a27b124841c9e8e0000000196005883d0000596d71b0e32050000000000000007cde110000000000002c8a8e9abc5c21425437a7757d7e192a872942a9d95f15652f01553a42e4158be9b29a9bb023c8381ca0ffd89f1decbac968a500292a04cae205e5c6ae33c11fe54f94182101847534dc8620d11bb40a9f9c3f2ad2ab2000874ac1624b4f830ab07a6709d81a005fe622c30514fa646c15c396a37c898081aacf148a4cc5b3c6a420c83c38eb46bd18630c72ef87465e7a63f1d7f69980000000000000047600000000000121bc61d7800000003621c340002dbb0000bb60000ae40000481b8000000000cea80100000fc287a2201b9f0000cae00018c800000006ab037a7672ae29819f1ab851130673a41c96d5830bb3950f00010ca0002e948e093cca00ac6089a1ab5000241491da294906800000024feb28198010c121a2282423b212f5e00009b19fc81b072c8ab6828888468899b302e278697909cc678d4fe32c0ed003e99e468c266c00005c0000000000000000000ad4000179b49110c80000000ac1255c0e597d72fb058262791fa9cb86890bb1c288331c9e7e797b88778f105afa3f16ba1ded8f610423508c463696b8201d94158858dec2f3000098707327178000b84c00000000005c9297000000000000000b148398b2380008f384f00002d829ed800074600005a8af0b49c94ad6ab999aac206e3000073e184c5ba794a17442f59ed18e25c5115110024c041c96fa78e12c80004618000a1500002ac853a9ca28a20
  | 36 => 0x321206857cdeca903866e1185f903a31a80b3405941f20867948114d3e302fd7074000849159688fa2b62a120ce00000000002f110f5114f00010d54c3dc964f00000a6213b286a16f40000000ba25def00007ce019229a327d15849412b8000084eb8f062f046800041d0acc00009600002e5d8d50000ba84c86000000056103b03ab80009fe0683a7faddcb3c0a6e000137286258dcaf1a10b0001d288e82a9a817ad9eb0429c074cc2f05e74fb476367fc0001c9054e8c8a000000057d2dd50478e004785b227eba21a00011904054074ad90000aac138c5c59f36000286ab9d85040001f2e0b6048300001b20451ed431519be76e9d5800002cc00000000000000000000009100004aec0001090d76a37a5727ac8000abb94965ed26508b3a0a432f2e9c7a71a262d49f63000242800000000000000594125a5faa0de43509b8287866226705c771e84c104e44dc3798084b6b90f60d28c560bc835242ec73a2af80003f4056036aa4b27b005243bb061a3658000a96198ea5caa0ab7c1d3704f8df451f49b58422a20872632e2f99d157611518316acae00001860001cc2976914800012820002a5496da50231994ec00028821be65643b2164ca07a7c6a36abaa9b08ed6276abf299bc1d2000270a02e93ac00000006bb000000014838ce813a0918dee70085bc99a959e0001b6c1688538b90a9027a8992cb86d96481d630063448a38ff0000000026c9caa9c262c169c00011c50000000000000018700000000000000000030fc000ae41a9f17895405da21bc9e59fec73b11f2afa0a20b0d16aa5b4d11700020e00002b3233897a0b06965c92a8e283b6990a73a13e525ea0f8656ccd85a3a100b5ec000ba6c99f00010aa00000008f14572000135bbc926ac0000000a1400006a9400069300003c8977d33d8f1d8e017fb89f874c00000001ca83b400019f21d6828f00001e95e14eea2861c5457525140aa00009d844f5924091c00017a9b3119b4ae2ab1400000004ce91781900a365cf29bfb3aab2c90663f675796dc071800000000002c900005e6105c22a8cb20df063422400000000e3c1578000000000000020ca00000006a8000051b8d7f51c010205586be4af8000af603100001da43d58000000088e8ed878a59658b76488f6e00000008b500001c400008661b820002c280001c370001ba0133000000020563571ba2b5f400000024ae9f926a102b002a83ed37e14a8ada24880b50002e6f92800fc8db860a863acd40000858830a5469d12d960000bd7708245e000258400000000499c223234ec016a000045d1cd837ea43200004df5eb6322930ac09a108c8c00010f8555c9ac68300000001bdeaca0000000181200012fb6c095444c728e80000000376800047788603d64000af2000000000001b98000000289b00000005be8
  | 37 => 0x931d3e780000000000b9c079e635944000011a2040233eb459312302905385ba12274700000002c409a91464000122471b088800027ea00009061ed05cc0002ad6785a6767f20196866ae7e1b480001c252d600004b1181074696ddd960002bea142ad4c56b92f300000002869af2a2c000000022137f340920978022989a94aac6aaba00000000002f58000271c4a2800016e0284948408a7c95c120000000b421b3800023aa002183f000086e0c90a725936e249c980009b385da747a7c400004ab39d00000000fc85e2e0005e4a8c807815e03d40f4c15b000046565cd63a4d82000000097180006d52b2e00bc000af90f923264000919800000000000002cb6ac2a652000000000000004e3800023e20f9000000052222a60002cf8325e2d60000c824df00009e6da0f000091213440006468000000166000005349c6031504212ce000000000007160c6196a0000000000204a0e712ef5ebc00057f23344ff0dc60002d545448000788400035f80000001d1727d9e7800001b9ac891050000f0400014b100003134bf1cbf87f12423c4981aad54c339ab8a2c000273645080002f9c26b52e466838ea4e465b8000000064db16800000000009124cf400000000002b57000000000000b30000000bae0000000193e00000000002c98653e8240000c5e0000000653a6dc00000000002c7a1400c6f8f94000b4980000001192a4d800085596e573f8000a6ce9d639300001d8a48400000000001fca38819d23cda3ec09e0770134ac8c76acfbf000277464b8e2c000246b4cf00000a0c15e91f000027a157467bc22a0000000563d67c796207a8a790160e25b0e7ffa1ba0c20bba2b2288e87b906e9cfe4d400000000000fc2b9d00004c9800052518e21b119481849f4e25b2ad86dba3ff7159a754ea919c7e0c00022f13df1fca1303d28a9a47c000002be89732ad3079d98000000270c0002c4a0000000b6922c81e90ac6bc49c04892a99c3bec28e0838e326e100004d000000000000711dcd73be8d061718f9a0000000000140a00010cf00000009e0000009e4984000244a00000007b89330410c0000254000000000068b1f500001dee057400000015be00000000002c5e0002daab7e8ddb2b580004ab422e000123b47a883e0002b50a6584ed0001c5746308204a2172046e4000891800093118400001b2661f86f04d380005c75125b610000069edc623f036f685117c926934d763212e00029dcb600000a8210a8b84984d4d200008048298b01826e18b177811fde4c8da0800515ca6c4c318f6a2955b9aad010e5b0a43e1172a7430c992a1b417ff9289c31844d9789e20c734adc8e217a1a096eb253e92012c09441034a76434f8f98dd661940984a825ac027c5e6b6c276894c05523fe0c16a1b03e87e763df702a5e26d8975e664420f
  | 38 => 0x26ef9caea9c0750000000010480005348db800002f600002d26a75846bc68bbe33e1ab1b6b0b903f12bfc60400000002d3c691961c815659b39e06ea6a6000034904b36e90000088229003d18130002767b5d1e948ce1308b0aac48ade05ac02b8d1043a28db60a400029384d9200e1ce5a089b9139adca5fd80000000000000251a3fb14120001f4400018be262e2de0028000007173a3a50d3a000220477f02a30c8c5f85b0132e5789c3e3ec2e0a2929eee8602b7413d0f60a722d0cb6f552daf6ab80533a70e5ac245292665d600000000000000000000035cc0001098cc80000000757235806a65bd609400000000000002077918163700022f674e827b952175c40b80000000e84bbd8000a31aec2000000000000000000000000000000028870000000000216a8f46c7e48f4478580ac0a0002784a958000aea000000011ec1b300000000000000289342d80001876dc2b1d87b6a66000000000001ad00009db1a7634b800093200001f820d280580500171f390000000a5a2cfe96c09b4967c000647d4ea10d2e4e748c37847d972c0a85d3f2ad40006d9188cad480000001f3800000006d8dabb000258c5b103465e408ba4ba885042d0c3818c8c8514a1cfa0f31c326aa5d3098010f900007f4bc98807573a1166ff1fe69589aa448fade4629aaa02ddad2c4c518cc580047c84493f4b5aabf66941a84a5b9010b2a175879c81f2325563e9c882936a7036c5d20cec0b0a12aadf8516000274820317643b6000095480000002c5812152b900028e697edc3819f800054744180185f23108945805fe0940ca1a6b689c0006fb1a48418269269440001fe000000015f5358aaa810e8000b38978662ce7f6854034891724c08fc80dc9b80435431884400000000000fa42a480000001cf86c20000000000096740000002b4c56495865ecc76c00007da000189b376148296aa6bc31b5d68a0d9a440000c880001c1e22d2516bcfa5ea1722eae6861d2b05b118085980000454000848000000019d4858400000019eca0e80004af103200000006d40000900800000006de2a3259e05486948a829ce9cc8a763dc2de0149a8947db00a40b7181eb089e08127a1a6ad1a5fe00027ae28a11bf1ba6eea9b31bb08cc223a0002da6ba799f5221c3da1cd0590488897612e4be41ac0000110c0008431fbe45f80007771904bbc8000000094a0519f862b99efe9980f9ca96800000015b6b75853e4c6a3ba5ea80000201fda00000006aa000066ec000000000099b8e803888b7461c99985e0c92c5a027129e8c00092e0dca1f62a141aaa74562e00001b6965e00000000000000000157000009c8277c16e000000000023b800000000001aa342827aa39080000002a1a000000045a143eb140000b8742ce5a06b200952a245f20e5860062bc550af48a2d
  | 39 => 0x232000127c0001c1f4f42ba012082f37fa000045681a02ae8000a652d868e6161e000000032dd42767680002eb220035a21ad5d38e06b5a00000679f0600010040001ace17e5a10bc51e6080780009dd8bd2a0f822282987518aa0f84b9900ea41989a60000e8a43e8000ba763eb3c98546bbd2f46bcb09163369e550001c6e3551788662942670ee4910000dc20b81acc86e04362369d010000000a2e2d125218000583af3c1bf15e40001f87000137a9418000bd344aeaf01024496235c3ee000058fe1aa94d27d000028a00001bc900003ecbbac00000013508ebad4040221820000000529471400e89de4ef000000006482d700386390d6021d800079a98d0a9f2d8c0c680002c4000052d400000000003b2a57a0002758000268285e011179b92fa0cd80000001f4f0002dd700583ce9f2c00060e00004e02f4c85340003268000000101e2294000000000000000006eb91c60000231b4b80003099f782060726ad22b404dbc00000000003ca188800014da3df5a9aae78c9e841432c657d1f49c4017a00006336ba61e80878000142ec9c83400000002efe000000000010550000000000076800012fdb3853b66f980001e8164a00818060001fd88110000a4c000044f8a16737999e00014a793e2c1c0000000536c000aef0000000192800000000000000000210a810000041410ee0000b883c720740000f205f2800000014a40002cda9e5046000000000002c6c0000ca8a7c9f18039c000b08085a90c23534f618ac5e359b81800000000000000000007301fb205ca59644380003ad8c3a742225494899620000c9d752c27418f9cc127bd01a4be22c66f09b66a878e4534c80000002473862cd86ab35c3f000013800010822ac0000000060340f8ae81470000bbc07605482cd60001538000010a0efa576ac700009059b0a00019d000022418ca80005d8ef0244ea43c455056ba4c80001941e445299bc42be000098b2ee42d3a2b00214d9102718ee9971b7877c184e616940b3e2118ea21275549d19455f197829e941541379f8e0e42856131082aa44194000000004d2c0008d00c5f97e9bfaac313464bc00000002418000213e000095600000003c194e764800000001c180000e6e00029e4a4316fc122a45ab959d2d3860e3e9f789c290daaae0001aeb000230e0e49b1559e800000000007d8000022b80000001f6b4ee2ec76561d2f43a5e9a471209c0000000540087a00000000000000000271a2e1800054b00000000000897a5f4ac1ab72ab1aaf24d30c68000048e15f16b53c58000b4524680001e771e1246e01b1a4f009a316a56995ca3868102ab07be6062a050690ddf143c00081fac166b6aaa42518000a4009c7179c70661781fe0000fc07039a782f68aeea9801160dc898f22515f2949000040f5e3c0001ae66364d9
  | 40 => 0xaf0002b5b2ca2ac8121ad9c7f5000094b0dad43800000000b50a4680005bd932c6198570add8000617191696ee19047f19003669e0084b0fd400000ee304400012803f500010db0000388a1802c40000a4c9770000025a3beb3ba5ec4369fa650812cd322c45244600003cbd0cc609dfcc6b48000000130933a26c0b290e763482224000267e0ff0c445d091401c6164855a80001c2a00864e603a56f11443e9e1f2504d16a8ec8eb22a882f89920000aee0c370001b1d00001aa4ad1c3945b1c263cc85d85d963a94cc8805848c00000000000000000000000098105be00027a20000000b22800000000002178000546d4600001dd118401070c082e66b4d23c8acad106ade72c35d26129c080006430000521160ca48969100008a2256879c1b0e2eebbf090e5ff000067b844c534000085ad86c0001d6f00000000002e4c00019365fb0fa800024ac4490000000292c8dc800051f00000000000000000061300000000000b899aca2c01f406af80009d1d83a0001e1c000244e0001774a6ca8b200000007be11fd00000004ec0f52049d4722ee0b4c79221657da087200002b1197c00051405fc19800000002afca28eaf000008f200028bc84bc0000001d65320cad800027cc000168400000007ab8a4056ae08666b418215da26400000000000000776674e45aeaa67bc88a86b7950e3dd273a02a8000443000022345034b8e162505ae9900000f54c79abaa9e948947d69a03260198370430389d2f056b1068690013b46d305a49c193411cb05981631b7c57499a439fab7a363166a3258f3c0671b7934691ba1009252582a477535109691528ca2e0ad5355faea372b25c84ae9815b8f8682736ca50ba5948b2750aae05f8c1e4af5f0caf4adde08100005b2637472909bb00005ec2c716206e3182b8d6a3884008000000203241f263463eadbf66a243b36f0c41bce9db8ba0203838b473620b93ba30b80002f8a47487b02fb000078085f0e24a559dbf868cad2af3970236da4a81c02ec0987a63d2be86d893c03680b196577ca2c885391cbd11e90c47349efc00007c0a3daae8126949cb7380007b09a775b1924e000000000017466c489659332e9718216388b31406b85400000000006bf00006a880002fa0cf29bb16302f54000a7f00009d09d25000289000019e85f99e2210f19e21bc8000000108e26b8000b940000a98acce0f893970002dc00000b3c6b00000b4d89d35d980d825c21147371f7433188c4a3514080001ed200022387c6d23f900400000003dc3d9213f487805f2d680008a72a9000000004a00bf601c00006e4827774140000001eba6fe000061a1f0807629a481198b2476014c5b81d53b5e0000294a700b9f00002e019838f4908c43047ae00008c065bc00087051e8aaf87e6516594a73240006c5ce96000000077
  | 41 => 0x23043d000000000000000000000a8d8d6a4f9214c000036e03c10780001d7d28500002d611916dc829100016147832a0cb81213875acb54731800040a400000000008ae0470384845100024348a58ab34366eb10000000a6b0000bc38000a2a1f2f93f087e00000003a6003220a2f620002bd40750c5c74da14e57d936036021e675d22d252b1dac5ec80002d007820000000b78800037d80009d91ce237554680002f3836c6ec40000000000163c0002da2000083c3ce8000000089e75f9cd40000c0c000000075e89c60c5a5f0185208071296663d6ccb50c18ce02e7997d2fd00000002504902536d0000000000046b7aa9a628d38cbe0000000a8ba13b00025f6931aeec00000000000644b705fb49f529506b59b11a751e2e00014ccab782be53a0000a6385570001ac200009b78ca675f0000000a9c80004c62a886891af8197a1e4357ab530c7a75472e29f8bb307a890e40006bc6e520820000af303d8462054c9b22ada5e983f6781848452f86c8412066398c0000462c2d63790a827dcd75061d1e5059d9ba662e8266277078601e160db1110e4a265edc8f5000055ae57c0001f6d250009a0e82d5c8c6abbe00000000000aaa1108000477400079902b6366075604706a4262a69ea9b98f49d6649e3786d6eb4d2f500000356b614000260a56aa3807872bb1cd35e521b670c00ec82a00005260b0e000000027b8fd158c80003e598f200023522c100000000ea677e000000000002bc0000a0a000000004fa000000027c97ee0a9c0008161ffc1a119f4000000000000000002c7c0000f76b66880b82e9d8843b206000000a54f5aba6183811f00026726a50054adaa62a187cede0002f528ec21406422d4e6a566a026ea52ebad59b766e8fe2284000028e8420000273db8d1f709c5897d83d896a00012ee00027d644ba2340000d3876c0b2a000185823380006b40ea4000130a0001d705df800065e96bca9000007f82f003076e30033c0002ae09557452c3e0000000000219d103a93e6ee93640e180006be80008240463000129800027a82788f3e44be7ad8be91c8b3a2f1552696a31d9979a1388b14775c9668f8640a8f700004bc5d3c60d8c9456603a618c284665fad4a1ff12c72d880003821b80034800034b0000b8b8aa5801800010aa128b95162e9d187381f304b6610d2f200000001b94000006af6644d000095990207385bca00005f2733cfbe0002d220000000950818700010527c700000000000516814041b2a3252e000000000004fb400090900c096c8000096c7e47d4ec0e5d866220000000679c0000002cac000000000023647bd9f5703340e614800006bf82509730000490115e0000410000000063a25e00001a0a60504c57d600007c3920c0000aca7d514484c1980400000003f040009ae288660380004ea64
  | 42 => 0x7b292d00004d0910a85cda3da2de63cb929dd3afe9b767109e2675b6d56b91019a68e18d426680000001c5a0000000000282a2abcdcb7fe91aa4a48000a6691eea25910351d897f46dab6e23daf40000021800000660000000850e65400001f80ce9cd95e701c42af103600000e576783c04211ac84580d029b5052e332400068e54b65945ba8000000000026c5567c7220000000000287400020aa0b006782738000000000000026140698000466184935c000000000000001d5f000262400024407192f1000003820000dc54e040000282ee63bbac3c00012ca39a000002dc00000d986200000c68e4a171226c55a0381cbeb5cae7159fe9828e840007eb21680002b9641528ce1c440003a82a3ca94956c8f64c9080c080a5720f540001ee800028624290f7800005b20002e5872d8c0886c5816862a87f02f8d30996955c50b9ec43842c967e308f40001c92584000061e9e2f000000000008c20332b1226a909a116266278f80003568d4ea0b000083582827de43e62f59b9400000005b88000a5a9b2844254660eb1e8c2481c490001a5c4731933bd6a38c056665e97e0a6aa3914c00000e66b15205a00023ee22c9d16a5d208c4cfeb9a6980edca5780001f19a8e0002e0e78c48e0a23141e5c616969329ff678d00000000000b5d9c463faef4b5f09c1617ec0000001a5d38de3a8000236a58ea87cbb2a8ba8d2994d6531018590000000000000002a98a3c01058781db55ed944655bddc8af417675a5cf301d780003b4800000020fc497a74376edcca00012ec5068caf7df51229a515c684129040589df68f9d82894da4a6322400094f174463006e82349ca60948449492a6ef3cd1d0fb7318020e3462082d97f044800005dc81be524639407b10d701300000000000a978000b6fa7ca21267518ae800000000004ff5c409010df001106ab9360000000066c8268000000196c25080a200015601f88000080248a14780000000342b680000695a89c000049d00019a721a182400000004e54000337861b3ea9d9fa4718f075ca24863600000001c6a1fd80009ee000036b91d25bba87083899b21509daf0d8aa160a2086222180004531e12000000000002b455a2e460351a5771100007938109000000039762f200009980002c0b8fa5c66588d6d51ab46280002ca20cc125cabe8ae276a82aa928c0002871d4c5de9c0072a06ec09ea5d5124e0fd6258248367c5300000bf844990d6961a85ab3b10e2056ada826912d05db05deba198546290000a888f2a47e584566f0dc852c8abb133400062b8000ba549887de94d600026be0c014805458bca743290e20404ea1a20d8a378277e22a581774805d659c8ee6365e167000129e00007ec84e4d046992b869b1ade60001f7e20cab303610e6200000000000e1a5ede3f500000006a2aa500
  | 43 => 0x3ae000000018dd43415f8000291e2798eacb95cfb6a1b8a0e1c14000ae480000001b3aae8ac56000173e000069000000830001bd20000000bac25ee81665c082ec0001236b4a26940000002146b64132800003344bf8000000268c1b080009184226000182a9e6137496913a199e10c003e01ce000010b75804699fc1f8100f083011000000001d4808a00002548000685d11000012db00022e21231d2265c801f61f2129424180c053a0e4943884f3e40000b1d26fa67a564144a0fb2a6d00006e5995a0fea3d3000023346800000001a0201f816a7d5a1fa144000059b093e84980001c385f7000000088c186e612d7b56a3eadcbca177cb7b0000a7dab1686a40001a020ff51fa3ea89b87720c80bea37e0f911a4800053d8000044017b77129349960000000000082dc00000000002350000000023e0002c822998e400001c2e4e6105e00004f75849ee17af000000000006b5000000005560c1000000023d58930d8f6b897c40000000000269000000006cb9d8655d80000000ad31321d778976e8a0000c480c8ab1e0000efc873138a00020280276bd61c6ab4212d29a8901ab36274565600c081200009b6b4c092a868400004b8018000000054c80000001d2a0000000329a3560000c3600025de0000000209156200000000000000000000093815502e306ba3f8103c9db4000970e0962980268af81603143158e0002b580002918000213a1782cfc240000000000005ef400000000000002306774000000000009d30ff0000095e4d781d629a00007d9ae085aba46a5dc000087601ac068a1ea0000000000149f000000019d297800018de23b0000ba92ec65e91a69000000000004686894000000000000002ae9f880000001a86000125f4d684a212b53c2bbb48464aa21b99aa8fa2858cee01619df23db1d5d7d4689a2260e5c00003446242442a6c1e1aa1e2127478000000018dfb1e00000001abd00001300000e2e5c29f5ca2740000000000173800079b000000000004c92ac436908928051ccca83a3c8000000000000000000000b9156e7a482e1c17129c302400000000000a03030b00005d480d838000000002a22020a3aaae0000288d49b000013942e29a8800075b800000001e291e26d02916462000000035107888e18000a0e19eb00010e600014a112708ee3df1a0d6d68e4b66649b09ef155a000000048400000000000a361f162760000bd71d5a000000000000000002eba000113c43ac76e00019b143aa5e87ea088f5eb200e15396a739256084e9c000683800000019967e9041407a0000a0c97e22de256c52481228b71bce0129d0432880002dc9c52a4b800002e6228140828168f160609880000000f98010a75b21846e2625000050d000080613de57aaa783b3951c7e609bc3a4a558000000000020261fc2d3873ce
  | 44 => 0x188e5c99dd8bad145c8fd044f51793ef6fb8e9c2421b3089681783dea42a1d104665e12bfe32a8e5482f8aab2dc01d0563022f096875c78a2946bcc152258d5ff0723935805d99de077998f74c8c725d81da262ac6361c829e02988d3e6c69f4c9d0016682214624dfc5014b1993c000000000000001d49f3d13cc87071827e0834de96a3023ca0b400001939b771ef0271000211180d111e19c911c00000002df044100020700002b0200016b784ac0007d79eb49d794a28e90ddc0462aca53216043aa277200003c64fb0dde590c548b5100bc5eb9fa00819300aab15dc1258000a3e8000000123400027699ecc00000000004b2d4a983691d6000000073d0b6044a8ba000000000002686000164f21307c47d24b6a000191d00000000000b9c00004c00002f3200009e07b5983cb009b735bc98420001a34000000000029b58e1252a524000000018c40000358030a708947000050bd20aa1da3360002c143be000005a000015e1e90038dc5c0bc49c54e51d446ad000029d0c70000242c00000003cb8f7e1b669e800000003fe80006810f1a00000006a20b4a0001aea55c5b5eb49ce7001c98ca8aaa7ab00000000000000a7480008f6a47a00025e3343824368f833c0000dce8b5ca3c0002594a3d00004f9cbfc0000d645a30b3e00020ae324a464441a4705b6800000004da7ba9e684a5494e632e23c82b0b1812f9e7e76dc6b665d11ae4f71a4a65d5d790af22c20b51f823cc5dda46f2914b309a3f8278b382de84a651d08a474b064ab9b8235873658ebc818640000ef224d8000a38a75a0000a3017e810c70f65d900015ee9799d2e463d826466947a36d15ec6a4896e0bbdf2b000000000000004bd8000000000000008be0a2400002d800060b86e08c0a9c7029800000027572ed00eb09d9e8400015de5cb877ca7425a08a380001ae2866bbba7b00000000000126eb31aad4000021a000000095411e249c062a768c0000001bc8344aee879880005a219e673fd64e62d15b46fc1f2053655b848aacdebb8a2ca15518ec1ee0190579a57e05f18927ee000053124bc66180007fecdf250e53c47d840003f4800078610ef4b112a5a12000027d0dc700000000001bdc00000001bb8000000000008f00000000e720001ac66478882000000000019c224e0000000000000000000000000b390b465e380008c48000ba11d27a5013eb0000e3000001042152666a8a81e6999c0001b38d9e0000c4a5f601847c286d62cba422966a10e211cc76b9c8de955e0dcd85c2bae7f3db2c162830c2158dbe1e49d00abd8b3243cac94b7ba0fe659839e8e39c245609be00a767ee00010c2135c0001f0a81490d5c8a00000004dd87aa0f080005f50000000000073b800030723fe5c1602e51301a800006f45598d2820981ca18b40003e980000002e02
  | 45 => 0x7000000000002ee000000000002b80000000000065c00002640001ebe48c19507c766f065f215238f61b00f205093bf46e40001ae48d990d2895800000000001c900004a8c0000000aa00000cb89cf202406502169ed009455f000000025db0002741a0990dfbaa942453f00a32fd551039282380000000964124c7da50880001c7c0002c2e00000007f88656346000022e1f000000000775800000006b90002e49ac01ee664dcccd115817039214f250ee39aaa589c454a8a9e08306a0868857f8b823767269b7400006700002e66477d4de000000038d5363a459c982700a584729cc56fd12049370000000000000000005c0cafca2f8000314a81ca7780005fcead28362c7250b2dd276ce3db46c1d9a4b31a2a9ce4550164ae7a5b50ba493c8de29358b447e881748d21558874a9c51e501c81968000657656e1438a946c140000002276014ae7317aa5d201a837e0000000000193a1e9af2a58d90ac9220e1e0002bb467017da554800020d9ede5689a583682a8a74d40006112cdc86b8cd667821598cf02ca35312ae85280004ac834d0cbc000000060b9ded9a00000bbc65a034c9c797103ae8296000230c2a39e80a34851a2144f0200005800000dc30001bbf48b1cf00bdd11300017564fc5bb30001a32696628800018820002328aac99ab82d1880000185274f4000aa52e2b1c9d6164db2d7c91d4ebe8a490be000170700022125e895cc96e98e06f41a209034dac74923e331e26e837421b71610d467c10bd80ac2177512a1889b5a3788dcde0e53d000e96607fa815c000afb059c4d892dc0002881000000061c03fe61804068e290223398c28539433200000000d0000000022788a01f452b1d834000113662fe3fdbc2467cab9000073ece8e1f7829a8c20957124a84c3fa27dc19958840abdafd7ade4be59ec35ebc32ce60001a6a0101df7870db0c96e59607ee8cbd8f00000091c000b9800003d6800011d1b6a0002e47000000056c91510000000000000000000000000000af79e0a491800098ba9ca28293d4000000000011a600000000000a70bc7a25c54c24eaa9980000001b68000000000000000002f492b400000000e14ba32e3f058c000960080625fa4a400020dc0000e5e0000c75189ef1c10698a218b92534a5e8e318ea42045d8bee8544cd0b4380002f50e362499910a920b262320e318d8a6da000074aa808802b0d91e42aa00007db900c5efe9c19882892000292866989fa1140000760939e06ee42b10011380000000131a3cc70f2dfb70d4004a3f96680eb8c7a0001a3a0001d9b42e5cc854d1bf677566eaaee8000a7627c800000004c09ab656b27a65fdddc200011465f3adefa81a82090e021c5f72c6a0d81b36b3302120001a5e2b0df260001a3b0a7174d660400057416c16909625697e052bd92effadc
  | 46 => 0x959b04071a080091ecea5529a66e62f5410dd172263046a57029bc25a65a29110564096260e8f419f1a7aa1da02c9a7e7a351ac3069cdd7cccd480001dce34d000011b04289822e6176b64ee6df9c2c41689a8628135c69f0fda14608ac240ae874ad9dca30d6e01534551eb90cda295e17fd4a46778b5c04eb98284bf00000000048ff600a00009400000000205464ec270000000000000004469ff8911970f00000000000000000000000000000001d8e9f6acd200024560000a5c3244000b79c00000022520001f1e000000000006f6103174b00016e69a700029f62b0e39046450002af86a30f62a9a85585070f48525c00059892dfb3000007640a35000000064c2e5f2b72b6c0000000b7d8f388bd000077a00009498210000014a000231ea2aaf441112e8e591654a0000ac40000000000000000003aa0000000baf00006c12c0c00000004a50cc09f0c00082805ca0321bb266703a264d064614461850000000b76808200027ba7f480000000000a7fc000abd1ca09d580000001ce69be1cf586f510256c00000d503053eb00000a000003a79c74766400032859ac92e95da71880000000000000208485040008ad1d103c31cb0a6e1ed80001ec685214300189d667a606436c9cd9097f214249d8a48bcac32e538022431393a65a4de75495078b664a1c097cae4090ddd387e68000af0aebb6f88c042172ac2081d723a801107111c6bc401466f2bd174f331026ab24a08a08b2b98974400076497305fcab56000091a5fe1f30117938800014f823600ca1e621c2000152611f8a54000288967aaaea064a2fe5d29de94a91f1213904e8000000012a000047000000002ee00001b58296960561d4fa00000d6663e000094e1f420000b36737c000000289e00022d974f90dd6cc863fb6d98487a4a1b24370ba2333800015b99b500000007e5800000023f800000006f680000b793f83d18000000000000026804e0a8c46c600e247eeed667118f99a213b5000000020b1bc085a52e5000000000016443e0000059600009022a125d5e0090000ca482c01db1ab0f6a65cc9ea000000083b800016ba0c40ca5a721a3a5a60000000118844581389c9374800030a400000000000001e4a4e4a07c5411aff19a93e14a3dde06f5243f2d9a616b5405a0000152e30424f6483a17900003bc000000021f15645f580005f82e31616c000021a16db061238b8d400c68b92360002d1c8fc13e95b2c0000000000a5f1f5a000254e8c40b3a00014280000e4e02d000000020e81dd000000000004cd22ea000279073a80d722728f273d876a5c50959000000051e02403048000807d54800000005c1000056200000001c2f0001eb00000c180000000000269800027c200009fc000167ea6c40ed2648ba65152e10a92a3c67502d1a20722e652f038a44b432
  | 47 => 0x44701a2145f79fee0000000808859a0000ce4b535dc65db6e3ba3b8a7e0002e2c107800000008cc297ae789078e1617d20622a702494c59de789610929b7800033e91d4ae72d8a91b1b5c65b43708a315f009583f41c21dcd914127a1a69361a8c2b947cf0fd345c07b25cbd030000220a8f5c00046a241b10283c4261800060c8c4000025c400017520002c300001be400000003d397d2777800067865820002a4600013ea9d2a9583944000aa3a9e25c4886c60806670a8000061749540000000000202c00028a96e219846f58000a6791824a693840002c5c15009f06ca9e245535d0a7b80a464768e6cb6ea656000098e2a8e1dc68717b03ff803e4fe895c0000d72b6e241161d8e1cb88989a00015e8846400092481956ace10278da9267a2af1650a874086799cd0ed950c50b5ce47fd13d27358000274a4e203f80008d40c2b88dabb65e59b7054f0bf214f1085b93550a687ab2a9e4a64e7dc9f774ff99d8000000087d1cf75d000002592f0a4dd4a7a000000099b59c99cd0baa1c08d7a5360c8e99a015877f400045485ee8bb0000499218726c80000002ed0b6c8c0e065d3100c998b683a9b9cad801232a19aa60e11a522d78506062ad3a03a2962239121407d8bb24b68ffc61e14e244ca49600005121f4171a0000000411a14453a64ceac90000863287213603766a7a43a00000006ae2512bbf6804000255608b57edb7fc000b8d870c3b1ae90000201a72e9a5313519065ef2e5949e5982881da405b48bd0308000099951089121119922c0000000000572ab5a999000000000000a35bbc00000002ea0093b8c8d6e71309d6790c000000103a00005d000010fe0001d12000036aa260ff400012dd00028884a5a79c2078d265fe80008514a00b0b00008fe867a0ee190795529c60000000904000084726fc0baae0f00b12ac00000001cb800061288fa83c800005428ae81ba08e0000d5885ea82261aa0bc0a18d1e1dea4d20002e6d39408de9d743940afca243b51c3aa9f95c2b7603d6135a5cb7790d78bc1cac0950086600029080515e8237313cb00021754b4800000019f700000005a55805975df4d8d080002f21cc329100c30001d985f9258832d04c9acd0e7c0001926541adc8251147b00006b22c81b7f0002ce0b63a8a6b3656d63400000b7e000029094324f1ca3e0001e2031324da0002a8200000000000a0c0815f857f9204c0312d60258970971c800069bab840000000b4611141246eb6a3b29bd00019fa000000000000001220000000132a4da80001aa00003d600001b194817588464a05a0102c59bb4334946a8d4595614519c62d08fbcb61d70e48722f0ae91963686800071395a04d58a260002570b4a6e2a78c1dae9b2aa26b41845a3b0a0d4b59000041f98c2a4e9886943032baf2d2087f5a91200000005a
  | 48 => 0xc99e1f00028d0b7f96a0909474804d0a0206e01819b60000b96c54a000234c088ebb200000007a180007c2d3042bc9de248098d306e9370499a6feba14c2479140000000db2000000022d800000020e61c3c0000002b5c000180a00008eaaf28efe5b6031f98a1c76958230a42dc64c8e5a63a2ad099e46f87ee8a184fc6a9da1588c85b3a9a25a89d7212d49ec00074e4000051229851e538d7d8866655c80000000000000141080315365d6871e654d6f831de486105811720c597074a400000000002e62e62035800000022f800000006448996000000089380001b769a24d4800000000000000e60b7c8d508c513cda6d8000a97000051fc00000026c44b60d526b6140c131dadc8b6a6389a2962a756409e89c80003e08c5531c6f1375180006c91fc4000169e000000000023a60000000a60000049aa5683fb85e501cd5514fb800006d8000b2e47d438e1436b09800054dc0003350c1b3b114b30001bb6000000000006ca8f5ae18061589f00029ccb520000000165352bdcd57d4ac9e9bc80008ed0c931dc54429aa008e448dba708c012aa530d22847c0007bd000081d823a899800062a84b8ace93386ac115c210a196651c88a5dd943114c83b2600e98aa20194224b8dc91b54fd6092dd648cc90769bb9e9e8262e2800016e400010fc890231c7730754afe00f6831a1765559ccb00000008908000000220238d1c149c802d9436111666d800000027c03c5000017ce6103e3dad10001780a13a79f4a702926518000b2f80008b90f6642fd655000154cbcb889154200008e9e1dd9da800094782ac91300f9ad98a2e81b0498485ae8b81c93b3a6e42e80f9083a000035a00d14a31ed69848e40e0c32b0d99482cd56303e79a9a740886d39edf6450000481a04800000005ad85e400000000000000000128e70cd9a29bd88dc25200004e414ae00013da72500cb32e8ee400012e00000000000000076f0c5818180000002ccaa5983e098080000001d80000239e10b906a318a1991859b420001f3b00000000000000ad880000000ae04658000882086a24a014b5ba1f3a1f489e4a4917ba5c89de627e00009b9aedc00013e6000000010f966eb8a427eba7cabd8e8cd0800013968bf26d2b01280a000000000026a646240000000ee8a8a1e425d4400017c00000002226875873096d2cc839a9a96138d0fbbc5e21c7345ff945bda0b9531997b7a2d7f18c6c661c722e8169aafe0002abc47e018e8a880003bc01bc50a57fe0ce64b64956ed44e9076d872278a25d63e8b905b607312b1800028b44a880000000000000050546d078ca810000000000000018db0000e82000211800000007bc0000b0e00000000000048000000000000000da8b0014ba097079a3d0572abb60000000118a6d593e22c28d0aa93800066500000000c2728aa2
  | 49 => 0x50ac000631400010b00000234000000000052c00000002e3973f23e20000d719fb00007a982fc1e3851567e4e0e5b281ae0ea21ac159972d000000000022620001eac86d40005ca0896000000000000004ce400048e8000934000014d8e4d6ac8c307dda5bc28e0c3e0000f4299100005c012260d729ae9cc1e5a96e26b0368d7a800018e625ad6ac00022ae000000000000000000f1e0001a70ae21f7c0001da81a881da18f00004e68deaa8d1070a930654865055c8cb14561a70d1430d2385990000058b0000180800004904cea4f006e000057e05e5a4e5578000751cee20000000af70cfc85600006bb9299000059e00007a2687cdfe48c9d42a1a02947f4000005dc00084f03bf7a900004528b7e0001c780000000ae319230000000112000000000000002e5e00000000000000ba800000001eb870715fe00029fa000000075a917a2f82403a2b6bee731d2d44ef9b20b9a11d00dad6345cd527e57bd73460890980001a1630b6e88514832a3fc5c502b8d044a86198804761a461deb3e00010bc0a88914a1715d826469f4328216cb0ca8a467953c99d2589c030444a79f1c2d855200b3b327e6a419d267f018a8234202a94e869e76a613641313f0673d12c6a0a20eb7504cabd1d8c944498a98c99b4890311b839856865fd5dfe193ce880770de835f10941df800070682ba8752e06904edf42eb891e189936899ea5186f188695c7056a242843891fa1a0599051b96cc00029906a678125e900002a6a30a7708df8a80174907a4de116e80f016050cc6194f8d98c45923185ef9d560002e5c00006edb549a6cbcd2f4eb3c8848b87a05c4456c86070a5d83f99732112d09c4a984083f72e37b49277c203a26a6d11f2153b9064486162692866b2664215abd087963c2936e2cc1438034238128181fa000000054508019ff8c801925f6452dd8004a41dd2330add004a0712634843f74184ee36f51dc89c260c204603e2d91d496772c62a128c60421ae330938000a
  | _ => 0
def gbK4 : Nat → Nat
  | 0 => 0x845e73d96410422eb9ecb208211b9cb65904108dae5b2c8208654639454104332314a2a08211ddd95410410aa8e6aa0820856472550410423abb0a6208211d5d852104108eeeab008208659539823104237396ca188211b5cb650c410aaae2a9862085557394431042abbaa6218821711c9310c410cd2a5304420845e73d94210422eb9eca10821595c55208410acae528842085677548421042e239a42108219398e6294010c9ac7314a00864e6358a5004326b1ac5280219598f4194010cccc5a0ca00847576106500432b31883280219998841940108bee6b2e800845c735974004237b92cba00211b1c965d0010ab0e6b2e80085687259740042ac39aa9a00215a1c954d00108f2ec29e80084797614b40042b8baec3a00211e5da51d0010ae2eba0e800857175107400422f39ecb20021175cf65900108dce5b2c800846d72d96400423bbaac3200211ddc765500108bce7b28800845d73d944004237396ca200211b5cb65100108eae2b28800845e73194400422eb98ca200211b9c865100108dae4328800863554984400423dbb2a820021561cd5410010ad0e4aa080086596598c400432cb2ac6200211e5d85310010cd2cb3108008669655884004364b1ac4200211e5d85210010ce2cb308800847b755844004338b2ac220021b458d6110010dc2c4b0880086716194440042b8bae82200219c5974110010ae2ea2088008671651044004398aa08220021539cb53cc010aace3a9e600846e72d963004236b96cb180211d5c5658c010c9ca7314600864d5398a300432b29cc3180219554e618c010a9ce5a9a600855671d4d30042ad386a698021179d8534c0108dce5b28600846d72d943004237394ca180211b5ca650c0108beeca9860084777558430042a739ea590021179cf65880108bae7b2c400864e6394a200432731aa5100219994a6188010ccaa530c400854e73d49200422f39cca10021175ce65080108eeeab08400847575193100423abb6a9880211ddd954c4010c6cc8aa620085547355310042b2392a9880211d5d853c4010d64c9a062008571751031004398aa081880211d5da5184010cacc728c200866662946100423cba8c908021965966384010cb2cab1c20086696598a1004334b2ac508021b258d62840108f2ed28c20086b264d06100423abacc8880211d9db54440108e8ecaa220086346455110042aa39aa888021591c954440108ecec29a20084767614910042ab39ca088021599ca5044010d60c9a0220085717510110042e8b988088021785c84044010ae2eb18220085e1728c110043a829a60880215c5d62044010ba2e7102200876052481100423cbacc888021745cf6144010bc2e5b0a200847a7694510042b8bae8288021ac1934144010ae6ea98a20085e3724c510042b9baa428802174dcd2144010
  | 1 => 0x104426b39ec908221399cb6484110c6ac82a420886565498e104432a2a4c708221399c86384110d8cc731420886c56398a10443332a4c508221991526284110d8cc6b1420886d263d421044371316a108221179ce60d50108bae7306a80846d729835404237b92c72a0211b1c963950108e8e2b1ca80845f7358a540422e39ac52a0211d1c56295010c9ec7b12a80864c63d895404327b18c4aa0219318c62550108bee6b0aa80845c735855404236392c2aa02195d8c6155010ca8c630aa808667621855404332310c2aa02117dcd60550108b8e6b02a80865b63181540432c318c0aa0219ad886055010cd0c4302a80867061181540421fbb2a82a0219398e6215010c9ac7310a80864e635885404326b1ac42a0219598e6115010caac7308a808666629845404332b14c22a0219658e6015010cd2c5300a808666629875304332b14c3a98219a58a60d4c10a9ce5a9ca6084747158a53042a7396c6a98211b1c96154c108beeca98a60846f725905304236392c8298211b5ca6014c108dce432e860846d72197430423b388cba1821539cb53d0c10aace3a9e860846e72d964304236b96cb218211b9ca6590c108dae532c860847671996430423abacc3218211ddd56190c108f2eb304860846e729954304236b94caa18211d9c66550c108f4e132a860845f735954304237b92caa18211b1c96550c108eee2b2a860847b70595430422f3b4a6a18219394c6250c10c9aa6312860847575185430432b298c2a18219554c6150c108f2ea302860865a53181430432ca98c0a18211b9c86510c108dae4328860847671194430423d380ca21821175db5310c10a9ce5a98860855671d4c430422ebb0a6218219598e61d4810caac730ea4086596398352042a739ea529021539cf62548108bee6b0aa40845c735855204237bb2a42902117dcd64148108b8e6b20a40845e73980520422eb9cc029021179cc65d08108bae632e840854e73d4b420422f39ecb21021175cf65908108bce732c840845d73996420423b38ccb210211ddd561908108bce732a840845d73995420423d384caa102117dcd65508108b8e6b2a840846f72595420423bb8acaa10219318e5250810c98c6a928408475751854204333290c2a10219954861508108f2ea302840866a521814204334a90c0a1021179cc65108108bae6328840847a701944204236bb6a421021539cf52108108f4e032c640847771595320423aba8c2990213c5c0614c8108ece3328640843e74194320421eba0ca19021535ca530c810a9ae7290640854f754c832042a6baa6419021711c5320c8108eeeab086408479759803204237b92c7288211b1c963944108bee6b14a20845c7358a5104338382cba0821551cd54d0410ac8e4aa682084757614f410423abb0a5a08215c5d760d0410ce2cbb0682
  | 2 => 0xc0a0a211d9d85450510ca8cbb1a82886546518d414434baa0c6a0a21959506350510ca8a831a82886945418d414433232ec4a0a21b118f6250510cc8ca31282886c7631894144362318c4a0a21a9d506250510ccca831282886645418941443522a0c4a0a219c1976050510da0c7b0282886e062d814144369b18c0a0a21b418c6050510dc6c430282886e06218141442793a8c0a0a219c9d46050510ce4a8302828867054181414423b3aec998a21399cb64cc5109e4e1b26628847475593314423abb4a998a214d1d153cc510ac8e4a9e62884f27598331443393acc198a219c95260cc510ce0a9306628851c7454e31442a6392a718a21179d8534c510c9ea6312628864c5318931442aab8ca618a2117dd9530c510a38e8a98628854c7254c31442e23926218a211d9d7640c5109c8e4b2062884f070590314423abb0a818a21555cc540c510ba2e129862884777654c314429a3a2a618a21591c9530c5109aeeca9862885947454c31442e2392a618a2174dc1530c510aaeeca9862886577654c314438bba2a618a21551d1530c510e28e8a9862885147454c31443a3b92a618a21551c9530c510e88e4a9862885447254c31442abb82a618a21d4dc1530c510aaeeba1862884d57610c31442aaba88618a21c5150430c510ba2e021862884f270988314423abb4a418a21555cc520c510aaeeb19062885d1708c831442aaba86418a21d1148320c5109cce530062884d673d932144279386c990a211d1d564c85108eaed2a642884f27018f214423abb4a790a213c9d660c8510ce4eb30642886725498321443382a4c190a214b1d15288510a98e6a94428864c63d4921442373b0a490a219318c5248510b88e6908428847675d90214426a39ac810a213c1c164085108eaec2a04288565721502144279384c610a211d9d463085108eaed29842885657214c21442f0b84a410a211ddd95208510a68e8a904288554735482144273bb2a410a21691d15208510b88e6a9042885e37054821442b3bb2a410a2199dd95208510e4ee8a9042885647454821443923a2a410a21491d15208510e8ee6a9042885647354821443a239aa410a21511cd5208510acee0a9042887637054821442b3bae8410a21395d84208510acaea21042887245410821442f0b808410a2159dd73208510bc2e19904288565750c821443a22986410a21359ce60085109a8e6b0e80884e472587404422fb9acaa0221171cd65501108dee4b2a808861f5418d404430e2a0c6a02218bd506250110c58a8312808863454d85404432a29ac398221391c961cc11087ee8b2a608843c745953044237b92ca9822195594314c1109a8e6b0e408866452587204421fba2ca902210f1d165481108bee6b2a408845c735952044332b284290221cc15141c4110ba0e6a0e20885e072507
  | 3 => 0x4e618c210caaa730c6108666529863084332a94c3184219594d618c210ccca4b0c610866552586308432b29cc2184219994a610c210caca6b0861086665258430843a4a926018421175da53882108beeca9c410865653986208432aa9cc3104219994a6188210caca6b0c4108655535862084333292c310421559cf54c4210acce5aa6210847776553108431b322a9884219559653c4210cacc929e21086546494f108432ab2aa788421599c853c4210ccacb29621087465394b10843a2a9ca5884219999252c4210cc8c929621086656554b10843a329aa5884219659653c4210cb2caa9e21086696594b1084334b2aa588421d254d52c42108bee6b0ca88845c7358654442aa39ac32a221591c96195110c3ec831aa88864f63d89544432631ec4aa2218bd906255110c9ec6312a88864c63189544432bb1ec2aa2219518f6155110ccec5b0aa88866462d85544432db1ec0aa2219618f6055110cd6c5b02a88866862d81544421fbb2a82a221471cd5415110a58e4aa0a88846f7258c5444236392c62a22117dcd62151108b8e6b10a88845e73180544422eb98c02a221591c96194d10c38c9b1aa68862f64d895344316326c4a9a218bd906254d10c58c8312a68864f63189534431a326c2a9a219918b6154d10c70c9b02a68845f7654c534428e3a2a629a21531c95314d108dee4b20a68846c72590534423bb8ac829a211edc16414d108dce5b2e868846d72d97434423a3aac3a1a213c1c161d0d108dce5b2c868846d72d96434423ab8ecb21a211e5c36590d108dce532a868846d729954344237b92caa1a211b1c96550d108eee2b2a868847b70595434423a388caa1a211e1c06550d108ecebb0a868847a75d814344237b92ca21a211b1c96510d108dce4328868846d72194434423a3aac221a219514d6110d109c8e4b0886884787558043442aa39ac32922187d936354910c38c9b1aa48861f6418d524430e320c6a92218d1936154910ca8c7b0aa48863864d815244237bb2a4292214b1d15214910a98e6a90a48845f73590524422e39ac8292211edc164149108bce7b2e848845d73d974244278382c3a1221179cf65909108bae7b2c848845e73995424422eb9ccaa122117dcd65509108b8e6b2a848847b70595424423d3aec0a122117dcd65109108b8e6b28848845e73194424422eb98ca21221351cd6110910cc8a4b08848847875580424421f3a6cb992210f5d365cc91087ce9b2c648843d74d96324423c3aac1192210fdd1654c910878e8b2a64884f270d85324423cb86ca192210fdd1650c910878e8b28648854d7214c32442a6b98a419221539d5320c910a98ea99064885c4714c83244279384c720a213c9c262905109ace730482884e672982414430faa0c6a0a21871506350510c5ea8312828862c54189414431c2a6
  | 4 => 0xb2a6b00850866a525804284334a94c1994219694d60cca10cd2a4b06650865953982328432ca9ac1194219a949608ca10a98e4a9a650854c73549328432b29ec2994219554f614ca10ccca5b0a650866552d85328432b298c2994219554c614ca10ccca430a65086655218532842a6b94a619421535ce520ca10a9eea990650854d754c83284327b2a641942193595320ca10b88e29906508656539843284333294c2194219594d610ca10ccca4b08650855673d5341842b3396a9a0c21c595253d0610acce429e83087265494b41843a329ca5a0c21d154e52d0610e8ca6a968308656535834184333292c1a0c21175d763506108baea31a830845e7694d418422e3b2a6a0c211b5d76250610c9ca7b12830864d53d894184236ba8c4a0c219394c6250610c9aa6312830846e769494184327b1ca4a0c219318e52506108d8eca92830864f63549418432631aa4a0c219694f6050610cb2a7b02830866a52d814184334a96c0a0c218e9506050610cb4a63028308659531814184335290c0a0c219a54860506108eaedaa0830855673d5041842b3396a820c21955965310610e2cc929883086556554c418423abb0a620c21599c85310610ccacb29083087465394841843a2a9ca420c21c99925210610ccacaa90830874653548418432b29ac020c21999496010610cd2a5306630865a535833184334a92c198c211b5d7624c610c9ca7b12630864d53d893184236ba8c498c219394c624c610c9aa6312630846e7694931842363b2a498c219654f604c610b88e49886308746524c431843a2a926218c219654e60c8610cb2a6b06430866a52583218422ebaec690c21175d463486108bced29a430845c7654d2184327b1ca490c219318e5248610c9ec6a92430864c635492184334a96c090c21711cd2108610e8ca6908430874553484218432b29cc3204219994a6190210caca6b0c810866652586408422f3b4a6a0421171d95350210c9ca7b12810864d53d894084327298c4a04219354c62502108dced292810864f63949408432631ca4a04211b1d95250210c9ec6a92810864c63549408432b29ec2a04219554f6150210ccca5b0a810866552d85408432b298c2a04219554c6150210ccca430a810866552185408422ebacc62042117dd563102108baed298810845f7654c4084236bacc4204219394e6210210c9aa7310810846f75588408432729ac4204219354d62102108daed290810864e639484084326b1ca4204211bdd95210210c9cc6a90810864d63548408432b29cc2204219554e6110210ccca5308810866552984408431aaa2c2204219594d6110210caaa6b088108666525844084332a92c2204211b5d6628c210c9ca7314610864d5398a3084237baac5184219394d628c210c9aa6b14610846d7694a3084237bb2a518421959
  | 5 => 0x854e7215153842a6b90a8a9c2153dc96454e10a98e4b22a7085577159153842ac382c8a9c21569c26254e10aaee2b12a70864d62189538428fba2c2a9c21471d16154e10a9ee4b0aa70854c7258553842a7394c0a9c21535ca6054e108beeca98a70864d539885384326a9ac429c219398e6214e10c9cc6b10a708666625845384334b14c029c219c5866014e108dce532e870846d729974384237390cba1c211b5c865d0e108dce532c870846d729964384237390cb21c211b5c86590e10caca730c8708656535864384237394caa1c211b5ca6550e108dee4b2a870846c725954384237390caa1c211b5c86550e108daebb12870864e53d894384326a9ec4a1c211b5d46250e10c9ca6312870864d53189438432b29ec2a1c219594c6150e10caaa630a870865a53d81438432ca9ec0a1c219694c6050e10cb2a6302870846e729944384236b94ca21c211b9c86510e108dae4328870865a5358043842a739ea529421535cf5294a108bee6b24a50845c7359252842a739ea929421535cf5494a10a9ce62a4a50854d7315252842b2b8ec92942153dcd6494a10a98e6b24a5085677159252842b4382c9294215a9c06494a10ad4e1b1ca5085677158e5284326b18c729421595c46394a10acce321ca5085657190e5284237bb287294211b1d94394a10acee2a1ca5085647150e52842b5b8287294215a1c14394a10a9ee6b0ca50854c7358652842a739cc129421535ce6094a10a9ce7b12a50854d73d8952842373b6a8a9421539cf5454a10a9ae7aa2a50846e7615152842a7398a8a9421535cc5454a108dceda9aa50846e7614d52842a7b9ac8a9421531cd6454a10acee2b22a5085687059152842b5384c6a942159dc56354a10c9ac631aa50846f7650d52842363b286a942159dc54354a10ac8e2a1aa50856b7050d52842b438286a94215a9c04354a10ad2e021aa50852f7458552842963a2c2a942153dcd6154a10a98e6b0aa50854e7398152842a6b9cc0a9421175da5314a108beeca98a50846f76548528432731aa4294219358d5214a108bce732e850845d73997428422f398cba1421175cc65d0a108bce732c850845d73996428432b29cc3214219994a6190a10caca6b0c850866652586428422f39ccaa1421175ce6550a108bee6b2a850845c73595428422f398caa1421175cc6550a108baebb1a850845d7518d428422f3b4a6a1421171da5350a108bceca9a850845c7654d4284327b1ca4a14219318e5250a10c9ec6a92850864c63549428432b29ec2a14219554f6150a10ccca5b0a850865653185428432aa98c2a1421999486150a10ccaa430a850865a53d81428432ca9ec0a14219a94b6050a10cd2a5b02850865a53181428432ca98c0a14219a9486050a10cd2a4302850845e73994428422eb9cca214219654e6010a10c
  | 6 => 0x1c43322a0c4a0e219cd976050710da0c7b0283886e062d8141c4369b18c0a0e21b418c6050710dc6c430283886e06218141c43392a0c0a0e219c15060507109cce5b2663884f270d9331c423abb4a998e21591c953cc7108eaec29663885557314b31c42a6392a718e21531c9530c710b88e4988638865a5358031c423bbaac818e21391c9640c7109e0e0b2063885557315031c423bbb2a618e21591c9530c710b88e4a9863885577654c31c432bbb2a618e21551d1530c710e8ee4a9863885547254c31c43a2392a618e21511c9530c710aaeeba1863885557510c31c42aab98a418e2155dd6320c710e8ca51906388555750c831c43a22906418e21745c0320c7109cce530063884d673d9321c4279386c990e211d5da54c87109e4e031e43884757614f21c42b2b90a790e21551cd52c8710a98e6a94438854c7354821c42e239a4210e219a94960087108eeeab2043884d47359021c4278382c810e21595c85408710acae429843885547354821c42e239aa410e2159dd95208710cceeca9043885647454821c43a3b9aa410e21591cd5208710e88e6a9043885447354821c42b3bae8410e21595d44208710aceeb990438874653cc821c42b2ba86410e21d114c3208710bc2e019043884d67398021c426a39ac3a0621391c961d0310ab4e7aa6818856a72d5340c42b5390a7a0621569cc52d0310ba0e6b0e81885e07258740c42e839a83a0621781c941d0310c6ca830a818847976d5040c42ad39ea8206215a9cb5410310cb2cab1881884797614c40c42b5390a6206219a5956210310d92c6b1081884797614840c42ad398a4206219c5966110310da4c6b0881886d16358440c4371312c220621b858961103109e2ed20881884f37650440c42e839a8220621781c941103109e2ec18881884f17608440c42a6392a798621391c961cc310a98e4a9a61886555318530c426a39ac3906219398e62d5210c9ac7316a90864e6358b5484326b1ac5aa4219598d61d5210cccc4b0ea90865a63983548432cb1cc1aa4219a98a60d5210cd2c5306a908671619835484237b92c72a4211b1c963952108bee6b14a90845c7358a548421fbb2a82a4219398e6215210c9ac7310a90864e635885484326b1ac42a4219598d6115210caac6b08a908666625845484332b12c22a4219998961d4e10ccac4b0ea70854e72d4e53842a6b96a729c211bdc96494e108d8e4b24a70854e72d5253842a6b96a929c21539c85494e10a9ae42a4a70855571d9253842a7b92c929c21531c96494e10aaee2b24a7085587059253842ad380c929c21569c36294e10aaee2b14a70864d6218a53842aab88c529c2153dc96194e10a98e4b0ca70854e7298253842a6b94c129c21539cb6354e10a9ae5b1aa70845e76d5153842a7396a8a9c21535cb5454e108bcec2a2a70
  | 7 => 0xaa08611b1c96550430ca8c728a821866462945410c32a31aa2a0861991895150430ce4a2302821867151181410c2abbaa6218861711c9310c4309b2e031a421845f7558c210c2b2b94a21086159dd52108430acaea90842185c473484210c22ebb087280619998a6194030cccc4b0ca01866562586500c23bb8acba00611d1c565d0030ae0e2b2e801857071553400c2acbaec7a0061565d743d0030ab2ea21e801845f7558e400c30eaa4c6200611edd95410030ae0e2aa080186596598c400c23dbaac620061965956310030cb2c7298801855975d0c400c32cb2e8620061565d44310030cb2ca21880187195410c400c338b2cc2200619c5956110030da2c6b0880186e162584400c22fbb2a9980618799154cc030aa8e2aa6601869a64d03300c2acba88198061c655040cc0308baed29c60184797694e300c34d3268718061b8589618c0308baeb322601845e76d51300c22e3b2a89806187191544c030aa8e2aa2601869864d01300c2acba88098061745c4404c0308f2eb32260185d171d8d300c2acbae8698061a6193434c030ab6ea98a60185cb724c5300c32731cc5aa6219358e62d5310c9cc6b16a98864d6358b54c432b31cc3aa6219558e61d5310cccc530ea9886656298754c432d31ac1aa6219a98960d5310ce4c2b06a98843f7655054c4237b92c62a6211b1c963153108bee6b10a98845c7358854c4237b92c929e211b1c96494f10c9ec6312a7886676218553c4332310c2a9e2117dd95314f10a98e4a98a78864d5358853c432731ac429e21991c56214f10ccac5308a78866a6258053c433930ac029e211b9cb65d0f108dae5b2e878846e7299743c4236b94cba1e21531c953d0f10caaa730e878846e7219643c4236b90cb21e213c5c66090f108dce532a878846d7299543c4237b92caa1e211b1c96550f108dce4328878846d7219443c42a6392a621e21391c96110f108bee6b24a58845c7359252c4326b90c6a96211bdd95214b10a98e6a90a58864d6354852c432a38ac6296219558e6114b10cb4c6b00a58845e73d9742c422eb9ecba1621179ce65d0b108bae732e858854c7354b42c4332a94c3a1621179cc6590b108bae632c85884f17198242c422fb9acaa1621171cd6550b108bce6328858845d7319442c42a639aa421621351cd6110b10a98e4a9e658854d7214e32c42a639aa519621179da534cb10a98e4a9a658854c7354932c432b298c2996219554c614cb10ccca430a65886655218532c422ebb6a619621535c8530cb10a98ea990658864f654c832c4326b2a6419621711c5320cb109e2e330065884d67398241c4273394c120e211d9d85450710caecbb1a83886576518d41c432b2a0c6a0e21951506350710ccecbb1283886c463d8941c4333b28c4a0e21b1d8c6250710d88c63128388666541894
  | 8 => 0xe5150230ca8c728a811866762945408c332314a2a04611d1d95150230caec6a8a811865463545408c333b12a2a0461991895150230c3aa8b18811847575984408c23bbaac2204611d5da5110230cacc7288811865563944408c333314a2204619958a51102308eeeca88811865663544408c32ab1aa220461999895110230ccac4a88811855671d53308c22fbb2a9984618799154cc230caacb28e611874652947308c32b324a3984619519251cc230caacaa8e611874652547308c338b2ca3984619c59551cc230ec2a4a8e61185547158e544c32bb1ec2aa26199d8b6155130c6ec830aa89865763185544c333b10c2aa261991886155130ce6c3b02a89867061d81544c21fbb2a82a2614d1c554151308dee4b08a89846c72584544c26d384c321a61359c66090d30c6ea830a869863454185434c31c2a6c0a1a61179d85450d30ca8cbb0a869865465185434c363b10c2a1a61b11886150d30d2ea830a869865654185434c32a2a0c2a1a61a51506150d30cb0cbb0286986d061d81434c369b08c0a1a61b41846050d309b4ea302869865a75181434c32d2a0c0a1a61961506050d308eeeca88a29853474544514c2b2392a228a611bdc964145308d8e4b20a2984d87058f414c237394caa0a611b5ca65505308dee4b28829846c72594414c237390ca20a611b5c86510530998e4b18829865563144414c267396c918a61369c3648c5308b8eab2462984da75982314c32d3acc118a6196952608c530cb0a9304629866462d45314c332310a298a61711c9310c5308bcebb2062984cc72590314c26c382c818a61175d8540c530aaae22a062984da70988314c2aab88a418a61745c2510c5309aeeca88629859474544314c2e2392a218a6174dc1510c5309aaec208629855575104314c38a2a08218a61745c0410c53099ce530062986c832582214c26d386c690a610fdd16508530878e8b2842984da70d8c214c22f3a8c610a61595c85108530caaca1884298744520c4214c2b33aa4210a61591d52108530b88e690842984d47158f404c30e2a6c6a02618dd506150130c68a830a80987185450f304c2e838a8798261359c7648c130c3ac82a460986c662986304c32b2a4c31826195152618c130d8cc4b0c60986d261d42304c237b92c32a0611b1c96195030ca8c7b0aa81866762d85540c32a318c2aa06199d886155030cc8c430aa81865863181540c339b08c0aa0619c184605503087eecaa0a81865663984540c333314c22a0619598d6115030cccc4b08a81866562584540c338b0cc02a061961c165d0c30aa8e2aa6861855975d83430c32cb2ec1a18619594c6150c308beecaa0861855471550430c22fbaac021861599cb51944308eeeca88a21846e72d96410c236b96cb208611b9ca65904308dae532c821845f7558e410c237b92c
  | 9 => 0xe2a1881986d16398440cc338b2ac220661b458d6110330dc2c4b0881984d9760c440cc32ab1cc3aa4619998a61d5230cccc4b0ea91866562587548c32cb1cc1aa4619c98660d5230ce2c3306a91846f72586548c236392c32a4610fdd95415230caac7308a91866662984548c32ab1ac22a461999896115230ccac4b08a91855671d53438c23abaec2a1c611d5d46150e30c74a8302871845d76d50438c2ab38ea821c61599cb5194630acae5a8ca31846f72592518c236392c928c61599cb5494630acae5aa4a31856672152518c2b2b90a928c61c59534394630aaaea21ca3187474394a518c3a221ca528c61555cf6494630aaee6b24a31856772592518c2b2392c928c615c1c16494630ae4e0324a31855570d0e518c23bbb28728c6159dc94394630ac8e4a1ca3185737050e518c2b83828728c61c59d04394630aaae021ca31857270d8a518c2abb9ac528c61555cc6294630ccac4314a31856672982518c2b2b94c128c611d9db5454630acce5aa2a31856572d51518c23b3b0a8a8c61599c85454630acae42a2a3185557510d518c3a3a1ca4a8c61d110e5254630aaee6b22a31856772591518c2b2392c8a8c615c1c16454630a6ee8b1aa3185347458d518c2b3b92c6a8c61591c963546308e8eca1aa3185677250d518c2b239286a8c615cdc14354630ae0e0a1aa31857270989518c2abb9ac4a8c61995886254630acce5302a31856572981518c236bb4a428c611bdd952146308eeeca88a31866662544518c332b12a228c611b9ca65d06308dae532e831846e72996418c236b94cb20c619398e5290630c9ac7294831865663946418c32ab1ca320c611bdc965506308d8e4b2a831846e72195418c236b90caa0c611b5d762506308daea312831846e76949418c2363b4a4a0c6193d8e5250630c98c7292831846e76549418c2363b2a4a0c6193d8d5250630c98c6a92831865763945418c32a31ca2a0c6199d8a5150630cc8c528a831865463545418c333b12a2a0c61991895150630cd4a5b02831866952d81418c33928ec0a0c619c5476050630cd4a4302831866952181418c339288c0a0c619c54460506308dce5328831846d72994418c334a94c020c619a5496010630ce4a2b00831866952982318c334a92c118c619c945608c6308daebb12631846d75189318c2373b4a498c611b1d9524c630ccec528a631866462945318c333b12a298c6199189514c630ce2a3b0263185c4724c4318c3a32926218c61d1549310c630cd2a5304431866952582218c33928ac110c6195d8e5148630ca8c728a431865763545218c32a31aa290c61591c95148630cacc7288431865563944218c2b2b94a210c6159dd52108630acaea908431866765484218c332b2a4210c61711cd2108630cacc728c811865563946408c23b3b4a2a046195d8
  | 10 => 0x6546354521102b2392a2908819c54760484408bce7328422045d7399421102b2b94a21088159dd52108440acaea9084220667654842110332b2a4210881691d12108440b88e690842207465348421103a2a9a421088178dc1210844087aed2a480204797695240103a8a9aa320081d854951900408b8ed29a802045e7654d401032b29ec2a00819554f6150040caca630a802065553185401023a3b4a2a008195d8e5150040ca8c728a8020667629454010332314a2a00811d9d95150040caec6a8a8020654635454010333b12a2a0081991895150040c3ee7b2a802061c73d95401031bb8ecaa00818d1c76550040c3ecbb1a802061f6518d401030fb2ca6a008187d955350040c6ecbb0a802063765185401034a318c2a0081a91886150040c6ecb28a802063765545401032db9ecaa0081961cf6550040ce6e3b2a802067071d95401032db2ec6a008196d946350040d34a831a80204d87694d401032db2ca6a0081361d95350040cb6caa9a802067365d85401036831ec2a00819cd946150040da6c630a80206d0631854010371b10c2a0081b81886150040d64a830a80206d2531854010368a98c2a00813c1da5150040ce6cb28a80206d0639454010370314a2a00813c1d95150040ce6caa8a80206d06354540103a8a9aa2a0081b81895150040ec2a4a8a80206566398754cc333314c3aa6619598d61d5330cccc4b0ea9986656258754cc32d31ac1aa6619c98560d533087eecaa0a99846f7258454cc236392c22a661359c66090f308bcec2a2879865765d8543cc32bb28c2a1e61b1d886150f30d88c430a87986565418543cc32a2a0c2a1e6196d976050f30da0c3b0287986d36118143cc368308c0a1e61969506050f30cb0a8302879846f7259251cc236392c928e611ddd95114730ac8e4a88a3986656254451cc237396cba0e611b5cb65d07308dce532e839846d7299741cc32b31aa3a0e61591c951d07309b2e7304839846f7259541cc236392caa0e61331c96310730ac8e4a8883985647254731cc267396c918e61369c3648c7308baed2a4639854c7254631cc2b2392a218e61711c9310c7308beeab2063984cc7259031cc26c382c818e61555c4540c730a98e4a8863985c47254431cc2abbb2a218e6195dd9510c730aa8e8a8863987477254431cc2aa392a218e61d11c9510c730a88e4a88639855775d0431cc2aaba88218e61339ca600c730c9eca19443987443294621cc2b2392a310e619518e5148730ca8c6a8a43985647254521cc26d386c610e61955943108730ac8ea90843986676548421cc332b2a4210e61711cd21087309b2e730043986d03158021cc26a38ac7a06615c9c754d0330ba0e2b1e81985d07150f40cc30f2a0c6a06611e5db5410330ae4e3aa081986596598c40cc26cbb4862066136dd94310330ba
  | 11 => 0x10332b10c528881559ce6094440aaae7304a2205667298251102b2b94c1288811d9db5354440acce5a9aa22056572d4d51103a8382a6a88811d9d85354440acce429aa2205657214d51102ab39ea4a8881555cf5254440e8ca7292a2207455394951103a329aa4a8881d154d5254440ea4a6302a2207515318151103b1290c0a8881d85486054440ae4e131aa2205347458d51102b3b92c6a8881591c96354440ae0e0b1aa2206556318d511023bbb286a888159dc94354440ac8e4a1aa2205737050d51102b938086a88815c5c04354440ae4e1312a2205347458951102abb9ac4a8881551cd6254440ae0e0b12a2206656218951102ab39cc0a8881555ce6054440acce5302a2205657298151102ab39880a8881555cc4054440acae4202a22045d7694c511022fbb2a6288819394e6214440c9aa7310a22064e535885110326a9ac4288811b5da5214440c9cc7290a22064d639485110237bb2a4288819398d5214440c9ac6a90a22065653984511032aa9cc2288819994a6114440ccaa5308a22047776544511032b31aa2288819558d5114440cccc4a88a220665625445110338a8ac1a0881171da53504408bceca9a822064e53d894110326a9ec4a08819394c6250440c9aa6312822046c769494110327b1ca4a08819318e52504408dceca92822064f63549411032631aa4a088195d8e5150440ca8c728a8220667629454110332314a2a08819694f6050440cb2a7b02822066a52d814110334a96c0a08819c9476050440cb2a7300822066952980411032ca9ac0208819a5496010440ce4a2b00822046e729973110236b94cb988819a54a60cc440ce2a3306622065a535833110334a92c1988819c54560cc4408dce532c622046d72996311032ca9cc1188819a54a608c440cb2a6b04622066952582311033928ac1188811bdc9654c4408d8e4b2a622046e721953110236b90ca9888187d91534c440aa8e2a9a622046d75d89311032729ec4988819354f624c4408daea312622064e531893110326a98c4988811b9da524c4408d8ed292622046e7654931102363b2a49888199d8a514c440cc8c528a62206376454531102aa39aa29888199d89514c440cc8c4a8a622065953d813110338a8ec0988811b9ca650c4408dae532862205557194c31102aab9ca21888155dd5310c440aaaea9886220657654c4311032ab2a6218881651d1310c440b88e49886220746524c431103a2a92621888174dc1310c4408bce732c422045d73996211032ca9cc1108819a54a6088440cb2a6b04422066952582211033928ac11088117dcd65484408b8e6b2a422045e73195211022eb98ca90881175d763484408baea31a422045e7694d211022e3b4a690881179d953484408b8eca9a422065763945211032a31ca2908818dd915148440caec6a8a4220
  | 12 => 0xa0a811b9d76250540c9ea7b1282a064c53d8941502373a8c4a0a8193d4c6250540c98a631282a046e76d494150327b1ea4a0a819318f52505408dcec29282a064f631494150326318a4a0a8195d8f5150540ca8c7a8a82a066762d454150332316a2a0a8195d8c5150540ca8c628a82a0667621454150332310a2a0a8196d4f6050540cb0a7b0282a066b52d814150334296c0a0a819c1476050540cb6a630282a0658531814150335a90c0a0a819a1486050540ce6a230282a046f725973150236392cb98a811bdc9658c5408d8e4b2c62a046e72d953150236b96ca98a811b9ca654c5408dae532a62a055671d4d31502373aec498a8193d4f624c540c98a7b1262a046e751893150327a98c498a819314c624c5408dceda9262a046c76d4931502373b0a498a811b1d8524c540aace7a8a62a066762d453150332316a298a8199d88514c540cc8c428a62a046f725943150236392ca18a81555c4530c540aaae628862a0556754c431502aa3aa6218a8195995310c540ca8ca98862a05c4724c431503a3a926218a81d1149310c540cb0a730062a066852980315033828cc018a819614d600c540cd0a4b0062a067051580315022fb9acb10a81171cd65885408bce7b2a42a045d73d95215022f39cca90a81175ce65485408bcebb1a42a045e7518d215022f3b6a690a81171db53485408bcec29a42a045c7614d215032bb1ea290a819518f5148540acce5a8a42a065763145215032a318a290a8117dcd65085408b8e6b2842a05657214421502b33aa4210a81591d52108540cccca90842a06646548421502e239a4210a81d1d4d2108540e88a690842a065853980215033828cc010a819614d6008540ce0a2b0042a075053d4740503a9a98a3a0281d414c51d0140ec6a428e80a076052147405038a298a320281c91485190140aace3a9ca62055571d4e5310237b92c3298811b1c96194c40ab4e1b0ca62054f7258653102a6392c329881955846194c40aace3304a6205557198253102ad384c2a9881471d16154c40a9ee4b0aa62054c7258553102ac382c2a9881955846154c40aace3302a62055571981531022fbb2a6298819554e6114c40caaa6b08a62065953583431032b29ec2a18819594c6150c40cb4a7b02862065a53580431032729cc5a88819354e62d4440c9ca6b16a22064d5358b51102ab39ea328881555cf5194440acce5a8ca22056572d465110237b92c7288811b1c963944408bee6b14a22045c7358a51102b3396a728881595cb5394440ea0e0a9ca2205667214e51102b2b90a728881559cf5294440aaae7a94a2207465394a51103a2a9ca5288815c9c36394440acee4b1ca2205647258e511032ab18c7288811d1d94394440acee4a1ca2205647250e51102b9b8287288815c9c36294440aaee6b14a2205547358a51
  | 13 => 0x6508740ac8ea90843a05c47348421d02f1b824210e81559c75394e408dee4b0ca72046c72586539022fbb2a629c819594c6150e40caaa630a872065a5318143902ab39ea328c81599cb51946408dee4b1ca32046c7258e519022fb9ac528c81171cd62946408eeeca88a320654639454190332314a2a0c819518d5150640cc8c4a8a8320672511814190237b92ca98c811b1c9654c6408dce5b28632046d72d943190237394ca18c811b5ca650c640aaae329863205557394431902abbaa6218c81555d5310c640b28e898863205c4724c4319022fb9aca90c81171cd65486408bce7b28432045d73d94219022f39cca10c81175ce6508640acae528843205677548421902b2baa4210c81691d12108640b88e690843205587359740902b838acba0481559c764d4d40aaae3b26a6a054e72d8753502a6b96c3a9a8195d8661d4d40caea730ca6a065753586535022fbb2a629a8155dc55314d40aa8e2a98a6a046f725845350236392c229a8153dc96114d40a98e4b08a6a06556118453502acb80c229a819614e6090d408ecebb0a86a065753d85435032a29ec2a1a811d9d46150d40caea630a86a065453185435032c29ec0a1a8196d4c6050d40acce529ea2a05657294f51502b3b92a7a8a81591c953d4540e8ea7a96a2a074453d4b51502ab39ec9a8a81555cf64d4540acce5b26a2a056572d9351502b3396c7a8a81595cb63d4540caec731ea2a04777650f51502b3b9287a8a81591c943d4540ae6e0a1ea2a05707050f51502ab39ec5a8a81555cf62d4540ccec5316a2a064f5398a515032629cc528a8193d4d6294540c98a6b14a2a064e63d4a5150326b1ea528a819598f5194540caac7a8ca2a066662d465150332b16a328a81179db53545408bcec29aa2a064f53d89515032629ec4a8a8193d4c6254540c98a6312a2a064f63d49515032631ea4a8a811ddd95114540aaee6a88a2a05547354451502b3b92a228a81591c951145408dee4b18a2a046c7258c515022fb9ac428a81171cd6214540caccba98a2a04757694c51502b3394a628a81595ca53145408eeeca98a2a05677254c51502b2392a628a81959945314540ccccba90a2a074753d4851503a229ea428a811d5da5214540aace7290a2a055573948515023bbb2a428a8155dcd5214540aa8e6a90a2a07475314851503a2298a428a8159dc96314540ac8e4b18a2a06556318c51502b8b80c628a815c9c24314540ae2e1218a2a04777650c51502b3b928628a81591c94314540ae6e0a18a2a05707050c51502abb9ac428a81551cd6214540ccac4310a2a05717018851502abb9a8028a81551cd4014540acee4a00a2a056472500515032c29cc120a819a14a6090540ce0a330482a0658535824150334292c120a81179d763505408bcea31a82a045e76d4d415022f3b0a6
  | 14 => 0xe63224210ce57019121086733b6a890843391da5448421d48c92a24210ce77655121086723b2a890843a91915448421b8ee6aa24210dc47355121086f1b82a890843781c154484219ccec2a24210dc67315121086e2b98a890843789c05448421bc2e02a24210ec765d8d21087a3b2ec690843b19936348421d88c9b1a4210d657598d21086e339cc690843395d66348421ccaeb31a4210ce67498d210867339cc690843319ce63484219cae131a4210d677558d2108762b18c690843399d06348421d8ce631a4210ce57018d21086e33b0c690843b19d86348421d8eca31a4210f476518d2108763b20c690843b19906348421d8ac831a4210ec46418d2108763ba8c690843b15d46348421d8ee831a4210ec67418d2108762ba0c690843b11d06348421d8ea831a4210ec65418d2108762aa0c690843b11506348421d8ee031a4210ec67018d2108762b80c690843b11c063484219cceda9a4210ec463d4d21086f1386a690843785c353484219c8ed29a4210ec46394d2108673bb2a690843391d95348421d88c6a9a4210ce67614d2108762318a690843d154c53484219cceda1a4210ce576d0d210876231e8690843399da43484219caed21a4210ec46390d2108673bb28690843391d94348421aceeaa1a4210d647550d210876231a869084378dc14348421bc0e0a1a4210ce77610d21086723b08690843599d44348421acaea21a4210ec46310d2108763b1ec090843b118f60484219cce9b024210ce673d8121086b2bacc090843719ce6048421b8ae73024210ec46398121086b3baac09084369dd16048421b48e8b024210dc77358121086e239ac090843b1d8d6048421d88c6b024210ec4631812108673bb243a8043711cd21d4021d8cc690ea010ec5634875008673bb24328043711cd2194021d8cc690ca010ec56348650086f1b824328043569cf5094021cb0e0b1ca010e5663d06500863abb083280439598c4194021ae2e020ca010ce77648550086e239a42a804378dc121540218bce6322a010c5d7319150087a219062a804339dd92114021b88e6908a010c7b7654050087b090aa02804399d8b6154f40ccec430aa7a06646218553d0339b0ec0a9e819c1876054f408beeca98a7a05547154c53d02aa38aa7a1e81551c55310f40c9ec7b12a3a064c63d8951d0327b18c4a8e819318c6254740cb6c7b02a3a065863d8151d0335b16c0a8e819a18b60547408eeeca88a3a05547354451d02b2392a228e81551cd51d0740ac8e4a8e83a05547354441d02b2392a220e811b9cb65cc7408dae5b2e63a046e72d9631d0236b96cb18e811bdc9654c7408d8e4b2a63a046f7259431d0236392ca18e81551d5310c740b88e498863a05d3704c431d022f39ecb10e81175cf65887408bee6b2a43a045c7359521d022fb9aca10e81171cd
  | 15 => 0x797019743086ad386a7a18431d5d661d0c219cae530e8610c7a70d96430863cb86cb218431e9c26590c218f2e132c8610c75759864308672b94c3218431d9c66550c218f4e132a8610c7970995430862fb9acaa18431edc16550c218f0e0b2a8610c5e7694d430863aba8c2a18439594c6150c21caaa630a8610ce572185430872d298c0a18439654c6050c218ece23288610c7a70194430863cb80ca21843175db5310c21ab4e1a988610c5d7614c43086aa39aa9a08435c1c154d04219cae531e8210c757614f41086b2baec5a0843719cf62d04219cee4b068210c5e73d96410862eb9ecb20843179cc65104218bae63288210ccc73588410863bbb2a820843551cd5410421ae0e0aa08210c757614c410863bbaac420843351cd6210421b88e6b108210ce7755884108733baac420843b1dcd62104219c8e6b108210ec473588410866239ac42084339dc16210421ccacba108210e65651084108672b94c9988431d5d464cc4218eaec2a66210d557315331086b8b80a9988435c5c353cc421acaebb166210de17018b31086733b08598843719cc42cc4219cee4b066210e4d5398a310863aba8c818843395c8640c4219e2e03206210c757615031086aab98a8188435c5c0540c421aaaeb3186210d7170d4c31086aabaca6188431ddd9530c421aaeeca986210e577654c31086aa3a2a618843d11c9530c421aaee0a986210d5775d0c31086e33968618843555d4430c4218eeeab106210ce7755883108733baac418843391d1620c4219cee0b106210ce776d0831086e339e8418843395d8420c421ccacb9906210f4553cc831086abbac641884395596320c421b8ce51906210ec5628c831086aaba8641884395594320c421ccaca1906210f46650c83108762b286418843d1594320c421c8aca1906210ec6640c831087623206418843d1950320c421e88a81906210ec4325803108678b80c7108431d5da5288421d4cc9a144210ec663cca210876231865108431d5d664484219ace73224210e5765d8d210863abacc690843359ce6348421caeca31a4210ec77218d2108762b90c6908439518e5248421d88c72924210ea464d09210876231e8490843399da4248421d88c72124210ce47650921086e3b9a8490843711cd4248421d88c6a124210de37050921086f03828490843b118c4248421d88c79924210ce6768c9210876231c6490843391d93248421d88c69924210ec4630c92108732baeca90843399d365484219cce7b2a4210ce570d9521087333b6ca90843595d66448421b8ce73224210dc5739912108672bacc890843995d664484219cce93224210ce673991210876339cc890843319ce6448421d8ae73224210ce57099121086b3baac89084371dcd6448421b88e6b224210de37059121086f0382c890843a99d064484219cc
  | 16 => 0x8726bb6a619443539d3530ca21e8ce3a986510d4d70d4c32886e3388a619443725c0530ca21a98eba186510d4e7510c32886e33888619443331cd6210621c9ca6b106310dc5710c831886e23926218c435c5c053c86218bee6b24a110c5c735925088636bb685284435a5c04294221c9ec6192a110c7b76540508872cb1aa028443179ce60d51218bae7306a890e5663586544872bb1ec2aa2439518f6155121cb6c7b02a890e5863d815448739b0ec0aa2438ed906055121cb6c6302a890e58631815448739b08c0aa2430fdd95415121a70e0aa0a890c777158c544862fb9ac02a243171cd6015121ab6e0aa6a690d587055353486aab8ec9a9a43569c364d4d21ab2e1b26a690e5b6098353486aab88c1a9a4317dd95314d218eee2b20a690c7b70590534863c382c829a43175da5414d218beecaa0a690d5b7055053486ac382a829a4355dc56414d21ab6e0b20a690d587059053486aab88c829a43569c06414d21ab2e0320a690d5a70d8453486acb86c229a43555c76014d21aaae3300a690e5960180534863ab8ecba1a431d5c76590d218f4e1b2c8690c7970d96434863d384caa1a431e5c26550d218eee2b2a8690c7b70595434863c382caa1a431d9d76150d21caea7b0a8690e5453d854348673396c2a1a4395d4c6150d21ca8a630a8690e5b53d81434872c29ec0a1a4396d4c6050d21cb0a63028690c7771594434863d380ca21a431e5c06510d218eceb3088690e5453984434863a3aac221a439514d6110d219c8e4b088690e4c5398b414872629ac5a0a43179cf65505218bae7b2a8290c5f73595414862e39acaa0a43179d763505218bcea31a8290c5e76d4d414862e3b6a6a0a43179d853505218b8ec29a8290e2c54d894148727a9ec4a0a439314f6250521c9ea63128290e4c53189414872da9ec0a0a439614f6050521c76a83028290e3854181414872da98c0a0a439614c6050521c98a73166290e4c5358b314872629ec498a4393d4c624c521c98a63126290d54754c431486e23926218a43539ce54885218bce7326a090c5d73993504862f3b6a6a824387d935354121c38c9a9aa090c5e7614d504870fb20a6a82438719053541218f6eca80a090d3874540504862fb9ac828243171cd64141218bce7306a810c5d73983540863db82c72a0431e1c163950218bee6b04a810c5c73582540872bb18c2aa0439518c6155021cc8c430aa810e5b63d81540872c31ec0aa0439c1876055021cb6c6302a810e58631815408738308c0aa0439c9c46055021ce2e2302a810c3f76550540872a38ac62a0439558e6115021cb4c7300a810e5963980540872d31ac02a0439658d6015021ce4c2b00a810e726158353086ad386a729843569c36354c21cc8c430aa610c5f7654c530863db82c8298431e1c16414c218f4e032e8610c
  | 17 => 0x8863749c0544c431ba2e02a26218ec765d89310c7a3b2ec498863b1993624c431d88c9b126218d5575989310c6e3394c49886355dd5624c431d8ac43126218cd674189310c66ab80c498863719d8624c431d8cec3126218ec765189310c7a3b28c498863b1d90624c431d8cc83126218ec564189310c762320c498863b1dd4624c431d8aea3126218ec774189310c7633a0c498863b15d0624c431d88e83126218ec754189310c7632a0c498863b1550624c431d88a83126218ec770189310c763380c498863b15c0624c431d88e03126218cd676d49310c762316a498863749c3524c431ba2e1a926218cd476949310c762314a498863351d9524c431d88c4a926218cd676149310c762310a498863d1548524c4319aceda126218cd576d09310c7623168498863359da424c4319aaed2126218ec462909310c66bbb28498863351d9424c431aaeeaa126218d5475509310c762312849886374dc1424c431ba0e0a126218cd476109310c6ab3a88498863555d4424c431d88c42126218ec762d81310c762316c098863359d3604c4319ace5b026218d5575981310c6e3394c098863715ca604c431d88c53026218d5775581310c6cbba2c098863651d1604c431b8ee4b026218dc472581310c763b12c098863b1189604c431d88c43026218cd7764c7500c6e239263a8063b198931d4031d8ac498ea018cd7764c6500c6e23926328063b19893194031d8ac498ca018dd3704c6500c6b5396a128063175d84394031ab2e021ca018e4f4398a500c72621cc5280639998b41940318eaec20ca018e6662106500c6b8b80832806335dd93154031b88e498aa018dd3704c5500c637390c8a80631b5c864540319aeec988a018dc4724c4500c63dbb2a028063d44c55014031c9cc6b16a910e5663987548872ab1cc3aa4439958a61d5221cb4c7306a910e59639835488734b14c1aa4439c98660d5221cd2e5306a910e5a63583548872cb1ac1aa4439c98560d52218bce6302a910c5d73181548861fbb2a82a443531cd6215221ccac5308a910e6562987538863db82c929c431e1c16494e218beeca98a710e59535805388732b14c229c439a58a6014e21cd2e5300a710e5a63580538873930ac029c431e9c265d0e218f2e132e8710c7a70196438863cb80cb21c431e9c26550e218f2e132a8710c7b70595438863c382caa1c431e9c06510e218f2e03288710ce47258443886a739ea9a14435a9c354d0a21ad4e029e8510e36541854288636bb6a821443539cf5410a21ad4e1aa08510c6d7614c42886b5380a621443331cd6110a21ab2e029c6510c5e7694d328872b298c2994439554c614ca218baeda986510d597014c3288672b88c8194433a5c0640ca21a9ae72a06510c6d761503288636bb6a619443335db530ca21b8ce3a986510d4d76d4c328
  | 18 => 0x15031cd2c4b00a818e7261580540c6a6392a9a1863561c154d0c319aae33168618d5575d87430c6e3396c3a186335dc560d0c319c8e4b088618c5f76550430c6a6392a821863561c15410c318beeab088618ccc72584430c6e2392c22186335dd56110c31caeeab088618ec772584430c66a392c221863b11c96110c31988e4b088618cd770584430c6b5386a5290631bdd952148319aae331e8418cd573987420c63d386cb210631e5c365908318f4e132c8418c7970996420c66ab8cc721063355ce61908318f6e0b2a8418c7870595420c66ab88c6a10639318e5250831c98c6a928418cd573185420c733290c2a1063995486150831cd4a43028418e6952181420c66ab8cc919063175d4648c8318baec2a46418d4d72152320c6acb80a919063555d7618c831ba2e030c6418cd771582320c6a6b90a819063565c0540c831d8842b086418cd775584320c72bbaac219063351d1610c8319aee0b086418d6472553410c6b8382a9a0863555d763d0431b8ce5b1e8218d557510f410c66ab9cc5a0863359d832d0431d8cc41968218cd773583410c666392c6208631ddd95410431ac8e4aa08218d7070550410c63bbaac620863391c96310431b88e4b188218cd77558c410c72bbaac620863b1dc963104319a8e4b188218ec47258c410c662392c62086335dc16310431caacba188218d557510c410c72ab28862086335dda3210431d8cc51908218cd5760c8410c74b3268398863175da538c4318eaed29c6218e9664d0e310c7633146518863175d6644c43199ce53226218e4f65d89310c727b28c498863b1dc4624c431d8ae23126218e9464d05310c7623168298863359da414c431d88c520a6218cd476505310c6e3b928298863711c9414c431d88c4a0a6218dd370505310c6e83828298863b1188414c4318eaeb3226218ce672991310c74a3268698863359da434c4319a8eca1a6218dc77250d310c6e2392869886374dc1434c431ba0e0a1a6218e6765d89310c733b28c498863b1d8c624c431d8ee63126218ec653189310c763a18c498863b190c624c431d8a863126218ec443189310c66b3b66498863b118b324c431d88c51926218ec4624c9310c72abaeca98863359d3654c4319ace5b2a6218cd570d95310c72b3b6ca98863555d6644c431b8ce53226218dc572991310c66abacc898863955d6644c4319ace93226218cd672991310c763394c898863319ca644c431d8ae53226218cd570991310c6abbaac89886371dc9644c431b88e4b226218dd370591310c6e8382c898863a59d0644c4319ace43226218cd570191310c66b3b6a898863351da544c431d28c92a26218cd776551310c66a3b2a898863a5191544c431b8ee4aa26218dc472551310c6e9b82a898863741c1544c4319acec2a26218dc672151310c6e2b90a89
  | 19 => 0x6b088518ccc7258c418c637b92c9284631b1c964942318baeda1ca118d597010e508c63dbb2a0284639a58950142318dce5306a898c6d72983544c726b1cc52a263999896195131c9ec7b12a898e4f63189544c733b16c2aa2639918b6155131cb6c7b02a898e6b62d81544c734316c0aa2639cd876055131c76c8302a898e5b63181544c735b10c0aa2639a1886055131ce6c2302a898c3f76550544c69c382a82a2631bdc960151318d8e4b00a898c6e75d89434c6373a8c4a1a638d1536150d31c76a83028698e3854181434c6b5b82a9a92635a1c154d4931a9ae7b26a498d6571d93524c6b5386c9a92635a5c364d49318deeca1ea498d677150f524c6b238a87a92635adc143d4931ad0e0a1ea498e6b60983524c6a6b98c1a9263595c460d49318deeca90a498c7b70590524c63c382c8292631b5da54149318deecaa0a498d6b70550524c6b4382a82926353dcd6414931acee2b20a498d6b70590524c6b4382c829263535cc6414931acae2320a498d6a70190524c6b4b80c8292635a9c36314931ad2e1b18a498d6671d0c524c6b2b8e86292631bdd94314931acee2a18a498d647150c524c6b5b8286292635a1c14314931ad4e1b08a498d6970d84524c6a6b9ec029263595c76014931a9ae7300a498d6571980524c734b00c0292631e9c265509318f2e132a8498cd671d8d424c727b1ea4a12639318f5250931c9ec62928498e4c63149424c66b39ec2a126399d4b6150931cc8a5b0a8498e6752185424c732290c2a12639ad4b6050931cd0a5b028498e6b52181424c734290c0a12631e9c065109318f2e03288498cd47158c424c727318a4212639358c5210931cc8a53088498cd473584424c732292c2212639914a618c931ccea430a6498e4e6314b414c726b18a5a0a638715363505318dcebb128298c6e75189414c6373b6a4a0a6393d8f5250531c98c7a928298c6e76149414c727b18a4a0a639318c5250531cd6a5b028298e6852d81414c71daa0c0a0a638e1506050531cd6a43028298e6852181414c6b3394a998a63539ca548c5318dce5326a098c6d72993504c6373b6a4a82638bd935254131c58c9a92a098c6e76149504c717b20a4a82638b19052541318f6eca80a098d3874540504c637b92c8282631b1c964141318dce5306a818c6d72983540c63db82c52a0631e1c162950318dee4b04a818c6c72582540c72631ec4aa0639318c6255031ca8c630aa818e6762185540c732310c2aa0639618f6055031cd6c5b02a818e6862d81540c73830ec0aa0639618c6055031cd6c4302a818e6862181540c738308c0aa063969cc6055031cb2e6302a818e7271181540c738b88c0aa0630fdd95415031c9cc6b10a818e4c73588540c73238ac42a0639958a6115031cd4c5300a818e6962980540c72d31ac02a0639a9896
  | 20 => 0x353d0450507a829e8228283d8d4b4114141ec0a5a08a0a0f1853904505079429482282835a9cb6314141ad2e5b18a0a0d7171d8c50506b8b88c6282835c9c64314141ae2e3218a0a0c7b7650c50506b5b9286282835a1c94314141ae6e2a18a0a0d707150c50506ad39ec428283565cf6214141ae2e3b10a0a0d717118850506b938c84282835c5c642141418f6eca10a0a0d5b7350850506ac39a84282835cdc54214141ae0e2a10a0a0d5a73d8450506acb9ec2282835a9cb6114141ad2e5b08a0a0d5b7350450506ac39a82282835adc94114141ad0e4a08a0a0c6e729825310636b94c12988399d886154c41cc8c430aa620c5f7654c53106a6392a6298839354d6214c41cb2a6b00a620d4c7254f43106a6392a621883391c96110c418bce7304a420c5d73982521072bb18c2a90839518c61548418deeca90a420d4c735485210726b1aa4290839a5496014841a98e6a968420cd473584421061ebb4a9208831d5da54904419ace73048220ce672982411070fb2ec6a088387d946350441c5ecbb128220e2f65189411071db2ec0a08838ed946050441d30c63028220ea862181411072bb2ec6a088395d946350441d2ca831a8220e6765d89411076231ec4a088399d946250441d8ec63128220ec46318941107532a0c4a08839cd976050441da0c7b028220ee062d814110739b28c0a0883b4d8c6050441da0c63028220ee3621814110770310c0a08839c5d46050441d64a83028220d727090550106aa39a82a8083591c94154041ae0e0a0aa020c7b76540501072cb1aa0280839a5895014041c9cc7316a998e4e6358b54cc72b31ac3aa6639998961d5331cb4c7306a998e6a6298354cc734b14c1aa6639c58660d5331ce2e3306a998e5a6358354cc735312c1aa6639a58960d53318dce4302a998c6d7218154cc61fbb2a82a6639598d6115331ac8e4b08a998ce47258443cc63db82c9296631e1c16494b318deeca90a598e695258052cc63d384cba16631e5c265d0b318f6e0b2a8598c787059542cc66a38ac621663599cb54d0731ae4e1aa68398e1e5418d41cc63abb6a820e63599cb5410731ae4e1aa08398ce47258c41cc637b92c9286631b1c964943318eaeda0ca198d717010650cc63dbb2a0286639a5895014331c9ac7316a918e5563987548c733314c3aa4639958a61d5231cb2c7306a918e6a62983548c734b14c1aa4639c98660d5231cb2e7306a918e6a62583548c734b12c1aa4639c98560d52318dce4302a918c6d72181548c61fbb2a82a463531c96315231caac7308a918d4e72d53438c6ad386a9a1c638d9506150e318baedaa08718d4e72d50438c6ad386a821c63331c96110e318f6e0b24a518c7870592528c637bb2a4294639a5496014a318f4e132e8518c7970997428c63db82caa14631e1c16550a319a8e
  | 21 => 0x6b4b86c9a9283595c763d4941c9ec731ea4a0c6f7650f52506b3b8a87a9283591c543d4941ad6e0a1ea4a0d687050f52506a739ec3a9283535cf61d4941a9ce6306a4a0d4d7318352506b2b88c1a92839398f5294941c9ac7a94a4a0e5b53982525072c29cc1292839ad4a6094941cb6a6b04a4a0e58535825250735a92c129283179db53549418bcec29aa4a0e5b53d81525072c29ec0a928396d4c6054941cb0a6302a4a0c6f7654852506a7b9aa429283531cd5214941ad6e0a90a4a0d6870548525062f39cc029283175ce6014941c9ccba98a4a0c6d7694c52506b5384a6292835a5c253149418deeca98a4a0d6b7054c52506b4382a629283939945314941acee2b18a4a0e4d6318c52506b2b88c629283599c64314941acae3218a4a0c6f7650c52506b3b8a8629283591c54314941ad6e0a18a4a0d687050c52506a7b9a8229283531cd4114941a9ce7300a4a0d4d7398052506b2b8cc029283595c46014941ca8a730c84a0e6452986425072a29ac321283179db53509418bcec29a84a0e5753d85425072a29ec2a128395d4c6150941ca8a630a84a0e675218542507a229ea5a0a83d1d4c52d0541e88a629682a0e54535834150732292c1a0a831bdc963d41418d8e4b1ea0a0c5f7358b505062e39ac5a82835a9ca53d4141ad2e529ea0a0d6b7254f50506b4392a7a8283d2d4f52d4141e90a7a96a0a0d5a7394b50506acb9ca5a828356dcd52d4141ab0e6a96a0a0f4b5314b50507a4298a5a8283d414f61d4141ec0a5b0ea0a0f5053d0750507b029683a8283569cf64d4141ab2e7b26a0a0d6a72d9350506b4b96c9a82835adc963d4141ad0e4b1ea0a0d737158f505063dbb287a82835adc943d4141ad0e4a1ea0a0d737150f50506b838a87a828356dcd62d4141ab0e6b16a0a0d737158b505063dbb285a828356dcd42d4141ab0e6a16a0a0d737150b50506b838a85a828393d4e6294141c98a7314a0a0e4f5358a505072629ac5282839398f5294141c9ac7a94a0a0e4e6314a5050726b18a5282839698f5094141cb2c7a84a0a0e6a62d425050734b16a128283179db53541418bcec29aa0a0e4f53d89505072629ec4a828393d4c6254141c98a6312a0a0c6e76d495050727b1ea4a82839318f52541418dcec292a0a0e4f631495050726318a4a82831edd95014141ab6e6a80a0a0d587354050506b5b92a0282835a1c95014141ae2e1a08a0a0e5a65d4c505063cbb4a6282835a9ca5314141ad2e5298a0a0c7b7654c50506b5b92a6282835a1c95314141cb4ca298a0a0e6a65d4850507a5a9ea428283d214f52141418f2ed290a0a0d5a7394850506acb9ca4282831edd95214141ab6e6a90a0a0d58735485050735328a428283d2d4c5214141e90a6290a0a0f535358450507a829ac228283d8d496114141ec0a4b08a0a0f5
  | 22 => 0x2875c5c764d4143ab6e6b0ea0a1d6b725875050eb4392c3a82879998b5194143ccac5a8ca0a1e66621465050f32b10a3282879c9875094143ce2c3a84a0a1c7676d455050f33b16a2a82879918b51541438ecec28aa0a1e67621455050f32310a2a82871edd95014143ae6e2a80a0a1d70715405050eacb8686282879c9975114143ec6a5a88a0a1f5163d445050fa9a1ea2282871e5da5114143ad4e5288a0a1d69729445050e3dbb2a2282875adc95114143ad0e4a88a0a1e72651445050fb1a90a228287d81485114143ea2c6288a0a1f53431445050f99218a2282875c9c76314143ae2e3b18a0a1d737150c5050eb838a8628287565cf6114143ad4e5b08a0a1d6972d845050eacb98c2282870f5da5490c438baed2a48621cd6719824310f1bb2ec2a18878dd946150c43c76cbb028621e3b651814310f58308c0a188795d976150c43caeca30a8621ec7621854310f62310c2a1887a59506150c43cb6cbb028621ed061d814310f2db28c0a1887b4d846050c43da0c23028621e59751814310f4d2a0c0a18871b9ca60944438dae5304a221c77765445110eb2392a228887995895114443ce2a2b00a221d5a7090d5010eaa38a86a8087561c143540438f6eca80a021e71615405010ea7396a729e831b9ca6094f418dae5304a7a0c5f7654c53d0672392c221e83539cf5294b418bce7304a5a0c5d7398252d0637bb2a4296831b9cb63543418dae5b1aa1a0c5e73d8950d062eb9ec4a86831edd95014341a9ce5a9ca720d5a70d4e539062fbb2a629c839394c6250e41c9aa63128720e5653185439072d298c0a1c839654c6050e41a9ce7a94a520d6a70d4a5290637bb2a429483569cf5094241ad4e5a84a120e4e6398a5090726b1cc5284839398d6294241c9ac6b14a120e5663d06509073331683284835c5c341942418dce5b1aa120c6d72d8d509062f39ec4a8483175cf62542418f6eca80a120d4e72d9353506a6b96c9a9a83569c364d4d41ab2e1b26a6a0d5571d8b5350727b14c5a9a83539cb61d4d41a9ae5b0ea6a0d4e7218353506a6b90c1a9a83555c460d4d41c9ea7314a6a0e4f5358a535072da9cc129a8396d4d6094d418beeca98a6a0d4f7254c53506a6392a629a8356dc15314d41ab0e0a98a6a0c6e729805350636b94c029a8355dc56214d41c9ac4310a6a0d557118853506a7b92c229a83531c96114d41a9ce5300a6a0d4d7298053506aab8cc029a83555c46014d41ca8a730c86a0c6e75d894350727a9ec4a1a839314f6250d418dcea31286a0e4f531894350726298c4a1a839514f6150d41caea630a86a0c7a75d81435072da9ec0a1a839614f6050d418f4ea30286a0e5b53181435072c298c0a1a835a9c253d4941ad2e129ea4a0d6b7054f52506b4382a7a9283539cf64d4941a9ae7b26a4a0d6a70d935250
  | 23 => 0x2800801200800080000040010030008000002001807c008000002002c00200400080000020010008018000003002000000200a000000400e000004800400400000600000000040010014000004001802c000000000000400400000080e00040000008008000004001000c002003000801c00600900000780000000048038002004000000401a000004800000e0070008000000002005800800000a00300100180030090000004001000000000601500080080300060000000000001000000c0000000000004006003001000c00000300600100100020000070002009000000800000600c0030000004000004c000003002800800a000000000000e03100300240060080040000002003000001c0040000068000004004005800000200000280540080040000000000011000800800000000100040020000068054002001007800400400200400180060000008024000024000800001a0000000004000002001801800000100000040040000018044000000002801c0000000060004000001000000c004004001000c00c00a00100080020020000000000001005000400000000c002400e00000000000040000010000000000000003c00000100180080180000000014002000000800400e00000380040020060018000000000004000400000c003002000c001000000000201800080180000170000004000002001800400401d003000002e0090000024000024000800000c00000e800400400b001000400000100080040000010038008001599cb51947438dce5304a3a1c6d7298251d0e3bbb2a228e871b9cb61543438dae5b0aa1a1c7b7654050d0eb3396a328c875c9c351946438eeeca88a321d7271d425090eacb8687284879998a6194243cae8730ca121e66625865090f32b12c3284871b9cb61542438dae5b0aa121c7b765405090eb3396c9a8a87595cb64d4543ae4e1b26a2a1d7170d935150eb3396c7a8a87595cb63d4543aaae7b16a2a1e676298b5150eaab98c1a8a87599c860d4543acae4306a2a1e6662d465150f32b16a328a879ad4a6094543ce6a3304a2a1e6b525825150f39a8ac128a879ad4b6054543cd6a4302a2a1c77765445150eb3b92a228a87591c95114543ae6e0a88a2a1d70705445150e37394c028a871b5ca6014543ccccba90a2a1f4743d485150e3abb4a428a875c9c25214543ae2e1290a2a1c77765485150eb9b82a428a875c1c15214543e8e86290a2a1d5570d0c5150eb3b928628a87591c94314543aaee6b10a2a1d55731885150f32b10c428a87555ce6014543acce5300a2a1d65729805150eaab98c028a871bdc961d41438d8e4b0ea0a1f6352d475050eb5394a3a82875a5ca51d4143ad6e4a8ea0a1d68725475050fb1a90a3a8287d814851d4143ea6c628ea0a1f53431475050eb938ec9a8
  | 24 => 0x380000060010010004000005001802400000300200000000080000004000003000000c00a008001801000a0000008008020001003800000a007000002c000006000000000002400080180020050000010000000001809400000300000040160180000000002003002802c062000000002000000400480140120060000044002008010000401a0020030004006004001001c0100080028014002011001000c000003002000005800200500400000020058000002001000800400c01d002800c02000000000140000010010004004011000802804200000000140000000000000004000007800c00a009001004c002008007800001a0030260000060004000800800600000000000200000008010000002002001800400d001003000400100800040100040030008054005003000400c001003001400a025001800c000008000800000400d0090000016001000002c05c00100b0000000001003803400600f000003003a00b000001400002c004800001c0110008018000000000000c00400700080740040000048014000000001002800e00000280140000050018000010000002000c00200e0040004006007003802000c005001001c01c010005001002600a001000001200e001802c006001000800c00e001001801c004001000800401a00d000000003e0060040008002001007801c008001000000000600300380600180000028028000000000800002401500000400060040000010000000001000800800300100440000040000004006000002000000000a000002800200500000200000000018004066001000000c000000000002000800500300040040000000008008004000800c010004003000400400100100280000000030000000000000001c0040010010008010013003000000000300080b8000000004007c0020000020000000000001000000000200480080000000028000000001002800400e000001000800000000000340020000000030034000009000001400300100040100000000034006002002001c0060010010064004014000001800c00000100000020050000014000000000008000a0000008004000011004000000a003000801402400500280100040040010020000001000000803c000008802000000200000040020050060014000002001800c00800f000800c0280000000004018000001001401000500980100060050000018002006000800000e000001005000c000006800400a0030000034006000002000000c0060018008000027001801c002001000000400400200000040080010000018000001000004c00200d005805c00e00100980040020020030000000001003000801000200080000000020010000004000000000c04c000002801000000700300700000000000004002000003000c00002700180000
  | 25 => 0x31581740006cfa000000520116e8c640b057f8b9e216760000003bd7466e0e4a00000000000071828daa400056d94ec0000ee9118d680003972e84001c703ac28c001600500100500000050008000002002000002c01001c007800000a00d0018024004001011802c03000100180040000000020018006011000800000000b00180340020040028010004000000001c00a00a0000000002041008000001401b002800000c0000038000016000001000000000300a8014002003003005800e00a000000003200100000000000060018000000001014000400a0000008000000000000000c02a00200280000060010058018006001000000802200300100000140020060004000005004803c0020060000004006002000000000a01a001800c00200600b804800200000280140040050030000012003005800800600b001801c00c00100200000020000008014018002000800000200000080480000010030000000000000800400a001001003000c0140070000010010003001400600600d0000000000000800002e00000500000200060018014002000002002800e0010020014000000000000000c0030000020002004007800400400000080180020000000008000003000800000e002001000c000002000800800a00100000100040070078000000001001000400e00d0000018000003008800c008000000001800a001001000001200401500040220020070010002000002801c012002004000001a0000060000000000000800800000000a80080000010008088004008000000000600300000000060000008010006000002000400a0000008014000004001800000600000000000000030028010006001002800c00400000080080000000008020000005011000000000600000100060040028000000000002800400800100000000000050008018000000002804c000003002000800600700a80340020030000000026000000000000000000080040000010008024000000000000003c00700000740020050008050004001006001000000000000040080030038008000006007802001000100a800000a0060020014002000003800c00c006001000400a005000000000c0000070090006000000000000201700100180060060050000000000000001000000e00100100000000018004002001000000000a0030020000000002000000c00a000004802c00200800180000040030000000002002000002404600000380000060040010004000005005801400c00300200000080020018024000008002000c00c009000000800c0020000028000006006001003000000180180040080000004010001000800400e002000001000c00d0040000046005001000000000000e800000400100080000060010000004000002000003401a0020
  | 26 => 0x177b4e881000027d516400000056e8f208581114fe83300000000001962e9a0004cb8000c2e00000000000000228001e989980000000000000097373e79c00040528625acf06672422831c606be46323255dfa306099c53c7605dc0d700c96529f0f28a381b7200071900e89a20bc0001cfdb64de816b800006500050100010640000d200b40002a90002f1800000000000011849db0000c2114288e038b0c8000b192d35d4c2000005b12fccc738283982314b4b04f4ec867a0c0dfe7040842a2ca8359756f016a9b200030ec39a00047400007ac88ea208001ad4d710c6497c00000000000007be000000000116cba544900000000000000000000000137800000064a000000000099f000105c000c7c000071d8ecab771fb659988b63000000000000000017cacf800010f9d8000000000006ed66e0000003d1d3940003c8195c000000000224643000064ba4c550700047694980006760f700003ee9bc0000000e6171580017b65280000002d5600005e8002b87cf2000000000000009f60a8e710a0c9a0001cc421e182ce2bbb196b0005094001d9e02b63c8f14e4200058ac00179ce5e00008411e69604f4cdecb240d53879741a6819924b15e197eb8a05ed1d1413f49125aa1066abeb25d317c0f257e2e063bb02c2765c09100bbecbc2ff9209e245ec66824d0c1a3e527828748189a941688e91bf48066480000000006a099a1368c6b0b2227a21bec739c9f5101a2861e3000073e33f2aa198c1cc0000001b2e673edb0001e8c000b1151322dcfbe00000000006962620000000000000000000000000000025c090c0004f60001ac64eb00002a00003a556dc00000070f8002355d728af5f6355862c95b236c4c54342120aa15d994a7c98783b82d9daa7000000171c90c51cbcd1102cd2264178f14669560a19590d0000329ebccb2a00047a400145200000000000000243d618083c60000064000000000000291c00029a11d800070a27f40933f0000a0637480009300000003a40cf000000036c0728e2a0000d08000000000000000075c55e1ba6f7edc1232c00000041b3ab0d500000004ba800045800000019dc6904b81b60658a1c7083a3926cdcd7bb000247477074034780000000006160000a6a94584f0de1c16ef3000205c0001d978e40000006def1d8001c5a000000000000000040bc00000000e59b1c497ee0006f184d80005237582b683040001652ebc6502068bf396d5160001de8eacfe000066980000009eb8000000000a3f75b2e851f20000001fbd44e0000b70000000000000000070813b800114c000d7c3920d491d73f02c780000000003fc000009f00045cb07c4c646072e156ed6064e5f727848e42590611e503434c90000000000e1e0001f2a84d0000000001892885782d250000b5401280019700004900
  | 27 => 0x87e989f59d0001bdc1866ef800000000006d97c9f44000ee35e616714de8d34502c7a4b85620fa9aa00503714e391ad598ba356895f6fec1de0c200b01396c9e270585a527b74a7149418d3b45873321aeaefd8001a3e5481d98000a2cd4e81900029eeda100040ce68c0000004942ba988a5cad212640b840dd1751b9c0008ff2e68096c38b5627a032b6e20003e3ca340002aa1ea8000632000000309ecaa76545aa79534c4873d3955703c608484b32c1b4aa85c000005809bd00036485c5cb511ab610598d2352f2a8abdcde636e6a1409d6996129c394800bd33fa2b4d8c00000004b00001e4000000121c21dc12237a000c210000001bee10247381bc2a2b040d50000e4a026629a7f60000002dc92829ae41534900010080002bf80009d8000000000172abb20500e1c8b53d0170b244000f451678000a24a9e091890cd6e63d7834001d5c0005331c3b64d2080000000fd68d9cf1d7aba308dc000000093400058a800106a0003be80000002f600003e4cf286c7221001614a206a484fd7d23379b7aed12f2f04a1ab8d086c0003db30d8000000082cb6f0ce00077db4a1c02e491b983b4f24f3e77367f8b4f87242432f421000015301d015fcfd4710000000000000000000000033025f8c02de00001a6cf6d9571088628eda0005be041c2d000052925e80000000001188d109ed78d199400076912a9b20000c3f72c040d952cd81d038402325a4d43a4e41eda05280b0c48ce9cd70e858c0006c24100f78000b9d64c00007270002d883cc2f4e0324983b0ae40000d614e8cd401335000011ba624283b68c00000000028b62daa930000000834718d44bbf314c450784d4017e0ad3c68885c0006aa2240b2493285d18508c47ce0000433bca00000076333bd5d85b2008a185b220005a88000000a3b378953c8626668000000fe800000037e9b32b5f00000016fc209002306d560d894a8b66008ed547a5a0a7c4561f0578c84c2225d0fd8c4c000ba43227bdc0d2a3d79d84e928299d774042e05ca9077c0e8c000cf467b8e78000249df6bab56c05a1dd8042409668c429000010600003f2c518f6cc74c683d8732acd0002b51df4ce8525990c9520000000e087cc0004971dc80007ae25bb405c7a40e00001079feab08003c4d02aec40050cac000b863e9000000002cd89b3b502b0ce8dc83a1292a0bf6ca4e8dccf1400034e0dea1605aeb604aa39010000ae80009a40001bb047e0001979c0e00086f1578001de45e32d7b0f1a2a7fb8001304000653000000000000000038140000000000000000e29000111a6c06b300037210b458a237995699408458f9004918df300000017b80000000000000c3e0000000c560000003388bc25ae4b223240000001b29f1cda5ec30000ff43be00000027ffa5a14d0003a9c0000000002b08000
  | 28 => 0xea3bb653a582010002f7c00119a00001c800000000000010600009593e08318000c6d294b00ca21f198001a718500002b0993c000c78175aa000000880000598726c525465b102e10000d68000af635600000008280000001548b8300005f8001de800000039bb9ea9d1535715144600026d9a7a00067cd0628d312190a00000000009f400000003ce0000000e578340003dc40000009e607d0a6c98cee5baf8a044340000000000a580000001ee800004852305400ce2f363aa1f400034347080000000000111184294df60003ae00007db231f5157cc9d00000698000f0000017c40007ce1a4b7b4000a36800000196000000032143aa00000000004a819e3b59375a44c9d2c68000000619572a094000575420136800082580000009420000000000000398032baec00000051617616600000000001e7a00000000016de00000029b0000d5d0002b540000170000000000a303ad80000000000001a7290785674010256cc62331009f438a0000000001de000000012b0c2c00000000014f405472837fdd44c2300023622ce3272270d90bf639b6d7bb43151094253e7016f000000033cd010f1f80000001777870a600008c6bca2f5c6a4000aff5ed3770000d9e87580006a000029586480000006593aad4f850b318b024fd403b1989ac4cd6d1f4911af59f079521538a1666b238002b05e0e8767938819dc29e200022080000005a640003b600040736a9d91ccc59f38440004af0ce806c0000770001bf4000a0804cf112000e23000000088605a00015280008142a9b53400095e42a00000008149eb800142e00000000013140004f4a7c729e00069017a8c34949800000030969e3ce00000000003421578000e2c0001b5c0000004f9d8f12390000001f20000000000000000005662b9b6140f0e9440f930290abe0000000000698d26baf6000000000000000054e40e00002d49000000ef1298000324000000000017f09e507a0c980010900008180000001d26af1d60030557012a00010748d1a10a50375000079a80016f60007e8c438000878a7734240003560000000001420e21000000096a10a00002911141d055d03380008ea43980000fe000053b5c11e21ef2aaaab8a70610129aa600002d980010d00000000003a158c4b3f1b9044c000000000000104e73500002e5241000000000003e00000037780002980c6ba9099c00048880016da12267d21e40009de2cf89b1b2a0002090000000000501400162484b285c0019d81578002c4e0007e6aa48928000eb30000b540000000001598df7b555fdb40c54490625b693800000005997940006f200000009b904a559d512ff300001c000000010b1613134b543fe000000022825602e00000000000000000000000000301e0006ef0f89b340920000000001b4c0005e780006720005e9
  | 29 => 0x16642e50001732adabd04f934680002b402000005a672667080014c200037fc00057265415f1bc350335700021093b8b47567c0000003f800000000000000001ed546eb9000000006167aa0003bba208f0a3c700000000000000000e7c0000000001dbf8970e980003121f303600000000005328000000000000000093f22b3aa25b80000007370001d425f803b28f14020004ca2a8c000236000000000000000029b400000000001da0000003e3658400000054d1b740003e442300000009150003104acd1b6000287e0000000000001a800003dac000f62f468003ce9601b9f1dc8000000cab000237c00000001001a800078600034f6b1c5ef0e90001bc26b906c30da95ca8f09c951c64871b70a8870000dce0001bead960000001e7601808b000000194f000571800000000064621f0000e183518001958c2964daa850a692c00025c800031e0c9c001afc5740e880005b2d216b98000000d16546a4c882cf2d70f945d7de00005908f8b82a5fb308001e3d00004eb895aa60000001e4d6000003671ac80009b678400012ceddd07796212fa24d215976d1eb000743b75d704f3000039fc000000000206c780b4a5e3961c000160c5167aa9680000d880000000005d638f0000e7800029a1cd20006c1800199cb6900026b800000000030711d9b568003a092b50004c1154146200073a3390826c3048d000000031100000011dc50375e00013de3db112800000000077a800000000000000008d22f2054c00142b99100000000000000003c9807ec7700000000005e280000000006e01e70db46f2e54616a6707881a131d9c640001945a90000000859515b2b406cd67794960d2f8579195cc6d4f0000000000000077552dc00000008a057045a00000011ea9ea9c216d8000000000227b918001b9e5b7ebe951eb52a000002870bd6a0d8000fd928800000032a000000062023f4c800002c61b82db6a7001a36d8b6600004ed86d12ceda1d4aa802c45de33241548045990000001c12902788ad428f800060bef888729d33773508000b3800000009960f82e1973ac8f6420003520ddd56a1b513955a47cf80000002fdabd8001ab80000003cd339d8662418001799778ad622a3c59726509799a6e803c06b5d008dce2500032a4000f86d4711cc95c2600330002c90eecee2b2bc000d2800050b00011c6a5b47480016a6570606a2b11360005ae175551cdc23b300000000005bc8000000c06455ce880009e7aa84262de68a9f5519ca00000038800011900007a159149c0428000000055c58044a25bc1885100001a050d682b00009dc000f0260219ec0d70cb47c2253e453d81820001dbba9c4d5b90c0004103ef00000000000000000000000000000000012b60580006660000001750f3094d03c0b6d4e287136a67a1c90ceb1149f18a4
  | 30 => 0xaa63956cbbf88f027a576b8cd5970000000000000ed1f3411e40006be00019d17ec0ac0002b70000000051d12400000002c3c180008910000c40000c1000008ef0145890f1345c0009c836d14140000001a38804dfebdf01b400101f000092924534a71551400000f8000673011b0985cb406215c7b8e1c397491d2f6b062c229c9a229894209644e927be073ca088bb6f903432d8067e9b0bdbb998e85da0002301bf2c1630621b9e018a1ad38b1d558000779f691294e2002e992c71aca669f1e30000abd0000e687d228810b14d14b8bb800000004d26dc3233a6181c0933fe882d95c48b15e96903071f466a961565a98b33802c7da69466da825884a0001499f800009256a32e21712c3781c40000001730003be40005e95df000000039500000000000000000000c440000000000c50c670002171592000000000006ae844d5014d49b000432f900000bae31c2c4b48619288a5d8c28ef4a19e0001468053d2a39e81096004e200000001b73c13c400000000000e3db962971e1800150c2dc00004344a00005e5a5619448066dc00016450000000001a327ad68227ee000ece25b000161200034484040000000000000000d0fcfb29825a8f04000165000070d3b611700006d4055b0e0d215602059605d1ea365ce24f5861d6915c26100009e5a0f997570a488000277c0000000000000a3c00051344dcd2c000205311ddc0f2c000000000064100000000000000000cdc00000000000000003eb33a80005fe08e5ad80018ca00000029479466a12cf0618000000003010aa2a000000270db5c7cc17b81880006340002ec4dd100035794c9bc89850000fd135e28929b92901e429e3e468a72520006bd8040000c86542629358c0001f12ee96921754d60000eb486600031b148bb2300000000004b0000153a000be3737a91a0000002c9800187bd3f00008e0000ae100000000003b35cb0f08428aee58c0001df3000000260cff824200029e522ce5240fb6f844400000031c00009b1000000035e00000034b80000006ed00008b97ca00000000005bf000000000019d8c189110aa00000000000000003ccc001ce68aa646bd0e1f60007903865dda5e214e862084c4b309a8eb45e00001d900000be000465e9fc00000000000011410000ca976626354d3828f50ce9b9171704900008f2000000193870034515ace650370001660bacb0552ade83abe00054080000000004fdb18d52a0000000ea820d0003f3ce4a000f4e69d9496ea4433f6f000054e3401810001ac45a60000cb00006a40003cd80000002d28000000b1bcc78ef8000b3db0a923dc1a748367800069c5ab916a3ec1ee0000002f851de0000001d4014a90f6bc80019940001122895330eb500036a448b6646cec001034ddb4eba550000b0337828783abe9d4b88a264802a280
  | 31 => 0x5cdd3105431f35e000100a1c628f804800069d6f11350000c8e50c9c53cd419b8000000000b6b00000017340006c30000000a30bf240000002835223c747de80b32c1810000b430000001a12d6e58d8468e509d54f187118a045a00030086fc77716b37ec8fcbc50002684000000000000095a92a000000094ca973c682b5e3c00051f31221600001d3b7a80d900000000000000000000000000d246ca101800000003aabc40000000000000c8e9a2343c000950e8313400017860002a60c7000055603841cfcce83635498b55624f36500001810ebe00032cc000837336b17031e0006c71da91c5dd36770838d250e50370000000e720002dd093a6054368001e861fe836800000000052eacb0000f1c00000017f8000007b5fb2ba18d8468dd00000000318015e3e000000291e0000006c036718de9364f6c87519516a8000001d1c48a4c3a63858acf0000222c0000001a300006028f00000000000ec05d681192cc00076e2ac60000003f480018565300000000c3c00000004181a8c4f4dc00000000000702470912a88b8eaed4000ebd2518834ccb5d380033158140000000000fcb392466e8e0000e4700028480000003710000000b2119a00000000000002ad8e162030003cd56967810001e754423610001949b6e00028e000000015700007203604ea69e0a818b222173a834400014e0001940f3c231d39929c144db1530eb7800000011380011340000000ab43f09b038ef5e0d26000273b91800011831b18989f2000000316000031a000000028400048dfcacdb71a0559b35c5f813e8000d71588b6e3419b8a43cd87000000010e0000000144e308c100000000000000000001d1400005a40000000004bbbb9c74c0000000000c0c0000000000d17ea900007010be0e1000284e000000000000000049765dc0000460000001c5e000000736a31c000b7b0001c5c3e42e74e7329d216cbefa21ffb1f454427e000007382945e80000fa2e000000005be9652d160f9a00681864911924c14568817d83cacf678d8fc5334c5e6ecada0ab00000003ae8972b5037a0edd4900000002f542ee00036f0001df100041780000008e42e6c0000008130de9aec7f879913a90340000f15f34001428afa5978000d927857665f5500460a47327dc0004420000001e18eb727e4001e300000000000392000000016cf840005b21d180e43cc00000000000002f75c27b8e0004978001a9400005f785d6e01334678000e0635b26290100000005e41cc9a14ce05fc9c47620d120000000000f4c1a894920f417676a45a2fcc0003f39cf1af40000000000000c260000001e0a65f633130cf6f0c50000001dc80001d42e3400049e29780012890003e80000000e5d5c60134000000733338daae72e46f03f541c8036953584a80df57908a641204a53475cdda
  | 32 => 0x7028002c76000000000000000089c52b000000001c0000000000d3962416efdec0006170000bb70000001dec9ff7b48000a291b600017c00000009f9517000164100038a17e4b2c00046a0000000000552a4b54be5cf41f8001822d8b4af9fc497ae4500006881d40006f90000c9acdf2bbc000cef0006adb130b6900000000013a415600032e4000000000286d0b0eb173f16f880ec5a0002b0a3f28d80001e45464ef084e37496a91c106ac7981a409a6b6323c4cebbf1b5935936a2b337e000030e016b372f94fae36700014513248950e132eaf16353de490bc335c013e997cc9e25a08002b4353e7088a4b6095f300000000000000000000001b2686a000000113200000034140000006452a318d45bb44fea6cb532462ad95831ecea807f2cf555eeb21673c87d827446d09ad83744e2491911075e3076546924010d087870000000ec200000003c21cc45980000001051682c5fdd40000000000000986000109c7d44470001154000a820ada272000d320f42e64b680000068000adc0000000000b8798857c8c4907200000000000006bf0000000d0400033e80000000000002b990746d1d62b2902fe52200004c800030f26f80000000000000d31e6241e000000085a000000000042b000000305c000dc54ba3b2a0007360210000000cc22ef40000002d887a8000000e7c1f700000000005ef000004746600021d4e66bd901a400132a00027f000004d000640280d062ad7551c0000002d200000016fa0003af251a0000007328001b40a96000076800052111cb594000d0c000000800011f2250000000ee22b8917c000508000000000063042d86c9c48000525018400000000031a48fe0004bc0cecac8c550002a50000cf22b263dc0001d600039b000045100011146ea5d30003afc2e0ec54ddbb601bc85e31864f1372c7d7311b158b68068e706955525d19438c80ee00003fe7b740000000000005c360006ec14f4cde701000158c000e970000054000000000158e2e800000000002fa6e3380f12cafa62961000000000000000130ae600024a800054a7c50711b9000000069a8001b3a0003661c11da4887c161527a7ab21b948c88149000232b7c56c2a4f0002eac317000000284cc6e1cf6c628ba5da31d6929dc5a04000000148a8e099e04c00004826fb3f20c5d62cf4d0be000172e4753d59d38ba2b3c3161ee758e47170522d1daadd6371c000a0c8341a20fedaa20eade097d00c838a486850141e36230eb5397d40be72a9be0bb14811e88a00ec49efb3fd619d280000000569c35b0f0001fb400039d00012140520001630fb00000000000c2400000000000000000003d9800000036300011a926aace37693640000000001c44000021b5c00000000002e14001b4400049f0d54870543177192e00000024914297280006
  | 33 => 0x1c70244a4850f00000012106fa624c474000dc43a0815d60266dbcfa1fc0009992e01ce92482ab2691a34c8876f6253d00000d8d7300000832b2588b05048b615343a3b3b54be27223f0521a000015b13a400083831f0001982707000006187aeac66887f568a330000061600084f00000016e6e423b2000054600009c37458720005ac943f932c9252ba7ad47400007223d56ec56f7528b6b002f2e5a696c20005a161a8000b169813436980a1aa0b575802c2b30000b62d78000b2dc828000aa900006519689aaecb0002f498247fb7012bdb1992335ff82a83290005e69e2800061400013dc00029044000005f4c45ee484e35d09fc80000000000000000176baeb265bfb6b4000000000093989d8b2561b2dc8d0e890b5a810000548142a27c8bc376199000000000044dc00000000000000006a100000001a20007d600030000009dd25f8000000bb300024840000002a5b8f9541c515034000000898434a94c0000000000000dc20000000000f52d2f0003a05c1e28e0003060000e0463089ac0005d90001b492d287b414400000000053f0000000466c8c9fe227ccc645f00005821ec4a412c369c5d2bd8000149d56c693955c8b300073eb0bedec2cd13a229a8c923c2e24d7da3820f047c5547c2000577a708c160000000000dc3b1a0001f720000004c62ce51b571e10cad957f44bb5ee80007f40729d729ec9567557941f3a0427a9af8400000000000000000007a00c4c001668c190eba832451659748a79177a0003360001b8000000014640000001ecb6f109278000000004e40000d40000000b720001f8915c0000000b4563800000027e6000b204499122a360736f39e5e000000000287245ed0e0002de96180c800000006fa0000000000224a2a757a24e00000034fc00000000000000009bc0000002e99c0e3bb27f889800093f40b496dcc828f3e5c3d17fa00070989ed76ec0700028d6436348d7c27f15e4d143fbb7d0e2cc90174a7c432e0d1ef4b98593e38006cb7f00a00957501d4424c716e55377d73626616436788ac77e54eb5710c0e3603d8fddb146c056f8d3cf447ff45d88318dc9f37259916e2732e1370ac88a4ae927720994124f63338a49baac73528245c3b82f536567fa67a72d3aba09b020c1e3dc00000000005a00001dffb1e000010c000b2561d0001e0256566ebc0c00000051540000000bb00000000000000002dddd680003bc8000000527f3580000000004f6718f156914241a1f954d79623680008590000000000000c82672934d2060000000000fb30000000000f683150a92c46000a64620c000a82314575e5405bce222078000e9600000000000001ea479c68c0000005d10774cb5000258800141a00031080000006693810000000338271946fa36bf1470cca800013d1f037e06d2000644ae2c
  | 34 => 0xc6600000039055e0b2200005a405ee77369892400000039a0f48b8f00000014f997c2954ad25080009e00000000000000645a3d0000000000000000011080028a33b457a0000001be11a700000012c60004fb448010f00000000000008e5531954484300066d179db76000372ce409205a8454ab9248a0006419bca31f24c13c09697805ac70037190f42300ec27a3a669f052d38e9968baa7a30001c60f3c4111161ac04c0f84a94a000b753f4d93000038c0001cec00e59a00000000006ab000279ba5800000030dc84000000001100000006575a18000a85f878f2ccccab20000050fc6ab5800099400000029510b969000000009cc0000001cb3a697a251a452bb7d3d4ab9176252c68a8b13740f8c86004dc1db8482e4a225ec04a419e0001d0800177648e5ab9ad41dcdee0af246cd74a6270a220cc2626a5ea0000000e570000000000b4f72511f584e7ec0002ad51080000001fe4000cc00000000000ab2e554000b5f71c29cada80637dc7a794cc132c9e000325000090400020cc86600014e39680002845cc36fc0000004e60001a98a4c0ccc0000009cb004a8b4a8412800000000009e48000000d8638600016ba2de397f9fa558296c7f561fa7900f5a246d2fa12c48305970d289805be80030d000000000000000000000330000000b35288e330000e370cfb6150f0391000023600072052ca85489e10c1a9a87771ea338ce25a83d22bb08b9b54ab517946b9ab11fc8a5fa097d5650dcd6d619f859763f12916f5b6852e21e83efd985dd9931cfb7f06073aea27901d2d8776c000000abf30919ccfb700000009f0e1b81d53580004fc0004a98224bc85cbe4b2b80c95abb606000008253c0c0a9c2cd15020002aac9f40000003564000000452024803a7bc00018c8ba40b08000000000ed42e31a95548bd601f2d1a0000000002c9c00036e27c24480324220001f6853f5c4136866cc12ede8601fcdbcaa451f69519851d5e1c1aea424e000000005944100000000000000001af0001ae40000001311974cdc0000000368000347000159691f71c80000005f0520b3f94489ee0000fe40005ad768a7ba0007970003740bfa60e3e200015ea37c7918001e1ad2b000176a00056baa140009f6e350001f000008cb1870cd6fba71379ca0f023888672f81e2a3a0000dfa0b800074a79b9df10426468000000b731581618000de3c87395bbee0007bd5e229d8000000000218d82b93b5407359d9f000000210c0000000f00000db19936cd3bbc0000005eb80011880000000001a624f56f625b000000053a10c87b449f00017b544b4e8318e5a160300007440000005821801a449faa1e80000000000005ed80001652e2291f53c006c1331c40002ba0000003938426ec7eb32c083188dbc99a2f00007d926789840000000000f355b9567
  | 35 => 0x15f117000000000000000006d28001d462b00001de886ef25000131c40a0007531f8e0000000273d2095400034b800000000000007ac42a41100000014fa0000001ec8a99200753c72dab00000c809c4000e1668f2cc2b8a0df0000000000000000000000000077480000009f28003d409c80000870aa00009ff611398c00000000000015ce0000000000000000000244d4233bf32dadb0a0870a66c80015a62646440000dcaef6e211b4400000000000000000000000068c4e71080006cc7eaa68e750001886648f650001e7043b0c881c12fe00059d0c8c00063531536400004ed5ac1270e4e54b8002fa70ee2a1348f6f40000000003591d0c55f0000ad4000000000000000000000023582365c7477c00005456a8cb733c0009e2b2f08def72b4c0000001ae800073b251c9440a1e830518618eeb01ae3b000000000013345e800000013715448ca000249c0000003c780000000000000880000d304fd06475c8a218d2c114abb9551868371c5e43e0d1c0004080001ae92c809903145d16ea702ac18979572d2019a66a0000ad029179919ee16ce2b3d40ed94aa767609d08c4500005814d04ffc2fd6ad28bd26066205e6ea04045aa800016560e6512daae9c000c937440adc000370366d20bc183ca36c823db50043ef5800077476e0001d8400000022e8f4d7ce637d7d8da0e5e5b72778639dfe2344d38dfd73c32928894a011812e0003b8f5994730205f348387cb57a2ca2000000000128e0007a8b1787fc000e5300000000002e400028ebad01638003a6441400033d034cefea05800112c0bce4d260cba03a8c42b1d5c8981e000360a5b5dae8bf05baa204908c32ff1f84fff8ce0428440e5f948c313aea000bb94df9da03307890001783046ec956365700005ba06b36cc0009a054c90fc28672a3e6da142b8333ad80f04bd06d014b2044b904645569bf95f8ce93b99085e48b676fea0468061fe63d0f7563a2da62eb0bd5548472d1b3ed9769f48002d0879e3c74fa944c22a8094e79e9128ae9c214800000000035a15681680000000000000e316343731bde3660a214c4000976353000012f00000000014d23f20001b58f42dab384b4989840000002828000b440000ac5da0c814a5f0a825acf91d202c5522185409d2107106fe9ca75dc66c7742eeb41cfd013b3a7acac60adca342ee1d23084e606eb284649be6c7a600b8bad878a800183a706678800000065c000241d16000044e86e1ce20007904b74000389426b42c0000a90003a30dd434d0000000d0ea8a12f28d4d3059b0003b5a1008fc0001bab3aca6e0002b88b70c7e7642659708052000000101eafe56c6760fdcaf6444a2341f8a110f805c43daf1ab01b3340004be2968d60762000000000140e53600000000007a500002e000088980029a800000061dc00
  | 36 => 0x7436b6999e000d4b6a800000000006b78c6176c79b3638000588e8b0003d080000002db57383000001cb40000000000996f08dd616fb6f9f60000b8301e1f94b920000001baf366000595000026800000029224b0557d641f6a2b29c90002d18b56000546c39c00089dbfd0bc4e708eb0002ad0000afda36057db4eed63e4a6a13f164978580926f40000000b8c0000004cd8000d440000000ffc000a1f0001895a6e2fb7383510000c2438fa86ebbf000567983db36f2200011ed6b4d4314f8000b2e00066f00000008d20002479c9e000000035dd2a663f493bb876ad1d2e50ab196f0000001130000000356800002900000015870e01bc2f90000f5ed8869b22a0000bf50002bf4b98973090819f094731800381935af190001a2c00067100000011205b63861cf400000022680000000000001234b20000446000000000033ac00114400023b000000055d4fac5e190869a0002b400000ff103995a0000002ae294518cc7149b80009cc0007951d15dabefe8da833615d5fc4a92a998254f2000299c0001ca38657dc00022e06d97e936e00071300016821c31a65860674d0d0183b957fcdefb1d32bd8880004441a6f1b27843f90298136c6dd76d0e800000000036e9286df0432275198600066d8000000a750002223b2ecb13ac0000d3ebe00002b3b0ca1fc7468001b86d1313800002788d000000008ee2bc0000000e330003172bdc000c4600024400000004e09514000000254ecc743016577892f12563e80000000e34f2f0b5c0004c003d5045a00e58778127a144000e563fa800045400068789440000002bbafd09a00cd0001d657248a754935ad3f00000000001d9a00000011e8000ca129f8ddd616000146223c1422cb173064c3ec9c62b4b5d8792000630000111f33e60291b94b0bf20000fcd610b171ac8afc1045e01c5b965662b0d013915cf9e8071969f03dc372cd2a64e1e0f08178ed681d3e7426bf80018e484426c39ed581e1a77e0000000000192956400018b4ac44795b36ed8df000000000
  | _ => 0
def gbK3 : Nat → Nat
  | 0 => 0xc6314540a44835886214540a4681d4c624c540c467318b514c540944825c4530c540944825cc510c540946829d5310c540946851c9310c540c46651c9310c540c44651c9310c54094687d49310c54094487149310c540c44639cb5148540944835c85108540946839d52108540946851cd2108540c46651cd2108540c44651cd210854094687d4d21085409448714d2108540a44825846194c40a14845846154c40a44825846154c40a448258c6394440a44835886294440a148458c6354440a448258c6354440a24845886254440a44835886254440a448154c624c440c4473189514c440944825c6530c440944825ce510c440944825d5310c440945851c9310c440c47651c9310c440c45651c9310c44094487949310c44094487549310c440c5165dc1310c440c44631c95148440944835ca5108440944835d52108440945851cd2108440c47651cd2108440c45651cd21084409448794d21084409448754d2108440c6165dc12108440a508654d5150040c507654d5150040e41531895150040c60765495150040e40635495150040c46631c951d0730944825c4540c73094682dd7410c730c44631c95148730864875952108730c47651cd2108730945851c9310c63094487549310c630c44631c95148630c47651cd2108630c45651cd2108630a448258c5110530944825c4540c530944825d4410c530a14845943108530d10541c543cc1309c1801cd2108430b10815504310030c14641c5544c030c1975193434c030a448254e61d0f10a44815c86354b10c44721c56314b10a448354a61d0b10a448254c614cb10a4483548614cb1084c87595320cb10c47651c5320cb10c45651c5320cb10944825cc540c71094682dd7430c710944835c8540871094683dd74208710a448254c614c310a448254c614ca10a4483548614ca10c47651c5320ca10c45651c5320ca10945851c9310c61094487549310c610945851cd21086109448754d2108610c44531c96110d10c44731496110910944825cc540c510c17761d1530c510d0474dc9530c510d07741c9530c510d04741c9530c510d1074dc1530c51094682dd7430c510944825d4430c51091684dd6320c510914845d4320c510944835c85408510c27761d15208510d0474dcd5208510d07741cd5208510d04741cd5208510d2074dc1520851094683dd74208510944835d4420851092684dd73208510924845d43208510c44531c961cc110a1484594314c110c447314961c8110a24845942148110a44835942148110d10541cd41c4110d20541c941c4110944815ca530c810945851c5320c8109c1801c5320c810944825c5530c410944825ce510c410944835c55208410944835ca5108410b10835504110010b20825504110010c14641cd5444010c24641c95444010c31751934144010
  | 1 => 0x1ac280dcc624c431ac180dcc624c4318c78750c624c431ac38050c624c431ac08050c624c4318c6829d3654c4318c4825c3654c4318c4825c0644c4318c686dc9544c431c90641c1544c4318c787590624c431a4785590624c431ac380590624c431ac080590624c431ac280dd4624c431ac180dd4624c431a47855d0624c431ac3805d0624c431ac0805d0624c431a45851d0624c431ac2801d0624c431ac1801d0624c4318c787550624c4318c487550624c431ac380550624c431ac080550624c4318c687150624c4318c587150624c431ac280150624c431ac180150624c431a4585dc0624c431a45859c0624c431cc1701c0624c431cc0629c3524c431cc0625c3524c4318d1801da524c431c4775189424c431c4475189424c431cc062dc1424c431cc0621c1424c4318d1801d8424c431854865d4424c431c4675188424c4318c6829d3604c431c457518a604c4318c687d89604c431c8474d89604c431c8774189604c431c8474189604c4318c48798931d40318c48758931d40318c5861c931940318c48798931940318c4875893194031b40824c55014031a448358a6115221c45769c7530ca21c44539cb6150d21c44531c96110d21c44721c563150218c683dc960d0421945859cb430c421b4180994320c421a4585190320c421ac180190320c421a4586150320c421b4180150320c421ac18018c3288421ac280dc86348421ac180dc863484218c686dcd42484218c68718d42484218c48718d4248421cc063dc14248421cc0631c142484218c6839d365484218c4835c365484218c4835c064484218c686dcd5448421ca0641c154484218c7875906348421a47855906348421ac3805906348421ac0805906348421ac280dd46348421ac180dd46348421a47855d06348421ac3805d06348421ac0805d06348421a45851d06348421ac2801d06348421ac1801d063484218c78755063484218c4875506348421ac3805506348421ac08055063484218c68715063484218c5871506348421ac2801506348421ac1801506348421a4585dc06348421a45859c06348421cc1701c06348421cc0639c35348421cc0635c353484218e1801da5348421a448654c5348421c477518d4348421c447518d4348421cc063dc14348421cc0631c143484218c683dd843484218e1801d84348421864865d44348421c467518c43484218c6839d36048421c457518e60484218c687d8d6048421c8474d8d6048421c877418d6048421c847418d60484218c48798d21d40218c48758d21d40218c5861cd21940218c48798d21940218c48758d2194021b40834855014021944825c6530c640944825ce510c640944825d5310c640944835ca5108640944835d52108640a4682d8661d4d40a44825846114d40a4682d8e63d4540a4683d8a62d4540a448258
  | 2 => 0x118002e8ee001846900000000000000010400000000000000000000248000000000000001620106a00000000000016c00000000000000000000000000d80000000001e000000788003b0000023c000488b800002283680000000000de8eca40000000000000b6000fc000320a13a00000000004b0002700081800000000022400000000260000000090000000017a00000000007b0000017884800000200000000000000002d06e000068e8008680000000000000012200000000000020c00000000000023d000000004e5f8cc6700000000388000560400000000007e18f622100000000000000000004a000000005c5600068000000ab100001f00000000001806a887061b2020502386c00242000000000000000000000000000000000ac000dc4c8000000000000000000000000000919083015c00000002080014a1fa30001f205d6800000000000000000000002168281a03c006e1508000020d2a2a80000000000000000000000000007480000000881d80000000000000000000000000000600010e000001900069c003c8000f800045380000000000400000000000000000001d800000002f1f07a80000000660000000000000000000000091000000004300000000000e6530000000000030001ce1cd1a00072001fa000002205432a0e278782a034000006a00000000000be000000000000000000008e1b000000002360000000000000006481e22800000000000000000000001d22a2c15a3c0847d04c79800000000000e0000066c0000000000000001c0005a63881000003f80046000000000011e000000000020a2200148000a9000008f800000000000000000089950000000000231c017c000000089800000000014e050d431000000d2000006992e0004290196440a04c03a870003900000000000000000000000000007180000000000000005800000000005c800000000002a000e000000320006b800000002b800000006180000000000000019365c001c0c27f02c000000000000000000000100001c010000000400000000000100000000000080000000000010000000001004000100100000000000000200800004010040000800000000140100800000010000800400008000000300801004010000200000000040000000401000000040700c0000000000000080400c0000001000000080000000000040040400000000000100301002a60825456014443a488254d6014c41a48835496014841c46631c96115331a448258e6115231a4681d8c5250931c467314b6150931a448158c5210931c44731496110931c44731c562150318c682dc560d0c318c682dcd60d0431ac280dc4624c431ac180dc4624c4318c686dc9414c4318c687189414c431cc062dc1414c431cc0621c1414c4318c686dc9434c43
  | 3 => 0x1c800140000003e19a5c00c878001bd7600000640000000000000000000018a001360000017400000000000000000000000015600000490000000000000158006d80000000000ce000001a0806f0000009600000002320000000000001448d05e6d1de4812800000001fe000000000000000000000000000000001cf000005a9420000000000000b2001a3000000000034000001ca00000000000000000000000000000067c0000000000160000047000028af689600000000000000000000000000000004084466400001c20013c0000000000000b8001744495e260f40013e0000000214000000010a75000000a61e82400000000000018d00000458120000025000358000000000000000000000000000000000000000000000ea0000060800000000019e518000000000000001ac001da0020200000001e877000000000000000000000000013400000000000000000000000001d400000865b8000002e000000f000000000011400000550003e9d000000000007d80071000001be8b000000a20000000000001ba000003d80000000184000000000000000000000000010498000000002c000016400000224000000000000000000001300062000000000000000199e40e000001660005200000269d7000000080064400001940000000000730000000000000000e8549065f18c86000000c60000036000001d6000000000000000001ee0
  | _ => 0
def gbN (k : Nat) : Nat :=
  match k with
  | 8 => 1
  | 7 => 27
  | 6 => 1098
  | 5 => 6068
  | 4 => 3921
  | 3 => 292
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
  | 6 => packedAt gbK6 (35670+((h/502+packedAt gbK6 (29646+(h % 502)*12) 12) % 2644)*12) 12
  | 5 => packedAt gbK5 (266186+((h/2543+packedAt gbK5 (230584+(h % 2543)*14) 14) % 10073)*14) 14
  | 4 => packedAt gbK4 (212422+((h/1561+packedAt gbK4 (192129+(h % 1561)*13) 13) % 6803)*13) 13
  | 3 => packedAt gbK3 (18600+((h/108+packedAt gbK3 (17520+(h % 108)*10) 10) % 1013)*10) 10
  | _ => 0
def gbPos : Nat → Bits
  | 0 => 0x3f81fff81ffffffe07c1f07fe0fffffe88e3ff
  | 1 => 0x3ffe03ffe03f81fff801ff83ff07c07f0f3ccf
  | 2 => 0xc00003ffffc001fffffe0003fff8007ff03f0f
  | 3 => 0xfffffc00000001fffffffffc0000007fffc00f
  | 4 => 0xfffffffffffffe1fffffffffffffff81fffff0
  | _ => 0
def gbNeg : Nat → Bits
  | 0 => 0x8a9418c8c285682e00c83234646b4716886157
  | 1 => 0x130ca951498a2a565810d691ad23892b0b2ccb
  | 2 => 0x9a6951a285134c9aab5a0422ce71124db0370d
  | 3 => 0x1c3061c7162c711d359d673808422471ddc00e
  | 4 => 0x2041820418300001c621884310843800669aa0
  | _ => 0
def gbAtlas : Atlas := ⟨8,rawDecor 31 gbPos gbNeg, 0xfeea8000feea8000feea8000feea8000feea8000feea8000feea8000feea8000feea8000feea8000feea8000feea8000feea8000feea8000feea8000feea8000, gbN, gbR, (fun _ _ => 0), gbI⟩
end PEqualNP.Outside.L_meta_12825
namespace PEqualNP.Outside.L_meta_12825
open PEqualNP.Outside.L_meta_12825.Model PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
theorem bgb_3_288 : Interval gbAtlas 3 288 4 := block_range (n:=4) (by decide +kernel)
theorem allgb_3 : Interval gbAtlas 3 0 292 := (concat (concat (concat bgb_3_0 bgb_3_32) (concat bgb_3_64 (concat bgb_3_96 bgb_3_128))) (concat (concat bgb_3_160 bgb_3_192) (concat bgb_3_224 (concat bgb_3_256 bgb_3_288))))
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
theorem bgb_4_3904 : Interval gbAtlas 4 3904 17 := block_range (n:=17) (by decide +kernel)
theorem allgb_4 : Interval gbAtlas 4 0 3921 := (concat (concat (concat (concat (concat (concat bgb_4_0 (concat bgb_4_32 bgb_4_64)) (concat (concat bgb_4_96 bgb_4_128) (concat bgb_4_160 bgb_4_192))) (concat (concat (concat bgb_4_224 bgb_4_256) (concat bgb_4_288 bgb_4_320)) (concat (concat bgb_4_352 bgb_4_384) (concat bgb_4_416 bgb_4_448)))) (concat (concat (concat bgb_4_480 (concat bgb_4_512 bgb_4_544)) (concat (concat bgb_4_576 bgb_4_608) (concat bgb_4_640 bgb_4_672))) (concat (concat (concat bgb_4_704 bgb_4_736) (concat bgb_4_768 bgb_4_800)) (concat (concat bgb_4_832 bgb_4_864) (concat bgb_4_896 bgb_4_928))))) (concat (concat (concat (concat bgb_4_960 (concat bgb_4_992 bgb_4_1024)) (concat (concat bgb_4_1056 bgb_4_1088) (concat bgb_4_1120 bgb_4_1152))) (concat (concat (concat bgb_4_1184 bgb_4_1216) (concat bgb_4_1248 bgb_4_1280)) (concat (concat bgb_4_1312 bgb_4_1344) (concat bgb_4_1376 bgb_4_1408)))) (concat (concat (concat (concat bgb_4_1440 bgb_4_1472) (concat bgb_4_1504 bgb_4_1536)) (concat (concat bgb_4_1568 bgb_4_1600) (concat bgb_4_1632 bgb_4_1664))) (concat (concat (concat bgb_4_1696 bgb_4_1728) (concat bgb_4_1760 bgb_4_1792)) (concat (concat bgb_4_1824 bgb_4_1856) (concat bgb_4_1888 bgb_4_1920)))))) (concat (concat (concat (concat (concat bgb_4_1952 (concat bgb_4_1984 bgb_4_2016)) (concat (concat bgb_4_2048 bgb_4_2080) (concat bgb_4_2112 bgb_4_2144))) (concat (concat (concat bgb_4_2176 bgb_4_2208) (concat bgb_4_2240 bgb_4_2272)) (concat (concat bgb_4_2304 bgb_4_2336) (concat bgb_4_2368 bgb_4_2400)))) (concat (concat (concat (concat bgb_4_2432 bgb_4_2464) (concat bgb_4_2496 bgb_4_2528)) (concat (concat bgb_4_2560 bgb_4_2592) (concat bgb_4_2624 bgb_4_2656))) (concat (concat (concat bgb_4_2688 bgb_4_2720) (concat bgb_4_2752 bgb_4_2784)) (concat (concat bgb_4_2816 bgb_4_2848) (concat bgb_4_2880 bgb_4_2912))))) (concat (concat (concat (concat bgb_4_2944 (concat bgb_4_2976 bgb_4_3008)) (concat (concat bgb_4_3040 bgb_4_3072) (concat bgb_4_3104 bgb_4_3136))) (concat (concat (concat bgb_4_3168 bgb_4_3200) (concat bgb_4_3232 bgb_4_3264)) (concat (concat bgb_4_3296 bgb_4_3328) (concat bgb_4_3360 bgb_4_3392)))) (concat (concat (concat (concat bgb_4_3424 bgb_4_3456) (concat bgb_4_3488 bgb_4_3520)) (concat (concat bgb_4_3552 bgb_4_3584) (concat bgb_4_3616 bgb_4_3648))) (concat (concat (concat bgb_4_3680 bgb_4_3712) (concat bgb_4_3744 bgb_4_3776)) (concat (concat bgb_4_3808 bgb_4_3840) (concat bgb_4_3872 bgb_4_3904)))))))
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
  exact frozen ready cert (by decide +kernel) (by decide) [(inputs.getD 0 zero, 14, 15),(inputs.getD 1 zero, 13, 15),(inputs.getD 2 zero, 11, 15),(inputs.getD 3 zero, 7, 15),(inputs.getD 4 zero, 1, 17)] (proper_of _ (by decide +kernel)) (by decide +kernel) (by decide +kernel)
def fullRoots : List Sig := [inputs.getD 5 zero,inputs.getD 0 zero,inputs.getD 1 zero,inputs.getD 2 zero,inputs.getD 3 zero,inputs.getD 4 zero]
def fullWord : Sig := 0xfeea800080008000feea800080008000feea800080008000feea800080008000feea800080008000feea800080008000feea800080008000feea800080008000
theorem fullBound (certgb : Complete gbAtlas) : Lower true fullRoots fullWord 10 := by
  have low := boundgb certgb
  have lift := lift_ok (u:=true) (ms:=fixRows 0 32) (raw:=fullRoots) (T:=fullWord) (xs:=[(inputs.getD 5 zero,17,49)]) (by decide +kernel) (proper_of _ (by decide +kernel)) (proper_of _ (by decide +kernel)) low
  have hc : ((([(inputs.getD 5 zero,17,49)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card) = 1 := by decide +kernel
  rw [hc] at lift
  exact lift
def posted (x : Fin 6 → Bool) : Bool := Nat.testBit (3936921736 * 2 ^ 32 + 3221225472) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
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
  unfold PEqualNP.Outside.L_meta_12825.Model.Repr at out
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

def mono : List Gate := [⟨.and,[0,5]⟩,⟨.and,[1,4]⟩,⟨.or,[6,7]⟩,⟨.and,[4,5]⟩,⟨.or,[2,3]⟩,⟨.and,[9,10]⟩,⟨.and,[3,8]⟩,⟨.or,[1,11]⟩,⟨.and,[2,12]⟩,⟨.and,[6,13]⟩,⟨.or,[14,15]⟩]
theorem monoShape : ∀ g ∈ mono, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [mono, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem monoEval : ∀ x, Circuit.eval ⟨mono,16⟩ (List.ofFn x) = posted x := by decide +kernel
theorem solve (low : Lower true fullRoots fullWord 10) : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3936921736 * 2 ^ 32 + 3221225472) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3936921736 * 2 ^ 32 + 3221225472) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
end PEqualNP.Outside.L_meta_12825

open PEqualNP.Outside.L_meta_12825 in
theorem PEqualNP.Outside.L_meta_12825 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3936921736 * 2 ^ 32 + 3221225472) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3936921736 * 2 ^ 32 + 3221225472) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  solve (fullBound allgb)
